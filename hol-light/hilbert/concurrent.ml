(* ========================================================================= *)
(* Forkable discovery which can be fed from the changing goal hypotheses.    *)
(* Forked discoverers can be paused and resumed.                             *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)
(* Concurrent discovery.

   The dependence on goal hypotheses is added in with a writer. 

*)

module Discovery_cc :
sig
  include DISCOVERY
  type command  = Pause | Resume    
  val to_list : 'a m -> 'a LazyList.t LazyList.t
  val hyps_discoverer : goal -> thm m    
  val monitor : unit -> thm m
  val with_deps : 'a m -> ((string * thm) list * 'a) m
  val with_tags : 'a m -> (term list * 'a) m
  val collapse  : 'a m -> 'a m
  val discharge : thm m -> thm m
  val disjuncts : thm -> thm m
  val split : thm m -> thm m
  val fork : ('a m -> 'b) -> 'a m -> command -> unit
  val fork_to_output : unit BatIO.output -> thm m -> command -> unit
end =
struct
  module Bo = BatOption
  module Bs = BatString    
  
  type command  = Pause | Resume

  module Command : sig
    type t
    val poll : t -> unit
    val send : command -> t -> unit
    val make : unit -> t
  end =
  struct
    type t = command Event.channel
        
    let make () = Event.new_channel ()
      
    let rec poll command_chan =
      let rec loop () =
        match Event.sync (Event.receive command_chan) with
            Resume -> ()
          | Pause  -> loop () in
      match Event.poll (Event.receive command_chan) with
          Some Pause  -> loop ()
          | _ -> ()
          
    let send command chan =
      Event.sync (Event.send chan command)
  end
    
  module Channels = struct
    module Hashtbl = BatHashtbl
    let env = Hashtbl.create 4
    let mutex = Mutex.create ()

    let with_channel f xs =
      let chan = Command.make () in
      ignore (Thread.create
                (fun xs -> Mutex.lock mutex;
                  Hashtbl.add env (Thread.id (Thread.self ())) chan;
                  Mutex.unlock mutex;
                  f xs) xs);
      chan
        
    let get_channel () =
      Mutex.lock mutex;
      let chan = Hashtbl.find_option env
        (Thread.id (Thread.self ())) in
      Mutex.unlock mutex;
      chan

    let poll () =
      Bo.may Command.poll (get_channel ())
  end
      
  module Hypset =
  struct
    include BatSet.Make(struct
      type t = string * thm
      let compare = compare
    end)
    let zero () = empty
    let plus    = union
  end

  module Hypwriter =
  struct
    include Monad.MakeWriter(Hypset)
    let cmp = (*C Hypset.subset*) fun x y -> true
  end

  module Hypwriterm = Monad.Make(Hypwriter)
  module Stream = Monad.CollectionWriter(Hypwriter)(Treestream)
  module Streamm = Monad.MakeLazyPlus(Stream)    
  module Treestreamm = Monad.MakeLazyPlus(Treestream)
  module Treestreama = Applicative.Make(Treestream)
  module Tm = Monad.MakeLazyPlus(Termtree)

  let with_deps xs =
    Stream.bind
      (Stream.pass (Stream.run xs))
      (fun (deps,x) ->
        Streamm.lift1 (fun () -> Hypset.elements deps, x)
          (Stream.write deps))

  let with_tags xs =
    Stream.bind
      (Stream.pass (Treestream.with_tags (Stream.run xs)))
      (fun (terms,(deps,x)) ->
        Streamm.lift1 (fun () -> terms,x)
          (Stream.write deps))

  let collapse xs =
    Stream.bind
      (Stream.pass (Treestream.collapse (Stream.run xs)))
      (fun (deps,x) ->
        Streamm.lift1 (fun () -> x)
          (Stream.write deps))

  let discharge xs =
    collapse (Streamm.lift1 (fun (terms,thm) -> rev_itlist DISCH terms thm)
                (with_tags xs))

  let bind xs f =
    Stream.bind xs (fun x -> Channels.poll (); f x)
      
  module Di = Discovery(struct
    include Stream
    type 'a t = 'a Hypwriter.m Treestream.t
    let bind = bind
    let (<*>) fs xs =
      Treestreama.lift2
        (fun f x ->
          Channels.poll ();
          Hypwriterm.(<*>) f x) fs xs
    let to_depth n = Treestream.to_depth n
    let delay xs = Treestream.delay xs
    let iterate f = Treestream.iterate f
    let to_list xs =
      Ll.map (Ll.map (fun _,(_,x) -> x))
        (Treestream.to_list (Stream.run (with_tags xs)))
    let to_thms xs =
      Treestream.to_thms
        (Treestreamm.lift1 (fun _,thm -> thm)
           (Stream.run xs))
  end)

  include Di

  let disjuncts thm = Stream.pass (Treestream.disjuncts thm)

  let hyps_discoverer =
    let with_hyp (label,thm) =
      Streamm.lift2 (fun () thm -> thm)
        (Stream.write (Hypset.singleton (label,thm)))
        (Stream.return thm) in
    fun (hyps,g) ->
      let sets = Bl.map snd (Bl.filter ((=) "=" o fst) hyps) in
      rewrite sets (Streamm.msum (map with_hyp hyps))
      
  let monitor () =
    Stream.unique ~cmp:(=)
      (Treestream.iterate
         (fun _ ->
           try
             hyps_discoverer (top_realgoal ())
           with _ -> Treestreamm.zero ())
         (Treestreamm.zero ()))

  let split =
    conjuncts o C Streamm.bind disjuncts
      o Streamm.lift1 (CONV_RULE DNF_CONV)

  let to_forced xs =
    Ll.fold_left Tm.plus (Termtree.zero ())
      (Ll.map Termtree.to_forced xs)

  let fork f xs =
    let chan = Channels.with_channel f xs in
    fun cmd -> Command.send cmd chan

  let fork_to_output =
    let string_of_dthm (hyps,(tags,thm)) =
      let thm = rev_itlist DISCH tags thm in
      Bs.join " " (map fst hyps) ^ " : " ^
        string_of_term (concl thm) in
    let delaying xss =
      Ll.map 
        (fun xs -> if Ll.is_empty xs then Channels.poll (); 
          Thread.delay 1.0;
          xs) xss in
    fun output xs ->
      fork (fun xs ->
        let strings = 
          Ll.map string_of_dthm
            (Ll.concat
               (delaying (to_list (with_deps (with_tags xs))))) in
        write_lazy_list output strings)
        xs
end
