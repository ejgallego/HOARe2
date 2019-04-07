(* -------------------------------------------------------------------- *)
exception Unexpected

let unexpected () = raise Unexpected

(* -------------------------------------------------------------------- *)
type 'a eq  = 'a -> 'a -> bool
type 'a cmp = 'a -> 'a -> int

(* -------------------------------------------------------------------- *)
let tryexn (ignoreexn : exn -> bool) (f : unit -> 'a) =
  try  Some (f ())
  with e -> if ignoreexn e then None else raise e

let try_nf (f : unit -> 'a) =
  tryexn (function Not_found -> true | _ -> false) f

let try_finally (body : unit -> 'a) (cleanup : unit -> unit) =
  let aout =
    try  body ()
    with e -> cleanup (); raise e
  in
    cleanup (); aout

let identity x = x 

let (^~) f = fun x y -> f y x

let (-|) f g = fun x -> f (g x)
let (|-) g f = fun x -> g (f x)

let (|>) x f = f x
let (<|) f x = f x

(* -------------------------------------------------------------------- *)
let copy (x : 'a) : 'a =
  Obj.obj (Obj.dup (Obj.repr x))

(* -------------------------------------------------------------------- *)
let reffold (f : 'a -> 'b * 'a) (r : 'a ref) : 'b =
  let (x, v) = f !r in r := v; x

(* -------------------------------------------------------------------- *)
type 'a tuple0 = unit
type 'a tuple1 = 'a
type 'a tuple2 = 'a * 'a
type 'a tuple3 = 'a * 'a * 'a
type 'a tuple4 = 'a * 'a * 'a * 'a
type 'a tuple5 = 'a * 'a * 'a * 'a * 'a
type 'a tuple6 = 'a * 'a * 'a * 'a * 'a * 'a
type 'a tuple7 = 'a * 'a * 'a * 'a * 'a * 'a * 'a
type 'a tuple8 = 'a * 'a * 'a * 'a * 'a * 'a * 'a * 'a
type 'a tuple9 = 'a * 'a * 'a * 'a * 'a * 'a * 'a * 'a * 'a

(* -------------------------------------------------------------------- *)
let as_seq0 = function [] -> () | _ -> assert false
let as_seq1 = function [x] -> x | _ -> assert false
let as_seq2 = function [x1; x2] -> (x1, x2) | _ -> assert false
let as_seq3 = function [x1; x2; x3] -> (x1, x2, x3) | _ -> assert false

let as_seq4 = function
  | [x1; x2; x3; x4] -> (x1, x2, x3, x4)
  | _ -> assert false

let as_seq5 = function
  | [x1; x2; x3; x4; x5] -> (x1, x2, x3, x4, x5)
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let proj3_1 (x, _, _) = x
let proj3_2 (_, x, _) = x
let proj3_3 (_, _, x) = x

let fst_map (f : 'a -> 'c) ((x, y) : 'a * 'b) =
  (f x, y)

let snd_map (f : 'b -> 'c) ((x, y) : 'a * 'b) =
  (x, f y)

let pair_equal tx ty (x1, y1) (x2, y2) =
  (tx x1 x2) && (ty y1 y2)

(* -------------------------------------------------------------------- *)
let opt_equal (f : 'a -> 'a -> bool) o1 o2 =
  match o1, o2 with
  | Some x1, Some x2 -> f x1 x2
  | None   , None    -> true
  | _      , _       -> false

(* -------------------------------------------------------------------- *)
let none = None
let some = fun x -> Some x

let oiter (f : 'a -> unit) (x : 'a option) =
  match x with None -> () | Some x -> f x

let obind (f : 'a -> 'b option) (x : 'a option) =
  match x with None -> None | Some x -> f x

let otolist (x : 'a option) =
  match x with None -> [] | Some x -> [x]

let ofold (f : 'a -> 'b -> 'b) (v : 'b) (x : 'a option) =
  match x with
  | None   -> v
  | Some x -> f x v

let ocompare cmp x1 x2 =
  match x1, x2 with
  | None   , None    -> 0
  | Some x1, Some x2 -> cmp x1 x2
  | None   , Some _  -> -1
  | Some _ , None    -> 1

let omap (f : 'a -> 'b) (x : 'a option) =
  match x with None -> None | Some x -> Some (f x)

let omap_dfl (f : 'a -> 'b) (d : 'b) (x : 'a option) =
  match x with None -> d  | Some x -> f x

let osmart_map (f : 'a -> 'b) (x : 'a option) =
  match x with 
  | None -> x 
  | Some y -> 
      let y' = f y in 
      if y == y' then x else Some y'

let odfl (d : 'a) (x : 'a option) =
  match x with None -> d | Some x -> x

let ofdfl (d : unit -> 'a) (x : 'a option) =
  match x with None -> d () | Some x -> x

let oget (x : 'a option) =
  match x with None -> assert false | Some x -> x

let oall2 f x y = 
  match x, y with
  | Some x, Some y -> f x y
  | None  , None   -> true
  | _     , _      -> false 

(* -------------------------------------------------------------------- *)
module Counter : sig
  type t

  val create : unit -> t
  val next   : t -> int
end = struct
  type t = {
    mutable state : int;
  }

  let create () = { state = 0; }

  let next (state : t) =
    let aout = state.state in
      state.state <- state.state + 1;
      aout
end    

(* -------------------------------------------------------------------- *)
module Disposable : sig
  type 'a t

  exception Disposed

  val create  : ?cb:('a -> unit) -> 'a -> 'a t
  val get     : 'a t -> 'a
  val dispose : 'a t -> unit
end = struct
  type 'a t = ((('a -> unit) option * 'a) option) ref

  exception Disposed

  let get (p : 'a t) =
    match !p with
    | None        -> raise Disposed
    | Some (_, x) -> x

  let dispose (p : 'a t) =
    let do_dispose p =
      match p with
      | Some (Some cb, x) -> cb x
      | _ -> ()
    in

    let oldp = !p in
      p := None; do_dispose oldp

  let create ?(cb : ('a -> unit) option) (x : 'a) =
    let r = ref (Some (cb, x)) in
      Gc.finalise (fun r -> dispose r) r; r
end

(* -------------------------------------------------------------------- *)
module List = struct
  include List

  let hd2 l = 
    match l with
    | a::b::_ -> a,b
    | _ -> assert false

  let ocons o l = 
    match o with
    | None -> l
    | Some e -> e :: l

  let isempty xs = xs == []

  let ohead (xs : 'a list) =
    match xs with [] -> None | x :: _ -> Some x

  let otail (xs : 'a list) =
    match xs with [] -> None | _ :: xs -> Some xs

  let min b xs = List.fold_left min b xs
  let max b xs = List.fold_left max b xs

  let create n x =
    let rec aux n xs =
      if n <= 0 then xs else aux (n-1) (x::xs)
    in
      aux n []

  let iteri f xs =
    let rec doit i = function
      | []      -> ()
      | x :: xs -> f i x; doit (i + 1) xs
    in
      doit 0 xs

  let iter2i f xs ys =
    let rec doit i = function
      | [], [] -> ()
      | x :: xs, y :: ys -> f i x y; doit (i + 1) (xs, ys)
      | _, _ -> failwith "List.iter2i"
    in
      doit 0 (xs, ys)

  let rec fusion f xs ys =
    match xs, ys with
    | _ , [] -> xs
    | [], _  -> ys

    | x::xs, y::ys ->
        let z = f x y in z :: (fusion f xs ys)

  let rec pmap (f : 'a -> 'b option) (xs : 'a list) =
    match xs with
    | []      -> []
    | x :: xs -> ocons (f x) (pmap f xs)

  let rec iter2o f xs ys =
    match xs, ys with
    | []   , []    -> ()
    | x::xs, []    -> f (Some x) (None  ); iter2o f xs []
    | []   , y::ys -> f (None  ) (Some y); iter2o f [] ys
    | x::xs, y::ys -> f (Some x) (Some y); iter2o f xs ys

  let prmap f l = 
    let rec aux r l = 
      match l with 
      | [] -> r
      | x::l -> aux (ocons (f x) r) l in
    aux [] l

  let findopt (f : 'a -> bool) (xs : 'a list) =
    try  Some (List.find f xs)
    with Not_found -> None

  let rec pick (f : 'a -> 'b option) (xs : 'a list) =
    match xs with
      | []      -> None
      | x :: xs -> begin
        match f x with
          | None        -> pick f xs
          | Some _ as r -> r
      end

  let rec fpick (xs : (unit -> 'a option) list) =
    match xs with
    | []      -> None
    | x :: xs -> begin
        match x () with
        | None   -> fpick xs
        | Some v -> Some v
    end

  let index (v : 'a) (xs : 'a list) : int option =
    let rec index (i : int) = function
      | [] -> None
      | x :: xs -> if x = v then Some i else index (i+1) xs
    in
      index 0 xs

  let all2 (f : 'a -> 'b -> bool) xs ys =
    let rec all2 = function
      | ([]     , []     ) -> true
      | (x :: xs, y :: ys) -> (f x y) && (all2 (xs, ys))
      | (_      , _      ) -> false
    in
      all2 (xs, ys)

  let rec uniqf (f : 'a -> 'a -> bool) (xs : 'a list) =
    match xs with
      | []      -> true
      | x :: xs -> (not (List.exists (f x) xs)) && (uniqf f xs)

  let uniq l = uniqf (=) l

  let assoc_eq eq (x : 'a) (xs : ('a * 'b) list) =
    snd (List.find (fun (x',_) -> eq x x') xs) 

  let tryassoc_eq eq x xs = 
    try_nf (fun () -> assoc_eq eq x xs)

  let tryassoc (x : 'a) (xs : ('a * 'b) list) =
    tryassoc_eq (=) x xs

  let take_n (n : int) (xs : 'a list) =
    let rec take n xs acc =
      match n, xs with
      | 0, _ | _, [] -> List.rev acc, xs
      | _, x :: xs -> take (n-1) xs (x :: acc)
    in
    take n xs []

  let take (n : int) (xs : 'a list) = fst (take_n n xs)

  let split_n n l = 
    let rec aux r n l = 
      match n, l with
      | _, [] -> raise Not_found 
      | 0, x::l -> r, x, l
      | _, x::l -> aux (x::r) (n-1) l in
    aux [] n l 

  let find_split f l = 
    let rec aux r l = 
      match l with 
      | [] -> raise Not_found
      | x::l -> if f x then r, x, l else aux (x::r) l in
    aux [] l
 
  let mapi (f : int -> 'a -> 'b) =
    let rec doit n xs =
      match xs with
      | [] -> []
      | x :: xs -> let x = f n x in x :: (doit (n+1) xs)
    in
      fun (xs : 'a list) -> doit 0 xs

  let map_fold (f : 'a -> 'b -> 'a * 'c) (a : 'a) (xs : 'b list) =
    let a = ref a in
    let f b = 
      let (a',c) = f !a b in
      a := a'; c in
    let l = List.map f xs in
    !a, l
  
  let map_combine
      (f1  : 'a -> 'c) (f2  : 'b -> 'd)
      (xs1 : 'a list ) (xs2 : 'b list )
  =
    let rec doit xs1 xs2 =
      match xs1, xs2 with
      | ([], []) -> []
      | (x1 :: xs1, x2 :: xs2) ->
        let y1, y2 = f1 x1, f2 x2 in
        let ys = doit xs1 xs2 in
          (y1, y2) :: ys
      | (_, _) -> invalid_arg "List.map_combine"

  in
      doit xs1 xs2

  let fold_lefti f a l = 
    let i = ref (-1) in
    let f a e =  incr i; f !i a e in
    List.fold_left f a l

  let rec filter2 f la lb = 
    match la, lb with
    | [], [] -> [], []
    | a::la, b::lb ->
        let (la,lb as r) = filter2 f la lb in
        if f a b then a::la, b::lb 
        else r
    | _, _ -> invalid_arg "List.filter2"

  let sum xs = List.fold_left (+) 0 xs

  module Smart = struct
    let rec map f l = 
      match l with
      | []    -> []
      | x::xs ->
        let x'  = f x in
        let xs' = map f xs in
          if x == x' && xs == xs' then l else x'::xs'

    let map_fold f a xs =
      let r = ref a in
      let f x = let (a, x) = f !r x in r := a; x in
      let xs = map f xs in
        (!r, xs)
  end
end

(* -------------------------------------------------------------------- *)
module Parray = struct
  type 'a t = 'a array

  include Array

  let empty = [||]

  let of_array = Array.copy

  let fmap (f : 'a -> 'b) (xs : 'a list) =
    Array.map f (of_list xs)

  let split a =
    (Array.init (Array.length a) (fun i -> fst a.(i)),
     Array.init (Array.length a) (fun i -> snd a.(i)))

  let fold_left2 f a t1 t2 =
    if Array.length t1 <> Array.length t2 then 
      raise (Invalid_argument "Parray.fold_left2");
    let aux i a t1 t2 = 
      if i < Array.length t1 then f a t1.(i) t2.(i) 
      else a in
    aux 0 a t1 t2

  let iter2 (f : 'a -> 'b -> unit) a1 a2 =
    for i = 0 to (min (length a1) (length a2)) - 1 do
      f a1.(i) a2.(i)
    done

  let exists f t =
    let rec aux i t = 
      if i < Array.length t then f t.(i) || aux (i+1) t 
      else false in
    aux 0 t 

  let for_all f t = 
    let rec aux i t =
      if i < Array.length t then f t.(i) && aux (i+1) t 
      else true in
    aux 0 t 
end

(* -------------------------------------------------------------------- *)
module String = struct
  include String

  let startswith ptn subject =
    let rec doit i =
      if   i = String.length ptn
      then true
      else ptn.[i] = subject.[i] && doit (i+1)
    in
      if   String.length ptn > String.length subject
      then false
      else doit 0

  let endswith ptn subject =
    let rec doit off i =
      if   i = String.length ptn
      then true
      else ptn.[i] = subject.[i+off] && doit off (i+1)
    in
      if   String.length ptn > String.length subject
      then false
      else doit (String.length subject - String.length ptn) 0

  let slice ?first ?last (s : string) =
    let first = odfl 0 first in
    let last  = odfl (String.length s) last in
      String.sub s first (last - first)

  let split (c : char) (s : string) =
    let rec split s acc =
      match try_nf (fun () -> rindex s c) with
      | None   -> if (s = "") then acc else (s :: acc)
      | Some i ->
          split
            (slice ~first:0 ~last:i s)
            ((slice ~first:(i+1) s) :: acc)
    in
      split s []
end

(* -------------------------------------------------------------------- *)
module Stream = struct
  include Stream

  let next_opt (stream : 'a Stream.t) =
    try  Some (Stream.next stream)
    with Stream.Failure -> None
end

(* -------------------------------------------------------------------- *)
module Os = struct
  let listdir (dir : string) =
    let rec doit db acc =
      match (try Some (Unix.readdir db) with End_of_file -> None) with
      | None      -> List.rev acc
      | Some name -> doit db (name :: acc)
    in

    let db = Unix.opendir dir in

      try
        let files = doit db [] in Unix.closedir db; files
      with e ->
        (try Unix.closedir db with Unix.Unix_error _ -> ());
        raise e
end
