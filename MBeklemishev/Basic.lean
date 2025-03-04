def slice (list : List α) (i j : Nat) : List α :=
  (list.drop i).take (j - i)

mutual
  def pSet (seq : List Nat) (n : Nat) : List Nat :=
    match n with
    | 0 => []
    | n' + 1 =>
      match p seq n' with
      | none => []
      | some ppn => (List.range ppn).filter (fun i => seq.drop i < seq.drop ppn)

  def p (seq : List Nat) (n : Nat) : Option Nat :=
    if n = 0
    then some (seq.length - 1)
    else (pSet seq n).max?
end

def u (seq : List Nat) (x n : Nat) : Nat :=
  let filterd := (pSet seq n).filter (fun i => x < i)
  filterd.min?.getD (seq.length - 1)

def fp (seq : List Nat) (x n : Nat) : Nat :=
  match n with
  | 0 => x
  | n' + 1 => fp seq (u seq x n) n'

def innerLoop (seq pList : List Nat) (p_m limit k : Nat) : Option Nat :=
  let n := limit - k
  match k with
  | 0 => none
  | k' + 1 =>
    if slice seq p_m (u seq p_m n) < slice seq (pList.get! n) (pList.get! (n - 1))
    then some (fp seq p_m n)
    else innerLoop seq pList p_m limit k'

def tp (seq pList : List Nat) (level k : Nat) : Option Nat :=
  let m := level - k
  match level with
  | 0 => some (seq.length - 2)
  | level' + 1 =>
    match p seq m with
    | none => none
    | some p_m =>
        if seq.get! p_m < seq.getLast! - 1
        then some p_m
        else let limit := min level' m
          match innerLoop seq pList p_m limit (limit - 1) with
          | some rev => some rev
          | none =>
            match k with
            | 0 => some (fp seq p_m level')
            | k' + 1 => tp seq (pList ++ [p_m]) level k'

def expand (seq : List Nat) (level n : Nat) : List Nat :=
  let p_0 := seq.length - 1
  match seq.getLast? with
  | none => []
  | some 0 => seq.take p_0
  | some (seqlast' + 1) =>
    match tp seq [p_0] level (level - 1) with
    | none =>
      let bp := seq.take p_0 ++ [seqlast']
      (List.replicate n bp).flatten
    | some parent =>
      let gp := seq.take (parent + 1)
      let bp := slice seq (parent + 1) p_0 ++ [seqlast']
      gp ++ (List.replicate n bp).flatten

#eval expand [1,0,1,0,0,0,0,1,0,1] 3 4 -- [1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0]
