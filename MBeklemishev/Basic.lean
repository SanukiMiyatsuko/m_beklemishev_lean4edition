def slice (i j : Nat) (list : List A) : List A :=
  (list.drop i).take (j - i)

mutual
  def p' (n : Nat) (seq : List Nat) : Option Nat :=
    match n with
    | 0 => some (seq.length - 1)
    | n' + 1 => (pSet' n' seq).max?

  def pSet' (n : Nat) (seq : List Nat) : List Nat :=
    match n with
    | 0 => [seq.length - 1]
    | n' + 1 =>
      match p' n' seq with
      | none => []
      | some ppn => (List.range ppn).filter (fun i => seq.drop i < seq.drop ppn)
end

def p (n : Nat) (seq : List Nat) : Option Nat :=
  p' (n + n) seq

def pSet (n : Nat) (seq : List Nat) : List Nat :=
  pSet' ((n + n) -1) seq

#eval pSet 1 [1,0,0,1,0,0,0,0,1,0,0,1] -- [1, 2, 4, 5, 6, 7, 9, 10]
#eval p 1 [1,0,0,1,0,0,0,0,1,0,0,1]    -- some 10
#eval pSet 2 [1,0,0,1,0,0,0,0,1,0,0,1] -- [1, 4, 5, 6, 9]
#eval p 2 [1,0,0,1,0,0,0,0,1,0,0,1]    -- some 9
#eval pSet 3 [1,0,0,1,0,0,0,0,1,0,0,1] -- [4, 5]
#eval p 3 [1,0,0,1,0,0,0,0,1,0,0,1]    -- some 5
#eval pSet 4 [1,0,0,1,0,0,0,0,1,0,0,1] -- [4]
#eval p 4 [1,0,0,1,0,0,0,0,1,0,0,1]    -- some 4
#eval pSet 5 [1,0,0,1,0,0,0,0,1,0,0,1] -- []
#eval p 5 [1,0,0,1,0,0,0,0,1,0,0,1]    -- none

def u (x n : Nat) (seq : List Nat) : Nat :=
  let filtered := (pSet n seq).filter (fun i => x < i)
  match filtered.min? with
  | none => seq.length - 1
  | some minif => minif

def fp (x n : Nat) (seq : List Nat) : Nat :=
  match n with
  | 0 => x
  | n' + 1 => fp (u x n seq) n' seq

#eval fp 9 1 [1,0,0,1,0,0,0,0,1,0,0,1] -- 10
#eval fp 5 1 [1,0,0,1,0,0,0,0,1,0,0,1] -- 6
#eval fp 5 2 [1,0,0,1,0,0,0,0,1,0,0,1] -- 7
#eval fp 4 1 [1,0,0,1,0,0,0,0,1,0,0,1] -- 5
#eval fp 4 2 [1,0,0,1,0,0,0,0,1,0,0,1] -- 6
#eval fp 4 3 [1,0,0,1,0,0,0,0,1,0,0,1] -- 7

def innerLoop (seq pList : List Nat) (p_m limit k : Nat) : Option Nat :=
  match k with
  | 0 => none
  | k' + 1 =>
    let n := limit - k
    match pList.get? n, pList.get? (n - 1) with
    | some pListn, some pListPredn =>
      if slice p_m (u p_m n seq) seq < slice pListn pListPredn seq
      then some (fp p_m n seq)
      else innerLoop seq pList p_m limit k'
    | _, _ => none

#eval innerLoop [1,0,0,1,0,0,0,0,1,0,0,1] [11,10] 9 2 1
#eval innerLoop [1,0,0,1,0,0,0,0,1,0,0,1] [11,10] 9 2 0
#eval innerLoop [1,0,0,1,0,0,0,0,1,0,0,1] [11,10,9] 5 2 1

def tp (seq pList : List Nat) (level k : Nat) : Option Nat :=
  match level with
  | 0 => some (seq.length - 2)
  | level' + 1 =>
    let m := level - k
    match p m seq with
    | none => none
    | some p_m =>
      match seq.get? p_m, seq.getLast? with
      | some seqp_m, some seqEnd =>
        if seqp_m < seqEnd - 1
        then some p_m
        else let limit := min level' m
          match innerLoop seq pList p_m limit (limit - 1) with
          | some rev => some rev
          | none =>
            match k with
            | 0 => some (fp p_m level' seq)
            | k' + 1 => tp seq (pList ++ [p_m]) level k'
      | _, _ => none

#eval tp [1,0,0,1,0,0,0,0,1,0,0,1] [11] 3 2
#eval innerLoop [1,0,0,1,0,0,0,0,1,0,0,1] [11] 10 1 0
#eval tp [1,0,0,1,0,0,0,0,1,0,0,1] [11,10] 3 1
#eval innerLoop [1,0,0,1,0,0,0,0,1,0,0,1] [11,10] 9 2 1
#eval tp [1,0,0,1,0,0,0,0,1,0,0,1] [11,10,9] 3 0
#eval innerLoop [1,0,0,1,0,0,0,0,1,0,0,1] [11,10,9] 5 2 1

def expand (seq : List Nat) (level n : Nat) : List Nat :=
  match seq.getLast? with
  | none => []
  | some seqEnd =>
    let initseq := seq.take (seq.length - 1)
    match seqEnd with
    | 0 => initseq
    | seqEnd + 1 =>
      match tp seq [seq.length - 1] level (level - 1) with
      | none => (List.replicate n initseq).flatten
      | some parent =>
        let (good, bad') := List.splitAt (parent + 1) initseq
        let bad :=  bad' ++ [seqEnd]
        good ++ (List.replicate n bad).flatten

#eval expand [1,0,1,0,0,0,0,1,0,1] 3 4
