import CLM.encode_term


open IFOL
open encodable
open fin

def fts{σ :Signature}{n:Nat}(ts :Fin n → Term σ) : List (Term σ) := List.ofFn ts --ts_to_list


def fts_inv{σ :Signature}{n:Nat}(ls :List (Term σ)) : Option (Fin n → (Term σ)) := if h : n = ls.length then some (fun id=> by rw[h] at id; exact ls.get id) else none
-- def fts_inv{σ :Signature}{n:Nat}(ls :List (Term σ)){h:n=ls.length} : Fin n → Term σ := fun id=> by rw[h] at id; exact ls.get id

#check cast
#check Fin.cast_eq_cast



instance {σ :Signature}{n:Nat} : Encodable (Fin n → Term σ) := by
  apply Encodable.ofLeftInjection fts fts_inv
  intro h
  unfold fts_inv
  unfold fts
  have h2: (List.ofFn h).length = n := by rw[List.length_ofFn]
  let h4 := Fin.cast_eq_cast h2
  simp [h2]
  funext id
  simp [h4]



