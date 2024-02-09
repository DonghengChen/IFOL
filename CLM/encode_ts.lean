import CLM.encode_term
open IFOL
open encodable
open fin

def fts{σ :Signature}{n:Nat}(ts :Fin n → Term σ) : List (Term σ) := List.ofFn ts --ts_to_list

def fts_inv{σ :Signature}{n:Nat}(ls :List (Term σ)) : Option (Fin n → (Term σ)) := if h : n = ls.length then some (fun id=> by rw[h] at id; exact ls.get id) else none

instance {σ :Signature}{n:Nat} : Encodable (Fin n → Term σ) := by
  apply Encodable.ofLeftInjection fts fts_inv
  simp[fts_inv,fts,List.length_ofFn,Fin.cast_eq_cast]
