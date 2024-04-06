import CLM.IFOL
import CLM.encode_term
open IFOL

def ent {σ : Signature}: (Term σ) → ℕ := fun term=> match term with
| Term.free n=> 2*n
| Term.const n => 2*n + 1

def det {σ : Signature}: ℕ → Term σ := fun n=>
  if Even n  then Term.free (n/2)
             else Term.const (n/2)


def de_bij {σ : Signature} : ∀ t : Term σ, det (ent t) = t := by
  intro t
  cases t with
  | free n => simp [ent, det]
  | const n => simp [ent, det]
               have h: Odd (2 * n + 1) := by simp
               simp [Nat.odd_iff_not_even.mp h]
               rw [Nat.add_div]
               simp
               simp



def ed_bij (σ : Signature) : ∀ n : ℕ, ent (@det σ n) = n := by
  intro n
  by_cases h: Even n
  simp [ent, det, h]
  rw [mul_comm]
  apply Nat.div_two_mul_two_of_even h
  simp [ent, det, h]
  have h:=Nat.odd_iff_not_even.mpr h
  rw [mul_comm,add_comm]
  exact Nat.one_add_div_two_mul_two_of_odd h
