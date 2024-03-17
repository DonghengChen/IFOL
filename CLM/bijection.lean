import CLM.IFOL
import CLM.encode_term
open IFOL

def ent {σ : Signature}: (Term σ) → ℕ := fun term=> match term with
| Term.free n=> 2*n
| Term.const n => 2*n + 1

def det {σ : Signature}: ℕ → Term σ := fun n=>
  if n%2=0  then Term.free (n/2)
             else Term.const ((n-1)/2)


lemma odd_false : (2 * n + 1) % 2 = 0 → False := by
               intro x
               induction n
               simp at x
               rename_i i j
               have h: 2 * Nat.succ i + 1 = 2 * i + 1 + 2 := by linarith
               rw [h] at x
               rw [Nat.mod_eq_sub_mod] at x
               simp at x
               exact j x
               linarith



def de_bij {σ : Signature} : ∀ t : Term σ, det (ent t) = t := by
  intro t
  cases t with
  | free n => simp [ent, det]
  | const n => simp [ent, det]
               intro x
               apply odd_false x

def ed_bij (σ : Signature) : ∀ n : ℕ, ent (@det σ n) = n := by
  intro n
  by_cases h: n%2=0
  simp [ent, det, h]
  nth_rw 2 [← Nat.div_add_mod n 2]
  simp [h]
  simp [ent, det,h]
  simp at h
  have hc:= @Odd.mod_even_iff n 2 even_two
  rw [h] at hc
  have z:(Even (n-1)):= by apply @Nat.Odd.sub_odd n 1 ;simp at hc;simp;exact hc;simp
  have zc:=Nat.div_two_mul_two_of_even z
  rw [mul_comm]
  rw [zc]
  cases n
  simp at h
  simp


