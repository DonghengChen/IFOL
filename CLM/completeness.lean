import CLM.IFOL
import CLM.encode_formula

open IFOL
open Set
open Classical


def is_closed (Γ : Set (Formula σ)):=
∀ (f : Formula σ), (Γ ⊢ f) → (f ∈ Γ)

def has_disj (Γ : Set (Formula σ)):=
∀ (f g : Formula σ),((f ∨ᵢ g) ∈ Γ) → ((f ∈ Γ) ∨ (g ∈ Γ))

def is_prime (Γ : Set (Formula σ)):=
is_closed Γ ∧ has_disj Γ

@[simp]
def insert_form (Γ : Set (Formula σ)) (p q r: Formula σ):Set (Formula σ) :=
if ((Γ∪{p})⊢ r) then Γ∪{q} else Γ∪{p}

@[simp]
def insert_code (Γ: Set (Formula σ))(r: Formula σ)(n:Nat): Set (Formula σ):=
match @Encodable.decode (Formula σ) _ n with
| some f=> match f with
  | f1 ∨ᵢ f2 => if Γ ⊢ f1 ∨ᵢ f2 then insert_form Γ f1 f2 r else Γ
  | _ => Γ
| none =>Γ

@[simp]
def insertn (Γ: Set (Formula σ))(r: Formula σ):Nat → Set (Formula σ)
| 0 => Γ
| n+1 => insert_code (insertn Γ r n) r n

@[simp]
def primen (Γ :Set (Formula σ))(r: Formula σ):Nat → Set (Formula σ)
| 0 => Γ
| n+1 => ⋃ i, insertn (primen Γ r n) r i

@[simp]
def prime (Γ :Set (Formula σ))(r: Formula σ): Set (Formula σ):=
⋃ n, primen Γ r n

lemma subss {α: Type}{a:α}{A B: Set α}(h1: a ∈ A)(h2: A ⊆ B): a ∈ B := by
apply h2
assumption

lemma subset_insert_code {Γ :Set (Formula σ)}{r: Formula σ}(n) :  Γ ⊆ insert_code Γ r n :=by
 intro v hv
 simp
 cases (@Encodable.decode (Formula σ) instEncodableFormula n : Option (Formula σ) )
 assumption
 rename_i val
 simp[*]
 cases val
 · simp;assumption
 · simp;assumption
 · rename_i f1 f2
   simp
   apply subss hv
   by_cases Γ⊢f1∨ᵢf2
   simp[h]
   by_cases insert f1 Γ⊢r
   simp [h]
   simp [h]
   simp [h]
   rfl
 · simp;assumption
 · simp;assumption
 · simp;assumption
 · simp;assumption
 · simp;assumption


lemma primen_subset_prime {Γ :Set (Formula σ)}{r: Formula σ}(n) :primen Γ r n ⊆ prime Γ r :=by
simp
exact subset_iUnion (primen Γ r) n



lemma subset_insertn {Γ :Set (Formula σ)}{r: Formula σ} (n) : Γ ⊆ insertn Γ r n :=by
induction n
· simp;rfl
· simp
  rename_i n nh
  cases (@Encodable.decode (Formula σ) instEncodableFormula n : Option (Formula σ))
  simp;assumption
  rename_i val
  cases val
  · simp;assumption
  · simp;assumption
  · rename_i f1 f2
    simp
    by_cases insertn Γ r n⊢f1∨ᵢf2
    simp[h]
    by_cases insert f1 (insertn Γ r n)⊢r
    simp [h]
    intro f hf
    apply Set.mem_insert_of_mem
    apply nh
    assumption
    simp [h]
    intro f hf
    apply Set.mem_insert_of_mem
    apply nh
    assumption
    simp [h]
    assumption
  · simp;assumption
  · simp;assumption
  · simp;assumption
  · simp;assumption
  · simp;assumption

lemma subset_prime_self{Γ :Set (Formula σ)}{r: Formula σ} : Γ ⊆ prime Γ r :=
primen_subset_prime 0


lemma insertn_sub_primen {Γ :Set (Formula σ)}{r: Formula σ} {n m : Nat} :
  insertn (primen Γ r n) r m ⊆ primen Γ r (n+1) := subset_iUnion _ _

lemma insertn_to_prime {Γ :Set (Formula σ)}{r: Formula σ} {n m : Nat} :
  insertn (primen Γ r n) r m ⊆ prime Γ r :=by
  induction m
  apply primen_subset_prime
  exact subset_trans insertn_sub_primen (primen_subset_prime _)

lemma in_prime_in_primen {Γ :Set (Formula σ)}{p r: Formula σ} :
 (p ∈ prime Γ r ) → ∃ n, p ∈ primen Γ r n :=
mem_iUnion.1

lemma in_primen_in_insertn  {Γ :Set (Formula σ)}{p r: Formula σ} {n} :
  (p ∈ primen Γ r (n+1) ) → ∃ i, p ∈ insertn (primen Γ r n) r i :=
mem_iUnion.1

lemma primen_subset_succ {Γ :Set (Formula σ)}{r: Formula σ} {n} :
  primen Γ r n ⊆ primen Γ r (n+1) := by
   apply subset_trans
   apply subset_insertn
   assumption'
   exact subset_iUnion _ _

lemma primen_mono {Γ :Set (Formula σ)}{r: Formula σ} {n m : Nat}(h : n ≤ m) :
  primen Γ r n ⊆ primen Γ r m :=by
  induction h
  rfl
  rename_i h_ih
  apply subset_trans h_ih primen_subset_succ

lemma insertn_mono {Γ :Set (Formula σ)}{r: Formula σ} {n m : Nat}(h : n ≤ m) :
  insertn Γ r n ⊆ insertn Γ r m :=by
  induction h
  rfl
  rename_i h_ih
  exact subset_trans h_ih (subset_insert_code _)

-- def prime_consq_iff_mem  {Γ :Set (Formula σ)}{p r: Formula σ} :
-- (p ∈ prime Γ r) ↔ (prime Γ r ⊢ p)   := by
-- constructor
-- intro h
-- apply Proof.ref h
-- intro h
-- unfold prime at h
-- by_contra hn
-- simp at hn



def primen_sub_prf {Γ :Set (Formula σ)}{p r: Formula σ} :
  (prime Γ r ⊢ p) → ∃ n, primen Γ r n ⊢ p := by
  generalize eq : prime Γ r = Γ'
  intro h
  induction h
  subst eq

  · rename_i A h_h
    rcases (in_prime_in_primen h_h) with ⟨n,hpq⟩
    use n
    exact Proof.ref hpq
  · rename_i A B Δ h1 h2
    have l1:= Proof.introI _ _ _ h1
    rw [← eq] at l1
    




  -- repeat (first |  apply Proof.introI | apply Proof.elimI| apply Proof.introA | apply Proof.elimA1 | apply Proof.elimA2 | apply Proof.introO1| apply Proof.introO2 | apply Proof.elimO | apply Proof.introN| apply Proof.ine| apply Proof.introF| apply Proof.elimF| apply Proof.introE| apply Proof.elimE )
