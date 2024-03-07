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

lemma cond_mono_proof {Γ :Set (Formula σ)}{r: Formula σ}(h: Γ ⊢ r): ∀ Q: Set (Formula σ), (Q ∪ Γ) ⊢ r :=by
intro Q
induction h with
| ref ha =>apply Proof.ref;apply subss ha;simp
| introI A B h2 _ h3=>
  apply Proof.introI
  rw [Set.union_assoc]
  exact h3
| elimI A B Δ h1 _ _ h3 h4=>
  have h:= Proof.elimI _ _ _ _ h3 h4
  rw [Set.union_assoc,← Set.union_assoc Δ Q h1,Set.union_comm Δ Q,Set.union_assoc,← Set.union_assoc,Set.union_self] at h
  exact h
| introA A B f g _ _ h3 h4=>
  have h:= Proof.introA _ _ _ _  h3 h4
  rw [Set.union_assoc,Set.union_comm A _,Set.union_assoc,← Set.union_assoc,Set.union_self,Set.union_comm B A] at h
  exact h
| elimA1 A B Δ _ g=>
  apply Proof.elimA1 _ _ _ g
| elimA2 A B Δ _ g=>
  apply Proof.elimA2 _ _ _ g
| introO1 A B f _ h1=>
  apply Proof.introO1 _ _ _ h1
| introO2 A B f _ h1=>
  apply Proof.introO2 _ _ _ h1
| elimO A B Δ f g h1 _ _ _ h5 h6 h7=>
  rw [←  Set.union_assoc] at h6
  rw [←  Set.union_assoc] at h7
  have h:= Proof.elimO A B Δ _ _ _ h5 h6 h7
  have zq:Q ∪ f ∪ (Q ∪ g) ∪ (Q ∪ h1)=Q ∪ (f ∪ g ∪ h1):=by
    rw[Set.union_assoc,Set.union_assoc,Set.union_assoc,← Set.union_assoc g Q _,Set.union_comm g Q]
    rw[Set.union_assoc Q g h1,← Set.union_assoc Q Q _,Set.union_self]
    rw[← Set.union_assoc Q f _,Set.union_comm Q f,Set.union_assoc f Q _,← Set.union_assoc Q Q _,Set.union_self]
    rw[← Set.union_assoc,Set.union_comm f Q,Set.union_assoc Q f _,Set.union_assoc]
  rw [zq] at h
  exact h
| introN A h1 P S _ _ h4 h5=>
  rw [←  Set.union_assoc] at h4
  rw [←  Set.union_assoc] at h5
  have hz:= Proof.introN _ _ _ _ h4 h5
  rw [Set.union_assoc,← Set.union_assoc P Q S,Set.union_comm P _, ← Set.union_assoc, ← Set.union_assoc,Set.union_self] at hz
  rw [Set.union_assoc] at hz
  exact hz
| ine A h1 P _ _ h3 h4 =>
  apply Proof.ine _ _ _ h3 h4
| introF A h1 P S h2 _ =>
  have Z:= Proof.introF _ _ _ S h2
  by_cases Q = ∅
  rw [h]
  rw [Set.union_comm ,Set.union_empty]
  exact Z
  have h: Q ≠ ∅ := by simp [h]
  have h:=Set.nonempty_iff_ne_empty.mpr h
  have h:=Set.nonempty_def.mp h
  cases h
  rename_i f hf
  have t:= Proof.ref hf
  have tt:= Proof.introA _ _ _ _ t Z
  exact Proof.elimA2 _ _ _ tt
| elimF A h1 P _ h2 =>
  apply Proof.elimF _ _ _ h2
| introE A h1 P S _ h3 =>
  apply Proof.introE _ _ _ _ h3
| elimE A h1 P S _ h3 h4 h5 h6 h7 =>
  rename_i τ
  rw [←  Set.union_assoc] at h7
  have z:= Proof.elimE A h1 (Q ∪ P) (Q ∪ S) τ h3  h6 h7
  rw [Set.union_assoc,← Set.union_assoc P Q S,Set.union_comm P _, ← Set.union_assoc, ← Set.union_assoc,Set.union_self] at z
  rw [Set.union_assoc] at z
  exact z

lemma cond_mono_proof2 {Γ :Set (Formula σ)}{r: Formula σ}(h: Γ ⊢ r): ∀ Q: Set (Formula σ), (Γ ∪ Q) ⊢ r :=by
intro Q
rw [Set.union_comm]
apply cond_mono_proof
assumption





lemma Finset_proof {Γ :Set (Formula σ)}{r: Formula σ}(h: Γ ⊢ r):∃ (Γ':Set (Formula σ)),(Γ' ⊆ Γ) ∧ (Γ' ⊢ r) ∧ (Γ'.Finite):=by
induction h with
| ref ha =>rename_i f Q;use {f};simp;constructor;trivial;constructor;simp
| introI A B h2 _ h3=>
  rcases h3 with ⟨Γ',h0,h1,h4⟩
  use Γ'\{A}
  constructor;
  rw [Set.diff_subset_iff]
  have utran: (h2 ∪ {A})=({A} ∪ h2) := by simp
  rw [utran] at h0
  exact h0
  constructor;
  apply Proof.introI
  rw [Set.diff_union_self]
  apply cond_mono_proof2
  exact h1
  apply Set.Finite.diff
  assumption
| elimI A B Δ h1 _ _ h3 h4=>
  rcases h3 with ⟨Γ',h11,h12,h13⟩
  rcases h4 with ⟨Γ'',h5,h6,h7⟩
  use Γ' ∪ Γ''
  constructor;
  rw [Set.union_subset_iff]
  constructor; exact subset_union_of_subset_left h11 h1; exact subset_union_of_subset_right h5 Δ
  constructor;
  apply Proof.elimI _ _ _ _ h12 h6
  apply Set.Finite.union
  assumption
  assumption
| introA A B f g _ _ h3 h4=>
  rcases h3 with ⟨Γ',h11,h12,h13⟩
  rcases h4 with ⟨Γ'',h5,h6,h7⟩
  use Γ' ∪ Γ''
  constructor;
  rw [Set.union_subset_iff]
  constructor; exact subset_union_of_subset_left h11 B; exact subset_union_of_subset_right h5 A
  constructor;
  apply Proof.introA _ _ _ _ h12 h6
  apply Set.Finite.union
  assumption
  assumption
| elimA1 A B Δ _ g=>
  rcases g with ⟨Γ',h1,h2,h3⟩
  use Γ'
  constructor;
  assumption
  constructor;
  apply Proof.elimA1 _ _ _ h2
  assumption
| elimA2 A B Δ _ g=>
  rcases g with ⟨Γ',h1,h2,h3⟩
  use Γ'
  constructor;
  assumption
  constructor;
  apply Proof.elimA2 _ _ _ h2
  assumption
| introO1 A B f _ h1=>
  rcases h1 with ⟨Γ',h2,h3,h4⟩
  use Γ'
  constructor;
  assumption
  constructor;
  apply Proof.introO1 _ _ _ h3
  assumption
| introO2 A B f _ h1=>
  rcases h1 with ⟨Γ',h2,h3,h4⟩
  use Γ'
  constructor;
  assumption
  constructor;
  apply Proof.introO2 _ _ _ h3
  assumption
| elimO A B Δ f g h1 _ _ _ h5 h6 h7=>
  rcases h6 with ⟨Γ',h61,h62,h63⟩
  rcases h7 with ⟨Γ'',h71,h72,h73⟩
  rcases h5 with ⟨Γ''',h51,h52,h53⟩
  use (((Γ'\{A}) ∪ (Γ''\ {B}) ∪ Γ''') )
  constructor;
  rw [Set.union_subset_iff]
  constructor
  rw [Set.union_subset_iff]
  constructor; apply subset_union_of_subset_right;
  apply diff_subset_iff.mpr; rw [Set.union_comm]; exact h61
  apply subset_union_of_subset_left; apply subset_union_of_subset_right; apply diff_subset_iff.mpr; rw [Set.union_comm]; exact h71
  apply subset_union_of_subset_left; apply subset_union_of_subset_left; exact h51
  constructor;
  rw [Set.union_comm,Set.union_comm (Γ' \ {A}) _ ,← Set.union_assoc]
  apply Proof.elimO
  exact h52
  rw [Set.diff_union_self]
  apply cond_mono_proof2
  exact h62
  rw [Set.diff_union_self]
  apply cond_mono_proof2
  exact h72
  apply Finite.union
  apply Finite.union
  apply Finite.diff
  assumption
  apply Finite.diff
  assumption
  assumption
| introN A h1 P S _ _ h4 h5=>
  rcases h4 with ⟨Γ',h41,h42,h43⟩
  rcases h5 with ⟨Γ'',h51,h52,h53⟩
  use ((Γ' \ {A}) ∪ (Γ'' \ {A}))
  constructor;
  rw [Set.union_subset_iff]
  constructor; apply subset_union_of_subset_left; apply diff_subset_iff.mpr;rw [Set.union_comm]; exact h41;
  apply subset_union_of_subset_right; apply diff_subset_iff.mpr;rw [Set.union_comm]; exact h51
  constructor;
  apply Proof.introN
  rw [Set.diff_union_self]
  apply cond_mono_proof2 h42
  rw [Set.diff_union_self]
  apply cond_mono_proof2 h52
  apply Finite.union
  apply Finite.diff
  assumption
  apply Finite.diff
  assumption
| ine A h1 P _ _ h3 h4 =>
  rcases h4 with ⟨Γ',h41,h42,h43⟩
  rcases h3 with ⟨Γ'',h51,h52,h53⟩
  use Γ' ∪ Γ''
  constructor;
  rw [Set.union_subset_iff]
  constructor; assumption; assumption
  constructor;
  rw [Set.union_comm]
  have h42:= cond_mono_proof2 h42 Γ''
  rw [Set.union_comm] at h42
  have h52:= cond_mono_proof2 h52 Γ'
  exact Proof.ine _ h1 _ h52 h42
  apply Finite.union
  assumption
  assumption
| introF A h1 P _ h2 h3 =>
  rcases h3 with ⟨Γ',h31,h32,h33⟩
  use Γ'
  constructor;
  assumption
  constructor;
  apply Proof.introF
  assumption
  intro t
  unfold free_variables at h2
  apply h2
  unfold free_variables at t
  apply Set.mem_iUnion.mpr
  have tt:= Set.mem_iUnion.mp t
  rcases tt with ⟨f,hf⟩
  simp at hf
  use f
  simp
  constructor
  apply Set.mem_of_subset_of_mem h31
  exact hf.left
  exact hf.right
  assumption
| elimF A S P _ h2 =>
  rcases h2 with ⟨Γ',h31,h32,h33⟩
  use Γ'
  constructor;
  assumption
  constructor;
  apply Proof.elimF
  assumption
  assumption
| introE A h1 P S _ h3=>
  rcases h3 with ⟨Γ',h31,h32,h33⟩
  use Γ'
  constructor;
  assumption
  constructor;
  apply Proof.introE
  assumption
  assumption
| elimE A h1 P S h2 h3 h4 h5 h6 h7 =>
  rename_i τ
  rcases h7 with ⟨Γ',h71,h72,h73⟩
  rcases h6 with ⟨Γ'',h61,h62,h63⟩
  generalize eq : IFOL.Formula.Substitution A (Term.free h3) τ = z
  rw [eq] at h5
  rw [eq] at h71
  use (Γ'\{z}) ∪ Γ''
  constructor;
  rw [Set.union_subset_iff]
  constructor; apply subset_union_of_subset_right; apply diff_subset_iff.mpr;rw [Set.union_comm]; exact h71;
  apply subset_union_of_subset_left; assumption
  constructor;
  rw [Set.union_comm]
  apply Proof.elimE
  exact τ
  exact h62
  rw [eq]
  rw [Set.diff_union_self]
  apply cond_mono_proof2 h72
  apply Finite.union
  apply Finite.diff
  assumption
  assumption



def primen_sub_prf {Γ :Set (Formula σ)}{p r: Formula σ} :
  (prime Γ r ⊢ p) → ∃ n, primen Γ r n ⊢ p := by
  intro h
  have h:= Finset_proof h
  rcases h with ⟨Γ',h1,h2,h3⟩
  unfold prime at h1
  have dq:∃ (I : Set ℕ), Set.Finite I ∧ Γ' ⊆ ⋃ i ∈ I, primen Γ r i := by
    apply Set.finite_subset_iUnion
    assumption
    exact h1

  rcases dq with ⟨I,h4,h5⟩
  by_cases I = ∅
  simp [h] at h5
  have h5:Γ' = ∅ := by apply Set.subset_eq_empty h5;rfl
  simp [h5] at h2
  use 0
  have h6:= cond_mono_proof h2 (primen Γ r 0)
  simp
  simp at h6
  exact h6
  have h7: I ≠ ∅ := by simp [h]
  have dp:=Set.Finite.exists_maximal_wrt (λ x=>x) I h4 (Set.nonempty_iff_ne_empty.mpr h7)
  simp at dp
  rcases dp with ⟨n,_,hn2⟩
  use n
  suffices hz:Γ' ⊆ primen Γ r n
  have hz2: (primen Γ r n ∪ Γ') ⊢ p := cond_mono_proof h2 _
  rw [Set.union_eq_self_of_subset_right] at hz2
  exact hz2
  exact hz
  apply subset_trans h5
  simp
  intro i hi
  suffices hq:i<= n
  exact primen_mono hq
  by_cases i ≤ n
  assumption
  have ht: n<=i:= by linarith
  have hq:= hn2 i hi ht
  linarith


lemma insert_subset1{σ : Signature}(S:Set (Formula σ) )(r: Formula σ )(nn:Nat) :S ⊆ insertn S r nn:= by
  induction nn
  simp
  rfl
  simp
  rename_i n nh
  cases (@Encodable.decode (Formula σ) _ n)
  simp
  assumption
  rename_i val
  simp
  cases val
  <;>simp<;> try assumption
  rename_i f1 f2
  by_cases insertn S r n⊢f1∨ᵢf2
  simp[h]
  by_cases insert f1 (insertn S r n)⊢r
  simp [h]
  apply subset_trans nh
  apply Set.subset_insert
  by_cases insert f1 (insertn S r n)⊢r
  simp [h]
  apply subset_trans nh
  apply Set.subset_insert
  simp [h]
  apply subset_trans nh
  apply Set.subset_insert
  simp [h]
  assumption

lemma prime_prf_disj_self {Γ : Set (Formula σ)} {p: Formula σ}(h:prime Γ r ⊢ p ∨ᵢ p) :
  ∃ n, p ∈ (insertn (primen Γ r n) r ((@Encodable.encode (Formula σ) _ (p ∨ᵢ p))+1)) :=by
  generalize eq : (@Encodable.encode (Formula σ) _ (p ∨ᵢ p)) = nn
  rcases primen_sub_prf h with ⟨n,ch⟩
  use n
  unfold insertn
  unfold insert_code
  simp
  rw [← eq]
  rw [Encodable.encodek  (p ∨ᵢ p)]
  rw [eq]
  simp
  suffices hc:insertn (primen Γ r n) r nn⊢p∨ᵢp
  simp [hc]
  have tz:= insert_subset1 (primen Γ r n) r nn
  have tt:= cond_mono_proof2 ch (insertn (primen Γ r n) r nn)
  rw [Set.union_eq_self_of_subset_left] at tt
  exact tt
  exact tz

def prime_consq_iff_mem  {Γ :Set (Formula σ)}{p r: Formula σ} :
  (p ∈ prime Γ r) ↔ (prime Γ r ⊢ p):= by
  constructor
  intro h
  exact Proof.ref h
  intro h
  have h:= primen_sub_prf h
  rcases h with ⟨_,_⟩
  simp
  have hz:=Proof.introO1 _ p _ h
  have hzz:= prime_prf_disj_self hz
  rcases hzz with ⟨i,hi⟩
  generalize eq : (@Encodable.encode (Formula σ) _ (p∨ᵢp)) = nn
  rw [eq] at hi
  have z:= @insertn_sub_primen σ Γ r i (nn+1)
  use i+1
  exact z hi

def primen_not_prfn {Γ :  set form} {r : form} {n} :
  (primen Γ r n ⊢ᵢ r) → (Γ ⊢ᵢ r) :=
















  -- repeat (first |  apply Proof.introI | apply Proof.elimI| apply Proof.introA | apply Proof.elimA1 | apply Proof.elimA2 | apply Proof.introO1| apply Proof.introO2 | apply Proof.elimO | apply Proof.introN| apply Proof.ine| apply Proof.introF| apply Proof.elimF| apply Proof.introE| apply Proof.elimE )
