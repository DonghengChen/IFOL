import CLM.IFOL
import CLM.encode_formula

open IFOL
open Set
open Classical


def is_closed (Γ : Set (Formula σ)):=
∀ (f : Formula σ), (Γ ⊢ f) → (f ∈ Γ)

def has_disj (Γ : Set (Formula σ)):=
∀ (f g : Formula σ),((f ∨ᵢ g) ∈ Γ) → ((f ∈ Γ) ∨ (g ∈ Γ))

def has_const (Γ : Set (Formula σ)):=
∀ (f : Formula σ),((∃ᵢ f) ∈ Γ) → (∃(c:Constant),(f.Substitution (Term.free (free_variable.free_variable 0)) (Term.const c)).down 1 0 ∈ Γ)

def is_prime (Γ : Set (Formula σ)):=
is_closed Γ ∧ has_disj Γ ∧ has_const Γ

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

lemma subss {α: Type}{a:α}{A B: Set α}(h1: a ∈ A)(h2: A ⊆ B): a ∈ B := h2 h1

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
by_cases h0:Q=∅
rw [h0];simp;exact h
have h1:=Set.nonempty_iff_ne_empty.mpr h0
have h1:=Set.nonempty_def.mp h1
rcases h1 with ⟨f,hf⟩
have h2:= Proof.ref hf
have h3:= Proof.introA _ _ _ _ h2 h
rw [Set.union_comm Q Γ]
rw[Set.union_comm Γ Q]
apply Proof.elimA2 _ _ _ h3

lemma cond_mono_proof2 {Γ :Set (Formula σ)}{r: Formula σ}(h: Γ ⊢ r): ∀ Q: Set (Formula σ), (Γ ∪ Q) ⊢ r :=by
intro Q
rw [Set.union_comm]
apply cond_mono_proof
assumption

lemma subset_proof {Γ :Set (Formula σ)}{r: Formula σ}(h: Γ ⊢ r)(h2: Γ ⊆ Γ'): (Γ' ⊢ r) :=by
have z:= cond_mono_proof h Γ'
rw [Set.union_eq_self_of_subset_right] at z
exact z
assumption

lemma v_insert_code {σ : Signature}(Γ: Set (Formula σ))(p q f r: Formula σ)(eq: f =(p∨ᵢq)){n:ℕ}(hn: Γ ⊢ f)(h:n=@Encodable.encode (Formula σ) _ f):  ((insert_code Γ r n) ⊢ p) ∨ ((insert_code Γ r n) ⊢ q) :=by
simp
have hi: @Encodable.decode (Formula σ) _ n = f :=by  rw [h];rw [Encodable.encodek f]
rw [hi,eq]
simp
rw [eq] at hn
simp [hn]
by_cases h2:insert p Γ⊢r
simp[h2]
right;apply Proof.ref;simp
simp[h2]
left;apply Proof.ref;simp

lemma v_insertn {σ : Signature}(Γ: Set (Formula σ))(p q f r: Formula σ)(eq: f =(p∨ᵢq)){n:ℕ}(hn: Γ ⊢ f)(h:n=@Encodable.encode (Formula σ) _ f):
((insertn Γ r (n+1)) ⊢ p) ∨ ((insertn Γ r (n+1)) ⊢ q):=by
unfold insertn
have z: Nat.add n 0 = n := by simp
rw [z]
apply v_insert_code
exact eq
apply subset_proof hn
exact subset_insertn n
exact h


--primen Γ r n⊢p∨ᵢq
lemma v_prime {σ : Signature}{Γ: Set (Formula σ)}{p q r: Formula σ}{n:ℕ}(h:primen Γ r n⊢p∨ᵢq):
((primen Γ r (n+1)) ⊢ p) ∨ ((primen Γ r (n+1)) ⊢ q):=by
unfold primen
have z: Nat.add n 1 = n+1 := by simp
have z2: Nat.add n 0 = n := by simp
rw [z2]
generalize eq:(p∨ᵢq)=f
have req:=eq.symm
rw [eq] at h
let nn:=@Encodable.encode (Formula σ) _ f
have tz:nn=@Encodable.encode (Formula σ) _ f:=by dsimp
have z3:=v_insertn (primen Γ r n) p q f r req h tz
cases z3 with
| inl hl=>left; apply subset_proof hl;intro x v;simp;use nn+1;
| inr hl=>right; apply subset_proof hl;intro x v;simp;use nn+1;




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

lemma ind(n:Nat): n=0 ∨ ∃ m, n=m+1 := by
  cases n
  simp
  right
  rename_i q
  use q

lemma insertn_prf {Γ :  Set (Formula σ)} {p: Formula σ} {i:Nat} :
  (insertn Γ p i ⊢ p) → (Γ ⊢ p) :=by
  induction i
  simp
  rename_i ni nh
  simp
  cases (@Encodable.decode (Formula σ) instEncodableFormula ni : Option (Formula σ))
  simp
  assumption
  rename_i val
  simp
  cases val
  <;>simp<;> try assumption
  rename_i f1 f2
  by_cases insertn Γ p ni⊢f1∨ᵢf2
  simp[h]
  by_cases insert f1 (insertn Γ p ni)⊢p
  simp [h]
  rename_i h2
  intro hf
  generalize eq : (insertn Γ p ni) = S
  rw [eq] at h2 h hf
  apply nh
  rw [eq]
  have t1: insert f2 S = S ∪ {f2} := by simp
  have t2: insert f1 S = S ∪ {f1} := by simp
  rw [t1] at hf
  rw [t2] at h
  have rz:= Proof.elimO _ _ _ _ _ _ h2 h hf
  rw [Set.union_eq_self_of_subset_right] at rz
  rw [Set.union_eq_self_of_subset_left] at rz
  exact rz
  rfl
  rw [Set.union_eq_self_of_subset_right]
  rfl
  by_cases insert f1 (insertn Γ p ni)⊢p
  simp [h]
  rename_i h2
  have t:=h2 h
  apply False.elim t
  simp [h]
  intro x
  simp [h] at x
  exact nh x

lemma prf_primen_prf_insertn {Γ :  Set (Formula σ)} {p r : Formula σ} {n:Nat} :
  (primen Γ r (n+1) ⊢ p) → ∃ i, insertn (primen Γ r n) r i ⊢ p := by
  generalize eq : primen Γ r (n+1) = Γ'
  subst eq
  intro h
  have hh:= Finset_proof h
  rcases hh with ⟨Γ',h1,h2,h3⟩
  unfold primen at h1
  simp at h1
  have dq:∃ (I : Set ℕ), Set.Finite I ∧ Γ' ⊆ ⋃ i ∈ I, insertn (primen Γ r n) r i := by
    apply Set.finite_subset_iUnion
    assumption
    exact h1
  rcases dq with ⟨I,h4,h5⟩
  by_cases I = ∅
  simp [h] at h5
  have h5:Γ' = ∅ := by apply Set.subset_eq_empty h5;rfl
  simp [h5] at h2
  use 0
  have h6:= cond_mono_proof h2 (insertn (primen Γ r n) r 0)
  simp
  simp at h6
  exact h6
  have h7: I ≠ ∅ := by simp [h]
  have dp:=Set.Finite.exists_maximal_wrt (λ x=>x) I h4 (Set.nonempty_iff_ne_empty.mpr h7)
  simp at dp
  rcases dp with ⟨i,_,hn2⟩
  use i
  suffices hz:Γ' ⊆ insertn (primen Γ r n) r i
  have hz2: (insertn (primen Γ r n) r i ∪ Γ') ⊢ p := cond_mono_proof h2 _
  rw [Set.union_eq_self_of_subset_right] at hz2
  exact hz2
  exact hz
  apply subset_trans h5
  simp
  intro ii hi
  suffices hq:ii<= i
  exact insertn_mono hq
  by_cases ii ≤ i
  assumption
  have ht: i<=ii:= by linarith
  have hq:= hn2 ii hi ht
  linarith

def prime_has_disj {Γ :   Set (Formula σ)} {p q r : Formula σ} :((p ∨ᵢ q) ∈ prime Γ r) → p ∈ prime Γ r ∨ q ∈ prime Γ r :=by
intro h0
have h1:=prime_consq_iff_mem.mp h0
have h2:=primen_sub_prf h1
rcases h2 with ⟨n,hn⟩
have h4:=v_prime hn
cases h4 with
| inl hz=>left;apply prime_consq_iff_mem.mpr;apply subset_proof hz;unfold prime;intro x v;simp;use n+1
| inr hz=>right;apply prime_consq_iff_mem.mpr;apply subset_proof hz;unfold prime;intro x v;simp;use n+1



def primen_not_prfn {Γ :  Set (Formula σ)} {r: Formula σ} {n : Nat} :
  (primen Γ r n ⊢ r) → (Γ ⊢ r) := by
  intro h
  induction n
  simp at h
  exact h

  rename_i n nh
  cases prf_primen_prf_insertn h
  rename_i i hi
  apply nh
  apply insertn_prf hi

def prime_not_prf {Γ :  Set (Formula σ)} {r : Formula σ} :
  (prime Γ r ⊢ r) → (Γ ⊢ r) :=by
  intro h
  cases primen_sub_prf h
  rename_i n nh
  apply primen_not_prfn nh



lemma prime_of_prime {Γ :  Set (Formula σ)} {r : Formula σ} :
 is_prime (prime Γ r) :=by
    constructor
    intro f
    apply prime_consq_iff_mem.mpr
    constructor
    intro h hx hp
    apply prime_has_disj
    exact hp
    sorry



lemma prime_no_prf {Γ :  Set (Formula σ)} {r : Formula σ} (h : ¬ (Γ ⊢ r)) :
 ¬ (prime Γ r ⊢ r) :=
λ hm=> h (prime_not_prf hm)
