import CLM.IFOL
import CLM.encode_formula
import CLM.general
import CLM.pigeon
open IFOL
open Set
open Classical

def insert_u {α:Type} {s: Set α} {a: α}: insert a s = s ∪ {a}:= by simp

def is_closed (Γ : Set (Formula σ)):=
∀ (f : Formula σ), (Γ ⊢ f) → (f ∈ Γ)

def has_disj (Γ : Set (Formula σ)):=
∀ (f g : Formula σ),((f ∨ᵢ g) ∈ Γ) → ((f ∈ Γ) ∨ (g ∈ Γ))

def has_const (Γ : Set (Formula σ)):=
∀ (f : Formula σ),((∃ᵢ f) ∈ Γ) → (∃(n c:ℕ),( p_bot_form ((f.Substitution (Term.free 0) (Term.const c)).down 0) n) ∈ Γ)

def is_prime (Γ : Set (Formula σ)):=
is_closed Γ ∧ has_disj Γ ∧ has_const Γ

def is_inf{σ:Signature}(Γ : Set (Formula σ))(bound:ℕ):=∀ N: ℕ, N ≥ bound →  (@Term.const σ (2*N)) ∉ free_terms Γ
--no const > 2*N
@[simp]
def insert_form (Γ : Set (Formula σ)) (p q r: Formula σ):Set (Formula σ) :=
if ((Γ∪{p})⊢ r) then {q} else {p}

def insert_c (_ : Set (Formula σ)) (f: Formula σ)(b:ℕ): Set (Formula σ):=by
    exact {(f.Substitution (Term.free 0) (Term.const (2*b))).down 0}


def if_elim {P:Prop}{α}{a}{X Y:Set α}(h1: a ∈ X)(h2: a ∈ Y): a ∈ (if P then X else Y):= by by_cases P;repeat simp[*]

def finite_free{σ:Signature}(f:Formula σ):∀n:ℕ, (Formula.free_terms f n).Finite:=by
  intro n
  induction f generalizing n
  simp[Formula.free_terms]
  apply Set.finite_iUnion
  intro x
  unfold Term.free_terms
  rename_i v vv;cases vv x;simp;rename_i v1;by_cases h:n ≤ v1;simp[h];simp[h];simp
  simp[ Formula.free_terms];rename_i a b c;constructor;exact b n;exact c n
  simp[ Formula.free_terms];rename_i a b c;constructor;exact b n;exact c n
  simp[ Formula.free_terms];rename_i a;exact a (n+1)
  simp[ Formula.free_terms];rename_i a;exact a (n+1)
  simp[ Formula.free_terms];rename_i a b c;constructor;exact b n;exact c n
  simp[ Formula.free_terms]

def const_show{σ:Signature}(t:Term σ):Nat := match t with
| Term.const n => n
| _ => 0

@[simp]
def insert_code (Γ: Set (Formula σ))(r: Formula σ)(n:Nat)(c:ℕ): Set (Formula σ):=
match @Encodable.decode (Formula σ) _ n with
| some f=> match f with
  | f1 ∨ᵢ f2 => if Γ ⊢ f1 ∨ᵢ f2 then insert_form Γ f1 f2 r else ∅
  | ∃ᵢ f => if Γ ⊢ ∃ᵢ f then insert_c Γ f c else ∅
  | _ => ∅
| none =>∅

def fin_insert_code{σ : Signature}{Γ: Set (Formula σ)}{r: Formula σ} : Set.Finite (insert_code Γ r n c) := by
  simp[insert_code]
  cases h:(@Encodable.decode (Formula σ) instEncodableFormula n : Option (Formula σ) )
  simp;simp;rename_i f
  cases f<;>simp
  rename_i f1 f2
  by_cases Γ ⊢ f1 ∨ᵢ f2
  simp[h]
  by_cases h2:insert f1 Γ⊢r
  simp[h2];simp[h2];simp[h]
  rename_i h3
  by_cases h4:Γ⊢∃ᵢh3
  simp[h4];simp[insert_c]
  simp[h4]





def inf_insert_one {Γ: Set (Formula σ)}(h0:is_inf Γ c)(f1:Formula σ): ∃ d, is_inf (insert f1 Γ) d:=by
  unfold is_inf
  unfold free_terms
  simp
  by_cases h:Set.Nonempty (Formula.free_terms f1 0)
  have ht:=Set.Finite.exists_maximal_wrt const_show (Formula.free_terms f1 0) (finite_free f1 0) h
  rcases ht with ⟨d,d2,hd⟩
  use (c+const_show d+1)
  intro N hN
  push_neg
  constructor
  intro hi
  have z:= hd _ hi
  cases d
  simp[const_show,Term.const] at z
  rw [z] at hN
  linarith
  simp[const_show,Term.const] at z
  rename_i p
  simp[const_show,Term.const] at hN
  have q: p ≤ 2* N := by linarith
  have z2:= z q
  rw [z2] at hN
  linarith
  unfold is_inf at h0
  intro f hi
  have h1:= h0 (N) (by linarith)
  unfold free_terms at h1
  simp at h1
  exact h1 f hi
  use c
  intro N hN
  push_neg
  constructor
  intro hi
  apply h
  use Term.const (2*N)
  unfold is_inf at h0
  intro f hi
  have h1:= h0 (N) (by linarith)
  unfold free_terms at h1
  simp at h1
  exact h1 f hi

def Finite_free {σ : Signature}{Γ: Set (Formula σ)}(h:Set.Finite Γ): Set.Finite (free_terms Γ):= by
  apply Set.Finite.biUnion h
  intro i _
  apply finite_free


noncomputable def set_max {σ : Signature}{Γ: Set (Formula σ)}(h:Set.Finite Γ):ℕ := by
  let s:= free_terms Γ
  by_cases h0:Set.Nonempty s
  have ht:=Set.Finite.exists_maximal_wrt const_show s (Finite_free h) h0
  let g:= const_show (Classical.choose ht)
  exact g+1
  exact 1




lemma no_const_max {σ: Signature}{Γ: Set (Formula σ)}(h:Set.Finite Γ): Term.const (2*(set_max h)) ∉ free_terms Γ := by
  intro hc
  by_cases h0:Set.Nonempty (free_terms Γ)
  simp[set_max] at hc
  simp [h0] at hc
  have ht:=Set.Finite.exists_maximal_wrt const_show _ (Finite_free h) h0
  have hpro:=Classical.choose_spec ht
  generalize eq:Classical.choose ht = d
  rw[eq] at hc
  rw[eq] at hpro
  have h5:const_show d ≤ const_show (@Term.const σ (2 * (const_show d + 1))) := match d with
                                                                      | Term.const n => by simp[const_show];linarith
                                                                      | Term.free n => by simp[const_show]
  have h3:=hpro.2 (Term.const (2 * (const_show d + 1))) hc h5
  simp[const_show] at h3
  match d with
  | Term.free n=> simp at h3;
  | Term.const n=> simp at h3;linarith














  have h1:free_terms Γ = ∅ := by generalize eq:free_terms Γ = s;
                                 rw[eq] at h0;
                                 rw[Set.nonempty_def] at h0;
                                 push_neg at h0;
                                 ext h3;constructor;
                                 intro h4;apply h0 h3 h4;
                                 intro h4;simp at h4
  rw[h1] at hc
  trivial





structure finForms (σ:Signature) where
  S: Set (Formula σ)
  h:Set.Finite S



@[simp]
def insertn (Γ: Set (Formula σ))(r: Formula σ):ℕ → finForms σ
| 0 => ⟨∅, by simp⟩
| n+1 => by have h0: Set.Finite (⋃ i:Fin (n+1), (insertn Γ r i).S):= by apply Set.finite_iUnion
                                                                        intro i;exact (insertn Γ r i).h
            let c:=set_max h0
            let s:=insert_code (Γ ∪ ⋃ i:Fin (n+1), (insertn Γ r i).S) r n c
            have hs: Set.Finite s:= by apply fin_insert_code
            exact ⟨s,hs⟩





@[simp]
def prime (Γ :Set (Formula σ))(r: Formula σ): Set (Formula σ):=
Γ ∪ (⋃ n, (insertn Γ r n).S)

def primen (Γ :Set (Formula σ))(r: Formula σ)(m:Nat): Set (Formula σ):=
Γ ∪ (⋃ n:Fin m, (insertn Γ r n).S)

-- lemma subset_insert_code {Γ :Set (Formula σ)}{r: Formula σ}(n) :  Γ ⊆ insert_code Γ r n :=by
--  intro v hv--  cases (@Encodable.decode (Formula σ) instEncodableFormula n : Option (Formula σ) )
--  assumption
--  rename_i val
--  simp[*]
--  cases val
--  · simp;assumption
--  · simp;assumption
--  · rename_i f1 f2
--    simp
--    apply if_elim
--    apply if_elim
--    simp;right;repeat trivial
--    simp;right;repeat trivial
--  · simp;apply if_elim;simp[insert_c];right;repeat trivial
--  · simp;assumption
--  · simp;assumption
--  · simp;assumption


-- lemma subset_insertn {Γ :Set (Formula σ)}{r: Formula σ} (n) : Γ ⊆ insertn Γ r n :=by
-- induction n
-- · simp;rfl
-- · simp
--   rename_i n nh
--   cases (@Encodable.decode (Formula σ) instEncodableFormula n : Option (Formula σ))
--   simp;assumption
--   rename_i val
--   cases val
--   · simp;assumption
--   · simp;assumption
--   · rename_i f1 f2
--     simp
--     by_cases insertn Γ r n⊢f1∨ᵢf2
--     simp[h]
--     by_cases insert f1 (insertn Γ r n)⊢r
--     simp [h]
--     intro f hf
--     apply Set.mem_insert_of_mem
--     apply nh
--     assumption
--     simp [h]
--     intro f hf
--     apply Set.mem_insert_of_mem
--     apply nh
--     assumption
--     simp [h]
--     assumption
--   · simp;intro x hx;apply if_elim;simp[insert_c];right;repeat {exact nh hx}
--   · simp;assumption
--   · simp;assumption
--   · simp;assumption

-- lemma subset_prime_self{Γ :Set (Formula σ)}{r: Formula σ} : Γ ⊆ prime Γ r :=by
-- simp;intro x hx;rw[Set.mem_iUnion];use 0;apply subset_insertn;exact hx


-- lemma in_prime_in_primen {Γ :Set (Formula σ)}{p r: Formula σ} :
--  (p ∈ prime Γ r ) → ∃ n, p ∈ insertn Γ r n :=
-- mem_iUnion.1

-- lemma insertn_mono {Γ :Set (Formula σ)}{r: Formula σ} {n m : Nat}(h : n ≤ m) :
--   insertn Γ r n ⊆ insertn Γ r m :=by
--   induction h
--   rfl
--   rename_i h_ih
--   exact subset_trans h_ih (subset_insert_code _)



lemma v_insert_code {σ : Signature}(Γ: Set (Formula σ))(p q f r: Formula σ)(eq: f =(p∨ᵢq)){n:ℕ}(hn: Γ ⊢ f)(h0:is_inf Γ c)(h:n=@Encodable.encode (Formula σ) _ f):  ((insert_code Γ r n c) ⊢ p) ∨ ((insert_code Γ r n c) ⊢ q) :=by
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

-- lemma v_insertn {σ : Signature}(Γ: Set (Formula σ))(p q f r: Formula σ)(eq: f =(p∨ᵢq)){n:ℕ}(hn: Γ ⊢ f)(h:n=@Encodable.encode (Formula σ) _ f):
-- ((insertn Γ r (n+1)).S ⊢ p) ∨ ((insertn Γ r (n+1)).S ⊢ q):=by
-- unfold insertn
-- have z: Nat.add n 0 = n := by simp
-- rw [z]
-- apply v_insert_code
-- exact eq
-- apply subset_proof hn
-- simp



lemma Finset_proof {Γ :Set (Formula σ)}{r: Formula σ}(h: Γ ⊢ r):∃ (Γ':Set (Formula σ)),(Γ' ⊆ Γ) ∧ (Γ' ⊢ r) ∧ (Γ'.Finite):=by
induction h with
| ref ha =>rename_i f Q;use {f};simp;constructor;trivial;constructor;simp
| introI A B =>
  rename_i s t v
  rcases B with ⟨Γ',h0,h1,h4⟩
  use Γ'\{s}
  constructor;
  rw [Set.diff_subset_iff]
  have utran: (v ∪ {s})=({s} ∪ v) := by simp
  rw [utran] at h0
  exact h0
  constructor;
  apply Proof.introI
  rw [Set.diff_union_self]
  apply cond_mono_proof2
  exact h1
  apply Set.Finite.diff
  assumption
| elimI  _ _ h3 h4=>
  rename_i h1 h2
  rcases h3 with ⟨Γ',h11,h12,h13⟩
  rcases h4 with ⟨Γ'',h5,h6,h7⟩
  use Γ' ∪ Γ''
  constructor;
  rw [Set.union_subset_iff]
  constructor; exact subset_union_of_subset_left h11 _; exact subset_union_of_subset_right h5 _
  constructor;
  apply Proof.elimI h12 h6
  apply Set.Finite.union
  assumption
  assumption
| introA  _ _ h3 h4=>
  rcases h3 with ⟨Γ',h11,h12,h13⟩
  rcases h4 with ⟨Γ'',h5,h6,h7⟩
  use Γ' ∪ Γ''
  constructor;
  rw [Set.union_subset_iff]
  constructor; exact subset_union_of_subset_left h11 _; exact subset_union_of_subset_right h5 _
  constructor;
  apply Proof.introA h12 h6
  apply Set.Finite.union
  assumption
  assumption
| elimA1  _ g=>
  rcases g with ⟨Γ',h1,h2,h3⟩
  use Γ'
  constructor;
  assumption
  constructor;
  apply Proof.elimA1  h2
  assumption
| elimA2  _ g=>
  rcases g with ⟨Γ',h1,h2,h3⟩
  use Γ'
  constructor;
  assumption
  constructor;
  apply Proof.elimA2  h2
  assumption
| introO1  _ _ h2=>
  rcases h2 with ⟨Γ',h2,h3,h4⟩
  use Γ'
  constructor;
  assumption
  constructor;
  apply Proof.introO1 _ h3
  assumption
| introO2  _ _ h2=>
  rcases h2 with ⟨Γ',h2,h3,h4⟩
  use Γ'
  constructor;
  assumption
  constructor;
  apply Proof.introO2 _ h3
  assumption
| elimO  _ _ _ h5 h6 h7=>
  rename_i A B Δ f g h1 h2 h3 h4
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
| introF _ h1 P =>
  rename_i f S tt
  rcases P with ⟨Γ',h31,h32,h33⟩
  use Γ'
  constructor;
  assumption
  constructor;
  apply Proof.introF
  assumption
  intro t
  unfold free_terms at t
  apply h1
  unfold free_terms at h1
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
| botE A h1 P =>
  rename_i Q
  cases P
  rename_i h3 h4
  use h3
  constructor;exact h4.left;constructor
  apply Proof.botE
  exact h4.right.left
  exact h4.right.right

| elimF A _ h2  =>
  rcases h2 with ⟨Γ',h31,h32,h33⟩
  use Γ'
  constructor;
  assumption
  constructor;
  apply Proof.elimF
  assumption
  assumption
| introE _ h1 =>
  rcases h1 with ⟨Γ',h31,h32,h33⟩
  use Γ'
  constructor;
  assumption
  constructor;
  apply Proof.introE
  assumption
  assumption
| elimE A h1 P S h2 h3 =>
  rename_i Q B C D E
  rcases h3 with ⟨Γ',h71,h72,h73⟩
  rcases h2 with ⟨Γ'',h61,h62,h63⟩
  generalize eq : Formula.down 0 (Formula.Substitution Q (Term.free 0) E) = z
  rw [eq] at h1
  rw [eq] at h71
  use (Γ'\{z}) ∪ Γ''
  constructor;
  rw [Set.union_subset_iff]
  constructor; apply subset_union_of_subset_right; apply diff_subset_iff.mpr;rw [Set.union_comm]; exact h71;
  apply subset_union_of_subset_left; assumption
  constructor;
  rw [Set.union_comm]
  apply Proof.elimE
  exact h62
  rw [eq]
  rw [Set.diff_union_self]
  apply cond_mono_proof2 h72
  simp [free_terms] at P
  simp [free_terms]
  intro x hx hxx
  apply P
  have s:= h71 hx
  simp [hxx] at s
  exact s
  assumption
  apply Finite.union
  apply Finite.diff
  assumption
  assumption

def subset_diff_union {α:Type} {u v w: Set α} : u \ v ⊆ w → u ⊆ v ∪ w:= by
  intro h x hx
  by_cases h2:x ∈ v
  simp [h2]
  apply Set.mem_union_right
  apply h
  simp [h2,hx]
def primen_sub_prf {Γ :Set (Formula σ)}{p r: Formula σ} :
  (prime Γ r ⊢ p) → ∃ n, primen Γ r n ⊢ p := by
  intro h
  have h:= Finset_proof h
  rcases h with ⟨Γ',h1,h2,h3⟩
  unfold prime at h1
  have dq:∃ (I : Set ℕ), Set.Finite I ∧ (Γ'\ Γ) ⊆ (⋃ i ∈ I, (insertn Γ r i).S) := by
    apply Set.finite_subset_iUnion
    apply Set.Finite.diff h3
    intro x hx
    have h2: x ∈ Γ' := ((Set.mem_diff x).mp hx).1
    have h3: x ∉ Γ := ((Set.mem_diff x).mp hx).2
    have h4:=h1 h2
    cases h4;trivial;assumption

  rcases dq with ⟨I,h4,h5⟩
  by_cases I = ∅
  simp [h] at h5
  have h5:Γ'\ Γ = ∅ := by apply Set.subset_eq_empty h5;rfl
  use 0
  simp[primen]
  apply subset_proof h2
  exact Iff.mp diff_eq_empty h5

  have h7: I ≠ ∅ := by simp [h]
  have dp:=Set.Finite.exists_maximal_wrt (λ x=>x) I h4 (Set.nonempty_iff_ne_empty.mpr h7)
  simp at dp
  rcases dp with ⟨n,_,hn2⟩
  use n+1
  suffices hz:Γ' ⊆ Γ ∪ ⋃ i:Fin (n+1),(insertn Γ r i).S
  apply subset_proof h2 hz
  have h6:= subset_diff_union h5
  suffices ht:⋃ (i : ℕ) (_ : i ∈ I), (insertn Γ r i).S ⊆ ⋃ (i : Fin (n+1)), (insertn Γ r ↑i).S
  apply subset_trans h6
  apply Set.union_subset_union_right
  exact ht
  simp
  intro i hi
  have h7:= hn2 i hi
  have h8: i < n + 1 :=by by_contra h9
                          have htt:=Nat.ge_of_not_lt h9
                          have h10:n ≤ i:= by linarith
                          have h11:= h7 h10
                          linarith
  intro q hq
  simp
  use ⟨i,h8⟩




lemma ind(n:Nat): n=0 ∨ ∃ m, n=m+1 := by
  cases n
  simp
  right
  rename_i q
  use q

def std{σ:Signature}(Γ :  Set (Formula σ))(r: Formula σ): Prop := is_inf Γ 0 ∧ is_inf {r} 0 --standard condition


lemma insertn_prf {Γ :  Set (Formula σ)} {p: Formula σ} {i:Nat}(hstd:std Γ p) :
  (primen Γ p i ⊢ p) → (Γ ⊢ p) :=by
  induction i
  simp[primen]
  rename_i ni nh
  simp[primen]
  intro h
  apply nh
  simp[primen]
  generalize eq : Γ ∪ ⋃ (n : Fin ni), (insertn Γ p ↑n).S = S
  have eq1:Γ ∪ ⋃ (n : Fin (Nat.succ ni)), (insertn Γ p ↑n).S = S ∪ (insertn Γ p ni).S := by
      ext f
      constructor
      intro hf
      cases hf with
      | inl hl=> left;rw[← eq];left;exact hl
      | inr hr=> simp at hr
                 rcases hr with ⟨⟨i,si⟩,hi⟩
                 by_cases i = ni
                 right
                 simp at hi
                 rw [h] at hi
                 exact hi
                 left
                 rw [← eq]
                 right
                 simp
                 have hz: i < ni := by by_contra hz; have hz2:=Nat.lt_succ.mp si;cases eq_or_lt_of_le hz2;trivial;trivial
                 exact ⟨⟨i,hz⟩,hi⟩
      intro hf
      cases hf with
      | inl hl=>  rw[← eq] at hl
                  cases hl with
                  | inl hl=>left;exact hl
                  | inr hr=> right
                             simp at hr
                             simp
                             rcases hr with ⟨⟨o,so⟩,ho⟩
                             use ⟨o,by linarith⟩
      | inr hr=> right
                 simp at hr
                 simp
                 use ⟨ni,by simp⟩
  rw [eq1] at h
  unfold insertn at h
  cases ni
  simp at h
  exact h
  rename_i ni
  cases h0:(@Encodable.decode (Formula σ) instEncodableFormula ni : Option (Formula σ))
  simp at h
  rw [h0] at h
  simp at h
  exact h
  simp at h
  rename_i val
  generalize eq3 :Γ ∪ ⋃ (i : Fin (ni + 1)), (insertn Γ p ↑i).S = Q
  have hqs: Q = S :=by
    rw[← eq3,← eq]
  cases hq:val
  rw [h0] at h<;> rw [hq] at h<;>simp at h<;> try assumption
  rw [h0] at h<;> rw [hq] at h<;>simp at h<;> try assumption
  rw [h0] at h<;> rw [hq] at h<;>simp at h
  rename_i f1 f2

  rw [eq] at h
  by_cases h04:S⊢f1∨ᵢf2
  simp[h04] at h
  by_cases h1:insert f1 S⊢p
  simp[h1] at h
  rw[← union_self S]
  nth_rw 1 [← union_self S]
  apply Proof.elimO h04
  apply subset_proof h1;simp
  rfl
  apply subset_proof h;simp;rfl
  simp [h1] at h
  simp[h04] at h
  exact h
  simp[h0] at h
  simp[hq] at h
  rename_i f
  by_cases hext: ¬ ((Γ ∪ ⋃ (i : Fin (ni + 1)), (insertn Γ p ↑i).S)⊢∃ᵢf)
  simp[hext] at h;exact h
  push_neg at hext;simp[hext] at h
  rw[eq] at hext
  unfold insert_c at h
  rw[← union_self S]
  apply Proof.elimE hext h
  generalize eq8:set_max (_ : Set.Finite (⋃ (i : Fin (ni + 1)), (insertn Γ p ↑i).S)) = i
  have h0:=hstd.1 i (by linarith)
  rw [← eq]
  simp [free_terms]
  intro x hx
  cases hx with
  | inl hl=> simp[free_terms] at h0; exact h0 x hl
  | inr hr=> simp[free_terms] at h
             rcases hr with ⟨ii,hii⟩
             have hsfin: Set.Finite (⋃ i:Fin (ni+1), (insertn Γ p i).S):= by apply Set.finite_iUnion
                                                                             intro i;exact (insertn Γ p i).h
             have hmax:=no_const_max hsfin
             rw [← eq8]
             simp[free_terms] at hmax
             have hmax2:=hmax x ii hii
             exact hmax2
  generalize eq8:set_max (_ : Set.Finite (⋃ (i : Fin (ni + 1)), (insertn Γ p ↑i).S)) = i
  have h0:=hstd.2 i (by linarith)
  simp [free_terms] at h0
  exact h0





  -- other
  rw [h0] at h; rw [hq] at h;simp at h;try assumption
  rw [h0] at h; rw [hq] at h;simp at h;try assumption
  rw [h0] at h; rw [hq] at h;simp at h;try assumption


def prime_has_disj {Γ :   Set (Formula σ)} {p q r : Formula σ} :((p ∨ᵢ q) ∈ prime Γ r) → p ∈ prime Γ r ∨ q ∈ prime Γ r :=by
intro h0
simp[prime] at h0
cases h0
· rename_i hpq
  generalize heq:(p ∨ᵢ q) = f
  generalize eq:(@Encodable.encode (Formula σ) _ f) = n
  by_cases hc:insert p (Γ ∪ ⋃ (i : Fin (n + 1)), (insertn Γ r ↑i).S)⊢r
  right
  right
  simp
  use n+1
  simp[insertn]
  have ed3:@Encodable.decode (Formula σ) instEncodableFormula n = (p ∨ᵢ q):= by rw[← eq];simp[heq]
  rw [ed3]
  simp
  constructor
  rw [heq] at hpq
  rw [heq]
  apply subset_proof (Proof.ref hpq)
  simp
  simp[hc]
  left
  right
  simp
  use n+1
  simp[insertn]
  have ed3:@Encodable.decode (Formula σ) instEncodableFormula n = (p ∨ᵢ q):= by rw[← eq];simp[heq]
  rw [ed3]
  simp
  constructor
  rw [heq] at hpq
  rw [heq]
  apply subset_proof (Proof.ref hpq)
  simp
  simp[hc]
· rename_i hz
  rcases hz with ⟨i,hi⟩
  have hinf:=inf_form_gen q p (i+1)
  rcases hinf with ⟨m,hm⟩
  generalize eq:Encodable.encode (qp_bot_form p q m) = num
  rw [eq] at hm
  by_cases hc:¬ (insert p (Γ ∪ ⋃ (i : Fin (num + 1)), (insertn Γ r ↑i).S)⊢r)
  left
  simp[prime]
  right
  use num+1
  simp [insertn]
  have ed3:@Encodable.decode (Formula σ) instEncodableFormula num = (qp_bot_form p q m):= by rw[← eq];simp
  rw[ed3]
  simp
  unfold qp_bot_form
  simp
  constructor
  apply (provable_qp_bot _ _ _ _).mpr
  apply Proof.ref
  right
  have hmi:i<num+1:=by linarith
  simp
  use⟨i,hmi⟩
  simp[hc]
  push_neg at hc

  right
  simp[prime]
  right
  have hr:(p_bot_form q m) ∈ (insertn Γ r (num+1)).S:= by
    simp [insertn]
    have ed3:@Encodable.decode (Formula σ) instEncodableFormula num = (qp_bot_form p q m):= by rw[← eq];simp
    rw[ed3]
    simp
    unfold qp_bot_form
    simp
    constructor
    apply (provable_qp_bot _ _ _ _).mpr
    apply Proof.ref
    right
    have hmi:i<num+1:=by linarith
    simp
    use⟨i,hmi⟩
    simp[hc]
  have hr2:(insertn Γ r (num+1)).S ⊢ q:= by apply (provable_p_bot _ _ _).mp;apply Proof.ref;exact hr
  have h3:=inf_form_gen2 p q (num+2)
  rcases h3 with ⟨n2,hn2⟩
  generalize eq2:Encodable.encode (pq_bot_form p q n2) = num2
  rw [eq2] at hn2
  use (num2+1)
  simp [insertn]
  have ed3:@Encodable.decode (Formula σ) instEncodableFormula num2 = (pq_bot_form p q n2):= by rw[← eq2];simp
  rw[ed3]
  simp[pq_bot_form]
  constructor
  apply Proof.introO2
  apply subset_proof hr2
  intro x hx
  right
  simp
  use ⟨(num+1),by linarith⟩
  have hsc:(Γ ∪ ⋃ (i : Fin (num+1)), (insertn Γ r ↑i).S) ⊢ p →ᵢ r := by
    apply Proof.introI
    apply subset_proof hc
    simp
    rfl
  generalize eq4:Γ ∪ ⋃ (i : Fin (num+1)), (insertn Γ r ↑i).S = S'
  rw [eq4] at hsc
  have hz0:{p_bot_form p n2}⊢p:= by apply (provable_p_bot _ _ n2).mp;apply Proof.ref;simp
  have hz:= Proof.elimI hsc hz0
  generalize eq5:Γ ∪ ⋃ (i : Fin (num2+1)), (insertn Γ r ↑i).S = S''
  have hss:S' ⊆ S'':= by rw[← eq4,← eq5];simp;intro x hx hxx;right;simp;use ⟨x.1,by linarith[x.2]⟩
  have hz2:insert (p_bot_form p n2) S''⊢r:= by apply subset_proof hz;simp;apply Set.insert_subset_insert hss
  simp [hz2]


def prime_consq_iff_mem  {Γ :Set (Formula σ)}{p r: Formula σ} :
  (p ∈ prime Γ r) ↔ (prime Γ r ⊢ p):= by
  constructor
  intro h
  exact Proof.ref h
  intro h
  have h:= primen_sub_prf h
  rcases h with ⟨n,hn⟩
  simp
  right
  have h3:=inf_form_gen2 ⊥ p (n+1)
  rcases h3 with ⟨m,hm⟩
  generalize eq2:Encodable.encode (pq_bot_form ⊥ p m) = num
  use (num+1)
  simp[insertn]
  have heq:@Encodable.decode (Formula σ) instEncodableFormula num = (pq_bot_form ⊥ p m):= by rw[← eq2];simp
  rw[heq]
  simp
  simp[pq_bot_form]
  constructor
  apply Proof.introO2
  apply subset_proof hn
  intro x hx
  simp
  simp[primen] at hx
  cases hx
  left;assumption;
  right;
  rename_i hi
  rcases hi with ⟨i,hi⟩
  use ⟨i.1,by linarith[i.2]⟩
  suffices hs:insert (p_bot_form ⊥ m) (Γ ∪ ⋃ (i : Fin (num+1)), (insertn Γ r ↑i).S)⊢r
  simp[hs]
  apply Proof.botE
  suffices hs:{p_bot_form ⊥ m} ⊢ ⊥
  apply subset_proof hs;simp
  apply (provable_p_bot _ _ m).mp
  apply Proof.ref
  rfl



def prime_not_prf {Γ :  Set (Formula σ)} {r : Formula σ}(hstd: std Γ r) :
  (prime Γ r ⊢ r) → (Γ ⊢ r) :=by
  intro h
  cases primen_sub_prf h
  rename_i n nh
  apply insertn_prf hstd nh



lemma prime_of_prime {Γ :  Set (Formula σ)} {r : Formula σ} :
 is_prime (prime Γ r) :=by
    constructor
    intro f
    apply prime_consq_iff_mem.mpr
    constructor
    intro h hx hp
    apply prime_has_disj
    exact hp
    unfold has_const
    intro f hf
    simp[prime] at hf
    cases hf with
    | inl hl=> generalize eq2:Encodable.encode (∃ᵢf) = num
               let sset := insertn Γ r (num+1)
               have h1:∃ c, Formula.down 0 (Formula.Substitution f (Term.free 0) (Term.const c)) ∈ sset.S := by
                  have :@Encodable.decode (Formula σ) instEncodableFormula num = (∃ᵢf) := by rw[← eq2];simp
                  simp [this]
                  constructor
                  apply subset_proof (Proof.ref hl);simp
                  unfold insert_c
                  simp
               rcases h1 with ⟨c,hc⟩
               use 0
               have h3:sset.S ⊆ prime Γ r:= by
                  unfold prime
                  intro s hs
                  right
                  simp
                  use num+1
               use c
               exact h3 hc
    | inr hr => rcases hr with ⟨i,hi⟩
                have h1:=inf_form_gene f (i+1)
                rcases h1 with ⟨m,hm⟩
                unfold prime
                use m
                suffices hs:∃ c, p_bot_form (Formula.down 0 (Formula.Substitution f (Term.free 0) (Term.const c))) m ∈ ⋃ (n : ℕ), (insertn Γ r n).S
                rcases hs with ⟨c,hc⟩
                use c
                right;exact hc
                simp
                generalize eq2:Encodable.encode (e_bot_form f m) = num
                apply exists_swap.mp
                use num+1
                simp
                have heq:@Encodable.decode (Formula σ) instEncodableFormula num = (e_bot_form f m):= by rw[← eq2];simp
                rw[heq]
                simp[e_bot_form]
                constructor
                suffices hg:(insertn Γ r i).S ⊢ ∃ᵢp_bot_form f m
                apply subset_proof hg
                apply Set.subset_union_of_subset_right
                intro x hx;simp
                use ⟨i,by linarith⟩
                generalize eq3:(insertn Γ r i).S=Q
                have st:=Proof.ref hi
                rw[eq3] at st
                -- let τ:=@Term.const σ (@set_max _ {f} (by simp))
                -- generalize eqg:Formula.down 0 (Formula.Substitution f (Term.free 0) τ) = g
                -- have h1:(∅ ∪ {(f.Substitution (Term.free 0) τ).down 0}) ⊢ (f.Substitution (Term.free 0) τ).down 0 := by apply Proof.ref;simp
                -- have h2:(∅ ∪ {(f.Substitution (Term.free 0) τ).down 0}) ⊢ (∃ᵢf) := by
                --   simp
                --   apply Proof.introE h1
                have := (provable_e_bot Q f m).mpr st
                simp[e_bot_form] at this
                exact this

                generalize eqx:2 * set_max (_ : Set.Finite (⋃ (i : Fin (num + 1)), (insertn Γ r ↑i).S))=x
                use x
                simp[insert_c]
                rw[eqx]
                rw[← @p_bot_form_cross_sub σ f m (Term.free 0) (Term.const x)]
                rw[← @p_bot_form_cross_down σ _ m 0]





















lemma prime_no_prf {Γ :  Set (Formula σ)} {r : Formula σ} (h : ¬ (Γ ⊢ r))(hstd: std Γ r) :
 ¬ (prime Γ r ⊢ r) :=
λ hm=> h (prime_not_prf hstd hm)
