import CLM.IFOL
import CLM.encode_formula

open IFOL
open Set

def is_closed (Γ : Set (Formula σ)):=
∀ (f : Formula σ), (Γ ⊢ f) → (f ∈ Γ)

def has_disj (Γ : Set (Formula σ)):=
∀ (f g : Formula σ),((f ∨ᵢ g) ∈ Γ) → ((f ∈ Γ) ∨ (g ∈ Γ))

def is_prime (Γ : Set (Formula σ)):=
is_closed Γ ∧ has_disj Γ

def insert_form (Γ : Set (Formula σ)) (f g h: Formula σ):Set (Formula σ) :=
if (Γ ⊢ h) then Γ∪{g} else Γ∪{f}

def insert_code(Γ: Set (Formula σ))(r: Formula σ)(n:Nat): Set (Formula σ):=
match Encodable.decode (Formula σ) n with
| some (p ∨ᵢ q) => if (Γ ⊢ p ∨ q) then insert_form Γ p q r else Γ
| _ => Γ
