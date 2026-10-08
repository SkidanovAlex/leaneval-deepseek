import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irreducible_character_mem_Irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Linear characters are irreducible

For a finite group `G`, a homomorphism `φ : G →* ℂˣ` is a one-dimensional complex
representation of `G`: multiplication by the scalar `φ g` on `ℂ`.  Its character is the
function `g ↦ (φ g : ℂ)`, and it is irreducible because `ℂ` is one-dimensional over `ℂ`.

The main statement is `Work.CharCore.exists_irr_of_monoidHom`: every monoid homomorphism
`G →* ℂˣ` is the character of an irreducible complex character of `G`.

The proof combines

* `Work.CharCore.irreducible_character_mem_Irr`, which says the character of any irreducible
  finite dimensional complex representation lies in `Irr G`;
* `is_simple_module_of_finrank_eq_one`, which says a module of `ℂ`-dimension one is simple.
-/

noncomputable section

open Classical

namespace Work.CharCore

variable {G : Type*} [Group G]

/-- Multiplication by a unit `c` of `ℂ`, as a `ℂ`-linear endomorphism of `ℂ`. -/
def unitMulLin (c : ℂˣ) : ℂ →ₗ[ℂ] ℂ where
  toFun x := (c : ℂ) * x
  map_add' x y := by ring
  map_smul' r x := by simp only [smul_eq_mul, RingHom.id_apply]; ring

/-- `unitMulLin c` is the scalar `(c : ℂ)`; its trace on the one-dimensional space `ℂ` is `c`. -/
theorem unitMulLin_trace (c : ℂˣ) : LinearMap.trace ℂ ℂ (unitMulLin c) = (c : ℂ) := by
  rw [show unitMulLin c = (c : ℂ) • (1 : ℂ →ₗ[ℂ] ℂ) from by
    apply LinearMap.ext; intro x
    change (c : ℂ) * x = ((c : ℂ) • (1 : ℂ →ₗ[ℂ] ℂ)) x
    rfl]
  simp only [LinearMap.map_smul, LinearMap.trace_one, Module.finrank_self, smul_eq_mul,
    Nat.cast_one, mul_one]

@[simp] theorem unitMulLin_apply (c : ℂˣ) (x : ℂ) : unitMulLin c x = (c : ℂ) * x := rfl

/-- The monoid homomorphism `ℂˣ →* End ℂ` sending a unit to multiplication by it. -/
def unitMulLinMonoidHom : ℂˣ →* (ℂ →ₗ[ℂ] ℂ) where
  toFun := unitMulLin
  map_one' := by
    apply LinearMap.ext; intro x
    change (↑(1 : ℂˣ) : ℂ) * x = x
    simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change (↑(a * b) : ℂ) * x = (↑a : ℂ) * (↑b * x)
    rw [Units.val_mul]; ring

/-- The one-dimensional complex representation of `G` attached to a homomorphism
`φ : G →* ℂˣ`: the group acts on `ℂ` by multiplication by the scalar `φ g`. -/
def monoidHomRep (φ : G →* ℂˣ) : Representation ℂ G ℂ :=
  unitMulLinMonoidHom.comp φ

@[simp] theorem monoidHomRep_apply (φ : G →* ℂˣ) (g : G) :
    monoidHomRep φ g = unitMulLin (φ g) := rfl

/-- The character of the one-dimensional representation attached to `φ` is `φ` itself. -/
theorem monoidHomRep_character (φ : G →* ℂˣ) :
    (monoidHomRep φ).character = (fun g : G => (φ g : ℂ)) := by
  funext g
  rw [Representation.character]
  show (LinearMap.trace ℂ ℂ) (monoidHomRep φ g) = (φ g : ℂ)
  rw [monoidHomRep_apply, unitMulLin_trace]

/-- The one-dimensional representation attached to `φ` is irreducible: its underlying
`ℂ[G]`-module is one-dimensional over `ℂ`, hence simple. -/
theorem monoidHomRep_isIrreducible (φ : G →* ℂˣ) : (monoidHomRep φ).IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  have hfr : Module.finrank ℂ (monoidHomRep φ).asModule = 1 := by
    rw [(Representation.asModuleEquiv (monoidHomRep φ)).finrank_eq, Module.finrank_self]
  rw [isSimpleModule_iff]
  exact is_simple_module_of_finrank_eq_one hfr

/-- Every monoid homomorphism `G →* ℂˣ` is the character of an irreducible complex character
of `G`. -/
theorem exists_irr_of_monoidHom {G : Type*} [Group G] [Fintype G] (φ : G →* ℂˣ) :
    ∃ χ ∈ Irr G, ∀ g : G, χ g = (φ g : ℂ) := by
  refine ⟨(monoidHomRep φ).character, ?_, ?_⟩
  · exact irreducible_character_mem_Irr (monoidHomRep φ) (monoidHomRep_isIrreducible φ)
  · intro g
    exact congrFun (monoidHomRep_character φ) g

end Work.CharCore
