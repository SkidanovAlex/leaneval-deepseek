import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Vero.MulDefs

/-!
# The `Ψ`-lift spaces for `Work.HP.Vero.lam_Gam_veronese_le`

For a pair of real points `z w : ℝ^{n+1}`, `Lam d n z w` is the space of degree-`d` forms
(coefficient vectors `Mon d n → ℝ`) vanishing at both `z` and `w`, and `Lam2V a d n z w` is the
span of the products `G · Q` of a degree-`a` form `G` with a quadric `Q` through `z` and `w`.

The key identity (`Work.HP.Vero.Lam_gen_a`, delegated separately) is
`Lam (a+2) n z w = Lam2V a (a+2) n z w`, which is the "Ψ-lift" spanning statement: products of
degree-`a` forms with quadrics through the two points span *all* degree-`(a+2)` forms through the
two points.
-/

set_option autoImplicit false
noncomputable section
open Finset

namespace Work.HP.Vero

/-- Evaluation `A ↦ ∑ m, A m * ν_{d,n}(z) m` of a real coefficient vector at a real point, as a
linear map. -/
def evalLinR (d n : ℕ) (z : Fin (n + 1) → ℝ) : (Mon d n → ℝ) →ₗ[ℝ] ℝ where
  toFun A := ∑ m, A m * veronese d n z m
  map_add' A B := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring

@[simp] lemma evalLinR_apply (d n : ℕ) (z : Fin (n + 1) → ℝ) (A : Mon d n → ℝ) :
    evalLinR d n z A = formEvalR d n A z := rfl

/-- The space of degree-`d` real forms vanishing at the two real points `z` and `w`. -/
def Lam (d n : ℕ) (z w : Fin (n + 1) → ℝ) : Submodule ℝ (Mon d n → ℝ) :=
  LinearMap.ker (evalLinR d n z) ⊓ LinearMap.ker (evalLinR d n w)

lemma mem_Lam_iff {d n : ℕ} {z w : Fin (n + 1) → ℝ} {A : Mon d n → ℝ} :
    A ∈ Lam d n z w ↔ formEvalR d n A z = 0 ∧ formEvalR d n A w = 0 := by
  simp [Lam]

/-- `Lam2V a d n z w`: the span of the products of a degree-`a` form with a quadric through
`z` and `w`. -/
def Lam2V (a d n : ℕ) (z w : Fin (n + 1) → ℝ) : Submodule ℝ (Mon d n → ℝ) :=
  Submodule.span ℝ { B : Mon d n → ℝ | ∃ G : Mon a n → ℝ, ∃ Q : Mon 2 n → ℝ,
    Q ∈ Lam 2 n z w ∧ B = mulVec a 2 d G Q }

end Work.HP.Vero
