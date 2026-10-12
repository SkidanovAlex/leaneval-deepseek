import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotExact_ae_bounded_of_bounded
import Submission.Work.BoseBoxFock.slotProj_peel_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotProj1_memLp_top`

The single-slot projection

`slotProj1 e i f x = ∫ w, PV e (x i) w * f (Function.update x i w)`

of an `L^∞` state `f` (with modes `e l` that are `L^∞` and supported in the box `boxL ℓ`) is
again `L^∞`.  There is **no** support hypothesis on `f` and no continuity: the state is only
a.e. bounded and a.e. strongly measurable, and the kernel `PV e (x i) w = Σ_l e l (x i) · conj (e l w)`
is supported in the box of finite volume `boxL ℓ`, so the `w`-integral of the (a.e.) bounded
integrand is bounded uniformly in `x` up to a null set of configurations.

## The reduction

The single-slot projection is the *singleton* slot projection

`slotProj e ({i} : Finset (Fin n)) f = slotProj1 e i f`   (`slotProj_singleton_eq_slotProj1`),

a hypothesis-free identity: the fibre space `↑{i} → Ω` is a copy of `Ω` via the constant-function
measure-preserving equivalence `MeasurableEquiv.funUnique`, the product over the subsingleton
fibre collapses to its single factor, and `Function.updateFinset x {i} (fun _ => w) =
Function.update x i w`.  Everything about `slotProj1` therefore follows from the corresponding
statement for `slotProj` at the singleton slot, which the library already provides:

* `slotProj_aesm` (`L^∞` modes and state → a.e. strong measurability of the slot projection);
* `slotProj_ae_bounded` (`L^∞`+box-supported modes, `L^∞` state → a.e. boundedness of the slot
  projection);

and `MeasureTheory.memLp_top_of_bound` converts "a.e. strongly measurable plus a.e. bounded" into
`MemLp · ⊤`.
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-- **The singleton slot projection is the single-slot projection.**  This is an identity of
functions, with no hypothesis whatsoever on the modes or on the state: the fibre `↑{i} → Ω` of the
singleton slot set is `Ω` through the constant-function equivalence `MeasurableEquiv.funUnique`,
which preserves the (product) volume. -/
theorem slotProj_singleton_eq_slotProj1 {m n : ℕ} (e : Fin m → Ω → ℂ) (i : Fin n)
    (f : (Fin n → Ω) → ℂ) :
    slotProj e ({i} : Finset (Fin n)) f = slotProj1 e i f := by
  have hφ : MeasureTheory.MeasurePreserving
      ((MeasurableEquiv.funUnique (↥({i} : Finset (Fin n))) Ω).symm)
      (volume : Measure Ω) (volume : Measure (↥({i} : Finset (Fin n)) → Ω)) :=
    MeasureTheory.MeasurePreserving.symm (MeasurableEquiv.funUnique (↥({i} : Finset (Fin n))) Ω)
      (MeasureTheory.volume_preserving_funUnique (↥({i} : Finset (Fin n))) Ω)
  funext x
  simp only [slotProj_eq_slotInt, slotInt, slotProj1]
  refine (hφ.integral_comp' (fun z : ↥({i} : Finset (Fin n)) → Ω =>
    (∏ j : ↥({i} : Finset (Fin n)), PV e (x j.1) (z j)) *
      f (Function.updateFinset x ({i} : Finset (Fin n)) z))).symm.trans ?_
  apply integral_congr_ae
  filter_upwards with w
  rw [funUnique_symm_apply_singleton i w]
  rw [Fintype.prod_subsingleton
    (fun j : ↥({i} : Finset (Fin n)) => PV e (x j.1) ((fun _ : ↥({i} : Finset (Fin n)) => w) j))
    ⟨i, Finset.mem_singleton_self i⟩]
  rw [updateFinset_singleton_eq_update i x w]

/-- **A.e. strong measurability of the single-slot projection.** -/
theorem slotProj1_aesm {m n : ℕ} {e : Fin m → Ω → ℂ}
    (he : ∀ l, AEStronglyMeasurable (e l) (volume : Measure Ω)) (i : Fin n)
    {f : (Fin n → Ω) → ℂ} (hf : AEStronglyMeasurable f (volume : Measure (Fin n → Ω))) :
    AEStronglyMeasurable (slotProj1 e i f) (volume : Measure (Fin n → Ω)) := by
  rw [← slotProj_singleton_eq_slotProj1 e i f]
  exact slotProj_aesm he ({i} : Finset (Fin n)) hf

/-- **A.e. boundedness of the single-slot projection.** -/
theorem slotProj1_ae_bounded {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (i : Fin n) {f : (Fin n → Ω) → ℂ} (hf : MemLp f ⊤) :
    ∃ C, ∀ᵐ x ∂(volume : Measure (Fin n → Ω)), ‖slotProj1 e i f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := slotProj_ae_bounded hbdd hsupp ({i} : Finset (Fin n)) hf
  exact ⟨C, by simpa only [slotProj_singleton_eq_slotProj1 e i f] using hC⟩

theorem slotProj1_memLp_top {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (i : Fin n) {f : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hf : MeasureTheory.MemLp f ⊤) :
    MeasureTheory.MemLp (Work.BoseBoxFock.slotProj1 e i f) ⊤ := by
  have haesm : MeasureTheory.AEStronglyMeasurable (Work.BoseBoxFock.slotProj1 e i f)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → EuclideanSpace ℝ (Fin 3))) :=
    slotProj1_aesm (fun l => (hbdd l).aestronglyMeasurable) i hf.aestronglyMeasurable
  obtain ⟨C, hC⟩ := slotProj1_ae_bounded hbdd hsupp i hf
  exact MeasureTheory.memLp_top_of_bound haesm C hC

end Work.BoseBoxFock
