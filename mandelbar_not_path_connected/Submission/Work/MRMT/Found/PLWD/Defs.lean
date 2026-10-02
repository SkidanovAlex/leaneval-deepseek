/-
Work.MRMT.Found.PLWD — vocabulary for the local weak-derivative lemma
`Work.MRMT.Found.principalData_local_weak_derivative`.

The proof of that lemma does **not** use the field `PrincipalData.dz_tendsto`.  What it uses is

* the uniform `L²` bound `∫_{B(0,R)} ‖∂(F n)‖² ≤ C` for the approximating `C¹` diffeomorphisms
  (`Work.MRMT.Found.uniform_dz_bound`), and
* the fact that for a `C¹` test function `ψ` supported in `B(0,R)` the pairings
  `∫ ∂(F n) · ψ = -∫ F n · ∂ψ` converge to `-∫ φ · ∂ψ` (integration by parts plus the locally
  uniform convergence `F n → φ`).

The pairings `ψ ↦ -∫ φ · ∂ψ` and `ψ ↦ -∫ φ · ∂̄ψ` are therefore bounded linear functionals for
the `L²` norm on the test functions, and they extend by density to bounded functionals on the
Hilbert space `L²(B(0,R))`.  The Riesz representation theorem then *produces* the weak
derivative.

This file fixes the vocabulary of that argument:

* `tsupport_add_subset'` — `tsupport (f + g) ⊆ tsupport f ∪ tsupport g`;
* `testSpace R` — the `ℂ`-submodule of `ℂ → ℂ` of `C¹` functions with compact support contained
  in `Metric.ball 0 R`;
* `memLp_of_mem_testSpace` — such a function is in `L²` for `volume.restrict (ball 0 R)`;
* `testLp R` — the linear map sending a test function to its class in `L²(B(0,R))`.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Topology ENNReal

namespace Work.MRMT.Found

/-- The topological support of a sum is contained in the union of the topological supports. -/
theorem tsupport_add_subset' (f g : ℂ → ℂ) :
    tsupport (f + g) ⊆ tsupport f ∪ tsupport g := by
  rw [tsupport, tsupport, tsupport]
  refine closure_minimal ?_ (isClosed_closure.union isClosed_closure)
  intro x hx
  rcases eq_or_ne (f x) 0 with hf | hf
  · refine Or.inr (subset_closure ?_)
    simpa [hf] using hx
  · exact Or.inl (subset_closure hf)

/-- Multiplication by a constant does not increase the topological support. -/
theorem tsupport_const_smul_subset (c : ℂ) (f : ℂ → ℂ) : tsupport (c • f) ⊆ tsupport f := by
  rw [tsupport, tsupport]
  refine closure_mono ?_
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hf
  exact hx (by simp [hf])

/-- The `ℂ`-submodule of `ℂ → ℂ` consisting of the `C¹` functions with compact support
contained in the ball of radius `R` around the origin.  These are the test functions used to
test the weak `∂`- and `∂̄`-derivatives. -/
def testSpace (R : ℝ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {ψ | ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Metric.ball 0 R}
  zero_mem' := by
    refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
    rw [tsupport_zero]
    exact Set.empty_subset _
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
    exact ⟨hf1.add hg1, hf2.add hg2, (tsupport_add_subset' f g).trans (Set.union_subset hf3 hg3)⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2, hf3⟩
    exact ⟨hf1.const_smul c, hf2.mul_left (f := fun _ : ℂ => c), (tsupport_const_smul_subset c f).trans hf3⟩

/-- Membership in `testSpace R`, unfolded. -/
@[simp] theorem mem_testSpace {R : ℝ} {ψ : ℂ → ℂ} :
    ψ ∈ testSpace R ↔ ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Metric.ball 0 R :=
  Iff.rfl

/-- A test function is square integrable for the restricted measure on the ball. -/
theorem memLp_of_mem_testSpace {R : ℝ} {ψ : ℂ → ℂ} (hψ : ψ ∈ testSpace R) :
    MemLp ψ 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R)) := by
  have hcd : ContDiff ℝ 1 ψ := hψ.1
  have hcs : HasCompactSupport ψ := hψ.2.1
  have hsq : HasCompactSupport (fun z : ℂ => ‖ψ z‖ ^ 2) :=
    hcs.comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
  have hint : Integrable (fun z : ℂ => ‖ψ z‖ ^ 2) (volume : Measure ℂ) :=
    (hcd.continuous.norm.pow 2).integrable_of_hasCompactSupport hsq
  refine (memLp_two_iff_integrable_sq_norm (f := ψ) ?_).mpr hint.integrableOn
  exact hcd.continuous.aestronglyMeasurable.restrict

/-- The class in `L²(B(0,R))` of a test function `ψ ∈ testSpace R`. -/
def testLp (R : ℝ) : testSpace R →ₗ[ℂ] Lp ℂ 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R)) where
  toFun ψ := (memLp_of_mem_testSpace ψ.2).toLp (ψ : ℂ → ℂ)
  map_add' ψ₁ ψ₂ := by
    rw [← MemLp.toLp_add (memLp_of_mem_testSpace ψ₁.2) (memLp_of_mem_testSpace ψ₂.2)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.refl _ _)
  map_smul' c ψ := by
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (memLp_of_mem_testSpace ψ.2)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.refl _ _)

@[simp] theorem testLp_apply (R : ℝ) (ψ : testSpace R) :
    testLp R ψ = (memLp_of_mem_testSpace ψ.2).toLp (ψ : ℂ → ℂ) := rfl

end Work.MRMT.Found
