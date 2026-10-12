import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SlotProjAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-- The projection kernel `PV e a y = Σ_l e l a * conj (e l y)` vanishes as soon as the modes
vanish at the *first* (output) variable.  This is the first-argument companion of
`PV_eq_zero_of_factors` (which handles the second argument). -/
theorem PV_eq_zero_of_fst {m : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    {a y : EuclideanSpace ℝ (Fin 3)} (h : ∀ l, e l a = 0) : PV e a y = 0 := by
  simp only [PV, h, zero_mul, Finset.sum_const_zero]

-- Compact support of the slot projection `slotProj e T Φ x = ∫ z, (∏_{i∈T} PV e (x i) (z i)) *
-- Φ(updateFinset x T z)`.  Show `slotProj e T Φ x = 0` when either (i) some `i ∈ T` has
-- `x i ∉ ⋃ l, tsupport (e l)` (then every factor `PV e (x i) (z i)` is `0`, so the integrand
-- vanishes for every `z`; use `PV_eq_zero_of_fst` below, the first-argument companion of
-- `PV_eq_zero_of_factors` of `SlotProjAux`), or (ii) some `i ∉ T` has
-- `x i ∉ (fun y => y i) '' tsupport Φ` (then the `i`-th coordinate of `updateFinset x T z`
-- is `x i` for every `z`, so `Φ` of it is `0`).  Conclude with `HasCompactSupport.intro` for the
-- compact set `Set.univ.pi (fun i => if i ∈ T then ⋃ l, tsupport (e l) else
-- (fun y => y i) '' tsupport Φ)` (`isCompact_univ_pi`).
theorem slotProj_hasCompactSupport {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (T : Finset (Fin n)) (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    HasCompactSupport (slotProj e T Φ) := by
  classical
  refine HasCompactSupport.intro
    (K := Set.univ.pi (fun i : Fin n => if i ∈ T then (⋃ l : Fin m, tsupport (e l))
      else (fun y : Fin n → EuclideanSpace ℝ (Fin 3) => y i) '' tsupport Φ)) ?_ ?_
  · -- The candidate support is the product of finitely many compact sets.
    refine isCompact_univ_pi (fun i => ?_)
    by_cases hi : i ∈ T
    · rw [if_pos hi]
      exact isCompact_iUnion (fun l : Fin m => (hec l).isCompact)
    · rw [if_neg hi]
      exact (hΦc.isCompact).image (continuous_apply i)
  · intro x hx
    have hx' : ∃ i : Fin n, x i ∉ (if i ∈ T then (⋃ l : Fin m, tsupport (e l))
        else (fun y : Fin n → EuclideanSpace ℝ (Fin 3) => y i) '' tsupport Φ) := by
      simpa only [Set.mem_univ_pi, not_forall] using hx
    obtain ⟨i, hi⟩ := hx'
    change (∫ z : ↑T → EuclideanSpace ℝ (Fin 3),
      (∏ j : ↑T, PV e (x j.1) (z j)) * Φ (fun k => if h : k ∈ T then z ⟨k,h⟩ else x k)) = 0
    by_cases hiT : i ∈ T
    · -- Case (i): the `i`-th mode overlap kernel vanishes identically in `z`.
      have hxi : x i ∉ ⋃ l : Fin m, tsupport (e l) := by simpa [hiT] using hi
      have hf : (fun z : ↑T → EuclideanSpace ℝ (Fin 3) =>
          (∏ j : ↑T, PV e (x j.1) (z j)) *
            Φ (fun k => if h : k ∈ T then z ⟨k,h⟩ else x k)) = 0 := by
        funext z
        rw [Pi.zero_apply, Finset.prod_eq_zero (Finset.mem_univ (⟨i, hiT⟩ : ↑T))]
        · exact zero_mul _
        · exact PV_eq_zero_of_fst e (fun l => image_eq_zero_of_notMem_tsupport
            (fun hmem => hxi (Set.mem_iUnion.mpr ⟨l, hmem⟩)))
      rw [hf]
      exact integral_zero _ _
    · -- Case (ii): the `i`-th coordinate is untouched and lies outside the support of `Φ`.
      have hxi : x i ∉ (fun y : Fin n → EuclideanSpace ℝ (Fin 3) => y i) '' tsupport Φ := by
        simpa [hiT] using hi
      have hf : (fun z : ↑T → EuclideanSpace ℝ (Fin 3) =>
          (∏ j : ↑T, PV e (x j.1) (z j)) *
            Φ (fun k => if h : k ∈ T then z ⟨k,h⟩ else x k)) = 0 := by
        funext z
        rw [Pi.zero_apply, mul_eq_zero]
        right
        by_contra hne
        exact hxi ⟨(fun k => if h : k ∈ T then z ⟨k,h⟩ else x k),
          subset_tsupport Φ (by rwa [Function.mem_support]), by simp [hiT]⟩
      rw [hf]
      exact integral_zero _ _

end Work.BoseBoxFock
