import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.BoxOrthDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.eFunOrthonormal` — the slab indicators are orthonormal in `L²`

The `k`-th slab indicator is `eFun ℓ N k x = V^{-1/2}·1_{eSlice ℓ N k}(x)` with `V = ℓ³/N`
(`BoxOrthDefs`).  Hence for all `k l : Fin N` the product `star (eFun k) * eFun l` is
`V^{-1}·1_{eSlice k ∩ eSlice l}`, an integrable compactly supported bounded function, whose
integral is `V^{-1}·vol(eSlice k ∩ eSlice l)`; the slabs are pairwise disjoint
(`eSlice_disjoint`) and each has volume `V` (`volume_eSlice`).  So the family is orthonormal.
-/

noncomputable section

open MeasureTheory Set

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseBoxFock

/-- The slab volume `ℓ³/N` is nonnegative. -/
private lemma slVol_nonneg (ℓ : ℝ) (N : ℕ) (hℓ : 0 ≤ ℓ) (hN : 0 < N) : 0 ≤ slVol ℓ N := by
  rw [slVol]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  positivity

/-- The slab volume `ℓ³/N` is positive. -/
private lemma slVol_pos (ℓ : ℝ) (N : ℕ) (hℓ : 0 < ℓ) (hN : 0 < N) : 0 < slVol ℓ N := by
  rw [slVol]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  positivity

/-- The normalisation is the inverse square root of the slab volume: `slScale²·slVol = 1`. -/
private lemma slScale_sq_mul_slVol (ℓ : ℝ) (N : ℕ) (hℓ : 0 < ℓ) (hN : 0 < N) :
    slScale ℓ N ^ 2 * slVol ℓ N = 1 := by
  have hVpos := slVol_pos ℓ N hℓ hN
  have hs : (Real.sqrt (slVol ℓ N))⁻¹ * (Real.sqrt (slVol ℓ N))⁻¹ = (slVol ℓ N)⁻¹ := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt hVpos.le]
  rw [slScale, pow_two, hs]
  exact inv_mul_cancel₀ (ne_of_gt hVpos)

/-- Pointwise form of the orthogonality: the product of two slab indicators is the
normalisation `slScale²` times the indicator of the intersection of the slabs (which is
either empty or one of the slabs). -/
private lemma eFun_mul_eq_indicator (ℓ : ℝ) (N : ℕ) (k l : Fin N) (x : ℝ³) :
    (starRingEnd ℂ) (eFun ℓ N k x) * eFun ℓ N l x
      = ((slScale ℓ N ^ 2 : ℝ) : ℂ) *
        ((eSlice ℓ N k ∩ eSlice ℓ N l).indicator (fun _ => (1 : ℂ)) x) := by
  by_cases hk : x ∈ eSlice ℓ N k <;> by_cases hl : x ∈ eSlice ℓ N l
  · rw [eFun_of_mem hk, eFun_of_mem hl,
      Set.indicator_of_mem (show x ∈ eSlice ℓ N k ∩ eSlice ℓ N l from ⟨hk, hl⟩)
        (fun _ => (1 : ℂ)), mul_one]
    simp [Complex.conj_ofReal, ← Complex.ofReal_mul, pow_two]
  · rw [eFun_of_mem hk, eFun_of_notMem hl, mul_zero,
      Set.indicator_of_notMem (fun h => hl h.2) (fun _ => (1 : ℂ)), mul_zero]
  · rw [eFun_of_notMem hk, map_zero, zero_mul,
      Set.indicator_of_notMem (fun h => hk h.1) (fun _ => (1 : ℂ)), mul_zero]
  · rw [eFun_of_notMem hk, map_zero, zero_mul,
      Set.indicator_of_notMem (fun h => hk h.1) (fun _ => (1 : ℂ)), mul_zero]

theorem eFunOrthonormal (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) (hN : 0 < N) (k l : Fin N) :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => (starRingEnd ℂ) (Work.BoseBoxFock.eFun ℓ N k x) * Work.BoseBoxFock.eFun ℓ N l x) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) ∧
    (∫ x, (starRingEnd ℂ) (Work.BoseBoxFock.eFun ℓ N k x) * Work.BoseBoxFock.eFun ℓ N l x) = (if k = l then (1 : ℂ) else 0) := by
  have hpw : ∀ x : ℝ³, (starRingEnd ℂ) (eFun ℓ N k x) * eFun ℓ N l x
      = ((slScale ℓ N ^ 2 : ℝ) : ℂ) *
        ((eSlice ℓ N k ∩ eSlice ℓ N l).indicator (fun _ => (1 : ℂ)) x) :=
    fun x => eFun_mul_eq_indicator ℓ N k l x
  have hmeas : MeasurableSet (eSlice ℓ N k ∩ eSlice ℓ N l) :=
    (measurableSet_eSlice ℓ N k).inter (measurableSet_eSlice ℓ N l)
  have hfin : volume (eSlice ℓ N k ∩ eSlice ℓ N l) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_left)
    rw [volume_eSlice hℓ hN k]
    exact ENNReal.ofReal_ne_top
  have hIntR : Integrable
      (fun x : ℝ³ => ((slScale ℓ N ^ 2 : ℝ) : ℂ) *
        ((eSlice ℓ N k ∩ eSlice ℓ N l).indicator (fun _ => (1 : ℂ)) x)) volume :=
    ((integrableOn_const (s := eSlice ℓ N k ∩ eSlice ℓ N l) hfin
      (C := (1 : ℂ))).integrable_indicator hmeas).const_mul _
  refine ⟨hIntR.congr (Filter.Eventually.of_forall fun x => (hpw x).symm), ?_⟩
  have hint : (∫ x, (starRingEnd ℂ) (eFun ℓ N k x) * eFun ℓ N l x)
      = ((slScale ℓ N ^ 2 : ℝ) : ℂ) *
        ((Measure.real volume (eSlice ℓ N k ∩ eSlice ℓ N l)) : ℂ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpw), integral_const_mul,
      integral_indicator_const (1 : ℂ) hmeas, Complex.real_smul, mul_one]
  rw [hint]
  by_cases hkl : k = l
  · subst hkl
    rw [Set.inter_self, Measure.real_def, volume_eSlice hℓ hN k,
      ENNReal.toReal_ofReal (slVol_nonneg ℓ N hℓ.le hN),
      ← Complex.ofReal_mul, slScale_sq_mul_slVol ℓ N hℓ hN, Complex.ofReal_one, if_pos rfl]
  · rw [eSlice_disjoint hℓ hN hkl, Measure.real_def, measure_empty, ENNReal.toReal_zero,
      Complex.ofReal_zero, mul_zero, if_neg hkl]

end Work.BoseBoxFock
