import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.GalBasis.cc.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Two elementary helpers

The estimate is the crudest possible one: on the whole angular interval `Iθ` the integrand
`(K θ · Sw θ)²` is bounded by `9` (`K ≤ 3` and `Sw ≤ 1` there), while the two end-pieces
`Iθ ∖ Icc ε (π/2-ε)` sit inside `Icc 0 ε ∪ Icc (π/2-ε) (π/2)`, a set of total length `2ε`.
Hence `K2 = 18` works. -/

/-- On the angular interval, `(K θ · Sw θ)² ≤ 9`. Indeed `0 ≤ K θ ≤ 3` and `0 ≤ Sw θ ≤ 1`
there (`K = 3 sin θ cos²θ` and `Sw = sin(2θ)^{η/2}` with `0 ≤ sin(2θ) ≤ 1`). -/
private lemma sq_K_Sw_le_nine {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ) ^ 2 ≤ 9 := by
  have hK0 : 0 ≤ Work.Spaces.K θ := Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθ
  have hK3 : Work.Spaces.K θ ≤ 3 := Work.FTS.GalBasis.cc.K_le_three_of_mem_Iθ hθ
  have hSw0 : 0 ≤ Work.FTS.GalBasis.cc.Sw θ :=
    Work.FTS.GalBasis.cc.Sw_nonneg_of_mem_Iθ hθ
  have hSw1 : Work.FTS.GalBasis.cc.Sw θ ≤ 1 := by
    rw [Work.FTS.GalBasis.cc.Sw]
    exact Real.rpow_le_one (Work.FTS.GalBasis.cc.sin_two_nonneg_of_mem_Iθ hθ)
      (Real.sin_le_one (2 * θ))
      (div_nonneg (le_of_lt Work.Spaces.eta_pos) (by norm_num))
  have hprod0 : 0 ≤ Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ := mul_nonneg hK0 hSw0
  have hprod3 : Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ ≤ 3 := by
    have h := mul_le_mul hK3 hSw1 hSw0 (by norm_num : (0 : ℝ) ≤ 3)
    simpa using h
  have h := pow_le_pow_left₀ hprod0 hprod3 2
  have h9 : (3 : ℝ) ^ 2 = 9 := by norm_num
  linarith [h, h9]

/-- The end-pieces `Iθ ∖ Icc ε (π/2-ε)` sit inside `Icc 0 ε ∪ Icc (π/2-ε) (π/2)`. -/
private lemma sdiff_Icc_subset {ε : ℝ} :
    Work.Spaces.Iθ \ Set.Icc ε (π / 2 - ε)
      ⊆ Set.Icc 0 ε ∪ Set.Icc (π / 2 - ε) (π / 2) := by
  intro θ hθ
  obtain ⟨hθI, hθnot⟩ := hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθI
  rcases lt_or_ge θ ε with h | h
  · exact Or.inl ⟨hθI.1, le_of_lt h⟩
  · refine Or.inr ⟨?_, hθI.2⟩
    by_contra hcon
    exact hθnot ⟨h, le_of_lt (lt_of_not_ge hcon)⟩

/-- The real Lebesgue measure of the two end-pieces is at most `2ε`. -/
private lemma measureReal_sdiff_Icc_le {ε : ℝ} (hε0 : 0 < ε) :
    volume.real (Work.Spaces.Iθ \ Set.Icc ε (π / 2 - ε)) ≤ 2 * ε := by
  have hmeasU : volume (Set.Icc 0 ε ∪ Set.Icc (π / 2 - ε) (π / 2)) < ⊤ :=
    measure_union_lt_top isCompact_Icc.measure_lt_top isCompact_Icc.measure_lt_top
  have hIcc0 : volume.real (Set.Icc 0 ε) = ε := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ ε - 0)]
    ring
  have hIcc1 : volume.real (Set.Icc (π / 2 - ε) (π / 2)) = ε := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      show π / 2 - (π / 2 - ε) = ε by ring, ENNReal.toReal_ofReal (le_of_lt hε0)]
  calc volume.real (Work.Spaces.Iθ \ Set.Icc ε (π / 2 - ε))
      ≤ volume.real (Set.Icc 0 ε ∪ Set.Icc (π / 2 - ε) (π / 2)) :=
        measureReal_mono sdiff_Icc_subset hmeasU.ne
    _ ≤ volume.real (Set.Icc 0 ε) + volume.real (Set.Icc (π / 2 - ε) (π / 2)) :=
        measureReal_union_le _ _
    _ = 2 * ε := by rw [hIcc0, hIcc1]; ring

/-- namespace `Work.FTS.StrongEps.L12`, declaration name `EndsBound`.
The two angular end-pieces of `(K θ · Sw θ)²` (with `K θ = 3 sin θ cos²θ`,
`Sw θ = sin(2θ)^{η/2}`) are small: there is `K2 ≥ 0` with
`∫_{θ ∈ Iθ ∖ Icc ε (π/2-ε)} (K θ Sw θ)² ≤ K2 · ε` for every `ε ∈ (0, π/4)`.
Indeed `(K Sw)²` is continuous on the compact `Iθ`, hence bounded there by some `C ≥ 0`, and the two
end-pieces `Iθ ∖ Icc ε (π/2-ε) = [0,ε) ∪ (π/2-ε, π/2]` have total length `2ε`, so `K2 := 2C` works
(even the crude `K2 := 18` does, since `(K Sw)² ≤ 9` on `Iθ`). -/
theorem EndsBound : ∃ K2 : ℝ, 0 ≤ K2 ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) (π / 4),
    ∫ θ in Work.Spaces.Iθ \ Set.Icc ε (π / 2 - ε),
      (Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ) ^ 2 ≤ K2 * ε := by
  refine ⟨18, by norm_num, ?_⟩
  intro ε hε
  obtain ⟨hε0, _hε4⟩ := hε
  set S : Set ℝ := Work.Spaces.Iθ \ Set.Icc ε (π / 2 - ε) with hS
  set F : ℝ → ℝ := fun θ => (Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ) ^ 2 with hF
  have hsub : S ⊆ Set.Icc 0 ε ∪ Set.Icc (π / 2 - ε) (π / 2) := by
    rw [hS]; exact sdiff_Icc_subset
  have hmeasS : volume S < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub)
      (measure_union_lt_top isCompact_Icc.measure_lt_top isCompact_Icc.measure_lt_top)
  have hbound : ∀ θ ∈ S, ‖F θ‖ ≤ 9 := by
    intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := (hS ▸ hθ).1
    rw [hF, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_K_Sw_le_nine hθI
  have key : ‖∫ θ in S, F θ‖ ≤ 9 * volume.real S :=
    norm_setIntegral_le_of_norm_le_const hmeasS hbound
  have hμ : volume.real S ≤ 2 * ε := by rw [hS]; exact measureReal_sdiff_Icc_le hε0
  calc ∫ θ in S, F θ
      ≤ |∫ θ in S, F θ| := le_abs_self _
    _ = ‖∫ θ in S, F θ‖ := (Real.norm_eq_abs _).symm
    _ ≤ 9 * volume.real S := key
    _ ≤ 9 * (2 * ε) := mul_le_mul_of_nonneg_left hμ (by norm_num)
    _ = 18 * ε := by ring

end Work.FTS.StrongEps.L12
