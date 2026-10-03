/-
# The two endpoint estimates for the minor-arc parts

For each of the two minor-arc parts `minorArc₁`, `minorArc₂` this file proves:

* the **loss** estimate, an `ℓ^{V₁} ⊗ ℓ^{V₂} → ℓ^{V₃}` bound with the polynomial constant `1 + C`
  (`C` the `ℓ^{V₁}` bound for the projection), from Hölder's inequality for the halved average
  (`eLpNorm_AhalfR_le`) and `iw-prop`(i);
* the **gain** estimate, an `ℓ² ⊗ ℓ² → ℓ¹` bound with the weight
  `improvWeight c ρ L N = 2^{-c(L-1)} + (Log N)^{-c/ρ}` of `ImprovKMT` (area A4), from `ImprovKMT`
  applied at the pair `(L-1, K-1)` (resp. `(L-1, K₂-d)`), which the projections reach by
  `kmtProj_sub_comp_eq_zero`.
-/
import Submission.Work.KMTAreas.A5.Setup
import Submission.Work.KMTAreas.A5.endpoint_trivial
import Submission.Work.KMTAreas.A7.ProjBound

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A5

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.KMTContract
open Work.Analysis.EndVar
open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier
open Submission.PointwiseErgodicTheorems

/-- **The `ℓ^p` bound for the concrete Ionescu--Wainger projections**, from area A1 via
`Work.KMTAreas.A7` (Lemma `iw-prop`(i)). -/
theorem kmtProj_lp_bound_A1 (hA1 : AreaA1) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {p : ℝ} (hp : 1 < p) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ≥0, 0 < C ∧
      ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → ∀ f : ℤ → ℂ,
        eLpNorm (kmtProj ρ l k f) (ENNReal.ofReal p) Measure.count
          ≤ ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (angleBracket l : ℝ)
              * eLpNorm f (ENNReal.ofReal p) Measure.count := by
  obtain ⟨M, hMpos, hMb⟩ := Work.KMTAreas.A7.EtaMult
  exact Work.KMTAreas.A7.kmtProj_lp_bound (Work.KMTAreas.A7.EtaProjGeTwo hA1 hMpos hMb)
    hρ0 hρ1 hp

/-- Monotonicity of the good-major-arc condition in its constant: the *larger* the constant, the
*stronger* the hypothesis, so a smaller constant also works. -/
theorem goodMajorArcs_mono {ρ C C' : ℝ} (h : C ≤ C') {l : ℕ} {k : ℤ}
    (hk : GoodMajorArcs ρ C' l k) : GoodMajorArcs ρ C l k := by
  rw [GoodMajorArcs] at hk ⊢
  have h2 : -C' * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ -C * (2 : ℝ) ^ (ρ * (l : ℝ)) := by
    have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) := Real.rpow_nonneg (by norm_num) _
    nlinarith
  linarith

/-- **The loss estimate for the second minor-arc part.** -/
theorem lossEndpoint₂ {ρ : ℝ} {L : ℕ} {K K₂ : ℤ} {N : ℝ≥0} {P : ℤ[X]} {V₁ V₂ V₃ : ℝ}
    (hV₁ : 1 < V₁) (hV₂ : 1 < V₂) (hV₃ : 1 ≤ V₃)
    (hrel : (ENNReal.ofReal V₁)⁻¹ + (ENNReal.ofReal V₂)⁻¹ = (ENNReal.ofReal V₃)⁻¹)
    {C₁ C₂ : ℝ≥0} (hC₁ : 0 < C₁) (hproj₁ : ∀ u : ℤ → ℂ,
      eLpNorm (kmtProj ρ L K u) (ENNReal.ofReal V₁) Measure.count
        ≤ (C₁ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal V₁) Measure.count)
    (hproj₂ : ∀ v : ℤ → ℂ,
      eLpNorm (kmtProj ρ L K₂ v) (ENNReal.ofReal V₂) Measure.count
        ≤ (C₂ : ℝ≥0∞) * eLpNorm v (ENNReal.ofReal V₂) Measure.count) :
    ∀ u v : ℤ → ℂ,
      eLpNorm (minorArc₂ ρ L K K₂ N P u v) (ENNReal.ofReal V₃) Measure.count
        ≤ ((C₁ * ((1 : ℝ≥0) + C₂) : ℝ≥0) : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal V₁) Measure.count
            * eLpNorm v (ENNReal.ofReal V₂) Measure.count := by
  refine endpoint_trivial (fun u v => minorArc₂ ρ L K K₂ N P u v)
    (p := ENNReal.ofReal V₁) (q := ENNReal.ofReal V₂) (r := ENNReal.ofReal V₃)
    (M := ((C₁ * ((1 : ℝ≥0) + C₂) : ℝ≥0) : ℝ≥0∞)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro h
    have h' : C₁ * ((1 : ℝ≥0) + C₂) = 0 := ENNReal.coe_eq_zero.mp h
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact hC₁.ne' h1
    · exact absurd h1 (by positivity)
  · exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  · exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  · intro v; exact minorArc₂_zero_left ρ L K K₂ N P v
  · intro u; exact minorArc₂_zero_right ρ L K K₂ N P u
  · intro u v hu hv
    have hmu : MemLp u (ENNReal.ofReal V₁) Measure.count :=
      MeasureTheory.memLp_iff.mpr hu
    have hmv : MemLp v (ENNReal.ofReal V₂) Measure.count :=
      MeasureTheory.memLp_iff.mpr hv
    have hPilt : eLpNorm (kmtProj ρ L K u) (ENNReal.ofReal V₁) Measure.count < ⊤ :=
      lt_of_le_of_lt (hproj₁ u) (ENNReal.mul_lt_top ENNReal.coe_lt_top hu)
    have hPimem : MemLp (kmtProj ρ L K u) (ENNReal.ofReal V₁) Measure.count :=
      MeasureTheory.memLp_iff.mpr hPilt
    have hQlt : eLpNorm (kmtProj ρ L K₂ v) (ENNReal.ofReal V₂) Measure.count < ⊤ :=
      lt_of_le_of_lt (hproj₂ v) (ENNReal.mul_lt_top ENNReal.coe_lt_top hv)
    have hQmem : MemLp (kmtProj ρ L K₂ v) (ENNReal.ofReal V₂) Measure.count :=
      MeasureTheory.memLp_iff.mpr hQlt
    have hsubmem : MemLp (v - kmtProj ρ L K₂ v) (ENNReal.ofReal V₂) Measure.count :=
      hmv.sub hQmem
    have hsub : eLpNorm (v - kmtProj ρ L K₂ v) (ENNReal.ofReal V₂) Measure.count
        ≤ (((1 : ℝ≥0) + C₂ : ℝ≥0) : ℝ≥0∞) * eLpNorm v (ENNReal.ofReal V₂) Measure.count := by
      refine (eLpNorm_sub_le
        (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hV₂.le)).trans ?_
      calc eLpNorm v (ENNReal.ofReal V₂) Measure.count
              + eLpNorm (kmtProj ρ L K₂ v) (ENNReal.ofReal V₂) Measure.count
          ≤ eLpNorm v (ENNReal.ofReal V₂) Measure.count
              + (C₂ : ℝ≥0∞) * eLpNorm v (ENNReal.ofReal V₂) Measure.count :=
            add_le_add_right (hproj₂ v) _
        _ = (((1 : ℝ≥0) + C₂ : ℝ≥0) : ℝ≥0∞) * eLpNorm v (ENNReal.ofReal V₂) Measure.count := by
            push_cast
            ring
    calc eLpNorm (minorArc₂ ρ L K K₂ N P u v) (ENNReal.ofReal V₃) Measure.count
        = eLpNorm (AhalfR TZ N X P (kmtProj ρ L K u)
            (v - kmtProj ρ L K₂ v)) (ENNReal.ofReal V₃) Measure.count := rfl
      _ ≤ eLpNorm (kmtProj ρ L K u) (ENNReal.ofReal V₁) Measure.count
            * eLpNorm (v - kmtProj ρ L K₂ v) (ENNReal.ofReal V₂) Measure.count :=
          eLpNorm_AhalfR_le TZ measurePreserving_TZ N X P hrel
            (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hV₃) hPimem hsubmem
      _ ≤ ((C₁ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal V₁) Measure.count)
            * ((((1 : ℝ≥0) + C₂ : ℝ≥0) : ℝ≥0∞) * eLpNorm v (ENNReal.ofReal V₂) Measure.count) :=
          mul_le_mul (hproj₁ u) hsub bot_le bot_le
      _ = ((C₁ * ((1 : ℝ≥0) + C₂) : ℝ≥0) : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal V₁) Measure.count
            * eLpNorm v (ENNReal.ofReal V₂) Measure.count := by
          push_cast
          ring

/-- **The loss estimate for the first minor-arc part.** -/
theorem lossEndpoint₁ {ρ : ℝ} {L : ℕ} {K : ℤ} {N : ℝ≥0} {P : ℤ[X]} {V₁ V₂ V₃ : ℝ}
    (hV₁ : 1 < V₁) (hV₂ : 1 < V₂) (hV₃ : 1 ≤ V₃)
    (hrel : (ENNReal.ofReal V₁)⁻¹ + (ENNReal.ofReal V₂)⁻¹ = (ENNReal.ofReal V₃)⁻¹)
    {C₁ : ℝ≥0} (hproj₁ : ∀ u : ℤ → ℂ,
      eLpNorm (kmtProj ρ L K u) (ENNReal.ofReal V₁) Measure.count
        ≤ (C₁ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal V₁) Measure.count) :
    ∀ u v : ℤ → ℂ,
      eLpNorm (minorArc₁ ρ L K N P u v) (ENNReal.ofReal V₃) Measure.count
        ≤ (((1 : ℝ≥0) + C₁ : ℝ≥0) : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal V₁) Measure.count
            * eLpNorm v (ENNReal.ofReal V₂) Measure.count := by
  refine endpoint_trivial (fun u v => minorArc₁ ρ L K N P u v)
    (p := ENNReal.ofReal V₁) (q := ENNReal.ofReal V₂) (r := ENNReal.ofReal V₃)
    (M := (((1 : ℝ≥0) + C₁ : ℝ≥0) : ℝ≥0∞)) ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  · exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  · intro v; exact minorArc₁_zero_left ρ L K N P v
  · intro u; exact minorArc₁_zero_right ρ L K N P u
  · intro u v hu hv
    have hmu : MemLp u (ENNReal.ofReal V₁) Measure.count :=
      MeasureTheory.memLp_iff.mpr hu
    have hmv : MemLp v (ENNReal.ofReal V₂) Measure.count :=
      MeasureTheory.memLp_iff.mpr hv
    have hPilt : eLpNorm (kmtProj ρ L K u) (ENNReal.ofReal V₁) Measure.count < ⊤ :=
      lt_of_le_of_lt (hproj₁ u)
        (ENNReal.mul_lt_top ENNReal.coe_lt_top hu)
    have hPimem : MemLp (kmtProj ρ L K u) (ENNReal.ofReal V₁) Measure.count :=
      MeasureTheory.memLp_iff.mpr hPilt
    have hsubmem : MemLp (u - kmtProj ρ L K u) (ENNReal.ofReal V₁) Measure.count :=
      hmu.sub hPimem
    have hsub : eLpNorm (u - kmtProj ρ L K u) (ENNReal.ofReal V₁) Measure.count
        ≤ (((1 : ℝ≥0) + C₁ : ℝ≥0) : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal V₁) Measure.count := by
      refine (eLpNorm_sub_le
        (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hV₁.le)).trans ?_
      calc eLpNorm u (ENNReal.ofReal V₁) Measure.count
              + eLpNorm (kmtProj ρ L K u) (ENNReal.ofReal V₁) Measure.count
          ≤ eLpNorm u (ENNReal.ofReal V₁) Measure.count
              + (C₁ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal V₁) Measure.count :=
            add_le_add_right (hproj₁ u) _
        _ = (((1 : ℝ≥0) + C₁ : ℝ≥0) : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal V₁) Measure.count := by
            push_cast
            ring
    calc eLpNorm (minorArc₁ ρ L K N P u v) (ENNReal.ofReal V₃) Measure.count
        = eLpNorm (AhalfR TZ N X P (u - kmtProj ρ L K u) v) (ENNReal.ofReal V₃)
            Measure.count := rfl
      _ ≤ eLpNorm (u - kmtProj ρ L K u) (ENNReal.ofReal V₁) Measure.count
            * eLpNorm v (ENNReal.ofReal V₂) Measure.count :=
          eLpNorm_AhalfR_le TZ measurePreserving_TZ N X P hrel
            (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hV₃) hsubmem hmv
      _ ≤ ((((1 : ℝ≥0) + C₁ : ℝ≥0) : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal V₁) Measure.count)
            * eLpNorm v (ENNReal.ofReal V₂) Measure.count :=
          mul_le_mul_of_nonneg_right hsub bot_le


/-- **The gain estimate for the first minor-arc part.** -/
theorem gainEndpoint₁ {P : ℤ[X]} (hImp : ImprovKMT P) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) {L : ℕ} {K : ℤ} (hLK : K = -(logN N) + (L : ℤ)) (hL : 1 ≤ L)
    (hcomp : ∀ u : ℤ → ℂ, BoundedZ u →
      kmtProj ρ (L - 1) (K - 1) (u - kmtProj ρ L K u) = 0)
    {C₂ : ℝ≥0} (hproj₂ : ∀ u : ℤ → ℂ, eLpNorm (kmtProj ρ L K u) 2 Measure.count
        ≤ (C₂ : ℝ≥0∞) * eLpNorm u 2 Measure.count) :
    ∃ (c : ℝ) (Cg : ℝ≥0), 0 < c ∧ 0 < Cg ∧ ∀ u v : ℤ → ℂ,
      eLpNorm (minorArc₁ ρ L K (N : ℝ≥0) P u v) 1 Measure.count
        ≤ (Cg : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
            * eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count := by
  obtain ⟨c, hc, hCrho⟩ := hImp
  obtain ⟨C₀imp, hbound⟩ := hCrho ρ hρ0 hρ1
  have hWpos : (0 : ℝ≥0) < improvWeight c ρ L N := improvWeight_pos c ρ L N
  refine ⟨c, (C₀imp + 1) * ((1 : ℝ≥0) + C₂), hc, mul_pos (by positivity) (by positivity), ?_⟩
  have hMne : (((C₀imp + 1) * ((1 : ℝ≥0) + C₂) : ℝ≥0) : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
      ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨by simp, ENNReal.coe_ne_zero.mpr hWpos.ne'⟩
  refine endpoint_trivial (fun u v => minorArc₁ ρ L K (N : ℝ≥0) P u v)
    (p := 2) (q := 2) (r := 1)
    (M := (((C₀imp + 1) * ((1 : ℝ≥0) + C₂) : ℝ≥0) : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞))
    hMne (by norm_num) (by norm_num)
    (by intro v; exact minorArc₁_zero_left ρ L K (N : ℝ≥0) P v)
    (by intro u; exact minorArc₁_zero_right ρ L K (N : ℝ≥0) P u) ?_
  intro u v hu hv
  have hmu : MemLp u 2 Measure.count :=
    MeasureTheory.memLp_iff.mpr hu
  have hmv : MemLp v 2 Measure.count :=
    MeasureTheory.memLp_iff.mpr hv
  have hbu : BoundedZ u := boundedZ_of_memLp (by norm_num) hmu
  have hPilt : eLpNorm (kmtProj ρ L K u) 2 Measure.count < ⊤ :=
    lt_of_le_of_lt (hproj₂ u) (ENNReal.mul_lt_top ENNReal.coe_lt_top hu)
  have hPimem : MemLp (kmtProj ρ L K u) 2 Measure.count :=
    MeasureTheory.memLp_iff.mpr hPilt
  have hPbdd : BoundedZ (kmtProj ρ L K u) := boundedZ_of_memLp (by norm_num) hPimem
  have hwbdd : BoundedZ (u - kmtProj ρ L K u) := boundedZ_sub hbu hPbdd
  have hwmem : MemLp (u - kmtProj ρ L K u) 2 Measure.count := hmu.sub hPimem
  have hzero : kmtProj ρ (L - 1) (-(logN N) + ((L - 1 : ℕ) : ℤ))
      (u - kmtProj ρ L K u) = 0 := by
    have hcast : ((L - 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by
      push_cast [Nat.cast_sub hL]
      ring
    have : (-(logN N) + ((L - 1 : ℕ) : ℤ) : ℤ) = K - 1 := by
      rw [hcast, hLK]; ring
    rw [this]
    exact hcomp u hbu
  have hgain := hbound N (L - 1) (u - kmtProj ρ L K u) v hN hwmem hmv (Or.inl hzero)
  have hW : ((2 : ℝ) ^ (-(c * ((L : ℝ) - 1))) + ((logN N : ℝ)) ^ (-(c / ρ)))
      = ((2 : ℝ) ^ (-(c * (((L - 1 : ℕ) : ℝ)))) + ((logN N : ℝ)) ^ (-(c / ρ))) := by
    have hcast : (((L - 1 : ℕ) : ℝ)) = (L : ℝ) - 1 := by
      push_cast [Nat.cast_sub hL]
      ring
    rw [hcast]
  have hsub : eLpNorm (u - kmtProj ρ L K u) 2 Measure.count
      ≤ (((1 : ℝ≥0) + C₂ : ℝ≥0) : ℝ≥0∞) * eLpNorm u 2 Measure.count := by
    refine (eLpNorm_sub_le
      (show (1 : ℝ≥0∞) ≤ 2 by norm_num)).trans ?_
    calc eLpNorm u 2 Measure.count + eLpNorm (kmtProj ρ L K u) 2 Measure.count
        ≤ eLpNorm u 2 Measure.count + (C₂ : ℝ≥0∞) * eLpNorm u 2 Measure.count :=
          add_le_add_right (hproj₂ u) _
      _ = (((1 : ℝ≥0) + C₂ : ℝ≥0) : ℝ≥0∞) * eLpNorm u 2 Measure.count := by
          push_cast
          ring
  rw [minorArc₁]
  have hgain' : eLpNorm (AhalfR TZ (N : ℝ≥0) X P (u - kmtProj ρ L K u) v) 1 Measure.count
      ≤ (C₀imp : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
          * eLpNorm (u - kmtProj ρ L K u) 2 Measure.count * eLpNorm v 2 Measure.count := by
    rw [improvWeight_coe c ρ L N, hW]
    exact hgain
  have hAB : eLpNorm (u - kmtProj ρ L K u) 2 Measure.count
      ≤ ((((1 : ℝ≥0) + C₂) : ℝ≥0) : ℝ≥0∞) * eLpNorm u 2 Measure.count := hsub
  have hconst : (C₀imp : ℝ≥0∞) * ((((1 : ℝ≥0) + C₂) : ℝ≥0) : ℝ≥0∞)
      ≤ ((((C₀imp + 1) * ((1 : ℝ≥0) + C₂)) : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_mul]
    refine ENNReal.coe_le_coe.mpr ?_
    show C₀imp * ((1 : ℝ≥0) + C₂) ≤ (C₀imp + 1) * ((1 : ℝ≥0) + C₂)
    exact mul_le_mul_of_nonneg_right (by simp) (by positivity)
  refine hgain'.trans ?_
  calc (C₀imp : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
        * eLpNorm (u - kmtProj ρ L K u) 2 Measure.count * eLpNorm v 2 Measure.count
      ≤ (C₀imp : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
        * (((((1 : ℝ≥0) + C₂) : ℝ≥0) : ℝ≥0∞) * eLpNorm u 2 Measure.count)
        * eLpNorm v 2 Measure.count :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAB (by positivity)) (by positivity)
    _ ≤ (((C₀imp + 1) * ((1 : ℝ≥0) + C₂) : ℝ≥0) : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
        * eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count := by
        have h1 : (C₀imp : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
            * (((((1 : ℝ≥0) + C₂) : ℝ≥0) : ℝ≥0∞) * eLpNorm u 2 Measure.count)
            * eLpNorm v 2 Measure.count
            = ((C₀imp : ℝ≥0∞) * ((((1 : ℝ≥0) + C₂) : ℝ≥0) : ℝ≥0∞))
              * (improvWeight c ρ L N : ℝ≥0∞) * eLpNorm u 2 Measure.count
              * eLpNorm v 2 Measure.count := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst (by positivity))
            (by positivity)) (by positivity)


/-- **The gain estimate for the second minor-arc part.** -/
theorem gainEndpoint₂ {P : ℤ[X]} (hImp : ImprovKMT P) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) {L : ℕ} {K K₂ : ℤ} {d : ℕ} (hd : d = P.natDegree)
    (hLK₂ : K₂ = -((d : ℤ) * logN N) + (d : ℤ) * (L : ℤ)) (hL : 1 ≤ L)
    (h₀ : ∀ w : ℤ → ℂ, BoundedZ w →
      kmtProj ρ (L - 1) (K₂ - (d : ℤ)) (w - kmtProj ρ L K₂ w) = 0)
    {C₁ : ℝ≥0} (hC₁ : 0 < C₁)
    (hproj₁ : ∀ u : ℤ → ℂ, eLpNorm (kmtProj ρ L K u) 2 Measure.count
        ≤ (C₁ : ℝ≥0∞) * eLpNorm u 2 Measure.count)
    {C₂ : ℝ≥0} (hproj₂ : ∀ v : ℤ → ℂ, eLpNorm (kmtProj ρ L K₂ v) 2 Measure.count
        ≤ (C₂ : ℝ≥0∞) * eLpNorm v 2 Measure.count) :
    ∃ (c : ℝ) (Cg : ℝ≥0), 0 < c ∧ 0 < Cg ∧ ∀ u v : ℤ → ℂ,
      eLpNorm (minorArc₂ ρ L K K₂ (N : ℝ≥0) P u v) 1 Measure.count
        ≤ (Cg : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
            * eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count := by
  obtain ⟨c, hc, hCrho⟩ := hImp
  obtain ⟨C₀imp, hbound⟩ := hCrho ρ hρ0 hρ1
  have hWpos : (0 : ℝ≥0) < improvWeight c ρ L N := improvWeight_pos c ρ L N
  refine ⟨c, C₁ * ((C₀imp + 1) * ((1 : ℝ≥0) + C₂)), hc, mul_pos hC₁ (by positivity), ?_⟩
  have hMne : (((C₁ * ((C₀imp + 1) * ((1 : ℝ≥0) + C₂)) : ℝ≥0)) : ℝ≥0∞)
      * (improvWeight c ρ L N : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨by simp [hC₁.ne'], ENNReal.coe_ne_zero.mpr hWpos.ne'⟩
  refine endpoint_trivial (fun u v => minorArc₂ ρ L K K₂ (N : ℝ≥0) P u v)
    (p := 2) (q := 2) (r := 1)
    (M := ((C₁ * ((C₀imp + 1) * ((1 : ℝ≥0) + C₂)) : ℝ≥0) : ℝ≥0∞)
      * (improvWeight c ρ L N : ℝ≥0∞))
    hMne (by norm_num) (by norm_num)
    (by intro v; exact minorArc₂_zero_left ρ L K K₂ (N : ℝ≥0) P v)
    (by intro u; exact minorArc₂_zero_right ρ L K K₂ (N : ℝ≥0) P u) ?_
  intro u v hu hv
  have hmu : MemLp u 2 Measure.count :=
    MeasureTheory.memLp_iff.mpr hu
  have hmv : MemLp v 2 Measure.count :=
    MeasureTheory.memLp_iff.mpr hv
  have hPmem : MemLp (kmtProj ρ L K u) 2 Measure.count :=
    MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt (hproj₁ u) (ENNReal.mul_lt_top ENNReal.coe_lt_top hu))
  have hQmem : MemLp (kmtProj ρ L K₂ v) 2 Measure.count :=
    MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt (hproj₂ v) (ENNReal.mul_lt_top ENNReal.coe_lt_top hv))
  have hvsub : MemLp (v - kmtProj ρ L K₂ v) 2 Measure.count := hmv.sub hQmem
  have hvsubbdd : BoundedZ (v - kmtProj ρ L K₂ v) :=
    boundedZ_sub (boundedZ_of_memLp (by norm_num) hmv) (boundedZ_of_memLp (by norm_num) hQmem)
  have hdcast : (d : ℤ) = (P.natDegree : ℤ) := by rw [hd]
  have hzero : kmtProj ρ (L - 1) ((P.natDegree : ℤ) * (-(logN N) + ((L - 1 : ℕ) : ℤ)))
      (v - kmtProj ρ L K₂ v) = 0 := by
    have hcast : ((L - 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by
      push_cast [Nat.cast_sub hL]
      ring
    have : ((P.natDegree : ℤ) * (-(logN N) + ((L - 1 : ℕ) : ℤ))) = K₂ - (d : ℤ) := by
      rw [hcast, hLK₂, hd]
      ring
    rw [this]
    exact h₀ v (boundedZ_of_memLp (by norm_num) hmv)
  have hgain := hbound N (L - 1) (kmtProj ρ L K u) (v - kmtProj ρ L K₂ v) hN hPmem hvsub
    (Or.inr hzero)
  have hW : ((2 : ℝ) ^ (-(c * ((L : ℝ) - 1))) + ((logN N : ℝ)) ^ (-(c / ρ)))
      = ((2 : ℝ) ^ (-(c * (((L - 1 : ℕ) : ℝ)))) + ((logN N : ℝ)) ^ (-(c / ρ))) := by
    have hcast : (((L - 1 : ℕ) : ℝ)) = (L : ℝ) - 1 := by
      push_cast [Nat.cast_sub hL]
      ring
    rw [hcast]
  have hQsub : eLpNorm (v - kmtProj ρ L K₂ v) 2 Measure.count
      ≤ ((((1 : ℝ≥0) + C₂) : ℝ≥0) : ℝ≥0∞) * eLpNorm v 2 Measure.count := by
    refine (eLpNorm_sub_le
      (show (1 : ℝ≥0∞) ≤ 2 by norm_num)).trans ?_
    calc eLpNorm v 2 Measure.count + eLpNorm (kmtProj ρ L K₂ v) 2 Measure.count
        ≤ eLpNorm v 2 Measure.count + (C₂ : ℝ≥0∞) * eLpNorm v 2 Measure.count :=
          add_le_add_right (hproj₂ v) _
      _ = (((1 : ℝ≥0) + C₂ : ℝ≥0) : ℝ≥0∞) * eLpNorm v 2 Measure.count := by
          push_cast
          ring
  have hgain' : eLpNorm (AhalfR TZ (N : ℝ≥0) X P (kmtProj ρ L K u)
        (v - kmtProj ρ L K₂ v)) 1 Measure.count
      ≤ (C₀imp : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
          * eLpNorm (kmtProj ρ L K u) 2 Measure.count
          * eLpNorm (v - kmtProj ρ L K₂ v) 2 Measure.count := by
    rw [improvWeight_coe c ρ L N, hW]
    exact hgain
  refine hgain'.trans ?_
  calc (C₀imp : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
        * eLpNorm (kmtProj ρ L K u) 2 Measure.count
        * eLpNorm (v - kmtProj ρ L K₂ v) 2 Measure.count
      ≤ (C₀imp : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
        * ((C₁ : ℝ≥0∞) * eLpNorm u 2 Measure.count)
        * (((((1 : ℝ≥0) + C₂) : ℝ≥0) : ℝ≥0∞) * eLpNorm v 2 Measure.count) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hproj₁ u) (by positivity)) hQsub (by positivity)
          (by positivity)
    _ ≤ (((C₁ * ((C₀imp + 1) * ((1 : ℝ≥0) + C₂)) : ℝ≥0)) : ℝ≥0∞)
        * (improvWeight c ρ L N : ℝ≥0∞) * eLpNorm u 2 Measure.count
        * eLpNorm v 2 Measure.count := by
        rw [show (C₀imp : ℝ≥0∞) * (improvWeight c ρ L N : ℝ≥0∞)
              * ((C₁ : ℝ≥0∞) * eLpNorm u 2 Measure.count)
              * (((((1 : ℝ≥0) + C₂) : ℝ≥0) : ℝ≥0∞) * eLpNorm v 2 Measure.count)
            = (C₁ : ℝ≥0∞) * ((C₀imp : ℝ≥0∞) * ((((1 : ℝ≥0) + C₂) : ℝ≥0) : ℝ≥0∞))
              * (improvWeight c ρ L N : ℝ≥0∞) * eLpNorm u 2 Measure.count
              * eLpNorm v 2 Measure.count from by ring]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right ?_ (by positivity)) (by positivity)) (by positivity)
        rw [← ENNReal.coe_mul, ← ENNReal.coe_mul]
        refine ENNReal.coe_le_coe.mpr ?_
        show C₁ * (C₀imp * ((1 : ℝ≥0) + C₂)) ≤ C₁ * ((C₀imp + 1) * ((1 : ℝ≥0) + C₂))
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by simp) (by positivity)) (by positivity)

end

end Work.KMTAreas.A5
