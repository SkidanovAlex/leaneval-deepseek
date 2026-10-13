/-
Copyright: work module for the Elgindi finite-time singularity project.

# `bump_mixed_EpsSq_le` — the uniform `ε`-bound for the level-`1` mixed slots of `bump`

`BumpEpsSqBound.lean` records the uniform bound for `bump` itself:
`EpsMem α bump` and `EpsSq α bump ≤ 1024` for every `α ∈ (0,1]`.  The linear auxiliary
estimates of the `ε`-scheme (the `L₁₂`-type bounds, the slot bounds with a *derivative* of the
datum) need the same statement for the first-order mixed slots of `bump`,

`mixed j i bump = D_z^j D_θ^i bump`  with  `j + i ≤ 1`,

i.e. for `bump`, `D_z bump = z ∂_z bump` and `D_θ bump = sin(2θ) ∂_θ bump`.

The mechanism is exactly the one that makes the `j = i = 0` case work, and it is concentrated in
the general Lemma `exists_K_epsSq_of_supported` below: **any** function which is `C^∞` on the open
quadrant and vanishes off the fixed compact box `bumpBox = [1/2,1] × [π/4,3π/8]` has

`EpsMem α g` and `EpsSq α g ≤ 1024·(C+1)²` for every `α ∈ (0,1]`,

where `C` is the sup of `|g|` over the box.  On the box the weights are bounded
(`w z ≤ 16`, `sin(2θ)^{γ/2} ≥ 1/2`, hence `epsW α ≤ 32`), the box has volume `π/4 < 1`, and off
the box the integrand vanishes identically.  The three admissible slots are handled by
`SmoothOpen.mixed` (smoothness) together with `bump_iter_eq_zero_of_not_mem` (vanishing).

The constants are deliberately generous; nothing downstream depends on their value.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.EpsSqTools.BumpEpsSqBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSqTools.LinAux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## A function supported on the bump box: membership and the uniform bound -/

/-- The complement of the closed box `[1/2,1] × [π/4,3π/8]`, expressed as a disjunction of
strict inequalities (the shape in which `bump_iter_eq_zero_of_not_mem` consumes it). -/
theorem lt_disj_of_not_mem_bumpBox {z θ : ℝ}
    (h : ¬ (z ∈ Set.Icc ((1 : ℝ) / 2) 1 ∧ θ ∈ Set.Icc (Real.pi / 4) (3 * Real.pi / 8))) :
    z < 1 / 2 ∨ 1 < z ∨ θ < Real.pi / 4 ∨ 3 * Real.pi / 8 < θ := by
  rcases not_and_or.mp h with hz | hθ
  · rcases not_and_or.mp hz with hz | hz
    · exact Or.inl (not_le.mp hz)
    · exact Or.inr (Or.inl (not_le.mp hz))
  · rcases not_and_or.mp hθ with hθ | hθ
    · exact Or.inr (Or.inr (Or.inl (not_le.mp hθ)))
    · exact Or.inr (Or.inr (Or.inr (not_le.mp hθ)))

/-- `epsW` is nonnegative on the support box. -/
theorem epsW_nonneg_of_mem_box {α z θ : ℝ}
    (_hz : z ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hθ : θ ∈ Set.Icc (Real.pi / 4) (3 * Real.pi / 8)) :
    0 ≤ Work.FTS.StrongEps.epsW α z θ := by
  rw [Work.FTS.StrongEps.epsW]
  refine div_nonneg (by rw [Work.Spaces.w]; positivity) ?_
  exact le_of_lt (Real.rpow_pos_of_pos
    (lt_of_lt_of_le (by norm_num) (sin_two_ge_half hθ)) _)

/-- **The general Lemma.**  A function `g` of class `C^∞` on the open quadrant which vanishes
outside the compact box `[1/2,1] × [π/4,3π/8]` lies in the weighted space `X` of the scheme and
has `EpsSq`-size bounded uniformly in `α ∈ (0,1]`.

All the information about `g` that is used is the sup of `|g|` on the box (which is finite by
compactness) and the vanishing. -/
theorem exists_K_epsSq_of_supported {g : ℝ → ℝ → ℝ}
    (hsmooth : Work.FTS.EllipticEst.SmoothOpen g)
    (hzero : ∀ z θ : ℝ,
      ¬ (z ∈ Set.Icc ((1 : ℝ) / 2) 1 ∧ θ ∈ Set.Icc (Real.pi / 4) (3 * Real.pi / 8)) →
      g z θ = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
      Work.FTS.StrongEps.EpsMem α g ∧ Work.FTS.StrongEps.EpsSq α g ≤ K := by
  -- `g` is continuous on the box, hence bounded there.
  have hcontg : ContinuousOn (Function.uncurry g) bumpBox :=
    (ContDiffOn.continuousOn hsmooth).mono box_subset_Q0
  obtain ⟨p₀, -, hp₀max⟩ := isCompact_bumpBox.exists_isMaxOn
    ⟨((1 : ℝ) / 2, Real.pi / 4), by
      rw [bumpBox, Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
      exact ⟨⟨le_rfl, by norm_num⟩, ⟨le_rfl, by linarith [Real.pi_pos]⟩⟩⟩
    hcontg.abs
  set C : ℝ := |g p₀.1 p₀.2| with hC
  have hC0 : 0 ≤ C := abs_nonneg _
  have hCb : ∀ z θ : ℝ, |g z θ| ≤ C + 1 := by
    intro z θ
    by_cases h : (z, θ) ∈ bumpBox
    · have h1 : |g z θ| ≤ C := by rw [hC]; exact hp₀max h
      linarith
    · have h0 : g z θ = 0 := hzero z θ (fun hc => h (by rw [bumpBox]; exact hc))
      rw [h0, abs_zero]; linarith
  refine ⟨1024 * (C + 1) ^ 2, by positivity, fun α hα => ⟨?_, ?_⟩⟩
  · -- membership: the integrand is continuous on the compact box and vanishes outside it
    show MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
    have hcont : ContinuousOn
        (fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) bumpBox :=
      (hcontg.mul (continuousOn_epsW_bumpBox α)).pow 2
    refine (hcont.integrableOn_compact isCompact_bumpBox).of_forall_sdiff_eq_zero
      (measurableSet_Ici.prod measurableSet_Icc) ?_
    rintro ⟨z, θ⟩ ⟨-, hs⟩
    have h0 : g z θ = 0 := hzero z θ (fun hc => hs (by rw [bumpBox]; exact hc))
    rw [h0, zero_mul, sq]
    norm_num
  · -- bound: the pointwise bound `(g · epsW)² ≤ (32(C+1))²`, integrated over the box
    have hIθ_fin : (volume : Measure ℝ) Work.Spaces.Iθ < ⊤ := by
      rw [Work.Spaces.Iθ]; exact isCompact_Icc.measure_lt_top
    have hpt : ∀ z θ : ℝ,
        (g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2 ≤ (32 * (C + 1)) ^ 2 := by
      intro z θ
      by_cases h : (z, θ) ∈ bumpBox
      · rw [bumpBox] at h
        obtain ⟨hz, hθ⟩ := h
        have hg : |g z θ| ≤ C + 1 := hCb z θ
        have he : |Work.FTS.StrongEps.epsW α z θ| ≤ 32 := by
          rw [abs_of_nonneg (epsW_nonneg_of_mem_box hz hθ)]
          exact epsW_le_box hα hz hθ
        have hmul : |g z θ * Work.FTS.StrongEps.epsW α z θ| ≤ 32 * (C + 1) := by
          rw [abs_mul, mul_comm]
          exact mul_le_mul he hg (abs_nonneg _) (by norm_num)
        calc (g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2
            = |g z θ * Work.FTS.StrongEps.epsW α z θ| ^ 2 := by rw [sq_abs]
          _ ≤ (32 * (C + 1)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hmul 2
      · have h0 : g z θ = 0 := hzero z θ (fun hc => h (by rw [bumpBox]; exact hc))
        rw [h0, zero_mul]
        simpa using sq_nonneg (32 * (C + 1))
    have hinner : ∀ z : ℝ, ‖∫ θ in Work.Spaces.Iθ,
        (g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
        ≤ (32 * (C + 1)) ^ 2 * (volume : Measure ℝ).real Work.Spaces.Iθ := by
      intro z
      refine MeasureTheory.norm_setIntegral_le_of_norm_le_const hIθ_fin (fun θ _ => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpt z θ
    have hEq : Work.FTS.StrongEps.EpsSq α g
        = ∫ z in Set.Icc ((1 : ℝ) / 2) 1,
            (∫ θ in Work.Spaces.Iθ, (g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2) := by
      rw [Work.FTS.StrongEps.EpsSq]
      refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        measurableSet_Ici ?_ ?_
      · intro z hz
        rw [Work.Spaces.Iz, Set.mem_Ici]
        linarith [hz.1]
      · rintro z ⟨-, hznot⟩
        have hzlt : z < 1 / 2 ∨ 1 < z := by
          by_contra hc
          push Not at hc
          exact hznot (Set.mem_Icc.mpr ⟨hc.1, hc.2⟩)
        refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun θ _ => ?_)
        have h0 : g z θ = 0 := hzero z θ (fun hc => hznot hc.1)
        rw [h0, zero_mul, sq]
        norm_num
    have hIcc_fin : (volume : Measure ℝ) (Set.Icc ((1 : ℝ) / 2) 1) < ⊤ :=
      isCompact_Icc.measure_lt_top
    have hbd : ‖∫ z in Set.Icc ((1 : ℝ) / 2) 1,
        (∫ θ in Work.Spaces.Iθ, (g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)‖
        ≤ ((32 * (C + 1)) ^ 2 * (volume : Measure ℝ).real Work.Spaces.Iθ)
          * (volume : Measure ℝ).real (Set.Icc ((1 : ℝ) / 2) 1) :=
      MeasureTheory.norm_setIntegral_le_of_norm_le_const hIcc_fin (fun z _ => hinner z)
    have hv1 : (volume : Measure ℝ).real (Set.Icc ((1 : ℝ) / 2) 1) = 1 / 2 := by
      rw [MeasureTheory.measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2)]
      norm_num
    have hv2 : (volume : Measure ℝ).real Work.Spaces.Iθ = Real.pi / 2 := by
      rw [Work.Spaces.Iθ, MeasureTheory.measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - 0)]
      ring
    calc Work.FTS.StrongEps.EpsSq α g
        = ∫ z in Set.Icc ((1 : ℝ) / 2) 1,
            (∫ θ in Work.Spaces.Iθ, (g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2) := hEq
      _ ≤ ‖∫ z in Set.Icc ((1 : ℝ) / 2) 1,
            (∫ θ in Work.Spaces.Iθ, (g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)‖ := by
          simpa only [Real.norm_eq_abs] using le_abs_self
            (∫ z in Set.Icc ((1 : ℝ) / 2) 1,
              (∫ θ in Work.Spaces.Iθ, (g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2))
      _ ≤ ((32 * (C + 1)) ^ 2 * (volume : Measure ℝ).real Work.Spaces.Iθ)
            * (volume : Measure ℝ).real (Set.Icc ((1 : ℝ) / 2) 1) := hbd
      _ = 1024 * (C + 1) ^ 2 * (Real.pi / 4) := by rw [hv1, hv2]; ring
      _ ≤ 1024 * (C + 1) ^ 2 := by
          have h4 : Real.pi / 4 ≤ 1 := by linarith [Real.pi_lt_four]
          have hnn : 0 ≤ 1024 * (C + 1) ^ 2 := by positivity
          calc 1024 * (C + 1) ^ 2 * (Real.pi / 4)
              = (1024 * (C + 1) ^ 2) * (Real.pi / 4) := by ring
            _ ≤ (1024 * (C + 1) ^ 2) * 1 := mul_le_mul_of_nonneg_left h4 hnn
            _ = 1024 * (C + 1) ^ 2 := by ring

/-! ## The three levels of `j + i ≤ 1` -/

/-- The slot `(j,i) = (0,0)`: `bump` itself (this is `BumpEpsSqBound`, in the present normal
form). -/
theorem exists_K_epsSq_bump :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
      Work.FTS.StrongEps.EpsMem α Work.FTS.StrongEps.bump ∧
      Work.FTS.StrongEps.EpsSq α Work.FTS.StrongEps.bump ≤ K :=
  exists_K_epsSq_of_supported Work.FTS.StrongEps.smoothOpen_bump
    (fun _ _ h => bump_eq_zero_of_not_mem_box h)

/-- The slot `(j,i) = (1,0)`: `D_z bump = z ∂_z bump`. -/
theorem exists_K_epsSq_Dz_bump :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
      Work.FTS.StrongEps.EpsMem α (Work.Spaces.Dz Work.FTS.StrongEps.bump) ∧
      Work.FTS.StrongEps.EpsSq α (Work.Spaces.Dz Work.FTS.StrongEps.bump) ≤ K :=
  exists_K_epsSq_of_supported Work.FTS.StrongEps.smoothOpen_bump.Dz
    (fun _ _ h => Work.FTS.StrongEps.bump_iter_eq_zero_of_not_mem
      (lt_disj_of_not_mem_bumpBox h) 1 0)

/-- The slot `(j,i) = (0,1)`: `D_θ bump = sin(2θ) ∂_θ bump`. -/
theorem exists_K_epsSq_Dth_bump :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
      Work.FTS.StrongEps.EpsMem α (Work.Spaces.Dth Work.FTS.StrongEps.bump) ∧
      Work.FTS.StrongEps.EpsSq α (Work.Spaces.Dth Work.FTS.StrongEps.bump) ≤ K :=
  exists_K_epsSq_of_supported Work.FTS.StrongEps.smoothOpen_bump.Dth
    (fun _ _ h => Work.FTS.StrongEps.bump_iter_eq_zero_of_not_mem
      (lt_disj_of_not_mem_bumpBox h) 0 1)

/-! ## The target -/

theorem bump_mixed_EpsSq_le :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ j i : ℕ, j + i ≤ 1 →
      Work.FTS.StrongEps.EpsMem α (Work.Spaces.mixed j i Work.FTS.StrongEps.bump) ∧
      Work.FTS.StrongEps.EpsSq α (Work.Spaces.mixed j i Work.FTS.StrongEps.bump) ≤ K := by
  obtain ⟨K0, hK0, h0⟩ := exists_K_epsSq_bump
  obtain ⟨K1, hK1, h1⟩ := exists_K_epsSq_Dz_bump
  obtain ⟨K2, hK2, h2⟩ := exists_K_epsSq_Dth_bump
  refine ⟨max K0 (max K1 K2), lt_of_lt_of_le hK0 (le_max_left _ _),
    fun α hα j i hji => ?_⟩
  have hcases : (j = 0 ∧ i = 0) ∨ (j = 1 ∧ i = 0) ∨ (j = 0 ∧ i = 1) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨(h0 α hα).1, le_trans (h0 α hα).2 (le_max_left _ _)⟩
  · exact ⟨(h1 α hα).1,
      le_trans (h1 α hα).2 (le_trans (le_max_left _ _) (le_max_right _ _))⟩
  · exact ⟨(h2 α hα).1,
      le_trans (h2 α hα).2 (le_trans (le_max_right _ _) (le_max_right _ _))⟩

end Work.FTS.StrongEps.EpsSqTools.LinAux
