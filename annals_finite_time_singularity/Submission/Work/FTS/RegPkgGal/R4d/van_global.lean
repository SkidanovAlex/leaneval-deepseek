/-
# `Work.FTS.RegPkgGal.R4d.van_global`

**R4d**: the class lemma `R4c.van_global` with the smoothness hypothesis put where the route can
actually supply it.  `R4c` assumes the slices `θ ↦ g z θ τ` to be `C¹` on an *open strip*
`(-1, π/2+1) ∋ [0,π/2]`, which is what makes the two boundary values `VanishTheta` the *limits* of
the slices.  Here the smoothness is only assumed on the **open quadrant**
`(0,∞) × (0,π/2)`, and the two endpoint limits are supplied as *hypotheses*
(`hcont0`, `hcontπ`: the one-sided continuity of every slice at `θ = 0⁺` and `θ = (π/2)⁻`), with
`hquad0` recording the vanishing of the profile at `z = 0`.  The conclusion is the same:

  `∃ Cv ≥ 0, ∀ τ ∈ [0,S], ∀ z ≥ 0, ∀ θ ∈ Iθ, |g z θ τ| ≤ Cv·Γ(θ)`.

## Proof

Exactly the argument of `R4c.van_global`, with the slice calculus redone for the finer hypotheses.

1. **The angular FTC with a one-sided endpoint** (`abs_sub_le_integral_of_continuousOn`): if `u` is
   continuous on `[a,b]`, differentiable on `(a,b)` with `‖u'‖ ≤ maj` there, and `maj` is interval
   integrable, then `|u b - u a| ≤ ∫_a^b maj`.  This replaces `R4b.slice_ftc_abs_le`, which needed
   differentiability *at* the endpoints; the proof uses the measure-theoretic FTC
   `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le` (continuity on the closed interval,
   differentiability off a countable set).
   The continuity on `[a,b]` is assembled from the interior differentiability (which the quadrant
   smoothness supplies) and the two boundary limits (`continuousWithinAt_Icc_of_tendsto_nhdsGT/LT`,
   feeding in `hcont0`/`hcontπ` via `continuousOn_Icc_of_interior`).
2. **The analytic core** (`van_zsq_weak`): the boundary rates `primBoundLeft`/`primBoundRight` of
   `Γ/sin(2θ)` turn the class bound into `|g z θ τ| ≤ K·z²·Γ(θ)` with `K` uniform in `(z,θ,τ)`;
   the `z²` factor is kept, which is why the bound is valid on the whole half-line.  The cases
   `z = 0` (`hquad0`) and `θ ∈ {0, π/2}` (`hvt`) are degenerate and immediate.
3. **Gluing** with the far-field bound `hfar` (`R4c.van_global_of_zsq`): below `Lz` use the
   `z²`-bound and `z² ≤ Lz²`, above `Lz` use `hfar`; `Cv := max (K·Lz²) Lz`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.RegPkgGal.R4b.van_of_dthvan
import Submission.Work.FTS.RegPkgGal.R4c.van_global

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal.R4d

set_option autoImplicit false

/-! ## The slice calculus for the weaker smoothness hypothesis -/

/-- **Continuity of a slice at the left endpoint of `[a,b]`**, from the one-sided limit at `a`
from the right.  (`hcont0` of the statement is exactly such a limit.)  The proof splits
`𝓝[Ici a] a = 𝓝[Ioi a] a ⊔ pure a`: the first component is the hypothesis, the second is trivial
because `u` is *evaluated* at `a`. -/
lemma continuousWithinAt_Icc_of_tendsto_nhdsGT {u : ℝ → ℝ} {a b : ℝ}
    (ha : Tendsto u (𝓝[>] a) (𝓝 (u a))) : ContinuousWithinAt u (Set.Icc a b) a := by
  have hIci : ContinuousWithinAt u (Set.Ici a) a := by
    rw [ContinuousWithinAt, ← Set.Ioi_union_left, nhdsWithin_union, nhdsWithin_singleton,
        Filter.tendsto_sup]
    exact ⟨ha, tendsto_pure_nhds u a⟩
  exact hIci.mono_of_mem_nhdsWithin
    (Filter.mem_of_superset self_mem_nhdsWithin Set.Icc_subset_Ici_self)

/-- **Continuity of a slice at the right endpoint of `[a,b]`**, from the one-sided limit at `b`
from the left (the `hcontπ` of the statement). -/
lemma continuousWithinAt_Icc_of_tendsto_nhdsLT {u : ℝ → ℝ} {a b : ℝ}
    (hb : Tendsto u (𝓝[<] b) (𝓝 (u b))) : ContinuousWithinAt u (Set.Icc a b) b := by
  have hIic : ContinuousWithinAt u (Set.Iic b) b := by
    rw [ContinuousWithinAt, ← Set.Iio_union_right, nhdsWithin_union, nhdsWithin_singleton,
        Filter.tendsto_sup]
    exact ⟨hb, tendsto_pure_nhds u b⟩
  exact hIic.mono_of_mem_nhdsWithin
    (Filter.mem_of_superset self_mem_nhdsWithin Set.Icc_subset_Iic_self)

/-- **Continuity on `[a,b]`** from continuity at the two endpoints within `[a,b]` and at the
interior points. -/
lemma continuousOn_Icc_of_interior {u : ℝ → ℝ} {a b : ℝ}
    (hint : ∀ x ∈ Set.Ioo a b, ContinuousAt u x)
    (ha : ContinuousWithinAt u (Set.Icc a b) a)
    (hb : ContinuousWithinAt u (Set.Icc a b) b) :
    ContinuousOn u (Set.Icc a b) := by
  intro x hx
  rcases lt_or_eq_of_le hx.1 with hlt | rfl
  · rcases lt_or_eq_of_le hx.2 with hlt2 | rfl
    · exact (hint x ⟨hlt, hlt2⟩).continuousWithinAt
    · exact hb
  · exact ha

/-- **The angular fundamental theorem of calculus with a one-sided endpoint.**  If `u` is
continuous on `[a,b]` and differentiable on `(a,b)` with `‖u'‖ ≤ maj` there, `maj` being interval
integrable, then `|u b - u a| ≤ ∫_a^b maj`.  Unlike `R4b.slice_ftc_abs_le` this needs no
differentiability *at* the endpoints, so it applies to a slice that is only `C¹` on the open
quadrant and merely *continuous* up to `θ = 0` and `θ = π/2`. -/
lemma abs_sub_le_integral_of_continuousOn {u u' maj : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn u (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt u (u' x) x)
    (hmaj_int : IntervalIntegrable maj volume a b)
    (hmaj : ∀ x ∈ Set.Ioo a b, ‖u' x‖ ≤ maj x) :
    |u b - u a| ≤ ∫ x in a..b, maj x := by
  have hb' : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b := by
    rw [MeasureTheory.ae_iff]
    simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
    exact MeasureTheory.measure_singleton _
  have hae' : ∀ᵐ x ∂(volume.restrict (Set.Ioc a b)), deriv u x = u' x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hb'] with x hxb hx
    exact (hderiv x ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩).deriv
  have hae : ∀ᵐ x ∂(volume.restrict (Set.Ioc a b)), ‖u' x‖ ≤ maj x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hb'] with x hxb hx
    exact hmaj x ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩
  have hmeas : AEStronglyMeasurable u' (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab]
    exact (measurable_deriv u).aestronglyMeasurable.congr hae'
  have hint : IntervalIntegrable u' volume a b := by
    refine IntervalIntegrable.mono_fun' hmaj_int hmeas ?_
    rw [Set.uIoc_of_le hab]
    exact hae
  have hftc : ∫ x in a..b, u' x = u b - u a := by
    refine MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le u u' hab
      Set.countable_empty hc ?_ hint
    intro x hx
    exact hderiv x (by simpa using hx.1)
  have hle : ∫ x in a..b, ‖u' x‖ ≤ ∫ x in a..b, maj x := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    refine MeasureTheory.integral_mono_ae ?_ ?_ hae
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint.norm
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hmaj_int
  calc |u b - u a| = ‖∫ x in a..b, u' x‖ := by rw [hftc, Real.norm_eq_abs]
    _ ≤ ∫ x in a..b, ‖u' x‖ := intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ x in a..b, maj x := hle

/-! ## The analytic core: `|g| ≤ K·z²·Γ` on the whole half-line -/

/-- **The analytic core of R4d.**  From the `Γ`-bound on `D_θg`, the vanishing on the two angular
boundary lines, the one-sided continuity at the endpoints of the slices and the vanishing at
`z = 0`, the profile is dominated by `K·z²·Γ(θ)` on the whole half-line `z ≥ 0`, uniformly in
`τ ∈ [0,S]`.  This is `R4c.van_zsq` with the smoothness hypothesis weakened to the open quadrant
(the endpoint limits being assumed instead). -/
theorem van_zsq_weak {α S Cθ : ℝ} (hα : 0 < α) (hCθ : 0 ≤ Cθ)
    {g : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 S,
      ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hquad0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, g 0 θ τ = 0)
    (hcont0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => g z θ τ) (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (g z 0 τ)))
    (hcontπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => g z θ τ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (g z (Real.pi / 2) τ)))
    (hd : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (Work.FTS.Regularity.gSlice g τ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ K * z ^ 2 * Work.FTS.Regularity.Gamma α θ := by
  obtain ⟨M, hM0, hM⟩ := R4b.primBoundLeft hα
  obtain ⟨N, hN0, hN⟩ := R4b.primBoundRight hα
  set c1 : ℝ := (1 / Real.pi) ^ α with hc1
  set c2 : ℝ := ((Real.sqrt 2 / 2) * (2 / Real.pi) ^ 2) ^ α with hc2
  have hc1pos : 0 < c1 := by rw [hc1]; exact Real.rpow_pos_of_pos (by positivity) _
  have hc2pos : 0 < c2 := by rw [hc2]; exact Real.rpow_pos_of_pos (by positivity) _
  refine ⟨Cθ * max (M / (α * c1)) (N / (2 * α * c2)), ?_, ?_⟩
  · exact mul_nonneg hCθ (le_trans (div_nonneg hM0 (by positivity)) (le_max_left _ _))
  · intro τ hτ z θ hz hθ
    have hzsq : 0 ≤ z ^ 2 := sq_nonneg z
    rcases eq_or_lt_of_le hz with rfl | hzpos
    · rw [hquad0 τ hτ θ hθ]; simp
    rcases lt_or_eq_of_le hθ.1 with hθpos | hθzero
    · rcases lt_or_eq_of_le hθ.2 with hθlt | hθpi2
      · have hzmem : z ∈ Set.Ioi (0:ℝ) := hzpos
        have hslice : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
            HasDerivAt (fun θ' => g z θ' τ)
              (Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x) x :=
          fun x hx => R4b.hasDerivAt_sliceTh isOpen_Ioi isOpen_Ioo (hsm τ hτ) hzmem hx
        rcases le_or_gt θ (Real.pi / 4) with hθle | hθgt
        · -- ## left half: `0 < θ ≤ π/4`, integrate from `0`
          have hθpi2lt : θ < Real.pi / 2 := lt_of_le_of_lt hθle (by linarith [Real.pi_pos])
          have hcontOn : ContinuousOn (fun θ' => g z θ' τ) (Set.Icc 0 θ) := by
            refine continuousOn_Icc_of_interior (fun x hx => ?_)
              (continuousWithinAt_Icc_of_tendsto_nhdsGT (hcont0 τ hτ z hz)) ?_
            · exact (hslice x ⟨hx.1, lt_trans hx.2 hθpi2lt⟩).continuousAt
            · exact (hslice θ ⟨hθpos, hθpi2lt⟩).continuousAt.continuousWithinAt
          have hmaj_int : IntervalIntegrable (fun x : ℝ => Cθ * z ^ 2 * M * x ^ (α - 1))
              volume 0 θ :=
            (intervalIntegral.intervalIntegrable_rpow' (show (-1:ℝ) < α - 1 by linarith)).const_mul _
          have hmaj : ∀ x ∈ Set.Ioo (0:ℝ) θ,
              ‖Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x‖
                ≤ Cθ * z ^ 2 * M * x ^ (α - 1) := by
            intro x hx
            rw [Real.norm_eq_abs]
            exact R4b.pth_le_majorant hCθ (hd τ hτ) hM hz hx.1
              (le_trans (le_of_lt hx.2) hθle)
          have hftc := abs_sub_le_integral_of_continuousOn hθ.1 hcontOn
            (fun x hx => hslice x ⟨hx.1, lt_trans hx.2 hθpi2lt⟩) hmaj_int hmaj
          have hval : ∫ x in (0:ℝ)..θ, Cθ * z ^ 2 * M * x ^ (α - 1)
              = Cθ * z ^ 2 * M * (θ ^ α / α) := by
            rw [intervalIntegral.integral_const_mul,
                integral_rpow (Or.inl (show (-1:ℝ) < α - 1 by linarith)),
                show α - 1 + 1 = α by ring, Real.zero_rpow (ne_of_gt hα), sub_zero]
          have hGam : c1 * θ ^ α ≤ Work.FTS.Regularity.Gamma α θ := by
            rw [hc1]; exact R4b.Gamma_left_lb hα hθpos.le hθle
          have hAc1 : θ ^ α * c1 ≤ Work.FTS.Regularity.Gamma α θ := by
            linarith [hGam, mul_comm c1 (θ ^ α)]
          have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ :=
            Work.ConstructionInstance.Gamma_nonneg hθ
          have hquot : θ ^ α / α ≤ Work.FTS.Regularity.Gamma α θ / (α * c1) := by
            rw [div_le_iff₀ (by linarith : (0:ℝ) < α),
                show Work.FTS.Regularity.Gamma α θ / (α * c1) * α
                  = Work.FTS.Regularity.Gamma α θ * α / (α * c1) by ring,
                le_div_iff₀ (by positivity : (0:ℝ) < α * c1)]
            nlinarith [hAc1, hα, hc1pos]
          have hstep2 : M * (θ ^ α / α)
              ≤ (M / (α * c1)) * Work.FTS.Regularity.Gamma α θ := by
            have h1 := mul_le_mul_of_nonneg_left hquot hM0
            rwa [show M * (Work.FTS.Regularity.Gamma α θ / (α * c1))
                  = (M / (α * c1)) * Work.FTS.Regularity.Gamma α θ by ring] at h1
          have hstep3 : (M / (α * c1)) * Work.FTS.Regularity.Gamma α θ
              ≤ max (M / (α * c1)) (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hΓ0
          calc |g z θ τ| = |g z θ τ - g z 0 τ| := by
                  rw [show g z 0 τ = 0 from (hvt τ hτ).1 z, sub_zero]
            _ ≤ ∫ x in (0:ℝ)..θ, Cθ * z ^ 2 * M * x ^ (α - 1) := hftc
            _ = Cθ * z ^ 2 * M * (θ ^ α / α) := hval
            _ = Cθ * z ^ 2 * (M * (θ ^ α / α)) := by ring
            _ ≤ Cθ * z ^ 2 * ((M / (α * c1)) * Work.FTS.Regularity.Gamma α θ) :=
                  mul_le_mul_of_nonneg_left hstep2 (mul_nonneg hCθ hzsq)
            _ ≤ Cθ * z ^ 2 * (max (M / (α * c1)) (N / (2 * α * c2))
                  * Work.FTS.Regularity.Gamma α θ) :=
                  mul_le_mul_of_nonneg_left hstep3 (mul_nonneg hCθ hzsq)
            _ = Cθ * max (M / (α * c1)) (N / (2 * α * c2)) * z ^ 2
                  * Work.FTS.Regularity.Gamma α θ := by ring
        · -- ## right half: `π/4 < θ < π/2`, integrate up to `π/2`
          have hθpi2le : θ ≤ Real.pi / 2 := hθ.2
          have hcontOn : ContinuousOn (fun θ' => g z θ' τ) (Set.Icc θ (Real.pi / 2)) := by
            refine continuousOn_Icc_of_interior (fun x hx => ?_)
              ((hslice θ ⟨hθpos, hθlt⟩).continuousAt.continuousWithinAt)
              (continuousWithinAt_Icc_of_tendsto_nhdsLT (hcontπ τ hτ z hz))
            exact (hslice x ⟨lt_trans hθpos hx.1, hx.2⟩).continuousAt
          have hbase : IntervalIntegrable (fun x : ℝ => x ^ (2 * α - 1)) volume 0
              (Real.pi / 2 - θ) :=
            intervalIntegral.intervalIntegrable_rpow' (show (-1:ℝ) < 2 * α - 1 by linarith)
          have hcomp : IntervalIntegrable (fun x : ℝ => (Real.pi / 2 - x) ^ (2 * α - 1))
              volume (Real.pi / 2) θ := by
            have h' := hbase.comp_sub_left (Real.pi / 2)
            rw [sub_zero, show Real.pi / 2 - (Real.pi / 2 - θ) = θ by ring] at h'
            exact h'
          have hmaj_int : IntervalIntegrable
              (fun x : ℝ => Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1))
              volume θ (Real.pi / 2) :=
            (hcomp.symm).const_mul _
          have hmaj : ∀ x ∈ Set.Ioo θ (Real.pi / 2),
              ‖Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x‖
                ≤ Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1) := by
            intro x hx
            rw [Real.norm_eq_abs]
            exact R4b.pth_le_majorant_right hCθ (hd τ hτ) hN hz
              (le_of_lt (lt_trans hθgt hx.1)) hx.2
          have hftc := abs_sub_le_integral_of_continuousOn hθpi2le hcontOn
            (fun x hx => hslice x ⟨lt_trans hθpos hx.1, hx.2⟩) hmaj_int hmaj
          have hval : ∫ x in θ..(Real.pi / 2), Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1)
              = Cθ * z ^ 2 * N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α)) := by
            rw [intervalIntegral.integral_const_mul]
            congr 1
            rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ => s ^ (2 * α - 1))
                  (Real.pi / 2),
                show Real.pi / 2 - Real.pi / 2 = 0 by ring,
                integral_rpow (Or.inl (show (-1:ℝ) < 2 * α - 1 by linarith)),
                show 2 * α - 1 + 1 = 2 * α by ring,
                Real.zero_rpow (by linarith : 2 * α ≠ 0), sub_zero]
          have hσ0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθpi2le]
          have hσle : Real.pi / 2 - θ ≤ Real.pi / 4 := by linarith [hθgt]
          have hGam : c2 * (Real.pi / 2 - θ) ^ (2 * α) ≤ Work.FTS.Regularity.Gamma α θ := by
            have h := R4b.Gamma_right_lb hα hσ0 hσle
            rwa [show Real.pi / 2 - (Real.pi / 2 - θ) = θ by ring] at h
          have hAc2 : (Real.pi / 2 - θ) ^ (2 * α) * c2 ≤ Work.FTS.Regularity.Gamma α θ := by
            linarith [hGam, mul_comm c2 ((Real.pi / 2 - θ) ^ (2 * α))]
          have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ :=
            Work.ConstructionInstance.Gamma_nonneg hθ
          have hquot : (Real.pi / 2 - θ) ^ (2 * α) / (2 * α)
              ≤ Work.FTS.Regularity.Gamma α θ / (2 * α * c2) := by
            rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * α),
                show Work.FTS.Regularity.Gamma α θ / (2 * α * c2) * (2 * α)
                  = Work.FTS.Regularity.Gamma α θ * (2 * α) / (2 * α * c2) by ring,
                le_div_iff₀ (by positivity : (0:ℝ) < 2 * α * c2)]
            nlinarith [hAc2, hα, hc2pos]
          have hstep2 : N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α))
              ≤ (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ := by
            have h1 := mul_le_mul_of_nonneg_left hquot hN0
            rwa [show N * (Work.FTS.Regularity.Gamma α θ / (2 * α * c2))
                  = (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ by ring] at h1
          have hstep3 : (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ
              ≤ max (M / (α * c1)) (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hΓ0
          calc |g z θ τ| = |g z (Real.pi / 2) τ - g z θ τ| := by
                  rw [show g z (Real.pi / 2) τ = 0 from (hvt τ hτ).2 z, zero_sub, abs_neg]
            _ ≤ ∫ x in θ..(Real.pi / 2), Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1) := hftc
            _ = Cθ * z ^ 2 * N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α)) := hval
            _ = Cθ * z ^ 2 * (N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α))) := by ring
            _ ≤ Cθ * z ^ 2 * ((N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ) :=
                  mul_le_mul_of_nonneg_left hstep2 (mul_nonneg hCθ hzsq)
            _ ≤ Cθ * z ^ 2 * (max (M / (α * c1)) (N / (2 * α * c2))
                  * Work.FTS.Regularity.Gamma α θ) :=
                  mul_le_mul_of_nonneg_left hstep3 (mul_nonneg hCθ hzsq)
            _ = Cθ * max (M / (α * c1)) (N / (2 * α * c2)) * z ^ 2
                  * Work.FTS.Regularity.Gamma α θ := by ring
      · -- ## the degenerate case `θ = π/2`: `Γ(π/2) = 0 = g`
        rw [hθpi2, show g z (Real.pi / 2) τ = 0 from (hvt τ hτ).2 z]
        simp [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma,
          Real.zero_rpow (ne_of_gt hα)]
    · -- ## the degenerate case `θ = 0`: `Γ(0) = 0 = g`
      rw [← hθzero, show g z 0 τ = 0 from (hvt τ hτ).1 z]
      simp [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma,
        Real.zero_rpow (ne_of_gt hα)]

/-! ## R4d -/

/-- **The class lemma R4d.**  On a strip `τ ∈ [0,S]`, a family `g` whose angular derivative
satisfies the `Γ`-bound `|D_θ g| = |sin(2θ)∂_θ g| ≤ Cθ·z²·Γ(θ)`, which vanishes on the two angular
boundary lines (`VanishTheta`) *and* has continuous slices up to those lines (`hcont0`, `hcontπ`),
and which satisfies the far-field bound `|g z θ τ| ≤ Lz·Γ(θ)` for `z ≥ Lz`, is dominated by `Γ` on
the whole half-line `z ≥ 0`. -/
theorem van_global {α S Cθ Lz : ℝ} (hα : 0 < α) (hS : 0 < S) (hCθ : 0 ≤ Cθ) (hLz : 0 ≤ Lz)
    {g : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 S,
      ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hquad0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, g 0 θ τ = 0)
    (hcont0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => g z θ τ) (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (g z 0 τ)))
    (hcontπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => g z θ τ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (g z (Real.pi / 2) τ)))
    (hd : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (Work.FTS.Regularity.gSlice g τ))
    (hfar : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lz ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Lz * Work.FTS.Regularity.Gamma α θ) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Cv * Work.FTS.Regularity.Gamma α θ := by
  obtain ⟨K, hK0, hzsq⟩ := van_zsq_weak hα hCθ hsm hquad0 hcont0 hcontπ hd hvt
  exact R4c.van_global_of_zsq hLz hK0 hzsq hfar

end Work.FTS.RegPkgGal.R4d
