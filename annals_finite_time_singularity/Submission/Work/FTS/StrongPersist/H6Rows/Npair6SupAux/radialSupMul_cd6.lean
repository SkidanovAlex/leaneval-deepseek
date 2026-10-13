/-
# `radialSupMul_cd6` — a bounded radial multiplier costs only its sup bound in `ℋ⁶`

The level-six multiplicativity of the weighted `ℋ⁶`-norm under multiplication by a
`z`-only (radial) factor `z ↦ a z` all of whose `D_z = z ∂_z` iterates up to order six are
bounded a.e. (by a constant `K`).

The route is the "lossless radial product": `D_z` is a derivation, so
`D_z^j (a·g) = Σ_b C(j,b) (D_z^b a)(D_z^{j-b} g)`, and `D_θ` kills the radial factor, so
every `D_θ`-derivative lands on `g`.  Consequently each slot of `HkIntegrand α 6 (a·g)` is a
Cauchy–Schwarz combination of slots of `HkIntegrand α 6 g`, with the scalar contributions
`|D_z^b a| ≤ K` pulled out.  This is the pointwise majorant
`HkIntegrand α 6 (a·g) z θ ≤ C₀ K² HkIntegrand α 6 g z θ`
(`RadAux.radialHkIntegrand_majorant_cd6`, with the two Leibniz identities
`RadAux.leibniz_rad_Dz_cd6`, `RadAux.leibniz_rad_mixed_cd6` supplied separately), which is
then transported through `Work.Blocks.HkMem_of_majorant_aesm`.

The a.e. hypothesis on the `D_z`-iterates of `a` is upgraded to a *pointwise* bound for
`z > 0` by continuity (an a.e. bound for a function continuous on the open half-line holds
everywhere there, since the set where it fails would be open and nonempty, hence of positive
measure).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.Cd6Basic
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.zslot_le_winf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_Dz_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_mixed_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.radialHkIntegrand_majorant_cd6
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Blocks.HkMem_of_majorant_aesm
import Submission.Work.Blocks.HalfInfra
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## Elementary auxiliary facts -/

/-- `gam α = 1 + α/10` does not vanish for `α > 0`. -/
private theorem gam_ne_zero_of_pos {α : ℝ} (hα : 0 < α) : Work.Spaces.gam α ≠ 0 := by
  rw [Work.Spaces.gam]; intro h; linarith

/-- The level-six `ℋ⁶`-integrand vanishes whenever `sin(2θ) = 0` (assuming `gam α ≠ 0`). -/
private theorem HkIntegrand6_eq_zero_of_sin_two_eq_zero {α : ℝ}
    (hgam : Work.Spaces.gam α ≠ 0) {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α 6 F z θ = 0 := by
  have hη : (Work.Spaces.eta / 2 : ℝ) ≠ 0 := by norm_num [Work.Spaces.eta]
  have hg : -(Work.Spaces.gam α / 2) ≠ 0 := by
    intro hc; exact hgam (by linarith [neg_eq_zero.mp hc])
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [h, Real.zero_rpow hη, Real.zero_rpow hg]
  simp

/-- For a radial `C^6` datum `a`, the one-variable iterate `DzdIter b a` is `C^{6-b}` on the
open half-line `(0,∞)`, hence in particular continuous there. -/
private theorem contDiffOn_DzdIter_query {a : ℝ → ℝ}
    (hacd : ContDiffOn ℝ 6 (Function.uncurry (fun z (_ : ℝ) => a z)) Work.FTS.EllipticEst.Q0)
    {b : ℕ} (hb : b ≤ 6) : ContDiffOn ℝ (6 - b) (Work.Elliptic.DzdIter b a) (Set.Ioi 0) := by
  have h2 : ContDiffOn ℝ (6 - b)
      (Function.uncurry (Work.Spaces.DzIter b (fun z (_ : ℝ) => a z)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.contDiffOn_uncurry_DzIter_aux
      (M := 6) hacd b (6 - b) (by omega)
  have hmaps : Set.MapsTo (fun z : ℝ => (z, (1 : ℝ))) (Set.Ioi 0) Work.FTS.EllipticEst.Q0 :=
    fun z hz => ⟨hz, by norm_num, by linarith [Real.pi_gt_three]⟩
  have hc : ContDiffOn ℝ (6 - b) (fun z : ℝ => (z, (1 : ℝ))) (Set.Ioi 0) :=
    contDiffOn_id.prodMk contDiffOn_const
  have h3 : ContDiffOn ℝ (6 - b)
      (fun z : ℝ => Work.Spaces.DzIter b (fun z (_ : ℝ) => a z) z 1) (Set.Ioi 0) :=
    (h2.comp hc hmaps).congr (fun z _ => rfl)
  exact h3.congr (fun z _ => (Work.Elliptic.DzIter_rad a b z 1).symm)

/-- **The a.e. `D_z`-bounds upgrade to pointwise bounds on `(0,∞)`.**  A function that is
continuous on the open half-line and bounded almost everywhere there is bounded everywhere:
the set where the bound fails is open and lies inside a null set, hence is empty. -/
private theorem dzdIter_bound_everywhere {a : ℝ → ℝ} {K : ℝ}
    (hacd : ContDiffOn ℝ 6 (Function.uncurry (fun z (_ : ℝ) => a z)) Work.FTS.EllipticEst.Q0)
    (haeb : ∀ b : ℕ, b ≤ 6 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      |Work.Elliptic.DzdIter b a z| ≤ K) :
    ∀ b : ℕ, b ≤ 6 → ∀ z : ℝ, 0 < z → |Work.Elliptic.DzdIter b a z| ≤ K := by
  intro b hb z hzpos
  by_contra hle
  have hK : K < |Work.Elliptic.DzdIter b a z| := not_le.mp hle
  have hcont : ContinuousOn (Work.Elliptic.DzdIter b a) (Set.Ioi 0) :=
    (contDiffOn_DzdIter_query hacd hb).continuousOn
  have hae : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), y ∈ Work.Spaces.Iz →
      |Work.Elliptic.DzdIter b a y| ≤ K :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp (haeb b hb)
  have hca : ContinuousAt (fun y : ℝ => |Work.Elliptic.DzdIter b a y|) z :=
    (hcont.continuousAt (isOpen_Ioi.mem_nhds hzpos)).abs
  have hpre : {y : ℝ | K < |Work.Elliptic.DzdIter b a y|} ∈ 𝓝 z :=
    hca.preimage_mem_nhds (isOpen_Ioi.mem_nhds hK)
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem hpre (isOpen_Ioi.mem_nhds hzpos))
  have hnull : MeasureTheory.volume
      {y : ℝ | ¬ (y ∈ Work.Spaces.Iz → |Work.Elliptic.DzdIter b a y| ≤ K)} = 0 :=
    MeasureTheory.ae_iff.mp hae
  have hsub : Metric.ball z ε ⊆
      {y : ℝ | ¬ (y ∈ Work.Spaces.Iz → |Work.Elliptic.DzdIter b a y| ≤ K)} := by
    intro y hy
    have hyK : K < |Work.Elliptic.DzdIter b a y| := (hball hy).1
    have hy0 : (0 : ℝ) < y := (hball hy).2
    intro hcon
    exact absurd (hcon (le_of_lt hy0)) (not_le.mpr hyK)
  have hzero : MeasureTheory.volume (Metric.ball z ε) = 0 :=
    le_antisymm (le_trans (MeasureTheory.measure_mono hsub) (le_of_eq hnull)) bot_le
  rw [Real.volume_ball] at hzero
  have hne : ENNReal.ofReal (2 * ε) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; positivity
  exact hne hzero

/-! ## The main theorem -/

theorem radialSupMul_cd6 : ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {a : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {K : ℝ},
    0 < α → α ≤ 1 → 0 ≤ K →
    ContDiffOn ℝ 6 (Function.uncurry (fun z (_ : ℝ) => a z)) Work.FTS.EllipticEst.Q0 →
    ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
    (∀ j : ℕ, j ≤ 6 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z (_ : ℝ) => a z) z θ| ≤ K) →
    Work.Spaces.HkMem α 6 g →
    ContDiffOn ℝ 6 (Function.uncurry (fun z θ => a z * g z θ)) Work.FTS.EllipticEst.Q0 ∧
      Work.Spaces.HkMem α 6 (fun z θ => a z * g z θ) ∧
      Work.Spaces.HkNorm α 6 (fun z θ => a z * g z θ) ≤ C * K * Work.Spaces.HkNorm α 6 g := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.radialHkIntegrand_majorant_cd6
  refine ⟨Real.sqrt C₀ + 1, by linarith [Real.sqrt_nonneg C₀], ?_⟩
  intro α a g K hα hα1 hK hacd hgcd hKj hgm
  -- the a.e. slot bounds for the radial datum
  have haeb : ∀ b : ℕ, b ≤ 6 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      |Work.Elliptic.DzdIter b a z| ≤ K := by
    intro b hb
    filter_upwards [hKj b hb] with z hz
    simpa [Work.Elliptic.DzIter_rad] using hz 0
  -- the same bounds at every `z > 0`
  have heverywhere := dzdIter_bound_everywhere hacd haeb
  -- the pointwise majorant of the child lemma, with the two Leibniz identities supplied
  have hmaj : ∀ {K' : ℝ} {z θ : ℝ}, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (∀ b : ℕ, b ≤ 6 → |Work.Elliptic.DzdIter b a z| ≤ K') →
      Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) z θ
        ≤ C₀ * K' ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
    intro K' z θ hz hθ0 hθ1 hbnd
    exact hC₀ (α := α) (K := K') (r := a) (g := g)
      (fun z θ hz hθ0 hθ1 j hj =>
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_Dz_cd6
          hacd hgcd hj z θ hz hθ0 hθ1)
      (fun z θ hz hθ0 hθ1 j i hi hij =>
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_mixed_cd6
          hacd hgcd hi hij z θ hz hθ0 hθ1)
      hz hθ0 hθ1 hbnd
  -- the pointwise majorant on the whole closed quadrant
  have hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) z θ
        ≤ (C₀ * K ^ 2) * Work.Spaces.HkIntegrand α 6 g z θ := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
    · have hz0 : z = 0 := hzz.symm
      subst hz0
      simp
    · by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
      · exact hmaj hzpos hθi.1 hθi.2 (fun b hb => heverywhere b hb z hzpos)
      · have hθc : θ = 0 ∨ θ = Real.pi / 2 := by
          rcases lt_or_ge (0 : ℝ) θ with h | h
          · right; exact le_antisymm hθ.2 (le_of_not_gt fun h' => hθi ⟨h, h'⟩)
          · left; exact le_antisymm h hθ.1
        have hsin : Real.sin (2 * θ) = 0 := by
          rcases hθc with h0 | hπ
          · rw [h0]; simp
          · rw [hπ, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        rw [HkIntegrand6_eq_zero_of_sin_two_eq_zero (gam_ne_zero_of_pos hα) hsin,
          HkIntegrand6_eq_zero_of_sin_two_eq_zero (F := g) (gam_ne_zero_of_pos hα) hsin]
        simp
  -- the product is `C^6` on the open quadrant
  have hfg : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => a z * g z θ))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.contDiffOn_uncurry_mul_cd6 hacd hgcd
  -- continuity of the integrand of the product on the open quadrant
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.continuousOn_HkIntegrand_cd6
      (le_refl 6) hfg
  -- a.e. strong measurability of the angular slices
  have hslice : ∀ z ∈ Work.Spaces.Iz, AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
    · have hz0 : z = 0 := hzz.symm
      subst hz0
      have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) 0 θ)
          = fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => Work.Blocks.Half.HkIntegrand_zero_z α 6 _ θ
      rw [hzero]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos
  -- a.e. strong measurability of the `z`-slice integral
  have houter : AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) p.1 p.2)
      hcont).integral_prod_right'
    have hfun : (fun z => ∫ θ, Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) z θ) := rfl
    rw [← hfun]
    exact h
  -- the honest membership
  have hHkMem : Work.Spaces.HkMem α 6 (fun z θ => a z * g z θ) :=
    Work.Blocks.HkMem_of_majorant_aesm α 6
      (M := fun z θ => (C₀ * K ^ 2) * Work.Spaces.HkIntegrand α 6 g z θ)
      hslice houter
      (fun z hz => (hgm.1 z hz).const_mul _)
      (by
        have hfun : (fun z => ∫ θ in Work.Spaces.Iθ,
              (C₀ * K ^ 2) * Work.Spaces.HkIntegrand α 6 g z θ)
            = fun z => (C₀ * K ^ 2) * ∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 6 g z θ :=
          funext fun z => MeasureTheory.integral_const_mul _ _
        rw [hfun]
        exact hgm.2.const_mul _)
      hle
  -- the squared-norm bound
  have hSq : Work.Spaces.HkSq α 6 (fun z θ => a z * g z θ)
      ≤ (C₀ * K ^ 2) * Work.Spaces.HkSq α 6 g := by
    have h1 : Work.Spaces.HkSq α 6 (fun z θ => a z * g z θ)
        ≤ ∫ z in Work.Spaces.Iz,
            (C₀ * K ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ) := by
      rw [Work.Spaces.HkSq]
      refine MeasureTheory.setIntegral_mono_of_nonneg
        (fun z _ => MeasureTheory.integral_nonneg fun θ =>
          Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
        (fun z hz => ?_)
        (hgm.2.const_mul _)
      have h3 := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
        ((hgm.1 z hz).const_mul (C₀ * K ^ 2))
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => hle z hz θ hθ))
      rwa [MeasureTheory.integral_const_mul] at h3
    calc Work.Spaces.HkSq α 6 (fun z θ => a z * g z θ)
        ≤ ∫ z in Work.Spaces.Iz,
            (C₀ * K ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ) := h1
      _ = (C₀ * K ^ 2) * Work.Spaces.HkSq α 6 g := by
          rw [MeasureTheory.integral_const_mul, Work.Spaces.HkSq]
  -- the norm bound
  have hnorm : Work.Spaces.HkNorm α 6 (fun z θ => a z * g z θ)
      ≤ Real.sqrt C₀ * K * Work.Spaces.HkNorm α 6 g := by
    have h1 : Real.sqrt (Work.Spaces.HkSq α 6 (fun z θ => a z * g z θ))
        ≤ Real.sqrt ((C₀ * K ^ 2) * Work.Spaces.HkSq α 6 g) := Real.sqrt_le_sqrt hSq
    have h2 : Real.sqrt ((C₀ * K ^ 2) * Work.Spaces.HkSq α 6 g)
        = Real.sqrt C₀ * K * Real.sqrt (Work.Spaces.HkSq α 6 g) := by
      rw [Real.sqrt_mul (show (0 : ℝ) ≤ C₀ * K ^ 2 by positivity),
        Real.sqrt_mul (le_of_lt hC₀pos), Real.sqrt_sq hK]
    rw [h2] at h1
    simpa only [Work.Spaces.HkNorm] using h1
  refine ⟨hfg, hHkMem, ?_⟩
  calc Work.Spaces.HkNorm α 6 (fun z θ => a z * g z θ)
      ≤ Real.sqrt C₀ * K * Work.Spaces.HkNorm α 6 g := hnorm
    _ ≤ (Real.sqrt C₀ + 1) * K * Work.Spaces.HkNorm α 6 g := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_right (by linarith [Real.sqrt_nonneg C₀]) hK

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
