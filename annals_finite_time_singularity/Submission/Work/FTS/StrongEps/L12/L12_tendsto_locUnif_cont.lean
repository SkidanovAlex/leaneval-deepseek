/-
# `L12_tendsto_locUnif_cont`: local uniform convergence of merely *continuous* data

`Work.FTS.StrongEps.L12.L12_tendsto_locUnif_cont`: the `ContinuousOn (uncurry ·) Q0`-form of
`Work.FTS.StrongEps.L12.L12_tendsto_locUnif`.  If `f n → g` uniformly on every compact subset of
the open quadrant `Q0`, the data are *continuous* on `Q0` (not necessarily `C^∞` as in
`SmoothOpen`), of honest weighted class `ℋ⁴` (`HkMem α 4`), and the `ℋ⁴`-sizes are uniformly
bounded by `B`, then for every `z ≥ 0` the `L₁₂`-functionals converge:
`L₁₂ (f n) z → L₁₂ g z`.

This is the form needed at the limit of the `ε`-approximation scheme: the extracted limit slices
are only `C⁴` (`NOTES_session16.md` §3), never `SmoothOpen`, but they *are* continuous on the open
quadrant.

## Route and the role of continuity

The parent proof (`L12_tendsto_locUnif.lean`) uses `SmoothOpen` at exactly two places, and in both
of them only the *continuity* of the profile on the open quadrant is consumed:

* `HkMemZeroSub` (`HkMem α 0 (a-b)` and `HkSq α 0 (a-b) ≤ 2(HkSq α 4 a + HkSq α 4 b)`) — its
  only smoothness input is the joint continuity of the level-`0` integrand
  `(z,θ) ↦ HkIntegrand α 0 (a-b) z θ`;
* `L12_sub_HkMem` (`L₁₂(f-g) z = L₁₂ f z - L₁₂ g z`) — its only smoothness input is the a.e.
  strong measurability of the angular slices and of the `L₁₂`-density, again from continuity.

We therefore re-prove those two (and their two ingredients: the angular-slice integrability and the
density integrability) with `ContinuousOn (Function.uncurry ·) Q0` in place of `SmoothOpen`, and
then repeat the parent assembly verbatim.  Nothing else in the chain
(`L12_master_bound`, `L12_tendsto_zero_of_GazBox`) mentions smoothness: they only need
`HkMem α 0` and a uniform `HkSq α 0`-bound.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.L12.L12_tendsto_locUnif
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.L12

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Continuity of the level-`0` integrand of a difference -/

/-- **The level-`0` integrand of a difference of two continuous data is continuous on the open
quadrant.**  Continuity of `a` and of `b` on `Q0` (together with the continuity there of the weight
`w z / sin(2θ)^{η/2}`) is preserved by subtraction, multiplication and squaring. -/
theorem continuousOn_HkIntegrand_zero_sub_of_continuousOn {α : ℝ} {a b : ℝ → ℝ → ℝ}
    (ha : ContinuousOn (Function.uncurry a) Work.FTS.EllipticEst.Q0)
    (hb : ContinuousOn (Function.uncurry b) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have ha' : ContinuousOn (fun p : ℝ × ℝ => a p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := ha
  have hb' : ContinuousOn (fun p : ℝ × ℝ => b p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hb
  have hw : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.w p.1 / Work.FTS.GalBasis.cc.Sw p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.EllipticEst.continuousOn_wdivsin_Q0
  have hfun : (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) p.1 p.2)
      = fun p : ℝ × ℝ => ((a p.1 p.2 - b p.1 p.2)
          * (Work.Spaces.w p.1 / Work.FTS.GalBasis.cc.Sw p.2)) ^ 2 := by
    funext p
    simp [Work.Spaces.HkIntegrand, Work.FTS.GalBasis.cc.Sw]
  rw [hfun]
  exact ((ha'.sub hb').mul hw).pow 2

/-- **`ℋ⁰`-membership of a difference of continuous `ℋ⁴`-data**, with the size bound.
This is the `ContinuousOn`-form of `Work.FTS.StrongEps.L12.HkMemZeroSub`: the pointwise domination
`HkIntegrand α 0 (a-b) ≤ 2(HkIntegrand α 4 a + HkIntegrand α 4 b)` and the numerical inequality
`(x-y)² ≤ 2(x²+y²)` are unchanged, and the only smoothness input — continuity of the level-`0`
integrand on the open quadrant — is `continuousOn_HkIntegrand_zero_sub_of_continuousOn`. -/
theorem HkMemZeroSub_of_continuousOn {α : ℝ} {a b : ℝ → ℝ → ℝ}
    (ha : ContinuousOn (Function.uncurry a) Work.FTS.EllipticEst.Q0)
    (hb : ContinuousOn (Function.uncurry b) Work.FTS.EllipticEst.Q0)
    (hma : Work.Spaces.HkMem α 4 a) (hmb : Work.Spaces.HkMem α 4 b) :
    Work.Spaces.HkMem α 0 (fun z θ => a z θ - b z θ) ∧
      Work.Spaces.HkSq α 0 (fun z θ => a z θ - b z θ)
        ≤ 2 * (Work.Spaces.HkSq α 4 a + Work.Spaces.HkSq α 4 b) := by
  let M : ℝ → ℝ → ℝ := fun z θ =>
    2 * (Work.Spaces.HkIntegrand α 4 a z θ + Work.Spaces.HkIntegrand α 4 b z θ)
  have hMslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ := by
    intro z hz
    show IntegrableOn (fun θ => 2 * (Work.Spaces.HkIntegrand α 4 a z θ
      + Work.Spaces.HkIntegrand α 4 b z θ)) Work.Spaces.Iθ
    exact ((hma.1 z hz).add (hmb.1 z hz)).const_mul 2
  have hMeq : ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, M z θ)
      = 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 a z θ)
          + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 b z θ) := by
    intro z hz
    rw [show M z = (fun θ => 2 * (Work.Spaces.HkIntegrand α 4 a z θ
        + Work.Spaces.HkIntegrand α 4 b z θ)) from rfl]
    rw [integral_const_mul, integral_add (hma.1 z hz) (hmb.1 z hz)]
  have hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz := by
    refine IntegrableOn.congr_fun (((hma.2.add hmb.2).const_mul 2)) ?_ measurableSet_Ici
    intro z hz
    exact (hMeq z hz).symm
  have hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) z θ ≤ M z θ := by
    intro z hz θ hθ
    simpa only [M] using HkIntegrand_zero_sub_le (α := α) (a := a) (b := b) z θ
  have hmem : Work.Spaces.HkMem α 0 (fun z θ => a z θ - b z θ) :=
    Work.FTS.LocData.HkMem_of_majorant α 0
      (continuousOn_HkIntegrand_zero_sub_of_continuousOn ha hb) hMslice hMz hle
  refine ⟨hmem, ?_⟩
  have hinner : ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
    intro z hz
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
      (hMslice z hz) ?_
    show ∀ᵐ θ ∂(volume.restrict (Set.Icc (0 : ℝ) (π / 2))),
      Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) z θ ≤ M z θ
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Eventually.of_forall fun θ hθ => hle z hz θ hθ
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) z θ)
      ≤ ∫ z in Work.Spaces.Iz, 2 * ((∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 a z θ)
          + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 b z θ) := by
    refine integral_mono_ae hmem.2 ((hma.2.add hmb.2).const_mul 2) ?_
    show ∀ᵐ z ∂(volume.restrict (Set.Ici (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) z θ)
        ≤ 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 a z θ)
          + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 b z θ)
    rw [ae_restrict_iff' measurableSet_Ici]
    exact Eventually.of_forall fun z hz =>
      le_trans (hinner z hz) (le_of_eq (hMeq z hz))
  have hfinal : (∫ z in Work.Spaces.Iz, 2 * ((∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 a z θ)
        + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 b z θ))
      = 2 * (Work.Spaces.HkSq α 4 a + Work.Spaces.HkSq α 4 b) := by
    rw [integral_const_mul, integral_add hma.2 hmb.2]
    rfl
  rw [Work.Spaces.HkSq]
  exact le_trans houter hfinal.le

/-! ## Integrability of the angular slices -/

/-- **The angular slice of the `L₁₂`-integrand is integrable**, for every `s > 0`, from
`HkMem α 4 F` together with continuity of `F` on the open quadrant (used only through the a.e.
strong measurability of the slice). -/
theorem integrableOn_slice_of_continuousOn_HkMem {α s : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 F) (hs : 0 < s) :
    IntegrableOn (fun θ => Work.Spaces.K θ * F s θ / s) Work.Spaces.Iθ := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hcontK : Continuous Work.Spaces.K := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hslice : ContinuousOn (fun θ => F s θ) (Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.continuousOn_slice_theta (G := F) hF hs
  have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.K θ * F s θ / s)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.GalBasis.cc.aesm_Icc_of_continuousOn_Ioo
      ((hcontK.continuousOn.mul hslice).div_const s)
  have hHk : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 F s θ) Work.Spaces.Iθ :=
    hmem.1 s hs.le
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    continuous_const.integrableOn_Icc
  have hdom : IntegrableOn
      (fun θ => Work.FTS.GalBasis.cc.Wlam s
        * (3 * (1 + Work.Spaces.HkIntegrand α 4 F s θ) / 2)) Work.Spaces.Iθ := by
    have h1 : IntegrableOn
        (fun θ => (Work.FTS.GalBasis.cc.Wlam s * (3 / 2))
          * (1 + Work.Spaces.HkIntegrand α 4 F s θ)) Work.Spaces.Iθ :=
      (hconst.add hHk).const_mul _
    refine h1.congr_fun (fun θ _ => ?_) hIθ
    ring
  refine hdom.mono' haesm ?_
  rw [ae_restrict_iff' hIθ]
  exact Eventually.of_forall fun θ hθ => by
    rw [Real.norm_eq_abs]
    exact Work.FTS.GalBasis.cc.abs_K_mul_F_div_s_le (α := α) hs hθ

/-! ## Integrability of the `L₁₂`-density -/

/-- **A.e. strong measurability of the `L₁₂`-density on `(0,∞)`**, for data merely continuous on
the open quadrant.  Same argument as `aesm_L12dens_of_SmoothOpen`, with the continuity hypothesis
used directly. -/
theorem aesm_L12dens_of_continuousOn_Q0 {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    AEStronglyMeasurable (Work.Construction.L12dens F) (volume.restrict (Set.Ioi 0)) := by
  have hcontK : Continuous Work.Spaces.K := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hFc : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hF
  have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hcontK.comp continuous_snd).continuousOn
  have hdiv : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 * F p.1 p.2 / p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (hK.mul hFc).div continuousOn_fst (fun p hp => ne_of_gt (Set.mem_prod.mp hp).1)
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Spaces.K p.2 * F p.1 p.2 / p.1) hdiv
  have h := hjoint.integral_prod_right' (μ := volume.restrict Work.Spaces.Iz)
  have h3 : AEStronglyMeasurable (Work.Construction.L12dens F)
      (volume.restrict Work.Spaces.Iz) := by
    convert h using 1
    funext z
    rfl
  have hset : Set.Ioi (0 : ℝ) =ᵐ[volume] Work.Spaces.Iz := MeasureTheory.Ioi_ae_eq_Ici
  rw [MeasureTheory.Measure.restrict_congr_set hset]
  exact h3

/-- **The `L₁₂`-density of a continuous `ℋ⁴`-datum is integrable on `(0,∞)`.**  The bound
`|L12dens F s| ≤ BK·(Wlam s·√(∫_θ HkIntegrand α 4 F s θ))` (from `HkMem α 4 F` alone) integrates by
Cauchy–Schwarz against `Wlam ∈ L²`; continuity provides the a.e. strong measurability. -/
theorem integrableOn_L12dens_of_continuousOn_HkMem {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 F) :
    IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0) := by
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 F s θ
  have hH_int : IntegrableOn H (Set.Ioi 0) :=
    hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi 0)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hH_int.aestronglyMeasurable
  have hA2_int : IntegrableOn (fun s => A s ^ 2) (Set.Ioi 0) :=
    hH_int.congr (Eventually.of_forall fun s => (Real.sq_sqrt (hHnn s)).symm)
  have hWlam_aesm : AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam
      (volume.restrict (Set.Ioi 0)) := by
    have hc : ContinuousOn (fun s : ℝ => s / (1 + s) ^ 2) (Set.Ioi 0) := by
      refine ContinuousOn.div continuousOn_id ?_ ?_
      · exact (continuousOn_const.add continuousOn_id).pow 2
      · intro s hs
        have h1 : (0 : ℝ) < 1 + s := by linarith [Set.mem_Ioi.mp hs]
        exact pow_ne_zero 2 (ne_of_gt h1)
    exact (show ContinuousOn Work.FTS.GalBasis.cc.Wlam (Set.Ioi 0) from hc).aestronglyMeasurable
      measurableSet_Ioi
  have hWlam2_int : IntegrableOn (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi 0) := by
    simpa only [Work.FTS.GalBasis.cc.Wlam] using Work.Elliptic.psi_sq_integrable_aux
  have hWlamA_int : IntegrableOn (fun s => Work.FTS.GalBasis.cc.Wlam s * A s) (Set.Ioi 0) := by
    refine (hWlam2_int.add hA2_int).mono' (hWlam_aesm.mul hA_aesm) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have h1 : 0 ≤ Work.FTS.GalBasis.cc.Wlam s := Work.FTS.GalBasis.cc.Wlam_nonneg hs.le
    have h2 : 0 ≤ A s := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2), Pi.add_apply]
    nlinarith [sq_nonneg (Work.FTS.GalBasis.cc.Wlam s - A s)]
  have hbd : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      ‖Work.Construction.L12dens F s‖ ≤ Work.FTS.GalBasis.cc.BK
        * (Work.FTS.GalBasis.cc.Wlam s * A s) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    have hb := Work.FTS.GalBasis.cc.abs_L12dens_le α F hmem hs
    rw [Real.norm_eq_abs]
    calc |Work.Construction.L12dens F s|
        ≤ Work.FTS.GalBasis.cc.Wlam s * (Work.FTS.GalBasis.cc.BK * A s) := by
          simpa only [hA, hH] using hb
      _ = Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) := by ring
  exact (hWlamA_int.const_mul Work.FTS.GalBasis.cc.BK).mono'
    (aesm_L12dens_of_continuousOn_Q0 hF) hbd

/-! ## Additivity of `L₁₂` on the continuous `ℋ⁴`-class -/

/-- **Additivity of `L₁₂` on the continuous `ℋ⁴`-class, on the half-line `z ∈ Iz`.**  Same proof as
`Work.FTS.StrongEps.EComparison.L12_sub_HkMem`, with continuity on `Q0` replacing `SmoothOpen` in
the two integrability inputs. -/
theorem L12_sub_of_continuousOn {α : ℝ} {a b : ℝ → ℝ → ℝ}
    (ha : ContinuousOn (Function.uncurry a) Work.FTS.EllipticEst.Q0)
    (hb : ContinuousOn (Function.uncurry b) Work.FTS.EllipticEst.Q0)
    (hma : Work.Spaces.HkMem α 4 a) (hmb : Work.Spaces.HkMem α 4 b) :
    ∀ z ∈ Work.Spaces.Iz, Work.Construction.L12 (fun z θ => a z θ - b z θ) z
      = Work.Construction.L12 a z - Work.Construction.L12 b z := by
  intro z hz
  have hz0 : 0 ≤ z := hz
  have hslt : ∀ s ∈ Set.Ioi z, 0 < s := fun s hs => lt_of_le_of_lt hz0 (Set.mem_Ioi.mp hs)
  refine Work.FTS.StrongEps.EComparison.L12_sub_of_integrable (z := z) ?_ ?_ ?_ ?_
  · intro s hs
    exact integrableOn_slice_of_continuousOn_HkMem ha hma (hslt s hs)
  · intro s hs
    exact integrableOn_slice_of_continuousOn_HkMem hb hmb (hslt s hs)
  · exact (integrableOn_L12dens_of_continuousOn_HkMem ha hma).mono_set
      (Set.Ioi_subset_Ioi hz0)
  · exact (integrableOn_L12dens_of_continuousOn_HkMem hb hmb).mono_set
      (Set.Ioi_subset_Ioi hz0)

/-! ## The theorem -/

theorem L12_tendsto_locUnif_cont (α : ℝ) (hα : 0 < α)
    (f : ℕ → Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fn) (B : ℝ)
    (hf : ∀ n : ℕ, ContinuousOn (Function.uncurry (f n)) Work.FTS.EllipticEst.Q0)
    (hmemf : ∀ n : ℕ, Work.Spaces.HkMem α 4 (f n))
    (hbf : ∀ n : ℕ, Work.FTS.Nonlin.Xn α (f n) ≤ B)
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hmemg : Work.Spaces.HkMem α 4 g)
    (hbg : Work.FTS.Nonlin.Xn α g ≤ B)
    (hconv : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n zθ => f n zθ.1 zθ.2) (fun zθ => g zθ.1 zθ.2) Filter.atTop K) :
    ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun n => Work.Construction.L12 (f n) z) Filter.atTop
        (nhds (Work.Construction.L12 g z)) := by
  intro z hz
  have hB0 : 0 ≤ B :=
    le_trans (by simp only [Work.Spaces.HkNorm]; exact Real.sqrt_nonneg _) (hbg)
  set D : ℕ → ℝ → ℝ → ℝ := fun n z θ => f n z θ - g z θ with hD
  have hDmem : ∀ n, Work.Spaces.HkMem α 0 (D n) :=
    fun n => (HkMemZeroSub_of_continuousOn (hf n) hg (hmemf n) hmemg).1
  have hDbd : ∀ n, Work.Spaces.HkSq α 0 (D n) ≤ 4 * B ^ 2 := by
    intro n
    have h1 := (HkMemZeroSub_of_continuousOn (hf n) hg (hmemf n) hmemg).2
    have hsq : ∀ x : ℝ → ℝ → ℝ, Work.FTS.Nonlin.Xn α x ≤ B →
        Work.Spaces.HkSq α 4 x ≤ B ^ 2 := by
      intro x hx
      have hnn : 0 ≤ Work.Spaces.HkNorm α 4 x := by
        simp only [Work.Spaces.HkNorm]
        exact Real.sqrt_nonneg _
      have hsqnn : 0 ≤ Work.Spaces.HkSq α 4 x := by
        rw [Work.Spaces.HkSq]
        exact integral_nonneg fun s =>
          integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 x s θ
      have h2 : Work.Spaces.HkNorm α 4 x ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hnn hx 2
      rwa [show Work.Spaces.HkNorm α 4 x = Real.sqrt (Work.Spaces.HkSq α 4 x) from rfl,
        Real.sq_sqrt hsqnn] at h2
    have h2 := hsq (f n) (hbf n)
    have h3 := hsq g hbg
    linarith
  have hGazBox : ∀ δ R ε : ℝ, 0 < δ → δ ≤ R → 0 < ε → ε ≤ Real.pi / 4 → ∀ η > 0,
      ∃ N : ℕ, ∀ n ≥ N, ∀ s ∈ Set.Icc δ R, ∀ θ ∈ Set.Icc ε (Real.pi / 2 - ε),
        |Work.FTS.GalBasis.cc.Gaz (D n) s θ| ≤ η := by
    intro δ R ε hδ hδR hε hε4 η hη
    have hsub : Set.Icc δ R ×ˢ Set.Icc ε (Real.pi / 2 - ε) ⊆ Work.FTS.EllipticEst.Q0 := by
      intro p hp
      have hp1 : p.1 ∈ Set.Icc δ R := hp.1
      have hp2 : p.2 ∈ Set.Icc ε (Real.pi / 2 - ε) := hp.2
      rw [Work.FTS.EllipticEst.mem_Q0]
      exact ⟨lt_of_lt_of_le hδ hp1.1, lt_of_lt_of_le hε hp2.1,
        by linarith [hp2.2, Real.pi_pos]⟩
    have hcomp : IsCompact (Set.Icc δ R ×ˢ Set.Icc ε (Real.pi / 2 - ε)) :=
      isCompact_Icc.prod isCompact_Icc
    have hunif := hconv _ hcomp hsub
    rw [Metric.tendstoUniformlyOn_iff] at hunif
    set cw : ℝ := Work.Spaces.w δ / Work.FTS.GalBasis.cc.Sw ε with hcw
    have hcwpos : 0 < cw := by
      rw [hcw]
      refine div_pos ?_ (Work.FTS.GalBasis.cc.Sw_pos_of_mem_Ioo hε
        (by linarith [hε4, Real.pi_pos]))
      rw [Work.Spaces.w]
      positivity
    have hcw0 : 0 ≤ cw := le_of_lt hcwpos
    obtain ⟨N, hN⟩ :=
      Filter.eventually_atTop.mp (hunif (η / (cw + 1)) (div_pos hη (by linarith)))
    refine ⟨N, fun n hn s hs θ hθ => ?_⟩
    have h1 : |D n s θ| ≤ η / (cw + 1) := by
      have h := hN n hn (s, θ) ⟨hs, hθ⟩
      rw [Real.dist_eq] at h
      rw [abs_sub_comm]
      exact h.le
    have h2 : Work.Spaces.w s / Work.FTS.GalBasis.cc.Sw θ ≤ cw := by
      rw [hcw]
      exact WSwBound δ ε hδ hε hε4 s θ hs.1 hθ.1 hθ.2
    have h2nn : 0 ≤ Work.Spaces.w s / Work.FTS.GalBasis.cc.Sw θ := by
      refine div_nonneg ?_ ?_
      · rw [Work.Spaces.w]
        positivity
      · exact le_of_lt (Work.FTS.GalBasis.cc.Sw_pos_of_mem_Ioo (lt_of_lt_of_le hε hθ.1)
          (by linarith [hθ.2, Real.pi_pos]))
    show |Work.FTS.GalBasis.cc.Gaz (D n) s θ| ≤ η
    rw [Work.FTS.GalBasis.cc.Gaz, abs_mul, abs_of_nonneg h2nn]
    calc |D n s θ| * (Work.Spaces.w s / Work.FTS.GalBasis.cc.Sw θ)
        ≤ (η / (cw + 1)) * cw := mul_le_mul h1 h2 h2nn (by positivity)
      _ ≤ η := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith [hcw0, hη]
  have hkey := L12_tendsto_zero_of_GazBox (α := α) (D := D) (C := 4 * B ^ 2)
    hDmem hDbd (by positivity) hGazBox hz
  have heq : ∀ n, Work.Construction.L12 (D n) z
      = Work.Construction.L12 (f n) z - Work.Construction.L12 g z := by
    intro n
    exact L12_sub_of_continuousOn (hf n) hg (hmemf n) hmemg z (by
      simp only [Work.Spaces.Iz, Set.mem_Ici]
      exact hz)
  have h2 : Filter.Tendsto (fun n => Work.Construction.L12 (D n) z + Work.Construction.L12 g z)
      Filter.atTop (nhds (0 + Work.Construction.L12 g z)) := hkey.add_const _
  have h3 : (fun n => Work.Construction.L12 (D n) z + Work.Construction.L12 g z)
      = fun n => Work.Construction.L12 (f n) z := by
    funext n
    rw [heq n]
    ring
  rw [h3] at h2
  simpa using h2

end Work.FTS.StrongEps.L12
