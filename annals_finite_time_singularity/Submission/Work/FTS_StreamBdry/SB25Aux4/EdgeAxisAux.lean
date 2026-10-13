import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2
import Submission.Work.FTS_StreamBdry.SB3.pth_DzIter_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux4.EdgeAxisAux` — helpers for the `θ = π/2` edge limits of `psiP`

Elementary lemmas shared by the three parts of `psiP_edge_axis_aux`:

* `s2_le_two_sub` (`sin 2θ ≤ 2(π/2 - θ)` on `(0, π/2)`);
* the squeezing helpers `tendsto_nhdsWithin_of_abs_le`, `eventually_nhdsWithin_Qd`, and the
  three `Tendsto`-of-majorant lemmas;
* the mean-value rate lemma `rate_of_deriv_le`;
* the differential identities `pz_pth_eq` (`∂_z∂_θP = ∂_z(V(P)) + tan θ ∂_zP`),
  `DzIter_two_eq` (`D_z²P = z∂_zP + z²∂_z²P`) and `pth_pz_eq`
  (`∂_θ∂_zP = (D_z(V(P)) + tan θ·D_zP)/z`).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25Aux4

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP)

set_option autoImplicit false

/-- `sin 2θ ≤ 2(π/2 - θ)` on `(0, π/2)`. -/
lemma s2_le_two_sub {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Construction.s2 θ ≤ 2 * (Real.pi / 2 - θ) := by
  rw [Work.FTS_StreamBdry.s2_eq_two_sin_cos]
  have hcos : 0 < Real.cos θ := Work.FTS_StreamBdry.cos_pos_of_Ioo hθ
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h1 : 2 * Real.sin θ * Real.cos θ ≤ 2 * Real.cos θ := by nlinarith
  have h2 : Real.cos θ = Real.sin (Real.pi / 2 - θ) := (Real.sin_pi_div_two_sub θ).symm
  have h3 : Real.sin (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := Real.sin_le (by linarith [hθ.2])
  linarith

/-- Squeezing inside the open quadrant. -/
lemma tendsto_nhdsWithin_of_abs_le {f : ℝ → ℝ → ℝ} {x : ℝ × ℝ} {L : ℝ} {g : ℝ × ℝ → ℝ}
    (hg : Tendsto g (𝓝 x) (𝓝 0))
    (h : ∀ᶠ p in 𝓝[Work.Construction.Qd] x, |Function.uncurry f p - L| ≤ g p) :
    Tendsto (Function.uncurry f) (𝓝[Work.Construction.Qd] x) (𝓝 L) := by
  have h1 : Tendsto (fun p : ℝ × ℝ => Function.uncurry f p - L)
      (𝓝[Work.Construction.Qd] x) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun p => abs_nonneg _) ?_
      (hg.mono_left nhdsWithin_le_nhds)
    filter_upwards [h] with p hp
    simpa [Real.norm_eq_abs] using hp
  have h3 := h1.add (tendsto_const_nhds :
    Tendsto (fun _ : ℝ × ℝ => L) (𝓝[Work.Construction.Qd] x) (𝓝 L))
  rw [zero_add] at h3
  simpa [sub_add_cancel] using h3

/-- A pointwise bound valid on `Qd` gives an eventual bound within `Qd`. -/
lemma eventually_nhdsWithin_Qd {φ : ℝ × ℝ → Prop} {x : ℝ × ℝ}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → φ (z, θ)) :
    ∀ᶠ p in 𝓝[Work.Construction.Qd] x, φ p :=
  eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun p hp => h p.1 p.2 hp)

/-- `Prod.fst` tends to `a` at `(a, b)` (with `𝓝 (a,b)` rather than `𝓝 a ×ˢ 𝓝 b`). -/
lemma tendsto_fst' {a b : ℝ} : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝 (a, b)) (𝓝 a) := by
  rw [nhds_prod_eq]; exact tendsto_fst

/-- The majorant `c * (π/2 - p.2)` tends to `0` at `(z₀, π/2)`. -/
lemma tendsto_const_mul_sub_snd_zero (c z0 : ℝ) :
    Tendsto (fun p : ℝ × ℝ => c * (Real.pi / 2 - p.2)) (𝓝 (z0, Real.pi / 2)) (𝓝 0) := by
  rw [nhds_prod_eq]
  have key : Tendsto (fun p : ℝ × ℝ => c * (Real.pi / 2 - p.2)) (𝓝 z0 ×ˢ 𝓝 (Real.pi / 2))
      (𝓝 (c * (Real.pi / 2 - Real.pi / 2))) :=
    tendsto_const_nhds.mul
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ × ℝ => Real.pi / 2)
          (𝓝 z0 ×ˢ 𝓝 (Real.pi / 2)) (𝓝 (Real.pi / 2))).sub
        (tendsto_snd : Tendsto (fun p : ℝ × ℝ => p.2) (𝓝 z0 ×ˢ 𝓝 (Real.pi / 2))
          (𝓝 (Real.pi / 2))))
  simpa using key

/-- The one-dimensional analogue: `c * (a - t) → 0` at `a`. -/
lemma tendsto_const_mul_sub_zero (c a : ℝ) :
    Tendsto (fun t : ℝ => c * (a - t)) (𝓝 a) (𝓝 0) := by
  have key : Tendsto (fun t : ℝ => c * (a - t)) (𝓝 a) (𝓝 (c * (a - a))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub tendsto_id)
  simpa using key

/-- `|h p.1 - h z₀| → 0` at `(z₀, π/2)` when `h` is continuous at `z₀`. -/
lemma tendsto_abs_sub_const {h : ℝ → ℝ} {z0 : ℝ} (hh : ContinuousAt h z0) :
    Tendsto (fun p : ℝ × ℝ => |h p.1 - h z0|) (𝓝 (z0, Real.pi / 2)) (𝓝 0) := by
  rw [nhds_prod_eq]
  have h1 : Tendsto (fun p : ℝ × ℝ => h p.1 - h z0) (𝓝 z0 ×ˢ 𝓝 (Real.pi / 2)) (𝓝 0) := by
    have h2 := (hh.tendsto.comp (tendsto_fst : Tendsto (fun p : ℝ × ℝ => p.1)
      (𝓝 z0 ×ˢ 𝓝 (Real.pi / 2)) (𝓝 z0))).sub_const (h z0)
    simpa using h2
  simpa using h1.abs

/-- The mean-value rate lemma: if `|g'| ≤ ε` near `π/2` and `g → v₀` at `π/2`, then
`|g t - v₀| ≤ ε(π/2 - t)` on `[θ₀, π/2)`. -/
lemma rate_of_deriv_le {g : ℝ → ℝ} {θ0 v0 ε : ℝ} (hθ0 : θ0 ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hε : 0 ≤ ε)
    (hd : ∀ t ∈ Ico θ0 (Real.pi / 2), DifferentiableAt ℝ g t)
    (hbd : ∀ t ∈ Ioo θ0 (Real.pi / 2), |deriv g t| ≤ ε)
    (hlim : Tendsto g (𝓝[Set.Iio (Real.pi / 2)] (Real.pi / 2)) (𝓝 v0)) :
    ∀ t ∈ Ico θ0 (Real.pi / 2), |g t - v0| ≤ ε * (Real.pi / 2 - t) := by
  have hmid : ∀ t ∈ Ioo θ0 (Real.pi / 2), |g t - v0| ≤ ε * (Real.pi / 2 - t) := by
    intro t ht
    have hmain : ∀ t' ∈ Ioo t (Real.pi / 2), |g t' - g t| ≤ ε * (t' - t) := by
      intro t' ht'
      have hkey := (convex_Ioo θ0 (Real.pi / 2)).norm_image_sub_le_of_norm_deriv_le
        (f := g) (C := ε)
        (fun x hx => hd x ⟨le_of_lt hx.1, hx.2⟩)
        (fun x hx => by rw [Real.norm_eq_abs]; exact hbd x hx) ht ⟨lt_trans ht.1 ht'.1, ht'.2⟩
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at hkey
      rw [abs_of_pos (by linarith [ht'.1] : (0 : ℝ) < t' - t)] at hkey
      exact hkey
    have h1 : Tendsto (fun t' => |g t' - g t|) (𝓝[Iio (Real.pi / 2)] (Real.pi / 2))
        (𝓝 |v0 - g t|) := (hlim.sub_const (g t)).abs
    have hb : ∀ᶠ t' in 𝓝[Iio (Real.pi / 2)] (Real.pi / 2),
        |g t' - g t| ≤ ε * (Real.pi / 2 - t) := by
      have hlt : ∀ᶠ t' in 𝓝[Iio (Real.pi / 2)] (Real.pi / 2), t < t' :=
        (eventually_gt_nhds ht.2).filter_mono nhdsWithin_le_nhds
      filter_upwards [hlt, self_mem_nhdsWithin] with t' h1' h2'
      have h2'' : t' < Real.pi / 2 := h2'
      exact le_trans (hmain t' ⟨h1', h2''⟩)
        (mul_le_mul_of_nonneg_left (by linarith) hε)
    haveI : (𝓝[Iio (Real.pi / 2)] (Real.pi / 2)).NeBot := nhdsWithin_Iio_neBot le_rfl
    have := le_of_tendsto h1 hb
    rwa [abs_sub_comm] at this
  intro t ht
  rcases lt_or_eq_of_le ht.1 with hlt | heq
  · exact hmid t ⟨hlt, ht.2⟩
  · subst heq
    have h1 : Tendsto (fun t' => |g t' - v0|) (𝓝[Ioi θ0] θ0) (𝓝 |g θ0 - v0|) :=
      (((hd θ0 ⟨le_refl θ0, hθ0.2⟩).continuousAt.tendsto).mono_left
        (nhdsWithin_le_nhds)).sub_const v0 |>.abs
    have hb : ∀ᶠ t' in 𝓝[Ioi θ0] θ0, |g t' - v0| ≤ ε * (Real.pi / 2 - θ0) := by
      have hlt : ∀ᶠ t' in 𝓝[Ioi θ0] θ0, t' < Real.pi / 2 :=
        (eventually_lt_nhds hθ0.2).filter_mono nhdsWithin_le_nhds
      filter_upwards [hlt, self_mem_nhdsWithin] with t' h1' h2'
      have h1'' : t' < Real.pi / 2 := h1'
      have h2'' : θ0 < t' := h2'
      exact le_trans (hmid t' ⟨h2'', h1''⟩)
        (mul_le_mul_of_nonneg_left (by linarith) hε)
    haveI : (𝓝[Ioi θ0] θ0).NeBot := nhdsWithin_Ioi_neBot le_rfl
    exact le_of_tendsto h1 hb

/-- `∂_z(∂_θP) = ∂_z(V(P)) + tan θ · ∂_zP` at any point of the open quadrant. -/
lemma pz_pth_eq {P : ℝ → ℝ → ℝ} (hP2 : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.pz (Work.Spaces.pth P) z θ
      = Work.Spaces.pz (Work.Construction.Vop P) z θ
        + Real.tan θ * Work.Spaces.pz P z θ := by
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hdP : DifferentiableAt ℝ (fun z' => P z' θ) z :=
    Work.Spaces.differentiableAt_curry_left
      ((hP2.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds h))
  have hpth1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth P)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.contDiffOn_uncurry_pth_qd (G := P) (n := 1) hP2
  have hdpth : DifferentiableAt ℝ (fun z' => Work.Spaces.pth P z' θ) z :=
    Work.Spaces.differentiableAt_curry_left
      ((hpth1.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds h))
  show deriv (fun z' => Work.Spaces.pth P z' θ) z
      = deriv (fun z' => Work.Construction.Vop P z' θ) z
        + Real.tan θ * deriv (fun z' => P z' θ) z
  have hV : deriv (fun z' => Work.Construction.Vop P z' θ) z
      = deriv (fun z' => Work.Spaces.pth P z' θ) z
        - Real.tan θ * deriv (fun z' => P z' θ) z := by
    have hfun : (fun z' => Work.Construction.Vop P z' θ)
        = fun z' => Work.Spaces.pth P z' θ - Real.tan θ * P z' θ := by
      funext z'; rw [Work.Construction.Vop]
    rw [hfun]
    have h2 : HasDerivAt (fun z' => Work.Spaces.pth P z' θ - Real.tan θ * P z' θ)
        (deriv (fun z' => Work.Spaces.pth P z' θ) z
          - Real.tan θ * deriv (fun z' => P z' θ) z) z := by
      have hA : HasDerivAt (fun z' => Work.Spaces.pth P z' θ)
          (deriv (fun z' => Work.Spaces.pth P z' θ) z) z := hdpth.hasDerivAt
      have hB : HasDerivAt (fun z' => Real.tan θ * P z' θ)
          (Real.tan θ * deriv (fun z' => P z' θ) z) z := (hdP.hasDerivAt).const_mul _
      have hsub := hA.sub hB
      have hfun2 : ((fun z' => Work.Spaces.pth P z' θ) - fun z' => Real.tan θ * P z' θ)
          = fun z' => Work.Spaces.pth P z' θ - Real.tan θ * P z' θ := by funext x; rfl
      rwa [hfun2] at hsub
    exact h2.deriv
  rw [hV]; ring

/-- `D_z²P = z·∂_zP + z²·∂_z²P` on the open quadrant. -/
lemma DzIter_two_eq {P : ℝ → ℝ → ℝ} (hP2 : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.DzIter 2 P z θ
      = z * Work.Spaces.pz P z θ + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz P) z θ := by
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hpz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz P)) Work.Construction.Qd := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ (Function.uncurry P)) Work.Construction.Qd :=
      hP2.fderiv_of_isOpen hQd (m := 1) (by norm_num)
    refine (hfd.clm_apply (contDiffOn_const (c := ((1 : ℝ), (0 : ℝ))))).congr (fun p hp => ?_)
    simp only [Function.uncurry]
    exact Work.Spaces.pz_eq_fderiv
      ((hP2.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hp))
  have hdiff : DifferentiableAt ℝ (fun t => Work.Spaces.pz P t θ) z :=
    Work.Spaces.differentiableAt_curry_left
      ((hpz1.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds h))
  show z * deriv (fun t => Work.Spaces.DzIter 1 P t θ) z = _
  have hfun : (fun t => Work.Spaces.DzIter 1 P t θ) = fun t => t * Work.Spaces.pz P t θ := by
    funext t; rfl
  rw [hfun]
  have h2 : HasDerivAt (fun t => t * Work.Spaces.pz P t θ)
      (Work.Spaces.pz P z θ + z * deriv (fun t => Work.Spaces.pz P t θ) z) z := by
    have hA : HasDerivAt (fun t : ℝ => t) 1 z := hasDerivAt_id z
    have hB : HasDerivAt (fun t => Work.Spaces.pz P t θ)
        (deriv (fun t => Work.Spaces.pz P t θ) z) z := hdiff.hasDerivAt
    have hmul := hA.mul hB
    have hfun2 : ((fun t : ℝ => t) * fun t => Work.Spaces.pz P t θ)
        = fun t => t * Work.Spaces.pz P t θ := by funext x; rfl
    rw [hfun2] at hmul
    simpa using hmul
  rw [h2.deriv]
  rw [show deriv (fun t => Work.Spaces.pz P t θ) z
      = Work.Spaces.pz (Work.Spaces.pz P) z θ from rfl]
  ring

/-- `∂_θ(∂_zP) = (D_z(V(P)) + tan θ · D_zP)/z` on the open quadrant. -/
lemma pth_pz_eq {P : ℝ → ℝ → ℝ} (hP2 : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.pth (Work.Spaces.pz P) z θ
      = (Work.Spaces.DzIter 1 (Work.Construction.Vop P) z θ
          + Real.tan θ * Work.Spaces.DzIter 1 P z θ) / z := by
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hz : z ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.Qd_pos h)
  have hcl := Work.Spaces.pz_pth_comm (f := P)
    ((hP2.contDiffAt (hQd.mem_nhds h)).of_le (le_refl (2 : WithTop ℕ∞)))
  rw [← hcl]
  rw [pz_pth_eq hP2 h]
  have h1 : Work.Spaces.pz (Work.Construction.Vop P) z θ
      = Work.Spaces.DzIter 1 (Work.Construction.Vop P) z θ / z := by
    rw [show Work.Spaces.DzIter 1 (Work.Construction.Vop P) z θ
        = z * Work.Spaces.pz (Work.Construction.Vop P) z θ from rfl]
    field_simp
  have h2 : Work.Spaces.pz P z θ = Work.Spaces.DzIter 1 P z θ / z := by
    rw [show Work.Spaces.DzIter 1 P z θ = z * Work.Spaces.pz P z θ from rfl]
    field_simp
  rw [h1, h2]
  field_simp

end Work.FTS_StreamBdry.SB25Aux4
