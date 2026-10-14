import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Ftau_bounds` — uniform bounds for `F(τ) = F_* + g(τ)`

`Ftau (pExp α) (GR α g) τ = F_* + gS α (tauExt g)(τ)`, and on the open quadrant
`gS α (tauExt g) z θ τ = g z θ τ` (`τ ≥ 0`), so `F(τ) = F_* + g(τ)` there.  The three
`D_z`-jets of order `≤ 2` of `F(τ)` are therefore bounded by the sum of those of `F_*`
(uniformly bounded on the closed quadrant, by `FstarJet7` together with the elementary bound
`|α Γ/c| ≤ 10`) and those of the slice `slice g τ` (`mixed_uniform`, slots `(b,a) = (j,0)`).

The only structural ingredient is that `D_z^j` is additive on the sum: `F_*` is `C²` on the
open quadrant (`ftau_contDiffOn_Fstar_Q0`) and `slice g τ` is `C⁴` there (`RegPkgMin.c4`),
so `deriv_add` applies slicewise (`ftau_DzIter_one_add`, `ftau_DzIter_two_add`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface.RXT (GR)

set_option autoImplicit false

/-! ## §1 `Γ` and `F_{*,rad}` are `C²` on the open quadrant -/

theorem ftau_contDiffOn_Gam_Q0 (α : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Work.FTS.EllipticEst.Q0 := by
  have hbase : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    (((Real.contDiff_sin.comp contDiff_snd).mul
      ((Real.contDiff_cos.comp contDiff_snd).pow 2)).contDiffOn).of_le le_top
  have hpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin p.2 * Real.cos p.2 ^ 2 := by
    intro p hp
    have hs : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hp.2.1, Real.pi_pos]) (by linarith [hp.2.2, Real.pi_pos])
    have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
    positivity
  simpa only [Work.Spaces.Gam] using
    hbase.rpow_const_of_ne (fun p hp => ne_of_gt (hpos p hp))

theorem ftau_contDiffOn_FM_Fstar (n : ℕ) :
    ContDiffOn ℝ n (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ n (fun z : ℝ => 2 * z) (Set.Ioi 0) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ n (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi 0) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have h := hnum.div hden (fun z hz => pow_ne_zero 2 (by
    have hz' : (0 : ℝ) < z := hz
    linarith))
  refine h.congr (fun z _ => ?_)
  simp only [Pi.div_apply, Work.FM.Fstar]

theorem ftau_contDiffOn_fst_of {n : ℕ} {a : ℝ → ℝ} (ha : ContDiffOn ℝ n a (Set.Ioi 0)) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => a p.1) Work.FTS.EllipticEst.Q0 :=
  ha.comp contDiffOn_fst (fun p hp => hp.1)

theorem ftau_contDiffOn_Fstar_Q0 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Fstar α)) Work.FTS.EllipticEst.Q0 := by
  have hGam : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
      Work.FTS.EllipticEst.Q0 := ftau_contDiffOn_Gam_Q0 α 2
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have h1 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2 / Work.Spaces.c α)
      Work.FTS.EllipticEst.Q0 :=
    hGam.div contDiffOn_const (fun _ _ => hc)
  have h2 : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ => α * (Work.Spaces.Gam α p.2 / Work.Spaces.c α))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul h1
  have h3 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Work.FM.Fstar p.1)
      Work.FTS.EllipticEst.Q0 :=
    ftau_contDiffOn_fst_of (ftau_contDiffOn_FM_Fstar 2)
  exact (h2.mul h3).congr (fun _ _ => rfl)

/-! ## §2 The sanitiser agrees with `g` on the open quadrant -/

theorem ftau_GR_of_quad {α : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) {z θ : ℝ}
    (hz : 0 < z) (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2) : GR α g z θ τ = g z θ τ := by
  have h : GR α g z θ τ = Work.FTS.FinalV2.tauExt g z θ τ := by
    simp only [Work.FTS.RegExportIface.RXT.GR, Work.FTS.FinalV2.gS, hz, h0, h1, and_self,
      ↓reduceIte]
  rw [h, Work.FTS.FinalV2.tauExt_of_nonneg g hτ]

theorem ftau_slice_GR_eq {α : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) {z θ : ℝ}
    (hz : 0 < z) (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2) : slice (GR α g) τ z θ = slice g τ z θ :=
  ftau_GR_of_quad hτ hz h0 h1

theorem ftau_contDiffOn_slice_GR_Q0 {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ContDiffOn ℝ 2 (Function.uncurry (slice (GR α g) τ)) Work.FTS.EllipticEst.Q0 := by
  have h4 : ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0 :=
    hOK.1.1.c4 τ hτ
  refine (h4.of_le (by norm_num)).congr ?_
  intro p hp
  exact ftau_slice_GR_eq hτ hp.1 hp.2.1.le hp.2.2.le

/-! ## §3 Linearity of the iterated `D_z` on the open quadrant -/

/-- `D_z^j` commutes with multiplication by a `θ`-dependent factor: the `z`-derivative of
`fun z => c θ * f z θ` is `c θ` times that of `f`. -/
lemma ftau_DzIter_mul_theta (c : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => c θ * f z θ)
      = fun z θ => c θ * Work.Spaces.DzIter j f z θ := by
  induction j with
  | zero => rfl
  | succ n ih =>
      funext z θ
      rw [Work.Spaces.DzIter_succ, ih]
      show z * deriv (fun z' => c θ * Work.Spaces.DzIter n f z' θ) z
        = c θ * (z * deriv (fun z' => Work.Spaces.DzIter n f z' θ) z)
      rw [deriv_const_mul_field]
      ring

/-- `D_z` is additive on the open quadrant for `C¹` data. -/
lemma ftau_DzIter_one_add {f h : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hh : ContDiffOn ℝ 1 (Function.uncurry h) Work.FTS.EllipticEst.Q0) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter 1 (fun z θ => f z θ + h z θ) z θ
        = Work.Spaces.DzIter 1 f z θ + Work.Spaces.DzIter 1 h z θ := by
  intro z θ hz h1 h2
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.Q0, Set.mem_prod]; exact ⟨hz, h1, h2⟩
  have hdf := hasDerivAt_slice_fst_of_contDiffOn (V := Work.FTS.EllipticEst.Q0)
    Work.FTS.EllipticEst.isOpen_Q0 hf hmem
  have hdh := hasDerivAt_slice_fst_of_contDiffOn (V := Work.FTS.EllipticEst.Q0)
    Work.FTS.EllipticEst.isOpen_Q0 hh hmem
  show z * deriv (fun z' => f z' θ + h z' θ) z
    = z * deriv (fun z' => f z' θ) z + z * deriv (fun z' => h z' θ) z
  rw [show (fun z' => f z' θ + h z' θ) = (fun z' => f z' θ) + (fun z' => h z' θ) from rfl,
    deriv_add hdf.differentiableAt hdh.differentiableAt]
  ring

/-- `D_z^2` is additive on the open quadrant for `C²` data (one more slice derivative). -/
lemma ftau_DzIter_two_add {f h : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hh : ContDiffOn ℝ 2 (Function.uncurry h) Work.FTS.EllipticEst.Q0) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter 2 (fun z θ => f z θ + h z θ) z θ
        = Work.Spaces.DzIter 2 f z θ + Work.Spaces.DzIter 2 h z θ := by
  intro z θ hz h1 h2
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.Q0, Set.mem_prod]; exact ⟨hz, h1, h2⟩
  have hf1 : ContDiffOn ℝ 1 (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    hf.of_le (by norm_num)
  have hh1 : ContDiffOn ℝ 1 (Function.uncurry h) Work.FTS.EllipticEst.Q0 :=
    hh.of_le (by norm_num)
  have hdf1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.DzIter 1 f))
      Work.FTS.EllipticEst.Q0 := by
    have h1' : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed 1 0 f))
        Work.FTS.EllipticEst.Q0 :=
      Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le (n := 2)
        Work.FTS.EllipticEst.isOpen_Q0 0 1 1 (by norm_num) hf
    simpa only [Work.Spaces.mixed, Work.Spaces.DthIter_zero] using h1'
  have hdh1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.DzIter 1 h))
      Work.FTS.EllipticEst.Q0 := by
    have h1' : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed 1 0 h))
        Work.FTS.EllipticEst.Q0 :=
      Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le (n := 2)
        Work.FTS.EllipticEst.isOpen_Q0 0 1 1 (by norm_num) hh
    simpa only [Work.Spaces.mixed, Work.Spaces.DthIter_zero] using h1'
  have hdf := hasDerivAt_slice_fst_of_contDiffOn (V := Work.FTS.EllipticEst.Q0)
    Work.FTS.EllipticEst.isOpen_Q0 hdf1 hmem
  have hdh := hasDerivAt_slice_fst_of_contDiffOn (V := Work.FTS.EllipticEst.Q0)
    Work.FTS.EllipticEst.isOpen_Q0 hdh1 hmem
  have heq : (fun z' => Work.Spaces.DzIter 1 (fun z θ => f z θ + h z θ) z' θ) =ᶠ[𝓝 z]
      (fun z' => Work.Spaces.DzIter 1 f z' θ + Work.Spaces.DzIter 1 h z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact ftau_DzIter_one_add hf1 hh1 z' θ hz' h1 h2
  show z * deriv (fun z' => Work.Spaces.DzIter 1 (fun z θ => f z θ + h z θ) z' θ) z
    = z * deriv (fun z' => Work.Spaces.DzIter 1 f z' θ) z
      + z * deriv (fun z' => Work.Spaces.DzIter 1 h z' θ) z
  rw [heq.deriv_eq]
  rw [show (fun z' => Work.Spaces.DzIter 1 f z' θ + Work.Spaces.DzIter 1 h z' θ)
      = (fun z' => Work.Spaces.DzIter 1 f z' θ) + (fun z' => Work.Spaces.DzIter 1 h z' θ)
      from rfl,
    deriv_add hdf.differentiableAt hdh.differentiableAt]
  ring

/-! ## §4 The `D_z`-jets of the reference profile are uniformly bounded -/

/-- The `θ`-dependent factor of `F_*` factors out of the iterated `D_z`. -/
lemma ftau_DzIter_Fstar_eq (p : ℝ) (j : ℕ) :
    Work.Spaces.DzIter j
        (fun z θ => p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * Work.FM.Fstar z)
      = fun z θ => (p * (Work.Spaces.Gam p θ / Work.Spaces.c p))
          * Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ :=
  ftau_DzIter_mul_theta (fun θ => p * (Work.Spaces.Gam p θ / Work.Spaces.c p))
    (fun z _ => Work.FM.Fstar z) j

/-- **`|D_z^j F_*| ≤ 10 M` on the open quadrant**, for any bound `M` of the `D_z`-jets of the
radial factor `2z/(1+z)²` on `[0,∞)` (`FstarJet7` supplies one, for `j ≤ 7`). -/
lemma ftau_DzIter_Fstar_le {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {M : ℝ}
    (hM : ∀ j : ℕ, j ≤ 7 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter j Work.FM.Fstar z| ≤ M)
    (j : ℕ) (hj : j ≤ 7) (z θ : ℝ) (hz : 0 < z) (h1 : 0 < θ) (h2 : θ < π / 2) :
    |Work.Spaces.DzIter j (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
      ≤ 10 * M := by
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨h1.le, h2.le⟩
  have hGam := Work.Spaces.Gam_bounds (Work.FTS.Regularity.pExp α) θ hp0 hθI
  have hc := Work.Spaces.c_bounds (Work.FTS.Regularity.pExp α) hp0 hp1
  have hcpos : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp α) := by linarith [hc.1]
  have hcoef : |Work.FTS.Regularity.pExp α
      * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          / Work.Spaces.c (Work.FTS.Regularity.pExp α))| ≤ 10 := by
    have hnn : 0 ≤ Work.FTS.Regularity.pExp α
        * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            / Work.Spaces.c (Work.FTS.Regularity.pExp α)) :=
      mul_nonneg hp0.le (div_nonneg hGam.1 hcpos.le)
    rw [abs_of_nonneg hnn, ← mul_div_assoc, div_le_iff₀ hcpos]
    nlinarith [hp0, hp1, hGam.1, hGam.2, hc.1]
  have hval : Work.Spaces.DzIter j (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
      = (Work.FTS.Regularity.pExp α
          * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)))
        * Work.Elliptic.DzdIter j Work.FM.Fstar z := by
    have h1' : Work.Spaces.DzIter j (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
        = (Work.FTS.Regularity.pExp α
            * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
                / Work.Spaces.c (Work.FTS.Regularity.pExp α)))
          * Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ := by
      change Work.Spaces.DzIter j (fun z θ =>
          Work.FTS.Regularity.pExp α
            * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
                / Work.Spaces.c (Work.FTS.Regularity.pExp α)) * Work.FM.Fstar z) z θ = _
      rw [ftau_DzIter_Fstar_eq (Work.FTS.Regularity.pExp α) j]
    rw [h1', Work.Elliptic.DzIter_rad (fun z => Work.FM.Fstar z) j z θ]
  rw [hval, abs_mul]
  exact mul_le_mul hcoef (hM j hj z hz.le) (abs_nonneg _) (by norm_num)

/-! ## §5 The `D_z`-jets of the slice of `g` satisfy the `mixed_uniform` bound -/

lemma ftau_DzIter_GR_le {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (τ : ℝ) (hτ : 0 ≤ τ) (j : ℕ) (hj : j ≤ 2) (z θ : ℝ)
    (hz : 0 < z) (h1 : 0 < θ) (h2 : θ < π / 2) :
    |Work.Spaces.DzIter j (slice (GR α g) τ) z θ|
      ≤ 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
        * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) := by
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.Q0, Set.mem_prod]; exact ⟨hz, h1, h2⟩
  have hEqOn : Set.EqOn (Function.uncurry (slice (GR α g) τ)) (Function.uncurry (slice g τ))
      Work.FTS.EllipticEst.Q0 :=
    fun p hp => ftau_slice_GR_eq hτ hp.1 hp.2.1.le hp.2.2.le
  have hcongr := Work.FTS.H2.DzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqOn j
  have hstep : Work.Spaces.DzIter j (slice (GR α g) τ) z θ
      = Work.Spaces.DzIter j (slice g τ) z θ := hcongr (x := (z, θ)) hmem
  rw [hstep]
  have hT : 0 < max τ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hτT : τ ∈ Set.Icc (0 : ℝ) (max τ 1) := ⟨hτ, le_max_left _ _⟩
  have h := mixed_uniform (α := Work.FTS.Regularity.pExp α) hp0 hp1 hOK.2 (max τ 1) hT
    τ hτT j 0 (by omega) z θ hmem
  simpa only [Work.Spaces.mixed_zero_right] using h

/-! ## §6 The target -/

/-- **Uniform bounds for the profile `F(τ) = F_* + g(τ)` and its `D_z`-derivatives.**  On the
open quadrant, `F_*(z,θ) = α (Γ(θ)/c(α)) · 2z/(1+z)²` and, for `0 < z, 0 < θ < π/2, τ ≥ 0`,
`gS α (tauExt g) z θ τ = g z θ τ`, so `F = F_* + g(τ)`; the `F_*`-part is elementary
(`Γ ≤ 1`, `1/10 ≤ c ≤ 10`, `2z/(1+z)² ≤ 1/2`, and `z h'(z)`, `z² h''(z)` are bounded for
`h(z) = 2z/(1+z)²`), while the `g`-part is bounded by `mixed_uniform` (slots `(b,a) = (0,0)`,
`(1,0)`, `(2,0)`), using that `gS α (tauExt g)` and `g` agree on a neighbourhood of every point
of the open quadrant and that `DzIter 2 = Dz + z² ∂_z²` (product rule). -/
theorem Ftau_bounds {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ z θ| ≤ C ∧
      |Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z θ| ≤ C ∧
      |Work.Spaces.DzIter 2 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z θ| ≤ C := by
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
  set K : ℝ := 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
      * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) with hK
  refine ⟨10 * M + |K|, ?_, ?_⟩
  · have h10M : 0 ≤ 10 * M := by linarith
    have habs : 0 ≤ |K| := abs_nonneg K
    linarith
  · intro z θ hz h1 h2
    have hFc : ContDiffOn ℝ 2
        (Function.uncurry (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
        Work.FTS.EllipticEst.Q0 :=
      ftau_contDiffOn_Fstar_Q0 (Work.FTS.Regularity.pExp_pos hα)
        (Work.FTS.Regularity.pExp_le_one hα13)
    have hGc : ContDiffOn ℝ 2
        (Function.uncurry (slice (GR α g) τ)) Work.FTS.EllipticEst.Q0 :=
      ftau_contDiffOn_slice_GR_Q0 hOK τ hτ
    have hF1 : ContDiffOn ℝ 1
        (Function.uncurry (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
        Work.FTS.EllipticEst.Q0 := hFc.of_le (by norm_num)
    have hG1 : ContDiffOn ℝ 1
        (Function.uncurry (slice (GR α g) τ)) Work.FTS.EllipticEst.Q0 := hGc.of_le (by norm_num)
    have sp0 : Work.Spaces.DzIter 0
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ
        = Work.Spaces.DzIter 0 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 0 (slice (GR α g) τ) z θ := rfl
    have sp1 : Work.Spaces.DzIter 1
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ
        = Work.Spaces.DzIter 1 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ := by
      change Work.Spaces.DzIter 1 (fun z θ =>
          Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + slice (GR α g) τ z θ) z θ
        = Work.Spaces.DzIter 1 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ
      exact ftau_DzIter_one_add hF1 hG1 z θ hz h1 h2
    have sp2 : Work.Spaces.DzIter 2
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ
        = Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ := by
      change Work.Spaces.DzIter 2 (fun z θ =>
          Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + slice (GR α g) τ z θ) z θ
        = Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ
      exact ftau_DzIter_two_add hFc hGc z θ hz h1 h2
    have hF00 : |Work.Spaces.DzIter 0
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ| ≤ 10 * M :=
      ftau_DzIter_Fstar_le hα hα13 hM 0 (by norm_num) z θ hz h1 h2
    have hF11 : |Work.Spaces.DzIter 1
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ| ≤ 10 * M :=
      ftau_DzIter_Fstar_le hα hα13 hM 1 (by norm_num) z θ hz h1 h2
    have hF22 : |Work.Spaces.DzIter 2
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ| ≤ 10 * M :=
      ftau_DzIter_Fstar_le hα hα13 hM 2 (by norm_num) z θ hz h1 h2
    have hG00 : |Work.Spaces.DzIter 0 (slice (GR α g) τ) z θ| ≤ K := by
      rw [hK]
      exact ftau_DzIter_GR_le hα hα13 hOK τ hτ 0 (by norm_num) z θ hz h1 h2
    have hG11 : |Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ| ≤ K := by
      rw [hK]
      exact ftau_DzIter_GR_le hα hα13 hOK τ hτ 1 (by norm_num) z θ hz h1 h2
    have hG22 : |Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ| ≤ K := by
      rw [hK]
      exact ftau_DzIter_GR_le hα hα13 hOK τ hτ 2 (by norm_num) z θ hz h1 h2
    refine ⟨?_, ?_, ?_⟩
    · calc |Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ z θ|
          = |Work.Spaces.DzIter 0
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ| := rfl
        _ = |Work.Spaces.DzIter 0 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
              + Work.Spaces.DzIter 0 (slice (GR α g) τ) z θ| := by rw [sp0]
        _ ≤ |Work.Spaces.DzIter 0 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
              + |Work.Spaces.DzIter 0 (slice (GR α g) τ) z θ| := abs_add_le _ _
        _ ≤ 10 * M + K := add_le_add hF00 hG00
        _ ≤ 10 * M + |K| := by linarith [le_abs_self K]
    · change |Work.Spaces.DzIter 1
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ|
          ≤ 10 * M + |K|
      calc |Work.Spaces.DzIter 1
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ|
          = |Work.Spaces.DzIter 1 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
              + Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ| := by rw [sp1]
        _ ≤ |Work.Spaces.DzIter 1 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
              + |Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ| := abs_add_le _ _
        _ ≤ 10 * M + K := add_le_add hF11 hG11
        _ ≤ 10 * M + |K| := by linarith [le_abs_self K]
    · calc |Work.Spaces.DzIter 2
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ|
          = |Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
              + Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ| := by rw [sp2]
        _ ≤ |Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
              + |Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ| := abs_add_le _ _
        _ ≤ 10 * M + K := add_le_add hF22 hG22
        _ ≤ 10 * M + |K| := by linarith [le_abs_self K]

end Work.FTS_RegExport.RXT
