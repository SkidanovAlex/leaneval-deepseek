import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Have
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.Gsing_ode
import Submission.Work.Elliptic.GsingFuncs
import Submission.Work.Elliptic.L12_eq_radial
import Submission.Work.FTS.EllipticEst.Gsing_deriv_rel
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.Fstar_contDiffOn
import Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.Defs
import Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.Fstar_div_integrable_of_sol_Hk
import Submission.Work.FTS.EllipticEst.Cert.GsingSmooth.contDiffOn_primitive_Ioi0
import Submission.Work.FTS.EllipticEst.Cert.GsingSmooth.contDiffOn_tailIntegral_Ioi0
import Submission.Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The smooth angular integrand of the moment

`Work.FTS.EllipticEst.Cert.FstarInt α Ψ` is the reformulation of
`bslOp α Ψ · sinθcos²θ` in which the `tan`-pole has been cancelled by the weight: it is
smooth on a neighbourhood of the closed quadrant as soon as `Ψ` is.  This is the first
step of the smoothness of the angular moment `F_*`: the moment of the source is the
`θ`-integral of a *smooth* function of `(z,θ)`, and parametric integrals of smooth
functions are smooth (`contDiffOn_infty_integral_Itheta_Ioi_neg_one`). -/

/-- **The smooth integrand is `SmoothNbhd`.**  `FstarInt α Ψ` is a sum of products of the
smooth functions `pzIter 2 Ψ`, `pz Ψ`, `pthIter 2 Ψ`, `pth Ψ`, `Ψ`, polynomials in `z` and
the angular data `sin`, `cos`; the `SmoothNbhd` toolkit assembles it. -/
theorem FstarInt_smoothNbhd (α : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    Work.Spaces.SmoothNbhd (FstarInt α Ψ) := by
  have h2 : Work.Spaces.SmoothNbhd (Work.Spaces.pzIter 2 Ψ) :=
    Work.Spaces.smoothNbhd_pzIter hΨ 2
  have h1 : Work.Spaces.SmoothNbhd (Work.Spaces.pz Ψ) := hΨ.pz
  have hd2 : Work.Spaces.SmoothNbhd (Work.Spaces.pthIter 2 Ψ) := smoothNbhd_pthIter hΨ 2
  have hd1 : Work.Spaces.SmoothNbhd (Work.Spaces.pth Ψ) := hΨ.pth
  have hS : Work.Spaces.SmoothNbhd (fun _ θ : ℝ => Real.sin θ) :=
    smoothNbhd_snd_comp _ Real.contDiff_sin
  have hC : Work.Spaces.SmoothNbhd (fun _ θ : ℝ => Real.cos θ) :=
    smoothNbhd_snd_comp _ Real.contDiff_cos
  have hsin2 : Work.Spaces.SmoothNbhd (fun _ θ : ℝ => Work.Elliptic.sinCos2 θ) := by
    refine SmoothNbhd_congr (smoothNbhd_mul' hS (smoothNbhd_mul' hC hC)) ?_
    intro z θ
    simp only [Work.Elliptic.sinCos2]
    ring
  have hsc : Work.Spaces.SmoothNbhd
      (fun _ θ : ℝ => Real.sin θ * (Real.sin θ * Real.cos θ)) :=
    smoothNbhd_mul' hS (smoothNbhd_mul' hS hC)
  -- the five summands
  have ht1 : Work.Spaces.SmoothNbhd (fun z θ : ℝ =>
      Work.Elliptic.sinCos2 θ * (-(α ^ 2) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))) :=
    smoothNbhd_mul' hsin2 (smoothNbhd_const_mul (-(α ^ 2))
      (smoothNbhd_mul' (smoothNbhd_pow_fst 2) h2))
  have ht2 : Work.Spaces.SmoothNbhd (fun z θ : ℝ =>
      Work.Elliptic.sinCos2 θ * (-(α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ))) :=
    smoothNbhd_mul' hsin2 (smoothNbhd_const_mul (-(α * (5 + α)))
      (smoothNbhd_mul' smoothNbhd_fst h1))
  have ht3 : Work.Spaces.SmoothNbhd (fun z θ : ℝ =>
      Work.Elliptic.sinCos2 θ * (-(Work.Spaces.pthIter 2 Ψ z θ))) :=
    smoothNbhd_mul' hsin2 (smoothNbhd_neg hd2)
  have ht4 : Work.Spaces.SmoothNbhd (fun z θ : ℝ =>
      Work.Elliptic.sinCos2 θ * (-(6 * Ψ z θ))) :=
    smoothNbhd_mul' hsin2 (smoothNbhd_neg (smoothNbhd_const_mul 6 hΨ))
  have ht5 : Work.Spaces.SmoothNbhd (fun z θ : ℝ =>
      Real.sin θ * Ψ z θ
        + Real.sin θ * (Real.sin θ * Real.cos θ) * Work.Spaces.pth Ψ z θ) :=
    smoothNbhd_add (smoothNbhd_mul' hS hΨ) (smoothNbhd_mul' hsc hd1)
  have hall : Work.Spaces.SmoothNbhd (fun z θ : ℝ =>
      Work.Elliptic.sinCos2 θ * (-(α ^ 2) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      + Work.Elliptic.sinCos2 θ * (-(α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ))
      + Work.Elliptic.sinCos2 θ * (-(Work.Spaces.pthIter 2 Ψ z θ))
      + Work.Elliptic.sinCos2 θ * (-(6 * Ψ z θ))
      + (Real.sin θ * Ψ z θ
          + Real.sin θ * (Real.sin θ * Real.cos θ) * Work.Spaces.pth Ψ z θ)) :=
    (((ht1.add ht2).add ht3).add ht4).add ht5
  refine SmoothNbhd_congr hall ?_
  intro z θ
  rw [FstarInt_apply]
  ring

/-- The angular moment of the source is the integral of the smooth integrand.  On the open
interval the two integrands are *equal* (`bslOp_mul_sinCos2_eq`), so the claim follows from
`Ioo 0 (π/2) =ᵐ Iθ`. -/
theorem Fstar_eq_integral_FstarInt' (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hΨ : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    ∀ z, 0 < z →
      Work.Elliptic.Fstar F z = ∫ θ in Work.Spaces.Iθ, FstarInt α Ψ z θ := by
  intro z hz
  have hae : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[MeasureTheory.volume] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc
  have hslice : ContDiffOn ℝ ⊤ (fun θ' : ℝ => Ψ z θ') (Set.Icc 0 (π / 2)) :=
    Work.Elliptic.contDiffOn_slice_of_smoothNbhd Ψ hΨ (by linarith [hz])
  calc Work.Elliptic.Fstar F z
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), F z θ * Work.Elliptic.sinCos2 θ := by
        rw [Work.Elliptic.Fstar]
        exact (MeasureTheory.setIntegral_congr_set hae).symm
    _ = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), FstarInt α Ψ z θ := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
        rw [← hsol.1 z hz θ hθ.1 hθ.2]
        have hcos : Real.cos θ ≠ 0 := by
          refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
          · linarith [Real.pi_pos, hθ.1]
          · linarith [Real.pi_pos, hθ.2]
        have hdiff : DifferentiableAt ℝ (fun θ' : ℝ => Ψ z θ') θ :=
          (hslice.contDiffAt (Icc_mem_nhds hθ.1 hθ.2)).differentiableAt (by simp)
        exact bslOp_mul_sinCos2_eq α Ψ hcos hdiff
    _ = ∫ θ in Work.Spaces.Iθ, FstarInt α Ψ z θ :=
        MeasureTheory.setIntegral_congr_set hae

/-- `r ↦ F_*(F)(r)/r` is integrable on `(0,∞)`. -/
theorem Fstar_div_integrable (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ)
    (hmem : Work.Spaces.HkMem α k F) :
    MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) :=
  FstarSmooth.Fstar_div_integrable_of_sol_Hk α k F Ψ hα hsm hsol hmem

/-- A scalar multiple of a `C^n` function on `ℝ` is `C^n`. -/
theorem contDiffOn_const_mul_real {c : ℝ} {m : ℕ} {f : ℝ → ℝ} {s : Set ℝ}
    (hf : ContDiffOn ℝ m f s) : ContDiffOn ℝ m (fun z => c * f z) s := by
  refine (hf.mul (contDiffOn_const (c := c))).congr ?_
  intro z _
  ring

/-! ## Piece 1: `F_*` is `C^∞` on `(0,∞)` -/

/-- The angular moment of the source of a solution of (PolarBSL) with `Ψ` smooth on a
neighbourhood of the closed quadrant is `C^n` on `(0,∞)` for every `n`. -/
theorem Fstar_smooth_of_bslSol (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) := by
  intro m
  have hInt := Fstar_eq_integral_FstarInt' α F Ψ hsm hsol
  have hsmI : Work.Spaces.SmoothNbhd (FstarInt α Ψ) := FstarInt_smoothNbhd α Ψ hsm
  have hbig : ContDiffOn ℝ ∞
      (fun z => ∫ θ in Work.Spaces.Iθ, FstarInt α Ψ z θ * (1 : ℝ)) (Set.Ioi (-1)) :=
    Work.FTS.EllipticEst.contDiffOn_infty_integral_Itheta_Ioi_neg_one (FstarInt α Ψ)
      (fun _ => (1 : ℝ)) hsmI continuousOn_const
  have hmono : ContDiffOn ℝ m
      (fun z => ∫ θ in Work.Spaces.Iθ, FstarInt α Ψ z θ * (1 : ℝ)) (Set.Ioi 0) :=
    (contDiffOn_infty.mp hbig m).mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))
  refine hmono.congr ?_
  intro z hz
  rw [hInt z hz]
  simp only [mul_one]

/-! ## Piece 2: `Gsing α F` is `C^∞` on `(0,∞)` -/

/-- The primitive of `s ↦ s^{(5-α)/α} F_*(s)`, i.e. `Jfun`, is `C^∞` on `(0,∞)`. -/
theorem Jfun_contDiffOn (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0))
    (hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioi 0)) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Jfun α F) (Set.Ioi 0) := by
  -- the integrand `h s = s^{(5-α)/α} F_*(s)` is smooth on `(0,∞)`
  have hh : ∀ m : ℕ,
      ContDiffOn ℝ m (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (Set.Ioi 0) := by
    intro m
    exact (contDiffOn_id.rpow_const_of_ne (fun z hz => ne_of_gt hz)).mul (hFsm m)
  -- and it is interval integrable on `(0,z]` for every `z > 0`
  have hloc : ∀ z ∈ Set.Ioi (0 : ℝ),
      IntervalIntegrable (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        MeasureTheory.volume 0 z := by
    intro z hz
    have hzpos : (0 : ℝ) < z := hz
    have hgIoc : IntegrableOn (fun x : ℝ => Work.Elliptic.Fstar F x / x) (Set.Ioc (0 : ℝ) z) :=
      hFint.mono_set (fun x hx => hx.1)
    have hIcc : IntegrableOn (fun x : ℝ => Work.Elliptic.Fstar F x / x) (Set.Icc (0 : ℝ) z) :=
      (integrableOn_Icc_iff_integrableOn_Ioc).mpr hgIoc
    have hcont' : ContinuousOn (fun x : ℝ => x ^ ((5 - α) / α + 1)) (Set.Icc (0 : ℝ) z) := by
      have hc1 : (5 - α) / α + 1 = 5 / α := by field_simp; ring
      refine (Real.continuous_rpow_const ?_).continuousOn
      rw [hc1]
      exact le_of_lt (div_pos (by norm_num) hα)
    have hmul : IntegrableOn
        (fun x : ℝ => (Work.Elliptic.Fstar F x / x) * x ^ ((5 - α) / α + 1))
        (Set.Icc (0 : ℝ) z) := hIcc.mul_continuousOn hcont' isCompact_Icc
    have hmul' : IntegrableOn
        (fun x : ℝ => (Work.Elliptic.Fstar F x / x) * x ^ ((5 - α) / α + 1))
        (Set.Ioc (0 : ℝ) z) := hmul.mono_set Set.Ioc_subset_Icc_self
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hzpos.le).mpr ?_
    refine hmul'.congr_fun ?_ measurableSet_Ioc
    intro x hx
    have hxpos : 0 < x := hx.1
    have hrw : x ^ ((5 - α) / α + 1) = x ^ ((5 - α) / α) * x := by
      rw [Real.rpow_add hxpos, Real.rpow_one]
    show Work.Elliptic.Fstar F x / x * x ^ ((5 - α) / α + 1)
      = x ^ ((5 - α) / α) * Work.Elliptic.Fstar F x
    rw [hrw]
    field_simp
  have h := GsingSmooth.contDiffOn_primitive_Ioi0
    (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) hh hloc
  intro m
  exact (h m).congr fun z _ => rfl

/-- `Gsing α F` is `C^n` on `(0,∞)` for every `n`. -/
theorem Gsing_contDiffOn (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0))
    (hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioi 0)) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0) := by
  -- the tail integral `L12rad F z = ∫_z^∞ F_*(r)/r dr` is `C^∞`
  have hg : ∀ m : ℕ, ContDiffOn ℝ m (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) := by
    intro m
    exact (hFsm m).div contDiffOn_id (fun z hz => ne_of_gt hz)
  have hL12rad : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.L12rad F) (Set.Ioi 0) :=
    GsingSmooth.contDiffOn_tailIntegral_Ioi0 (fun r : ℝ => Work.Elliptic.Fstar F r / r) hg hFint
  -- hence `L12 F = 3 L12rad F`, hence `Gstar α F = -(1/(4α)) L12 F`
  have hL12 : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.L12 F) (Set.Ioi 0) := by
    intro m
    refine (contDiffOn_const_mul_real (c := (3 : ℝ)) (hL12rad m)).congr fun z _ => ?_
    exact Work.Elliptic.L12_eq_radial F z
  have hGstar : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gstar α F) (Set.Ioi 0) := by
    intro m
    exact (contDiffOn_const_mul_real (c := -(1 / (4 * α))) (hL12 m)).congr fun z _ => rfl
  -- the homogeneous factor `Abar` and the primitive `Jfun`
  have hAbar : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Abar α) (Set.Ioi 0) := by
    intro m
    exact contDiffOn_const_mul_real (c := -(3 / (4 * α)))
      (contDiffOn_id.rpow_const_of_ne (fun z hz => ne_of_gt hz))
  have hJfun := Jfun_contDiffOn α F hα hFsm hFint
  have hGbar : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi 0) := by
    intro m
    exact ((hAbar m).mul (hJfun m)).congr fun z _ => rfl
  intro m
  exact (hGstar m).add (hGbar m)

/-! ## Assembly -/

theorem Gsing_identities_eh (k : ℕ) : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 / 4 → Work.FTS.EllipticEst.EllHyp α k F Ψ →
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0)) ∧
      (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0)) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ),
        α * z * deriv (Work.Elliptic.Gsing α F) z = -5 * Work.Elliptic.Gbar α F z) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ),
        α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
          = (15 / 4) * Work.Elliptic.Fstar F z + 5 * (5 + α) * Work.Elliptic.Gbar α F z) := by
  intro α F Ψ hα hα4 hHyp
  have hα1 : α ≤ 1 := by linarith
  -- the three analytic inputs
  have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    Fstar_smooth_of_bslSol α F Ψ hHyp.smoothNbhd hHyp.sol
  have hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioi 0) :=
    Fstar_div_integrable α k F Ψ hα hHyp.smoothNbhd hHyp.sol hHyp.memF
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => Work.Elliptic.L12 F z') (-(3 * Work.Elliptic.Fstar F z / z)) z :=
    Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts F hFsm hFint
  have hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z := by
    intro z hz
    have hdiff : DifferentiableAt ℝ (Work.Elliptic.Fstar F) z :=
      ((hFsm 1).differentiableOn_one).differentiableAt (isOpen_Ioi.mem_nhds hz)
    exact hdiff.hasDerivAt
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z :=
    Jfun_hasDerivAt_of_Fstar α F hFsm hFint hα hα1
  -- the two identities
  have hfirst := Work.FTS.EllipticEst.Gsing_deriv_rel α F hα hL12 hFc hJ
  have hsecond := Work.Elliptic.Gsing_ode α F hα hL12 hFc hJ
  refine ⟨hFsm, Gsing_contDiffOn α F hα hFsm hFint, hfirst, ?_⟩
  intro z hz
  have h1 := hsecond z hz
  have h2 : α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
      = -(5 * (5 + α) * Work.Elliptic.Gbar α F z) := by
    rw [show α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
        = (5 + α) * (α * z * deriv (Work.Elliptic.Gsing α F) z) by ring,
      hfirst z hz]
    ring
  linarith [h1, h2]

end Work.FTS.EllipticEst.Cert
