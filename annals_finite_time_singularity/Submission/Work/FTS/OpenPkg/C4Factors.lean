/-
# The `C⁴`-smoothness of the factors of the N4 pieces, from the a-priori data

`Work.FTS.OpenPkg.FourFactors` collects the `C^4` facts about the factors of the 27 pieces of
the §8 assembly.  This file **inhabits** it from the data of the primed route
(`GalClass`, `StarPkgo`, `EllPkgGo`), i.e. it proves:

* `L₁₂(g)` is `C^5` on `(0,∞)` — the tower `D_z^{k+1}L₁₂(g) = -Qang g k`
  (`Work.FTS.Nonlinear.Pieces.L12_dzdIter_moment`) identifies `∂_zL₁₂(g) = -FK(g)/z`, and
  `FK g` is `C^4` (`RNP24.fk_contDiffOn_four`, from `SmoothQuad g` and `HkMem α 6 g`);
* the radial functions `L₁₂(F_*)`, `FK(F_*)` and `F_*` are smooth, being explicit
  (`L12_Fstar_eq`, `FK_Fstar`, `SmoothQuad_Fstar`);
* the residuals `Φ̃_g = PhiTil α g Φg` and `Φ̃_* = PhiTil α (F_*) Φs` are `C^5`, hence their
  images under `Rop`, `Uop`, `Vop` (each of which costs one order) are `C^4`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.OpenPkg.FourFactors
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.fk_contDiffOn_four
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg
import Submission.Work.FTS.EllipticEst.Uop_bound_reg
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.LocData.SmoothQuad_Fstar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary bridges -/

/-- `C^∞` on the open quadrant gives `C^n` there, for every `n : ℕ`. -/
theorem contDiffOn_nat_of_smoothOpen {F : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen F) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry F) Q0 :=
  h.of_le (by simp [Work.Stability.smoothOrder])

/-- `SmoothQuad` gives `SmoothOpen`, hence `C^n` on the open quadrant. -/
theorem contDiffOn_nat_of_smoothQuad {F : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad F) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry F) Q0 :=
  contDiffOn_nat_of_smoothOpen (Work.FTS.EllipticEst.smoothOpen_of_smoothQuad h) n

/-- A radial function, as a function of the two self-similar variables. -/
theorem contDiffOn_uncurry_radial {R : ℝ → ℝ} {n : ℕ} (h : ContDiffOn ℝ n R (Set.Ioi 0)) :
    ContDiffOn ℝ n (Function.uncurry (Rad R)) Q0 :=
  h.comp contDiffOn_fst (fun p hp => hp.1)

/-- `(z,θ) ↦ sin θ / cos θ` is smooth on the quadrant (where `cos θ > 0`). -/
theorem contDiffOn_sin_div_cos_Q0 (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2) Q0 := by
  have hsin : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2) Q0 :=
    ((Real.contDiff_sin.comp contDiff_snd).contDiffOn).of_le le_top
  have hcos : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.cos p.2) Q0 :=
    ((Real.contDiff_cos.comp contDiff_snd).contDiffOn).of_le le_top
  exact hsin.div hcos (fun p hp => ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩))

/-! ## The angular moment `FK = Qang g 0` and the derivative of `L₁₂` -/

/-- The two normalisations of the angular weight agree. -/
theorem Ktheta_eq_K : Work.Elliptic.Ktheta = Work.Spaces.K := by
  funext θ
  simp [Work.Elliptic.Ktheta, Work.Spaces.K]

/-- `Work.Elliptic.Qang g 0` is `Work.Construction.FK g`. -/
theorem Qang_zero_eq_FK (g : ℝ → ℝ → ℝ) : Work.Elliptic.Qang g 0 = Work.Construction.FK g := by
  funext z
  rw [Work.Elliptic.Qang, Work.Construction.FK]
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [Work.Spaces.DzIter_zero, Ktheta_eq_K]
  ring

/-- **The derivative of `L₁₂(g)`**: `∂_z L₁₂(g)(z) = -FK(g)(z)/z` for `z > 0`, from the tower
`D_z L₁₂(g) = -Qang g 0`. -/
theorem deriv_L12_eq {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    (h0 : Work.Construction.L12 g 0 = 0) {z : ℝ} (hz : 0 < z) :
    deriv (fun z' => Work.Construction.L12 g z') z = -Work.Construction.FK g z / z := by
  have hmom := (Work.FTS.Nonlinear.Pieces.L12_dzdIter_moment α hα hα1 hsm hmem h0).1 0
    (by norm_num) z hz
  rw [Qang_zero_eq_FK] at hmom
  rw [Work.Elliptic.DzdIter_succ, Work.Elliptic.DzdIter_zero] at hmom
  show deriv (fun z' => Work.Construction.L12 g z') z = -Work.Construction.FK g z / z
  rw [eq_div_iff (ne_of_gt hz), mul_comm]
  rw [Work.Elliptic.Dzd] at hmom
  linarith [hmom]

/-- **`L₁₂(g)` is `C^5` on `(0,∞)`.** -/
theorem contDiffOn_five_L12 {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem6 : Work.Spaces.HkMem α 6 g)
    (h0 : Work.Construction.L12 g 0 = 0) :
    ContDiffOn ℝ 5 (fun z => Work.Construction.L12 g z) (Set.Ioi 0) := by
  have hmem5 : Work.Spaces.HkMem α 5 g := Work.GalerkinFix.RegQ.HkMem_mono_Q (k := 5) hsm hmem6
  have hmem4 : Work.Spaces.HkMem α 4 g := Work.GalerkinFix.RegQ.HkMem_mono_Q (k := 4) hsm hmem5
  have hFK : ContDiffOn ℝ 4 (fun z => Work.Construction.FK g z) (Set.Ioi 0) :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.fk_contDiffOn_four hα hα1 hsm hmem6
  have hG : ContDiffOn ℝ 4 (fun z => -Work.Construction.FK g z / z) (Set.Ioi 0) :=
    (hFK.neg).div contDiffOn_id (fun z hz => ne_of_gt hz)
  refine Work.FTS.EllipticEst.UopHk.contDiffOn_succ_of_hasDerivAt (m := 4) ?_ hG
  intro z hz
  have hd := (Work.FTS.Nonlinear.Pieces.L12_dzdIter_moment α hα hα1 hsm hmem4 h0).2 0
    (by norm_num) z hz
  exact (hd.hasDerivAt).congr_deriv (deriv_L12_eq hα hα1 hsm hmem4 h0 hz)

/-- The two-variable version of `contDiffOn_five_L12`. -/
theorem contDiffOn_uncurry_five_L12 {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem6 : Work.Spaces.HkMem α 6 g)
    (h0 : Work.Construction.L12 g 0 = 0) :
    ContDiffOn ℝ 5 (Function.uncurry (Rad (Work.Construction.L12 g))) Q0 :=
  contDiffOn_uncurry_radial (contDiffOn_five_L12 hα hα1 hsm hmem6 h0)

/-! ## The radial functions `L₁₂(F_*)`, `FK g`, `FK(F_*)` -/

/-- `L₁₂(F_*) = 2α/(1+z)` is smooth on `(0,∞)`, hence `C^n` on the quadrant. -/
theorem contDiffOn_uncurry_L12Fstar (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (Rad (Work.Construction.L12 (Work.Construction.Fstar α))))
      Q0 := by
  have hR : ContDiffOn ℝ n (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi 0) :=
    contDiffOn_const.div (contDiffOn_const.add contDiffOn_id)
      (fun z hz => ne_of_gt (by linarith [Set.mem_Ioi.mp hz] : (0 : ℝ) < 1 + z))
  refine (contDiffOn_uncurry_radial hR).congr (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  exact Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hp.1)

/-- `FK g` is `C^4` on the quadrant. -/
theorem contDiffOn_uncurry_four_FKg {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem6 : Work.Spaces.HkMem α 6 g) :
    ContDiffOn ℝ 4 (Function.uncurry (Rad (Work.Construction.FK g))) Q0 :=
  contDiffOn_uncurry_radial
    (Work.FTS.Nonlinear.Pieces.RNP.RNP24.fk_contDiffOn_four hα hα1 hsm hmem6)

/-- `FK(F_*) = α·2z/(1+z)²` is smooth on the quadrant. -/
theorem contDiffOn_uncurry_FKFstar (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (Rad (Work.Construction.FK (Work.Construction.Fstar α))))
      Q0 := by
  have hR : ContDiffOn ℝ n (fun z : ℝ => α * (2 * z / (1 + z) ^ 2)) (Set.Ioi 0) := by
    refine contDiffOn_const.mul ?_
    exact (contDiffOn_const.mul contDiffOn_id).div ((contDiffOn_const.add contDiffOn_id).pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt (by linarith [Set.mem_Ioi.mp hz] : (0 : ℝ) < 1 + z)))
  refine (contDiffOn_uncurry_radial hR).congr (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  exact Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1

/-! ## The fixed profile and the perturbation, and their operators -/

/-- `F_*` and its two first-order operators are smooth on the quadrant. -/
theorem contDiffOn_Fstar_ops (α : ℝ) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.Fstar α)) Q0 ∧
    ContDiffOn ℝ 4 (Function.uncurry (Work.Spaces.pth (Work.Construction.Fstar α))) Q0 ∧
    ContDiffOn ℝ 4 (Function.uncurry (Work.Spaces.Dz (Work.Construction.Fstar α))) Q0 := by
  have h4 := contDiffOn_nat_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α) 4
  have h5 := contDiffOn_nat_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α) 5
  exact ⟨h4, Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pth_fin Work.FTS.EllipticEst.isOpen_Q0 h5,
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_Dz_fin Work.FTS.EllipticEst.isOpen_Q0 h5⟩

/-- `g` and its three first-order operators are `C^4` on the quadrant. -/
theorem contDiffOn_g_ops {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g) :
    ContDiffOn ℝ 4 (Function.uncurry g) Q0 ∧
    ContDiffOn ℝ 4 (Function.uncurry (Work.Spaces.pth g)) Q0 ∧
    ContDiffOn ℝ 4 (Function.uncurry (Work.Spaces.Dz g)) Q0 ∧
    ContDiffOn ℝ 4 (Function.uncurry (Work.Spaces.Dth g)) Q0 := by
  have h5 := contDiffOn_nat_of_smoothQuad hsm 5
  have hpth := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pth_fin Work.FTS.EllipticEst.isOpen_Q0 h5
  have hDz := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_Dz_fin Work.FTS.EllipticEst.isOpen_Q0 h5
  exact ⟨contDiffOn_nat_of_smoothQuad hsm 4, hpth, hDz,
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_Dth_fin Work.FTS.EllipticEst.isOpen_Q0 h5⟩

/-! ## The residuals `Φ̃` and the operators `Rop`, `Uop`, `Vop` -/

/-- `Φ̃ = PhiTil α F Φ = Φ - (1/(4α))·sin(2θ)·L₁₂(F)` is `C^5` once `Φ` is `SmoothOpen` and
`L₁₂(F)` is `C^5` on `(0,∞)`. -/
theorem contDiffOn_five_PhiTil {α : ℝ} {F Φ : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    (hL12 : ContDiffOn ℝ 5 (Function.uncurry (Rad (Work.Construction.L12 F))) Q0) :
    ContDiffOn ℝ 5 (Function.uncurry (Work.Construction.PhiTil α F Φ)) Q0 := by
  have hΦ5 := contDiffOn_nat_of_smoothOpen hΦ 5
  have hθ : ContDiffOn ℝ 5 (Function.uncurry
      (fun z θ => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z)) Q0 :=
    (contDiffOn_const.mul (contDiffOn_s2_Q0 5)).mul hL12
  refine (hΦ5.sub hθ).congr (fun p _ => ?_)
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry, Work.Construction.PhiTil, Work.Construction.Theta,
    Work.Construction.s2]

/-- `ℛ(Ψ)` is `C^4` once `Ψ` is `C^5` (the division by `cos θ` is harmless on the quadrant). -/
theorem contDiffOn_four_Rop {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ 5 (Function.uncurry Ψ) Q0) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.Rop α Ψ)) Q0 := by
  have hz : IsOpen Q0 := Work.FTS.EllipticEst.isOpen_Q0
  have hpz := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pz_fin hz hΨ
  have hpth := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pth_fin hz hΨ
  have hsin : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => Real.sin p.2) Q0 :=
    ((Real.contDiff_sin.comp contDiff_snd).contDiffOn).of_le le_top
  have hcos : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => Real.cos p.2) Q0 :=
    ((Real.contDiff_cos.comp contDiff_snd).contDiffOn).of_le le_top
  have hΨ4 : ContDiffOn ℝ 4 (Function.uncurry Ψ) Q0 := hΨ.of_le (m := 4) (by norm_num)
  have h1 : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p) Q0 :=
    ((contDiffOn_const (c := (2 : ℝ))).mul hsin).mul hΨ4
  have h2 : ContDiffOn ℝ 4
      (fun p : ℝ × ℝ => α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p) Q0 :=
    (((contDiffOn_const (c := α)).mul hsin).mul contDiffOn_fst).mul hpz
  have h3 : ContDiffOn ℝ 4
      (fun p : ℝ × ℝ => Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p) Q0 :=
    hcos.mul hpth
  have hnum := (h1.add h2).add h3
  have hcosne : ∀ p ∈ Q0, Real.cos p.2 ≠ 0 := by
    intro p hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩)
  refine ((hnum.div hcos hcosne)).congr (fun p _ => ?_)
  rcases p with ⟨z, θ⟩
  show (2 * Real.sin θ * Ψ z θ + α * Real.sin θ * z * Work.Spaces.pz Ψ z θ
      + Real.cos θ * Work.Spaces.pth Ψ z θ) / Real.cos θ
    = Work.Construction.Rop α Ψ z θ
  rw [Work.Construction.Rop]

/-- `U(Ψ) = -3Ψ - α z ∂_zΨ` is `C^4` once `Ψ` is `C^5`. -/
theorem contDiffOn_four_Uop {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ 5 (Function.uncurry Ψ) Q0) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.Uop α Ψ)) Q0 := by
  have hz : IsOpen Q0 := Work.FTS.EllipticEst.isOpen_Q0
  have hpz := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pz_fin hz hΨ
  have h1 : ContDiffOn ℝ 4 (Function.uncurry Ψ) Q0 := hΨ.of_le (m := 4) (by norm_num)
  refine ((((contDiffOn_const (c := (-3 : ℝ))).mul h1).sub
    (((contDiffOn_const (c := α)).mul contDiffOn_fst).mul hpz))).congr (fun p _ => ?_)
  rcases p with ⟨z, θ⟩
  show -3 * Ψ z θ - α * z * Work.Spaces.pz Ψ z θ = Work.Construction.Uop α Ψ z θ
  rw [Work.Construction.Uop]

/-- `V(Ψ) = ∂_θΨ - tan θ·Ψ` is `C^4` once `Ψ` is `C^5`. -/
theorem contDiffOn_four_Vop {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ 5 (Function.uncurry Ψ) Q0) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.Vop Ψ)) Q0 := by
  have hz : IsOpen Q0 := Work.FTS.EllipticEst.isOpen_Q0
  have hpth := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pth_fin hz hΨ
  have htan : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2) Q0 :=
    contDiffOn_sin_div_cos_Q0 4
  have h1 : ContDiffOn ℝ 4 (Function.uncurry Ψ) Q0 := hΨ.of_le (m := 4) (by norm_num)
  refine (hpth.sub (htan.mul h1)).congr (fun p _ => ?_)
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry, Work.Construction.Vop, Real.tan_eq_sin_div_cos]

/-! ## The bundle -/

/-- **`FourFactors` is inhabited by the a-priori data.** -/
theorem fourFactors_of_gal {α Cs Ce : ℝ} {g Φs Φg : Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hgal : Work.FTS.Nonlin.GalClass α g)
    (hstar : Work.FTS.VocabO.StarPkgo α Cs Φs)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    FourFactors α g Φs Φg := by
  have hsm : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 g := hgal.reg.2.1
  have h0 : Work.Construction.L12 g 0 = 0 := hgal.l12
  obtain ⟨hF, hpthF, hDzF⟩ := contDiffOn_Fstar_ops α
  obtain ⟨hg, hpthg, hDzg, hDthg⟩ := contDiffOn_g_ops hsm
  -- the residuals
  have hL12g5 := contDiffOn_uncurry_five_L12 hα hα1 hsm hmem6 h0
  have hΦg : Work.FTS.EllipticEst.SmoothOpen Φg := hell.smooth
  have hΦs : Work.FTS.EllipticEst.SmoothOpen Φs := hstar.smooth
  have hPhiTg := contDiffOn_five_PhiTil (F := g) (Φ := Φg) hα hΦg hL12g5
  have hL12F5 := contDiffOn_uncurry_L12Fstar α hα hα1 5
  have hPhiTs := contDiffOn_five_PhiTil (F := Work.Construction.Fstar α) (Φ := Φs) hα hΦs hL12F5
  exact
    { hg := hg
      hpthg := hpthg
      hDzg := hDzg
      hDthg := hDthg
      hF := hF
      hpthF := hpthF
      hDzF := hDzF
      hL12g := hL12g5.of_le (by norm_num)
      hL12F := contDiffOn_uncurry_L12Fstar α hα hα1 4
      hFKg := contDiffOn_uncurry_four_FKg hα hα1 hsm hmem6
      hFKF := contDiffOn_uncurry_FKFstar α hα hα1 4
      hRopTg := contDiffOn_four_Rop hPhiTg
      hUopTg := contDiffOn_four_Uop hPhiTg
      hVopTg := contDiffOn_four_Vop hPhiTg
      hRopTs := contDiffOn_four_Rop hPhiTs
      hUopTs := contDiffOn_four_Uop hPhiTs
      hVopTs := contDiffOn_four_Vop hPhiTs }

end Work.FTS.OpenPkg
