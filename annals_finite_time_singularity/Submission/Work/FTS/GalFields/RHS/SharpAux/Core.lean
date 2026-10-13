/-
# `SharpAux/Core` — the pointwise telescoping of `N` along a difference `h = g - g'`

This file contains the *master identity* of `sharp_N_diff`: with

* `F = F_*+g`, `F' = F_*+g'`, `h = g - g'` (so `F = F'+h`),
* `Φ = Φ_s+EllSol g`, `Φ' = Φ_s+EllSol g'` (so `Φ - Φ' = EllSol h`),
* `Z = PhiTil α F Φ`, `Z' = PhiTil α F' Φ'`, `Zs = PhiTil α F_* Φ_s`,
  `Zg = PhiTil α g (EllSol g)`, `Zg' = PhiTil α g' (EllSol g')`, `Δ = PhiTil α h (EllSol h)`

(so that `Z = Zs + Zg`, `Z' = Zs + Zg'`, `Zg = Δ + Zg'` on `{z ≥ 0}`), the difference

`N α F Φ - N α F' Φ'`

telescopes, on the open quadrant `Qd`, into the twenty monomials `Sharp.TRA … Sharp.TED` of
`SharpAux/Defs.lean`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalFields.RHS.SharpAux.Defs
import Submission.Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.Nonlinear.Pieces.L12FK_add_ge0
import Submission.Work.FTS.GalBasis.exists_cc_of_honClass
import Submission.Work.FTS.PhiStar.CoreAux.EVDefs
import Submission.Work.FTS.PhiStar.CoreAux.fields_smooth
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.LocData.L12_add_mul
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.Sharp

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Locality and linearity of the operators on the open quadrant -/

/-- `∂_z` only sees the values on `Q0`. -/
theorem pz_congr_Q0 {f g : Fn} (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    f z θ = g z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
  intro z θ hz h1 h2
  have h1' := Work.FTS.EllipticEst.SmoothOpen.DzIter_congr (F := f) (G := g) h 1 z θ hz h1 h2
  have h2' : Work.Spaces.Dz f z θ = Work.Spaces.Dz g z θ := by
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h1'
  simp only [Work.Spaces.Dz] at h2'
  exact mul_left_cancel₀ (ne_of_gt hz) h2'

/-- `ℛ` only sees the values on `Q0`. -/
theorem Rop_congr_Q0 {α : ℝ} {f g : Fn}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Rop α f z θ = Work.Construction.Rop α g z θ := by
  intro z θ hz h1 h2
  have hpz := pz_congr_Q0 h z θ hz h1 h2
  have hpth := Work.FTS.PhiStar.CoreAux.pth_congr_Q0 h z θ hz h1 h2
  simp only [Work.Construction.Rop]
  rw [h z θ hz h1 h2, hpz, hpth]

/-- `U` only sees the values on `Q0`. -/
theorem Uop_congr_Q0 {α : ℝ} {f g : Fn}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Uop α f z θ = Work.Construction.Uop α g z θ := by
  intro z θ hz h1 h2
  have hpz := pz_congr_Q0 h z θ hz h1 h2
  simp only [Work.Construction.Uop]
  rw [h z θ hz h1 h2, hpz]

/-- `V` only sees the values on `Q0`. -/
theorem Vop_congr_Q0 {f g : Fn}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Vop f z θ = Work.Construction.Vop g z θ := by
  intro z θ hz h1 h2
  have hpth := Work.FTS.PhiStar.CoreAux.pth_congr_Q0 h z θ hz h1 h2
  simp only [Work.Construction.Vop]
  rw [h z θ hz h1 h2, hpth]

/-- Additivity of `∂_z` on two `SmoothOpen` data. -/
theorem pz_add_Q0 {f g : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pz (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pz f z θ + Work.Spaces.pz g z θ := by
  intro z θ hz h1 h2
  have h1' := Work.FTS.EllipticEst.SmoothOpen.DzIter_add hf hg 1 z θ hz h1 h2
  have h2' : Work.Spaces.Dz (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.Dz f z θ + Work.Spaces.Dz g z θ := by
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h1'
  simp only [Work.Spaces.Dz] at h2'
  have h3 : z * Work.Spaces.pz (fun z θ => f z θ + g z θ) z θ
      = z * (Work.Spaces.pz f z θ + Work.Spaces.pz g z θ) := by
    rw [h2']; ring
  exact mul_left_cancel₀ (ne_of_gt hz) h3

/-- Additivity of `∂_θ` on two `SmoothOpen` data. -/
theorem pth_add_Q0 {f g : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pth f z θ + Work.Spaces.pth g z θ :=
  Work.FTS.PhiStar.CoreAux.pth_add_Q0 hf hg

/-- Additivity of `ℛ` on two `SmoothOpen` data. -/
theorem Rop_add_Q0 {α : ℝ} {f g : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Rop α (fun z θ => f z θ + g z θ) z θ
        = Work.Construction.Rop α f z θ + Work.Construction.Rop α g z θ := by
  intro z θ hz h1 h2
  exact Work.FTS.Nonlinear.Pieces.Rop_add_of_diff (pz_add_Q0 hf hg z θ hz h1 h2)
    (pth_add_Q0 hf hg z θ hz h1 h2)

/-- Additivity of `U` on two `SmoothOpen` data. -/
theorem Uop_add_Q0 {α : ℝ} {f g : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Uop α (fun z θ => f z θ + g z θ) z θ
        = Work.Construction.Uop α f z θ + Work.Construction.Uop α g z θ := by
  intro z θ hz h1 h2
  exact Work.FTS.Nonlinear.Pieces.Uop_add_of_diff (pz_add_Q0 hf hg z θ hz h1 h2)

/-- Additivity of `V` on two `SmoothOpen` data. -/
theorem Vop_add_Q0 {f g : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Vop (fun z θ => f z θ + g z θ) z θ
        = Work.Construction.Vop f z θ + Work.Construction.Vop g z θ := by
  intro z θ hz h1 h2
  exact Work.FTS.Nonlinear.Pieces.Vop_add_of_diff (pth_add_Q0 hf hg z θ hz h1 h2)

/-! ## Subtraction of the two moments on `{z ≥ 0}` -/

/-- `L₁₂` is additive on differences of honest profiles, on the closed half-line `z ≥ 0`. -/
theorem L12_sub_ge0 {α : ℝ} {a b d : Fn}
    (haS : Work.FTS.EllipticEst.SmoothOpen a) (hbS : Work.FTS.EllipticEst.SmoothOpen b)
    (hdS : Work.FTS.EllipticEst.SmoothOpen d)
    (ha4 : Work.Spaces.HkMem α 4 a) (hb4 : Work.Spaces.HkMem α 4 b)
    (hd4 : Work.Spaces.HkMem α 4 d) (hd : ∀ z θ : ℝ, d z θ = a z θ - b z θ)
    {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 a z = Work.Construction.L12 d z + Work.Construction.L12 b z := by
  have h1 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ :=
    fun s hs => Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hbS hb4
      (lt_of_le_of_lt hz hs)
  have h2 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * d s θ / s) Work.Spaces.Iθ :=
    fun s hs => Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hdS hd4
      (lt_of_le_of_lt hz hs)
  have h3 : MeasureTheory.IntegrableOn (Work.Construction.L12dens b) (Set.Ioi z) :=
    (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hbS hb4).mono_set
      (Set.Ioi_subset_Ioi hz)
  have h4 : MeasureTheory.IntegrableOn (Work.Construction.L12dens d) (Set.Ioi z) :=
    (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hdS hd4).mono_set
      (Set.Ioi_subset_Ioi hz)
  have hkey := (Work.FTS.LocData.L12_add_mul (c := 1) (a := b) (b := d) (z := z)
    h1 h2 h3 h4).1
  have hcongr : Work.Construction.L12 (fun z θ => b z θ + d z θ) z
      = Work.Construction.L12 a z :=
    Work.FTS.GalBasis.L12_congr_all (fun z θ => by rw [hd z θ]; ring) z
  rw [← hcongr, hkey]
  ring

/-- The angular moment is additive on differences of honest profiles, on `z > 0`. -/
theorem FK_sub {α : ℝ} {a b d : Fn}
    (haS : Work.FTS.EllipticEst.SmoothOpen a) (hbS : Work.FTS.EllipticEst.SmoothOpen b)
    (hdS : Work.FTS.EllipticEst.SmoothOpen d)
    (ha4 : Work.Spaces.HkMem α 4 a) (hb4 : Work.Spaces.HkMem α 4 b)
    (hd4 : Work.Spaces.HkMem α 4 d) (hd : ∀ z θ : ℝ, d z θ = a z θ - b z θ)
    {z : ℝ} (hz : 0 < z) :
    Work.Construction.FK a z = Work.Construction.FK d z + Work.Construction.FK b z := by
  have hb : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * b z θ / z)
      Work.Spaces.Iθ :=
    Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hbS hb4 hz
  have hd' : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * d z θ / z)
      Work.Spaces.Iθ :=
    Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hdS hd4 hz
  have hkey := Work.FTS.GalFields.RHS.FK_add_of_slices (a := b) (b := d) (ne_of_gt hz) hb hd'
  have hcongr : Work.Construction.FK (fun z θ => b z θ + d z θ) z
      = Work.Construction.FK a z := by
    simp only [Work.Construction.FK]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [hd z θ]; ring
  rw [← hcongr, hkey]
  ring

/-! ## Smoothness of the potentials -/

/-- `z ↦ L₁₂(g)(z)` is `C^∞` on `Q0` for a Galerkin-elliptic package. -/
theorem smoothOpen_L12_gal {α Ce : ℝ} {g Φg : Fn}
    (hα : 0 < α) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => Work.Construction.L12 g z) :=
  Work.FTS.NonlinRows.smoothOpen_L12_radial hα hell.smooth hell.V.1.1

/-- `Φ̃_g = PhiTil α g Φg` is `C^∞` on `Q0`. -/
theorem smoothOpen_PhiTil {α Ce : ℝ} {g Φg : Fn}
    (hα : 0 < α) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α g Φg) := by
  have hEq : Work.Construction.PhiTil α g Φg = fun z θ =>
      Φg z θ - (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g z := rfl
  rw [hEq]
  simp only [Work.Construction.s2]
  refine Work.FTS.NonlinRows.smoothOpen_sub hell.smooth ?_
  exact Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul
    (Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (4 * α))
      Work.FTS.GalFields.RHS.smoothOpen_sin_two)
    (smoothOpen_L12_gal hα hell)

/-- `Φ̃_* = PhiTil α F_* Φs` is `C^∞` on `Q0`. -/
theorem smoothOpen_PhiTil_star {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) := by
  have hV : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) :=
    (Work.FTS.PhiStar.CoreAux.fields_smooth hα hα1 hstar.smooth).2.2.1
  have hL : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hstar.smooth hV
  have hEq : Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs = fun z θ =>
      Φs z θ - (1 / (4 * α)) * Work.Construction.s2 θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z := rfl
  rw [hEq]
  simp only [Work.Construction.s2]
  refine Work.FTS.NonlinRows.smoothOpen_sub hstar.smooth ?_
  exact Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul
    (Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (4 * α))
      Work.FTS.GalFields.RHS.smoothOpen_sin_two)
    hL

end Work.FTS.GalFields.RHS.Sharp
