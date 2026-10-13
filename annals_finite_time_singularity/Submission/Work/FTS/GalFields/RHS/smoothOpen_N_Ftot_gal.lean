/-
# `smoothOpen_N_Ftot` needs the `GalClass`-strength hypothesis on `g`

`Submission/Work/FTS/GalFields/RHS/smoothOpen_N_Ftot.lean` (the assigned file) asks for

  `SmoothOpen (N α (Ftot α g) (fun z θ => Φs z θ + Φg z θ))`

from the *open-quadrant* elliptic packages `hell : EllPkgGo α Ce g Φg`,
`hstar : StarPkgo2 α Cs Φs` together with `hg : SmoothOpen g`.  That statement is
**under-hypothesised**; the diagnosis is recorded in `RHS/NOTES_smoothOpen_N_Ftot_FALSE.md`
(the same defect that was already established, and repaired, for the sibling
`RHS/smoothOpen_FK_of_pkg.lean`, see `RHS/NOTES_smoothOpen_FK_of_pkg_FALSE.md`).

This file records the *repair*, proved: the conclusion holds as soon as the datum `g` carries
the honesty/regularity facts that every consumer of this chapter has anyway (`GalClass α g`,
i.e. `SmoothQuad g`, `HkMem α 6 g`, `L12 g 0 = 0`, `VanishTheta g`, the axis conditions and
decay) — which is exactly the form of the paper's own setting (`RHS/NOTES_discharge.md` §3 and
the `lip` clause of `Defs.RHSData`, whose hypotheses begin with `GalClass α g`).

Why the extra hypothesis is needed: the conclusion requires the two *moments* of the full
profile `F = F_* + g`,

  `z ↦ L₁₂(F_*+g)(z)  = L₁₂(F_*)(z) + L₁₂(g)(z)`  and  `z ↦ FK(F_*+g)(z) = FK(F_*)(z) + FK(g)(z)`,

to be `C^∞`.  The `F_*`-halves are explicit (`L12_Fstar_eq`, `FK_Fstar`), but the additivity and
the smoothness of `FK g` need the θ-slice integrability of `g` (`IntegrableOn (fun θ ↦ K θ·g z θ) Iθ`),
which in this tree is supplied *only* by the weighted-`L²` honesty `HkMem α 4 g`
(`GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem`, used by `L12AddFstar`) together with
`SmoothQuad g` and `L12 g 0 = 0` (used by `OpenPkg.deriv_L12_eq` in
`AuxFK.smoothOpen_FK_radial`).  None of the two packages constrains `g` itself, only the
residuals `Rop/Uop/Vop (PhiTil α g Φg)`, so none of these three facts is derivable.

Everything below is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.NonlinRows.smoothOpen_radA
import Submission.Work.FTS.GalFields.RHS.smoothOpen_FK_of_gal
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.OpenPkg.C4Factors
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.Stability.L12Add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Angular factors -/

/-- `θ ↦ sin(2θ)` is `C^∞` on the open quadrant. -/
theorem smoothOpen_sin_two :
    Work.FTS.EllipticEst.SmoothOpen (fun (_ : ℝ) (θ : ℝ) => Real.sin (2 * θ)) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0
  exact (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn

/-- `θ ↦ sin θ ^ 2` is `C^∞` on the open quadrant. -/
theorem smoothOpen_sin_sq :
    Work.FTS.EllipticEst.SmoothOpen (fun (_ : ℝ) (θ : ℝ) => Real.sin θ ^ 2) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) Work.FTS.EllipticEst.Q0
  exact (((Real.contDiff_sin.comp contDiff_snd).pow 2).contDiffOn)

/-! ## The two explicit `F_*`-moments -/

/-- `z ↦ L₁₂(F_*)(z) = 2α/(1+z)` is `C^∞` on the open quadrant. -/
theorem smoothOpen_L12_Fstar_rad (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Fstar α) z) := by
  have hr : ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi 0) := fun n =>
    contDiffOn_const.div (contDiffOn_const.add contDiffOn_id)
      (fun z hz => ne_of_gt (by
        have h : (0 : ℝ) < z := hz
        linarith))
  have hmain := Work.FTS.NonlinRows.smoothOpen_radial (r := fun z : ℝ => 2 * α / (1 + z)) hr
  refine hmain.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry]
  exact Work.Construction.L12_Fstar_eq hα hα1
    (le_of_lt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-- `z ↦ FK(F_*)(z) = α·2z/(1+z)²` is `C^∞` on the open quadrant. -/
theorem smoothOpen_FK_Fstar_rad (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z) := by
  have hr : ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => α * (2 * z / (1 + z) ^ 2)) (Set.Ioi 0) :=
    fun n =>
      contDiffOn_const.mul
        ((contDiffOn_const.mul contDiffOn_id).div
          ((contDiffOn_const.add contDiffOn_id).pow 2)
          (fun z hz => pow_ne_zero 2 (ne_of_gt (by
            have h : (0 : ℝ) < z := hz
            linarith))))
  have hmain := Work.FTS.NonlinRows.smoothOpen_radial
    (r := fun z : ℝ => α * (2 * z / (1 + z) ^ 2)) hr
  refine hmain.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry]
  exact Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1

/-! ## Additivity of the angular moment `FK` in the profile -/

/-- **The angular moment is additive** as soon as the two θ-slices are integrable on `Iθ`: this
is `L12dens_add_of_integrableOn` transported through the definitional identity
`FK f z = z · L12dens K f z`. -/
theorem FK_add_of_slices {a b : ℝ → ℝ → ℝ} {z : ℝ} (hz : z ≠ 0)
    (ha : IntegrableOn (fun θ => Work.Spaces.K θ * a z θ / z) Work.Spaces.Iθ)
    (hb : IntegrableOn (fun θ => Work.Spaces.K θ * b z θ / z) Work.Spaces.Iθ) :
    Work.Construction.FK (fun z θ => a z θ + b z θ) z
      = Work.Construction.FK a z + Work.Construction.FK b z := by
  have hd := Work.FTS.LocData.L12dens_add_of_integrableOn Work.Spaces.K ha hb
  have hkey : ∀ f : ℝ → ℝ → ℝ, Work.Construction.FK f z
      = z * Work.FM.L12dens Work.Spaces.K f z := by
    intro f
    simp only [Work.Construction.FK, Work.FM.L12dens, Work.Spaces.Iθ]
    rw [show (fun θ => Work.Spaces.K θ * f z θ / z)
        = fun θ => (1 / z) * (f z θ * Work.Spaces.K θ) from by funext θ; ring]
    rw [MeasureTheory.integral_const_mul]
    field_simp
  rw [hkey (fun z θ => a z θ + b z θ), hd, mul_add, ← hkey a, ← hkey b]

/-! ## The repaired statement -/

/-- **`N α (F_* + g) (Φ_s + Φ_g)` is `C^∞` on the open quadrant — the repaired form of
`smoothOpen_N_Ftot`.**

Drop-in replacement for `Work.FTS.GalFields.RHS.smoothOpen_N_Ftot` with the single extra
hypothesis `hgal : GalClass α g` (supplied by the `lip`/`bdd` clauses of `Defs.RHSData` and by
`Nonlin.GalClass` in every row of §8). -/
theorem smoothOpen_N_Ftot_gal {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {g Φs Φg : Fn} (hgal : Work.FTS.Nonlin.GalClass α g)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs)
    (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg) (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ)) := by
  have hsm : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 g := hgal.reg.2.1
  have hmem5 : Work.Spaces.HkMem α 5 g := Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem6
  have hmem4 : Work.Spaces.HkMem α 4 g := Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem5
  have hL12g : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hΦg hell.V.1.1
  have hFKg : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK g z) :=
    smoothOpen_FK_of_pkg_gal hα hα1 hgal hg hΦs hΦg hell hstar
  have hL12F := smoothOpen_L12_Fstar_rad α hα hα1
  have hFKF := smoothOpen_FK_Fstar_rad α hα hα1
  -- additivity of the two moments over `F = F_* + g`
  have hL : ∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α g) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z :=
    Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar hα hα1 hg hmem4
  have hFK : ∀ z : ℝ, 0 < z → Work.Construction.FK (Work.Construction.Ftot α g) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK g z := by
    intro z hz
    exact FK_add_of_slices (a := Work.Construction.Fstar α) (b := g) (ne_of_gt hz)
      (Work.Stability.integrableOn_slice_Fstar α hα z)
      (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hg hmem4 hz)
  -- the two `F`-moments are `C^∞` on the quadrant
  have hLtot : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Ftot α g) z) :=
    (Work.FTS.NonlinRows.smoothOpen_add hL12F hL12g).congr (by
      intro p hp
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry]
      exact hL z (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hFKtot : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Ftot α g) z) :=
    (Work.FTS.NonlinRows.smoothOpen_add hFKF hFKg).congr (by
      intro p hp
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry]
      exact hFK z (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  -- the residual and the three operators
  have hΦ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Φs z θ + Φg z θ) :=
    Work.FTS.NonlinRows.smoothOpen_add hΦs hΦg
  have hTheta : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / (4 * α)) * (Real.sin (2 * θ)
        * Work.Construction.L12 (Work.Construction.Ftot α g) z)) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (4 * α))
      (Work.FTS.NonlinRows.smoothOpen_mul smoothOpen_sin_two hLtot)
  have hPsi_eq : Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)
      = fun z θ => (Φs z θ + Φg z θ)
        - (1 / (4 * α)) * (Real.sin (2 * θ)
          * Work.Construction.L12 (Work.Construction.Ftot α g) z) := by
    funext z θ
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
    ring
  have hPsi : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) :=
    hPsi_eq ▸ (Work.FTS.NonlinRows.smoothOpen_sub hΦ hTheta)
  have hRop := Work.FTS.NonlinRows.smoothOpen_Rop (α := α) hPsi
  have hUop : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ))) :=
    Work.FTS.EllipticEst.smoothOpen_Uop hPsi
  have hVop := Work.FTS.NonlinRows.smoothOpen_Vop hPsi
  -- the profile and its two first-order operators
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Ftot α g) :=
    Work.FTS.NonlinRows.smoothOpen_add
      (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)) hg
  have hpthF := Work.FTS.EllipticEst.SmoothOpen.pth hF
  have hDzF := Work.FTS.EllipticEst.SmoothOpen.Dz hF
  -- the five summands of `N`
  have t1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (2 * Work.Construction.Rop α (Work.Construction.PhiTil α
          (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) z θ)
        * Work.Construction.Ftot α g z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_const_mul 2 hRop) hF
  have t2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (2 * Work.Construction.Uop α (Work.Construction.PhiTil α
          (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) z θ)
        * Work.Spaces.pth (Work.Construction.Ftot α g) z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_const_mul 2 hUop) hpthF
  have t3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => ((2 * α) * Work.Construction.Vop (Work.Construction.PhiTil α
          (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) z θ)
        * Work.Spaces.Dz (Work.Construction.Ftot α g) z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_const_mul (2 * α) hVop) hDzF
  have t4 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (((1 / 2) * Real.sin (2 * θ)) * Work.Construction.FK
          (Work.Construction.Ftot α g) z)
        * Work.Spaces.pth (Work.Construction.Ftot α g) z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_const_mul (1 / 2) smoothOpen_sin_two) hFKtot) hpthF
  have t5 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftot α g) z)
        * Work.Construction.Ftot α g z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_mul smoothOpen_sin_sq hFKtot) hF
  have hmain : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α
            (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Construction.Ftot α g z θ
        - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α
            (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Spaces.pth (Work.Construction.Ftot α g) z θ
        - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α
            (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Spaces.Dz (Work.Construction.Ftot α g) z θ
        - (1 / 2) * Real.sin (2 * θ) * Work.Construction.FK (Work.Construction.Ftot α g) z
          * Work.Spaces.pth (Work.Construction.Ftot α g) z θ
        - Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftot α g) z
          * Work.Construction.Ftot α g z θ) :=
    Work.FTS.NonlinRows.smoothOpen_sub
      (Work.FTS.NonlinRows.smoothOpen_sub
        (Work.FTS.NonlinRows.smoothOpen_sub
          (Work.FTS.NonlinRows.smoothOpen_sub t1 t2) t3) t4) t5
  change Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α
            (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Construction.Ftot α g z θ
        - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α
            (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Spaces.pth (Work.Construction.Ftot α g) z θ
        - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α
            (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) z θ
          * Work.Spaces.Dz (Work.Construction.Ftot α g) z θ
        - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK (Work.Construction.Ftot α g) z
          * Work.Spaces.pth (Work.Construction.Ftot α g) z θ
        - Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftot α g) z
          * Work.Construction.Ftot α g z θ)
  exact hmain

end Work.FTS.GalFields.RHS
