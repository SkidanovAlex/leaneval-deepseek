/-
# `E4R3/N4C/PairingT/Atoms` — the honest §8-assembly vocabulary

This module fixes the pieces of the *honest* (class-`C`) version of the §8 assembly of the level
four pairing estimate `N4C.pairingBoundT`:

* `AtomsO α g Φs Φg` — the twelve `SmoothOpen`-atoms out of which every one of the 27 pieces of
  the §8 split is built, together with `atomsO_of_ctx`, which produces them from the honest
  context (`ClassC α g`, `EllPkgGo α Ce g Φg`, `StarPkgo2 α Cs Φs`);
* `GoodO α F` — the honest class `HQo α 4 = SmoothOpen ∧ HkMem α 4` (the `N4ExtraH` interface
  consumes exactly this), with its closure under sums, negation, scalar multiples and transfer
  along equality on the open quadrant `Qd`;
* the linearity of `IP` on the honest class (`IPO_add2` … `IPO_add7`), the `HQo` analogues of
  `OpenPkg.IP_add4'` … `IP_add7'`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.NonlinRows.smoothOpen_radA
import Submission.Work.FTS.NonlinRows.Rl1.PvecMeasOpen
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal
import Submission.Work.FTS_RegExport.RXT.velPert
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)
open Work.FTS.EllipticEst (SmoothOpen)
open Work.FTS.VocabO (HQo)
open Work.FTS.Nonlin (PhiTg PhiTs)
open Work.Construction (Fstar FK L12 Rop Uop Vop PhiTil)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The atoms -/

/-- **The twelve smoothness atoms of the §8 pieces**: the profile `g`, the two angular moments
`L₁₂` and the two `FK`-moments, the fixed profile `F_*`, and the six transported coefficients
`ℛ`/`𝒰`/`𝒱` of the residuals `Φ̃_g` and `Φ̃_*`. -/
structure AtomsO (α : ℝ) (g Φs Φg : Fn) : Prop where
  sg : SmoothOpen g
  sFs : SmoothOpen (Fstar α)
  sLg : SmoothOpen (fun z _ => L12 g z)
  sLFs : SmoothOpen (fun z _ => L12 (Fstar α) z)
  sFKg : SmoothOpen (fun z _ => FK g z)
  sFKFs : SmoothOpen (fun z _ => FK (Fstar α) z)
  sRg : SmoothOpen (Rop α (PhiTg α g Φg))
  sUg : SmoothOpen (Uop α (PhiTg α g Φg))
  sVg : SmoothOpen (Vop (PhiTg α g Φg))
  sRs : SmoothOpen (Rop α (PhiTs α Φs))
  sUs : SmoothOpen (Uop α (PhiTs α Φs))
  sVs : SmoothOpen (Vop (PhiTs α Φs))

/-- `SmoothOpen (x ↦ f x)` from all-order smoothness of `f` on `(0,∞)` bundled with our
convention (`_`-named angular variable). -/
theorem atomsO_sFKg {α : ℝ} {g : Fn} (hfsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0)) :
    SmoothOpen (fun z _ => FK g z) := by
  have hfs : SmoothOpen (fun z _ : ℝ => Work.Elliptic.Fstar g z) :=
    Work.FTS.NonlinRows.smoothOpen_radial (r := Work.Elliptic.Fstar g) hfsm
  refine (SmoothOpen.congr (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul 3 hfs) ?_)
  intro z _ _ _ _
  exact (Work.FTS_RegExport.RXT.velPert_FK_eq g z).symm

/-- `sin(2θ)` as a smooth function of the quadrant. -/
theorem smoothOpen_s2 : SmoothOpen (fun _ (θ : ℝ) => Work.Construction.s2 θ) :=
  SmoothOpen.congr Work.FTS.GalFields.RHS.smoothOpen_sin_two
    (fun _ _ _ _ _ => rfl)

/-- `Uop` of a smooth residual is smooth: `Uop = sin(2θ)·(Uop/sin(2θ))` on the quadrant. -/
theorem smoothOpen_Uop_of_div {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (h : SmoothOpen (fun z θ => Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ)) :
    SmoothOpen (Work.Construction.Uop α Ψ) := by
  refine SmoothOpen.congr
    (Work.FTS.StrongPersist.H6Pair6Aux.so_mul smoothOpen_s2 h) ?_
  intro z θ hz hθ _
  have hs : Work.Construction.s2 θ ≠ 0 := by
    rw [Work.Construction.s2_eq]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  rw [mul_div_cancel₀ _ hs]

/-- **The atoms from the honest context.** -/
theorem atomsO_of_ctx {Cs Ce α : ℝ} {g Φs Φg : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : Work.FTS.ClassC.ClassC α g) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) : AtomsO α g Φs Φg where
  sg := hg.reg
  sFs := Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  sLg := Work.FTS.NonlinRows.smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  sLFs := Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_L12_Fstar α
  sFKg := atomsO_sFKg (α := α) hg.fsm
  sFKFs := Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα hα1
  sRg := hell.R.1.1
  sUg := smoothOpen_Uop_of_div hell.U.1.1
  sVg := hell.V.1.1
  sRs := Work.FTS.NonlinRows.smoothOpen_Rop
    (Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hstar.toStarPkgo)
  sUs := Work.FTS.NonlinRows.Rl1.smoothOpen_Uop_open
    (Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hstar.toStarPkgo)
  sVs := Work.FTS.NonlinRows.smoothOpen_Vop
    (Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hstar.toStarPkgo)

/-! ## `GoodO = HQo α 4`: closure properties -/

/-- The honest class of the §8 assembly: interior `C^∞` plus `ℋ⁴`-honesty.  This is exactly the
class of the `N4ExtraH` interface. -/
abbrev GoodO (α : ℝ) (F : Fn) : Prop := HQo α 4 F

theorem goodO_add {α : ℝ} {f g : Fn} (hf : GoodO α f) (hg : GoodO α g) :
    GoodO α (fun z θ => f z θ + g z θ) :=
  ⟨Work.FTS.StrongPersist.H6Pair6Aux.so_add hf.1 hg.1,
    Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf.1 4)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hg.1 4) hf.2 hg.2⟩

theorem goodO_const_mul {α : ℝ} (c : ℝ) {f : Fn} (hf : GoodO α f) :
    GoodO α (fun z θ => c * f z θ) :=
  ⟨Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul c hf.1,
    Work.FTS.LocData.HkMem_const_mul α 4 c hf.2⟩

/-- Transfer of goodness along equality on the open quadrant. -/
theorem goodO_of_eqOn_Qd {α : ℝ} {f g : Fn} (hf : GoodO α f)
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = g z θ) : GoodO α g :=
  ⟨SmoothOpen.congr hf.1 (fun z θ hz hθ hlt => h z θ ⟨hz, ⟨hθ, hlt⟩⟩),
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hf.2
      (fun z hz θ hθ => h z θ ⟨hz, hθ⟩)⟩

theorem goodO_neg {α : ℝ} {f : Fn} (hf : GoodO α f) : GoodO α (fun z θ => -f z θ) :=
  goodO_of_eqOn_Qd (goodO_const_mul (-1) hf) (fun z θ _ => by ring)

/-! ## Linearity of `IP` on the honest class -/

theorem IPO_add2 {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct α : ℝ} (hE : N4ExtraH IP α₂ Ct)
    (hα : α ∈ Set.Ioc 0 α₂) {g f₁ f₂ : Fn} (hg : HQo α 4 g)
    (h1 : HQo α 4 f₁) (h2 : HQo α 4 f₂) :
    IP α (f₁ + f₂) g = IP α f₁ g + IP α f₂ g :=
  hE.add α hα f₁ f₂ g h1 h2 hg

theorem IPO_add4 {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct α : ℝ} (hE : N4ExtraH IP α₂ Ct)
    (hα : α ∈ Set.Ioc 0 α₂) {g f₁ f₂ f₃ f₄ : Fn} (hg : HQo α 4 g)
    (h1 : HQo α 4 f₁) (h2 : HQo α 4 f₂) (h3 : HQo α 4 f₃) (h4 : HQo α 4 f₄)
    (h12 : HQo α 4 (f₁ + f₂)) (h123 : HQo α 4 (f₁ + f₂ + f₃)) :
    IP α (f₁ + f₂ + f₃ + f₄) g = IP α f₁ g + IP α f₂ g + IP α f₃ g + IP α f₄ g := by
  rw [hE.add α hα (f₁ + f₂ + f₃) f₄ g h123 h4 hg,
    hE.add α hα (f₁ + f₂) f₃ g h12 h3 hg,
    hE.add α hα f₁ f₂ g h1 h2 hg]

theorem IPO_add5 {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct α : ℝ} (hE : N4ExtraH IP α₂ Ct)
    (hα : α ∈ Set.Ioc 0 α₂) {g f₁ f₂ f₃ f₄ f₅ : Fn} (hg : HQo α 4 g)
    (h1 : HQo α 4 f₁) (h2 : HQo α 4 f₂) (h3 : HQo α 4 f₃) (h4 : HQo α 4 f₄)
    (h5 : HQo α 4 f₅)
    (h12 : HQo α 4 (f₁ + f₂)) (h123 : HQo α 4 (f₁ + f₂ + f₃))
    (h1234 : HQo α 4 (f₁ + f₂ + f₃ + f₄)) :
    IP α (f₁ + f₂ + f₃ + f₄ + f₅) g
      = IP α f₁ g + IP α f₂ g + IP α f₃ g + IP α f₄ g + IP α f₅ g := by
  rw [hE.add α hα (f₁ + f₂ + f₃ + f₄) f₅ g h1234 h5 hg]
  exact congrArg (· + IP α f₅ g) (IPO_add4 hE hα hg h1 h2 h3 h4 h12 h123)

theorem IPO_add7 {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct α : ℝ} (hE : N4ExtraH IP α₂ Ct)
    (hα : α ∈ Set.Ioc 0 α₂) {g f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Fn} (hg : HQo α 4 g)
    (h1 : HQo α 4 f₁) (h2 : HQo α 4 f₂) (h3 : HQo α 4 f₃) (h4 : HQo α 4 f₄)
    (h5 : HQo α 4 f₅) (h6 : HQo α 4 f₆) (h7 : HQo α 4 f₇)
    (h12 : HQo α 4 (f₁ + f₂)) (h123 : HQo α 4 (f₁ + f₂ + f₃))
    (h1234 : HQo α 4 (f₁ + f₂ + f₃ + f₄))
    (h12345 : HQo α 4 (f₁ + f₂ + f₃ + f₄ + f₅))
    (h123456 : HQo α 4 (f₁ + f₂ + f₃ + f₄ + f₅ + f₆)) :
    IP α (f₁ + f₂ + f₃ + f₄ + f₅ + f₆ + f₇) g
      = IP α f₁ g + IP α f₂ g + IP α f₃ g + IP α f₄ g + IP α f₅ g + IP α f₆ g + IP α f₇ g := by
  rw [hE.add α hα (f₁ + f₂ + f₃ + f₄ + f₅ + f₆) f₇ g h123456 h7 hg]
  have h56 : IP α (f₁ + f₂ + f₃ + f₄ + f₅ + f₆) g
      = IP α f₁ g + IP α f₂ g + IP α f₃ g + IP α f₄ g + IP α f₅ g + IP α f₆ g := by
    rw [hE.add α hα (f₁ + f₂ + f₃ + f₄ + f₅) f₆ g h12345 h6 hg]
    exact congrArg (· + IP α f₆ g) (IPO_add5 hE hα hg h1 h2 h3 h4 h5 h12 h123 h1234)
  rw [h56]

end Work.FTS.StrongEps.E4R3.N4C
