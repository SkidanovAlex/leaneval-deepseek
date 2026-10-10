import Submission.Work.Wire123.TransLink
import Submission.Work.CrauderKatz.cInv_conj_eq
import Submission.Work.LLink.Count
import Submission.Work.Motivic.not_gen_of_cInv_ne_zero

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Wire123.MinLink` — the *sharpest* form of the `n = 5` residual

`Work.Wire123.TransLink` still carries the whole paper-shaped list of fields (`Z`, `Z'`, the two
`ℙ¹`-bundles, the bridge, Totaro's conclusion, the (L2) strong birationality).  The counting chain
consumes *only* the following, and this module records it:

* a fivefold `P` with an L-link `ψ : P ⇢ P'` whose exceptional divisors in the two directions are
  single points `x`, `y` of **different** birational classes (`ResEquiv 𝕜 y z₀` but
  `¬ ResEquiv 𝕜 x z₀` at the base point `z₀`), so that `cInv 𝕜 z₀ ψ = 1`
  (`Work.LLink.cInv_eq_one_of_exDiv_eq_singletons`);
* *one* birational map `γ : P ⇢ P'` over `𝕜` with `cInv 𝕜 z₀ γ ≠ 1` — this is what turns `ψ` into
  a self-map `ψ.trans γ.symm` of `P` with nonzero coefficient (in the paper `γ` is the strong
  birationality of `Work.CY3.G2Grassmannian`, with all coefficients zero);
* *one* birational map `𝔸⁵ ⇢ P` over `𝕜` (in the paper the big Bruhat cell of `G/P`).

Everything else — `Z`, `Z'`, `IsKTrivial`, `PicardRankOne`, `ZW`, the `ℙ¹`-bundle identifications,
the bridge, Totaro's conclusion, and the (L2) *vanishing* of the strong birationality — is either
fieldless or is precisely the paper's mechanism *for proving* the two `ResEquiv` clauses of the
first item.  So `MinLink` is stated directly in terms of those: it is the weakest residual in the
vocabulary of this area, and `Work.Wire123.TransLink.toMinLink` shows nothing is lost.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Wire123

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **The sharpest residual for the `n = 5` case**: a link with two *distinguished* exceptional
divisors, a map `γ : P ⇢ P'` not equal to `ψ` at the base point, and a birational map `𝔸⁵ ⇢ P`. -/
structure MinLink (𝕜 : Type) [Field 𝕜] where
  /-- the source fivefold of the link. -/
  P : Scheme.{0}
  [varietyP : Variety 𝕜 P]
  /-- the target fivefold of the link. -/
  P' : Scheme.{0}
  [varietyP' : Variety 𝕜 P']
  /-- the L-link. -/
  psi : P.BirationalMap P'
  [isOverPsi : psi.IsOver (Spec (.of 𝕜))]
  /-- the exceptional divisor of `ψ`. -/
  x : P
  /-- the exceptional divisor of `ψ⁻¹`. -/
  y : P'
  /-- `ψ` has no other exceptional divisor. -/
  exDiv_psi : exDiv psi = {x}
  /-- `ψ⁻¹` has no other exceptional divisor. -/
  exDiv_psi_symm : exDiv psi.symm = {y}
  /-- a base point, of the class of `y` and *not* of the class of `x`. -/
  ZW : Scheme.{0}
  [overZW : ZW.Over (Spec (.of 𝕜))]
  /-- the base point. -/
  z₀ : ZW
  /-- `κ(y) ≅ κ(z₀)`. -/
  resEquiv_y : ResEquiv 𝕜 y z₀
  /-- `κ(x) ≇ κ(z₀)`. -/
  not_resEquiv_x : ¬ ResEquiv 𝕜 x z₀
  /-- a birational map `P ⇢ P'` over `𝕜` which does *not* have the coefficient of `ψ` at `z₀`. -/
  gamma : P.BirationalMap P'
  [isOverGamma : gamma.IsOver (Spec (.of 𝕜))]
  /-- the non-degeneracy: `γ` differs from `ψ` in the `[κ(z₀)]`-coefficient. -/
  cInv_gamma_ne : cInv 𝕜 z₀ gamma ≠ 1
  /-- a birational map `𝔸⁵ ⇢ P` over `𝕜`. -/
  iota : (Work.CY3.Affine 𝕜 5).BirationalMap P
  [isOverIota : iota.IsOver (Spec (.of 𝕜))]

attribute [instance] MinLink.varietyP MinLink.varietyP' MinLink.isOverPsi MinLink.overZW
  MinLink.isOverGamma MinLink.isOverIota

namespace MinLink

variable {𝕜 : Type} [Field 𝕜]

/-- **The `n = 5` case of Theorem 1.2 (3), from the sharpest residual.** -/
theorem not_gen_five (D : MinLink 𝕜) : ¬ GenByPseudoRegularizable 𝕜 5 := by
  classical
  haveI hψ : D.psi.IsOver (Spec (.of 𝕜)) := D.isOverPsi
  haveI hγ : D.gamma.IsOver (Spec (.of 𝕜)) := D.isOverGamma
  haveI hγs : (D.gamma.symm).IsOver (Spec (.of 𝕜)) :=
    inferInstanceAs (D.gamma.inv.IsOver (Spec (.of 𝕜)))
  -- the self-map of `P` with nonzero coefficient at `z₀`
  let φ : D.P.BirationalMap D.P := D.psi.trans D.gamma.symm
  haveI hφ : φ.IsOver (Spec (.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans (S := Spec (.of 𝕜)) D.psi D.gamma.symm
  have hψval : cInv 𝕜 D.z₀ D.psi = 1 :=
    Work.LLink.cInv_eq_one_of_exDiv_eq_singletons (𝕜 := 𝕜) (X := D.P) (Y := D.P')
      D.z₀ D.psi D.exDiv_psi D.exDiv_psi_symm D.not_resEquiv_x D.resEquiv_y
  have hφval : cInv 𝕜 D.z₀ φ ≠ 0 := by
    show cInv 𝕜 D.z₀ (D.psi.trans D.gamma.symm) ≠ 0
    rw [Work.Motivic.cInv_add (𝕜 := 𝕜) (X := D.P) (Y := D.P') (Z := D.P) D.z₀ D.psi D.gamma.symm,
      Work.LLink.cInv_eq_neg_symm (𝕜 := 𝕜) (X := D.P) (Y := D.P') D.z₀ D.gamma, hψval]
    intro h
    exact D.cInv_gamma_ne (by linarith)
  -- the transport to `𝔸⁵` (conjugation preserves the coefficient)
  haveI hι : D.iota.IsOver (Spec (.of 𝕜)) := D.isOverIota
  haveI hιs : (D.iota.symm).IsOver (Spec (.of 𝕜)) :=
    inferInstanceAs (D.iota.inv.IsOver (Spec (.of 𝕜)))
  let Ψ : (Work.CY3.Affine 𝕜 5).BirationalMap (Work.CY3.Affine 𝕜 5) :=
    D.iota.trans (φ.trans D.iota.symm)
  haveI hφι : (φ.trans D.iota.symm).IsOver (Spec (.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans (S := Spec (.of 𝕜)) φ D.iota.symm
  haveI hΨ : Ψ.IsOver (Spec (.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans (S := Spec (.of 𝕜)) D.iota (φ.trans D.iota.symm)
  have hΨval : cInv 𝕜 D.z₀ Ψ ≠ 0 := by
    have h : cInv 𝕜 D.z₀ (D.iota.trans (φ.trans D.iota.symm)) = cInv 𝕜 D.z₀ φ :=
      Work.CrauderKatz.cInv_conj_eq (𝕜 := 𝕜) (S := Work.CY3.Affine 𝕜 5)
        (T := D.P) D.z₀ D.iota φ
    rw [show Ψ = D.iota.trans (φ.trans D.iota.symm) from rfl, h]
    exact hφval
  exact Work.Motivic.not_gen_of_cInv_ne_zero 𝕜 5
    ⟨D.ZW, D.overZW, D.z₀, ⟨Ψ, hΨ⟩, hΨval⟩

/-- The challenge shape of the previous result. -/
theorem theorem_1_2_3 (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] (D : MinLink 𝕜) :
    ¬ GenByPseudoRegularizable 𝕜 5 := MinLink.not_gen_five D

end MinLink

/-- **A `TransLink` gives a `MinLink`**: the fieldless data, the two centres, the `ℙ¹`-bundles, the
bridge and Totaro's conclusion are only the paper's way of producing the two `ResEquiv` clauses of
`MinLink`, and `StronglyBirational 𝕜 P P'` implies `cInv 𝕜 z₀ γ ≠ 1` in the sharpest possible
way (`cInv 𝕜 z₀ γ = 0`). -/
def TransLink.toMinLink {𝕜 : Type} [Field 𝕜] (D : TransLink 𝕜) : MinLink 𝕜 where
  P := D.P
  varietyP := D.varietyP
  P' := D.P'
  varietyP' := D.varietyP'
  psi := D.psi
  isOverPsi := D.isOverPsi
  x := D.x
  y := D.y
  exDiv_psi := D.exDiv_psi
  exDiv_psi_symm := D.exDiv_psi_symm
  ZW := D.ZW
  overZW := D.overZW
  z₀ := D.z₀
  resEquiv_y := D.resEquiv_y
  not_resEquiv_x := D.not_resEquiv_x_z₀
  gamma := D.stronglyBirational.choose
  isOverGamma := D.stronglyBirational.choose_spec.1
  cInv_gamma_ne := by
    rw [D.stronglyBirational.choose_spec.2 D.ZW D.z₀]
    norm_num
  iota := D.iota
  isOverIota := D.isOverIota

end

end Work.Wire123
