import Submission.Work.Wire123.TransLink
import Submission.Work.CrauderKatz.cInv_conj_eq
import Submission.Work.LLink.Count
import Submission.Work.Motivic.not_gen_of_cInv_ne_zero
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Wire123.TransLinkWiring` — the transport-free wiring of Theorem 1.2 (3)

The `n = 5` case, from the residual `Work.Wire123.TransLink 𝕜` (the L-link, its (L2) strong
birationality, and *one* birational map `𝔸⁵ ⇢ P`), by the conjugation argument:

* the link `ψ : P ⇢ P'` and the strong birationality `γ : P ⇢ P'` give the self-map
  `φ := ψ.trans γ.symm` of `P` with `cInv 𝕜 z₀ φ = cInv 𝕜 z₀ ψ - cInv 𝕜 z₀ γ = 1 - 0 = 1`
  (the first from the two singleton `exDiv`s of the link and the residue-field data, the second
  from (L2));
* conjugating `φ` along `iota : 𝔸⁵ ⇢ P` gives an element of `Cr 𝕜 5` with the *same* coefficient
  (`Work.CrauderKatz.cInv_conj_eq`), whence `Work.Motivic.not_gen_of_cInv_ne_zero`.

Consequently `Work.Wire123.LeanLink` is *not* needed: its transport fields (`eps`, `delta`) and the
two vanishing conditions `cInv 𝕜 z₀ eps = 0`, `cInv 𝕜 z₀ delta = 0` are redundant, and
`Work.Wire123.LeanLink.toTransLink` records that every `LeanLink` is a `TransLink`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Wire123

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **The `n = 5` case of Theorem 1.2 (3), from the transport-free residual `TransLink`.** -/
theorem not_gen_of_transLink_five (𝕜 : Type) [Field 𝕜] (D : TransLink 𝕜) :
    ¬ GenByPseudoRegularizable 𝕜 5 := by
  classical
  obtain ⟨γ, hγover, hγ0⟩ := D.stronglyBirational
  haveI hγ : γ.IsOver (Spec (.of 𝕜)) := hγover
  haveI hγs : (γ.symm).IsOver (Spec (.of 𝕜)) :=
    inferInstanceAs (γ.inv.IsOver (Spec (.of 𝕜)))
  -- the self-map of `P` obtained from the link and the strong birationality
  let φ : D.P.BirationalMap D.P := D.psi.trans γ.symm
  haveI hφ : φ.IsOver (Spec (.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans (S := Spec (.of 𝕜)) D.psi γ.symm
  -- the link contributes `1` at the base point
  have hψval : cInv 𝕜 D.z₀ D.psi = 1 :=
    Work.LLink.cInv_eq_one_of_exDiv_eq_singletons (𝕜 := 𝕜) (X := D.P) (Y := D.P')
      D.z₀ D.psi D.exDiv_psi D.exDiv_psi_symm D.not_resEquiv_x_z₀ D.resEquiv_y
  -- (L2) contributes nothing
  have hγsval : cInv 𝕜 D.z₀ γ.symm = 0 := by
    rw [Work.LLink.cInv_eq_neg_symm (𝕜 := 𝕜) (X := D.P) (Y := D.P') D.z₀ γ,
      hγ0 D.ZW D.z₀]
    first | refl_ring1 | ring
  have hφval : cInv 𝕜 D.z₀ φ = 1 := by
    show cInv 𝕜 D.z₀ (D.psi.trans γ.symm) = 1
    rw [Work.Motivic.cInv_add (𝕜 := 𝕜) (X := D.P) (Y := D.P') (Z := D.P) D.z₀ D.psi γ.symm,
      hψval, hγsval]
    norm_num
  -- the transport to `𝔸⁵`: conjugation preserves the coefficient exactly
  haveI hι : D.iota.IsOver (Spec (.of 𝕜)) := D.isOverIota
  haveI hιs : (D.iota.symm).IsOver (Spec (.of 𝕜)) :=
    inferInstanceAs (D.iota.inv.IsOver (Spec (.of 𝕜)))
  let Ψ : (Work.CY3.Affine 𝕜 5).BirationalMap (Work.CY3.Affine 𝕜 5) :=
    D.iota.trans (φ.trans D.iota.symm)
  haveI hφι : (φ.trans D.iota.symm).IsOver (Spec (.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans (S := Spec (.of 𝕜)) φ D.iota.symm
  haveI hΨ : Ψ.IsOver (Spec (.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans (S := Spec (.of 𝕜)) D.iota (φ.trans D.iota.symm)
  have hΨval : cInv 𝕜 D.z₀ Ψ = 1 := by
    have h := Work.CrauderKatz.cInv_conj_eq (𝕜 := 𝕜) (S := Work.CY3.Affine 𝕜 5)
      (T := D.P) D.z₀ D.iota φ
    rw [hφval] at h
    exact h
  refine Work.Motivic.not_gen_of_cInv_ne_zero 𝕜 5
    ⟨D.ZW, D.overZW, D.z₀, ⟨Ψ, hΨ⟩, ?_⟩
  rw [hΨval]
  norm_num

/-- **The challenge shape of the `n = 5` statement** (with the `Infinite 𝕜` binder of
`Submission.MotivicInvariants.theorem_1_2_3`, which is not needed for `n = 5`). -/
theorem theorem_1_2_3_of_transLink_five (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] (D : TransLink 𝕜) :
    ¬ GenByPseudoRegularizable 𝕜 5 :=
  not_gen_of_transLink_five 𝕜 D

/-- **A `LeanLink` is a `TransLink`**: the transport fields (`eps`, `delta`) and the two vanishing
conditions of `Work.Wire123.LeanLink` are redundant, so the residual `TransLink` is *weaker*. -/
def LeanLink.toTransLink {𝕜 : Type} [Field 𝕜] (L : LeanLink 𝕜) : TransLink 𝕜 where
  P := L.P
  varietyP := L.varietyP
  P' := L.P'
  varietyP' := L.varietyP'
  psi := L.psi
  isOverPsi := L.isOverPsi
  x := L.x
  y := L.y
  exDiv_psi := L.exDiv_psi
  exDiv_psi_symm := L.exDiv_psi_symm
  Z := L.Z
  varietyZ := L.varietyZ
  Z' := L.Z'
  varietyZ' := L.varietyZ'
  isKTrivial_Z := L.isKTrivial_Z
  isKTrivial_Z' := L.isKTrivial_Z'
  picardOne_Z := L.picardOne_Z
  picardOne_Z' := L.picardOne_Z'
  ZW := L.ZW
  overZW := L.overZW
  z₀ := L.z₀
  resEquiv_y := L.resEquiv_y
  p1Bundle_y := L.p1Bundle_y
  p1Bundle_x := L.p1Bundle_x
  stronglyBirational := L.stronglyBirational
  iota := L.eps
  isOverIota := L.isOverEps
  bridge := L.bridge
  not_stablyBirat := L.not_stablyBirat

/-- **The `n = 5` case from `LeanLink`**, now a one-liner: the transport hypotheses of
`LeanLink` are not used (they were used by the `gInv`-transport route of
`Work.Wire123.exists_cInv_ne_zero_of_leanLink`). -/
theorem not_gen_of_leanLink_five (𝕜 : Type) [Field 𝕜] (L : LeanLink 𝕜) :
    ¬ GenByPseudoRegularizable 𝕜 5 :=
  not_gen_of_transLink_five 𝕜 L.toTransLink

end

end Work.Wire123
