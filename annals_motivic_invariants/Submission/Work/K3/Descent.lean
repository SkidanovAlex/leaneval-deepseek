import Mathlib
import Submission.Work.K3.Defs
import Submission.Work.K3.K3Link
import Submission.Work.K3.HL
import Submission.Work.K3.BaseChange
import Submission.Work.K3.baseChange_map_isOver
import Submission.Work.K3.baseChange_map_isIso
import Submission.Work.K3.baseChange_isoOver
import Submission.Work.K3.baseChange_comp

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3.Descent` — the descent step of Theorem `thm:K3`

Lin–Shinder's Theorem `thm:K3` is stated for an arbitrary subfield `𝕜 ⊆ ℂ`, but the construction
of the L-link is carried out over `ℚ`: a `ℚ`-rational smooth `3`-dimensional linear section `V` of
the Mukai Grassmannian `OG₊(5,10)`, an HL-admissible pair `(ℙ⁶, Σ)` defined over `ℚ`
(`lem:HL-admis-pencil`), and members of the resulting Lefschetz pencil with geometric Picard rank
one (Terasoma, `pro-K3HLPic1`).  The last sentence of `thm-HL` upgrades the construction to a
statement over `ℚ`:

> Finally, if `S ↪ ℙ⁷` and `Σ ⊂ S` are defined over a subfield `k ⊂ ℂ`, then both `ψ` and the pair
> `(S', Σ')` are defined over `k`.

This module formalises the **field arithmetic** of that sentence: what is *proved* here is that
`ℚ`-definedness, together with the geometry of the link over `𝕜`, gives the `𝕜`-level statement
that the theorem needs — in particular the fact that the two centres of the `𝕜`-link are
non-isomorphic (which the paper uses in the form "Since `S_𝕜` and `S'_𝕜` are non-isomorphic K3
surfaces because `S_ℂ ≄ S'_ℂ`"), and hence, with Totaro's input, the non-vanishing of the
invariant coefficient over `𝕜`.

## What is proved

* `ratCast_mem` — every subfield of `ℂ` contains `ℚ`; this is why the `ℚ`-model of the
  construction is available over `𝕜`, so that "defined over `ℚ`" implies "defined over `𝕜`";
* `not_isoOver_baseChange` — **monotonicity of the field of definition**: base change preserves
  isomorphisms (`baseChange_isoOver`) and is transitive (`baseChange_comp`), hence if the `ℂ`-base
  changes of two `ℚ`-schemes are non-isomorphic, so are their `𝕜`-base changes.  This is the
  formal content of the paper's passage from `S_ℂ ≄ S'_ℂ` to `S_𝕜 ≄ S'_𝕜`;
* `HLDescent.notIso` — the two centres of the `𝕜`-model of the link are non-isomorphic over `𝕜`;
* `HLDescent.exists_cInv_ne_zero` — the invariant coefficient of the transported `𝕜`-link does
  not vanish, i.e. the `n = 4` conclusion of Theorem 1.2 (2) over `𝕜`.

## `HLDescent` is a construction

`HLDescent` is an *interface*, not an input: it is produced from the `ℚ`-model by base change in
`Submission/Work/K3/Uniform.lean` (`Work.K3.HassettLaiTheorem.toHLDescent`), which also proves
that the two exceptional divisors of `ψ_𝕜` are the base-changed divisors.  This module contains
the two field-arithmetic ingredients of that passage — `definedOver_mono` (base change is
transitive, so "defined over `ℚ`" implies "defined over `𝕜`") and `not_isoOver_baseChange` (so the
`ℂ`-non-isomorphism of the two centres implies their `𝕜`-non-isomorphism) — and the resulting
non-vanishing of the invariant coefficient over `𝕜`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral
attribute [instance] Work.K3.TerasomaInput.varietyS Work.K3.TerasomaInput.overSigma
  Work.K3.TerasomaInput.isOverSigma Work.K3.HassettLaiTheorem.overSigma'
  Work.K3.HassettLaiTheorem.isOverSigma' Work.K3.K3Data.varietyS
  Work.K3.K3Data.varietyS' Work.K3.K3Data.varietyP

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

/-! ## 1. Every subfield of `ℂ` contains `ℚ` -/

/-- **Every subfield of `ℂ` contains `ℚ`** (`ℚ` is the prime field of characteristic zero).  This
is the reason why the `ℚ`-model produced by `thm-HL` is automatically a `𝕜`-model for every
subfield `𝕜 ⊆ ℂ`: the extension `ℚ → 𝕜` always exists. -/
theorem ratCast_mem (𝕜 : Subfield ℂ) (q : ℚ) : (q : ℂ) ∈ 𝕜 :=
  SubfieldClass.ratCast_mem 𝕜 q

/-! ## 2. Monotonicity of the field of definition -/

/-- **Monotonicity of the field of definition.**  Let `K ⊆ L ⊆ M` be a tower of fields and let
`X`, `Y` be `K`-schemes.  If the `M`-base changes of `X` and `Y` are *not* `M`-isomorphic, then
their `L`-base changes are not `L`-isomorphic.

Contrapositively: an isomorphism over `L` base changes to an isomorphism over `M`
(`baseChange_isoOver`), so non-isomorphism over the larger field descends to the smaller one.
This is the formal content of the paper's step "Since `S_𝕜` and `S'_𝕜` are non-isomorphic K3
surfaces because `S_ℂ ≄ S'_ℂ`": the geometric non-isomorphism over `ℂ` forces non-isomorphism
over every intermediate field, in particular over `𝕜`. -/
theorem not_isoOver_baseChange (K L M : Type) [Field K] [Field L] [Field M] [Algebra K L]
    [Algebra L M] [Algebra K M] [IsScalarTower K L M] {X Y : Scheme.{0}}
    [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    (h : ¬ IsoOver M (baseChange K M X) (baseChange K M Y)) :
    ¬ IsoOver L (baseChange K L X) (baseChange K L Y) := by
  intro h'
  apply h
  have hM : IsoOver M (baseChange L M (baseChange K L X)) (baseChange L M (baseChange K L Y)) :=
    baseChange_isoOver L M h'
  obtain ⟨eX, heX⟩ := baseChange_comp K L M X
  obtain ⟨eY, heY⟩ := baseChange_comp K L M Y
  exact IsoOver.congr eX eY hM

/-- **Monotonicity of the field of definition** (positive form).  A scheme over `M` which is the
base change of a `K`-scheme is the base change of an `L`-scheme, for every intermediate field
`K ⊆ L ⊆ M`: "defined over `K` implies defined over `L`".  This is the formal content of the
paper's passage from the `ℚ`-model of the link to its `𝕜`-model (`ℚ ⊆ 𝕜` for every subfield
`𝕜 ⊆ ℂ`, see `ratCast_mem`), and it uses the transitivity of base change
(`baseChange_comp`). -/
theorem definedOver_mono (K L M : Type) [Field K] [Field L] [Field M] [Algebra K L]
    [Algebra L M] [Algebra K M] [IsScalarTower K L M] (X : Scheme.{0}) [X.Over (Spec (.of M))] :
    (∃ (Y : Scheme.{0}) (_ : Y.Over (Spec (.of K))), Nonempty (X ≅ baseChange K M Y)) →
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of L))), Nonempty (X ≅ baseChange L M Z) := by
  rintro ⟨Y, hY, ⟨e⟩⟩
  obtain ⟨e', -⟩ := baseChange_comp K L M Y
  exact ⟨baseChange K L Y, inferInstance, ⟨e ≪≫ e'.symm⟩⟩


/-! ## 3. The descent step -/

variable {T : TerasomaInput} {h : HassettLaiTheorem T} {𝕜 : Subfield ℂ}

/-- **The descent step of `thm:K3`.**  The two centres of the `𝕜`-model of the link produced by
`HLDescent` are non-isomorphic over `𝕜`.

Proof: their `ℂ`-base changes are the `ℂ`-model's centres (`ℚ ⊆ 𝕜 ⊆ ℂ`, transitivity of base
change), which are non-isomorphic by `thm-HL` ("`S_ℂ ≄ S'_ℂ`", Hassett–Lai Thm 3.1 with Oguiso
Prop 1.10); by monotonicity of the field of definition (`not_isoOver_baseChange`) the `𝕜`-base
changes of the `ℚ`-model's centres are non-isomorphic over `𝕜`; and these are the `𝕜`-centres up
to `𝕜`-isomorphism (`HLDescent.centre`, `HLDescent.centrePartner`). -/
theorem HLDescent.notIso (D : HLDescent T h 𝕜) : ¬ IsoOver 𝕜 D.data.S D.data.S' := by
  intro hbad
  have h_a : IsoOver 𝕜 (baseChange ℚ 𝕜 h.data.S) D.data.S' :=
    IsoOver.trans (X := baseChange ℚ 𝕜 h.data.S) (Y := D.data.S) (Z := D.data.S')
      D.centre hbad
  have h₁ : IsoOver 𝕜 (baseChange ℚ 𝕜 h.data.S) (baseChange ℚ 𝕜 h.data.S') :=
    IsoOver.trans (X := baseChange ℚ 𝕜 h.data.S) (Y := D.data.S')
      (Z := baseChange ℚ 𝕜 h.data.S') h_a
      (IsoOver.symm (X := baseChange ℚ 𝕜 h.data.S') (Y := D.data.S') D.centrePartner)
  exact (not_isoOver_baseChange ℚ 𝕜 ℂ h.notIsoGeom) h₁

/-- **The K3 L-link over `𝕜`.**  From the `𝕜`-model of the `ℚ`-link (the descent input), Totaro's
input and the geometric data, the non-triviality input `¬ ResEquiv 𝕜 y x` of the link is
derived. -/
noncomputable def HLDescent.toK3Link (D : HLDescent T h 𝕜)
    (Tt : TotaroInputAt 𝕜 D.data.S D.data.S') : K3Link 𝕜 :=
  D.data.toK3Link Tt D.notIso

/-- **Main theorem of this file**: the invariant coefficient of the transported `𝕜`-link does not
vanish.  This is the `n = 4` shape consumed by `Work.Motivic.not_gen_of_cInv_ne_zero` for
Theorem 1.2 (2) of the challenge. -/
theorem HLDescent.exists_cInv_ne_zero (D : HLDescent T h 𝕜)
    (Tt : TotaroInputAt 𝕜 D.data.S D.data.S') :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 4),
      cInv 𝕜 z₀ (φ : (Affine4 𝕜).BirationalMap (Affine4 𝕜)) ≠ 0 :=
  D.data.exists_cInv_ne_zero Tt D.notIso

end Work.K3
