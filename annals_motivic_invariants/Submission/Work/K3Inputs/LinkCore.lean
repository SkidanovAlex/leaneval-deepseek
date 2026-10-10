import Submission.Work.K3Inputs.Defs
import Submission.Work.K3Inputs.StablyBiratK3

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3Inputs.LinkCore` — the K3 link data with the `ℙ¹`-bundle bridge *proved*

The geometric data of the K3 L-link is the structure `Work.K3.K3Data 𝕜`, whose field

```lean
bridge : ResEquiv 𝕜 D.y D.x → Work.K3.StablyBirational 𝕜 D.S D.S'
```

is the paper's ℙ¹-bundle bridge (Lemma `lemma:L-link` (2)): the two exceptional divisors of `ψ`
are birational to `S' × ℙ¹` and `S × ℙ¹`, so an isomorphism of their function fields makes the
two K3 surfaces stably birational.

That field is *not* an irreducible assumption: it follows from two named geometric clauses

* **(F1)** the point `y` (resp. `x`) has function field `κ(S)(t)` (resp. `κ(S')(t)`) —
  `Work.K3Inputs.IsP1BundleOver 𝕜 y D.S`, `… 𝕜 x D.S'` — the description of the two exceptional
  divisors as `ℙ¹`-bundles over the centres (`thm-HL` (1)),
* **(F2)** *cylinder rigidity* (`lem-stbirCY` at `W = ℙ¹`) — a `𝕜`-isomorphism
  `κ(S)(t) ≅ κ(S')(t)` descends to a birational map `S × ℙ¹ ⤏ S' × ℙ¹`; for K3 surfaces this is
  the statement that `S × ℙ¹` has a unique fibration over `ℙ¹`,

and this file *proves* the bridge from them (`Work.K3Inputs.bridge_of_clauses` in `Defs.lean`):
the clause (F1) composes with `ResEquiv 𝕜 y x` to give `κ(S)(t) ≅ κ(S')(t)`, and (F2) turns that
into stable birationality.

`LinkCore 𝕜` is therefore the link data *without* the opaque bridge field: a caller who has the
geometric clauses (F1), (F2) instead of the bridge gets the same downstream results
(`LinkCore.toK3Data`, `LinkCore.toK3Link`, `LinkCore.exists_cInv_ne_zero`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral
attribute [instance] Work.K3.K3Data.varietyS Work.K3.K3Data.varietyS' Work.K3.K3Data.varietyP

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **The K3 L-link data, with the ℙ¹-bundle bridge proved from (F1) and (F2).**

All fields are those of `Work.K3.K3Data 𝕜` except the pair `bridge` (which is replaced by the
two clauses `y_cylinder`, `x_cylinder` of (F1) and the rigidity clause `cylinderRigid` of (F2)),
so that `LinkCore.toK3Data` below *derives* the bridge.  See the module documentation. -/
structure LinkCore (𝕜 : Type) [Field 𝕜] where
  /-- The first K3 surface `S` (the centre `S₀ ⊂ ℙ⁴`, minimal model `S`). -/
  S : Scheme.{0}
  [varietyS : Variety 𝕜 S]
  /-- `S` is a K3 surface of degree `12` (named predicate). -/
  isK3 : Work.K3.IsK3Degree12 𝕜 S
  /-- `S` is `K`-trivial (named predicate). -/
  kTrivial : Work.K3.IsKTrivial 𝕜 S
  /-- `S` has geometric Picard rank one (named predicate). -/
  picardOne : Work.K3.PicardRankOneGeom 𝕜 S
  /-- The Fourier–Mukai partner `S'` (the minimal model of the other centre `S'_0`). -/
  S' : Scheme.{0}
  [varietyS' : Variety 𝕜 S']
  /-- `S'` is a K3 surface of degree `12` (named predicate). -/
  isK3' : Work.K3.IsK3Degree12 𝕜 S'
  /-- `S'` is `K`-trivial (named predicate). -/
  kTrivial' : Work.K3.IsKTrivial 𝕜 S'
  /-- `S'` has geometric Picard rank one (named predicate). -/
  picardOne' : Work.K3.PicardRankOneGeom 𝕜 S'
  /-- The fourfold carrying the link (a model of `ℙ⁴`). -/
  P : Scheme.{0}
  [varietyP : Variety 𝕜 P]
  /-- The Cremona transformation `ψ : ℙ⁴ ⤏ ℙ⁴` of the link. -/
  ψ : P.BirationalMap P
  [isOverψ : ψ.IsOver (Spec (.of 𝕜))]
  /-- The exceptional divisor of `ψ` on the source (birational to `S' × ℙ¹`). -/
  x : P
  /-- The exceptional divisor of `ψ⁻¹` on the target (birational to `S × ℙ¹`). -/
  y : P
  /-- `x` is the only exceptional divisor of `ψ`. -/
  exDiv_ψ : exDiv ψ = {x}
  /-- `y` is the only exceptional divisor of `ψ⁻¹`. -/
  exDiv_ψ_symm : exDiv ψ.symm = {y}
  /-- The base point `z₀` of the invariant. -/
  z₀ : P
  /-- `κ(y) ≅ κ(z₀)`: both are the function field `κ(S)(t)` of `S × ℙ¹`. -/
  resEquiv_y : ResEquiv 𝕜 y z₀
  /-- The birational identification `𝔸⁴ ⤏ P` (strong rationality of `ℙ⁴`). -/
  ε : (Work.K3.Affine4 𝕜).BirationalMap P
  [isOverε : ε.IsOver (Spec (.of 𝕜))]
  /-- The birational identification `P ⤏ 𝔸⁴`. -/
  δ : P.BirationalMap (Work.K3.Affine4 𝕜)
  [isOverδ : δ.IsOver (Spec (.of 𝕜))]
  /-- The transport `ε` contributes nothing to the coefficient. -/
  cInv_ε : cInv 𝕜 z₀ ε = 0
  /-- The transport `δ` contributes nothing to the coefficient. -/
  cInv_δ : cInv 𝕜 z₀ δ = 0
  /-- **(F1)**: the exceptional divisor `y` is birational to `S × ℙ¹`, i.e. its function field is
  `κ(S)(t)` (the paper: the exceptional divisor of `Bl_{S_0}` is birational to `S_0 × ℙ¹`, hence
  to `S × ℙ¹`). -/
  y_cylinder : IsP1BundleOver 𝕜 y S
  /-- **(F1)**: the exceptional divisor `x` is birational to `S' × ℙ¹`. -/
  x_cylinder : IsP1BundleOver 𝕜 x S'
  /-- **(F2)**: the cylinder rigidity of the paper's Lemma `lem-stbirCY` at `W = ℙ¹`. -/
  cylinderRigid : CylinderRigid 𝕜 S S'

attribute [instance] LinkCore.varietyS LinkCore.varietyS' LinkCore.varietyP
  LinkCore.isOverψ LinkCore.isOverε LinkCore.isOverδ

namespace LinkCore

variable {𝕜 : Type} [Field 𝕜] (C : LinkCore 𝕜)

local instance instVarS : Variety 𝕜 C.S := C.varietyS
local instance instVarS' : Variety 𝕜 C.S' := C.varietyS'
local instance instVarP : Variety 𝕜 C.P := C.varietyP
local instance instIsIntegralS : IsIntegral C.S := C.varietyS.isIntegral
local instance instIsIntegralS' : IsIntegral C.S' := C.varietyS'.isIntegral
local instance instOverP : C.P.Over (Spec (.of 𝕜)) := C.varietyP.over
local instance instOverS : C.S.Over (Spec (.of 𝕜)) := C.varietyS.over
local instance instOverS' : C.S'.Over (Spec (.of 𝕜)) := C.varietyS'.over

/-- **The ℙ¹-bundle bridge, proved from (F1) and (F2).**  This is the field `bridge` of
`Work.K3.K3Data`, derived rather than assumed: the two exceptional divisors of the link are
`ℙ¹`-bundles over the two centres, and the cylinder rigidity (F2) identifies the stable
birationality of the centres. -/
theorem bridge : ResEquiv 𝕜 C.y C.x → StablyBirat 𝕜 C.S C.S' :=
  bridge_of_clauses C.y_cylinder C.x_cylinder C.cylinderRigid

end LinkCore

/-! ## 4. The downstream K3 chapter objects -/

namespace LinkCore

variable {𝕜 : Type} [Field 𝕜] (C : LinkCore 𝕜)

local instance instVarS₂ : Variety 𝕜 C.S := C.varietyS
local instance instVarS'₂ : Variety 𝕜 C.S' := C.varietyS'
local instance instVarP₂ : Variety 𝕜 C.P := C.varietyP

/-- **The K3 link data `Work.K3.K3Data 𝕜`**, with the field `bridge` *proved* from (F1) and (F2).

This is the constructor a caller uses when they have the two geometric clauses
`IsP1BundleOver 𝕜 y S`, `IsP1BundleOver 𝕜 x S'` and the cylinder rigidity `CylinderRigid 𝕜 S S'`
instead of the opaque bridge. -/
noncomputable def toK3Data : Work.K3.K3Data 𝕜 where
  S := C.S
  varietyS := C.varietyS
  isK3 := C.isK3
  kTrivial := C.kTrivial
  picardOne := C.picardOne
  S' := C.S'
  varietyS' := C.varietyS'
  isK3' := C.isK3'
  kTrivial' := C.kTrivial'
  picardOne' := C.picardOne'
  P := C.P
  varietyP := C.varietyP
  ψ := C.ψ
  isOverψ := C.isOverψ
  x := C.x
  y := C.y
  exDiv_ψ := C.exDiv_ψ
  exDiv_ψ_symm := C.exDiv_ψ_symm
  z₀ := C.z₀
  resEquiv_y := C.resEquiv_y
  ε := C.ε
  isOverε := C.isOverε
  δ := C.δ
  isOverδ := C.isOverδ
  cInv_ε := C.cInv_ε
  cInv_δ := C.cInv_δ
  bridge := fun hres => StablyBirat_to_stablyBirational C.S C.S' (C.bridge hres)

/-- The K3 L-link `Work.K3.K3Link 𝕜`, from the bridge-free data, Totaro's input and the
non-isomorphism of the two centres. -/
noncomputable def toK3Link (T : Work.K3.TotaroInputAt 𝕜 C.S C.S')
    (h : ¬ Work.K3.IsoOver 𝕜 C.S C.S') :
    Work.K3.K3Link 𝕜 :=
  { toK3Data := C.toK3Data
    not_resEquiv_yx := (C.toK3Data).not_resEquiv_yx_of_totaro T h }

end LinkCore

/-- **The two exceptional divisors are not birational, from the bridge-free link data.**

This is the input `¬ ResEquiv 𝕜 y x` of the link (`Work.K3.K3Link.not_resEquiv_yx`), derived from
Totaro's input by the proved bridge: `κ(y) ≅ κ(x)` would make the centres stably birational, which
Totaro forbids for non-isomorphic `K`-trivial varieties of Picard number one. -/
theorem LinkCore.not_resEquiv_yx_of_totaro {𝕜 : Type} [Field 𝕜] (C : LinkCore 𝕜)
    (T : Work.K3.TotaroInputAt 𝕜 C.S C.S') (h : ¬ Work.K3.IsoOver 𝕜 C.S C.S') :
    ¬ ResEquiv 𝕜 C.y C.x :=
  (C.toK3Link T h).not_resEquiv_yx

/-- **The non-vanishing of the invariant coefficient, from the bridge-free link data.**  This is
the shape consumed by `Work.Motivic.not_gen_of_cInv_ne_zero` for `n = 4`. -/
theorem exists_cInv_ne_zero_of_LinkCore {𝕜 : Type} [Field 𝕜] (C : LinkCore 𝕜)
    (T : Work.K3.TotaroInputAt 𝕜 C.S C.S') (h : ¬ Work.K3.IsoOver 𝕜 C.S C.S') :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 4),
      cInv 𝕜 z₀ (φ : (Work.K3.Affine4 𝕜).BirationalMap (Work.K3.Affine4 𝕜)) ≠ 0 :=
  (C.toK3Link T h).exists_cInv_ne_zero

end

end Work.K3Inputs
