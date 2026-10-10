import Mathlib
import Submission.Work.MotT.Defs
import Submission.Work.MotA.resEquiv_iff_fractionRing
import Submission.Work.MotC.algEquiv_ratFunc_cancel
import Submission.Work.MotC.ruling_of_constantsOnly
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.MotT

noncomputable section

/-! ## §1 `ConstantsOnly` versus geometric ruledness

Two elementary facts about `Work.MotV.ConstantsOnly`: it is an isomorphism invariant of the base
field, and it is incompatible with `Work.MotV.GeomRuled` (a non-constant embedding into a rational
function field).  Both convert the "junk class" alternative of the link certificate into a
contradiction. -/

/-- `ConstantsOnly` is preserved by a `𝕜`-algebra isomorphism of the base fields: if `e : F ≃ₐ[𝕜] F'`
and every `𝕜`-embedding of `F` into a one-variable rational function field lands in the constants,
then the same holds for `F'` (compose with `e`). -/
theorem constantsOnly_of_algEquiv {𝕜 : Type} [Field 𝕜] {F F' : Type} [Field F] [Field F']
    [Algebra 𝕜 F] [Algebra 𝕜 F'] (e : F ≃ₐ[𝕜] F') (h : Work.MotV.ConstantsOnly 𝕜 F) :
    Work.MotV.ConstantsOnly 𝕜 F' := by
  intro M _ _ ι x
  obtain ⟨c, hc⟩ := h M (ι.comp e.toAlgHom) (e.symm x)
  exact ⟨c, by simpa using hc⟩

/-- A geometrically ruled field is not constants-only: the non-constant embedding witnessing
`GeomRuled` contradicts `ConstantsOnly` applied to it. -/
theorem not_constantsOnly_of_geomRuled {𝕜 : Type} [Field 𝕜] (F : Type) [Field F] [Algebra 𝕜 F]
    (h : Work.MotV.GeomRuled 𝕜 F) : ¬ Work.MotV.ConstantsOnly 𝕜 F := by
  rintro hc
  obtain ⟨M, hM, hA, ι, x, hx⟩ := h
  letI := hM
  letI := hA
  obtain ⟨c, hc'⟩ := hc M ι x
  exact hx c hc'

/-! ## §2 The class separation -/

/-- **Class separation (general form).**  Let `z` be a point of `𝔸³_𝕜` whose class is
`RatFunc F₁` with `F₁` constants-only, and `x` a point whose class is `RatFunc B`.  If `x` and `z`
have the same class (`ResEquiv`), then the base fields are isomorphic: the composite
`RatFunc F₁ ≅ RatFunc B` has its ruling hypothesis supplied by `ConstantsOnly` via
`Work.MotC.ruling_of_constantsOnly`, so `Work.MotC.algEquiv_ratFunc_cancel` applies.

The assertion that `RatFunc F₁` and `RatFunc B` have no `𝕜`-algebra isomorphism is therefore
exactly a statement about `F₁` and `B` — this is the whole content of the class separation in the
`n = 3` certificate. -/
theorem nonempty_algEquiv_of_resEquiv_of_class {𝕜 : Type} [Field 𝕜] {F₁ B : Type} [Field F₁]
    [Field B] [Algebra 𝕜 F₁] [Algebra 𝕜 B] (hCO : Work.MotV.ConstantsOnly 𝕜 F₁)
    {x z : Work.MotA.polySpec 𝕜 3}
    (hz : Nonempty (Work.MotV.resF 𝕜 z ≃ₐ[𝕜] RatFunc F₁))
    (hx : Nonempty (Work.MotV.resF 𝕜 x ≃ₐ[𝕜] RatFunc B))
    (hres : ResEquiv 𝕜 x z) :
    Nonempty (F₁ ≃ₐ[𝕜] B) := by
  obtain ⟨e1⟩ := hx
  obtain ⟨e2⟩ := hz
  obtain ⟨e3⟩ := (Work.MotA.resEquiv_iff_fractionRing 𝕜 3 3 x z).mp hres
  have θ : RatFunc F₁ ≃ₐ[𝕜] RatFunc B := e2.symm.trans (e3.symm.trans e1)
  exact Work.MotC.algEquiv_ratFunc_cancel θ (Work.MotC.ruling_of_constantsOnly hCO θ)

/-- **T9.** The `n = 3` certificate from a link certificate at the base field: no spreading is
needed, and the only content is the class separation.  Given `L : Work.MotV.LinkCert 𝕜 F₁ F₂`, its
special divisor `zP` (with residue field `RatFunc F₁`) already satisfies the certificate conditions
once one shows that no *other* divisor of `G` and no divisor of `F` has residue field
`𝕜`-isomorphic to `κ(zP)`.

Route.  `Work.MotV.CertN` needs, for `x` of coheight one with `G ∈ x.asIdeal` (resp. `F ∈ x.asIdeal`),
the failure of `ResEquiv 𝕜 x zP`.
* If `x` is a *junk* class (`Work.MotV.JunkClass 𝕜 x`, i.e. `resF 𝕜 x ≅ RatFunc F₀` for some
  `F₀` with `Work.MotV.GeomRuled 𝕜 F₀`), then `ResEquiv 𝕜 x zP` gives
  `RatFunc F₁ ≅ RatFunc F₀` by `Work.MotA.resEquiv_iff_fractionRing` (transitivity of `≅`), hence
  `F₁ ≅ F₀` by `Work.MotC.algEquiv_ratFunc_cancel` with the ruling hypothesis
  `Work.MotC.ruling_of_constantsOnly` applied to `hCO`; transporting `ConstantsOnly 𝕜 F₁` along that
  isomorphism contradicts `GeomRuled 𝕜 F₀` (a non-constant map `F₀ →ₐ[𝕜] RatFunc M` is composed with
  `ConstantsOnly` to force constancy).  Note the orientation: apply the cancellation to the iso
  `RatFunc F₁ ≃ RatFunc F₀` whose ruling hypothesis is supplied by `hCO` on `F₁`.
* On the `F` side, `resF 𝕜 x ≅ RatFunc F₂` together with `ResEquiv 𝕜 x zP` gives
  `RatFunc F₁ ≅ RatFunc F₂`, hence `F₁ ≅ F₂`, contradicting `hR`.
The fields and points of `CertN 𝕜 3` are those of `L` (`F`, `G`, `hF`, `hG`, `Φ`, `z := zP`,
`z_ht`, `z_mem`).

Declare it in namespace `Work.MotT` so that its full name is `Work.MotT.certN3_of_linkCert`. -/
theorem certN3_of_linkCert (𝕜 : Type) [Field 𝕜] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Algebra 𝕜 F₁] [Algebra 𝕜 F₂] (L : Work.MotV.LinkCert 𝕜 F₁ F₂)
    (hCO : Work.MotV.ConstantsOnly 𝕜 F₁) (hR : IsEmpty (F₁ ≃ₐ[𝕜] F₂)) :
    Nonempty (Work.MotV.CertN 𝕜 3) := by
  classical
  refine ⟨{ F := L.F, G := L.G, hF := L.hF, hG := L.hG, Φ := L.Φ, z := L.zP,
            z_ht := L.zP_ht, z_mem := L.zP_mem, G_other := ?_, F_none := ?_ }⟩
  · -- `G`-side: the only prime divisor of `V(G)` with the class of `zP` is `zP` itself; every
    -- other one is junk, and a junk class cannot coincide with `κ(zP) = RatFunc F₁`.
    intro x hx1 hxmem hne hres
    obtain ⟨F₀, hF₀, hA₀, hgeom, hiso⟩ := L.G_other x hx1 hxmem hne
    letI := hF₀
    letI := hA₀
    exact not_constantsOnly_of_geomRuled F₀ hgeom (constantsOnly_of_algEquiv
      (Classical.choice (nonempty_algEquiv_of_resEquiv_of_class hCO L.zP_res hiso hres)) hCO)
  · -- `F`-side: no prime divisor of `V(F)` has the class of `zP`; an `F₂`-class gives `F₁ ≅ F₂`
    -- (contradicting `hR`), a junk class gives `F₁ ≅ F₀` and hence constants-only-ness of `F₀`.
    intro x hx1 hxmem hres
    rcases L.F_all x hx1 hxmem with hiso | ⟨F₀, hF₀, hA₀, hgeom, hiso⟩
    · exact hR.false
        (Classical.choice (nonempty_algEquiv_of_resEquiv_of_class hCO L.zP_res hiso hres))
    · letI := hF₀
      letI := hA₀
      exact not_constantsOnly_of_geomRuled F₀ hgeom (constantsOnly_of_algEquiv
        (Classical.choice (nonempty_algEquiv_of_resEquiv_of_class hCO L.zP_res hiso hres)) hCO)

end

end Work.MotT
