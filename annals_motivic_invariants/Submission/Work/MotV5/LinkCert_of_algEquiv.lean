import Mathlib
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

noncomputable section

/-- **Functoriality of `RatFunc` in the field.**

A `K`-algebra isomorphism `e : F ≃ₐ[K] F'` of fields induces a `K`-algebra isomorphism
`RatFunc F ≃ₐ[K] RatFunc F'` of their rational function fields.

Route: `RatFunc F ≃ₐ[K] FractionRing F[X]` (`RatFunc.toFractionRingAlgEquiv`), the latter transported
along `Polynomial.mapAlgEquiv e : F[X] ≃ₐ[K] F'[X]` by `IsFractionRing.algEquivOfAlgEquiv`
(note `RatFunc F' = FractionRing F'[X]`). -/
def ratFuncAlgEquivOfAlgEquiv {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (e : F ≃ₐ[K] F') : RatFunc F ≃ₐ[K] RatFunc F' :=
  (RatFunc.toFractionRingAlgEquiv F K).trans
    ((IsFractionRing.algEquivOfAlgEquiv (Polynomial.mapAlgEquiv e)).trans
      (RatFunc.toFractionRingAlgEquiv F' K).symm)

/-- **Transport of a link certificate along `K`-algebra isomorphisms of the two fields.**

`Work.MotV.LinkCert K F₁ F₂` consists of polynomials `F, G`, an isomorphism
`Localization.Away F ≃ₐ[K] Localization.Away G`, a height-one prime `zP` containing `G`, and the
clauses `zP_res : Nonempty (resF K zP ≃ₐ[K] RatFunc F₁)`, `G_other` and `F_all` — the last two
mentioning `F₁`, `F₂` only through `resF … ≃ₐ[K] RatFunc Fᵢ`.  Hence an isomorphism
`e₁ : F₁ ≃ₐ[K] F₁'` transports the certificate to `F₁'` as soon as one has the induced isomorphism
`RatFunc F₁ ≃ₐ[K] RatFunc F₁'` (functoriality of `RatFunc`, e.g. via
`RatFunc F = FractionRing F[X]`, `Polynomial.mapAlgEquiv` and
`IsFractionRing.algEquivOfAlgEquiv`), and similarly for `e₂`.

**Why it is needed.**  The characteristic-`5` Crauder–Katz chart, built by the new subproject
`MotAS` (`MOTIVIC_KDATA_LEAD.md` §6), is stated for the *explicit* twist field
`twistFieldAS D g = K(y_j/y_0)` with `y = M(asRoot g)⁻¹κ` (where `M_ij = (w + i)^j` and
`℘(w) = g`), not for `MotV5`'s abstract `asTwistFieldTrue D g τ σS`; the node AS-EQ
(`twistFieldAS_eq`) identifies the two twist fields.  So the subproject's `linkCert_AS'`, whose
conclusion is `Nonempty (Work.MotV.LinkCert (RatFunc 𝕜) ↥(twistFieldAS D (fAS 𝕜))
↥(twistFieldAS D (2 • fAS 𝕜)))` under `KleinData.ASGood D`, can be moved across to `MotV5`'s fields
by this transport, yielding the LK_AS node for `MotV5`. -/
theorem LinkCert_of_algEquiv {K : Type} [Field K] {F₁ F₂ F₁' F₂' : Type}
    [Field F₁] [Field F₂] [Field F₁'] [Field F₂']
    [Algebra K F₁] [Algebra K F₂] [Algebra K F₁'] [Algebra K F₂']
    (e₁ : F₁ ≃ₐ[K] F₁') (e₂ : F₂ ≃ₐ[K] F₂') (L : Work.MotV.LinkCert K F₁ F₂) :
    Nonempty (Work.MotV.LinkCert K F₁' F₂') := by
  have r₁ := ratFuncAlgEquivOfAlgEquiv e₁
  have r₂ := ratFuncAlgEquivOfAlgEquiv e₂
  refine ⟨L.F, L.G, L.hF, L.hG, L.Φ, L.zP, L.zP_ht, L.zP_mem, ?_, L.G_other, ?_⟩
  · rcases L.zP_res with ⟨e⟩
    exact ⟨e.trans r₁⟩
  · intro x hx hmem
    rcases L.F_all x hx hmem with h | h
    · exact Or.inl ⟨h.some.trans r₂⟩
    · exact Or.inr h

end

end Work.MotV5
