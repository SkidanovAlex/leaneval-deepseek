import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CY3Stab.Prod

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

/-- General form of the computation of the range of `Triplet.SpecTensorTo`: for any triple
`T = (x, y, s)` over `f : X ⟶ S` and `g : Y ⟶ S`, the image of
`T.SpecTensorTo : Spec (κ(x) ⊗_{κ(s)} κ(y)) ⟶ X ×_S Y` is exactly the set of points of the
fibre product whose two projections are `T.x` and `T.y`.  No hypothesis on `T` is needed. -/
theorem range_specTensorTo_aux {X Y S : Scheme.{0}} {f : X ⟶ S} {g : Y ⟶ S}
    (T : Scheme.Pullback.Triplet f g) :
    Set.range (fun p : PrimeSpectrum T.tensor => T.SpecTensorTo p) =
      {z : ↥(pullback f g) | pullback.fst f g z = T.x ∧ pullback.snd f g z = T.y} := by
  ext z
  constructor
  · -- the image of `SpecTensorTo` lies over `T.x` and `T.y`
    rintro ⟨p, rfl⟩
    exact ⟨Scheme.Pullback.Triplet.fst_SpecTensorTo_apply T p,
      Scheme.Pullback.Triplet.snd_SpecTensorTo_apply T p⟩
  · -- a point over the pair `(T.x, T.y)` is `(ofPoint z).SpecTensorTo ` of its eigene point
    rintro ⟨h1, h2⟩
    have hT : Scheme.Pullback.Triplet.ofPoint (f := f) (g := g) z = T := by
      apply Scheme.Pullback.Triplet.ext
      · simpa using h1
      · simpa using h2
    refine Set.mem_range.mpr ⟨Spec.map (Scheme.Pullback.Triplet.tensorCongr hT).inv
      (Scheme.Pullback.SpecOfPoint z), ?_⟩
    -- transport along the identification of the two tensors
    rw [← Scheme.Pullback.tensorCongr_SpecTensorTo hT]
    have hpoint : Spec.map (Scheme.Pullback.Triplet.tensorCongr hT).hom
        (Spec.map (Scheme.Pullback.Triplet.tensorCongr hT).inv
          (Scheme.Pullback.SpecOfPoint z)) = Scheme.Pullback.SpecOfPoint z := by
      rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
      rfl
    rw [Scheme.Hom.comp_apply, hpoint, Scheme.Pullback.SpecTensorTo_SpecOfPoint]

/-- **The range of `Triplet.SpecTensorTo` is the "double fibre" over the pair `(T.x, T.y)`.**
The points of the fibre product `𝔸ⁿ ×_{Spec 𝕜} X` lying over the pair `(T.x, T.y)` are exactly
the points `T.SpecTensorTo p` (`p` a prime of `T.tensor`).

Route: `⊆` is `Triplet.fst_SpecTensorTo_apply`/`Triplet.snd_SpecTensorTo_apply`; for `⊇`, a point
`z` with `fst z = T.x`, `snd z = T.y` satisfies `Triplet.ofPoint z = T` (`Triplet.ext`) and
`Triplet.SpecTensorTo_SpecOfPoint` writes `z = (Triplet.ofPoint z).SpecTensorTo (SpecOfPoint z)`,
which transports to `T.SpecTensorTo _` along `Triplet.tensorCongr_SpecTensorTo`.  The hypotheses
`hTx`/`hTy` are in fact not needed for the two inclusions, so a prover may prove the general
`f`/`g` version first and specialise. -/
theorem range_specTensorTo {𝕜 : Type} [Field 𝕜] (σ : Type) (X : Scheme.{0})
    [X.Over (Spec (CommRingCat.of 𝕜))] (x : X)
    (T : Scheme.Pullback.Triplet
      (CategoryTheory.over (𝔸(σ; Spec (CommRingCat.of 𝕜))) (Spec (CommRingCat.of 𝕜)))
      (CategoryTheory.over X (Spec (CommRingCat.of 𝕜))))
    (hTx : T.x = genericPoint (𝔸(σ; Spec (CommRingCat.of 𝕜)))) (hTy : T.y = x) :
    Set.range (fun p : PrimeSpectrum T.tensor => T.SpecTensorTo p) =
      {z | pullback.fst (CategoryTheory.over (𝔸(σ; Spec (CommRingCat.of 𝕜))) (Spec (CommRingCat.of 𝕜)))
              (CategoryTheory.over X (Spec (CommRingCat.of 𝕜))) z = T.x ∧
           pullback.snd (CategoryTheory.over (𝔸(σ; Spec (CommRingCat.of 𝕜))) (Spec (CommRingCat.of 𝕜)))
              (CategoryTheory.over X (Spec (CommRingCat.of 𝕜))) z = T.y} :=
  range_specTensorTo_aux T

end Work.CY3Stab.Prod
