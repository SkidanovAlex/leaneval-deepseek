import Mathlib
import Submission.Work.K3Inputs.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option backward.isDefEq.respectTransparency false

/-- **Affine spaces are additive under `×_{Spec 𝕜}`.**

The fibre product over `Spec 𝕜` of `𝔸ⁿ` and `𝔸ᵐ` (`Work.K3Inputs.AffineN 𝕜 _` is Mathlib's
`𝔸(Fin _; Spec 𝕜)`) is isomorphic to `𝔸^{n+m}`, compatibly with the structure maps to `Spec 𝕜`.

Indeed `𝔸(Fin k; Spec 𝕜) ≅ Spec (MvPolynomial (Fin k) 𝕜)` over `Spec 𝕜`
(`AlgebraicGeometry.AffineSpace.SpecIso`), the fibre product of two such spectra is the spectrum
of the tensor product (`AlgebraicGeometry.pullbackSpecIso`), and
`MvPolynomial (Fin n) 𝕜 ⊗[𝕜] MvPolynomial (Fin m) 𝕜 ≅ MvPolynomial (Fin n ⊕ Fin m) 𝕜 ≅
MvPolynomial (Fin (n+m)) 𝕜` (`MvPolynomial.tensorEquivSum` + `MvPolynomial.renameEquiv`). -/
theorem affineN_prodOver_affineN_iso (𝕜 : Type) [Field 𝕜] (n m : ℕ) :
    ∃ e : Work.K3.prodOver 𝕜 (AffineN 𝕜 n) (AffineN 𝕜 m) ≅ AffineN 𝕜 (n + m),
      e.hom.IsOver (Spec (.of 𝕜)) := by
  have hspec : ∀ k : ℕ,
      (AffineSpace.SpecIso (Fin k) (CommRingCat.of 𝕜)).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin k) 𝕜))) =
      (AffineN 𝕜 k ↘ Spec (CommRingCat.of 𝕜)) := by
    intro k
    have h := AffineSpace.SpecIso_inv_over (n := Fin k) (CommRingCat.of 𝕜)
    simp only [MvPolynomial.algebraMap_eq]
    rw [← h, Iso.hom_inv_id_assoc]
    rfl
  let S := Spec (CommRingCat.of 𝕜)
  let ιn := AffineSpace.SpecIso (Fin n) (CommRingCat.of 𝕜)
  let ιm := AffineSpace.SpecIso (Fin m) (CommRingCat.of 𝕜)
  let ιnm := AffineSpace.SpecIso (Fin (n + m)) (CommRingCat.of 𝕜)
  have he1 : (AffineN 𝕜 n ↘ S) ≫ 𝟙 S =
      ιn.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜))) := by
    rw [Category.comp_id, hspec n]
  have he2 : (AffineN 𝕜 m ↘ S) ≫ 𝟙 S =
      ιm.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin m) 𝕜))) := by
    rw [Category.comp_id, hspec m]
  let φ1 := pullback.map (AffineN 𝕜 n ↘ S) (AffineN 𝕜 m ↘ S)
      (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜))))
      (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin m) 𝕜))))
      ιn.hom ιm.hom (𝟙 S) he1 he2
  haveI hI : IsIso φ1 := pullback.map_isIso _ _ _ _ ιn.hom ιm.hom (𝟙 S) he1 he2
  let s1 : Work.K3.prodOver 𝕜 (AffineN 𝕜 n) (AffineN 𝕜 m) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜))))
        (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin m) 𝕜)))) := asIso φ1
  let s2 := pullbackSpecIso 𝕜 (MvPolynomial (Fin n) 𝕜) (MvPolynomial (Fin m) 𝕜)
  let ρa : TensorProduct 𝕜 (MvPolynomial (Fin n) 𝕜) (MvPolynomial (Fin m) 𝕜) ≃ₐ[𝕜]
      MvPolynomial (Fin (n + m)) 𝕜 :=
    (MvPolynomial.tensorEquivSum 𝕜 (Fin n) (Fin m) 𝕜).trans
      (MvPolynomial.renameEquiv 𝕜 (finSumFinEquiv (m := n) (n := m)))
  let s3 : Spec (CommRingCat.of (TensorProduct 𝕜 (MvPolynomial (Fin n) 𝕜) (MvPolynomial (Fin m) 𝕜))) ≅
      Spec (CommRingCat.of (MvPolynomial (Fin (n + m)) 𝕜)) :=
    Scheme.Spec.mapIso (ρa.symm.toRingEquiv.toCommRingCatIso.op)
  let s4 : Spec (CommRingCat.of (MvPolynomial (Fin (n + m)) 𝕜)) ≅ AffineN 𝕜 (n + m) := ιnm.symm
  have h1 : s1.hom ≫ (pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜))))
        (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin m) 𝕜))))
      ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜))))
      = Work.K3.prodOver 𝕜 (AffineN 𝕜 n) (AffineN 𝕜 m) ↘ S := by
    rw [show s1.hom = φ1 from rfl, show φ1 = pullback.map (AffineN 𝕜 n ↘ S)
      (AffineN 𝕜 m ↘ S) (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜))))
      (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin m) 𝕜))))
      ιn.hom ιm.hom (𝟙 S) he1 he2 from rfl, ← Category.assoc]
    simp only [pullback.map, pullback.lift_fst]
    rw [Category.assoc, hspec n]
    rfl
  have h2 : s2.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜
        (TensorProduct 𝕜 (MvPolynomial (Fin n) 𝕜) (MvPolynomial (Fin m) 𝕜))))
      = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜))))
          (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin m) 𝕜))))
        ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜))) := by
    simpa [s2] using pullbackSpecIso_hom_base 𝕜 (MvPolynomial (Fin n) 𝕜) (MvPolynomial (Fin m) 𝕜)
  have h3 : s3.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin (n + m)) 𝕜))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝕜
        (TensorProduct 𝕜 (MvPolynomial (Fin n) 𝕜) (MvPolynomial (Fin m) 𝕜)))) := by
    have hs3 : s3.hom = Spec.map (CommRingCat.ofHom ρa.symm.toRingEquiv.toRingHom) := by
      simp [s3, Functor.mapIso_hom, Iso.op_hom, Spec.map]
    rw [hs3, ← Spec.map_comp (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin (n + m)) 𝕜)))
      (CommRingCat.ofHom ρa.symm.toRingEquiv.toRingHom), ← CommRingCat.ofHom_comp]
    congr 1
    congr 1
    ext a
    exact ρa.symm.commutes a
  have h4 : s4.hom ≫ (AffineN 𝕜 (n + m) ↘ S) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin (n + m)) 𝕜))) := by
    have h := AffineSpace.SpecIso_inv_over (n := Fin (n + m)) (CommRingCat.of 𝕜)
    simp only [MvPolynomial.algebraMap_eq]
    exact h
  refine ⟨s1 ≪≫ s2 ≪≫ s3 ≪≫ s4, ?_⟩
  rw [Hom.isOver_iff]
  rw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom]
  simp only [Category.assoc]
  rw [h4, h3, h2, h1]

/-- **Associativity of the affine exponents.**  For a `𝕜`-scheme `X` and `n m : ℕ`,
`(X × 𝔸ⁿ) × 𝔸ᵐ ≅ X × 𝔸^{n+m}` over `Spec 𝕜`: `pullbackAssoc` re-brackets the fibre product
`(X ×_S 𝔸ⁿ) ×_S 𝔸ᵐ ≅ X ×_S (𝔸ⁿ ×_S 𝔸ᵐ)` and `affineN_prodOver_affineN_iso` identifies
`𝔸ⁿ ×_S 𝔸ᵐ` with `𝔸^{n+m}`. -/
theorem prodOver_assoc_iso (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))]
    (n m : ℕ) :
    Nonempty (Work.K3.prodOver 𝕜 (Work.K3.prodOver 𝕜 X (AffineN 𝕜 n)) (AffineN 𝕜 m) ≅
      Work.K3.prodOver 𝕜 X (AffineN 𝕜 (n + m))) := by
  obtain ⟨e, he⟩ := affineN_prodOver_affineN_iso 𝕜 n m
  let S := Spec (CommRingCat.of 𝕜)
  let f : X ⟶ S := X ↘ S
  let gn : AffineN 𝕜 n ⟶ S := AffineN 𝕜 n ↘ S
  let gm : AffineN 𝕜 m ⟶ S := AffineN 𝕜 m ↘ S
  let gnm : AffineN 𝕜 (n + m) ⟶ S := AffineN 𝕜 (n + m) ↘ S
  have heo : e.hom ≫ gnm = pullback.fst gn gm ≫ gn := by
    have h := (Hom.isOver_iff S).mp he
    rw [show (Work.K3.prodOver 𝕜 (AffineN 𝕜 n) (AffineN 𝕜 m)) ↘ S
        = pullback.fst gn gm ≫ gn from rfl] at h
    exact h
  have hcongr : pullback (pullback.fst f gn ≫ f) gm ≅ pullback (pullback.snd f gn ≫ gn) gm :=
    pullback.congrHom pullback.condition rfl
  have hassoc : pullback (pullback.snd f gn ≫ gn) gm ≅ pullback f (pullback.fst gn gm ≫ gn) :=
    pullbackAssoc f gn gn gm
  have he1 : f ≫ 𝟙 S = 𝟙 X ≫ f := by simp
  have he2 : (pullback.fst gn gm ≫ gn) ≫ 𝟙 S = e.hom ≫ gnm := by
    rw [Category.comp_id, heo]
  have hmap : pullback f (pullback.fst gn gm ≫ gn) ≅ pullback f gnm := by
    haveI : IsIso (pullback.map f (pullback.fst gn gm ≫ gn) f gnm (𝟙 X) e.hom (𝟙 S) he1 he2) :=
      pullback.map_isIso _ _ _ _ (𝟙 X) e.hom (𝟙 S) he1 he2
    exact asIso (pullback.map f (pullback.fst gn gm ≫ gn) f gnm (𝟙 X) e.hom (𝟙 S) he1 he2)
  exact ⟨hcongr ≪≫ hassoc ≪≫ hmap⟩

/-- **Stable birationality is insensitive to multiplication by affine space.**

`Work.K3Inputs.StablyBirat 𝕜 X Y` is `∃ n m, X × 𝔸ⁿ ∼ Y × 𝔸ᵐ` (birational in the sense of
Mathlib's `Scheme.Birational`, i.e. existence of a partial isomorphism).  Multiplying both sides
by `𝔸ᵏ`, `𝔸ˡ` shifts the exponents, so the relation is unchanged: this is the statement used in
the K3 chapter as "`S` and `S'` not stably birational implies `S × ℙ¹` and `S' × ℙ¹` are not
stably birational", i.e. the `[κ(S)(t)]`-coefficient of `c(ψ)` is computed at the correct
stratum.

Proved from the exponent bookkeeping `(X × 𝔸ⁿ) × 𝔸ᵐ ≅ X × 𝔸^{n+m}` (an isomorphism over
`Spec 𝕜`, from `pullbackAssoc` and `𝔸ⁿ ×_{Spec 𝕜} 𝔸ᵐ ≅ 𝔸^{n+m}`). -/
theorem not_stablyBirat_prod (𝕜 : Type) [Field 𝕜] {X Y : Scheme.{0}}
    [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))]
    (h : ¬ Work.K3Inputs.StablyBirat 𝕜 X Y) (n m : ℕ) :
    ¬ Work.K3Inputs.StablyBirat 𝕜 (Work.K3.prodOver 𝕜 X (Work.K3Inputs.AffineN 𝕜 n))
      (Work.K3.prodOver 𝕜 Y (Work.K3Inputs.AffineN 𝕜 m)) := by
  intro h'
  apply h
  obtain ⟨p, q, hpq⟩ := h'
  obtain ⟨eX⟩ := prodOver_assoc_iso 𝕜 X n p
  obtain ⟨eY⟩ := prodOver_assoc_iso 𝕜 Y m q
  refine ⟨n + p, m + q, ?_⟩
  exact (Scheme.Birational.symm ⟨PartialIso.ofIso eX⟩).trans
    (hpq.trans ⟨PartialIso.ofIso eY⟩)

end Work.K3Inputs
