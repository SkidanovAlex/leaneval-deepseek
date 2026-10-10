import Mathlib
import Submission.Work.K3.coheight_le_of_flat
import Submission.Work.CY3Stab.Prod.range_specTensorTo
import Submission.Work.CY3Stab.Prod.isPrime_map_includeRight_tensor
import Submission.Work.CY3Stab.Prod.height_map_includeRight_tensor
import Submission.Work.CY3Stab.Prod.chart_of_isos
import Submission.Work.CY3Stab.Prod.isoSpec_over

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CY3Stab.Prod

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory.Limits TensorProduct

noncomputable section

set_option linter.style.haveILetI false

/-! ## Auxiliary lemmas -/

/-- The generic point of `Spec R` for a domain `R` is the zero prime. -/
theorem genericPoint_Spec_eq_bot {R : Type} [CommRing R] [IsDomain R] :
    genericPoint (Spec (CommRingCat.of R)) = (⊥ : PrimeSpectrum R) := by
  have h : IsGenericPoint (⊥ : PrimeSpectrum R) (Set.univ : Set (PrimeSpectrum R)) := by
    rw [isGenericPoint_def, PrimeSpectrum.closure_singleton]
    ext p
    simp [PrimeSpectrum.zeroLocus]
  exact (h.eq (genericPoint_spec _)).symm

/-! ## The core computation -/

set_option maxHeartbeats 2000000 in
/-- **The local computation of the coheight of the generic point of a fibre of a cylinder.**

Let `f : W ⟶ Spec 𝕜`, `g : X' ⟶ Spec 𝕜` be a cospan, `eW : W ≅ Spec 𝕜[X_σ]` over `Spec 𝕜`,
`U ⊆ X'` an affine open with `eU : U ≅ Spec A` over `Spec 𝕜`, and `T` a `Triplet` over the cospan
with `T.x = genericPoint W` and `T.y ∈ U`.  Then the coheight of the point
`T.SpecTensorTo pt` (where `pt` is the zero prime of `T.tensor`) equals the height of the prime of
`T.y` in the affine model `Spec A`. -/
theorem coheight_cospan {𝕜 : Type} [Field 𝕜] (σ : Type) (A : Type) [CommRing A] [Algebra 𝕜 A]
    [IsNoetherianRing A] {W X' : Scheme.{0}}
    (f : W ⟶ Spec (CommRingCat.of 𝕜)) (g : X' ⟶ Spec (CommRingCat.of 𝕜))
    (eW : W ≅ Spec (CommRingCat.of (MvPolynomial σ 𝕜)))
    (heW : eW.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial σ 𝕜))) = f)
    (U : X'.Opens) (eU : ↑U ≅ Spec (CommRingCat.of A))
    (heU : eU.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜 A)) = U.ι ≫ g)
    (T : Scheme.Pullback.Triplet f g) [IrreducibleSpace W] (hTx : T.x = genericPoint W)
    (hyU : T.y ∈ U) (pt : PrimeSpectrum T.tensor) (hpt : pt.asIdeal = ⊥) [IsDomain T.tensor] :
    Order.coheight (T.SpecTensorTo pt) = (eU.hom (⟨T.y, hyU⟩ : ↑U)).asIdeal.height := by
  haveI hD : IsDomain (↥T.tensor) := ‹IsDomain T.tensor›
  have hSdom : IsDomain (MvPolynomial σ 𝕜) := inferInstance
  -- the prime of `T.y` in the affine model
  set 𝔭 : Ideal A := (eU.hom (⟨T.y, hyU⟩ : ↑U)).asIdeal with h𝔭def
  have h𝔭 : 𝔭.IsPrime := (eU.hom (⟨T.y, hyU⟩ : ↑U)).isPrime
  haveI := h𝔭
  -- the extension prime
  obtain ⟨hqpr, hqA, hqS⟩ := isPrime_map_includeRight_tensor 𝕜 σ A 𝔭
  let q : Ideal (MvPolynomial σ 𝕜 ⊗[𝕜] A) :=
    Ideal.map (Algebra.TensorProduct.includeRight (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)).toRingHom 𝔭
  have hqpr' : q.IsPrime := hqpr
  have hqA' : q.comap (Algebra.TensorProduct.includeRight (R := 𝕜)
      (A := MvPolynomial σ 𝕜) (B := A)).toRingHom = 𝔭 := hqA
  have hqS' : q.comap (Algebra.TensorProduct.includeLeftRingHom (R := 𝕜)
      (A := MvPolynomial σ 𝕜) (B := A)) = ⊥ := hqS
  -- the chart
  obtain ⟨Φ, hΦimm, hrest⟩ := chart_of_isos (𝕜 := 𝕜) (σ := σ) (A := A)
    (f := f) (g := g) (U := U) (eW := eW) (heW := heW) (eU := eU) (heU := heU)
  obtain ⟨hrange, hfst, hsnd⟩ := hrest
  haveI := hΦimm
  -- the point of the chart and its image in the fibre product
  let qPt : ↥(Spec (CommRingCat.of (MvPolynomial σ 𝕜 ⊗[𝕜] A))) := ⟨q, hqpr'⟩
  let z : ↥(pullback f g) := Φ qPt
  have hzdef : z = Φ qPt := rfl
  -- the two projections of `z`
  have hzpt : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := 𝕜)
      (A := MvPolynomial σ 𝕜) (B := A))) qPt = (⊥ : PrimeSpectrum (MvPolynomial σ 𝕜)) := by
    refine PrimeSpectrum.ext ?_
    show (PrimeSpectrum.comap (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := 𝕜)
      (A := MvPolynomial σ 𝕜) (B := A))).hom qPt).asIdeal = (⊥ : PrimeSpectrum (MvPolynomial σ 𝕜)).asIdeal
    rw [PrimeSpectrum.comap_asIdeal]
    exact hqS'
  have hz₁ : pullback.fst f g z = T.x := by
    have h1 : pullback.fst f g z = eW.inv (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A))) qPt) := by
      show (Φ ≫ pullback.fst f g) qPt = _
      rw [hfst]
      simp only [Scheme.Hom.comp_apply]
    rw [h1, hzpt]
    rw [← genericPoint_Spec_eq_bot (R := MvPolynomial σ 𝕜), hTx]
    exact genericPoint_eq_of_isOpenImmersion eW.inv
  have hz₂ : pullback.snd f g z = T.y := by
    have h1 : pullback.snd f g z = U.ι (eU.inv (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)).toRingHom) qPt)) := by
      show (Φ ≫ pullback.snd f g) qPt = _
      rw [hsnd]
      simp only [Scheme.Hom.comp_apply]
    rw [h1]
    have h0 : ∀ Y : ↑U, eU.inv (eU.hom Y) = Y := by
      intro Y
      show (eU.hom ≫ eU.inv) Y = Y
      rw [Iso.hom_inv_id]
      rfl
    have h0' : ∀ Y : ↥(Spec (CommRingCat.of A)), eU.hom (eU.inv Y) = Y := by
      intro Y
      show (eU.inv ≫ eU.hom) Y = Y
      rw [Iso.inv_hom_id]
      rfl
    have h2 : eU.hom (eU.inv (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)).toRingHom) qPt)) = eU.hom (⟨T.y, hyU⟩ : ↑U) := by
      rw [h0']
      refine PrimeSpectrum.ext ?_
      show (PrimeSpectrum.comap (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := 𝕜)
        (A := MvPolynomial σ 𝕜) (B := A)).toRingHom).hom qPt).asIdeal = (eU.hom (⟨T.y, hyU⟩ : ↑U)).asIdeal
      rw [PrimeSpectrum.comap_asIdeal]
      simp only [CommRingCat.hom_ofHom]
      rw [hqA', h𝔭def]
    have h3 : eU.inv (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)).toRingHom) qPt) = (⟨T.y, hyU⟩ : ↑U) := by
      have h4 := congrArg eU.inv h2
      rwa [h0 (⟨T.y, hyU⟩ : ↑U), h0] at h4
    rw [h3]
    rfl
  -- `z` is in the range of `T.SpecTensorTo`
  have hzrange : z ∈ Set.range (fun p : PrimeSpectrum T.tensor => T.SpecTensorTo p) := by
    rw [range_specTensorTo_aux (T := T)]
    exact ⟨hz₁, hz₂⟩
  obtain ⟨Q, hQ₀⟩ := hzrange
  have hQ : T.SpecTensorTo Q = z := hQ₀
  -- the lift of `SpecTensorTo` through the chart
  have hrange' : Set.range (fun p : ↥(Spec T.tensor) => T.SpecTensorTo p)
      ⊆ Set.range (Φ : _ ⟶ pullback f g) := by
    have hop : Set.range (Φ : _ ⟶ pullback f g) = ((pullback.snd f g) ⁻¹ᵁ U : Set _) := by
      rw [← hrange]
      exact Set.ext fun y => (Scheme.Hom.mem_opensRange (f := Φ)).trans Set.mem_range.symm
    rw [hop]
    rintro _ ⟨p, rfl⟩
    show pullback.snd f g (T.SpecTensorTo p) ∈ U
    rw [Scheme.Pullback.Triplet.snd_SpecTensorTo_apply]
    exact hyU
  let lift : Spec T.tensor ⟶ Spec (CommRingCat.of (MvPolynomial σ 𝕜 ⊗[𝕜] A)) :=
    IsOpenImmersion.lift (Φ : _ ⟶ _) (T.SpecTensorTo) hrange'
  have hlift_fac : lift ≫ Φ = T.SpecTensorTo := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨fc, hfc⟩ := Spec.map_surjective lift
  -- the key inequality
  have hcomap : ∀ R : ↥(Spec T.tensor), (lift R).asIdeal = Ideal.comap fc.hom R.asIdeal := by
    intro R
    have h1 : lift R = (Spec.map fc) R := by rw [hfc]
    rw [h1]
    exact PrimeSpectrum.comap_asIdeal fc.hom R
  have hQ' : Ideal.comap fc.hom Q.asIdeal = q := by
    have h1 : lift Q = qPt := by
      have h2 : Φ (lift Q) = Φ qPt := by
        have h3 : Φ (lift Q) = T.SpecTensorTo Q := by
          show (lift ≫ Φ) Q = _
          rw [hlift_fac]
        rw [h3, hQ, hzdef]
      exact (Scheme.Hom.isOpenEmbedding Φ).injective h2
    rw [← hcomap Q, h1]
  have hker : RingHom.ker fc.hom ≤ q := by
    have hbot : RingHom.ker fc.hom = Ideal.comap fc.hom pt.asIdeal := by
      rw [hpt]
      exact RingHom.ker_eq_comap_bot fc.hom
    rw [hbot, ← hQ']
    exact Ideal.comap_mono (hpt.symm ▸ bot_le)
  -- bookkeeping
  have hco : Order.coheight (T.SpecTensorTo pt) = (RingHom.ker fc.hom).height := by
    have h1 : T.SpecTensorTo pt = Φ (lift pt) := by
      show T.SpecTensorTo pt = (lift ≫ Φ) pt
      rw [hlift_fac]
    rw [h1, coheight_eq_of_isOpenImmersion (f := Φ) (x := lift pt),
      ← idealHeight_eq_coheight (CommRingCat.of (MvPolynomial σ 𝕜 ⊗[𝕜] A)) (lift pt),
      hcomap pt, hpt, RingHom.ker_eq_comap_bot]
  have hle : (RingHom.ker fc.hom).height ≤ 𝔭.height :=
    (Ideal.height_mono hker).trans_eq (height_map_includeRight_tensor 𝕜 σ A 𝔭)
  have hge : 𝔭.height ≤ Order.coheight (T.SpecTensorTo pt) := by
    have h1 : Order.coheight T.y ≤ Order.coheight (T.SpecTensorTo pt) := by
      have h1' := Work.K3.coheight_le_of_flat (pullback.snd f g) (T.SpecTensorTo pt)
      rwa [Scheme.Pullback.Triplet.snd_SpecTensorTo_apply (T := T) pt] at h1'
    have h3 : Order.coheight T.y = 𝔭.height := by
      rw [show T.y = U.ι (⟨T.y, hyU⟩ : ↑U) from rfl,
        coheight_eq_of_isOpenImmersion (f := U.ι) (x := (⟨T.y, hyU⟩ : ↑U)),
        ← coheight_eq_of_isOpenImmersion (f := eU.hom) (x := (⟨T.y, hyU⟩ : ↑U)),
        ← idealHeight_eq_coheight (CommRingCat.of A) (eU.hom (⟨T.y, hyU⟩ : ↑U)), h𝔭def]
    exact h3 ▸ h1
  rw [show (eU.hom (⟨T.y, hyU⟩ : ↑U)).asIdeal.height = 𝔭.height from rfl, hco]
  exact le_antisymm hle (hco ▸ hge)

set_option maxHeartbeats 2000000 in
/-- **The reduction of the target statement to the local computation.** -/
theorem coheight_specTensorTo_bot_aux {𝕜 : Type} [Field 𝕜] (n : Type) (X : Scheme.{0})
    [X.Over (Spec (CommRingCat.of 𝕜))] [IsLocallyNoetherian X] (x : X)
    (T : Scheme.Pullback.Triplet
      (CategoryTheory.over (𝔸(n; Spec (CommRingCat.of 𝕜))) (Spec (CommRingCat.of 𝕜)))
      (CategoryTheory.over X (Spec (CommRingCat.of 𝕜))))
    (hTx : T.x = genericPoint (𝔸(n; Spec (CommRingCat.of 𝕜)))) (hTy : T.y = x)
    [IsDomain T.tensor] :
    Order.coheight (T.SpecTensorTo (⊥ : PrimeSpectrum T.tensor)) = Order.coheight x := by
  -- an affine open neighbourhood of `x`
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  -- the `𝕜`-algebra structure on `Γ(X,U)` and its Noetherianity
  letI alg : Algebra 𝕜 ↥(X.presheaf.obj (Opposite.op U)) :=
    ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫ (X ↘ Spec (CommRingCat.of 𝕜)).appLE ⊤ U le_top).hom.toAlgebra
  haveI : IsNoetherianRing ↥(X.presheaf.obj (Opposite.op U)) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  -- the affine model of `𝔸ⁿ` is a morphism over `Spec 𝕜`
  have heW : (AffineSpace.SpecIso n (CommRingCat.of 𝕜)).hom ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : 𝕜 →+* MvPolynomial n 𝕜)) =
      (𝔸(n; Spec (CommRingCat.of 𝕜)) ↘ Spec (CommRingCat.of 𝕜)) := by
    rw [← AffineSpace.SpecIso_inv_over (n := n) (R := CommRingCat.of 𝕜), Iso.hom_inv_id_assoc]
  -- the affine chart of `X` is a morphism over `Spec 𝕜`
  have heU : hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap 𝕜 ↥(X.presheaf.obj (Opposite.op U)))) =
      U.ι ≫ (X ↘ Spec (CommRingCat.of 𝕜)) := isoSpec_over 𝕜 X U hU
  have hyU : T.y ∈ U := by rw [hTy]; exact hxU
  -- apply the local computation
  have hcore := coheight_cospan (𝕜 := 𝕜) (σ := n) (A := ↥(X.presheaf.obj (Opposite.op U)))
    (f := (𝔸(n; Spec (CommRingCat.of 𝕜)) ↘ Spec (CommRingCat.of 𝕜)))
    (g := (X ↘ Spec (CommRingCat.of 𝕜)))
    (eW := AffineSpace.SpecIso n (CommRingCat.of 𝕜)) heW U hU.isoSpec heU
    T hTx hyU (⊥ : PrimeSpectrum T.tensor) rfl
  -- the right hand side is the coheight of `x`
  have h1 : Order.coheight x = (hU.isoSpec.hom (⟨T.y, hyU⟩ : ↑U)).asIdeal.height := by
    have h2 : (⟨T.y, hyU⟩ : ↑U) = (⟨x, hxU⟩ : ↑U) := Subtype.ext hTy
    rw [h2,
      idealHeight_eq_coheight (CommRingCat.of ↥(X.presheaf.obj (Opposite.op U)))
        (hU.isoSpec.hom (⟨x, hxU⟩ : ↑U)),
      coheight_eq_of_isOpenImmersion (f := hU.isoSpec.hom) (x := (⟨x, hxU⟩ : ↑U))]
    exact coheight_eq_of_isOpenImmersion (f := U.ι) (x := (⟨x, hxU⟩ : ↑U))
  rw [hcore, h1]

/-- **The coheight of the generic point of a `Triplet` fibre over the generic point of `𝔸ⁿ`.**

For a locally Noetherian `𝕜`-scheme `X`, a point `x : X` and a `Triplet` `T` over the cospan
`(𝔸ⁿ ⟶ Spec 𝕜, X ⟶ Spec 𝕜)` whose first point is the generic point of `𝔸ⁿ` and whose second point
is `x`, the coheight of the point `T.SpecTensorTo ⊥` — the generic point of the `Triplet` fibre —
equals the coheight of `x`. -/
theorem coheight_specTensorTo_bot {𝕜 : Type} [Field 𝕜] {n : Type}
    (X : AlgebraicGeometry.Scheme.{0})
    [AlgebraicGeometry.Scheme.Over X (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [IsLocallyNoetherian X] (x : X)
    (T : AlgebraicGeometry.Scheme.Pullback.Triplet
      (CategoryTheory.over (AlgebraicGeometry.AffineSpace n (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
        (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
      (CategoryTheory.over X (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))))
    (hTx : T.x = genericPoint (AlgebraicGeometry.AffineSpace n (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))))
    (hTy : T.y = x) [IsDomain T.tensor] :
    Order.coheight (T.SpecTensorTo (⊥ : PrimeSpectrum T.tensor)) = Order.coheight x :=
  coheight_specTensorTo_bot_aux n X x T hTx hTy

end

end Work.CY3Stab.Prod
