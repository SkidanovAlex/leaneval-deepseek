import Mathlib
import Submission.Work.DSMap.Map

namespace Work.DSCOH

open CategoryTheory CategoryTheory.Limits

/-- A zero `A`-module is finite. -/
lemma moduleCat_finite_of_isZero {A : Type*} [CommRing A] (M : ModuleCat A)
    (h : IsZero M) : Module.Finite A M := by
  have hs : Subsingleton M := ModuleCat.subsingleton_of_isZero h
  refine Module.Finite.of_fg_top ?_
  have hb : (⊤ : Submodule A M) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x _
    exact hs.elim x 0
  rw [hb]
  exact Submodule.fg_bot

/-- Finiteness is transported across an isomorphism of `A`-modules. -/
lemma moduleCat_finite_of_iso {A : Type*} [CommRing A] {M N : ModuleCat A}
    (h : Module.Finite A M) (e : M ≅ N) : Module.Finite A N :=
  h.equiv e.toLinearEquiv

theorem cechZ_coherence_of_homology_iso (A : Type*) [CommRing A]
    (X : AlgebraicGeometry.Scheme) (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    {ι : Type _} (U : ι → X.Opens) (K : CochainComplex (ModuleCat A) ℕ)
    (hK : ∀ q : ℕ, Nonempty ((DSMap.cech A X f U).homology q ≅ K.homology q))
    (hZ : ∃ N : ℤ, ∀ i : ℤ, Module.Finite A ((K.extend ComplexShape.embeddingUpNat).homology i) ∧
      (N < i → CategoryTheory.Limits.IsZero ((K.extend ComplexShape.embeddingUpNat).homology i))) :
    ∃ N : ℤ, ∀ i : ℤ, Module.Finite A ((DSMap.cechZ A X f U).homology i) ∧
      (N < i → CategoryTheory.Limits.IsZero ((DSMap.cechZ A X f U).homology i)) := by
  classical
  obtain ⟨N₀, hN₀⟩ := hZ
  refine ⟨N₀, fun i => ?_⟩
  by_cases hi : 0 ≤ i
  · -- `i ≥ 0`: compare the homology in degree `i` with the `ℕ`-indexed homology of `cech`
    have he : ComplexShape.embeddingUpNat.f i.toNat = i := Int.toNat_of_nonneg hi
    have isoC := HomologicalComplex.extendHomologyIso (DSMap.cech A X f U)
      ComplexShape.embeddingUpNat he
    have isoK := HomologicalComplex.extendHomologyIso K ComplexShape.embeddingUpNat he
    have isoHK : (DSMap.cech A X f U).homology i.toNat ≅ K.homology i.toNat :=
      Classical.choice (hK i.toNat)
    have iso : (DSMap.cechZ A X f U).homology i ≅
        (K.extend ComplexShape.embeddingUpNat).homology i := isoC ≪≫ isoHK ≪≫ isoK.symm
    obtain ⟨hfin, hzero⟩ := hN₀ i
    exact ⟨moduleCat_finite_of_iso hfin iso.symm, fun hN => IsZero.of_iso (hzero hN) iso⟩
  · -- `i < 0`: the extension is exact there, so the homology vanishes
    have hi' : i < 0 := not_le.mp hi
    have hev : ∀ n : ℕ, ComplexShape.embeddingUpNat.f n ≠ i := by
      intro n hn
      rw [ComplexShape.embeddingUpNat_f] at hn
      omega
    have hEx : ((DSMap.cech A X f U).extend ComplexShape.embeddingUpNat).ExactAt i :=
      HomologicalComplex.extend_exactAt (DSMap.cech A X f U) ComplexShape.embeddingUpNat i hev
    have hz : IsZero ((DSMap.cechZ A X f U).homology i) :=
      (HomologicalComplex.exactAt_iff_isZero_homology
        ((DSMap.cech A X f U).extend ComplexShape.embeddingUpNat) i).mp hEx
    exact ⟨moduleCat_finite_of_isZero _ hz, fun _ => hz⟩

end Work.DSCOH
