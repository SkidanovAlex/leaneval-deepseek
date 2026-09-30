import Mathlib
import Submission.Work.Pi6.BOCK.BockMaps
import Submission.Work.Pi6.BOCK.ExpTensBasic
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-!
# AREA BOCK — exactness of the Bockstein sequence

The three exactness statements of
`Hₙ₊₁(X;ℤ) --·p--> Hₙ₊₁(X;ℤ) --red--> Hₙ₊₁(X;ℤ/p) --del--> Hₙ(X;ℤ) --·p--> Hₙ(X;ℤ)`,
obtained from the homology long exact sequence of the short exact sequence of chain complexes
`Work.Pi6.EMZ.bockSES` and the identification `Work.Pi6.BOCK.eCIso'` of the homology of its third
term with `H_*(X;ℤ/p)`.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

namespace Work.Pi6.BOCK

noncomputable section

/-- **Exactness is invariant under conjugation by additive equivalences.** -/
theorem Function.Exact.of_comp_addEquiv {A B C A' B' C' : Type*}
    [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]
    [AddCommMonoid A'] [AddCommMonoid B'] [AddCommMonoid C']
    {f : A → B} {g : B → C} {f' : A' → B'} {g' : B' → C'}
    (eA : A' ≃+ A) (eB : B' ≃+ B) (eC : C' ≃+ C)
    (hf : ∀ x, eB (f' x) = f (eA x)) (hg : ∀ y, eC (g' y) = g (eB y)) :
    Function.Exact f g → Function.Exact f' g' := by
  intro h y
  constructor
  · intro hy
    have hy' : g (eB y) = 0 := by rw [← hg y, hy, map_zero]
    obtain ⟨a, ha⟩ := (h (eB y)).mp hy'
    refine ⟨eA.symm a, ?_⟩
    have hh : eB (f' (eA.symm a)) = f a := by rw [hf, eA.apply_symm_apply]
    exact eB.injective (by rw [hh, ha])
  · rintro ⟨a', rfl⟩
    apply eC.injective
    rw [map_zero, hg, hf]
    exact (h _).mpr ⟨eA a', rfl⟩

/-- `H_n(C_*(X;ℤ) ⊗ ℤ) ≃+ H_n(X;ℤ)`. -/
def eOne (X : Type) [TopologicalSpace X] (n : ℕ) :
    ↥((Work.SSS.expTens (Work.Pi6.EMZ.chZ X) zZ).homology n) ≃+ ↥(Work.Pi6.HR ℤ X n) :=
  (Iso.toLinearEquiv (Work.Pi6.EMZ.expTensUnitHomologyIso X n)).toAddEquiv

/-- `H_n(C_*(X;ℤ) ⊗ ℤ/p) ≃+ H_n(X;ℤ/p)`. -/
def eCAdd (p : ℕ) (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ) :
    ↥((Work.SSS.expTens (Work.Pi6.EMZ.chZ X) (Mp p)).homology n) ≃+
      ↥((Fp p).obj (Work.Pi6.HR (ZMod p) X n)) :=
  (Iso.toLinearEquiv (eCIso' p hp X n)).toAddEquiv

/-- Evaluation of the reduction. -/
theorem redHom_apply (p : ℕ) (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ)
    (x : Work.Pi6.HR ℤ X n) :
    redHom p hp X n x =
      eCAdd p hp X n
        ((HomologicalComplex.homologyMap
          (Work.SSS.expTensHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.redP p)) n).hom
          ((eOne X n).symm x)) := rfl

/-- Evaluation of the connecting map. -/
theorem delHom_apply (p : ℕ) (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ)
    (y : Work.Pi6.HR (ZMod p) X (n + 1)) :
    delHom p hp X n y =
      (eOne X n) (delta p hp X n ((eCAdd p hp X (n + 1)).symm y)) := rfl

/-- Exactness at `H_n(X;ℤ)`: `p · H_n(X;ℤ) = ker red`. -/
theorem redHom_exact (p : ℕ) (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ) :
    Function.Exact (fun x : Work.Pi6.HR ℤ X n => (p : ℤ) • x) ⇑(redHom p hp X n) := by
  have h2 := (bSES_shortExact p hp X).homology_exact₂ n |>.moduleCat_range_eq_ker
  have hE : Function.Exact ⇑(HomologicalComplex.homologyMap (bSES p X).f n).hom
      ⇑(HomologicalComplex.homologyMap (bSES p X).g n).hom :=
    LinearMap.exact_iff.mpr h2.symm
  refine Function.Exact.of_comp_addEquiv (eOne X n).symm (eOne X n).symm
    (eCAdd p hp X n).symm ?_ ?_ hE
  · intro x
    show (eOne X n).symm ((p : ℤ) • x) =
      (HomologicalComplex.homologyMap (bSES p X).f n).hom ((eOne X n).symm x)
    rw [map_zsmul]
    exact (homologyMap_expTensHom_mulP p (Work.Pi6.EMZ.chZ X) n _).symm
  · intro y
    show (eCAdd p hp X n).symm (redHom p hp X n y) =
      (HomologicalComplex.homologyMap (bSES p X).g n).hom ((eOne X n).symm y)
    rw [redHom_apply, AddEquiv.symm_apply_apply]

/-- Exactness at `H_{n+1}(X;ℤ/p)`: `im red = ker del`. -/
theorem redHom_delHom_exact (p : ℕ) (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ) :
    Function.Exact ⇑(redHom p hp X (n + 1)) ⇑(delHom p hp X n) := by
  have h3 := (bSES_shortExact p hp X).homology_exact₃ (n + 1) n
    (by rw [ComplexShape.down_Rel]) |>.moduleCat_range_eq_ker
  have hE : Function.Exact ⇑(HomologicalComplex.homologyMap (bSES p X).g (n + 1)).hom
      ⇑((bSES_shortExact p hp X).δ (n + 1) n (by rw [ComplexShape.down_Rel])).hom :=
    LinearMap.exact_iff.mpr h3.symm
  refine Function.Exact.of_comp_addEquiv (eOne X (n + 1)).symm
    (eCAdd p hp X (n + 1)).symm (eOne X n).symm ?_ ?_ hE
  · intro x
    show (eCAdd p hp X (n + 1)).symm (redHom p hp X (n + 1) x) =
      (HomologicalComplex.homologyMap (bSES p X).g (n + 1)).hom ((eOne X (n + 1)).symm x)
    rw [redHom_apply, AddEquiv.symm_apply_apply]
  · intro y
    show (eOne X n).symm (delHom p hp X n y) =
      delta p hp X n ((eCAdd p hp X (n + 1)).symm y)
    rw [delHom_apply, AddEquiv.symm_apply_apply]

/-- Exactness at `H_n(X;ℤ)`: `im del = ker (·p)`. -/
theorem delHom_exact (p : ℕ) (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ) :
    Function.Exact ⇑(delHom p hp X n) (fun x : Work.Pi6.HR ℤ X n => (p : ℤ) • x) := by
  have h1 := (bSES_shortExact p hp X).homology_exact₁ (n + 1) n
    (by rw [ComplexShape.down_Rel]) |>.moduleCat_range_eq_ker
  have hE : Function.Exact
      ⇑((bSES_shortExact p hp X).δ (n + 1) n (by rw [ComplexShape.down_Rel])).hom
      ⇑(HomologicalComplex.homologyMap (bSES p X).f n).hom :=
    LinearMap.exact_iff.mpr h1.symm
  refine Function.Exact.of_comp_addEquiv (eCAdd p hp X (n + 1)).symm
    (eOne X n).symm (eOne X n).symm ?_ ?_ hE
  · intro y
    show (eOne X n).symm (delHom p hp X n y) =
      delta p hp X n ((eCAdd p hp X (n + 1)).symm y)
    rw [delHom_apply, AddEquiv.symm_apply_apply]
  · intro y
    show (eOne X n).symm ((p : ℤ) • y) =
      (HomologicalComplex.homologyMap (bSES p X).f n).hom ((eOne X n).symm y)
    rw [map_zsmul]
    exact (homologyMap_expTensHom_mulP p (Work.Pi6.EMZ.chZ X) n _).symm

end

end Work.Pi6.BOCK
