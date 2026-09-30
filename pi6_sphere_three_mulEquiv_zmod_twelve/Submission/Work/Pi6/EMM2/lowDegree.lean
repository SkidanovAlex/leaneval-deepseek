import Mathlib
import Submission.Work.Pi6.EMM2.Defs
import Submission.Work.Pi6.EMM2.coeffVanishing
import Submission.Work.Pi6.EMM2.hZeroFree
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Cohomology.singularCohomology_zero
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Pi6.SQASM.connHomology
import Submission.Work.SSS.singularCoeffFG
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Area EMM2: the low-degree cohomology of a `K(A,m)` range model

`Work.Serre.IsEMSpaceUpTo A m _ M X x` says that `X` is a model of `K(A,m)` through degree `M`:
`π_m(X,x) ≃* A` and `π_i(X,x) = 0` for `m ≠ i` with `i < m` or `i ≤ M`.  The lemma below records the
three elementary consequences used by the forcing arguments of area EMM2:

* `X` is simply connected (for `m ≥ 2`);
* `H⁰(X;𝕜) = 𝕜` (the space is connected);
* `H^i(X;𝕜) = 0` for `1 ≤ i < m`.

The vanishing statement is the coefficient-change input which is not available in Mathlib for an
arbitrary field: `X` being `(m-1)`-connected, the *integral* homology `H_i(X;ℤ)` vanishes for
`0 < i < m` (`Work.Pi6.SQASM.connHomology`), and a coefficient change
(`Work.Pi6.EMM2.coeffVanishing`, the universal coefficient theorem in vanishing form, together with
`Work.SSS.chainCoeffExpIso`) gives the vanishing of `H_i(X;𝕜)`, which `Work.StemsB.fieldDualUCT`
turns into the vanishing of the cohomology `H^i(X;𝕜) ≅ Hom_𝕜(H_i(X;𝕜), 𝕜)`.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Pi6.EMM2

noncomputable section

namespace LowDegree

/-- An isomorphism of abelian groups transfers `Subsingleton`. -/
theorem subsingleton_of_iso_ab {A B : AddCommGrpCat} (e : A ≅ B) (h : Subsingleton ↥A) :
    Subsingleton ↥B := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2 x
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2 y
  rw [h.elim a b]

/-- **The cross-ring comparison.**  If the homology of the singular chain complex of `X` with
coefficients in the `ℤ`-module `𝕜` vanishes in degree `j`, then so does the `𝕜`-homology
`H_j(X;𝕜)`: the two complexes are the images of one another under the forgetful functors to abelian
groups, and both are the singular chain complex of `X` with coefficients in the abelian group `𝕜`
(`Work.StemsB.SphRat.chainComplexBaseChange`, `Work.StemsB.SphRat.homologyMapBaseChange`). -/
theorem subsingleton_HR_of_intCoeff {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X] (j : ℕ)
    (h : Subsingleton ↥(((TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (ModuleCat.of ℤ 𝕜)).homology j)) :
    Subsingleton ↥(Work.Pi6.HR 𝕜 X j) := by
  let F1 := forget₂ (ModuleCat ℤ) AddCommGrpCat
  let F2 := forget₂ (ModuleCat 𝕜) AddCommGrpCat
  let S : SSet := TopCat.toSSet.obj (TopCat.of X)
  let KZ : ChainComplex (ModuleCat ℤ) ℕ := S.chainComplex (ModuleCat.of ℤ 𝕜)
  let KK : ChainComplex (ModuleCat 𝕜) ℕ := S.chainComplex (ModuleCat.of 𝕜 𝕜)
  have t1 : Subsingleton
      ↥(((F1.mapHomologicalComplex (ComplexShape.down ℕ)).obj KZ).homology j) := by
    obtain ⟨e⟩ := Work.StemsB.SphRat.homologyMapBaseChange F1 KZ j
    exact subsingleton_of_iso_ab e.symm (show Subsingleton ↥(F1.obj (KZ.homology j)) from h)
  have eC : ((F1.mapHomologicalComplex (ComplexShape.down ℕ)).obj KZ) ≅
      ((F2.mapHomologicalComplex (ComplexShape.down ℕ)).obj KK) :=
    Work.StemsB.SphRat.chainComplexBaseChange F1 S (ModuleCat.of ℤ 𝕜) ≪≫
      (Work.StemsB.SphRat.chainComplexBaseChange F2 S (ModuleCat.of 𝕜 𝕜)).symm
  have t2 : Subsingleton
      ↥(((F2.mapHomologicalComplex (ComplexShape.down ℕ)).obj KK).homology j) :=
    subsingleton_of_iso_ab ((homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) j).mapIso eC) t1
  have t3 : Subsingleton ↥(F2.obj (KK.homology j)) := by
    obtain ⟨e⟩ := Work.StemsB.SphRat.homologyMapBaseChange F2 KK j
    exact subsingleton_of_iso_ab e t2
  show Subsingleton ↥(KK.homology j)
  exact t3

/-- Vanishing of the `𝕜`-cohomology in degree `j` from the vanishing of the `𝕜`-homology, by the
universal coefficient theorem over the field `𝕜`
(`Work.StemsB.fieldDualUCT`: `H^j(X;𝕜) ≅ Hom_𝕜(H_j(X;𝕜), 𝕜)`). -/
theorem isZero_Coh_of_subsingleton_HR {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X]
    (j : ℕ) (h : Subsingleton ↥(Work.Pi6.HR 𝕜 X j)) : IsZero (Work.Pi6.Coh 𝕜 X j) := by
  obtain ⟨e⟩ := Work.StemsB.fieldDualUCT 𝕜 (Work.Cohomology.singularChains 𝕜 (TopCat.of X)) j
  have hsub : Subsingleton (↥(Work.Pi6.HR 𝕜 X j) →ₗ[𝕜] 𝕜) :=
    ⟨fun f g => LinearMap.ext fun y => by rw [h.elim y 0, map_zero, map_zero]⟩
  have hz : IsZero (ModuleCat.of 𝕜 (↥(Work.Pi6.HR 𝕜 X j) →ₗ[𝕜] 𝕜)) :=
    ModuleCat.isZero_of_subsingleton _
  change IsZero ((Work.Cohomology.dualComplex 𝕜
    (Work.Cohomology.singularChains 𝕜 (TopCat.of X))).homology j)
  exact IsZero.of_iso hz e

/-- The `π₀` and `π₁` of a `K(A,m)` range model with `m ≥ 2` are trivial. -/
theorem simplyConn_of_isEMSpaceUpTo {A : Type} [AddCommGroup A] {m M : ℕ} (hm : 2 ≤ m)
    {X : Type} [TopologicalSpace X] (x : X)
    (hX : Work.Serre.IsEMSpaceUpTo A m (by omega) M X x) : Work.PiS.SimplyConn X x :=
  ⟨hX.2 0 (by omega) (Or.inl (by omega)), hX.2 1 (by omega) (Or.inl (by omega))⟩

/-- `H⁰(X;𝕜) = 𝕜` for a space with trivial `π₀` (`Work.Cohomology.singularCohomology_zero`). -/
theorem finrank_Coh_zero {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X] (x : X)
    (hX : Subsingleton (HomotopyGroup (Fin 0) X x)) :
    Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 X 0) = 1 := by
  haveI : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x hX
  obtain ⟨e⟩ := Work.Cohomology.singularCohomology_zero 𝕜 (TopCat.of X)
  have hfr : Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 X 0) = Module.finrank 𝕜 (ModuleCat.of 𝕜 𝕜) :=
    LinearEquiv.finrank_eq
      (LinearEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom))
  rw [hfr]
  simp

end LowDegree

/-- **Low-degree cohomology of a `K(A,m)` range model.**  If `X` is a model of `K(A,m)` through
degree `M ≥ m` (`m ≥ 2`), then `X` is simply connected, `H⁰(X;𝕜)` is one-dimensional, and
`H^i(X;𝕜) = 0` for `1 ≤ i < m`. -/
theorem lowDegree (𝕜 : Type) [Field 𝕜] {A : Type} [AddCommGroup A] (hA : Module.Finite ℤ A)
    {m M : ℕ} (hm : 2 ≤ m) (hM : m ≤ M) {X : Type} [TopologicalSpace X] (x : X)
    (hX : Work.Serre.IsEMSpaceUpTo A m (by omega) M X x) :
    Work.PiS.SimplyConn X x ∧
      Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 X 0) = 1 ∧
      (∀ i : ℕ, 1 ≤ i → i < m → CategoryTheory.Limits.IsZero (Work.Pi6.Coh 𝕜 X i)) := by
  refine ⟨LowDegree.simplyConn_of_isEMSpaceUpTo hm x hX,
    LowDegree.finrank_Coh_zero x ?_, ?_⟩
  · exact hX.2 0 (by omega) (Or.inl (by omega))
  · intro i hi him
    apply LowDegree.isZero_Coh_of_subsingleton_HR
    apply LowDegree.subsingleton_HR_of_intCoeff
    let S : SSet := TopCat.toSSet.obj (TopCat.of X)
    let K : ChainComplex (ModuleCat ℤ) ℕ := S.chainComplex (ModuleCat.of ℤ ℤ)
    -- `X` is `(m-1)`-connected, so its integral homology vanishes below degree `m`
    have hconn : ∀ j : ℕ, j ≤ m - 1 → Subsingleton (HomotopyGroup (Fin j) X x) :=
      fun j hj => hX.2 j (by omega) (Or.inl (by omega))
    have hvan : ∀ j : ℕ, 1 ≤ j → j ≤ i → IsZero (K.homology j) := by
      intro j hj hji
      exact Work.Pi6.SQASM.connHomology x (m - 1) j hconn (by omega) (by omega)
    have hZ := coeffVanishing K i hi (fun n => Work.SSS.sChains_free S n) ?_ hvan
      (ModuleCat.of ℤ 𝕜)
    · -- transfer the vanishing back along the coefficient extension `C_*(X;𝕜) ≅ C_*(X;ℤ) ⊗ 𝕜`
      have e : S.chainComplex (ModuleCat.of ℤ 𝕜) ≅
          Work.SSS.expTens K (ModuleCat.of ℤ 𝕜) :=
        Work.SSS.chainCoeffExpIso S (ModuleCat.of ℤ 𝕜)
      exact ModuleCat.subsingleton_of_isZero (IsZero.of_iso hZ ((homologyFunctor (ModuleCat ℤ)
        (ComplexShape.down ℕ) i).mapIso e))
    · -- `H_0(X;ℤ) = ℤ` is free
      exact hZeroFree x (hX.2 0 (by omega) (Or.inl (by omega)))

end

end Work.Pi6.EMM2
