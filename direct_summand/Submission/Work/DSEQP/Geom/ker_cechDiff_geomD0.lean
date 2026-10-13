import Mathlib
import Submission.Work.DSEQP.gf_defs

namespace Work.DSEQP.Geom

universe a

open CategoryTheory

/-! ## Two elementary helpers

`Work.DSCOH.degZero` is the degree-zero part of a chart localisation, and
`Work.DSCOH.degPartRestrict` restricts a map of chart localisations to these degree-zero parts;
the first projection of the result is the original map applied to the first projection
(`degPartRestrict_coe`).  `kerEquivOfComp` is the standard fact that a linear equivalence of the
sources and targets of two linear maps that commutes with them induces an equivalence of the
kernels. -/

/-- A finset whose cardinality is a successor is nonempty. -/
private lemma nonempty_of_card_succ {N : ℕ} {S : Finset (Fin (N + 1))} {k : ℕ}
    (h : S.card = k + 1) : S.Nonempty := Finset.card_pos.mp (by omega)

/-- The underlying element of `degPartRestrict ℳ ψ h x` is `ψ` applied to the underlying element
of `x` (the compatibility proof is a proposition, hence irrelevant). -/
private lemma degPartRestrict_coe {A : Type*} [CommRing A] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module A M] [Module (Work.DSCOH.Poly A n) M]
    [IsScalarTower A (Work.DSCOH.Poly A n) M]
    {ℳ : ℕ → Submodule A M} {S T : Finset (Fin n)}
    (ψ : Work.DSCOH.locAt (A := A) (M := M) S →ₗ[Work.DSCOH.Poly A n]
      Work.DSCOH.locAt (A := A) (M := M) T)
    (h : ∀ x ∈ Work.DSCOH.degZero (A := A) ℳ S, ψ x ∈ Work.DSCOH.degZero (A := A) ℳ T)
    (x : ↥(Work.DSCOH.degZero (A := A) ℳ S)) :
    Work.DSCOH.degPartRestrict (A := A) (M := M) ℳ ψ h x = ⟨ψ x.1, h x.1 x.2⟩ := rfl

/-- Linear equivalences of the sources and the targets of two linear maps that commute with the
maps induce a linear equivalence of their kernels. -/
private noncomputable def kerEquivOfComp {R : Type a} [Semiring R] {M M' N N' : Type a}
    [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N] [AddCommMonoid N']
    [Module R M] [Module R M'] [Module R N] [Module R N']
    (e₀ : M ≃ₗ[R] M') (e₁ : N ≃ₗ[R] N') (d : M →ₗ[R] N) (g : M' →ₗ[R] N')
    (h : ∀ x, g (e₀ x) = e₁ (d x)) : LinearMap.ker d ≃ₗ[R] LinearMap.ker g where
  toFun x := ⟨e₀ x.1, LinearMap.mem_ker.mpr (by rw [h, LinearMap.mem_ker.mp x.2, map_zero])⟩
  invFun y := ⟨e₀.symm y.1, LinearMap.mem_ker.mpr (e₁.map_eq_zero_iff.mp (by
    rw [← h (e₀.symm y.1), e₀.apply_symm_apply, LinearMap.mem_ker.mp y.2]))⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
/-- **The degree-`0` comparison of the algebraic and the geometric chart Čech complexes.**
Given a termwise identification `e` of the degree-zero chart localisations of `M = R ⧸ J` with the
sections of `𝒪_X` over the charts, compatible with the restriction maps (`hnat`), the `0`-cocycles
of the algebraic chart Čech complex `Work.DSCOH.cechDiff (Mg i) 0` are the `0`-cocycles of the
geometric alternating complex `Work.DSEQP.geomD0 i f`: both complexes are indexed by the
`(q+1)`-element subsets of `Fin (N+1)` and their differentials have the same sign convention and the
same component formula, so `e` identifies them (in degrees `0` and `1`). -/
theorem ker_cechDiff_geomD0 (A : Type a) [CommRing A] {N : ℕ} {X : AlgebraicGeometry.Scheme.{a}}
    (i : X ⟶ DSMap.PSpace A N) (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (e : ∀ (S : Finset (Fin (N + 1))) (hS : S.Nonempty),
        (↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
          (Work.DSEQP.Mg i) S) ≃ₗ[A]
          ↥((DSMap.cechPresheaf A X f).obj (Opposite.op (Work.DSEQP.Ucmp i S)))))
    (hnat : ∀ (S T : Finset (Fin (N + 1))) (hST : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty)
        (x : ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
          (Work.DSEQP.Mg i) S)),
        e T hT ⟨Work.DSCOH.resAt (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i) hST x.1,
            Work.DSCOH.resAt_degZero (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
              (ℳ := Work.DSEQP.Mg i) hST x.1 x.2⟩
          = (DSMap.cechPresheaf A X f).map (homOfLE (Work.DSEQP.Ucmp_anti i hST)).op (e S hS x)) :
    Nonempty (↥(LinearMap.ker (Work.DSCOH.cechDiff (A := A) (n := N + 1)
        (M := Work.DSEQP.Mmod i) (Work.DSEQP.Mg i) 0))
      ≃ₗ[A] ↥(LinearMap.ker (Work.DSEQP.geomD0 i f))) := by
  classical
  -- The termwise identification of the degree-`0` and degree-`1` terms of the two complexes.
  let Φ0 : Work.DSCOH.CechTerm (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
      (Work.DSEQP.Mg i) 0 ≃ₗ[A] Work.DSEQP.GC0 (A := A) (N := N) i f :=
    LinearEquiv.piCongrRight (fun S : {S : Finset (Fin (N + 1)) // S.card = 0 + 1} =>
      e S.1 (nonempty_of_card_succ (S := S.1) (k := 0) S.2))
  let Φ1 : Work.DSCOH.CechTerm (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
      (Work.DSEQP.Mg i) 1 ≃ₗ[A] Work.DSEQP.GC1 (A := A) (N := N) i f :=
    LinearEquiv.piCongrRight (fun S : {S : Finset (Fin (N + 1)) // S.card = 0 + 1 + 1} =>
      e S.1 (nonempty_of_card_succ (S := S.1) (k := 1) S.2))
  -- Their components.
  have hΦ0 : ∀ (x : Work.DSCOH.CechTerm (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
        (Work.DSEQP.Mg i) 0) (S : {S : Finset (Fin (N + 1)) // S.card = 0 + 1}),
      Φ0 x S = e S.1 (nonempty_of_card_succ (S := S.1) (k := 0) S.2) (x S) := by
    intro x S
    rw [show Φ0 = LinearEquiv.piCongrRight
        (fun S : {S : Finset (Fin (N + 1)) // S.card = 0 + 1} =>
          e S.1 (nonempty_of_card_succ (S := S.1) (k := 0) S.2)) from rfl,
      LinearEquiv.piCongrRight_apply]
  have hΦ1 : ∀ (x : Work.DSCOH.CechTerm (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
        (Work.DSEQP.Mg i) 1) (S : {S : Finset (Fin (N + 1)) // S.card = 0 + 1 + 1}),
      Φ1 x S = e S.1 (nonempty_of_card_succ (S := S.1) (k := 1) S.2) (x S) := by
    intro x S
    rw [show Φ1 = LinearEquiv.piCongrRight
        (fun S : {S : Finset (Fin (N + 1)) // S.card = 0 + 1 + 1} =>
          e S.1 (nonempty_of_card_succ (S := S.1) (k := 1) S.2)) from rfl,
      LinearEquiv.piCongrRight_apply]
  -- The two differentials have the same components, so `Φ` is a map of complexes.
  have hcomm : ∀ x : Work.DSCOH.CechTerm (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
        (Work.DSEQP.Mg i) 0,
      Work.DSEQP.geomD0 i f (Φ0 x) = Φ1 (Work.DSCOH.cechDiff (A := A) (n := N + 1)
        (M := Work.DSEQP.Mmod i) (Work.DSEQP.Mg i) 0 x) := by
    intro x
    funext T
    rw [Work.DSEQP.geomD0_apply, Work.DSEQP.geomD0Comp]
    rw [hΦ1 (Work.DSCOH.cechDiff (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
      (Work.DSEQP.Mg i) 0 x) T]
    rw [Work.DSCOH.cechDiff, LinearMap.pi_apply, Work.DSCOH.cechDiffComp]
    conv_lhs => rw [LinearMap.sum_apply]
    conv_rhs => rw [LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    conv_lhs => rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    conv_rhs => rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_zsmul]
    rw [hΦ0 x ⟨T.1.erase i'.1, by rw [Finset.card_erase_of_mem i'.2]; omega⟩]
    rw [degPartRestrict_coe]
    rw [← hnat (T.1.erase i'.1) T.1 (Finset.erase_subset i'.1 T.1)
      (nonempty_of_card_succ (S := T.1.erase i'.1) (k := 0)
        (by rw [Finset.card_erase_of_mem i'.2]; omega))
      (nonempty_of_card_succ (S := T.1) (k := 1) T.2)
      (x ⟨T.1.erase i'.1, by rw [Finset.card_erase_of_mem i'.2]; omega⟩)]
  exact ⟨kerEquivOfComp Φ0 Φ1
    (Work.DSCOH.cechDiff (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
      (Work.DSEQP.Mg i) 0) (Work.DSEQP.geomD0 i f) hcomm⟩

end Work.DSEQP.Geom
