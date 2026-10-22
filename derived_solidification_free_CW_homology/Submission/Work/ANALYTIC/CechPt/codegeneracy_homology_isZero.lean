import Mathlib

/-!
# Vanishing of the homology of a simplicial object with a codegeneracy

Let `S` be a simplicial object in `ModuleCat ℤ` and `u n : S n ⟶ S (n+1)` a family of
morphisms that behaves like an *extra degeneracy* (`σ (-1)`), in the sense that

* `u n ≫ S.δ 0 = 𝟙 (S n)` (`h₀`), and
* `u (n+1) ≫ S.δ i.succ = S.δ i ≫ u n` (`h₁`).

Then the alternating face map complex `C = AlternatingFaceMapComplex.obj S` has vanishing
homology in all positive degrees.  The reason is that `u` is a *contracting homotopy above
degree `0`*: writing `objD n` for the differential `C (n+1) ⟶ C n` one checks

`u (n+1) ≫ objD (n+1) + objD n ≫ u n = 𝟙 (C (n+1))`   (`n ≥ 0`),

while in degree `0` one gets `u 0 ≫ objD 0 = 𝟙 - p` with `p = u 0 ≫ S.δ 1`; the defect `p`
is exactly the composite `ε ≫ ι` of the canonical chain maps `C ⟶ single₀ (C 0)` and
`single₀ (C 0) ⟶ C` (the former exists because `objD 0 ≫ p = 0`).  The homotopy
`Homotopy (ε ≫ ι) (𝟙 C)` with components `-(u i)` therefore shows that `𝟙` and `ε ≫ ι`
induce the same map on homology; since `ε ≫ ι` factors through the complex `single₀ (C 0)`,
which is acyclic in positive degrees, the identity map on `H (k+1)` is zero.

This is the general form of the statement that the (presheaf-level) Čech complex of a cover
is acyclic in positive degrees; see `Submission/Work/ANALYTIC/CechPt/Contraction.lean` for
the geometric input (`h₀`, `h₁` for the Čech nerve of a map of light condensed sets).
-/

namespace Work.ANALYTIC.CechPt

open CategoryTheory Limits AlgebraicTopology CategoryTheory.SimplicialObject
open scoped Simplicial

set_option maxHeartbeats 1000000

/-- The codegeneracy relation in degrees `≥ 1`: `u` is a contracting homotopy of the
alternating face map complex away from degree `0`. -/
theorem codegeneracy_contraction (S : SimplicialObject (ModuleCat ℤ))
    (u : ∀ n : ℕ, S.obj (Opposite.op ⦋n⦌) ⟶ S.obj (Opposite.op ⦋n + 1⦌))
    (h₀ : ∀ n : ℕ, u n ≫ S.δ (0 : Fin (n + 2)) = 𝟙 (S.obj (Opposite.op ⦋n⦌)))
    (h₁ : ∀ (n : ℕ) (i : Fin (n + 2)), u (n + 1) ≫ S.δ i.succ = S.δ i ≫ u n) (m : ℕ) :
    u (m+1) ≫ AlgebraicTopology.AlternatingFaceMapComplex.objD S (m+1)
      + AlgebraicTopology.AlternatingFaceMapComplex.objD S m ≫ u m
      = 𝟙 (S.obj (Opposite.op ⦋m+1⦌)) := by
  have h1 : u (m+1) ≫ AlgebraicTopology.AlternatingFaceMapComplex.objD S (m+1)
      = ∑ i : Fin (m+3), ((-1 : ℤ) ^ (i : ℕ)) • (u (m+1) ≫ S.δ i) := by
    simp only [AlgebraicTopology.AlternatingFaceMapComplex.objD, Preadditive.comp_sum,
      Preadditive.comp_zsmul]
  have h4 : (∑ i : Fin (m+2), ((-1 : ℤ) ^ (i : ℕ)) • (S.δ i ≫ u m))
      = AlgebraicTopology.AlternatingFaceMapComplex.objD S m ≫ u m := by
    simp only [AlgebraicTopology.AlternatingFaceMapComplex.objD, Preadditive.sum_comp,
      Preadditive.zsmul_comp]
  have hsign : ∀ (i : Fin (m+2)), ((-1 : ℤ) ^ ((i.succ : Fin (m+3)) : ℕ))
      = -((-1 : ℤ) ^ (i : ℕ)) := by
    intro i
    rw [Fin.val_succ, pow_succ, mul_neg_one]
  have h2 : (∑ i : Fin (m+3), ((-1 : ℤ) ^ (i : ℕ)) • (u (m+1) ≫ S.δ i))
      = 𝟙 (S.obj (Opposite.op ⦋m+1⦌))
        + ∑ i : Fin (m+2), ((-1 : ℤ) ^ ((i.succ : Fin (m+3)) : ℕ)) • (S.δ i ≫ u m) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_zsmul]
    rw [h₀ (m+1)]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [h₁ m i])
  have h3 : (∑ i : Fin (m+2), ((-1 : ℤ) ^ ((i.succ : Fin (m+3)) : ℕ)) • (S.δ i ≫ u m))
      = -∑ i : Fin (m+2), ((-1 : ℤ) ^ (i : ℕ)) • (S.δ i ≫ u m) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hsign i, neg_zsmul]
  have h2' : (∑ i : Fin (m+3), ((-1 : ℤ) ^ (i : ℕ)) • (u (m+1) ≫ S.δ i))
      = 𝟙 (S.obj (Opposite.op ⦋m+1⦌))
        - AlgebraicTopology.AlternatingFaceMapComplex.objD S m ≫ u m := by
    rw [h2, h3, ← sub_eq_add_neg, h4]
  rw [h1.trans h2', sub_add_cancel]

/-- The codegeneracy relation in degree `0`. -/
theorem codegeneracy_contraction_zero (S : SimplicialObject (ModuleCat ℤ))
    (u : ∀ n : ℕ, S.obj (Opposite.op ⦋n⦌) ⟶ S.obj (Opposite.op ⦋n + 1⦌))
    (h₀ : ∀ n : ℕ, u n ≫ S.δ (0 : Fin (n + 2)) = 𝟙 (S.obj (Opposite.op ⦋n⦌))) :
    u 0 ≫ AlgebraicTopology.AlternatingFaceMapComplex.objD S 0
      = 𝟙 (S.obj (Opposite.op ⦋0⦌)) - u 0 ≫ S.δ (1 : Fin 2) := by
  have hd0 : AlgebraicTopology.AlternatingFaceMapComplex.objD S 0
      = S.δ (0 : Fin 2) - S.δ (1 : Fin 2) := by
    rw [AlgebraicTopology.AlternatingFaceMapComplex.objD]
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one', pow_zero, one_zsmul]
    abel
  rw [hd0, Preadditive.comp_sub, h₀ 0]

/-- The defect `p = u 0 ≫ S.δ 1` in degree `0` is killed by `objD 0`, so that `p` defines a
chain map `C ⟶ single₀ (C 0)`. -/
theorem codegeneracy_d_zero (S : SimplicialObject (ModuleCat ℤ))
    (u : ∀ n : ℕ, S.obj (Opposite.op ⦋n⦌) ⟶ S.obj (Opposite.op ⦋n + 1⦌))
    (h₁ : ∀ (n : ℕ) (i : Fin (n + 2)), u (n + 1) ≫ S.δ i.succ = S.δ i ≫ u n) :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj S).d 1 0 ≫ (u 0 ≫ S.δ (1 : Fin 2)) = 0 := by
  show AlgebraicTopology.AlternatingFaceMapComplex.objD S 0 ≫ (u 0 ≫ S.δ (1 : Fin 2)) = 0
  have hd0 : AlgebraicTopology.AlternatingFaceMapComplex.objD S 0
      = S.δ (0 : Fin 2) - S.δ (1 : Fin 2) := by
    rw [AlgebraicTopology.AlternatingFaceMapComplex.objD]
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one', pow_zero, one_zsmul]
    abel
  rw [hd0, Preadditive.sub_comp]
  simp only [← Category.assoc]
  rw [← h₁ 0 0, ← h₁ 0 1]
  simp only [Category.assoc]
  rw [← SimplicialObject.δ_comp_δ_self S (n := 0) (i := (1 : Fin 2))]
  exact sub_eq_zero.mpr rfl

theorem codegeneracy_homology_isZero (S : SimplicialObject (ModuleCat ℤ))
    (u : ∀ n : ℕ, S.obj (Opposite.op ⦋n⦌) ⟶ S.obj (Opposite.op ⦋n + 1⦌))
    (h₀ : ∀ n : ℕ, u n ≫ S.δ (0 : Fin (n + 2)) = 𝟙 (S.obj (Opposite.op ⦋n⦌)))
    (h₁ : ∀ (n : ℕ) (i : Fin (n + 2)), u (n + 1) ≫ S.δ i.succ = S.δ i ≫ u n)
    (k : ℕ) : IsZero ((AlgebraicTopology.AlternatingFaceMapComplex.obj S).homology (k + 1)) := by
  let C : ChainComplex (ModuleCat ℤ) ℕ := AlgebraicTopology.AlternatingFaceMapComplex.obj S
  have hid := codegeneracy_contraction S u h₀ h₁
  have hz := codegeneracy_contraction_zero S u h₀
  have hp : C.d 1 0 ≫ (u 0 ≫ S.δ (1 : Fin 2)) = 0 := codegeneracy_d_zero S u h₁
  have hCd : ∀ n : ℕ, C.d (n+1) n = AlgebraicTopology.AlternatingFaceMapComplex.objD S n :=
    fun n => AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq S n
  have hXn : ∀ n : ℕ, 𝟙 (C.X n) = 𝟙 (S.obj (Opposite.op ⦋n⦌)) := fun n => rfl
  let ε : C ⟶ (ChainComplex.single₀ (ModuleCat ℤ)).obj (C.X 0) :=
    (ChainComplex.toSingle₀Equiv C (C.X 0)).symm ⟨u 0 ≫ S.δ (1 : Fin 2), hp⟩
  let ι : (ChainComplex.single₀ (ModuleCat ℤ)).obj (C.X 0) ⟶ C :=
    (ChainComplex.fromSingle₀Equiv C (C.X 0)).symm (𝟙 (C.X 0))
  have hq0 : (ε ≫ ι).f 0 = u 0 ≫ S.δ (1 : Fin 2) := by simp [ε, ι]
  have hqn : ∀ n : ℕ, (ε ≫ ι).f (n+1) = 0 := by intro n; simp [ι]
  have hHom : Homotopy (ε ≫ ι) (𝟙 C) :=
    { hom i := Pi.single (i+1) (-(u i))
      zero i j hij := Pi.single_eq_of_ne (Ne.symm hij) _
      comm i := by
        cases i with
        | zero =>
          rw [hq0, Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex,
            Pi.single_eq_same, hCd 0, HomologicalComplex.id_f, hXn 0, Preadditive.neg_comp, hz]
          abel
        | succ n =>
          rw [hqn n, Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex,
            Pi.single_eq_same, Pi.single_eq_same, hCd n, hCd (n+1), HomologicalComplex.id_f,
            hXn (n+1), Preadditive.comp_neg, Preadditive.neg_comp, ← hid n]
          abel }
  have hD : IsZero (((ChainComplex.single₀ (ModuleCat ℤ)).obj (C.X 0)).homology (k+1)) :=
    HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) 0 (C.X 0) (k+1) (by simp)
  have hzero : HomologicalComplex.homologyMap (ε ≫ ι) (k+1) = 0 := by
    rw [HomologicalComplex.homologyMap_comp]
    rw [IsZero.eq_zero_of_tgt hD (HomologicalComplex.homologyMap ε (k+1)), zero_comp]
  have h3 : (𝟙 (C.homology (k+1))) = 0 := by
    rw [← HomologicalComplex.homologyMap_id C (k+1), ← hHom.homologyMap_eq (k+1)]
    exact hzero
  exact (IsZero.iff_id_eq_zero (C.homology (k+1))).mpr h3

end Work.ANALYTIC.CechPt
