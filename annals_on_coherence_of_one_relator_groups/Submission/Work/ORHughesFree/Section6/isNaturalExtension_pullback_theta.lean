import Mathlib
import Submission.Work.ORHughesFree.Section6.HughesFreeEnv
import Submission.Work.Section6.StepA
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.naturalExtension_exists
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.Epic
import Submission.Work.RankAPI.rk_eq_of_isUnit

namespace Work.ORHughesFree.Section6

theorem isNaturalExtension_pullback_theta {K : Type} [Field K] {G : Type} [Group G]
    {U : Type} [Ring U] [StarRing U] [IsStarRegular U]
    (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (hHfg : H.FG) (hHne : H ≠ ⊥)
    (N : Subgroup H) (hN : N.Normal) (t : H)
    (hstar : star ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) =
      (φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t⁻¹ (1 : K)))
    (rkU : Work.ORHughesFree.SylvesterRank U) (hfaith : rkU.IsFaithful)
    (hHF : Work.ORHughesFree.IsHughesFreeEnv φ)
    (hdecomp : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k)
    (htinf : ∀ k : ℤ, t ^ k ∈ N → k = 0)
    [tau : MulSemiringAction (Multiplicative ℤ) (Work.Section6.UNty φ H N)]
    (θ : SkewMonoidAlgebra (Work.Section6.UNty φ H N) (Multiplicative ℤ) →+* U)
    (hθ : ∀ (k : ℤ) (x : Work.Section6.UNty φ H N),
      θ (SkewMonoidAlgebra.single (Multiplicative.ofAdd k) x) =
        (x : U) * ((((Work.Section6.uUnit φ H t) ^ k : Uˣ)) : U)) :
    Work.ORHughesFree.IsNaturalExtension (Work.Section6.rkN φ H N rkU)
      (Work.ORHughesFree.SylvesterRank.pullback θ rkU) := by
  -- `θ` is the identity on constants: `single 1 x ↦ x`.
  have hθ0 : ∀ x : Work.Section6.UNty φ H N,
      θ (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x) = (x : U) := by
    intro x; simpa using hθ 0 x
  -- and `single (ofAdd 1) x ↦ x * φ(t)` on the generator.
  have hθ1 : ∀ x : Work.Section6.UNty φ H N,
      θ (SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) x) =
        (x : U) * (((Work.Section6.uUnit φ H t : Uˣ) : U)) := by
    intro x; simpa using hθ 1 x
  -- Clause 1 of the natural extension: `θ` is the inclusion on constants.
  have hmat_const : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (Work.Section6.UNty φ H N)),
      (Work.ORHughesFree.skewLaurentConst n m A).map θ =
        A.map (Subring.subtype (Work.Section6.UNsub φ H N)) := by
    intro n m A
    ext i j
    simp only [Matrix.map_apply, Work.ORHughesFree.skewLaurentConst]
    exact hθ0 (A i j)
  -- Clause 2 of the natural extension: `θ (I + A t) = 1 + A · φ(t)`, the matrix of `H3`.
  have hmat_onePlus : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (Work.Section6.UNty φ H N)),
      (Work.ORHughesFree.onePlusAt n A).map θ =
        1 + A.map (Subtype.val) * Matrix.scalar (Fin n)
          ((φ.comp (inducedMapRing (K := K) H)) (MonoidAlgebra.single t (1 : K))) := by
    intro n A
    ext i j
    rw [Matrix.map_apply, Matrix.add_apply, Matrix.scalar_apply, Matrix.mul_diagonal,
      Matrix.map_apply, Matrix.one_apply]
    rw [Work.ORHughesFree.onePlusAt, Matrix.add_apply, Matrix.map_apply, Matrix.one_apply]
    rw [map_add, hθ1]
    have hif : θ (if i = j then
          (1 : SkewMonoidAlgebra (Work.Section6.UNty φ H N) (Multiplicative ℤ)) else 0) =
        (if i = j then (1 : U) else 0) := by
      by_cases h : i = j <;> simp [h]
    rw [hif, ← Work.Section6.uUnit_val]
  refine ⟨?_, ?_⟩
  · intro n m A
    show rkU.rk n m ((Work.ORHughesFree.skewLaurentConst n m A).map θ) =
      rkU.rk n m (A.map (Subring.subtype (Work.Section6.UNsub φ H N)))
    rw [hmat_const n m A]
  · intro n A
    show rkU.rk n n ((Work.ORHughesFree.onePlusAt n A).map θ) = (n : ℝ)
    rw [hmat_onePlus n A]
    exact Work.RankAPI.rk_eq_of_isUnit rkU _
      (hHF H hHfg hHne N hN t hdecomp htinf n A)

end Work.ORHughesFree.Section6
