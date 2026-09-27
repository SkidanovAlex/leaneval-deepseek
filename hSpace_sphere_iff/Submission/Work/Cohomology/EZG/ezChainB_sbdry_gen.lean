/-
# The boundary of the Eilenberg–Zilber shuffle chain (general degrees)

`Work.Cohomology.EZG.ezChainB_sbdry_gen`: for `a : X_{P+1}`, `b : Y_{Q+1}`,
`∂ (ezChainB a b) = ezA P Q a b + (-1)^{P+1} • ezB P Q a b`.

The boundary is expanded as a sum over `Idx P Q = {A // A.card = P+1} × Fin ((P+1)+Q+2)`; the
index set is partitioned into the `a`-side, the `b`-side and the mixed indices.  The `a`-side
reindexes (via the bijection `aFwd`) onto `TargetA P Q` and contributes `ezA`; the `b`-side
reindexes onto `TargetB P Q` and contributes `(-1)^{P+1} • ezB`; the mixed indices are paired by
the sign-reversing involution swapping two adjacent letters and cancel.
-/
import Mathlib
import Submission.Work.Cohomology.EZG.EZShufSetup
import Submission.Work.Cohomology.EZG.a_roundtrips
import Submission.Work.Cohomology.EZG.b_roundtrips
import Submission.Work.Cohomology.EZG.aSide_Fsum
import Submission.Work.Cohomology.EZG.Fsum_eq_ezBsum
import Submission.Work.Cohomology.EZG.sumD_eq_zero

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology.EZG

noncomputable section

variable {X Y : SSet.{0}}

/-- Boundary of a single chain concentrated on one simplex with coefficient `1`. -/
lemma sbdry_single_one (S : SSet.{0}) (n : ℕ) (σ : S.obj (op ⦋n+1⦌)) :
    Submission.Cohomology.sbdry S ℚ n (Finsupp.single σ 1)
      = ∑ k : Fin (n+2), Finsupp.single (S.δ k σ) ((-1 : ℚ) ^ (k : ℕ)) := by
  rw [Submission.Cohomology.sbdry_single]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [zsmul_eq_mul, mul_one]
  push_cast
  ring

lemma ezChainB_eq_sum (P Q : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌)) :
    ezChainB (p := P+1) (q := Q+1) a b
      = ∑ A : {A : Finset (Fin ((P+1)+(Q+1))) // A.card = P+1},
          (sgnA A.1 : ℚ) • Finsupp.single (ezPair P Q a b A.1 A.2) 1 := rfl

/-- The expansion of the boundary of the shuffle chain as a sum over the index set
`{A // A.card = P+1} × Fin ((P+1)+Q+2)` of "shuffle together with face index". -/
lemma sbdry_ezChainB_raw (P Q : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌)) :
    Submission.Cohomology.sbdry (MonoidalCategoryStruct.tensorObj X Y) ℚ ((P+1)+Q)
      (ezChainB (p := P+1) (q := Q+1) a b)
    = ∑ x : Idx P Q,
        Finsupp.single ((MonoidalCategoryStruct.tensorObj X Y).δ x.2 (ezPair P Q a b x.1.1 x.1.2))
          ((sgnA x.1.1 : ℚ) * (-1 : ℚ) ^ (x.2 : ℕ)) := by
  rw [ezChainB_eq_sum P Q a b]
  rw [map_sum]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [map_smul, sbdry_single_one, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finsupp.smul_single, smul_eq_mul]

lemma sbdry_ezChainB_expand (P Q : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌)) :
    Submission.Cohomology.sbdry (MonoidalCategoryStruct.tensorObj X Y) ℚ ((P+1)+Q)
      (ezChainB (p := P+1) (q := Q+1) a b)
    = ∑ x : Idx P Q, Fsum P Q X Y a b x := by
  rw [sbdry_ezChainB_raw]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fsum]
  congr 1

/-! ### The reindexing equivalences -/

instance instFintypeIdxA (P Q : ℕ) : Fintype (IdxA P Q) := by
  classical exact Subtype.fintype _

instance instFintypeIdxB (P Q : ℕ) : Fintype (IdxB P Q) := by
  classical exact Subtype.fintype _

noncomputable def aEquiv (P Q : ℕ) : IdxA P Q ≃ TargetA P Q where
  toFun := aFwd P Q
  invFun := fun y => ⟨aInvIdx P Q y, (a_roundtrips P Q).1 y⟩
  left_inv := fun x => Subtype.ext ((a_roundtrips P Q).2.2 x.1 x.2)
  right_inv := fun y => (a_roundtrips P Q).2.1 y ((a_roundtrips P Q).1 y)

noncomputable def bEquiv (P Q : ℕ) : IdxB P Q ≃ TargetB P Q where
  toFun := bFwd P Q
  invFun := fun y => ⟨bInvIdx P Q y, (b_roundtrips P Q).1 y⟩
  left_inv := fun x => Subtype.ext ((b_roundtrips P Q).2.2 x.1 x.2)
  right_inv := fun y => (b_roundtrips P Q).2.1 y ((b_roundtrips P Q).1 y)

/-! ### The three pieces of the sum -/

lemma sumA_eq_ezA (P Q : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌)) :
    (∑ x ∈ sA P Q, Fsum P Q X Y a b x) = ezA P Q a b := by
  rw [Finset.sum_subtype (p := fun x : Idx P Q => IsA ((P+1)+Q) x.1.1 x.2) (sA P Q)
        (fun x => by simp [sA]) (Fsum P Q X Y a b)]
  rw [Fintype.sum_equiv (aEquiv P Q) (fun x : IdxA P Q => Fsum P Q X Y a b x.1)
        (fun y : TargetA P Q => ezAsum P Q X Y a b y)
        (fun x => aSide_Fsum P Q X Y a b x)]
  rw [← ezA_eq_sum P Q a b]

lemma sumB_eq_ezB (P Q : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌)) :
    (∑ x ∈ sB P Q, Fsum P Q X Y a b x) = (-1 : ℚ) ^ (P+1) • ezB P Q a b := by
  rw [Finset.sum_subtype (p := fun x : Idx P Q => IsB ((P+1)+Q) x.1.1 x.2) (sB P Q)
        (fun x => by simp [sB]) (Fsum P Q X Y a b)]
  rw [Fintype.sum_equiv (bEquiv P Q) (fun x : IdxB P Q => Fsum P Q X Y a b x.1)
        (fun y : TargetB P Q => (-1 : ℚ) ^ (P+1) • ezBsum P Q X Y a b y)
        (fun x => Fsum_eq_ezBsum P Q X Y a b x)]
  rw [← smul_sum_gen, ← ezB_eq_sum P Q a b]
  rfl

lemma partition_sum (P Q : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌)) :
    (∑ x : Idx P Q, Fsum P Q X Y a b x)
      = (∑ x ∈ sA P Q, Fsum P Q X Y a b x)
        + (∑ x ∈ sB P Q, Fsum P Q X Y a b x)
        + (∑ x ∈ sD P Q, Fsum P Q X Y a b x) := by
  classical
  have h1 : (Finset.univ : Finset (Idx P Q)) = sA P Q ∪ sB P Q ∪ sD P Q := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_union, mem_sA, mem_sB, mem_sD, IsD, true_iff]
    tauto
  have h2 : Disjoint (sA P Q) (sB P Q) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [mem_sA] at hx
    rw [mem_sB] at hx'
    exact hx'.1 hx.1
  have h3 : Disjoint (sA P Q ∪ sB P Q) (sD P Q) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_union] at hx
    rw [mem_sD] at hx'
    rcases hx with hx | hx
    · rw [mem_sA] at hx
      exact hx'.1 hx
    · rw [mem_sB] at hx
      exact hx'.2 hx
  rw [h1, Finset.sum_union h3, Finset.sum_union h2]

/-- **The Eilenberg–Zilber shuffle lemma**: the boundary of the shuffle chain is the sum of the
`a`-side `ezA` and, with the Koszul sign `(-1)^{P+1}`, the `b`-side `ezB`. -/
theorem ezChainB_sbdry_gen (P Q : ℕ) (X Y : SSet.{0})
    (a : X.obj (Opposite.op (SimplexCategory.mk (P+1))))
    (b : Y.obj (Opposite.op (SimplexCategory.mk (Q+1)))) :
    Submission.Cohomology.sbdry (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ ((P+1)+Q)
        (Work.Cohomology.ezChainB (p := P+1) (q := Q+1) a b)
      = Work.Cohomology.ezA P Q a b + (-1 : ℚ) ^ (P+1) • Work.Cohomology.ezB P Q a b := by
  rw [sbdry_ezChainB_expand, partition_sum, sumA_eq_ezA, sumB_eq_ezB, sumD_eq_zero, add_zero]
  rfl

end

end Work.Cohomology.EZG
