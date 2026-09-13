import Mathlib.Algebra.Field.ZMod
import Submission.Commons.LinearAlgebra.Matrix.rank_le_iff_exists_factor
import Submission.Commons.LinearAlgebra.Matrix.rank_eq_zero_iff

namespace Commons.LinearAlgebra.Matrix

open _root_.Matrix

variable {m n : ℕ}

/-- In `ZMod 2` every non-zero element is `1`. -/
lemma zmod_two_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  have hlt : x.val < 2 := ZMod.val_lt x
  rcases (show x.val = 0 ∨ x.val = 1 by omega) with h | h
  · exact absurd ((ZMod.val_eq_zero x).mp h) hx
  · rw [← ZMod.natCast_zmod_val x, h]
    norm_num

lemma exists_apply_ne_zero {α : Type*} {u : α → ZMod 2} (hu : u ≠ 0) : ∃ i, u i ≠ 0 := by
  by_contra h
  push Not at h
  exact hu (funext fun i => h i)

/-- A product of a column and a row (with a single inner index) is an outer product. -/
lemma mul_fin_one_eq_vecMulVec {K : Type*} [Mul K] [AddCommMonoid K]
    (Bm : Matrix (Fin m) (Fin 1) K) (Cm : Matrix (Fin 1) (Fin n) K) :
    Bm * Cm = Matrix.vecMulVec (fun i => Bm i 0) (fun j => Cm 0 j) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.vecMulVec_apply]

/-- The rank of a non-zero outer product over `𝔽₂` is `1`. -/
lemma rank_vecMulVec_zmod_two_eq_one {u : Fin m → ZMod 2} {v : Fin n → ZMod 2}
    (hu : u ≠ 0) (hv : v ≠ 0) : (Matrix.vecMulVec u v).rank = 1 := by
  refine le_antisymm (rank_vecMulVec_le u v) ?_
  rw [rank_eq_finrank_span_cols]
  obtain ⟨j0, hj0⟩ := exists_apply_ne_zero hv
  have hj0' : v j0 = 1 := zmod_two_eq_one_of_ne_zero hj0
  have hcol : (Matrix.vecMulVec u v).col j0 = u := by
    funext i
    rw [Matrix.col_apply, Matrix.vecMulVec_apply, hj0', mul_one]
  have hmem : u ∈ Submodule.span (ZMod 2) (Set.range (Matrix.vecMulVec u v).col) :=
    Submodule.subset_span ⟨j0, hcol⟩
  calc 1 = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({u} : Set (Fin m → ZMod 2))) :=
        (finrank_span_singleton (K := ZMod 2) (v := u) hu).symm
    _ ≤ Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2) (Set.range (Matrix.vecMulVec u v).col)) :=
        Submodule.finrank_mono (Submodule.span_le.mpr (by rintro x rfl; exact hmem))

/-- Over `𝔽₂`, two non-zero outer products are equal only if they are literally equal. -/
lemma vecMulVec_inj_of_ne_zero {u u' : Fin m → ZMod 2} {v v' : Fin n → ZMod 2}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (h : Matrix.vecMulVec u v = Matrix.vecMulVec u' v') : u = u' ∧ v = v' := by
  obtain ⟨i0, hi0⟩ := exists_apply_ne_zero hu
  obtain ⟨j0, hj0⟩ := exists_apply_ne_zero hv
  have hi0' : u i0 = 1 := zmod_two_eq_one_of_ne_zero hi0
  have hj0' : v j0 = 1 := zmod_two_eq_one_of_ne_zero hj0
  have hentry : u' i0 * v' j0 = 1 := by
    have h1 := congrFun (congrFun h i0) j0
    rw [Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, hi0', hj0', one_mul] at h1
    exact h1.symm
  have hu'1 : u' i0 = 1 := by
    refine zmod_two_eq_one_of_ne_zero ?_
    intro h0
    rw [h0, zero_mul] at hentry
    exact zero_ne_one hentry
  have hv'1 : v' j0 = 1 := by
    refine zmod_two_eq_one_of_ne_zero ?_
    intro h0
    rw [h0, mul_zero] at hentry
    exact zero_ne_one hentry
  refine ⟨?_, ?_⟩
  · funext i
    have h1 := congrFun (congrFun h i) j0
    rw [Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, hj0', hv'1, mul_one, mul_one] at h1
    exact h1
  · funext j
    have h1 := congrFun (congrFun h i0) j
    rw [Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, hi0', hu'1, one_mul, one_mul] at h1
    exact h1

/-- The canonical map from pairs of non-zero vectors to rank-one matrices. -/
def rankOneMap (m n : ℕ) :
    {p : (Fin m → ZMod 2) × (Fin n → ZMod 2) // p.1 ≠ 0 ∧ p.2 ≠ 0} →
      {B : Matrix (Fin m) (Fin n) (ZMod 2) // B.rank = 1} :=
  fun p => ⟨Matrix.vecMulVec p.1.1 p.1.2,
    rank_vecMulVec_zmod_two_eq_one p.2.1 p.2.2⟩

lemma rankOneMap_injective (m n : ℕ) : Function.Injective (rankOneMap m n) := by
  rintro ⟨⟨u, v⟩, hu, hv⟩ ⟨⟨u', v'⟩, hu', hv'⟩ h
  have hmat : Matrix.vecMulVec u v = Matrix.vecMulVec u' v' := congrArg Subtype.val h
  obtain ⟨h1, h2⟩ := vecMulVec_inj_of_ne_zero hu hv hmat
  subst h1
  subst h2
  exact Subtype.ext rfl

lemma rankOneMap_surjective (m n : ℕ) : Function.Surjective (rankOneMap m n) := by
  intro B
  obtain ⟨Bm, Cm, hBC⟩ := (rank_le_iff_exists_factor B.1 1).mp (le_of_eq B.2)
  have hmat : B.1 = Matrix.vecMulVec (fun i => Bm i 0) (fun j => Cm 0 j) := by
    rw [hBC, mul_fin_one_eq_vecMulVec]
  have hu : (fun i => Bm i 0) ≠ 0 := by
    intro hzero
    have hB0 : B.1 = 0 := by
      rw [hmat, hzero]
      ext i j
      simp [Matrix.vecMulVec_apply]
    have hB2 := B.2
    rw [hB0, Matrix.rank_zero] at hB2
    exact one_ne_zero hB2.symm
  have hv : (fun j => Cm 0 j) ≠ 0 := by
    intro hzero
    have hB0 : B.1 = 0 := by
      rw [hmat, hzero]
      ext i j
      simp [Matrix.vecMulVec_apply]
    have hB2 := B.2
    rw [hB0, Matrix.rank_zero] at hB2
    exact one_ne_zero hB2.symm
  refine ⟨⟨((fun i => Bm i 0), (fun j => Cm 0 j)), hu, hv⟩, ?_⟩
  exact Subtype.ext hmat.symm

/-- Rank-one matrices over `𝔽₂` correspond bijectively to pairs of non-zero vectors. -/
noncomputable def rankOneEquiv (m n : ℕ) :
    {p : (Fin m → ZMod 2) × (Fin n → ZMod 2) // p.1 ≠ 0 ∧ p.2 ≠ 0} ≃
      {B : Matrix (Fin m) (Fin n) (ZMod 2) // B.rank = 1} :=
  Equiv.ofBijective (rankOneMap m n) ⟨rankOneMap_injective m n, rankOneMap_surjective m n⟩

/-- Splitting a pair together with the non-vanishing of both components. -/
noncomputable def pairEquiv (m n : ℕ) :
    {p : (Fin m → ZMod 2) × (Fin n → ZMod 2) // p.1 ≠ 0 ∧ p.2 ≠ 0} ≃
      {u : Fin m → ZMod 2 // u ≠ 0} × {v : Fin n → ZMod 2 // v ≠ 0} where
  toFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
  invFun q := ⟨(q.1.1, q.2.1), ⟨q.1.2, q.2.2⟩⟩
  left_inv p := by obtain ⟨⟨u, v⟩, ⟨hu, hv⟩⟩ := p; rfl
  right_inv q := by obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := q; rfl

lemma natCard_ne_zero_fun (m : ℕ) :
    Nat.card {u : Fin m → ZMod 2 // u ≠ 0} = 2 ^ m - 1 := by
  classical
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun u : Fin m → ZMod 2 => u = 0)]
  rw [Fintype.card_subtype_eq (0 : Fin m → ZMod 2)]
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]

theorem card_rank_one_zmod_two {m n : ℕ} :
    Nat.card {B : Matrix (Fin m) (Fin n) (ZMod 2) // B.rank = 1} = (2 ^ m - 1) * (2 ^ n - 1) := by
  rw [← Nat.card_congr (rankOneEquiv m n)]
  rw [Nat.card_congr (pairEquiv m n), Nat.card_prod,
    natCard_ne_zero_fun m, natCard_ne_zero_fun n]

end Commons.LinearAlgebra.Matrix