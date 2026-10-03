import Mathlib
import Submission.Work.ORBassSerre.Interface
import Submission.Work.ORBassSerre.HNN.Tree

set_option autoImplicit false

universe u

namespace Work.ORLocInd.CohenLyndon

open HNNExtension
open Work.ORBassSerre.HNN

variable {K : Type u} [Group K] {A B : Subgroup K} {φ : A ≃* B}

/-- Left multiplication by an element of the base group does not change the `t`-length: the
reduced word of `g` is still reduced when its head is multiplied on the left by `x`. -/
theorem tlen_of_mul (x : K) (g : HNNExtension K A B φ) :
    tlen (HNNExtension.of (A := A) (B := B) (φ := φ) x * g) = tlen g := by
  obtain ⟨w, hw⟩ := exists_reducedWord (A := A) (B := B) (φ := φ) g
  have hprod : NormalWord.ReducedWord.prod φ
      ({ head := x * w.head, toList := w.toList, chain := w.chain } :
        NormalWord.ReducedWord K A B) = HNNExtension.of (A := A) (B := B) (φ := φ) x * g := by
    rw [← hw]
    simp only [NormalWord.ReducedWord.prod, map_mul]
    group
  rw [tlen_eq_of_prod (φ := φ) hprod, tlen_eq_of_prod (φ := φ) hw]

/-- Left multiplication by an element of the base group does not change the `t`-length function
`N` of the Bass--Serre tree of an HNN extension. -/
theorem N_smul_of (x : K) (Z : VSet (G := K) (A := A) (B := B) (φ := φ)) :
    N (HNNExtension.of (A := A) (B := B) (φ := φ) x • Z) = N Z := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep Z
  rw [smul_qmk, N_qmk, N_qmk, tlen_of_mul]

/-- **Conjugating a non-identity element of the normal closure into the base group.**
Let `E = HNNExtension K A B φ` be an HNN extension, `r ∈ K` with `⟪r⟫_K ⊓ A = ⟂ = ⟪r⟫_K ⊓ B`,
and `m ∈ ⟪r⟫_K`, `m ≠ 1`.  If `y * of m * y⁻¹` lies in the image of the base group, then so does
`y`.

Equivalently (see the proof): the element `of m` of the base group fixes only the base vertex `of K`
of the Bass--Serre tree of `E`.  The hypotheses `⟪r⟫ ⊓ A = ⟂` and `⟪r⟫ ⊓ B = ⟂` enter at the last
step: a vertex adjacent to the base vertex is `qmk (of m' * t^ε)`, whose stabilizer consists of the
elements conjugated into the subgroup `toSubgroup A B ε` (`A` or `B`); an element `of m` of it
satisfies `m'⁻¹ m m' ∈ toSubgroup A B (-ε)`, and since `m'⁻¹ m m' ∈ ⟪r⟫` too, the intersection
hypothesis forces `m = 1`, a contradiction. -/
theorem hnn_conj_mem_range {K : Type u} [Group K] (A B : Subgroup K) (φ : A ≃* B) {r : K}
    (hA : Subgroup.normalClosure ({r} : Set K) ⊓ A = ⊥)
    (hB : Subgroup.normalClosure ({r} : Set K) ⊓ B = ⊥)
    {m : K} (hm : m ∈ Subgroup.normalClosure ({r} : Set K)) (hm1 : m ≠ 1)
    {y : HNNExtension K A B φ}
    (hy : y * HNNExtension.of m * y⁻¹ ∈
      (HNNExtension.of (A := A) (B := B) (φ := φ)).range) :
    y ∈ (HNNExtension.of (A := A) (B := B) (φ := φ)).range := by
  classical
  -- The vertex of the Bass--Serre tree on which `of m` acts: `of m` fixes `qmk y⁻¹`
  -- exactly when `y * of m * y⁻¹` lies in the base group.
  set X : VSet (G := K) (A := A) (B := B) (φ := φ) := qmk y⁻¹ with hXdef
  by_cases hX : X = base
  · -- then `y⁻¹`, hence `y`, lies in the base group
    have hmem : y⁻¹ ∈ (HNNExtension.of (A := A) (B := B) (φ := φ)).range := by
      rw [hXdef] at hX
      rw [qmk_eq_iff] at hX
      simpa using hX
    simpa using Subgroup.inv_mem _ hmem
  · exfalso
    have heX : HNNExtension.of (A := A) (B := B) (φ := φ) m • X = X := by
      rw [hXdef, smul_qmk, qmk_eq_iff]
      have hy' : y * (HNNExtension.of (A := A) (B := B) (φ := φ) m)⁻¹ * y⁻¹ ∈
          (HNNExtension.of (A := A) (B := B) (φ := φ)).range := by
        have h3 : (y * HNNExtension.of (A := A) (B := B) (φ := φ) m * y⁻¹)⁻¹ =
            y * (HNNExtension.of (A := A) (B := B) (φ := φ) m)⁻¹ * y⁻¹ := by group
        rw [← h3]
        exact Subgroup.inv_mem _ hy
      have h4 : (HNNExtension.of (A := A) (B := B) (φ := φ) m * y⁻¹)⁻¹ * y⁻¹ =
          y * (HNNExtension.of (A := A) (B := B) (φ := φ) m)⁻¹ * y⁻¹ := by group
      rw [h4]
      exact hy'
    -- Descend the `t`-length: a fixed vertex of positive level has a fixed parent.
    have key : ∀ n : ℕ, ∀ Z : VSet (G := K) (A := A) (B := B) (φ := φ),
        N Z = n → HNNExtension.of (A := A) (B := B) (φ := φ) m • Z = Z →
        (N Z = 0 ∨ ∃ Y : VSet (G := K) (A := A) (B := B) (φ := φ),
          N Y = 1 ∧ adj base Y ∧
          HNNExtension.of (A := A) (B := B) (φ := φ) m • Y = Y) := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro Z hZn heZ
        by_cases hZb : Z = base
        · left
          exact (N_eq_zero_iff Z).mpr hZb
        · right
          obtain ⟨P, hPadj, hPN⟩ := parent_exists Z hZb
          have heP : HNNExtension.of (A := A) (B := B) (φ := φ) m • P = P := by
            refine parent_unique Z _ P ?_ hPadj ?_ hPN
            · rw [← heZ]; exact smul_adj _ hPadj
            · rw [N_smul_of (A := A) (B := B) (φ := φ) m P, hPN]
          rcases Nat.eq_zero_or_pos (N P) with hP0 | hPpos
          · have hPb : P = base := (N_eq_zero_iff P).mp hP0
            refine ⟨Z, ?_, ?_, heZ⟩
            · rw [← hPN, hP0]
            · rw [hPb] at hPadj; exact hPadj.symm
          · have hlt : N P < n := by rw [hZn] at hPN; omega
            rcases ih (N P) hlt P rfl heP with h0 | hY
            · exact absurd h0 hPpos.ne'
            · exact hY
    rcases key (N X) X rfl heX with hNX0 | ⟨Y, hYN, hYadj, heY⟩
    · exact hX ((N_eq_zero_iff X).mp hNX0)
    · -- `Y` is a neighbour of the base vertex, hence of the form `qmk (of m' * t^ε)`
      obtain ⟨m', ε, hYeq⟩ := (adj_iff (1 : HNNExtension K A B φ) Y).mp hYadj
      have hYeq' : Y = qmk (ofE (A := A) (B := B) (φ := φ) m' *
          tpow (A := A) (B := B) (φ := φ) ε) := by
        rw [hYeq, step_eq, one_mul]
      have hmem : HNNExtension.of (A := A) (B := B) (φ := φ) m ∈
          MulAction.stabilizer (HNNExtension K A B φ)
            (qmk (ofE (A := A) (B := B) (φ := φ) m' * tpow (A := A) (B := B) (φ := φ) ε)) := by
        rw [MulAction.mem_stabilizer_iff, ← hYeq', heY]
      -- the stabilizer of `qmk (of m' * t^ε)` is the conjugate of the base group by `of m' * t^ε`
      rw [stabilizer_qmk, Subgroup.mem_map] at hmem
      obtain ⟨w, hw, hwe⟩ := hmem
      obtain ⟨k, hk⟩ := hw
      have hmem2 : (ofE (A := A) (B := B) (φ := φ) m' * tpow (A := A) (B := B) (φ := φ) ε)⁻¹ *
          HNNExtension.of (A := A) (B := B) (φ := φ) m *
          (ofE (A := A) (B := B) (φ := φ) m' * tpow (A := A) (B := B) (φ := φ) ε) ∈
          (HNNExtension.of (A := A) (B := B) (φ := φ)).range := by
        refine ⟨k, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom] at hwe
        rw [← hk] at hwe
        rw [MulAut.conj_apply] at hwe
        rw [← hwe]
        group
      -- conjugating back by `of m' * t^ε` exhibits `t^(-ε) * of (m'⁻¹ * m * m') * t^ε` in the base
      have heq : (ofE (A := A) (B := B) (φ := φ) m' * tpow (A := A) (B := B) (φ := φ) ε)⁻¹ *
          HNNExtension.of (A := A) (B := B) (φ := φ) m *
          (ofE (A := A) (B := B) (φ := φ) m' * tpow (A := A) (B := B) (φ := φ) ε) =
          tpow (A := A) (B := B) (φ := φ) (-ε) * ofE (A := A) (B := B) (φ := φ) (m'⁻¹ * m * m') *
            tpow (A := A) (B := B) (φ := φ) ε := by
        have e1 : (ofE (A := A) (B := B) (φ := φ) m' * tpow (A := A) (B := B) (φ := φ) ε)⁻¹ =
            tpow (A := A) (B := B) (φ := φ) (-ε) * ofE (A := A) (B := B) (φ := φ) (m'⁻¹) := by
          rw [mul_inv_rev, tpow_inv, ← map_inv]
        rw [e1, show ofE (A := A) (B := B) (φ := φ) (m'⁻¹ * m * m') =
            ofE (A := A) (B := B) (φ := φ) (m'⁻¹) * ofE (A := A) (B := B) (φ := φ) m *
              ofE (A := A) (B := B) (φ := φ) m' from by rw [map_mul, map_mul]]
        group
      have hmem3 : tpow (A := A) (B := B) (φ := φ) (-ε) *
          ofE (A := A) (B := B) (φ := φ) (m'⁻¹ * m * m') *
          tpow (A := A) (B := B) (φ := φ) ε ∈
          (HNNExtension.of (A := A) (B := B) (φ := φ)).range := by
        rw [← heq]; exact hmem2
      -- hence `m'⁻¹ * m * m'` lies in `A` or `B` ...
      have hT : m'⁻¹ * m * m' ∈ HNNExtension.toSubgroup A B (-ε) := by
        rw [← tconjMemRange (A := A) (B := B) (φ := φ) (-ε) (m'⁻¹ * m * m')]
        simpa using hmem3
      -- ... as well as in the normal closure of `r`, so it is trivial
      have hNm : m'⁻¹ * m * m' ∈ Subgroup.normalClosure ({r} : Set K) :=
        Subgroup.Normal.conj_mem' Subgroup.normalClosure_normal (n := m) hm m'
      have hone : m'⁻¹ * m * m' = 1 := by
        rcases Int.units_eq_one_or (-ε) with h | h
        · exact Subgroup.mem_bot.mp (by rw [← hA]; exact ⟨hNm, by simpa [h] using hT⟩)
        · exact Subgroup.mem_bot.mp (by rw [← hB]; exact ⟨hNm, by simpa [h] using hT⟩)
      have hm1' : m = 1 := by
        have h3 : m' * (m'⁻¹ * m * m') * m'⁻¹ = m := by group
        rw [← h3, hone]
        group
      exact hm1 hm1'

end Work.ORLocInd.CohenLyndon
