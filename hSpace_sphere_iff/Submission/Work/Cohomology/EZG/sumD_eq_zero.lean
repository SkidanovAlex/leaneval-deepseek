import Mathlib
import Submission.Work.Cohomology.EZG.EZShufSetup
import Submission.Work.Cohomology.EZG.dAux
import Submission.Work.Cohomology.EZG.cnt_swapA_of_ne
import Submission.Work.Cohomology.EZG.cntB_swapA_of_ne
import Submission.Work.Cohomology.EZG.delta_shA_swapA
import Submission.Work.Cohomology.EZG.delta_shB_swapA
import Submission.Work.Cohomology.EZG.isD_iff_dcond

namespace Work.Cohomology.EZG

open CategoryTheory Simplicial Opposite
open Work.Cohomology

noncomputable section

variable {X Y : SSet.{0}}

/-! ### The involution on the mixed indices -/

/-- The position preceding the deleted one, for a mixed index `x = (A,k)`: `q.succ = delIdx k`. -/
noncomputable def sDq (P Q : ℕ) (x : Idx P Q) (hx : x ∈ sD P Q) : Fin ((P+1)+Q) :=
  ⟨x.2.val - 1, by
    classical
    have hz := IsD_not_z ((Finset.mem_filter.mp hx).2)
    omega⟩

lemma sDq_val (P Q : ℕ) (x : Idx P Q) (hx : x ∈ sD P Q) :
    x.2.val = (sDq P Q x hx).val + 1 := by
  classical
  have hz := IsD_not_z ((Finset.mem_filter.mp hx).2)
  have h1 : 1 ≤ x.2.val := by omega
  show x.2.val = x.2.val - 1 + 1
  omega

lemma sDq_dcond (P Q : ℕ) (x : Idx P Q) (hx : x ∈ sD P Q) :
    (sDq P Q x hx).castSucc ∈ x.1.1 ↔ (sDq P Q x hx).succ ∉ x.1.1 := by
  classical
  exact (isD_iff_dcond x.1.1 x.2 (sDq P Q x hx) (sDq_val P Q x hx)).mp
    ((Finset.mem_filter.mp hx).2)

lemma sDq_card (P Q : ℕ) (x : Idx P Q) (hx : x ∈ sD P Q) :
    (swapA ((P+1)+Q) x.1.1 (sDq P Q x hx)).card = P+1 := by
  rw [swapA_card (N := (P+1)+Q) x.1.1 (sDq P Q x hx) (sDq_dcond P Q x hx)]
  exact x.1.2

/-- The involution on the mixed indices: exchange the membership of the two adjacent positions
`q.castSucc`, `q.succ` of the shuffle, keeping the face index `k` fixed. -/
noncomputable def dSwap (P Q : ℕ) (x : Idx P Q) (hx : x ∈ sD P Q) : Idx P Q :=
  (⟨swapA ((P+1)+Q) x.1.1 (sDq P Q x hx), sDq_card P Q x hx⟩, x.2)

lemma sDq_dSwap (P Q : ℕ) (x : Idx P Q) (hx : x ∈ sD P Q)
    (hx' : dSwap P Q x hx ∈ sD P Q) :
    sDq P Q (dSwap P Q x hx) hx' = sDq P Q x hx := rfl

lemma dSwap_mem (P Q : ℕ) (x : Idx P Q) (hx : x ∈ sD P Q) : dSwap P Q x hx ∈ sD P Q := by
  classical
  rw [sD, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  change IsD ((P+1)+Q) (swapA ((P+1)+Q) x.1.1 (sDq P Q x hx)) x.2
  refine (isD_iff_dcond (A := swapA ((P+1)+Q) x.1.1 (sDq P Q x hx)) x.2 (sDq P Q x hx)
    (sDq_val P Q x hx)).mpr ?_
  rw [swapA_mem_castSucc (N := (P+1)+Q) x.1.1 (sDq P Q x hx) (sDq_dcond P Q x hx),
    swapA_mem_succ (N := (P+1)+Q) x.1.1 (sDq P Q x hx) (sDq_dcond P Q x hx)]
  exact dcond_iff.mp (sDq_dcond P Q x hx)

lemma dSwap_invol (P Q : ℕ) (x : Idx P Q) (hx : x ∈ sD P Q) :
    dSwap P Q (dSwap P Q x hx) (dSwap_mem P Q x hx) = x := by
  have hq := sDq_dSwap P Q x hx (dSwap_mem P Q x hx)
  refine Prod.ext ?_ ?_
  · refine Subtype.ext ?_
    show swapA ((P+1)+Q) (swapA ((P+1)+Q) x.1.1 (sDq P Q x hx))
        (sDq P Q (dSwap P Q x hx) (dSwap_mem P Q x hx)) = x.1.1
    rw [hq]
    exact swapA_invol (N := (P+1)+Q) x.1.1 (sDq P Q x hx) (sDq_dcond P Q x hx)
  · rfl

/-! ### The two terms of a cancelling pair are opposite -/

/-- The summand at the swapped index is the negative of the summand at the index: the two
staircases have the same `k`-th face and the shuffle sign flips. -/
lemma Fsum_neg_of_swapA (P Q : ℕ) (X Y : SSet.{0})
    (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌))
    (A : Finset (Fin ((P+1)+(Q+1)))) (hA : A.card = P+1)
    (q : Fin ((P+1)+Q)) (k : Fin ((P+1)+Q+2))
    (hk : k.val = q.val + 1) (hd : q.castSucc ∈ A ↔ q.succ ∉ A) :
    Fsum P Q X Y a b
        (⟨swapA ((P+1)+Q) A q, by rw [swapA_card (N := (P+1)+Q) A q hd]; exact hA⟩, k)
      = - Fsum P Q X Y a b (⟨A, hA⟩, k) := by
  have hA' : (swapA ((P+1)+Q) A q).card = P+1 := by
    rw [swapA_card (N := (P+1)+Q) A q hd]; exact hA
  have key1 : ∀ (B : Finset (Fin ((P+1)+(Q+1)))) (hB : B.card = P+1),
      X.δ k (ezPair P Q a b B hB).1
        = X.map (SimplexCategory.δ k ≫ shA B (le_of_eq hB)).op a := by
    intro B hB
    rw [ezPair]
    exact delta_map X k (shA B (le_of_eq hB)) a
  have key2 : ∀ (B : Finset (Fin ((P+1)+(Q+1)))) (hB : B.card = P+1),
      Y.δ k (ezPair P Q a b B hB).2
        = Y.map (SimplexCategory.δ k ≫ shB B (by have := hB; omega)).op b := by
    intro B hB
    rw [ezPair]
    exact delta_map Y k (shB B (by have := hB; omega)) b
  have hs : sgnA (swapA ((P+1)+Q) A q) = - sgnA A := sgnA_swap A q hd
  have hsign : (sgnA (swapA ((P+1)+Q) A q) : ℚ) = - (sgnA A : ℚ) := by
    rw [hs]; push_cast; ring
  have hpt1 : X.δ k (ezPair P Q a b (swapA ((P+1)+Q) A q) hA').1
      = X.δ k (ezPair P Q a b A hA).1 := by
    rw [key1 (swapA ((P+1)+Q) A q) hA', key1 A hA]
    exact (congrArg (fun φ => X.map φ.op a)
      (delta_shA_swapA (N := (P+1)+Q) A q k hk hd (le_of_eq hA) (le_of_eq hA'))).symm
  have hpt2 : Y.δ k (ezPair P Q a b (swapA ((P+1)+Q) A q) hA').2
      = Y.δ k (ezPair P Q a b A hA).2 := by
    rw [key2 (swapA ((P+1)+Q) A q) hA', key2 A hA]
    exact (congrArg (fun ψ => Y.map ψ.op b)
      (delta_shB_swapA (N := (P+1)+Q) A q k hk hd (by have := hA; omega)
        (by have := hA'; omega))).symm
  have hpt : (X.δ k (ezPair P Q a b (swapA ((P+1)+Q) A q) hA').1,
      Y.δ k (ezPair P Q a b (swapA ((P+1)+Q) A q) hA').2)
      = (X.δ k (ezPair P Q a b A hA).1, Y.δ k (ezPair P Q a b A hA).2) := by
    rw [hpt1, hpt2]
  have hgoal : Fsum P Q X Y a b (⟨swapA ((P+1)+Q) A q, hA'⟩, k)
      = - Fsum P Q X Y a b (⟨A, hA⟩, k) := by
    rw [Fsum, Fsum, hpt, hsign, neg_mul]
    exact Finsupp.single_neg _ _
  exact hgoal

lemma Fsum_dSwap (P Q : ℕ) (X Y : SSet.{0})
    (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌))
    (x : Idx P Q) (hx : x ∈ sD P Q) :
    Fsum P Q X Y a b (dSwap P Q x hx) = - Fsum P Q X Y a b x := by
  show Fsum P Q X Y a b (⟨swapA ((P+1)+Q) x.1.1 (sDq P Q x hx), _⟩, x.2)
      = - Fsum P Q X Y a b x
  exact Fsum_neg_of_swapA P Q X Y a b x.1.1 x.1.2 (sDq P Q x hx) x.2 (sDq_val P Q x hx)
    (sDq_dcond P Q x hx)

/-! ### The mixed terms cancel -/

theorem sumD_eq_zero (P Q : ℕ) (X Y : SSet.{0}) (a : X.obj (Opposite.op (SimplexCategory.mk (P+1)))) (b : Y.obj (Opposite.op (SimplexCategory.mk (Q+1)))) : (∑ x ∈ Work.Cohomology.EZG.sD P Q, Work.Cohomology.EZG.Fsum P Q X Y a b x) = 0 := by
  classical
  refine Finset.sum_involution (s := sD P Q) (f := Fsum P Q X Y a b) (dSwap P Q) ?_ ?_
    (fun x hx => dSwap_mem P Q x hx) ?_
  · intro x hx
    rw [Fsum_dSwap P Q X Y a b x hx, add_neg_cancel]
  · intro x hx hne hcon
    have hAeq : swapA ((P+1)+Q) x.1.1 (sDq P Q x hx) = x.1.1 := by
      simpa only [dSwap] using congrArg (fun y : Idx P Q => y.1.1) hcon
    have hd := sDq_dcond P Q x hx
    have hiff : (sDq P Q x hx).succ ∈ x.1.1 ↔ (sDq P Q x hx).castSucc ∈ x.1.1 := by
      have h := swapA_mem_succ (N := (P+1)+Q) x.1.1 (sDq P Q x hx) hd
      rw [hAeq] at h
      exact h
    by_cases hs : (sDq P Q x hx).succ ∈ x.1.1
    · exact absurd hs (hd.mp (hiff.mp hs))
    · exact absurd (hiff.mpr (hd.mpr hs)) hs
  · intro x hx
    exact dSwap_invol P Q x hx

end

end Work.Cohomology.EZG
