import Mathlib
import Submission.Work.Cohomology.EZG.EZShufSetup

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology.EZG

/-! # The `b`-side of the expanded boundary, reindexed

`Fsum P Q a b x` is the summand of the expanded boundary of the shuffle chain
`ezChainB a b` at the index `x = (A, k)` (a `(P+1,Q+1)`-shuffle `A` together with a face
index `k`).  `ezBsum P Q a b y` is the summand of the `b`-side `ezB P Q a b` at
`y = (A'', j)`.

This file proves that on the `b`-side (`x : IdxB P Q`, i.e. the letter deleted by `k` is a
`b`-letter) the boundary summand at `x` is the `b`-side summand at `bFwd x`, multiplied by
the Koszul sign `(-1)^(P+1)`.

The three cases (`k = 0`, `k = last`, and `0 < k < last`) are handled by the corresponding
face lemmas `faceB_zero(_g)`, `faceB_last(_g)`, `faceB_mid(_g)` together with the sign
lemmas `sgnA_delPos_zero`, `sgnA_delPos_last`, `sgnA_delPos_succ_B`. -/

noncomputable section

variable {X Y : SSet.{0}}

/-- The last-face version of `faceB_last_g`, without the superfluous hypothesis `A.card = Q+1`
(the proof of `faceB_last_g` never uses it, and `N ≤ A.card + Q` already follows from `hB`). -/
theorem faceB_last_g' {N Q : ℕ} (A : Finset (Fin (N+1))) (hB : N + 1 ≤ A.card + (Q+1))
    (hN : (Fin.last N) ∉ A) :
    (CategoryTheory.CategoryStruct.comp (SimplexCategory.δ (Fin.last (N+1))) (shB A hB)) =
      (CategoryTheory.CategoryStruct.comp
        (shB (delPosP A (Fin.last N))
          (by rw [delPosP_card_of_notMem hN]; omega))
        (SimplexCategory.δ (Fin.last (Q+1)))) := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    shB_apply, delta_toOrderHom]
  rw [Fin.succAbove_last_apply, Fin.succAbove_last_apply, Fin.val_castSucc, Fin.val_castSucc]
  exact (cntB_delPosP_of_le A (Fin.last N) j.val (Fin.le_last j)).symm

theorem Fsum_eq_ezBsum (P Q : ℕ) (X Y : SSet.{0})
    (a : X.obj (Opposite.op (SimplexCategory.mk (P+1))))
    (b : Y.obj (Opposite.op (SimplexCategory.mk (Q+1)))) (x : Work.Cohomology.EZG.IdxB P Q) :
    Work.Cohomology.EZG.Fsum P Q X Y a b x.1
      = (-1 : ℚ) ^ (P+1) • Work.Cohomology.EZG.ezBsum P Q X Y a b
          (Work.Cohomology.EZG.bFwd P Q x) := by
  obtain ⟨⟨⟨A,hA⟩,k⟩,hB⟩ := x
  dsimp only at hB
  have hL : Fsum P Q X Y a b (⟨⟨A,hA⟩,k⟩ : Idx P Q) =
      Finsupp.single ((MonoidalCategoryStruct.tensorObj X Y).δ k (ezPair P Q a b A hA))
        ((sgnA A : ℚ) * (-1 : ℚ) ^ (k : ℕ)) := rfl
  rw [delta_ezPair P Q a b A hA k] at hL
  rw [hL]
  have hbf : bFwd P Q (⟨(⟨A,hA⟩,k), hB⟩ : IdxB P Q) =
      (⟨delPosP A (delIdx k), by rw [delPosP_card_of_notMem hB.1]; exact hA⟩,
       ⟨cntB A k.val, by have := cntB_le_card A k.val; have := hA; omega⟩) := rfl
  rw [hbf]
  rw [ezBsum, Finsupp.smul_single, smul_eq_mul]
  by_cases h0 : k.val = 0
  · -- Case `k = 0`.
    have hdel0 : delIdx k = (0 : Fin ((P+1)+Q+1)) := by
      rw [delIdx_of_le k (by omega)]; ext; simpa using h0
    have hk0 : k = (0 : Fin ((P+1)+Q+2)) := Fin.ext h0
    have hnot0 : (0 : Fin ((P+1)+Q+1)) ∉ A := by rw [← hdel0]; exact hB.1
    have hcnt0 : cntB A 0 = 0 := by simp [cntB]
    have hAf : SimplexCategory.δ k ≫ shA A (le_of_eq hA) =
        shA (delPosP A (delIdx k)) (by rw [delPosP_card_of_notMem hB.1]; exact le_of_eq hA) := by
      have h := faceB_zero (N := (P+1)+Q) (P := P) A (le_of_eq hA) hnot0
      rw [← hk0] at h
      simpa only [hdel0] using h
    have hBf : SimplexCategory.δ k ≫ shB A (q := Q+1) (by have := hA; omega) =
        shB (delPosP A (delIdx k) : Finset (Fin ((P+1)+Q))) (q := Q)
          (by rw [delPosP_card_of_notMem hB.1]; have := hA; omega) ≫
          SimplexCategory.δ (0 : Fin (Q+2)) := by
      have h := faceB_zero_g (N := (P+1)+Q) (Q := Q) A (by have := hA; omega) hnot0
      rw [← hk0] at h
      simpa only [hdel0] using h
    have hj : (⟨cntB A k.val, by have := cntB_le_card A k.val; have := hA; omega⟩ : Fin (Q+2)) = 0 := by
      apply Fin.ext; rw [Fin.val_mk, h0]; simp [cntB]
    have hs : (sgnA A : ℚ) = (sgnA (delPosP A (delIdx k)) : ℚ) * (-1:ℚ)^(P+1) := by
      have hdd : delPosP A (delIdx k) = delPosP A 0 := by rw [hdel0]
      have h := sgnA_delPos_zero (n := (P+1)+Q) A
      rw [if_neg hnot0, hA, ← hdd] at h
      have h2 := congrArg (fun z : ℤ => (z : ℚ)) h
      push_cast at h2
      exact h2
    congr 1
    · dsimp only
      rw [hAf, hBf, hj]
      simp only [CategoryTheory.op_comp, Functor.map_comp]
      rfl
    · dsimp only
      rw [h0, hcnt0]
      simp only [pow_zero, mul_one, one_mul]
      rw [hs]
      ring
  · by_cases hlast : k.val = (P+1)+Q+1
    · -- Case `k = last`.
      have hklast : k = Fin.last ((P+1)+Q+1) := Fin.ext hlast
      have hdellast : delIdx k = Fin.last ((P+1)+Q) := by
        rw [delIdx_of_val k hlast]; rfl
      have hN : (Fin.last ((P+1)+Q) : Fin ((P+1)+Q+1)) ∉ A := by rw [← hdellast]; exact hB.1
      have hAf : SimplexCategory.δ k ≫ shA A (le_of_eq hA) =
          shA (delPosP A (delIdx k)) (by rw [delPosP_card_of_notMem hB.1]; exact le_of_eq hA) := by
        have h := faceB_last (N := (P+1)+Q) (P := P) A (le_of_eq hA) hN
        rw [← hklast] at h
        simpa only [hdellast] using h
      have hBf : SimplexCategory.δ k ≫ shB A (q := Q+1) (by have := hA; omega) =
          shB (delPosP A (delIdx k) : Finset (Fin ((P+1)+Q))) (q := Q)
            (by rw [delPosP_card_of_notMem hB.1]; have := hA; omega) ≫
            SimplexCategory.δ (Fin.last (Q+1)) := by
        have h := faceB_last_g' (N := (P+1)+Q) (Q := Q) A (by have := hA; omega) hN
        rw [← hklast] at h
        simpa only [hdellast] using h
      have hj : (⟨cntB A k.val, by have := cntB_le_card A k.val; have := hA; omega⟩ : Fin (Q+2))
          = Fin.last (Q+1) := by
        apply Fin.ext
        rw [Fin.val_mk, Fin.val_last, hlast, cntB_eq_sub A (m := (P+1)+Q+1) (by omega),
          cnt_eq_card A (m := (P+1)+Q+1) (by omega), hA]
        omega
      have hs : (sgnA A : ℚ) * (-1:ℚ)^((P+1)+Q+1) = (-1:ℚ)^(P+1) *
          ((-1:ℚ)^(cntB A ((P+1)+Q+1)) * (sgnA (delPosP A (delIdx k)) : ℚ)) := by
        have hZ := sgnA_delPos_last (n := (P+1)+Q) A
        rw [if_neg hN] at hZ
        have hdd : delPosP A (Fin.last ((P+1)+Q)) = delPosP A (delIdx k) := by rw [hdellast]
        rw [hdd] at hZ
        have hQ : cntB A ((P+1)+Q+1) = (P+1)+Q+1 - A.card := by
          rw [cntB_eq_sub A (m := (P+1)+Q+1) (by omega),
            cnt_eq_card A (m := (P+1)+Q+1) (by omega)]
        have h2 := congrArg (fun z : ℤ => (z:ℚ)) hZ
        push_cast at h2
        rw [← hQ, hA] at h2
        rw [h2]; ring
      congr 1
      · dsimp only
        rw [hAf, hBf, hj]
        simp only [CategoryTheory.op_comp, Functor.map_comp]
        rfl
      · dsimp only
        rw [hlast]
        rw [hs]
    · -- Interior case `0 < k < last`.
      have hklt : k.val < (P+1)+Q+1 := lt_of_le_of_ne (Nat.lt_succ_iff.mp k.isLt) hlast
      have hdelk : delIdx k = (⟨k.val, by omega⟩ : Fin ((P+1)+Q+1)) := delIdx_of_le k (by omega)
      set q : Fin ((P+1)+Q) := ⟨k.val - 1, by omega⟩ with hqdef
      have hqval : q.val = k.val - 1 := by rw [hqdef]
      have hqsucc : (q.succ : Fin ((P+1)+Q+1)) = delIdx k := by
        apply Fin.ext; simp only [Fin.val_succ, Fin.val_mk, hqval, hdelk]; omega
      have hck : (Fin.castSucc q.succ : Fin ((P+1)+Q+2)) = k := by
        apply Fin.ext; simp only [Fin.val_castSucc, hqsucc, hdelk]
      have hq : (q.castSucc : Fin ((P+1)+Q+1)) ∉ A := by
        rcases hB.2 with hh | hh | hh
        · exact absurd hh h0
        · exact absurd hh hlast
        · exact hh
      have hq' : (q.succ : Fin ((P+1)+Q+1)) ∉ A := by rw [hqsucc]; exact hB.1
      have hAf : SimplexCategory.δ k ≫ shA A (le_of_eq hA) =
          shA (delPosP A (delIdx k)) (by rw [delPosP_card_of_notMem hB.1]; exact le_of_eq hA) := by
        have h := faceB_mid (N := (P+1)+Q) (P := P) A (le_of_eq hA) q hq hq'
        rw [hck] at h
        simpa only [hqsucc] using h
      have hBf : SimplexCategory.δ k ≫ shB A (q := Q+1) (by have := hA; omega) =
          shB (delPosP A (delIdx k) : Finset (Fin ((P+1)+Q))) (q := Q)
            (by rw [delPosP_card_of_notMem hB.1]; have := hA; omega) ≫
            SimplexCategory.δ (⟨cntB A k.val, by have := cntB_le_card A k.val; have := hA; omega⟩ : Fin (Q+2)) := by
        have h := faceB_mid_g (N := (P+1)+Q) (P := P) (Q := Q) A (le_of_eq hA) (by have := hA; omega) q hq hq'
        rw [hck] at h
        have hdv : (delIdx k).val = k.val := by rw [hdelk]
        simp only [hqsucc, hdv] at h
        exact h
      have hs : (sgnA A : ℚ) * (-1:ℚ)^(k.val) = (-1:ℚ)^(P+1) *
          ((-1:ℚ)^(cntB A k.val) * (sgnA (delPosP A (delIdx k)) : ℚ)) := by
        have hZ := sgnA_delPos_succ_B A q hq hq'
        have hqs' : delPosP A q.succ = delPosP A (delIdx k) := by rw [hqsucc]
        rw [hqs'] at hZ
        have hq1 : q.val + 1 = k.val := by rw [hqval]; omega
        have h2 := congrArg (fun z : ℤ => (z:ℚ)) hZ
        push_cast at h2
        rw [hq1, hA] at h2
        rw [h2]; ring
      -- The two components of the pair are proved by `hAf`/`hBf` (using `hqsucc` to identify
      -- the face index with `cntB A k.val`); the coefficient is discharged by `congr` from `hs`.
      congr 1
      · dsimp only
        rw [hAf, hBf]
        simp only [CategoryTheory.op_comp, Functor.map_comp]
        rfl

end

end Work.Cohomology.EZG
