/-
# The `a`-side of the Eilenberg–Zilber shuffle lemma: identification of the summand

For `a : X_{P+1}`, `b : Y_{Q+1}`, the `a`-side summand `Fsum P Q X Y a b x` of the expanded
boundary of the shuffle chain at an index `x = (A, k)` of `IdxA P Q` (a `(P+1,Q+1)`-shuffle `A`
together with a face index `k` whose deleted letter is an `a`-letter) equals the summand
`ezAsum P Q X Y a b (aFwd P Q x)` of the `a`-side `ezA` of the shuffle boundary, reindexed by
`aFwd`.

The proof is bookkeeping: the `k`-th face of the staircase simplex of `A` is the staircase of
`delPosP A (delIdx k)` applied to the `cnt A k`-th face of `a` and to `b`, with the sign changed
by `(-1)^{cnt A k}`, provided the deleted letter is an `a`-letter and is either the first letter
(face `0`) or preceded by an `a`-letter (interior face).
-/
import Mathlib
import Submission.Work.Cohomology.EZG.EZShufSetup

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology.EZG

noncomputable section

variable {X Y : SSet.{0}}

/-! ### General helpers for comparing shuffle maps -/

/-- The face of a simplex whiskered by a morphism: `X.map ψ.op (X.δ i x) = X.map (ψ ≫ δ i).op x`.
-/
lemma map_delta_apply (X : SSet.{0}) {n P : ℕ} (ψ : ⦋n⦌ ⟶ ⦋P⦌) (i : Fin (P+2))
    (x : X.obj (op ⦋P+1⦌)) :
    X.map ψ.op (X.δ i x) = X.map (ψ ≫ SimplexCategory.δ i).op x := by
  rw [SimplicialObject.δ, op_comp, Functor.map_comp]
  rfl

/-- The shuffle map `shA` does not depend on the proof of the cardinality bound. -/
lemma shA_congr_aux {n p : ℕ} (A : Finset (Fin n)) (h1 h2 : A.card ≤ p) :
    Work.Cohomology.shA A h1 = Work.Cohomology.shA A h2 := by
  apply SimplexCategory.Hom.ext
  ext j
  simp only [Work.Cohomology.shA_apply]

/-- The shuffle map `shB` does not depend on the proof of the cardinality bound. -/
lemma shB_congr_aux {n q : ℕ} (A : Finset (Fin n)) (h1 h2 : n ≤ A.card + q) :
    Work.Cohomology.shB A h1 = Work.Cohomology.shB A h2 := by
  apply SimplexCategory.Hom.ext
  ext j
  simp only [Work.Cohomology.shB_apply]

/-- The shuffle map `shA` only depends on the shuffle as a set. -/
lemma shA_congr_finset {n p : ℕ} {A B : Finset (Fin n)} (hAB : A = B)
    (h1 : A.card ≤ p) (h2 : B.card ≤ p) :
    Work.Cohomology.shA A h1 = Work.Cohomology.shA B h2 := by
  subst hAB
  exact shA_congr_aux _ _ _

/-- The shuffle map `shB` only depends on the shuffle as a set. -/
lemma shB_congr_finset {n r : ℕ} {A B : Finset (Fin n)} (hAB : A = B)
    (h1 : n ≤ A.card + r) (h2 : n ≤ B.card + r) :
    Work.Cohomology.shB A h1 = Work.Cohomology.shB B h2 := by
  subst hAB
  exact shB_congr_aux _ _ _

/-! ### The `a`-side face identity in the three cases -/

/-- The interior `a`-face identity, phrased with `delIdx`/`cnt`: when the deleted letter `k` is an
`a`-letter preceded by an `a`-letter, the face `δ k` of `shA A` is `shA (delPosP A (delIdx k))`
followed by the `cnt A k`-th face of `a`. -/
lemma shA_face_interior {N P : ℕ} (A : Finset (Fin (N+1))) (hcard : A.card = P+1)
    (k : Fin (N+2)) (hdel : Work.Cohomology.delIdx k ∈ A)
    (h0 : ¬ k.val = 0) (hlast : ¬ k.val = N+1)
    (hmid : (⟨k.val - 1, by omega⟩ : Fin (N+1)) ∈ A) :
    (SimplexCategory.δ k ≫ Work.Cohomology.shA A (le_of_eq hcard)) =
      (Work.Cohomology.shA (Work.Cohomology.delPosP A (Work.Cohomology.delIdx k))
          (by rw [Work.Cohomology.delPosP_card hdel]; omega) ≫
        SimplexCategory.δ (⟨Work.Cohomology.cnt A k.val,
          by have := Work.Cohomology.cnt_le_card A k.val; omega⟩ : Fin (P+2))) := by
  have hk1 : 1 ≤ k.val := by omega
  have hkN : k.val ≤ N := by omega
  let q : Fin N := ⟨k.val - 1, by omega⟩
  have hqval : q.val = k.val - 1 := rfl
  have hd : Work.Cohomology.delIdx k = q.succ := by
    ext
    simp only [Work.Cohomology.delIdx_val, Fin.val_succ]
    omega
  have hq : q.castSucc ∈ A := by
    have h1 : q.castSucc = (⟨k.val - 1, by omega⟩ : Fin (N+1)) := Fin.ext (by simp [q])
    rwa [h1]
  have hq' : q.succ ∈ A := by rwa [hd] at hdel
  have hkm : k = Fin.castSucc q.succ := by
    ext
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  have hqval2 : q.succ.val = k.val := by
    rw [Fin.val_succ, hqval]
    omega
  have hface := faceA_mid A (le_of_eq hcard) q hq hq'
  have hac : SimplexCategory.δ k = SimplexCategory.δ (Fin.castSucc q.succ) := congrArg _ hkm
  have hac' : (SimplexCategory.δ k ≫ Work.Cohomology.shA A (le_of_eq hcard)) =
      (SimplexCategory.δ (Fin.castSucc q.succ) ≫ Work.Cohomology.shA A (le_of_eq hcard)) :=
    congrArg (fun f => f ≫ Work.Cohomology.shA A (le_of_eq hcard)) hac
  refine (hac'.trans hface).trans ?_
  congr 1
  · exact shA_congr_finset (by rw [hd]) _ _
  · congr 1
    exact Fin.ext (congrArg (fun m => Work.Cohomology.cnt A m) hqval2)

/-- The `a`-side face identity: `δ k ≫ shA A = shA (delPosP A (delIdx k)) ≫ δ (cnt A k)` whenever
`delIdx k ∈ A` and the deleted letter at `k` is the first letter or preceded by an `a`-letter. -/
lemma shA_face_gen {N P : ℕ} (A : Finset (Fin (N+1))) (hcard : A.card = P+1)
    (k : Fin (N+2)) (hdel : Work.Cohomology.delIdx k ∈ A)
    (hcase : k.val = 0 ∨ k.val = N+1 ∨ (⟨k.val - 1, by omega⟩ : Fin (N+1)) ∈ A) :
    (SimplexCategory.δ k ≫ Work.Cohomology.shA A (le_of_eq hcard)) =
      (Work.Cohomology.shA (Work.Cohomology.delPosP A (Work.Cohomology.delIdx k))
          (by rw [Work.Cohomology.delPosP_card hdel]; omega) ≫
        SimplexCategory.δ (⟨Work.Cohomology.cnt A k.val,
          by have := Work.Cohomology.cnt_le_card A k.val; omega⟩ : Fin (P+2))) := by
  by_cases h0 : k.val = 0
  · have hk : k = 0 := Fin.ext h0
    subst hk
    have hd : Work.Cohomology.delIdx (0 : Fin (N+2)) = (0 : Fin (N+1)) := by
      ext; simp [Work.Cohomology.delIdx]
    have hdel0 : (0 : Fin (N+1)) ∈ A := by rwa [hd] at hdel
    have h := faceA_zero A (le_of_eq hcard) hdel0
    convert h
    simp [Work.Cohomology.cnt]
  · by_cases hlast : k.val = N+1
    · have hk : k = Fin.last (N+1) := Fin.ext (by rw [hlast, Fin.val_last])
      subst hk
      have hd : Work.Cohomology.delIdx (Fin.last (N+1)) = (Fin.last N) := by
        ext; simp [Work.Cohomology.delIdx]
      have hdelN : (Fin.last N) ∈ A := by rwa [hd] at hdel
      have h := faceA_last A (le_of_eq hcard) hdelN
      convert h
      rw [Fin.val_last, Fin.val_last, Work.Cohomology.cnt_eq_card A (le_refl (N+1)), hcard]
    · have hmid : (⟨k.val - 1, by omega⟩ : Fin (N+1)) ∈ A := by
        rcases hcase with h | h | h
        · exact absurd h h0
        · exact absurd h hlast
        · exact h
      exact shA_face_interior A hcard k hdel h0 hlast hmid

/-- The analogous `b`-side face identity: `δ k ≫ shB A = shB (delPosP A (delIdx k))` under the
same hypotheses on the deleted letter. -/
lemma shB_face_gen {N P Q : ℕ} (A : Finset (Fin (N+1))) (hA : A.card ≤ P+1)
    (hB : N + 1 ≤ A.card + (Q+1)) (k : Fin (N+2)) (hdel : Work.Cohomology.delIdx k ∈ A)
    (hcase : k.val = 0 ∨ k.val = N+1 ∨ (⟨k.val - 1, by omega⟩ : Fin (N+1)) ∈ A) :
    (SimplexCategory.δ k ≫ Work.Cohomology.shB A hB) =
      (Work.Cohomology.shB (Work.Cohomology.delPosP A (Work.Cohomology.delIdx k))
          (by rw [Work.Cohomology.delPosP_card hdel]; omega)) := by
  by_cases h0 : k.val = 0
  · have hk : k = 0 := Fin.ext h0
    subst hk
    have hd : Work.Cohomology.delIdx (0 : Fin (N+2)) = (0 : Fin (N+1)) := by
      ext; simp [Work.Cohomology.delIdx]
    have hdel0 : (0 : Fin (N+1)) ∈ A := by rwa [hd] at hdel
    have h := faceA_zero_g A hB hdel0
    convert h
  · by_cases hlast : k.val = N+1
    · have hk : k = Fin.last (N+1) := Fin.ext (by rw [hlast, Fin.val_last])
      subst hk
      have hd : Work.Cohomology.delIdx (Fin.last (N+1)) = (Fin.last N) := by
        ext; simp [Work.Cohomology.delIdx]
      have hdelN : (Fin.last N) ∈ A := by rwa [hd] at hdel
      have h := faceA_last_g A hB hdelN
      convert h
    · have hmid : (⟨k.val - 1, by omega⟩ : Fin (N+1)) ∈ A := by
        rcases hcase with h | h | h
        · exact absurd h h0
        · exact absurd h hlast
        · exact h
      have hk1 : 1 ≤ k.val := by omega
      have hkN : k.val ≤ N := by omega
      let q : Fin N := ⟨k.val - 1, by omega⟩
      have hqval : q.val = k.val - 1 := rfl
      have hd : Work.Cohomology.delIdx k = q.succ := by
        ext
        simp only [Work.Cohomology.delIdx_val, Fin.val_succ]
        omega
      have hq : q.castSucc ∈ A := by
        have h1 : q.castSucc = (⟨k.val - 1, by omega⟩ : Fin (N+1)) := Fin.ext (by simp [q])
        rwa [h1]
      have hq' : q.succ ∈ A := by rwa [hd] at hdel
      have hkm : k = Fin.castSucc q.succ := by
        ext
        simp only [Fin.val_castSucc, Fin.val_succ]
        omega
      have hface := faceA_mid_g A hA hB q hq hq'
      have hac : SimplexCategory.δ k = SimplexCategory.δ (Fin.castSucc q.succ) := congrArg _ hkm
      have hac' : (SimplexCategory.δ k ≫ Work.Cohomology.shB A hB) =
          (SimplexCategory.δ (Fin.castSucc q.succ) ≫ Work.Cohomology.shB A hB) :=
        congrArg (fun f => f ≫ Work.Cohomology.shB A hB) hac
      refine (hac'.trans hface).trans ?_
      exact shB_congr_finset (by rw [hd]) _ _

/-- The sign identity on the `a`-side: the sign of the shuffle `A` changes by `(-1)^{k}` on
deleting the letter at `k` and by `(-1)^{cnt A k}` when the `cnt A k`-th face of `a` is taken. -/
lemma sgnA_face_gen {N : ℕ} (A : Finset (Fin (N+1))) (k : Fin (N+2))
    (hdel : Work.Cohomology.delIdx k ∈ A)
    (hcase : k.val = 0 ∨ k.val = N+1 ∨ (⟨k.val - 1, by omega⟩ : Fin (N+1)) ∈ A) :
    Work.Cohomology.sgnA A * (-1 : ℤ) ^ (k : ℕ)
      = Work.Cohomology.sgnA (Work.Cohomology.delPosP A (Work.Cohomology.delIdx k))
        * (-1 : ℤ) ^ (Work.Cohomology.cnt A k.val) := by
  by_cases h0 : k.val = 0
  · have hk : k = 0 := Fin.ext h0
    subst hk
    have hd : Work.Cohomology.delIdx (0 : Fin (N+2)) = (0 : Fin (N+1)) := by
      ext; simp [Work.Cohomology.delIdx]
    have hdel0 : (0 : Fin (N+1)) ∈ A := by rwa [hd] at hdel
    have h := sgnA_delPos_zero A
    rw [if_pos hdel0, mul_one] at h
    rw [h, hd]
    simp [Work.Cohomology.cnt]
  · by_cases hlast : k.val = N+1
    · have hk : k = Fin.last (N+1) := Fin.ext (by rw [hlast, Fin.val_last])
      subst hk
      have hd : Work.Cohomology.delIdx (Fin.last (N+1)) = (Fin.last N) := by
        ext; simp [Work.Cohomology.delIdx]
      have hdelN : (Fin.last N) ∈ A := by rwa [hd] at hdel
      have h := sgnA_delPos_last A
      rw [if_pos hdelN] at h
      rw [hd, show ((Fin.last (N+1) : Fin (N+2)) : ℕ) = N+1 from Fin.val_last _, h,
        Work.Cohomology.cnt_eq_card A (le_refl (N+1))]
    · have hmid : (⟨k.val - 1, by omega⟩ : Fin (N+1)) ∈ A := by
        rcases hcase with h | h | h
        · exact absurd h h0
        · exact absurd h hlast
        · exact h
      have hk1 : 1 ≤ k.val := by omega
      have hkN : k.val ≤ N := by omega
      let q : Fin N := ⟨k.val - 1, by omega⟩
      have hqval : q.val = k.val - 1 := rfl
      have hd : Work.Cohomology.delIdx k = q.succ := by
        ext
        simp only [Work.Cohomology.delIdx_val, Fin.val_succ]
        omega
      have hq : q.castSucc ∈ A := by
        have h1 : q.castSucc = (⟨k.val - 1, by omega⟩ : Fin (N+1)) := Fin.ext (by simp [q])
        rwa [h1]
      have hq' : q.succ ∈ A := by rwa [hd] at hdel
      have hqval2 : q.succ.val = k.val := by
        rw [Fin.val_succ, hqval]
        omega
      have hkval3 : (k : ℕ) = q.val + 1 := by rw [← hqval2, Fin.val_succ]
      have h := sgnA_delPos_succ A q hq hq'
      rw [hkval3, hd, h]

theorem aSide_Fsum (P Q : ℕ) (X Y : SSet.{0}) (a : X.obj (Opposite.op (SimplexCategory.mk (P+1)))) (b : Y.obj (Opposite.op (SimplexCategory.mk (Q+1)))) (x : Work.Cohomology.EZG.IdxA P Q) : Work.Cohomology.EZG.Fsum P Q X Y a b x.1 = Work.Cohomology.EZG.ezAsum P Q X Y a b (Work.Cohomology.EZG.aFwd P Q x) := by
  obtain ⟨⟨⟨A, hcard⟩, k⟩, hdel, hcase⟩ := x
  simp only [Work.Cohomology.EZG.Fsum, Work.Cohomology.EZG.ezAsum, Work.Cohomology.EZG.aFwd,
    Work.Cohomology.EZG.ezPair]
  congr 1
  · apply Prod.ext
    · dsimp only
      rw [Work.Cohomology.EZG.delta_map]
      rw [shA_face_gen A hcard k hdel hcase]
      rw [Work.Cohomology.EZG.map_delta_apply]
    · dsimp only
      rw [Work.Cohomology.EZG.delta_map]
      rw [shB_face_gen A (le_of_eq hcard) _ k hdel hcase]
  · have h := sgnA_face_gen A k hdel hcase
    have h2 : (Work.Cohomology.sgnA A : ℚ) * (-1 : ℚ) ^ (k : ℕ)
        = (Work.Cohomology.sgnA (Work.Cohomology.delPosP A (Work.Cohomology.delIdx k)) : ℚ)
          * (-1 : ℚ) ^ (Work.Cohomology.cnt A k.val) := by
      have h3 := congrArg (fun z : ℤ => (z : ℚ)) h
      push_cast at h3
      exact h3
    rw [h2, mul_comm]

end

end Work.Cohomology.EZG
