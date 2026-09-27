import Mathlib
import Submission.Work.Drive.FamBox.Defs
import Submission.Work.Drive.famMeetDefs
import Submission.Work.Drive.even_ncard_of_involution
import Submission.Work.Drive.ncard_eq_of_involution_swap

/-!
# The parity of the two end slices of the family box, from an even boundary meet count

This file proves `Work.Drive.FamBox.famMeet_parity_of_even_boxBMeet`: for the pair
`(famLoop L, famChain N)` of maps on the five-box `Amb 4 = ℝ⁵`, if the *boundary* meet set
`boxBMeet (famLoop L) (famChain N)` is finite and of even cardinality, and if every boundary meet
lies on exactly one face of the box (`hface`), then the two end slices
`famMeet L N 0`, `famMeet L N 1` (the meets with `p 0 = 0`, resp. `p 0 = 1`) have the same parity.

The argument is the combinatorial half of the boundary-counting engine of
`Submission/Work/Drive/odd_ncard_loopFamMeet_iff.lean`, in the `(5,4)` setting of this file; no
transversality or smoothness is needed, only the face decomposition.

Write `Z = boxBMeet (famLoop L) (famChain N)`.  The five coordinates of a point of `Z` are
`(t, s, x₀, x₁, x₂) = (p 0, p 1, p 2, p 3, p 4)`; `famLoop` reads only `(p 0, p 1)`, while `famChain`
reads only `(p 0, p 2, p 3, p 4)`.  By `hface` the meet set splits disjointly into the five pieces

* `A t = {b ∈ Z | b 0 = t}` for `t = 0, 1` — these are the two end slices `famMeet L N 0/1`;
* `Q c = {b ∈ Z | b 1 = c}` for `c = 0, 1` — paired by `hloop` (the involution `phaseSwap5`);
* `E = {b ∈ Z | onSeam (famT3 (b 2) (b 3) (b 4))}` — paired by `hseam` (the involution
  `seamSwap5`, which complements the coordinates `2` and `3`);

the faces `p 4 ∈ {0,1}` are empty by `havoid`.  Hence
`ncard Z = ncard A 0 + ncard A 1 + (even)` and, `Z` being even, `ncard A 0 + ncard A 1` is even, which
is the claim.

The gap "there is nothing on the fourth face" needs no separate piece: `havoid` is applied inside the
normal-form step, where the face index of `hface` is shown not to be `4`.
-/

namespace Work.Drive.FamBox

open Manifold Set Filter
open scoped Manifold ContDiff

/-- The **seam involution of the five-box**: it complements the coordinates `2` and `3` (the two seam
coordinates of the chain parameter `famT3 (p 2) (p 3) (p 4)`) and fixes the other three. -/
def seamSwap5 (p : Amb 4) : Amb 4 :=
  WithLp.toLp 2 fun i : Fin 5 => if i = 2 ∨ i = 3 then 1 - p i else p i

/-- The **phase involution of the five-box**: it complements the coordinate `1` (the loop parameter
`p 1`) and fixes the other four. -/
def phaseSwap5 (p : Amb 4) : Amb 4 :=
  WithLp.toLp 2 fun i : Fin 5 => if i = 1 then 1 - p i else p i

@[simp] lemma seamSwap5_involutive (p : Amb 4) : seamSwap5 (seamSwap5 p) = p := by
  ext i
  simp only [seamSwap5]
  by_cases h : i = 2 ∨ i = 3 <;> simp [h]

@[simp] lemma phaseSwap5_involutive (p : Amb 4) : phaseSwap5 (phaseSwap5 p) = p := by
  ext i
  simp only [phaseSwap5]
  by_cases h : i = 1 <;> simp [h]

lemma seamSwap5_mem_unitBox {p : Amb 4} (hp : p ∈ Submission.Drive.unitBox 4) :
    seamSwap5 p ∈ Submission.Drive.unitBox 4 := by
  intro i
  have hpi : p i ∈ Set.Icc (0 : ℝ) 1 := hp i
  by_cases h : i = 2 ∨ i = 3
  · have h1 : seamSwap5 p i = 1 - p i := by simp [seamSwap5, h]
    rw [h1]
    exact ⟨by linarith [hpi.2], by linarith [hpi.1]⟩
  · have h1 : seamSwap5 p i = p i := by simp [seamSwap5, h]
    rw [h1]; exact hpi

lemma phaseSwap5_mem_unitBox {p : Amb 4} (hp : p ∈ Submission.Drive.unitBox 4) :
    phaseSwap5 p ∈ Submission.Drive.unitBox 4 := by
  intro i
  have hpi : p i ∈ Set.Icc (0 : ℝ) 1 := hp i
  by_cases h : i = 1
  · have h1 : phaseSwap5 p i = 1 - p i := by simp [phaseSwap5, h]
    rw [h1]
    exact ⟨by linarith [hpi.2], by linarith [hpi.1]⟩
  · have h1 : phaseSwap5 p i = p i := by simp [phaseSwap5, h]
    rw [h1]; exact hpi

/-- The **seam predicate** of the five-box in coordinates: the chain argument `(p 2, p 3, p 4)` is on
the seam exactly when one of the first two coordinates is `0` or `1`. -/
lemma onSeam_famT3_iff (b : Amb 4) :
    Work.Drive.onSeam (Work.Drive.famT3 (b 2) (b 3) (b 4)) ↔
      (b 2 = 0 ∨ b 2 = 1 ∨ b 3 = 0 ∨ b 3 = 1) := by
  simp [Work.Drive.onSeam, Work.Drive.famT3]

lemma famLoop_seamSwap5 {M : Type*} [TopologicalSpace M]
    (L : EuclideanSpace ℝ (Fin 2) → M) (p : Amb 4) :
    Work.Drive.famLoop L (seamSwap5 p) = Work.Drive.famLoop L p := rfl

lemma famLoop_phaseSwap5 {M : Type*} [TopologicalSpace M]
    (L : EuclideanSpace ℝ (Fin 2) → M) (p : Amb 4) :
    Work.Drive.famLoop L (phaseSwap5 p) = L (Work.Drive.mk2 (p 0) (1 - p 1)) := rfl

lemma famChain_phaseSwap5 {M : Type*} [TopologicalSpace M]
    (N : EuclideanSpace ℝ (Fin 4) → M) (p : Amb 4) :
    Work.Drive.famChain N (phaseSwap5 p) = Work.Drive.famChain N p := rfl

/-- The `famChain` interface of the seam involution: on the seam, `seamSwap5` does not change the
chain side. -/
lemma famChain_seamSwap5 {M : Type*} [TopologicalSpace M]
    (N : EuclideanSpace ℝ (Fin 4) → M) (p : Amb 4)
    (hs : Work.Drive.onSeam (Work.Drive.famT3 (p 2) (p 3) (p 4)))
    (hseam : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)), Work.Drive.onSeam x →
      N (Work.Drive.famPt t (Work.Drive.seamInv x)) = N (Work.Drive.famPt t x)) :
    Work.Drive.famChain N (seamSwap5 p) = Work.Drive.famChain N p := by
  have h0 : (seamSwap5 p) 0 = p 0 := by simp [seamSwap5]
  have h2 : (seamSwap5 p) 2 = 1 - p 2 := by simp [seamSwap5]
  have h3 : (seamSwap5 p) 3 = 1 - p 3 := by simp [seamSwap5]
  have h4 : (seamSwap5 p) 4 = p 4 := by simp [seamSwap5]
  have hhem := hseam (p 0) (Work.Drive.famT3 (p 2) (p 3) (p 4)) hs
  rw [show Work.Drive.seamInv (Work.Drive.famT3 (p 2) (p 3) (p 4))
      = Work.Drive.famT3 (1 - p 2) (1 - p 3) (p 4) from by
        ext i; fin_cases i <;> simp [Work.Drive.seamInv, Work.Drive.famT3]] at hhem
  simp only [Work.Drive.famChain, h0, h2, h3, h4]
  exact hhem

theorem famMeet_parity_of_even_boxBMeet {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (L : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 4) → M)
    (hloop : ∀ t ∈ Set.Icc (0 : ℝ) 1, L (Work.Drive.mk2 t 0) = L (Work.Drive.mk2 t 1))
    (hseam : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)), Work.Drive.onSeam x →
      N (Work.Drive.famPt t (Work.Drive.seamInv x)) = N (Work.Drive.famPt t x))
    (havoid : ∀ p : EuclideanSpace ℝ (Fin 5), p ∈ Submission.Drive.unitBox 4 →
      Work.Drive.famLoop L p = Work.Drive.famChain N p → (p 4 = 0 ∨ p 4 = 1) → False)
    (hfin : (Work.Drive.FamBox.boxBMeet (Work.Drive.famLoop L) (Work.Drive.famChain N)).Finite)
    (heven : Even (Work.Drive.FamBox.boxBMeet (Work.Drive.famLoop L) (Work.Drive.famChain N)).ncard)
    (hface : ∀ b ∈ Work.Drive.FamBox.boxBMeet (Work.Drive.famLoop L) (Work.Drive.famChain N),
      ∃ i : Fin 5, (b i = 0 ∨ b i = 1) ∧ (∀ j : Fin 5, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1)) :
    Odd ((Work.Drive.famMeet L N 0).ncard) ↔ Odd ((Work.Drive.famMeet L N 1).ncard) := by
  classical
  set Z : Set (Amb 4) := boxBMeet (famLoop L) (famChain N) with hZ
  have hZfin : Z.Finite := by rw [hZ]; exact hfin
  have hZeven : Even Z.ncard := by rw [hZ]; exact heven
  -- the pieces
  let A : ℝ → Set (Amb 4) := fun t => {b | b ∈ Z ∧ b 0 = t}
  let Q : ℝ → Set (Amb 4) := fun c => {b | b ∈ Z ∧ b 1 = c}
  let E : Set (Amb 4) := {b | b ∈ Z ∧ onSeam (famT3 (b 2) (b 3) (b 4))}
  have hAfin : ∀ t : ℝ, (A t).Finite := fun t => hZfin.subset fun b hb => hb.1
  have hQfin : ∀ c : ℝ, (Q c).Finite := fun c => hZfin.subset fun b hb => hb.1
  have hEfin : E.Finite := hZfin.subset fun b hb => hb.1
  -- the two directions of the identification with `boxBMeet`
  have hmemZ : ∀ {b : Amb 4}, b ∈ Z → b ∈ boxBMeet (famLoop L) (famChain N) :=
    fun hb => by rw [hZ] at hb; exact hb
  have hmemZ' : ∀ {b : Amb 4}, b ∈ boxBMeet (famLoop L) (famChain N) → b ∈ Z :=
    fun hb => by rw [hZ]; exact hb
  -- ## the normal form of a boundary meet
  have hnf : ∀ b ∈ Z,
      ((b 0 = 0 ∨ b 0 = 1) ∧ (∀ j : Fin 5, j ≠ 0 → b j ∈ Set.Ioo (0 : ℝ) 1)) ∨
      ((b 1 = 0 ∨ b 1 = 1) ∧ (∀ j : Fin 5, j ≠ 1 → b j ∈ Set.Ioo (0 : ℝ) 1)) ∨
      (onSeam (famT3 (b 2) (b 3) (b 4)) ∧ b 0 ∈ Set.Ioo (0 : ℝ) 1 ∧
        b 1 ∈ Set.Ioo (0 : ℝ) 1) := by
    intro b hb
    obtain ⟨hbox, hmeet, hbdry⟩ :=
      (mem_boxBMeet (F := famLoop L) (G := famChain N)).mp (hmemZ hb)
    obtain ⟨i, hi, hint⟩ := hface b (hmemZ hb)
    fin_cases i
    · exact Or.inl ⟨hi, fun j hj => hint j hj⟩
    · exact Or.inr (Or.inl ⟨hi, fun j hj => hint j hj⟩)
    · refine Or.inr (Or.inr ⟨?_, hint 0 (by decide), hint 1 (by decide)⟩)
      rcases hi with h | h
      · exact Or.inl (by simpa [famT3] using h)
      · exact Or.inr (Or.inl (by simpa [famT3] using h))
    · refine Or.inr (Or.inr ⟨?_, hint 0 (by decide), hint 1 (by decide)⟩)
      rcases hi with h | h
      · exact Or.inr (Or.inr (Or.inl (by simpa [famT3] using h)))
      · exact Or.inr (Or.inr (Or.inr (by simpa [famT3] using h)))
    · exact (havoid b hbox hmeet hi).elim
  -- ## `E` carries no point with two of the first coordinates interior
  have onSeam_not_Ioo : ∀ b : Amb 4, onSeam (famT3 (b 2) (b 3) (b 4)) →
      b 2 ∈ Set.Ioo (0 : ℝ) 1 → b 3 ∈ Set.Ioo (0 : ℝ) 1 → False := by
    intro b hs h2 h3
    rcases hs with h | h | h | h
    · have h' : b 2 = 0 := by simpa [famT3] using h
      linarith [h2.1, h']
    · have h' : b 2 = 1 := by simpa [famT3] using h
      linarith [h2.2, h']
    · have h' : b 3 = 0 := by simpa [famT3] using h
      linarith [h3.1, h']
    · have h' : b 3 = 1 := by simpa [famT3] using h
      linarith [h3.2, h']
  -- ## the pieces cover `Z`
  have hcoverOr : ∀ b : Amb 4, b ∈ Z ↔ b ∈ A 0 ∨ b ∈ A 1 ∨ b ∈ Q 0 ∨ b ∈ Q 1 ∨ b ∈ E := by
    intro b
    constructor
    · intro hb
      rcases hnf b hb with ⟨h0, -⟩ | ⟨h1, -⟩ | ⟨hs, -⟩
      · rcases h0 with h0 | h0
        · exact Or.inl ⟨hb, h0⟩
        · exact Or.inr (Or.inl ⟨hb, h0⟩)
      · rcases h1 with h1 | h1
        · exact Or.inr (Or.inr (Or.inl ⟨hb, h1⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, h1⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hb, hs⟩)))
    · intro h
      rcases h with h | h | h | h | h <;> exact h.1
  have hcover : Z = A 0 ∪ A 1 ∪ Q 0 ∪ Q 1 ∪ E := by
    ext b
    rw [hcoverOr b]
    simp only [Set.mem_union]
    tauto
  -- ## pairwise disjointness of the pieces
  have hdisj_A01 : Disjoint (A 0) (A 1) := by
    rw [Set.disjoint_left]
    rintro b ⟨-, h0⟩ ⟨-, h1⟩
    linarith
  have hdisj_Q01 : Disjoint (Q 0) (Q 1) := by
    rw [Set.disjoint_left]
    rintro b ⟨-, h0⟩ ⟨-, h1⟩
    linarith
  have hdisj_AQ : ∀ {t c : ℝ}, (t = 0 ∨ t = 1) → (c = 0 ∨ c = 1) →
      Disjoint (A t) (Q c) := by
    intro t c ht hc
    rw [Set.disjoint_left]
    rintro b ⟨hZb, hbt⟩ ⟨-, hbc⟩
    rcases hnf b hZb with ⟨-, hrest⟩ | ⟨-, hrest⟩ | ⟨-, h0, -⟩
    · obtain ⟨hl, hr⟩ := hrest 1 (by decide)
      rcases hc with hc | hc <;> linarith
    · obtain ⟨hl, hr⟩ := hrest 0 (by decide)
      rcases ht with ht | ht <;> linarith
    · obtain ⟨h0l, h0r⟩ := h0
      rcases ht with ht | ht <;> linarith
  have hdisj_AE : ∀ {t : ℝ}, (t = 0 ∨ t = 1) → Disjoint (A t) E := by
    intro t ht
    rw [Set.disjoint_left]
    rintro b ⟨hZb, hbt⟩ ⟨-, hs⟩
    rcases hnf b hZb with ⟨-, hrest⟩ | ⟨-, hrest⟩ | ⟨-, h0, -⟩
    · exact onSeam_not_Ioo b hs (hrest 2 (by decide)) (hrest 3 (by decide))
    · obtain ⟨hl, hr⟩ := hrest 0 (by decide)
      rcases ht with ht | ht <;> linarith
    · obtain ⟨h0l, h0r⟩ := h0
      rcases ht with ht | ht <;> linarith
  have hdisj_QE : ∀ {c : ℝ}, (c = 0 ∨ c = 1) → Disjoint (Q c) E := by
    intro c hc
    rw [Set.disjoint_left]
    rintro b ⟨hZb, hbc⟩ ⟨-, hs⟩
    rcases hnf b hZb with ⟨-, hrest⟩ | ⟨-, hrest⟩ | ⟨-, -, h1⟩
    · exact onSeam_not_Ioo b hs (hrest 2 (by decide)) (hrest 3 (by decide))
    · exact onSeam_not_Ioo b hs (hrest 2 (by decide)) (hrest 3 (by decide))
    · obtain ⟨h1l, h1r⟩ := h1
      rcases hc with hc | hc <;> linarith
  -- ## `E` is even: the seam involution
  have hEeven : Even E.ncard := by
    refine Work.Drive.even_ncard_of_involution hEfin seamSwap5 ?_ ?_ ?_
    · intro b hb
      obtain ⟨hZb, hs⟩ := hb
      obtain ⟨hbox, hmeet, -⟩ :=
        (mem_boxBMeet (F := famLoop L) (G := famChain N)).mp (hmemZ hZb)
      have hs01 : b 2 = 0 ∨ b 2 = 1 ∨ b 3 = 0 ∨ b 3 = 1 := (onSeam_famT3_iff b).mp hs
      have hbox' : seamSwap5 b ∈ Submission.Drive.unitBox 4 := seamSwap5_mem_unitBox hbox
      have hmeet' : famLoop L (seamSwap5 b) = famChain N (seamSwap5 b) := by
        rw [famLoop_seamSwap5 L b, famChain_seamSwap5 N b hs hseam]
        exact hmeet
      have hbdry' : seamSwap5 b ∈ Submission.Drive.unitBoxBdry 4 := by
        refine ⟨hbox', ?_⟩
        rcases hs01 with h | h | h | h
        · exact ⟨2, Or.inr (by simp [seamSwap5, h])⟩
        · exact ⟨2, Or.inl (by simp [seamSwap5, h])⟩
        · exact ⟨3, Or.inr (by simp [seamSwap5, h])⟩
        · exact ⟨3, Or.inl (by simp [seamSwap5, h])⟩
      have hs' : onSeam (famT3 ((seamSwap5 b) 2) ((seamSwap5 b) 3) ((seamSwap5 b) 4)) := by
        rw [onSeam_famT3_iff]
        rcases hs01 with h | h | h | h
        · exact Or.inr (Or.inl (by simp [seamSwap5, h]))
        · exact Or.inl (by simp [seamSwap5, h])
        · exact Or.inr (Or.inr (Or.inr (by simp [seamSwap5, h])))
        · exact Or.inr (Or.inr (Or.inl (by simp [seamSwap5, h])))
      exact ⟨hmemZ' ⟨hbox', hmeet', hbdry'⟩, hs'⟩
    · intro b _
      exact seamSwap5_involutive b
    · intro b hb
      obtain ⟨-, hs⟩ := hb
      intro heq
      have hs01 : b 2 = 0 ∨ b 2 = 1 ∨ b 3 = 0 ∨ b 3 = 1 := (onSeam_famT3_iff b).mp hs
      have c2 : (seamSwap5 b) 2 = b 2 := congrArg (fun p : Amb 4 => p 2) heq
      have c3 : (seamSwap5 b) 3 = b 3 := congrArg (fun p : Amb 4 => p 3) heq
      rw [show (seamSwap5 b) 2 = 1 - b 2 from by simp [seamSwap5]] at c2
      rw [show (seamSwap5 b) 3 = 1 - b 3 from by simp [seamSwap5]] at c3
      rcases hs01 with h | h | h | h <;> linarith
  -- ## the two `p 1`-faces are swapped by `hloop`
  have hQeq : (Q 0).ncard = (Q 1).ncard := by
    have hsQ1 : ∀ b : Amb 4, b ∈ Q 0 → phaseSwap5 b ∈ Q 1 := by
      rintro b ⟨hZb, hb1⟩
      obtain ⟨hbox, hmeet, -⟩ :=
        (mem_boxBMeet (F := famLoop L) (G := famChain N)).mp (hmemZ hZb)
      have hp := hloop (b 0) (hbox 0)
      have hbox' : phaseSwap5 b ∈ Submission.Drive.unitBox 4 := phaseSwap5_mem_unitBox hbox
      have hmeet' : famLoop L (phaseSwap5 b) = famChain N (phaseSwap5 b) := by
        calc famLoop L (phaseSwap5 b) = L (mk2 (b 0) (1 - b 1)) := famLoop_phaseSwap5 L b
          _ = L (mk2 (b 0) 1) := by simp [hb1]
          _ = L (mk2 (b 0) 0) := hp.symm
          _ = famLoop L b := by
                simp only [Work.Drive.famLoop]; rw [hb1]
          _ = famChain N b := hmeet
          _ = famChain N (phaseSwap5 b) := (famChain_phaseSwap5 N b).symm
      have hone : (phaseSwap5 b) 1 = 1 := by
        rw [show (phaseSwap5 b) 1 = 1 - b 1 from by simp [phaseSwap5], hb1]; norm_num
      exact ⟨hmemZ' ⟨hbox', hmeet', ⟨hbox', ⟨1, Or.inr hone⟩⟩⟩, hone⟩
    have hsQ0 : ∀ b : Amb 4, b ∈ Q 1 → phaseSwap5 b ∈ Q 0 := by
      rintro b ⟨hZb, hb1⟩
      obtain ⟨hbox, hmeet, -⟩ :=
        (mem_boxBMeet (F := famLoop L) (G := famChain N)).mp (hmemZ hZb)
      have hp := hloop (b 0) (hbox 0)
      have hbox' : phaseSwap5 b ∈ Submission.Drive.unitBox 4 := phaseSwap5_mem_unitBox hbox
      have hmeet' : famLoop L (phaseSwap5 b) = famChain N (phaseSwap5 b) := by
        calc famLoop L (phaseSwap5 b) = L (mk2 (b 0) (1 - b 1)) := famLoop_phaseSwap5 L b
          _ = L (mk2 (b 0) 0) := by simp [hb1]
          _ = L (mk2 (b 0) 1) := hp
          _ = famLoop L b := by
                simp only [Work.Drive.famLoop]; rw [hb1]
          _ = famChain N b := hmeet
          _ = famChain N (phaseSwap5 b) := (famChain_phaseSwap5 N b).symm
      have hone : (phaseSwap5 b) 1 = 0 := by
        rw [show (phaseSwap5 b) 1 = 1 - b 1 from by simp [phaseSwap5], hb1]; norm_num
      exact ⟨hmemZ' ⟨hbox', hmeet', ⟨hbox', ⟨1, Or.inl hone⟩⟩⟩, hone⟩
    refine Work.Drive.ncard_eq_of_involution_swap ((hQfin 0).union (hQfin 1)) phaseSwap5
      ?_ ?_ hdisj_Q01 rfl ?_ ?_
    · intro b hb
      rcases hb with hb | hb
      · exact Or.inr (hsQ1 b hb)
      · exact Or.inl (hsQ0 b hb)
    · intro b _
      exact phaseSwap5_involutive b
    · intro b hb
      exact hsQ1 b hb
    · intro b hb
      exact hsQ0 b hb
  have hQeven : Even ((Q 0).ncard + (Q 1).ncard) := by
    rw [hQeq]
    exact ⟨(Q 1).ncard, rfl⟩
  -- ## the cardinality bookkeeping
  have hd_A0E : Disjoint (A 0) E := hdisj_AE (Or.inl rfl)
  have hd_A1E : Disjoint (A 1) E := hdisj_AE (Or.inr rfl)
  have hd_Q0E : Disjoint (Q 0) E := hdisj_QE (Or.inl rfl)
  have hd_Q1E : Disjoint (Q 1) E := hdisj_QE (Or.inr rfl)
  have hd_A0Q0 : Disjoint (A 0) (Q 0) := hdisj_AQ (Or.inl rfl) (Or.inl rfl)
  have hd_A0Q1 : Disjoint (A 0) (Q 1) := hdisj_AQ (Or.inl rfl) (Or.inr rfl)
  have hd_A1Q0 : Disjoint (A 1) (Q 0) := hdisj_AQ (Or.inr rfl) (Or.inl rfl)
  have hd_A1Q1 : Disjoint (A 1) (Q 1) := hdisj_AQ (Or.inr rfl) (Or.inr rfl)
  have hd1 : Disjoint (A 0 ∪ A 1) (Q 0) := hd_A0Q0.union_left hd_A1Q0
  have hd2 : Disjoint (A 0 ∪ A 1) (Q 1) := hd_A0Q1.union_left hd_A1Q1
  have hd3 : Disjoint (A 0 ∪ A 1 ∪ Q 0) (Q 1) := hd2.union_left hdisj_Q01
  have hd4 : Disjoint (A 0 ∪ A 1) E := hd_A0E.union_left hd_A1E
  have hd5 : Disjoint (A 0 ∪ A 1 ∪ Q 0) E := hd4.union_left hd_Q0E
  have hd6 : Disjoint (A 0 ∪ A 1 ∪ Q 0 ∪ Q 1) E := hd5.union_left hd_Q1E
  have hsum1 : (A 0 ∪ A 1 ∪ Q 0 ∪ Q 1 ∪ E).ncard =
      (A 0 ∪ A 1 ∪ Q 0 ∪ Q 1).ncard + E.ncard :=
    Set.ncard_union_eq hd6 ((((hAfin 0).union (hAfin 1)).union (hQfin 0)).union (hQfin 1)) hEfin
  have hsum2 : (A 0 ∪ A 1 ∪ Q 0 ∪ Q 1).ncard = (A 0 ∪ A 1 ∪ Q 0).ncard + (Q 1).ncard :=
    Set.ncard_union_eq hd3 (((hAfin 0).union (hAfin 1)).union (hQfin 0)) (hQfin 1)
  have hsum3 : (A 0 ∪ A 1 ∪ Q 0).ncard = (A 0 ∪ A 1).ncard + (Q 0).ncard :=
    Set.ncard_union_eq hd1 ((hAfin 0).union (hAfin 1)) (hQfin 0)
  have hsum4 : (A 0 ∪ A 1).ncard = (A 0).ncard + (A 1).ncard :=
    Set.ncard_union_eq hdisj_A01 (hAfin 0) (hAfin 1)
  have hZsum : Z.ncard = (A 0).ncard + (A 1).ncard + (Q 0).ncard + (Q 1).ncard + E.ncard := by
    rw [hcover, hsum1, hsum2, hsum3, hsum4]
  -- ## parity arithmetic
  have hsumEven : Even ((A 0).ncard + (A 1).ncard + (Q 0).ncard + (Q 1).ncard + E.ncard) := by
    rw [← hZsum]; exact hZeven
  have hmain : Even (((A 0).ncard + (A 1).ncard) + (((Q 0).ncard + (Q 1).ncard) + E.ncard)) := by
    rw [show ((A 0).ncard + (A 1).ncard) + (((Q 0).ncard + (Q 1).ncard) + E.ncard)
        = (A 0).ncard + (A 1).ncard + (Q 0).ncard + (Q 1).ncard + E.ncard from by ring]
    exact hsumEven
  have hAeven : Even ((A 0).ncard + (A 1).ncard) := by
    have hy : Even (((Q 0).ncard + (Q 1).ncard) + E.ncard) := hQeven.add hEeven
    rw [Nat.even_add] at hmain
    exact hmain.mpr hy
  have hgoal : Odd ((A 0).ncard) ↔ Odd ((A 1).ncard) := Nat.even_add'.mp hAeven
  -- ## the two `p 0`-faces are the two end slices
  have hA0 : A 0 = famMeet L N 0 := by
    ext b
    constructor
    · rintro ⟨hZb, h0⟩
      obtain ⟨hbox, hmeet, -⟩ :=
        (mem_boxBMeet (F := famLoop L) (G := famChain N)).mp (hmemZ hZb)
      exact ⟨hbox, h0, hmeet⟩
    · rintro ⟨hbox, h0, hmeet⟩
      exact ⟨hmemZ' ⟨hbox, hmeet, ⟨hbox, ⟨0, Or.inl h0⟩⟩⟩, h0⟩
  have hA1 : A 1 = famMeet L N 1 := by
    ext b
    constructor
    · rintro ⟨hZb, h1⟩
      obtain ⟨hbox, hmeet, -⟩ :=
        (mem_boxBMeet (F := famLoop L) (G := famChain N)).mp (hmemZ hZb)
      exact ⟨hbox, h1, hmeet⟩
    · rintro ⟨hbox, h1, hmeet⟩
      exact ⟨hmemZ' ⟨hbox, hmeet, ⟨hbox, ⟨0, Or.inr h1⟩⟩⟩, h1⟩
  rw [← hA0, ← hA1]
  exact hgoal

end Work.Drive.FamBox
