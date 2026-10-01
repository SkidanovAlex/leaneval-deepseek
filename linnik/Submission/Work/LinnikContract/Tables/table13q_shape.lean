import Mathlib
import Submission.Work.LinnikContract.Pre

namespace Work.LinnikContract.Tables

set_option maxHeartbeats 1000000

/- Shape of HB Table 13 (as the explicit rational data `table13q`, entries `(λ, λ₁, N₀)`): every
entry has `λ ∈ [0.8, 1.325]`, `λ₁ ∈ [0.348, 0.58]` and `N₀ > 0`; and within each fixed `λ₁`-column,
`N₀` is non-decreasing in `λ` (the monotonicity used when the density bound is summed over the
layers `Λ_r = Λ - 0.025 r`). -/

/- The table splits into its five `λ₁`-columns, recorded here as explicit `(λ, N₀)` pair lists
`colA … colE`.  Each is an `IsChain` of `R a b := a.1 < b.1 ∧ a.2 ≤ b.2` (checked by `norm_num`),
and the general induction `R_mono` turns such a chain into the monotonicity statement.  The
lemmas `mem_colX` place every table entry in its column by `fin_cases`/`norm_num`. -/

/-- The `λ₁ = (348:ℚ)/1000` column of `table13q`, as `(λ, N₀)` pairs. -/
def colA : List (ℚ × ℕ) :=
  [((8:ℚ)/10, 8),
   ((825:ℚ)/1000, 9),
   ((85:ℚ)/100, 10),
   ((875:ℚ)/1000, 11),
   ((9:ℚ)/10, 12),
   ((925:ℚ)/1000, 13),
   ((95:ℚ)/100, 15),
   ((975:ℚ)/1000, 16),
   (1, 18),
   ((1025:ℚ)/1000, 21),
   ((105:ℚ)/100, 24),
   ((1075:ℚ)/1000, 28),
   ((11:ℚ)/10, 34),
   ((1125:ℚ)/1000, 42),
   ((115:ℚ)/100, 54),
   ((1175:ℚ)/1000, 73),
   ((12:ℚ)/10, 111),
   ((1225:ℚ)/1000, 218),
   ((125:ℚ)/100, 2583)]

/-- The `λ₁ = (4:ℚ)/10` column of `table13q`, as `(λ, N₀)` pairs. -/
def colB : List (ℚ × ℕ) :=
  [((8:ℚ)/10, 8),
   ((825:ℚ)/1000, 9),
   ((85:ℚ)/100, 9),
   ((875:ℚ)/1000, 10),
   ((9:ℚ)/10, 11),
   ((925:ℚ)/1000, 12),
   ((95:ℚ)/100, 14),
   ((975:ℚ)/1000, 15),
   (1, 17),
   ((1025:ℚ)/1000, 19),
   ((105:ℚ)/100, 22),
   ((1075:ℚ)/1000, 26),
   ((11:ℚ)/10, 30),
   ((1125:ℚ)/1000, 36),
   ((115:ℚ)/100, 45),
   ((1175:ℚ)/1000, 58),
   ((12:ℚ)/10, 81),
   ((1225:ℚ)/1000, 127),
   ((125:ℚ)/100, 279)]

/-- The `λ₁ = (44:ℚ)/100` column of `table13q`, as `(λ, N₀)` pairs. -/
def colC : List (ℚ × ℕ) :=
  [((8:ℚ)/10, 8),
   ((825:ℚ)/1000, 8),
   ((85:ℚ)/100, 9),
   ((875:ℚ)/1000, 10),
   ((9:ℚ)/10, 11),
   ((925:ℚ)/1000, 12),
   ((95:ℚ)/100, 13),
   ((975:ℚ)/1000, 15),
   (1, 16),
   ((1025:ℚ)/1000, 18),
   ((105:ℚ)/100, 21),
   ((1075:ℚ)/1000, 24),
   ((11:ℚ)/10, 28),
   ((1125:ℚ)/1000, 33),
   ((115:ℚ)/100, 40),
   ((1175:ℚ)/1000, 51),
   ((12:ℚ)/10, 67),
   ((1225:ℚ)/1000, 97),
   ((125:ℚ)/100, 166),
   ((1275:ℚ)/1000, 520)]

/-- The `λ₁ = (5:ℚ)/10` column of `table13q`, as `(λ, N₀)` pairs. -/
def colD : List (ℚ × ℕ) :=
  [((8:ℚ)/10, 7),
   ((825:ℚ)/1000, 8),
   ((85:ℚ)/100, 9),
   ((875:ℚ)/1000, 9),
   ((9:ℚ)/10, 10),
   ((925:ℚ)/1000, 11),
   ((95:ℚ)/100, 12),
   ((975:ℚ)/1000, 14),
   (1, 15),
   ((1025:ℚ)/1000, 17),
   ((105:ℚ)/100, 19),
   ((1075:ℚ)/1000, 22),
   ((11:ℚ)/10, 25),
   ((1125:ℚ)/1000, 29),
   ((115:ℚ)/100, 35),
   ((1175:ℚ)/1000, 42),
   ((12:ℚ)/10, 54),
   ((1225:ℚ)/1000, 71),
   ((125:ℚ)/100, 104),
   ((1275:ℚ)/1000, 184),
   ((13:ℚ)/10, 667)]

/-- The `λ₁ = (58:ℚ)/100` column of `table13q`, as `(λ, N₀)` pairs. -/
def colE : List (ℚ × ℕ) :=
  [((8:ℚ)/10, 7),
   ((825:ℚ)/1000, 8),
   ((85:ℚ)/100, 8),
   ((875:ℚ)/1000, 9),
   ((9:ℚ)/10, 10),
   ((925:ℚ)/1000, 11),
   ((95:ℚ)/100, 12),
   ((975:ℚ)/1000, 13),
   (1, 14),
   ((1025:ℚ)/1000, 15),
   ((105:ℚ)/100, 17),
   ((1075:ℚ)/1000, 19),
   ((11:ℚ)/10, 22),
   ((1125:ℚ)/1000, 25),
   ((115:ℚ)/100, 29),
   ((1175:ℚ)/1000, 35),
   ((12:ℚ)/10, 42),
   ((1225:ℚ)/1000, 53),
   ((125:ℚ)/100, 70),
   ((1275:ℚ)/1000, 100),
   ((13:ℚ)/10, 167),
   ((1325:ℚ)/1000, 460)]

def R : ℚ × ℕ → ℚ × ℕ → Prop := fun a b => a.1 < b.1 ∧ a.2 ≤ b.2

/-- Every `b` in the tail of an `IsChain R`-list headed by `x` exceeds `x` in both coordinates
(first strictly, second non-strictly). -/
lemma head_min : ∀ (x : ℚ × ℕ) (l : List (ℚ × ℕ)), List.IsChain R (x :: l) →
    ∀ b ∈ l, x.1 < b.1 ∧ x.2 ≤ b.2 := by
  intro x l
  induction l generalizing x with
  | nil => intro _ b hb; simp at hb
  | cons y ys ih =>
      intro h b hb
      rw [List.isChain_cons_cons] at h
      obtain ⟨hxy, hrest⟩ := h
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hxy
      · obtain ⟨h1, h2⟩ := ih y hrest b hb'
        exact ⟨hxy.1.trans h1, hxy.2.trans h2⟩

/-- Monotonicity of an `IsChain R`-list: comparable first coordinates give comparable second
coordinates. -/
lemma R_mono : ∀ (l : List (ℚ × ℕ)), List.IsChain R l →
    ∀ a ∈ l, ∀ b ∈ l, a.1 ≤ b.1 → a.2 ≤ b.2 := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x xs ih =>
      intro h a ha b hb hab
      have hhead := head_min x xs h
      rcases List.mem_cons.mp ha with rfl | ha'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact le_refl _
        · exact (hhead b hb').2
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd hab (not_le_of_gt (hhead a ha').1)
        · exact ih h.of_cons a ha' b hb' hab


lemma colA_chain : List.IsChain R colA := by
  simp only [colA, R, List.isChain_cons_cons, List.isChain_singleton]
  norm_num

lemma colA_mono : ∀ a ∈ colA, ∀ b ∈ colA, a.1 ≤ b.1 → a.2 ≤ b.2 :=
  R_mono colA colA_chain

lemma mem_colA : ∀ e ∈ table13q, e.2.1 = (348:ℚ)/1000 → (e.1, e.2.2) ∈ colA := by
  intro e he h
  fin_cases he <;> norm_num at h <;> simp [colA]

lemma colB_chain : List.IsChain R colB := by
  simp only [colB, R, List.isChain_cons_cons, List.isChain_singleton]
  norm_num

lemma colB_mono : ∀ a ∈ colB, ∀ b ∈ colB, a.1 ≤ b.1 → a.2 ≤ b.2 :=
  R_mono colB colB_chain

lemma mem_colB : ∀ e ∈ table13q, e.2.1 = (4:ℚ)/10 → (e.1, e.2.2) ∈ colB := by
  intro e he h
  fin_cases he <;> norm_num at h <;> simp [colB]

lemma colC_chain : List.IsChain R colC := by
  simp only [colC, R, List.isChain_cons_cons, List.isChain_singleton]
  norm_num

lemma colC_mono : ∀ a ∈ colC, ∀ b ∈ colC, a.1 ≤ b.1 → a.2 ≤ b.2 :=
  R_mono colC colC_chain

lemma mem_colC : ∀ e ∈ table13q, e.2.1 = (44:ℚ)/100 → (e.1, e.2.2) ∈ colC := by
  intro e he h
  fin_cases he <;> norm_num at h <;> simp [colC]

lemma colD_chain : List.IsChain R colD := by
  simp only [colD, R, List.isChain_cons_cons, List.isChain_singleton]
  norm_num

lemma colD_mono : ∀ a ∈ colD, ∀ b ∈ colD, a.1 ≤ b.1 → a.2 ≤ b.2 :=
  R_mono colD colD_chain

lemma mem_colD : ∀ e ∈ table13q, e.2.1 = (5:ℚ)/10 → (e.1, e.2.2) ∈ colD := by
  intro e he h
  fin_cases he <;> norm_num at h <;> simp [colD]

lemma colE_chain : List.IsChain R colE := by
  simp only [colE, R, List.isChain_cons_cons, List.isChain_singleton]
  norm_num

lemma colE_mono : ∀ a ∈ colE, ∀ b ∈ colE, a.1 ≤ b.1 → a.2 ≤ b.2 :=
  R_mono colE colE_chain

lemma mem_colE : ∀ e ∈ table13q, e.2.1 = (58:ℚ)/100 → (e.1, e.2.2) ∈ colE := by
  intro e he h
  fin_cases he <;> norm_num at h <;> simp [colE]

/- Shape of HB Table 13. -/
theorem table13q_shape :
    (∀ e ∈ Work.LinnikContract.table13q, (348:ℚ)/1000 ≤ e.2.1 ∧ e.2.1 ≤ (58:ℚ)/100 ∧
      (8:ℚ)/10 ≤ e.1 ∧ e.1 ≤ (1325:ℚ)/1000 ∧ 0 < e.2.2) ∧
    (∀ e ∈ Work.LinnikContract.table13q, ∀ e' ∈ Work.LinnikContract.table13q,
      e.2.1 = e'.2.1 → e.1 ≤ e'.1 → e.2.2 ≤ e'.2.2) := by
  constructor
  · intro e he
    fin_cases he <;> norm_num
  · intro e he e' he' h1 h2
    have hcol : e.2.1 ∈ ([(348:ℚ)/1000, (4:ℚ)/10, (44:ℚ)/100, (5:ℚ)/10, (58:ℚ)/100] : List ℚ) := by
      fin_cases he <;> simp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcol
    rcases hcol with hc | hc | hc | hc | hc
    · exact colA_mono (e.1, e.2.2) (mem_colA e he hc) (e'.1, e'.2.2) (mem_colA e' he' (h1.symm.trans hc)) h2
    · exact colB_mono (e.1, e.2.2) (mem_colB e he hc) (e'.1, e'.2.2) (mem_colB e' he' (h1.symm.trans hc)) h2
    · exact colC_mono (e.1, e.2.2) (mem_colC e he hc) (e'.1, e'.2.2) (mem_colC e' he' (h1.symm.trans hc)) h2
    · exact colD_mono (e.1, e.2.2) (mem_colD e he hc) (e'.1, e'.2.2) (mem_colD e' he' (h1.symm.trans hc)) h2
    · exact colE_mono (e.1, e.2.2) (mem_colE e he hc) (e'.1, e'.2.2) (mem_colE e' he' (h1.symm.trans hc)) h2

end Work.LinnikContract.Tables
