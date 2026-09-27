import Mathlib
import Submission.Work.Drive.ppParity.Bdry
import Submission.Work.Drive.even_ncard_pairMeetBdry
import Submission.Work.Drive.even_ncard_of_involution

/-!
# The parity of the pair-meet counts at the two ends of the family

`Work.Drive.ppMeetBdry E E' V W` is the set of *pair meets* of the two plane chains `E`, `E'` with
the two sweep chains `V`, `W` that lie on the boundary of the `9`-box, and `Work.Drive.ppMeetEnd` is
the part of the meet set at a fixed family parameter.  The box-parity engine
(`Work.Drive.even_ncard_ppMeetBdry`, proved in `Drive/even_ncard_ppMeetBdry.lean`) produces the
evenness of the whole boundary count; this file performs the **bookkeeping** that splits that count
into the two end faces `s = 0, 1` and the *seam* faces, and shows that the seam part is even.

The seam part is the set of boundary meets with `ftS x ∉ {0,1}`.  By the face hypothesis every such
meet lies on exactly one face coordinate `i`, all other coordinates being strictly interior.  The
two level coordinates `5` and `8` are excluded by `havY`/`havZ`, so `i ∈ {1,2,3,4,6,7}`, and the
antipodal involution of the corresponding parameter square (or cube) — `seamInv2` on `u`, `seamInv`
on `y` resp. `z` — maps the meet set to itself (hypotheses `hseamU`/`hseamU'`/`hseamV`/`hseamW`),
fixes the unique face coordinate, and is a fixed-point-free involution.  Hence the seam part has an
even number of points and `K 0 + K 1` is even.

The involution is the three-way composite of the involutions, selected by the (unique) face
coordinate of the point: `ppInv`.
-/

namespace Work.Drive

open Submission.Drive

noncomputable section

namespace PPE

open Work.Drive.PMB

variable {M : Type*} [TopologicalSpace M] [T2Space M]

/-! ## 1. Coordinates -/

lemma mem_ppMeet_iff {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M} {x : Amb 8} :
    x ∈ ppMeet E E' V W ↔ x ∈ unitBox 8 ∧ E (ftS x) (ftU x) = V (ftY x) ∧
      E' (ftS x) (ftU x) = W (ftZ x) := Iff.rfl

lemma one_sub_mem_Ioo {c : ℝ} (h : c ∈ Set.Ioo (0 : ℝ) 1) :
    1 - c ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨by linarith [h.2], by linarith [h.1]⟩

lemma uInv_apply_other (x : Amb 8) {j : Fin 9} (h1 : j ≠ 1) (h2 : j ≠ 2) :
    uInv x j = x j := by
  fin_cases j <;> simp_all [uInv, mk9, ftS, ftU, ftY, ftZ, WithLp.ofLp_toLp]

lemma yInv_apply_other (x : Amb 8) {j : Fin 9} (h1 : j ≠ 3) (h2 : j ≠ 4) :
    yInv x j = x j := by
  fin_cases j <;> simp_all [yInv, mk9, ftS, ftU, ftY, ftZ, seamInv_apply_two, WithLp.ofLp_toLp]

lemma zInv_apply_other (x : Amb 8) {j : Fin 9} (h1 : j ≠ 6) (h2 : j ≠ 7) :
    zInv x j = x j := by
  fin_cases j <;> simp_all [zInv, mk9, ftS, ftU, ftY, ftZ, seamInv_apply_two, WithLp.ofLp_toLp]

/-! ## 2. The face-coordinate predicate -/

/-- `x` lies on exactly the face `i` of the `9`-box: the coordinate `i` is `0` or `1` and every
other coordinate is strictly between `0` and `1`. -/
def FaceCoord (x : Amb 8) (i : Fin 9) : Prop :=
  (x i = 0 ∨ x i = 1) ∧ ∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1

lemma faceCoord_unique {x : Amb 8} {i i' : Fin 9} (h : FaceCoord x i) (h' : FaceCoord x i') :
    i = i' := by
  by_contra hne
  have hne' : i' ≠ i := fun hh => hne hh.symm
  have hmem := h.2 i' hne'
  rcases h'.1 with h0 | h1
  · rw [h0] at hmem
    exact absurd hmem.1 (by norm_num)
  · rw [h1] at hmem
    exact absurd hmem.2 (by norm_num)

lemma uInv_faceCoord {x : Amb 8} {i : Fin 9} (hi : FaceCoord x i) (h12 : i = 1 ∨ i = 2) :
    FaceCoord (uInv x) i := by
  rcases h12 with rfl | rfl
  · refine ⟨?_, ?_⟩
    · rw [uInv_apply_one]
      rcases hi.1 with h | h <;> rw [h] <;> norm_num
    · intro j hj
      by_cases hj1 : j = 1
      · exact absurd hj1 hj
      · by_cases hj2 : j = 2
        · rw [hj2, uInv_apply_two]
          exact one_sub_mem_Ioo (hi.2 2 (by decide))
        · rw [uInv_apply_other x hj1 hj2]
          exact hi.2 j hj
  · refine ⟨?_, ?_⟩
    · rw [uInv_apply_two]
      rcases hi.1 with h | h <;> rw [h] <;> norm_num
    · intro j hj
      by_cases hj1 : j = 1
      · rw [hj1, uInv_apply_one]
        exact one_sub_mem_Ioo (hi.2 1 (by decide))
      · by_cases hj2 : j = 2
        · exact absurd hj2 hj
        · rw [uInv_apply_other x hj1 hj2]
          exact hi.2 j hj

lemma yInv_faceCoord {x : Amb 8} {i : Fin 9} (hi : FaceCoord x i) (h34 : i = 3 ∨ i = 4) :
    FaceCoord (yInv x) i := by
  rcases h34 with rfl | rfl
  · refine ⟨?_, ?_⟩
    · rw [yInv_apply_three]
      rcases hi.1 with h | h <;> rw [h] <;> norm_num
    · intro j hj
      by_cases hj3 : j = 3
      · exact absurd hj3 hj
      · by_cases hj4 : j = 4
        · rw [hj4, yInv_apply_four]
          exact one_sub_mem_Ioo (hi.2 4 (by decide))
        · rw [yInv_apply_other x hj3 hj4]
          exact hi.2 j hj
  · refine ⟨?_, ?_⟩
    · rw [yInv_apply_four]
      rcases hi.1 with h | h <;> rw [h] <;> norm_num
    · intro j hj
      by_cases hj3 : j = 3
      · rw [hj3, yInv_apply_three]
        exact one_sub_mem_Ioo (hi.2 3 (by decide))
      · by_cases hj4 : j = 4
        · exact absurd hj4 hj
        · rw [yInv_apply_other x hj3 hj4]
          exact hi.2 j hj

lemma zInv_faceCoord {x : Amb 8} {i : Fin 9} (hi : FaceCoord x i) (h67 : i = 6 ∨ i = 7) :
    FaceCoord (zInv x) i := by
  rcases h67 with rfl | rfl
  · refine ⟨?_, ?_⟩
    · rw [zInv_apply_six]
      rcases hi.1 with h | h <;> rw [h] <;> norm_num
    · intro j hj
      by_cases hj6 : j = 6
      · exact absurd hj6 hj
      · by_cases hj7 : j = 7
        · rw [hj7, zInv_apply_seven]
          exact one_sub_mem_Ioo (hi.2 7 (by decide))
        · rw [zInv_apply_other x hj6 hj7]
          exact hi.2 j hj
  · refine ⟨?_, ?_⟩
    · rw [zInv_apply_seven]
      rcases hi.1 with h | h <;> rw [h] <;> norm_num
    · intro j hj
      by_cases hj6 : j = 6
      · rw [hj6, zInv_apply_six]
        exact one_sub_mem_Ioo (hi.2 6 (by decide))
      · by_cases hj7 : j = 7
        · exact absurd hj7 hj
        · rw [zInv_apply_other x hj6 hj7]
          exact hi.2 j hj

/-! ## 3. The seam part and its involution -/

/-- The boundary pair meets that are **not** on the two family-parameter faces `s = 0, 1`. -/
def ppSeam (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M) (V W : EuclideanSpace ℝ (Fin 3) → M) :
    Set (Amb 8) :=
  {x | x ∈ ppMeetBdry E E' V W ∧ ftS x ≠ 0 ∧ ftS x ≠ 1}

lemma mem_ppSeam {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M} {x : Amb 8} :
    x ∈ ppSeam E E' V W ↔ x ∈ ppMeetBdry E E' V W ∧ ftS x ≠ 0 ∧ ftS x ≠ 1 := Iff.rfl

/-- **The seam involution**: on the seam part the (unique) face coordinate selects one of the three
antipodal involutions. -/
noncomputable def ppInv (x : Amb 8) : Amb 8 := by
  classical
  exact if (∃ i : Fin 9, FaceCoord x i ∧ (i = 1 ∨ i = 2)) then uInv x
    else if (∃ i : Fin 9, FaceCoord x i ∧ (i = 3 ∨ i = 4)) then yInv x
    else zInv x

lemma ppInv_of_faceU {x : Amb 8} {i : Fin 9} (hi : FaceCoord x i) (h : i = 1 ∨ i = 2) :
    ppInv x = uInv x := by
  unfold ppInv
  exact if_pos ⟨i, hi, h⟩

lemma not_exists_face_of {x : Amb 8} {i : Fin 9} (hi : FaceCoord x i)
    (h : ¬ (i = 1 ∨ i = 2)) : ¬ (∃ j : Fin 9, FaceCoord x j ∧ (j = 1 ∨ j = 2)) := by
  rintro ⟨j, hj, hj12⟩
  have hij : i = j := faceCoord_unique hi hj
  exact h (hij ▸ hj12)

lemma not_exists_face_of' {x : Amb 8} {i : Fin 9} (hi : FaceCoord x i)
    (h : ¬ (i = 3 ∨ i = 4)) : ¬ (∃ j : Fin 9, FaceCoord x j ∧ (j = 3 ∨ j = 4)) := by
  rintro ⟨j, hj, hj34⟩
  have hij : i = j := faceCoord_unique hi hj
  exact h (hij ▸ hj34)

lemma fin9_34_not12 {i : Fin 9} (h : i = 3 ∨ i = 4) : ¬ (i = 1 ∨ i = 2) := by
  rcases h with h | h <;> rw [h] <;> decide

lemma fin9_67_not12 {i : Fin 9} (h : i = 6 ∨ i = 7) : ¬ (i = 1 ∨ i = 2) := by
  rcases h with h | h <;> rw [h] <;> decide

lemma fin9_67_not34 {i : Fin 9} (h : i = 6 ∨ i = 7) : ¬ (i = 3 ∨ i = 4) := by
  rcases h with h | h <;> rw [h] <;> decide

lemma ppInv_of_faceY {x : Amb 8} {i : Fin 9} (hi : FaceCoord x i) (h : i = 3 ∨ i = 4) :
    ppInv x = yInv x := by
  unfold ppInv
  rw [if_neg (not_exists_face_of hi (fin9_34_not12 h)), if_pos ⟨i, hi, h⟩]

lemma ppInv_of_faceZ {x : Amb 8} {i : Fin 9} (hi : FaceCoord x i) (h : i = 6 ∨ i = 7) :
    ppInv x = zInv x := by
  unfold ppInv
  rw [if_neg (not_exists_face_of hi (fin9_67_not12 h)),
    if_neg (not_exists_face_of' hi (fin9_67_not34 h))]

/-! ## 4. The meet and boundary conditions are invariant -/

lemma uInv_mem_ppMeet {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E s (seamInv2 u) = E s u)
    (hseamU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E' s (seamInv2 u) = E' s u)
    {x : Amb 8} (hx : x ∈ ppMeet E E' V W) (h : onSeam2 (ftU x)) :
    uInv x ∈ ppMeet E E' V W := by
  rw [mem_ppMeet_iff] at hx ⊢
  obtain ⟨hbox, h1, h2⟩ := hx
  refine ⟨uInv_mem_unitBox hbox, ?_, ?_⟩
  · rw [ftS_uInv, ftU_uInv, ftY_uInv, hseamU (ftS x) (ftU x) h]
    exact h1
  · rw [ftS_uInv, ftU_uInv, ftZ_uInv, hseamU' (ftS x) (ftU x) h]
    exact h2

lemma yInv_mem_ppMeet {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V (seamInv y) = V y)
    {x : Amb 8} (hx : x ∈ ppMeet E E' V W) (h : onSeam (ftY x)) :
    yInv x ∈ ppMeet E E' V W := by
  rw [mem_ppMeet_iff] at hx ⊢
  obtain ⟨hbox, h1, h2⟩ := hx
  refine ⟨yInv_mem_unitBox hbox, ?_, ?_⟩
  · rw [ftS_yInv, ftU_yInv, ftY_yInv, hseamV (ftY x) h]
    exact h1
  · rw [ftS_yInv, ftU_yInv, ftZ_yInv]
    exact h2

lemma zInv_mem_ppMeet {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W (seamInv z) = W z)
    {x : Amb 8} (hx : x ∈ ppMeet E E' V W) (h : onSeam (ftZ x)) :
    zInv x ∈ ppMeet E E' V W := by
  rw [mem_ppMeet_iff] at hx ⊢
  obtain ⟨hbox, h1, h2⟩ := hx
  refine ⟨zInv_mem_unitBox hbox, ?_, ?_⟩
  · rw [ftS_zInv, ftU_zInv, ftY_zInv]
    exact h1
  · rw [ftS_zInv, ftU_zInv, ftZ_zInv, hseamW (ftZ x) h]
    exact h2

lemma uInv_mem_unitBoxBdry {x : Amb 8} (hx : x ∈ unitBoxBdry 8)
    (hco : (x 1 = 0 ∨ x 1 = 1) ∨ (x 2 = 0 ∨ x 2 = 1)) :
    uInv x ∈ unitBoxBdry 8 := by
  obtain ⟨hbox, i, hi⟩ := hx
  refine ⟨uInv_mem_unitBox hbox, ?_⟩
  rcases hco with (h | h) | (h | h)
  · exact ⟨1, Or.inr (by rw [uInv_apply_one, h]; norm_num)⟩
  · exact ⟨1, Or.inl (by rw [uInv_apply_one, h]; norm_num)⟩
  · exact ⟨2, Or.inr (by rw [uInv_apply_two, h]; norm_num)⟩
  · exact ⟨2, Or.inl (by rw [uInv_apply_two, h]; norm_num)⟩

lemma yInv_mem_unitBoxBdry {x : Amb 8} (hx : x ∈ unitBoxBdry 8)
    (hco : (x 3 = 0 ∨ x 3 = 1) ∨ (x 4 = 0 ∨ x 4 = 1)) :
    yInv x ∈ unitBoxBdry 8 := by
  obtain ⟨hbox, i, hi⟩ := hx
  refine ⟨yInv_mem_unitBox hbox, ?_⟩
  rcases hco with (h | h) | (h | h)
  · exact ⟨3, Or.inr (by rw [yInv_apply_three, h]; norm_num)⟩
  · exact ⟨3, Or.inl (by rw [yInv_apply_three, h]; norm_num)⟩
  · exact ⟨4, Or.inr (by rw [yInv_apply_four, h]; norm_num)⟩
  · exact ⟨4, Or.inl (by rw [yInv_apply_four, h]; norm_num)⟩

lemma zInv_mem_unitBoxBdry {x : Amb 8} (hx : x ∈ unitBoxBdry 8)
    (hco : (x 6 = 0 ∨ x 6 = 1) ∨ (x 7 = 0 ∨ x 7 = 1)) :
    zInv x ∈ unitBoxBdry 8 := by
  obtain ⟨hbox, i, hi⟩ := hx
  refine ⟨zInv_mem_unitBox hbox, ?_⟩
  rcases hco with (h | h) | (h | h)
  · exact ⟨6, Or.inr (by rw [zInv_apply_six, h]; norm_num)⟩
  · exact ⟨6, Or.inl (by rw [zInv_apply_six, h]; norm_num)⟩
  · exact ⟨7, Or.inr (by rw [zInv_apply_seven, h]; norm_num)⟩
  · exact ⟨7, Or.inl (by rw [zInv_apply_seven, h]; norm_num)⟩

/-! ## 5. The seam part is preserved by the involution -/

lemma uInv_mem_ppSeam {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E s (seamInv2 u) = E s u)
    (hseamU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E' s (seamInv2 u) = E' s u)
    {x : Amb 8} (hx : x ∈ ppMeetBdry E E' V W) (h0 : ftS x ≠ 0) (h1 : ftS x ≠ 1)
    (hco : (x 1 = 0 ∨ x 1 = 1) ∨ (x 2 = 0 ∨ x 2 = 1)) :
    uInv x ∈ ppSeam E E' V W := by
  obtain ⟨hm, hb⟩ := hx
  refine ⟨⟨uInv_mem_ppMeet hseamU hseamU' hm (onSeam2_ftU_of x hco),
      uInv_mem_unitBoxBdry hb hco⟩, ?_, ?_⟩
  · rw [ftS_uInv]; exact h0
  · rw [ftS_uInv]; exact h1

lemma yInv_mem_ppSeam {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V (seamInv y) = V y)
    {x : Amb 8} (hx : x ∈ ppMeetBdry E E' V W) (h0 : ftS x ≠ 0) (h1 : ftS x ≠ 1)
    (hco : (x 3 = 0 ∨ x 3 = 1) ∨ (x 4 = 0 ∨ x 4 = 1)) :
    yInv x ∈ ppSeam E E' V W := by
  obtain ⟨hm, hb⟩ := hx
  refine ⟨⟨yInv_mem_ppMeet hseamV hm (onSeam_ftY_of x hco),
      yInv_mem_unitBoxBdry hb hco⟩, ?_, ?_⟩
  · rw [ftS_yInv]; exact h0
  · rw [ftS_yInv]; exact h1

lemma zInv_mem_ppSeam {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W (seamInv z) = W z)
    {x : Amb 8} (hx : x ∈ ppMeetBdry E E' V W) (h0 : ftS x ≠ 0) (h1 : ftS x ≠ 1)
    (hco : (x 6 = 0 ∨ x 6 = 1) ∨ (x 7 = 0 ∨ x 7 = 1)) :
    zInv x ∈ ppSeam E E' V W := by
  obtain ⟨hm, hb⟩ := hx
  refine ⟨⟨zInv_mem_ppMeet hseamW hm (onSeam_ftZ_of x hco),
      zInv_mem_unitBoxBdry hb hco⟩, ?_, ?_⟩
  · rw [ftS_zInv]; exact h0
  · rw [ftS_zInv]; exact h1

/-- **The face coordinate of a seam meet.**  It is unique, it is not `0` (the meet is not on an end
face) and it is not `5` or `8` (the level coordinates are avoided by `havY`/`havZ`). -/
lemma faceCoord_of_mem_ppSeam {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hface : ∀ x ∈ ppMeetBdry E E' V W, ∃ i : Fin 9, FaceCoord x i)
    (havY : ∀ x ∈ ppMeet E E' V W, ftY2 x ≠ 0 ∧ ftY2 x ≠ 1)
    (havZ : ∀ x ∈ ppMeet E E' V W, ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1)
    {x : Amb 8} (hx : x ∈ ppSeam E E' V W) :
    ∃ i : Fin 9, FaceCoord x i ∧ i ≠ 0 ∧ i ≠ 5 ∧ i ≠ 8 := by
  rw [mem_ppSeam] at hx
  obtain ⟨hb, h0, h1⟩ := hx
  obtain ⟨i, hi⟩ := hface x hb
  refine ⟨i, hi, ?_, ?_, ?_⟩
  · intro h
    rw [h] at hi
    rcases hi.1 with hh | hh
    · exact h0 hh
    · exact h1 hh
  · intro h
    rw [h] at hi
    rcases hi.1 with hh | hh
    · exact (havY x hb.1).1 (by rw [ftY2_eq_coord]; exact hh)
    · exact (havY x hb.1).2 (by rw [ftY2_eq_coord]; exact hh)
  · intro h
    rw [h] at hi
    rcases hi.1 with hh | hh
    · exact (havZ x hb.1).1 (by rw [ftZ2_eq_coord]; exact hh)
    · exact (havZ x hb.1).2 (by rw [ftZ2_eq_coord]; exact hh)

lemma hco_u_of_faceCoord {x : Amb 8} {i : Fin 9} (hi : FaceCoord x i) (h12 : i = 1 ∨ i = 2) :
    (x 1 = 0 ∨ x 1 = 1) ∨ (x 2 = 0 ∨ x 2 = 1) := by
  rcases h12 with h | h
  · rw [h] at hi
    exact Or.inl hi.1
  · rw [h] at hi
    exact Or.inr hi.1

lemma hco_y_of_faceCoord {x : Amb 8} {i : Fin 9} (hi : FaceCoord x i) (h34 : i = 3 ∨ i = 4) :
    (x 3 = 0 ∨ x 3 = 1) ∨ (x 4 = 0 ∨ x 4 = 1) := by
  rcases h34 with h | h
  · rw [h] at hi
    exact Or.inl hi.1
  · rw [h] at hi
    exact Or.inr hi.1

lemma hco_z_of_faceCoord {x : Amb 8} {i : Fin 9} (hi : FaceCoord x i) (h67 : i = 6 ∨ i = 7) :
    (x 6 = 0 ∨ x 6 = 1) ∨ (x 7 = 0 ∨ x 7 = 1) := by
  rcases h67 with h | h
  · rw [h] at hi
    exact Or.inl hi.1
  · rw [h] at hi
    exact Or.inr hi.1

/-- A face coordinate different from `0, 5, 8` is one of `1, 2, 3, 4, 6, 7`. -/
lemma fin9_case {i : Fin 9} (h0 : i ≠ 0) (h5 : i ≠ 5) (h8 : i ≠ 8) :
    i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 7 := by
  fin_cases i <;> simp_all

lemma ppInv_mem {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hface : ∀ x ∈ ppMeetBdry E E' V W, ∃ i : Fin 9, FaceCoord x i)
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E s (seamInv2 u) = E s u)
    (hseamU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E' s (seamInv2 u) = E' s u)
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V (seamInv y) = V y)
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W (seamInv z) = W z)
    (havY : ∀ x ∈ ppMeet E E' V W, ftY2 x ≠ 0 ∧ ftY2 x ≠ 1)
    (havZ : ∀ x ∈ ppMeet E E' V W, ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1)
    {x : Amb 8} (hx : x ∈ ppSeam E E' V W) : ppInv x ∈ ppSeam E E' V W := by
  obtain ⟨i, hi, hi0, hi5, hi8⟩ := faceCoord_of_mem_ppSeam hface havY havZ hx
  rw [mem_ppSeam] at hx
  rcases fin9_case hi0 hi5 hi8 with h | h | h | h | h | h
  · rw [h] at hi
    rw [ppInv_of_faceU hi (Or.inl rfl)]
    exact uInv_mem_ppSeam hseamU hseamU' hx.1 hx.2.1 hx.2.2 (hco_u_of_faceCoord hi (Or.inl rfl))
  · rw [h] at hi
    rw [ppInv_of_faceU hi (Or.inr rfl)]
    exact uInv_mem_ppSeam hseamU hseamU' hx.1 hx.2.1 hx.2.2 (hco_u_of_faceCoord hi (Or.inr rfl))
  · rw [h] at hi
    rw [ppInv_of_faceY hi (Or.inl rfl)]
    exact yInv_mem_ppSeam hseamV hx.1 hx.2.1 hx.2.2 (hco_y_of_faceCoord hi (Or.inl rfl))
  · rw [h] at hi
    rw [ppInv_of_faceY hi (Or.inr rfl)]
    exact yInv_mem_ppSeam hseamV hx.1 hx.2.1 hx.2.2 (hco_y_of_faceCoord hi (Or.inr rfl))
  · rw [h] at hi
    rw [ppInv_of_faceZ hi (Or.inl rfl)]
    exact zInv_mem_ppSeam hseamW hx.1 hx.2.1 hx.2.2 (hco_z_of_faceCoord hi (Or.inl rfl))
  · rw [h] at hi
    rw [ppInv_of_faceZ hi (Or.inr rfl)]
    exact zInv_mem_ppSeam hseamW hx.1 hx.2.1 hx.2.2 (hco_z_of_faceCoord hi (Or.inr rfl))

lemma ppInv_invol {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hface : ∀ x ∈ ppMeetBdry E E' V W, ∃ i : Fin 9, FaceCoord x i)
    (havY : ∀ x ∈ ppMeet E E' V W, ftY2 x ≠ 0 ∧ ftY2 x ≠ 1)
    (havZ : ∀ x ∈ ppMeet E E' V W, ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1)
    {x : Amb 8} (hx : x ∈ ppSeam E E' V W) : ppInv (ppInv x) = x := by
  obtain ⟨i, hi, hi0, hi5, hi8⟩ := faceCoord_of_mem_ppSeam hface havY havZ hx
  rcases fin9_case hi0 hi5 hi8 with h | h | h | h | h | h
  · rw [h] at hi
    rw [ppInv_of_faceU hi (Or.inl rfl),
      ppInv_of_faceU (uInv_faceCoord hi (Or.inl rfl)) (Or.inl rfl), uInv_invol]
  · rw [h] at hi
    rw [ppInv_of_faceU hi (Or.inr rfl),
      ppInv_of_faceU (uInv_faceCoord hi (Or.inr rfl)) (Or.inr rfl), uInv_invol]
  · rw [h] at hi
    rw [ppInv_of_faceY hi (Or.inl rfl),
      ppInv_of_faceY (yInv_faceCoord hi (Or.inl rfl)) (Or.inl rfl), yInv_invol]
  · rw [h] at hi
    rw [ppInv_of_faceY hi (Or.inr rfl),
      ppInv_of_faceY (yInv_faceCoord hi (Or.inr rfl)) (Or.inr rfl), yInv_invol]
  · rw [h] at hi
    rw [ppInv_of_faceZ hi (Or.inl rfl),
      ppInv_of_faceZ (zInv_faceCoord hi (Or.inl rfl)) (Or.inl rfl), zInv_invol]
  · rw [h] at hi
    rw [ppInv_of_faceZ hi (Or.inr rfl),
      ppInv_of_faceZ (zInv_faceCoord hi (Or.inr rfl)) (Or.inr rfl), zInv_invol]

lemma ppInv_ne {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hface : ∀ x ∈ ppMeetBdry E E' V W, ∃ i : Fin 9, FaceCoord x i)
    (havY : ∀ x ∈ ppMeet E E' V W, ftY2 x ≠ 0 ∧ ftY2 x ≠ 1)
    (havZ : ∀ x ∈ ppMeet E E' V W, ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1)
    {x : Amb 8} (hx : x ∈ ppSeam E E' V W) : ppInv x ≠ x := by
  obtain ⟨i, hi, hi0, hi5, hi8⟩ := faceCoord_of_mem_ppSeam hface havY havZ hx
  rcases fin9_case hi0 hi5 hi8 with h | h | h | h | h | h
  · rw [h] at hi
    rw [ppInv_of_faceU hi (Or.inl rfl)]
    exact uInv_ne (Or.inl hi.1)
  · rw [h] at hi
    rw [ppInv_of_faceU hi (Or.inr rfl)]
    exact uInv_ne (Or.inr hi.1)
  · rw [h] at hi
    rw [ppInv_of_faceY hi (Or.inl rfl)]
    exact yInv_ne (Or.inl hi.1)
  · rw [h] at hi
    rw [ppInv_of_faceY hi (Or.inr rfl)]
    exact yInv_ne (Or.inr hi.1)
  · rw [h] at hi
    rw [ppInv_of_faceZ hi (Or.inl rfl)]
    exact zInv_ne (Or.inl hi.1)
  · rw [h] at hi
    rw [ppInv_of_faceZ hi (Or.inr rfl)]
    exact zInv_ne (Or.inr hi.1)

/-! ## 6. The final bookkeeping -/

theorem even_of_even_add {a b : ℕ} (h : Even (a + b)) (hb : Even b) : Even a :=
  (Nat.even_add.mp h).mpr hb

end PPE

open PPE

theorem ppMeetEnd_even
    {M : Type*} [TopologicalSpace M] [T2Space M]
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M)
    (hface : ∀ x ∈ Work.Drive.ppMeetBdry E E' V W, ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧
      (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), Work.Drive.onSeam2 u →
      E s (Work.Drive.seamInv2 u) = E s u)
    (hseamU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), Work.Drive.onSeam2 u →
      E' s (Work.Drive.seamInv2 u) = E' s u)
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), Work.Drive.onSeam y →
      V (Work.Drive.seamInv y) = V y)
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), Work.Drive.onSeam z →
      W (Work.Drive.seamInv z) = W z)
    (havY : ∀ x ∈ Work.Drive.ppMeet E E' V W, Work.Drive.ftY2 x ≠ 0 ∧ Work.Drive.ftY2 x ≠ 1)
    (havZ : ∀ x ∈ Work.Drive.ppMeet E E' V W, Work.Drive.ftZ2 x ≠ 0 ∧ Work.Drive.ftZ2 x ≠ 1)
    (hfin : (Work.Drive.ppMeetBdry E E' V W).Finite)
    (heven : Even ((Work.Drive.ppMeetBdry E E' V W).ncard)) :
    Even ((Work.Drive.ppMeetEnd E E' V W 0).ncard + (Work.Drive.ppMeetEnd E E' V W 1).ncard) := by
  classical
  have hend : ∀ s : ℝ, s = 0 ∨ s = 1 →
      ppMeetEnd E E' V W s = {x | x ∈ ppMeetBdry E E' V W ∧ ftS x = s} := by
    intro s hs
    ext x
    constructor
    · intro hx
      rw [mem_ppMeetEnd] at hx
      refine ⟨⟨hx.1, ?_⟩, hx.2⟩
      refine ⟨hx.1.1, ⟨0, ?_⟩⟩
      rcases hs with h | h
      · exact Or.inl (hx.2.trans h)
      · exact Or.inr (hx.2.trans h)
    · rintro ⟨hbd, hsx⟩
      rw [mem_ppMeetEnd]
      exact ⟨hbd.1, hsx⟩
  have hfin0 : (ppMeetEnd E E' V W 0).Finite := by
    refine hfin.subset ?_
    intro x hx
    rw [hend 0 (Or.inl rfl)] at hx
    exact hx.1
  have hfin1 : (ppMeetEnd E E' V W 1).Finite := by
    refine hfin.subset ?_
    intro x hx
    rw [hend 1 (Or.inr rfl)] at hx
    exact hx.1
  have hfinP : (ppSeam E E' V W).Finite := by
    refine hfin.subset ?_
    intro x hx
    rw [mem_ppSeam] at hx
    exact hx.1
  have hsplit : ppMeetBdry E E' V W =
      (ppMeetEnd E E' V W 0 ∪ ppMeetEnd E E' V W 1) ∪ ppSeam E E' V W := by
    rw [hend 0 (Or.inl rfl), hend 1 (Or.inr rfl)]
    ext x
    constructor
    · intro hx
      by_cases h0 : ftS x = 0
      · exact Or.inl (Or.inl ⟨hx, h0⟩)
      · by_cases h1 : ftS x = 1
        · exact Or.inl (Or.inr ⟨hx, h1⟩)
        · exact Or.inr ⟨hx, h0, h1⟩
    · rintro ((⟨hx, -⟩ | ⟨hx, -⟩) | ⟨hx, -, -⟩)
      · exact hx
      · exact hx
      · exact hx
  have hdisj01 : Disjoint (ppMeetEnd E E' V W 0) (ppMeetEnd E E' V W 1) := by
    rw [Set.disjoint_left]
    rintro x hx hy
    rw [hend 0 (Or.inl rfl), Set.mem_setOf_eq] at hx
    rw [hend 1 (Or.inr rfl), Set.mem_setOf_eq] at hy
    rw [hx.2] at hy
    exact absurd hy.2 (by norm_num)
  have hdisjP : Disjoint ((ppMeetEnd E E' V W 0) ∪ (ppMeetEnd E E' V W 1))
      (ppSeam E E' V W) := by
    rw [Set.disjoint_left]
    rintro x hx hy
    rw [mem_ppSeam] at hy
    rcases hx with h | h
    · rw [hend 0 (Or.inl rfl)] at h
      exact hy.2.1 h.2
    · rw [hend 1 (Or.inr rfl)] at h
      exact hy.2.2 h.2
  have hncard : (ppMeetBdry E E' V W).ncard
      = ((ppMeetEnd E E' V W 0).ncard + (ppMeetEnd E E' V W 1).ncard)
        + (ppSeam E E' V W).ncard := by
    rw [hsplit, Set.ncard_union_eq hdisjP (hfin0.union hfin1) hfinP,
      Set.ncard_union_eq hdisj01 hfin0 hfin1]
  have hPeven : Even (ppSeam E E' V W).ncard :=
    even_ncard_of_involution hfinP ppInv
      (fun x hx => ppInv_mem hface hseamU hseamU' hseamV hseamW havY havZ hx)
      (fun x hx => ppInv_invol hface havY havZ hx)
      (fun x hx => ppInv_ne hface havY havZ hx)
  have hEvenS : Even ((ppMeetEnd E E' V W 0).ncard + (ppMeetEnd E E' V W 1).ncard
      + (ppSeam E E' V W).ncard) := by
    rw [← hncard]
    exact heven
  exact even_of_even_add hEvenS hPeven

end

end Work.Drive
