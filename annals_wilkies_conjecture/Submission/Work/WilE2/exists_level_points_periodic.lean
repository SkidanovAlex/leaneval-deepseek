import Mathlib
import Submission.Work.WilE2.Rolle

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Classical Set
namespace Work.WilE2

/-! ## The padded sequence

Given `u : Fin p → ℝ` we append the point `u 0 + T` as the `p`-th entry, obtaining
`v : Fin (p+1) → ℝ`.  The `p` consecutive open intervals `(v i, v (i+1))`, `i : Fin p`, tile
`(u 0, u 0 + T)`, and the sign of `w` alternates between the left and right endpoint of each of
them. -/
def padSeq {p : ℕ} (hp : 0 < p) (T : ℝ) (u : Fin p → ℝ) : Fin (p + 1) → ℝ :=
  fun i => if h : (i : ℕ) < p then u ⟨(i : ℕ), h⟩ else u ⟨0, hp⟩ + T

theorem padSeq_castSucc {p : ℕ} (hp : 0 < p) (T : ℝ) (u : Fin p → ℝ) (i : Fin p) :
    padSeq hp T u i.castSucc = u i := by
  simp only [padSeq, Fin.val_castSucc]
  rw [dif_pos i.isLt]

theorem padSeq_last {p : ℕ} (hp : 0 < p) (T : ℝ) (u : Fin p → ℝ) :
    padSeq hp T u ⟨p, Nat.lt_succ_self p⟩ = u ⟨0, hp⟩ + T := by
  simp only [padSeq]
  rw [dif_neg (lt_irrefl p)]

theorem padSeq_succ_of_lt {p : ℕ} (hp : 0 < p) (T : ℝ) (u : Fin p → ℝ) (i : Fin p)
    (h : (i : ℕ) + 1 < p) :
    padSeq hp T u i.succ = u ⟨(i : ℕ) + 1, h⟩ := by
  simp only [padSeq, Fin.val_succ]
  rw [dif_pos h]

theorem padSeq_succ_of_not_lt {p : ℕ} (hp : 0 < p) (T : ℝ) (u : Fin p → ℝ) (i : Fin p)
    (h : ¬ (i : ℕ) + 1 < p) :
    padSeq hp T u i.succ = u ⟨0, hp⟩ + T := by
  simp only [padSeq, Fin.val_succ]
  rw [dif_neg h]

/-- The padded sequence is strictly increasing. -/
theorem padSeq_strictMono {p : ℕ} (hp : 0 < p) (T : ℝ) (u : Fin p → ℝ)
    (hmono : StrictMono u) (hhi : ∀ j, u j < u ⟨0, hp⟩ + T) :
    StrictMono (padSeq hp T u) := by
  intro i j hij
  have hi : (i : ℕ) < p := by have := i.isLt; have := j.isLt; omega
  have hjle : (j : ℕ) ≤ p := by have := j.isLt; omega
  have hvi : padSeq hp T u i = u ⟨(i : ℕ), hi⟩ := by
    simp only [padSeq]; rw [dif_pos hi]
  rcases lt_or_eq_of_le hjle with hj | hj
  · have hvj : padSeq hp T u j = u ⟨(j : ℕ), hj⟩ := by
      simp only [padSeq]; rw [dif_pos hj]
    rw [hvi, hvj]
    exact hmono (Fin.lt_def.mpr (Fin.lt_def.mp hij))
  · have hvj : padSeq hp T u j = u ⟨0, hp⟩ + T := by
      simp only [padSeq]; rw [dif_neg (by omega)]
    rw [hvi, hvj]
    exact hhi ⟨(i : ℕ), hi⟩

/-- The right endpoint of the `i`-th interval carries the value of `w` at `u (cycSucc hp i)`. -/
theorem padSeq_w_succ {p : ℕ} (hp : 0 < p) {w : ℝ → ℝ} (T : ℝ) (u : Fin p → ℝ)
    (hper : ∀ t, w (t + T) = w t) (i : Fin p) :
    w (padSeq hp T u i.succ) = w (u (cycSucc hp i)) := by
  rcases lt_or_ge ((i : ℕ) + 1) p with h | h
  · have h1 : padSeq hp T u i.succ = u ⟨(i : ℕ) + 1, h⟩ := padSeq_succ_of_lt hp T u i h
    have h4 : cycSucc hp i = ⟨(i : ℕ) + 1, h⟩ := Fin.ext (cycSucc_of_lt hp i h)
    rw [h1, h4]
  · have h2 : padSeq hp T u i.succ = u ⟨0, hp⟩ + T := padSeq_succ_of_not_lt hp T u i (by omega)
    have h3 : cycSucc hp i = ⟨0, hp⟩ := cycSucc_of_not_lt hp i (by omega)
    rw [h2, h3, hper (u ⟨0, hp⟩)]

/-- **Level points of a periodic function with alternating signs.**

Let `w` be continuous and `T`-periodic, `δ > 0`, and let `u 0 < … < u (p-1)` lie in
`[u 0, u 0 + T)` with `δ < |w (u j)|` and with the signs of `w (u j)` alternating around the
cycle (`w (u j) * w (u (cycSucc hp j)) < 0`).  Then the level set `{w = δ}` meets the open
interval `(u 0, u 0 + T)` in at least `p` points.

The proof produces, for each `i : Fin p`, a crossing of the level `δ` in the open interval
`(v i, v (i+1))` of the padded sequence `v := padSeq hp T u`; these `p` intervals tile
`(u 0, u 0 + T)` and hence the crossings are distinct. -/
theorem exists_level_points_periodic {w : ℝ → ℝ} {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hw : Continuous w) (hper : ∀ t, w (t + T) = w t) {p : ℕ} (hp : 0 < p) (u : Fin p → ℝ)
    (hmono : StrictMono u) (hhi : ∀ j, u j < u ⟨0, hp⟩ + T)
    (habs : ∀ j, δ < |w (u j)|) (halt : ∀ j, w (u j) * w (u (cycSucc hp j)) < 0) :
    ∃ S : Finset ℝ, p ≤ S.card ∧ (∀ s ∈ S, w s = δ) ∧
      (∀ s ∈ S, u ⟨0, hp⟩ < s ∧ s < u ⟨0, hp⟩ + T) := by
  classical
  set v : Fin (p + 1) → ℝ := padSeq hp T u with hvdef
  have hv_castSucc : ∀ i : Fin p, v i.castSucc = u i := fun i => padSeq_castSucc hp T u i
  have hv_last : v ⟨p, Nat.lt_succ_self p⟩ = u ⟨0, hp⟩ + T := padSeq_last hp T u
  have hv_mono : StrictMono v := padSeq_strictMono hp T u hmono hhi
  have hw_succ : ∀ i : Fin p, w (v i.succ) = w (u (cycSucc hp i)) :=
    fun i => padSeq_w_succ hp T u hper i
  -- a crossing of the level `δ` in each of the `p` intervals
  have hcross : ∀ i : Fin p, ∃ c ∈ Set.Ioo (v i.castSucc) (v i.succ), w c = δ := by
    intro i
    have hab : v i.castSucc ≤ v i.succ := (hv_mono Fin.castSucc_lt_succ).le
    have ha : w (v i.castSucc) ≠ δ := by
      rw [hv_castSucc i]; exact ne_delta_of_lt_abs hδ (habs i)
    have hb : w (v i.succ) ≠ δ := by
      rw [hw_succ i]; exact ne_delta_of_lt_abs hδ (habs (cycSucc hp i))
    have hbr : δ ∈ Set.Icc (w (v i.castSucc)) (w (v i.succ)) ∪
        Set.Icc (w (v i.succ)) (w (v i.castSucc)) := by
      rw [hv_castSucc i, hw_succ i]
      exact bracket_of_mul_neg hδ (halt i) (habs i) (habs (cycSucc hp i))
    exact exists_eq_Ioo_of_bracket hab hw.continuousOn ha hb hbr
  choose c hc hcw using hcross
  have hinj : Function.Injective c := by
    intro i j hij
    rcases lt_trichotomy i j with h | h | h
    · have h1 : c i < v i.succ := (hc i).2
      have h2 : v i.succ ≤ v j.castSucc :=
        hv_mono.monotone (by
          rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          exact Nat.succ_le_of_lt (Fin.lt_def.mp h))
      have h3 : v j.castSucc < c j := (hc j).1
      linarith
    · exact h
    · have h1 : c j < v j.succ := (hc j).2
      have h2 : v j.succ ≤ v i.castSucc :=
        hv_mono.monotone (by
          rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          exact Nat.succ_le_of_lt (Fin.lt_def.mp h))
      have h3 : v i.castSucc < c i := (hc i).1
      linarith
  refine ⟨Finset.univ.image c, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    exact hcw i
  · intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    constructor
    · have h1 : u ⟨0, hp⟩ ≤ u i :=
        hmono.monotone (by rw [Fin.le_def]; exact Nat.zero_le _)
      have h2 : v i.castSucc < c i := (hc i).1
      rw [hv_castSucc i] at h2
      linarith
    · have h1 : v i.succ ≤ v ⟨p, Nat.lt_succ_self p⟩ :=
        hv_mono.monotone (by
          rw [Fin.le_def, Fin.val_succ]
          show (i : ℕ) + 1 ≤ p
          have := i.isLt; omega)
      have h2 : c i < v i.succ := (hc i).2
      rw [hv_last] at h1
      linarith

end Work.WilE2
