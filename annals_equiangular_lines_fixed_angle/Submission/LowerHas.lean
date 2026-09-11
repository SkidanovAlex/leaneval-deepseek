import Submission.LowerV

open EquiangularLinesFixedAngle
open Filter
open Matrix
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option maxHeartbeats 1200000

/-! Stage 4 of the disjoint-union lower bound: assemble the configuration into
`HasLines`. -/

/-- inner product equals the Gram entry when the Gram matrix is `A`. -/
lemma gram_inner {n d : ℕ} {v : Fin n → Euc d} (A : Matrix (Fin n) (Fin n) ℝ)
    (hv : Matrix.gram ℝ v = A) (i j : Fin n) : ⟪v i, v j⟫ = A i j := by
  have h := congrFun (congrFun hv i) j
  rwa [Matrix.gram_apply] at h

/-- inner product of two copy-lines in terms of the per-copy vectors. -/
lemma inner_copy_copy {k0 c t : ℕ} (y : Fin k0 → Euc (k0 - 1)) (a : ℝ)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ 1 - a) (s s' : Fin c) (i j : Fin k0) :
    ⟪linesFamily (k0 := k0) (c := c) (t := t) y a (Sum.inl (s, i)),
      linesFamily (k0 := k0) (c := c) (t := t) y a (Sum.inl (s', j))⟫
      = (if s = s' then (1 - a) * ⟪y i, y j⟫ else 0) + a := by
  classical
  unfold linesFamily
  rw [inner_wToEuc]
  rw [wDot_split]
  have hm : wMain (copyCoord (k0 := k0) (c := c) (t := t) y a s i)
        ⬝ᵥ wMain (copyCoord (k0 := k0) (c := c) (t := t) y a s' j)
      = (if s = s' then (1 - a) * ⟪y i, y j⟫ else 0) := by
    exact copyMain_dot y a hb0 s s' i j
  have hzi : wIso (copyCoord (k0 := k0) (c := c) (t := t) y a s i) = 0 :=
    funext (wIso_copy_zero (k0 := k0) (c := c) (t := t) y a s i)
  have hzj : wIso (copyCoord (k0 := k0) (c := c) (t := t) y a s' j) = 0 :=
    funext (wIso_copy_zero (k0 := k0) (c := c) (t := t) y a s' j)
  have hi0 : wIso (copyCoord (k0 := k0) (c := c) (t := t) y a s i)
        ⬝ᵥ wIso (copyCoord (k0 := k0) (c := c) (t := t) y a s' j) = 0 := by
    rw [hzi, hzj]
    exact dotProduct_zero_fun_left (fun _ => 0)
  have ho : wOne (copyCoord (k0 := k0) (c := c) (t := t) y a s i)
        ⬝ᵥ wOne (copyCoord (k0 := k0) (c := c) (t := t) y a s' j) = a :=
    wOne_lines _ _ a ha0 (wOne_copy_val (k0 := k0) (c := c) (t := t) y a s i)
      (wOne_copy_val (k0 := k0) (c := c) (t := t) y a s' j)
  rw [hm, hi0, ho]
  ring

/-- inner product of a copy-line and an isolate line is `a`. -/
lemma inner_copy_iso {k0 c t : ℕ} (y : Fin k0 → Euc (k0 - 1)) (a : ℝ)
    (ha0 : 0 ≤ a) (s : Fin c) (i : Fin k0) (u : Fin t) :
    ⟪linesFamily (k0 := k0) (c := c) (t := t) y a (Sum.inl (s, i)),
      linesFamily (k0 := k0) (c := c) (t := t) y a (Sum.inr u)⟫ = a := by
  classical
  unfold linesFamily
  rw [inner_wToEuc]
  rw [wDot_split]
  have hzi : wMain (isoCoord (k0 := k0) (c := c) (t := t) a u) = 0 :=
    funext (wMain_iso_zero (k0 := k0) (c := c) (t := t) a u)
  have hm : wMain (copyCoord (k0 := k0) (c := c) (t := t) y a s i)
        ⬝ᵥ wMain (isoCoord (k0 := k0) (c := c) (t := t) a u) = 0 := by
    rw [hzi]
    exact dotProduct_zero_fun_right _
  have hc : wIso (copyCoord (k0 := k0) (c := c) (t := t) y a s i) = 0 :=
    funext (wIso_copy_zero (k0 := k0) (c := c) (t := t) y a s i)
  have hi0 : wIso (copyCoord (k0 := k0) (c := c) (t := t) y a s i)
        ⬝ᵥ wIso (isoCoord (k0 := k0) (c := c) (t := t) a u) = 0 := by
    rw [hc]
    exact dotProduct_zero_fun_left _
  have ho : wOne (copyCoord (k0 := k0) (c := c) (t := t) y a s i)
        ⬝ᵥ wOne (isoCoord (k0 := k0) (c := c) (t := t) a u) = a :=
    wOne_lines _ _ a ha0 (wOne_copy_val (k0 := k0) (c := c) (t := t) y a s i)
      (wOne_iso_val (k0 := k0) (c := c) (t := t) a u)
  rw [hm, hi0, ho]
  ring

/-- inner product of two isolate lines (the `y`-part is irrelevant). -/
lemma inner_iso_iso {k0 c t : ℕ} (y₁ y₂ : Fin k0 → Euc (k0 - 1)) (a : ℝ)
    (hb0 : 0 ≤ 1 - a) (ha0 : 0 ≤ a) (u u' : Fin t) :
    ⟪linesFamily (k0 := k0) (c := c) (t := t) y₁ a (Sum.inr u),
      linesFamily (k0 := k0) (c := c) (t := t) y₂ a (Sum.inr u')⟫
      = (if u = u' then 1 - a else 0) + a := by
  classical
  unfold linesFamily
  rw [inner_wToEuc]
  rw [wDot_split]
  have hm : wMain (isoCoord (k0 := k0) (c := c) (t := t) a u)
        ⬝ᵥ wMain (isoCoord (k0 := k0) (c := c) (t := t) a u') = 0 := by
    rw [funext (wMain_iso_zero (k0 := k0) (c := c) (t := t) a u),
        funext (wMain_iso_zero (k0 := k0) (c := c) (t := t) a u')]
    exact dotProduct_zero_fun_left (fun _ => 0)
  have hi : wIso (isoCoord (k0 := k0) (c := c) (t := t) a u)
        ⬝ᵥ wIso (isoCoord (k0 := k0) (c := c) (t := t) a u') = (if u = u' then 1 - a else 0) := by
    exact wIso_iso_dot a hb0 u u'
  have ho : wOne (isoCoord (k0 := k0) (c := c) (t := t) a u)
        ⬝ᵥ wOne (isoCoord (k0 := k0) (c := c) (t := t) a u') = a :=
    wOne_lines _ _ a ha0 (wOne_iso_val (k0 := k0) (c := c) (t := t) a u)
      (wOne_iso_val (k0 := k0) (c := c) (t := t) a u')
  rw [hm, hi, ho]
  ring

open Classical in
/-- The final value of the inner product of two copy-lines. -/
lemma inner_copy_copy_val (α : ℝ) {k0 c t : ℕ} (H : SimpleGraph (Fin k0))
    (hα0 : 0 < α) (hα1 : α < 1) {y : Fin k0 → Euc (k0 - 1)}
    (hy : Matrix.gram ℝ y = perCopyGram (lam α) H)
    (s s' : Fin c) (i j : Fin k0) :
    ⟪linesFamily (k0 := k0) (c := c) (t := t) y α (Sum.inl (s, i)),
      linesFamily (k0 := k0) (c := c) (t := t) y α (Sum.inl (s', j))⟫
      = (if s = s' ∧ i = j then 1 else if s = s' ∧ H.Adj i j then -α else α) := by
  classical
  have ha0 : 0 ≤ α := le_of_lt hα0
  have hb0 : 0 ≤ 1 - α := by linarith
  have hgram := gram_inner (perCopyGram (lam α) H) hy i j
  have hmain := inner_copy_copy (t := t) y α ha0 hb0 s s' i j
  rw [hmain]
  by_cases hss' : s = s'
  · subst s'
    simp
    by_cases hij : i = j
    · subst j
      have hd : perCopyGram (lam α) H i i = 1 := by
        rw [perCopyGram_apply (lam α) H (lam_ne_zero' hα0 hα1) i i]
        simp
      rw [hgram, hd]
      simp
    · by_cases hadj : H.Adj i j
      · have hpc : perCopyGram (lam α) H i j = - (1 / lam α) := by
          rw [perCopyGram_apply (lam α) H (lam_ne_zero' hα0 hα1) i j]
          simp [hij, hadj]
        rw [hgram, hpc]
        rw [show (if i = j then 1 else if H.Adj i j then -α else α) = -α by simp [hij, hadj]]
        exact adj_value hα0 hα1
      · have hpc : perCopyGram (lam α) H i j = 0 := by
          rw [perCopyGram_apply (lam α) H (lam_ne_zero' hα0 hα1) i j]
          simp [hij, hadj]
        rw [hgram, hpc]
        simp [hij, hadj]
  · simp [hss']

open Classical in
/-- The norm of every line is `1`. -/
lemma linesFamily_norm {α : ℝ} {k0 c t : ℕ} (H : SimpleGraph (Fin k0))
    (hα0 : 0 < α) (hα1 : α < 1) {y : Fin k0 → Euc (k0 - 1)}
    (hy : Matrix.gram ℝ y = perCopyGram (lam α) H)
    (v : UType k0 c t) :
    ‖linesFamily (k0 := k0) (c := c) (t := t) y α v‖ = 1 := by
  classical
  cases v with
  | inl ps =>
    rcases ps with ⟨s, i⟩
    have hmain := inner_copy_copy_val (t := t) α H hα0 hα1 hy s s i i
    have hself : ⟪linesFamily (k0 := k0) (c := c) (t := t) y α (Sum.inl (s, i)),
        linesFamily (k0 := k0) (c := c) (t := t) y α (Sum.inl (s, i))⟫ = 1 := by
      rw [hmain]
      simp
    have hsq : ‖linesFamily (k0 := k0) (c := c) (t := t) y α (Sum.inl (s, i))‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      exact hself
    have hnn : 0 ≤ ‖linesFamily (k0 := k0) (c := c) (t := t) y α (Sum.inl (s, i))‖ := norm_nonneg _
    rcases sq_eq_one_iff.mp hsq with hpos | hneg
    · exact hpos
    · linarith
  | inr u =>
    have ha0 : 0 ≤ α := le_of_lt hα0
    have hb0 : 0 ≤ 1 - α := by linarith
    have hinner := inner_iso_iso (k0 := k0) (c := c) (t := t) y y α hb0 ha0 u u
    have hself : ⟪linesFamily (k0 := k0) (c := c) (t := t) y α (Sum.inr u),
        linesFamily (k0 := k0) (c := c) (t := t) y α (Sum.inr u)⟫ = 1 := by
      rw [hinner]
      simp
    have hsq : ‖linesFamily (k0 := k0) (c := c) (t := t) y α (Sum.inr u)‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      exact hself
    have hnn : 0 ≤ ‖linesFamily (k0 := k0) (c := c) (t := t) y α (Sum.inr u)‖ := norm_nonneg _
    rcases sq_eq_one_iff.mp hsq with hpos | hneg
    · exact hpos
    · linarith



open Classical in
/-- inner product of two distinct copy-lines has absolute value `α`. -/
lemma abs_inner_copy_copy (α : ℝ) {k0 c t : ℕ} (H : SimpleGraph (Fin k0))
    (hα0 : 0 < α) (hα1 : α < 1) {y : Fin k0 → Euc (k0 - 1)}
    (hy : Matrix.gram ℝ y = perCopyGram (lam α) H)
    {s s' : Fin c} {i j : Fin k0} (hne : (s, i) ≠ (s', j)) :
    |⟪linesFamily (k0 := k0) (c := c) (t := t) y α (Sum.inl (s, i)),
      linesFamily (k0 := k0) (c := c) (t := t) y α (Sum.inl (s', j))⟫| = α := by
  classical
  rw [inner_copy_copy_val α H hα0 hα1 hy s s' i j]
  by_cases h1 : s = s' ∧ i = j
  · exfalso
    exact hne (Prod.ext h1.1 h1.2)
  · by_cases h2 : s = s' ∧ H.Adj i j
    · have hij : i ≠ j := by
        intro h
        apply H.loopless.irrefl i
        simpa [h] using h2.2
      simp [h1, h2, hij]
      exact le_of_lt hα0
    · simp [h1, h2, abs_of_nonneg (le_of_lt hα0)]

open Classical in
/-- inner product of a copy-line and an isolate line has absolute value `α`. -/
lemma abs_inner_copy_iso {α : ℝ} {k0 c t : ℕ} {y : Fin k0 → Euc (k0 - 1)}
    (hα0 : 0 < α) (s : Fin c) (i : Fin k0) (u : Fin t) :
    |⟪linesFamily (k0 := k0) (c := c) (t := t) y α (Sum.inl (s, i)),
      linesFamily (k0 := k0) (c := c) (t := t) y α (Sum.inr u)⟫| = α := by
  classical
  rw [inner_copy_iso y α (le_of_lt hα0) s i u]
  exact abs_of_nonneg (le_of_lt hα0)

/-- inner products are symmetric up to absolute value. -/
lemma abs_inner_comm {d : ℕ} (x y : Euc d) : |⟪x, y⟫| = |⟪y, x⟫| := by
  rw [real_inner_comm]

open Classical in
/-- inner product of two distinct isolate lines has absolute value `α`. -/
lemma abs_inner_iso_iso {α : ℝ} {k0 c t : ℕ} {y₁ y₂ : Fin k0 → Euc (k0 - 1)}
    (hα0 : 0 < α) (hα1 : α < 1) {u u' : Fin t} (hne : u ≠ u') :
    |⟪linesFamily (k0 := k0) (c := c) (t := t) y₁ α (Sum.inr u),
      linesFamily (k0 := k0) (c := c) (t := t) y₂ α (Sum.inr u')⟫| = α := by
  classical
  have hb0 : 0 ≤ 1 - α := by linarith
  rw [inner_iso_iso y₁ y₂ α hb0 (le_of_lt hα0) u u']
  simp [hne, abs_of_nonneg (le_of_lt hα0)]

open Classical in
/-- The disjoint-union construction gives an equiangular family of the right size. -/
lemma hasLinesAny_union {α : ℝ} {k0 c t : ℕ} (H : SimpleGraph (Fin k0))
    (hα0 : 0 < α) (hα1 : α < 1) (hk0 : 2 ≤ k0)
    (hρ : spectralRadius ℝ (H.adjMatrix ℝ) = ENNReal.ofReal (lam α)) :
    HasLinesAny α (UType k0 c t) (Fintype.card (WType k0 c t)) := by
  classical
  rcases perCopyRealize (lam α) H hk0 (lam_pos hα0 hα1) hρ with ⟨y, hy⟩
  refine ⟨linesFamily (k0 := k0) (c := c) (t := t) y α, ?_, ?_⟩
  · exact linesFamily_norm H hα0 hα1 hy
  · intro v w hvw
    cases v with
    | inl ps₁ =>
      rcases ps₁ with ⟨s, i⟩
      cases w with
      | inl ps₂ =>
        rcases ps₂ with ⟨s', j⟩
        have hne : (s, i) ≠ (s', j) := by
          intro h
          apply hvw
          simp [h]
        exact abs_inner_copy_copy α H hα0 hα1 hy hne
      | inr u =>
        exact abs_inner_copy_iso hα0 s i u
    | inr u =>
      cases w with
      | inl ps =>
        rcases ps with ⟨s, i⟩
        rw [abs_inner_comm]
        exact abs_inner_copy_iso hα0 s i u
      | inr u' =>
        have hne' : u ≠ u' := by
          intro h
          apply hvw
          simp [h]
        exact abs_inner_iso_iso hα0 hα1 hne'

/-- Cardinality of the vertex type. -/
lemma card_UType {k0 c t : ℕ} : Fintype.card (UType k0 c t) = c * k0 + t := by
  classical
  simp [UType, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]

/-- Cardinality of the coordinate type. -/
lemma card_WType {k0 c t : ℕ} : Fintype.card (WType k0 c t) = c * (k0 - 1) + t + 1 := by
  classical
  simp [WType, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

open Classical in
/-- The disjoint-union lower bound for `HasLines`. -/
lemma hasLines_union_dim {α : ℝ} {k0 d : ℕ} (H : SimpleGraph (Fin k0))
    (hα0 : 0 < α) (hα1 : α < 1) (hk0 : 2 ≤ k0) (hd : 1 ≤ d)
    (hρ : spectralRadius ℝ (H.adjMatrix ℝ) = ENNReal.ofReal (lam α)) :
    HasLines α (((d - 1) / (k0 - 1)) * k0 + ((d - 1) % (k0 - 1))) d := by
  classical
  let c : ℕ := (d - 1) / (k0 - 1)
  let t : ℕ := (d - 1) % (k0 - 1)
  have hl := hasLinesAny_union (c := c) (t := t) H hα0 hα1 hk0 hρ
  have hl' : HasLines α (Fintype.card (UType k0 c t)) (Fintype.card (WType k0 c t)) :=
    hasLines_of_hasLinesAny α (UType k0 c t) (Fintype.card (WType k0 c t)) hl
  have hcd : Fintype.card (WType k0 c t) = d := by
    rw [card_WType]
    dsimp [c, t]
    exact dim_eq_of_div_mod hk0 hd
  have hl'' : HasLines α (Fintype.card (UType k0 c t)) d := by
    rw [hcd] at hl'
    exact hl'
  have hcv : Fintype.card (UType k0 c t) = c * k0 + t := card_UType
  have hgo : c * k0 + t = ((d - 1) / (k0 - 1)) * k0 + ((d - 1) % (k0 - 1)) := by
    dsimp [c, t]
  rw [hcv, hgo] at hl''
  exact hl''

end Submission
