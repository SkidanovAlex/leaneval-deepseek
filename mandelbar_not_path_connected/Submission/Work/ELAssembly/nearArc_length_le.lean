import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELNest.T_iterate_bAng

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-! ## A private copy of the pure circle-arc length bound

The module `Submission/Work/ELAssembly/nearArc_length_bound.lean` states exactly the pure
real-variable bound that the proof below consumes, but it is not needed as an import: the
argument is short and is reproduced here, privately, so that this file is self-contained. -/

/-- **A circular arc avoiding two cyclic arcs is not longer than the two near arcs.**
Let `0 < β < γ < δ < 1` and let the "near" set be `N = (β, γ) ∪ (δ, 1) ⊆ ℝ/ℤ`.  If the circular
arc `{Int.fract (r + s) | s ∈ (0, L)}` of length `L` is contained in `N`, then
`L ≤ (γ - β) + (1 - δ)` (indeed `L ≤ γ - β` or `L ≤ 1 - δ`, according to where `Int.fract r`
lies). -/
private lemma nearArc_bound {β γ δ r L : ℝ} (hβ : 0 < β) (hβγ : β < γ) (hγδ : γ < δ)
    (hδ : δ < 1) (hL : 0 < L)
    (h : ∀ s ∈ Set.Ioo (0 : ℝ) L, Int.fract (r + s) ∈ Set.Ioo β γ ∪ Set.Ioo δ 1) :
    L ≤ (γ - β) + (1 - δ) := by
  have hβ1 : β < 1 := lt_trans hβγ (lt_trans hγδ hδ)
  set q : ℝ := Int.fract r with hq
  have hq0 : 0 ≤ q := Int.fract_nonneg r
  have hq1 : q < 1 := Int.fract_lt_one r
  -- the fractional parts of `r + s` and of `q + s` agree
  have hfract : ∀ s : ℝ, Int.fract (r + s) = Int.fract (q + s) := by
    intro s
    have hff := Int.floor_add_fract r
    have hrs : r + s = (q + s) + (⌊r⌋ : ℝ) := by rw [hq]; linarith
    rw [hrs, Int.fract_add_intCast]
  -- `q = fract r` cannot lie in the first far arc
  have hqβ : β ≤ q := by
    by_contra hcon
    push_neg at hcon
    set s : ℝ := min L (β - q) / 2 with hs
    have hmpos : 0 < min L (β - q) := lt_min hL (by linarith)
    have hle1 : min L (β - q) ≤ L := min_le_left _ _
    have hle2 : min L (β - q) ≤ β - q := min_le_right _ _
    have hs0 : 0 < s := by rw [hs]; linarith
    have hsL : s < L := by rw [hs]; linarith
    have hsβ : q + s < β := by rw [hs]; linarith
    have hfrac : Int.fract (q + s) = q + s :=
      Int.fract_eq_self.mpr ⟨by linarith, lt_trans hsβ hβ1⟩
    have hmem := h s ⟨hs0, hsL⟩
    rw [hfract s, hfrac] at hmem
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  -- if `q` missed the second far arc from below then `L ≤ γ - q`
  have hcase2 : q < γ → L ≤ γ - q := by
    intro hqγ
    by_contra hcon
    push_neg at hcon
    set s : ℝ := (γ - q + min L (δ - q)) / 2 with hs
    have hmγ : γ - q < min L (δ - q) := lt_min hcon (by linarith)
    have hle1 : min L (δ - q) ≤ L := min_le_left _ _
    have hle2 : min L (δ - q) ≤ δ - q := min_le_right _ _
    have hs0 : 0 < s := by rw [hs]; linarith
    have hsL : s < L := by rw [hs]; linarith
    have hsγ : γ < q + s := by rw [hs]; linarith
    have hsδ : q + s < δ := by rw [hs]; linarith
    have hfrac : Int.fract (q + s) = q + s :=
      Int.fract_eq_self.mpr ⟨by linarith, lt_trans hsδ hδ⟩
    have hmem := h s ⟨hs0, hsL⟩
    rw [hfract s, hfrac] at hmem
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  -- if `q` missed the second far arc from below and above then it is past `δ`
  have hcase3 : γ ≤ q → δ ≤ q := by
    intro hγq
    by_contra hcon
    push_neg at hcon
    set s : ℝ := min L (δ - q) / 2 with hs
    have hmpos : 0 < min L (δ - q) := lt_min hL (by linarith)
    have hle1 : min L (δ - q) ≤ L := min_le_left _ _
    have hle2 : min L (δ - q) ≤ δ - q := min_le_right _ _
    have hs0 : 0 < s := by rw [hs]; linarith
    have hsL : s < L := by rw [hs]; linarith
    have hsδ : q + s < δ := by rw [hs]; linarith
    have hfrac : Int.fract (q + s) = q + s :=
      Int.fract_eq_self.mpr ⟨by linarith, lt_trans hsδ hδ⟩
    have hmem := h s ⟨hs0, hsL⟩
    rw [hfract s, hfrac] at hmem
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  -- and then `L` cannot exceed the remaining part of the line
  have hcase4 : δ ≤ q → L ≤ 1 - q := by
    intro hδq
    by_contra hcon
    push_neg at hcon
    set s : ℝ := (1 - q + min L (1 - q + β)) / 2 with hs
    have hm1 : 1 - q < min L (1 - q + β) := lt_min hcon (by linarith)
    have hle1 : min L (1 - q + β) ≤ L := min_le_left _ _
    have hle2 : min L (1 - q + β) ≤ 1 - q + β := min_le_right _ _
    have hs0 : 0 < s := by rw [hs]; linarith
    have hsL : s < L := by rw [hs]; linarith
    have hs1 : 1 < q + s := by rw [hs]; linarith
    have hsβ : q + s < 1 + β := by rw [hs]; linarith
    have hfrac : Int.fract (q + s) = q + s - 1 := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, ⟨1, ?_⟩⟩
      push_cast
      ring
    have hmem := h s ⟨hs0, hsL⟩
    rw [hfract s, hfrac] at hmem
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  rcases lt_or_ge q γ with hqγ | hqγ
  · have h2 := hcase2 hqγ
    linarith
  · have h3 := hcase3 hqγ
    have h4 := hcase4 h3
    linarith

/-! ## The two cyclic arcs of a four-angle window -/

/-- The length of the cyclic arc from `a` to `b` is the difference `b - a` when the window
`[a, b]` has length less than `1`. -/
private lemma arcLen_eq_sub {a b : ℝ} (hab : a < b) (hb : b < a + 1) :
    Work.EL.arcLen a b = b - a := by
  unfold Work.EL.arcLen
  exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩

/-- An angle avoiding the closed cyclic arc `[A, B]` of a window `A < B < A + 1` lies
strictly beyond `B` in the shifted coordinate `fract (· - A)`. -/
private lemma not_inClosedArc_left {A B y : ℝ} (hAB : A < B) (hB : B < A + 1)
    (h : ¬ Work.EL.InClosedArc y A B) : B - A < Int.fract (y - A) := by
  rw [Work.EL.InClosedArc, arcLen_eq_sub hAB hB] at h
  by_contra hc
  push_neg at hc
  exact h ⟨Int.fract_nonneg _, hc⟩

/-- An angle avoiding the closed cyclic arc `[C, D]` of a window `A < C < D < A + 1` lies
outside the interval `[C - A, D - A]` in the shifted coordinate `fract (· - A)`. -/
private lemma not_inClosedArc_right {A C D y : ℝ} (hAC : A < C) (hCD : C < D)
    (hD : D < A + 1) (h : ¬ Work.EL.InClosedArc y C D) :
    Int.fract (y - A) < C - A ∨ D - A < Int.fract (y - A) := by
  rcases le_or_gt (C - A) (Int.fract (y - A)) with hge | hlt
  · right
    have hfy : Int.fract (y - C) = Int.fract (Int.fract (y - A) - (C - A)) := by
      rw [Int.fract_eq_fract]
      refine ⟨⌊y - A⌋, ?_⟩
      have hff := Int.floor_add_fract (y - A)
      linarith
    have hz1 : Int.fract (y - A) < 1 := Int.fract_lt_one (y - A)
    have hval : Int.fract (Int.fract (y - A) - (C - A))
        = Int.fract (y - A) - (C - A) :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [Work.EL.InClosedArc, arcLen_eq_sub hCD (by linarith), hfy, hval] at h
    by_contra hc
    push_neg at hc
    exact h ⟨by linarith, by linarith⟩
  · exact Or.inl hlt

/-- **The image of an interval under the angle map `T^[10]` is short whenever it avoids the far
arcs.**  Let `A < B < C < D < A + 1` be the four angles of a two-pair ray polygon (far arcs
`[A, B]` and `[C, D]`; near arcs `(B, C)` and `(D, A+1)`, of total length `(C - B) + (A + 1 - D)`).
If every `x ∈ (x₁, x₂)` is carried by `T^[10] x = Int.fract (1024 * x)` into one of the two near
arcs, then `1024 * (x₂ - x₁) ≤ (C - B) + (A + 1 - D)`.

Suggested proof.  Put `x = x₁ + s/1024` with `s ∈ (0, L)`, `L = 1024 * (x₂ - x₁)`, `r = 1024 * x₁`;
the change of variable is a bijection `(0,L) → (x₁,x₂)`.  Since `T^[10] x = Int.fract (1024 * x)`
(`Work.ELNest.T_iterate_ten`), and `Int.fract (T^[10] x - A) = Int.fract (1024 * x - A) =
Int.fract (r + s)`, the hypothesis says `Int.fract (r + s)` avoids the two closed far arcs.  In the
shifted coordinates `q = Int.fract ((x : ℝ) - A)`:
`¬ InClosedArc y A B ↔ q > B - A` (because `arcLen A B = fract (B - A) = B - A`, using
`0 < B - A < 1`) and `¬ InClosedArc y C D ↔ q ∉ [C - A, D - A]` (because
`InClosedArc y C D ↔ fract (q - (C - A)) ≤ D - C`, using `0 < C - A < D - A < 1`).  So
`q ∈ (B - A, C - A) ∪ (D - A, 1)`, and the pure circle-arc bound `Work.ELAssembly.nearArc_length_bound`
(proved independently; reproduce its argument here as a private helper if you prefer, since the
module may not exist yet) with `β = B - A`, `γ = C - A`, `δ = D - A` gives
`1024 * (x₂ - x₁) ≤ ((C - A) - (B - A)) + (1 - (D - A)) = (C - B) + (A + 1 - D)`.
Note the two equivalences above need `A < B < C < D < A + 1`; no other hypothesis is used. -/
theorem nearArc_length_le {A B C D x₁ x₂ : ℝ} (hAB : A < B) (hBC : B < C) (hCD : C < D)
    (hD : D < A + 1) (hx : x₁ < x₂)
    (h : ∀ x ∈ Set.Ioo x₁ x₂,
      ¬ Work.EL.InClosedArc (Work.EL.T^[10] x) A B ∧
      ¬ Work.EL.InClosedArc (Work.EL.T^[10] x) C D) :
    (1024 : ℝ) * (x₂ - x₁) ≤ (C - B) + (A + 1 - D) := by
  have hB1 : B < A + 1 := by linarith
  have hAC : A < C := lt_trans hAB hBC
  have hA1B : 0 < B - A := by linarith
  have hBC' : B - A < C - A := by linarith
  have hCD' : C - A < D - A := by linarith
  have hD' : D - A < 1 := by linarith
  have hLpos : 0 < (1024 : ℝ) * (x₂ - x₁) := by linarith
  have hmain : ∀ s ∈ Set.Ioo (0 : ℝ) ((1024 : ℝ) * (x₂ - x₁)),
      Int.fract (((1024 : ℝ) * x₁ - A) + s) ∈
        Set.Ioo (B - A) (C - A) ∪ Set.Ioo (D - A) 1 := by
    intro s hs
    obtain ⟨hs0, hsL⟩ := hs
    have hxgt : x₁ < x₁ + s / 1024 := by
      have hpos : 0 < s / 1024 := by positivity
      linarith
    have hxlt : x₁ + s / 1024 < x₂ := by
      have hdiv : s / 1024 < x₂ - x₁ := by
        rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 1024)]
        linarith
      linarith
    obtain ⟨hfar1, hfar2⟩ := h (x₁ + s / 1024) ⟨hxgt, hxlt⟩
    have hTx : Work.EL.T^[10] (x₁ + s / 1024) = Int.fract ((1024 : ℝ) * x₁ + s) := by
      rw [Work.ELNest.T_iterate_ten]
      congr 1
      ring
    rw [hTx] at hfar1 hfar2
    have hfl : Int.fract (((1024 : ℝ) * x₁ - A) + s)
        = Int.fract (Int.fract ((1024 : ℝ) * x₁ + s) - A) := by
      rw [Int.fract_eq_fract]
      refine ⟨⌊(1024 : ℝ) * x₁ + s⌋, ?_⟩
      have hff := Int.floor_add_fract ((1024 : ℝ) * x₁ + s)
      linarith
    have hz1 : B - A < Int.fract (((1024 : ℝ) * x₁ - A) + s) := by
      rw [hfl]
      exact not_inClosedArc_left hAB hB1 hfar1
    have hz2 : Int.fract (((1024 : ℝ) * x₁ - A) + s) < C - A ∨
        D - A < Int.fract (((1024 : ℝ) * x₁ - A) + s) := by
      rw [hfl]
      exact not_inClosedArc_right hAC hCD hD hfar2
    have hz3 : Int.fract (((1024 : ℝ) * x₁ - A) + s) < 1 := Int.fract_lt_one _
    rcases hz2 with h2 | h2
    · exact Or.inl ⟨hz1, h2⟩
    · exact Or.inr ⟨h2, hz3⟩
  have hb := nearArc_bound hA1B hBC' hCD' hD' hLpos hmain
  linarith

end Work.ELAssembly
