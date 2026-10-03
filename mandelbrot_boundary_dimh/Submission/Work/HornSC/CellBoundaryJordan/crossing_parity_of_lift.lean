import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.ray_crossing_parity

/-!
# Parity of the number of level crossings of a periodic lift

Let `Θ : ℝ → ℝ` be continuous and periodic up to a drift: `Θ (t + 1) = Θ t + m·2π`, with `Θ 0`
*not* a multiple of `2π`.  Suppose that `Θ` crosses the levels `2πℤ` transversally on `[0,1)`
(`hstrict`: at every crossing time the product `(Θ u - Θ t)(u - t)` has a constant sign near `t`),
and that the set `S` of crossing times in `[0,1)` is finite.

Then the number of crossings in one period has the same parity as the drift `m`.

The proof defines the *strip index* `strip Θ t = ⌊Θ t / 2π⌋`, which is locally constant off the
crossing set and jumps by `±1` across each crossing (`strip_jump`).  Hence the predicate
`t ↦ Even (strip Θ t)` flips at every point of `S` and is locally constant elsewhere, so the
counting lemma `even_card_iff_parity` applied on `[0,1]` gives
`(Even (strip Θ 0) ↔ Even (strip Θ 1)) ↔ Even |S|`, while `strip Θ 1 = strip Θ 0 + m` telescopes the
drift, yielding `Even m ↔ Even |S|`, i.e. `Odd |S| ↔ Odd m`.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

noncomputable section

/-- The strip index of `Θ` at `t`: the integer `k` with `k·2π ≤ Θ t < (k+1)·2π`. -/
private def strip (Θ : ℝ → ℝ) (t : ℝ) : ℤ := ⌊Θ t / (2 * Real.pi)⌋

/-- `strip` is characterised by the strict inequalities of the strip. -/
private lemma strip_eq_of_strip {Θ : ℝ → ℝ} {t : ℝ} {n : ℤ}
    (h1 : (n:ℝ) * (2*Real.pi) < Θ t) (h2 : Θ t < ((n:ℝ) + 1) * (2*Real.pi)) :
    strip Θ t = n := by
  have h2π : (0:ℝ) < 2*Real.pi := by positivity
  rw [strip, Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ h2π]; linarith
  · rw [div_lt_iff₀ h2π]; linarith

/-- **`strip` is locally constant off the levels `2πℤ`.** -/
private lemma strip_local {Θ : ℝ → ℝ} (hΘc : Continuous Θ) {t : ℝ}
    (ht : ¬ ∃ n : ℤ, Θ t = (n:ℝ) * (2*Real.pi)) :
    ∃ δ > 0, ∀ u, |u - t| < δ → strip Θ u = strip Θ t := by
  have h2π : (0:ℝ) < 2*Real.pi := by positivity
  have hle : (strip Θ t : ℝ) * (2*Real.pi) ≤ Θ t := by
    have h := Int.floor_le (Θ t / (2*Real.pi))
    rw [strip]
    rwa [le_div_iff₀ h2π] at h
  have hlt : (strip Θ t : ℝ) * (2*Real.pi) < Θ t := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd ⟨strip Θ t, by rw [← h]⟩ ht
  have hgt : Θ t < ((strip Θ t : ℝ) + 1) * (2*Real.pi) := by
    have h := Int.lt_floor_add_one (Θ t / (2*Real.pi))
    rw [strip]
    have h' := (div_lt_iff₀ h2π).mp h
    linarith
  have hε : 0 < min (Θ t - (strip Θ t : ℝ) * (2*Real.pi))
      (((strip Θ t : ℝ) + 1) * (2*Real.pi) - Θ t) := lt_min (by linarith) (by linarith)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hΘc.continuousAt _ hε
  refine ⟨δ, hδpos, fun u hu => ?_⟩
  have hd : |Θ u - Θ t| < min (Θ t - (strip Θ t : ℝ)*(2*Real.pi))
      (((strip Θ t : ℝ)+1)*(2*Real.pi) - Θ t) := by
    have := hδ (show dist u t < δ from by simpa [Real.dist_eq] using hu)
    simpa [Real.dist_eq] using this
  have h1 : (strip Θ t : ℝ)*(2*Real.pi) < Θ u := by
    have h2 := lt_of_lt_of_le hd (min_le_left _ _)
    rw [abs_lt] at h2
    linarith [h2.1]
  have h2 : Θ u < ((strip Θ t : ℝ)+1)*(2*Real.pi) := by
    have h3 := lt_of_lt_of_le hd (min_le_right _ _)
    rw [abs_lt] at h3
    linarith [h3.2]
  exact strip_eq_of_strip h1 h2

/-- **The jump of the strip index at a transversal crossing.**  If `Θ t = n·2π` and `Θ` crosses the
level `n·2π` transversally at `t`, then near `t` the index is `n-1` on one side and `n` on the
other (which side is which depending on the direction of the crossing). -/
private lemma strip_jump {Θ : ℝ → ℝ} (hΘc : Continuous Θ)
    (hstrict : ∀ t : ℝ, t ∈ Set.Ico (0:ℝ) 1 → (∃ n : ℤ, Θ t = (n:ℝ)*(2*Real.pi)) →
      ∃ δ : ℝ, 0 < δ ∧
        ((∀ u : ℝ, |u - t| < δ → u ≠ t → (Θ u - Θ t)*(u - t) > 0) ∨
         (∀ u : ℝ, |u - t| < δ → u ≠ t → (Θ u - Θ t)*(u - t) < 0)))
    {t : ℝ} (htI : t ∈ Set.Ico (0:ℝ) 1) {n : ℤ} (htn : Θ t = (n:ℝ)*(2*Real.pi)) :
    ∃ δ > 0, ((∀ u, |u - t| < δ → u < t → strip Θ u = n - 1) ∧
              (∀ u, |u - t| < δ → t < u → strip Θ u = n)) ∨
             ((∀ u, |u - t| < δ → u < t → strip Θ u = n) ∧
              (∀ u, |u - t| < δ → t < u → strip Θ u = n - 1)) := by
  have h2π : (0:ℝ) < 2*Real.pi := by positivity
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hstrict t htI ⟨n, htn⟩
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.continuousAt_iff.mp hΘc.continuousAt (2*Real.pi) h2π
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  have hclose : ∀ u, |u - t| < min δ₁ δ₂ → |Θ u - Θ t| < 2*Real.pi := fun u hu => by
    have hdt : dist u t < δ₂ :=
      lt_of_lt_of_le (by simpa [Real.dist_eq] using hu) (min_le_right _ _)
    have := hδ₂ hdt
    simpa [Real.dist_eq] using this
  have hlt1 : ∀ u, |u - t| < min δ₁ δ₂ → |u - t| < δ₁ := fun u hu =>
    lt_of_lt_of_le hu (min_le_left _ _)
  rcases hδ₁ with hinc | hdec
  · left
    have hbelow : ∀ u, |u - t| < min δ₁ δ₂ → u < t → Θ u < Θ t := by
      intro u hu hut
      have hp := hinc u (hlt1 u hu) (ne_of_lt hut)
      have h1 : u - t < 0 := by linarith
      nlinarith
    have habove : ∀ u, |u - t| < min δ₁ δ₂ → t < u → Θ t < Θ u := by
      intro u hu htu
      have hp := hinc u (hlt1 u hu) (ne_of_gt htu)
      have h1 : 0 < u - t := by linarith
      nlinarith
    constructor
    · intro u hu hut
      have hb := hbelow u hu hut
      have hcl := hclose u hu
      rw [abs_lt] at hcl
      rw [htn] at hb
      exact strip_eq_of_strip (by push_cast; linarith [hcl.1, hb]) (by push_cast; linarith)
    · intro u hu htu
      have ha := habove u hu htu
      have hcl := hclose u hu
      rw [abs_lt] at hcl
      rw [htn] at ha
      exact strip_eq_of_strip (by linarith) (by linarith [hcl.2, ha])
  · right
    have hbelow : ∀ u, |u - t| < min δ₁ δ₂ → u < t → Θ t < Θ u := by
      intro u hu hut
      have hp := hdec u (hlt1 u hu) (ne_of_lt hut)
      have h1 : u - t < 0 := by linarith
      nlinarith
    have habove : ∀ u, |u - t| < min δ₁ δ₂ → t < u → Θ u < Θ t := by
      intro u hu htu
      have hp := hdec u (hlt1 u hu) (ne_of_gt htu)
      have h1 : 0 < u - t := by linarith
      nlinarith
    constructor
    · intro u hu hut
      have hb := hbelow u hu hut
      have hcl := hclose u hu
      rw [abs_lt] at hcl
      rw [htn] at hb
      exact strip_eq_of_strip (by linarith) (by linarith [hcl.2, hb])
    · intro u hu htu
      have ha := habove u hu htu
      have hcl := hclose u hu
      rw [abs_lt] at hcl
      rw [htn] at ha
      exact strip_eq_of_strip (by push_cast; linarith [hcl.1, ha]) (by push_cast; linarith)

/-- Parity flips when subtracting one. -/
private lemma parity_flip (k : ℤ) : Even k ↔ ¬ Even (k - 1) := by
  have h : Even (k - 1) ↔ ¬ Even k := by rw [Int.even_sub]; simp
  tauto

/-- Parity flips when subtracting one (the other orientation). -/
private lemma parity_flip' (k : ℤ) : Even (k - 1) ↔ ¬ Even k := by
  rw [Int.even_sub]; simp

theorem crossing_parity_of_lift {Θ : ℝ → ℝ} (hΘc : Continuous Θ) {m : ℤ}
    (hper : ∀ t, Θ (t + 1) = Θ t + (m : ℝ) * (2 * Real.pi))
    (h0 : ¬ ∃ n : ℤ, Θ 0 = (n : ℝ) * (2 * Real.pi))
    (hstrict : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → (∃ n : ℤ, Θ t = (n : ℝ) * (2 * Real.pi)) →
      ∃ δ : ℝ, 0 < δ ∧
        ((∀ u : ℝ, |u - t| < δ → u ≠ t → (Θ u - Θ t) * (u - t) > 0) ∨
         (∀ u : ℝ, |u - t| < δ → u ≠ t → (Θ u - Θ t) * (u - t) < 0)))
    (hfin : {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ n : ℤ, Θ t = (n : ℝ) * (2 * Real.pi)}.Finite) :
    (Odd {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ n : ℤ, Θ t = (n : ℝ) * (2 * Real.pi)}.ncard ↔
      Odd m) := by
  classical
  have h2π : (0:ℝ) < 2*Real.pi := by positivity
  have hmem : ∀ t : ℝ, t ∈ hfin.toFinset ↔
      (t ∈ Set.Ico (0:ℝ) 1 ∧ ∃ n : ℤ, Θ t = (n:ℝ)*(2*Real.pi)) :=
    fun t => Set.Finite.mem_toFinset hfin
  -- `0` is not a crossing time
  have h0T : (0:ℝ) ∉ hfin.toFinset := fun h => h0 ((hmem 0).mp h).2
  -- `1` is not a level `2πℤ` either (it differs from `Θ 0` by `m·2π`)
  have h1mult : ¬ ∃ n : ℤ, Θ 1 = (n:ℝ)*(2*Real.pi) := by
    rintro ⟨n, hn⟩
    refine h0 ⟨n - m, ?_⟩
    have hp := hper 0
    rw [zero_add] at hp
    have hsub : Θ 0 = Θ 1 - (m:ℝ)*(2*Real.pi) := by linarith
    rw [hsub, hn]; push_cast; ring
  have h1T : (1:ℝ) ∉ hfin.toFinset := fun h => (not_lt.mpr le_rfl) ((hmem 1).mp h).1.2
  -- every crossing time lies strictly inside `(0,1)`
  have hTsub : ∀ t ∈ hfin.toFinset, (0:ℝ) < t ∧ t < 1 := by
    intro t ht
    obtain ⟨⟨ht0, ht1⟩, htM⟩ := (hmem t).mp ht
    refine ⟨lt_of_le_of_ne ht0 ?_, ht1⟩
    intro h
    obtain ⟨n, hn⟩ := htM
    exact h0 ⟨n, by rw [h]; exact hn⟩
  -- the parity of the strip index is locally constant off the crossings
  have hloc : ∀ t ∈ Set.Icc (0:ℝ) 1, t ∉ hfin.toFinset →
      ∃ δ > 0, ∀ s, |s - t| < δ → (Even (strip Θ s) ↔ Even (strip Θ t)) := by
    intro t htI htT
    have htmult : ¬ ∃ n : ℤ, Θ t = (n:ℝ)*(2*Real.pi) := by
      rintro ⟨n, hn⟩
      by_cases hlt : t < 1
      · exact htT ((hmem t).mpr ⟨⟨htI.1, hlt⟩, n, hn⟩)
      · have ht1 : t = 1 := le_antisymm htI.2 (not_lt.mp hlt)
        rw [ht1] at hn
        exact h1mult ⟨n, hn⟩
    obtain ⟨δ, hδpos, hδ⟩ := strip_local hΘc htmult
    exact ⟨δ, hδpos, fun s hs => by rw [hδ s hs]⟩
  -- the parity of the strip index flips at every crossing
  have hflip : ∀ t ∈ hfin.toFinset, ∃ δ > 0, ∀ s, 0 < s → s < δ →
      (Even (strip Θ (t + s)) ↔ ¬ Even (strip Θ (t - s))) := by
    intro t ht
    obtain ⟨⟨ht0, ht1⟩, n, hn⟩ := (hmem t).mp ht
    obtain ⟨δ, hδpos, hδ⟩ := strip_jump hΘc hstrict ⟨ht0, ht1⟩ hn
    refine ⟨δ, hδpos, ?_⟩
    intro s hs0 hsd
    have h1 : |(t + s) - t| < δ := by rw [add_sub_cancel_left, abs_of_pos hs0]; exact hsd
    have h2 : |(t - s) - t| < δ := by
      have hsub : (t - s) - t = -s := by ring
      rw [hsub, abs_neg, abs_of_pos hs0]; exact hsd
    rcases hδ with ⟨hL, hR⟩ | ⟨hL, hR⟩
    · rw [hR (t+s) h1 (by linarith), hL (t-s) h2 (by linarith)]
      exact parity_flip n
    · rw [hR (t+s) h1 (by linarith), hL (t-s) h2 (by linarith)]
      exact parity_flip' n
  have key := even_card_iff_parity (S := hfin.toFinset) (a := 0) (b := 1)
      (P := fun t => Even (strip Θ t)) (by norm_num) hTsub hloc hflip
  -- the drift telescopes the strip index
  have hK1 : strip Θ 1 = strip Θ 0 + m := by
    have hp := hper 0
    rw [zero_add] at hp
    have hdiv : Θ 1 / (2*Real.pi) = Θ 0 / (2*Real.pi) + (m:ℝ) := by
      rw [hp]; field_simp
    rw [strip, strip, hdiv, Int.floor_add_intCast]
  have hevenm : Even m ↔ Even hfin.toFinset.card := by
    have h1 : Even (strip Θ 1) ↔ (Even (strip Θ 0) ↔ Even m) := by
      rw [hK1]; exact Int.even_add
    rw [← key, h1]
    tauto
  have hncard : {t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧ ∃ n : ℤ, Θ t = (n:ℝ)*(2*Real.pi)}.ncard
      = hfin.toFinset.card := Set.ncard_eq_toFinset_card _ hfin
  rw [hncard, ← Nat.not_even_iff_odd, ← Int.not_even_iff_odd, hevenm]

end

end Work.HornSC.CellBoundaryJordan
