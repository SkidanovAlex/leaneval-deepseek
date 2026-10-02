import Mathlib
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELTop.PolyCurve

/-! ## General facts about integer-indexed sequences increasing at each step -/

theorem int_le_add_nat {f : ℤ → ℝ} (hf : ∀ k : ℤ, f k < f (k + 1)) (k : ℤ) (n : ℕ) :
    f k ≤ f (k + (n : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h2 : f (k + (n : ℤ)) < f (k + (n : ℤ) + 1) := hf _
      have h3 : k + (n : ℤ) + 1 = k + (((n : ℕ) + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [h3] at h2
      linarith

theorem int_mono_of_succ {f : ℤ → ℝ} (hf : ∀ k : ℤ, f k < f (k + 1)) : Monotone f := by
  intro i j hij
  have hnn : 0 ≤ j - i := by omega
  have hcast : (((j - i).toNat : ℕ) : ℤ) = j - i := Int.toNat_of_nonneg hnn
  have hj : j = i + (((j - i).toNat : ℕ) : ℤ) := by rw [hcast]; ring
  rw [hj]
  exact int_le_add_nat hf i (j - i).toNat

theorem int_strictMono_of_succ {f : ℤ → ℝ} (hf : ∀ k : ℤ, f k < f (k + 1)) : StrictMono f := by
  intro i j hij
  have h1 : i + 1 ≤ j := by omega
  have h2 := hf i
  have h3 : f (i + 1) ≤ f j := int_mono_of_succ hf h1
  linarith

/-! ## Periodicity lemmas -/

theorem shift_sub {f : ℤ → ℝ} {m : ℕ} (hf : ∀ k : ℤ, f (k + (m : ℤ)) = f k + 1) (k : ℤ) :
    f (k - (m : ℤ)) = f k - 1 := by
  have h := hf (k - (m : ℤ))
  rw [sub_add_cancel] at h
  linarith

theorem shift_of_add {f : ℤ → ℝ} {m : ℕ} (hf : ∀ k : ℤ, f (k + (m : ℤ)) = f k + 1)
    (k q : ℤ) : f (k + (m : ℤ) * q) = f k + (q : ℝ) := by
  induction q using Int.induction_on with
  | zero => simp
  | succ i ih =>
      have h1 : k + (m : ℤ) * (↑i + 1) = (k + (m : ℤ) * (↑i : ℤ)) + (m : ℤ) := by ring
      rw [h1, hf, ih]
      push_cast
      ring
  | pred i ih =>
      have h1 : k + (m : ℤ) * (-(↑i : ℤ) - 1) = (k + (m : ℤ) * (-(↑i : ℤ))) - (m : ℤ) := by ring
      rw [h1, shift_sub hf, ih]
      push_cast
      ring

/-! ## Existence of the interval containing `θ` -/

theorem exists_A_le_lt {A : ℤ → ℝ} {m : ℕ} (hm : 0 < m)
    (hA : ∀ k : ℤ, A (k + (m : ℤ)) = A k + 1) (θ : ℝ) :
    ∃ k : ℤ, A k ≤ θ ∧ θ < A (k + 1) := by
  classical
  set q : ℤ := ⌊θ - A 0⌋ with hq
  have hle : A 0 + (q : ℝ) ≤ θ := by
    have h := Int.floor_le (θ - A 0)
    rw [hq]
    linarith
  have hlt : θ < A 0 + (q : ℝ) + 1 := by
    have h := Int.lt_floor_add_one (θ - A 0)
    rw [hq]
    linarith
  have hAq : A ((m : ℤ) * q) = A 0 + (q : ℝ) := by
    have h := shift_of_add hA 0 q
    simpa using h
  have hAq1 : A ((m : ℤ) * q + (m : ℤ)) = A 0 + (q : ℝ) + 1 := by
    have h := shift_of_add hA 0 (q + 1)
    have h' : (m : ℤ) * (q + 1) = (m : ℤ) * q + (m : ℤ) := by ring
    rw [zero_add, h'] at h
    rw [h]
    push_cast
    ring
  let P : ℕ → Prop := fun j => θ < A ((m : ℤ) * q + (j : ℤ))
  have hPm : P m := by
    dsimp only [P]
    rw [hAq1]
    exact hlt
  have hP0 : ¬ P 0 := by
    dsimp only [P]
    simp only [Nat.cast_zero, add_zero]
    rw [hAq]
    exact not_lt.mpr hle
  have hex : ∃ j, P j := ⟨m, hPm⟩
  have hj0pos : 0 < Nat.find hex := (Nat.find_pos hex).mpr hP0
  have hspec : P (Nat.find hex) := Nat.find_spec hex
  have hmin : ¬ P (Nat.find hex - 1) :=
    Nat.find_min hex (by omega)
  dsimp only [P] at hspec hmin
  have hcast : ((Nat.find hex - 1 : ℕ) : ℤ) = (Nat.find hex : ℤ) - 1 := by omega
  rw [hcast] at hmin
  refine ⟨(m : ℤ) * q + ((Nat.find hex : ℤ) - 1), ?_, ?_⟩
  · exact not_lt.mp hmin
  · have hidx : (m : ℤ) * q + ((Nat.find hex : ℤ) - 1) + 1
        = (m : ℤ) * q + (Nat.find hex : ℤ) := by ring
    rw [hidx]
    exact hspec

/-! ## Disjointness of the open and closed arcs -/

theorem disjoint_open_closed {A B : ℤ → ℝ}
    (hAB : ∀ k : ℤ, A k < B k) (hBA : ∀ k : ℤ, B k < A (k + 1))
    (hAmono : Monotone A) (hBmono : Monotone B)
    {θ : ℝ} {j k : ℤ} (h1 : A j < θ ∧ θ < B j) (h2 : B k ≤ θ ∧ θ ≤ A (k + 1)) : False := by
  rcases lt_trichotomy k j with hkj | hkj | hkj
  · have hAx : A (k + 1) ≤ A j := hAmono (by omega)
    linarith [h2.2, h1.1, hAx]
  · subst hkj
    linarith [h1.2, h2.1]
  · have hBx : B (j + 1) ≤ B k := hBmono (by omega)
    have h3 := hAB (j + 1)
    have h4 := hBA j
    linarith [h1.2, h4, h3, hBx, h2.1]

/-! ## The arcs partition the circle -/

theorem not_between_iff_exists_Icc {A B : ℤ → ℝ}
    (hAB : ∀ k : ℤ, A k < B k) (hBA : ∀ k : ℤ, B k < A (k + 1))
    (hAmono : Monotone A) (hBmono : Monotone B)
    (hex : ∀ θ : ℝ, ∃ k : ℤ, A k ≤ θ ∧ θ < A (k + 1)) (θ : ℝ) :
    (∀ j : ℤ, ¬ (A j < θ ∧ θ < B j)) ↔ ∃ k : ℤ, B k ≤ θ ∧ θ ≤ A (k + 1) := by
  constructor
  · intro h
    obtain ⟨k, hk1, hk2⟩ := hex θ
    by_cases hBk : B k ≤ θ
    · exact ⟨k, hBk, le_of_lt hk2⟩
    · push_neg at hBk
      by_cases hAk : A k < θ
      · exact absurd ⟨hAk, hBk⟩ (h k)
      · push_neg at hAk
        have hθ : θ = A k := le_antisymm hAk hk1
        refine ⟨k - 1, ?_, ?_⟩
        · have h4 := hBA (k - 1)
          have h5 : (k - 1) + 1 = k := by ring
          rw [h5] at h4
          linarith
        · have h5 : (k - 1) + 1 = k := by ring
          rw [h5]
          linarith
  · rintro ⟨k, hk1, hk2⟩ j ⟨hj1, hj2⟩
    exact disjoint_open_closed hAB hBA hAmono hBmono ⟨hj1, hj2⟩ ⟨hk1, hk2⟩

/-! ## `InArc` as membership in a translate of the open interval -/

theorem InArc_iff_exists {A B : ℤ → ℝ} {m : ℕ} (hm : 0 < m)
    (hA : ∀ k : ℤ, A (k + (m : ℤ)) = A k + 1)
    (hAB : ∀ k : ℤ, A k < B k) (hBA : ∀ k : ℤ, B k < A (k + 1))
    (hAmono : Monotone A) (k : ℤ) (θ : ℝ) :
    Work.EL.InArc θ (A k) (B k) ↔ ∃ n : ℤ, A k + (n : ℝ) < θ ∧ θ < B k + (n : ℝ) := by
  have hk1 : A k < B k := hAB k
  have hk2 : B k < A (k + 1) := hBA k
  have hA1 : A (k + 1) ≤ A (k + (m : ℤ)) := hAmono (by omega)
  rw [hA k] at hA1
  have hd_pos : 0 < B k - A k := by linarith
  have hd_lt : B k - A k < 1 := by linarith
  have hfracd : Int.fract (B k - A k) = B k - A k :=
    Int.fract_eq_iff.mpr ⟨le_of_lt hd_pos, hd_lt, ⟨0, by ring⟩⟩
  constructor
  · intro hIn
    unfold Work.EL.InArc Work.EL.arcLen at hIn
    obtain ⟨hpos, hlt⟩ := hIn
    rw [hfracd] at hlt
    have hf := Int.fract_add_floor (θ - A k)
    refine ⟨⌊θ - A k⌋, ?_, ?_⟩
    · linarith
    · linarith
  · rintro ⟨n, hn1, hn2⟩
    unfold Work.EL.InArc Work.EL.arcLen
    have hy0 : 0 < (θ - A k) - (n : ℝ) := by linarith
    have hy1 : (θ - A k) - (n : ℝ) < 1 := by linarith
    have hfrac : Int.fract (θ - A k) = (θ - A k) - (n : ℝ) := by
      rw [← Int.fract_sub_intCast (θ - A k) n]
      exact Int.fract_eq_iff.mpr ⟨le_of_lt hy0, hy1, ⟨0, by ring⟩⟩
    rw [hfrac, hfracd]
    constructor
    · linarith
    · linarith

/-! ## The target theorem -/

theorem notInArc_iff_exists_Icc {A B : ℤ → ℝ} {m : ℕ} (hm : 0 < m)
    (hA : ∀ k : ℤ, A (k + (m : ℤ)) = A k + 1) (hB : ∀ k : ℤ, B (k + (m : ℤ)) = B k + 1)
    (hAB : ∀ k : ℤ, A k < B k) (hBA : ∀ k : ℤ, B k < A (k + 1)) (θ : ℝ) :
    (∀ k : ℤ, ¬ Work.EL.InArc θ (A k) (B k)) ↔ ∃ k : ℤ, B k ≤ θ ∧ θ ≤ A (k + 1) := by
  have hsuccA : ∀ k : ℤ, A k < A (k + 1) := fun k => lt_trans (hAB k) (hBA k)
  have hsuccB : ∀ k : ℤ, B k < B (k + 1) := fun k => lt_trans (hBA k) (hAB (k + 1))
  have hAmono : Monotone A := int_mono_of_succ hsuccA
  have hBmono : Monotone B := int_mono_of_succ hsuccB
  rw [← not_between_iff_exists_Icc hAB hBA hAmono hBmono (fun t => exists_A_le_lt hm hA t) θ]
  constructor
  · intro h j hj
    exact h j ((InArc_iff_exists hm hA hAB hBA hAmono j θ).mpr
      ⟨0, by simpa using hj.1, by simpa using hj.2⟩)
  · intro h k hInk
    obtain ⟨n, hn1, hn2⟩ := (InArc_iff_exists hm hA hAB hBA hAmono k θ).mp hInk
    exact h (k + (m : ℤ) * n)
      ⟨by rw [shift_of_add hA k n]; exact hn1, by rw [shift_of_add hB k n]; exact hn2⟩

end Work.ELTop.PolyCurve
