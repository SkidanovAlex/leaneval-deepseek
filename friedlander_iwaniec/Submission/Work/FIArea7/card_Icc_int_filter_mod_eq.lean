import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace Work.FIArea7

/-! ## Auxiliary counting lemmas

`card_range_filter_mod` is the `ℕ`-form of the exact residue-class count in `[0, n)`; it is a
direct consequence of `Nat.count_modEq_card`.  `card_Icc_int_filter_mod_eq_range` transfers it to
the symmetric integer interval `[−R, R]` (for `R ≥ 0`) by the bijection `a ↦ (a + R).toNat`
onto `range (2R+1)`. -/

/-- In `[0, n)`, a residue class modulo `q > 0` represented by `v < q` occurs `n / q` times, plus
one more when `v < n % q`.  In particular it occurs `n / q` or `n / q + 1` times. -/
theorem card_range_filter_mod {n q : ℕ} (hq : 0 < q) (v : ℕ) (hv : v < q) :
    ((Finset.range n).filter (fun k : ℕ => k % q = v)).card
      = n / q + (if v < n % q then 1 else 0) := by
  have hfil : (Finset.range n).filter (fun k : ℕ => k % q = v)
      = (Finset.range n).filter (fun k : ℕ => k ≡ v [MOD q]) := by
    apply Finset.filter_congr
    intro k _
    simp only [Nat.ModEq, Nat.mod_eq_of_lt hv]
  rw [hfil, ← Nat.count_eq_card_filter_range (p := fun k : ℕ => k ≡ v [MOD q]),
    Nat.count_modEq_card n hq v, Nat.mod_eq_of_lt hv]

/-- For `R ≥ 0`, the residue-class count in `[−R, R]` equals the count in `range (2R+1)`, the
bijection being `a ↦ (a + R).toNat`. -/
theorem card_Icc_int_filter_mod_eq_range (R : ℤ) (hR : 0 ≤ R) {q : ℕ} (hq : 0 < q)
    (u : ZMod q) :
    ((Finset.Icc (-R) R).filter (fun a : ℤ => (a : ZMod q) = u)).card
      = ((Finset.range (2 * R + 1).toNat).filter
          (fun k : ℕ => k % q = (u + (R : ZMod q)).val)).card := by
  classical
  haveI : NeZero q := ⟨hq.ne'⟩
  set n : ℕ := (2 * R + 1).toNat with hn
  set v : ℕ := (u + (R : ZMod q)).val with hv
  have hn2 : (n : ℤ) = 2 * R + 1 := by
    rw [hn]; exact Int.toNat_of_nonneg (by linarith)
  have hvlt : v < q := by rw [hv]; exact ZMod.val_lt _
  refine Finset.card_bij
    (fun a (_ : a ∈ (Finset.Icc (-R) R).filter (fun a : ℤ => (a : ZMod q) = u)) =>
      (a + R).toNat) ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    obtain ⟨haI, haP⟩ := ha
    rw [Finset.mem_Icc] at haI
    obtain ⟨h1, h2⟩ := haI
    have h0 : 0 ≤ a + R := by linarith
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_range]
      have : ((a + R).toNat : ℤ) < (n : ℤ) := by
        rw [Int.toNat_of_nonneg h0, hn2]; linarith
      exact_mod_cast this
    · have hmod : ((a + R).toNat : ZMod q) = u + (R : ZMod q) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
        push_cast
        rw [haP]
      have := congrArg ZMod.val hmod
      rw [ZMod.val_natCast] at this
      simpa [hv] using this
  · intro a1 ha1 a2 ha2 heq
    rw [Finset.mem_filter, Finset.mem_Icc] at ha1 ha2
    have h1 : 0 ≤ a1 + R := by linarith [ha1.1.1]
    have h2 : 0 ≤ a2 + R := by linarith [ha2.1.1]
    have heq' : ((a1 + R).toNat : ℤ) = ((a2 + R).toNat : ℤ) := by rw [heq]
    rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at heq'
    linarith
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hklt, hkmod⟩ := hk
    refine ⟨(k : ℤ) - R, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
      have hklt' : (k : ℤ) < (n : ℤ) := by exact_mod_cast hklt
      rw [hn2] at hklt'
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      have hkq : (k : ZMod q) = (v : ZMod q) := by
        rw [ZMod.natCast_eq_natCast_iff', hkmod, Nat.mod_eq_of_lt hvlt]
      have hval : (v : ZMod q) = u + (R : ZMod q) := by
        rw [hv]; exact ZMod.natCast_zmod_val _
      have : (((k : ℤ) - R : ℤ) : ZMod q) = u := by
        push_cast
        rw [hkq, hval]
        ring
      exact this
    · have : (k : ℤ) - R + R = (k : ℤ) := by ring
      rw [this]
      exact Int.toNat_natCast k

/-- **The exact count of a residue class in a symmetric interval, up to `1`.**  For `q > 0`, the
number of integers `a ∈ [−R, R]` in a fixed residue class mod `q` is `⌊(2R+1)/q⌋` or
`⌊(2R+1)/q⌋ + 1`.  This is the *two-sided* refinement of `Work.FIArea7.card_gBox_filter_mod`
(which gives only `≤ (2R+1)/q + 1`): it is what produces the explicit main term
`((2R+1)/q)²·Σ_{ζ}F(ζ)` and the error `≪ R/q + 1` in the "elementary counting" step of *FI*
Lemma 21.2, where the sum over a box of a periodic function is compared with the sum over the
complete residue system. -/
theorem card_Icc_int_filter_mod_eq (R : ℤ) (q : ℕ) (hq : 0 < q) (u : ZMod q) :
    ∃ θ : ℕ, θ ≤ 1 ∧ ((Finset.Icc (-R) R).filter (fun a : ℤ => (a : ZMod q) = u)).card
      = (2 * R + 1).toNat / q + θ := by
  classical
  by_cases hR : 0 ≤ R
  · refine ⟨if (u + (R : ZMod q)).val < (2 * R + 1).toNat % q then 1 else 0, ?_, ?_⟩
    · split <;> omega
    · haveI : NeZero q := ⟨hq.ne'⟩
      rw [card_Icc_int_filter_mod_eq_range R hR hq u]
      rw [card_range_filter_mod hq ((u + (R : ZMod q)).val) (ZMod.val_lt _)]
  · push Not at hR
    refine ⟨0, by omega, ?_⟩
    have hempty : Finset.Icc (-R) R = ∅ := by
      rw [Finset.Icc_eq_empty_iff]; omega
    have hz : (2 * R + 1).toNat = 0 := Int.toNat_eq_zero.mpr (by linarith)
    rw [hempty, Finset.filter_empty, Finset.card_empty, hz, Nat.zero_div, Nat.zero_add]

end Work.FIArea7
