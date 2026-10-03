import Mathlib
import Submission.Work.FIArea7.FIsymbols

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-! ## Counting integers of a fixed residue class in an interval

The two elementary lemmas below are the "elementary counting" of *FI* §21: an interval of `N`
consecutive integers meets a single residue class modulo `q > 0` in at most `N / q + 1` points.
They are stated for `ℕ` (via the injection `k ↦ k / q`) and for `ℤ` (by translating the interval
`[−R, R]` to `[0, 2R]`). -/

/-- In an interval `[0, n]` of naturals, a residue class modulo `q` meets at most `n / q + 1`
integers: two elements of the same class with the same quotient by `q` coincide.  (The statement
is in fact true also for `q = 0`, where it says `≤ 1`.) -/
private lemma card_Icc_nat_filter_mod_le {q : ℕ} (hq : 0 < q) (n : ℕ) (c : ZMod q) :
    ((Finset.Icc 0 n).filter (fun (k : ℕ) => (k : ZMod q) = c)).card ≤ n / q + 1 := by
  have _ := hq
  classical
  refine le_trans (Finset.card_le_card_of_injOn (t := Finset.Icc 0 (n / q))
    (fun k : ℕ => k / q) ?_ ?_) ?_
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hk
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_div_right hk.1.2⟩
  · intro k hk k' hk' h
    have h : k / q = k' / q := h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hk hk'
    have hkq : k % q = k' % q := by
      have h1 : (k : ZMod q) = (k' : ZMod q) := hk.2.trans hk'.2.symm
      exact (ZMod.natCast_eq_natCast_iff k k' q).mp h1
    have h1 := Nat.div_add_mod k q
    have h2 := Nat.div_add_mod k' q
    rw [← h1, ← h2, h, hkq]
  · rw [Nat.card_Icc]; simp

/-- In the integer interval `[−R, R]`, a residue class modulo `q` meets at most
`(2R+1) / q + 1` integers: shift by `R` to `[0, 2R]` (`a ↦ (a + R).toNat`) and apply
`card_Icc_nat_filter_mod_le`.  For `R < 0` the interval is empty and the bound is trivial. -/
private lemma card_Icc_int_filter_mod_le (R : ℤ) {q : ℕ} (hq : 0 < q) (u : ℤ) :
    ((Finset.Icc (-R) R).filter (fun (a : ℤ) => (a : ZMod q) = (u : ZMod q))).card
      ≤ (2 * R + 1).toNat / q + 1 := by
  classical
  refine le_trans (Finset.card_le_card_of_injOn
    (t := (Finset.Icc 0 ((2 * R + 1).toNat)).filter
      (fun (k : ℕ) => (k : ZMod q) = ((u + R : ℤ) : ZMod q)))
    (fun a : ℤ => (a + R).toNat) ?_ ?_) ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨h1, h2⟩, hmod⟩ := ha
    have h0 : 0 ≤ a + R := by linarith
    have h3 : a + R ≤ 2 * R + 1 := by linarith
    have hnn : (0 : ℤ) ≤ 2 * R + 1 := le_trans h0 h3
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩, ?_⟩
    · rw [Int.toNat_le, Int.toNat_of_nonneg hnn]; exact h3
    · have h4 : ((a + R : ℤ) : ZMod q) = ((u + R : ℤ) : ZMod q) := by
        rw [Int.cast_add, Int.cast_add, hmod]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
      exact h4
  · intro a ha a' ha' h
    have h : (a + R).toNat = (a' + R).toNat := h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha ha'
    have h1 : 0 ≤ a + R := by linarith [ha.1.1]
    have h2 : 0 ≤ a' + R := by linarith [ha'.1.1]
    have h3 : a + R = a' + R := by
      have := congrArg (fun n : ℕ => (n : ℤ)) h
      rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at this
      exact this
    linarith
  · exact card_Icc_nat_filter_mod_le hq _ _

/-- **The residue-class count in the box, used by the character expansion of *FI* §§16–21.**

The box `gBox R = {|re| ≤ R, |im| ≤ R}` contains at most `((2R+1)/q + 1)²` Gaussian integers in
any fixed class mod `q` (i.e. with `re ≡ u` and `im ≡ v (mod q)`): in each coordinate, `[−R,R]`
meets a single residue class mod `q` in at most `(2R+1)/q + 1` points, and the box is the product
of the two coordinate ranges (`Work.FIPlan.gBox` is the injective image of
`Icc (−R) R × Icc (−R) R`, `Work.FIPlan.gaussMk_injective`).

This is the "elementary counting" of the proof of Lemma 21.1/21.2 (`FI`: *"Splitting the inner
summation into residue classes `ζ (mod q)` … we get by elementary counting"*), which turns a sum
over `z` of a character of modulus `q` into `(1/q²)·(sum over the box)` plus an error of the shape
`(2R+1)²/q + (2R+1) + q²`; it is the counting half of the bilinear-form estimates of §21, and it
applies verbatim to the frozen sums, which range over `Work.FIPlan.gBox (Work.FITop.radN Pa)`.

Verified numerically (no counterexample over `0 ≤ R ≤ 13`, `1 ≤ q ≤ 15`, `|u|,|v| ≤ 3`).  For
`R < 0` the box is empty, so the left side is `0` and the inequality is trivial (`(2R+1).toNat = 0`
makes the right side `1`); `hq : 0 < q` is what makes the statement meaningful (for `q = 0` every
`z` is in the class and the bound would be false). -/
theorem card_gBox_filter_mod (R : ℤ) (q : ℕ) (hq : 0 < q) (u v : ℤ) :
    ((Work.FIPlan.gBox R).filter
        (fun z => ((z.re : ZMod q) = (u : ZMod q)) ∧ ((z.im : ZMod q) = (v : ZMod q)))).card
      ≤ ((2 * R + 1).toNat / q + 1) * ((2 * R + 1).toNat / q + 1) := by
  classical
  -- the box is the injective image of the product `[−R,R] × [−R,R]`
  have hbox : Work.FIPlan.gBox R
      = ((Finset.Icc (-R) R) ×ˢ (Finset.Icc (-R) R)).image
          (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : GaussianInt)) := by
    rw [Work.FIPlan.gBox, Finset.product_eq_sprod]
  rw [hbox, Finset.filter_image]
  rw [Finset.card_image_of_injective _ Work.FIPlan.gaussMk_injective]
  -- the class condition is a product condition on the two coordinates
  rw [Finset.filter_product (fun (a : ℤ) => (a : ZMod q) = (u : ZMod q))
    (fun (b : ℤ) => (b : ZMod q) = (v : ZMod q))]
  rw [Finset.card_product]
  exact Nat.mul_le_mul (card_Icc_int_filter_mod_le R hq u) (card_Icc_int_filter_mod_le R hq v)

end Work.FIArea7
