import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n4_window_modEq_card

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- If `A` is a unit mod `q` and `n ^ m ≡ A ^ m (mod q)` with `m ≥ 1`, then the residue class of
`n` mod `q` differs from that of `A` by an `m`-th root of unity `ζ`:
`(n : ZMod q) = (ζ : ZMod q) * (A : ZMod q)` with `ζ ^ m = 1` in `(ZMod q)ˣ`. -/
lemma zmod_root_of_pow_eq {A q m n : ℕ} [NeZero q] (hm : 1 ≤ m) (hA : A.Coprime q)
    (hn : (n : ZMod q) ^ m = (A : ZMod q) ^ m) :
    ∃ ζ : (ZMod q)ˣ, ζ ^ m = 1 ∧ (n : ZMod q) = (ζ : ZMod q) * (A : ZMod q) := by
  classical
  have hAunit : IsUnit (A : ZMod q) := (ZMod.isUnit_iff_coprime A q).mpr hA
  have hnpow : IsUnit ((n : ZMod q) ^ m) := by rw [hn]; exact hAunit.pow m
  have hnunit : IsUnit (n : ZMod q) :=
    (isUnit_pow_iff (show m ≠ 0 by omega)).mp hnpow
  have hcop : n.Coprime q := (ZMod.isUnit_iff_coprime n q).mp hnunit
  refine ⟨ZMod.unitOfCoprime n hcop * (ZMod.unitOfCoprime A hA)⁻¹, ?_, ?_⟩
  · have hunpow : ZMod.unitOfCoprime n hcop ^ m = ZMod.unitOfCoprime A hA ^ m := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
        ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime]
      exact hn
    rw [mul_pow, hunpow, inv_pow, mul_inv_cancel]
  · have hζuA : ZMod.unitOfCoprime n hcop * (ZMod.unitOfCoprime A hA)⁻¹ *
        ZMod.unitOfCoprime A hA = ZMod.unitOfCoprime n hcop := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have hcoe := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hζuA
    rw [Units.val_mul, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime] at hcoe
    exact hcoe.symm

lemma n4_pow_congr_card {A q m : ℕ} [NeZero q] (hq : 1 ≤ q) (hm : 1 ≤ m) (hA : A.Coprime q) {W : ℝ}
    (hW0 : 0 ≤ W) {S : Finset ℕ}
    (hW : ∀ n ∈ S, |(n : ℝ) - A| ≤ W) (hcong : ∀ n ∈ S, n ^ m ≡ A ^ m [MOD q]) :
    (S.card : ℝ) ≤
      (((Finset.univ : Finset (ZMod q)ˣ).filter (fun ζ ↦ ζ ^ m = 1)).card : ℝ) *
        (2 * W / (q : ℝ) + 1) := by
  classical
  -- convert the given congruences into equalities inside `ZMod q`
  have hcong' : ∀ n ∈ S, (n : ZMod q) ^ m = (A : ZMod q) ^ m := by
    intro n hn
    have h1 : ((n ^ m : ℕ) : ZMod q) = ((A ^ m : ℕ) : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff (n ^ m) (A ^ m) q).mpr (hcong n hn)
    simpa only [Nat.cast_pow] using h1
  -- the canonical `m`-th root of unity attached to each `n ∈ S`
  let φ : ℕ → (ZMod q)ˣ := fun n =>
    if h : n ∈ S then Classical.choose (zmod_root_of_pow_eq hm hA (hcong' n h)) else 1
  have hφ_spec : ∀ n (hn : n ∈ S),
      φ n ^ m = 1 ∧ (n : ZMod q) = (φ n : ZMod q) * (A : ZMod q) := by
    intro n hn
    have hspec := Classical.choose_spec (zmod_root_of_pow_eq hm hA (hcong' n hn))
    simpa only [φ, dite_eq_left hn] using hspec
  -- every element of `S` maps to an `m`-th root of unity
  have hmaps : Set.MapsTo φ ↑S ↑(Finset.univ.filter (fun ζ : (ZMod q)ˣ ↦ ζ ^ m = 1)) := by
    intro n hn
    simp only [Finset.coe_filter, Finset.mem_univ, Set.mem_ofPred_eq, true_and]
    exact (hφ_spec n hn).1
  -- each fiber lies in a single residue class mod `q`, hence has at most `2W/q + 1` elements
  have hfiber : ∀ b ∈ (Finset.univ.filter (fun ζ : (ZMod q)ˣ ↦ ζ ^ m = 1)),
      ((S.filter (fun n => φ n = b)).card : ℝ) ≤ 2 * W / (q : ℝ) + 1 := by
    intro b hb
    apply n4_window_modEq_card (A := (A : ℝ)) hq hW0
    · intro n hn
      exact hW n (Finset.mem_of_mem_filter n hn)
    · intro n hn n' hn'
      have hnS : n ∈ S := Finset.mem_of_mem_filter n hn
      have hn'S : n' ∈ S := Finset.mem_of_mem_filter n' hn'
      have hnφ : φ n = b := (Finset.mem_filter.mp hn).2
      have hn'φ : φ n' = b := (Finset.mem_filter.mp hn').2
      have h1 : (n : ZMod q) = (n' : ZMod q) := by
        rw [(hφ_spec n hnS).2, (hφ_spec n' hn'S).2, hnφ, hn'φ]
      exact (ZMod.natCast_eq_natCast_iff n n' q).mp h1
  calc (S.card : ℝ)
      = ∑ b ∈ (Finset.univ.filter (fun ζ : (ZMod q)ˣ ↦ ζ ^ m = 1)),
          ((S.filter (fun n => φ n = b)).card : ℝ) := by
          rw [Finset.card_eq_sum_card_fiberwise hmaps]; push_cast; rfl
    _ ≤ ∑ b ∈ (Finset.univ.filter (fun ζ : (ZMod q)ˣ ↦ ζ ^ m = 1)),
          (2 * W / (q : ℝ) + 1) := Finset.sum_le_sum hfiber
    _ = (((Finset.univ : Finset (ZMod q)ˣ).filter (fun ζ ↦ ζ ^ m = 1)).card : ℝ) *
          (2 * W / (q : ℝ) + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]

end Work.BMF
