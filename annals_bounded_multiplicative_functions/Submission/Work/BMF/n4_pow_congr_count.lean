import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n4_window_modEq_card

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset

/-- If `A` is a unit mod `q` and `n ^ m ≡ A ^ m (mod q)` with `m ≥ 1`, then `n` is a unit
mod `q`: a prime dividing both `n` and `q` would divide `n ^ m ≡ A ^ m`, hence `A`, contradiction. -/
private lemma coprime_of_pow_eq_zmod {A q m n : ℕ} (hm : 1 ≤ m) (hA : Nat.Coprime A q)
    (h : (n : ZMod q) ^ m = (A : ZMod q) ^ m) : n.Coprime q := by
  have hAunit : IsUnit (A : ZMod q) := (ZMod.isUnit_iff_coprime A q).mpr hA
  have hnpow : IsUnit ((n : ZMod q) ^ m) := by rw [h]; exact hAunit.pow m
  exact (ZMod.isUnit_iff_coprime n q).mp ((isUnit_pow_iff (n := m) (by omega)).mp hnpow)

/-- The canonical `m`-th root of unity witnessing `n ^ m ≡ A ^ m (mod q)`: it is the quotient of
the units of `n` and of `A` in `(ZMod q)ˣ`. -/
private lemma coe_unitOfCoprime_mul_inv_mul {A q n : ℕ} [NeZero q] (hA : Nat.Coprime A q)
    (hcop : n.Coprime q) :
    (((ZMod.unitOfCoprime n hcop) * (ZMod.unitOfCoprime A hA)⁻¹ : (ZMod q)ˣ) : ZMod q)
      * (A : ZMod q) = (n : ZMod q) := by
  have hAu : ((ZMod.unitOfCoprime A hA : (ZMod q)ˣ) : ZMod q) = (A : ZMod q) :=
    ZMod.coe_unitOfCoprime A hA
  have hnu : ((ZMod.unitOfCoprime n hcop : (ZMod q)ˣ) : ZMod q) = (n : ZMod q) :=
    ZMod.coe_unitOfCoprime n hcop
  have h2 : ((ZMod.unitOfCoprime n hcop) * (ZMod.unitOfCoprime A hA)⁻¹ : (ZMod q)ˣ)
      * ZMod.unitOfCoprime A hA = ZMod.unitOfCoprime n hcop := by
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have h2' := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) h2
  rw [← hAu, ← Units.val_mul, h2', hnu]

/-- **Residue-class count for a power congruence.**  Let `q ≥ 1`, `m ≥ 1`, `A` coprime to `q`,
and let `S` be a finite set of natural numbers lying in a window `|n - A| ≤ W` around `A`
(`W ≥ 0`) and satisfying `n^m ≡ A^m [MOD q]`.  Then

`#S ≤ r_m(q) · (2W/q + 1)`,  `r_m(q) = #(m-torsion of (ZMod q)ˣ)`.

Proof: since `A` is a unit mod `q`, the solutions of `x^m = A^m` in `(ZMod q)ˣ` form a coset of
the subgroup of `m`-th roots of unity, of cardinality `r_m(q)`; any `n` with `n^m ≡ A^m (mod q)`
is automatically coprime to `q` (a prime dividing both `n` and `q` would force `p ∣ A^m`).  So
`S` is contained in at most `r_m(q)` residue classes mod `q`, and each class contributes at most
`2W/q + 1` integers to the window (`Work.BMF.n4_window_modEq_card` in this directory already
proves the one-class case, i.e. the special case `r_m(q) = 1`).
This is the same claim as the (currently unproved) `Work.BMF.n4_pow_congr_card`; it is repeated
here because the consumer needs a proved version. -/
lemma n4_pow_congr_count {A q m : ℕ} [NeZero q] (hq : 1 ≤ q) (hm : 1 ≤ m) (hA : Nat.Coprime A q)
    {W : ℝ} (hW0 : 0 ≤ W) {S : Finset ℕ} (hW : ∀ n ∈ S, |(n : ℝ) - (A : ℝ)| ≤ W)
    (hcong : ∀ n ∈ S, n ^ m ≡ A ^ m [MOD q]) :
    (S.card : ℝ) ≤
      (((Finset.univ : Finset (ZMod q)ˣ).filter (fun ζ ↦ ζ ^ m = 1)).card : ℝ)
        * (2 * W / (q : ℝ) + 1) := by
  classical
  -- the congruences, read inside `ZMod q`
  have hcong' : ∀ n ∈ S, (n : ZMod q) ^ m = (A : ZMod q) ^ m := by
    intro n hn
    have h1 : ((n ^ m : ℕ) : ZMod q) = ((A ^ m : ℕ) : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff (n ^ m) (A ^ m) q).mpr (hcong n hn)
    simpa only [Nat.cast_pow] using h1
  -- the group of `m`-th roots of unity mod `q`
  let T : Finset (ZMod q)ˣ := Finset.univ.filter (fun ζ ↦ ζ ^ m = 1)
  -- the class label attached to `n ∈ S`: the root of unity `n / A` in `(ZMod q)ˣ`
  let φ : ℕ → (ZMod q)ˣ := fun n =>
    if hn : n ∈ S then
      ZMod.unitOfCoprime n (coprime_of_pow_eq_zmod hm hA (hcong' n hn)) *
        (ZMod.unitOfCoprime A hA)⁻¹
    else 1
  have hφ_eq : ∀ n (hn : n ∈ S), φ n =
      ZMod.unitOfCoprime n (coprime_of_pow_eq_zmod hm hA (hcong' n hn)) *
        (ZMod.unitOfCoprime A hA)⁻¹ := fun n hn => dite_eq_left hn
  -- every label is an `m`-th root of unity
  have hφ_mem : ∀ n (hn : n ∈ S), φ n ∈ T := by
    intro n hn
    rw [hφ_eq n hn]
    have hu : (ZMod.unitOfCoprime n (coprime_of_pow_eq_zmod hm hA (hcong' n hn))) ^ m =
        (ZMod.unitOfCoprime A hA) ^ m := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime,
        ZMod.coe_unitOfCoprime]
      exact hcong' n hn
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mul_pow, hu, inv_pow, mul_inv_cancel]
  -- two numbers with the same label are congruent mod `q`
  have hφ_congr : ∀ n ∈ S, ∀ n' ∈ S, φ n = φ n' → n ≡ n' [MOD q] := by
    intro n hn n' hn' h
    refine (ZMod.natCast_eq_natCast_iff n n' q).mp ?_
    have h1 := coe_unitOfCoprime_mul_inv_mul hA (coprime_of_pow_eq_zmod hm hA (hcong' n hn))
    have h2 := coe_unitOfCoprime_mul_inv_mul hA (coprime_of_pow_eq_zmod hm hA (hcong' n' hn'))
    rw [← hφ_eq n hn] at h1
    rw [← hφ_eq n' hn'] at h2
    rw [← h1, ← h2, h]
  -- each label class lies in a single residue class, so contributes at most `2W/q + 1` elements
  have hfiber : ∀ b ∈ T, ((S.filter (fun n ↦ φ n = b)).card : ℝ) ≤ 2 * W / (q : ℝ) + 1 := by
    intro b _
    apply n4_window_modEq_card (A := (A : ℝ)) hq hW0
    · intro n hn
      exact hW n (Finset.mem_of_mem_filter n hn)
    · intro n hn n' hn'
      exact hφ_congr n (Finset.mem_of_mem_filter n hn) n' (Finset.mem_of_mem_filter n' hn')
        ((Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hn').2.symm)
  -- sum the class counts
  have hmaps : Set.MapsTo φ ↑S ↑T := fun n hn => hφ_mem n hn
  calc (S.card : ℝ)
      = ∑ b ∈ T, ((S.filter (fun n ↦ φ n = b)).card : ℝ) := by
        rw [Finset.card_eq_sum_card_fiberwise hmaps]; push_cast; rfl
    _ ≤ ∑ _b ∈ T, (2 * W / (q : ℝ) + 1) := Finset.sum_le_sum hfiber
    _ = (T.card : ℝ) * (2 * W / (q : ℝ) + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Work.BMF
