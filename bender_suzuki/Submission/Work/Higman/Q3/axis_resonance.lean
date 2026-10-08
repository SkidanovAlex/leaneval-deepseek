import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.resonance_of_equivariant_biadditive

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.Higman.Q3

/-! ## The resonance lemma, without any generator hypothesis

The eigenvalue bookkeeping behind `axis_resonance` only uses that the pairing `B` is
*Frobenius scalar* under `(x, y) ↦ (ν * x, ν * y)`: expanding `B` in the bivariate Frobenius
basis `x ^ (2 ^ i) * y ^ (2 ^ j)` and comparing coefficients, every non-zero coefficient `d i j`
satisfies `ν ^ (2 ^ i + 2 ^ j) = lam`.  In particular no hypothesis on `ν` (like being a
generator of the multiplicative group) is needed here. -/

/-- **Frobenius resonance.**  Let `|F| = 2 ^ n` with `2 ≤ n`, let `B : F → F → F` be additive in
each variable and satisfy `B (ν * a) (ν * b) = lam * B a b`.  If `B` is not identically zero then
`ν ^ (2 ^ i + 2 ^ j) = lam` for some `i, j < n`. -/
theorem frob_resonance_eq {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) (hcard : Fintype.card F = 2 ^ n)
    (nu lam : F) (B : F → F → F)
    (hB1 : ∀ a b d : F, B (a + b) d = B a d + B b d)
    (hB2 : ∀ a b d : F, B a (b + d) = B a b + B a d)
    (heq : ∀ a b : F, B (nu * a) (nu * b) = lam * B a b)
    (hne : ∃ a b : F, B a b ≠ 0) :
    ∃ i j : ℕ, i < n ∧ j < n ∧ nu ^ (2 ^ i + 2 ^ j) = lam := by
  classical
  obtain ⟨d, hdexp⟩ :=
    Work.Higman.bilinear_frob_general hcard B (fun y x x' => hB1 x x' y)
      (fun x y y' => hB2 x y y')
  -- the coefficient constraint coming from the equivariance
  have hc : ∀ k ∈ Finset.range n, ∀ l ∈ Finset.range n,
      d k l * (nu ^ (2 ^ k + 2 ^ l) - lam) = 0 := by
    intro k hk l hl
    have h :=
      Work.Higman.bilinear_frob_general_constraint hcard B d hdexp nu nu lam heq k hk l hl
    rwa [← pow_add] at h
  -- `B ≠ 0` forces some Frobenius coefficient to be non-zero
  have hex : ∃ k l, k < n ∧ l < n ∧ d k l ≠ 0 := by
    by_contra hcon
    obtain ⟨a, b, hab⟩ := hne
    refine hab ?_
    rw [hdexp a b]
    refine Finset.sum_eq_zero (fun k hk => Finset.sum_eq_zero (fun l hl => ?_))
    by_contra hkl
    exact hcon ⟨k, l, Finset.mem_range.mp hk, Finset.mem_range.mp hl,
      fun h0 => hkl (by rw [h0]; ring)⟩
  obtain ⟨i, j, hi, hj, hdij⟩ := hex
  refine ⟨i, j, hi, hj, ?_⟩
  have h0 := hc i (Finset.mem_range.mpr hi) j (Finset.mem_range.mpr hj)
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h hdij
  · exact sub_eq_zero.mp h

/-- The statement exactly as requested. -/
theorem axis_resonance {n : ℕ}
    {b : GaloisField 2 n → GaloisField 2 n → GaloisField 2 n} [Biadd b]
    {ν lam : (GaloisField 2 n)ˣ} (hν : orderOf ν = 2 ^ n - 1)
    (heq : ∀ x y : GaloisField 2 n,
      b ((ν : GaloisField 2 n) * x) ((ν : GaloisField 2 n) * y) =
        (lam : GaloisField 2 n) * b x y)
    (hne : ∃ x y : GaloisField 2 n, b x y ≠ 0) :
    ∃ i j : ℕ, i < n ∧ j < n ∧ ν ^ (2 ^ i + 2 ^ j) = lam := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- `n = 0` or `n = 1`
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · -- `n = 0`: the unit group is finite, so `orderOf ν ≠ 0`
      have h0 : orderOf ν = 0 := by simpa using hν
      haveI : Fintype ((GaloisField 2 0)ˣ) := Fintype.ofFinite _
      have hdvd : orderOf ν ∣ Fintype.card ((GaloisField 2 0)ˣ) := orderOf_dvd_card
      rw [h0, zero_dvd_iff] at hdvd
      have hpos : 0 < Fintype.card ((GaloisField 2 0)ˣ) := Fintype.card_pos_iff.mpr ⟨1⟩
      omega
    · -- `n = 1`: `orderOf ν = 1` forces `ν = 1`, and then `lam = 1`
      have hν1 : ν = 1 := orderOf_eq_one_iff.mp (by simpa using hν)
      obtain ⟨x, y, hxy⟩ := hne
      have hh := heq x y
      rw [hν1, Units.val_one, one_mul, one_mul] at hh
      have hlam1 : (lam : GaloisField 2 1) = 1 := by
        have h2 : (lam : GaloisField 2 1) * b x y = (1 : GaloisField 2 1) * b x y := by
          rw [one_mul]; exact hh.symm
        exact mul_right_cancel₀ hxy h2
      refine ⟨0, 0, by norm_num, by norm_num, ?_⟩
      have hsum : (2 : ℕ) ^ 0 + 2 ^ 0 = 2 := by norm_num
      rw [hsum, hν1]
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, one_pow, hlam1]
  · -- `n ≥ 2`
    haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    haveI : DecidableEq (GaloisField 2 n) := Classical.decEq _
    have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card 2 n (by omega)
    obtain ⟨i, j, hi, hj, hpow⟩ :=
      frob_resonance_eq (F := GaloisField 2 n) (by omega) hcard (ν : GaloisField 2 n)
        (lam : GaloisField 2 n) b (fun a c d => Biadd.add_left a c d)
        (fun a c d => Biadd.add_right a c d) heq hne
    refine ⟨i, j, hi, hj, ?_⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact hpow

end Work.Higman.Q3
