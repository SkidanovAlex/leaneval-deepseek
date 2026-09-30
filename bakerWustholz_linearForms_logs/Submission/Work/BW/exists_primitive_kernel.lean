import Mathlib
import Submission.Work.BW.aligned_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-!
# Existence of a primitive element of the torsion-relation kernel with bounded weight

Given logarithms `ℓ : Fin m → ℂ` and a nonzero integer vector `t` in the kernel of the
`ℤ`-linear form `θ y = ∑ i, y i * ℓ i`, we produce a *primitive* nonzero kernel element `r`
(i.e. `r ≠ k • y` for every kernel element `y` and every integer `k` with `|k| ≥ 2`, the
"division" order) whose weighted `ℓ¹`-weight `wn c r = ∑ i, |r i| * c i` does not exceed
that of `t`.

The mathematics is elementary: dividing a nonzero kernel element `y` by an integer `k` with
`|k| ≥ 2` strictly decreases the quantity `∑ i, |y i|` (it is divided by `|k|`), and does not
increase the nonnegative weight `wn c`.  Iterating this "division descent" terminates, and the
terminal element is exactly a primitive one.
-/

section Helpers

variable {m : ℕ}

/-- Dividing by `k` with `|k| ≥ 2` does not increase the (nonnegative) weighted weight. -/
private lemma wn_le_wn_smul (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) {k : ℤ} (hk : 2 ≤ |k|)
    (y : Fin m → ℤ) : wn c y ≤ wn c (k • y) := by
  rw [wn_smul, ← Int.cast_abs]
  have h2 : (2 : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast hk
  nlinarith [wn_nonneg c hc y]

/-- Dividing a nonzero vector by `k` with `|k| ≥ 2` strictly decreases `∑ i, |y i|`. -/
private lemma sum_natAbs_lt_of_smul {k : ℤ} (hk : 2 ≤ |k|) {y y' : Fin m → ℤ}
    (hy : y = k • y') (hy' : y' ≠ 0) : ∑ i, (y' i).natAbs < ∑ i, (y i).natAbs := by
  have h1 : ∑ i, ((k • y') i).natAbs = k.natAbs * ∑ i, (y' i).natAbs := by
    simp only [Pi.smul_apply, smul_eq_mul, Int.natAbs_mul]
    rw [Finset.mul_sum]
  rw [hy, h1]
  have hk' : 2 ≤ k.natAbs := by
    have : (2 : ℤ) ≤ (k.natAbs : ℤ) := by simpa [Int.natCast_natAbs] using hk
    omega
  have hex : ∃ i, y' i ≠ 0 := by
    by_contra h
    push Not at h
    exact hy' (funext h)
  obtain ⟨i, hi⟩ := hex
  have hSpos : 1 ≤ ∑ i, (y' i).natAbs := by
    have hpos : 0 < (y' i).natAbs := Int.natAbs_pos.mpr hi
    have := Finset.single_le_sum (f := fun i => (y' i).natAbs)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hle : 2 * (∑ i, (y' i).natAbs) ≤ k.natAbs * (∑ i, (y' i).natAbs) :=
    Nat.mul_le_mul_right _ hk'
  omega

/-- **Division descent.**  Any nonzero kernel element of weight at most `W` has a primitive
multiple-free representative (in the division order) of weight at most `W`. -/
private lemma exists_primitive_of_weight_le (ℓ : Fin m → ℂ) (c : Fin m → ℝ)
    (hc : ∀ i, 0 ≤ c i) (W : ℝ) :
    ∀ y : Fin m → ℤ, thetaC ℓ y = 0 → y ≠ 0 → wn c y ≤ W →
      ∃ r : Fin m → ℤ, thetaC ℓ r = 0 ∧ r ≠ 0 ∧
        (∀ (k : ℤ) (y : Fin m → ℤ), thetaC ℓ y = 0 → 2 ≤ |k| → k • y ≠ r) ∧
        wn c r ≤ W := by
  have key : ∀ n : ℕ, ∀ y : Fin m → ℤ, (∑ i, (y i).natAbs) ≤ n → thetaC ℓ y = 0 →
      y ≠ 0 → wn c y ≤ W →
      ∃ r : Fin m → ℤ, thetaC ℓ r = 0 ∧ r ≠ 0 ∧
        (∀ (k : ℤ) (y : Fin m → ℤ), thetaC ℓ y = 0 → 2 ≤ |k| → k • y ≠ r) ∧
        wn c r ≤ W := by
    intro n
    induction n with
    | zero =>
      intro y hy0 _ hyne _
      exfalso
      have hsum : (∑ i, (y i).natAbs) = 0 := Nat.le_zero.mp hy0
      apply hyne
      funext i
      have h0 : (y i).natAbs = 0 := by
        have := (Finset.sum_eq_zero_iff.mp hsum) i (Finset.mem_univ i)
        simpa using this
      simpa using Int.natAbs_eq_zero.mp h0
    | succ n ih =>
      intro y hy hz0 hyne hW
      by_cases hprim : ∀ (k : ℤ) (z : Fin m → ℤ), thetaC ℓ z = 0 → 2 ≤ |k| → k • z ≠ y
      · exact ⟨y, hz0, hyne, hprim, hW⟩
      · push Not at hprim
        obtain ⟨k, z, hz, hk, hkz⟩ := hprim
        have hzne : z ≠ 0 := by
          intro hz0'
          apply hyne
          rw [← hkz, hz0', smul_zero]
        have hzW : wn c z ≤ W := by
          calc wn c z ≤ wn c (k • z) := wn_le_wn_smul c hc hk z
            _ = wn c y := by rw [hkz]
            _ ≤ W := hW
        have hlt : (∑ i, (z i).natAbs) < (∑ i, (y i).natAbs) :=
          sum_natAbs_lt_of_smul hk hkz.symm hzne
        have hsum_le : (∑ i, (z i).natAbs) ≤ n := by omega
        exact ih z hsum_le hz hzne hzW
  intro y hy hyne hW
  exact key (∑ i, (y i).natAbs) y le_rfl hy hyne hW

end Helpers

theorem exists_primitive_kernel {m : ℕ} (ℓ : Fin m → ℂ) (t : Fin m → ℤ) (ht : thetaC ℓ t = 0)
    (ht0 : t ≠ 0) (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∃ r : Fin m → ℤ, thetaC ℓ r = 0 ∧ r ≠ 0 ∧
      (∀ (k : ℤ) (y : Fin m → ℤ), thetaC ℓ y = 0 → 2 ≤ |k| → k • y ≠ r) ∧
      wn c r ≤ wn c t :=
  exists_primitive_of_weight_le ℓ c hc (wn c t) t ht ht0 le_rfl

end Work.BW
