import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs

/-!
# Auxiliary notions for `Work.HP.detL_latOrth`

This file collects the small definitions and lemmas the proof of
`detL (latOrth c) = eNorm c` (for `c` primitive) is built on.

* `sqN c = ∑ i, (c i).natAbs ^ 2` is the square of the Euclidean norm of `c`, as a natural
  number.
* `pdot x y = ∑ i, x i * y i` is the standard pairing (an alias of `Work.HP.dotZ`).
* `LM c = Λ_c^{(m)} = {y : (m : ℤ) ∣ ∑ i, y i * c i}` with `m = sqN c`; this is the lattice
  `Λ_c + ℤc`, the middle term of the chain `Λ_c ⊆ LM c ⊆ ℤ^ι`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard pairing `∑ i, x i * y i` (an alias for `Work.HP.dotZ`). -/
abbrev pdot (x y : ι → ℤ) : ℤ := dotZ x y

/-- The square of the Euclidean norm of `c`, as a natural number. -/
def sqN (c : ι → ℤ) : ℕ := ∑ i, (c i).natAbs ^ 2

/-- The lattice `{y : (m : ℤ) ∣ ∑ i, y i * c i}` where `m = ∑ i, (c i)^2`; concretely it is
`latOrth c + ℤc`. -/
def LM (c : ι → ℤ) : Submodule ℤ (ι → ℤ) := latMod c (sqN c)

variable {c y z : ι → ℤ}

@[simp] lemma pdot_apply (x w : ι → ℤ) : pdot x w = ∑ i, x i * w i := rfl

@[simp] lemma pdot_zero_left : pdot (0 : ι → ℤ) c = 0 := by simp [pdot, dotZ]

@[simp] lemma pdot_zero_right : pdot c (0 : ι → ℤ) = 0 := by simp [pdot, dotZ]

lemma pdot_add_left (x x' w : ι → ℤ) : pdot (x + x') w = pdot x w + pdot x' w := by
  simp only [pdot, dotZ, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma pdot_add_right (x w w' : ι → ℤ) : pdot x (w + w') = pdot x w + pdot x w' := by
  simp only [pdot, dotZ, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma pdot_smul_left (a : ℤ) (x w : ι → ℤ) : pdot (a • x) w = a * pdot x w := by
  simp only [pdot, dotZ, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

lemma pdot_smul_right (a : ℤ) (x w : ι → ℤ) : pdot x (a • w) = a * pdot x w := by
  simp only [pdot, dotZ, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Membership in the orthogonal lattice, in terms of the displayed pairing. -/
lemma mem_latOrth : y ∈ latOrth c ↔ pdot y c = 0 := by
  rw [latOrth, LinearMap.mem_ker, Fintype.linearCombination_apply, pdot, dotZ]
  simp only [smul_eq_mul]

/-- Membership in `LM c`, unfolded. -/
lemma mem_LM : y ∈ LM c ↔ (sqN c : ℤ) ∣ pdot y c := by
  rw [LM, latMod, Submodule.mem_comap, Fintype.linearCombination_apply, pdot, dotZ,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa [smul_eq_mul, mul_comm] using ha.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa [smul_eq_mul, mul_comm] using ha.symm⟩

lemma latOrth_le_LM (c : ι → ℤ) : latOrth c ≤ LM c := by
  intro y hy
  rw [mem_LM, mem_latOrth] at *
  rw [hy]
  exact dvd_zero _

/-- `sqN` as an integer is the self-pairing of `c`. -/
lemma sqN_cast_eq_pdot (c : ι → ℤ) : (sqN c : ℤ) = pdot c c := by
  simp only [sqN, pdot, dotZ, Nat.cast_sum, Nat.cast_pow]
  exact Finset.sum_congr rfl fun i _ => by rw [Int.natAbs_sq, pow_two]

/-- The lattice `span {c}` is contained in `LM c`. -/
lemma span_singleton_le_LM (c : ι → ℤ) : Submodule.span ℤ {c} ≤ LM c := by
  rw [Submodule.span_singleton_le_iff_mem, mem_LM, sqN_cast_eq_pdot]

/-- A primitive vector is nonzero. -/
lemma isPrim_ne_zero (hc : IsPrim c) : c ≠ 0 := by
  intro h
  rw [IsPrim, h] at hc
  have h0 : Finset.univ.gcd (0 : ι → ℤ) = 0 := by
    rw [Finset.gcd_eq_zero_iff]; simp
  rw [h0] at hc
  exact one_ne_zero hc.symm

lemma sqN_pos (hc : IsPrim c) : 0 < sqN c := by
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact isPrim_ne_zero hc (funext h)
  exact Finset.sum_pos' (fun j _ => Nat.zero_le _)
    ⟨i, Finset.mem_univ i, pow_pos (Int.natAbs_pos.mpr hi) 2⟩

/-- The square of the Euclidean norm is `sqN`. -/
lemma eNorm_sq_eq_sqN (c : ι → ℤ) : eNorm c ^ 2 = (sqN c : ℝ) := by
  rw [eNorm, sqN, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := congr_arg (fun z : ℤ => (z : ℝ)) (Int.natAbs_mul_self (a := c i))
  simp only [Nat.cast_mul] at h
  rw [Nat.cast_pow]
  simp [pow_two]

end Work.HP
