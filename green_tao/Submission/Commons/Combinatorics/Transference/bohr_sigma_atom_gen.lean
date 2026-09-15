import Mathlib
import Submission.Commons.Combinatorics.Transference.bohr_sigma_atom
import Submission.Commons.Combinatorics.Transference.cube_corr_half
import Submission.Commons.Combinatorics.Transference.davg_smul
import Submission.Commons.Combinatorics.Transference.Unorm_smul_of_nonneg

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- **Green–Tao Proposition 6.6, core estimate, with the bound `|F_j| ≤ C(ν+1)`.**

This is the form actually needed in Green–Tao §7: the anti-uniform generators satisfy only
`|F_j| ≤ (1+o(1))(ν+1)`, not `|F_j| ≤ ν`.  The proof replaces `ν` by the halfway measure
`ν' = (ν+1)/2` and `F_j` by `F_j/(2C)` (Green–Tao Lemma 3.1, `cube_corr_half`), so that the
scaled generators satisfy `|F_j/(2C)| ≤ ν'`; then `bohr_sigma_atom` applies verbatim, and the
conclusion is converted back using `𝒟(cF) = c^{2^d-1}𝒟F` (`davg_smul`) and
`‖(ν-1)/2‖_{U^d} = ‖ν-1‖_{U^d}/2` (`Unorm_half_sub`).

The hypothesis `hcorr` is the *finset form* of the correlation condition for `ν` (the form
supplied by `cube_corr_half`), together with the mean bound `𝔼ν = 1 + O(εm)`. -/
theorem bohr_sigma_atom_gen {p : ℕ} [Fact p.Prime] {d K : ℕ} (hd : 1 ≤ d)
    (F : Fin K → ZMod p → ℝ) {ν τ : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x) (hτ : ∀ x, 0 ≤ τ x)
    {C : ℝ} (hC : 1 ≤ C) (hF : ∀ (j : Fin K) (x : ZMod p), |F j x| ≤ C * (ν x + 1))
    (hcorr : ∀ (A : Finset (Fin d → Bool)), 2 ≤ A.card → ∀ h : Fin d → ZMod p,
      ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p,
          ∏ ω ∈ A, ν (y + ∑ i, (if ω i then h i else 0))
        ≤ ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'),
            τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))))
    {εm : ℝ} (hεm0 : 0 ≤ εm) (hεm1 : εm ≤ 1)
    (hmean : |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, ν x - 1| ≤ εm)
    {Cm : ℕ → ℝ} (hmom : ∀ q : ℕ, 1 ≤ q →
      ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, (τ x) ^ q ≤ Cm q)
    {M : ℝ} (hM : 0 ≤ M)
    (hMbound : ∀ (j : Fin K) (x : ZMod p), |davg d (fun y => F j y / (2 * C)) x| ≤ M)
    {ε η η' : ℝ} (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1 / 4) (hη' : 0 < η')
    (α : Fin K → ℝ) (T : Fin K → Finset (ZMod p))
    (hT : ∀ (j : Fin K) (y : ZMod p),
      (∃ n : ℤ, |(davg d (fun z => F j z / (2 * C)) y - α j) / ε - n| ≤ η) → y ∈ T j) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ x : ZMod p,
      |∑ y ∈ Finset.univ.filter (fun y => ∀ j : Fin K, y ∈ Finset.univ.filter
          (fun y => ⌊(davg d (fun z => F j z / (2 * C)) y - α j) / ε⌋
              = ⌊(davg d (fun z => F j z / (2 * C)) x - α j) / ε⌋)),
          (ν y - 1)|
        ≤ (Fintype.card (ZMod p) : ℝ) * (Unorm d (fun y => ν y - 1) * E
            + η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, |ν y - 1|))
          + ((3 * K : ℕ) : ℝ) * ∑ j : Fin K, ∑ y ∈ T j, (ν y + 1) := by
  classical
  have hCpos : 0 < C := by linarith
  -- Step 0: positivity and the pointwise bound for the halved generator
  have hν' : ∀ x : ZMod p, 0 ≤ (ν x + 1) / 2 := fun x => by have := hν x; linarith
  have hF' : ∀ (j : Fin K) (x : ZMod p), |F j x / (2 * C)| ≤ (ν x + 1) / 2 := by
    intro j x
    have h2C : (0 : ℝ) < 2 * C := by linarith
    rw [abs_div, abs_of_pos h2C]
    have hstep : |F j x| / (2 * C) ≤ C * (ν x + 1) / (2 * C) :=
      div_le_div_of_nonneg_right (hF j x) h2C.le
    have heq : C * (ν x + 1) / (2 * C) = (ν x + 1) / 2 := by
      rw [show (2 : ℝ) * C = C * 2 by ring]
      exact mul_div_mul_left (ν x + 1) 2 (ne_of_gt hCpos)
    linarith
  -- Step 1: the correlation condition for the halfway measure
  obtain ⟨Cm', hCm'nn, τ', hτ'nn, hmom', hcorr'⟩ :=
    cube_corr_half hd ν hν hεm0 hεm1 hmean hτ hmom hcorr
  obtain ⟨E, hE, hEbound⟩ := bohr_sigma_atom (p := p) (d := d) (K := K) hd
    (fun j z => F j z / (2 * C)) hν' hτ'nn hF' hcorr' hmom' hM hMbound hε hη hη1 hη' α T hT
  refine ⟨E, hE, fun x => ?_⟩
  -- Step 2: the conversion identities between ν and ν' = (ν+1)/2
  have hU : Unorm d (fun y => ν y - 1) = 2 * Unorm d (fun y => (ν y + 1) / 2 - 1) := by
    have h : (fun y : ZMod p => ν y - 1) = fun y => (2 : ℝ) * ((ν y + 1) / 2 - 1) := by
      funext y; ring
    rw [h, Unorm_smul_of_nonneg hd (by norm_num : (0 : ℝ) ≤ 2)]
  have hS : (∑ y : ZMod p, |ν y - 1|) = 2 * ∑ y : ZMod p, |(ν y + 1) / 2 - 1| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro y _
    rw [show ν y - 1 = 2 * ((ν y + 1) / 2 - 1) by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hT2 : 2 * (∑ j : Fin K, ∑ y ∈ T j, ((ν y + 1) / 2 + 1))
      ≤ 3 * (∑ j : Fin K, ∑ y ∈ T j, (ν y + 1)) := by
    have h1 : ∀ j : Fin K,
        2 * (∑ y ∈ T j, ((ν y + 1) / 2 + 1)) ≤ 3 * (∑ y ∈ T j, (ν y + 1)) := by
      intro j
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum; intro y _
      have := hν y; linarith
    calc 2 * (∑ j : Fin K, ∑ y ∈ T j, ((ν y + 1) / 2 + 1))
        = ∑ j : Fin K, 2 * (∑ y ∈ T j, ((ν y + 1) / 2 + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ j : Fin K, 3 * (∑ y ∈ T j, (ν y + 1)) := Finset.sum_le_sum (fun j _ => h1 j)
      _ = 3 * (∑ j : Fin K, ∑ y ∈ T j, (ν y + 1)) := by rw [Finset.mul_sum]
  -- Step 3: the atom sums
  set A : Finset (ZMod p) := Finset.univ.filter (fun y => ∀ j : Fin K, y ∈ Finset.univ.filter
      (fun y => ⌊(davg d (fun z => F j z / (2 * C)) y - α j) / ε⌋
          = ⌊(davg d (fun z => F j z / (2 * C)) x - α j) / ε⌋)) with hA
  have hb := hEbound x
  simp only [← hA] at hb
  have hL : |∑ y ∈ A, (ν y - 1)| = 2 * |∑ y ∈ A, ((ν y + 1) / 2 - 1)| := by
    have hh : (∑ y ∈ A, (ν y - 1)) = 2 * (∑ y ∈ A, ((ν y + 1) / 2 - 1)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
    rw [hh, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hlast : 2 * (K : ℝ) * (∑ j : Fin K, ∑ y ∈ T j, ((ν y + 1) / 2 + 1))
      ≤ ((3 * K : ℕ) : ℝ) * (∑ j : Fin K, ∑ y ∈ T j, (ν y + 1)) := by
    have hco : ((3 * K : ℕ) : ℝ) = 3 * (K : ℝ) := by push_cast; ring
    rw [hco]
    have hmul := mul_le_mul_of_nonneg_left hT2 hKnn
    nlinarith [hmul]
  calc |∑ y ∈ A, (ν y - 1)|
      = 2 * |∑ y ∈ A, ((ν y + 1) / 2 - 1)| := hL
    _ ≤ 2 * ((Fintype.card (ZMod p) : ℝ) * (Unorm d (fun y => (ν y + 1) / 2 - 1) * E
          + η' * ((Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, |(ν y + 1) / 2 - 1|))
        + (K : ℝ) * ∑ j : Fin K, ∑ y ∈ T j, ((ν y + 1) / 2 + 1)) := by linarith [hb]
    _ = (Fintype.card (ZMod p) : ℝ) * (Unorm d (fun y => ν y - 1) * E
          + η' * ((Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, |ν y - 1|))
        + 2 * (K : ℝ) * ∑ j : Fin K, ∑ y ∈ T j, ((ν y + 1) / 2 + 1) := by
        rw [hU, hS]; ring
    _ ≤ (Fintype.card (ZMod p) : ℝ) * (Unorm d (fun y => ν y - 1) * E
          + η' * ((Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, |ν y - 1|))
        + ((3 * K : ℕ) : ℝ) * ∑ j : Fin K, ∑ y ∈ T j, (ν y + 1) := by linarith [hlast]



end Commons.Combinatorics.Transference
