import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.mem_uminus_of_entry_form
import Submission.Work.EKLC6Core.uminus_entry_zero

/-!
# `EKLC6Core.mem_uminus_of_shadowing`

**Shadowing.**  If the conjugates `α^m g α^{-m}` of `g ∈ SL₃(ℝ)` by the diagonal flow
`α = aDiag t` are bounded (`hbdd`), and along a shadowing sequence of exponents `φ k` the
conjugates factor as

`α^{φ k} g α^{-φ k} = u_k · h_k`,  `u_k ∈ Uminus t ∩ V R`,  `h_k → 1` entrywise,

then `g ∈ Uminus t = ⨆_{t i < t j} U_ij`, the stable horospherical subgroup of `aDiag t`.

## Proof

Write `α = aDiag t`; conjugation scales entries (`boxi_conj_pow_apply`):

`(α^n g α^{-n})ᵢⱼ = e^{n (tᵢ - tⱼ)} gᵢⱼ`.

Two regimes:

* `tᵢ > tⱼ` (`i ≠ j`): the factor `e^{n (tᵢ - tⱼ)}` grows without bound along `n`, so boundedness
  of the conjugates for *all* `n` forces `gᵢⱼ = 0`.
* `tᵢ = tⱼ`: the factor is `1`, so the entry of the conjugate is `gᵢⱼ` itself; comparing with the
  shadowing factorisation and using that every element of `Uminus t` has diagonal entry `1` and
  `(i,j)`-entry `0` whenever `tⱼ ≤ tᵢ` (`uminus_entry_facts`) gives `gᵢⱼ = δᵢⱼ`.

Concretely, in the second regime `gᵢⱼ = (u_k h_k)ᵢⱼ = δᵢⱼ + (u_k (h_k - 1))ᵢⱼ`, where the
correction term is bounded entrywise by `3 (R + 1) ε_k → 0` (the `u_k` lie in `V R`, the
deviation of `h_k` from `1` is `< ε_k`).  Since the left-hand side does not depend on `k`, this
forces `gᵢⱼ = δᵢⱼ`.

The entry conditions `gᵢᵢ = 1` and `gᵢⱼ = 0` for `tⱼ ≤ tᵢ`, `i ≠ j`, are exactly the hypotheses of
`mem_uminus_of_entry_form`, which concludes `g ∈ Uminus t`.  Note that only the *existence* of
the shadowing factorisation for arbitrarily large times is used, and no compactness: the limit
argument is a squeeze on a constant sequence.
-/

open Filter Topology
open Work.EKLContract

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

theorem mem_uminus_of_shadowing {t : Fin 3 → ℝ} {g : Work.EKLContract.SL3}
    (hbdd : ∃ C : ℝ, ∀ m : ℕ, ∀ i j : Fin 3,
      |(Work.EKLContract.aDiag t ^ m * g * (Work.EKLContract.aDiag t ^ m)⁻¹) i j| ≤ C)
    (hseq : ∃ (φ : ℕ → ℕ) (ε : ℕ → ℝ) (R : ℝ),
      StrictMono φ ∧ Filter.Tendsto ε Filter.atTop (nhds 0) ∧ 0 < R ∧
      ∀ k : ℕ, ∃ u : Work.EKLContract.SL3,
        u ∈ Work.EKLC6Core.Uminus t ∧ u ∈ Work.EKLContract.V R ∧
        ∃ h : Work.EKLContract.SL3,
          (∀ i j : Fin 3, |h i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < ε k) ∧
          Work.EKLContract.aDiag t ^ (φ k) * g * (Work.EKLContract.aDiag t ^ (φ k))⁻¹ = u * h) :
    g ∈ Work.EKLC6Core.Uminus t := by
  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨φ, ε, R, hφ, hε, hR, hsh⟩ := hseq
  choose u hu hv h hh heq using hsh
  have hR1 : 0 ≤ R + 1 := by linarith
  -- ## Every element of `V R` has entries bounded by `R + 1`
  have hUbound : ∀ k : ℕ, ∀ i l : Fin 3,
      |((u k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i l| ≤ R + 1 := by
    intro k i l
    have h1 : |((u k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i l| < R := hv k i l
    have h2 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i l| ≤ 1 := by
      by_cases hil : i = l
      · subst hil; rw [Matrix.one_apply_eq]; norm_num
      · rw [Matrix.one_apply_ne hil]; norm_num
    calc |((u k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i l|
        = |(((u k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i l
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i l)
            + (1 : Matrix (Fin 3) (Fin 3) ℝ) i l| := by
          exact congrArg abs (by ring)
      _ ≤ |((u k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i l
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i l|
          + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i l| := abs_add_le _ _
      _ ≤ R + 1 := add_le_add (le_of_lt h1) h2
  -- ## The entrywise statement
  have key : ∀ i j : Fin 3, t j ≤ t i →
      (g : Matrix (Fin 3) (Fin 3) ℝ) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
    intro i j hle
    rcases lt_or_eq_of_le hle with hlt | heqij
    · -- ## Expanded direction `t j < t i`: boundedness along the whole orbit
      have hij : i ≠ j := by rintro rfl; exact absurd hlt (lt_irrefl _)
      rw [Matrix.one_apply_ne hij]
      by_contra hg0
      have hgpos : 0 < |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_pos.mpr hg0
      have hΔ : 0 < t i - t j := by linarith
      have hb : ∀ m : ℕ,
          Real.exp ((m : ℝ) * (t i - t j)) * |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C := by
        intro m
        have h := hC m i j
        rw [boxi_conj_pow_apply, abs_mul, abs_of_pos (Real.exp_pos _)] at h
        exact h
      obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp
        ((boxi_tendsto_exp_nat_mul_atTop hΔ).eventually_gt_atTop
          (C / |(g : Matrix (Fin 3) (Fin 3) ℝ) i j|))
      have hm' := hm m le_rfl
      rw [div_lt_iff₀ hgpos] at hm'
      have := hb m
      linarith
    · -- ## Fixed direction `t i = t j`: the shadowing identity
      have huk : ∀ k : ℕ, ((u k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
          = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
        intro k
        obtain ⟨hdiag, hzero⟩ := uminus_entry_facts t (hu k)
        by_cases hij : i = j
        · subst hij
          rw [hdiag i, Matrix.one_apply_eq]
        · rw [hzero i j hij (le_of_eq heqij), Matrix.one_apply_ne hij]
      have hdec : ∀ k : ℕ, (g : Matrix (Fin 3) (Fin 3) ℝ) i j
          = ((u k * h k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j := by
        intro k
        rw [← heq k, boxi_conj_pow_apply,
          show t i - t j = 0 from by linarith, mul_zero, Real.exp_zero, one_mul]
      -- the deviation `gᵢⱼ - δᵢⱼ` is bounded by `3 (R+1) ε_k`
      have hgdiff : ∀ k : ℕ, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 3 * (R + 1) * ε k := by
        intro k
        have h1 : (g : Matrix (Fin 3) (Fin 3) ℝ) i j
            = ∑ l : Fin 3, ((u k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i l
                * (((h k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) l j) := by
          rw [hdec k, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
        have h2 : ((u k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
            = ∑ l : Fin 3, ((u k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i l
                * (1 : Matrix (Fin 3) (Fin 3) ℝ) l j := by
          rw [← Matrix.mul_apply, Matrix.mul_one]
        have h3 : ∀ l : Fin 3, ((u k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i l
              * (((h k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) l j)
            - ((u k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i l
              * (1 : Matrix (Fin 3) (Fin 3) ℝ) l j
            = ((u k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i l
              * ((((h k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) l j)
                - (1 : Matrix (Fin 3) (Fin 3) ℝ) l j) := by
          intro l; ring
        rw [h1, ← huk k, h2, ← Finset.sum_sub_distrib]
        simp only [h3]
        calc |∑ l : Fin 3, ((u k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i l
                * ((((h k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) l j)
                  - (1 : Matrix (Fin 3) (Fin 3) ℝ) l j)|
            ≤ ∑ l : Fin 3, |((u k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i l
                * ((((h k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) l j)
                  - (1 : Matrix (Fin 3) (Fin 3) ℝ) l j)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ l : Fin 3, |((u k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i l|
                * |(((h k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) l j)
                  - (1 : Matrix (Fin 3) (Fin 3) ℝ) l j| :=
              Finset.sum_congr rfl (fun l _ => abs_mul _ _)
          _ ≤ ∑ _l : Fin 3, (R + 1) * ε k := Finset.sum_le_sum (fun l _ =>
                mul_le_mul (hUbound k i l) (le_of_lt (hh k l j)) (abs_nonneg _) hR1)
          _ = 3 * (R + 1) * ε k := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              ring
      -- the constant sequence `|gᵢⱼ - δᵢⱼ|` is squeezed to `0`
      have htend : Tendsto (fun k : ℕ => |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|) atTop (nhds 0) :=
        squeeze_zero (fun k => abs_nonneg _) hgdiff
          (by simpa using hε.const_mul (3 * (R + 1)))
      have hz : |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| = 0 :=
        (tendsto_nhds_unique htend tendsto_const_nhds).symm
      have hz' : (g : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := abs_eq_zero.mp hz
      linarith
  -- ## Assembly
  refine mem_uminus_of_entry_form (t := t) (g := g) ?_ ?_
  · intro i
    exact (key i i le_rfl).trans (Matrix.one_apply_eq i)
  · intro i j hij hle
    have h := key i j hle
    rwa [Matrix.one_apply_ne hij] at h

end Work.EKLC6Core

end
