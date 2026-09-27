import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.mem_uminus_of_shadowing

/-!
# `EKLC6Route.mem_uminus_of_shadowing_seq`

**Shadowing along a sequence.**  The boundedness hypothesis of
`Work.EKLC6Core.mem_uminus_of_shadowing` is used only along the shadowing times `φ k`, and the
shadowing times only through the fact that they run off to infinity.  Here is that weakening:
if

* `φ k → ∞`,
* `ε k → 0`, `0 < R`,
* the conjugates `α^{φ k} g α^{-φ k}` (`α = aDiag t`) are *entrywise bounded along the
  subsequence* `φ k`,
* and along `φ k` each conjugate factors as `u_k · h_k` with `u_k ∈ Uminus t ∩ V R` and `h_k`
  entrywise `< ε k`-close to `1`,

then `g ∈ Uminus t`.

The proof is the same entrywise analysis as in `Work.EKLC6Core.mem_uminus_of_shadowing`: for
`t j ≤ t i` the conjugate's `(i,j)`-entry equals `e^{φ k (t i - t j)} gᵢⱼ`, which is bounded as
`k → ∞`; if `t j < t i` this forces `gᵢⱼ = 0`, while if `t i = t j` the factor is `1` and
comparing with the factorisation `u_k h_k` (whose `(i,j)`-entry is `δᵢⱼ + O(ε k) → δᵢⱼ`) again
forces `gᵢⱼ = δᵢⱼ`.  The entry conditions are exactly the hypotheses of
`Work.EKLC6Core.mem_uminus_of_entry_form`.
-/

open Filter Topology
open Work.EKLContract

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Route

theorem mem_uminus_of_shadowing_seq {t : Fin 3 → ℝ} {g : Work.EKLContract.SL3}
    {φ : ℕ → ℕ} {ε : ℕ → ℝ} {R : ℝ}
    (hφ : Filter.Tendsto φ Filter.atTop Filter.atTop)
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) (hR : 0 < R)
    (hbdd : ∃ C : ℝ, ∀ k : ℕ, ∀ i j : Fin 3,
      |(Work.EKLContract.aDiag t ^ (φ k) * g * (Work.EKLContract.aDiag t ^ (φ k))⁻¹) i j| ≤ C)
    (hsh : ∀ k : ℕ, ∃ u : Work.EKLContract.SL3,
        u ∈ Work.EKLC6Core.Uminus t ∧ u ∈ Work.EKLContract.V R ∧
        ∃ h : Work.EKLContract.SL3,
          (∀ i j : Fin 3, |h i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < ε k) ∧
          Work.EKLContract.aDiag t ^ (φ k) * g * (Work.EKLContract.aDiag t ^ (φ k))⁻¹ = u * h) :
    g ∈ Work.EKLC6Core.Uminus t := by
  obtain ⟨C, hC⟩ := hbdd
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
    · -- ## Expanded direction `t j < t i`: boundedness along the sequence `φ k`
      have hij : i ≠ j := by rintro rfl; exact absurd hlt (lt_irrefl _)
      rw [Matrix.one_apply_ne hij]
      by_contra hg0
      have hgpos : 0 < |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_pos.mpr hg0
      have hΔ : 0 < t i - t j := by linarith
      have hb : ∀ k : ℕ,
          Real.exp ((φ k : ℝ) * (t i - t j)) * |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C := by
        intro k
        have h := hC k i j
        rw [Work.EKLC6Core.boxi_conj_pow_apply, abs_mul,
          abs_of_pos (Real.exp_pos _)] at h
        exact h
      -- the exponential factor is unbounded along `φ`
      have hexp : Tendsto (fun k : ℕ => Real.exp ((φ k : ℝ) * (t i - t j))) atTop atTop :=
        (Work.EKLC6Core.boxi_tendsto_exp_nat_mul_atTop hΔ).comp hφ
      obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp
        (hexp.eventually_gt_atTop (C / |(g : Matrix (Fin 3) (Fin 3) ℝ) i j|))
      have hk' := hk k le_rfl
      rw [div_lt_iff₀ hgpos] at hk'
      have := hb k
      linarith
    · -- ## Fixed direction `t i = t j`: the shadowing identity
      have huk : ∀ k : ℕ, ((u k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
          = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
        intro k
        obtain ⟨hdiag, hzero⟩ := Work.EKLC6Core.uminus_entry_facts t (hu k)
        by_cases hij : i = j
        · subst hij
          rw [hdiag i, Matrix.one_apply_eq]
        · rw [hzero i j hij (le_of_eq heqij), Matrix.one_apply_ne hij]
      have hdec : ∀ k : ℕ, (g : Matrix (Fin 3) (Fin 3) ℝ) i j
          = ((u k * h k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j := by
        intro k
        rw [← heq k, Work.EKLC6Core.boxi_conj_pow_apply,
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
  refine Work.EKLC6Core.mem_uminus_of_entry_form (t := t) (g := g) ?_ ?_
  · intro i
    exact (key i i le_rfl).trans (Matrix.one_apply_eq i)
  · intro i j hij hle
    have h := key i j hle
    rwa [Matrix.one_apply_ne hij] at h

end Work.EKLC6Route

end
