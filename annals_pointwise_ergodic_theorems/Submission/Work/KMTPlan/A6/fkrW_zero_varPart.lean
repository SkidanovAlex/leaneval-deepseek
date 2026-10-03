/-
# Vanishing of the `V^R(ℕ; L^r)` norm forces vanishing of the pointwise `r`-variation

`Work.KMTPlan.A6.fkrW_zero_varPart`: if the right-hand side `fkrW μ R r g` of the `fkr`
interchange lemma vanishes, then the `L^r`-norm of the pointwise `r`-variation part of the
sequence `k ↦ g k x` vanishes as well.

The proof is elementary.  `fkrW μ R r g` is the supremum over chains `k 0 ≤ ⋯ ≤ k J` of
`(∑_i ‖g (k (i+1)) - g (k i)‖_{L^r}^R)^{1/R}`; taking the two-term chain `m ≤ n` and using
`ENNReal.rpow_mul` with `R > 0` turns the vanishing of `fkrW` into
`eLpNorm (g n - g m) r μ = 0` for every `m ≤ n`.  By `eLpNorm_eq_zero_iff` this says
`g m =ᵐ[μ] g n`, so the whole sequence is a.e. constant, and the variation part of a constant
sequence is `0` because all its increments vanish.

This is the degenerate case of the interchange lemma (the one used in
`Work.KMTPlan.A6.FkrInterchange` when `fkrW μ R r g = 0`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.FkrAux
import Submission.Work.KMTPlan.A6.accVr_exists

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal BigOperators

/-- If the `V^R(ℕ; L^r)` norm of a sequence vanishes then its pointwise `r`-variation vanishes. -/
theorem fkrW_zero_varPart {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    {R : ℝ} (hR : 0 < R) {r : NNReal} (hr : 0 < (r : ℝ)) (g : ℕ → X → ℂ)
    (hg : ∀ k, MeasureTheory.AEStronglyMeasurable (g k) μ)
    (h : Work.KMTPlan.A6.fkrW μ R r g = 0) :
    MeasureTheory.eLpNorm
        (fun x => Submission.PointwiseErgodicTheorems.varPart r (fun k => g k x))
        (r : ENNReal) μ = 0 := by
  -- `(r : ℝ≥0∞) ≠ 0`, so `eLpNorm_eq_zero_iff` is available.
  have hrne : (r : ENNReal) ≠ 0 := by exact_mod_cast hr.ne'
  -- Every term of the `fkrW`-supremum vanishes.
  have hterm : ∀ (J : ℕ) (k : Fin (J + 1) → ℕ), Monotone k →
      (∑ i : Fin J, (MeasureTheory.eLpNorm
        (fun x => g (k i.succ) x - g (k i.castSucc) x) (r : ENNReal) μ) ^ R) ^ (1 / R) = 0 := by
    intro J k hk
    have hle : (∑ i : Fin J, (MeasureTheory.eLpNorm
        (fun x => g (k i.succ) x - g (k i.castSucc) x) (r : ENNReal) μ) ^ R) ^ (1 / R)
        ≤ Work.KMTPlan.A6.fkrW μ R r g :=
      le_iSup_of_le J (le_iSup_of_le k (le_iSup_of_le hk le_rfl))
    rw [h] at hle
    exact le_antisymm hle bot_le
  -- Hence every increment of the sequence has vanishing `L^r` norm.
  have key : ∀ m n : ℕ, m ≤ n →
      MeasureTheory.eLpNorm (fun x => g n x - g m x) (r : ENNReal) μ = 0 := by
    intro m n hmn
    -- the two-term chain `m ≤ n`
    set k : Fin 2 → ℕ := fun i => if (i : ℕ) = 0 then m else n with hkdef
    have hkmono : Monotone k := by
      intro i j hij
      have hi2 : (i : ℕ) < 2 := i.isLt
      have hj2 : (j : ℕ) < 2 := j.isLt
      have hij' : (i : ℕ) ≤ (j : ℕ) := hij
      simp only [hkdef]
      split_ifs with hi hj
      · exact le_rfl
      · exact hmn
      · exfalso; omega
      · exact le_rfl
    have hk1 : k 1 = n := by simp [hkdef]
    have hk0 : k 0 = m := by simp [hkdef]
    have hterm1 := hterm 1 k hkmono
    have hsum : (∑ i : Fin 1, (MeasureTheory.eLpNorm
          (fun x => g (k i.succ) x - g (k i.castSucc) x) (r : ENNReal) μ) ^ R)
        = (MeasureTheory.eLpNorm (fun x => g n x - g m x) (r : ENNReal) μ) ^ R := by
      rw [Fin.sum_univ_one, Fin.succ_zero_eq_one, Fin.castSucc_zero, hk1, hk0]
    rw [hsum] at hterm1
    -- `(a ^ R) ^ (1 / R) = a ^ (R * (1 / R)) = a`
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hR.ne', ENNReal.rpow_one] at hterm1
    exact hterm1
  -- So all the functions `g k` are a.e. equal.
  have haeeq : ∀ m n : ℕ, g m =ᵐ[μ] g n := by
    intro m n
    rcases le_total m n with hmn | hnm
    · have h0 := key m n hmn
      have hmeas : MeasureTheory.AEStronglyMeasurable (fun x => g n x - g m x) μ :=
        (hg n).sub (hg m)
      have hz : (fun x => g n x - g m x) =ᵐ[μ] 0 :=
        (MeasureTheory.eLpNorm_eq_zero_iff hrne).mp h0
      filter_upwards [hz] with x hx
      exact (sub_eq_zero.mp hx).symm
    · have h0 := key n m hnm
      have hmeas : MeasureTheory.AEStronglyMeasurable (fun x => g m x - g n x) μ :=
        (hg m).sub (hg n)
      have hz : (fun x => g m x - g n x) =ᵐ[μ] 0 :=
        (MeasureTheory.eLpNorm_eq_zero_iff hrne).mp h0
      filter_upwards [hz] with x hx
      exact sub_eq_zero.mp hx
  have hall : ∀ᵐ x ∂μ, ∀ k, g k x = g 0 x := by
    rw [MeasureTheory.ae_all_iff]
    intro k
    exact haeeq k 0
  -- A constant sequence has zero variation part.
  have hnorm0 : ∀ J : ℕ,
      ENNReal.ofReal ‖WithLp.toLp (r : ENNReal) (0 : Fin J → ℂ)‖ = 0 := by
    intro J
    rw [PiLp.norm_eq_sum (p := (r : ENNReal)) (by rw [ENNReal.coe_toReal]; exact hr),
      ENNReal.coe_toReal]
    have h1 : ∀ i : Fin J,
        ‖WithLp.ofLp (WithLp.toLp (r : ENNReal) (0 : Fin J → ℂ)) i‖ ^ (r : ℝ) = 0 := by
      intro i
      rw [WithLp.ofLp_toLp, Pi.zero_apply, norm_zero, Real.zero_rpow hr.ne']
    rw [Finset.sum_eq_zero (fun i _ => h1 i), Real.zero_rpow (by positivity),
      ENNReal.ofReal_zero]
  have hpoint : ∀ x, (∀ k, g k x = g 0 x) →
      Submission.PointwiseErgodicTheorems.varPart r (fun k => g k x) = 0 := by
    intro x hx
    refine le_antisymm ?_ bot_le
    refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
    have hthis : (fun (i : Fin J) => g (N (↑i + 1)) x - g (N ↑i) x) = (0 : Fin J → ℂ) := by
      funext i
      simp only [Pi.zero_apply]
      rw [hx (N (↑i + 1)), hx (N ↑i), sub_self]
    rw [hthis]
    exact le_of_eq (hnorm0 J)
  have hcongr : (fun x => Submission.PointwiseErgodicTheorems.varPart r (fun k => g k x))
      =ᵐ[μ] (0 : X → ENNReal) := by
    filter_upwards [hall] with x hx
    exact hpoint x hx
  rw [MeasureTheory.eLpNorm_congr_ae hcongr]
  simp

end Work.KMTPlan.A6
