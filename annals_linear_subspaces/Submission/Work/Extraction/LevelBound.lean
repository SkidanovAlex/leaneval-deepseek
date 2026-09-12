import Mathlib
import Submission.Work.Lattice.Prop5Iteration
import Submission.Work.Lattice.BatchAccumulation

/-!
# Explicit lower bounds for the `ε`-sequence of the orthonormal extension

Iterating `Lemma5Extension.exists_orthonormal_cone_family` along the §3 flag is only useful for the
final theorem if the dominance level stays **uniformly bounded below**: this module proves

    `e₀^{2^i} · (2^{i+1})^{2^i}⁻¹ ≤ epsSeq i m e₀ k`     (for `0 < e₀ ≤ 1`),

by the cruder (but elementary) induction `x_{k+1} ≥ x_k² / 2^{i+1}`.

Module `Submission.Work.Extraction.LevelBound`, namespace `Submission.LevelBound`.
-/

noncomputable section
open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Submission.LevelBound

open Submission.Prop5Iteration
open Submission.Lemma5Extension
open Submission.ExteriorCoordinates

variable {d : ℕ}

/-- The crude exponent ratio of the `ε`-sequence. -/
noncomputable def qq (n k : ℕ) : ℝ := (((2 : ℕ) ^ (min k n) : ℕ) : ℝ)

@[simp] lemma qq_zero (n : ℕ) : qq n 0 = 1 := by
  simp [qq]

lemma qq_pos (n k : ℕ) : 0 < qq n k := by
  simp only [qq]; positivity

/-- The main induction invariant:
`e₀^{qq k} · c^{−(qq k − 1)} ≤ epsSeq i m e₀ k`, `c = 2^{i+1}`. -/
lemma epsSeq_ge_aux {i m : ℕ} {e₀ : ℝ} (he₀ : 0 < e₀) (he₁ : e₀ ≤ 1) (k : ℕ) :
    e₀ ^ (qq (i - m) k) * (((2 : ℝ) ^ (i + 1 : ℕ)) ^ (-(qq (i - m) k - 1))) ≤
      epsSeq i m e₀ k := by
  induction k with
  | zero =>
    rw [qq_zero, epsSeq_zero]
    simp only [Real.rpow_one, sub_self, neg_zero, rpow_zero, mul_one]
    exact le_rfl
  | succ k ih =>
    have hcpos : (0 : ℝ) < (2 : ℝ) ^ (i + 1 : ℕ) := by positivity
    have hc1 : (1 : ℝ) ≤ (2 : ℝ) ^ (i + 1 : ℕ) := one_le_pow₀ (by norm_num)
    rcases lt_or_ge k (i - m) with hk | hk
    · -- the genuinely decreasing step: `x_{k+1} = x·(x/c)^α` with `α = 1/(i−m−k) ≤ 1`
      have hαpos : (0 : ℝ) < ((i - m - k : ℕ) : ℝ) := by
        have : 0 < i - m - k := by omega
        exact_mod_cast this
      have hαle : ((i - m - k : ℕ) : ℝ)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ hαpos]
        exact_mod_cast (by omega : 1 ≤ i - m - k)
      have hαnn : 0 ≤ ((i - m - k : ℕ) : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hαpos)
      have hxpos : 0 < epsSeq i m e₀ k := epsSeq_pos (i := i) (m := m) he₀ k
      have hx1 : epsSeq i m e₀ k ≤ 1 :=
        le_trans (epsSeq_le_zero (i := i) (m := m) he₀ he₁ k) he₁
      rw [epsSeq_succ, one_div]
      -- step 1: expand
      have hstep : epsSeq i m e₀ k *
            (epsSeq i m e₀ k / (2 : ℝ) ^ (i + 1 : ℕ)) ^ ((i - m - k : ℕ) : ℝ)⁻¹ =
          (epsSeq i m e₀ k) ^ (1 + ((i - m - k : ℕ) : ℝ)⁻¹) *
            ((2 : ℝ) ^ (i + 1 : ℕ)) ^ (-((i - m - k : ℕ) : ℝ)⁻¹) := by
        calc epsSeq i m e₀ k *
              (epsSeq i m e₀ k / (2 : ℝ) ^ (i + 1 : ℕ)) ^ ((i - m - k : ℕ) : ℝ)⁻¹
            = epsSeq i m e₀ k * ((epsSeq i m e₀ k) ^ ((i - m - k : ℕ) : ℝ)⁻¹ *
                (((2 : ℝ) ^ (i + 1 : ℕ)) ^ ((i - m - k : ℕ) : ℝ)⁻¹)⁻¹) := by
              rw [Real.div_rpow hxpos.le hcpos.le, div_eq_mul_inv]
          _ = ((epsSeq i m e₀ k) ^ (1:ℝ) * (epsSeq i m e₀ k) ^ ((i - m - k : ℕ) : ℝ)⁻¹) *
                (((2 : ℝ) ^ (i + 1 : ℕ)) ^ ((i - m - k : ℕ) : ℝ)⁻¹)⁻¹ := by
              rw [Real.rpow_one]; ring
          _ = (epsSeq i m e₀ k) ^ (1 + ((i - m - k : ℕ) : ℝ)⁻¹) *
                (((2 : ℝ) ^ (i + 1 : ℕ)) ^ ((i - m - k : ℕ) : ℝ)⁻¹)⁻¹ := by
              rw [← Real.rpow_add hxpos]
          _ = (epsSeq i m e₀ k) ^ (1 + ((i - m - k : ℕ) : ℝ)⁻¹) *
                ((2 : ℝ) ^ (i + 1 : ℕ)) ^ (-((i - m - k : ℕ) : ℝ)⁻¹) := by
              rw [Real.rpow_neg hcpos.le]
      rw [hstep]
      -- step 2: compare exponents
      have hexp : (1 : ℝ) + ((i - m - k : ℕ) : ℝ)⁻¹ ≤ 2 := by linarith
      have hpow : (epsSeq i m e₀ k) ^ (2:ℝ) ≤
          (epsSeq i m e₀ k) ^ (1 + ((i - m - k : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow_of_exponent_ge hxpos hx1 hexp
      have hcneg : ((2 : ℝ) ^ (i + 1 : ℕ)) ^ (-((i - m - k : ℕ) : ℝ)⁻¹) ≥
          ((2 : ℝ) ^ (i + 1 : ℕ)) ^ (-(1:ℝ)) := by
        refine Real.rpow_le_rpow_of_exponent_le hc1 ?_
        linarith
      have h2 : (epsSeq i m e₀ k) ^ (2:ℝ) * ((2 : ℝ) ^ (i + 1 : ℕ)) ^ (-(1:ℝ)) ≤
          (epsSeq i m e₀ k) ^ (1 + ((i - m - k : ℕ) : ℝ)⁻¹) *
            ((2 : ℝ) ^ (i + 1 : ℕ)) ^ (-((i - m - k : ℕ) : ℝ)⁻¹) :=
        mul_le_mul hpow hcneg (by positivity) (Real.rpow_nonneg hxpos.le _)
      -- step 3: the induction hypothesis, squared
      have hsq : (e₀ ^ (qq (i - m) k) *
            ((2 : ℝ) ^ (i + 1 : ℕ)) ^ (-(qq (i - m) k - 1))) ^ (2:ℝ) ≤
          (epsSeq i m e₀ k) ^ (2:ℝ) :=
        Real.rpow_le_rpow (by positivity) ih (by norm_num)
      -- step 4: exponent identities
      have hq : qq (i - m) (k + 1) = 2 * qq (i - m) k := by
        simp only [qq]
        rw [Nat.min_eq_left (show k + 1 ≤ i - m by omega),
          Nat.min_eq_left (show k ≤ i - m by omega), pow_succ]
        push_cast
        ring
      have hid : (e₀ ^ (qq (i - m) k) *
            ((2 : ℝ) ^ (i + 1 : ℕ)) ^ (-(qq (i - m) k - 1))) ^ (2:ℝ) *
            ((2 : ℝ) ^ (i + 1 : ℕ)) ^ (-(1:ℝ)) =
          e₀ ^ (qq (i - m) (k + 1)) *
            ((2 : ℝ) ^ (i + 1 : ℕ)) ^ (-(qq (i - m) (k + 1) - 1)) := by
        have hqid : -(qq (i - m) k - 1) * 2 + (-(1:ℝ)) = -(qq (i - m) (k + 1) - 1) := by
          rw [hq]; ring
        rw [Real.mul_rpow (Real.rpow_nonneg he₀.le _) (Real.rpow_nonneg hcpos.le _),
          ← Real.rpow_mul he₀.le, ← Real.rpow_mul hcpos.le, mul_assoc, ← Real.rpow_add hcpos,
          hqid]
        congr 1
        rw [hq]; ring
      rw [← hid]
      exact le_trans (mul_le_mul_of_nonneg_right hsq (by positivity)) h2
    · -- the frozen step
      have hzero : i - m - k = 0 := by omega
      rw [epsSeq_succ, hzero]
      simp only [Nat.cast_zero, div_zero, rpow_zero, mul_one]
      have hq : qq (i - m) (k + 1) = qq (i - m) k := by
        simp only [qq]
        rw [Nat.min_eq_right (show i - m ≤ k + 1 by omega),
          Nat.min_eq_right (show i - m ≤ k by omega)]
      rw [hq]
      exact ih

/-- **The quantitative bound for the `ε`-sequence.** -/
theorem epsSeq_ge {i m : ℕ} {e₀ : ℝ} (he₀ : 0 < e₀) (he₁ : e₀ ≤ 1) (k : ℕ) :
    e₀ ^ ((2 : ℝ) ^ i) * (((2 : ℝ) ^ (i + 1 : ℕ)) ^ (-((2 : ℝ) ^ i))) ≤ epsSeq i m e₀ k := by
  have hmain := epsSeq_ge_aux (i := i) (m := m) he₀ he₁ k
  have hcpos : (0 : ℝ) < (2 : ℝ) ^ (i + 1 : ℕ) := by positivity
  have hc1 : (1 : ℝ) ≤ (2 : ℝ) ^ (i + 1 : ℕ) := one_le_pow₀ (by norm_num)
  have hq1 : 1 ≤ qq (i - m) k := by
    simp only [qq]
    exact_mod_cast Nat.one_le_two_pow
  have hq2 : qq (i - m) k ≤ (2 : ℝ) ^ i := by
    simp only [qq]
    have h : (2 : ℕ) ^ min k (i - m) ≤ (2 : ℕ) ^ i :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast h
  have hpow : e₀ ^ ((2 : ℝ) ^ i) ≤ e₀ ^ (qq (i - m) k) :=
    Real.rpow_le_rpow_of_exponent_ge he₀ he₁ hq2
  have hb : ((2 : ℝ) ^ (i + 1 : ℕ)) ^ (-((2 : ℝ) ^ i)) ≤
      ((2 : ℝ) ^ (i + 1 : ℕ)) ^ (-(qq (i - m) k - 1)) := by
    refine Real.rpow_le_rpow_of_exponent_le hc1 ?_
    linarith
  calc e₀ ^ ((2 : ℝ) ^ i) * ((2 : ℝ) ^ (i + 1 : ℕ)) ^ (-((2 : ℝ) ^ i))
      ≤ e₀ ^ (qq (i - m) k) * (((2 : ℝ) ^ (i + 1 : ℕ)) ^ (-(qq (i - m) k - 1))) :=
        mul_le_mul hpow hb (by positivity) (by positivity)
    _ ≤ epsSeq i m e₀ k := hmain

/-- **The bounded extension step.**  The same statement as
`BatchAccumulation.exists_dominated_extension`, with the explicit lower bound
`e₀^{2^i}·(2^{i+1})^{−2^i}` (`e₀ = min (min lev c) 1`) for the resulting dominance level. -/
theorem exists_dominated_extension_bound {m i : ℕ} (hmi : m < i) (hm0 : 1 ≤ m)
    (P : RD d →ₗ[ℝ] RD d) (hP : ∀ x, ‖P x‖ ≤ ‖x‖) {W : Submodule ℝ (RD d)}
    {e : Fin m → RD d} (he : Orthonormal ℝ e) (heW : ∀ k, e k ∈ W) {lev c : ℝ}
    (hlev : 0 < lev) (hlevc : lev ≤ c)
    (hdom : lev ≤ ‖exteriorPower.map m P (exteriorPower.ιMulti ℝ m e)‖)
    {u : Fin i → RD d} (hu : Orthonormal ℝ u) (huW : ∀ k, u k ∈ W)
    (hbig : c ≤ ‖exteriorPower.map i P (exteriorPower.ιMulti ℝ i u)‖) :
    ∃ (e' : Fin i → RD d) (lev' : ℝ), 0 < lev' ∧ lev' ≤ c ∧ Orthonormal ℝ e' ∧
      (∀ k, e' k ∈ W) ∧ (∀ k : Fin m, e' (Fin.castLE (le_of_lt hmi) k) = e k) ∧
      (min (min lev c) 1) ^ ((2 : ℝ) ^ i) * (((2 : ℝ) ^ (i + 1 : ℕ)) ^ (-((2 : ℝ) ^ i))) ≤ lev' ∧
      lev' ≤ ‖exteriorPower.map i P (exteriorPower.ιMulti ℝ i e')‖ := by
  classical
  set e₀ : ℝ := min (min lev c) 1 with he₀
  have he₀pos : 0 < e₀ := lt_min (lt_min hlev (lt_of_lt_of_le hlev hlevc)) one_pos
  have he₀le1 : e₀ ≤ 1 := min_le_right _ _
  have he₀lelev : e₀ ≤ lev := le_trans (min_le_left _ _) (min_le_left _ _)
  have he₀lec : e₀ ≤ c := le_trans (min_le_left _ _) (min_le_right _ _)
  obtain ⟨εseq, γ, hεpos, hεle, hεm, hγ0, hγ1, hstep, hεi⟩ :=
    exists_epsSeq_expl (i := i) (m := m) hmi he₀pos he₀le1
  obtain ⟨e', he'ON, he'W, he'ext, he'cone⟩ :=
    exists_orthonormal_cone_family (d := d) P hP (le_of_lt hmi) hm0 W e he heW u hu huW
      εseq hεpos hεle (by rw [hεm]; exact le_trans he₀lelev hdom)
      (by rw [hεm]; exact le_trans he₀lec hbig) γ hγ0 hγ1 hstep
  refine ⟨e', εseq i, hεpos i, le_trans (hεle i) (hεm ▸ he₀lec), he'ON, he'W, he'ext, ?_, he'cone⟩
  rw [hεi]
  exact epsSeq_ge (i := i) (m := m) he₀pos he₀le1 (i - m)

end Submission.LevelBound

end
