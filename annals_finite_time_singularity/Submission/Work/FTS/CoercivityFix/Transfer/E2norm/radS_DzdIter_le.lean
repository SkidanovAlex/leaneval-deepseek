/-
# `Transfer/E2norm/radS_DzdIter_le` — the weighted `L²`-bound for the `D_z`-iterates of `radS`

The second summand `Γ(θ)·radS α f z` of the transfer defect `E2 α f` has to be controlled in the
`ℋⁿ`-norm at level `n ≤ 3`.  This file supplies exactly that estimate: there is a universal
constant `C` (independent of `α ∈ (0,1]`, `n`, `f`, `KB`, `KC`, `j`) with

  `∫_z (D_z^j (radS α f)(z))² w(z)² dz ≤ C (KB+1)(KC+1)(|f|²_{ℋⁿ} + |D_θ f|²_{ℋⁿ})`

for `j ≤ n ≤ 3`, where `KB` bounds the weighted squares of the `(z∂_z)`-iterates of the
projector profile `ampB α` and `KC·|D_θ f|²_{ℋⁿ}` bounds `(L₁₂(Transport f)(0))²`.

## The route

`E2pkg.radS_sq_le_SmajA` dominates `(D_z^j (radS α f))²w²` pointwise on `(0,∞)` by the explicit
majorant

  `SmajA α f j K z = 3·(A·K²·∑_{b≤j}(D_z^{j-b}L₁₂f)²w² + A·K²·∑_{b≤j}(Qang f (j-b))²w²
                        + (L₁₂(Transport f)(0)/c α)²·(D_z^{j+1}ampB)²w²)`, `A = ∑_{b≤j}C(j,b)²`,

with `K` the `α`-uniform bound on the `D_z`-iterates of `ampA` (`ampA_dzdIter_bound_uniform`).
Integrating the majorant (`E2norm.smajA_integral_eq` pushes the integral inside) and using

* `E2norm.sum_L12_iter_integral_le`: the first sum is `≤ (j+1)·107·(∫_θ Kθ²)·|f|²_{ℋⁿ}`
  (`E2norm.L12f_DzdIter_sq_w_sq_le`; note `j - b ≤ j ≤ n`),
* `E2norm.sum_Qang_iter_integral_le`: the second sum is `≤ (j+1)·(∫_θ Kθ²)·|f|²_{ℋⁿ}`
  (`E2norm.qang_sq_w_sq_le`),
* the third block is `≤ (100·KC·|D_θ f|²_{ℋⁿ})·KB`: `1/c(α) ≤ 10` (`Spaces.c_bounds`) and the
  `KB`-hypothesis at `c = j+1 ≤ 4`,
* `∑_{b≤j}C(j,b)² ≤ 4^j ≤ 64` and `j + 1 ≤ 4`,

gives the claim with the explicit constant `C = 82944·K²·(∫_θ Kθ²) + 301`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.Pieces
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadSBnd
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadSAux
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadS
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAPieces
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.sum_L12_iter_integral_le
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.sum_Qang_iter_integral_le
import Submission.Work.Spaces.c_bounds
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.E2norm

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The sum of the squares of the binomial coefficients is at most `4^j`
(its value is `C(2j,j) ≤ 4^j`). -/
private theorem sum_choose_sq_le (j : ℕ) :
    (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) ≤ 4 ^ j := by
  have hsum : (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ)) = (2 : ℝ) ^ j := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
  have hcb : ∀ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ≤ (2 : ℝ) ^ j := by
    intro b hb
    have h1 := Finset.single_le_sum (f := fun i : ℕ => ((j.choose i : ℕ) : ℝ))
      (fun i _ => Nat.cast_nonneg _) hb
    rwa [hsum] at h1
  calc (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2)
      ≤ ∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) * (2 : ℝ) ^ j := by
        refine Finset.sum_le_sum fun b hb => ?_
        rw [sq]
        exact mul_le_mul_of_nonneg_left (hcb b hb) (Nat.cast_nonneg _)
    _ = (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ)) * (2 : ℝ) ^ j := by
        rw [Finset.sum_mul]
    _ = 4 ^ j := by
        rw [hsum, ← mul_pow]
        norm_num

/-- **Linearity of the interval integral over the majorant `SmajA`.**  Unfolding `SmajA` and
pushing the integral inside turns it into the sum of the three block integrals. -/
private theorem smajA_integral_eq_aux (α : ℝ) {f : ℝ → ℝ → ℝ} (j : ℕ) (KA : ℝ)
    (h1 : ∀ b ∈ Finset.range (j + 1), MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)))
    (h2 : ∀ b ∈ Finset.range (j + 1), MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi (0 : ℝ)))
    (h3 : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ))) :
    ∫ z in Set.Ioi (0 : ℝ), Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA α f j KA z
      = 3 * ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
              * (∑ b ∈ Finset.range (j + 1), ∫ z in Set.Ioi (0 : ℝ),
                  (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
                    * (Work.Spaces.w z) ^ 2)
            + (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
              * (∑ b ∈ Finset.range (j + 1), ∫ z in Set.Ioi (0 : ℝ),
                  (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
            + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
              * (∫ z in Set.Ioi (0 : ℝ),
                  (Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
                    * (Work.Spaces.w z) ^ 2)) := by
  have hF1 : MeasureTheory.IntegrableOn (fun z : ℝ => ∑ b ∈ Finset.range (j + 1),
      (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.integrable_finsetSum (Finset.range (j + 1)) h1
  have hF2 : MeasureTheory.IntegrableOn (fun z : ℝ => ∑ b ∈ Finset.range (j + 1),
      (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.integrable_finsetSum (Finset.range (j + 1)) h2
  have hXint : MeasureTheory.IntegrableOn (fun z : ℝ =>
      ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2)
        * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
              * (Work.Spaces.w z) ^ 2)) (Set.Ioi (0 : ℝ)) := hF1.const_mul _
  have hYint : MeasureTheory.IntegrableOn (fun z : ℝ =>
      ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2)
        * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2))
      (Set.Ioi (0 : ℝ)) := hF2.const_mul _
  have hZint : MeasureTheory.IntegrableOn (fun z : ℝ =>
      (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
        * ((Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2)) (Set.Ioi (0 : ℝ)) := h3.const_mul _
  have hXYint : MeasureTheory.IntegrableOn (fun z : ℝ =>
      ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2)
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
                * (Work.Spaces.w z) ^ 2)
        + ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2)
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2))
      (Set.Ioi (0 : ℝ)) := hXint.add hYint
  simp only [Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [MeasureTheory.integral_add hXYint hZint]
  rw [MeasureTheory.integral_add hXint hYint]
  simp only [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_finsetSum (Finset.range (j + 1)) h1,
    MeasureTheory.integral_finsetSum (Finset.range (j + 1)) h2]

theorem radS_DzdIter_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 →
      ∀ f : ℝ → ℝ → ℝ, Work.FTS.Nonlin.CoerAdm α f →
      ∀ (KB : ℝ), 0 ≤ KB → (∀ c : ℕ, c ≤ 4 → ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
            * (Work.Spaces.w z) ^ 2 ≤ KB) →
      ∀ (KC : ℝ), 0 ≤ KC → (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
          ≤ KC * Work.Spaces.HkSq α n (Work.Spaces.Dth f) →
      ∀ j : ℕ, j ≤ n → ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2
        ≤ C * (KB + 1) * (KC + 1)
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
  obtain ⟨KA, hKAnn, hKAbd0⟩ := ampA_dzdIter_bound_uniform
  have hKθ2nn0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hCnn : 0 ≤ 82944 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 301 := by
    have h1 : (0 : ℝ) ≤ 82944 * KA ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg KA)) hKθ2nn0
    linarith
  refine ⟨82944 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 301, hCnn, ?_⟩
  intro α hα hα1 n hn f hf KB hKBnn hKB KC hKCnn hKC j hj
  -- shorthand for the five quantities entering the final arithmetic
  generalize hAdef : (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) = A
  generalize hKθ2def : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) = Kθ2
  generalize hHdef : Work.Spaces.HkSq α n f = H
  generalize hH'def : Work.Spaces.HkSq α n (Work.Spaces.Dth f) = H'
  generalize hI1def : (∑ b ∈ Finset.range (j + 1), ∫ z in Set.Ioi (0 : ℝ),
      (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) = I1
  generalize hI2def : (∑ b ∈ Finset.range (j + 1), ∫ z in Set.Ioi (0 : ℝ),
      (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2) = I2
  generalize hI3def : (∫ z in Set.Ioi (0 : ℝ),
      (Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) = I3
  generalize hD2def :
    (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2 = D2
  have hKθ2nn : 0 ≤ Kθ2 := by rw [← hKθ2def]; exact hKθ2nn0
  have hHnn : 0 ≤ H := by rw [← hHdef]; exact Work.Spaces.HkSq_nonneg α n f
  have hH'nn : 0 ≤ H' := by rw [← hH'def]; exact Work.Spaces.HkSq_nonneg α n (Work.Spaces.Dth f)
  have hj3 : j ≤ 3 := by omega
  have hj1 : (j : ℝ) + 1 ≤ 4 := by
    have : (j : ℝ) ≤ 3 := by exact_mod_cast hj3
    linarith
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.CoercivityFix.Coer1T.HkMem_four_of_five α hsm hf.reg.2.1
  -- the pointwise domination on `(0,∞)` and the two integrability statements
  have hKbd : ∀ b ≤ 4, ∀ z ∈ Work.FTS.CoercivityFix.Transfer.E2pkg.IoiA,
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ KA :=
    fun b hb z hz => hKAbd0 α hα hα1 b hb z hz
  have hIntL : MeasureTheory.IntegrableOn (fun z : ℝ =>
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.CoercivityFix.Transfer.E2pkg.radS_DzdIter_sq_w_sq_integrable α hα hα1 hf j
      hj3).mono_set Set.Ioi_subset_Ici_self
  have hIntR : MeasureTheory.IntegrableOn
      (Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA α f j KA) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.integrableOn_SmajA α hα hα1 hf hj3 KA
  have hstep : (∫ z in Set.Ioi (0 : ℝ),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Set.Ioi (0 : ℝ), Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA α f j KA z :=
    MeasureTheory.integral_mono_ae hIntL hIntR
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun z hz =>
        Work.FTS.CoercivityFix.Transfer.E2pkg.radS_sq_le_SmajA α hα hα1 hf hj3 hKAnn hKbd z hz)
  -- integrability of the summands of the majorant
  have hint1 : ∀ b ∈ Finset.range (j + 1), MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    intro b hb
    have hb1 : j - b ≤ 3 := by
      have := Finset.mem_range.mp hb
      omega
    exact Work.FTS.CoercivityFix.Transfer.E1Parts.L12f_DzdIter_sq_w_sq_integrable_Ioi α hα hα1 hf
      (j - b) hb1
  have hint2 : ∀ b ∈ Finset.range (j + 1), MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    intro b hb
    have hb1 : j - b ≤ 4 := by
      have := Finset.mem_range.mp hb
      omega
    exact Work.FTS.CoercivityFix.Transfer.E1Parts.Qang_sq_w_sq_integrable_Ioi α hα hα1 hsm hmem4
      hb1
  have hint3 : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.CoercivityFix.Transfer.E1Parts.ampB_DzdIter_sq_w_sq_integrable_Ioi α hα hα1
      (show j + 1 ≤ 4 by omega)
  -- the linearity of the integral of the majorant
  have hlin : (∫ z in Set.Ioi (0 : ℝ), Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA α f j KA z)
      = 3 * (A * KA ^ 2 * I1 + A * KA ^ 2 * I2 + D2 * I3) := by
    have hs := smajA_integral_eq_aux α (f := f) (j := j) (KA := KA) hint1 hint2 hint3
    rw [hAdef, hI1def, hI2def, hI3def, hD2def] at hs
    exact hs
  -- the three integral bounds
  have hI1le : I1 ≤ ((j : ℝ) + 1) * (107 * Kθ2 * H) := by
    have hs := sum_L12_iter_integral_le α hα hα1 hn hf hj
    rw [hI1def, hKθ2def, hHdef] at hs
    exact hs
  have h1' : I1 ≤ 4 * (107 * Kθ2 * H) :=
    le_trans hI1le (mul_le_mul_of_nonneg_right hj1 (mul_nonneg (mul_nonneg (by norm_num) hKθ2nn) hHnn))
  have hI2le : I2 ≤ ((j : ℝ) + 1) * (Kθ2 * H) := by
    have hs := sum_Qang_iter_integral_le α hα hα1 hn hf hj
    rw [hI2def, hKθ2def, hHdef] at hs
    exact hs
  have h2' : I2 ≤ 4 * (Kθ2 * H) :=
    le_trans hI2le (mul_le_mul_of_nonneg_right hj1 (mul_nonneg hKθ2nn hHnn))
  have hI3le : I3 ≤ KB := by
    rw [← hI3def]
    rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact hKB (j + 1) (by omega)
  have hKC' : (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2 ≤ KC * H' := by
    rw [hH'def] at hKC
    exact hKC
  have hd2le : D2 ≤ 100 * KC * H' := by
    rw [← hD2def]
    have hc := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    have hcsq : (1 : ℝ) / 100 ≤ (Work.Spaces.c α) ^ 2 := by nlinarith [hc, hcpos]
    have hinv : ((Work.Spaces.c α) ^ 2)⁻¹ ≤ 100 := by
      rw [inv_eq_one_div, div_le_iff₀ (pow_pos hcpos 2)]
      nlinarith [hcsq]
    calc (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
        = (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
            * ((Work.Spaces.c α) ^ 2)⁻¹ := by rw [div_pow, div_eq_mul_inv]
      _ ≤ (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2 * 100 :=
          mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
      _ ≤ (KC * H') * 100 := mul_le_mul_of_nonneg_right hKC' (by norm_num)
      _ = 100 * KC * H' := by ring
  -- nonnegativity and the bound on the binomial sum
  have hAnn : 0 ≤ A := by rw [← hAdef]; exact Finset.sum_nonneg (fun b _ => sq_nonneg _)
  have hA64 : A ≤ 64 := by
    rw [← hAdef]
    calc (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) ≤ 4 ^ j := sum_choose_sq_le j
      _ ≤ 4 ^ 3 := pow_le_pow_right₀ (by norm_num) hj3
      _ = 64 := by norm_num
  have hI1nn : 0 ≤ I1 := by
    rw [← hI1def]
    exact Finset.sum_nonneg fun b _ =>
      MeasureTheory.integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hI2nn : 0 ≤ I2 := by
    rw [← hI2def]
    exact Finset.sum_nonneg fun b _ =>
      MeasureTheory.integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hI3nn : 0 ≤ I3 := by
    rw [← hI3def]
    exact MeasureTheory.integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hD2nn : 0 ≤ D2 := by rw [← hD2def]; exact sq_nonneg _
  have hKA2 : 0 ≤ KA ^ 2 := sq_nonneg KA
  -- the three products
  have hP1 : A * KA ^ 2 * I1 ≤ 27392 * KA ^ 2 * Kθ2 * H := by
    have h1 : A * KA ^ 2 ≤ 64 * KA ^ 2 := mul_le_mul_of_nonneg_right hA64 hKA2
    have h2 : (0 : ℝ) ≤ 64 * KA ^ 2 := mul_nonneg (by norm_num) hKA2
    have h3 := mul_le_mul h1 h1' hI1nn h2
    calc A * KA ^ 2 * I1 ≤ (64 * KA ^ 2) * (4 * (107 * Kθ2 * H)) := h3
      _ = 27392 * KA ^ 2 * Kθ2 * H := by ring
  have hP2 : A * KA ^ 2 * I2 ≤ 256 * KA ^ 2 * Kθ2 * H := by
    have h1 : A * KA ^ 2 ≤ 64 * KA ^ 2 := mul_le_mul_of_nonneg_right hA64 hKA2
    have h2 : (0 : ℝ) ≤ 64 * KA ^ 2 := mul_nonneg (by norm_num) hKA2
    have h3 := mul_le_mul h1 h2' hI2nn h2
    calc A * KA ^ 2 * I2 ≤ (64 * KA ^ 2) * (4 * (Kθ2 * H)) := h3
      _ = 256 * KA ^ 2 * Kθ2 * H := by ring
  have hP3 : D2 * I3 ≤ (100 * KC * H') * KB := by
    have hnn : (0 : ℝ) ≤ 100 * KC * H' := mul_nonneg (mul_nonneg (by norm_num) hKCnn) hH'nn
    exact mul_le_mul hd2le hI3le hI3nn hnn
  -- summing up
  have hSum : 3 * (A * KA ^ 2 * I1 + A * KA ^ 2 * I2 + D2 * I3)
      ≤ 82944 * KA ^ 2 * Kθ2 * H + 300 * (KC * H' * KB) := by
    have e : 3 * (27392 * KA ^ 2 * Kθ2 * H + 256 * KA ^ 2 * Kθ2 * H + (100 * KC * H') * KB)
        = 82944 * KA ^ 2 * Kθ2 * H + 300 * (KC * H' * KB) := by ring
    linarith [hP1, hP2, hP3, e]
  -- the final arithmetic
  have hXnn : 0 ≤ (KB + 1) * (KC + 1) * (H + H') := by
    have h1 : (0 : ℝ) ≤ KB + 1 := by linarith
    have h2 : (0 : ℝ) ≤ KC + 1 := by linarith
    have h3 : (0 : ℝ) ≤ H + H' := by linarith
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hX1 : (1 : ℝ) ≤ (KB + 1) * (KC + 1) := by nlinarith
  have hXB : (0 : ℝ) ≤ (KB + 1) * (KC + 1) := by linarith
  have hHX : H ≤ (KB + 1) * (KC + 1) * (H + H') := by
    have h := mul_le_mul hX1 (show H ≤ H + H' by linarith) hHnn hXB
    simpa using h
  have hKBKC : KB * KC ≤ (KB + 1) * (KC + 1) := by nlinarith
  have hKBKC' : KC * H' * KB ≤ (KB + 1) * (KC + 1) * (H + H') := by
    have h := mul_le_mul hKBKC (show H' ≤ H + H' by linarith) hH'nn hXB
    calc KC * H' * KB = (KB * KC) * H' := by ring
      _ ≤ ((KB + 1) * (KC + 1)) * (H + H') := h
      _ = (KB + 1) * (KC + 1) * (H + H') := by ring
  have hfin : 3 * (A * KA ^ 2 * I1 + A * KA ^ 2 * I2 + D2 * I3)
      ≤ (82944 * KA ^ 2 * Kθ2 + 301) * ((KB + 1) * (KC + 1) * (H + H')) := by
    have hT1 : 82944 * KA ^ 2 * Kθ2 * H
        ≤ (82944 * KA ^ 2 * Kθ2) * ((KB + 1) * (KC + 1) * (H + H')) :=
      mul_le_mul_of_nonneg_left hHX
        (mul_nonneg (mul_nonneg (by norm_num) hKA2) hKθ2nn)
    have hT2 : 300 * (KC * H' * KB) ≤ 300 * ((KB + 1) * (KC + 1) * (H + H')) :=
      mul_le_mul_of_nonneg_left hKBKC' (by norm_num)
    linarith [hSum, hT1, hT2, hXnn]
  -- transfer from `Iz` to `(0,∞)` and assemble
  have hIz : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2 := by
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
    exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
  calc (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2 := hIz
    _ ≤ ∫ z in Set.Ioi (0 : ℝ), Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA α f j KA z := hstep
    _ = 3 * (A * KA ^ 2 * I1 + A * KA ^ 2 * I2 + D2 * I3) := hlin
    _ ≤ (82944 * KA ^ 2 * Kθ2 + 301) * ((KB + 1) * (KC + 1) * (H + H')) := hfin
    _ = (82944 * KA ^ 2 * Kθ2 + 301) * (KB + 1) * (KC + 1) * (H + H') := by ring

end Work.FTS.CoercivityFix.Transfer.E2norm
