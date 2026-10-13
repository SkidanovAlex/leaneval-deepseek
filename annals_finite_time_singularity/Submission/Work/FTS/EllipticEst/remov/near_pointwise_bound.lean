import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.remov.Lzero1_iteratedDeriv_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Pointwise near-axis bound for the top derivative of the slice ODE

The slice ODE `g = Lzero1 u` reads `u'' = ∂_θ(tan θ · u) - 6u - g`, and differentiating it `k`
times (`Lzero1_iteratedDeriv_eq`) gives, at every `θ ∈ (0, π/2)`,

  `u^{(k+2)}(θ) = ∑_{i≤k+1} C(k+1,i)(tan)^{(i)}(θ) u^{(k+1-i)}(θ) - 6u^{(k)}(θ) - g^{(k)}(θ)`.

The interval `[0, π/8]` is contained in `(-π/2, π/2)`, where `tan` is analytic, so the finitely
many coefficient functions `(tan)^{(i)}`, `i ≤ k+1`, are continuous on it and therefore bounded
by a single constant `M` depending only on `k`.  Combining the identity with the elementary
finite-sum Cauchy–Schwarz inequality yields the stated pointwise bound for `θ ∈ (0, π/8)`.
-/

open scoped Real Topology
open Set Filter

namespace Work.FTS.EllipticEst.remov

/-- `Real.tan` is `C^n` on any set on which the cosine does not vanish. -/
theorem contDiffOn_tan_of_cos_ne_zero {s : Set ℝ} (h : ∀ x ∈ s, Real.cos x ≠ 0)
    (n : WithTop ℕ∞) : ContDiffOn ℝ n Real.tan s :=
  fun x hx => (Real.contDiffAt_tan.mpr (h x hx)).contDiffWithinAt

/-- The cosine does not vanish on `[0, π/8]`. -/
lemma cos_ne_zero_Icc_pi_div_eight {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (Real.pi / 8)) :
    Real.cos x ≠ 0 := by
  have hx' : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo hx')

/-- Every iterated derivative of `Real.tan` is continuous on the compact interval `[0, π/8]`. -/
lemma continuousOn_iteratedDeriv_tan (i : ℕ) :
    ContinuousOn (iteratedDeriv i Real.tan) (Set.Icc (0 : ℝ) (Real.pi / 8)) := by
  have hlt : (0 : ℝ) < Real.pi / 8 := by linarith [Real.pi_pos]
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (Real.pi / 8)) := uniqueDiffOn_Icc hlt
  have hcd : ContDiffOn ℝ (⊤ : WithTop ℕ∞) Real.tan (Set.Icc (0 : ℝ) (Real.pi / 8)) :=
    contDiffOn_tan_of_cos_ne_zero (fun x hx => cos_ne_zero_Icc_pi_div_eight hx) ⊤
  have hc : ContinuousOn (iteratedDerivWithin i Real.tan (Set.Icc (0 : ℝ) (Real.pi / 8)))
      (Set.Icc (0 : ℝ) (Real.pi / 8)) :=
    hcd.continuousOn_iteratedDerivWithin le_top huniq
  refine hc.congr (fun x hx => ?_)
  exact (iteratedDerivWithin_eq_iteratedDeriv huniq
    ((Real.contDiffAt_tan.mpr (cos_ne_zero_Icc_pi_div_eight hx)).of_le le_top) hx).symm

/-- The iterated derivatives of `Real.tan`, of all orders up to a fixed `N`, are bounded by a
single constant `M ≥ 1` on `[0, π/8]`. -/
theorem tan_deriv_bound_Icc (N : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i ≤ N, ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 8),
      |iteratedDeriv i Real.tan θ| ≤ M := by
  classical
  have hb : ∀ i : ℕ, ∃ C : ℝ, ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 8),
      |iteratedDeriv i Real.tan θ| ≤ C := by
    intro i
    obtain ⟨C, hC⟩ :=
      (isCompact_Icc (a := (0 : ℝ)) (b := Real.pi / 8)).exists_bound_of_continuousOn
        (continuousOn_iteratedDeriv_tan i)
    exact ⟨C, fun θ hθ => by simpa [Real.norm_eq_abs] using hC θ hθ⟩
  choose C hC using hb
  refine ⟨max 1 (∑ j ∈ Finset.range (N + 1), |C j|), le_max_left _ _, ?_⟩
  intro i hi θ hθ
  have h1 : |iteratedDeriv i Real.tan θ| ≤ C i := hC i θ hθ
  have h2 : |C i| ≤ ∑ j ∈ Finset.range (N + 1), |C j| :=
    Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have h3 : C i ≤ |C i| := le_abs_self (C i)
  have h4 : (∑ j ∈ Finset.range (N + 1), |C j|)
      ≤ max 1 (∑ j ∈ Finset.range (N + 1), |C j|) := le_max_right _ _
  linarith

/-- Finite-sum Cauchy–Schwarz with the reflection reindexing `i ↦ n-1-i`: if every coefficient
`c i` (`i < n`) is bounded by `D ≥ 0`, then
`(∑_{i<n} c i · v (n-1-i))² ≤ D² · n · ∑_{m<n} (v m)²`. -/
theorem sum_cs_reflect_bound (n : ℕ) (D : ℝ) (_hD : 0 ≤ D) (c v : ℕ → ℝ)
    (hc : ∀ i < n, |c i| ≤ D) :
    (∑ i ∈ Finset.range n, c i * v (n - 1 - i)) ^ 2
      ≤ D ^ 2 * n * ∑ m ∈ Finset.range n, (v m) ^ 2 := by
  set S : ℝ := ∑ i ∈ Finset.range n, c i * v (n - 1 - i) with hSdef
  set Sig : ℝ := ∑ m ∈ Finset.range n, |v m| with hSigdef
  have hSabs : |S| ≤ D * Sig := by
    rw [hSdef, hSigdef]
    calc |∑ i ∈ Finset.range n, c i * v (n - 1 - i)|
        ≤ ∑ i ∈ Finset.range n, |c i * v (n - 1 - i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n, D * |v (n - 1 - i)| := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hc i (Finset.mem_range.mp hi)) (abs_nonneg _)
      _ = D * ∑ i ∈ Finset.range n, |v (n - 1 - i)| := by rw [Finset.mul_sum]
      _ = D * ∑ m ∈ Finset.range n, |v m| := by
          rw [Finset.sum_range_reflect (fun m => |v m|) n]
  have hSigsq : Sig ^ 2 ≤ (n : ℝ) * ∑ m ∈ Finset.range n, (v m) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range n) (f := fun m => |v m|)
    rw [Finset.card_range] at h
    rw [hSigdef]
    simpa only [sq_abs] using h
  have hSignn : 0 ≤ Sig := by
    rw [hSigdef]
    exact Finset.sum_nonneg (fun m _ => abs_nonneg _)
  calc S ^ 2 = |S| ^ 2 := by rw [sq_abs]
    _ ≤ (D * Sig) ^ 2 := by
        have h := mul_self_le_mul_self (abs_nonneg S) hSabs
        simpa [pow_two] using h
    _ = D ^ 2 * Sig ^ 2 := by ring
    _ ≤ D ^ 2 * ((n : ℝ) * ∑ m ∈ Finset.range n, (v m) ^ 2) :=
        mul_le_mul_of_nonneg_left hSigsq (sq_nonneg D)
    _ = D ^ 2 * n * ∑ m ∈ Finset.range n, (v m) ^ 2 := by ring

theorem near_pointwise_bound (k : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (u g : ℝ → ℝ),
      ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)) →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 8),
        (iteratedDeriv (k + 2) u θ) ^ 2
          ≤ K * ((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m u θ) ^ 2)
              + (iteratedDeriv k g θ) ^ 2) := by
  classical
  obtain ⟨M, hM1, hM⟩ := tan_deriv_bound_Icc (k + 1)
  set D : ℝ := ∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ) * M with hDdef
  have hDterm : ∀ i ∈ Finset.range (k + 2),
      0 ≤ ((k + 1).choose i : ℝ) * M :=
    fun i _ => mul_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one hM1)
  have hDnn : 0 ≤ D := by
    rw [hDdef]
    exact Finset.sum_nonneg hDterm
  have hDle : ∀ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ) * M ≤ D := by
    intro i hi
    rw [hDdef]
    exact Finset.single_le_sum hDterm hi
  set Kc : ℝ := max 1 (max (2 * (2 * (D ^ 2 * ((k + 2 : ℕ) : ℝ)) + 72)) 2) with hKdef
  refine ⟨Kc, ?_, ?_⟩
  · rw [hKdef]
    exact le_max_left _ _
  · intro u g hu hg θ hθ
    have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hθIcc : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 8) := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hcoef : ∀ i < k + 2,
        |((k + 1).choose i : ℝ) * iteratedDeriv i Real.tan θ| ≤ D := by
      intro i hi
      have hi' : i ≤ k + 1 := by omega
      have hMi : |iteratedDeriv i Real.tan θ| ≤ M := hM i hi' θ hθIcc
      have hc0 : (0 : ℝ) ≤ ((k + 1).choose i : ℝ) := Nat.cast_nonneg _
      rw [abs_mul, abs_of_nonneg hc0]
      exact le_trans (mul_le_mul_of_nonneg_left hMi hc0)
        (hDle i (Finset.mem_range.mpr hi))
    have hid := Lzero1_iteratedDeriv_eq k hu hg θ hθ'
    set S : ℝ := ∑ i ∈ Finset.range (k + 2),
        ((k + 1).choose i : ℝ) * iteratedDeriv i Real.tan θ
          * iteratedDeriv (k + 1 - i) u θ with hSdef
    set uk : ℝ := iteratedDeriv k u θ with hukdef
    set gk : ℝ := iteratedDeriv k g θ with hgkdef
    set Sig2 : ℝ := ∑ m ∈ Finset.range (k + 2), (iteratedDeriv m u θ) ^ 2 with hSig2def
    have hid' : iteratedDeriv (k + 2) u θ = S - 6 * uk - gk := by
      rw [hid, hSdef, hukdef, hgkdef]
    have hS : S ^ 2 ≤ D ^ 2 * ((k + 2 : ℕ) : ℝ) * Sig2 := by
      have hraw := sum_cs_reflect_bound (k + 2) D hDnn
        (fun i => ((k + 1).choose i : ℝ) * iteratedDeriv i Real.tan θ)
        (fun m => iteratedDeriv m u θ) hcoef
      rw [hSdef, hSig2def]
      exact hraw
    have hSig2nn : 0 ≤ Sig2 := by
      rw [hSig2def]
      exact Finset.sum_nonneg (fun m _ => sq_nonneg _)
    have huk_le : uk ^ 2 ≤ Sig2 := by
      rw [hukdef, hSig2def]
      exact Finset.single_le_sum (s := Finset.range (k + 2)) (a := k)
        (fun m _ => sq_nonneg (iteratedDeriv m u θ))
        (Finset.mem_range.mpr (by omega))
    rw [hid']
    have h2Q : 2 * (2 * (D ^ 2 * ((k + 2 : ℕ) : ℝ)) + 72) ≤ Kc := by
      rw [hKdef]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have h2 : (2 : ℝ) ≤ Kc := by
      rw [hKdef]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hstep1 : (S - 6 * uk) ^ 2 ≤ (2 * (D ^ 2 * ((k + 2 : ℕ) : ℝ)) + 72) * Sig2 := by
      have hA : 2 * S ^ 2 ≤ 2 * (D ^ 2 * ((k + 2 : ℕ) : ℝ) * Sig2) := by linarith [hS]
      have hB : 2 * (6 * uk) ^ 2 ≤ 72 * Sig2 := by nlinarith [huk_le]
      have hC : (S - 6 * uk) ^ 2 ≤ 2 * S ^ 2 + 2 * (6 * uk) ^ 2 := by
        nlinarith [sq_nonneg (S + 6 * uk)]
      linarith [hA, hB, hC]
    have hstep2 : (S - 6 * uk - gk) ^ 2 ≤ 2 * (S - 6 * uk) ^ 2 + 2 * gk ^ 2 := by
      nlinarith [sq_nonneg ((S - 6 * uk) + gk)]
    have hfin1 : 2 * (S - 6 * uk) ^ 2
        ≤ 2 * ((2 * (D ^ 2 * ((k + 2 : ℕ) : ℝ)) + 72) * Sig2) := by linarith [hstep1]
    have hfin2 : 2 * gk ^ 2 ≤ Kc * gk ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg gk)
    have hfin3 : 2 * ((2 * (D ^ 2 * ((k + 2 : ℕ) : ℝ)) + 72) * Sig2) ≤ Kc * Sig2 := by
      have h := mul_le_mul_of_nonneg_right h2Q hSig2nn
      linarith [h]
    have hexpand : Kc * (Sig2 + gk ^ 2) = Kc * Sig2 + Kc * gk ^ 2 := by ring
    rw [hexpand]
    linarith [hstep2, hfin1, hfin2, hfin3]

end Work.FTS.EllipticEst.remov
