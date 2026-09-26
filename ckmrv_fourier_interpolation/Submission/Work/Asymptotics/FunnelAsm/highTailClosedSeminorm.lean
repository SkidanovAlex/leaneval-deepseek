import Mathlib
import Submission.Work.Asymptotics.highPart_seminorm
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.FunnelAsm.aexpClosed
import Submission.Work.Asymptotics.compose_grow
import Submission.Work.Asymptotics.gaussian_deriv_bound
import Submission.Work.Asymptotics.poly_mul_gaussian_bounded
import Submission.Work.Asymptotics.psi1_contDiff
import Submission.Work.Asymptotics.psi1_iteratedDeriv_bound
import Submission.Work.RadialSpace.iteratedDeriv_ofReal

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology ContDiff

namespace Work.Asymptotics

open Work.Kernels

set_option maxHeartbeats 4000000

/-- Iterated derivatives of `x ↦ e^{-c x²}` for `c ≥ π`, with the sharp scaling `(c/π)^j` in `j`
and the Gaussian decay kept.  Obtained from `gaussian_deriv_bound` for `e^{-π x²}` by the change
of variable `x ↦ √(c/π) x`. -/
theorem expQuad_deriv_bound (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ), Real.pi ≤ c → ∀ r : ℝ,
      ‖iteratedDeriv l (fun x : ℝ => ((Real.exp (-(c * x ^ 2)) : ℝ) : ℂ)) r‖
        ≤ C * (c / Real.pi) ^ l * (1 + |r|) ^ l * Real.exp (-(c * r ^ 2)) := by
  obtain ⟨Cg, hCg0, hCg⟩ := gaussian_deriv_bound l
  refine ⟨Cg, hCg0, fun c hc r => ?_⟩
  have hcpos : 0 < c := lt_of_lt_of_le Real.pi_pos hc
  set s : ℝ := Real.sqrt (c / Real.pi) with hsdef
  have hs2 : s ^ 2 = c / Real.pi := Real.sq_sqrt (div_nonneg hcpos.le Real.pi_pos.le)
  have hs1 : 1 ≤ s := by
    rw [hsdef, Real.one_le_sqrt, le_div_iff₀ Real.pi_pos]
    linarith
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  set g : ℝ → ℝ := fun y => Real.exp (-(Real.pi * y ^ 2)) with hgdef
  have hg : ContDiff ℝ (↑l) g := by rw [hgdef]; fun_prop
  have hgc : (fun y : ℝ => ((g y : ℝ) : ℂ))
      = fun y : ℝ => ((Real.exp (-(Real.pi * y ^ 2)) : ℝ) : ℂ) := rfl
  have hstep1 : (fun x : ℝ => ((Real.exp (-(c * x ^ 2)) : ℝ) : ℂ))
      = fun x : ℝ => ((g (s * x) : ℝ) : ℂ) := by
    funext x
    simp only [hgdef]
    congr 2
    rw [mul_pow, hs2]
    field_simp
  rw [hstep1]
  have h2 : iteratedDeriv l (fun x : ℝ => ((g (s * x) : ℝ) : ℂ)) r
      = ((s ^ l * iteratedDeriv l g (s * r) : ℝ) : ℂ) := by
    rw [Work.RadialSpace.iteratedDeriv_ofReal l (fun x : ℝ => g (s * x)) r]
    rw [iteratedDeriv_comp_const_mul hg s]
  rw [h2]
  have hgn : ‖((iteratedDeriv l g (s * r) : ℝ) : ℂ)‖
      = ‖iteratedDeriv l (fun y : ℝ => ((Real.exp (-(Real.pi * y ^ 2)) : ℝ) : ℂ)) (s * r)‖ := by
    rw [← hgc, Work.RadialSpace.iteratedDeriv_ofReal l g (s * r)]
  have hgn' : |iteratedDeriv l g (s * r)|
      = ‖iteratedDeriv l (fun y : ℝ => ((Real.exp (-(Real.pi * y ^ 2)) : ℝ) : ℂ)) (s * r)‖ := by
    rw [← norm_ofReal_eq_abs]
    exact hgn
  rw [norm_ofReal_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hspos.le l), hgn']
  have h5 := hCg (s * r)
  have h6 : Real.exp (-(Real.pi * (s * r) ^ 2)) = Real.exp (-(c * r ^ 2)) := by
    congr 1
    rw [mul_pow, hs2]
    field_simp
  have h7 : (1 + |s * r|) ^ l ≤ s ^ l * (1 + |r|) ^ l := by
    have habs : |s * r| = s * |r| := by rw [abs_mul, abs_of_nonneg hspos.le]
    rw [habs, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [abs_nonneg r, hs1]) l
  calc s ^ l * ‖iteratedDeriv l (fun y : ℝ => ((Real.exp (-(Real.pi * y ^ 2)) : ℝ) : ℂ)) (s * r)‖
      ≤ s ^ l * (Cg * (1 + |s * r|) ^ l * Real.exp (-(Real.pi * (s * r) ^ 2))) :=
        mul_le_mul_of_nonneg_left h5 (pow_nonneg hspos.le l)
    _ ≤ s ^ l * (Cg * (s ^ l * (1 + |r|) ^ l) * Real.exp (-(c * r ^ 2))) := by
        rw [h6]
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hspos.le l)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h7 hCg0) (Real.exp_nonneg _)
    _ = Cg * (c / Real.pi) ^ l * (1 + |r|) ^ l * Real.exp (-(c * r ^ 2)) := by
        have hs2l : s ^ l * s ^ l = (c / Real.pi) ^ l := by
          rw [← pow_add, show l + l = 2 * l by ring, pow_mul, hs2]
        calc s ^ l * (Cg * (s ^ l * (1 + |r|) ^ l) * Real.exp (-(c * r ^ 2)))
            = Cg * (s ^ l * s ^ l) * (1 + |r|) ^ l * Real.exp (-(c * r ^ 2)) := by ring
          _ = Cg * (c / Real.pi) ^ l * (1 + |r|) ^ l * Real.exp (-(c * r ^ 2)) := by rw [hs2l]

/-- The same bound, uniformly in the order `j ≤ L`. -/
theorem expQuad_deriv_bound_all (L : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ), j ≤ L → ∀ (c : ℝ), Real.pi ≤ c → ∀ r : ℝ,
      ‖iteratedDeriv j (fun x : ℝ => ((Real.exp (-(c * x ^ 2)) : ℝ) : ℂ)) r‖
        ≤ C * (c / Real.pi) ^ j * (1 + |r|) ^ j * Real.exp (-(c * r ^ 2)) := by
  induction L with
  | zero =>
    obtain ⟨C, hC0, hC⟩ := expQuad_deriv_bound 0
    refine ⟨C, hC0, fun j hj => ?_⟩
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    rw [hj0]
    exact hC
  | succ L ih =>
    obtain ⟨C₁, hC₁0, hC₁⟩ := ih
    obtain ⟨C₂, hC₂0, hC₂⟩ := expQuad_deriv_bound (L + 1)
    refine ⟨max C₁ C₂, le_trans hC₁0 (le_max_left _ _), fun j hj c hc r => ?_⟩
    have hc0 : (0 : ℝ) ≤ (c / Real.pi) ^ j := by
      exact pow_nonneg (div_nonneg (le_trans Real.pi_pos.le hc) Real.pi_pos.le) j
    have h1r : (0 : ℝ) ≤ (1 + |r|) ^ j := by positivity
    rcases Nat.lt_or_eq_of_le hj with hlt | heq
    · have hjL : j ≤ L := Nat.lt_succ_iff.mp hlt
      have h := hC₁ j hjL c hc r
      calc ‖iteratedDeriv j (fun x : ℝ => ((Real.exp (-(c * x ^ 2)) : ℝ) : ℂ)) r‖
          ≤ C₁ * (c / Real.pi) ^ j * (1 + |r|) ^ j * Real.exp (-(c * r ^ 2)) := h
        _ ≤ max C₁ C₂ * (c / Real.pi) ^ j * (1 + |r|) ^ j
              * Real.exp (-(c * r ^ 2)) := by
            have hle : C₁ * (c / Real.pi) ^ j ≤ max C₁ C₂ * (c / Real.pi) ^ j :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hc0
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle h1r)
              (Real.exp_nonneg _)
    · rw [heq]
      have hc0' : (0 : ℝ) ≤ (c / Real.pi) ^ (L + 1) :=
        pow_nonneg (div_nonneg (le_trans Real.pi_pos.le hc) Real.pi_pos.le) (L + 1)
      have h1r' : (0 : ℝ) ≤ (1 + |r|) ^ (L + 1) := by positivity
      calc ‖iteratedDeriv (L + 1) (fun x : ℝ => ((Real.exp (-(c * x ^ 2)) : ℝ) : ℂ)) r‖
          ≤ C₂ * (c / Real.pi) ^ (L + 1) * (1 + |r|) ^ (L + 1)
              * Real.exp (-(c * r ^ 2)) := hC₂ c hc r
        _ ≤ max C₁ C₂ * (c / Real.pi) ^ (L + 1) * (1 + |r|) ^ (L + 1)
              * Real.exp (-(c * r ^ 2)) := by
            have hle : C₂ * (c / Real.pi) ^ (L + 1)
                ≤ max C₁ C₂ * (c / Real.pi) ^ (L + 1) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hc0'
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle h1r')
              (Real.exp_nonneg _)

/-- **Seminorm bound for one factor of the regularised tail.**  If `φ` is smooth with derivatives
growing at most like `(1+|x|)^m`, then `r ↦ φ (πr² - a) · e^{-(πr²-b)Y}` has `|r|^k`-weighted
`l`-th derivatives bounded by `C e^b Y^l` on the region `b ≤ πr²`, `Y ≥ 1`. -/
theorem seminorm_facY (φ : ℝ → ℂ) (a b : ℝ) (k l : ℕ) (A : ℝ) (m : ℕ)
    (hA : 0 ≤ A) (hφ : ContDiff ℝ ∞ φ)
    (h : ∀ j ≤ l + 1, ∀ x : ℝ, ‖iteratedDeriv j φ x‖ ≤ A * (1 + |x|) ^ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : ℝ), 1 ≤ Y → ∀ r : ℝ, b ≤ Real.pi * r ^ 2 →
      |r| ^ k * ‖iteratedDeriv l (fun r : ℝ =>
        φ (Real.pi * r ^ 2 - a) * ((Real.exp (-((Real.pi * r ^ 2 - b) * Y)) : ℝ) : ℂ)) r‖
        ≤ C * Real.exp b * Y ^ l := by
  obtain ⟨D, hD0, hD⟩ := compose_grow φ a l A m hA hφ h
  obtain ⟨Gc, hGc0, hGc⟩ := expQuad_deriv_bound_all l
  obtain ⟨C3, hC30, hC3⟩ := poly_mul_gaussian_bounded k (2 * m + 2 * l)
  refine ⟨(2 : ℝ) ^ l * D * Gc * C3, by positivity, fun Y hY r hb => ?_⟩
  set F : ℝ → ℂ := fun r => φ (Real.pi * r ^ 2 - a) with hFdef
  set E : ℝ → ℂ := fun r => ((Real.exp (-((Real.pi * r ^ 2 - b) * Y)) : ℝ) : ℂ) with hEdef
  have hFY : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hcpi : Real.pi ≤ Real.pi * Y := by nlinarith [Real.pi_pos]
  have hbase : (1 : ℝ) ≤ 1 + |r| := by have := abs_nonneg r; linarith
  have hexpnn : (0 : ℝ) ≤ Real.exp (-((Real.pi * r ^ 2 - b) * Y)) := Real.exp_nonneg _
  have hFb : ∀ j ≤ l, ∀ r : ℝ, ‖iteratedDeriv j F r‖ ≤ D * (1 + |r|) ^ (2 * m + l) := by
    intro j hj r
    rw [hFdef]
    exact hD j hj r
  have hEeq : E = fun r : ℝ => ((Real.exp (b * Y) : ℝ) : ℂ)
      * ((Real.exp (-((Real.pi * Y) * r ^ 2)) : ℝ) : ℂ) := by
    rw [hEdef]
    funext r
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have hEderiv : ∀ j : ℕ, ∀ r : ℝ, iteratedDeriv j E r
      = ((Real.exp (b * Y) : ℝ) : ℂ)
        * iteratedDeriv j (fun r : ℝ => ((Real.exp (-((Real.pi * Y) * r ^ 2)) : ℝ) : ℂ)) r := by
    intro j r
    rw [hEeq]
    refine iteratedDeriv_const_mul (((Real.exp (b * Y) : ℝ) : ℂ)) ?_
    have h1 : ContDiff ℝ (↑j) (fun r : ℝ => ((Real.exp (-((Real.pi * Y) * r ^ 2)) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp
        (Real.contDiff_exp.comp (by fun_prop : ContDiff ℝ (↑j) (fun x : ℝ => -((Real.pi * Y) * x ^ 2))))
    exact h1.contDiffAt
  have hEb : ∀ j ≤ l, ∀ r : ℝ,
      ‖iteratedDeriv j E r‖
        ≤ Gc * Y ^ j * (1 + |r|) ^ j * Real.exp (-((Real.pi * r ^ 2 - b) * Y)) := by
    intro j hj r
    rw [hEderiv]
    have hnormexp : ‖((Real.exp (b * Y) : ℝ) : ℂ)‖ = Real.exp (b * Y) := by
      rw [norm_ofReal_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [norm_mul, hnormexp]
    have hdiv : (Real.pi * Y) / Real.pi = Y := by field_simp
    have hglue := hGc j hj (Real.pi * Y) hcpi r
    rw [hdiv] at hglue
    have hsame : Real.exp (b * Y) * Real.exp (-((Real.pi * Y) * r ^ 2))
        = Real.exp (-((Real.pi * r ^ 2 - b) * Y)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc Real.exp (b * Y)
          * ‖iteratedDeriv j (fun r : ℝ => ((Real.exp (-((Real.pi * Y) * r ^ 2)) : ℝ) : ℂ)) r‖
        ≤ Real.exp (b * Y) * (Gc * Y ^ j * (1 + |r|) ^ j
            * Real.exp (-((Real.pi * Y) * r ^ 2))) :=
          mul_le_mul_of_nonneg_left hglue (Real.exp_pos _).le
      _ = Gc * Y ^ j * (1 + |r|) ^ j * Real.exp (-((Real.pi * r ^ 2 - b) * Y)) := by
          rw [← hsame]; ring
  have hFsmo : ContDiffAt ℝ (↑l) F r := by
    rw [hFdef]
    have h1 : ContDiff ℝ (↑l) (fun r : ℝ => Real.pi * r ^ 2 - a) := by fun_prop
    exact ((hφ.of_le (WithTop.coe_le_coe.mpr le_top)).comp h1).contDiffAt
  have hEsmo : ContDiffAt ℝ (↑l) E r := by
    rw [hEdef]
    have h1 : ContDiff ℝ (↑l) (fun r : ℝ => -((Real.pi * r ^ 2 - b) * Y)) := by fun_prop
    exact (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp h1)).contDiffAt
  have hprod : ‖iteratedDeriv l (F * E) r‖
      ≤ (2 : ℝ) ^ l * (D * Gc * Y ^ l * (1 + |r|) ^ (2 * m + 2 * l)
          * Real.exp (-((Real.pi * r ^ 2 - b) * Y))) := by
    rw [iteratedDeriv_mul hFsmo hEsmo]
    have hterm : ∀ i ∈ Finset.range (l + 1),
        ‖((l.choose i : ℕ) : ℂ) * iteratedDeriv i F r * iteratedDeriv (l - i) E r‖
          ≤ (l.choose i : ℝ) * (D * Gc * Y ^ l * (1 + |r|) ^ (2 * m + 2 * l)
              * Real.exp (-((Real.pi * r ^ 2 - b) * Y))) := by
      intro i hi
      have hi' : i ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hli : l - i ≤ l := Nat.sub_le _ _
      have h1 : ‖iteratedDeriv i F r‖ ≤ D * (1 + |r|) ^ (2 * m + l) := hFb i hi' r
      have h2 : ‖iteratedDeriv (l - i) E r‖
          ≤ Gc * Y ^ (l - i) * (1 + |r|) ^ (l - i)
              * Real.exp (-((Real.pi * r ^ 2 - b) * Y)) := hEb (l - i) hli r
      have hchoose : ‖(((l.choose i : ℕ)) : ℂ)‖ = (l.choose i : ℝ) := by simp
      rw [norm_mul, norm_mul, hchoose]
      have hYl : Y ^ (l - i) ≤ Y ^ l := pow_le_pow_right₀ hY hli
      have hX : (1 + |r|) ^ (2 * m + l) * (1 + |r|) ^ (l - i)
          ≤ (1 + |r|) ^ (2 * m + 2 * l) := by
        rw [← pow_add]
        exact pow_le_pow_right₀ hbase (by omega)
      have hstep1 : (l.choose i : ℝ) * ‖iteratedDeriv i F r‖ * ‖iteratedDeriv (l - i) E r‖
          ≤ (l.choose i : ℝ) * (D * (1 + |r|) ^ (2 * m + l))
              * (Gc * Y ^ (l - i) * (1 + |r|) ^ (l - i)
                * Real.exp (-((Real.pi * r ^ 2 - b) * Y))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
          (norm_nonneg _) (by positivity)
      have hstep2 : (l.choose i : ℝ) * (D * (1 + |r|) ^ (2 * m + l))
              * (Gc * Y ^ (l - i) * (1 + |r|) ^ (l - i)
                * Real.exp (-((Real.pi * r ^ 2 - b) * Y)))
          = ((l.choose i : ℝ) * D * Gc * Y ^ (l - i))
              * ((1 + |r|) ^ (2 * m + l) * (1 + |r|) ^ (l - i))
              * Real.exp (-((Real.pi * r ^ 2 - b) * Y)) := by ring
      have hstep3 : ((l.choose i : ℝ) * D * Gc * Y ^ (l - i))
              * ((1 + |r|) ^ (2 * m + l) * (1 + |r|) ^ (l - i))
              * Real.exp (-((Real.pi * r ^ 2 - b) * Y))
          ≤ (l.choose i : ℝ) * (D * Gc * Y ^ l * (1 + |r|) ^ (2 * m + 2 * l)
              * Real.exp (-((Real.pi * r ^ 2 - b) * Y))) := by
        calc ((l.choose i : ℝ) * D * Gc * Y ^ (l - i))
                * ((1 + |r|) ^ (2 * m + l) * (1 + |r|) ^ (l - i))
                * Real.exp (-((Real.pi * r ^ 2 - b) * Y))
            = ((l.choose i : ℝ) * D * Gc) * (Y ^ (l - i)
                * ((1 + |r|) ^ (2 * m + l) * (1 + |r|) ^ (l - i)))
                * Real.exp (-((Real.pi * r ^ 2 - b) * Y)) := by ring
          _ ≤ ((l.choose i : ℝ) * D * Gc) * (Y ^ l * (1 + |r|) ^ (2 * m + 2 * l))
                * Real.exp (-((Real.pi * r ^ 2 - b) * Y)) := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
                hexpnn
              exact mul_le_mul hYl hX (by positivity) (by positivity)
          _ = (l.choose i : ℝ) * (D * Gc * Y ^ l * (1 + |r|) ^ (2 * m + 2 * l)
                * Real.exp (-((Real.pi * r ^ 2 - b) * Y))) := by ring
      exact le_trans hstep1 (le_trans (le_of_eq hstep2) hstep3)
    calc ‖∑ i ∈ Finset.range (l + 1), ((l.choose i : ℕ) : ℂ) * iteratedDeriv i F r
            * iteratedDeriv (l - i) E r‖
        ≤ ∑ i ∈ Finset.range (l + 1), ‖((l.choose i : ℕ) : ℂ) * iteratedDeriv i F r
            * iteratedDeriv (l - i) E r‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * (D * Gc * Y ^ l
            * (1 + |r|) ^ (2 * m + 2 * l) * Real.exp (-((Real.pi * r ^ 2 - b) * Y))) :=
          Finset.sum_le_sum hterm
      _ = (∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ)) * (D * Gc * Y ^ l
            * (1 + |r|) ^ (2 * m + 2 * l) * Real.exp (-((Real.pi * r ^ 2 - b) * Y))) := by
          rw [Finset.sum_mul]
      _ = (2 : ℝ) ^ l * (D * Gc * Y ^ l * (1 + |r|) ^ (2 * m + 2 * l)
            * Real.exp (-((Real.pi * r ^ 2 - b) * Y))) := by
          have h2l : (∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ)) = (2 : ℝ) ^ l := by
            rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
          rw [h2l]
  have hfinal : |r| ^ k * (1 + |r|) ^ (2 * m + 2 * l)
      * Real.exp (-((Real.pi * r ^ 2 - b) * Y)) ≤ Real.exp b * C3 := by
    have hb0 : 0 ≤ Real.pi * r ^ 2 - b := by linarith
    have hexp : Real.exp (-((Real.pi * r ^ 2 - b) * Y)) ≤ Real.exp (-((Real.pi * r ^ 2 - b))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hb0, hY]
    have hsplit : Real.exp (-((Real.pi * r ^ 2 - b))) = Real.exp b * Real.exp (-(Real.pi * r ^ 2)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit] at hexp
    calc |r| ^ k * (1 + |r|) ^ (2 * m + 2 * l) * Real.exp (-((Real.pi * r ^ 2 - b) * Y))
        ≤ |r| ^ k * (1 + |r|) ^ (2 * m + 2 * l) * (Real.exp b * Real.exp (-(Real.pi * r ^ 2))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Real.exp b * (|r| ^ k * (1 + |r|) ^ (2 * m + 2 * l) * Real.exp (-(Real.pi * r ^ 2))) := by
          ring
      _ ≤ Real.exp b * C3 := mul_le_mul_of_nonneg_left (hC3 r) (Real.exp_pos b).le
  have hgoal : (fun r : ℝ => φ (Real.pi * r ^ 2 - a)
      * ((Real.exp (-((Real.pi * r ^ 2 - b) * Y)) : ℝ) : ℂ)) = F * E := by
    funext s
    rw [Pi.mul_apply, hFdef, hEdef]
  rw [hgoal]
  have hYnonneg : (0 : ℝ) ≤ Y ^ l := by positivity
  calc |r| ^ k * ‖iteratedDeriv l (F * E) r‖
      ≤ |r| ^ k * ((2 : ℝ) ^ l * (D * Gc * Y ^ l * (1 + |r|) ^ (2 * m + 2 * l)
          * Real.exp (-((Real.pi * r ^ 2 - b) * Y)))) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (2 : ℝ) ^ l * D * Gc * (|r| ^ k * (1 + |r|) ^ (2 * m + 2 * l)
          * Real.exp (-((Real.pi * r ^ 2 - b) * Y))) * Y ^ l := by ring
    _ ≤ (2 : ℝ) ^ l * D * Gc * (Real.exp b * C3) * Y ^ l := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfinal (by positivity)) hYnonneg
    _ = (2 : ℝ) ^ l * D * Gc * C3 * Real.exp b * Y ^ l := by ring

/-- **The `r`-seminorm bound of `highTailClosed` on the funnel**, under the region condition
`d = 8 ∨ 2 ≤ r²`. -/
theorem highTailClosedSeminorm (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (k l : ℕ) :
    ∃ c N : ℝ, 0 ≤ c ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), Funnel τ →
      (d = 8 ∨ 2 ≤ r ^ 2) →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => highTailClosed ℓ d τ s) r‖
        ≤ c * (scale τ) ^ N := by
  obtain ⟨A₀, hA₀0, hA₀⟩ := highAmp0_grow (l + 1)
  have hpsi : ∀ j ≤ l + 1, ∀ x : ℝ,
      ‖iteratedDeriv j (fun x : ℝ => ((psi1 x : ℝ) : ℂ)) x‖ ≤ 2 * (1 + |x|) ^ (0 : ℕ) := by
    intro j _ x
    have h := psi1_iteratedDeriv_bound j x
    rw [show psiC = (fun x : ℝ => ((psi1 x : ℝ) : ℂ)) from rfl] at h
    simpa using h
  have hpsiCD : ContDiff ℝ ∞ (fun x : ℝ => ((psi1 x : ℝ) : ℂ)) := psi1_contDiff
  obtain ⟨C00, hC000, hC00⟩ := seminorm_facY highAmp0 0 0 k l A₀ 1 hA₀0 highAmp0_contDiff hA₀
  obtain ⟨C01, hC010, hC01⟩ := seminorm_facY (fun x : ℝ => ((psi1 x : ℝ) : ℂ)) 0 0 k l 2 0
    (by norm_num) hpsiCD hpsi
  obtain ⟨C10, hC100, hC10⟩ := seminorm_facY highAmp0 (2 * Real.pi) (2 * Real.pi) k l A₀ 1
    hA₀0 highAmp0_contDiff hA₀
  obtain ⟨C11, hC110, hC11⟩ := seminorm_facY (fun x : ℝ => ((psi1 x : ℝ) : ℂ))
    (2 * Real.pi) (2 * Real.pi) k l 2 0 (by norm_num) hpsiCD hpsi
  obtain ⟨α00, N00, hα00, hN00, hb00⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale DomainD (Gcusp ℓ d 0 0)).mp (GcuspInP ℓ d 0 0)
  obtain ⟨α01, N01, hα01, hN01, hb01⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale DomainD (Gcusp ℓ d 0 1)).mp (GcuspInP ℓ d 0 1)
  obtain ⟨α10, N10, hα10, hN10, hb10⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale DomainD (Gcusp ℓ d 1 0)).mp (GcuspInP ℓ d 1 0)
  obtain ⟨α11, N11, hα11, hN11, hb11⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale DomainD (Gcusp ℓ d 1 1)).mp (GcuspInP ℓ d 1 1)
  set K : ℝ := max (max (max α00 α01) (max α10 α11)) 1 with hKdef
  set Nc : ℝ := max (max (max N00 N01) (max N10 N11)) 0 with hNcdef
  set Cm : ℝ := max (max C00 C01) (max C10 C11) with hCmdef
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  have hK00 : α00 ≤ K :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hK01 : α01 ≤ K :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hK10 : α10 ≤ K :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hK11 : α11 ≤ K :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hN00 : N00 ≤ Nc :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hN01 : N01 ≤ Nc :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hN10 : N10 ≤ Nc :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hN11 : N11 ≤ Nc :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hCm0 : 0 ≤ Cm := le_trans hC000 (le_trans (le_max_left _ _) (le_max_left _ _))
  have hCm00 : C00 ≤ Cm := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCm01 : C01 ≤ Cm := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCm10 : C10 ≤ Cm := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCm11 : C11 ≤ Cm := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨20 * K * Cm * Real.exp (2 * Real.pi), Nc + 1 + l, by positivity, by positivity, ?_⟩
  intro τ r hτ hreg
  obtain ⟨hτD, hτ2⟩ := hτ
  set Y : ℝ := τ.im + 1 with hYdef
  have hY1 : 1 ≤ Y := by rw [hYdef]; linarith
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
  have hscale1 : 1 ≤ scale τ := Work.Kernels.one_le_scale τ
  have hscalepos : 0 < scale τ := Work.Kernels.scale_pos τ
  have hYscale : Y ≤ scale τ := by
    rw [hYdef, Work.Kernels.scale]
    have h1 : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr τ.im_pos.le
    have h2 : τ.im ≤ ‖(τ : ℂ)‖ := by
      have h := Complex.abs_im_le_norm (τ : ℂ)
      rwa [UpperHalfPlane.coe_im, abs_of_pos τ.im_pos] at h
    linarith
  have hb00' : ‖Gcusp ℓ d 0 0 τ‖ ≤ K * (scale τ) ^ Nc := by
    refine le_trans (hb00 τ hτD) ?_
    exact mul_le_mul hK00 (Real.rpow_le_rpow_of_exponent_le hscale1 hN00)
      (Real.rpow_nonneg hscalepos.le _) (le_trans hα00 hK00)
  have hb01' : ‖Gcusp ℓ d 0 1 τ‖ ≤ K * (scale τ) ^ Nc := by
    refine le_trans (hb01 τ hτD) ?_
    exact mul_le_mul hK01 (Real.rpow_le_rpow_of_exponent_le hscale1 hN01)
      (Real.rpow_nonneg hscalepos.le _) (le_trans hα01 hK01)
  have hb10' : ‖Gcusp ℓ d 1 0 τ‖ ≤ K * (scale τ) ^ Nc := by
    refine le_trans (hb10 τ hτD) ?_
    exact mul_le_mul hK10 (Real.rpow_le_rpow_of_exponent_le hscale1 hN10)
      (Real.rpow_nonneg hscalepos.le _) (le_trans hα10 hK10)
  have hb11' : ‖Gcusp ℓ d 1 1 τ‖ ≤ K * (scale τ) ^ Nc := by
    refine le_trans (hb11 τ hτD) ?_
    exact mul_le_mul hK11 (Real.rpow_le_rpow_of_exponent_le hscale1 hN11)
      (Real.rpow_nonneg hscalepos.le _) (le_trans hα11 hK11)
  have hscaleNc_le : (scale τ) ^ Nc ≤ (scale τ) ^ (Nc + 1) :=
    Real.rpow_le_rpow_of_exponent_le hscale1 (by linarith)
  have hfactor : K * (scale τ) ^ Nc ≤ 2 * K * (scale τ) ^ (Nc + 1) := by
    have h1 : K * (scale τ) ^ Nc ≤ K * (scale τ) ^ (Nc + 1) :=
      mul_le_mul_of_nonneg_left hscaleNc_le hK0
    have h2 : (0 : ℝ) ≤ K * (scale τ) ^ (Nc + 1) :=
      mul_nonneg hK0 (Real.rpow_nonneg hscalepos.le _)
    linarith
  have hYfactor : K * (scale τ) ^ Nc * Y ≤ 2 * K * (scale τ) ^ (Nc + 1) := by
    have h1 : K * (scale τ) ^ Nc * Y ≤ K * (scale τ) ^ Nc * scale τ :=
      mul_le_mul_of_nonneg_left hYscale (mul_nonneg hK0 (Real.rpow_nonneg hscalepos.le _))
    have h2 : K * (scale τ) ^ Nc * scale τ = K * (scale τ) ^ (Nc + 1) := by
      rw [Real.rpow_add hscalepos, Real.rpow_one]; ring
    rw [h2] at h1
    have h3 : (0 : ℝ) ≤ K * (scale τ) ^ (Nc + 1) :=
      mul_nonneg hK0 (Real.rpow_nonneg hscalepos.le _)
    linarith
  set EY0 : ℝ → ℂ := fun r => ((Real.exp (-((Real.pi * r ^ 2 - 0) * Y)) : ℝ) : ℂ) with hEY0def
  set EY1 : ℝ → ℂ := fun r => ((Real.exp (-((Real.pi * r ^ 2 - 2 * Real.pi) * Y)) : ℝ) : ℂ)
    with hEY1def
  set q0 : ℝ → ℂ := fun r => ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((psi1 (Real.pi * r ^ 2) : ℝ) : ℂ)
    * EY0 r * Gcusp ℓ d 0 0 τ with hq0def
  set q1 : ℝ → ℂ := fun r => Complex.I * ((psi1 (Real.pi * r ^ 2) : ℝ) : ℂ) * EY0 r
    * Gcusp ℓ d 0 1 τ with hq1def
  set q2 : ℝ → ℂ := fun r => Complex.I * ((psi1 (Real.pi * r ^ 2) : ℝ) : ℂ)
    * (((Real.pi * r ^ 2 : ℝ) : ℂ) * (Y : ℂ)) * EY0 r * Gcusp ℓ d 0 1 τ with hq2def
  set q3 : ℝ → ℂ := fun r => ((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)
    * ((psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℝ) : ℂ) * EY1 r * Gcusp ℓ d 1 0 τ with hq3def
  set q4 : ℝ → ℂ := fun r => Complex.I * ((psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℝ) : ℂ)
    * EY1 r * Gcusp ℓ d 1 1 τ with hq4def
  set q5 : ℝ → ℂ := fun r => Complex.I * ((psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℝ) : ℂ)
    * (((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ) * (Y : ℂ)) * EY1 r * Gcusp ℓ d 1 1 τ
    with hq5def
  have hdecomp : (fun s : ℝ => highTailClosed ℓ d τ s) = q0 + q1 + q2 + q3 + q4 + q5 := by
    funext s
    simp only [highTailClosed, hYdef, hEY0def, hEY1def, hq0def, hq1def, hq2def, hq3def, hq4def,
      hq5def, Pi.add_apply]
    rw [show (-(((Real.pi * s ^ 2 : ℝ) : ℂ) * ((τ.im + 1 : ℝ) : ℂ)))
          = ((-((Real.pi * s ^ 2 - 0) * (τ.im + 1)) : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_exp]
    rw [show (-(((Real.pi * s ^ 2 - 2 * Real.pi : ℝ) : ℂ) * ((τ.im + 1 : ℝ) : ℂ)))
          = ((-((Real.pi * s ^ 2 - 2 * Real.pi) * (τ.im + 1)) : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_exp]
    ring
  have hA0' : (fun r : ℝ => highAmp0 (Real.pi * r ^ 2 - 0)
      * ((Real.exp (-((Real.pi * r ^ 2 - 0) * Y)) : ℝ) : ℂ))
      = fun r : ℝ => highAmp0 (Real.pi * r ^ 2)
        * ((Real.exp (-(Real.pi * r ^ 2 * Y)) : ℝ) : ℂ) := by
    funext x
    simp only [sub_zero]
  have hq0set : q0 = fun r : ℝ => Gcusp ℓ d 0 0 τ * (highAmp0 (Real.pi * r ^ 2 - 0)
      * ((Real.exp (-((Real.pi * r ^ 2 - 0) * Y)) : ℝ) : ℂ)) := by
    rw [hq0def, hEY0def]
    funext x
    simp only [highAmp0, sub_zero, Complex.ofReal_mul]
    ring
  have hq1set : q1 = fun r : ℝ => (Complex.I * Gcusp ℓ d 0 1 τ)
      * (((psi1 (Real.pi * r ^ 2 - 0) : ℝ) : ℂ)
        * ((Real.exp (-((Real.pi * r ^ 2 - 0) * Y)) : ℝ) : ℂ)) := by
    rw [hq1def, hEY0def]
    funext x
    simp only [sub_zero]
    ring
  have hq2set : q2 = fun r : ℝ => ((Complex.I * Gcusp ℓ d 0 1 τ) * (Y : ℂ))
      * (highAmp0 (Real.pi * r ^ 2 - 0)
        * ((Real.exp (-((Real.pi * r ^ 2 - 0) * Y)) : ℝ) : ℂ)) := by
    rw [hq2def, hEY0def]
    funext x
    simp only [highAmp0, sub_zero]
    push_cast
    ring
  have hq3set : q3 = fun r : ℝ => Gcusp ℓ d 1 0 τ * (highAmp0 (Real.pi * r ^ 2 - 2 * Real.pi)
      * ((Real.exp (-((Real.pi * r ^ 2 - 2 * Real.pi) * Y)) : ℝ) : ℂ)) := by
    rw [hq3def, hEY1def]
    funext x
    simp only [highAmp0]
    push_cast
    ring
  have hq4set : q4 = fun r : ℝ => (Complex.I * Gcusp ℓ d 1 1 τ)
      * (((psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℝ) : ℂ)
        * ((Real.exp (-((Real.pi * r ^ 2 - 2 * Real.pi) * Y)) : ℝ) : ℂ)) := by
    rw [hq4def, hEY1def]
    funext x
    ring
  have hq5set : q5 = fun r : ℝ => ((Complex.I * Gcusp ℓ d 1 1 τ) * (Y : ℂ))
      * (highAmp0 (Real.pi * r ^ 2 - 2 * Real.pi)
        * ((Real.exp (-((Real.pi * r ^ 2 - 2 * Real.pi) * Y)) : ℝ) : ℂ)) := by
    rw [hq5def, hEY1def]
    funext x
    simp only [highAmp0]
    push_cast
    ring
  have hcdPair : ∀ (ψ : ℝ → ℂ) (a b : ℝ), ContDiff ℝ ∞ ψ →
      ContDiff ℝ (↑l) (fun r : ℝ => ψ (Real.pi * r ^ 2 - a)
        * ((Real.exp (-((Real.pi * r ^ 2 - b) * Y)) : ℝ) : ℂ)) := by
    intro ψ a b hψ
    have h1 : ContDiff ℝ (↑l) (fun r : ℝ => ψ (Real.pi * r ^ 2 - a)) :=
      (hψ.of_le (WithTop.coe_le_coe.mpr le_top)).comp
        (by fun_prop : ContDiff ℝ (↑l) (fun r : ℝ => Real.pi * r ^ 2 - a))
    have h2 : ContDiff ℝ (↑l)
        (fun r : ℝ => ((Real.exp (-((Real.pi * r ^ 2 - b) * Y)) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (by fun_prop))
    exact h1.mul h2
  have hA0cd : ContDiff ℝ (↑l) (fun r : ℝ => highAmp0 (Real.pi * r ^ 2 - 0)
      * ((Real.exp (-((Real.pi * r ^ 2 - 0) * Y)) : ℝ) : ℂ)) :=
    hcdPair highAmp0 0 0 highAmp0_contDiff
  have hS0cd : ContDiff ℝ (↑l) (fun r : ℝ => ((psi1 (Real.pi * r ^ 2 - 0) : ℝ) : ℂ)
      * ((Real.exp (-((Real.pi * r ^ 2 - 0) * Y)) : ℝ) : ℂ)) :=
    hcdPair (fun x : ℝ => ((psi1 x : ℝ) : ℂ)) 0 0 hpsiCD
  have hA1cd : ContDiff ℝ (↑l) (fun r : ℝ => highAmp0 (Real.pi * r ^ 2 - 2 * Real.pi)
      * ((Real.exp (-((Real.pi * r ^ 2 - 2 * Real.pi) * Y)) : ℝ) : ℂ)) :=
    hcdPair highAmp0 (2 * Real.pi) (2 * Real.pi) highAmp0_contDiff
  have hS1cd : ContDiff ℝ (↑l) (fun r : ℝ => ((psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℝ) : ℂ)
      * ((Real.exp (-((Real.pi * r ^ 2 - 2 * Real.pi) * Y)) : ℝ) : ℂ)) :=
    hcdPair (fun x : ℝ => ((psi1 x : ℝ) : ℂ)) (2 * Real.pi) (2 * Real.pi) hpsiCD
  set B : ℝ := Cm * Real.exp (2 * Real.pi) * Y ^ l with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hYl0 : (0 : ℝ) ≤ Y ^ l := by positivity
  have keyC : ∀ Cx : ℝ, Cx ≤ Cm →
      |r| ^ k * ‖iteratedDeriv l (fun r : ℝ => highAmp0 (Real.pi * r ^ 2 - 0)
        * ((Real.exp (-((Real.pi * r ^ 2 - 0) * Y)) : ℝ) : ℂ)) r‖ ≤ B → Cx ≤ Cm :=
    fun _ h hb => h
  have hAm0 : |r| ^ k * ‖iteratedDeriv l (fun r : ℝ => highAmp0 (Real.pi * r ^ 2 - 0)
      * ((Real.exp (-((Real.pi * r ^ 2 - 0) * Y)) : ℝ) : ℂ)) r‖ ≤ B := by
    have hb := hC00 Y hY1 r (by positivity : (0:ℝ) ≤ Real.pi * r ^ 2)
    rw [hBdef]
    calc |r| ^ k * ‖iteratedDeriv l (fun r : ℝ => highAmp0 (Real.pi * r ^ 2 - 0)
          * ((Real.exp (-((Real.pi * r ^ 2 - 0) * Y)) : ℝ) : ℂ)) r‖
        ≤ C00 * Real.exp 0 * Y ^ l := hb
      _ = C00 * Y ^ l := by rw [Real.exp_zero, mul_one]
      _ ≤ Cm * Y ^ l := mul_le_mul_of_nonneg_right hCm00 hYl0
      _ ≤ Cm * (Real.exp (2 * Real.pi) * Y ^ l) :=
          mul_le_mul_of_nonneg_left
            (le_mul_of_one_le_left hYl0 (Real.one_le_exp (by positivity))) hCm0
      _ = Cm * Real.exp (2 * Real.pi) * Y ^ l := by ring
  have hSm0 : |r| ^ k * ‖iteratedDeriv l (fun r : ℝ => ((psi1 (Real.pi * r ^ 2 - 0) : ℝ) : ℂ)
      * ((Real.exp (-((Real.pi * r ^ 2 - 0) * Y)) : ℝ) : ℂ)) r‖ ≤ B := by
    have hb := hC01 Y hY1 r (by positivity : (0:ℝ) ≤ Real.pi * r ^ 2)
    rw [hBdef]
    calc |r| ^ k * ‖iteratedDeriv l (fun r : ℝ => ((psi1 (Real.pi * r ^ 2 - 0) : ℝ) : ℂ)
          * ((Real.exp (-((Real.pi * r ^ 2 - 0) * Y)) : ℝ) : ℂ)) r‖
        ≤ C01 * Real.exp 0 * Y ^ l := hb
      _ = C01 * Y ^ l := by rw [Real.exp_zero, mul_one]
      _ ≤ Cm * Y ^ l := mul_le_mul_of_nonneg_right hCm01 hYl0
      _ ≤ Cm * (Real.exp (2 * Real.pi) * Y ^ l) :=
          mul_le_mul_of_nonneg_left
            (le_mul_of_one_le_left hYl0 (Real.one_le_exp (by positivity))) hCm0
      _ = Cm * Real.exp (2 * Real.pi) * Y ^ l := by ring
  have hAm1 : 2 ≤ r ^ 2 → |r| ^ k * ‖iteratedDeriv l (fun r : ℝ =>
      highAmp0 (Real.pi * r ^ 2 - 2 * Real.pi)
      * ((Real.exp (-((Real.pi * r ^ 2 - 2 * Real.pi) * Y)) : ℝ) : ℂ)) r‖ ≤ B := by
    intro h2
    have hb := hC10 Y hY1 r (by have hp := Real.pi_pos; nlinarith)
    rw [hBdef]
    calc |r| ^ k * ‖iteratedDeriv l (fun r : ℝ => highAmp0 (Real.pi * r ^ 2 - 2 * Real.pi)
          * ((Real.exp (-((Real.pi * r ^ 2 - 2 * Real.pi) * Y)) : ℝ) : ℂ)) r‖
        ≤ C10 * Real.exp (2 * Real.pi) * Y ^ l := hb
      _ ≤ Cm * Real.exp (2 * Real.pi) * Y ^ l :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCm10 (Real.exp_pos _).le) hYl0
  have hSm1 : 2 ≤ r ^ 2 → |r| ^ k * ‖iteratedDeriv l (fun r : ℝ =>
      ((psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℝ) : ℂ)
      * ((Real.exp (-((Real.pi * r ^ 2 - 2 * Real.pi) * Y)) : ℝ) : ℂ)) r‖ ≤ B := by
    intro h2
    have hb := hC11 Y hY1 r (by have hp := Real.pi_pos; nlinarith)
    rw [hBdef]
    calc |r| ^ k * ‖iteratedDeriv l (fun r : ℝ =>
          ((psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℝ) : ℂ)
          * ((Real.exp (-((Real.pi * r ^ 2 - 2 * Real.pi) * Y)) : ℝ) : ℂ)) r‖
        ≤ C11 * Real.exp (2 * Real.pi) * Y ^ l := hb
      _ ≤ Cm * Real.exp (2 * Real.pi) * Y ^ l :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCm11 (Real.exp_pos _).le) hYl0
  have h8of : ¬ (2 ≤ r ^ 2) → d = 8 := by
    intro h2
    rcases hd with h24 | h24
    · exact h24
    · rw [h24] at hreg
      rcases hreg with hh | hh
      · exact h24.trans hh
      · exact absurd hh h2
  have hpiece : ∀ (c : ℂ) (f : ℝ → ℂ), ContDiff ℝ (↑l) f →
      |r| ^ k * ‖iteratedDeriv l f r‖ ≤ B → ‖c‖ ≤ 2 * K * (scale τ) ^ (Nc + 1) →
      |r| ^ k * ‖iteratedDeriv l (fun r : ℝ => c * f r) r‖
        ≤ (2 * K * (scale τ) ^ (Nc + 1)) * B := by
    intro c f hf hbd hc
    rw [iteratedDeriv_const_mul c hf.contDiffAt, norm_mul]
    have hgoal : |r| ^ k * (‖c‖ * ‖iteratedDeriv l f r‖)
        = ‖c‖ * (|r| ^ k * ‖iteratedDeriv l f r‖) := by ring
    rw [hgoal]
    calc ‖c‖ * (|r| ^ k * ‖iteratedDeriv l f r‖) ≤ ‖c‖ * B :=
          mul_le_mul_of_nonneg_left hbd (norm_nonneg _)
      _ ≤ (2 * K * (scale τ) ^ (Nc + 1)) * B := mul_le_mul_of_nonneg_right hc hB0
  have hq0b : |r| ^ k * ‖iteratedDeriv l q0 r‖ ≤ (2 * K * (scale τ) ^ (Nc + 1)) * B := by
    rw [hq0set]
    exact hpiece _ _ hA0cd hAm0 (le_trans hb00' hfactor)
  have hq1b : |r| ^ k * ‖iteratedDeriv l q1 r‖ ≤ (2 * K * (scale τ) ^ (Nc + 1)) * B := by
    rw [hq1set]
    refine hpiece _ _ hS0cd hSm0 ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    exact le_trans hb01' hfactor
  have hq2b : |r| ^ k * ‖iteratedDeriv l q2 r‖ ≤ (2 * K * (scale τ) ^ (Nc + 1)) * B := by
    rw [hq2set]
    refine hpiece _ _ hA0cd hAm0 ?_
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, norm_ofReal_eq_abs, abs_of_pos hYpos]
    exact le_trans (mul_le_mul_of_nonneg_right hb01' hYpos.le) hYfactor
  have hq3b : |r| ^ k * ‖iteratedDeriv l q3 r‖ ≤ (2 * K * (scale τ) ^ (Nc + 1)) * B := by
    by_cases h2 : 2 ≤ r ^ 2
    · rw [hq3set]
      exact hpiece _ _ hA1cd (hAm1 h2) (le_trans hb10' hfactor)
    · have hcz : Gcusp ℓ d 1 0 τ = 0 := FunnelAsm.gcusp_one_zero ℓ (h8of h2) 0 τ
      rw [hq3set, hcz, iteratedDeriv_const_mul (0 : ℂ) hA1cd.contDiffAt, norm_mul]
      simp only [norm_zero, zero_mul, mul_zero]
      exact mul_nonneg (by positivity) hB0
  have hq4b : |r| ^ k * ‖iteratedDeriv l q4 r‖ ≤ (2 * K * (scale τ) ^ (Nc + 1)) * B := by
    by_cases h2 : 2 ≤ r ^ 2
    · rw [hq4set]
      refine hpiece _ _ hS1cd (hSm1 h2) ?_
      rw [norm_mul, Complex.norm_I, one_mul]
      exact le_trans hb11' hfactor
    · have hcz : Complex.I * Gcusp ℓ d 1 1 τ = 0 := by
        rw [FunnelAsm.gcusp_one_zero ℓ (h8of h2) 1 τ, mul_zero]
      rw [hq4set, hcz, iteratedDeriv_const_mul (0 : ℂ) hS1cd.contDiffAt, norm_mul]
      simp only [norm_zero, zero_mul, mul_zero]
      exact mul_nonneg (by positivity) hB0
  have hq5b : |r| ^ k * ‖iteratedDeriv l q5 r‖ ≤ (2 * K * (scale τ) ^ (Nc + 1)) * B := by
    by_cases h2 : 2 ≤ r ^ 2
    · rw [hq5set]
      refine hpiece _ _ hA1cd (hAm1 h2) ?_
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, norm_ofReal_eq_abs, abs_of_pos hYpos]
      exact le_trans (mul_le_mul_of_nonneg_right hb11' hYpos.le) hYfactor
    · have hcz : (Complex.I * Gcusp ℓ d 1 1 τ) * (Y : ℂ) = 0 := by
        rw [FunnelAsm.gcusp_one_zero ℓ (h8of h2) 1 τ, mul_zero, zero_mul]
      rw [hq5set, hcz, iteratedDeriv_const_mul (0 : ℂ) hA1cd.contDiffAt, norm_mul]
      simp only [norm_zero, zero_mul, mul_zero]
      exact mul_nonneg (by positivity) hB0
  have hc0 : ContDiffAt ℝ (↑l) q0 r := by
    rw [hq0set]; exact (contDiff_const.mul hA0cd).contDiffAt
  have hc1 : ContDiffAt ℝ (↑l) q1 r := by
    rw [hq1set]; exact (contDiff_const.mul hS0cd).contDiffAt
  have hc2 : ContDiffAt ℝ (↑l) q2 r := by
    rw [hq2set]; exact (contDiff_const.mul hA0cd).contDiffAt
  have hc3 : ContDiffAt ℝ (↑l) q3 r := by
    rw [hq3set]; exact (contDiff_const.mul hA1cd).contDiffAt
  have hc4 : ContDiffAt ℝ (↑l) q4 r := by
    rw [hq4set]; exact (contDiff_const.mul hS1cd).contDiffAt
  have hc5 : ContDiffAt ℝ (↑l) q5 r := by
    rw [hq5set]; exact (contDiff_const.mul hA1cd).contDiffAt
  have hcd01 : ContDiffAt ℝ (↑l) (q0 + q1) r := hc0.add hc1
  have hcd012 : ContDiffAt ℝ (↑l) (q0 + q1 + q2) r := hcd01.add hc2
  have hcd0123 : ContDiffAt ℝ (↑l) (q0 + q1 + q2 + q3) r := hcd012.add hc3
  have hcd01234 : ContDiffAt ℝ (↑l) (q0 + q1 + q2 + q3 + q4) r := hcd0123.add hc4
  rw [hdecomp]
  rw [iteratedDeriv_add hcd01234 hc5, iteratedDeriv_add hcd0123 hc4,
    iteratedDeriv_add hcd012 hc3, iteratedDeriv_add hcd01 hc2, iteratedDeriv_add hc0 hc1]
  have hnorm : ‖iteratedDeriv l q0 r + iteratedDeriv l q1 r + iteratedDeriv l q2 r
        + iteratedDeriv l q3 r + iteratedDeriv l q4 r + iteratedDeriv l q5 r‖
      ≤ ‖iteratedDeriv l q0 r‖ + ‖iteratedDeriv l q1 r‖ + ‖iteratedDeriv l q2 r‖
        + ‖iteratedDeriv l q3 r‖ + ‖iteratedDeriv l q4 r‖ + ‖iteratedDeriv l q5 r‖ := by
    have h1 := norm_add_le (iteratedDeriv l q0 r + iteratedDeriv l q1 r + iteratedDeriv l q2 r
      + iteratedDeriv l q3 r + iteratedDeriv l q4 r) (iteratedDeriv l q5 r)
    have h2 := norm_add_le (iteratedDeriv l q0 r + iteratedDeriv l q1 r + iteratedDeriv l q2 r
      + iteratedDeriv l q3 r) (iteratedDeriv l q4 r)
    have h3 := norm_add_le (iteratedDeriv l q0 r + iteratedDeriv l q1 r + iteratedDeriv l q2 r)
      (iteratedDeriv l q3 r)
    have h4 := norm_add_le (iteratedDeriv l q0 r + iteratedDeriv l q1 r) (iteratedDeriv l q2 r)
    have h5 := norm_add_le (iteratedDeriv l q0 r) (iteratedDeriv l q1 r)
    have n0 := norm_nonneg (iteratedDeriv l q0 r)
    have n1 := norm_nonneg (iteratedDeriv l q1 r)
    have n2 := norm_nonneg (iteratedDeriv l q2 r)
    have n3 := norm_nonneg (iteratedDeriv l q3 r)
    have n4 := norm_nonneg (iteratedDeriv l q4 r)
    have n5 := norm_nonneg (iteratedDeriv l q5 r)
    linarith
  have hsum : |r| ^ k * ‖iteratedDeriv l q0 r + iteratedDeriv l q1 r + iteratedDeriv l q2 r
        + iteratedDeriv l q3 r + iteratedDeriv l q4 r + iteratedDeriv l q5 r‖
      ≤ (2 * K * (scale τ) ^ (Nc + 1)) * B + (2 * K * (scale τ) ^ (Nc + 1)) * B
        + (2 * K * (scale τ) ^ (Nc + 1)) * B + (2 * K * (scale τ) ^ (Nc + 1)) * B
        + (2 * K * (scale τ) ^ (Nc + 1)) * B + (2 * K * (scale τ) ^ (Nc + 1)) * B := by
    calc |r| ^ k * ‖iteratedDeriv l q0 r + iteratedDeriv l q1 r + iteratedDeriv l q2 r
          + iteratedDeriv l q3 r + iteratedDeriv l q4 r + iteratedDeriv l q5 r‖
        ≤ |r| ^ k * (‖iteratedDeriv l q0 r‖ + ‖iteratedDeriv l q1 r‖ + ‖iteratedDeriv l q2 r‖
          + ‖iteratedDeriv l q3 r‖ + ‖iteratedDeriv l q4 r‖ + ‖iteratedDeriv l q5 r‖) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = |r| ^ k * ‖iteratedDeriv l q0 r‖ + |r| ^ k * ‖iteratedDeriv l q1 r‖
          + |r| ^ k * ‖iteratedDeriv l q2 r‖ + |r| ^ k * ‖iteratedDeriv l q3 r‖
          + |r| ^ k * ‖iteratedDeriv l q4 r‖ + |r| ^ k * ‖iteratedDeriv l q5 r‖ := by ring
      _ ≤ (2 * K * (scale τ) ^ (Nc + 1)) * B + (2 * K * (scale τ) ^ (Nc + 1)) * B
          + (2 * K * (scale τ) ^ (Nc + 1)) * B + (2 * K * (scale τ) ^ (Nc + 1)) * B
          + (2 * K * (scale τ) ^ (Nc + 1)) * B + (2 * K * (scale τ) ^ (Nc + 1)) * B :=
          add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hq0b hq1b) hq2b) hq3b)
            hq4b) hq5b
  have hfinal : (2 * K * (scale τ) ^ (Nc + 1)) * B + (2 * K * (scale τ) ^ (Nc + 1)) * B
      + (2 * K * (scale τ) ^ (Nc + 1)) * B + (2 * K * (scale τ) ^ (Nc + 1)) * B
      + (2 * K * (scale τ) ^ (Nc + 1)) * B + (2 * K * (scale τ) ^ (Nc + 1)) * B
      ≤ 20 * K * Cm * Real.exp (2 * Real.pi) * (scale τ) ^ (Nc + 1 + l) := by
    have hYl : Y ^ l ≤ (scale τ) ^ (l : ℝ) := by
      rw [Real.rpow_natCast]
      exact pow_le_pow_left₀ hYpos.le hYscale l
    have hsplit : (scale τ) ^ (Nc + 1 + l)
        = (scale τ) ^ (Nc + 1) * (scale τ) ^ (l : ℝ) := by
      rw [show Nc + 1 + (l : ℝ) = (Nc + 1) + (l : ℝ) by ring, Real.rpow_add hscalepos]
    have hcomb : (2 * K * (scale τ) ^ (Nc + 1)) * B + (2 * K * (scale τ) ^ (Nc + 1)) * B
        + (2 * K * (scale τ) ^ (Nc + 1)) * B + (2 * K * (scale τ) ^ (Nc + 1)) * B
        + (2 * K * (scale τ) ^ (Nc + 1)) * B + (2 * K * (scale τ) ^ (Nc + 1)) * B
        = 12 * K * (scale τ) ^ (Nc + 1) * B := by ring
    rw [hcomb, hBdef]
    have hX : (0 : ℝ) ≤ (scale τ) ^ (Nc + 1) * (scale τ) ^ (l : ℝ) := by positivity
    have hred : 12 * K * (scale τ) ^ (Nc + 1) * (Cm * Real.exp (2 * Real.pi) * Y ^ l)
        ≤ 12 * K * Cm * Real.exp (2 * Real.pi) * ((scale τ) ^ (Nc + 1)
          * (scale τ) ^ (l : ℝ)) := by
      have h1 : Cm * Real.exp (2 * Real.pi) * Y ^ l
          ≤ Cm * Real.exp (2 * Real.pi) * (scale τ) ^ (l : ℝ) :=
        mul_le_mul_of_nonneg_left hYl (by positivity)
      calc 12 * K * (scale τ) ^ (Nc + 1) * (Cm * Real.exp (2 * Real.pi) * Y ^ l)
          ≤ 12 * K * (scale τ) ^ (Nc + 1) * (Cm * Real.exp (2 * Real.pi)
              * (scale τ) ^ (l : ℝ)) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 12 * K * Cm * Real.exp (2 * Real.pi) * ((scale τ) ^ (Nc + 1)
              * (scale τ) ^ (l : ℝ)) := by ring
    have hE1 : (1 : ℝ) ≤ Real.exp (2 * Real.pi) := Real.one_le_exp (by positivity)
    have hbig : 12 * K * Cm * Real.exp (2 * Real.pi) * ((scale τ) ^ (Nc + 1)
          * (scale τ) ^ (l : ℝ))
        ≤ 20 * K * Cm * Real.exp (2 * Real.pi) * ((scale τ) ^ (Nc + 1)
          * (scale τ) ^ (l : ℝ)) := by
      have hK0' : (0 : ℝ) ≤ K := hK0
      have hCm0' : (0 : ℝ) ≤ Cm := hCm0
      have hE0 : (0 : ℝ) ≤ Real.exp (2 * Real.pi) := (Real.exp_pos _).le
      have h12 : (12 : ℝ) ≤ 20 * Real.exp (2 * Real.pi) := by nlinarith [hE1]
      have hpre : (0 : ℝ) ≤ K * Cm * Real.exp (2 * Real.pi)
          * ((scale τ) ^ (Nc + 1) * (scale τ) ^ (l : ℝ)) := by positivity
      nlinarith [hpre, h12, Real.exp_nonneg (2 * Real.pi)]
    calc 12 * K * (scale τ) ^ (Nc + 1) * (Cm * Real.exp (2 * Real.pi) * Y ^ l)
        ≤ 12 * K * Cm * Real.exp (2 * Real.pi) * ((scale τ) ^ (Nc + 1)
            * (scale τ) ^ (l : ℝ)) := hred
      _ ≤ 20 * K * Cm * Real.exp (2 * Real.pi) * ((scale τ) ^ (Nc + 1)
            * (scale τ) ^ (l : ℝ)) := hbig
      _ = 20 * K * Cm * Real.exp (2 * Real.pi) * (scale τ) ^ (Nc + 1)
            * (scale τ) ^ (l : ℝ) := by ring
      _ = 20 * K * Cm * Real.exp (2 * Real.pi) * (scale τ) ^ (Nc + 1 + l) := by
          rw [hsplit]; ring
  exact le_trans hsum hfinal

end Work.Asymptotics
