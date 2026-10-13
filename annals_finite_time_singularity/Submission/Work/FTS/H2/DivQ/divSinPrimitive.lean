import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.H2.DivQ.divSinPrimitiveDeriv
import Submission.Work.FTS.H2.DivQ.divSinPrimitiveVanish
import Submission.Work.FTS.H2.DivQ.primIntegrable
import Submission.Work.FTS.H2.DivQ.hardyIter_tendsto_zero
import Submission.Work.FTS.H2.DivQ.csWeightedInterval

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set Filter
open scoped Topology

/-! ### The family `V_j = x^{j+1}·∂_x^j (f/x)`, whose derivative is `x^j·f^{(j+1)}` on `(0,x₁)`. -/

private noncomputable def dspV (f : ℝ → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  x ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) x

/-! ### The primitive `G u = ∫_0^u s^k f^{(k+1)}(s) ds`: integrability, derivative, limit at `0⁺`. -/

private theorem dsp_iteratedDeriv_continuousOn_Ioo {f : ℝ → ℝ} {x₁ : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁)) (m : ℕ) :
    ContinuousOn (fun x : ℝ => iteratedDeriv m f x) (Set.Ioo 0 x₁) := by
  have hs : UniqueDiffOn ℝ (Set.Ioo (0 : ℝ) x₁) := isOpen_Ioo.uniqueDiffOn
  have hcont : ContinuousOn (iteratedDerivWithin m f (Set.Ioo (0 : ℝ) x₁)) (Set.Ioo (0 : ℝ) x₁) :=
    (hf.mono Set.Ioo_subset_Ioc_self).continuousOn_iteratedDerivWithin (by simp) hs
  exact hcont.congr fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm

private theorem dspPrimProps (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁))
    (hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioc 0 x₁) ∧
    (∀ x ∈ Set.Ioo 0 x₁,
        HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, s ^ k * iteratedDeriv (k + 1) f s)
          (x ^ k * iteratedDeriv (k + 1) f x) x) ∧
    Filter.Tendsto (fun u : ℝ => ∫ s in (0 : ℝ)..u, s ^ k * iteratedDeriv (k + 1) f s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hψ := primIntegrable k γ x₁ hx₁ hγ f hf hint
  refine ⟨hψ, ?_, ?_⟩
  · intro x hx
    have hInt : IntervalIntegrable (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
        volume (0 : ℝ) x := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hx.1.le]
      exact hψ.mono_set (Set.Ioc_subset_Ioc le_rfl hx.2.le)
    have hcontψ : ContinuousOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioo 0 x₁) :=
      (continuous_id.pow k).continuousOn.mul (dsp_iteratedDeriv_continuousOn_Ioo hf (k + 1))
    have hcontAt : ContinuousAt (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) x :=
      hcontψ.continuousAt (isOpen_Ioo.mem_nhds hx)
    have hsm := hcontψ.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo x hx
    exact intervalIntegral.integral_hasDerivAt_right hInt hsm hcontAt
  · refine Filter.Tendsto.congr' ?_ ((hardyIter_tendsto_zero hx₁ hψ).mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (intervalIntegral.integral_of_le hδ.le).symm

/-- **The primitive form of `∂_x^k (f/x)`, and the boundary control.**

Let `0 < x₁`, `γ > -1`, and let `f` be of class `C^∞` on the half-open interval `(0,x₁]`, with
`f(x) → 0` as `x → 0⁺` (the *limit*, not merely the value at `0`), and with
`B := ∫_0^{x₁} x^{2k-γ}(∂_x^{k+1} f)² < ∞` (honest — the hypothesis under which `paperHardyIter`
applies).  Then for every `x ∈ (0,x₁)` (note: the *open* interval, because `iteratedDeriv` is the
two-sided derivative)

  `x^{k+1} · ∂_x^k (fun y => f y / y) x = ∫_0^x s^k · ∂_x^{k+1} f (s) ds`

and the *boundary control*

  `x^{2k+1-γ} · (∂_x^k (fun y => f y / y) x)² ≤ 1/(1+γ) · ∫_0^x s^{2k-γ}(∂_x^{k+1} f (s))² ds`,

in particular `x^{2k+1-γ}(∂_x^k(f/x) x)² → 0` as `x → 0⁺`.

This is the missing ingredient for the *honesty* of the left-hand integral in
`Submission/Work/FTS/H2/DivQ/NOTES.md` §9.1: with it, the truncated integration-by-parts of
`paperHardyIter` gives `A_ε = ∫_ε^{x₁}x^{2k-γ}(∂_x^k(f/x))² ≤ C' B` uniformly in `ε`, hence
`A < ∞` by monotone convergence — the left-hand side of the paper's Lemma 2 *is* integrable, which
the junk-safe formulation of `paperHardyIter` alone cannot certify.

ROUTE.  Let `H = f/x`.  Write `P_k(x) := x^{k+1}H^{(k)}(x) - ∫_0^x s^k f^{(k+1)}(s)ds`.  By the
Leibniz identity `f^{(k+1)} = xH^{(k+1)} + (k+1)H^{(k)}` we get the *formal* derivative identity
`(x^{k+1}H^{(k)})' = x^k f^{(k+1)}` on `(0,x₁)`, hence `P_k` is constant there.  Then prove

  `(⋆_k)   |x^{k+1}H^{(k)}(x)| ≤ (1/(1+γ))^{1/2} x^{(1+γ)/2} B^{1/2}   for x ∈ (0,x₁)`

by induction on `k`: `⋆_0` is `|f(x)|`; `⋆_k` gives `lim_{ε→0}P_k(ε) = 0` because
`ε^{k+1}H^{(k)}(ε) → 0` by `⋆_k` and `|∫_0^ε s^k f^{(k+1)}| ≤ (∫_0^ε s^{2k-γ}(f^{(k+1)})²)^{1/2}
(∫_0^ε s^γ)^{1/2} → 0` by Cauchy–Schwarz and integrability; so `P_k ≡ 0` on `(0,x₁)`, which is the
claimed identity, and then Cauchy–Schwarz applied to `∫_0^x s^k f^{(k+1)}` gives `⋆_{k+1}`.
(`f(x) → 0` is needed exactly for `⋆_0`; with only `f 0 = 0` the statement is false, e.g.
`f = 1` on `(0,x₁)`.) -/
theorem divSinPrimitive (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁) →
      Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
        (Set.Ioc 0 x₁) →
      (∀ x ∈ Set.Ioo (0 : ℝ) x₁,
          x ^ (k + 1) * iteratedDeriv k (fun y : ℝ => f y / y) x
            = ∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s) ∧
        (∀ x ∈ Set.Ioo (0 : ℝ) x₁,
          x ^ (2 * (k : ℝ) + 1 - γ) * (iteratedDeriv k (fun y : ℝ => f y / y) x) ^ 2
            ≤ 1 / (1 + γ) * (∫ s in (0 : ℝ)..x,
                s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2)) := by
  intro f hf hf0 hint
  obtain ⟨hVd, hVr⟩ := divSinPrimitiveDeriv x₁ hx₁ f hf
  obtain ⟨hψint, hGd, hGt⟩ := dspPrimProps k γ x₁ hx₁ hγ f hf hint
  have hvan : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      Filter.Tendsto (fun x : ℝ => x ^ j * iteratedDeriv j f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    divSinPrimitiveVanish k γ x₁ hx₁ hγ f hf hint
  have hVd' : ∀ (j : ℕ) (x : ℝ), x ∈ Set.Ioo 0 x₁ →
      HasDerivAt (dspV f j) (x ^ j * iteratedDeriv (j + 1) f x) x := by
    intro j x hx
    change HasDerivAt (fun t : ℝ => t ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) t)
      (x ^ j * iteratedDeriv (j + 1) f x) x
    exact hVd j x hx
  have hVr' : ∀ (j : ℕ) (y : ℝ), y ∈ Set.Ioo 0 x₁ →
      dspV f (j + 1) y = y ^ (j + 1) * iteratedDeriv (j + 1) f y
        - (j + 1) * dspV f j y := by
    intro j y hy
    have h := hVr j y hy
    have hgoal : dspV f (j + 1) y
        = y ^ (j + 2) * iteratedDeriv (j + 1) (fun y : ℝ => f y / y) y := by
      simp only [dspV]
    rw [hgoal, h]
    simp only [dspV]
  -- the vanishings kill the boundary term
  have hVtend : ∀ j ≤ k,
      Filter.Tendsto (dspV f j) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hEq : dspV f 0 =ᶠ[nhdsWithin 0 (Set.Ioi 0)] f := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [dspV, iteratedDeriv_zero, Nat.zero_add, pow_one]
        rw [mul_comm x (f x / x), div_mul_cancel₀ (f x) (ne_of_gt hx)]
      exact hf0.congr' hEq.symm
    | succ n ih =>
      intro hn
      have hn' : n ≤ k := by omega
      have h1 : Filter.Tendsto (fun y : ℝ => y ^ (n + 1) * iteratedDeriv (n + 1) f y)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := hvan (n + 1) (by omega) hn
      have h2 : Filter.Tendsto (fun y : ℝ => (n + 1) * dspV f n y)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have h := (ih hn').const_mul ((n + 1 : ℕ) : ℝ)
        simpa using h
      have h3 := h1.sub h2
      have hstep : dspV f (n + 1) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          fun y : ℝ => y ^ (n + 1) * iteratedDeriv (n + 1) f y - (n + 1) * dspV f n y := by
        filter_upwards [Ioo_mem_nhdsGT hx₁] with y hy
        exact hVr' n y hy
      simpa using h3.congr' hstep.symm
  have hVk : Filter.Tendsto (dspV f k) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := hVtend k le_rfl
  -- the identity
  have hVg : ∀ x ∈ Set.Ioo (0 : ℝ) x₁, dspV f k x
      = ∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s := by
    have ha : x₁ / 2 ∈ Set.Ioo (0 : ℝ) x₁ := ⟨by linarith, by linarith⟩
    have hconst : ∀ x ∈ Set.Ioo (0 : ℝ) x₁,
        dspV f k x - (∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s)
          = dspV f k (x₁ / 2)
            - (∫ s in (0 : ℝ)..(x₁ / 2), s ^ k * iteratedDeriv (k + 1) f s) := by
      intro x hx
      have hder : ∀ y ∈ Set.uIcc (x₁ / 2) x,
          HasDerivAt (fun z : ℝ => dspV f k z
            - (∫ s in (0 : ℝ)..z, s ^ k * iteratedDeriv (k + 1) f s)) 0 y := by
        intro y hy
        have hyI : y ∈ Set.Ioo (0 : ℝ) x₁ := by
          rw [Set.mem_uIcc] at hy
          rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨lt_of_lt_of_le (by linarith) h1, lt_of_le_of_lt h2 hx.2⟩
          · exact ⟨lt_of_lt_of_le hx.1 h1, lt_of_le_of_lt h2 (by linarith)⟩
        have h := (hVd' k y hyI).sub (hGd y hyI)
        rw [sub_self] at h
        change HasDerivAt (fun z : ℝ => dspV f k z
          - (∫ s in (0 : ℝ)..z, s ^ k * iteratedDeriv (k + 1) f s)) 0 y
        exact h
      have hint0 : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (x₁ / 2) x :=
        intervalIntegrable_const
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint0
      simp only [intervalIntegral.integral_const, smul_eq_mul] at hftc
      linarith
    have hlim : Filter.Tendsto (fun x : ℝ => dspV f k x
        - (∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 - 0)) := hVk.sub hGt
    have hlimc : Filter.Tendsto (fun x : ℝ => dspV f k x
        - (∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (dspV f k (x₁ / 2)
          - (∫ s in (0 : ℝ)..(x₁ / 2), s ^ k * iteratedDeriv (k + 1) f s))) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hx₁] with x hx
      exact (hconst x hx).symm
    have hzero : dspV f k (x₁ / 2)
        - (∫ s in (0 : ℝ)..(x₁ / 2), s ^ k * iteratedDeriv (k + 1) f s) = 0 := by
      have h := tendsto_nhds_unique hlim hlimc
      linarith
    intro x hx
    have h := hconst x hx
    linarith
  refine ⟨?_, ?_⟩
  · intro x hx
    simpa [dspV] using hVg x hx
  · intro x hx
    set A : ℝ := iteratedDeriv k (fun y : ℝ => f y / y) x with hA
    set J : ℝ := ∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s with hJ
    set I0 : ℝ := ∫ s in (0 : ℝ)..x,
      s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2 with hI0
    have hx0 : 0 < x := hx.1
    have hxle : x ≤ x₁ := le_of_lt hx.2
    have hId : x ^ (k + 1) * A = J := by
      rw [hA, hJ]
      simpa [dspV] using hVg x hx
    have hi1 : MeasureTheory.IntegrableOn (fun s : ℝ =>
        s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2) (Set.Ioc 0 x) :=
      hint.mono_set (fun s hs => ⟨hs.1, le_trans hs.2 hxle⟩)
    have hi2 : MeasureTheory.IntegrableOn
        (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioc 0 x) :=
      hψint.mono_set (fun s hs => ⟨hs.1, le_trans hs.2 hxle⟩)
    have hCS := csWeightedInterval k γ x hx0 hγ (fun s : ℝ => iteratedDeriv (k + 1) f s) hi1 hi2
    rw [← hJ] at hCS
    have hIntγ : (∫ s in (0 : ℝ)..x, s ^ γ) = x ^ (1 + γ) / (1 + γ) := by
      rw [integral_rpow (Or.inl hγ), Real.zero_rpow (by linarith : γ + 1 ≠ 0), sub_zero,
        show γ + 1 = 1 + γ by ring]
    rw [hIntγ] at hCS
    rw [← hId] at hCS
    have h2 := mul_le_mul_of_nonneg_right hCS (Real.rpow_nonneg hx0.le (-1 - γ))
    have hcomb : x ^ (2 * (k : ℝ) + 2) * x ^ (-1 - γ) = x ^ (2 * (k : ℝ) + 1 - γ) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    have hsq : (x ^ (k + 1) * A) ^ 2 = x ^ (2 * (k : ℝ) + 2) * A ^ 2 := by
      rw [mul_pow]
      congr 1
      rw [← pow_mul, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have hxpow : x ^ (1 + γ) * x ^ (-1 - γ) = 1 := by
      rw [← Real.rpow_add hx0, show (1 : ℝ) + γ + (-1 - γ) = 0 by ring, Real.rpow_zero]
    have id1 : x ^ (2 * (k : ℝ) + 1 - γ) * A ^ 2
        = (x ^ (k + 1) * A) ^ 2 * x ^ (-1 - γ) := by
      rw [hsq, mul_assoc, mul_comm (A ^ 2) (x ^ (-1 - γ)), ← mul_assoc, hcomb]
    have id2 : ((x ^ (1 + γ) / (1 + γ)) * I0) * x ^ (-1 - γ) = (1 / (1 + γ)) * I0 := by
      have h1 : ((x ^ (1 + γ) / (1 + γ)) * I0) * x ^ (-1 - γ)
          = (x ^ (1 + γ) * x ^ (-1 - γ) * I0) / (1 + γ) := by ring
      rw [h1, hxpow, one_mul]
      ring
    calc x ^ (2 * (k : ℝ) + 1 - γ) * A ^ 2
        = (x ^ (k + 1) * A) ^ 2 * x ^ (-1 - γ) := id1
      _ ≤ ((x ^ (1 + γ) / (1 + γ)) * I0) * x ^ (-1 - γ) := h2
      _ = (1 / (1 + γ)) * I0 := id2


end Work.FTS.H2.DivQ
