import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.remov.HardyFin.Basic
import Submission.Work.FTS.EllipticEst.remov.HardyFin.divSinPrimitiveDeriv_fin
import Submission.Work.FTS.EllipticEst.remov.HardyFin.divSinPrimitiveVanish_fin
import Submission.Work.FTS.H2.DivQ.csWeightedInterval

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The finite-order primitive form of `∂_x^k (f/x)`

Finite-order version of `Work.FTS.H2.DivQ.divSinPrimitive`: with `f` of class `C^N` on `(0,x₁]`
for a *finite* `N ≥ k+2`, `f → 0` at `0⁺` and `∫_0^{x₁} x^{2k-γ}(f^{(k+1)})² < ∞` (`γ > -1`), we
get the primitive identity `x^{k+1}(f/x)^{(k)}(x) = ∫_0^x s^k f^{(k+1)}(s) ds` and the boundary
control `x^{2k+1-γ}((f/x)^{(k)}(x))² ≤ (1+γ)^{-1}∫_0^x s^{2k-γ}(f^{(k+1)})²`, both on `(0,x₁)`.
-/

namespace Work.FTS.EllipticEst.remov.HardyFin

open MeasureTheory Set Filter
open scoped Topology

/-- `V_j(x) = x^{j+1}·∂_x^j (f/x)(x)`, the family whose derivative is `x^j f^{(j+1)}`. -/
private noncomputable def finV (f : ℝ → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  x ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) x

theorem divSinPrimitive_fin (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ) (N : ℕ)
    (hN : k + 2 ≤ N) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁) →
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
  have hfA : ContDiffOn ℝ (((k + 2 : ℕ)) : WithTop ℕ∞) f (Set.Ioc 0 x₁) :=
    hf.of_le (by exact_mod_cast hN)
  obtain ⟨hVd, hVr⟩ := divSinPrimitiveDeriv_fin x₁ hx₁ k f hfA
  obtain ⟨hψint, hGcont, hGd⟩ := primitiveDerivData_fin k γ x₁ hx₁ hγ f hf (by omega) hint
  have hGt : Filter.Tendsto (fun u : ℝ => ∫ s in (0 : ℝ)..u, s ^ k * iteratedDeriv (k + 1) f s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := Work.FTS.H2.DivQ.hardyIter_tendsto_zero hx₁ hψint
    refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (intervalIntegral.integral_of_le hδ.le).symm
  have hvan : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      Filter.Tendsto (fun x : ℝ => x ^ j * iteratedDeriv j f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    divSinPrimitiveVanish_fin k γ x₁ hx₁ hγ N (by omega) f hf hint
  have hVd' : ∀ (j : ℕ) (x : ℝ), j ≤ k → x ∈ Set.Ioo 0 x₁ →
      HasDerivAt (finV f j) (x ^ j * iteratedDeriv (j + 1) f x) x := by
    intro j x hj hx
    change HasDerivAt (fun t : ℝ => t ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) t)
      (x ^ j * iteratedDeriv (j + 1) f x) x
    exact hVd j x hj hx
  have hVr' : ∀ (j : ℕ) (y : ℝ), j + 1 ≤ k → y ∈ Set.Ioo 0 x₁ →
      finV f (j + 1) y = y ^ (j + 1) * iteratedDeriv (j + 1) f y - (j + 1) * finV f j y := by
    intro j y hj hy
    have h := hVr j y (by omega) hy
    have hgoal : finV f (j + 1) y
        = y ^ (j + 2) * iteratedDeriv (j + 1) (fun y : ℝ => f y / y) y := by
      simp only [finV]
    rw [hgoal, h]
    simp only [finV]
  -- the vanishings kill the boundary term
  have hVtend : ∀ j ≤ k,
      Filter.Tendsto (finV f j) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hEq : finV f 0 =ᶠ[nhdsWithin 0 (Set.Ioi 0)] f := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [finV, iteratedDeriv_zero, Nat.zero_add, pow_one]
        rw [mul_comm x (f x / x), div_mul_cancel₀ (f x) (ne_of_gt hx)]
      exact hf0.congr' hEq.symm
    | succ n ih =>
      intro hn
      have hn' : n ≤ k := by omega
      have h1 : Filter.Tendsto (fun y : ℝ => y ^ (n + 1) * iteratedDeriv (n + 1) f y)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := hvan (n + 1) (by omega) hn
      have h2 : Filter.Tendsto (fun y : ℝ => (n + 1) * finV f n y)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have h := (ih hn').const_mul ((n + 1 : ℕ) : ℝ)
        simpa using h
      have h3 := h1.sub h2
      have hstep : finV f (n + 1) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          fun y : ℝ => y ^ (n + 1) * iteratedDeriv (n + 1) f y - (n + 1) * finV f n y := by
        filter_upwards [Ioo_mem_nhdsGT hx₁] with y hy
        exact hVr' n y hn hy
      simpa using h3.congr' hstep.symm
  have hVk : Filter.Tendsto (finV f k) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := hVtend k le_rfl
  -- the identity
  have hVg : ∀ x ∈ Set.Ioo (0 : ℝ) x₁, finV f k x
      = ∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s := by
    have ha : x₁ / 2 ∈ Set.Ioo (0 : ℝ) x₁ := ⟨by linarith, by linarith⟩
    have hconst : ∀ x ∈ Set.Ioo (0 : ℝ) x₁,
        finV f k x - (∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s)
          = finV f k (x₁ / 2)
            - (∫ s in (0 : ℝ)..(x₁ / 2), s ^ k * iteratedDeriv (k + 1) f s) := by
      intro x hx
      have hder : ∀ y ∈ Set.uIcc (x₁ / 2) x,
          HasDerivAt (fun z : ℝ => finV f k z
            - (∫ s in (0 : ℝ)..z, s ^ k * iteratedDeriv (k + 1) f s)) 0 y := by
        intro y hy
        have hyI : y ∈ Set.Ioo (0 : ℝ) x₁ := by
          rw [Set.mem_uIcc] at hy
          rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨lt_of_lt_of_le (by linarith) h1, lt_of_le_of_lt h2 hx.2⟩
          · exact ⟨lt_of_lt_of_le hx.1 h1, lt_of_le_of_lt h2 (by linarith)⟩
        have h := (hVd' k y le_rfl hyI).sub (hGd y hyI)
        rw [sub_self] at h
        change HasDerivAt (fun z : ℝ => finV f k z
          - (∫ s in (0 : ℝ)..z, s ^ k * iteratedDeriv (k + 1) f s)) 0 y
        exact h
      have hint0 : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (x₁ / 2) x :=
        intervalIntegrable_const
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint0
      simp only [intervalIntegral.integral_const, smul_eq_mul] at hftc
      linarith
    have hlim : Filter.Tendsto (fun x : ℝ => finV f k x
        - (∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 - 0)) := hVk.sub hGt
    have hlimc : Filter.Tendsto (fun x : ℝ => finV f k x
        - (∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (finV f k (x₁ / 2)
          - (∫ s in (0 : ℝ)..(x₁ / 2), s ^ k * iteratedDeriv (k + 1) f s))) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hx₁] with x hx
      exact (hconst x hx).symm
    have hzero : finV f k (x₁ / 2)
        - (∫ s in (0 : ℝ)..(x₁ / 2), s ^ k * iteratedDeriv (k + 1) f s) = 0 := by
      have h := tendsto_nhds_unique hlim hlimc
      linarith
    intro x hx
    have h := hconst x hx
    linarith
  refine ⟨?_, ?_⟩
  · intro x hx
    simpa [finV] using hVg x hx
  · intro x hx
    set A : ℝ := iteratedDeriv k (fun y : ℝ => f y / y) x with hA
    set J : ℝ := ∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s with hJ
    set I0 : ℝ := ∫ s in (0 : ℝ)..x,
      s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2 with hI0
    have hx0 : 0 < x := hx.1
    have hxle : x ≤ x₁ := le_of_lt hx.2
    have hId : x ^ (k + 1) * A = J := by
      rw [hA, hJ]
      simpa [finV] using hVg x hx
    have hi1 : MeasureTheory.IntegrableOn (fun s : ℝ =>
        s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2) (Set.Ioc 0 x) :=
      hint.mono_set (fun s hs => ⟨hs.1, le_trans hs.2 hxle⟩)
    have hi2 : MeasureTheory.IntegrableOn
        (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioc 0 x) :=
      hψint.mono_set (fun s hs => ⟨hs.1, le_trans hs.2 hxle⟩)
    have hCS := Work.FTS.H2.DivQ.csWeightedInterval k γ x hx0 hγ
      (fun s : ℝ => iteratedDeriv (k + 1) f s) hi1 hi2
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

end Work.FTS.EllipticEst.remov.HardyFin
