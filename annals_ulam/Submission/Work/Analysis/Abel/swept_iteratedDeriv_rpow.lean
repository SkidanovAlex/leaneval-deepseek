import Mathlib
import Submission.Work.Analysis.Abel.SweptKernelDefs
import Submission.Work.Analysis.Abel.SweptKernelExpansion
import Submission.Work.Analysis.Abel.contDiffOn_pder_param
import Submission.Work.Analysis.Abel.hasDerivAt_integral_swept_rpow
import Submission.Work.Analysis.Abel.intervalIntegrable_rpow_sub_mul
import Submission.Work.Analysis.Abel.SweptKernelStep

namespace Work.Analysis.Abel

open scoped ContDiff Topology
open MeasureTheory Filter

/-- **Swept iterated derivative of a moving-limit integral with a fractional-power kernel.**

For `p = n + 1/2` and `k = n + 1` (so `p = k - 1/2 > k - 1`), the `(n+1)`-st derivative at `s`
of `u ↦ ∫_u^b (σ-u)^p A(u,σ) dσ` equals the integral over `σ ∈ [s,b]` of the `(n+1)`-st
derivative at `u = s` of `u ↦ (σ-u)^p A(u,σ)`.

Proof plan: put `Q_j(x,σ) = Σ_{i≤j} C(j,i)(-1)^i (p)_i (σ-x)^{p-i} ∂_u^{j-i}A(x,σ)` (the
explicit Leibniz expansion of `∂_u^j((σ-u)^p A(u,σ))` evaluated at `u = x`, with
`(p)_i = p(p-1)…(p-i+1)`) and `S_j(x) = ∫_σ in x..b Q_j(x,σ) dσ`. Show by induction on
`j ≤ n+1` that `iteratedDeriv j (fun u => ∫_σ in u..b (σ-u)^p A u σ) x = S_j x` for `x` near `s`.
Key facts: `∂_x Q_j(x,σ) = Q_{j+1}(x,σ)`; the boundary value `Q_j(x,x)` is `0` because every term
carries a factor `(σ-x)^{p-i}` with `p - i ≠ 0` for every integer `i` (`Real.zero_rpow`); and
`|Q_j(x,σ)| ≤ C |σ-x|^{p-j}` on the relevant region (from the explicit formula and boundedness of
the partials of `A`), so the moving part of the integral is `o(x-s)` whenever `j ≤ n`, since
`p - j + 1 > 1`. -/
theorem swept_iteratedDeriv_rpow (n : ℕ) {b s δ : ℝ} (hsb : s < b) (hδ : 0 < δ)
    {A : ℝ → ℝ → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2)
      (Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (b + δ))) :
    iteratedDeriv (n + 1) (fun u : ℝ => ∫ σ in u..b, (σ - u) ^ ((n : ℝ) + 1 / 2) * A u σ) s =
      ∫ σ in s..b, iteratedDeriv (n + 1) (fun u : ℝ => (σ - u) ^ ((n : ℝ) + 1 / 2) * A u σ) s := by
  set p : ℝ := (n : ℝ) + 1 / 2 with hp
  set ρ : ℝ := min (δ / 4) ((b - s) / 4) with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]
    exact lt_min (by linarith) (by linarith)
  have hρδ : ρ ≤ δ / 4 := by rw [hρdef]; exact min_le_left _ _
  have hρb : ρ ≤ (b - s) / 4 := by rw [hρdef]; exact min_le_right _ _
  have hsI : s ∈ Set.Ioo (s - ρ) (s + ρ) := ⟨by linarith, by linarith⟩
  -- The induction: `iteratedDeriv j F = S_j` on the neighbourhood `(s-ρ, s+ρ)`.
  have key : ∀ j, j ≤ n + 1 → ∀ y ∈ Set.Ioo (s - ρ) (s + ρ),
      iteratedDeriv j (fun u : ℝ => ∫ σ in u..b, (σ - u) ^ p * A u σ) y
        = ∫ σ in y..b, ks A p j y σ := by
    intro j
    induction j with
    | zero =>
        intro _ y _
        rw [iteratedDeriv_zero]
        simp only [ks_zero]
    | succ j ih =>
        intro hj y hy
        have hjn : j ≤ n := by omega
        rw [iteratedDeriv_succ]
        have hev : iteratedDeriv j (fun u : ℝ => ∫ σ in u..b, (σ - u) ^ p * A u σ)
            =ᶠ[𝓝 y] (fun z : ℝ => ∫ σ in z..b, ks A p j z σ) := by
          filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
          exact ih (by omega) z hz
        rw [Filter.EventuallyEq.deriv_eq hev]
        exact (hasDerivAt_integral_ks_succ hsb hδ hρ hρδ hρb hjn hA hy).deriv
  rw [key (n + 1) le_rfl s hsI]
  -- Identify the remaining integrand with the iterated derivative of the kernel.
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun σ hσ => ?_)
  have hσ' : σ ∈ Set.Ioc s b := by
    rwa [Set.uIoc_of_le hsb.le] at hσ
  have hσs : s < σ := hσ'.1
  have hσb : σ ≤ b := hσ'.2
  have hmem : (s, σ) ∈ Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (b + δ) :=
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hAt : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) (s, σ) :=
    hA.contDiffAt ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hmem)
  exact (ks_eq_iteratedDeriv hσs hAt (n + 1)).symm

end Work.Analysis.Abel
