import Mathlib
import Submission.Work.OddVolterra.Swept.ksBounds
import Submission.Work.OddVolterra.Swept.ksLeibniz
import Submission.Work.OddVolterra.Swept.ks_swept_integral_hasDerivAt

/-!
# The swept iterated derivative of `C u + ∫_σ in u..b, (σ-u)^(n+1/2) A u σ`

The `(n+1)`-st derivative at `s` of the sum of a smooth function `C` and the swept integral
`u ↦ ∫_σ in u..b, (σ-u)^(n+1/2) A u σ` is the sum of the `(n+1)`-st derivative of `C` and the
integral of the `(n+1)`-st `u`-derivative of the kernel.

The proof is an induction on the order: `iteratedDeriv j` of `C + I` equals `iteratedDeriv j C`
plus the `ks`-integral `∫_σ in x..b, ks A (n+1/2) j x σ` (the Leibniz expansion of the `j`-th
`u`-derivative of the kernel), using that the latter's `x`-derivative is the integral of the next
`ks`, and finally identifying `ks A (n+1/2) (n+1) x σ` with the honest iterated derivative of the
kernel (the Leibniz identity `iteratedDeriv_rpow_mul_smooth`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Swept

open Work.OddVolterra
open Work.OddVolterra.Swept.Smooth

/-- **The reduction**: given the differentiation of the swept `ks`-integral (the `_core`
hypothesis), the `(n+1)`-st iterated derivative of `C u + ∫_σ in u..b, (σ-u)^(n+1/2) A u σ`
splits. -/
theorem swept_iteratedDeriv_rpow_add_of_core {n : ℕ} {b s δ : ℝ} (hsb : s < b) (hδ : 0 < δ)
    {A : ℝ → ℝ → ℝ} {C : ℝ → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2)
      (Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (b + δ)))
    (hC : ContDiffOn ℝ (⊤ : ℕ∞) C (Set.Ioo (s - δ) (s + δ)))
    (hcore : ∀ (j : ℕ), j ≤ n → ∀ (x : ℝ), x ∈ Set.Ioo (s - δ / 2) (s + δ / 2) → x < b →
      HasDerivAt (fun x' : ℝ => ∫ σ in x'..b, ks A ((n : ℝ) + 1 / 2) j x' σ)
        (∫ σ in x..b, ks A ((n : ℝ) + 1 / 2) (j + 1) x σ) x) :
    iteratedDeriv (n + 1) (fun u : ℝ => C u + ∫ σ in u..b, (σ - u) ^ ((n : ℝ) + 1 / 2) * A u σ) s =
      iteratedDeriv (n + 1) C s +
        ∫ σ in s..b, iteratedDeriv (n + 1) (fun u : ℝ => (σ - u) ^ ((n : ℝ) + 1 / 2) * A u σ) s := by
  have hδ2 : 0 < δ / 2 := by linarith
  have hU : IsOpen (Set.Ioo (s - δ) (s + δ)) := isOpen_Ioo
  -- the neighbourhood on which the induction takes place
  set N : Set ℝ := Set.Ioo (s - δ / 2) (s + δ / 2) ∩ Set.Iio b with hN
  have hNopen : IsOpen N := isOpen_Ioo.inter isOpen_Iio
  have hsN : s ∈ N := ⟨⟨by linarith, by linarith⟩, hsb⟩
  have hN_sub : ∀ x ∈ N, x ∈ Set.Ioo (s - δ) (s + δ) := by
    intro x hx
    exact ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
  have hN_lo : ∀ x ∈ N, x ∈ Set.Ioo (s - δ / 2) (s + δ / 2) := fun x hx => hx.1
  have hN_b : ∀ x ∈ N, x < b := fun x hx => hx.2
  -- compact box for the Leibniz identity
  have key : ∀ m : ℕ, m ≤ n + 1 → ∀ x ∈ N,
      iteratedDeriv m (fun u : ℝ => C u + ∫ σ in u..b, (σ - u) ^ ((n : ℝ) + 1 / 2) * A u σ) x
        = iteratedDeriv m C x + ∫ σ in x..b, ks A ((n : ℝ) + 1 / 2) m x σ := by
    intro m hm
    induction m with
    | zero =>
      intro x hx
      simp only [iteratedDeriv_zero]
      congr 1
      simp only [ks, lcoef, pder]
      simp
    | succ m ih =>
      intro x hx
      rw [iteratedDeriv_succ]
      have hev : (fun y : ℝ => iteratedDeriv m
            (fun u : ℝ => C u + ∫ σ in u..b, (σ - u) ^ ((n : ℝ) + 1 / 2) * A u σ) y)
          =ᶠ[𝓝 x] (fun y : ℝ => iteratedDeriv m C y + ∫ σ in y..b, ks A ((n : ℝ) + 1 / 2) m y σ) := by
        filter_upwards [hNopen.mem_nhds hx] with y hy
        exact ih (by omega) y hy
      rw [hev.deriv_eq]
      have hm' : m ≤ n := by omega
      have hderS : HasDerivAt (fun y : ℝ => ∫ σ in y..b, ks A ((n : ℝ) + 1 / 2) m y σ)
          (∫ σ in x..b, ks A ((n : ℝ) + 1 / 2) (m + 1) x σ) x :=
        hcore m hm' x (hN_lo x hx) (hN_b x hx)
      have hdiffC : DifferentiableAt ℝ (iteratedDeriv m C) x :=
        differentiableAt_iteratedDeriv_of_contDiffOn hU (hN_sub x hx) hC m
      have hsum : (fun y : ℝ => iteratedDeriv m C y + ∫ σ in y..b, ks A ((n : ℝ) + 1 / 2) m y σ)
          = (iteratedDeriv m C + fun y : ℝ => ∫ σ in y..b, ks A ((n : ℝ) + 1 / 2) m y σ) := by
        funext y; rfl
      rw [hsum, deriv_add hdiffC hderS.differentiableAt, hderS.deriv, ← iteratedDeriv_succ]
  -- apply the induction at the top order
  have htop := key (n + 1) le_rfl s hsN
  rw [htop]
  congr 1
  -- identify the `ks` expansion with the honest iterated derivative
  refine intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hsb) fun σ hσ => ?_
  have hσO : (s, σ) ∈ Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (b + δ) :=
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith [hσ.1], by linarith [hσ.2]⟩⟩
  have hAt : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) (s, σ) :=
    hA.contDiffAt ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hσO)
  exact (iteratedDeriv_rpow_mul_smooth (A := A) (p := (n : ℝ) + 1 / 2) (j := n + 1)
    (u := s) (σ := σ) hσ.1 hAt).symm

/-- **The swept iterated derivative of a sum.**
The `(n+1)`-st derivative at `s` of `u ↦ C u + ∫_σ in u..b, (σ-u)^(n+1/2) A u σ` is the sum of
the `(n+1)`-st derivative of `C` and the integral over `σ ∈ [s,b]` of the `(n+1)`-st
`u`-derivative of the kernel. -/
theorem swept_iteratedDeriv_rpow_add {n : ℕ} {b s δ : ℝ} (hsb : s < b) (hδ : 0 < δ)
    {A : ℝ → ℝ → ℝ} {C : ℝ → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2)
      (Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (b + δ)))
    (hC : ContDiffOn ℝ (⊤ : ℕ∞) C (Set.Ioo (s - δ) (s + δ))) :
    iteratedDeriv (n + 1) (fun u : ℝ => C u + ∫ σ in u..b, (σ - u) ^ ((n : ℝ) + 1 / 2) * A u σ) s =
      iteratedDeriv (n + 1) C s +
        ∫ σ in s..b, iteratedDeriv (n + 1) (fun u : ℝ => (σ - u) ^ ((n : ℝ) + 1 / 2) * A u σ) s := by
  refine swept_iteratedDeriv_rpow_add_of_core (n := n) hsb hδ hA hC ?_
  intro j hj x hx hxb
  exact ks_swept_integral_hasDerivAt (n := n) hsb hδ hA hj hx hxb

end Work.OddVolterra.Swept
