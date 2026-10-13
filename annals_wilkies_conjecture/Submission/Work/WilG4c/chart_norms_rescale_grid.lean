import Mathlib
import Submission.Work.WilG2.CompStep
import Submission.Work.WilG2.Tnorm
import Submission.Work.WilG2.CompBound
import Submission.Work.WilG4c.Norm
import Submission.Work.WilG4c.tnorm_comp_le_exp
import Submission.Work.WilG4c.norm_iteratedFDeriv_rescale_le
import Submission.Work.WilG4c.mem_openCube_rescale
import Submission.Work.WilG4c.factorial_mul_exp_div_le_one

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- **Norm control for a rescaled chart on a grid.**  Let `F : ℝ^N → ℝ` and `Φ : ℝ^N → ℝ^N`
be `C^r` at every point of the open cube, with `Φ` mapping the open cube into itself, with `F`
of unit derivative norms at the points `Φ x` and with the jet sum `Σ_{1≤k≤r} ‖D^k Φ x‖/k!`
bounded by `S` on the cube.  Then for a suitable constant `c > 0` (depending only on `N` and
`S`), and for every scaling `lam ≥ c(r+1)` and every grid point `v` with `0 ≤ v i ≤ lam - 1`,
the translated rescaled chart `y ↦ Φ ((v + y)/lam)` has the composite
`y ↦ F (Φ ((v + y)/lam))` of operator norm `≤ 1` in every order `≤ r` on the cube. -/
theorem chart_norms_rescale_grid (N : ℕ) (hN : 1 ≤ N) (S : ℝ) (hS : 0 ≤ S) :
    ∃ c : ℝ, 0 < c ∧ ∀ (r : ℕ) (hr : 1 ≤ r) (F : (Fin N → ℝ) → ℝ)
      (Φ : (Fin N → ℝ) → (Fin N → ℝ)) (lam : ℝ) (v : Fin N → ℝ),
      c * (r + 1) ≤ lam →
      (∀ x ∈ WilkiesDesign.openCube N, ContDiffAt ℝ r F (Φ x)) →
      (∀ x ∈ WilkiesDesign.openCube N, ContDiffAt ℝ r Φ x) →
      (∀ x ∈ WilkiesDesign.openCube N, Φ x ∈ WilkiesDesign.openCube N) →
      (∀ x ∈ WilkiesDesign.openCube N, ∀ m, m ≤ r → ‖iteratedFDeriv ℝ m F (Φ x)‖ ≤ 1) →
      (∀ x ∈ WilkiesDesign.openCube N,
        ∑ k ∈ Finset.Ico 1 (r + 1), ‖iteratedFDeriv ℝ k Φ x‖ / (k.factorial : ℝ) ≤ S) →
      (∀ i : Fin N, 0 ≤ v i ∧ v i ≤ lam - 1) →
      ∀ m, m ≤ r → ∀ x ∈ WilkiesDesign.openCube N,
        ‖iteratedFDeriv ℝ m
          (fun y : Fin N → ℝ => F (Φ (fun i => (v i + y i) / lam))) x‖ ≤ 1 := by
  -- The constant `c = 1 + exp S` has to beat the two growth factors produced by the
  -- composition bound: `m! ≤ (r+1)^m` (the inner Faà di Bruno sum) and `exp S`
  -- (the exponential bound on the jet sum of `Φ`).
  refine ⟨1 + Real.exp S, by positivity, ?_⟩
  intro r hr F Φ lam v hlam hF hΦ _hΦmem hFb hΦb hv m hm x hx
  have hc1 : (1 : ℝ) ≤ 1 + Real.exp S := by have := Real.exp_pos S; linarith
  have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by
    exact_mod_cast (show (1 : ℕ) ≤ r + 1 by omega)
  have hlam_pos : 0 < lam := by
    have h1 : (1 : ℝ) ≤ (1 + Real.exp S) * ((r : ℝ) + 1) :=
      one_le_mul_of_one_le_of_one_le hc1 hr1
    linarith
  -- the rescaled point is again a point of the cube
  have hξ : (fun i : Fin N => (v i + x i) / lam) ∈ WilkiesDesign.openCube N :=
    Work.WilG4c.mem_openCube_rescale hlam_pos hv hx
  rcases m with _ | m'
  · -- order `0`: this is the hypothesis on `F` at the rescaled point
    simp only [norm_iteratedFDeriv_zero]
    have h0 := hFb (fun i : Fin N => (v i + x i) / lam) hξ 0 (Nat.zero_le r)
    simpa only [norm_iteratedFDeriv_zero] using h0
  · -- order `m' + 1`: chain rule for the affine rescaling, then the jet bounds
    have hm1 : 1 ≤ Nat.succ m' := Nat.succ_le_succ (Nat.zero_le m')
    have hjet : ‖iteratedFDeriv ℝ (Nat.succ m') (F ∘ Φ) (fun i : Fin N => (v i + x i) / lam)‖
        ≤ (Nat.succ m').factorial * Real.exp S := by
      refine le_trans (Work.WilkG4c.NormJet r (Nat.succ m') hm (F ∘ Φ) _) ?_
      have hA : WilkiesDesign.CG.tnorm r (F ∘ Φ) (fun i : Fin N => (v i + x i) / lam)
          ≤ Real.exp S :=
        Work.WilG4c.tnorm_comp_le_exp S hS F Φ hF hΦ hFb hΦb _ hξ
      exact mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg _)
    calc ‖iteratedFDeriv ℝ (Nat.succ m')
            (fun y : Fin N → ℝ => F (Φ (fun i => (v i + y i) / lam))) x‖
        = ‖iteratedFDeriv ℝ (Nat.succ m')
            (fun y : Fin N → ℝ => (F ∘ Φ) (fun i => (v i + y i) / lam)) x‖ := by
          simp only [Function.comp_apply]
      _ ≤ ‖iteratedFDeriv ℝ (Nat.succ m') (F ∘ Φ)
            (fun i : Fin N => (v i + x i) / lam)‖ * lam⁻¹ ^ (Nat.succ m') :=
          Work.WilG4c.norm_iteratedFDeriv_rescale_le lam hlam_pos (F ∘ Φ) v x (Nat.succ m')
      _ ≤ ((Nat.succ m').factorial * Real.exp S) * lam⁻¹ ^ (Nat.succ m') :=
          mul_le_mul_of_nonneg_right hjet (pow_nonneg (inv_nonneg.mpr hlam_pos.le) _)
      _ ≤ 1 := by
          have harith :=
            Work.WilG4c.factorial_mul_exp_div_le_one S lam hS hlam hm1 hm
          have heq : ((Nat.succ m').factorial * Real.exp S) * lam⁻¹ ^ (Nat.succ m')
              = (Nat.succ m').factorial * Real.exp S / lam ^ (Nat.succ m') := by
            rw [inv_pow, div_eq_mul_inv]
          rw [heq]; exact harith

end Work.WilG4c
