import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Iterated form of the slice ODE `Lzero1 u = g`

`Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u`, so the relation `g = Lzero1 u` on `(0, π/2)` is the
second order ODE `u'' = ∂_θ(tan θ · u) - 6u - g`.  Differentiating it `k` times and using the
Leibniz rule for the product `tan · u` gives the stated expansion

`u^{(k+2)} = ∑_{i=0}^{k+1} C(k+1,i) (tan)^{(i)} u^{(k+1-i)} - 6 u^{(k)} - g^{(k)}`

at every point of `(0, π/2)`. -/

open scoped Real Topology

namespace Work.FTS.EllipticEst.remov

theorem Lzero1_iteratedDeriv_eq (k : ℕ) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      iteratedDeriv (k + 2) u θ
        = (∑ i ∈ Finset.range (k + 2), (k + 1).choose i *
              iteratedDeriv i Real.tan θ * iteratedDeriv (k + 1 - i) u θ)
          - 6 * iteratedDeriv k u θ - iteratedDeriv k g θ := by
  intro θ hθ
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  -- the ODE, rewritten on `U` as an identity for the second derivative of `u`
  have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (fun s => deriv u s) t
        = deriv (fun s => Real.tan s * u s) t - 6 * u t - g t := by
    intro t ht
    have h := hg t ht
    simp only [Work.FTS.EllipticEst.Lzero1] at h
    linarith
  -- regularity facts at `θ`
  have huk2 : ContDiffAt ℝ (k + 2 : WithTop ℕ∞) u θ := hu.contDiffAt (hU.mem_nhds hθ)
  have huAt1 : ContDiffAt ℝ (k + 1 : WithTop ℕ∞) u θ :=
    huk2.of_le (m := (k + 1 : WithTop ℕ∞)) (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
  have huk : ContDiffAt ℝ (k : WithTop ℕ∞) u θ :=
    huk2.of_le (m := (k : WithTop ℕ∞)) (by exact_mod_cast (show k ≤ k + 2 by omega))
  have htan1 : ContDiffAt ℝ (k + 1 : WithTop ℕ∞) Real.tan θ :=
    (Real.contDiffAt_tan (n := (k + 1 : WithTop ℕ∞))).mpr hcos
  have hA : ContDiffAt ℝ (k : WithTop ℕ∞) (fun t => deriv (fun s => Real.tan s * u s) t) θ :=
    (htan1.mul huAt1).derivWithin (m := (k : WithTop ℕ∞))
      (by exact_mod_cast (show k + 1 ≤ k + 1 by omega))
  have hB : ContDiffAt ℝ (k : WithTop ℕ∞) (fun t => 6 * u t) θ := huk.const_smul (6 : ℝ)
  -- `g` agrees with `Lzero1 u` near `θ`, and `Lzero1 u` is `C^k` there
  have hLzero : ContDiffAt ℝ (k : WithTop ℕ∞) (Work.FTS.EllipticEst.Lzero1 u) θ := by
    have hdu : ContDiffAt ℝ (k + 1 : WithTop ℕ∞) (fun s => deriv u s) θ :=
      huk2.derivWithin (m := (k + 1 : WithTop ℕ∞))
        (by exact_mod_cast (show k + 1 + 1 ≤ k + 2 by omega))
    have hddu : ContDiffAt ℝ (k : WithTop ℕ∞) (fun t => deriv (fun s => deriv u s) t) θ :=
      hdu.derivWithin (m := (k : WithTop ℕ∞)) (by exact_mod_cast (show k + 1 ≤ k + 1 by omega))
    exact ((hddu.neg).add hA).sub hB
  have hgev : g =ᶠ[𝓝 θ] Work.FTS.EllipticEst.Lzero1 u :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hθ) (fun t ht => hg t ht)
  have hC : ContDiffAt ℝ (k : WithTop ℕ∞) g θ := hLzero.congr_of_eventuallyEq hgev
  -- differentiate the ODE `k` times
  have step1 : iteratedDeriv (k + 2) u θ
      = iteratedDeriv k (fun t => deriv (fun s => deriv u s) t) θ := by
    rw [show k + 2 = (k + 1) + 1 by omega, iteratedDeriv_succ', iteratedDeriv_succ']
  have step2 : iteratedDeriv k (fun t => deriv (fun s => deriv u s) t) θ
      = iteratedDeriv k (fun t => deriv (fun s => Real.tan s * u s) t - 6 * u t - g t) θ :=
    Set.EqOn.iteratedDeriv_of_isOpen hpt hU k hθ
  have step3 : iteratedDeriv k (fun t => deriv (fun s => Real.tan s * u s) t - 6 * u t - g t) θ
      = iteratedDeriv k (fun t => deriv (fun s => Real.tan s * u s) t) θ
        - 6 * iteratedDeriv k u θ - iteratedDeriv k g θ := by
    have hAB : ContDiffAt ℝ (k : WithTop ℕ∞)
        ((fun t => deriv (fun s => Real.tan s * u s) t) - (fun t => 6 * u t)) θ := hA.sub hB
    rw [show (fun t => deriv (fun s => Real.tan s * u s) t - 6 * u t - g t)
        = ((fun t => deriv (fun s => Real.tan s * u s) t) - (fun t => 6 * u t)) - g from rfl]
    rw [iteratedDeriv_sub hAB hC, iteratedDeriv_sub hA hB, iteratedDeriv_const_mul_field]
  -- Leibniz for the product `tan · u`
  have step4 : iteratedDeriv k (fun t => deriv (fun s => Real.tan s * u s) t) θ
      = ∑ i ∈ Finset.range (k + 2), (k + 1).choose i *
            iteratedDeriv i Real.tan θ * iteratedDeriv (k + 1 - i) u θ := by
    rw [← iteratedDeriv_succ' (n := k) (f := fun s => Real.tan s * u s)]
    exact iteratedDeriv_mul htan1 huAt1
  rw [step1, step2, step3, step4]

end Work.FTS.EllipticEst.remov
