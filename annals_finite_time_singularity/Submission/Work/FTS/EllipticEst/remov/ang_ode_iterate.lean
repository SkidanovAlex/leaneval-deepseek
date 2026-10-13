import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.EllipticEst.remov

/-- **The `k`-fold differentiated slice ODE, in the `∂^{k+1}(tan θ · u)` form.**

`Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u`, so `g = Lzero1 u` on `(0,π/2)` says
`∂_θ(tan θ · u) = u'' + 6u + g` there; applying `∂_θ^k` to that identity gives, at every
`θ ∈ (0,π/2)`,

`∂_θ^{k+1}(tan θ · u)(θ) = u^{(k+2)}(θ) + 6 u^{(k)}(θ) + g^{(k)}(θ)`.

Route: the pointwise identity `deriv (fun t => Real.tan t * u t) θ = deriv (deriv u) θ + 6*u θ + g θ`
on `(0,π/2)` (from the definition of `Lzero1`), upgraded to an `=ᶠ[𝓝 θ]` statement, on which
`Filter.EventuallyEq.iteratedDeriv_eq k` applies; then `iteratedDeriv k` of the sum is the sum
(`iteratedDeriv_add` with the `ContDiffAt` regularity of the summands: for `u` from `hu`, for
`deriv (deriv u)` from `hu`, and for `g` from `g =ᶠ[𝓝 θ] Lzero1 u` together with the regularity of
`Lzero1 u`), and `iteratedDeriv k (deriv (deriv u)) = iteratedDeriv (k+2) u`,
`iteratedDeriv k (deriv f) = iteratedDeriv (k+1) f` (`iteratedDeriv_succ'`).  (The proved
`remov/Lzero1_iteratedDeriv_eq` gives the same content in expanded form with
`Σ_i C(k+1,i) (tan)^{(i)} u^{(k+1-i)}` on the left-hand side, so a proof can also be assembled from
it plus `iteratedDeriv_mul`.) -/
theorem ang_ode_iterate (k : ℕ) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
        = iteratedDeriv (k + 2) u θ + 6 * iteratedDeriv k u θ + iteratedDeriv k g θ := by
  intro θ hθ
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  -- the ODE, solved for `∂_θ(tan θ · u)` and read as a pointwise identity on `(0, π/2)`
  have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (fun s => Real.tan s * u s) t
        = deriv (fun s => deriv u s) t + 6 * u t + g t := by
    intro t ht
    have h := hg t ht
    simp only [Work.FTS.EllipticEst.Lzero1] at h
    linarith
  have hev : deriv (fun s => Real.tan s * u s) =ᶠ[𝓝 θ]
      fun t => deriv (fun s => deriv u s) t + 6 * u t + g t :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hθ) (fun t ht => hpt t ht)
  -- regularity facts at `θ`
  have huk2 : ContDiffAt ℝ (k + 2 : WithTop ℕ∞) u θ := hu.contDiffAt (hU.mem_nhds hθ)
  have huAt1 : ContDiffAt ℝ (k + 1 : WithTop ℕ∞) u θ :=
    huk2.of_le (m := (k + 1 : WithTop ℕ∞)) (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
  have huk : ContDiffAt ℝ (k : WithTop ℕ∞) u θ :=
    huk2.of_le (m := (k : WithTop ℕ∞)) (by exact_mod_cast (show k ≤ k + 2 by omega))
  have htan1 : ContDiffAt ℝ (k + 1 : WithTop ℕ∞) Real.tan θ :=
    (Real.contDiffAt_tan (n := (k + 1 : WithTop ℕ∞))).mpr hcos
  have hA : ContDiffAt ℝ (k : WithTop ℕ∞)
      (fun t => deriv (fun s => Real.tan s * u s) t) θ :=
    (htan1.mul huAt1).derivWithin (m := (k : WithTop ℕ∞))
      (by exact_mod_cast (show k + 1 ≤ k + 1 by omega))
  have hB : ContDiffAt ℝ (k : WithTop ℕ∞) (fun t => 6 * u t) θ := huk.const_smul (6 : ℝ)
  have hdu : ContDiffAt ℝ (k + 1 : WithTop ℕ∞) (fun s => deriv u s) θ :=
    huk2.derivWithin (m := (k + 1 : WithTop ℕ∞))
      (by exact_mod_cast (show k + 1 + 1 ≤ k + 2 by omega))
  have hddu : ContDiffAt ℝ (k : WithTop ℕ∞)
      (fun t => deriv (fun s => deriv u s) t) θ :=
    hdu.derivWithin (m := (k : WithTop ℕ∞)) (by exact_mod_cast (show k + 1 ≤ k + 1 by omega))
  have hLzero : ContDiffAt ℝ (k : WithTop ℕ∞) (Work.FTS.EllipticEst.Lzero1 u) θ :=
    ((hddu.neg).add hA).sub hB
  have hgev : g =ᶠ[𝓝 θ] Work.FTS.EllipticEst.Lzero1 u :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hθ) (fun t ht => hg t ht)
  have hC : ContDiffAt ℝ (k : WithTop ℕ∞) g θ := hLzero.congr_of_eventuallyEq hgev
  -- differentiate the identity `k` times and expand
  have step1 : iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
      = iteratedDeriv k (fun t => deriv (fun s => Real.tan s * u s) t) θ := by
    rw [iteratedDeriv_succ']
  have step2 : iteratedDeriv k (fun t => deriv (fun s => Real.tan s * u s) t) θ
      = iteratedDeriv k (fun t => deriv (fun s => deriv u s) t + 6 * u t + g t) θ :=
    hev.iteratedDeriv_eq k
  have step3 : iteratedDeriv k (fun t => deriv (fun s => deriv u s) t + 6 * u t + g t) θ
      = iteratedDeriv k (fun t => deriv (fun s => deriv u s) t) θ
        + 6 * iteratedDeriv k u θ + iteratedDeriv k g θ := by
    have hAB : ContDiffAt ℝ (k : WithTop ℕ∞)
        ((fun t => deriv (fun s => deriv u s) t) + (fun t => 6 * u t)) θ := hddu.add hB
    rw [show (fun t => deriv (fun s => deriv u s) t + 6 * u t + g t)
        = ((fun t => deriv (fun s => deriv u s) t) + (fun t => 6 * u t)) + g from rfl]
    rw [iteratedDeriv_add hAB hC, iteratedDeriv_add hddu hB,
      iteratedDeriv_const_mul_field]
  have step4 : iteratedDeriv k (fun t => deriv (fun s => deriv u s) t) θ
      = iteratedDeriv (k + 2) u θ := by
    rw [show k + 2 = (k + 1) + 1 by omega, iteratedDeriv_succ', iteratedDeriv_succ']
  rw [step1, step2, step3, step4]

end Work.FTS.EllipticEst.remov
