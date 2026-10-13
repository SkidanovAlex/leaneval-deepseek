/-
Copyright: work module for the Elgindi finite-time singularity project.

# Uniqueness for the Euler-type ODE `α²z²u'' + α(5+α)zu' = 0` with decay and a `z = 0` bound

The angular moment `u = F_*(Ψ) = ∫_θ Ψ(z,θ) sinθcos²θ dθ` of any solution of (PolarBSL) with
moment-free source (`F_*(F) ≡ 0`) satisfies the Euler-type ODE

  `α² z² u''(z) + α (5 + α) z u'(z) = 0`   on `(0,∞)`

(the adjoint-kernel property of `sinθcos²θ`, `Work.Elliptic.Lzero_orthogonal`).  Its solution
space is spanned by `1` and `z^{-(5/α)}`; the decay `u → 0` at `+∞` kills the constant
(`Work.FTS.ClassC.euler_ode_solution_of_decay` leaves `u = B z^{-(5/α)}`), and the *second*
boundary condition at `z = 0` kills the remaining branch: either boundedness of `u` near `0`
(equivalently `u = o(1)`), or the paper's condition `z²u → 0` (`R²Ψ → 0` at `R = 0`).  Both
statements of the present file are therefore

  `u` solves the ODE, `u → 0` at `+∞`, and `u` is controlled at `z = 0`  ⟹  `u ≡ 0`,

which is the exact form in which the moment `F_*(Ψ)` is proved to vanish in the elliptic
existence node (`Work.FTS.PhiStar.bslOp_sol_exists`, see
`Submission/Work/FTS/ClassC/NOTES_session_node_gap.md` and the dossier
`Submission/Work/FTS/PhiStar/NOTES_bslOp_sol_exists.md`): the node's weak class
`Work.FTS.EllipticEst.TT.EllWeakPos` carries `Fstar Ψ z = 0` as a field.

Both results are proved from `euler_ode_solution_of_decay` alone; they are `sorry`-free and
rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib
import Submission.Work.FTS.ClassC.euler_ode_solution_of_decay

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter Set MeasureTheory

namespace Work.FTS.ClassC

set_option autoImplicit false

/-- **Uniqueness of the Euler-type ODE with decay and boundedness at `z = 0`.**

If `u ∈ C²(0,∞)` solves `α²z²u'' + α(5+α)zu' = 0` on `(0,∞)`, tends to `0` at `+∞` and is
bounded on `(0,1)`, then `u ≡ 0`.

Indeed `u = B z^{-(5/α)}`; boundedness on `(0,1)` forces `|B| ≤ M z^{5/α}` along `z = 1/(n+2)`,
hence `|B| = 0`. -/
theorem euler_ode_eq_zero_of_decay_of_bdd {α : ℝ} {u : ℝ → ℝ} (hα : 0 < α)
    (hu : ContDiffOn ℝ 2 u (Set.Ioi (0 : ℝ)))
    (hode : ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv u z') z + α * (5 + α) * z * deriv u z = 0)
    (hdec : Filter.Tendsto u Filter.atTop (nhds 0))
    (hbdd : ∃ M : ℝ, ∀ z ∈ Set.Ioo (0 : ℝ) 1, |u z| ≤ M) :
    ∀ z ∈ Set.Ioi (0 : ℝ), u z = 0 := by
  obtain ⟨B, hB⟩ := euler_ode_solution_of_decay hα hu hode hdec
  obtain ⟨M, hM⟩ := hbdd
  -- the substitution `z = ((n : ℝ) + 2)⁻¹` turns `z ^ (-(5/α))` into `((n : ℝ) + 2) ^ (5/α)`
  have hpow : ∀ n : ℕ, (((n : ℝ) + 2)⁻¹) ^ (-(5 / α)) = ((n : ℝ) + 2) ^ (5 / α) := by
    intro n
    have hpos : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
    calc (((n : ℝ) + 2)⁻¹) ^ (-(5 / α))
        = ((((n : ℝ) + 2)⁻¹) ^ (5 / α))⁻¹ := Real.rpow_neg (x := ((n : ℝ) + 2)⁻¹) (by positivity) _
      _ = ((((n : ℝ) + 2) ^ (5 / α))⁻¹)⁻¹ := by
            rw [Real.inv_rpow (x := (n : ℝ) + 2) hpos (5 / α)]
      _ = ((n : ℝ) + 2) ^ (5 / α) := inv_inv _
  have hB0 : B = 0 := by
    have hkey : ∀ n : ℕ, |B| ≤ M / (((n : ℝ) + 2) ^ (5 / α)) := by
      intro n
      have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hlt : (1 : ℝ) < (n : ℝ) + 2 := by
        have h0 := Nat.cast_nonneg (α := ℝ) n
        linarith
      have hz : ((n : ℝ) + 2)⁻¹ ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨by positivity, inv_lt_one_of_one_lt₀ hlt⟩
      have h1 : |u (((n : ℝ) + 2)⁻¹)| = |B| * (((n : ℝ) + 2) ^ (5 / α)) := by
        rw [hB _ hz.1, hpow n, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
      rw [le_div_iff₀ (Real.rpow_pos_of_pos hpos _), ← h1]
      exact hM _ hz
    have hlim : Filter.Tendsto (fun n : ℕ => M / (((n : ℝ) + 2) ^ (5 / α)))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2)) Filter.atTop Filter.atTop :=
        tendsto_atTop_add_const_right _ (2 : ℝ) tendsto_natCast_atTop_atTop
      have h2 : Filter.Tendsto (fun n : ℕ => (((n : ℝ) + 2)) ^ (5 / α))
          Filter.atTop Filter.atTop :=
        ((tendsto_rpow_atTop (show (0 : ℝ) < 5 / α by positivity)).comp h1)
      exact Filter.Tendsto.div_atTop tendsto_const_nhds h2
    have hle : |B| ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hkey)
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg B))
  intro z hz
  rw [hB z hz, hB0, zero_mul]

/-- **Uniqueness of the Euler-type ODE with decay and `z²u → 0` at `z = 0`.**

Same statement as `euler_ode_eq_zero_of_decay_of_bdd` with the paper's `z = 0` condition
`z²u(z) → 0` in place of boundedness; `α < 5/2` is all that is needed (the application has
`α ≤ 1/4`).  With `u = B z^{-(5/α)}` one has `z²u(z) = B z^{2-5/α} → ±∞` for `B ≠ 0`. -/
theorem euler_ode_eq_zero_of_decay_of_zsq {α : ℝ} {u : ℝ → ℝ} (hα : 0 < α)
    (hα2 : α < 5 / 2)
    (hu : ContDiffOn ℝ 2 u (Set.Ioi (0 : ℝ)))
    (hode : ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv u z') z + α * (5 + α) * z * deriv u z = 0)
    (hdec : Filter.Tendsto u Filter.atTop (nhds 0))
    (hzsq : Filter.Tendsto (fun z : ℝ => z ^ 2 * u z) (𝓝[>] 0) (nhds 0)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), u z = 0 := by
  obtain ⟨B, hB⟩ := euler_ode_solution_of_decay hα hu hode hdec
  -- the exponent is strictly positive: `5/α - 2 > 0`
  have hpos_exp : 0 < 5 / α - 2 := by
    have h2 : (2 : ℝ) < 5 / α := by
      rw [lt_div_iff₀ hα]
      linarith
    linarith
  have hB0 : B = 0 := by
    by_contra hBne
    have hBpos : 0 < |B| := abs_pos.mpr hBne
    -- on `(0,∞)` one has `B z^(2-5/α) = z² u z`
    have hcongr : (fun z : ℝ => B * z ^ (2 - 5 / α)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun z : ℝ => z ^ 2 * u z) := by
      have hmem : ∀ᶠ z in 𝓝[>] (0 : ℝ), z ∈ Set.Ioi (0 : ℝ) := self_mem_nhdsWithin
      refine hmem.mono (fun z hz => ?_)
      dsimp only
      have step : z ^ 2 * (B * z ^ (-(5 / α))) = B * z ^ (2 - 5 / α) := by
        rw [← mul_assoc, mul_comm (z ^ 2) B, mul_assoc, ← Real.rpow_natCast,
          ← Real.rpow_add hz,
          show ((2 : ℕ) : ℝ) + -(5 / α) = 2 - 5 / α by push_cast; ring]
      rw [hB z hz, step]
    -- but `|B z^(2-5/α)| = |B| (z⁻¹)^(5/α-2) → +∞`
    have hatTop : Filter.Tendsto (fun z : ℝ => |B * z ^ (2 - 5 / α)|) (𝓝[>] 0) Filter.atTop := by
      have h1 : Filter.Tendsto (fun z : ℝ => (z⁻¹) ^ (5 / α - 2)) (𝓝[>] 0) Filter.atTop :=
        (tendsto_rpow_atTop hpos_exp).comp tendsto_inv_nhdsGT_zero
      have h2 : Filter.Tendsto (fun z : ℝ => |B| * (z⁻¹) ^ (5 / α - 2)) (𝓝[>] 0) Filter.atTop :=
        h1.const_mul_atTop hBpos
      refine Filter.Tendsto.congr' ?_ h2
      have hmem : ∀ᶠ z in 𝓝[>] (0 : ℝ), z ∈ Set.Ioi (0 : ℝ) := self_mem_nhdsWithin
      refine hmem.mono (fun z hz => ?_)
      dsimp only
      have hle : (0 : ℝ) ≤ z := hz.le
      have hinv : (z⁻¹) ^ (5 / α - 2) = z ^ (2 - 5 / α) := by
        rw [Real.inv_rpow (x := z) hle, ← Real.rpow_neg (x := z) hle (5 / α - 2)]
        congr 1
        ring
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hle _), hinv]
    have hnhds : Filter.Tendsto (fun z : ℝ => |B * z ^ (2 - 5 / α)|) (𝓝[>] 0) (nhds 0) := by
      have h1 : Filter.Tendsto (fun z : ℝ => B * z ^ (2 - 5 / α)) (𝓝[>] 0) (nhds 0) :=
        Filter.Tendsto.congr' hcongr.symm hzsq
      simpa using h1.abs
    exact not_tendsto_nhds_of_tendsto_atTop hatTop 0 hnhds
  intro z hz
  rw [hB z hz, hB0, zero_mul]

end Work.FTS.ClassC
