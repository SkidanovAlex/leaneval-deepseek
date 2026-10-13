import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Taylor.E3_taylor_closure_proved

namespace Work.WilE3.Taylor

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

/-
  annals_wilkies_conjecture, AREA E3: the polar set of the Łojasiewicz argument (Gabrielov 1995,
  Selecta Math. 1, §3), part 1 — the definition, its agreement with the classical "parallel
  gradients" formulation, the radial description of the fibres at regular points, and the fact that
  the polar set is locally cut out by exactly `k` equations (the shape `E3_identity` consumes in the
  `2k` variables `(x, z)`).
-/

/-! ## The polar set of the Łojasiewicz argument

Gabrielov's route to the effective Łojasiewicz inequality (Selecta Math. 1 (1995), §3) is:

* the **polar set** — the pairs `(x, z)` where `z` is a zero of `Φ` and `∇Φ (x)` is parallel to
  `x - z` — carries the slow-decay locus of `Φ` (the points where `Φ` is small relative to
  `dist (·, Z)` are critical points of `Φ` on the shells `{dist (·, Z) = ρ}`, and by Lagrange those
  lie on the polar set);
* the **order bound along the polar set** (the already-proved
  `Work.WilE3.Identity.E3_identity_proved_of_multiplicity`) converts the order of vanishing of `Φ`
  along the polar set into the Łojasiewicz exponent.

This section lays the first brick: the definition of the polar relation, its agreement with the
usual "parallel gradients" formulation, the fact that the polar *fibre* over a regular point `x` is
exactly the intersection of the zero set with the gradient-line through `x`, and closedness of the
polar set.  The local manifold structure at regular points and the Lagrange step are the next
bricks; the Puiseux/parametrisation theory and the (15)/(16) solution count are delegated (see
`NOTES_hasLoj_of_multiplicity.md`). -/

section Polar

variable {k : ℕ}
/-- The gradient vector of `Φ` at `x`, `(∇Φ x) i = fderiv ℝ Φ x (eᵢ)`. -/
noncomputable def grad (Φ : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) : Fin k → ℝ :=
  fun i => fderiv ℝ Φ x (Pi.single i (1 : ℝ))

/-- `Polar Φ x z` says: `z` is a zero of `Φ` and `∇Φ x` is parallel to `x - z`, written without
division as the vanishing of all the `2 × 2` minors
`(∇Φ x) i * (x - z) j - (∇Φ x) j * (x - z) i`.  These are precisely the pairs consisting of a point
`x` of the gradient-line through a zero `z` of `Φ`. -/
def Polar (Φ : (Fin k → ℝ) → ℝ) (x z : Fin k → ℝ) : Prop :=
  Φ z = 0 ∧ ∀ i j : Fin k, grad Φ x i * (x j - z j) - grad Φ x j * (x i - z i) = 0

/-- On the diagonal, the polar relation is just membership in the zero set. -/
theorem Polar.self (Φ : (Fin k → ℝ) → ℝ) (z : Fin k → ℝ) : Polar Φ z z ↔ Φ z = 0 := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, by intro i j; ring⟩

/-- If `∇Φ x` is a *scalar multiple* of `x - z` (the usual formulation "parallel"), all the minors
vanish.  This is the direction of `Polar` that the Lagrange multiplier theorem produces. -/
theorem Polar.of_smul (Φ : (Fin k → ℝ) → ℝ) {x z : Fin k → ℝ} (hz : Φ z = 0) {c : ℝ}
    (h : grad Φ x = c • (x - z)) : Polar Φ x z := by
  refine ⟨hz, ?_⟩
  intro i j
  rw [h]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- The vanishing of all `2 × 2` minors is exactly linear dependence of the two vectors. -/
theorem minors_eq_zero_iff (u v : Fin k → ℝ) :
    (∀ i j : Fin k, u i * v j - u j * v i = 0) ↔ (∃ c : ℝ, u = c • v) ∨ (∃ d : ℝ, v = d • u) := by
  constructor
  · intro h
    by_cases hv : v = 0
    · exact Or.inr ⟨0, by rw [hv]; simp⟩
    · left
      have ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hv (funext hcon)
      refine ⟨u j / v j, ?_⟩
      funext i
      have h1 : u i * v j = u j * v i := by
        have := h i j
        linarith
      rw [Pi.smul_apply, smul_eq_mul]
      field_simp
      linarith
  · rintro (⟨c, rfl⟩ | ⟨d, rfl⟩) <;> intro i j <;>
      · simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- At a point where the gradient does not vanish, the polar relation is exactly the classical
statement "`x` lies on the gradient-line through `z`". -/
theorem Polar.regular_iff (Φ : (Fin k → ℝ) → ℝ) {x z : Fin k → ℝ} (hg : grad Φ x ≠ 0) :
    Polar Φ x z ↔ Φ z = 0 ∧ ∃ c : ℝ, x - z = c • grad Φ x := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    rcases (minors_eq_zero_iff (grad Φ x) (x - z)).mp h.2 with ⟨c, hc⟩ | ⟨d, hd⟩
    · refine ⟨c⁻¹, ?_⟩
      have hc0 : c ≠ 0 := by
        intro h0
        exact hg (by rw [hc, h0]; simp)
      rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    · exact ⟨d, hd⟩
  · rintro ⟨hz, c, hc⟩
    rcases eq_or_ne c 0 with hc0 | hc0
    · have hxz : x = z := sub_eq_zero.mp (by rw [hc, hc0, zero_smul])
      rw [hxz]
      exact (Polar.self Φ z).mpr hz
    · exact Polar.of_smul Φ hz (show grad Φ x = c⁻¹ • (x - z) by
        rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul])

/-- **Local geometry of the polar set at a regular point.**  For a point `x` with `∇Φ x ≠ 0`, the
polar fibre over `x` is exactly the set of zeros of `Φ` on the gradient-line through `x`:
`{z | Polar Φ x z} = Z ∩ (x + ℝ • ∇Φ x)`.  In particular the polar set is the union, over the
gradient-lines of the regular points, of their intersections with `Z` — the "radial" picture of
Gabrielov's polar variety. -/
theorem polar_fiber (Φ : (Fin k → ℝ) → ℝ) {x : Fin k → ℝ} (hg : grad Φ x ≠ 0) :
    {z : Fin k → ℝ | Polar Φ x z}
      = {z : Fin k → ℝ | Φ z = 0 ∧ ∃ c : ℝ, x - z = c • grad Φ x} := by
  ext z
  exact Polar.regular_iff Φ hg

/-- The polar fibre over a regular point `x` is the zero set, along the gradient-line through `x`,
of the one-variable **radial function** `c ↦ Φ (x - c • ∇Φ x)`.  This is the form in which the
Puiseux/parametrisation theory applies to `Q`: the fibre is the zero set of a one-variable function,
so it is a discrete set or an arc of the gradient-line. -/
theorem polar_fiber_eq_radialZeros (Φ : (Fin k → ℝ) → ℝ) {x : Fin k → ℝ} (hg : grad Φ x ≠ 0) :
    {z : Fin k → ℝ | Polar Φ x z}
      = {z : Fin k → ℝ | ∃ c : ℝ, z = x - c • grad Φ x ∧ Φ (x - c • grad Φ x) = 0} := by
  rw [polar_fiber Φ hg]
  ext z
  constructor
  · rintro ⟨hz, c, hc⟩
    have hxz : x - c • grad Φ x = z := by rw [← hc]; abel
    exact ⟨c, hxz.symm, by rw [hxz]; exact hz⟩
  · rintro ⟨c, hc, hz⟩
    rw [← hc] at hz
    exact ⟨hz, c, by rw [hc]; abel⟩

/-- **Local geometry of the polar set at a regular point: the radial dichotomy.**  Let `Φ` be
real-analytic everywhere (e.g. `Φ = ∑ f_i²` for EA polynomials `f_i`).  Then for every `x` and every
`c` the one-variable radial function `c' ↦ Φ (x - c' • ∇Φ x)` is analytic at `c`, so *either* it
vanishes on a neighbourhood of `c` (the gradient-line is locally contained in the zero set, and the
polar fibre is an arc of the line) *or* its zero at `c` is isolated.  Together with
`polar_fiber_eq_radialZeros` this says that at a regular point `x` the polar fibre over `x` is a
discrete set or an arc of the gradient-line — the local structure that the order bound along `Q`
consumes. -/
theorem analytic_radial_zeros_dichotomy {Φ : (Fin k → ℝ) → ℝ} (hΦ : ∀ y, AnalyticAt ℝ Φ y)
    (x : Fin k → ℝ) (c : ℝ) :
    (∀ᶠ c' in 𝓝 c, Φ (x - c' • grad Φ x) = 0) ∨
      (∃ δ > 0, ∀ c' : ℝ, |c' - c| < δ → Φ (x - c' • grad Φ x) = 0 → c' = c) := by
  have h1 : AnalyticAt ℝ (fun c' : ℝ => x - c' • grad Φ x) c :=
    analyticAt_const.sub (analyticAt_id.smul analyticAt_const)
  have han : AnalyticAt ℝ (fun c' : ℝ => Φ (x - c' • grad Φ x)) c := by
    have h2 := AnalyticAt.comp (f := fun c' : ℝ => x - c' • grad Φ x) (x := c)
      (hΦ (x - c • grad Φ x)) h1
    simpa [Function.comp_def] using h2
  rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact Or.inl h
  · right
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp h
    refine ⟨δ, hδ, fun c' hc' hc'0 => ?_⟩
    by_contra hne
    refine hδsub ⟨?_, hne⟩ hc'0
    rw [Metric.mem_ball, Real.dist_eq]
    exact hc'

/-- **The polar set is locally cut out by exactly `k` equations.**  Where the `i`-th partial
derivative of `Φ` does not vanish, the parallelism `∇Φ x ∥ x - z` is equivalent to the `k - 1`
minors of the *single* index `i`; together with `Φ z = 0` this presents the polar set near
`(x, z)` by `k` equations — the shape `E3_identity` consumes in the `2k` variables `(x, z)`, where
the full family of `k(k-1)/2` minors is a dependent set. -/
theorem polar_iff_fixed_index {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {x z : Fin k → ℝ} (i : Fin k)
    (hi : grad Φ x i ≠ 0) :
    Polar Φ x z ↔ Φ z = 0 ∧
      ∀ j : Fin k, grad Φ x i * (x j - z j) - grad Φ x j * (x i - z i) = 0 := by
  constructor
  · intro h
    exact ⟨h.1, fun j => h.2 i j⟩
  · rintro ⟨hz, h⟩
    -- the `i`-th minors force `x - z = ((x i - z i) / ∇Φ x i) • ∇Φ x`
    have hw : x - z = ((x i - z i) / grad Φ x i) • grad Φ x := by
      funext j
      have hj : grad Φ x j * (x i - z i) = grad Φ x i * (x j - z j) := by
        have := h j
        linarith
      rw [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, div_mul_eq_mul_div, eq_div_iff hi]
      linarith
    refine ⟨hz, fun j l => ?_⟩
    have hj := congrFun hw j
    have hl := congrFun hw l
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hj hl
    rw [hj, hl]
    ring

/-- The polar set is closed (for continuous `Φ` with continuous gradient components). -/
theorem isClosed_polarSet (Φ : (Fin k → ℝ) → ℝ) (hΦ : Continuous Φ)
    (hg : ∀ i : Fin k, Continuous fun p : (Fin k → ℝ) × (Fin k → ℝ) => grad Φ p.1 i) :
    IsClosed {p : (Fin k → ℝ) × (Fin k → ℝ) | Polar Φ p.1 p.2} := by
  have hZ : IsClosed {p : (Fin k → ℝ) × (Fin k → ℝ) | Φ p.2 = 0} :=
    isClosed_eq (hΦ.comp continuous_snd) continuous_const
  have hmin : ∀ i j : Fin k, IsClosed {p : (Fin k → ℝ) × (Fin k → ℝ) |
      grad Φ p.1 i * (p.1 j - p.2 j) - grad Φ p.1 j * (p.1 i - p.2 i) = 0} := by
    intro i j
    refine isClosed_eq ?_ continuous_const
    have h1 : Continuous fun p : (Fin k → ℝ) × (Fin k → ℝ) => grad Φ p.1 i := hg i
    have h2 : Continuous fun p : (Fin k → ℝ) × (Fin k → ℝ) => grad Φ p.1 j := hg j
    have h3 : Continuous fun p : (Fin k → ℝ) × (Fin k → ℝ) => p.1 j - p.2 j :=
      ((continuous_apply j).comp continuous_fst).sub ((continuous_apply j).comp continuous_snd)
    have h4 : Continuous fun p : (Fin k → ℝ) × (Fin k → ℝ) => p.1 i - p.2 i :=
      ((continuous_apply i).comp continuous_fst).sub ((continuous_apply i).comp continuous_snd)
    exact (h1.mul h3).sub (h2.mul h4)
  have hall : IsClosed {p : (Fin k → ℝ) × (Fin k → ℝ) |
      ∀ i j : Fin k, grad Φ p.1 i * (p.1 j - p.2 j) - grad Φ p.1 j * (p.1 i - p.2 i) = 0} := by
    have heq : {p : (Fin k → ℝ) × (Fin k → ℝ) |
        ∀ i j : Fin k, grad Φ p.1 i * (p.1 j - p.2 j) - grad Φ p.1 j * (p.1 i - p.2 i) = 0}
        = ⋂ i, ⋂ j, {p : (Fin k → ℝ) × (Fin k → ℝ) |
            grad Φ p.1 i * (p.1 j - p.2 j) - grad Φ p.1 j * (p.1 i - p.2 i) = 0} := by
      ext p; simp [Set.mem_iInter]
    rw [heq]
    exact isClosed_iInter fun i => isClosed_iInter fun j => hmin i j
  have hsplit : {p : (Fin k → ℝ) × (Fin k → ℝ) | Polar Φ p.1 p.2} =
      {p : (Fin k → ℝ) × (Fin k → ℝ) | Φ p.2 = 0} ∩
        {p : (Fin k → ℝ) × (Fin k → ℝ) |
          ∀ i j : Fin k, grad Φ p.1 i * (p.1 j - p.2 j) - grad Φ p.1 j * (p.1 i - p.2 i) = 0} := by
    ext p; simp [Polar]
  rw [hsplit]
  exact hZ.inter hall

end Polar



end Work.WilE3.Taylor
