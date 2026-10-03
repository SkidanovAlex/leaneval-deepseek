import Mathlib
import Submission.Work.L62.lift_fatou
import Submission.Work.L62.tsum_decay

/-!
# `Work.L62.fatou_coord_fix` (a local copy of `Work.L62.fatou_of_decay_up`)

**Do not edit `Submission/Work/L62/fatou_of_decay_up.lean` (it belongs to another agent).**  That file
contains a *formalization* defect: the `simpa only [Pi.add_apply, id_eq]` at its line 104 fails
because the `Module ℂ ℂ` instance in the goal is the `CommCStarAlgebra`-one, not `Semiring.toModule`
(the statement itself is correct and the two functions are definitionally equal).  This module is a
verbatim copy with that one proof step replaced by `exact (differentiableAt_id.add hSat)`, so that
`Work.L62.tail_uniform3` (and hence `Work.L62.l62c`) can build.  Namespace and names are unchanged,
so this module is a drop-in replacement for `Submission.Work.L62.fatou_of_decay_up`.

Original header follows.

# `Work.L62.fatou_of_decay_up`

The Fatou coordinate for a self-map `H w = w + β + ρ w` of the half-plane `{y < im}` whose
perturbation decays exponentially at the upper end, `‖ρ w - c‖ ≤ M exp (-2π (im w - y))`, and which
has uniform upward drift `κ > 0`.

The coordinate is the (absolutely convergent) series

`L w = w + ∑' n, (ρ (H^[n] w) - c)`,

which satisfies `L (H w) = L w + (β + c)` by telescoping, and whose derivative is `1 + O (exp (-2π
(im w - y - 1/2)))`; the hypothesis `hnum` makes that `O (·)` smaller than `1/2` on the half-plane
`{Y < im}`, `Y ≥ y + 1/2`.  The analytic input is the Cauchy estimate for a series of holomorphic
functions with exponentially weighted geometric majorant (`Work.L62.tsum_decay`).
-/
namespace Work.L62

open Complex Filter Set Topology
open scoped Topology

noncomputable section

/-- Telescoping along the iterates. -/
lemma tsum_iterate_telescope {H ψ : ℂ → ℂ} {w : ℂ}
    (hsum : Summable fun n : ℕ => ψ ((H^[n]) w)) :
    (∑' n : ℕ, ψ ((H^[n]) (H w))) = (∑' n : ℕ, ψ ((H^[n]) w)) - ψ w := by
  have h1 : ∀ n : ℕ, ψ ((H^[n]) (H w)) = ψ ((H^[n+1]) w) := by
    intro n
    have h2 : (H^[n]) (H w) = (H^[n+1]) w := by
      simpa [Nat.succ_eq_add_one] using (Function.iterate_succ_apply H n w).symm
    rw [h2]
  rw [tsum_congr h1]
  have h := Summable.tsum_eq_zero_add hsum
  rw [h]
  simp only [Function.iterate_zero_apply]
  ring

/-! ## The Fatou coordinate -/

theorem fatou_of_decay_up {y Y κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M) (hy : y + 1 / 2 ≤ Y)
    {β c : ℂ} {H ρ : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H {w : ℂ | y < Complex.im w})
    (hmap : ∀ w : ℂ, y < Complex.im w → y < Complex.im (H w))
    (hinc : ∀ w : ℂ, y < Complex.im w → H w = w + β + ρ w)
    (hρd : DifferentiableOn ℂ ρ {w : ℂ | y < Complex.im w})
    (hdec : ∀ w : ℂ, y < Complex.im w → ‖ρ w - c‖ ≤ M * Real.exp (-2 * Real.pi * (Complex.im w - y)))
    (hdrift : ∀ w : ℂ, y < Complex.im w → κ ≤ Complex.im (H w - w))
    (hnum : 2 * M * Real.exp (-2 * Real.pi * (Y - y - 1 / 2)) /
      (1 - Real.exp (-2 * Real.pi * κ)) ≤ 1 / 2) :
    ∃ L : ℂ → ℂ, ∀ w : ℂ, Y < Complex.im w → DifferentiableAt ℂ L w ∧
      L (H w) = L w + (β + c) ∧ Y < Complex.im (H w) ∧ ‖deriv L w - 1‖ ≤ 1 / 2 := by
  set r : ℝ := Real.exp (-2 * Real.pi * κ) with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; exact Real.exp_nonneg _
  have hr1 : r < 1 := by
    rw [hrdef, Real.exp_lt_one_iff]
    have : (0 : ℝ) < 2 * Real.pi * κ := by positivity
    linarith
  have hψd : ∀ n : ℕ, DifferentiableOn ℂ (fun z : ℂ => ρ ((H^[n]) z) - c)
      {z : ℂ | y < Complex.im z} := by
    intro n
    have hmt : Set.MapsTo (H^[n]) {z : ℂ | y < z.im} {z : ℂ | y < z.im} :=
      iterate_mapsTo (fun u hu => hmap u hu) n
    have h := (hρd.sub_const c).comp (iterate_diff hH hmap n) hmt
    simpa [Function.comp_def] using h
  have hψbd : ∀ (n : ℕ) (z : ℂ), y < z.im →
      ‖ρ ((H^[n]) z) - c‖ ≤ M * Real.exp (-2 * Real.pi * (z.im - y)) * r ^ n := by
    intro n z hz
    obtain ⟨h1, h2⟩ := iterate_im hmap hdrift hz n
    have hd1 := hdec ((H^[n]) z) h1
    have h3 : Real.exp (-2 * Real.pi * (((H^[n]) z).im - y))
        ≤ Real.exp (-2 * Real.pi * (z.im + n * κ - y)) :=
      exp_neg_two_pi_anti (by linarith)
    have h4 : M * Real.exp (-2 * Real.pi * (((H^[n]) z).im - y))
        ≤ M * Real.exp (-2 * Real.pi * (z.im + n * κ - y)) :=
      mul_le_mul_of_nonneg_left h3 hM
    have hexp : Real.exp (-2 * Real.pi * (z.im + n * κ - y))
        = Real.exp (-2 * Real.pi * (z.im - y)) * r ^ n := by
      rw [hrdef, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    calc ‖ρ ((H^[n]) z) - c‖ ≤ M * Real.exp (-2 * Real.pi * (((H^[n]) z).im - y)) := hd1
      _ ≤ M * Real.exp (-2 * Real.pi * (z.im + n * κ - y)) := h4
      _ = M * Real.exp (-2 * Real.pi * (z.im - y)) * r ^ n := by rw [hexp]; ring
  obtain ⟨hsumm, hSdiff, hSder⟩ :=
    tsum_decay (g := fun n z => ρ ((H^[n]) z) - c) (a := y) (Y := Y) (A := M) (r := r)
      hy hr0 hr1 hM hψd hψbd
  refine ⟨fun z : ℂ => z + ∑' n, (ρ ((H^[n]) z) - c), ?_⟩
  intro w hw
  have hyw : y < w.im := by linarith
  have hHw : Y < (H w).im := by
    have h := hdrift w hyw
    have h2 : (H w - w).im = (H w).im - w.im := Complex.sub_im _ _
    rw [h2] at h
    linarith
  have hSat : DifferentiableAt ℂ (fun z : ℂ => ∑' n, (ρ ((H^[n]) z) - c)) w :=
    hSdiff.differentiableAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hw)
  refine ⟨?_, ?_, hHw, ?_⟩
  · have h1 : DifferentiableAt ℂ (fun z : ℂ => z) w := differentiableAt_id
    exact h1.add hSat
  · have htel : (∑' n : ℕ, (ρ ((H^[n]) (H w)) - c))
        = (∑' n : ℕ, (ρ ((H^[n]) w) - c)) - (ρ w - c) :=
      tsum_iterate_telescope (H := H) (ψ := fun z => ρ z - c) (w := w)
        (hsumm w (by linarith))
    have hHwinc : H w = w + β + ρ w := hinc w hyw
    simp only []
    rw [htel, hHwinc]
    ring
  · have hder : deriv (fun z : ℂ => z + ∑' n, (ρ ((H^[n]) z) - c)) w
        = 1 + deriv (fun z : ℂ => ∑' n, (ρ ((H^[n]) z) - c)) w := by
      have h1 : HasDerivAt (fun z : ℂ => z + ∑' n, (ρ ((H^[n]) z) - c))
          (1 + deriv (fun z : ℂ => ∑' n, (ρ ((H^[n]) z) - c)) w) w :=
        (hasDerivAt_id w).add hSat.hasDerivAt
      exact h1.deriv
    rw [hder]
    have hsub : (1 + deriv (fun z : ℂ => ∑' n, (ρ ((H^[n]) z) - c)) w) - 1
        = deriv (fun z : ℂ => ∑' n, (ρ ((H^[n]) z) - c)) w := by ring
    rw [hsub]
    refine le_trans (hSder w hw) ?_
    rw [hrdef]
    exact hnum

end

end Work.L62
