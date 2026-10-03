import Mathlib
import Submission.Work.Interfaces.Basic
import Submission.Work.Mset.escape
import Submission.Work.Mset.bdd_closed

/-! Basic facts about the Mandelbrot set (area MSET).

`Tc c z = z ^ 2 + c`, `Mandelbrot = {c | ∃ R, ∀ n, ‖(Tc c)^[n] 0‖ ≤ R}`.

The mathematical content is the classical *escape criterion* for the quadratic family:

* if `2 < ‖z‖` and `‖c‖ ≤ ‖z‖` then `‖(Tc c)^[k] z‖ ≥ ‖z‖ (‖z‖ - 1) ^ k`, so the orbit of `z`
  escapes to infinity (`Work.Mset.escape`);
* consequently `c ∈ Mandelbrot ↔ ∀ n, ‖(Tc c)^[n] 0‖ ≤ 2`, and off the Mandelbrot set the
  norms `‖(Tc c)^[n] 0‖` tend to infinity along `atTop`;
* each set `{c | ‖(Tc c)^[n] 0‖ ≤ 2}` is closed, because `c ↦ (Tc c)^[n] 0` is a polynomial,
  so `Mandelbrot` is closed and lies in `closedBall 0 2`;
* the trivial upper bound `dimH (frontier Mandelbrot) ≤ dimH ℂ = 2`.

Guidance from the project lead (the requester):

AREA MSET (basic facts about the Mandelbrot set). Interface: Submission/Work/Interfaces/Basic.lean,
def MandelDim.MsetStatement.
Tc c z = z^2 + c; Mandelbrot = {c | exists R, forall n, ||(Tc c)^[n] 0|| <= R} (ChallengeDeps,
namespace LeanEval.Dynamics.MandelbrotBoundary).
Route (all elementary, ~2-5K lines):
1. Escape lemma: if ||z|| > 2 and ||z|| >= ||c|| then ||Tc c z|| >= ||z||^2 - ||c|| >= ||z|| (||z|| - 1),
   and the orbit grows geometrically (factor ||z|| - 1 > 1), so it tends to infinity. Also: if ||c|| > 2
   then ||(Tc c)^[2] 0|| = ||c^2 + c|| > ||c|| and escape follows.
2. Hence c in Mandelbrot iff forall n, ||(Tc c)^[n] 0|| <= 2 (if some iterate has norm > 2, case on
   ||c|| <= 2 or > 2 and apply 1), and c not in M gives Tendsto (norm of iterate) atTop atTop.
3. Mandelbrot = Inter_n {c | ||(Tc c)^[n] 0|| <= 2}: each set is closed (c |-> (Tc c)^[n] 0 is a
   polynomial in c, continuous: prove Continuous by induction on n), so IsClosed. Subset of
   closedBall 0 2 from n = 1.
4. dimH (frontier Mandelbrot) <= 2: dimH_mono (subset_univ _) plus Real.dimH_univ_eq_finrank and
   Complex.finrank_real_complex (dimH is for the norm metric on C = R^2).
-/

open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter Topology MeasureTheory
open MandelDim

namespace Work.Mset

/-- Shifting a sequence to infinity: if `k ↦ f (k + m)` tends to infinity, so does `f`. -/
lemma tendsto_atTop_of_tendsto_shift (f : ℕ → ℝ) (m : ℕ)
    (h : Tendsto (fun k : ℕ => f (k + m)) atTop atTop) : Tendsto f atTop atTop := by
  rw [tendsto_atTop_atTop] at h ⊢
  intro b
  obtain ⟨i, hi⟩ := h b
  refine ⟨i + m, fun a ha => ?_⟩
  have hma : m ≤ a := le_trans (Nat.le_add_left m i) ha
  have hia : i ≤ a - m := Nat.le_sub_of_add_le ha
  have := hi (a - m) hia
  rwa [Nat.sub_add_cancel hma] at this

/-- Escape start: an orbit point of norm `> 2` whose norm dominates `‖c‖` makes the orbit
unbounded. -/
lemma not_bounded_of_escape_start (c z : ℂ) (hz : 2 < ‖z‖) (hc : ‖c‖ ≤ ‖z‖)
    (n : ℕ) (hn : z = (Tc c)^[n] 0) :
    ¬ (∃ R : ℝ, ∀ k : ℕ, ‖(Tc c)^[k] 0‖ ≤ R) := by
  rintro ⟨R, hR⟩
  have h1 : Tendsto (fun k : ℕ => ‖(Tc c)^[k] z‖) atTop atTop := (escape c z hz hc).2
  have h2 : (fun k : ℕ => ‖(Tc c)^[k] z‖) = fun k : ℕ => ‖(Tc c)^[k + n] 0‖ := by
    funext k
    show ‖(Tc c)^[k] z‖ = ‖(Tc c)^[k + n] 0‖
    rw [hn, Function.iterate_add_apply]
  rw [h2] at h1
  obtain ⟨K, hK⟩ := tendsto_atTop_atTop.mp h1 (R + 1)
  have hK' := hK K le_rfl
  have hRK := hR (K + n)
  linarith

/-- If some iterate of `0` has norm `> 2`, the orbit is unbounded. -/
lemma not_bounded_of_exists_iterate_gt (c : ℂ) (h : ∃ n : ℕ, 2 < ‖(Tc c)^[n] 0‖) :
    ¬ (∃ R : ℝ, ∀ n : ℕ, ‖(Tc c)^[n] 0‖ ≤ R) := by
  by_cases hc : ‖c‖ ≤ 2
  · obtain ⟨n, hn⟩ := h
    exact not_bounded_of_escape_start c ((Tc c)^[n] 0) hn (le_trans hc hn.le) n rfl
  · have hc' : 2 < ‖c‖ := not_le.mp hc
    exact not_bounded_of_escape_start c c hc' le_rfl 1 (by simp [Tc])

/-- Every element of the Mandelbrot set has all iterates of `0` of norm at most `2`. -/
lemma orbit_le_two_of_mem_mandelbrot (c : ℂ) (hc : c ∈ Mandelbrot) :
    ∀ n : ℕ, ‖(Tc c)^[n] 0‖ ≤ 2 := by
  by_contra h
  obtain ⟨n, hn⟩ := not_forall.mp h
  exact not_bounded_of_exists_iterate_gt c ⟨n, not_le.mp hn⟩ hc

lemma mem_mandelbrot_of_orbit_le_two (c : ℂ) (h : ∀ n : ℕ, ‖(Tc c)^[n] 0‖ ≤ 2) :
    c ∈ Mandelbrot :=
  ⟨2, h⟩

/-- The escape criterion: `c` lies in the Mandelbrot set iff every iterate of `0` stays within
distance `2` of the origin. -/
theorem mandelbrot_eq_setOf_orbit_le_two :
    Mandelbrot = {c : ℂ | ∀ n : ℕ, ‖(Tc c)^[n] 0‖ ≤ 2} := by
  ext c
  exact ⟨orbit_le_two_of_mem_mandelbrot c, mem_mandelbrot_of_orbit_le_two c⟩

/-- The Mandelbrot set is closed. -/
theorem isClosed_mandelbrot : IsClosed Mandelbrot := by
  rw [mandelbrot_eq_setOf_orbit_le_two]
  exact bdd_closed

/-- The Mandelbrot set is contained in the closed ball of radius `2`. -/
theorem mandelbrot_subset_closedBall : Mandelbrot ⊆ closedBall (0 : ℂ) 2 := by
  intro c hc
  have h1 : ‖(Tc c)^[1] 0‖ ≤ 2 := orbit_le_two_of_mem_mandelbrot c hc 1
  simpa [mem_closedBall, dist_eq_norm, Tc] using h1

/-- Once an orbit point has norm `> 2` and dominates `‖c‖`, the whole orbit of `0` tends to
infinity in norm (the tail starting at that point escapes). -/
lemma tendsto_norm_orbit_of_escape (c : ℂ) (m : ℕ) (z : ℂ) (hz : z = (Tc c)^[m] 0)
    (hz2 : 2 < ‖z‖) (hc : ‖c‖ ≤ ‖z‖) :
    Tendsto (fun n : ℕ => ‖(Tc c)^[n] 0‖) atTop atTop := by
  have h1 : Tendsto (fun k : ℕ => ‖(Tc c)^[k] z‖) atTop atTop := (escape c z hz2 hc).2
  have h2 : (fun k : ℕ => ‖(Tc c)^[k] z‖)
      = fun k : ℕ => (fun n : ℕ => ‖(Tc c)^[n] 0‖) (k + m) := by
    funext k
    show ‖(Tc c)^[k] z‖ = ‖(Tc c)^[k + m] 0‖
    rw [hz, Function.iterate_add_apply]
  rw [h2] at h1
  exact tendsto_atTop_of_tendsto_shift _ m h1

/-- Off the Mandelbrot set the norms of the iterates of `0` tend to infinity. -/
theorem tendsto_norm_orbit_of_not_mem (c : ℂ) (hc : c ∉ Mandelbrot) :
    Tendsto (fun n : ℕ => ‖(Tc c)^[n] 0‖) atTop atTop := by
  have hnc : ¬ (∃ R : ℝ, ∀ n : ℕ, ‖(Tc c)^[n] 0‖ ≤ R) := hc
  have hgt : ∀ R : ℝ, ∃ n : ℕ, R < ‖(Tc c)^[n] 0‖ := by
    intro R
    by_contra h
    exact hnc ⟨R, fun n => le_of_not_gt fun hlt => h ⟨n, hlt⟩⟩
  by_cases hc2 : 2 < ‖c‖
  · exact tendsto_norm_orbit_of_escape c 1 c (by simp [Tc]) hc2 le_rfl
  · have hc2' : ‖c‖ ≤ 2 := le_of_not_gt hc2
    obtain ⟨n, hn⟩ := hgt 2
    exact tendsto_norm_orbit_of_escape c n _ rfl hn (le_trans hc2' hn.le)

/-- The boundary of the Mandelbrot set has Hausdorff dimension at most `2`. -/
theorem dimH_frontier_mandelbrot_le_two : dimH (frontier Mandelbrot) ≤ 2 := by
  calc dimH (frontier Mandelbrot) ≤ dimH (univ : Set ℂ) := dimH_mono (subset_univ _)
    _ = 2 := by
        rw [Real.dimH_univ_eq_finrank ℂ, Complex.finrank_real_complex]
        norm_num

theorem mset : MsetStatement :=
  ⟨isClosed_mandelbrot, mandelbrot_subset_closedBall,
   fun c hc n => orbit_le_two_of_mem_mandelbrot c hc n,
   tendsto_norm_orbit_of_not_mem,
   dimH_frontier_mandelbrot_le_two⟩

end Work.Mset
