import Mathlib
import Submission.Work.Peluse.WindowControl.boxNormPow_one_window

/-!
# The first box-norm power as a `tsum`

`Work.Peluse.boxNormPow t Q S g` is defined through a `tsum` over all of `ℤ` (the `x`-sum in
`prodCubeSum`), and the window `S` enters only through the normalising factor `1/|S|`.  For
`t = 1` and a function `g` supported in `[-N,N]` the summand `‖∑_{a ∈ Q} g (x+a)‖²` vanishes once
`x` leaves the finite window `ball 1 (fun _ => Q) N = [-rad, rad]`, `rad = N + ∑_{a ∈ Q} |a|`, so
the `tsum` is a finite sum and the box-norm power takes the elementary form

  `‖g‖^{2}_{□¹_Q(S)} = (1/|S|) (1/|Q|)² ∑_{x ∈ ℤ} ‖∑_{a ∈ Q} g (x+a)‖²`.

This is the identity used to peel the first level of the Gowers box norm.

## Main results

* `Work.Peluse.Peel.sum_window_eq_zero_of_not_mem_ball` : off the ball the window sum
  `∑_{a ∈ Q} g (x+a)` vanishes;
* `Work.Peluse.Peel.boxNormPow_one_tsum` : the box-norm power as a `tsum` over `ℤ`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Peel

/-- **Vanishing of the window sum off the box-norm ball.**  If `g` is supported in `[-N,N]` and
`x` is outside `ball 1 (fun _ => Q) N = [-rad, rad]` with `rad = N + ∑_{a ∈ Q} |a|`, then every
term `g (x + a)`, `a ∈ Q`, vanishes: `|x| > rad ≥ N + |a|` forces `|x + a| ≥ |x| - |a| > N`. -/
lemma sum_window_eq_zero_of_not_mem_ball {N : ℕ} {Q : Finset ℤ} {g : ℤ → ℂ}
    (hsupp : Work.Peluse.SupportIn g N) {x : ℤ}
    (hx : x ∉ Work.Peluse.BoxNorm.ball 1 (fun _ : Fin 1 => Q) N) :
    ∑ a ∈ Q, g (x + a) = 0 := by
  have hrad : ((Work.Peluse.BoxNorm.rad 1 (fun _ : Fin 1 => Q) N : ℕ) : ℤ)
      = (N : ℤ) + ∑ a ∈ Q, |a| := by
    rw [show Work.Peluse.BoxNorm.rad 1 (fun _ : Fin 1 => Q) N
        = N + Q.sum (fun z => z.natAbs) from by
      simp [Work.Peluse.BoxNorm.rad]]
    simp
  have hlt : ((Work.Peluse.BoxNorm.rad 1 (fun _ : Fin 1 => Q) N : ℕ) : ℤ) < |x| := by
    rw [Work.Peluse.BoxNorm.ball, Finset.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  refine Finset.sum_eq_zero (fun a ha => hsupp (x + a) ?_)
  have hle : |a| ≤ ∑ a' ∈ Q, |a'| :=
    Finset.single_le_sum (fun i _ => abs_nonneg i) ha
  have hxa : (N : ℤ) < |x + a| := by
    have h1 : |x| ≤ |x + a| + |a| := by
      calc |x| = |(x + a) + (-a)| := by rw [show (x + a) + (-a) = x by ring]
        _ ≤ |x + a| + |-a| := abs_add_le _ _
        _ = |x + a| + |a| := by rw [abs_neg]
    rw [hrad] at hlt
    linarith
  have h2 : (N : ℤ) < (((x + a).natAbs : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    exact hxa
  exact_mod_cast h2

/-- **The first box-norm power over a window, as a `tsum` over `ℤ`.**  For `g` supported in
`[-N,N]`,

  `boxNormPow 1 (fun _ => Q) S g = (1/|S|) (1/|Q|)² ∑'_{x ∈ ℤ} ‖∑_{a ∈ Q} g (x+a)‖²`.

The `tsum` is a finite sum: its summand vanishes off `ball 1 (fun _ => Q) N`. -/
theorem boxNormPow_one_tsum {N : ℕ} (Q : Finset ℤ) (S : Finset ℤ) {g : ℤ → ℂ}
    (hsupp : Work.Peluse.SupportIn g N) :
    Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Q) S g
      = ((S.card : ℝ))⁻¹ * ((Q.card : ℝ))⁻¹ ^ 2
        * ∑' x : ℤ, ‖∑ a ∈ Q, g (x + a)‖ ^ 2 := by
  rw [Work.Peluse.WindowControl.boxNormPow_one_eq_boxScaling_normSqSum Q S g hsupp,
    Work.Peluse.WindowControl.boxScaling_one_eq S Q,
    Work.Peluse.WindowControl.normSqSum_one_eq_sum_ball]
  have h : (∑ x ∈ Work.Peluse.BoxNorm.ball 1 (fun _ : Fin 1 => Q) N,
        ‖∑ a ∈ Q, g (x + a)‖ ^ 2)
      = ∑' x : ℤ, ‖∑ a ∈ Q, g (x + a)‖ ^ 2 := by
    symm
    exact tsum_eq_sum (fun x hx => by
      rw [sum_window_eq_zero_of_not_mem_ball hsupp hx]
      simp)
  rw [h]

end Work.Peluse.Peel
