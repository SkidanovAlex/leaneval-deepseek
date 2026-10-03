import Mathlib
import Submission.Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow

/-!
# The window of the one-dimensional box norm is the interval `[-2N, 2N]`

For the one-dimensional box norm the sum over `x` is taken over the interval
`ball 1 (fun _ => Q0) N = [-rad, rad]` with `rad = N + ∑_{a ∈ Q0} |a|`
(`Work.Peluse.BoxNorm.ball`, `Work.Peluse.BoxNorm.rad`).  In the window-control step the
`x`-sum is instead taken over the fixed interval `[-2N, 2N]`, obtained from the support
hypotheses alone:

* `g` is supported in `[-N,N]` (`Work.Peluse.SupportIn g N`), and
* every `a ∈ Q0` satisfies `|a| ≤ N`;

so the term `∑_{a ∈ Q0} g (x + a)` can only be nonzero when `x` lies at distance at most
`N + |a| ≤ 2N` from the origin — and also at most `rad`, since `|a| ≤ ∑_{a' ∈ Q0} |a'|`.
Hence the two sums agree: the summand vanishes off `ball ∩ [-2N,2N]`, and both sums are the
sum over that intersection.

The main content of the file is the first lemma: the sum `∑_{a ∈ Q0} g (x+a)` can only be
nonzero when `|x| ≤ N + |a|` for some `a ∈ Q0`.
-/

namespace Work.Peluse.WindowControl

/-- **Vanishing of the window sum away from the window.**  If `g` is supported in `[-N, N]` and
`∑_{a ∈ Q0} g (x + a) ≠ 0`, then `|x| ≤ N + |a|` for some `a ∈ Q0`: any non-zero term in the sum
comes from an `a` with `|x + a| ≤ N`, and `|x| ≤ |x + a| + |a|`. -/
lemma sum_window_ne_zero_le {N : ℕ} {Q0 : Finset ℤ} {g : ℤ → ℂ}
    (hsupp : Work.Peluse.SupportIn g N) {x : ℤ}
    (hne : (∑ a ∈ Q0, g (x + a)) ≠ 0) :
    ∃ a ∈ Q0, |x| ≤ (N : ℤ) + |a| := by
  obtain ⟨a, ha, hga⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine ⟨a, ha, ?_⟩
  have hxa : |x + a| ≤ (N : ℤ) := by
    by_contra h
    rw [not_le] at h
    refine hga (hsupp (x + a) ?_)
    have hh := Int.natCast_natAbs (x + a)
    rw [← hh] at h
    exact_mod_cast h
  calc |x| = |(x + a) + (-a)| := by rw [show (x + a) + (-a) = x by ring]
    _ ≤ |x + a| + |-a| := abs_add_le _ _
    _ = |x + a| + |a| := by rw [abs_neg]
    _ ≤ (N : ℤ) + |a| := by linarith

/-- **The window-control identity.**  If `Q0 ⊆ [-N,N]` and `g` is supported in `[-N,N]`, then the
`x`-sum of `‖∑_{a ∈ Q0} g (x+a)‖^2` over the box-norm ball `ball 1 (fun _ => Q0) N` equals the
sum over the fixed interval `[-2N, 2N]`. -/
theorem sum_ball_eq_sum_Icc {N : ℕ} (Q0 : Finset ℤ) (g : ℤ → ℂ)
    (hbd : ∀ a ∈ Q0, |a| ≤ (N : ℤ)) (hsupp : Work.Peluse.SupportIn g N) :
    ∑ x ∈ Work.Peluse.BoxNorm.ball 1 (fun _ : Fin 1 => Q0) N, ‖∑ a ∈ Q0, g (x + a)‖ ^ 2
      = ∑ x ∈ Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)), ‖∑ a ∈ Q0, g (x + a)‖ ^ 2 := by
  set F : ℤ → ℝ := fun x => ‖∑ a ∈ Q0, g (x + a)‖ ^ 2 with hF
  -- the radius of the ball, computed: `rad = N + ∑_{a ∈ Q0} |a|`
  have hrad : ((Work.Peluse.BoxNorm.rad 1 (fun _ : Fin 1 => Q0) N : ℕ) : ℤ)
      = (N : ℤ) + ∑ a ∈ Q0, |a| := by
    rw [show Work.Peluse.BoxNorm.rad 1 (fun _ : Fin 1 => Q0) N = N + Q0.sum (fun z => z.natAbs
      ) from by simp [Work.Peluse.BoxNorm.rad]]
    simp
  -- where the summand can be nonzero: `|x| ≤ N + |a|` for some `a ∈ Q0`
  have key : ∀ x : ℤ, (∑ a ∈ Q0, g (x + a)) ≠ 0 → |x| ≤ (N : ℤ) + ∑ a ∈ Q0, |a| := by
    intro x hne
    obtain ⟨a, ha, hxa⟩ := sum_window_ne_zero_le hsupp hne
    have hle : |a| ≤ ∑ a' ∈ Q0, |a'| :=
      Finset.single_le_sum (fun i _ => abs_nonneg i) ha
    linarith
  have hne_of_F : ∀ x : ℤ, F x ≠ 0 → (∑ a ∈ Q0, g (x + a)) ≠ 0 := by
    intro x hx h0
    exact hx (by rw [hF]; simp [h0])
  -- membership in the two windows, as bounds on `|x|`
  have hmemBall : ∀ x : ℤ, x ∈ Work.Peluse.BoxNorm.ball 1 (fun _ : Fin 1 => Q0) N ↔
      |x| ≤ ((Work.Peluse.BoxNorm.rad 1 (fun _ : Fin 1 => Q0) N : ℕ) : ℤ) := by
    intro x
    rw [Work.Peluse.BoxNorm.ball, Finset.mem_Icc]
    exact abs_le.symm
  have hmemIcc : ∀ x : ℤ, x ∈ Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)) ↔
      |x| ≤ 2 * (N : ℤ) := by
    intro x
    rw [Finset.mem_Icc]
    exact abs_le.symm
  -- the summand vanishes off `ball ∩ [-2N,2N]`, on both sides
  have hzero1 : ∀ x ∈ Work.Peluse.BoxNorm.ball 1 (fun _ : Fin 1 => Q0) N,
      x ∉ Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)) → F x = 0 := by
    intro x _ hxnot
    by_contra hne
    have hlt : 2 * (N : ℤ) < |x| := not_le.mp (fun h => hxnot ((hmemIcc x).mpr h))
    obtain ⟨a, ha, hxa⟩ := sum_window_ne_zero_le hsupp (hne_of_F x hne)
    have := hbd a ha
    linarith
  have hzero2 : ∀ x ∈ Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)),
      x ∉ Work.Peluse.BoxNorm.ball 1 (fun _ : Fin 1 => Q0) N → F x = 0 := by
    intro x _ hxnot
    by_contra hne
    have hlt : ((Work.Peluse.BoxNorm.rad 1 (fun _ : Fin 1 => Q0) N : ℕ) : ℤ) < |x| :=
      not_le.mp (fun h => hxnot ((hmemBall x).mpr h))
    have hkey := key x (hne_of_F x hne)
    rw [hrad] at hlt
    linarith
  -- both sums are the sum over the intersection
  have hsum : ∑ x ∈ Work.Peluse.BoxNorm.ball 1 (fun _ : Fin 1 => Q0) N, F x
      = ∑ x ∈ Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)), F x := by
    have h1 : ∑ x ∈ Work.Peluse.BoxNorm.ball 1 (fun _ : Fin 1 => Q0) N
          ∩ Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)), F x
        = ∑ x ∈ Work.Peluse.BoxNorm.ball 1 (fun _ : Fin 1 => Q0) N, F x :=
      Finset.sum_subset Finset.inter_subset_left (fun x hx hxnot =>
        hzero1 x hx (fun h => hxnot (Finset.mem_inter.mpr ⟨hx, h⟩)))
    have h2 : ∑ x ∈ Work.Peluse.BoxNorm.ball 1 (fun _ : Fin 1 => Q0) N
          ∩ Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)), F x
        = ∑ x ∈ Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)), F x :=
      Finset.sum_subset Finset.inter_subset_right (fun x hx hxnot =>
        hzero2 x hx (fun h => hxnot (Finset.mem_inter.mpr ⟨h, hx⟩)))
    exact h1.symm.trans h2
  exact hsum

end Work.Peluse.WindowControl
