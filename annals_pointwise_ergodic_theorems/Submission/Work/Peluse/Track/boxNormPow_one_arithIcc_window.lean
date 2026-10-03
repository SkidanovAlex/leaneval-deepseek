import Mathlib
import Submission.Work.Peluse.BoxNormDilation.dilated_directions_ge

/-!
# The first box-norm power for an arithmetic-progression direction set

`Work.Peluse.Peel.boxNormPow_one_tsum` writes the first box-norm power of a function `ψ` supported
in `[-N,N]` as

`‖ψ‖²_{□¹_Q(S)} = |S|⁻¹ |Q|⁻² ∑'_{x : ℤ} ‖∑_{a ∈ Q} ψ (x + a)‖²`,

a `tsum` over all of `ℤ`.  For the direction set `Q = c[H] = arithIcc c H` (`c ≠ 0`), the summand
can be re-indexed as `‖∑_{y ∈ [H]} ψ (x + c y)‖²`, and it vanishes as soon as `|x| > N + H|c|`:
each `ψ (x + c y)` has `|x + c y| ≥ |x| - H|c| > N`, hence is zero by the support hypothesis.  So
the `tsum` collapses to the *finite* sum over the symmetric window `[-N - H|c|, N + H|c|]`:

`‖ψ‖²_{□¹_{c[H]}([-N,N])}
    = |[-N,N]|⁻¹ H⁻² ∑_{x ∈ [-N-H|c|, N+H|c|]} ‖∑_{y ∈ [H]} ψ (x + c y)‖²`.

This is the "level one" normal form used when the direction set is an arithmetic progression; the
window `[-N - H|c|, N + H|c|]` is exactly the set of `x` for which the inner sum can be nonzero.

## Main results

* `Work.Peluse.Track.sum_arithIcc_eq_Icc` : the pointwise re-indexing of the window sum;
* `Work.Peluse.Track.sum_arithIcc_eq_zero_of_not_mem_symIcc` : the vanishing off the window;
* `Work.Peluse.Track.boxNormPow_one_arithIcc_window` : the identity above.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Peluse.Track

/-- **Re-indexing the window sum along an arithmetic progression.**  For `c ≠ 0` the shift set
`c[L] = arithIcc c L` is the injective image of `[L] = {1, …, L}` under `y ↦ c y`, so the window sum
over `c[L]` is the same as the sum over `y ∈ [L]` of `ψ (x + c y)`. -/
lemma sum_arithIcc_eq_Icc {d : ℤ} (hd : d ≠ 0) (H : ℕ) (ψ : ℤ → ℂ) (x : ℤ) :
    ∑ a ∈ Work.Peluse.arithIcc d H, ψ (x + a)
      = ∑ y ∈ Finset.Icc 1 H, ψ (x + d * (y : ℤ)) := by
  rw [Work.Peluse.arithIcc]
  exact Finset.sum_image (f := fun a : ℤ => ψ (x + a)) (g := fun n : ℕ => d * (n : ℤ))
    (s := Finset.Icc 1 H)
    (fun a _ b _ hab => Nat.cast_injective (mul_left_cancel₀ hd hab))

/-- **Vanishing of the window sum off the symmetric window.**  If `ψ` is supported in `[-N,N]` and
`x ∉ symIcc (N + H |d|)`, i.e. `|x| > N + H |d|`, then every term `ψ (x + d y)`, `1 ≤ y ≤ H`,
vanishes: `|d y| ≤ H |d|` gives `|x + d y| ≥ |x| - H|d| > N`. -/
lemma sum_arithIcc_eq_zero_of_not_mem_symIcc {d : ℤ} {H N : ℕ} {ψ : ℤ → ℂ}
    (hsup : Work.Peluse.SupportIn ψ N) {x : ℤ}
    (hx : x ∉ Work.Peluse.symIcc (N + H * d.natAbs)) :
    ∑ y ∈ Finset.Icc 1 H, ψ (x + d * (y : ℤ)) = 0 := by
  refine Finset.sum_eq_zero (fun y hy => hsup _ ?_)
  have hyH : y ≤ H := (Finset.mem_Icc.mp hy).2
  have hMabs : ((N + H * d.natAbs : ℕ) : ℤ) < |x| := by
    rw [Work.Peluse.symIcc, Finset.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hdy : |d * (y : ℤ)| ≤ (H : ℤ) * (d.natAbs : ℤ) := by
    rw [abs_mul, Int.natCast_natAbs, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (y : ℤ))]
    have hyH' : (y : ℤ) ≤ (H : ℤ) := by exact_mod_cast hyH
    nlinarith [abs_nonneg d, (by positivity : (0 : ℤ) ≤ (y : ℤ))]
  have hMN : ((N + H * d.natAbs : ℕ) : ℤ) = (N : ℤ) + (H : ℤ) * (d.natAbs : ℤ) := by
    push_cast; ring
  have key : (N : ℤ) < |x + d * (y : ℤ)| := by
    have h1 : |x| ≤ |x + d * (y : ℤ)| + |d * (y : ℤ)| := by
      have h2 := abs_add_le (x + d * (y : ℤ)) (-(d * (y : ℤ)))
      rw [show x + d * (y : ℤ) + -(d * (y : ℤ)) = x by ring, abs_neg] at h2
      exact h2
    rw [hMN] at hMabs
    linarith
  have h2 : (N : ℤ) < (((x + d * (y : ℤ)).natAbs : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]; exact key
  exact_mod_cast h2

/-- **The first box-norm power for an arithmetic-progression direction set.**  For `d ≠ 0` and `ψ`
supported in `[-N,N]`, the `tsum` of `boxNormPow_one_tsum` collapses to the finite sum over the
window `symIcc (N + H |d|)`:

`‖ψ‖²_{□¹_{d[H]}([-N,N])}
    = |[-N,N]|⁻¹ H⁻² ∑_{x ∈ [-N-H|d|, N+H|d|]} ‖∑_{y ∈ [H]} ψ (x + d y)‖²`. -/
theorem boxNormPow_one_arithIcc_window {d : ℤ} (hd : d ≠ 0) {H : ℕ} (hH : 1 ≤ H) {N : ℕ}
    (ψ : ℤ → ℂ) (hsup : Work.Peluse.SupportIn ψ N) :
    Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Work.Peluse.arithIcc d H)
        (Work.Peluse.symIcc N) ψ
      = ((Work.Peluse.symIcc N).card : ℝ)⁻¹ * ((H : ℝ))⁻¹ ^ 2
        * ∑ x ∈ Work.Peluse.symIcc (N + H * d.natAbs),
            ‖∑ y ∈ Finset.Icc 1 H, ψ (x + d * (y : ℤ))‖ ^ 2 := by
  rw [Work.Peluse.Peel.boxNormPow_one_tsum (N := N) (Q := Work.Peluse.arithIcc d H)
      (S := Work.Peluse.symIcc N) hsup,
    Work.Peluse.BoxNormDilation.card_arithIcc hd H]
  have htsum : (∑' x : ℤ, ‖∑ a ∈ Work.Peluse.arithIcc d H, ψ (x + a)‖ ^ 2)
      = ∑ x ∈ Work.Peluse.symIcc (N + H * d.natAbs),
          ‖∑ y ∈ Finset.Icc 1 H, ψ (x + d * (y : ℤ))‖ ^ 2 := by
    rw [tsum_eq_sum (s := Work.Peluse.symIcc (N + H * d.natAbs)) (fun x hx => by
      rw [sum_arithIcc_eq_Icc hd H ψ x, sum_arithIcc_eq_zero_of_not_mem_symIcc hsup hx]
      simp)]
    exact Finset.sum_congr rfl (fun x _ => by rw [sum_arithIcc_eq_Icc hd H ψ x])
  rw [htsum]

end Work.Peluse.Track
