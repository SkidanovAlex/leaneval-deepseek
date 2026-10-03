import Mathlib
import Submission.Work.KMTAreas.A4Z.kappa_sum_le

/-!
# Schur's test for a finite family of `ℓ²(ℤ)` functions

`Work.KMTAreas.A4Z.schur_finite`: given finitely many vectors `u i · : ℤ → ℂ` in `ℓ²(ℤ)` whose
Gram entries `⟨u i, u j⟩ = ∑'_x u i x * conj (u j x)` are bounded by `κ (i - j) * a i * a j` for a
nonnegative summable kernel `κ`, the `ℓ²` norm of `∑_{i ∈ S} u i ·` is at most
`(∑'_m κ m) * ∑_{i ∈ S} a i ^ 2`.

The two ingredients are
* `gram_expansion` (below): the Gram expansion
  `∑'_x ‖∑_{i∈S} u i x‖^2 = ∑_{i,j∈S} Re ⟨u i, u j⟩` of the squared `ℓ²` norm of a finite sum of
  `ℓ²` functions — the cross terms are summable by
  `‖u i x * conj (u j x)‖ = ‖u i x‖ ‖u j x‖ ≤ (‖u i x‖^2 + ‖u j x‖^2)/2`;
* `Work.KMTAreas.A4Z.kappa_sum_le`: the elementary quadratic-form bound
  `∑_{i,j∈S} κ (i-j) a i a j ≤ (∑'_m κ m) * ∑_{i∈S} a i^2` for a nonnegative summable kernel.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A4Z

/-- **Gram expansion.**  If each `u i` (`i ∈ S`) lies in `ℓ²(ℤ)`, then expanding the pointwise
identity `‖∑_{i∈S} u i x‖^2 = ∑_{i,j∈S} (u i x * conj (u j x)).re` and summing over `x` gives the
double sum of the Gram entries. -/
theorem gram_expansion (S : Finset ℤ) (u : ℤ → ℤ → ℂ)
    (hu : ∀ i ∈ S, Summable (fun x : ℤ => ‖u i x‖ ^ 2)) :
    ∑' x : ℤ, ‖∑ i ∈ S, u i x‖ ^ 2
      = ∑ i ∈ S, ∑ j ∈ S, (∑' x : ℤ, u i x * star (u j x)).re := by
  have hN : ∀ i ∈ S, ∀ j ∈ S, Summable (fun x : ℤ => u i x * star (u j x)) := by
    intro i hi j hj
    refine Summable.of_norm_bounded ((hu i hi).add (hu j hj) |>.mul_right (1/2 : ℝ)) (fun x => ?_)
    rw [norm_mul, norm_star]
    have := two_mul_le_add_sq ‖u i x‖ ‖u j x‖
    linarith
  have hre : ∀ i ∈ S, ∀ j ∈ S, Summable (fun x : ℤ => (u i x * star (u j x)).re) :=
    fun i hi j hj => ContinuousLinearMap.summable Complex.reCLM (hN i hi j hj)
  have hkey : ∀ i ∈ S, ∀ j ∈ S,
      (∑' x : ℤ, u i x * star (u j x)).re = ∑' x : ℤ, (u i x * star (u j x)).re :=
    fun i hi j hj => Summable.map_tsum (hN i hi j hj) Complex.reCLM Complex.continuous_re
  have hpt : ∀ x : ℤ, ‖∑ i ∈ S, u i x‖ ^ 2
      = ∑ i ∈ S, ∑ j ∈ S, (u i x * star (u j x)).re := by
    intro x
    have h1 : (↑(‖∑ i ∈ S, u i x‖ ^ 2) : ℂ)
        = (∑ i ∈ S, u i x) * star (∑ j ∈ S, u j x) := by
      rw [← Complex.normSq_eq_norm_sq]
      exact (Complex.mul_conj _).symm
    have h2 := congrArg Complex.re h1
    simpa only [Complex.ofReal_re, star_sum, Finset.sum_mul_sum, Complex.re_sum] using h2
  have h1 : (∑' x : ℤ, ∑ p ∈ S ×ˢ S, (u p.1 x * star (u p.2 x)).re)
      = ∑ p ∈ S ×ˢ S, ∑' x : ℤ, (u p.1 x * star (u p.2 x)).re := by
    have hmem : ∀ p ∈ S ×ˢ S, Summable (fun x : ℤ => (u p.1 x * star (u p.2 x)).re) := by
      intro p hp
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
      exact hre p.1 h1 p.2 h2
    exact Summable.tsum_finsetSum (s := S ×ˢ S) hmem
  rw [tsum_congr hpt]
  rw [show (∑ i ∈ S, ∑ j ∈ S, (∑' x : ℤ, u i x * star (u j x)).re)
      = ∑ i ∈ S, ∑ j ∈ S, ∑' x : ℤ, (u i x * star (u j x)).re from
    Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hkey i hi j hj]
  rw [show (∑' x : ℤ, ∑ i ∈ S, ∑ j ∈ S, (u i x * star (u j x)).re)
      = ∑' x : ℤ, ∑ p ∈ S ×ˢ S, (u p.1 x * star (u p.2 x)).re from
    tsum_congr fun x => (Finset.sum_product S S (fun p => (u p.1 x * star (u p.2 x)).re)).symm]
  rw [h1, Finset.sum_product]

/-- **Schur's test / Cotlar–Stein bound, finite form.** -/
theorem schur_finite (S : Finset ℤ) (u : ℤ → ℤ → ℂ) (a κ : ℤ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hκ : ∀ m, 0 ≤ κ m)
    (hκsum : Summable κ)
    (hu : ∀ i ∈ S, Summable (fun x : ℤ => ‖u i x‖ ^ 2))
    (hpair : ∀ i ∈ S, ∀ j ∈ S, ‖∑' x : ℤ, u i x * star (u j x)‖ ≤ κ (i - j) * a i * a j) :
    ∑' x : ℤ, ‖∑ i ∈ S, u i x‖ ^ 2 ≤ (∑' m : ℤ, κ m) * ∑ i ∈ S, (a i) ^ 2 := by
  rw [gram_expansion S u hu]
  refine le_trans (Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_)
    (kappa_sum_le S a κ ha hκ hκsum)
  exact (Complex.re_le_norm _).trans (hpair i hi j hj)

end Work.KMTAreas.A4Z
