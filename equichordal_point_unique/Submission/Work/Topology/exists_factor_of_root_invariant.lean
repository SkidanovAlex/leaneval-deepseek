import Mathlib

/-!
# Functions invariant under a primitive root of unity are functions of `t ^ d`

Let `f` be analytic on the punctured disc `0 < ‖t‖ < ρ` and suppose that `f (ω * t) = f t` for a
*primitive* `d`-th root of unity `ω`.  Then `f` factors through the `d`-to-`1` covering
`t ↦ t ^ d`: there is `g`, analytic on the punctured disc of radius `ρ ^ d`, with `f t = g (t ^ d)`.

The proof is by descent along the covering `t ↦ t ^ d`, which avoids any Laurent expansion:

* the map `t ↦ t ^ d` is surjective onto the punctured disc of radius `ρ ^ d`, and every preimage
  of a point of that disc that has the right modulus statement lies in the punctured disc of
  radius `ρ` (`exists_root_mem_ball_diff_singleton`);
* two points of the punctured disc with the same `d`-th power differ by a power of `ω`
  (`pow_invariant_fibre_const`), so `f` is constant on the fibres and the descent `g` is
  well defined;
* `t ↦ t ^ d` is a local biholomorphism away from `0` (inverse function theorem for analytic
  functions), so the descended function is analytic (`analyticAt_of_comp_pow`).

## Main results

* `Work.Topology.exists_factor_of_root_invariant`
-/

open Filter Metric
open scoped Topology

namespace Work.Topology

/-- The punctured ball `0 < ‖t‖ < ρ` is open. -/
theorem isOpen_ball_diff_singleton (ρ : ℝ) :
    IsOpen (Metric.ball (0 : ℂ) ρ \ {0}) := by
  rw [Set.sdiff_eq]
  exact Metric.isOpen_ball.inter isClosed_singleton.isOpen_compl

/-- Raising to the `d`-th power maps the punctured ball of radius `ρ` into the punctured ball of
radius `ρ ^ d`. -/
theorem pow_mem_ball_diff_singleton {ρ : ℝ} (hρ : 0 < ρ) {d : ℕ} (hd : 0 < d) {t : ℂ}
    (ht : t ∈ Metric.ball (0 : ℂ) ρ \ {0}) :
    t ^ d ∈ Metric.ball (0 : ℂ) (ρ ^ d) \ {0} := by
  have htn : ‖t‖ < ρ := by
    have h := ht.1
    rwa [Metric.mem_ball, dist_zero_right] at h
  have ht0 : t ≠ 0 := by simpa using ht.2
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_pow]
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hρ.le hd.ne').mpr htn
  · simpa using pow_ne_zero d ht0

/-- Every point `z` of the punctured disc of radius `ρ ^ d` has a `d`-th root `t` whose (automatic)
membership in the punctured disc of radius `ρ` is recorded.  We use the explicit root
`t = z ^ (d⁻¹ : ℂ)` (`Complex.cpow_nat_inv_pow`) and note that `‖t‖ ^ d = ‖z‖ < ρ ^ d`. -/
theorem exists_root_mem_ball_diff_singleton {ρ : ℝ} (hρ : 0 < ρ) {d : ℕ} (hd : 0 < d) (z : ℂ) :
    ∃ t : ℂ, t ^ d = z ∧
      (z ∈ Metric.ball (0 : ℂ) (ρ ^ d) \ {0} → t ∈ Metric.ball (0 : ℂ) ρ \ {0}) := by
  have hdne : d ≠ 0 := hd.ne'
  refine ⟨z ^ ((d : ℂ)⁻¹), Complex.cpow_nat_inv_pow z hdne, ?_⟩
  intro hz
  have hz0 : z ≠ 0 := by simpa using hz.2
  have hznorm : ‖z‖ < ρ ^ d := by
    have h := hz.1
    rwa [Metric.mem_ball, dist_zero_right] at h
  have hpow : ‖z ^ ((d : ℂ)⁻¹)‖ ^ d = ‖z‖ := by
    rw [← norm_pow, Complex.cpow_nat_inv_pow z hdne]
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right]
    have hlt : ‖z ^ ((d : ℂ)⁻¹)‖ ^ d < ρ ^ d := by rw [hpow]; exact hznorm
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hρ.le hdne).mp hlt
  · intro h0
    have hz0' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
    rw [h0, norm_zero, zero_pow hdne] at hpow
    exact hz0' hpow.symm

/-- **`f` is constant on the fibres of `t ↦ t ^ d`.**

If `f (ω * t) = f t` on the punctured disc for a primitive `d`-th root of unity `ω`, then
`t ^ d = s ^ d` (with `t`, `s` in the punctured disc) forces `f t = f s`.  Indeed `(t / s) ^ d = 1`,
so `t / s = ω ^ m` for some `m` by primitivity of `ω`, and `f` is invariant under the iterations
`t ↦ ω * t` because `‖ω‖ = 1`. -/
theorem pow_invariant_fibre_const {ρ : ℝ} (hρ : 0 < ρ) {f : ℂ → ℂ} {d : ℕ} (hd : 0 < d)
    {ω : ℂ} (hω : ω ^ d = 1) (hprim : ∀ m : ℕ, 0 < m → m < d → ω ^ m ≠ 1)
    (hinv : ∀ t : ℂ, t ∈ Metric.ball (0 : ℂ) ρ \ {0} → f (ω * t) = f t)
    {t s : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) ρ \ {0})
    (hs : s ∈ Metric.ball (0 : ℂ) ρ \ {0}) (h : t ^ d = s ^ d) : f t = f s := by
  have hdne : d ≠ 0 := hd.ne'
  have hprimroot : IsPrimitiveRoot ω d := by
    rw [IsPrimitiveRoot.iff_def]
    refine ⟨hω, ?_⟩
    intro l hl
    rw [Nat.dvd_iff_mod_eq_zero]
    by_contra hne
    have hpos : 0 < l % d := Nat.pos_of_ne_zero hne
    have hlt : l % d < d := Nat.mod_lt _ hd
    have hpow : ω ^ (l % d) = 1 := by
      have h1 : ω ^ l = ω ^ (l % d) := by
        conv_lhs => rw [← Nat.mod_add_div l d]
        rw [pow_add, pow_mul, hω]
        simp
      rw [← h1]; exact hl
    exact hprim _ hpos hlt hpow
  have hnorm : ‖ω‖ = 1 := hprimroot.norm'_eq_one hdne
  have hsne : s ≠ 0 := by simpa using hs.2
  have hdiv : (t / s) ^ d = 1 := by
    rw [div_pow, h, div_self (pow_ne_zero _ hsne)]
  haveI : NeZero d := ⟨hdne⟩
  obtain ⟨m, _, hm⟩ := hprimroot.eq_pow_of_pow_eq_one hdiv
  have ht_eq : t = ω ^ m * s := by
    calc t = t / s * s := (div_mul_cancel₀ t hsne).symm
      _ = ω ^ m * s := by rw [hm]
  rw [ht_eq]
  have hωne : ω ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnorm; norm_num at hnorm
  have hiter : ∀ m : ℕ, f (ω ^ m * s) = f s := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have hstep : f (ω ^ (k + 1) * s) = f (ω * (ω ^ k * s)) := by
        congr 1; rw [pow_succ]; ring
      rw [hstep, hinv (ω ^ k * s) ?_, ih]
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_pow, hnorm, one_pow, one_mul]
        have hs1 := hs.1
        rwa [Metric.mem_ball, dist_zero_right] at hs1
      · exact mul_ne_zero (pow_ne_zero _ hωne) hsne
  exact hiter m

/-- **Analyticity of a function whose `d`-th power pullback is analytic.**

If `G (t ^ d) = f t` near a nonzero point `t0` and `f` is analytic at `t0`, then `G` is analytic at
`t0 ^ d`.  This is the analytic inverse function theorem: `t ↦ t ^ d` has nonzero derivative
`d * t0 ^ (d - 1)` at `t0`, so it is a local biholomorphism, and `G` is locally the composition of
`f` with the inverse branch. -/
theorem analyticAt_of_comp_pow {f G : ℂ → ℂ} {d : ℕ} (hd : 0 < d) {t0 : ℂ} (ht0 : t0 ≠ 0)
    (hf : AnalyticAt ℂ f t0) (h : ∀ᶠ t in 𝓝 t0, G (t ^ d) = f t) :
    AnalyticAt ℂ G (t0 ^ d) := by
  have hP : AnalyticAt ℂ (fun t : ℂ => t ^ d) t0 := (analyticAt_id (z := t0)).pow d
  have hderiv : deriv (fun t : ℂ => t ^ d) t0 ≠ 0 := by
    have h1 : deriv (fun t : ℂ => t ^ d) t0 = (d : ℂ) * t0 ^ (d - 1) := by
      have := deriv_fun_pow (f := fun t : ℂ => t) differentiableAt_id (x := t0) d
      simpa using this
    rw [h1]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hd.ne') (pow_ne_zero _ ht0)
  have hcomp : AnalyticAt ℂ (G ∘ fun t : ℂ => t ^ d) t0 := by
    refine hf.congr ?_
    filter_upwards [h] with t ht
    exact ht.symm
  exact (analyticAt_comp_iff_of_deriv_ne_zero hP hderiv).mp hcomp

/-- **A function on a punctured disc invariant under a primitive root of unity is a function of
`t ^ d`.**

Let `f` be analytic on the punctured disc `0 < ‖t‖ < ρ` and suppose that `f (ω * t) = f t` for a
*primitive* `d`-th root of unity `ω` (`ω ^ d = 1` and `ω ^ m ≠ 1` for `0 < m < d`).  Then `f`
factors through the `d`-to-`1` covering `t ↦ t ^ d`: there is `g`, analytic on the punctured disc
of radius `ρ ^ d`, with `f t = g (t ^ d)`.

`f` is constant on the orbits of the cyclic group `⟨ω⟩ ≅ μ_d`, and the fibres of `t ↦ t ^ d` are
exactly these orbits; descend along the covering `t ↦ t ^ d`, which is locally a biholomorphism
away from `0`.  (Equivalently, in the Laurent expansion of `f` only the coefficients of indices
divisible by `d` survive.) -/
theorem exists_factor_of_root_invariant {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) ρ \ {0}))
    {d : ℕ} (hd : 0 < d) {ω : ℂ} (hω : ω ^ d = 1)
    (hprim : ∀ m : ℕ, 0 < m → m < d → ω ^ m ≠ 1)
    (hinv : ∀ t : ℂ, t ∈ Metric.ball (0 : ℂ) ρ \ {0} → f (ω * t) = f t) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) (ρ ^ d) \ {0}) ∧
      ∀ t : ℂ, t ∈ Metric.ball (0 : ℂ) ρ \ {0} → f t = g (t ^ d) := by
  classical
  -- `f` is constant along the fibres of `t ↦ t ^ d`.
  have hfib : ∀ t s : ℂ, t ∈ Metric.ball (0 : ℂ) ρ \ {0} →
      s ∈ Metric.ball (0 : ℂ) ρ \ {0} → t ^ d = s ^ d → f t = f s :=
    fun t s ht hs h => pow_invariant_fibre_const hρ hd hω hprim hinv ht hs h
  -- choose, for every `z`, a `d`-th root; on the punctured disc of radius `ρ ^ d` it lies in the
  -- punctured disc of radius `ρ`.
  let root : ℂ → ℂ :=
    fun z => Classical.choose (exists_root_mem_ball_diff_singleton hρ hd z)
  have hroot_spec : ∀ z, root z ^ d = z ∧
      (z ∈ Metric.ball (0 : ℂ) (ρ ^ d) \ {0} →
        root z ∈ Metric.ball (0 : ℂ) ρ \ {0}) :=
    fun z => Classical.choose_spec (exists_root_mem_ball_diff_singleton hρ hd z)
  -- the descended function
  let g : ℂ → ℂ := fun z => f (root z)
  have hg_apply : ∀ t : ℂ, t ∈ Metric.ball (0 : ℂ) ρ \ {0} → g (t ^ d) = f t := by
    intro t ht
    have htd := pow_mem_ball_diff_singleton hρ hd ht
    have hr' := hroot_spec (t ^ d)
    show f (root (t ^ d)) = f t
    exact hfib _ _ (hr'.2 htd) ht hr'.1
  refine ⟨g, ?_, ?_⟩
  · -- analyticity of the descent
    intro z hz
    have hrz := hroot_spec z
    have ht0 : root z ∈ Metric.ball (0 : ℂ) ρ \ {0} := hrz.2 hz
    have ht0ne : root z ≠ 0 := by simpa using ht0.2
    have hev : ∀ᶠ t in 𝓝 (root z), g (t ^ d) = f t :=
      Filter.eventually_of_mem
        ((isOpen_ball_diff_singleton ρ).mem_nhds ht0) fun t ht => hg_apply t ht
    have hana := analyticAt_of_comp_pow hd ht0ne (hf (root z) ht0) hev
    rwa [hrz.1] at hana
  · -- the factorisation identity
    intro t ht
    exact (hg_apply t ht).symm

end Work.Topology
