import Mathlib

namespace Work.LinnikAreas.Density4

/-- Double-counting identity for a divisor sum over a box.

The left side sums `F d (δ / d)` over all pairs `(δ, d)` with `δ ∈ I` and `d ∣ δ`; the right
side sums `F d e` over the pairs `(d, e)` in the box `[1, M]²` with `d * e ∈ I` (and `0`
otherwise).  The identity is the bijection `(δ, d) ↦ (d, δ / d)`: for `δ ∈ I` and `d ∈ δ.divisors`
both `d` and `δ / d` lie in `[1, M]` since `δ ≤ M`, and conversely if `d, e ∈ [1, M]` with
`d * e ∈ I` then `d ∣ d * e` and `d * e ≤ M` forces `d, e ≤ M`.  Elements with `δ = 0` contribute
nothing to either side because `Nat.divisors 0 = ∅`. -/
theorem box_divisor_identity (I : Finset ℕ) (M : ℕ) (hI : ∀ δ ∈ I, δ ≤ M) (F : ℕ → ℕ → ℝ) :
    (∑ δ ∈ I, ∑ d ∈ δ.divisors, F d (δ / d))
      = ∑ d ∈ Finset.Icc 1 M, ∑ e ∈ Finset.Icc 1 M,
          (if d * e ∈ I then F d e else 0) := by
  classical
  -- Rewrite the right side as a sum over the filtered box, so that the two sides are sums over
  -- the respective sigma types of a single pair-summand.
  have hR : (∑ d ∈ Finset.Icc 1 M, ∑ e ∈ Finset.Icc 1 M,
        (if d * e ∈ I then F d e else 0))
      = ∑ d ∈ Finset.Icc 1 M, ∑ e ∈ (Finset.Icc 1 M).filter (fun e => d * e ∈ I), F d e := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.sum_filter (fun e => d * e ∈ I) (fun e => F d e)]
  rw [hR, Finset.sum_sigma', Finset.sum_sigma']
  -- The bijection `(δ, d) ↦ (d, δ / d)`.
  refine Finset.sum_bij (fun x _ => (⟨x.2, x.1 / x.2⟩ : Sigma fun _ : ℕ => ℕ)) ?_ ?_ ?_ ?_
  · -- the map lands in the right sigma type
    intro x hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hxI, hxd⟩ := hx
    rw [Nat.mem_divisors] at hxd
    obtain ⟨hdvd, hxne⟩ := hxd
    have hx1pos : 0 < x.1 := Nat.pos_of_ne_zero hxne
    have hx2pos : 0 < x.2 := Nat.pos_of_dvd_of_pos hdvd hx1pos
    have hx2le : x.2 ≤ x.1 := Nat.le_of_dvd hx1pos hdvd
    have hx1M : x.1 ≤ M := hI x.1 hxI
    rw [Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_Icc]; exact ⟨hx2pos, le_trans hx2le hx1M⟩
    · rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_Icc]
        exact ⟨(Nat.one_le_div_iff hx2pos).mpr hx2le, le_trans (Nat.div_le_self x.1 x.2) hx1M⟩
      · rw [Nat.mul_div_cancel' hdvd]; exact hxI
  · -- injectivity
    intro x1 hx1 x2 hx2 heq
    rw [Finset.mem_sigma] at hx1 hx2
    obtain ⟨_, hx1d⟩ := hx1
    obtain ⟨_, hx2d⟩ := hx2
    rw [Nat.mem_divisors] at hx1d hx2d
    obtain ⟨hdvd1, _⟩ := hx1d
    obtain ⟨hdvd2, _⟩ := hx2d
    rw [Sigma.mk.injEq] at heq
    obtain ⟨h2, h1⟩ := heq
    have h1' : x1.1 / x1.2 = x2.1 / x2.2 := eq_of_heq h1
    have ha : x1.1 = x2.1 := by
      rw [← Nat.mul_div_cancel' hdvd1, ← Nat.mul_div_cancel' hdvd2, h1', h2]
    exact Sigma.ext ha (heq_of_eq h2)
  · -- surjectivity
    intro y hy
    rw [Finset.mem_sigma] at hy
    obtain ⟨hdIcc, hefilt⟩ := hy
    rw [Finset.mem_filter] at hefilt
    obtain ⟨heIcc, hdeI⟩ := hefilt
    rw [Finset.mem_Icc] at hdIcc heIcc
    obtain ⟨hd1, _⟩ := hdIcc
    obtain ⟨he1, _⟩ := heIcc
    refine ⟨⟨y.1 * y.2, y.1⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      refine ⟨hdeI, ?_⟩
      rw [Nat.mem_divisors]
      exact ⟨dvd_mul_right y.1 y.2, Nat.mul_ne_zero (by omega) (by omega)⟩
    · exact Sigma.ext rfl (heq_of_eq (Nat.mul_div_right y.2 hd1))
  · -- the summands agree
    intro x hx
    rfl

end Work.LinnikAreas.Density4
