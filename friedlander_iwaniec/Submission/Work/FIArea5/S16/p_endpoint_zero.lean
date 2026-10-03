import Mathlib

set_option linter.unusedVariables false

namespace Work.FIArea5.S16

/-- Endpoint vanishing for a nonnegative `C²` function `p` whose support is contained
in the interval `(N, (1+θ)·N]`.

Since `p ≥ 0` and `p N = p ((1+θ)·N) = 0`, both endpoints are global minima of `p`,
so (by Fermat's theorem, `IsLocalMin.deriv_eq_zero`) the derivative vanishes there.
`p N = 0` is immediate from the support condition; `p ((1+θ)·N) = 0` follows from
continuity, because the support condition forces `p` to vanish on the open ray
`((1+θ)·N, ∞)` and this ray accumulates at `(1+θ)·N`. -/
theorem p_endpoint_zero (p : ℝ → ℝ) (N θ : ℝ) (hN : 0 < N)
    (hpC : ContDiff ℝ 2 p) (hp0 : ∀ u, 0 ≤ p u)
    (hsupp : ∀ u, p u ≠ 0 → N < u ∧ u ≤ (1 + θ) * N) :
    p N = 0 ∧ p ((1 + θ) * N) = 0 ∧ deriv p N = 0 ∧ deriv p ((1 + θ) * N) = 0 := by
  have hcont : Continuous p := hpC.continuous
  -- `p N = 0`: if `p N ≠ 0` then the support condition would give `N < N`.
  have hpN : p N = 0 := by
    by_contra h
    exact absurd (hsupp N h).1 (lt_irrefl N)
  -- `p M = 0` for `M = (1+θ)*N`: `p` vanishes on the open ray `(M, ∞)`, whose closure
  -- contains `M`; since `{p = 0}` is closed, `p M = 0`.
  have hpM : p ((1 + θ) * N) = 0 := by
    have hclosed : IsClosed {u : ℝ | p u = 0} := isClosed_singleton.preimage hcont
    have hsub : Set.Ioi ((1 + θ) * N) ⊆ {u : ℝ | p u = 0} := by
      intro u hu
      by_contra h
      exact absurd (hsupp u h).2 (not_le.mpr hu)
    have hmem : (1 + θ) * N ∈ closure (Set.Ioi ((1 + θ) * N)) := by
      have h : closure (Set.Ioi ((1 + θ) * N)) = Set.Ici ((1 + θ) * N) :=
        closure_Ioi ((1 + θ) * N)
      rw [h]; exact le_refl ((1 + θ) * N)
    have h2 : (1 + θ) * N ∈ closure {u : ℝ | p u = 0} := closure_mono hsub hmem
    rw [hclosed.closure_eq] at h2
    simpa using h2
  -- Both endpoints are global minima of `p`; Fermat's theorem gives vanishing derivatives.
  have hminN : IsLocalMin p N :=
    IsMinOn.isLocalMin (isMinOn_iff.mpr (fun x _ => by rw [hpN]; exact hp0 x)) Filter.univ_mem
  have hminM : IsLocalMin p ((1 + θ) * N) :=
    IsMinOn.isLocalMin (isMinOn_iff.mpr (fun x _ => by rw [hpM]; exact hp0 x)) Filter.univ_mem
  exact ⟨hpN, hpM, hminN.deriv_eq_zero, hminM.deriv_eq_zero⟩

end Work.FIArea5.S16
