import Mathlib
import Submission.Work.Drive.N2.roundConfigDefs
import Submission.Work.N2C.reparamOnRoundCircle

namespace Work.Drive.N2Lead

open scoped ContDiff Topology

/-- **Smooth (`C^∞`, not analytic) reparametrisation of a curve drawn on a round circle.**

`E : ℝ → ℝ³` is a `C^∞` `1`-periodic closed curve whose image lies in the circle of centre `c` and
positive radius `r`, is injective modulo the period and is immersive.  Then there is a `C^∞` change of
parameter `h : ℝ → ℝ` which is a bijection of `ℝ`, commutes with the period
(`h (x+1) = h x ± 1`), has nowhere vanishing derivative, and reads `E` as *exactly* the round
picture at unit speed: `E (h x) = c + r • roundPic (2 * Real.pi * x)`.

The smoothness level is `((⊤ : ℕ∞) : WithTop ℕ∞)` (plain `C^∞`), deliberately NOT the bare `⊤` of
`ContDiff ℝ ⊤`, which in this library means *analytic*.

Proof route (spelled out so no further design decisions are needed): write `E = c + r • (a, b, 0)`
with `a, b` smooth `1`-periodic and `a² + b² = 1`; then `ω := a * deriv b - b * deriv a` is nowhere
zero (if it vanished at `x`, then together with `a * deriv a + b * deriv b = 0` — the derivative of
the constant `a² + b² = 1` — the invertible system `[[a,b],[b,-a]] (a',b')ᵀ = 0` forces `a' = b' = 0`,
hence `fderiv ℝ E x = 0`, against immersivity).  Lift the argument: `θ := θ₀ + ∫₀ˣ ω` with
`cos θ₀ = a 0`, `sin θ₀ = b 0` (exists by `him` at `0`) satisfies `cos ∘ θ = a`, `sin ∘ θ = b`: the two
combinations `a cos θ + b sin θ` and `b cos θ - a sin θ` have vanishing derivative and the right
values at `0`, so `[[a,b],[b,-a]] (cos θ, sin θ)ᵀ = (1,0)ᵀ` and the matrix is invertible.  Then
`deriv θ = ω ≠ 0` and `θ (x + 1) = θ x + δ * 2π` with `δ = ±1`: the difference `x ↦ θ (x+1) - θ x` is
continuous with values in `(2π) • ℤ`, hence constant on the connected `ℝ`; the value `0` and the
values `±2kπ`, `k ≥ 2`, are excluded by `hinj` (intermediate value property).  Finally
`h := (Function.invFun θ) ∘ (fun x => 2 * Real.pi * x)`; the inverse of a strictly monotone `C^∞`
function with nonvanishing derivative is `C^∞` (inverse function results
`ContDiffAt.to_localInverse`, `HasStrictDerivAt.to_local_left_inverse`,
`Function.leftInverse_invFun`). -/
theorem roundImageReparamCinf {E : ℝ → EuclideanSpace ℝ (Fin 3)} {c : EuclideanSpace ℝ (Fin 3)}
    {r : ℝ} (hr : 0 < r) (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E)
    (him : ∀ x : ℝ, ∃ t : ℝ, E x = c + r • Work.Drive.N2.roundPic t)
    (hper : ∀ x : ℝ, E (x + 1) = E x)
    (hinj : ∀ x y : ℝ, E x = E y → ∃ k : ℤ, y = x + k)
    (himm : ∀ x : ℝ, fderiv ℝ E x ≠ 0) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧
      (∀ x, E (h x) = c + r • Work.Drive.N2.roundPic (2 * Real.pi * x)) ∧
      Function.Injective h ∧ Function.Surjective h ∧ (∀ x, deriv h x ≠ 0) ∧
      ∃ δ : ℝ, (δ = 1 ∨ δ = -1) ∧ ∀ x, h (x + 1) = h x + δ := by
  -- ### The curve is injective on the fundamental domain `[0,1)`
  have hInjOn : Set.InjOn E (Set.Ico 0 1) := by
    intro x hx y hy hxy
    obtain ⟨k, hk⟩ := hinj x y hxy
    have hk1 : (k : ℝ) < 1 := by linarith [hx.1, hx.2, hy.1, hy.2, hk]
    have hk2 : (-1 : ℝ) < (k : ℝ) := by linarith [hx.1, hx.2, hy.1, hy.2, hk]
    have hk0 : k = 0 := by
      have h1 : k ≤ 0 := by
        by_contra h
        have h2 : (1 : ℤ) ≤ k := by omega
        have h3 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h2
        linarith
      have h2 : 0 ≤ k := by
        by_contra h
        have h3 : k ≤ (-1 : ℤ) := by omega
        have h4 : (k : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h3
        linarith
      omega
    rw [hk0] at hk
    simpa using hk.symm
  -- ### The derivative of `E` never vanishes
  have hderiv : ∀ x : ℝ, deriv E x ≠ 0 := by
    intro x hx0
    refine himm x (ContinuousLinearMap.ext_ring ?_)
    simpa using hx0
  -- ### The analytic-circle input
  obtain ⟨τ, φ, ε, hε, hτcd, hτper, hτsurj, hτinj, hτder, hτarg⟩ :=
    Work.N2C.reparamOnRoundCircle (g := E) (pos := c) (rad := r) hE hper hInjOn hderiv hr him
  -- ### Absorb the phase `φ` into the parameter
  refine ⟨fun x => τ (x - φ / (2 * Real.pi)), ?hcd, ?harg, ?hinj, ?hsurj, ?hder, (ε : ℝ), ?hδ, ?hper⟩
  · have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ => x - φ / (2 * Real.pi)) := contDiff_id.sub contDiff_const
    exact hτcd.comp hlin
  · intro x
    rw [hτarg (x - φ / (2 * Real.pi))]
    congr 1
    rw [show φ + 2 * Real.pi * (x - φ / (2 * Real.pi)) = 2 * Real.pi * x by
      field_simp
      ring]
  · intro x y hxy
    exact sub_left_injective (hτinj hxy)
  · intro y
    obtain ⟨z, hz⟩ := hτsurj y
    refine ⟨z + φ / (2 * Real.pi), ?_⟩
    change τ (z + φ / (2 * Real.pi) - φ / (2 * Real.pi)) = y
    rw [show z + φ / (2 * Real.pi) - φ / (2 * Real.pi) = z by ring]
    exact hz
  · intro x
    rw [deriv_comp_sub_const]
    exact hτder _
  · rcases hε with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num
  · intro x
    change τ (x + 1 - φ / (2 * Real.pi)) = τ (x - φ / (2 * Real.pi)) + (ε : ℝ)
    rw [show x + 1 - φ / (2 * Real.pi) = (x - φ / (2 * Real.pi)) + 1 by ring, hτper]


end Work.Drive.N2Lead
