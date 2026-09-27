import Mathlib
import Submission.Work.EQ.orbit_tendsto_lower
import Submission.Work.EQ.orbit_tendsto_upper
import Submission.Work.EQ.sign_uniform

namespace Work.EQ

/-- **The orbit of any `x ∈ (0, 2π)` under a `2π`-equivariant order isomorphism converges to
one of the three fixed points `0, π, 2π`.**

Let `σ : ℝ ≃o ℝ` be strictly increasing, `2π`-periodic in the sense
`σ (θ + 2π) = σ θ + 2π`, with `σ 0 = 0`, `σ π = π`, and no fixed point in `(0,π)` nor in
`(π,2π)`. Then `g θ = σ θ - θ` is continuous, vanishes at `0` and `π`, and is nonzero on
`(0,π)`; a uniform-sign argument (`sign_uniform`) shows `g` has one sign there, and the
monotone-orbit lemmas `orbit_tendsto_upper` / `orbit_tendsto_lower` applied with the fixed
endpoints `a = 0`, `b = π` send the orbit of `x ∈ (0,π)` to `π` respectively `0`.  The same
argument on `(π, 2π)` (endpoints `π`, `2π`, zero set `hfix2`) sends the orbit of `x ∈ (π,2π)`
to `2π` respectively `π`, and `x = π` is a fixed point. -/
theorem sigma_orbit_tendsto_multiple {σ : ℝ ≃o ℝ}
    (hσper : ∀ θ, σ (θ + 2 * Real.pi) = σ θ + 2 * Real.pi)
    (hσ0 : σ 0 = 0) (hσπ : σ Real.pi = Real.pi)
    (hfix1 : ∀ θ, 0 < θ → θ < Real.pi → σ θ ≠ θ)
    (hfix2 : ∀ θ, Real.pi < θ → θ < 2 * Real.pi → σ θ ≠ θ)
    {x : ℝ} (hx0 : 0 < x) (hx2 : x < 2 * Real.pi) :
    ∃ L : ℝ, (L = 0 ∨ L = Real.pi ∨ L = 2 * Real.pi) ∧
      Filter.Tendsto (fun n : ℕ => σ^[n] x) Filter.atTop (nhds L) := by
  have hcont : Continuous σ := σ.continuous
  have hmono : StrictMono σ := σ.strictMono
  -- `σ (2π) = 2π` follows from the periodicity relation at `0`.
  have hσ2π : σ (2 * Real.pi) = 2 * Real.pi := by simpa [hσ0] using hσper 0
  -- On `(0,π)` the function `σ θ - θ` has a uniform sign.
  have hsign1 : (∀ θ, 0 < θ → θ < Real.pi → θ < σ θ) ∨
      (∀ θ, 0 < θ → θ < Real.pi → σ θ < θ) := by
    have h := sign_uniform (f := fun θ => σ θ - θ) (hcont.sub continuous_id)
      (a := 0) (b := Real.pi) Real.pi_pos (by simp [hσ0]) (by simp [hσπ])
      (fun θ h1 h2 => by simp only [sub_ne_zero]; exact hfix1 θ h1 h2)
    rcases h with h | h
    · left; intro θ h1 h2; linarith [h θ h1 h2]
    · right; intro θ h1 h2; linarith [h θ h1 h2]
  -- On `(π,2π)` similarly.
  have hsign2 : (∀ θ, Real.pi < θ → θ < 2 * Real.pi → θ < σ θ) ∨
      (∀ θ, Real.pi < θ → θ < 2 * Real.pi → σ θ < θ) := by
    have h := sign_uniform (f := fun θ => σ θ - θ) (hcont.sub continuous_id)
      (a := Real.pi) (b := 2 * Real.pi) (by linarith [Real.pi_pos]) (by simp [hσπ])
      (by simp [hσ2π]) (fun θ h1 h2 => by simp only [sub_ne_zero]; exact hfix2 θ h1 h2)
    rcases h with h | h
    · left; intro θ h1 h2; linarith [h θ h1 h2]
    · right; intro θ h1 h2; linarith [h θ h1 h2]
  rcases lt_trichotomy x Real.pi with hxlt | hxeq | hxgt
  · -- `0 < x < π`: the orbit is monotone and trapped by the fixed points `0`, `π`.
    rcases hsign1 with hup | hdown
    · exact ⟨Real.pi, Or.inr (Or.inl rfl),
        orbit_tendsto_upper (τ := σ) hcont hmono (a := 0) (b := Real.pi)
          (hab := Real.pi_pos) (ha := hσ0) (hb := hσπ) (hfix := hfix1) (θ := x)
          (hθa := hx0) (hθb := hxlt) (hθ := hup x hx0 hxlt)⟩
    · exact ⟨0, Or.inl rfl,
        orbit_tendsto_lower (τ := σ) hcont hmono (a := 0) (b := Real.pi)
          (hab := Real.pi_pos) (ha := hσ0) (hb := hσπ) (hfix := hfix1) (θ := x)
          (hθa := hx0) (hθb := hxlt) (hθ := hdown x hx0 hxlt)⟩
  · -- `x = π`: the orbit is constant.
    refine ⟨Real.pi, Or.inr (Or.inl rfl), ?_⟩
    rw [hxeq]
    rw [show (fun n : ℕ => σ^[n] Real.pi) = (fun _ => Real.pi) from
      funext (fun n => Function.iterate_fixed hσπ n)]
    exact tendsto_const_nhds
  · -- `π < x < 2π`.
    rcases hsign2 with hup | hdown
    · exact ⟨2 * Real.pi, Or.inr (Or.inr rfl),
        orbit_tendsto_upper (τ := σ) hcont hmono (a := Real.pi) (b := 2 * Real.pi)
          (hab := by linarith [Real.pi_pos]) (ha := hσπ) (hb := hσ2π) (hfix := hfix2)
          (θ := x) (hθa := hxgt) (hθb := hx2) (hθ := hup x hxgt hx2)⟩
    · exact ⟨Real.pi, Or.inr (Or.inl rfl),
        orbit_tendsto_lower (τ := σ) hcont hmono (a := Real.pi) (b := 2 * Real.pi)
          (hab := by linarith [Real.pi_pos]) (ha := hσπ) (hb := hσ2π) (hfix := hfix2)
          (θ := x) (hθa := hxgt) (hθb := hx2) (hθ := hdown x hxgt hx2)⟩

end Work.EQ
