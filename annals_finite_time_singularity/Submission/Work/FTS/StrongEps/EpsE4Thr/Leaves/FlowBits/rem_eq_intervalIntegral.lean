import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.E4R3.Flow5
import Submission.Work.FTS.EpsEngine.EpsClass
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

/-!
# `rem_eq_intervalIntegral` — the remainder of the fake-time increment is the interval
integral of the (shifted) right-hand side

`rem u v s τ = u s - u τ - (s - τ) • v` is the remainder of the first-order expansion of a curve
of profiles at fake time `τ` with derivative `v` (`E4R5.rem`).  For a family `g` whose fake-time
increment is *volterra* — `g z θ t = g z θ 0 + ∫₀^t Feps (slice g u) z θ du` on `[0,δ]` — the
remainder is exactly the integral over `[τ,s]` of the difference
`Feps (slice g u) - Feps (slice g τ)`.

The proof is the fundamental theorem of calculus in its "interval difference" form: two
primitives differ by the integral over the interval between the two base points, and the integral
of a constant is `(s - τ) • c`.
-/

/-- **Interval difference of a primitive.**  If `F` is a primitive of `f` on `[0,δ]` with base
point `0` (i.e. `F t = C + ∫₀^t f` for `t ∈ [0,δ]`) and `f` is interval integrable on `[0,δ]`,
then for any two points `a`, `b` of `[0,δ]`,
`F b - F a = ∫_a^b f`.

(The extra flexibility of arbitrary *signed* base points is what makes this usable for the
oriented integral `∫_τ^s`: when `s < τ` both sides change sign.) -/
theorem sub_eq_intervalIntegral_of_primitive {f : ℝ → ℝ} {F : ℝ → ℝ} {δ C : ℝ}
    (hF : ∀ t ∈ Set.Icc (0 : ℝ) δ, F t = C + ∫ u in (0 : ℝ)..t, f u)
    (hint : IntervalIntegrable f MeasureTheory.volume 0 δ)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) δ) (hb : b ∈ Set.Icc (0 : ℝ) δ) :
    F b - F a = ∫ u in a..b, f u := by
  have hδ0 : (0 : ℝ) ≤ δ := le_trans ha.1 ha.2
  have hIa : IntervalIntegrable f MeasureTheory.volume 0 a :=
    hint.mono_set (by
      rw [Set.uIcc_of_le ha.1, Set.uIcc_of_le hδ0]
      exact Set.Icc_subset_Icc le_rfl ha.2)
  have hIb : IntervalIntegrable f MeasureTheory.volume 0 b :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hb.1, Set.uIcc_of_le hδ0]
      exact Set.Icc_subset_Icc le_rfl hb.2)
  have hkey := intervalIntegral.integral_interval_sub_left hIb hIa
  rw [← hkey, hF b hb, hF a ha]
  ring

theorem rem_eq_intervalIntegral {α δ ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hvol : ∀ z θ τ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → τ ∈ Set.Icc 0 δ →
      g z θ τ = g z θ 0 + ∫ s in (0 : ℝ)..τ,
        Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ)
    (hint : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      IntervalIntegrable (fun u : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E
        (Work.FTS.Galerkin.slice g u) z θ) MeasureTheory.volume 0 δ)
    {s τ z θ : ℝ} (hs : s ∈ Set.Icc 0 δ) (hτ : τ ∈ Set.Icc 0 δ)
    (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.FTS.StrongEps.EpsE4Thr.E4R5.rem (Work.FTS.Galerkin.slice g)
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ)) s τ z θ
      = ∫ u in τ..s, (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g u) z θ
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ) := by
  have hprim : ∀ t ∈ Set.Icc (0 : ℝ) δ,
      g z θ t = g z θ 0 + ∫ u in (0 : ℝ)..t, Work.FTS.EpsEngine.Feps α ρ ε Φs E
        (Work.FTS.Galerkin.slice g u) z θ := fun t ht => hvol z θ t hzθ ht
  have hdiff : g z θ s - g z θ τ = ∫ u in τ..s, Work.FTS.EpsEngine.Feps α ρ ε Φs E
      (Work.FTS.Galerkin.slice g u) z θ :=
    sub_eq_intervalIntegral_of_primitive hprim (hint z θ hzθ) hτ hs
  -- the integrand is interval integrable on the (oriented) interval `τ..s`
  have hintτs : IntervalIntegrable (fun u : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E
      (Work.FTS.Galerkin.slice g u) z θ) MeasureTheory.volume τ s := by
    refine (hint z θ hzθ).mono_set' ?_
    intro x hx
    rw [Set.mem_uIoc] at hx ⊢
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨lt_of_le_of_lt hτ.1 h1, le_trans h2 hs.2⟩
    · exact Or.inl ⟨lt_of_le_of_lt hs.1 h1, le_trans h2 hτ.2⟩
  have hcint : IntervalIntegrable (fun _ : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E
      (Work.FTS.Galerkin.slice g τ) z θ) MeasureTheory.volume τ s := intervalIntegrable_const
  -- integral of the difference = difference of the integrals = the remainder
  have hsub : ∫ u in τ..s, (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g u) z θ
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ)
      = (g z θ s - g z θ τ) - (s - τ) * Work.FTS.EpsEngine.Feps α ρ ε Φs E
          (Work.FTS.Galerkin.slice g τ) z θ := by
    rw [intervalIntegral.integral_sub hintτs hcint, hdiff.symm, intervalIntegral.integral_const,
      smul_eq_mul]
  rw [hsub]
  simp only [Work.FTS.StrongEps.EpsE4Thr.E4R5.rem, Work.FTS.Galerkin.slice_apply]

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
