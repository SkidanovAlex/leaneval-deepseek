import Mathlib
import Submission.Work.Drive.Mono.Band.BandChartDefs
import Submission.Work.Drive.Mono.Band.BadFaceDefs

namespace Work.Drive.Mono.Band

/-- **A bad point is a point of the chart fibre.**  Let `v, a₀, b₀` be orthonormal and
`n := dirOf τ a₀ b₀` (the unit direction of projective coordinate `τ` in the pair `(a₀,b₀)`).  If the
Gauss normal of the surface of the challenge at `p` is orthogonal to `v ⨯ n` (the "bad point"
condition `⟪v × n, N p⟫ = 0`, i.e. `N p ∈ span{v, n}`), and the projection of the normal to `v^⊥` does
not vanish, then the projective coordinate of that projection is exactly `τ`:

`alphaV ψ v a₀ p / betaV ψ v b₀ p = τ`, and in particular `betaV ψ v b₀ p ≠ 0`.

Proof: `Work.Drive.Mono.Band.mem_span_of_inner_crossE_eq_zero` (in `BadFaceDefs.lean`), applied with
`hv`, `norm_dirOf`, `inner_v_dirOf`, gives `N p ∈ span{v, n}`; write `N p = λ • v + μ • n`; then
`projV p = μ • n` (using `inner_projV_v` and `⟪v,v⟫ = 1`, `⟪v,n⟫ = 0`), `μ ≠ 0` by `hne` and
`norm_dirOf`, and the two coordinate formulae `inner_a₀_dirOf`, `inner_b₀_dirOf` (both in
`BandChartDefs.lean`) give the quotient `τ` and the non-vanishing of `betaV`. -/
theorem badPoint_chart (ψ : Submission.Diffeo) {v a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3}
    (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) {τ : ℝ} {p : ℝ × ℝ}
    (hbad : inner ℝ (Work.Drive.Generic.crossE v (Work.Drive.Mono.Band.dirOf τ a₀ b₀))
      (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) = 0)
    (hne : Work.Drive.Mono.Band.projV (Work.BoxShrink.Pinch.par ψ) v p ≠ 0) :
    Work.Drive.Mono.Band.alphaV ψ v a₀ p / Work.Drive.Mono.Band.betaV ψ v b₀ p = τ ∧
      Work.Drive.Mono.Band.betaV ψ v b₀ p ≠ 0 := by
  set n := dirOf τ a₀ b₀ with hn_def
  have hn : ‖n‖ = 1 := by rw [hn_def]; exact norm_dirOf ha hb hab τ
  have hvn : inner ℝ v n = 0 := by rw [hn_def]; exact inner_v_dirOf hva hvb τ
  have hspan := mem_span_of_inner_crossE_eq_zero hv hn hvn hbad
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hspan
  -- `N p = α • v + β • n`; the projection to `v^⊥` keeps the `β • n` part.
  have hproj : projV (Work.BoxShrink.Pinch.par ψ) v p = β • n := by
    rw [projV, ← hαβ]
    simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv, hvn,
      mul_zero, mul_one, add_zero, one_pow]
    abel
  have hβ : β ≠ 0 := by
    intro hβ0
    exact hne (by rw [hproj, hβ0, zero_smul])
  have hden : ‖τ • a₀ + b₀‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (dirOf_denom_ne_zero ha hb hab τ)
  have halpha : alphaV ψ v a₀ p = β * (τ * (‖τ • a₀ + b₀‖)⁻¹) := by
    rw [alphaV, projVv, hproj, real_inner_smul_right, hn_def,
      inner_a₀_dirOf ha hb hab τ]
  have hbeta : betaV ψ v b₀ p = β * (‖τ • a₀ + b₀‖)⁻¹ := by
    rw [betaV, projVv, hproj, real_inner_smul_right, hn_def,
      inner_b₀_dirOf ha hb hab τ]
  refine ⟨?_, ?_⟩
  · rw [halpha, hbeta]
    field_simp
  · rw [hbeta]
    exact mul_ne_zero hβ (inv_ne_zero hden)

end Work.Drive.Mono.Band
