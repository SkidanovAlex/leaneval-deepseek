import Mathlib
import Submission.Work.Drive.N2Lead.starShapedComponents

open scoped Manifold ContDiff Topology
open Set Filter

namespace Work.Drive.N2Lead

noncomputable section

/-- **The kernel of the flattening radial map, in the planar projection.**  With the notation of
`Work.Drive.N2Lead.radFlat` (`Submission/Work/Drive/N2Lead/starShapedComponents.lean`, proved,
`sorry`-free; the map `v ↦ radFlat o r s v` pushes the plane radially towards the round circle of
radius `r` about `o` at time `s`, and scales the vertical part by `1 - smoothTransition s`), if
`fderiv ℝ (radFlat o r s) v` kills `w` (at a point `v` with `proj2 (v - o) ≠ 0`), then the *planar
projection* `proj2 w` is a real multiple of `proj2 (v - o)`.

Proof: `hasDerivAt_radFlat` (same file) gives the derivative of the line
`τ ↦ radFlat o r s (v + τ • w)` at `0` explicitly:
`(1 - σ) • w + σ • ((r / ‖a‖) • pl q - (r * ⟪a, q⟫ / ‖a‖ ^ 3) • pl a)`  with `a = proj2 (v - o)`,
`q = proj2 w`, `σ = Real.smoothTransition s`; it equals `fderiv ℝ (radFlat o r s) v w = 0`.  Apply
the linear map `proj2` to that identity and multiply by `star a`; with `z := star a * q` one gets
`A * z = (σ r / ‖a‖) * re z` where `A = (1 - σ) + σ r / ‖a‖ > 0`, whence `im z = 0` and
`(1 - σ) * re z = 0`: for `σ = 1` this leaves `q ∈ ℝ a`, for `σ < 1` it gives `q = 0` (the case
`s < 1` of the conclusion, with `t = 0`). -/
theorem radFlatKernel {o : E3} {r s : ℝ} (hr : 0 < r) {v w : E3}
    (hv : Work.Drive.N2Lead.proj2 (v - o) ≠ 0)
    (h : fderiv ℝ (Work.Drive.N2Lead.radFlat o r s) v w = 0) :
    ∃ t : ℝ, Work.Drive.N2Lead.proj2 w = t • Work.Drive.N2Lead.proj2 (v - o) := by
  -- Notation: `σ = smoothTransition s`, `a = proj2 (v - o)`, `q = proj2 w`.
  set σ := Real.smoothTransition s with hσdef
  set a : ℂ := proj2 (v - o) with hadef
  set q : ℂ := proj2 w with hqdef
  have ha0 : a ≠ 0 := by rw [hadef]; exact hv
  have hnpos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hσnn : 0 ≤ σ := by rw [hσdef]; exact Real.smoothTransition.nonneg s
  have hσle : σ ≤ 1 := by rw [hσdef]; exact Real.smoothTransition.le_one s
  -- **Step A**: the derivative of the line `τ ↦ radFlat o r s (v + τ • w)` at `0`, computed two
  -- ways (chain rule and `hasDerivAt_radFlat`), and the hypothesis `h`.
  have hdiff : DifferentiableAt ℝ (radFlat o r s) v :=
    (contDiffAt_radFlat o r s hv).differentiableAt (by simp [tpC])
  have hline : HasDerivAt (fun τ : ℝ => v + τ • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  have hF' : HasFDerivAt (radFlat o r s) (fderiv ℝ (radFlat o r s) v) (v + (0 : ℝ) • w) := by
    simpa using hdiff.hasFDerivAt
  have hchain : HasDerivAt (fun τ : ℝ => radFlat o r s (v + τ • w))
      ((fderiv ℝ (radFlat o r s) v) w) 0 :=
    HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := E3) (E := E3) (f := fun τ : ℝ => v + τ • w)
      (f' := w) (0 : ℝ) (l := radFlat o r s) (l' := fderiv ℝ (radFlat o r s) v) hF' hline
  have hexp := hasDerivAt_radFlat (o := o) (r := r) (s := s) (v := v) (w := w) hv
  have hderiv : ((fderiv ℝ (radFlat o r s) v) w) =
      ((1 - σ) • w + σ • ((r / ‖a‖) • pl q - (r * inner ℝ a q / ‖a‖ ^ 3) • pl a)) := by
    have h2 := hchain.unique hexp
    simpa only [← hσdef, ← hadef, ← hqdef] using h2
  have hmain :
      ((1 - σ) • w + σ • ((r / ‖a‖) • pl q - (r * inner ℝ a q / ‖a‖ ^ 3) • pl a)) = 0 := by
    rw [← hderiv]
    exact h
  -- **Step B**: apply the linear projection `proj2`.
  have hplane : (1 - σ) • q + σ • ((r / ‖a‖) • q - (r * inner ℝ a q / ‖a‖ ^ 3) • a) = 0 := by
    have h1 := congrArg (fun x : E3 => proj2 x) hmain
    simpa only [proj2_zero, proj2_add, proj2_sub, proj2_smul, proj2_pl] using h1
  -- **Step C**: collect the two occurrences of `q` on one side.
  have hAB : ((1 - σ) + σ * (r / ‖a‖)) • q = (σ * (r * inner ℝ a q / ‖a‖ ^ 3)) • a := by
    have h := hplane
    rw [smul_sub, smul_smul, smul_smul, ← add_sub_assoc, ← add_smul, sub_eq_zero] at h
    exact h
  -- **Step D**: the coefficient `A` is positive.
  have hApos : 0 < (1 - σ) + σ * (r / ‖a‖) := by
    rcases eq_or_lt_of_le hσle with h1 | h1
    · have h2 : 1 - σ = 0 := by rw [h1]; ring
      rw [h2, zero_add, h1, one_mul]
      exact div_pos hr hnpos
    · have h2 : 0 < 1 - σ := sub_pos.mpr h1
      have h3 : 0 ≤ σ * (r / ‖a‖) := mul_nonneg hσnn (div_nonneg hr.le (norm_nonneg a))
      linarith
  -- **Step E**: solve for `q`.
  have hq : q = (((1 - σ) + σ * (r / ‖a‖))⁻¹ * (σ * (r * inner ℝ a q / ‖a‖ ^ 3))) • a := by
    have h1 : ((1 - σ) + σ * (r / ‖a‖))⁻¹ • (((1 - σ) + σ * (r / ‖a‖)) • q)
        = ((1 - σ) + σ * (r / ‖a‖))⁻¹ • ((σ * (r * inner ℝ a q / ‖a‖ ^ 3)) • a) :=
      congrArg (fun z => ((1 - σ) + σ * (r / ‖a‖))⁻¹ • z) hAB
    rw [smul_smul] at h1
    rw [smul_smul] at h1
    rw [inv_mul_cancel₀ hApos.ne', one_smul] at h1
    exact h1
  exact ⟨_, hq⟩

end

end Work.Drive.N2Lead
