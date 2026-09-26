import Mathlib
import Submission.Work.Residues.KernelPoleLocation
import Submission.Work.CKFinal.LineDecay.F1Half.Basic
import Submission.Work.Asymptotics.continuousOn_Kfun_clean

/-!
# Continuity and holomorphy of the shifted kernel `z ↦ K̂(τ, z+1) · e^{iπr²z}`

For the contour shift of the `K̂`-side of the CKMRV functional equation one works with the
*shifted* second variable `ζ = z + 1`, where `z` runs over the left half-strip
`{-1 ≤ Re z ≤ 0, 1 ≤ Im z}`.  On this strip the second variable `z + 1` has real part in
`[0,1]` and imaginary part `≥ 1`, and the hypothesis `hclean` says that on this strip (minus
the single point `z₀`) the kernel stays off its pole divisor, `j τ ≠ j (z + 1)`.

The function `ζ ↦ K̂^{(d)}(τ,ζ)` is meromorphic with poles contained in `{j = j τ}`
(`Work.Residues.mdifferentiableAt_Khat_snd`), and off that divisor it is the *cleared* kernel
divided by `Δ(τ)Δ(ζ)^e(j τ - j ζ)` (`Work.Kernels.ClearLink`).  The cleared kernel is entire,
so on the clean set the shifted kernel is holomorphic; this file assembles that into the two
statements needed for differentiating and integrating contour integrals of the kernel along
the shifted line:

* `ContinuousOn` of `z ↦ K̂(τ, z+1) e^{iπr²z}` on the closed strip minus `z₀`;
* `DifferentiableAt` of the same function at each point of the *open* strip minus `z₀`.
-/

namespace Work.CKFinal.LineDecay

open UpperHalfPlane Filter Topology
open scoped Topology Manifold

namespace KhatShiftContDiff

open Work.Kernels

/-- The growth prefactor of Theorem 4.9(4) does not vanish off the coincidence divisor. -/
lemma growthPrefactor_ne_zero (d : ℕ) {τ z : UpperHalfPlane}
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.growthPrefactor d τ z ≠ 0 := by
  rw [Work.Kernels.growthPrefactor]
  exact mul_ne_zero (mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
    (pow_ne_zero _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z))) (sub_ne_zero.mpr h)

/-- Off the coincidence divisor, `K̂` is the cleared kernel divided by the growth prefactor:
`Δ(τ)Δ(ζ)^e(j τ - j ζ) · K̂(τ,ζ) = K̂^{Clear}(τ,ζ)`. -/
lemma khat_eq_khatClear_div (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ z : UpperHalfPlane} (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.Khat ℓ d τ z
      = Work.Kernels.KhatClear ℓ d τ z / Work.Kernels.growthPrefactor d τ z := by
  rw [eq_div_iff (growthPrefactor_ne_zero d h)]
  rw [Work.Kernels.KhatClear, Work.Kernels.Khat,
    Work.Kernels.ClearLink.KPlusClear_eq_smul d hd τ z h,
    Work.Kernels.ClearLink.KMinusClear_eq_smul ℓ d hd τ z h]
  ring

/-- The exponential factor `e^{iπr²z}` is continuous. -/
lemma continuous_kerExp (r : ℝ) :
    Continuous fun z : ℂ => Work.Asymptotics.kerExp r z := by
  change Continuous fun z : ℂ => Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * z)
  exact ((continuous_const.mul continuous_id).cexp)

/-- The exponential factor `e^{iπr²z}` is entire. -/
lemma differentiable_kerExp (r : ℝ) (z : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ => Work.Asymptotics.kerExp r z) z := by
  change DifferentiableAt ℂ (fun z : ℂ => Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * z)) z
  exact ((differentiableAt_const (c := (Real.pi : ℂ) * Complex.I * (r : ℂ) ^ 2)).mul
    differentiableAt_id).cexp

/-- The growth prefactor is continuous in its second variable. -/
lemma continuous_growthPrefactor_snd (d : ℕ) (τ : UpperHalfPlane) :
    Continuous fun ζ : UpperHalfPlane => Work.Kernels.growthPrefactor d τ ζ := by
  have hΔ : Continuous fun ζ : UpperHalfPlane => Work.Kernels.DeltaFun ζ :=
    Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.1.continuous
  have hj : Continuous fun ζ : UpperHalfPlane => Work.Kernels.jInvariantFun ζ :=
    Work.Asymptotics.continuous_jInvariantFun'
  have h : (fun ζ : UpperHalfPlane => Work.Kernels.growthPrefactor d τ ζ)
      = fun ζ : UpperHalfPlane => Work.Kernels.DeltaFun τ
          * Work.Kernels.DeltaFun ζ ^ (if d = 8 then 1 else 2)
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ) := by
    funext ζ; rw [Work.Kernels.growthPrefactor]
  rw [h]
  exact (continuous_const.mul (hΔ.pow _)).mul (continuous_const.sub hj)

/-- **Continuity of the shifted kernel on a clean set.**  On a set `S` of `z`'s for which the
shifted variable `z + 1` lies in `ℍ` and stays off the coincidence divisor `j τ = j (z+1)`,
the function `z ↦ K̂(τ,z+1) e^{iπr²z}` is continuous.

The proof writes `K̂(τ,ζ) = K̂^{Clear}(τ,ζ)/growthPrefactor(τ,ζ)` off the divisor; the numerator
is `K̂^{Clear}` composed with the entire shift and is holomorphic, the denominator is a
non-vanishing continuous function, and the exponential factor is continuous. -/
lemma continuousOn_khat_shift (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (r : ℝ) (S : Set ℂ)
    (him : ∀ z ∈ S, 0 < (z + 1).im)
    (hj : ∀ z ∈ S, Work.Kernels.jInvariantFun τ ≠
      Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (z + 1))) :
    ContinuousOn (fun z : ℂ => Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex (z + 1))
      * Work.Asymptotics.kerExp r z) S := by
  have hKCdiff : DifferentiableOn ℂ
      (fun u : ℂ => Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex u))
      {u : ℂ | 0 < u.im} :=
    (UpperHalfPlane.mdifferentiable_iff).mp (Work.Kernels.KernelClear_growth_z ℓ d hd τ).2.1
  have hshift : ContinuousOn (fun z : ℂ => z + 1) S :=
    (continuous_id.add continuous_const).continuousOn
  have hmapshift : Set.MapsTo (fun z : ℂ => z + 1) S {u : ℂ | 0 < u.im} := fun z hz => him z hz
  have h₁ : ContinuousOn (fun z : ℂ =>
      Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex (z + 1))) S :=
    hKCdiff.continuousOn.comp hshift hmapshift
  have hgpc : ContinuousOn
      (fun u : ℂ => Work.Kernels.growthPrefactor d τ (UpperHalfPlane.ofComplex u))
      {u : ℂ | 0 < u.im} :=
    (continuous_growthPrefactor_snd d τ).comp_continuousOn
      Work.Asymptotics.continuousOn_ofComplex_of_im_pos
  have h₂ : ContinuousOn (fun z : ℂ =>
      Work.Kernels.growthPrefactor d τ (UpperHalfPlane.ofComplex (z + 1))) S :=
    hgpc.comp hshift hmapshift
  have hne : ∀ z ∈ S, Work.Kernels.growthPrefactor d τ (UpperHalfPlane.ofComplex (z + 1)) ≠ 0 :=
    fun z hz => growthPrefactor_ne_zero d (hj z hz)
  have h₄ := (h₁.div h₂ hne).mul (continuous_kerExp r).continuousOn
  exact h₄.congr (fun z hz => by
    show Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex (z + 1)) * Work.Asymptotics.kerExp r z
      = (Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex (z + 1))
          / Work.Kernels.growthPrefactor d τ (UpperHalfPlane.ofComplex (z + 1)))
        * Work.Asymptotics.kerExp r z
    rw [khat_eq_khatClear_div ℓ d hd (hj z hz)])

/-- **Holomorphy of the shifted kernel at a clean point.**  If `0 < Im (z+1)` and
`j τ ≠ j (z+1)`, then `z ↦ K̂(τ,z+1) e^{iπr²z}` is complex differentiable at `z`. -/
lemma differentiableAt_khat_shift (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (r : ℝ) {z : ℂ} (him : 0 < (z + 1).im)
    (hj : Work.Kernels.jInvariantFun τ ≠
      Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (z + 1))) :
    DifferentiableAt ℂ (fun z : ℂ => Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex (z + 1))
      * Work.Asymptotics.kerExp r z) z := by
  have hcoe : ((UpperHalfPlane.ofComplex (z + 1) : UpperHalfPlane) : ℂ) = z + 1 := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have hMD := Work.Residues.mdifferentiableAt_Khat_snd ℓ d hd τ
    (UpperHalfPlane.ofComplex (z + 1)) hj.symm
  have hdiff₁ : DifferentiableAt ℂ
      (fun u : ℂ => Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex u)) (z + 1) := by
    have h := (UpperHalfPlane.mdifferentiableAt_iff).mp hMD
    rwa [hcoe] at h
  have hdiff₂ : DifferentiableAt ℂ
      (fun w : ℂ => Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex (w + 1))) z :=
    hdiff₁.comp z (differentiableAt_id.add_const 1)
  exact hdiff₂.mul (differentiable_kerExp r z)

end KhatShiftContDiff

/-- **Continuity and holomorphy of the shifted kernel `K̂` on the left strip.**  With `τ` fixed
and the shift `ζ = z + 1` landing in the region `{0 ≤ Re ≤ 1, Im ≥ 1}` of the `ζ`-plane off
the coincidence divisor `j τ = j ζ` (`hclean`), the function `z ↦ K̂^{(d)}(τ, z+1) · e^{iπr²z}`
is continuous on the closed strip `{-1 ≤ Re z ≤ 0, Im z ≥ 1}` minus `z₀`, and is complex
differentiable at every point of the open strip `{-1 < Re z < 0, Im z > 1}` minus `z₀`. -/
theorem khat_shift_cont_diff (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (r : ℝ) {z₀ : ℂ} (hclean : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 0 → 1 ≤ z.im → z ≠ z₀ → Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (z + 1))) : ContinuousOn (fun z : ℂ => Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex (z + 1)) * Work.Asymptotics.kerExp r z) ({z : ℂ | -1 ≤ z.re ∧ z.re ≤ 0 ∧ 1 ≤ z.im} \ {z₀}) ∧ (∀ z : ℂ, -1 < z.re → z.re < 0 → 1 < z.im → z ≠ z₀ → DifferentiableAt ℂ (fun z : ℂ => Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex (z + 1)) * Work.Asymptotics.kerExp r z) z) := by
  constructor
  · refine KhatShiftContDiff.continuousOn_khat_shift ℓ d hd τ r _ ?_ ?_
    · intro z hz
      rcases hz with ⟨hzA, hz0⟩
      simp only [Set.mem_ofPred_eq] at hzA
      obtain ⟨h1, h2, h3⟩ := hzA
      simp only [Complex.add_im, Complex.one_im]
      linarith
    · intro z hz
      rcases hz with ⟨hzA, hz0⟩
      simp only [Set.mem_ofPred_eq] at hzA
      simp only [Set.mem_singleton_iff] at hz0
      obtain ⟨h1, h2, h3⟩ := hzA
      exact hclean z h1 h2 h3 hz0
  · intro z h1 h2 h3 hz0
    refine KhatShiftContDiff.differentiableAt_khat_shift ℓ d hd τ r ?_ ?_
    · simp only [Complex.add_im, Complex.one_im]
      linarith
    · exact hclean z (le_of_lt h1) (le_of_lt h2) (le_of_lt h3) hz0

end Work.CKFinal.LineDecay
