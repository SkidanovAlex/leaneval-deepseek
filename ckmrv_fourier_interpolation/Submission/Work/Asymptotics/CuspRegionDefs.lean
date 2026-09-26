/-
# The four cusp regions of `𝒟` and the transport of the slashed funnel bound

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022)) reduce the moderate
growth of the `r`-seminorms of `F₂` on the fundamental domain `𝒟` of `Γ(2)` to the funnel
`𝓕 = {τ ∈ 𝒟 : 2 ≤ Im τ}` of its four cusps `∞, 0, 1, -1`.  A neighbourhood of the cusp attached to
`γ ∈ {I, S, TS, T⁻¹S}` is the image under `γ` of the strip `{|Re τ| ≤ 1, Im τ ≥ 2}`, i.e. the set

  `cuspRegion γ = {w : ℍ | (γ⁻¹ • w) ∈ 𝒟 ∧ 2 ≤ (γ⁻¹ • w).im}`

of `Work.Asymptotics.cuspRegion`; for `γ = 1` this is exactly the funnel `𝓕`.

This file only contains the definition and its elementary API; the transport of the *slashed*
funnel bound to a seminorm bound for `K` itself on `cuspRegion γ` is
`Work.Asymptotics.seminorm_on_cuspRegion_of_slashed`.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-- **The cusp region attached to `γ`**: the set of `w ∈ ℍ` whose `γ⁻¹`-image lies in the funnel
`𝓕 = {τ ∈ 𝒟 : 2 ≤ Im τ}`.  For `γ = 1` this is the funnel itself; for `γ = S, TS, T⁻¹S` it is a
neighbourhood of the cusp `0`, `1`, `-1` of `𝒟`. -/
def cuspRegion (γ : SL(2,ℤ)) : Set ℍ :=
  {w : ℍ | (γ⁻¹ • w) ∈ Work.Asymptotics.DomainD ∧ 2 ≤ (γ⁻¹ • w).im}

lemma mem_cuspRegion {γ : SL(2,ℤ)} {w : ℍ} :
    w ∈ cuspRegion γ ↔ (γ⁻¹ • w) ∈ Work.Asymptotics.DomainD ∧ 2 ≤ (γ⁻¹ • w).im := Iff.rfl

/-- The funnel is the cusp region of `γ = 1`. -/
lemma cuspRegion_one : cuspRegion (1 : SL(2,ℤ)) = {w : ℍ | w ∈ Work.Asymptotics.DomainD ∧ 2 ≤ w.im} := by
  ext w
  simp [mem_cuspRegion]

/-- `γ` maps the funnel into the cusp region of `γ`. -/
lemma smul_mem_cuspRegion {γ : SL(2,ℤ)} {τ : ℍ}
    (hτ : τ ∈ Work.Asymptotics.DomainD ∧ 2 ≤ τ.im) : γ • τ ∈ cuspRegion γ := by
  rw [mem_cuspRegion]
  have h : γ⁻¹ • (γ • τ) = τ := by
    rw [← mul_smul, inv_mul_cancel, one_smul]
  rw [h]
  exact hτ

end Work.Asymptotics
