import Mathlib

open scoped Topology

namespace Work.Drive.N2

/-- If `β` is `C^n` everywhere, `h` is `C^n` on an open set `s`, and the (topological) support of
`β` is contained in `s`, then the pointwise product `β * h` is `C^n` everywhere.

Outside `s`, `β` vanishes identically (its support is contained in `s`), so the product is `0`;
on `s` it is a product of two `C^n` functions. -/
theorem contDiff_mul_of_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {β h : E → ℝ} {s : Set E}
    (hβ : ContDiff ℝ n β) (hh : ContDiffOn ℝ n h s) (hs : IsOpen s) (hsub : tsupport β ⊆ s) :
    ContDiff ℝ n (fun y => β y * h y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ s
  · -- On `s` the product is the product of two `C^n` functions.
    have hmem : s ∈ 𝓝 x := hs.mem_nhds hx
    simpa only [Pi.mul_apply] using hβ.contDiffAt.mul (hh.contDiffAt hmem)
  · -- Outside `s`, `β` vanishes on a neighbourhood of `x`.
    have hx' : x ∉ tsupport β := fun h => hx (hsub h)
    have hnhds : (fun y => β y * h y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_closure.isOpen_compl).mem_nhds (by rwa [tsupport] at hx')] with y hy
      have hy0 : β y = 0 := by
        by_contra hne
        exact hy (subset_closure (Function.mem_support.mpr hne))
      rw [hy0, zero_mul]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hnhds

end Work.Drive.N2
