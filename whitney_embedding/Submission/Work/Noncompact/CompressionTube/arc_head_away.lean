import Mathlib

/-!
# The head of an injective arc's trace stays away from its endpoint

Step (a) of SESSION 29 of `NOTES_new_plan_gate_balls.md` for `exists_side_arc_of_arc_end`: the first
thing the localisation needs is that for `τ < 1` the *head* `w '' Icc 0 τ` of an injective arc whose
endpoint is `q = w 1` is closed and does not contain `q` — i.e. it stays at positive distance from `q`
in any chart.  Proof: the head is the continuous image of the compact `Icc 0 τ`, hence compact, hence
closed (`T2`); and `q = w 1` is not in it because `w` is injective on `Icc 0 1` and `1 ∉ Icc 0 τ`.

This is independent of the spine recursion and of the delegation of `exists_side_arc_of_arc_end`.
-/

set_option linter.unusedSectionVars false

namespace Work.Noncompact.CompressionTube

open Set Topology

variable {M : Type*} [TopologicalSpace M]

/-- **The head of the trace is compact.** -/
theorem isCompact_image_Icc_of_le_one {w : ℝ → M} (hwc : Continuous w) {τ : ℝ}
    (hτ : τ ≤ 1) : IsCompact (w '' Set.Icc (0:ℝ) τ) :=
  (isCompact_Icc (a := (0:ℝ)) (b := τ)).image_of_continuousOn
    (hwc.continuousOn.mono (Set.Icc_subset_Icc_right hτ))

/-- **The head of the trace is closed** (`M` Hausdorff). -/
theorem isClosed_image_Icc_of_le_one [T2Space M] {w : ℝ → M} (hwc : Continuous w) {τ : ℝ}
    (hτ : τ ≤ 1) : IsClosed (w '' Set.Icc (0:ℝ) τ) :=
  (isCompact_image_Icc_of_le_one hwc hτ).isClosed

/-- **The endpoint is not on the head of the trace**, for `τ < 1`. -/
theorem notMem_image_Icc_of_lt_one {w : ℝ → M} (hwi : Set.InjOn w (Set.Icc (0:ℝ) 1))
    {q : M} (hq : w 1 = q) {τ : ℝ} (hτ : τ < 1) : q ∉ w '' Set.Icc (0:ℝ) τ := by
  rintro ⟨t, ht, htw⟩
  have ht1 : t ≤ 1 := le_trans ht.2 hτ.le
  have hmem : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, ht1⟩
  have heq : w t = w 1 := by rw [htw, hq]
  have h1 : t = 1 := hwi hmem (by norm_num) heq
  exact absurd (h1 ▸ ht.2) (not_le.mpr hτ)

/-- **The head of the trace is closed and avoids the endpoint** — the "positive distance" input of
the localisation in `exists_side_arc_of_arc_end`. -/
theorem isClosed_image_Icc_and_notMem {w : ℝ → M} (hwc : Continuous w)
    (hwi : Set.InjOn w (Set.Icc (0:ℝ) 1)) [T2Space M] {q : M} (hq : w 1 = q)
    {τ : ℝ} (hτ : τ < 1) :
    IsClosed (w '' Set.Icc (0:ℝ) τ) ∧ q ∉ w '' Set.Icc (0:ℝ) τ :=
  ⟨isClosed_image_Icc_of_le_one hwc hτ.le, notMem_image_Icc_of_lt_one hwi hq hτ⟩

end Work.Noncompact.CompressionTube
