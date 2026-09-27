import Mathlib

namespace Work.EQ

open Filter
open scoped Topology

set_option linter.unusedVariables false

/-- If `f` is meromorphic at `x` and is bounded (by `C`) along a sequence `t n → x`
(approaching `x` inside the punctured neighbourhood), then `f` has no pole at `x`:
its meromorphic order at `x` is nonnegative.

Route: if the order were negative, `f` would tend to infinity (`cobounded`) at `x`,
so along the sequence `‖f (t n)‖ → ∞`, contradicting the uniform bound `‖f (t n)‖ ≤ C`. -/
theorem meromorphicOrderAt_nonneg_of_seq_bounded {f : ℂ → ℂ} {x : ℂ} {t : ℕ → ℂ} {C : ℝ}
    (hf : MeromorphicAt f x) (ht : Filter.Tendsto t Filter.atTop (nhdsWithin x {x}ᶜ))
    (h : ∀ n, ‖f (t n)‖ ≤ C) : 0 ≤ meromorphicOrderAt f x := by
  by_contra hc
  rw [not_le] at hc
  -- a negative order forces `f` to blow up at `x`
  have hcob : Filter.Tendsto f (nhdsWithin x {x}ᶜ) (Bornology.cobounded ℂ) :=
    tendsto_cobounded_of_meromorphicOrderAt_neg hc
  have hnorm : Filter.Tendsto (fun z => ‖f z‖) (nhdsWithin x {x}ᶜ) atTop :=
    tendsto_norm_atTop_iff_cobounded.2 hcob
  have hcomp : Filter.Tendsto (fun n => ‖f (t n)‖) Filter.atTop atTop := hnorm.comp ht
  have hgt : ∀ᶠ n in Filter.atTop, C < ‖f (t n)‖ := hcomp.eventually (eventually_gt_atTop C)
  have hle : ∀ᶠ n in Filter.atTop, ‖f (t n)‖ ≤ C := Filter.Eventually.of_forall h
  obtain ⟨n, hn1, hn2⟩ := (hgt.and hle).exists
  exact absurd hn2 (not_le.mpr hn1)

end Work.EQ
