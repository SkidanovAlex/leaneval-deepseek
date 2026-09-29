import Mathlib

set_option linter.style.haveILetI false

namespace Work.TMC14Core

/-- The set of real `E` for which there exists `θ ∈ [a,b]` with `‖F (E,θ)‖ ≤ 2`
is closed, for `F` continuous. This is the closedness of the image of a closed
subset of `Icc a b × ℝ` under the (proper, hence closed) projection onto the
second coordinate; the fibre `Icc a b` is compact. -/
theorem isClosed_exists_norm_le (F : ℝ × ℝ → ℂ) (hF : Continuous F) (a b : ℝ) :
    IsClosed {E : ℝ | ∃ θ ∈ Set.Icc a b, ‖F (E, θ)‖ ≤ 2} := by
  haveI : CompactSpace (Set.Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hcont : Continuous (fun p : Set.Icc a b × ℝ => F (p.2, ↑p.1)) :=
    hF.comp (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
  have hclosed : IsClosed {p : Set.Icc a b × ℝ | ‖F (p.2, ↑p.1)‖ ≤ 2} :=
    isClosed_Iic.preimage (continuous_norm.comp hcont)
  have hmap := isClosedMap_snd_of_compactSpace (X := Set.Icc a b) (Y := ℝ)
    {p : Set.Icc a b × ℝ | ‖F (p.2, ↑p.1)‖ ≤ 2} hclosed
  convert hmap using 1
  ext E
  constructor
  · rintro ⟨θ, hθ, h⟩
    exact ⟨(⟨θ, hθ⟩, E), h, rfl⟩
  · rintro ⟨q, hq, hqE⟩
    exact ⟨↑q.1, q.1.2, hqE ▸ hq⟩

end Work.TMC14Core
