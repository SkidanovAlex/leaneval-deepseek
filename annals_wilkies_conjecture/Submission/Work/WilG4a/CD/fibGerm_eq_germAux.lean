import Mathlib
import Submission.Work.WilG4a.CD.germDefs

namespace Work.WilG4a.CD

/-- `(a - b)² < δ²` is the same as `|a - b| < δ` for `δ > 0`; this is the translation
between the (`δ`-adapted) atom of `germBody` and the (`ρ`-adapted) atom of `fibGerm`. -/
lemma sq_lt_sq_abs {a δ : ℝ} (hδ : 0 < δ) : a ^ 2 < δ ^ 2 ↔ |a| < δ := by
  rw [sq_lt_sq, abs_of_pos hδ]

/-- **`fibGerm` is the `Ω`-construction `germAux`.**  The pointwise description
`mem_germAux` of `germAux p X` says that `z ∈ germAux p X` iff there is `δ > 0` such that for
every `t ≠ z(last)` with `(t - z(last))² < δ²` the fibre point `Fin.snoc (Fin.init z) t` lies in
`X`.  With `X = badLocus f j = (smoothLocus f j)ᶜ` (so `σ ∉ X` means `σ ∈ smoothLocus f j`) and
`(t - z(last))² < δ² ↔ |t - z(last)| < δ` (`sq_lt_sq_abs`), this is literally the defining
condition of the fibre germ `fibGerm f j`. -/
theorem fibGerm_eq_germAux {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) :
    Work.WilG4a.CD.fibGerm f j = Work.WilG4a.CD.germAux p (Work.WilG4a.badLocus f j) := by
  ext z
  rw [mem_germAux, mem_fibGerm]
  constructor
  · -- A fibre neighbourhood in `smoothLocus` witnesses the `germAux` condition, because
    -- `σ ∈ badLocus` is the negation of `σ ∈ smoothLocus`.
    rintro ⟨ρ, hρ, hall⟩
    refine ⟨ρ, hρ, fun t => ?_⟩
    rintro ⟨htne, hsq, hbad⟩
    have hbad' : Fin.snoc (Fin.init z) t ∉ Work.WilG4a.smoothLocus f j := by
      simpa [Work.WilG4a.badLocus] using hbad
    have habs : |t - z (Fin.last p)| < ρ := (sq_lt_sq_abs hρ).mp hsq
    exact absurd (hall t htne habs) hbad'
  · -- Conversely the `germAux` condition (all fibre points outside `badLocus`) is exactly the
    -- punctured fibre neighbourhood lying in `smoothLocus`.
    rintro ⟨δ, hδ, hall⟩
    refine ⟨δ, hδ, fun t htne habs => ?_⟩
    by_contra hbad
    have hbad' : Fin.snoc (Fin.init z) t ∈ Work.WilG4a.badLocus f j := by
      simpa [Work.WilG4a.badLocus] using hbad
    have hsq : (t - z (Fin.last p)) ^ 2 < δ ^ 2 := (sq_lt_sq_abs hδ).mpr habs
    exact absurd ⟨htne, hsq, hbad'⟩ (hall t)

end Work.WilG4a.CD
