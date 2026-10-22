import Mathlib
import Submission.Work.DISC.Defs

namespace Work.DISC

theorem uniform_tail_of_open (S : LightProfinite.{0}) (U : Set (↥S × OnePoint ℕ))
    (hU : IsOpen U) (h : ∀ s : ↥S, (s, OnePoint.infty) ∈ U) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ s : ↥S, (s, (n : OnePoint ℕ)) ∈ U := by
  -- `S` is compact, so the projection `S × (ℕ∪{∞}) → ℕ∪{∞}` is a closed map.
  have hmap : IsClosedMap (Prod.snd : ↥S × OnePoint ℕ → OnePoint ℕ) :=
    isClosedMap_snd_of_compactSpace
  -- The complement of `U` is closed (as `U` is open).
  have hB : IsClosed ((Prod.snd : ↥S × OnePoint ℕ → OnePoint ℕ) '' Uᶜ) :=
    hmap _ hU.isClosed_compl
  -- Its image under the projection does not contain `∞`.
  have hinf : OnePoint.infty ∉ (Prod.snd : ↥S × OnePoint ℕ → OnePoint ℕ) '' Uᶜ := by
    rintro ⟨⟨s, t⟩, ht, ht'⟩
    have ht'' : t = OnePoint.infty := ht'
    rw [ht'', Set.mem_compl_iff] at ht
    exact ht (h s)
  -- A closed set of `ℕ∪{∞}` avoiding `∞` meets `ℕ` in a compact, hence finite, set.
  have hcomp : IsCompact (OnePoint.some ⁻¹' ((Prod.snd : ↥S × OnePoint ℕ → OnePoint ℕ) '' Uᶜ) : Set ℕ) :=
    ((OnePoint.isClosed_iff_of_notMem hinf).mp hB).2
  have hfin : (OnePoint.some ⁻¹' ((Prod.snd : ↥S × OnePoint ℕ → OnePoint ℕ) '' Uᶜ) : Set ℕ).Finite :=
    isCompact_iff_finite.mp hcomp
  -- Hence only finitely many "bad" coordinates `n` occur.
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N + 1, fun n hn s => ?_⟩
  have hnB : (n : OnePoint ℕ) ∉ (Prod.snd : ↥S × OnePoint ℕ → OnePoint ℕ) '' Uᶜ := by
    intro hmem
    have hmem' : n ∈ (OnePoint.some ⁻¹' ((Prod.snd : ↥S × OnePoint ℕ → OnePoint ℕ) '' Uᶜ) : Set ℕ) := hmem
    have := hN hmem'
    omega
  have : (s, (n : OnePoint ℕ)) ∉ Uᶜ := fun hc =>
    hnB ⟨(s, (n : OnePoint ℕ)), hc, rfl⟩
  simpa using this

end Work.DISC
