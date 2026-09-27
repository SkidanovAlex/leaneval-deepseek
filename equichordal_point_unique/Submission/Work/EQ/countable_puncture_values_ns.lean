import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.countable_puncture_psi1_limits
import Submission.Work.EQ.countable_puncture_psi2_limits

/-!
# Namespace copy of `Work.EQ.countable_puncture_values`

This is the assembly of Rychlik's step 2 (the countability of the puncture values `(u₀v₀)⁻¹`) on
top of the *proved* modules `Work.EQ.countable_puncture_psi1_limits` and
`Work.EQ.countable_puncture_psi2_limits`; the original module
`Submission/Work/EQ/countable_puncture_values.lean` contains a stale, still-`sorry`ed inline copy of
the first of these, and is deliberately not imported.  Declarations live in `Work.EQ.CPV` so that
this module can coexist with the original.
-/

noncomputable section

open Filter _root_.Topology Complex Metric
open scoped Topology

namespace Work.EQ.CPV

theorem countable_puncture_values {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    Set.Countable {w : ℂ | ∃ (e : ℂ → ChainData) (u₀ v₀ : ℂ) (k : ℕ),
      IsPuncturedChart a h e u₀ k ∧
      (¬ ∃ q ∈ H0 a h, Filter.Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q)) ∧
      Filter.Tendsto (fun ζ : ℂ => (e ζ).2.2) (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ))
        (nhds v₀) ∧
      w = (u₀ * v₀)⁻¹} := by
  have hU := countable_puncture_psi1_limits ha0 ha1 hh
  -- the set of pairs `(u₀, v₀)` realising a genuine puncture
  set P : Set (ℂ × ℂ) := {p | ∃ (e : ℂ → ChainData) (k : ℕ),
      IsPuncturedChart a h e p.1 k ∧
      (¬ ∃ q ∈ H0 a h, Filter.Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q)) ∧
      Filter.Tendsto (fun ζ : ℂ => (e ζ).2.2)
        (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds p.2)} with hP
  have hPc : P.Countable := by
    have hsub : P ⊆ ⋃ u₀ ∈ {u₀ : ℂ | ∃ (e : ℂ → ChainData) (v₀ : ℂ) (k : ℕ),
        IsPuncturedChart a h e u₀ k ∧
        (¬ ∃ q ∈ H0 a h, Filter.Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q)) ∧
        Filter.Tendsto (fun ζ : ℂ => (e ζ).2.2)
          (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds v₀)},
        {p : ℂ × ℂ | p.1 = u₀ ∧ p ∈ P} := by
      rintro p hpP
      obtain ⟨e, k, he, hno, hv⟩ := hpP
      exact Set.mem_iUnion.mpr ⟨p.1, Set.mem_iUnion.mpr ⟨⟨e, p.2, k, he, hno, hv⟩, rfl,
        ⟨e, k, he, hno, hv⟩⟩⟩
    refine Set.Countable.mono hsub ?_
    refine Set.Countable.biUnion hU fun u₀ _ => ?_
    -- the fibre over `u₀` is countable
    have : {p : ℂ × ℂ | p.1 = u₀ ∧ p ∈ P} ⊆
        Prod.mk u₀ '' {v₀ : ℂ | ∃ (e : ℂ → ChainData) (k : ℕ),
          IsPuncturedChart a h e u₀ k ∧
          (¬ ∃ q ∈ H0 a h, Filter.Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q)) ∧
          Filter.Tendsto (fun ζ : ℂ => (e ζ).2.2)
            (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds v₀)} := by
      rintro p ⟨hp1, e, k, he, hno, hv⟩
      exact ⟨p.2, ⟨e, k, hp1 ▸ he, hno, hv⟩, Prod.ext hp1.symm rfl⟩
    exact Set.Countable.mono this
      ((countable_puncture_psi2_limits ha0 ha1 hh u₀).image (Prod.mk u₀))
  refine Set.Countable.mono ?_ (hPc.image (fun p : ℂ × ℂ => (p.1 * p.2)⁻¹))
  rintro w ⟨e, u₀, v₀, k, he, hno, hv, rfl⟩
  exact ⟨(u₀, v₀), ⟨e, k, he, hno, hv⟩, rfl⟩

end Work.EQ.CPV
