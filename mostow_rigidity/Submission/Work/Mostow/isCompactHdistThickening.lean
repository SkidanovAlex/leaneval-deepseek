import Mathlib
import Submission.Work.Mostow.QIDefs

/-!
# The `hdist`-thickening of a compact set is compact

For a compact `K ⊆ ℍⁿ` and `r : ℝ`, the set `{w | ∃ v ∈ K, hdist w v ≤ r}` of points within
hyperbolic distance `r` of `K` is compact.

The proof is the metric-space argument, purely from the hypothesis `HypIsometryProp n`:

* pick `v₀ ∈ K` (if `K` is empty, the thickening is empty and there is nothing to prove);
* `v ↦ hdist v v₀` is continuous, so its image on the compact `K` is bounded above by some `D`;
  hence every `w` of the thickening satisfies `hdist v₀ w ≤ r + D`;
* the thickening is therefore the image under `Prod.snd` of the set
  `(K ×ˢ B) ∩ {p | hdist p.2 p.1 ≤ r}`, where `B = {w | hdist v₀ w ≤ r + D}` is the compact
  ball of hypothesis `HypIsometryProp`;
* that set is compact (a closed subset of the compact product `K ×ˢ B`), and a continuous image
  of a compact set is compact.
-/

set_option maxHeartbeats 1000000

namespace Work.Mostow

open Submission.Mostow

theorem isCompactHdistThickening {n : ℕ} (hI : Submission.Mostow.HypIsometryProp n)
    (K : Set (Submission.Mostow.E n)) (hK : IsCompact K) (r : ℝ) :
    IsCompact {w : Submission.Mostow.E n | ∃ v ∈ K, Submission.Mostow.hdist w v ≤ r} := by
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  by_cases hne : K.Nonempty
  · obtain ⟨v₀, hv₀⟩ := hne
    -- the continuous function `v ↦ hdist v v₀` is bounded above on `K`
    have hf : Continuous (fun v : E n => hdist v v₀) := by
      show Continuous ((fun p : E n × E n => hdist p.1 p.2) ∘ (fun v : E n => (v, v₀)))
      exact hI'.continuous.comp (Continuous.prodMk_left v₀)
    obtain ⟨D, hD⟩ := (hK.image hf).bddAbove
    have hBd : ∀ v ∈ K, hdist v v₀ ≤ D := fun v hv => hD ⟨v, hv, rfl⟩
    have hBd2 : ∀ v ∈ K, hdist v₀ v ≤ D := fun v hv => by
      rw [hI'.symm v₀ v]; exact hBd v hv
    -- the thickening of `K` is contained in the compact ball `B` of radius `r + D` about `v₀`
    set B : Set (E n) := {w : E n | hdist v₀ w ≤ r + D} with hBdef
    have hball : IsCompact B := by rw [hBdef]; exact hI'.ball_compact v₀ (r + D)
    have hrel : Continuous (fun p : E n × E n => hdist p.2 p.1) := by
      show Continuous ((fun p : E n × E n => hdist p.1 p.2) ∘ Prod.swap)
      exact hI'.continuous.comp continuous_swap
    have hclosed : IsClosed {p : E n × E n | hdist p.2 p.1 ≤ r} :=
      isClosed_le hrel continuous_const
    have hC : IsCompact ((K ×ˢ B) ∩ {p : E n × E n | hdist p.2 p.1 ≤ r}) :=
      (hK.prod hball).inter_right hclosed
    have himg : IsCompact (Prod.snd '' ((K ×ˢ B) ∩ {p : E n × E n | hdist p.2 p.1 ≤ r})) :=
      hC.image continuous_snd
    have hseq : Prod.snd '' ((K ×ˢ B) ∩ {p : E n × E n | hdist p.2 p.1 ≤ r})
        = {w : E n | ∃ v ∈ K, hdist w v ≤ r} := by
      ext w
      constructor
      · rintro ⟨p, hp, rfl⟩
        simp only [Set.mem_inter_iff, Set.mem_prod] at hp
        exact ⟨p.1, hp.1.1, hp.2⟩
      · rintro ⟨v, hv, hvle⟩
        refine ⟨(v, w), ?_, rfl⟩
        simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_ofPred_eq]
        refine ⟨⟨hv, ?_⟩, hvle⟩
        rw [hBdef]
        have h1 := hI'.triangle v₀ v w
        have h2 := hBd2 v hv
        have h3 : hdist v w ≤ r := by rw [hI'.symm v w]; exact hvle
        calc hdist v₀ w ≤ hdist v₀ v + hdist v w := h1
          _ ≤ D + r := add_le_add h2 h3
          _ = r + D := by ring
    rw [hseq] at himg
    exact himg
  · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hSempty : {w : E n | ∃ v ∈ K, hdist w v ≤ r} = ∅ := by
      rw [hKempty]
      simp
    rw [hSempty]
    exact isCompact_empty

end Work.Mostow
