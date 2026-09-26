import Mathlib
import Submission.MiddleConvergence
import Submission.Work.Drive.middle_tangency

/-!
# The strict-middle locus of a family of chords: endpoint transversality and closedness

This module collects the two elementary structural facts about the correspondence

    D = {(u, m) : IsMiddleOnChord r (a u) (b u) m}   (u : ℝ, m : AddCircle period)

for a smooth knot `r` in transverse torus general position and a continuous family of chords
`(a u, b u)` whose classes are distinct and each of which carries a strict middle:

* `chord_transverse_of_middle` — the chord carrying a strict middle is transverse at both of its
  endpoints (the `∂`-conditions contained in `TorusGeneralPositionTransverse`, transported from the
  general-position representatives of the collinear triple);
* `middleLocus_seq_closed` / `isClosed_middleLocus` — `D` is closed.  The limit of strict middles is
  a *closed* middle (closedness of the closed-middle data), and the endpoint-escape lemmas
  (`no_circle_middle_to_endpoint_a`/`_b`, which use exactly the chord transversality above and the
  existence of some middle on every chord) exclude the limit being an endpoint, so the limit middle
  is strict.

Both are used by the continuation lemma `Work.Drive.advancing_middle_family`.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology

set_option maxHeartbeats 1600000

noncomputable section


/-- Endpoint transversality of a chord carrying a strict middle (real parameters). -/
theorem chord_transverse_of_middle {r : ℝ → Space} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPositionTransverse r)
    {A B M : ℝ} (hAB : (A : KnotParam) ≠ (B : KnotParam))
    (hmid : IsMiddleOnChord r (A : KnotParam) (B : KnotParam) (M : KnotParam)) :
    cross3 (r A - r B) (velocity r A) ≠ 0 ∧ cross3 (r A - r B) (velocity r B) ≠ 0 := by
  have hreal : r M ∈ openSegment ℝ (r A) (r B) := by
    have h' := hmid
    rw [IsMiddleOnChord] at h'
    simpa [knotMap_eq_r h] using h'
  have hMAn : (M : KnotParam) ≠ (A : KnotParam) := (IsMiddleOnChord.ne_params h hAB hmid).1
  have hMBn : (M : KnotParam) ≠ (B : KnotParam) := (IsMiddleOnChord.ne_params h hAB hmid).2
  have hcol : torusCollinearity r (torusQuotient (A, (B, M))) = 0 := by
    have h0 : cross3 (r A - r B) (r A - r M) = 0 := mem_openSegment_cross3 hreal
    simpa [torusCollinearity, torusQuotient, knotMap_eq_r h] using h0
  have hoff : torusQuotient (A, (B, M)) ∈ TorusOffDiag r := by
    refine ⟨?_, ?_, ?_⟩
    · show knotMap r (A : KnotParam) ≠ knotMap r (B : KnotParam)
      exact fun hk => hAB ((knotMap_inj_iff h).mp hk)
    · show knotMap r (A : KnotParam) ≠ knotMap r (M : KnotParam)
      exact fun hk => hMAn ((knotMap_inj_iff h).mp hk).symm
    · show knotMap r (B : KnotParam) ≠ knotMap r (M : KnotParam)
      exact fun hk => hMBn ((knotMap_inj_iff h).mp hk).symm
  rcases hgp (torusQuotient (A, (B, M))) hcol hoff with
    ⟨a, b, m, _, _, _, hac, hbc, _, hGP⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hGP.2
  have hra : r a = r A := r_eq_of_coe_eq h hac
  have hrb : r b = r B := r_eq_of_coe_eq h hbc
  have hva : velocity r a = velocity r A := velocity_eq_of_coe_eq h hac
  have hvb : velocity r b = velocity r B := velocity_eq_of_coe_eq h hbc
  refine ⟨?_, ?_⟩
  · simpa only [← hra, ← hrb, ← hva] using h1
  · simpa only [← hra, ← hrb, ← hvb] using h2

/-- Sequential closedness of the strict-middle locus of a chord family.  Uses the
endpoint-escape lemmas and the existence of a middle on every chord. -/
theorem middleLocus_seq_closed {r : ℝ → Space} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPositionTransverse r)
    {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hne : ∀ u : ℝ, (a u : KnotParam) ≠ (b u : KnotParam))
    (hmem : ∀ u : ℝ, ∃ m : KnotParam, IsMiddleOnChord r (a u : KnotParam) (b u : KnotParam) m)
    {u : ℕ → ℝ} {M : ℕ → KnotParam} {u₀ : ℝ} {M₀ : KnotParam}
    (hu : Tendsto u atTop (𝓝 u₀)) (hM : Tendsto M atTop (𝓝 M₀))
    (hmid : ∀ n, IsMiddleOnChord r (a (u n) : KnotParam) (b (u n) : KnotParam) (M n)) :
    IsMiddleOnChord r (a u₀ : KnotParam) (b u₀ : KnotParam) M₀ := by
  have hcoe : Continuous (fun x : ℝ => (x : KnotParam)) := QuotientAddGroup.continuous_mk
  have hau : Tendsto (fun n : ℕ => (a (u n) : KnotParam)) atTop (𝓝 (a u₀ : KnotParam)) :=
    (hcoe.tendsto (a u₀)).comp ((ha.tendsto u₀).comp hu)
  have hbu : Tendsto (fun n : ℕ => (b (u n) : KnotParam)) atTop (𝓝 (b u₀ : KnotParam)) :=
    (hcoe.tendsto (b u₀)).comp ((hb.tendsto u₀).comp hu)
  -- the closed-middle condition at the limit
  have hcl : IsMiddleOnClosedChord r (a u₀ : KnotParam) (b u₀ : KnotParam) M₀ := by
    have hp : ((a u₀ : KnotParam), ((b u₀ : KnotParam), M₀)) ∈ closedMiddleData r := by
      have hseq : Tendsto (fun n : ℕ => ((a (u n) : KnotParam), ((b (u n) : KnotParam), M n)))
          atTop (𝓝 ((a u₀ : KnotParam), ((b u₀ : KnotParam), M₀))) :=
        Filter.Tendsto.prodMk_nhds hau (Filter.Tendsto.prodMk_nhds hbu hM)
      refine IsClosed.mem_of_tendsto (isClosed_closedMiddleData h) hseq ?_
      refine Eventually.of_forall (fun n => ?_)
      have hmemO : ((a (u n) : KnotParam), ((b (u n) : KnotParam), M n)) ∈ openMiddleData r := by
        change IsMiddleOnOpenChord r (a (u n) : KnotParam) (b (u n) : KnotParam) (M n)
        simpa [IsMiddleOnOpenChord, IsMiddleOnChord] using hmid n
      exact openMiddleData_subset_closedMiddleData r hmemO
    exact (mem_closedMiddleData_iff r).mp hp
  -- the limit middle is not an endpoint class
  have hAne : r (a u₀) ≠ r (b u₀) := by
    intro hk
    exact hne u₀ ((knotMap_inj_iff h).mp (by simpa [knotMap_eq_r h] using hk))
  have htrA : cross3 (r (a u₀) - r (b u₀)) (velocity r (a u₀)) ≠ 0 := by
    rcases hmem u₀ with ⟨m, hm⟩
    have hmreal : IsMiddleOnChord r (a u₀ : KnotParam) (b u₀ : KnotParam)
        ((Quotient.out m : ℝ) : KnotParam) := by
      rwa [QuotientAddGroup.out_eq']
    exact (chord_transverse_of_middle h hgp (hne u₀) hmreal).1
  have htrB : cross3 (r (a u₀) - r (b u₀)) (velocity r (b u₀)) ≠ 0 := by
    rcases hmem u₀ with ⟨m, hm⟩
    have hmreal : IsMiddleOnChord r (a u₀ : KnotParam) (b u₀ : KnotParam)
        ((Quotient.out m : ℝ) : KnotParam) := by
      rwa [QuotientAddGroup.out_eq']
    exact (chord_transverse_of_middle h hgp (hne u₀) hmreal).2
  have hM₀neA : M₀ ≠ (a u₀ : KnotParam) := by
    intro hMA
    have hm : Tendsto M atTop (𝓝 (a u₀ : KnotParam)) := by rw [← hMA]; exact hM
    exact no_circle_middle_to_endpoint_a h hAne htrA hau hbu hm (Eventually.of_forall hmid)
  have hM₀neB : M₀ ≠ (b u₀ : KnotParam) := by
    intro hMB
    have hm : Tendsto M atTop (𝓝 (b u₀ : KnotParam)) := by rw [← hMB]; exact hM
    exact no_circle_middle_to_endpoint_b h hAne htrB hau hbu hm (Eventually.of_forall hmid)
  -- convert to strictness
  have hseg : knotMap r M₀ ∈ segment ℝ (knotMap r (a u₀ : KnotParam))
      (knotMap r (b u₀ : KnotParam)) := by
    have h' := hcl
    rw [IsMiddleOnClosedChord] at h'
    simpa using h'
  have hxA : knotMap r M₀ ≠ knotMap r (a u₀ : KnotParam) := by
    intro hk
    exact hM₀neA ((knotMap_injective h) hk)
  have hxB : knotMap r M₀ ≠ knotMap r (b u₀ : KnotParam) := by
    intro hk
    exact hM₀neB ((knotMap_injective h) hk)
  exact segment_mem_openSegment_of_ne hseg hxA hxB

/-- The strict-middle locus of a chord family is closed. -/
theorem isClosed_middleLocus {r : ℝ → Space} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPositionTransverse r)
    {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hne : ∀ u : ℝ, (a u : KnotParam) ≠ (b u : KnotParam))
    (hmem : ∀ u : ℝ, ∃ m : KnotParam, IsMiddleOnChord r (a u : KnotParam) (b u : KnotParam) m) :
    IsClosed {p : ℝ × KnotParam |
      IsMiddleOnChord r (a p.1 : KnotParam) (b p.1 : KnotParam) p.2} := by
  rw [← isSeqClosed_iff_isClosed]
  intro u' x' hu' hx'
  have h1 : Tendsto (fun n : ℕ => (u' n).1) atTop (𝓝 x'.1) :=
    (continuous_fst.tendsto x').comp hx'
  have h2 : Tendsto (fun n : ℕ => (u' n).2) atTop (𝓝 x'.2) :=
    (continuous_snd.tendsto x').comp hx'
  exact middleLocus_seq_closed h hgp ha hb hne hmem h1 h2 hu'


end

end Work.Drive
