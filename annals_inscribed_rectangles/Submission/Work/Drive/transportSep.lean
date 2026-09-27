import Mathlib
import Submission.Work.Drive.transportFaces
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.pairMeet2

/-!
# The perturbed level-face avoidances by *separation*

The transport's box-parity stage (`Work.Drive.even_colCount_add2`) needs the two *level-face*
avoidances `havY`/`havZ` — at every zero of the pair map the levels `ftY2 x`, `ftZ2 x` of the two
sweep parameters are neither `0` nor `1` — and the design produces them by perturbing the two *chart*
blocks (the weighted chart-shift of `TRANSPORT_COLLAPSE_STATUS.md` §8.7ter).  For the perturbed pair
map the *honest* argument of `Work.Drive.pairDiff_faceY_ne` is no longer available: the chart-shift
leaves the image of the chart, so membership is not inherited.

This file replaces that argument by a **separation** argument, which is stable under a small additive
perturbation:

* `Work.Drive.ne_sub_of_dist_ge` — if two sets are separated by `d` and `‖v‖ < d`, then `a ≠ b - v`
  for `a ∈ A`, `b ∈ B`;
* `Work.Drive.pairDiff2_faceY_ne_of_sep` / `pairDiff2_faceZ_ne_of_sep` — at a zero of the *perturbed*
  pair map, `ftY2 x` (resp. `ftZ2 x`) is neither `0` nor `1`, given that the honest chart block stays
  in a fixed set `A`, that the sweep's top and bottom faces stay in the sets `B`, `B'` separated from
  `A`, and that the perturbation is smaller than the separation.  The geometric inputs are exactly the
  data the design owns (`P ∩ Pᵢ = ∅` and "the floors lie below the levels");
* `Work.Drive.exists_pos_dist_of_isCompact_disjoint` — the *production* of the separation constants:
  two compact, disjoint sets of the capping space have charted images at positive distance, whenever
  the chart is injective on their union.  This is how the design turns its geometric inputs into the
  hypotheses of the two avoidances above.

All declarations are `sorry`-free and rest on `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## 1. The elementary separation lemma -/

/-- **Separation of two sets prevents a small additive shift from turning one into the other.**  If
every pair `(a, b) ∈ A × B` is at distance at least `d`, and `‖v‖ < d`, then no `a ∈ A` equals
`b - v` with `b ∈ B`. -/
theorem ne_sub_of_dist_ge {F : Type*} [SeminormedAddCommGroup F] {A B : Set F} {d : ℝ}
    (hsep : ∀ a ∈ A, ∀ b ∈ B, d ≤ dist a b) {a : F} (ha : a ∈ A) {b : F} (hb : b ∈ B)
    {v : F} (hv : ‖v‖ < d) : a ≠ b - v := by
  intro h
  have hd : dist a b = ‖v‖ := by
    rw [h, dist_eq_norm, show (b - v) - b = -v by abel, norm_neg]
  linarith [hsep a ha b hb]

/-! ## 2. The perturbed level-face avoidances -/

/-- **`havY` for the perturbed pair map, by separation.**  The pair map has both chart blocks shifted
by the weighted chart-shift of the parameter `t`.  If

* the *honest* first chart block `E₀` takes its values in `A`;
* the *honest* second chart block's values `E'₀` are irrelevant here — what is used is that the first
  sweep `V'` takes the value `B` on its **top** face (`y 2 = 1`) and `B'` on its **bottom** face
  (`y 2 = 0`);
* `A` is separated from `B` and from `B'` by `d > 0`;
* the shift is smaller than `d` at every family parameter,

then at every zero of the perturbed pair map the level `ftY2` of the first sweep parameter is neither
`0` nor `1`. -/
theorem pairDiff2_faceY_ne_of_sep
    (E₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V' W' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (w : ℝ → ℝ) (t : EuclideanSpace ℝ (Fin 8))
    {A B B' : Set (EuclideanSpace ℝ (Fin 4))} {d : ℝ}
    (hA : ∀ s : ℝ, ∀ u ∈ Submission.Drive.unitBox 1, E₀ s u ∈ A)
    (hBtop : ∀ y ∈ Submission.Drive.unitBox 2, y 2 = 1 → V' y ∈ B)
    (hBbot : ∀ y ∈ Submission.Drive.unitBox 2, y 2 = 0 → V' y ∈ B')
    (hsep : ∀ a ∈ A, ∀ b ∈ B, d ≤ dist a b)
    (hsep' : ∀ a ∈ A, ∀ b ∈ B', d ≤ dist a b)
    (hbound : ∀ s : ℝ, ‖w s • unpackFst t‖ < d) :
    ∀ x ∈ Submission.Drive.unitBox 8,
      pairDiff2 (fun s u => E₀ s u + w s • unpackFst t)
        (fun s u => E'₀ s u + w s • unpackSnd t) V' W' x = 0 →
      ftY2 x ≠ 0 ∧ ftY2 x ≠ 1 := by
  intro x hx hzero
  have hboxU : ftU x ∈ Submission.Drive.unitBox 1 := ftU_mem_unitBox hx
  have hboxY : ftY x ∈ Submission.Drive.unitBox 2 := ftY_mem_unitBox hx
  have heq : E₀ (ftS x) (ftU x) + w (ftS x) • unpackFst t = V' (ftY x) :=
    ((pairDiff2_eq_zero_iff _ _ _ _ x).mp hzero).1
  have hsub : E₀ (ftS x) (ftU x) = V' (ftY x) - w (ftS x) • unpackFst t :=
    eq_sub_iff_add_eq.mpr heq
  refine ⟨?_, ?_⟩
  · intro h0
    have hmem : V' (ftY x) ∈ B' := hBbot (ftY x) hboxY (by rw [ftY_two]; exact h0)
    exact ne_sub_of_dist_ge hsep' (hA (ftS x) (ftU x) hboxU) hmem (hbound (ftS x)) hsub
  · intro h1
    have hmem : V' (ftY x) ∈ B := hBtop (ftY x) hboxY (by rw [ftY_two]; exact h1)
    exact ne_sub_of_dist_ge hsep (hA (ftS x) (ftU x) hboxU) hmem (hbound (ftS x)) hsub

/-- **`havZ` for the perturbed pair map, by separation.**  The same statement for the second sweep: the
*honest* second chart block `E'₀` takes its values in `A`, the second sweep's top/bottom faces land in
`B`/`B'`, and `A` is separated from both by more than the shift. -/
theorem pairDiff2_faceZ_ne_of_sep
    (E₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V' W' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (w : ℝ → ℝ) (t : EuclideanSpace ℝ (Fin 8))
    {A B B' : Set (EuclideanSpace ℝ (Fin 4))} {d : ℝ}
    (hA : ∀ s : ℝ, ∀ u ∈ Submission.Drive.unitBox 1, E'₀ s u ∈ A)
    (hBtop : ∀ z ∈ Submission.Drive.unitBox 2, z 2 = 1 → W' z ∈ B)
    (hBbot : ∀ z ∈ Submission.Drive.unitBox 2, z 2 = 0 → W' z ∈ B')
    (hsep : ∀ a ∈ A, ∀ b ∈ B, d ≤ dist a b)
    (hsep' : ∀ a ∈ A, ∀ b ∈ B', d ≤ dist a b)
    (hbound : ∀ s : ℝ, ‖w s • unpackSnd t‖ < d) :
    ∀ x ∈ Submission.Drive.unitBox 8,
      pairDiff2 (fun s u => E₀ s u + w s • unpackFst t)
        (fun s u => E'₀ s u + w s • unpackSnd t) V' W' x = 0 →
      ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1 := by
  intro x hx hzero
  have hboxU : ftU x ∈ Submission.Drive.unitBox 1 := ftU_mem_unitBox hx
  have hboxZ : ftZ x ∈ Submission.Drive.unitBox 2 := ftZ_mem_unitBox hx
  have heq : E'₀ (ftS x) (ftU x) + w (ftS x) • unpackSnd t = W' (ftZ x) :=
    ((pairDiff2_eq_zero_iff _ _ _ _ x).mp hzero).2
  have hsub : E'₀ (ftS x) (ftU x) = W' (ftZ x) - w (ftS x) • unpackSnd t :=
    eq_sub_iff_add_eq.mpr heq
  refine ⟨?_, ?_⟩
  · intro h0
    have hmem : W' (ftZ x) ∈ B' := hBbot (ftZ x) hboxZ (by rw [ftZ_two]; exact h0)
    exact ne_sub_of_dist_ge hsep' (hA (ftS x) (ftU x) hboxU) hmem (hbound (ftS x)) hsub
  · intro h1
    have hmem : W' (ftZ x) ∈ B := hBtop (ftZ x) hboxZ (by rw [ftZ_two]; exact h1)
    exact ne_sub_of_dist_ge hsep (hA (ftS x) (ftU x) hboxU) hmem (hbound (ftS x)) hsub

/-! ## 3. Producing the separation constants from compactness -/

/-- **Two compact, disjoint sets have charted images at positive distance** (once the chart is
injective on their union).  This is the form in which the design's geometric inputs
(`P ∩ Pᵢ = ∅`, "the floors lie below the levels") turn into the separation hypotheses of the two
avoidances above. -/
theorem exists_pos_dist_of_isCompact_disjoint {X Y : Type*} [TopologicalSpace X]
    [MetricSpace Y]
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B)
    (hdisj : Disjoint A B) (f : X → Y) (hf : ContinuousOn f (A ∪ B))
    (hinj : Set.InjOn f (A ∪ B)) :
    ∃ d : ℝ, 0 < d ∧ ∀ a ∈ A, ∀ b ∈ B, d ≤ dist (f a) (f b) := by
  have hK : IsCompact (A ×ˢ B) := hA.prod hB
  have hf1 : ContinuousOn (fun p : X × X => f p.1) (A ×ˢ B) :=
    hf.comp continuous_fst.continuousOn (fun p hp => Or.inl hp.1)
  have hf2 : ContinuousOn (fun p : X × X => f p.2) (A ×ˢ B) :=
    hf.comp continuous_snd.continuousOn (fun p hp => Or.inr hp.2)
  have hcont : ContinuousOn (fun p : X × X => dist (f p.1) (f p.2)) (A ×ˢ B) := by
    simpa only [Function.comp_def] using
      (continuous_dist.comp_continuousOn (hf1.prodMk hf2))
  have hpos : ∀ p ∈ A ×ˢ B, (0 : ℝ) < dist (f p.1) (f p.2) := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    refine dist_pos.mpr fun h => ?_
    have h1 : a ∈ A ∪ B := Or.inl ha
    have h2 : b ∈ A ∪ B := Or.inr hb
    exact Set.disjoint_left.mp hdisj ha (hinj h1 h2 h ▸ hb)
  obtain ⟨d, hdpos, hdle⟩ := hK.exists_forall_le' hcont hpos
  exact ⟨d, hdpos, fun a ha b hb => hdle (a, b) ⟨ha, hb⟩⟩

/-- **Two compact, disjoint sets of a charted manifold have charted images at positive distance**,
whenever both lie in the source of the chart.  This is the exact form in which the design turns
`P ∩ Pᵢ = ∅` (and "the floors lie below the levels") into the separation hypotheses of
`Work.Drive.pairDiff2_faceY_ne_of_sep` / `pairDiff2_faceZ_ne_of_sep`. -/
theorem exists_sep_chart {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]
    (p : M) {S T : Set M} (hS : IsCompact S) (hT : IsCompact T) (hdisj : Disjoint S T)
    (hSsrc : S ⊆ (chr p).source) (hTsrc : T ⊆ (chr p).source) :
    ∃ d : ℝ, 0 < d ∧ ∀ a ∈ S, ∀ b ∈ T, d ≤ dist (chr p a) (chr p b) :=
  exists_pos_dist_of_isCompact_disjoint hS hT hdisj (chr p)
    ((chr p).continuousOn.mono (fun x hx => hx.elim (fun h => hSsrc h) (fun h => hTsrc h)))
    ((chr p).injOn.mono (fun x hx => hx.elim (fun h => hSsrc h) (fun h => hTsrc h)))

end

end Work.Drive
