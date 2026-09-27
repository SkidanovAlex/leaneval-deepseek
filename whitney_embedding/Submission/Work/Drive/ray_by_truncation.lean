import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.ray_of_pieces_with_germs
import Submission.Work.Drive.trailAssembly

/-!
# `Work.Drive.ray_by_truncation`

A smooth, injective, proper, immersed ray from `ρ 0` inside an open set `W` containing a continuous
escaping path `ρ` (the smoothing step of the non-compact case of Whitney's strong embedding
theorem).

The proof is the two-line assembly `target_of_pieces` below, applied to the piece family produced by
`Work.Drive.rayPieceFamilyTrail` (see `NOTES_ray_by_truncation_DESIGN_TRAIL.md` for the design of
that family: junctions on the `ρ`-trail at "last visit" times, per-step regions
`ball (σ i) r i ∪ Tube i` where `Tube i` is a thin neighbourhood of the trail avoiding the already
built pieces and a compact exhaustion of `M`, and the engine
`Work.Drive.stagePieceDrawnArcContained` whose *trace row* gives the adjacent separation).

The earlier `State`/`Data'` machinery that lived in this file (needing the unresolved adjacent
`hsep`) has been moved out to `_backups/ray_by_truncation_full_S29.lean.txt`.
-/

namespace Work.Drive

open Set Topology
open scoped Manifold ContDiff
open Work.Noncompact.CompressionTube (MC MCreal smoothOrder)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M]

/-- **The assembly of the target from the piece family.**

A `ℕ`-indexed family of pieces `P i`, each `C^∞`, an immersion, injective on `[0,1]`, chained
(`P i 1 = P (i+1) 0`), with *matching straight germs* at every junction, pairwise meeting only at
the junction points, escaping every compact set, and lying in `W`, starting at `ρ 0` with a
prescribed germ, produces the target's ray: `Work.Noncompact.CompressionTube.ray_of_pieces_with_germs`
gives the ray, and the membership row (`⊆ {P 0 0} ∪ ⋃ i, P i '' Icc`) plus `P i '' Icc ⊆ W`
gives `r t ∈ W`. -/
theorem target_of_pieces {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M]
    {W : Set M} {ρ : ℝ → M} (hρ0W : ρ 0 ∈ W)
    (P : ℕ → ℝ → M) (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) (e : ℝ)
    (hP0 : P 0 0 = ρ 0) (he : 0 < e) (he1 : e ≤ 1) (hu : u ≠ 0)
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M) (hsrc : ρ 0 ∈ c.source)
    (hgerm0 : ∀ t : ℝ, 0 ≤ t → t ≤ e → P 0 t = c.symm (c (ρ 0) + t • u))
    (hsm : ∀ i : ℕ, ContMDiff MCreal (MC n) smoothOrder (P i))
    (himm : ∀ (i : ℕ) (t : ℝ), t ∈ Set.Icc (0:ℝ) 1 →
      Function.Injective (mfderiv MCreal (MC n) (P i) t))
    (hinj : ∀ i : ℕ, Set.InjOn (P i) (Set.Icc (0:ℝ) 1))
    (hjun : ∀ i : ℕ, P i 1 = P (i + 1) 0)
    (hWsub : ∀ i : ℕ, P i '' Set.Icc (0:ℝ) 1 ⊆ W)
    (hgerm : ∀ i : ℕ, ∃ (c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (u' : EuclideanSpace ℝ (Fin n)) (e' : ℝ),
      0 < e' ∧ c' ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ P i 1 ∈ c'.source ∧
      (∀ t : ℝ, 1 - e' ≤ t → t ≤ 1 → P i t = c'.symm (c' (P i 1) + (t - 1) • u')) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e' → P (i + 1) t = c'.symm (c' (P (i + 1) 0) + t • u')))
    (hsep : ∀ i j : ℕ, i < j →
      P i '' Set.Icc (0:ℝ) 1 ∩ P j '' Set.Icc (0:ℝ) 1 ⊆ {P i 1})
    (hesc : ∀ K : Set M, IsCompact K → ∃ I : ℕ, ∀ i : ℕ, I ≤ i →
      P i '' Set.Icc (0:ℝ) 1 ∩ K = ∅) :
    ∃ r : ℝ → M, r 0 = ρ 0 ∧ ContMDiffOn MCreal (MC n) smoothOrder r (Set.Ici (0:ℝ)) ∧
      Set.InjOn r (Set.Ici (0:ℝ)) ∧ IsProperMap (fun t : Set.Ici (0:ℝ) => r t) ∧
      (∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) r t)) ∧
      (∀ t : ℝ, 0 ≤ t → r t ∈ W) := by
  obtain ⟨r, hrle, hrcd, hrinj, hrpr, hrimm, hrmem, -⟩ :=
    Work.Noncompact.CompressionTube.ray_of_pieces_with_germs (n := n) (M := M) (c := c) (u := u)
      (e := e) hn P hsm himm hinj hjun hgerm hsep hesc he he1 hu hc (hP0.symm ▸ hsrc)
      (by intro t ht0 hte; rw [hP0]; exact hgerm0 t ht0 hte)
  refine ⟨r, ?_, hrcd, hrinj, hrpr, hrimm, ?_⟩
  · rw [hrle (t := (0:ℝ)) le_rfl, zero_smul, add_zero, c.left_inv (hP0.symm ▸ hsrc)]
    exact hP0
  · intro t ht
    rcases hrmem t ht with h | h
    · rw [h]; exact hP0.symm ▸ hρ0W
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
      exact hWsub i hi

open Work.Noncompact.CompressionTube in
/-- A smooth, injective, proper, immersed ray from `ρ 0` inside an open set `W` that contains a continuous
escaping path `ρ`. -/
theorem ray_by_truncation {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {W : Set M} (hW : IsOpen W) {ρ : ℝ → M} (hρ : Continuous ρ)
    (hρW : ∀ t : ℝ, 0 ≤ t → ρ t ∈ W)
    (hρesc : ∀ K : Set M, IsCompact K → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ρ t ∉ K) :
    ∃ r : ℝ → M, r 0 = ρ 0 ∧
      ContMDiffOn MCreal (MC n) smoothOrder r (Set.Ici (0:ℝ)) ∧
      Set.InjOn r (Set.Ici (0:ℝ)) ∧
      IsProperMap (fun t : Set.Ici (0:ℝ) => r t) ∧
      (∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) r t)) ∧
      (∀ t : ℝ, 0 ≤ t → r t ∈ W) := by
  obtain ⟨P, c, u, e, hP0, he, he1, hu, hc, hsrc, hgerm0, hsm, himm, hinj, hjun, hWsub, hgerm,
    hsep, hesc⟩ :=
    Work.Drive.rayPieceFamilyTrail (n := n) (M := M) hn hW hρ (hρW 0 le_rfl) hρW hρesc
  exact target_of_pieces (n := n) (M := M) hn (W := W) (ρ := ρ) (hρW 0 le_rfl) P c u e hP0 he he1
    hu hc hsrc hgerm0 hsm himm hinj hjun hWsub hgerm hsep hesc


end Work.Drive
