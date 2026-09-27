import Mathlib
import Submission.Work.Brown.Basic
import Submission.Work.PL.Defs
import Submission.Work.Brown.Cell.isOpenCell_ball
import Submission.Work.Brown.Compactify.exists_collapseMap
import Submission.Work.Brown.Compactify.isClosed_compl_image_coe
import Submission.Work.Brown.Compactify.antitone_compl_image_coe
import Submission.Work.Brown.Compactify.iInter_compl_image_coe_eq_infty
import Submission.Work.Brown.Compactify.secondCountableTopology_onePoint
import Submission.Work.Brown.Compactify.nonempty_homeomorph_of_onePoint_homeomorph
import Submission.Work.Brown.Main.sphere_of_collapse_sequence

/-!
# A space in which every compact subset lies in an open `n`-cell is `ℝⁿ`

This file proves `Work.Brown.Main.nonempty_homeomorph_of_compact_subsets_in_openCell`:
if every compact subset of a second countable locally compact Hausdorff space `W` is contained
in an open `n`-cell (an open subset homeomorphic to `ℝⁿ`), then `W ≃ₜ ℝⁿ`.

The "criterion" hypothesis is equivalent to the hypothesis of Brown's monotone union theorem,
and the proof proceeds in two steps:

* the criterion produces an exhaustion of `W` by closed balls of charts, hence a monotone open
  cover of `W` by open `n`-cells (`Work.Brown.MonotoneOpenCellCover`);
* Brown's monotone union theorem (Uspenskij's proof, implemented in
  `Work.Brown.Engine.sphere_of_collapse_sequence`) then identifies `W` with `ℝⁿ`.
-/

open Set Metric
open scoped Topology

namespace Work.Brown.Main

variable {n : ℕ} {W : Type*} [TopologicalSpace W]

/-! ### Chart balls -/

/-- A **chart ball** in `W`: an open cell `V ⊆ W` together with a homeomorphism
`e : V ≃ₜ ℝⁿ` and a positive radius `r`.  The closed ball and the open ball it cuts out of `W`
are `cellSet` and `ballSet`. -/
structure BallChart (n : ℕ) (W : Type*) [TopologicalSpace W] where
  /-- the chart domain -/
  V : Set W
  /-- the chart domain is open -/
  isOpen : IsOpen V
  /-- the chart -/
  e : ↥V ≃ₜ PL.E n
  /-- the radius -/
  r : ℝ
  /-- the radius is positive -/
  hr : 0 < r

namespace BallChart

variable (bc : BallChart n W)

/-- The closed ball cut out by the chart. -/
def cellSet : Set W := Subtype.val '' (bc.e ⁻¹' closedBall (0 : PL.E n) bc.r)

/-- The open ball cut out by the chart. -/
def ballSet : Set W := Subtype.val '' (bc.e ⁻¹' ball (0 : PL.E n) bc.r)

lemma isCompact_cellSet : IsCompact bc.cellSet := by
  rw [cellSet]
  exact ((bc.e.isCompact_preimage).mpr (isCompact_closedBall (0 : PL.E n) bc.r)).image
    continuous_subtype_val

lemma isOpen_ballSet : IsOpen bc.ballSet := by
  rw [ballSet]
  exact bc.isOpen.isOpenMap_subtype_val _ (bc.e.isOpen_preimage.mpr isOpen_ball)

lemma ballSet_subset_cellSet : bc.ballSet ⊆ bc.cellSet :=
  image_mono (preimage_mono ball_subset_closedBall)

/-- The open ball cut out by a chart is an open `n`-cell. -/
lemma nonempty_homeomorph_ballSet : Nonempty (↥bc.ballSet ≃ₜ PL.E n) := by
  set S : Set ↥bc.V := bc.e ⁻¹' ball (0 : PL.E n) bc.r with hS
  have hf : Topology.IsEmbedding (fun x : ↥S => ((x : ↥bc.V) : W)) :=
    (Topology.IsEmbedding.subtypeVal (p := fun w : W => w ∈ bc.V)).comp
      (Topology.IsEmbedding.subtypeVal (p := fun v : ↥bc.V => v ∈ S))
  have hrange : Set.range (fun x : ↥S => ((x : ↥bc.V) : W)) = bc.ballSet := by
    rw [BallChart.ballSet, ← hS]
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : ↥bc.V), x.2, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  have h1 : ↥bc.ballSet ≃ₜ ↥S :=
    ((hf.toHomeomorph).trans (Homeomorph.setCongr hrange)).symm
  have h2 : ↥S ≃ₜ ↥(ball (0 : PL.E n) bc.r) := by
    refine (Homeomorph.image bc.e S).trans (Homeomorph.setCongr ?_)
    rw [hS, Set.image_preimage_eq _ bc.e.surjective]
  exact ⟨h1.trans (h2.trans (Work.Brown.Cell.isOpenCell_ball bc.hr).2.some)⟩

/-- The open ball cut out by a chart is an open `n`-cell. -/
lemma isOpenCell_ballSet : PL.IsOpenCell n bc.ballSet :=
  ⟨bc.isOpen_ballSet, bc.nonempty_homeomorph_ballSet⟩

end BallChart

/-- The criterion applied to a compact set: there is a chart ball whose open ball contains it. -/
lemma exists_ballChart
    (h : ∀ K : Set W, IsCompact K → ∃ V : Set W, PL.IsOpenCell n V ∧ K ⊆ V)
    {C : Set W} (hC : IsCompact C) :
    ∃ bc : BallChart n W, C ⊆ bc.ballSet := by
  obtain ⟨V, hVcell, hCV⟩ := h C hC
  obtain ⟨hVopen, ⟨e⟩⟩ := hVcell
  set g : ↥C → PL.E n := fun x => e ⟨(x : W), hCV x.2⟩ with hg
  have hgcont : Continuous g := by
    rw [hg]
    exact e.continuous.comp (continuous_subtype_val.subtype_mk (fun x => hCV x.2))
  haveI : CompactSpace ↥C := isCompact_iff_compactSpace.mp hC
  obtain ⟨R, hR⟩ := (isCompact_range hgcont).isBounded.subset_closedBall (0 : PL.E n)
  have hR' : ∀ x : ↥C, ‖g x‖ ≤ R := fun x => by
    have hx : g x ∈ closedBall (0 : PL.E n) R := hR (Set.mem_range_self x)
    rwa [Metric.mem_closedBall, dist_zero_right] at hx
  refine ⟨⟨V, hVopen, e, max R 0 + 1, by positivity⟩, fun x hx => ?_⟩
  have hlt : ‖g ⟨x, hx⟩‖ < max R 0 + 1 := by
    have hxg : ‖g ⟨x, hx⟩‖ ≤ R := hR' ⟨x, hx⟩
    have hle : R ≤ max R 0 := le_max_left R 0
    linarith
  have hmem : e ⟨x, hCV hx⟩ ∈ ball (0 : PL.E n) (max R 0 + 1) := by
    rw [hg] at hlt
    rw [Metric.mem_ball, dist_zero_right]
    simpa using hlt
  exact ⟨⟨x, hCV hx⟩, hmem, rfl⟩

/-! ### The exhaustion by chart balls -/

section Exhaustion

variable (h : ∀ K : Set W, IsCompact K → ∃ V : Set W, PL.IsOpenCell n V ∧ K ⊆ V)
variable (K : ℕ → Set W) (hK : ∀ k, IsCompact (K k))

/-- One step of the exhaustion: a chart ball containing the previous closed ball and the next
compact set. -/
noncomputable def stepBall (m : ℕ) (bc : BallChart n W) : BallChart n W :=
  Classical.choose (exists_ballChart h (bc.isCompact_cellSet.union (hK m)))

lemma stepBall_spec (m : ℕ) (bc : BallChart n W) :
    bc.cellSet ∪ K m ⊆ (stepBall h K hK m bc).ballSet :=
  Classical.choose_spec (exists_ballChart h (bc.isCompact_cellSet.union (hK m)))

/-- The exhaustion of `W` by chart balls. -/
noncomputable def CB : ℕ → BallChart n W :=
  Nat.rec (Classical.choose (exists_ballChart h (hK 0)))
    (fun k bc => stepBall h K hK (k+1) bc)

lemma CB_init : K 0 ⊆ (CB h K hK 0).ballSet :=
  Classical.choose_spec (exists_ballChart h (hK 0))

lemma CB_succ (k : ℕ) :
    (CB h K hK k).cellSet ∪ K (k+1) ⊆ (CB h K hK (k+1)).ballSet := by
  have hs : CB h K hK (k+1) = stepBall h K hK (k+1) (CB h K hK k) := rfl
  rw [hs]
  exact stepBall_spec h K hK (k+1) (CB h K hK k)

lemma K_subset_CB_ballSet (k : ℕ) : K k ⊆ (CB h K hK k).ballSet := by
  cases k with
  | zero => exact CB_init h K hK
  | succ j =>
      exact (Set.subset_union_right).trans (CB_succ h K hK j)

lemma CB_ballSet_monotone : Monotone (fun k => (CB h K hK k).ballSet) := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => exact subset_rfl
  | succ n _ ih =>
      exact ih.trans ((BallChart.ballSet_subset_cellSet _).trans
        ((Set.subset_union_left).trans (CB_succ h K hK n)))

lemma iUnion_CB_ballSet (hcover : ⋃ k, K k = univ) :
    (⋃ k, (CB h K hK k).ballSet) = univ :=
  Set.eq_univ_of_univ_subset (by
    rw [← hcover]
    exact iUnion_mono fun k => K_subset_CB_ballSet h K hK k)

end Exhaustion

/-! ### The one-point compactification of a σ-compact second countable space -/

/-- The one-point compactification of a second countable, σ-compact, locally compact space is
second countable. -/
theorem secondCountableTopology_onePoint' {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [LocallyCompactSpace X] [SigmaCompactSpace X] :
    SecondCountableTopology (OnePoint X) := by
  let K : CompactExhaustion X := CompactExhaustion.choice X
  exact Work.Brown.Compactify.secondCountableTopology_onePoint_of_cofinal
    ⟨K, fun n => ⟨(K.isCompact n).isClosed, K.isCompact n⟩,
      fun s _ hs => K.exists_superset_of_isCompact hs⟩

/-! ### The main theorem -/

theorem nonempty_homeomorph_of_compact_subsets_in_openCell {n : ℕ} (hn : 1 ≤ n) {W : Type*}
    [TopologicalSpace W] [T2Space W] [LocallyCompactSpace W] [SecondCountableTopology W]
    (h : ∀ K : Set W, IsCompact K → ∃ V : Set W, PL.IsOpenCell n V ∧ K ⊆ V) :
    Nonempty (W ≃ₜ PL.E n) := by
  haveI : SigmaCompactSpace W := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SecondCountableTopology (OnePoint W) := secondCountableTopology_onePoint' (X := W)
  obtain ⟨K, hK, hcover⟩ := SigmaCompactSpace.exists_compact_covering (X := W)
  set U : ℕ → Set W := fun k => (CB h K hK k).ballSet with hUdef
  have hUopen : ∀ k, IsOpen (U k) := fun k => (CB h K hK k).isOpen_ballSet
  have hUmono : Monotone U := CB_ballSet_monotone h K hK
  have hUcell : ∀ k, PL.IsOpenCell n (U k) := fun k => (CB h K hK k).isOpenCell_ballSet
  have hUcover : (⋃ k, U k) = univ := iUnion_CB_ballSet h K hK hcover
  have hFcl : ∀ k, IsClosed (((↑) '' U k : Set (OnePoint W))ᶜ) := fun k =>
    Work.Brown.Compactify.isClosed_compl_image_coe (hUopen k)
  have hFanti : Antitone (fun k => (((↑) '' U k : Set (OnePoint W))ᶜ)) :=
    Work.Brown.Compactify.antitone_compl_image_coe hUmono
  have hFint : (⋂ k, (((↑) '' U k : Set (OnePoint W))ᶜ)) = {OnePoint.infty} :=
    Work.Brown.Compactify.iInter_compl_image_coe_eq_infty hUmono hUcover
  have hq : ∀ k, ∃ q : OnePoint W → ↥(Metric.sphere (0 : PL.E (n + 1)) 1),
      Continuous q ∧ Function.Surjective q ∧ ∀ x y, q x = q y ↔ x = y ∨
        (x ∈ (((↑) '' U k : Set (OnePoint W))ᶜ) ∧
          y ∈ (((↑) '' U k : Set (OnePoint W))ᶜ)) :=
    fun k => Work.Brown.Compactify.exists_collapseMap (hUopen k) (hUcell k).2
  have hZ : Nonempty (OnePoint W ≃ₜ ↥(Metric.sphere (0 : PL.E (n + 1)) 1)) :=
    sphere_of_collapse_sequence
      (F := fun k => (((↑) '' U k : Set (OnePoint W))ᶜ)) hFcl hFanti hFint hq
  exact Work.Brown.Compactify.nonempty_homeomorph_of_onePoint_homeomorph hZ

end Work.Brown.Main
