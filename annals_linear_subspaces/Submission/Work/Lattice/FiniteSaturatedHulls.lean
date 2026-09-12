import Mathlib
import Submission.Work.Lattice.IntrinsicIndex
import Submission.Work.Lattice.WedgeDeterminesSpan

/-!
# H1 — finite saturated hulls (covolume-spectrum discreteness at rank `r`)

ROADMAP item (ii), last open sub-lemma H1: for a full-rank lattice `Λ ≤ ℝᵈ`
(`E d = EuclideanSpace ℝ (Fin d)`, `Λ : Submodule ℤ (E d)`, `[DiscreteTopology Λ]
[IsZLattice ℝ Λ]`), a rank `0 < r ≤ d` and a bound `C`, there are only finitely many
**saturated** rank-`r` subgroups `M ≤ Λ` (i.e. `M = MixedRankSpectrum.hull Λ M`, the
direct-summand-like lattices `Λ ∩ realSpan M`) with intrinsic covolume `latticeCovol M
≤ C`:

    `finite_saturatedHulls_covol_le` : Finite {M ≤ Λ // subDim M = r ∧
        latticeCovol M ≤ C ∧ M = hull Λ M}

**Proof (Plücker / integer-wedge counting).**  Fix the ambient `ℝ`-basis `bR` of `E d`
induced by a `ℤ`-basis of `Λ` (`latticeZBasisE`); its `r`-fold exterior products form
the `ℝ`-basis `B := bR.exteriorPower r` of the exterior-power space `⋀^r (E d)`, indexed
by the `r`-subsets of `Fin d`.  A saturated rank-`r` `M ≤ Λ` is mapped to the wedge
`w_M := ιMulti r u` of (a `ℤ`-basis family `u` of `M`, `M = span ℤ (range u)`):

1. **integer coordinates** — since `u i ∈ Λ = span ℤ (range (latticeZBasisE))`, the
   coordinates of `w_M` in the basis `B` are the minor determinants of the integer
   coefficient matrix of `u` over `bR` (`ιMultiDual_apply_ιMulti`), hence integers;
   so `w_M` lies in the full-rank lattice `Λ_r := span ℤ (range B)` of `⋀^r (E d)`;
2. **bounded** — `‖w_M‖ = latticeCovol M ≤ C` (`latticeCovol_span`), so
   `w_M ∈ {‖·‖ ≤ max C 0} ∩ Λ_r`, a finite set (`ZLattice.setFinite_inter` on the
   finite-dimensional exterior-power space);
3. **injective** — equal wedges give equal spans
   (`WedgeDeterminesSpan.span_eq_of_ιMulti_eq`), hence equal real spans, hence equal
   hulls, and saturated `M` equals its hull (`M = hull Λ M`).

The module then assembles the **mixed-rank covolume-spectrum statement**
(`finite_mixedRankSpectrum` = `MixedRankSpectrum.mixedRankSpectrumStatement r Λ C`,
the un-saturated form) by the hull-fibre decomposition: `W ↦ (M = hull Λ W, W)` with
`M` running over the (finite, H1) saturated hull set
(`covol_hull_le_covol` puts the hull in the bound, `hull_idempotent` saturates it) and
`W` running over the finite per-hull fibre `finite_fibre_covol_le` (H2).  This closes
ROADMAP item (ii) completely.

All declarations are Mathlib + Submission (IntrinsicIndex/WedgeDeterminesSpan/
GraysonLattice/MixedRankSpectrum).
-/

noncomputable section

open Set Module Real exteriorPower
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Submission.FiniteSaturatedHulls

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.IntrinsicIndex
open Submission.WedgeDeterminesSpan
open Submission.MixedRankSpectrum

/-- **Wedge of an integer-coefficient family lies in the `ℤ`-lattice of exterior products
of a lattice basis**: if `b` is an `ℝ`-basis of `ℝᵈ` and `u : Fin r → ℝᵈ` has all its
members in the `ℤ`-span of `b`, then `ιMulti ℝ r u` lies in the `ℤ`-span of the `r`-fold
exterior products `B s` of the basis vectors (`B := b.exteriorPower r`).  Coordinates of
`ιMulti u` in the basis `B` are the `r×r` minors of the integer coefficient matrix
(`ιMultiDual_apply_ιMulti`), which are integers. -/
lemma ιMulti_mem_intSpan_of_mem_intSpan {d r : ℕ} (b : Basis (Fin d) ℝ (E d))
    (u : Fin r → E d)
    (hu : ∀ i : Fin r, u i ∈ Submodule.span ℤ (Set.range (fun j : Fin d => (b j : E d)))) :
    exteriorPower.ιMulti ℝ r u ∈ Submodule.span ℤ
      (Set.range (fun s : Set.powersetCard (Fin d) r =>
        ((b.exteriorPower r) s : ⋀[ℝ]^r (E d)))) := by
  classical
  let w : ⋀[ℝ]^r (E d) := exteriorPower.ιMulti ℝ r u
  let B : Basis (Set.powersetCard (Fin d) r) ℝ (⋀[ℝ]^r (E d)) := b.exteriorPower r
  have hcoord : ∀ s : Set.powersetCard (Fin d) r,
      (B.repr w) s ∈ Set.range (algebraMap ℤ ℝ) := by
    intro s
    let C : Matrix (Fin r) (Fin r) ℝ := fun i j =>
      b.coord (Set.powersetCard.ofFinEmbEquiv.symm s j) (u i)
    have hint : ∀ i j : Fin r, ∃ z : ℤ, (z : ℝ) = C i j := by
      intro i j
      have hmem : u i ∈ Submodule.span ℤ (Set.range (fun j : Fin d => (b j : E d))) := hu i
      have hco : (b.repr (u i)) (Set.powersetCard.ofFinEmbEquiv.symm s j) ∈
          Set.range (algebraMap ℤ ℝ) :=
        (b.mem_span_iff_repr_mem ℤ (u i)).mp hmem (Set.powersetCard.ofFinEmbEquiv.symm s j)
      rcases hco with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      simpa [C] using hz
    let M : Matrix (Fin r) (Fin r) ℤ := fun i j => Classical.choose (hint i j)
    have hMcast : ∀ i j : Fin r, (M i j : ℝ) = C i j := by
      intro i j
      dsimp [M]
      exact Classical.choose_spec (hint i j)
    have hCmap : C = M.map (Int.castRingHom ℝ) := by
      ext i j
      exact (hMcast i j).symm
    have hdet : C.det = (M.det : ℝ) := by
      rw [hCmap]
      exact (RingHom.map_det (Int.castRingHom ℝ) M).symm
    -- the coordinate of w at s equals the determinant of the coefficient matrix
    have hBw : (B.repr w) s = exteriorPower.ιMultiDual ℝ r b s w := by
      dsimp [B]
      rw [exteriorPower.basis_repr_apply ℝ r b w s]
    have hD : exteriorPower.ιMultiDual ℝ r b s w = C.det := by
      dsimp [w, C]
      rw [exteriorPower.ιMultiDual_apply_ιMulti]
      rfl
    rw [hBw, hD, hdet]
    exact ⟨M.det, rfl⟩
  have hBmem : w ∈ Submodule.span ℤ (Set.range (fun s : Set.powersetCard (Fin d) r =>
      ((b.exteriorPower r) s : ⋀[ℝ]^r (E d)))) := by
    exact (B.mem_span_iff_repr_mem ℤ w).mpr (by
      intro s
      have h := hcoord s
      -- match the coordinates (B.repr w) s
      simpa [B] using h)
  simpa [w, B] using hBmem


/-- The `r`-fold exterior power of `ℝᵈ` (ambient wedge space of `r`-planes). -/
abbrev WK (d r : ℕ) : Type := ⋀[ℝ]^r (E d)

/-- The index type of the exterior-power basis: `r`-subsets of `Fin d`. -/
abbrev IDX (d r : ℕ) : Type := Set.powersetCard (Fin d) r

/-- **Saturated hull family**: rank-`r` subgroups `M ≤ Λ` with covolume ≤ `C` which equal
their own hull (`M = hull Λ M`, i.e. `M = Λ ∩ realSpan M`). -/
abbrev SaturatedHulls {d : ℕ} (r : ℕ) (Λ : Submodule ℤ (E d)) (C : ℝ) : Type :=
  {M : Submodule ℤ (E d) // M ≤ Λ ∧ subDim M = r ∧ latticeCovol M ≤ C ∧
    M = Submission.MixedRankSpectrum.hull Λ M}

/-- The ambient `ℝ`-basis of `E d` induced by a `ℤ`-basis of the full-rank lattice `Λ`. -/
noncomputable def latticeBasisR {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) : Basis (Fin d) ℝ (E d) :=
  Module.Basis.mk (latticeZBasisE_linearIndependent_real (d := d) Λ hΛfin) (by
    rw [latticeZBasisE_spanReal_top (d := d) Λ hΛfin])

/-- The ambient basis `latticeBasisR` coincides with the ambient `ℤ`-basis of `Λ`. -/
lemma latticeBasisR_apply {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) :
    (fun i : Fin d => ((latticeBasisR Λ hΛfin i) : E d)) =
      latticeZBasisE (d := d) Λ hΛfin := by
  dsimp [latticeBasisR]
  exact Module.Basis.coe_mk (latticeZBasisE_linearIndependent_real (d := d) Λ hΛfin)
    (by rw [latticeZBasisE_spanReal_top (d := d) Λ hΛfin])

/-- Every rank-`r` subgroup `M ≤ Λ` (`0 < r`, `subDim M = r`) admits an `ℝ`-independent
`ℤ`-spanning member family indexed by `Fin r`. -/
lemma exists_repFamily {d r : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (hr0 : 0 < r)
    (M : Submodule ℤ (E d)) (hMΛ : M ≤ Λ) (hrM : subDim M = r) :
    ∃ u : Fin r → E d, LinearIndependent ℝ u ∧ (∀ i : Fin r, u i ∈ (Λ : Set (E d))) ∧
      M = Submodule.span ℤ (Set.range u) := by
  classical
  have hM0 : M ≠ ⊥ := by
    intro hz
    have hz' : subDim M = 0 := (subDim_eq_zero_iff_bot M).mpr hz
    omega
  rcases exists_basis_family_int_of_le_lattice (d := d) Λ hΛfin M hMΛ hM0 with
    ⟨cW, hli, _hzli, hmem, hM_eq⟩
  let e : Fin (subDim M) ≃ Fin r := (Fin.castOrderIso hrM).toEquiv
  let u : Fin r → E d := fun i => cW (e.symm i)
  refine ⟨u, ?_, ?_, ?_⟩
  · have hli' : LinearIndependent ℝ (fun i : Fin r => cW (e.symm i)) :=
      hli.comp e.symm e.symm.injective
    simpa [u] using hli'
  · intro i
    simpa [u] using hmem (e.symm i)
  · have hspan0 : Submodule.span ℤ (Set.range u) = Submodule.span ℤ (Set.range cW) := by
      dsimp [u]
      exact span_int_range_comp_bijective (u := cW) (e := e)
    calc
      M = Submodule.span ℤ (Set.range cW) := hM_eq
      _ = Submodule.span ℤ (Set.range u) := hspan0.symm

/-- A chosen rank-`r` `ℤ`-spanning member family of a saturated hull (see
`exists_repFamily` for the properties). -/
noncomputable def repFamily {d r : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (hr0 : 0 < r) (C : ℝ)
    (M : SaturatedHulls (d := d) r Λ C) : Fin r → E d :=
  Classical.choose (exists_repFamily (d := d) Λ hΛfin hr0 M.1 M.2.1 M.2.2.1)

/-- The wedge (Plücker vector) of a saturated hull: `ιMulti r` of its chosen family. -/
noncomputable def repWedge {d r : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (hr0 : 0 < r) (C : ℝ)
    (M : SaturatedHulls (d := d) r Λ C) : WK d r :=
  exteriorPower.ιMulti ℝ r (repFamily (d := d) Λ hΛfin hr0 C M)

/-- Properties of the chosen family: `ℝ`-independent, members of `Λ`, and `M` is its
`ℤ`-span. -/
lemma repFamily_props {d r : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (hr0 : 0 < r) (C : ℝ)
    (M : SaturatedHulls (d := d) r Λ C) :
    LinearIndependent ℝ (repFamily (d := d) Λ hΛfin hr0 C M) ∧
      (∀ i : Fin r, repFamily (d := d) Λ hΛfin hr0 C M i ∈ (Λ : Set (E d))) ∧
      M.1 = Submodule.span ℤ (Set.range (repFamily (d := d) Λ hΛfin hr0 C M)) := by
  exact Classical.choose_spec (exists_repFamily (d := d) Λ hΛfin hr0 M.1 M.2.1 M.2.2.1)

/-- **Covol = wedge norm**: for a saturated hull `M`, `latticeCovol M = ‖repWedge M‖`. -/
lemma repWedge_covol {d r : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (hr0 : 0 < r) (C : ℝ)
    (M : SaturatedHulls (d := d) r Λ C) :
    latticeCovol M.1 = ‖repWedge (d := d) Λ hΛfin hr0 C M‖ := by
  classical
  have hp := repFamily_props (d := d) Λ hΛfin hr0 C M
  calc
    latticeCovol M.1
        = latticeCovol (Submodule.span ℤ (Set.range (repFamily (d := d) Λ hΛfin hr0 C M))) := by
          exact congrArg (fun Y : Submodule ℤ (E d) => latticeCovol Y) hp.2.2
    _ = ‖exteriorPower.ιMulti ℝ r (repFamily (d := d) Λ hΛfin hr0 C M)‖ := by
          exact latticeCovol_span (d := d) (r := r) hr0
            (repFamily (d := d) Λ hΛfin hr0 C M) hp.1
    _ = ‖repWedge (d := d) Λ hΛfin hr0 C M‖ := by rfl

/-- **Integer coordinates**: the wedge of a saturated hull lies in the `ℤ`-lattice of
`⋀^r (E d)` generated by the `r`-fold exterior products of the lattice basis
(`latticeBasisR`). -/
lemma repWedge_mem_wedgeLattice {d r : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (hr0 : 0 < r) (C : ℝ)
    (M : SaturatedHulls (d := d) r Λ C) :
    repWedge (d := d) Λ hΛfin hr0 C M ∈ Submodule.span ℤ (Set.range
      (fun s : IDX d r => (((latticeBasisR (d := d) Λ hΛfin).exteriorPower r) s : WK d r))) := by
  classical
  have hp := repFamily_props (d := d) Λ hΛfin hr0 C M
  have hmem := ιMulti_mem_intSpan_of_mem_intSpan (d := d) (r := r)
    (latticeBasisR (d := d) Λ hΛfin) (repFamily (d := d) Λ hΛfin hr0 C M) (by
      intro i
      have huiΛ : repFamily (d := d) Λ hΛfin hr0 C M i ∈ (Λ : Set (E d)) := hp.2.1 i
      have hspan : repFamily (d := d) Λ hΛfin hr0 C M i ∈
          Submodule.span ℤ (Set.range (fun j : Fin d => latticeZBasisE (d := d) Λ hΛfin j)) := by
        rw [span_latticeZBasisE (d := d) Λ hΛfin]
        exact huiΛ
      have hrng : Set.range (fun j : Fin d => ((latticeBasisR (d := d) Λ hΛfin j) : E d)) =
          Set.range (fun j : Fin d => latticeZBasisE (d := d) Λ hΛfin j) := by
        rw [latticeBasisR_apply (d := d) Λ hΛfin]
      rw [hrng]
      exact hspan)
  simpa [repWedge] using hmem

/-- **Plücker injectivity on saturated hulls**: two saturated hulls with equal wedges are
equal (equal wedges give equal real spans; saturated hulls are determined by their real
span: `M = hull Λ M`). -/
lemma hull_eq_of_repWedge_eq {d r : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (hr0 : 0 < r) (C : ℝ)
    (M N : SaturatedHulls (d := d) r Λ C)
    (h : repWedge (d := d) Λ hΛfin hr0 C M = repWedge (d := d) Λ hΛfin hr0 C N) :
    M.1 = N.1 := by
  classical
  have hpM := repFamily_props (d := d) Λ hΛfin hr0 C M
  have hpN := repFamily_props (d := d) Λ hΛfin hr0 C N
  have hspanℝ : Submodule.span ℝ (Set.range (repFamily (d := d) Λ hΛfin hr0 C M)) =
      Submodule.span ℝ (Set.range (repFamily (d := d) Λ hΛfin hr0 C N)) :=
    span_eq_of_ιMulti_eq (repFamily (d := d) Λ hΛfin hr0 C M)
      (repFamily (d := d) Λ hΛfin hr0 C N) hpM.1 hpN.1 (by simpa [repWedge] using h)
  have hrM : realSpan M.1 =
      Submodule.span ℝ (Set.range (repFamily (d := d) Λ hΛfin hr0 C M)) := by
    calc
      realSpan M.1 = realSpan (Submodule.span ℤ (Set.range (repFamily (d := d) Λ hΛfin hr0 C M))) :=
            congrArg realSpan hpM.2.2
      _ = Submodule.span ℝ (Set.range (repFamily (d := d) Λ hΛfin hr0 C M)) :=
            realSpan_span_range (repFamily (d := d) Λ hΛfin hr0 C M)
  have hrN : realSpan N.1 =
      Submodule.span ℝ (Set.range (repFamily (d := d) Λ hΛfin hr0 C N)) := by
    calc
      realSpan N.1 = realSpan (Submodule.span ℤ (Set.range (repFamily (d := d) Λ hΛfin hr0 C N))) :=
            congrArg realSpan hpN.2.2
      _ = Submodule.span ℝ (Set.range (repFamily (d := d) Λ hΛfin hr0 C N)) :=
            realSpan_span_range (repFamily (d := d) Λ hΛfin hr0 C N)
  have hspanEq : realSpan M.1 = realSpan N.1 := by
    calc
      realSpan M.1 = Submodule.span ℝ (Set.range (repFamily (d := d) Λ hΛfin hr0 C M)) := hrM
      _ = Submodule.span ℝ (Set.range (repFamily (d := d) Λ hΛfin hr0 C N)) := hspanℝ
      _ = realSpan N.1 := hrN.symm
  have hsatM : M.1 = hull Λ M.1 := M.2.2.2.2
  have hsatN : N.1 = hull Λ N.1 := N.2.2.2.2
  have hhull : hull Λ M.1 = hull Λ N.1 := by
    apply Submodule.ext
    intro x
    rw [hull_mem_iff Λ M.1 x, hull_mem_iff Λ N.1 x]
    constructor
    · rintro ⟨hxΛ, hxV⟩
      exact ⟨hxΛ, by rw [← hspanEq]; exact hxV⟩
    · rintro ⟨hxΛ, hxV⟩
      exact ⟨hxΛ, by rw [hspanEq]; exact hxV⟩
  calc
    M.1 = hull Λ M.1 := hsatM
    _ = hull Λ N.1 := hhull
    _ = N.1 := hsatN.symm

/-- **H1 — finite saturated hulls**: for a full-rank lattice `Λ ≤ ℝᵈ`, a rank
`0 < r` and a bound `C`, only finitely many saturated rank-`r` subgroups `M ≤ Λ`
(`M = hull Λ M`) have intrinsic covolume `latticeCovol M ≤ C`.  Proof: the Plücker map
`M ↦ ιMulti r (ℤ-basis of M)` is injective (hull determined by real span, wedge
determines span) and lands in the finite set of integer-wedge points of `⋀^r (E d)` with
norm ≤ `max C 0` (integer coordinates from the lattice basis; boundedness from
`‖ιMulti u‖ = latticeCovol M ≤ C`). -/
theorem finite_saturatedHulls_covol_le {d r : ℕ} (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hr0 : 0 < r) (_hrd : r ≤ d) (C : ℝ) :
    Finite (SaturatedHulls (d := d) r Λ C) := by
  classical
  have hΛfin : Module.finrank ℤ Λ = d := finrank_zLattice (d := d) Λ
  let Λr : Submodule ℤ (WK d r) := Submodule.span ℤ
    (Set.range ⇑((latticeBasisR (d := d) Λ hΛfin).exteriorPower r))
  let B0 : ℝ := max C 0
  have hfinSet : ({w : WK d r | ‖w‖ ≤ B0} ∩ (Λr : Set (WK d r))).Finite := by
    have hset : {w : WK d r | ‖w‖ ≤ B0} = Metric.closedBall (0 : WK d r) B0 := by
      ext w
      rw [Metric.mem_closedBall, dist_eq_norm]
      simp
    rw [hset]
    dsimp [Λr]
    exact ZSpan.setFinite_inter (E := WK d r)
      (b := ((latticeBasisR (d := d) Λ hΛfin).exteriorPower r))
      (s := Metric.closedBall (0 : WK d r) B0) Metric.isBounded_closedBall
  let T : Type := {w : WK d r // w ∈ {x : WK d r | ‖x‖ ≤ B0} ∩ (Λr : Set (WK d r))}
  haveI : Finite T := by
    dsimp [T]
    exact hfinSet.to_subtype
  let ψ : SaturatedHulls (d := d) r Λ C → T := fun M => by
    classical
    let w : WK d r := repWedge (d := d) Λ hΛfin hr0 C M
    have hw1 : ‖w‖ ≤ B0 := by
      dsimp [w, B0]
      have hcov : latticeCovol M.1 = ‖repWedge (d := d) Λ hΛfin hr0 C M‖ :=
        repWedge_covol (d := d) Λ hΛfin hr0 C M
      calc
        ‖repWedge (d := d) Λ hΛfin hr0 C M‖ = latticeCovol M.1 := hcov.symm
        _ ≤ C := M.2.2.2.1
        _ ≤ max C 0 := le_max_left C 0
    have hw2 : w ∈ (Λr : Set (WK d r)) := by
      dsimp [Λr, w]
      simpa using (repWedge_mem_wedgeLattice (d := d) Λ hΛfin hr0 C M)
    exact ⟨w, ⟨hw1, hw2⟩⟩
  have hψinj : Function.Injective ψ := by
    intro M N hMN
    apply Subtype.ext
    exact hull_eq_of_repWedge_eq (d := d) Λ hΛfin hr0 C M N (by
      simpa [ψ] using congrArg (fun t : T => t.1) hMN)
  exact Finite.of_injective ψ hψinj

/-- **Mixed-rank covolume-spectrum discreteness** (`H1 + H2 + H3` assembly): for a
full-rank lattice `Λ ≤ ℝᵈ`, every rank `0 < r ≤ d` and bound `C`, only finitely many
rank-`r` discrete subgroups `W ≤ Λ` have intrinsic covolume `latticeCovol W ≤ C` (no
saturation hypothesis).  Decompose `W ↦ (M = hull Λ W, W)`: the hull `M` runs over the
finite saturated-hull set of bound `C` (`finite_saturatedHulls_covol_le` +
`covol_hull_le_covol`), and `W` runs over the finite fibre above `M`
(`IntrinsicIndex.finite_fibre_covol_le`). -/
theorem finite_mixedRankSpectrum {d r : ℕ} (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hr0 : 0 < r) (hrd : r ≤ d) (C : ℝ) :
    mixedRankSpectrumStatement r Λ C := by
  classical
  dsimp [mixedRankSpectrumStatement]
  have hΛfin : Module.finrank ℤ Λ = d := finrank_zLattice (d := d) Λ
  let H : Type := SaturatedHulls (d := d) r Λ C
  let β : H → Type := fun M => {W : Submodule ℤ (E d) // W ≤ M.1 ∧
    subDim W = subDim M.1 ∧ latticeCovol W ≤ C}
  haveI : Finite H := by
    dsimp [H]
    exact finite_saturatedHulls_covol_le (d := d) Λ hr0 hrd C
  haveI : ∀ M : H, Finite (β M) := by
    intro M
    have hM0 : M.1 ≠ ⊥ := by
      intro hz
      have hz' : subDim M.1 = 0 := (subDim_eq_zero_iff_bot M.1).mpr hz
      have hrM : subDim M.1 = r := M.2.2.1
      omega
    dsimp [β]
    exact finite_fibre_covol_le (d := d) Λ M.1 M.2.1 hM0 C
  let A : Type := {W : Submodule ℤ (E d) // W ≤ Λ ∧ subDim W = r ∧ latticeCovol W ≤ C}
  let F : Type := Σ M : H, β M
  haveI : Finite F := by
    dsimp [F]
    infer_instance
  let ψ : A → F := fun X => by
    classical
    -- the hull M = hull Λ X.1 is a saturated rank-r subgroup of Λ with covol ≤ C
    have hW0 : X.1 ≠ ⊥ := by
      intro hz
      have hz' : subDim X.1 = 0 := (subDim_eq_zero_iff_bot X.1).mpr hz
      omega
    have hMΛ : hull Λ X.1 ≤ Λ := hull_le_Λ Λ X.1
    have hMsub : subDim (hull Λ X.1) = r := by
      rw [subDim_hull_eq Λ X.1 X.2.1, X.2.2.1]
    have hMcov : latticeCovol (hull Λ X.1) ≤ C := by
      exact le_trans (covol_hull_le_covol (d := d) Λ X.1 X.2.1 hW0) X.2.2.2
    have hMsat : hull Λ X.1 = hull Λ (hull Λ X.1) := (hull_idempotent Λ X.1 X.2.1).symm
    -- X.1 in the fibre over the hull
    have hXle : X.1 ≤ hull Λ X.1 := W_le_hull Λ X.1 X.2.1
    have hXsub : subDim X.1 = subDim (hull Λ X.1) := by
      rw [hMsub, X.2.2.1]
    exact ⟨⟨hull Λ X.1, ⟨hMΛ, hMsub, hMcov, hMsat⟩⟩, ⟨X.1, hXle, hXsub, X.2.2.2⟩⟩
  have hψinj : Function.Injective ψ := by
    intro U V h
    apply Subtype.ext
    exact congrArg (fun t : F => t.2.1) h
  haveI : Finite A := Finite.of_injective ψ hψinj
  -- A is definitionally the goal type
  simpa [A]

end Submission.FiniteSaturatedHulls

