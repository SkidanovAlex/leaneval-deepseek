import Mathlib
import Submission.Work.Whitney.PathTools.JaniszewskiTwo
import Submission.Work.Whitney.PathTools.snapping
import Submission.Work.Whitney.PathTools.plane_arc_nonseparation
import Submission.Work.Whitney.PathTools.TotallyDisconnectedPlane
import Submission.Work.Whitney.PathTools.GridAux

/-!
# The complement of a compact arc in the plane is path connected

Target: `Work.Whitney.PathTools.joinedIn_compl_of_arc_plane`: for `K ⊆ ℝ` compact and
`γ : ℝ → ℝ²` continuous and injective on `K`, any two points outside `γ '' K` can be joined by a
path avoiding `γ '' K`.

The proof is assembled from the classical planar theory built in this directory:

* `Grid.exists_subinterval_subset_not_joinedIn` (Zorn / minimal-separator reduction, adapted from
  `plane_arc_nonseparation.exists_subinterval_not_joinedIn`) reduces the statement to the genuine
  arc case: there are `a ≤ b` with `Icc a b ⊆ K` such that `γ '' Icc a b` still separates;
* `Grid.arc_compl_joinedIn_interval` (the classical "a Jordan arc does not separate the plane",
  McCleary, *A First Course in Topology*, Chapter 9) handles that case by bisection, using
  `Grid.janis_singleton_general` (the planar Janiszewski theorem for two compacta meeting in a
  single point) at each bisection step.

The grid-theoretic part of the argument for `janis_singleton_general` (McCleary's "Alexander
Theorem", via a two-mesh subdivision of the mod-two grid chain complex of
`Submission/Work/Whitney/PathTools/Grid.lean`) is set up below: `Grid.sub2`/`Grid.sub1` and the
chain-map property `Grid.bdry2_sub2`.
-/

namespace Work.Whitney.PathTools
namespace Grid

noncomputable section

open Set Metric
open scoped BigOperators Topology

/-! ## Reading off paths from chains -/

/-- An edge outside `edgeSet (cellSet h K)` has a locus disjoint from `K`. -/
lemma disjoint_gseg_of_notMem_edgeSet {h : ℝ} (hh : 0 < h) {K : Set Pt} {e : Edge}
    (he : e ∉ edgeSet (cellSet h K)) : Disjoint (gseg h e) K := by
  rw [Set.disjoint_left]
  intro z hz hzK
  exact he ⟨eCell e, ⟨z, gseg_subset_gsq hh e hz, hzK⟩, mem_cellEdges_eCell e⟩

/-! ## Two-mesh subdivision of grid chains
The subdivision `sub2`/`sub1`/`sub0` of grid chains and the chain-map properties
`bdry2_sub2`, `bdry1_sub1` live in `Submission/Work/Whitney/PathTools/GridAux.lean`. -/

set_option maxHeartbeats 1600000 in
/-- **The planar Janiszewski theorem for two compacta meeting in a single point.**

If `K, L` are compact, `K ∩ L = {p}`, and `x, y ∉ K ∪ L` can be joined by paths avoiding `K`
and avoiding `L` respectively, then they can be joined by a path avoiding `K ∪ L`.

Classical; McCleary, *A First Course in Topology*, Chapter 9, Corollary 9.11, deduced there from
the "Alexander Theorem" of that chapter.  The combinatorial toolkit is the mod-two grid chain
complex of `Grid.lean`: `bdry2_fill` (every grid `1`-cycle is a boundary), `edgeSet`, `cellSet`,
`cellSet_geometry` (grid separation of the cell sets of two compacta at distance `> 8h√2`) and
`exists_chain_avoiding_union` (the Alexander splitting lemma), plus `Snap.exists_chain_avoiding`
and `joinedIn_of_chain` to pass between paths and chains.

*Proof plan (McCleary's Alexander theorem with the two-mesh subdivision above).*  Snap the two
paths at a coarse mesh `h₀` to chains `l₁` (avoiding `edgeSet (cellSet h₀ K)`) and `l₂` (avoiding
`edgeSet (cellSet h₀ L)`) with a common boundary `u + v`.  Let `W` be a `2`-chain with
`∂W = l₁ + l₂` and `p ∉ |W|`; for the two natural fillings `fill (l₁+l₂)` and
`fill (l₁+l₂) + Θ₂` (`Θ₂` the constant `2`-chain, with `∂Θ₂ = 0`) this holds whenever `p` lies in
the interior of a mesh cell, as one of the two avoids that cell.  Subdivide at a mesh `h₀/n` fine
compared with `δ = dist (|W| ∩ K, |W| ∩ L) > 0`.  Subdivision preserves loci, so every fine cell of
`W*` meeting `K` meets `|W| ∩ K` and hence avoids `|W| ∩ L`, therefore avoids `L`: this is the
condition (α) needed for McCleary's modification `l₀ = l₂* + ∂(w_K)`, where `w_K` is the
restriction of `W*` to the cells meeting `K`.  Then `l₀ = l₁* + ∂(W* + w_K)` avoids `K` (no cell
of `W* + w_K` meets `K`) and `l₀` avoids `L` (by (α), since `|l₂*| ∩ L = ∅`); reading off the walk
from `l₀` gives the required path. -/
theorem janis_singleton_general {K L : Set Pt} (hK : IsCompact K) (hL : IsCompact L)
    {p : Pt} (hKL : K ∩ L = {p}) {x y : Pt} (hx : x ∉ K ∪ L) (hy : y ∉ K ∪ L)
    (h₁ : JoinedIn (Kᶜ) x y) (h₂ : JoinedIn (Lᶜ) x y) :
    JoinedIn ((K ∪ L)ᶜ) x y := by
  classical
  rcases eq_or_ne x y with rfl | hxy
  · exact JoinedIn.refl (by
      rw [Set.mem_compl_iff, Set.mem_union, not_or]
      exact ⟨fun h => hx (Or.inl h), fun h => hx (Or.inr h)⟩)
  obtain ⟨γ₁, hγ₁⟩ := h₁
  obtain ⟨γ₂, hγ₂⟩ := h₂
  -- ================= STEP 1: the mesh =================
  obtain ⟨d₁, hd₁pos, hd₁⟩ := exists_pos_le_dist (isCompact_range γ₁.continuous) hK
    (fun a ha b hb => dist_pos.mpr (fun h0 => by
      obtain ⟨t, rfl⟩ := ha
      have h1 : γ₁ t ∈ Kᶜ := hγ₁ t
      rw [Set.mem_compl_iff] at h1
      exact h1 (h0 ▸ hb)))
  obtain ⟨d₂, hd₂pos, hd₂⟩ := exists_pos_le_dist (isCompact_range γ₂.continuous) hL
    (fun a ha b hb => dist_pos.mpr (fun h0 => by
      obtain ⟨t, rfl⟩ := ha
      have h1 : γ₂ t ∈ Lᶜ := hγ₂ t
      rw [Set.mem_compl_iff] at h1
      exact h1 (h0 ▸ hb)))
  obtain ⟨dx, hdxpos, hdx⟩ := exists_pos_le_dist ((Set.finite_singleton x).isCompact) (hK.union hL)
    (fun a ha b hb => dist_pos.mpr (fun h0 => by
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hx (h0 ▸ hb)))
  obtain ⟨dy, hdypos, hdy⟩ := exists_pos_le_dist ((Set.finite_singleton y).isCompact) (hK.union hL)
    (fun a ha b hb => dist_pos.mpr (fun h0 => by
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hy (h0 ▸ hb)))
  set hh : ℝ := min (min d₁ d₂) (min dx dy) / 80 with hhh
  have hhpos : 0 < hh := by
    rw [hhh]
    exact div_pos (lt_min (lt_min hd₁pos hd₂pos) (lt_min hdxpos hdypos)) (by norm_num)
  have hh_d₁ : 20 * hh ≤ d₁ := by
    have h1 : hh ≤ d₁ / 80 := by
      rw [hhh]
      have h2 : min (min d₁ d₂) (min dx dy) ≤ d₁ := (min_le_left _ _).trans (min_le_left _ _)
      linarith
    linarith
  have hh_d₂ : 20 * hh ≤ d₂ := by
    have h1 : hh ≤ d₂ / 80 := by
      rw [hhh]
      have h2 : min (min d₁ d₂) (min dx dy) ≤ d₂ := (min_le_left _ _).trans (min_le_right _ _)
      linarith
    linarith
  have hh_dx : 80 * hh ≤ dx := by
    have h1 : hh ≤ dx / 80 := by
      rw [hhh]
      have h2 : min (min d₁ d₂) (min dx dy) ≤ dx := (min_le_right _ _).trans (min_le_left _ _)
      linarith
    linarith
  have hh_dy : 80 * hh ≤ dy := by
    have h1 : hh ≤ dy / 80 := by
      rw [hhh]
      have h2 : min (min d₁ d₂) (min dx dy) ≤ dy := (min_le_right _ _).trans (min_le_right _ _)
      linarith
    linarith
  -- ================= STEP 2: the shift =================
  set v : Pt := p - (hh / 3) • gpt (1, 1) with hv
  have hpv0 : (p - v) 0 = hh / 3 := by
    rw [hv]
    simp only [PiLp.sub_apply, PiLp.smul_apply, gpt_apply_zero]
    norm_num
  have hpv1 : (p - v) 1 = hh / 3 := by
    rw [hv]
    simp only [PiLp.sub_apply, PiLp.smul_apply, gpt_apply_one]
    norm_num
  set x' : Pt := x - v with hx'
  set y' : Pt := y - v with hy'
  set K' : Set Pt := (fun z => z - v) '' K with hK'
  set L' : Set Pt := (fun z => z - v) '' L with hL'
  have hK'c : IsCompact K' := by rw [hK']; exact hK.image (continuous_id.sub continuous_const)
  have hL'c : IsCompact L' := by rw [hL']; exact hL.image (continuous_id.sub continuous_const)
  have hx'ne : x' ∉ K' ∪ L' := by
    rw [hx', hK', hL', Set.mem_union]
    push_neg
    constructor
    · rintro ⟨z, hz, hzv⟩
      refine hx (Or.inl ?_)
      have h2 : z = x := by
        have := congrArg (fun s : Pt => s + v) hzv
        simpa using this
      rwa [h2] at hz
    · rintro ⟨z, hz, hzv⟩
      refine hx (Or.inr ?_)
      have h2 : z = x := by
        have := congrArg (fun s : Pt => s + v) hzv
        simpa using this
      rwa [h2] at hz
  have hy'ne : y' ∉ K' ∪ L' := by
    rw [hy', hK', hL', Set.mem_union]
    push_neg
    constructor
    · rintro ⟨z, hz, hzv⟩
      refine hy (Or.inl ?_)
      have h2 : z = y := by
        have := congrArg (fun s : Pt => s + v) hzv
        simpa using this
      rwa [h2] at hz
    · rintro ⟨z, hz, hzv⟩
      refine hy (Or.inr ?_)
      have h2 : z = y := by
        have := congrArg (fun s : Pt => s + v) hzv
        simpa using this
      rwa [h2] at hz
  have hγ₁c : Continuous (fun t : unitInterval => γ₁ t - v) :=
    γ₁.continuous.sub continuous_const
  have hγ₂c : Continuous (fun t : unitInterval => γ₂ t - v) :=
    γ₂.continuous.sub continuous_const
  let γ₁' : Path x' y' := ⟨⟨fun t => γ₁ t - v, hγ₁c⟩,
    (by dsimp only; rw [hx', Path.source]),
    (by dsimp only; rw [hy', Path.target])⟩
  let γ₂' : Path x' y' := ⟨⟨fun t => γ₂ t - v, hγ₂c⟩,
    (by dsimp only; rw [hx', Path.source]),
    (by dsimp only; rw [hy', Path.target])⟩
  have hγ₁'val : ∀ t : unitInterval, γ₁' t = γ₁ t - v := fun t => rfl
  have hγ₂'val : ∀ t : unitInterval, γ₂' t = γ₂ t - v := fun t => rfl
  have hγ₁'mem : ∀ t : unitInterval, γ₁' t ∈ (K')ᶜ := by
    intro t
    rw [Set.mem_compl_iff]
    rintro ⟨z, hz, hzv⟩
    have h1 : γ₁ t ∈ Kᶜ := hγ₁ t
    rw [Set.mem_compl_iff] at h1
    refine h1 ?_
    rw [hγ₁'val t] at hzv
    have h3 : γ₁ t = z := by
      simpa using (congrArg (fun s : Pt => s + v) hzv).symm
    rw [h3]
    exact hz
  have hγ₂'mem : ∀ t : unitInterval, γ₂' t ∈ (L')ᶜ := by
    intro t
    rw [Set.mem_compl_iff]
    rintro ⟨z, hz, hzv⟩
    have h1 : γ₂ t ∈ Lᶜ := hγ₂ t
    rw [Set.mem_compl_iff] at h1
    refine h1 ?_
    rw [hγ₂'val t] at hzv
    have h3 : γ₂ t = z := by
      simpa using (congrArg (fun s : Pt => s + v) hzv).symm
    rw [h3]
    exact hz
  have hsub_dist : ∀ a b : Pt, dist (a - v) (b - v) = dist a b := by
    intro a b
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    abel
  have hdist₁ : ∀ t : unitInterval, ∀ s ∈ K', 20 * hh ≤ dist (γ₁' t) s := by
    rintro t s ⟨z, hz, rfl⟩
    rw [hγ₁'val t, hsub_dist]
    exact le_trans hh_d₁ (hd₁ (γ₁ t) ⟨t, rfl⟩ z hz)
  have hdist₂ : ∀ t : unitInterval, ∀ s ∈ L', 20 * hh ≤ dist (γ₂' t) s := by
    rintro t s ⟨z, hz, rfl⟩
    rw [hγ₂'val t, hsub_dist]
    exact le_trans hh_d₂ (hd₂ (γ₂ t) ⟨t, rfl⟩ z hz)
  have hdx' : ∀ s ∈ K' ∪ L', 20 * hh ≤ dist x' s := by
    rintro s (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · have h2 : x' = x - v := by rw [hx']
      rw [h2, hsub_dist]
      exact le_trans (by linarith [hh_dx]) (hdx x rfl z (Or.inl hz))
    · have h2 : x' = x - v := by rw [hx']
      rw [h2, hsub_dist]
      exact le_trans (by linarith [hh_dx]) (hdx x rfl z (Or.inr hz))
  have hdy' : ∀ s ∈ K' ∪ L', 20 * hh ≤ dist y' s := by
    rintro s (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · have h2 : y' = y - v := by rw [hy']
      rw [h2, hsub_dist]
      exact le_trans (by linarith [hh_dy]) (hdy y rfl z (Or.inl hz))
    · have h2 : y' = y - v := by rw [hy']
      rw [h2, hsub_dist]
      exact le_trans (by linarith [hh_dy]) (hdy y rfl z (Or.inr hz))
  -- ================= STEP 3: snapping to the coarse grid =================
  obtain ⟨m1, hb₁, hav₁⟩ := exists_chain_avoiding (S := K') hhpos (X := x') (Y := y')
    (γ := γ₁') hdist₁
  obtain ⟨m2, hb₂, hav₂⟩ := exists_chain_avoiding (S := L') hhpos (X := x') (Y := y')
    (γ := γ₂') hdist₂
  set P : ℤ × ℤ := nearGrid hh x' with hP
  set Q : ℤ × ℤ := nearGrid hh y' with hQ
  have hb₁' : ∀ w : ℤ × ℤ, bdry1 ((m1 : Chain1) : Edge → ZMod 2) w
      = (if w = P then 1 else 0) + (if w = Q then 1 else 0) := by
    intro w
    rw [hb₁ w, hP, hQ]
  have hb₂' : ∀ w : ℤ × ℤ, bdry1 ((m2 : Chain1) : Edge → ZMod 2) w
      = (if w = P then 1 else 0) + (if w = Q then 1 else 0) := by
    intro w
    rw [hb₂ w, hP, hQ]
  -- ================= STEP 4: the filling =================
  set c : Chain1 := m1 + m2 with hc
  have hbc : bdry1 (c : Edge → ZMod 2) = 0 := by
    funext w
    rw [hc, Finsupp.coe_add, bdry1_add, Pi.add_apply, hb₁' w, hb₂' w, Pi.zero_apply]
    rw [show (if w = P then (1 : ZMod 2) else 0) + (if w = Q then (1 : ZMod 2) else 0)
          + ((if w = P then (1 : ZMod 2) else 0) + (if w = Q then (1 : ZMod 2) else 0))
        = ((if w = P then (1 : ZMod 2) else 0) + (if w = P then (1 : ZMod 2) else 0))
          + ((if w = Q then (1 : ZMod 2) else 0) + (if w = Q then (1 : ZMod 2) else 0))
        from by abel,
      CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
  set W₀ : C2 := fill c with hW₀
  have hW₀b : bdry2 W₀ = (c : Edge → ZMod 2) := by rw [hW₀]; exact bdry2_fill c hbc
  have hcell_unique : ∀ cc : Cell, p - v ∈ gsq hh cc → cc = (0, 0) := by
    intro cc hc
    obtain ⟨g1, g2, g3, g4⟩ := hc
    rw [hpv0] at g1 g2
    rw [hpv1] at g3 g4
    have h1 : cc.1 = 0 := by
      have hle : (cc.1 : ℝ) < 1 := by nlinarith [hhpos]
      have hge : (-1 : ℝ) < (cc.1 : ℝ) := by nlinarith [hhpos, g2]
      have hle' : cc.1 < 1 := by exact_mod_cast hle
      have hge' : -1 < cc.1 := by exact_mod_cast hge
      omega
    have h2 : cc.2 = 0 := by
      have hle : (cc.2 : ℝ) < 1 := by nlinarith [hhpos]
      have hge : (-1 : ℝ) < (cc.2 : ℝ) := by nlinarith [hhpos, g4]
      have hle' : cc.2 < 1 := by exact_mod_cast hle
      have hge' : -1 < cc.2 := by exact_mod_cast hge
      omega
    exact Prod.ext h1 h2
  have hZMod2 : ∀ z : ZMod 2, z + 1 ≠ 0 → z ≠ 0 → False := by decide
  set W : C2 := if W₀ (0, 0) = 0 then W₀ else W₀ + Theta2 with hW
  have hWb : bdry2 W = (c : Edge → ZMod 2) := by
    rw [hW]
    split
    · exact hW₀b
    · rw [bdry2_add, hW₀b, bdry2_Theta2, add_zero]
  have hpvW : p - v ∉ locus hh W := by
    rw [hW]
    split
    · rename_i h0
      rintro ⟨cc, hcc, hccm⟩
      rw [hcell_unique cc hccm] at hcc
      exact hcc h0
    · rename_i h0
      rintro ⟨cc, hcc, hccm⟩
      rw [hcell_unique cc hccm] at hcc
      exact hZMod2 _ hcc h0
  -- ================= STEP 5: the separation and the fine mesh =================
  have hKW : IsCompact (locus hh W ∩ K') := by
    have heq : locus hh W ∩ K' =
        ⋃ cc ∈ (Function.support W ∩ cellSet hh K'), (gsq hh cc ∩ K') := by
      ext z
      constructor
      · rintro ⟨⟨cc, hcc, hccm⟩, hzK⟩
        exact Set.mem_iUnion.mpr ⟨cc, Set.mem_iUnion.mpr ⟨⟨hcc, ⟨z, hccm, hzK⟩⟩, ⟨hccm, hzK⟩⟩⟩
      · intro hz
        obtain ⟨cc, hz2⟩ := Set.mem_iUnion.mp hz
        obtain ⟨hccT, hzK⟩ := Set.mem_iUnion.mp hz2
        exact ⟨⟨cc, hccT.1, hzK.1⟩, hzK.2⟩
    rw [heq]
    have hTfin : (Function.support W ∩ cellSet hh K').Finite :=
      Set.Finite.subset (cellSet_finite hhpos hK'c) (fun x hx => hx.2)
    have hfin_eq : (⋃ cc ∈ hTfin.toFinset, (gsq hh cc ∩ K'))
        = (⋃ cc ∈ (Function.support W ∩ cellSet hh K'), (gsq hh cc ∩ K')) := by
      ext z
      simp only [Set.mem_iUnion, hTfin.mem_toFinset]
    rw [← hfin_eq]
    exact isCompact_biUnion_finset hTfin.toFinset
      (fun cc _ => hK'c.of_isClosed_subset ((isClosed_gsq hh cc).inter hK'c.isClosed)
        (fun z hz => hz.2))
  have hLW : IsCompact (locus hh W ∩ L') := by
    have heq : locus hh W ∩ L' =
        ⋃ cc ∈ (Function.support W ∩ cellSet hh L'), (gsq hh cc ∩ L') := by
      ext z
      constructor
      · rintro ⟨⟨cc, hcc, hccm⟩, hzK⟩
        exact Set.mem_iUnion.mpr ⟨cc, Set.mem_iUnion.mpr ⟨⟨hcc, ⟨z, hccm, hzK⟩⟩, ⟨hccm, hzK⟩⟩⟩
      · intro hz
        obtain ⟨cc, hz2⟩ := Set.mem_iUnion.mp hz
        obtain ⟨hccT, hzK⟩ := Set.mem_iUnion.mp hz2
        exact ⟨⟨cc, hccT.1, hzK.1⟩, hzK.2⟩
    rw [heq]
    have hTfin : (Function.support W ∩ cellSet hh L').Finite :=
      Set.Finite.subset (cellSet_finite hhpos hL'c) (fun x hx => hx.2)
    have hfin_eq : (⋃ cc ∈ hTfin.toFinset, (gsq hh cc ∩ L'))
        = (⋃ cc ∈ (Function.support W ∩ cellSet hh L'), (gsq hh cc ∩ L')) := by
      ext z
      simp only [Set.mem_iUnion, hTfin.mem_toFinset]
    rw [← hfin_eq]
    exact isCompact_biUnion_finset hTfin.toFinset
      (fun cc _ => hL'c.of_isClosed_subset ((isClosed_gsq hh cc).inter hL'c.isClosed)
        (fun z hz => hz.2))
  have hdisjW : Disjoint (locus hh W ∩ K') (locus hh W ∩ L') := by
    rw [Set.disjoint_left]
    rintro z ⟨hzW, hzK⟩ ⟨-, hzL⟩
    have hKLeq : K' ∩ L' = {p - v} := by
      rw [hK', hL', ← Set.image_inter (fun a b hab => by simpa using hab), hKL]
      simp
    exact hpvW (by
      have hthis : z ∈ K' ∩ L' := ⟨hzK, hzL⟩
      rw [hKLeq, Set.mem_singleton_iff] at hthis
      rwa [← hthis])
  obtain ⟨δc, hδcpos, hδc⟩ := exists_pos_le_dist hKW hLW
    (fun a ha b hb => dist_pos.mpr fun h0 => Set.disjoint_left.mp hdisjW ha (h0 ▸ hb))
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨n, hnpos, hnδ⟩ : ∃ n : ℕ, 0 < n ∧ 2 * ((hh / n) * Real.sqrt 2) < δc := by
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * hh * Real.sqrt 2 / δc)
    refine ⟨k + 1, Nat.succ_pos k, ?_⟩
    have h1 : 2 * hh * Real.sqrt 2 / δc < ((k + 1 : ℕ) : ℝ) := by
      have h2 : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
      linarith
    rw [div_lt_iff₀ hδcpos] at h1
    have h3 : 2 * ((hh / ((k + 1 : ℕ) : ℝ)) * Real.sqrt 2)
        = 2 * hh * Real.sqrt 2 / ((k + 1 : ℕ) : ℝ) := by ring
    rw [h3, div_lt_iff₀ (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))]
    linarith
  set hf : ℝ := hh / n with hfdef
  have hfpos : 0 < hf := by rw [hfdef]; exact div_pos hhpos (by exact_mod_cast hnpos)
  have hnfac : 2 * (hf * Real.sqrt 2) < δc := by
    rw [hfdef]; exact hnδ
  -- ================= STEP 6: the fine chains and the modification =================
  set l1f : Edge → ZMod 2 := sub1 n (m1 : Edge → ZMod 2) with hl1f
  set l2f : Edge → ZMod 2 := sub1 n (m2 : Edge → ZMod 2) with hl2f
  set Wf : C2 := sub2 n W with hWf
  have hWfb : bdry2 Wf = l1f + l2f := by
    rw [hWf, bdry2_sub2 hnpos, hWb, hc, Finsupp.coe_add, sub1_add]
  set S : Set Cell := cellSet hf K' with hS
  have hSfin : S.Finite := by rw [hS]; exact cellSet_finite hfpos hK'c
  set WK : C2 := arestrict Wf S with hWK
  have hWKzero : ∀ cc ∉ S, WK cc = 0 := by
    intro cc hcc; rw [hWK]; exact arestrict_zero Wf S cc hcc
  have hWKself : ∀ cc ∈ S, WK cc = Wf cc := by
    intro cc hcc; rw [hWK]; exact arestrict_self Wf S cc hcc
  have hsupp_sub : Function.support (fun e => l2f e + bdry2 WK e) ⊆
      Function.support l2f ∪ edgeSet S := by
    intro e he
    rw [Function.mem_support] at he
    by_cases h2 : l2f e = 0
    · refine Or.inr (support_bdry2 WK (by intro cc hcc; exact hWKzero cc hcc) ?_)
      intro h0
      exact he (by rw [h2, h0, add_zero])
    · exact Or.inl (Function.mem_support.mpr h2)
  have h2supp : (Function.support ((m2 : Chain1) : Edge → ZMod 2)).Finite := by
    rw [Finsupp.fun_support_eq]
    exact m2.support.finite_toSet
  have hfin0 : (Function.support (fun e => l2f e + bdry2 WK e)).Finite :=
    ((support_sub1_finite hnpos h2supp).union (edgeSet_finite hSfin)).subset hsupp_sub
  set m0 : Chain1 := Finsupp.ofSupportFinite (fun e => l2f e + bdry2 WK e) hfin0 with hl0
  have hl0coe : (m0 : Edge → ZMod 2) = fun e => l2f e + bdry2 WK e := Finsupp.ofSupportFinite_coe
  have hl0eq : (m0 : Edge → ZMod 2) = l2f + bdry2 WK := by
    rw [hl0coe]; rfl
  -- ================= STEP 7: the new chain and its boundary =================
  have hb0 : ∀ w : ℤ × ℤ, bdry1 ((m0 : Chain1) : Edge → ZMod 2) w
      = (if w = (n * P.1, n * P.2) then 1 else 0)
        + (if w = (n * Q.1, n * Q.2) then 1 else 0) := by
    intro w
    rw [hl0eq, bdry1_add, Pi.add_apply, hl2f, bdry1_sub1 hnpos,
      show bdry1 ((m2 : Chain1) : Edge → ZMod 2)
        = (fun w => (if w = P then (1 : ZMod 2) else 0) + (if w = Q then 1 else 0))
        from funext hb₂', sub0_pair hnpos P Q, bdry1_bdry2, Pi.zero_apply, add_zero]
  -- ================= STEP 8: the avoidances =================
  -- `m0 = l1f + ∂(Wf + WK)`
  have hdecomp1 : ((m0 : Chain1) : Edge → ZMod 2) = l1f + bdry2 (Wf + WK) := by
    funext e
    rw [hl0coe]
    change l2f e + bdry2 WK e = l1f e + (bdry2 (Wf + WK)) e
    rw [bdry2_add, Pi.add_apply, congrFun hWfb e]
    simp only [Pi.add_apply]
    generalize l1f e = A
    generalize l2f e = B
    generalize bdry2 WK e = C
    rw [show A + (A + B + C) = (A + A) + (B + C) from by abel, CharTwo.add_self_eq_zero,
      zero_add]
  -- `m0 = l2f + ∂WK`
  have hdecomp2 : ((m0 : Chain1) : Edge → ZMod 2) = l2f + bdry2 WK := hl0eq
  have hloc0K : elocus hf ((m0 : Chain1) : Edge → ZMod 2)
      ⊆ elocus hh ((m1 : Chain1) : Edge → ZMod 2) ∪ locus hf (Wf + WK) := by
    intro z hz
    rw [hdecomp1] at hz
    rcases elocus_add_subset hz with h | h
    · exact Or.inl (by
        have hh' : elocus hf l1f ⊆ elocus hh ((m1 : Chain1) : Edge → ZMod 2) := by
          rw [hl1f, hfdef]
          exact elocus_sub1_subset hnpos hhpos
        exact hh' h)
    · exact Or.inr ((elocus_bdry2_subset_locus (h := hf) hfpos (Wf + WK)) h)
  have hloc0L : elocus hf ((m0 : Chain1) : Edge → ZMod 2)
      ⊆ elocus hh ((m2 : Chain1) : Edge → ZMod 2) ∪ locus hf WK := by
    intro z hz
    rw [hdecomp2] at hz
    rcases elocus_add_subset hz with h | h
    · exact Or.inl (by
        have hh' : elocus hf l2f ⊆ elocus hh ((m2 : Chain1) : Edge → ZMod 2) := by
          rw [hl2f, hfdef]
          exact elocus_sub1_subset hnpos hhpos
        exact hh' h)
    · exact Or.inr ((elocus_bdry2_subset_locus (h := hf) hfpos WK) h)
  -- the avoidances of the coarse chains
  have hlocm1 : Disjoint (elocus hh ((m1 : Chain1) : Edge → ZMod 2)) K' := by
    rw [Set.disjoint_left]
    rintro z ⟨e, he, hz⟩
    exact Set.disjoint_left.mp (disjoint_gseg_of_notMem_edgeSet hhpos (hav₁ e (Finsupp.mem_support_iff.mpr he))) hz
  have hlocm2 : Disjoint (elocus hh ((m2 : Chain1) : Edge → ZMod 2)) L' := by
    rw [Set.disjoint_left]
    rintro z ⟨e, he, hz⟩
    exact Set.disjoint_left.mp (disjoint_gseg_of_notMem_edgeSet hhpos (hav₂ e (Finsupp.mem_support_iff.mpr he))) hz
  -- no cell of `Wf + WK` meets `K'`
  have hcellK : ∀ cc, (Wf + WK) cc ≠ 0 → Disjoint (gsq hf cc) K' := by
    intro cc hcc
    rw [Set.disjoint_left]
    intro z hz hzK
    by_cases hccS : cc ∈ S
    · have h1 : WK cc = Wf cc := hWKself cc hccS
      rw [Pi.add_apply, h1, CharTwo.add_self_eq_zero] at hcc
      exact hcc rfl
    · exact hccS (by rw [hS]; exact ⟨z, hz, hzK⟩)
  have hlocWL : Disjoint (locus hf (Wf + WK)) K' := by
    rw [Set.disjoint_left]
    rintro z ⟨cc, hcc, hccm⟩ hzK
    exact Set.disjoint_left.mp (hcellK cc hcc) hccm hzK
  -- no cell of `WK` meets `L'` (condition (α))
  have hcellL : ∀ cc, WK cc ≠ 0 → Disjoint (gsq hf cc) L' := by
    intro cc hcc
    have hccS : cc ∈ S := by
      by_contra hcon
      rw [hWKzero cc hcon] at hcc
      exact hcc rfl
    have hccW : W (cc.1 / (n : ℤ), cc.2 / (n : ℤ)) ≠ 0 := by
      have h1 : WK cc = Wf cc := hWKself cc hccS
      have h2 : Wf cc = W (cc.1 / (n : ℤ), cc.2 / (n : ℤ)) := by rw [hWf]; rfl
      rw [h1, h2] at hcc
      exact hcc
    have hccS' := hccS
    obtain ⟨k, hk⟩ := hccS'
    obtain ⟨hkgsq, hkK⟩ := hk
    rw [Set.disjoint_left]
    intro z hz hzL
    have hk_loc : k ∈ locus hh W ∩ K' :=
      ⟨⟨(cc.1 / (n : ℤ), cc.2 / (n : ℤ)), hccW, gsq_sub2_subset hnpos hhpos cc hkgsq⟩, hkK⟩
    have hz_loc : z ∈ locus hh W ∩ L' :=
      ⟨⟨(cc.1 / (n : ℤ), cc.2 / (n : ℤ)), hccW, gsq_sub2_subset hnpos hhpos cc hz⟩, hzL⟩
    have hd1 : δc ≤ dist k z := hδc k hk_loc z hz_loc
    obtain ⟨hk1, hk2, hk3, hk4⟩ := hkgsq
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
    have hcoord1 : |k 0 - z 0| ≤ hf := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith [hk1, hz2], by linarith [hk2, hz1]⟩
    have hcoord2 : |k 1 - z 1| ≤ hf := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith [hk3, hz4], by linarith [hk4, hz3]⟩
    have hd2 : dist k z ≤ hf * Real.sqrt 2 := dist_le_of_coord hcoord1 hcoord2
    have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hd3 : hf * Real.sqrt 2 ≤ 2 * (hf * Real.sqrt 2) := by nlinarith [hs2, hfpos]
    linarith [hd1, hd2, hd3, hnfac]
  have hlocKL : Disjoint (locus hf WK) L' := by
    rw [Set.disjoint_left]
    rintro z ⟨cc, hcc, hccm⟩ hzL
    exact Set.disjoint_left.mp (hcellL cc hcc) hccm hzL
  -- the avoidance for the support of `m0`
  have havo : ∀ e ∈ m0.support, Disjoint (gseg hf e) (K' ∪ L') := by
    intro e he
    have hne : (m0 : Edge → ZMod 2) e ≠ 0 := Finsupp.mem_support_iff.mp he
    rw [Set.disjoint_left]
    intro z hz hzKL
    have hzloc : z ∈ elocus hf ((m0 : Chain1) : Edge → ZMod 2) := ⟨e, hne, hz⟩
    rcases hzKL with hzK | hzL
    · rcases hloc0K hzloc with h | h
      · exact Set.disjoint_left.mp hlocm1 h hzK
      · exact Set.disjoint_left.mp hlocWL h hzK
    · rcases hloc0L hzloc with h | h
      · exact Set.disjoint_left.mp hlocm2 h hzL
      · exact Set.disjoint_left.mp hlocKL h hzL
  -- ================= STEP 9: the walk and the assembly =================
  have hseg40x : ∀ s ∈ K' ∪ L', 40 * hh ≤ dist x' s := by
    rintro s (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · have h2 : x' = x - v := by rw [hx']
      rw [h2, hsub_dist]
      exact le_trans (by linarith [hh_dx]) (hdx x rfl z (Or.inl hz))
    · have h2 : x' = x - v := by rw [hx']
      rw [h2, hsub_dist]
      exact le_trans (by linarith [hh_dx]) (hdx x rfl z (Or.inr hz))
  have hseg40y : ∀ s ∈ K' ∪ L', 40 * hh ≤ dist y' s := by
    rintro s (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · have h2 : y' = y - v := by rw [hy']
      rw [h2, hsub_dist]
      exact le_trans (by linarith [hh_dy]) (hdy y rfl z (Or.inl hz))
    · have h2 : y' = y - v := by rw [hy']
      rw [h2, hsub_dist]
      exact le_trans (by linarith [hh_dy]) (hdy y rfl z (Or.inr hz))
  have hjoin : JoinedIn ((K' ∪ L')ᶜ) x' y' := by
    by_cases hPQ : P = Q
    · have h1 : dist x' y' ≤ 2 * hh := by
        have a : dist x' (gptH hh P) ≤ hh := by rw [hP]; exact nearGrid_dist hhpos x'
        have b : dist y' (gptH hh P) ≤ hh := by
          have b0 : dist y' (gptH hh Q) ≤ hh := by rw [hQ]; exact nearGrid_dist hhpos y'
          rw [← hPQ] at b0
          exact b0
        calc dist x' y' ≤ dist x' (gptH hh P) + dist (gptH hh P) y' := dist_triangle _ _ _
          _ ≤ 2 * hh := by
              have hc := dist_comm (gptH hh P) y'
              linarith
      refine joinedIn_seg (S := K' ∪ L') (r := 2 * hh) (by linarith) h1 ?_
      intro s hs
      have h1' := hseg40x s hs
      have : 20 * (2 * hh) = 40 * hh := by ring
      linarith
    · have hpq : (n * P.1, n * P.2) ≠ (n * Q.1, n * Q.2) := by
        intro hcon
        have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hnpos)
        exact hPQ (Prod.ext (mul_left_cancel₀ hn0 (congrArg Prod.fst hcon))
          (mul_left_cancel₀ hn0 (congrArg Prod.snd hcon)))
      have hpK : gptH hf (n * P.1, n * P.2) ∉ K' ∪ L' := by
        rw [gptH_scaled hnpos P]
        intro hmem
        have h1 := hdx' _ hmem
        have h2 : dist x' (gptH hh P) ≤ hh := by rw [hP]; exact nearGrid_dist hhpos x'
        linarith
      have hwalk := joinedIn_of_chain (h := hf) (K := K' ∪ L') (l := m0) hpq hpK hb0 havo
      rw [gptH_scaled hnpos P, gptH_scaled hnpos Q] at hwalk
      have hseg1 : JoinedIn ((K' ∪ L')ᶜ) x' (gptH hh P) := by
        refine joinedIn_seg (S := K' ∪ L') (r := hh) hhpos ?_ ?_
        · rw [hP]; exact nearGrid_dist hhpos x'
        · intro s hs; exact hdx' s hs
      have hseg2 : JoinedIn ((K' ∪ L')ᶜ) (gptH hh Q) y' := by
        refine (joinedIn_seg (S := K' ∪ L') (r := hh) hhpos ?_ ?_).symm
        · rw [hQ]; exact nearGrid_dist hhpos y'
        · intro s hs; exact hdy' s hs
      exact hseg1.trans (hwalk.trans hseg2)
  -- translate back
  have hK'L' : (fun z => z - v) '' (K ∪ L) = K' ∪ L' := by
    rw [hK', hL', Set.image_union]
  refine (joinedIn_compl_sub_iff v).mp ?_
  rw [← hx', ← hy', hK'L']
  exact hjoin


/-- **The Jordan arc theorem in the plane, `JoinedIn` form.**  If `γ : ℝ → ℝ²` is continuous and
injective on a compact interval `Icc a b`, then any two points outside the arc `γ '' Icc a b` can
be joined by a path avoiding it.

*Proof.*  Bisection (McCleary, Chapter 9).  If `γ '' Icc a b` separated `x` from `y`, then
applying `janis_singleton_general` to the two halves `γ '' Icc a ((a+b)/2)`,
`γ '' Icc ((a+b)/2) b` (which meet in the single point `γ ((a+b)/2)`) shows that one half already
separates.  Iterating gives nested intervals `Iₙ` of length `(b-a)/2ⁿ` whose images separate `x`
from `y`; their intersection is a single point `t*`, and `γ '' Iₙ` lies in an arbitrarily small
closed ball around `γ t*` (continuity).  Since `x, y ∉ closedBall (γ t*) ε` and the complement of a
closed ball is path connected, `γ '' Iₙ` cannot separate `x` from `y` for large `n`: contradiction.-/
theorem arc_compl_joinedIn_interval {a b : ℝ} (hab : a ≤ b) {γ : ℝ → Pt}
    (hcont : ContinuousOn γ (Set.Icc a b)) (hinj : Set.InjOn γ (Set.Icc a b))
    {x y : Pt} (hx : x ∉ γ '' Set.Icc a b) (hy : y ∉ γ '' Set.Icc a b) :
    JoinedIn ((γ '' Set.Icc a b)ᶜ) x y := by
  classical
  rcases eq_or_lt_of_le hab with h | hablt
  · subst h
    rw [Set.Icc_self, Set.image_singleton] at hx hy ⊢
    refine joinedIn_compl_singleton_pt2 (fun hh => hx ?_) (fun hh => hy ?_) <;>
      · rw [hh]; exact Set.mem_singleton _
  by_contra hsep
  have hnonempty : (γ '' Set.Icc a b).Nonempty := ⟨γ a, a, ⟨le_rfl, hab⟩, rfl⟩
  have hSclosed : IsClosed (γ '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hcont).isClosed
  have hxpos : 0 < Metric.infDist x (γ '' Set.Icc a b) :=
    (Metric.infDist_pos_iff_notMem_closure hnonempty).mp
      (by rw [hSclosed.closure_eq]; exact hx)
  have hypos : 0 < Metric.infDist y (γ '' Set.Icc a b) :=
    (Metric.infDist_pos_iff_notMem_closure hnonempty).mp
      (by rw [hSclosed.closure_eq]; exact hy)
  set δ : ℝ := min (Metric.infDist x (γ '' Set.Icc a b))
    (Metric.infDist y (γ '' Set.Icc a b)) with hδdef
  have hδpos : 0 < δ := lt_min hxpos hypos
  have hδx : δ ≤ Metric.infDist x (γ '' Set.Icc a b) := by rw [hδdef]; exact min_le_left _ _
  have hδy : δ ≤ Metric.infDist y (γ '' Set.Icc a b) := by rw [hδdef]; exact min_le_right _ _
  obtain ⟨η, hηpos, hη⟩ := (Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hcont)) (δ / 2) (by linarith)
  obtain ⟨n, hnpos, hn⟩ : ∃ n : ℕ, 0 < n ∧ (b - a) / n < η := by
    obtain ⟨k, hk⟩ := exists_nat_gt ((b - a) / η)
    refine ⟨k + 1, Nat.succ_pos k, ?_⟩
    have h2 : (b - a) < ((k : ℝ) + 1) * η := by
      have h3 := (div_lt_iff₀ hηpos).mp hk
      nlinarith [hηpos]
    rw [show (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 by push_cast; ring]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
    linarith
  set t : ℕ → ℝ := fun k => a + (k : ℝ) * (b - a) / n with htdef
  have htval : ∀ k, t k = a + (k : ℝ) * (b - a) / n := fun k => by rw [htdef]
  have ht0 : t 0 = a := by simp [htdef]
  have hnne' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hnpos)
  have htn : t n = b := by
    simp only [htdef]
    have h1 : (n : ℝ) * (b - a) / n = b - a := by field_simp
    rw [h1]; ring
  have htstep : ∀ k, t (k + 1) - t k = (b - a) / n := by
    intro k
    simp only [htdef]
    push_cast
    ring
  have htge_a : ∀ k, a ≤ t k := by
    intro k
    rw [htval k]
    have h2 : (0 : ℝ) ≤ (k : ℝ) * (b - a) / n := by positivity
    linarith
  have htble : ∀ k, k ≤ n → t k ≤ b := by
    intro k hk
    rw [htval k]
    have h2 : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    have h5 : (k : ℝ) * (b - a) / n ≤ (n : ℝ) * (b - a) / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (by linarith [hab])) (by positivity)
    have h6 : (n : ℝ) * (b - a) / n = b - a := by field_simp
    linarith [h5, h6]
  have hpiece : ∀ k, k + 1 ≤ n → JoinedIn ((γ '' Set.Icc (t k) (t (k + 1)))ᶜ) x y := by
    intro k hk
    have hkk : k ≤ n := le_trans (Nat.le_succ k) hk
    have hm : t k ≤ t (k + 1) := by
      have h1 : (0 : ℝ) ≤ (b - a) / n := by positivity
      have h2 := htstep k
      linarith
    have hsub : Set.Icc (t k) (t (k + 1)) ⊆ Set.Icc a b := fun s hs =>
      ⟨le_trans (htge_a k) hs.1, le_trans hs.2 (htble (k + 1) hk)⟩
    have hsubk : t k ∈ Set.Icc a b := ⟨htge_a k, htble k hkk⟩
    have htk : t k ∈ Set.Icc (t k) (t (k + 1)) := ⟨le_rfl, hm⟩
    have hball : γ '' Set.Icc (t k) (t (k + 1)) ⊆ Metric.closedBall (γ (t k)) (δ / 2) := by
      rintro z ⟨s, hs, rfl⟩
      rw [Metric.mem_closedBall]
      have h2 : |s - t k| ≤ t (k + 1) - t k := by
        rw [abs_sub_le_iff]
        exact ⟨by linarith [hs.1, hs.2], by linarith [hs.1, hs.2]⟩
      have h3 : (t (k + 1) - t k) = (b - a) / n := htstep k
      have h4 : dist s (t k) < η := by
        rw [Real.dist_eq]
        linarith
      exact le_of_lt (hη s (hsub hs) (t k) hsubk h4)
    have hx' : x ∈ (Metric.closedBall (γ (t k)) (δ / 2))ᶜ := by
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le]
      have h1 : δ ≤ dist x (γ (t k)) := by
        have h2 := Metric.infDist_le_dist_of_mem (x := x) (s := γ '' Set.Icc a b)
          (show γ (t k) ∈ γ '' Set.Icc a b from ⟨t k, hsubk, rfl⟩)
        linarith
      linarith
    have hy' : y ∈ (Metric.closedBall (γ (t k)) (δ / 2))ᶜ := by
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le]
      have h1 : δ ≤ dist y (γ (t k)) := by
        have h2 := Metric.infDist_le_dist_of_mem (x := y) (s := γ '' Set.Icc a b)
          (show γ (t k) ∈ γ '' Set.Icc a b from ⟨t k, hsubk, rfl⟩)
        linarith
      linarith
    exact ((isPathConnected_compl_closedBall_pt2 (γ (t k)) (by linarith)).joinedIn x hx' y hy').mono
      (Set.compl_subset_compl.mpr hball)
  have antitone_image : ∀ {s u : Set ℝ}, s ⊆ u → ∀ {z : Pt}, z ∉ γ '' u → z ∉ γ '' s :=
    fun hsu z h hmem => h (Set.image_mono hsu hmem)
  have hind : ∀ k, k ≤ n → JoinedIn ((γ '' Set.Icc a (t k))ᶜ) x y := by
    intro k
    induction k with
    | zero =>
        intro _
        have hI : Set.Icc a (t 0) = {a} := by rw [ht0, Set.Icc_self]
        have hsub0 : Set.Icc a (t 0) ⊆ Set.Icc a b := by
          intro s hs
          exact ⟨hs.1, le_trans hs.2 (by rw [ht0]; exact hab)⟩
        have hx0 : x ∉ γ '' Set.Icc a (t 0) := antitone_image hsub0 hx
        have hy0 : y ∉ γ '' Set.Icc a (t 0) := antitone_image hsub0 hy
        rw [hI, Set.image_singleton] at hx0 hy0 ⊢
        exact joinedIn_compl_singleton_pt2 hx0 hy0
    | succ k ih =>
        intro hk
        have hkk : k ≤ n := Nat.le_of_succ_le hk
        have him := ih hkk
        have hm : t k ≤ t (k + 1) := by
          have h1 : (0 : ℝ) ≤ (b - a) / n := by positivity
          have h2 := htstep k
          linarith
        have hsubK : Set.Icc a (t k) ⊆ Set.Icc a b := fun s hs =>
          ⟨hs.1, le_trans hs.2 (htble k hkk)⟩
        have hsubL : Set.Icc (t k) (t (k + 1)) ⊆ Set.Icc a b := fun s hs =>
          ⟨le_trans (htge_a k) hs.1, le_trans hs.2 (htble (k + 1) hk)⟩
        have hKc : IsCompact (γ '' Set.Icc a (t k)) :=
          isCompact_Icc.image_of_continuousOn (hcont.mono hsubK)
        have hLc : IsCompact (γ '' Set.Icc (t k) (t (k + 1))) :=
          isCompact_Icc.image_of_continuousOn (hcont.mono hsubL)
        have hinter : (γ '' Set.Icc a (t k)) ∩ (γ '' Set.Icc (t k) (t (k + 1))) =
            {γ (t k)} := by
          ext z
          constructor
          · rintro ⟨⟨s, hs, rfl⟩, ⟨u, hu, hsu⟩⟩
            have hsu' : s = u := hinj (hsubK hs) (hsubL hu) hsu.symm
            have hstk : s = t k := by
              rw [← hsu'] at hu
              exact le_antisymm hs.2 hu.1
            rw [hstk]
            exact Set.mem_singleton _
          · rintro hz
            rw [Set.mem_singleton_iff] at hz
            subst hz
            exact ⟨⟨t k, ⟨htge_a k, le_rfl⟩, rfl⟩, ⟨t k, ⟨le_rfl, hm⟩, rfl⟩⟩
        have hxKL : x ∉ (γ '' Set.Icc a (t k)) ∪ (γ '' Set.Icc (t k) (t (k + 1))) := by
          intro hmem
          rcases hmem with h | h
          · exact hx (Set.image_mono hsubK h)
          · exact hx (Set.image_mono hsubL h)
        have hyKL : y ∉ (γ '' Set.Icc a (t k)) ∪ (γ '' Set.Icc (t k) (t (k + 1))) := by
          intro hmem
          rcases hmem with h | h
          · exact hy (Set.image_mono hsubK h)
          · exact hy (Set.image_mono hsubL h)
        have hjoin := janis_singleton_general hKc hLc hinter hxKL hyKL him (hpiece k hk)
        have hunion : Set.Icc a (t k) ∪ Set.Icc (t k) (t (k + 1)) = Set.Icc a (t (k + 1)) :=
          Set.Icc_union_Icc_eq_Icc (htge_a k) hm
        rwa [← Set.image_union, hunion] at hjoin
  have hfinal := hind n le_rfl
  rw [htn] at hfinal
  exact hsep hfinal

/-- **Zorn reduction with the sub-interval inside `K`.**  If `γ '' K` separates `x` from `y` then
some compact sub-interval `Icc a b ⊆ K` already does (the minimal separator produced by the
minimal-separator argument is `γ '' Icc a b` with `Icc a b = γ ⁻¹' L ∩ K ⊆ K`). -/
theorem exists_subinterval_subset_not_joinedIn {K : Set ℝ} (hK : IsCompact K) {γ : ℝ → Pt}
    (hcont : ContinuousOn γ K) (hinj : Set.InjOn γ K) {X Y : Pt} (hX : X ∉ γ '' K)
    (hY : Y ∉ γ '' K) (hsep : ¬ JoinedIn ((γ '' K)ᶜ) X Y) :
    ∃ a b : ℝ, a ≤ b ∧ Set.Icc a b ⊆ K ∧ ¬ JoinedIn ((γ '' Set.Icc a b)ᶜ) X Y := by
  classical
  set A : Set Pt := γ '' K with hAdef
  have hAcomp : IsCompact A := hK.image_of_continuousOn hcont
  set S : Set (Set Pt) := {L | L ⊆ A ∧ IsCompact L ∧ ¬ JoinedIn (Lᶜ) X Y} with hSdef
  have hAmem : A ∈ S := ⟨subset_rfl, hAcomp, hsep⟩
  have hchaincond : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s := by
    intro c hcS hchain
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨A, hAmem, fun s hs => absurd hs (by simp)⟩
    · refine ⟨⋂₀ c, ⟨?_, ?_, ?_⟩, fun s hs => sInter_subset_of_mem hs⟩
      · obtain ⟨L₀, hL₀⟩ := hne
        exact (sInter_subset_of_mem hL₀).trans (hcS hL₀).1
      · refine hAcomp.of_isClosed_subset ?_ ?_
        · exact isClosed_sInter (fun s hs => ((hcS hs).2.1).isClosed)
        · obtain ⟨L₀, hL₀⟩ := hne
          exact (sInter_subset_of_mem hL₀).trans (hcS hL₀).1
      · rintro ⟨σ, hσ⟩
        have hcover : range σ ⊆ ⋃ i : {L // L ∈ c}, ((i : Set Pt))ᶜ := by
          intro z hz
          obtain ⟨t, rfl⟩ := hz
          have h1 : σ t ∉ ⋂₀ c := hσ t
          rw [Set.mem_sInter] at h1
          push_neg at h1
          obtain ⟨L, hLc, hLt⟩ := h1
          exact Set.mem_iUnion.mpr ⟨⟨L, hLc⟩, hLt⟩
        obtain ⟨u, hu⟩ := (isCompact_range σ.continuous).elim_finite_subcover
          (fun i : {L // L ∈ c} => ((i : Set Pt))ᶜ)
          (fun i => ((hcS i.2).2.1).isClosed.isOpen_compl) hcover
        have hufin : ∀ L' ∈ u.image Subtype.val, L' ∈ c := by
          intro L' hL'
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hL'
          exact i.2
        rcases u.eq_empty_or_nonempty with rfl | uone
        · exfalso
          have h0 := hu ⟨(0 : unitInterval), rfl⟩
          simpa using h0
        obtain ⟨L', hL'u, hL'min⟩ := Finset.exists_subset_of_isChain' hchain hufin
          (uone.image Subtype.val)
        have hsub : range σ ⊆ ((L' : Set Pt))ᶜ := by
          intro z hz
          have h1 := hu hz
          rw [Set.mem_iUnion] at h1
          obtain ⟨i, h1⟩ := h1
          rw [Set.mem_iUnion] at h1
          obtain ⟨hiu, hzi⟩ := h1
          have h2 : (i : Set Pt) ∈ u.image Subtype.val :=
            Finset.mem_image.mpr ⟨i, hiu, rfl⟩
          exact fun hzL => hzi ((hL'min (i : Set Pt) h2) hzL)
        have hL'c : L' ∈ c := hufin L' hL'u
        exact (hcS hL'c).2.2 ⟨σ, fun t => hsub ⟨t, rfl⟩⟩
  obtain ⟨L, hLmin⟩ := zorn_superset S hchaincond
  have hLmem : L ∈ S := hLmin.1
  obtain ⟨hLA, hLcomp, hLsep⟩ := hLmem
  have hLmin' : ∀ a ∈ S, a ⊆ L → L ⊆ a := hLmin.2
  -- `L` is nonempty
  have hLne : L.Nonempty := by
    rcases L.eq_empty_or_nonempty with rfl | h
    · exfalso
      refine hLsep ?_
      simpa using (convex_univ.isPathConnected ⟨X, mem_univ X⟩).joinedIn X (mem_univ X) Y (mem_univ Y)
    · exact h
  -- `L` is connected
  have hLpre : IsPreconnected L := by
    by_contra hcon
    unfold IsPreconnected at hcon
    push_neg at hcon
    obtain ⟨u, v, hu, hv, hLuv, hLu, hLv, hLuv'⟩ := hcon
    have hAeq : L ∩ u = L ∩ vᶜ := by
      ext z; constructor
      · rintro ⟨hzL, hzu⟩
        exact ⟨hzL, fun hzv => Set.eq_empty_iff_forall_notMem.mp hLuv' z ⟨hzL, hzu, hzv⟩⟩
      · rintro ⟨hzL, hzv⟩
        rcases hLuv hzL with h | h
        · exact ⟨hzL, h⟩
        · exact absurd h hzv
    have hBeq : L ∩ v = L ∩ uᶜ := by
      ext z; constructor
      · rintro ⟨hzL, hzv⟩
        exact ⟨hzL, fun hzu => Set.eq_empty_iff_forall_notMem.mp hLuv' z ⟨hzL, hzu, hzv⟩⟩
      · rintro ⟨hzL, hzu⟩
        rcases hLuv hzL with h | h
        · exact absurd h hzu
        · exact ⟨hzL, h⟩
    have hAcpt : IsCompact (L ∩ u) := by
      rw [hAeq]
      exact hLcomp.of_isClosed_subset (hLcomp.isClosed.inter hv.isClosed_compl) inter_subset_left
    have hBcpt : IsCompact (L ∩ v) := by
      rw [hBeq]
      exact hLcomp.of_isClosed_subset (hLcomp.isClosed.inter hu.isClosed_compl) inter_subset_left
    have hAneK : (L ∩ u) ⊆ A := inter_subset_left.trans hLA
    have hBneK : (L ∩ v) ⊆ A := inter_subset_left.trans hLA
    have hAjoin : JoinedIn ((L ∩ u)ᶜ) X Y := by
      by_contra hcon2
      have : L ∩ u ∈ S := ⟨hAneK, hAcpt, hcon2⟩
      have hsub := hLmin' (L ∩ u) this inter_subset_left
      obtain ⟨z, hz⟩ := hLv
      have hz1 : z ∈ L := hz.1
      have hz2 : z ∈ L ∩ u := hsub hz1
      have hz3 : z ∈ L ∩ (u ∩ v) := ⟨hz1, hz2.2, hz.2⟩
      rw [hLuv'] at hz3
      exact hz3
    have hBjoin : JoinedIn ((L ∩ v)ᶜ) X Y := by
      by_contra hcon2
      have : L ∩ v ∈ S := ⟨hBneK, hBcpt, hcon2⟩
      have hsub := hLmin' (L ∩ v) this inter_subset_left
      obtain ⟨z, hz⟩ := hLu
      have hz1 : z ∈ L := hz.1
      have hz2 : z ∈ L ∩ v := hsub hz1
      have hz3 : z ∈ L ∩ (u ∩ v) := ⟨hz1, hz.2, hz2.2⟩
      rw [hLuv'] at hz3
      exact hz3
    have hsepuv : ∀ a ∈ L ∩ u, ∀ b ∈ L ∩ v, 0 < dist a b := by
      intro a ha b hb
      refine dist_pos.mpr fun h => ?_
      have : a ∈ L ∩ (u ∩ v) := ⟨ha.1, ha.2, h ▸ hb.2⟩
      rw [hLuv'] at this
      exact this
    have hXAB : X ∉ (L ∩ u) ∪ (L ∩ v) := by
      intro hmem
      rcases hmem with h | h
      · exact hX (hLA h.1)
      · exact hX (hLA h.1)
    have hYAB : Y ∉ (L ∩ u) ∪ (L ∩ v) := by
      intro hmem
      rcases hmem with h | h
      · exact hY (hLA h.1)
      · exact hY (hLA h.1)
    have := _root_.Work.Whitney.PathTools.Grid.joinedIn_compl_union hAcpt hBcpt hsepuv hXAB hYAB hAjoin hBjoin
    refine hLsep ?_
    have hunion : (L ∩ u) ∪ (L ∩ v) = L := by
      ext z; constructor
      · rintro (h | h) <;> exact h.1
      · intro hz
        rcases hLuv hz with h | h
        · exact Or.inl ⟨hz, h⟩
        · exact Or.inr ⟨hz, h⟩
    rwa [hunion] at this
  -- the parameter set whose image is `L`
  set K' : Set ℝ := {t | t ∈ K ∧ γ t ∈ L} with hK'def
  have hK'image : γ '' K' = L := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht.2
    · intro hz
      obtain ⟨t, htK, htz⟩ := hLA hz
      exact ⟨t, ⟨htK, htz ▸ hz⟩, htz⟩
  have hK'ne : K'.Nonempty := by
    obtain ⟨z, hz⟩ := hLne
    obtain ⟨t, ht, rfl⟩ := hLA hz
    exact ⟨t, ⟨ht, hz⟩⟩
  have hK'comp : IsCompact K' := by
    have hsub : K' = (Subtype.val : ↥K → ℝ) '' ((fun t : ↥K => γ t.1) ⁻¹' L) := by
      ext t
      constructor
      · rintro ⟨htK, htL⟩
        exact ⟨⟨t, htK⟩, htL, rfl⟩
      · rintro ⟨t, htL, rfl⟩
        exact ⟨t.2, htL⟩
    rw [hsub]
    haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
    have hcont' : Continuous (fun t : ↥K => γ t.1) := hcont.domRestrict
    have hcl : IsClosed ((fun t : ↥K => γ t.1) ⁻¹' L) := hLcomp.isClosed.preimage hcont'
    exact (hcl.isCompact).image continuous_subtype_val
  -- `K'` is order-connected
  have hK'ord : K'.OrdConnected := by
    refine ⟨fun s hs t ht => ?_⟩
    intro r hr
    by_cases hrs : r = s
    · rwa [hrs]
    by_cases hrt : r = t
    · rwa [hrt]
    have hsr : s < r := lt_of_le_of_ne hr.1 (Ne.symm hrs)
    have hrt' : r < t := lt_of_le_of_ne hr.2 hrt
    by_contra hrK'
    have hcompP : IsCompact (K' ∩ Iic r) := hK'comp.inter_right isClosed_Iic
    have hcompQ : IsCompact (K' ∩ Ici r) := hK'comp.inter_right isClosed_Ici
    have hcontP : ContinuousOn γ (K' ∩ Iic r) :=
      hcont.mono (inter_subset_left.trans inter_subset_left)
    have hcontQ : ContinuousOn γ (K' ∩ Ici r) :=
      hcont.mono (inter_subset_left.trans inter_subset_left)
    have hPcomp : IsCompact (γ '' (K' ∩ Iic r)) := hcompP.image_of_continuousOn hcontP
    have hQcomp : IsCompact (γ '' (K' ∩ Ici r)) := hcompQ.image_of_continuousOn hcontQ
    have hPne : (γ '' (K' ∩ Iic r)).Nonempty :=
      ⟨γ s, s, ⟨hs, le_of_lt hsr⟩, rfl⟩
    have hQne : (γ '' (K' ∩ Ici r)).Nonempty :=
      ⟨γ t, t, ⟨ht, le_of_lt hrt'⟩, rfl⟩
    have hunion' : γ '' (K' ∩ Iic r) ∪ γ '' (K' ∩ Ici r) = L := by
      rw [← Set.image_union, ← hK'image]
      congr 1
      ext x
      constructor
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
      · intro hx
        rcases lt_trichotomy x r with h | h | h
        · exact Or.inl ⟨hx, le_of_lt h⟩
        · exact absurd (h ▸ hx) hrK'
        · exact Or.inr ⟨hx, le_of_lt h⟩
    have hdisj' : γ '' (K' ∩ Iic r) ∩ γ '' (K' ∩ Ici r) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨⟨a, ⟨ha, har⟩, haz⟩, ⟨b, ⟨hb, hbr⟩, hbz⟩⟩
      have hab : a = b := hinj ha.1 hb.1 (by rw [haz, hbz])
      have hra : r = a := le_antisymm (hab.symm ▸ hbr) har
      exact hrK' (by rw [hra]; exact ha)
    -- contradict connectivity of `L`
    have hLuv : L ⊆ (γ '' (K' ∩ Ici r))ᶜ ∪ (γ '' (K' ∩ Iic r))ᶜ := by
      intro z hz
      have hz' : z ∈ γ '' (K' ∩ Iic r) ∪ γ '' (K' ∩ Ici r) := by
        rw [hunion']; exact hz
      rcases hz' with hP | hQ
      · exact Or.inl (fun hQ' => Set.eq_empty_iff_forall_notMem.mp hdisj' z ⟨hP, hQ'⟩)
      · exact Or.inr (fun hP' => Set.eq_empty_iff_forall_notMem.mp hdisj' z ⟨hP', hQ⟩)
    have hLu : (L ∩ (γ '' (K' ∩ Ici r))ᶜ).Nonempty := by
      refine ⟨γ s, ?_, ?_⟩
      · rw [← hunion']; exact Or.inl (Set.mem_image_of_mem γ ⟨hs, le_of_lt hsr⟩)
      · intro hc
        obtain ⟨w, ⟨hw, hwr⟩, hweq⟩ := hc
        rw [mem_Ici] at hwr
        have hsw : s = w := hinj hs.1 hw.1 hweq.symm
        linarith
    have hLv : (L ∩ (γ '' (K' ∩ Iic r))ᶜ).Nonempty := by
      refine ⟨γ t, ?_, ?_⟩
      · rw [← hunion']; exact Or.inr (Set.mem_image_of_mem γ ⟨ht, le_of_lt hrt'⟩)
      · intro hc
        obtain ⟨w, ⟨hw, hwr⟩, hweq⟩ := hc
        rw [mem_Iic] at hwr
        have htw : t = w := hinj ht.1 hw.1 hweq.symm
        linarith
    obtain ⟨z, hz1, hzQ, hzP⟩ :=
      hLpre ((γ '' (K' ∩ Ici r))ᶜ) ((γ '' (K' ∩ Iic r))ᶜ)
        hQcomp.isClosed.isOpen_compl hPcomp.isClosed.isOpen_compl hLuv hLu hLv
    rw [← hunion'] at hz1
    rcases hz1 with h | h
    · exact hzP h
    · exact hzQ h
  -- conclude
  set a : ℝ := sInf K' with hadef
  set b : ℝ := sSup K' with hbdef
  have hbddB : BddBelow K' := hK'comp.isBounded.bddBelow
  have hbddA : BddAbove K' := hK'comp.isBounded.bddAbove
  have hab : a ≤ b := le_trans (csInf_le hbddB hK'ne.choose_spec)
    (le_csSup hbddA hK'ne.choose_spec)
  have hK'eq : K' = Icc a b := eq_Icc_of_isCompact_ordConnected hK'comp hK'ne hK'ord
  have haK : a ∈ K' := by rw [hK'eq]; exact ⟨le_rfl, hab⟩
  have hbK : b ∈ K' := by rw [hK'eq]; exact ⟨hab, le_rfl⟩
  have hLab : γ '' Icc a b = L := by rw [← hK'eq]; exact hK'image
  have hsubK : Set.Icc a b ⊆ K := by rw [← hK'eq]; exact fun t ht => ht.1
  exact ⟨a, b, hab, hsubK, by rw [hLab]; exact hLsep⟩


/-! ## Two geometric facts used by the refinement step of McCleary's argument -/

/-- A single cell cannot meet both of two sets whose distance exceeds the mesh size times `√2`. -/
lemma not_meet_both_of_sep {h : ℝ} (hh : 0 < h) {K₁ K₂ : Set Pt}
    (hsep : ∀ x ∈ K₁, ∀ y ∈ K₂, 8 * h * Real.sqrt 2 < dist x y) {c : Cell}
    (h₁ : (gsq h c ∩ K₁).Nonempty) (h₂ : (gsq h c ∩ K₂).Nonempty) : False := by
  obtain ⟨x, hxc, hxK⟩ := h₁
  obtain ⟨y, hyc, hyK⟩ := h₂
  have h0 : |x 0 - y 0| ≤ h := by
    have a := gsq_fst hxc; have b := gsq_fst' hxc
    have c := gsq_fst hyc; have d := gsq_fst' hyc
    rw [abs_le]; constructor <;> linarith
  have h1 : |x 1 - y 1| ≤ h := by
    have a := gsq_snd hxc; have b := gsq_snd' hxc
    have c := gsq_snd hyc; have d := gsq_snd' hyc
    rw [abs_le]; constructor <;> linarith
  have hd : dist x y ≤ h * Real.sqrt 2 := dist_le_of_coord h0 h1
  have hs := hsep x hxK y hyK
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [hd, hs, hpos, hh]

end

end Grid

/-- **The complement of the image of a compact subset of `ℝ` in the plane is path connected**
(in `JoinedIn` form): the target of this file. -/
theorem joinedIn_compl_of_arc_plane {K : Set ℝ} (hK : IsCompact K)
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)} (hcont : ContinuousOn γ K) (hinj : Set.InjOn γ K)
    {x y : EuclideanSpace ℝ (Fin 2)} (hx : x ∉ γ '' K) (hy : y ∉ γ '' K) :
    JoinedIn ((γ '' K)ᶜ) x y := by
  classical
  by_contra hsep
  obtain ⟨a, b, hab, hsub, hsep'⟩ :=
    Grid.exists_subinterval_subset_not_joinedIn hK hcont hinj hx hy hsep
  refine hsep' (Grid.arc_compl_joinedIn_interval hab (hcont.mono hsub) (hinj.mono hsub)
    (fun h => hx (Set.image_mono hsub h)) (fun h => hy (Set.image_mono hsub h)))

end Work.Whitney.PathTools
