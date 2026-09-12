import Mathlib
import Submission.Work.Lattice.FlowRate
import Submission.Commons.Analysis.InnerProductSpace.orthonormal_family_adapted_to_inf
import Submission.Commons.LinearAlgebra.Alternating.iMulti_proportional_of_span_eq
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent
import Submission.GeometryOfNumbers.PlaneFinrank
import Submission.GeometryOfNumbers.FlowLatticeCovolume
import Submission.GeometryOfNumbers.WedgeBlockZero

/-!
# The top block index of the wedge of a subspace is its complement-rank

Coordinate model: `ℝᵈ = EuclideanSpace ℝ (Fin d)`, reference plane
`L = modelX ℓ = span {e i | i < ℓ}` and its orthogonal complement `Lᗮ`; for a `k`-vector
`w ∈ ⋀^k ℝᵈ` the **block** `blockElem w u` is the component with exactly `u` factors in `Lᗮ`
(`Submission.ExteriorCoordinates`), and `IsTopBlock ℓ w u` (`Submission.FlowRate`) says that
block `u` is the *highest* nonvanishing block of `w`.

**Main theorem (`isTopBlock_iMulti`)**: for a subspace `P ≤ ℝᵈ` with orthonormal basis
`u : Fin (finrank P) → ℝᵈ`, the top block of the wedge `ιMulti u` (which represents `P`, hence is
well defined up to a nonzero scalar) is exactly

    u_max = finrank P − finrank (P ⊓ L),

the number of "complement directions" of `P`.  Equivalently: every Plücker coordinate of
`ιMulti u` at a subset `I` with more than `finrank P − finrank (P ⊓ L)` indices `≥ ℓ` vanishes,
and the block at exactly that index does not vanish.  With Pythagoras this gives
`‖w‖² = Σ_{v ≤ u_max} ‖blockElem w v‖²` (the mass of the wedge lives in the blocks up to
`u_max`, `pythagoras_of_isTopBlock`).

This is the interface between the flow-rate engine (`Submission.FlowRate`) and the lattice
layer: with the two-scale flow `D = scaleMap (twoScale a b ℓ)` the block `u` is an eigenvector of
`⋀^j D` with eigenvalue `a^(j-u) b^u`, so the theorem identifies the *flow rate* of the covolume
of a rank-`j` subgroup with real span `P` as `a^(j-r) b^r`, `r = finrank (P ⊓ L)` — the
"position" of `P` with respect to `L`.

Proof strategy.  Choose an orthonormal basis `u` of `P` adapted to `P ⊓ L` (Commons
`orthonormal_family_adapted_to_inf`: the first `r := finrank (P ⊓ L)` vectors lie in `L`).
Write `π_L u i + π_{Lᗮ} u i = u i` for the orthogonal projections and expand `ιMulti u`
multilinearly over the `2^j` "mixed" wedges (`AlternatingMap.map_add_univ`).  A mixed wedge in
which one of the first `r` slots receives its `Lᗮ`-part vanishes (that part is zero, since
`u i ∈ L` there), so every surviving mixed wedge has at most `j - r` `Lᗮ`-factors.  The mixed
wedge with *all* low slots in `L` and all high slots in `Lᗮ` is the unique surviving term of
block `j - r`; it is nonzero by the independence of `π_{Lᗮ} u r, …, π_{Lᗮ} u (j-1)` (their span
is the `(j-r)`-dimensional space `π_{Lᗮ}(P)`, since `span {u i | i < r} = P ⊓ L`).  The general
case (an arbitrary orthonormal basis of `P`) follows since the wedges of two orthonormal bases
differ by a nonzero scalar.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks
open Submission.WedgeBlockZero
open Submission.FlowRate

namespace Submission.TopBlockIndex

variable {d : ℕ}

/-! ## Elementary projection facts -/

lemma modelProj_mem (ℓ : ℕ) (x : RD d) : modelProj ℓ x ∈ modelX (d := d) ℓ :=
  Submission.WedgeGeneralE1.projMap_mem (modelX (d := d) ℓ) x

lemma modelProj_fixes (ℓ : ℕ) {x : RD d} (hx : x ∈ modelX (d := d) ℓ) :
    modelProj ℓ x = x := by
  simpa [modelProj, Submission.WedgeGeneralE1.projMap_apply] using
    (Submodule.starProjection_eq_self_iff (K := modelX (d := d) ℓ)).mpr hx

lemma sub_modelProj_mem_orth (ℓ : ℕ) (x : RD d) : x - modelProj ℓ x ∈ (modelX (d := d) ℓ)ᗮ := by
  have h : x - modelProj ℓ x = x - (modelX (d := d) ℓ).starProjection x := by
    simp [modelProj, Submission.WedgeGeneralE1.projMap_apply]
  rw [h]
  exact Submodule.sub_starProjection_mem_orthogonal x

/-- The projection kills the orthogonal part. -/
lemma modelProj_sub_modelProj (ℓ : ℕ) (x : RD d) :
    modelProj ℓ (x - modelProj ℓ x) = 0 := by
  rw [modelProj, Submission.WedgeGeneralE1.projMap_apply]
  exact (Submodule.starProjection_apply_eq_zero_iff (modelX (d := d) ℓ)).mpr
    (sub_modelProj_mem_orth ℓ x)

/-- Block projection commutes with finite sums of vectors. -/
lemma blockElem_sum' {k ℓ j : ℕ} {ι : Type*} (s : Finset ι) (x : ι → WK d k) :
    blockElem (d := d) (k := k) (ℓ := ℓ) (s.sum x) j =
      s.sum (fun i => blockElem (d := d) (k := k) (ℓ := ℓ) (x i) j) := by
  have h := blockElem_sum (d := d) (k := k) (ℓ := ℓ) (j := j) s (fun _ => (1 : ℝ)) x
  simpa using h

/-- `blockElem` is scale-equivariant. -/
lemma blockElem_smul' {k ℓ j : ℕ} (a : ℝ) (x : WK d k) :
    blockElem (d := d) (k := k) (ℓ := ℓ) (a • x) j =
      a • blockElem (d := d) (k := k) (ℓ := ℓ) x j :=
  blockElem_smul (d := d) (k := k) (ℓ := ℓ) (j := j) a x

/-! ## The mixed-wedge expansion -/

/-- Pointwise form of the mixed wedge in terms of `Finset.piecewise`. -/
lemma mixedWedge_eq_piecewise {j : ℕ} (e c : Fin j → RD d) (T : Finset (Fin j)) :
    mixedWedge e c T = T.piecewise c e := by
  funext i
  by_cases h : i ∈ T <;> simp [mixedWedge, Finset.piecewise, h]

/-- **Multilinear expansion** of the wedge along the orthogonal splitting
`u = (π_{Lᗮ} ∘ u) + (π_L ∘ u)`. -/
theorem iMulti_eq_sum_mixedWedge {j : ℕ} (e c u : Fin j → RD d)
    (h : ∀ i, c i + e i = u i) :
    exteriorPower.ιMulti ℝ j u =
      (Finset.univ : Finset (Finset (Fin j))).sum
        (fun T => exteriorPower.ιMulti ℝ j (mixedWedge e c T)) := by
  have hm : c + e = u := funext h
  have key := AlternatingMap.map_add_univ (exteriorPower.ιMulti ℝ j) c e
  rw [hm] at key
  rw [key]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [mixedWedge_eq_piecewise]

/-- A mixed wedge in which a low slot (`< r`) receives its `Lᗮ`-part vanishes, because that
`Lᗮ`-part is zero (the corresponding basis vector lies in `L`). -/
lemma mixedWedge_eq_zero_of_low_mem {j ℓ r : ℕ} (e c u : Fin j → RD d)
    (_he : ∀ i, e i = modelProj ℓ (u i)) (hc : ∀ i, c i = u i - modelProj ℓ (u i))
    (hlow : ∀ i : Fin j, (i : ℕ) < r → u i ∈ modelX (d := d) ℓ)
    {T : Finset (Fin j)} (hT : ∃ i ∈ T, (i : ℕ) < r) :
    exteriorPower.ιMulti ℝ j (mixedWedge e c T) = 0 := by
  obtain ⟨i, hiT, hir⟩ := hT
  have hzi : mixedWedge e c T i = 0 := by
    have h1 : mixedWedge e c T i = u i - modelProj ℓ (u i) := by
      rw [show mixedWedge e c T i = (if i ∈ T then c i else e i) from rfl, if_pos hiT, hc]
    rw [h1, modelProj_fixes ℓ (hlow i hir), sub_self]
  refine AlternatingMap.map_linearDependent (exteriorPower.ιMulti ℝ j) _ (fun hLI => ?_)
  exact hLI.ne_zero i hzi

/-! ## The intersection `P ⊓ L` is spanned by the low vectors -/

lemma span_low_eq_inf {j ℓ r : ℕ} (u : Fin j → RD d) (P : Submodule ℝ (RD d))
    (hu : Orthonormal ℝ u) (hspan : Submodule.span ℝ (Set.range u) = P)
    (hlow : ∀ i : Fin j, (i : ℕ) < r → u i ∈ modelX (d := d) ℓ)
    (hfin : Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)) = r) (hrj : r ≤ j) :
    Submodule.span ℝ (Set.range (fun k : Fin r => u (Fin.castLE hrj k))) =
      (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)) := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨k, rfl⟩
    exact Submodule.mem_inf.mpr
      ⟨by rw [← hspan]; exact Submodule.subset_span ⟨Fin.castLE hrj k, rfl⟩,
       hlow (Fin.castLE hrj k) k.isLt⟩
  · have hli : LinearIndependent ℝ (fun k : Fin r => u (Fin.castLE hrj k)) :=
      hu.linearIndependent.comp _ (Fin.castLE_injective hrj)
    rw [finrank_span_eq_card (R := ℝ) hli, Fintype.card_fin, hfin]

/-- **The mixed wedge of a subspace in adapted position is linearly independent**: the family
`u 0, …, u (r-1), π_{Lᗮ} u r, …, π_{Lᗮ} u (j-1)`. -/
lemma linearIndependent_mixed_high {j ℓ r : ℕ} (u : Fin j → RD d) (P : Submodule ℝ (RD d))
    (hu : Orthonormal ℝ u) (hspan : Submodule.span ℝ (Set.range u) = P)
    (hrj : r ≤ j) (hfin : Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)) = r)
    (hlow : ∀ i : Fin j, (i : ℕ) < r → u i ∈ modelX (d := d) ℓ) :
    LinearIndependent ℝ (fun i : Fin j =>
      if r ≤ (i : ℕ) then u i - modelProj ℓ (u i) else u i) := by
  classical
  set w : Fin j → RD d := fun i => if r ≤ (i : ℕ) then u i - modelProj ℓ (u i) else u i
    with hw
  have hw_low : ∀ i : Fin j, ¬ (r ≤ (i : ℕ)) → w i = u i := by
    intro i hi; rw [hw]; simp [hi]
  have hw_high : ∀ i : Fin j, r ≤ (i : ℕ) → w i = u i - modelProj ℓ (u i) := by
    intro i hi; rw [hw]; simp [hi]
  have hspan_low := span_low_eq_inf u P hu hspan hlow hfin hrj
  have hu_mem_P : ∀ i, u i ∈ P := by
    intro i; rw [← hspan]; exact Submodule.subset_span ⟨i, rfl⟩
  have hite : ∀ i j : Fin j, inner ℝ (u i) (u j) = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp hu
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set high : Finset (Fin j) := Finset.univ.filter (fun i : Fin j => r ≤ (i : ℕ)) with hhigh
  set S : RD d := ∑ i ∈ high, g i • u i with hS
  have hmem_high : ∀ i : Fin j, i ∈ high ↔ r ≤ (i : ℕ) := by
    intro i; rw [hhigh]; simp
  -- (1) `π S = S`, hence `S ∈ L`.
  have hA : (∑ i ∈ high, g i • (u i - modelProj ℓ (u i))) = 0 := by
    have h2 : (∑ i : Fin j, g i • (w i - modelProj ℓ (w i))) = 0 := by
      have h3 := congrArg
        (fun x : RD d => (LinearMap.id - modelProj ℓ : RD d →ₗ[ℝ] RD d) x) hg
      simpa only [map_sum, map_smul, LinearMap.sub_apply, LinearMap.id_apply, map_zero,
        sub_self] using h3
    rw [← h2, hhigh, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : r ≤ (i : ℕ)
    · rw [if_pos hi, hw_high i hi, modelProj_sub_modelProj, sub_zero]
    · rw [if_neg hi, hw_low i hi, modelProj_fixes ℓ (hlow i (by omega)), sub_self, smul_zero]
  have hS_L : S ∈ modelX (d := d) ℓ := by
    have hπ : modelProj ℓ S = S := by
      have h1 : modelProj ℓ S - S = ∑ i ∈ high, g i • (modelProj ℓ (u i) - u i) := by
        rw [hS, map_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul, smul_sub]
      have h2 : (∑ i ∈ high, g i • (modelProj ℓ (u i) - u i)) =
          -(∑ i ∈ high, g i • (u i - modelProj ℓ (u i))) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← smul_neg, neg_sub]
      have hzero : modelProj ℓ S - S = 0 := by rw [h1, h2, hA, neg_zero]
      exact sub_eq_zero.mp hzero
    rw [modelProj, Submission.WedgeGeneralE1.projMap_apply] at hπ
    exact (Submodule.starProjection_eq_self_iff).mp hπ
  -- (2) `S ∈ P`.
  have hS_P : S ∈ P := by
    rw [hS]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hu_mem_P i))
  -- (3) `S = 0`.
  have hS_zero : S = 0 := by
    have hmem : S ∈ Submodule.span ℝ (Set.range (fun k : Fin r => u (Fin.castLE hrj k))) := by
      rw [hspan_low]
      exact Submodule.mem_inf.mpr ⟨hS_P, hS_L⟩
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    set S' : RD d := ∑ k : Fin r, b k • u (Fin.castLE hrj k) with hS'def
    have hS'eq : S' = S := hb
    have horth : ∀ k : Fin r, inner ℝ S (u (Fin.castLE hrj k)) = 0 := by
      intro k
      have h1 : inner ℝ S (u (Fin.castLE hrj k)) =
          ∑ i ∈ high, g i * inner ℝ (u i) (u (Fin.castLE hrj k)) := by
        rw [hS, sum_inner]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [inner_smul_left]
        simp
      rw [h1]
      refine Finset.sum_eq_zero (fun i hi => ?_)
      have hi' : r ≤ (i : ℕ) := (hmem_high i).mp hi
      have hne : i ≠ Fin.castLE hrj k := by
        intro hc
        have hval : (i : ℕ) = k.val := by rw [hc]; rfl
        omega
      rw [hite i (Fin.castLE hrj k), if_neg hne, mul_zero]
    have h0 : inner ℝ S S' = 0 := by
      rw [hS'def, inner_sum]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      rw [inner_smul_right, horth k, mul_zero]
    rw [hS'eq] at h0
    exact inner_self_eq_zero.mp h0
  -- (4) `g i = 0` for `i ∈ high`.
  have hhigh_zero : ∀ i : Fin j, r ≤ (i : ℕ) → g i = 0 := by
    intro i hi
    have h1 : inner ℝ (u i) S = g i := by
      have hkey : inner ℝ (u i) S = ∑ k ∈ high, inner ℝ (u i) (g k • u k) := by
        rw [hS, inner_sum]
      have hsum_eq : (∑ k ∈ high, inner ℝ (u i) (g k • u k)) = g i := by
        have hval : (∑ k ∈ high, inner ℝ (u i) (g k • u k)) = inner ℝ (u i) (g i • u i) := by
          refine Finset.sum_eq_single (s := high) i ?_ ?_
          · intro k _ hne
            have hne' : i ≠ k := fun h => hne h.symm
            rw [inner_smul_right, hite i k, if_neg hne', mul_zero]
          · intro hnot
            exact absurd ((hmem_high i).mpr hi) hnot
        rw [hval, inner_smul_right, hite i i, if_pos rfl, mul_one]
      rw [hkey, hsum_eq]
    rw [hS_zero, inner_zero_right] at h1
    exact h1.symm
  -- (5) `g i = 0` in general.
  intro i
  by_cases hi : r ≤ (i : ℕ)
  · exact hhigh_zero i hi
  · have hcomp : inner ℝ (u i) (∑ k : Fin j, g k • w k) = g i := by
      have hkey : inner ℝ (u i) (∑ k : Fin j, g k • w k) =
          ∑ k : Fin j, inner ℝ (u i) (g k • w k) := inner_sum _ _ _
      have hsum_eq : (∑ k : Fin j, inner ℝ (u i) (g k • w k)) = g i := by
        have hval : (∑ k : Fin j, inner ℝ (u i) (g k • w k)) = inner ℝ (u i) (g i • w i) := by
          refine Finset.sum_eq_single i ?_ ?_
          · intro k _ hne
            rw [inner_smul_right]
            by_cases hk2 : r ≤ (k : ℕ)
            · rw [hw_high k hk2, hhigh_zero k hk2, zero_mul]
            · rw [hw_low k hk2, hite i k, if_neg (fun h : i = k => hne h.symm), mul_zero]
          · intro hnot; exact absurd (Finset.mem_univ i) hnot
        rw [hval, hw_low i hi, inner_smul_right, hite i i, if_pos rfl, mul_one]
      rw [hkey, hsum_eq]
    rw [hg, inner_zero_right] at hcomp
    exact hcomp.symm

/-! ## The main theorem -/

/-- **Adapted-position form**: if `u : Fin j → ℝᵈ` is an orthonormal basis of `P` whose first
`r = finrank (P ⊓ L)` vectors lie in `L`, then the top block of `ιMulti u` is `j - r`. -/
theorem isTopBlock_adapted_gen {ℓ j r : ℕ} (P : Submodule ℝ (RD d)) (u : Fin j → RD d)
    (hu : Orthonormal ℝ u) (hspan : Submodule.span ℝ (Set.range u) = P)
    (hr : Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)) = r) (hrj : r ≤ j)
    (hlow : ∀ i : Fin j, (i : ℕ) < r → u i ∈ modelX (d := d) ℓ) :
    IsTopBlock (d := d) (ℓ := ℓ) (exteriorPower.ιMulti ℝ j u) (j - r) := by
  classical
  set e : Fin j → RD d := fun i => modelProj ℓ (u i) with hedef
  set c : Fin j → RD d := fun i => u i - modelProj ℓ (u i) with hcdef
  have he : ∀ i, e i = modelProj ℓ (u i) := fun i => rfl
  have hc : ∀ i, c i = u i - modelProj ℓ (u i) := fun i => rfl
  have he_mem : ∀ i, e i ∈ modelX (d := d) ℓ := fun i => modelProj_mem ℓ (u i)
  have hc_mem : ∀ i, c i ∈ (modelX (d := d) ℓ)ᗮ := fun i => sub_modelProj_mem_orth ℓ (u i)
  have hsum : ∀ i, c i + e i = u i := fun i => by simp [hc, he, add_comm]
  have hexp := iMulti_eq_sum_mixedWedge e c u hsum
  set high : Finset (Fin j) := Finset.univ.filter (fun i : Fin j => r ≤ (i : ℕ)) with hhigh
  have hhigh_card : high.card = j - r := by
    rw [hhigh]
    exact Submission.FlowLattice.card_filter_val_ge (d := j) (ℓ := r) hrj
  have hterm : ∀ T : Finset (Fin j),
      blockElem (d := d) (k := j) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ j (mixedWedge e c T)) (j - r) =
      if T = high then exteriorPower.ιMulti ℝ j (mixedWedge e c T) else 0 := by
    intro T
    by_cases hTeq : T = high
    · rw [if_pos hTeq, hTeq, ← hhigh_card]
      exact blockElem_mixedWedge (d := d) (ℓ := ℓ) e c he_mem hc_mem high
    · rw [if_neg hTeq]
      by_cases hlowT : ∃ i ∈ T, (i : ℕ) < r
      · rw [mixedWedge_eq_zero_of_low_mem e c u he hc hlow hlowT, blockElem_zero]
      · have hsub : ∀ i ∈ T, r ≤ (i : ℕ) := by
          intro i hiT
          by_contra hlt
          exact hlowT ⟨i, hiT, by omega⟩
        have hThigh : T ⊆ high := fun i hi => by
          rw [hhigh]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hsub i hi⟩
        exact blockElem_mixedWedge_eq_zero (d := d) (ℓ := ℓ) e c he_mem hc_mem T (by
          intro hcc
          exact hTeq (Finset.eq_of_subset_of_card_le hThigh (by rw [hhigh_card, hcc])))
  constructor
  · have hkey : blockElem (d := d) (k := j) (ℓ := ℓ) (exteriorPower.ιMulti ℝ j u) (j - r) =
        exteriorPower.ιMulti ℝ j (mixedWedge e c high) := by
      rw [hexp, blockElem_sum']
      rw [Finset.sum_eq_single high ?_ ?_]
      · simpa using hterm high
      · intro T _ hT
        rw [hterm T, if_neg hT]
      · intro hnot; exact absurd (Finset.mem_univ high) hnot
    rw [hkey]
    have hLI := linearIndependent_mixed_high u P hu hspan hrj hr hlow
    have hLI' : LinearIndependent ℝ (mixedWedge e c high) := by
      convert hLI using 1
      funext i
      by_cases hi : r ≤ (i : ℕ)
      · rw [mixedWedge,
          if_pos (by rw [hhigh]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩),
          hc, if_pos hi]
      · rw [mixedWedge, if_neg (by rw [hhigh]; simp [hi]), he, if_neg hi,
          modelProj_fixes ℓ (hlow i (by omega))]
    exact Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent
      (mixedWedge e c high) hLI'
  · intro m hm hrk
    rw [hexp, blockElem_sum']
    refine Finset.sum_eq_zero (fun T _ => ?_)
    by_cases hlowT : ∃ i ∈ T, (i : ℕ) < r
    · rw [mixedWedge_eq_zero_of_low_mem e c u he hc hlow hlowT, blockElem_zero]
    · have hsub : ∀ i ∈ T, r ≤ (i : ℕ) := by
        intro i hiT
        by_contra hlt'
        exact hlowT ⟨i, hiT, by omega⟩
      have hcard : T.card ≤ j - r := by
        have h1 : T ⊆ high := fun i hi => by
          rw [hhigh]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hsub i hi⟩
        calc T.card ≤ high.card := Finset.card_le_card h1
          _ = j - r := hhigh_card
      exact blockElem_mixedWedge_eq_zero (d := d) (ℓ := ℓ) e c he_mem hc_mem T
        (by intro hc_eq; omega)

/-- **Adapted-position form** (specialised to `j = finrank P`, `r = finrank (P ⊓ L)`). -/
theorem isTopBlock_adapted {ℓ : ℕ} (P : Submodule ℝ (RD d))
    (u : Fin (Module.finrank ℝ P) → RD d)
    (hu : Orthonormal ℝ u) (hspan : Submodule.span ℝ (Set.range u) = P)
    (hlow : ∀ i : Fin (Module.finrank ℝ P),
      (i : ℕ) < Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d)) →
        u i ∈ modelX (d := d) ℓ) :
    IsTopBlock (d := d) (ℓ := ℓ) (exteriorPower.ιMulti ℝ (Module.finrank ℝ P) u)
      (Module.finrank ℝ P -
        Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d))) :=
  isTopBlock_adapted_gen P u hu hspan rfl
    (Submodule.finrank_mono (R := ℝ) (inf_le_left : P ⊓ modelX (d := d) ℓ ≤ P)) hlow

/-- **Main theorem**: for a subspace `P ≤ ℝᵈ` and an orthonormal basis `u` of `P`, the top
nonvanishing block of the wedge `ιMulti u` is `finrank P − finrank (P ⊓ L)`. -/
theorem isTopBlock_iMulti {ℓ : ℕ} (P : Submodule ℝ (RD d))
    (u : Fin (Module.finrank ℝ P) → RD d)
    (hu : Orthonormal ℝ u) (hspan : Submodule.span ℝ (Set.range u) = P) :
    IsTopBlock (d := d) (ℓ := ℓ) (exteriorPower.ιMulti ℝ (Module.finrank ℝ P) u)
      (Module.finrank ℝ P -
        Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d))) := by
  classical
  obtain ⟨v, hv, _hvm, hvspan, hlow⟩ :=
    Commons.Analysis.InnerProductSpace.orthonormal_family_adapted_to_inf P (modelX (d := d) ℓ)
  have ha := isTopBlock_adapted P v hv hvspan hlow
  obtain ⟨a, ha0, haeq⟩ :=
    Commons.LinearAlgebra.Alternating.iMulti_proportional_of_span_eq u v
      hu.linearIndependent hv.linearIndependent (by rw [hspan, hvspan])
  constructor
  · rw [haeq, blockElem_smul (d := d) (k := Module.finrank ℝ P) (ℓ := ℓ)
      (j := Module.finrank ℝ P -
        Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (RD d))) a _]
    intro h
    exact ha.1 ((smul_eq_zero.mp h).resolve_left ha0)
  · intro u' hu' hu'k
    rw [haeq, blockElem_smul (d := d) (k := Module.finrank ℝ P) (ℓ := ℓ) (j := u') a _,
      ha.2 u' hu' hu'k, smul_zero]

/-- **Pythagoras for a vector with top block `u'`**: the mass of `w` is carried by the blocks
`v ≤ u'`. -/
lemma pythagoras_of_isTopBlock {k ℓ : ℕ} (w : WK d k) {u' : ℕ} (hu' : u' ≤ k)
    (htop : IsTopBlock (d := d) (ℓ := ℓ) w u') :
    ‖w‖ ^ 2 =
      (Finset.range (u' + 1)).sum
        (fun v => ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖ ^ 2) := by
  have hsum := sum_normSq_blockElem (d := d) (k := k) (ℓ := ℓ) w
  have hzero : ∀ v : ℕ, v ∈ Finset.range (k + 1) → v ∉ Finset.range (u' + 1) →
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖ ^ 2 = 0 := by
    intro v hv hvnot
    simp only [Finset.mem_range] at hv hvnot
    rw [htop.2 v (by omega) (Nat.lt_succ_iff.mp hv), norm_zero]
    norm_num
  rw [← hsum]
  refine (Finset.sum_subset ?_ hzero).symm
  intro v hv
  simp only [Finset.mem_range] at hv ⊢
  omega

end Submission.TopBlockIndex
