import Mathlib
import Submission.Cvp

open Module MeasureTheory Metric Set
open scoped Real BigOperators InnerProductSpace RealInnerProductSpace ENNReal NNReal Pointwise
set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# `monotone_Voronoi_wins` variants with the volume hypothesis

`Cvp.monotone_Voronoi_wins` compares integrals over a fundamental body `K` of a lattice
`ℒ` with the integral over the Voronoi cell.  Its proof uses the hypothesis
`hKfund : IsAddFundamentalDomain ℒ K` ONLY to conclude `volume K = volume (VC ℒ)`
(through `volume_interior_eq_volume_voronoi`).  The boundary case ([C]-final) supplies the
body `K := voronoi (ℒ₁ ⊔ Q)` whose translates over the host lattice `ℒ` are disjoint
(`Disjointness.voronoi_interior_disjoint`) and whose volume equals that of `VC ℒ`, but
whose `ae_covers`-property over `ℒ` is not available; the three lemmas below are the same
theorems with the (easily supplied) volume equality replacing the full fundamental-domain
hypothesis.
-/

namespace Submission.Cvp

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "VC" => Submission.Voronoi.voronoi

lemma volume_interior_eq_volume_voronoi_of_vol {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (K : Set E) (hKmeas : MeasurableSet K)
    (hvolK : volume K = volume (VC ℒ : Set E))
    (hKboundary : volume (K \ interior K) = 0) :
    volume (interior K) = volume (VC ℒ : Set E) := by
  classical
  have hKV : volume K = volume (VC ℒ : Set E) := hvolK
  have hKmeasInt : MeasurableSet (interior K) := isOpen_interior.measurableSet
  have hsplit : K = interior K ∪ (K \ interior K) := by
    ext x
    constructor
    · intro hx
      by_cases h : x ∈ interior K
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    · intro hx
      rcases hx with hx | hx
      · exact interior_subset hx
      · exact hx.1
  have hvolsplit : volume K = volume (interior K) + volume (K \ interior K) := by
    calc
      volume K = volume (interior K ∪ (K \ interior K)) := congrArg volume hsplit
      _ = volume (interior K) + volume (K \ interior K) := by
        exact measure_union (by
          rw [Set.disjoint_left]
          intro x hxInt hxOut
          exact hxOut.2 hxInt) (hKmeas.diff hKmeasInt)
  have hKvol : volume (interior K) = volume K := by
    rw [hvolsplit, hKboundary, add_zero]
  calc
    volume (interior K) = volume K := hKvol
    _ = volume (VC ℒ : Set E) := hKV





lemma image_pieces_ae_voronoi_of_vol {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    [Countable ℒ] (hℒ : IsZLattice ℝ ℒ) (K : Set E) (hKmeas : MeasurableSet K)
    (hvolK : volume K = volume (VC ℒ : Set E))
    (hKdisj : ∀ y : ℒ, y ≠ 0 → Disjoint (interior K) (((y : E) +ᵥ K)))
    (hKboundary : volume (K \ interior K) = 0)
    (hVfin : volume (VC ℒ : Set E) ≠ ⊤) :
    (⋃ y : ℒ, (psiCan hℒ '' (piece K y))) =ᵐ[volume] (VC ℒ : Set E) := by
  classical
  let Q : ℒ → Set E := fun y => psiCan hℒ '' (piece K y)
  have hsub (y : ℒ) : piece K y ⊆ interior K := by
    intro x hx
    exact (mem_piece_iff K y x).mp hx |>.1
  have hQmeas (y : ℒ) : MeasurableSet (Q y) := by
    dsimp [Q]
    have hm := measurableSet_psiCan_image_piece hℒ K (Set.univ : Set E) y
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set E))
    simpa using hm
  have hQdisj : Pairwise (Function.onFun Disjoint Q) := by
    intro y z hyz
    change Disjoint (psiCan hℒ '' (piece K y)) (psiCan hℒ '' (piece K z))
    have hd := psiCan_image_piece_disjoint hℒ K hKdisj (interior K) (fun x hx => hx) y z hyz
    have heq₁ : psiCan hℒ '' (interior K ∩ piece K y) = psiCan hℒ '' (piece K y) := by
      congr 1
      exact Set.inter_eq_right.mpr (hsub y)
    have heq₂ : psiCan hℒ '' (interior K ∩ piece K z) = psiCan hℒ '' (piece K z) := by
      congr 1
      exact Set.inter_eq_right.mpr (hsub z)
    rw [heq₁, heq₂] at hd
    exact hd
  have hvolQ : volume (⋃ y : ℒ, Q y) = ∑' y : ℒ, volume (Q y) := by
    dsimp [Q]
    exact measure_iUnion hQdisj hQmeas
  have hvolQpieces : (∑' y : ℒ, volume (Q y)) = ∑' y : ℒ, volume (piece K y) := by
    apply tsum_congr
    intro y
    dsimp [Q]
    simpa using volume_psiCan_image_piece hℒ K (Set.univ : Set E) y
  have hvolInt : (∑' y : ℒ, volume (piece K y)) = volume (interior K) := by
    -- from restrict_eq_sum_restrict_piece applied to univ
    have hrest := restrict_eq_sum_restrict_piece (ℒ := ℒ) hℒ K
    -- (restrict IntK) univ = vol IntK; Measure.sum side = Σ vol piece
    have hleft : volume.restrict (interior K) (Set.univ : Set E) = volume (interior K) := by
      rw [Measure.restrict_apply (MeasurableSet.univ : MeasurableSet (Set.univ : Set E))]
      simp
    have hright : (Measure.sum (fun y : ℒ => volume.restrict (piece K y))) (Set.univ : Set E) =
        ∑' y : ℒ, volume (piece K y) := by
      rw [Measure.sum_apply (fun y : ℒ => volume.restrict (piece K y))
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set E))]
      apply tsum_congr
      intro y
      rw [Measure.restrict_apply (MeasurableSet.univ : MeasurableSet (Set.univ : Set E))]
      simp
    have heq := congrArg (fun m : Measure E => m (Set.univ : Set E)) hrest
    rw [hleft, hright] at heq
    exact heq.symm
  have hvolV : volume (interior K) = volume (VC ℒ : Set E) :=
    volume_interior_eq_volume_voronoi_of_vol (ℒ := ℒ) K hKmeas hvolK hKboundary
  -- assemble vol (⋃Q) = vol V
  have hvol : volume (⋃ y : ℒ, Q y) = volume (VC ℒ : Set E) := by
    calc
      volume (⋃ y : ℒ, Q y) = ∑' y : ℒ, volume (Q y) := hvolQ
      _ = ∑' y : ℒ, volume (piece K y) := hvolQpieces
      _ = volume (interior K) := hvolInt
      _ = volume (VC ℒ : Set E) := hvolV
  -- ae_eq: ⋃Q =ᵐ V
  have hsubV : (⋃ y : ℒ, Q y) ⊆ (VC ℒ : Set E) := by
    simpa [Q] using image_piece_subset_voronoi hℒ K
  have hnull2 : volume (((⋃ y : ℒ, Q y)) \ (VC ℒ : Set E)) = 0 := by
    have hd : (⋃ y : ℒ, Q y) \ (VC ℒ : Set E) = ∅ := Set.sdiff_eq_empty.mpr hsubV
    rw [hd]
    simp
  have hVmeas : MeasurableSet (VC ℒ : Set E) := Submission.Voronoi.voronoi_measurable ℒ
  have hUmeas : MeasurableSet (⋃ y : ℒ, Q y) := MeasurableSet.iUnion hQmeas
  have hnull1 : volume ((VC ℒ : Set E) \ ⋃ y : ℒ, Q y) = 0 := by
    -- vol V = vol U + vol(V∖U) (V = U ∪ (V∖U)); vol U = vol V so difference = 0
    have hsplit : (VC ℒ : Set E) = (⋃ y : ℒ, Q y) ∪ ((VC ℒ : Set E) \ ⋃ y : ℒ, Q y) := by
      ext x
      constructor
      · intro hx
        by_cases hxU : x ∈ ⋃ y : ℒ, Q y
        · exact Or.inl hxU
        · exact Or.inr ⟨hx, hxU⟩
      · intro hx
        rcases hx with hxU | hxAU
        · exact hsubV hxU
        · exact hxAU.1
    have hvolsplit : volume (VC ℒ : Set E) =
        volume (⋃ y : ℒ, Q y) + volume ((VC ℒ : Set E) \ ⋃ y : ℒ, Q y) := by
      calc
        volume (VC ℒ : Set E)
            = volume ((⋃ y : ℒ, Q y) ∪ ((VC ℒ : Set E) \ ⋃ y : ℒ, Q y)) := congrArg volume hsplit
        _ = volume (⋃ y : ℒ, Q y) + volume ((VC ℒ : Set E) \ ⋃ y : ℒ, Q y) := by
          exact measure_union (by
            rw [Set.disjoint_left]
            intro x hxU hxAU
            exact hxAU.2 hxU) (hVmeas.diff hUmeas)
    have hUfin : volume (⋃ y : ℒ, Q y) ≠ ⊤ := by
      rw [hvol]
      exact hVfin
    have hres : volume ((VC ℒ : Set E) \ ⋃ y : ℒ, Q y) = volume (VC ℒ : Set E) - volume (⋃ y : ℒ, Q y) :=
      measure_sdiff hsubV hUmeas.nullMeasurableSet hUfin
    rw [hres, hvol]
    simp
  rw [ae_eq_set]
  exact ⟨hnull2, hnull1⟩



theorem monotone_voronoi_wins_of_vol {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [Countable ℒ]
    (hℒ : IsZLattice ℝ ℒ) (K : Set E) (hKmeas : MeasurableSet K)
    (hvolK : volume K = volume (VC ℒ : Set E))
    (hKdisj : ∀ y : ℒ, y ≠ 0 → Disjoint (interior K) (((y : E) +ᵥ K)))
    (hKboundary : volume (K \ interior K) = 0)
    (F : E → ℝ) (hFmono : ∀ a b, ‖a‖ ≤ ‖b‖ → F b ≤ F a)
    (hFintInt : IntegrableOn F (interior K))
    (hFψint : IntegrableOn (fun x => F (psiCan hℒ x)) (interior K))
    (hFV : IntegrableOn F (VC ℒ : Set E)) (hVfin : volume (VC ℒ : Set E) ≠ ⊤) :
    (∫ x in K, F x) ≤ ∫ x in (VC ℒ : Set E), F x := by
  classical
  have h1 : (∫ x in K, F x) = ∫ x in (interior K), F x :=
    setIntegral_eq_interior_of_null_boundary K hKboundary F
  have h2 : (∫ x in (interior K), F x) ≤ ∫ x in (interior K), F (psiCan hℒ x) :=
    setIntegral_le_psiCan hℒ K F hFmono hFintInt hFψint
  have h3 : (∫ x in (interior K), F (psiCan hℒ x)) =
      ∑' y : ℒ, ∫ x in (piece K y), F (psiCan hℒ x) :=
    setIntegral_eq_tsum_pieces hℒ K (fun x => F (psiCan hℒ x)) hFψint
  have h4 : (∑' y : ℒ, ∫ x in (piece K y), F (psiCan hℒ x)) =
      ∑' y : ℒ, ∫ x in (psiCan hℒ '' (piece K y)), F x := by
    apply tsum_congr
    intro y
    exact (setIntegral_psiCan_piece hℒ K y F).symm
  have hrest := restrict_eq_sum_restrict_image_piece hℒ K hKdisj
  have hsubU : (⋃ y : ℒ, (psiCan hℒ '' (piece K y))) ⊆ (VC ℒ : Set E) :=
    image_piece_subset_voronoi hℒ K
  have hFU : IntegrableOn F (⋃ y : ℒ, (psiCan hℒ '' (piece K y))) := hFV.mono_set hsubU
  have hsumint : Integrable F (Measure.sum (fun y : ℒ => volume.restrict
      (psiCan hℒ '' (piece K y)))) := by
    rw [← hrest]
    exact hFU
  have h5 : (∑' y : ℒ, ∫ x in (psiCan hℒ '' (piece K y)), F x) =
      ∫ x in (⋃ y : ℒ, (psiCan hℒ '' (piece K y))), F x := by
    calc
      (∑' y : ℒ, ∫ x in (psiCan hℒ '' (piece K y)), F x)
          = ∑' y : ℒ, ∫ x, F x ∂(volume.restrict (psiCan hℒ '' (piece K y))) := by rfl
      _ = ∫ x, F x ∂(Measure.sum (fun y : ℒ => volume.restrict
            (psiCan hℒ '' (piece K y)))) := (integral_sum_measure hsumint).symm
      _ = ∫ x, F x ∂(volume.restrict (⋃ y : ℒ, (psiCan hℒ '' (piece K y)))) := by
        rw [hrest]
      _ = ∫ x in (⋃ y : ℒ, (psiCan hℒ '' (piece K y))), F x := by rfl
  have hae := image_pieces_ae_voronoi_of_vol (ℒ := ℒ) hℒ K hKmeas hvolK hKdisj hKboundary hVfin
  have h6 : (∫ x in (⋃ y : ℒ, (psiCan hℒ '' (piece K y))), F x) =
      ∫ x in (VC ℒ : Set E), F x :=
    setIntegral_congr_set hae
  calc
    (∫ x in K, F x) ≤ ∫ x in (VC ℒ : Set E), F x := by
      rw [h1]
      calc
        (∫ x in (interior K), F x) ≤ ∫ x in (interior K), F (psiCan hℒ x) := h2
        _ = ∫ x in (VC ℒ : Set E), F x := by
          rw [h3, h4, h5, h6]



end Submission.Cvp
