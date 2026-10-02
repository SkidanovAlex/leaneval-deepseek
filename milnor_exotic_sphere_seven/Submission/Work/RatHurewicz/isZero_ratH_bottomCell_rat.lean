import Mathlib
import Submission.Work.RatHurewicz.fibreRangeVanishing
import Submission.Work.Stems.bottomCellReduction

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `H_{k+1}(Z;ℚ) = 0` for a range model of `K(ℤ,k)` — the rational bottom-cell degree

This is the *rational* form of `Work.Stems.isZero_ratH_bottomCell`: the integral,
Künneth-backed Serre exact sequence in the stable range
(`Work.Serre.SerreExactRangeCorrected`, still an open target of area SERRE) is replaced by the
*proved* rational, homological-fibre pair comparison `Work.Serre.ratSerrePairComparison`, packaged
as the `Prop` `Work.RatHurewicz.RatPairComparison`.

Let `k ≥ 3`, let `Z` be a space whose homotopy groups vanish in degrees `≤ k+1` except in degree
`k` (`Work.RatHurewicz.IsRangeKModel k (k+1) z₀`), and let `f : Sᵏ → Z` be a based map inducing a
bijection on `πₖ` (the "bottom cell" of the range model; it exists by
`Work.RatHurewicz.exists_bijective_piMapN_rangeModel`).  Write `F` for the homotopy fibre of `f` —
the `k`-connected cover of `Sᵏ` — and `Track f` for the mapping track of `f`, whose total space is
homotopy equivalent to `Sᵏ`, whose fibre is `F`, and whose base is `Z`.

The argument is the rational transcription of the proof of `Work.Stems.isZero_homology_bottomCell`,
run on the track fibration `trackMap f : Track f → Z`:

* `H_{k+1}(Z;ℚ) ≅ H_{k+1}(Z,{z₀};ℚ)` (the point has no homology in degrees `k`, `k+1`),
* `≅ H_{k+1}(Track f, fibre;ℚ)` (the rational pair comparison at `b = k`, `f = k+1`, stable up to
  `2k+1`),
* `= 0`: the long exact sequence of the pair reads
  `H_{k+1}(Track f;ℚ) → H_{k+1}(Track f, fibre;ℚ) → H_k(fibre;ℚ)`, the first term vanishes
  (`Track f ≃ Sᵏ` has no homology in degree `k+1`) so the connecting map is injective, and its
  target `H_k(F;ℚ)` vanishes because `F` is `k`-connected.

Everything here is *homological and rational*: no cup product, no Euler class, no Serre spectral
sequence, and no cup-product/Whitney formula.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option linter.style.haveILetI false

namespace Work.RatHurewicz

noncomputable section

variable {Z : Type} [TopologicalSpace Z]

/-! ## Auxiliary statements about the mapping track

The mapping track `Track f` of `f : Sᵏ → Z` is homotopy equivalent to `Sᵏ` (via the projection
`trackProj f`, whose homotopy inverse is the constant-path section `trackSec f`).  Its rational
homology therefore vanishes away from the degrees `0` and `k`; this is the first ingredient of the
exact-sequence argument. -/

/-- **The mapping track of a map out of a sphere is path connected** (`k ≥ 1`): every point `z` is
joined to the section point `trackSec f (trackProj f z)` by the collapsing deformation
`trackProj_trackSec_homotopy`, and two points of the section are joined through the path
connectedness of `Sᵏ`. -/
theorem pathConnectedSpace_track_bottom {k : ℕ} (hk : 1 ≤ k) (f : C(Work.Serre.Sph k, Z))
    (s₀ : Work.Serre.Sph k) : PathConnectedSpace (Track f) := by
  haveI hpcSph : PathConnectedSpace (Work.Serre.Sph k) :=
    pathConnectedSpace_of_subsingleton_pi_zero s₀
      (Work.Stems.sphereConnectivity k 0 (by omega) s₀)
  have H := trackProj_trackSec_homotopy f
  refine ⟨⟨trackBase f s₀⟩, fun x y => ?_⟩
  have hpath : ∀ z : Track f, Joined (trackSec f (trackProj f z)) z :=
    fun z => ⟨{ toFun := fun s => H (s, z)
                continuous_toFun := H.continuous_toFun.comp (continuous_id.prodMk continuous_const)
                source' := H.map_zero_left z
                target' := H.map_one_left z }⟩
  exact (hpath x).symm.trans
    (((PathConnectedSpace.joined (trackProj f x) (trackProj f y)).map
      (trackSec f).continuous_toFun).trans (hpath y))

/-- The homotopy equivalence `Track f ≃ Sᵏ` given by the projection of the mapping track (its
homotopy inverse is the constant-path section `trackSec f`). -/
def trackBottomHomotopyEquiv {k : ℕ} (f : C(Work.Serre.Sph k, Z)) :
    ContinuousMap.HomotopyEquiv (Track f) (Work.Serre.Sph k) where
  toFun := trackProj f
  invFun := trackSec f
  left_inv := ⟨trackProj_trackSec_homotopy f⟩
  right_inv := ⟨trackSec_trackProj_homotopy f⟩

/-- The rational homology of `Sᵏ` vanishes away from the degrees `0` and `k`. -/
theorem isZero_ratH_sph_bottom {k j : ℕ} (hk : 1 ≤ k) (hj0 : j ≠ 0) (hjk : j ≠ k) :
    IsZero (Work.Serre.ratH (TopCat.of (Work.Serre.Sph k)) j) :=
  Work.StemsB.isZero_homology_rat_of_isZero_homology_int (TopCat.of (Work.Serre.Sph k)) j
    (Work.Cohomology.sphereVanishing k j hk hj0 hjk)

/-- The rational homology of the mapping track of `f : Sᵏ → Z` vanishes away from the degrees `0`
and `k` (it is homotopy equivalent to `Sᵏ`). -/
theorem isZero_ratH_track_bottom {k j : ℕ} (hk : 1 ≤ k) (f : C(Work.Serre.Sph k, Z))
    (hj0 : j ≠ 0) (hjk : j ≠ k) :
    IsZero (Work.Serre.ratH (TopCat.of (Track f)) j) :=
  Work.Stems.isZero_ratH_of_homotopyEquiv (trackBottomHomotopyEquiv f) j
    (isZero_ratH_sph_bottom hk hj0 hjk)

/-- **A monomorphism into a zero `ℚ`-module has zero source.** -/
theorem isZero_of_mono_of_isZero_rat {M N : ModuleCat ℚ} (f : M ⟶ N) (hmono : Mono f)
    (h : IsZero N) : IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  exact ⟨fun a b => (ModuleCat.mono_iff_injective f).mp hmono (Subsingleton.elim _ _)⟩

/-! ## The target -/

theorem isZero_ratH_bottomCell_rat {Z : Type} [TopologicalSpace Z] {k : ℕ} (hk : 3 ≤ k)
    (f : C(Work.Serre.Sph k, Z)) (s₀ : Work.Serre.Sph k)
    (hmodel : Work.RatHurewicz.IsRangeKModel k (k + 1) (f s₀))
    (hbij : Function.Bijective (Work.Serre.piMapN f k s₀)) :
    CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of Z) (k + 1)) := by
  -- the homotopy fibre `F` of the bottom cell is `k`-connected
  have hFconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j)
      (Work.RatHurewicz.homotopyFibre f s₀)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) :=
    Work.Stems.subsingleton_homotopyFibre_bottomCell hk f s₀ hmodel hbij
  -- path connectedness of `Z` and of the mapping track
  have hpcZ : PathConnectedSpace Z :=
    pathConnectedSpace_of_subsingleton_pi_zero (f s₀) (hmodel 0 (by omega) (by omega))
  have hpcTrack : PathConnectedSpace (Track f) := pathConnectedSpace_track_bottom (by omega) f s₀
  -- `F` is rationally acyclic below `k+1` (it is `k`-connected)
  have hFvanish : ∀ j : ℕ, 0 < j → j < k + 1 →
      IsZero (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre f s₀)) j) :=
    Work.Serre.serreE0Range (Work.RatHurewicz.homotopyFibre f s₀)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀) k (fun i hi => hFconn i hi)
  -- the same vanishing for the *strict* fibre of the track fibration
  have hTFvanish : ∀ j : ℕ, 0 < j → j < k + 1 →
      IsZero (Work.Serre.ratH (TopCat.of ↥(trackFibre f (f s₀))) j) := by
    intro j hj hj'
    exact Work.Stems.isZero_ratH_of_homotopyEquiv ((trackHomeo f s₀).symm.toHomotopyEquiv) j
      (hFvanish j hj hj')
  -- the track fibration is a Serre fibration, with path-connected fibre
  have hserre : Work.StemsB.IsSerreFibration (trackMap f) :=
    Work.StemsB.IsHurewiczFibration.isSerreFibration (isHurewiczFibration_trackMap f)
  have hpcFib : PathConnectedSpace (Work.StemsB.fibre (trackMap f) (f s₀)) :=
    Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration (trackMap f) hserre (f s₀)
      hpcTrack hpcZ (hmodel 1 (by omega) (by omega))
  have hconnZ : ∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) Z (f s₀)) :=
    fun i hi => hmodel i (by omega) (by omega)
  -- **the rational pair comparison at `(b,f) = (k,k+1)`, stable up to `2k+1`**
  obtain ⟨hpair, -⟩ := ratPairComparison_proof (trackMap f) hserre (f s₀) k (k + 1)
    (by omega) (by omega) hpcTrack hpcZ hconnZ hpcFib (fun j hj hj' => hTFvanish j hj hj')
  -- the total space of the track fibration has no rational homology in degree `k+1`
  have hTrack : IsZero (Work.Serre.ratH (TopCat.of (Track f)) (k + 1)) :=
    isZero_ratH_track_bottom (k := k) (j := k + 1) (by omega) f (by omega) (by omega)
  -- so the connecting map `H_{k+1}(Track,fibre) → H_k(fibre)` of the pair sequence is injective
  have hmono : Mono (Work.StemsB.relChainsRδ ℚ (TopCat.of (Track f))
      (trackFibre f (f s₀)) k) :=
    ShortComplex.Exact.mono_g
      (Work.StemsB.relChainsR_exact₃ ℚ (TopCat.of (Track f)) (trackFibre f (f s₀)) k)
      (IsZero.eq_zero_of_src hTrack _)
  -- its target vanishes because the fibre is `k`-connected
  have hrel : IsZero (relHRat (TopCat.of (Track f)) (trackFibre f (f s₀)) (k + 1)) :=
    isZero_of_mono_of_isZero_rat _ hmono (hTFvanish k (by omega) (by omega))
  -- the point has no positive-degree rational homology
  obtain ⟨e1⟩ := nonempty_iso_cokernelπ_of_isZero (TopCat.of Z) ({f s₀} : Set Z) k
    (isZero_ratH_singleton (f s₀) (by omega)) (isZero_ratH_singleton (f s₀) (by omega))
  obtain ⟨e2⟩ := hpair (k + 1) (by omega)
  exact IsZero.of_iso (IsZero.of_iso hrel e2.symm) e1

end

end Work.RatHurewicz
