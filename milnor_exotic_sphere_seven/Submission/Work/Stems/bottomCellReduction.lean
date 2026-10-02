import Mathlib
import Submission.Work.RatHurewicz.S3Corr
import Submission.Work.RatHurewicz.injective_homologyMap_trackProj
import Submission.Work.StemsB.SphLoopTools
import Submission.Work.Stems.homotopyFibre_conn
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.Serre.ZeroCase.Bridge
import Submission.Work.StemsB.RatBaseNaturality
import Submission.Work.Serre.Engine

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The bottom cell of a range model of `K(ℤ,k)`: the reduction to the `k`-connected cover

Let `k ≥ 3`, let `Z` be a space whose homotopy groups vanish in degrees `≤ 2k-1` except in degree
`k` (`Work.Serre.IsRangeKModel k (2*k-1) z₀`), and let `f : Sᵏ → Z` be a based map inducing a
bijection on `πₖ` (the "bottom cell" of the range model; it exists by
`Work.RatHurewicz.exists_bijective_piMapN_rangeModel`).  Write `F` for the homotopy fibre of `f` —
the `k`-connected cover of `Sᵏ`.

The **stable-range Serre exact sequence** applied to the mapping track of `f` — whose total space is
`Sᵏ` up to homotopy and whose fibre is `F` — has stable range `b + f = k + k = 2k`, which is
*exactly* the range needed for the Eilenberg–MacLane computation (the range-form `C2` induction
loses a constant number of degrees per level and cannot reach it).  This module records the
resulting reduction:

* `Work.Stems.subsingleton_homotopyFibre_bottomCell` — `F` is `k`-connected;
* `Work.Stems.homologyIso_bottomCell` — `H_{n+2}(Z; ℤ) ≅ H_{n+1}(F; ℤ)` for `k ≤ n ≤ 2k-3`;
* `Work.Stems.isZero_homology_bottomCell` — `H_{k+1}(Z; ℤ) = 0`.

Consequently the homology of a range model of `K(ℤ,k)` vanishes in the range `k < i ≤ 2k-1`
**if and only if** the `k`-connected cover of `Sᵏ` is acyclic there — the "cover of the sphere"
form of the `C2` computation, with no deficit.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology Topology.Homotopy unitInterval

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Stems

noncomputable section

/-- **A monomorphism into a zero module has zero source** (for `ℤ`-modules). -/
theorem isZero_of_mono_of_isZero_int {M N : ModuleCat ℤ} (f : M ⟶ N) (hmono : Mono f)
    (h : IsZero N) : IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  exact ⟨fun a b => (ModuleCat.mono_iff_injective f).mp hmono (Subsingleton.elim _ _)⟩

/-- An isomorphism from a monomorphism that is also an epimorphism. -/
noncomputable def isoOfMonoEpi {M N : ModuleCat ℤ} (f : M ⟶ N) (h1 : Mono f) (h2 : Epi f) : M ≅ N := by
  haveI := h1
  haveI := h2
  haveI : IsIso f := isIso_of_mono_of_epi f
  exact asIso f

/-- **Flat base change for singular homology**, `H_n(X; ℚ) ≅ H_n(X; ℤ) ⊗[ℤ] ℚ`.

This is a verbatim copy of `Work.StemsB.homologyBaseChangeRat`
(`Submission/Work/StemsB/WangCohRat.lean`, subproject STEMSB) into this module: that module's import
closure is incompatible with the one of this file (it pulls in `Work.Cohomology.relComplexIsoDualZ`
in addition to its copy `Work.Cohomology.CompatTrans.relComplexIsoDualZ`), while
`Work.StemsB.RatBC.Phi` and `Work.StemsB.SphRat.homologyMapBaseChange` are available. -/
noncomputable def homologyBaseChangeRatG (X : TopCat) (n : ℕ) :
    (Work.Cohomology.singularChains ℚ X).homology n ≅
      Work.StemsB.RatBC.IntRat.obj ((Work.Cohomology.singularChains ℤ X).homology n) := by
  haveI : PreservesFiniteLimits Work.StemsB.RatBC.IntRat :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by rw [RingHom.Flat]; infer_instance)
  haveI : PreservesFiniteColimits Work.StemsB.RatBC.IntRat := inferInstance
  haveI : Work.StemsB.RatBC.IntRat.PreservesHomology := inferInstance
  exact (HomologicalComplex.homologyMapIso (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X)) n).symm ≪≫
    (Work.StemsB.SphRat.homologyMapBaseChange Work.StemsB.RatBC.IntRat
      (Work.Cohomology.singularChains ℤ X) n).some

/-- **The absolute homology of a space with a base point whose positive-degree homology vanishes**:
`H_{i+1}(Z; ℤ) ≅ H_{i+1}(Z, {z}; ℤ)` for `1 ≤ i`.  Both ends of the pair sequence of
`(Z, {z})` vanish, so the middle map is an isomorphism. -/
theorem homologyIso_rel_singleton (Z : TopCat) (z : Z) {i : ℕ} (hi : 1 ≤ i) :
    Nonempty ((Work.Cohomology.singularChains ℤ Z).homology (i + 1) ≅
      (Work.Cohomology.relChains Z ({z} : Set Z)).homology (i + 1)) := by
  have hpt : IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥({z} : Set Z))).homology (i + 1)) :=
    Work.Cohomology.homologyContractible (i + 1) (by omega)
  have hpt' : IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥({z} : Set Z))).homology i) :=
    Work.Cohomology.homologyContractible i hi
  have hmono : Mono (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains Z ({z} : Set Z))) (i + 1)) :=
    ShortComplex.Exact.mono_g (Work.Cohomology.hPair_exact₂ Z ({z} : Set Z) (i + 1))
      (IsZero.eq_zero_of_src hpt _)
  have hepi : Epi (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains Z ({z} : Set Z))) (i + 1)) :=
    ShortComplex.Exact.epi_f (Work.Cohomology.hPair_exact₃ Z ({z} : Set Z) i)
      (IsZero.eq_zero_of_tgt hpt' _)
  exact ⟨isoOfMonoEpi _ hmono hepi⟩

variable {Z : Type} [TopologicalSpace Z]

/-- **The homotopy fibre of the bottom cell of a range model of `K(ℤ,k)` is `k`-connected.** -/
theorem subsingleton_homotopyFibre_bottomCell {k : ℕ} (hk : 3 ≤ k)
    (f : C(Work.Serre.Sph k, Z)) (s₀ : Work.Serre.Sph k)
    (hmodel : Work.RatHurewicz.IsRangeKModel k (k + 1) (f s₀))
    (hbij : Function.Bijective (Work.Serre.piMapN f k s₀)) :
    ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j)
      (Work.RatHurewicz.homotopyFibre f s₀)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) := by
  refine Work.Stems.subsingleton_homotopyFibre_of_inj_surj f k (by omega) s₀ ?_ ?_
  · intro i hi
    by_cases hin : i = k
    · subst hin; exact hbij.1
    · haveI : Subsingleton (HomotopyGroup (Fin i) (Work.Serre.Sph k) s₀) :=
        Work.Stems.sphereConnectivity k i (by omega) s₀
      exact fun a b _ => Subsingleton.elim a b
  · intro i hi
    by_cases hin : i = k
    · subst hin; exact hbij.2
    · haveI : Subsingleton (HomotopyGroup (Fin i) Z (f s₀)) := hmodel i (by omega) hin
      exact fun y => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩

/-- **The singular homology of the mapping track of the bottom cell vanishes away from the sphere's
homology degrees.**  For `j ≠ 0, k`, `H_j(Track f; ℤ) = 0`: the projection `Track f → Sᵏ` is a
homotopy equivalence, hence injective on homology, and `H_j(Sᵏ; ℤ) = 0`. -/
theorem isZero_homology_track_of_bottomCell {k : ℕ} (hk : 1 ≤ k)
    (f : C(Work.Serre.Sph k, Z)) (s₀ : Work.Serre.Sph k) {j : ℕ} (hj0 : j ≠ 0) (hjk : j ≠ k) :
    IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of (Work.RatHurewicz.Track f))).homology j) := by
  refine isZero_of_mono_of_isZero_int
    (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of (Work.RatHurewicz.Track f)) (TopCat.of (Work.Serre.Sph k))
      (TopCat.ofHom (Work.RatHurewicz.trackProj f))) j) ?_ ?_
  · exact (ModuleCat.mono_iff_injective _).mpr
      (Work.RatHurewicz.injective_homologyMap_trackProj f j)
  · exact Work.Cohomology.sphereVanishing k j hk hj0 hjk

/-- **The homotopy fibre of the bottom cell is the `k`-connected cover of `Sᵏ`.**  For a space `Z`
whose homotopy groups vanish below degree `N` except in degree `k`, the projection
`π_{n+2}(F) → π_{n+2}(Sᵏ)` of the homotopy fibre of the bottom cell `f` is an isomorphism for
`k + 1 ≤ n + 2 ≤ N - 1`: it is surjective because `π_{n+2}(Z) = 0`, and injective because
`π_{n+3}(Z) = 0` kills the connecting map.  This is the input of the *next* stage of the EHP
recursion (the fibre over the cover is `(k+1)`-connected, with Serre range `2k+2`). -/
theorem piMap_homotopyFibreFst_bijective {k N n : ℕ} (hk : 2 ≤ k)
    (f : C(Work.Serre.Sph k, Z)) (s₀ : Work.Serre.Sph k)
    (hmodel : ∀ j : ℕ, j ≤ N → j ≠ k → Subsingleton (HomotopyGroup (Fin j) Z (f s₀)))
    (hn1 : k - 1 ≤ n) (hn2 : n + 3 ≤ N) :
    Function.Bijective (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst f s₀) (n + 1)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) := by
  obtain ⟨del, d, h1, h2, _h3, _h4⟩ := Work.RatHurewicz.pair_les f s₀ n (by omega)
  constructor
  · intro x y hxy
    have hker : Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst f s₀) (n + 1)
        (Work.RatHurewicz.homotopyFibreBasepoint f s₀) (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    obtain ⟨u, hu⟩ := (h1 (x * y⁻¹)).mp hker
    have hu1 : u = 1 := (hmodel (n + 3) (by omega) (by omega)).elim u 1
    have : x * y⁻¹ = 1 := by rw [← hu, hu1, map_one]
    exact mul_inv_eq_one.mp this
  · intro y
    have hy : Work.StemsB.πmap f (n + 1) s₀ y = 1 :=
      (hmodel (n + 2) (by omega) (by omega)).elim _ 1
    obtain ⟨x, hx⟩ := (h2 y).mp hy
    exact ⟨x, hx⟩

/-- **The stable-range Serre comparison for the mapping track**, in the *connectivity* form: for a
map `inc : X → Z` whose source is `k`-connected and whose homotopy fibre is `k`-connected, the pair
map of the track is an isomorphism in degrees `< 2k`.

This is `Work.RatHurewicz.S3Corr.isIso_relPairMap_trackMap` with the range-model hypothesis on the
base weakened to the connectivity that the Serre exact sequence actually uses, so that it applies
to arbitrary `(k-1)`-connected bases — the form the iterated EHP reduction needs. -/
theorem isIso_relPairMap_trackMap_of_conn (h : Work.Serre.SerreExactRangeCorrected) {X : Type}
    [TopologicalSpace X] (inc : C(X, Z)) (x₀ : X) {k n : ℕ} (hk : 2 ≤ k)
    (hb : ∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) Z (inc x₀)))
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j)
      (Work.RatHurewicz.homotopyFibre inc x₀)
      (Work.RatHurewicz.homotopyFibreBasepoint inc x₀)))
    (hrange : n + 1 ≤ 2 * k - 2) :
    IsIso (HomologicalComplex.homologyMap
      (Work.StemsB.relPairMap (Work.RatHurewicz.trackMap inc) (inc x₀)) (n + 2)) := by
  refine h (Work.RatHurewicz.Track inc) Z (Work.RatHurewicz.trackMap inc)
    (Work.RatHurewicz.isHurewiczFibration_trackMap inc) (Work.RatHurewicz.trackBase inc x₀)
    (inc x₀) (Work.RatHurewicz.trackMap_trackBase inc x₀) k (k + 1) (by omega) ?_ ?_ (n + 2) ?_
  · intro i hi
    exact hb i hi
  · intro i hi
    have hbase :
        (⟨Work.RatHurewicz.trackBase inc x₀, Work.RatHurewicz.trackMap_trackBase inc x₀⟩ :
          ↥{x : Work.RatHurewicz.Track inc | Work.RatHurewicz.trackMap inc x = inc x₀})
        = ⟨Work.RatHurewicz.trackBase inc x₀,
            Work.RatHurewicz.trackBase_mem_trackFibre inc x₀⟩ := rfl
    rw [hbase]
    exact Work.RatHurewicz.subsingleton_homotopyGroup_trackFibre inc x₀ (f := k + 1)
      (fun j hj => hconn j (by omega)) i hi
  · omega

/-- **The reduction in the connectivity form.**  For a `(k-1)`-connected space `Y` with a based map
`f : Sᵏ → Y` (playing the role of the "bottom cell"; only the `k`-connectivity of the homotopy fibre
is needed), `H_{n+2}(Y; ℤ) ≅ H_{n+1}(F; ℤ)` for `k ≤ n ≤ 2k-3`, where `F` is the homotopy fibre of
`f`.  The stable range of the Serre exact sequence is `k + k = 2k`, so no degree is lost. -/
theorem homologyIso_bottomCell_gen (h : Work.Serre.SerreExactRangeCorrected) {k n : ℕ} (hk : 3 ≤ k)
    (f : C(Work.Serre.Sph k, Z)) (s₀ : Work.Serre.Sph k)
    (hb : ∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) Z (f s₀)))
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j)
      (Work.RatHurewicz.homotopyFibre f s₀)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)))
    (hn1 : k ≤ n) (hn2 : n ≤ 2 * k - 3) :
    Nonempty ((Work.Cohomology.singularChains ℤ (TopCat.of Z)).homology (n + 2) ≅
      (Work.Cohomology.singularChains ℤ (TopCat.of (Work.RatHurewicz.homotopyFibre f s₀))).homology
        (n + 1)) := by
  have hserre : IsIso (HomologicalComplex.homologyMap
      (Work.StemsB.relPairMap (Work.RatHurewicz.trackMap f) (f s₀)) (n + 2)) :=
    isIso_relPairMap_trackMap_of_conn h f s₀ (by omega) hb hconn (by omega)
  have hdelta : IsIso (Work.Cohomology.hPairδ (TopCat.of (Work.RatHurewicz.Track f))
      (Work.RatHurewicz.trackFibre f (f s₀)) (n + 1)) :=
    Work.StemsB.isIso_hPairδ_of_isZero _ _ (n + 2) (by omega)
      (isZero_homology_track_of_bottomCell (by omega) f s₀ (by omega) (by omega))
      (isZero_homology_track_of_bottomCell (by omega) f s₀ (by omega) (by omega))
  obtain ⟨eZ⟩ := homologyIso_rel_singleton (TopCat.of Z) (f s₀) (i := n + 1) (by omega)
  obtain ⟨eF⟩ := Work.Cohomology.homologyIso_of_homotopyEquiv
    (Work.RatHurewicz.trackHomeo f s₀).toHomotopyEquiv (n + 1)
  exact ⟨eZ ≪≫ (asIso (HomologicalComplex.homologyMap
      (Work.StemsB.relPairMap (Work.RatHurewicz.trackMap f) (f s₀)) (n + 2))).symm
    ≪≫ asIso (Work.Cohomology.hPairδ (TopCat.of (Work.RatHurewicz.Track f))
      (Work.RatHurewicz.trackFibre f (f s₀)) (n + 1)) ≪≫ eF.symm⟩

/-- **The `k`-connected cover form of the `C2` computation.**  With `f : Sᵏ → Z` the bottom cell of
a range model of `K(ℤ,k)` and `F` its homotopy fibre, `H_{n+2}(Z; ℤ) ≅ H_{n+1}(F; ℤ)` for
`k ≤ n ≤ 2k - 3`.  The two identifications are the stable-range Serre exact sequence for the
mapping track of `f` (stable range `k + k = 2k`) and the pair sequence of the track. -/
theorem homologyIso_bottomCell (h : Work.Serre.SerreExactRangeCorrected) {k n : ℕ} (hk : 3 ≤ k)
    (f : C(Work.Serre.Sph k, Z)) (s₀ : Work.Serre.Sph k)
    (hmodel : Work.RatHurewicz.IsRangeKModel k (k + 1) (f s₀))
    (hbij : Function.Bijective (Work.Serre.piMapN f k s₀))
    (hn1 : k ≤ n) (hn2 : n ≤ 2 * k - 3) :
    Nonempty ((Work.Cohomology.singularChains ℤ (TopCat.of Z)).homology (n + 2) ≅
      (Work.Cohomology.singularChains ℤ (TopCat.of (Work.RatHurewicz.homotopyFibre f s₀))).homology
        (n + 1)) :=
  homologyIso_bottomCell_gen h hk f s₀ (fun i hi => hmodel i (by omega) (by omega))
    (subsingleton_homotopyFibre_bottomCell hk f s₀ hmodel hbij) hn1 hn2

/-- **`H_{k+1}` of a range model of `K(ℤ,k)` vanishes.**  The degree just above the generator is
not reached by the range-form `C2` statements for odd `k`; here it follows from the same Serre
exact sequence, because the pair `(Sᵏ, F)` has `H_{k+1} = H_k(F) = 0` with `F` `k`-connected. -/
theorem isZero_homology_bottomCell (h : Work.Serre.SerreExactRangeCorrected) {k : ℕ} (hk : 3 ≤ k)
    (f : C(Work.Serre.Sph k, Z)) (s₀ : Work.Serre.Sph k)
    (hmodel : Work.RatHurewicz.IsRangeKModel k (k + 1) (f s₀))
    (hbij : Function.Bijective (Work.Serre.piMapN f k s₀)) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of Z)).homology (k + 1)) := by
  have hconn := subsingleton_homotopyFibre_bottomCell hk f s₀ hmodel hbij
  -- the `k`-connected cover `F` has no homology in degrees `≤ k`
  have hF : IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of (Work.RatHurewicz.homotopyFibre f s₀))).homology k) :=
    Work.Serre.isZero_singularChains_homology_of_pi_subsingleton
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀) (k + 1)
      (fun i hi => hconn i (by omega)) k (by omega) (by omega)
  obtain ⟨eF⟩ := Work.Cohomology.homologyIso_of_homotopyEquiv
    (Work.RatHurewicz.trackHomeo f s₀).toHomotopyEquiv k
  -- over the track, `H_{k+1}` of the pair is a submodule of `H_k` of the fibre, which vanishes
  have htrackFib : IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(Work.RatHurewicz.trackFibre f (f s₀)))).homology k) :=
    IsZero.of_iso hF eF.symm
  have hmono : Mono (Work.Cohomology.hPairδ (TopCat.of (Work.RatHurewicz.Track f))
      (Work.RatHurewicz.trackFibre f (f s₀)) k) :=
    ShortComplex.Exact.mono_g (Work.Cohomology.hPair_exact₃ (TopCat.of (Work.RatHurewicz.Track f))
      (Work.RatHurewicz.trackFibre f (f s₀)) k)
      (IsZero.eq_zero_of_src
        (isZero_homology_track_of_bottomCell (by omega) f s₀ (by omega) (by omega)) _)
  have hpair : IsZero ((Work.Cohomology.relChains (TopCat.of (Work.RatHurewicz.Track f))
      (Work.RatHurewicz.trackFibre f (f s₀))).homology (k + 1)) :=
    isZero_of_mono_of_isZero_int _ hmono htrackFib
  -- Serre's exact sequence replaces the track pair by the pair of `Z`
  have hserre : IsIso (HomologicalComplex.homologyMap
      (Work.StemsB.relPairMap (Work.RatHurewicz.trackMap f) (f s₀)) (k + 1)) := by
    have h1 := isIso_relPairMap_trackMap_of_conn (k := k) (n := k - 1) h f s₀ (by omega)
      (fun i hi => hmodel i (by omega) (by omega)) hconn (by omega)
    rwa [show (k - 1) + 2 = k + 1 from by omega] at h1
  have hrel : IsZero ((Work.Cohomology.relChains (TopCat.of Z)
      ({f s₀} : Set Z)).homology (k + 1)) :=
    IsZero.of_iso hpair (asIso (HomologicalComplex.homologyMap
      (Work.StemsB.relPairMap (Work.RatHurewicz.trackMap f) (f s₀)) (k + 1))).symm
  obtain ⟨eZ⟩ := homologyIso_rel_singleton (TopCat.of Z) (f s₀) (i := k) (by omega)
  exact IsZero.of_iso hrel eZ


/-! ## The rational form, and the resulting reduction of the `C2` computation -/
/-- **The reduction to the `k`-connected cover, over `ℚ`.**  `H_{n+2}(Y; ℚ) ≅ H_{n+1}(F; ℚ)` for
`k ≤ n ≤ 2k-3`: the integral isomorphism `Work.Stems.homologyIso_bottomCell_gen` transported along
the flat base change `H_*(−; ℚ) ≅ H_*(−; ℤ) ⊗[ℤ] ℚ`. -/
theorem ratH_iso_bottomCell_gen (h : Work.Serre.SerreExactRangeCorrected) {k n : ℕ} (hk : 3 ≤ k)
    (f : C(Work.Serre.Sph k, Z)) (s₀ : Work.Serre.Sph k)
    (hb : ∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) Z (f s₀)))
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j)
      (Work.RatHurewicz.homotopyFibre f s₀)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)))
    (hn1 : k ≤ n) (hn2 : n ≤ 2 * k - 3) :
    Nonempty (Work.Serre.ratH (TopCat.of Z) (n + 2) ≅
      Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre f s₀)) (n + 1)) := by
  obtain ⟨eℤ⟩ := homologyIso_bottomCell_gen h hk f s₀ hb hconn hn1 hn2
  exact ⟨homologyBaseChangeRatG (TopCat.of Z) (n + 2) ≪≫
    Work.StemsB.RatBC.IntRat.mapIso eℤ ≪≫
    (homologyBaseChangeRatG (TopCat.of (Work.RatHurewicz.homotopyFibre f s₀)) (n + 1)).symm⟩

/-- **The reduction in the connectivity form, over `ℚ`.**  If the homotopy fibre `F` of the bottom
cell is rationally acyclic in degree `n+1` (`k ≤ n ≤ 2k-3`) then `H_{n+2}(Y; ℚ) = 0`. -/
theorem isZero_ratH_of_cover_gen (h : Work.Serre.SerreExactRangeCorrected) {k n : ℕ} (hk : 3 ≤ k)
    (f : C(Work.Serre.Sph k, Z)) (s₀ : Work.Serre.Sph k)
    (hb : ∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) Z (f s₀)))
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j)
      (Work.RatHurewicz.homotopyFibre f s₀)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)))
    (hn1 : k ≤ n) (hn2 : n ≤ 2 * k - 3)
    (hF : IsZero (Work.Serre.ratH
      (TopCat.of (Work.RatHurewicz.homotopyFibre f s₀)) (n + 1))) :
    IsZero (Work.Serre.ratH (TopCat.of Z) (n + 2)) :=
  IsZero.of_iso hF (ratH_iso_bottomCell_gen h hk f s₀ hb hconn hn1 hn2).some

/-- **The `C2` computation for a range model of `K(ℤ,k)` from the acyclicity of its `k`-connected
cover.**  For `k ≤ n ≤ 2k-3`, if the homotopy fibre of the bottom cell is rationally acyclic in
degree `n+1`, then `H_{n+2}(Z; ℚ) = 0`. -/
theorem isZero_ratH_rangeModel_of_cover (h : Work.Serre.SerreExactRangeCorrected) {k n : ℕ}
    (hk : 3 ≤ k) (f : C(Work.Serre.Sph k, Z)) (s₀ : Work.Serre.Sph k)
    (hmodel : Work.RatHurewicz.IsRangeKModel k (k + 1) (f s₀))
    (hbij : Function.Bijective (Work.Serre.piMapN f k s₀))
    (hn1 : k ≤ n) (hn2 : n ≤ 2 * k - 3)
    (hF : IsZero (Work.Serre.ratH
      (TopCat.of (Work.RatHurewicz.homotopyFibre f s₀)) (n + 1))) :
    IsZero (Work.Serre.ratH (TopCat.of Z) (n + 2)) :=
  isZero_ratH_of_cover_gen h hk f s₀ (fun i hi => hmodel i (by omega) (by omega))
    (subsingleton_homotopyFibre_bottomCell hk f s₀ hmodel hbij) hn1 hn2 hF

/-- **`H_{k+1}` of a range model of `K(ℤ,k)` vanishes rationally.** -/
theorem isZero_ratH_bottomCell (h : Work.Serre.SerreExactRangeCorrected) {k : ℕ} (hk : 3 ≤ k)
    (f : C(Work.Serre.Sph k, Z)) (s₀ : Work.Serre.Sph k)
    (hmodel : Work.RatHurewicz.IsRangeKModel k (k + 1) (f s₀))
    (hbij : Function.Bijective (Work.Serre.piMapN f k s₀)) :
    IsZero (Work.Serre.ratH (TopCat.of Z) (k + 1)) :=
  Work.StemsB.isZero_homology_rat_of_isZero_homology_int (TopCat.of Z) (k + 1)
    (isZero_homology_bottomCell h hk f s₀ hmodel hbij)

end

end Work.Stems
