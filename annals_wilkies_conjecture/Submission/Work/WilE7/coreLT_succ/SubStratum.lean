/-
  `Work.WilE7.coreLT_succ.SubStratum`: the tangent-space structure of a `Good` absolute stratum
  contained in another one.

  The `CoreLT_succ` assembly splits each level-`(n+1)` piece of `piFamilyTop` by its `π_n`-rank.
  The piece has `π_{n+1}`-rank `= dim`, and on the locus where also the `π_n`-rank equals `dim`
  it is an immersion for `π_n`; the `Good` strata of that locus then automatically satisfy the
  `hrank` hypothesis `projRank T z = n + (m+1) - T.j` of the sheet lemmas
  (`Work.CoreStep.sheets_over_cell_of_hrank`, `Work.CoreStep.branchDomain_open`).

  The key structural lemma is `ker_jac_le_ker_jac`: for absolute `Good` strata `S ⊆ T` the
  tangent space of `S` is contained in that of `T`.  It is the absolute version of the argument
  used in `Work.WilE7.DimAPI.projRank_eq_dim_of_sub_fibreGood`
  (`Work.WilE7.Auxiliary.kerLeKerOfVanishLevelSet` applied to the defining equation maps),
  and it needs no fibrewise hypothesis.

  Consequences proved here:

  * `projRank_le_of_sub` — `projRank` is monotone under inclusion of absolute `Good` strata;
  * `projRank_eq_dim_of_sub_rankLocus` — **`hrank` is inherited**: if every point of `S` lies in
    the locus of `T` where `projRank T = dim T`, then `projRank S z = dim S` for every
    `z ∈ S.X.set`;
  * `fiber_subset_of_sub` / `fiber_finite_of_sub` — the fibres over the base are inherited.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.rankLocusAux
import Submission.Work.WilE7.DimAPI.rankLocus_nullDimLE
import Submission.Work.WilE7.DimAPI.ProjRankAux
import Submission.Work.WilE7.Auxiliary.kerLeKerOfVanishLevelSet
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.coreLT_succ

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-! ## Two linear-algebra helpers -/

/-- Rank–nullity in the form needed here: the dimension of the kernel of the Jacobian of an
absolute `Good` stratum at one of its points is the dimension `N - S.j` of the stratum. -/
theorem finrank_ker_jac {N : ℕ} (S : Stratum 0 N) (hS : S.Good) {z : Fin (0 + N) → ℝ}
    (hz : z ∈ S.X.set) :
    Module.finrank ℝ (LinearMap.ker (jac S z)) = N - S.j := by
  have h := LinearMap.finrank_range_add_finrank_ker (jac S z)
  rw [Work.WilE7.DimAPI.jacRankGood S hS hz, Module.finrank_fin_fun] at h
  omega

/-- If `B` is injective on the submodule `p` (equivalently `p ⊓ ker B = ⊥`), then `p` and its
image have the same dimension. -/
theorem finrank_map_eq_of_inf_ker_eq_bot {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (B : V →ₗ[ℝ] W) (p : Submodule ℝ V)
    (h : p ⊓ LinearMap.ker B = ⊥) : Module.finrank ℝ (p.map B) = Module.finrank ℝ p := by
  have hinj : Function.Injective (B.domRestrict p) := by
    intro x y hxy
    have hxy' : B (x : V) = B (y : V) := hxy
    have hmem : (x : V) - (y : V) ∈ p ⊓ LinearMap.ker B := by
      refine Submodule.mem_inf.mpr ⟨p.sub_mem x.2 y.2, ?_⟩
      rw [LinearMap.mem_ker, map_sub, hxy', sub_self]
    rw [h] at hmem
    simp only [Submodule.mem_bot] at hmem
    exact Subtype.ext (sub_eq_zero.mp hmem)
  rw [← LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj hinj

/-! ## The defining-equation family, as a map to `Fin S.j → ℝ` -/

/-- The defining-equation family of an absolute stratum. -/
def eqFam {N : ℕ} (S : Stratum 0 N) : (Fin (0 + N) → ℝ) → (Fin S.j → ℝ) :=
  fun w a => eaEval S.X.c (S.h a) w

@[simp] theorem eqFam_apply {N : ℕ} (S : Stratum 0 N) (w : Fin (0 + N) → ℝ) (a : Fin S.j) :
    eqFam S w a = eaEval S.X.c (S.h a) w := rfl

/-- **The tangent space of an absolute `Good` sub-stratum.**  If `S ⊆ T` are absolute `Good`
strata and `z ∈ S.X.set`, then `ker (jac S z) ≤ ker (jac T z)`: every vector tangent to `S` at
`z` is tangent to `T`. -/
theorem ker_jac_le_ker_jac {N : ℕ} (S T : Stratum 0 N) (hS : S.Good) (hT : T.Good)
    (hsub : S.X.set ⊆ T.X.set) {z : Fin (0 + N) → ℝ} (hz : z ∈ S.X.set) :
    LinearMap.ker (jac S z) ≤ LinearMap.ker (jac T z) := by
  have hzT : z ∈ T.X.set := hsub hz
  -- the equation family of `S`, as a map
  have hgan : AnalyticAt ℝ (eqFam S) z := Work.WilE7.DimAPI.eaFamily_analyticAt S.X.c S.h z
  have hgz : eqFam S z = 0 := by
    funext a
    exact (hS z hz).1 a
  have hsurj : (fderiv ℝ (eqFam S) z).range = ⊤ :=
    LinearMap.range_eq_top.mpr (Work.WilE7.DimAPI.eaFamily_surj_of_good S hS hz)
  -- the locality clause of `S.Good` (the `projFirst 0 N` condition is vacuous)
  have hloc : ∀ᶠ z' in 𝓝 z, (∀ a : Fin S.j, eaEval S.X.c (S.h a) z' = 0) → z' ∈ S.X.set :=
    (hS z hz).2.2.mono fun z' hz' hg' => hz' (Subsingleton.elim _ _) hg'
  -- every defining equation of `T` vanishes along the level set of `S`
  have key : ∀ a : Fin T.j, ∀ v : Fin (0 + N) → ℝ, v ∈ LinearMap.ker (jac S z) →
      (∑ i : Fin (0 + N), eaEval T.X.c (eaD T.X.c i (T.h a)) z * v i) = 0 := by
    intro a v hv
    have hv' : (fderiv ℝ (eqFam S) z) v = 0 := by
      rw [show (fderiv ℝ (eqFam S) z) v
            = fderiv ℝ (fun w : Fin (0 + N) → ℝ => fun b : Fin S.j =>
                eaEval S.X.c (S.h b) w) z v from rfl,
        Work.WilE7.DimAPI.fderiv_eaFamily_apply_jac S z v]
      exact LinearMap.mem_ker.mp hv
    have hvan : ∀ᶠ z' in 𝓝 z,
        eqFam S z' = 0 → (fun w : Fin (0 + N) → ℝ => eaEval T.X.c (T.h a) w) z'
          = (fun w : Fin (0 + N) → ℝ => eaEval T.X.c (T.h a) w) z := by
      refine hloc.mono fun z' hz' hg' => ?_
      have hz'S : z' ∈ S.X.set := hz' fun b => congrFun hg' b
      have hz'T : z' ∈ T.X.set := hsub hz'S
      show eaEval T.X.c (T.h a) z' = eaEval T.X.c (T.h a) z
      rw [(hT z' hz'T).1 a, (hT z hzT).1 a]
    have hF0 := Work.WilE5.Calc.hasFDerivAt_eaEval T.X.c (T.h a) z
    have hF' : HasFDerivAt (fun w : Fin (0 + N) → ℝ => eaEval T.X.c (T.h a) w)
        (fderiv ℝ (fun w : Fin (0 + N) → ℝ => eaEval T.X.c (T.h a) w) z) z := by
      rw [hF0.fderiv]; exact hF0
    have hle := Work.WilE7.Auxiliary.kerLeKerOfVanishLevelSet (eqFam S)
      (fun w : Fin (0 + N) → ℝ => eaEval T.X.c (T.h a) w) z (fderiv ℝ (eqFam S) z)
      (fderiv ℝ (fun w : Fin (0 + N) → ℝ => eaEval T.X.c (T.h a) w) z)
      hgan.hasStrictFDerivAt hF' hsurj hgz hvan
    have h0 : fderiv ℝ (fun w : Fin (0 + N) → ℝ => eaEval T.X.c (T.h a) w) z v = 0 := hle hv'
    rw [hF0.fderiv] at h0
    simpa [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul] using h0
  -- assemble: the derivative of the whole family of `T` vanishes on `ker (jac S z)`
  intro v hv
  rw [LinearMap.mem_ker, Work.WilE7.DimAPI.jac_apply]
  funext a
  exact key a v hv

/-! ## Monotonicity of `projRank` -/

/-- **`projRank` is monotone under inclusion of absolute `Good` strata.** -/
theorem projRank_le_of_sub {n m : ℕ} (S T : Stratum 0 (n + m)) (hS : S.Good) (hT : T.Good)
    (hsub : S.X.set ⊆ T.X.set) {z : Fin (0 + (n + m)) → ℝ} (hz : z ∈ S.X.set) :
    projRank S z ≤ projRank T z := by
  have hle := ker_jac_le_ker_jac S T hS hT hsub hz
  exact Submodule.finrank_mono (Submodule.map_mono hle)

/-- The fibres over the base are inherited by sub-strata. -/
theorem fiber_subset_of_sub {n m : ℕ} (S T : Stratum 0 (n + m)) (hsub : S.X.set ⊆ T.X.set) :
    ∀ x : Fin n → ℝ, fiber (absSet S) x ⊆ fiber (absSet T) x := by
  intro x y hy
  obtain ⟨w, hw, hwy⟩ := hy
  exact ⟨w, hsub hw, hwy⟩

/-- Finiteness of the fibres over the base is inherited by sub-strata. -/
theorem fiber_finite_of_sub {n m : ℕ} (S T : Stratum 0 (n + m)) (hsub : S.X.set ⊆ T.X.set)
    (hfin : ∀ x : Fin n → ℝ, (fiber (absSet T) x).Finite) :
    ∀ x : Fin n → ℝ, (fiber (absSet S) x).Finite :=
  fun x => (hfin x).subset (fiber_subset_of_sub S T hsub x)

/-! ## The `hrank` transfer -/

/-- **The `hrank` transfer.**  Let `S ⊆ T` be absolute `Good` strata and suppose that every
point of `S` lies in the locus of `T` where `projRank T = dim T` (i.e. `π_n` is an immersion for
`T` there).  Then `projRank S z = dim S` for every `z ∈ S.X.set`: the sheet lemmas apply to
`S`. -/
theorem projRank_eq_dim_of_sub_rankLocus {n m : ℕ} (S T : Stratum 0 (n + m))
    (hS : S.Good) (hT : T.Good) (hsub : S.X.set ⊆ T.X.set)
    (hrankT : ∀ z ∈ S.X.set, projRank T z = n + m - T.j) :
    ∀ z ∈ S.X.set, projRank S z = n + m - S.j := by
  intro z hz
  have hzT : z ∈ T.X.set := hsub hz
  -- `π_n` is injective on the tangent space of `T` at `z`
  have hdimT : Module.finrank ℝ (LinearMap.ker (jac T z)) = n + m - T.j := finrank_ker_jac T hT hzT
  have hmapT : Module.finrank ℝ ((LinearMap.ker (jac T z)).map (basePrLin n m)) = n + m - T.j :=
    hrankT z hz
  have hdisjT : Disjoint (LinearMap.ker (jac T z)) (LinearMap.ker (basePrLin n m)) :=
    Submodule.disjoint_ker_of_finrank_le (L := LinearMap.ker (jac T z)) (f := basePrLin n m)
      (by rw [hmapT, hdimT])
  have hkerT : LinearMap.ker (jac T z) ⊓ LinearMap.ker (basePrLin n m) = ⊥ :=
    disjoint_iff.mp hdisjT
  -- hence the same for the tangent space of `S`
  have hkerS : LinearMap.ker (jac S z) ⊓ LinearMap.ker (basePrLin n m) = ⊥ := by
    refine eq_bot_iff.mpr fun v hv => ?_
    exact eq_bot_iff.mp hkerT (Submodule.mem_inf.mpr
      ⟨ker_jac_le_ker_jac S T hS hT hsub hz hv.1, hv.2⟩)
  have hdimS : Module.finrank ℝ (LinearMap.ker (jac S z)) = n + m - S.j := finrank_ker_jac S hS hz
  show Module.finrank ℝ ((LinearMap.ker (jac S z)).map (basePrLin n m)) = n + m - S.j
  rw [finrank_map_eq_of_inf_ker_eq_bot (basePrLin n m) _ hkerS, hdimS]

end Work.WilE7.coreLT_succ
