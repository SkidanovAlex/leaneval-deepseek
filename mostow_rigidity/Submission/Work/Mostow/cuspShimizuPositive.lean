import Mathlib
import Submission.Work.Mostow.cuspShimizuDefs
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.hptOf_hdist
import Submission.Work.Mostow.cuspZ2Defs
import Submission.Work.Mostow.cuspHoroInterIff
import Submission.Work.Mostow.paraUniqueFixed
import Submission.Work.Mostow.margulisCusp
import Submission.Work.Mostow.bieberbach
import Submission.Work.Mostow.cuspParabolicFlatTrans

/-!
# Positivity of the Shimizu exponent of a cusp of a lattice

`Work.Mostow.cuspShimizuPositive`: for a lattice `Γ ≤ PO(n,1)` (`n ≥ 2`), a parabolic fixed
point `ξ ∈ parFixed Γ` and the hypothesis `hvan` (every element of `Γ` fixing a parabolic fixed
point preserves the horosphere levels there), the Shimizu exponent `cuspShimizu Γ ξ` is positive.

## Proof

* A *flat translation* in the cusp stabiliser `Γ_ξ` is a parabolic `δ ∈ Γ` fixing `ξ`, preserving
  the horosphere levels, and acting on the flat coordinate by `yc ξ (δ • u) = yc ξ u + v` with
  `v ≠ 0`; its displacement at `u` is `hdist u (δ • u) = arccosh (1 + (lev ξ u)²‖v‖²/2)`, hence
  tends to `0` as `u` goes deep into the cusp at `ξ`, *uniformly* in the flat coordinate.
  Such a `δ` exists by `Work.Mostow.cuspParabolicFlatTrans` (which uses Bieberbach's theorem
  applied to the cocompact action of the cusp stabiliser on its horosphere).
* Suppose the horoball at `ξ` of level `τ` meets its `γ`-translate, `γ ∈ Γ` with `bd γ ξ ≠ ξ`,
  at a point `u`.  Then `δ` is `ε`-short at `u` and the conjugate `σ = γ⁻¹ δ γ` is `1`-short at
  `u` (its displacement at `u` is the displacement of `δ` at `γ • u`, which is deep as well).
  The Margulis lemma `Work.Mostow.margulisCusp` (with `R = 1`) forces `bd σ ξ = ξ`; but `σ` is
  parabolic with the fixed point `bd γ⁻¹ ξ ≠ ξ`, contradicting uniqueness of the fixed point of a
  parabolic isometry (`Work.Mostow.paraUniqueFixed`).
* Hence some horoball at `ξ` is precisely invariant; comparing the level of first contact of the
  horoballs of `ξ` and of `bd γ ξ` with the Shimizu distortion of `γ` (`horoInterSelf`, which
  rests on `cuspHoroInterIff`) bounds every element of the Shimizu set below by
  `2 exp (2 τ) > 0`, and `cuspShimizu Γ ξ` is their infimum.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Classical

noncomputable section

variable {n : ℕ}

/-! ## The displacement of a flat translation -/

/-- The flat coordinate of a point of the chart is orthogonal to `ξ` on the sphere. -/
lemma shimizu_yc_inner_orth {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) : inner ℝ (yc ξ u) ξ = 0 := by
  have h1 : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have h : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
    rw [h]; norm_num
  rw [yc, real_inner_smul_left, wc, inner_sub_left, real_inner_smul_left, h1, mul_one, sub_self,
    mul_zero]

/-- For a flat translation `δ` (`yc ξ (δ • u) = yc ξ u + v`, level preserving), the hyperbolic
distance to its translate is `arccosh (1 + (lev ξ u)^2 ‖v‖^2 / 2)`. -/
lemma shimizu_flatTrans_disp {ξ : E n} (hξ : ξ ∈ Sph n) {δ : PO n 1} {v : E n}
    (hlev : ∀ u : E n, lev ξ (δ • u) = lev ξ u)
    (hyc : ∀ u : E n, yc ξ (δ • u) = yc ξ u + v) (u : E n) :
    hdist u (δ • u) = Real.arcosh (1 + (lev ξ u) ^ 2 * ‖v‖ ^ 2 / 2) := by
  have hD : 0 < lev ξ u := lev_pos ξ hξ u
  have h := hdist_of_lev_eq (D := lev ξ u) hξ hD rfl (hlev u)
  rw [h, hyc u]
  have h2 : yc ξ u - (yc ξ u + v) = -v := by abel
  rw [h2, norm_neg]
  congr 1
  ring

/-- **Uniform deepness.**  A point of level `< D` is moved by the flat translation `δ` by less
than `ε`, provided `1 + D^2 ‖v‖^2/2 < cosh ε`. -/
lemma shimizu_flatTrans_lt_of_level {ξ : E n} (hξ : ξ ∈ Sph n) {δ : PO n 1} {v : E n}
    (hlev : ∀ u : E n, lev ξ (δ • u) = lev ξ u)
    (hyc : ∀ u : E n, yc ξ (δ • u) = yc ξ u + v)
    {D ε : ℝ} (_hDnn : 0 ≤ D) (hε : 0 < ε)
    (hbound : 1 + D ^ 2 * ‖v‖ ^ 2 / 2 < Real.cosh ε) {u : E n} (hu : lev ξ u < D) :
    hdist u (δ • u) < ε := by
  rw [shimizu_flatTrans_disp hξ hlev hyc u, ← Real.arcosh_cosh (le_of_lt hε)]
  refine (Real.arcosh_lt_arcosh (by positivity) (Real.cosh_pos ε)).mpr ?_
  have h1 : lev ξ u ^ 2 < D ^ 2 := by
    have hpos : 0 < lev ξ u := lev_pos ξ hξ u
    nlinarith
  have h2 : (lev ξ u) ^ 2 * ‖v‖ ^ 2 / 2 ≤ D ^ 2 * ‖v‖ ^ 2 / 2 := by
    have := sq_nonneg ‖v‖
    nlinarith
  linarith

/-! ## Shimizu's lemma from a flat translation -/

/-- **The Margulis argument.**  Given a flat translation in the cusp stabiliser of `ξ`, the
horoballs at `ξ` of a sufficiently deep level are precisely invariant: no point and its
`γ`-image (for `γ ∈ Γ` with `bd γ ξ ≠ ξ`) can both lie inside. -/
theorem cuspPreciseInvariantOfFlatTrans (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n)
    (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ)
    (ξ : E n) (hξ : ξ ∈ parFixed Γ)
    (hδ : ∃ δ : Γ, IsParabolic (δ : PO n 1) ∧ bd (δ : PO n 1) ξ = ξ ∧
      bCocy (δ : PO n 1) ξ = 0 ∧
      ∃ v : E n, v ≠ 0 ∧ inner ℝ v ξ = 0 ∧
        ∀ u : E n, yc ξ ((δ : PO n 1) • u) = yc ξ u + v) :
    ∃ τ : ℝ, ∀ γ : Γ, bd (γ : PO n 1) ξ ≠ ξ →
      ¬ ∃ u : E n, busemann ξ u < τ ∧ busemann ξ ((γ : PO n 1) • u) < τ := by
  have hξS : ξ ∈ Sph n := hξ.1
  obtain ⟨δ, hδpar, hδfix, hδbc, v, hvne, -, hyc⟩ := hδ
  have hpb : POBasic n := POBasic.ofProp hA
  have hvd : HypIsoData n := HypIsoData.ofProp hI
  have hδlev : ∀ u : E n, lev ξ ((δ : PO n 1) • u) = lev ξ u := by
    intro u
    have hbus := hvd.busemann_cocycle (δ : PO n 1) ξ u hξS
    have h0 : busemann ξ ((δ : PO n 1) • (0 : E n)) = 0 := by
      simpa only [bCocy, hδfix] using hδbc
    rw [hδfix, h0, add_zero] at hbus
    rw [lev_eq_exp hξS u, lev_eq_exp hξS ((δ : PO n 1) • u), hbus]
  -- the Margulis constant, with `R = 1`
  obtain ⟨ε, hεpos, hεall⟩ := margulisCusp n hn hA hI 1
  set e : ℝ := min ε 1 with hedef
  have hepos : 0 < e := lt_min hεpos one_pos
  have hele : e ≤ ε := min_le_left _ _
  have hele1 : e ≤ 1 := min_le_right _ _
  have hv2 : 0 < ‖v‖ ^ 2 := by
    have : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    positivity
  -- the level at which both displacements are `< e`
  have hcoshe : 1 < Real.cosh e := Real.one_lt_cosh.mpr (ne_of_gt hepos)
  set D : ℝ := Real.sqrt (2 * (Real.cosh e - 1) / ‖v‖ ^ 2) * (1 / 2) with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    exact mul_pos (Real.sqrt_pos.mpr (div_pos (by linarith) hv2)) (by norm_num)
  have hDnn : 0 ≤ D := le_of_lt hDpos
  have hD2 : D ^ 2 * ‖v‖ ^ 2 / 2 = (Real.cosh e - 1) / 4 := by
    rw [hDdef, mul_pow, Real.sq_sqrt (le_of_lt (div_pos (by linarith) hv2))]
    field_simp
    ring
  have hbound : 1 + D ^ 2 * ‖v‖ ^ 2 / 2 < Real.cosh e := by
    rw [hD2]; linarith
  refine ⟨Real.log D, fun γ hγ => ?_⟩
  rintro ⟨u, hu1, hu2⟩
  have hle1 : lev ξ u < D := by
    rw [lev_eq_exp hξS u, ← Real.exp_log hDpos, Real.exp_lt_exp]; exact hu1
  have hle2 : lev ξ ((γ : PO n 1) • u) < D := by
    rw [lev_eq_exp hξS ((γ : PO n 1) • u), ← Real.exp_log hDpos, Real.exp_lt_exp]; exact hu2
  have h1 : hdist u ((δ : PO n 1) • u) < ε :=
    lt_of_lt_of_le (shimizu_flatTrans_lt_of_level hξS hδlev hyc hDnn hepos hbound hle1) hele
  -- the conjugate `σ = γ⁻¹ δ γ`
  set σ : Γ := ⟨(γ : PO n 1)⁻¹ * (δ : PO n 1) * (γ : PO n 1),
    mul_mem (mul_mem (inv_mem γ.2) δ.2) γ.2⟩ with hσdef
  have hσcoe : (σ : PO n 1) = (γ : PO n 1)⁻¹ * (δ : PO n 1) * (γ : PO n 1) := rfl
  have hγσ : (γ : PO n 1) • ((σ : PO n 1) • u) = (δ : PO n 1) • ((γ : PO n 1) • u) := by
    rw [← hpb.mul_smul, hσcoe]
    have h1' : ((γ : PO n 1) * ((γ : PO n 1)⁻¹ * (δ : PO n 1) * (γ : PO n 1)))
        = (δ : PO n 1) * (γ : PO n 1) := by group
    rw [h1', hpb.mul_smul]
  have h2 : hdist u ((σ : PO n 1) • u) ≤ 1 := by
    have hA1 : hdist u ((σ : PO n 1) • u)
        = hdist ((γ : PO n 1) • u) ((γ : PO n 1) • ((σ : PO n 1) • u)) :=
      (hvd.isom_smul (γ : PO n 1) u ((σ : PO n 1) • u)).symm
    rw [hA1, hγσ]
    exact le_trans (le_of_lt (shimizu_flatTrans_lt_of_level hξS hδlev hyc hDnn hepos hbound hle2))
      hele1
  -- the Margulis lemma
  have hbdσ : bd (σ : PO n 1) ξ = ξ :=
    hεall Γ hΓ.1 u ξ δ σ hδpar hξS hδfix h1 h2
  have hηS : bd (γ : PO n 1)⁻¹ ξ ∈ Sph n := hpb.bd_mem _ _ hξS
  have hσpar : IsParabolic (σ : PO n 1) := by
    have h := isParabolic_conj hA hI (γ : PO n 1)⁻¹ (δ : PO n 1) hδpar
    simpa [hσcoe, inv_inv] using h
  have hη1 : bd (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) = ξ := by
    rw [← hpb.bd_mul (γ : PO n 1) ((γ : PO n 1)⁻¹) ξ hξS, mul_inv_cancel, hpb.bd_one ξ hξS]
  have hfixσ' : bd (σ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) = bd (γ : PO n 1)⁻¹ ξ := by
    have hcoe : (σ : PO n 1) = (γ : PO n 1)⁻¹ * ((δ : PO n 1) * (γ : PO n 1)) := by
      rw [hσcoe]; group
    rw [hcoe, hpb.bd_mul ((γ : PO n 1)⁻¹) ((δ : PO n 1) * (γ : PO n 1))
        (bd (γ : PO n 1)⁻¹ ξ) hηS,
      hpb.bd_mul (δ : PO n 1) (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) hηS, hη1, hδfix]
  have heq : bd (γ : PO n 1)⁻¹ ξ = ξ :=
    paraUniqueFixed hpb hvd hσpar hξS hbdσ hηS hfixσ'
  refine hγ ?_
  have h3 : bd (γ : PO n 1) ξ = bd (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) := by rw [heq]
  rw [h3, hη1]

/-! ## The Shimizu exponent is positive -/

/-- Reassembly of the criterion in self-intersection form: the horoballs of `ξ` and of `bd γ ξ` of
a common level `t` intersect exactly when the Shimizu distortion of `γ` at `ξ` is below
`2 exp (2 t)`. -/
lemma horoInterSelf (hA : POActionProp n) (hI : HypIsometryProp n)
    (ξ : E n) (hξ : ξ ∈ Sph n) (γ : PO n 1) (hγ : bd γ ξ ≠ ξ) (t : ℝ) :
    ((∃ u : E n, busemann ξ u < t ∧ busemann ξ (γ • u) < t) ↔
      Real.exp (2 * t + bCocy γ ξ) > (1 - inner ℝ ξ (bd γ ξ)) / 2) := by
  have hpb := POBasic.ofProp hA
  have hvd := HypIsoData.ofProp hI
  have hη : bd γ ξ ∈ Sph n := hpb.bd_mem γ ξ hξ
  have hne : ξ ≠ bd γ ξ := fun h => hγ h.symm
  have hcrit := cuspHoroInterIff n hA hI ξ (bd γ ξ) hξ hη hne t (t + bCocy γ ξ)
  have hgoal1 : (∃ u : E n, busemann ξ u < t ∧ busemann ξ (γ • u) < t) ↔
      (∃ w : E n, busemann ξ w < t ∧ busemann (bd γ ξ) w < t + bCocy γ ξ) := by
    constructor
    · rintro ⟨u, hu1, hu2⟩
      refine ⟨γ • u, hu2, ?_⟩
      have h := hvd.busemann_cocycle γ ξ u hξ
      have hc : busemann (bd γ ξ) (γ • (0 : E n)) = bCocy γ ξ := rfl
      rw [hc] at h
      linarith
    · rintro ⟨w, hw1, hw2⟩
      refine ⟨γ⁻¹ • w, ?_, ?_⟩
      · have h := hvd.busemann_cocycle γ⁻¹ (bd γ ξ) w hη
        have hb : bd (γ⁻¹ * γ) ξ = ξ := by rw [inv_mul_cancel, hpb.bd_one ξ hξ]
        rw [hpb.bd_mul γ⁻¹ γ ξ hξ] at hb
        rw [hb] at h
        have h2 : busemann ξ (γ⁻¹ • (0 : E n)) = -bCocy γ ξ := by
          have h3 := hvd.busemann_cocycle γ ξ (γ⁻¹ • (0 : E n)) hξ
          have hγ0 : γ • (γ⁻¹ • (0 : E n)) = (0 : E n) := by
            rw [← hpb.mul_smul γ γ⁻¹, mul_inv_cancel, hpb.one_smul]
          rw [hγ0] at h3
          have hc2 : busemann (bd γ ξ) (γ • (0 : E n)) = bCocy γ ξ := rfl
          have h0 : busemann (bd γ ξ) (0 : E n) = 0 := by
            have ht : tpart (0 : E n) = 1 := by simp [tpart]
            rw [busemann, ht]
            simp
          rw [h0, hc2] at h3
          linarith
        rw [h2] at h
        linarith
      · rw [← hpb.mul_smul γ γ⁻¹ w, mul_inv_cancel, hpb.one_smul]
        exact hw1
  rw [hgoal1, hcrit]
  ring_nf

/-- Every element of the Shimizu set is bounded below by `2 exp (2 t)` as soon as the horoballs of
`ξ` and of its `γ`-images are disjoint at level `t`. -/
lemma cuspShimizuSet_ge (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (ξ : E n) (hξS : ξ ∈ Sph n) (t : ℝ)
    (ht : ∀ γ : Γ, bd (γ : PO n 1) ξ ≠ ξ →
      ¬ ∃ u : E n, busemann ξ u < t ∧ busemann ξ ((γ : PO n 1) • u) < t)
    (ν : Γ) (hν : bd (ν : PO n 1) ξ ≠ ξ) :
    2 * Real.exp (2 * t) ≤
      (1 - inner ℝ ξ (bd (ν : PO n 1) ξ)) * Real.exp (-(bCocy (ν : PO n 1) ξ)) := by
  have hcrit := horoInterSelf hA hI ξ hξS (ν : PO n 1) hν t
  have hnot : ¬ Real.exp (2 * t + bCocy (ν : PO n 1) ξ)
      > (1 - inner ℝ ξ (bd (ν : PO n 1) ξ)) / 2 :=
    fun hc => ht ν hν (hcrit.mpr hc)
  rw [gt_iff_lt, not_lt] at hnot
  have hpos : 0 < Real.exp (bCocy (ν : PO n 1) ξ) := Real.exp_pos _
  rw [Real.exp_add] at hnot
  have h2 := mul_le_mul_of_nonneg_right hnot
    (by positivity : (0 : ℝ) ≤ 2 * (Real.exp (bCocy (ν : PO n 1) ξ))⁻¹)
  have hL : (Real.exp (2 * t) * Real.exp (bCocy (ν : PO n 1) ξ))
      * (2 * (Real.exp (bCocy (ν : PO n 1) ξ))⁻¹) = 2 * Real.exp (2 * t) := by
    field_simp
  have hR : ((1 - inner ℝ ξ (bd (ν : PO n 1) ξ)) / 2)
      * (2 * (Real.exp (bCocy (ν : PO n 1) ξ))⁻¹)
      = (1 - inner ℝ ξ (bd (ν : PO n 1) ξ)) * Real.exp (-(bCocy (ν : PO n 1) ξ)) := by
    rw [Real.exp_neg]
    field_simp
  rwa [hL, hR] at h2

/-- **Positivity of the Shimizu exponent, from a flat translation in the cusp stabiliser.** -/
theorem cuspShimizuPositiveOfFlatTrans (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n)
    (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ)
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ → bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (ξ : E n) (hξ : ξ ∈ parFixed Γ)
    (hδ : ∃ δ : Γ, IsParabolic (δ : PO n 1) ∧ bd (δ : PO n 1) ξ = ξ ∧
      bCocy (δ : PO n 1) ξ = 0 ∧
      ∃ v : E n, v ≠ 0 ∧ inner ℝ v ξ = 0 ∧
        ∀ u : E n, yc ξ ((δ : PO n 1) • u) = yc ξ u + v) :
    0 < cuspShimizu Γ ξ := by
  by_cases h : ∃ ν : Γ, bd (ν : PO n 1) ξ ≠ ξ
  · rw [cuspShimizu_eq_sInf Γ ξ h]
    obtain ⟨t, ht⟩ := cuspPreciseInvariantOfFlatTrans n hn hA hI Γ hΓ ξ hξ hδ
    obtain ⟨ν₀, hν₀⟩ := h
    refine lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 * Real.exp (2 * t)) (le_csInf ?_ ?_)
    · exact ⟨_, mem_cuspShimizuSet Γ ξ ν₀ hν₀⟩
    · rintro r ⟨ν, hν, rfl⟩
      exact cuspShimizuSet_ge hA hI Γ ξ hξ.1 t ht ν hν
  · rw [cuspShimizu_eq_one Γ ξ h]
    norm_num

/-- **Positivity of the Shimizu exponent of a cusp of a lattice.** -/
theorem cuspShimizuPositive (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n) (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ) (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ → Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ → Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0) (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) : 0 < Work.Mostow.cuspShimizu Γ ξ :=
  cuspShimizuPositiveOfFlatTrans n hn hA hI Γ hΓ hvan ξ hξ
    (cuspParabolicFlatTrans n hn hA hI (fun m => bieberbach m) Γ hΓ hvan ξ hξ)


end

end Work.Mostow
