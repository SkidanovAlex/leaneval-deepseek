import Mathlib
import Submission.Work.Lattice.FlagMemberMinima
import Submission.Work.Lattice.MaxPhi
import Submission.Work.Lattice.MaxEuclidBridge
import Submission.Work.Lattice.MaxAttainment
import Submission.Work.Lattice.FlagAnnulus

/-!
# The flag-member successive-minima bound for **max-norm** tight members

`FlagMemberMinima.successiveMinimum_le_of_tight_subgroup` bounds the successive minima of a
flag member `V ≤ Λ` by `C·λ_{dim V}(Λ)`, assuming the member is tight for the *Euclidean*
`φ`-polygon.  The §3 flag produced by `MaxPhiFlag.exists_tight_flag` is however tight for the
**max-norm** data (`maxphiData`), so this module re-derives the bound in that setting.

The two data functions differ by at most the norm-comparability constant
`maxRankData Λ j ≤ rankData Λ j` (because `cnorm ≤ ‖·‖`), hence the max-norm slacked polygon is
below the Euclidean one (`maxphiPolygon_le_phiPolygon`), and the same chain as in
`FlagMemberMinima` goes through with an extra factor `exp(½log (choose d (subDim V)))` in the
constant — still a constant depending only on `d`.

Module `Submission.Work.Lattice.MaxFlagMinima`, namespace `Submission.MaxFlagMinima`.
-/

noncomputable section
open Set Module Real
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Submission.MaxFlagMinima

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.JoinSubmodularity
open Submission.Polygon
open Submission.LatticePolygon
open Submission.PhiSlack
open Submission.PhiPolygon
open Submission.PhiPolygonCompare
open Submission.Prop42Upper
open Submission.IntrinsicIndex
open Submission.FamilySpanMinkowski
open Submission.UniformBddBelow
open Submission.QuotientMinima
open Submission.MaxCovol
open Submission.MaxPhi
open Submission.MaxPhiPolygon
open Submission.MaxRankData
open Commons.Lattice.SuccessiveMinima
open Submission.MaxNorm
open Submission.MaxNormFlow

variable {d : ℕ}

/-- Reindexing a wedge along `Fin.cast` does not change its norm. -/
lemma norm_iMulti_cast {k : ℕ} {n : ℕ} (h : n = k) (v : Fin k → E d) :
    ‖exteriorPower.ιMulti ℝ n (fun i => v (Fin.cast h i))‖ =
      ‖exteriorPower.ιMulti ℝ k v‖ := by
  subst h
  rfl

/-- The rank-`0` Euclidean data of a lattice vanishes. -/
lemma rankData_zero (Λ : Submodule ℤ (E d)) : rankData (d := d) Λ 0 = 0 := by
  have hset : rankDataSet (d := d) Λ 0 = {0} := by
    rw [Set.eq_singleton_iff_unique_mem]
    refine ⟨⟨⊥, bot_le, (subDim_eq_zero_iff_bot (⊥ : Submodule ℤ (E d))).mpr rfl, logCovol_bot.symm⟩, ?_⟩
    rintro r ⟨W, -, hdim, rfl⟩
    have hW : W = ⊥ := (subDim_eq_zero_iff_bot W).mp hdim
    rw [hW]
    exact logCovol_bot
  rw [rankData, hset, csInf_singleton]

/-- **The max-norm data is at most the Euclidean data.** -/
lemma maxRankData_le_rankData (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛfin : Module.finrank ℤ Λ = d) {j : ℕ} (hjd : j ≤ d)
    (hBdd : BddBelow (maxRankDataSet (d := d) Λ j hjd)) :
    maxRankData (d := d) Λ j hjd ≤ rankData (d := d) Λ j := by
  classical
  by_cases hj : j = 0
  · subst hj
    rw [maxRankData_zero, rankData_zero]
  have hj1 : 1 ≤ j := by omega
  refine le_csInf ?hne ?_
  · -- the rank data set is nonempty (transport any presentation family)
    obtain ⟨r, ⟨v, hvmem, hvli, rfl⟩⟩ :=
      Submission.MaxEuclidBridge.maxRankDataSet_nonempty (d := d) (Λ := Λ) hΛfin hj1 hjd
    refine ⟨Real.log (latticeCovol (Submodule.span ℤ (Set.range v))),
      Submodule.span ℤ (Set.range v), Submodule.span_le.mpr (Set.range_subset_iff.mpr hvmem),
      subDim_span_range_of_linearIndependent v hvli, rfl⟩
  · rintro r ⟨W, hWΛ, hdim, rfl⟩
    have hW0 : W ≠ ⊥ := by
      intro hbot
      have h0 : subDim (⊥ : Submodule ℤ (E d)) = 0 :=
        (subDim_eq_zero_iff_bot (⊥ : Submodule ℤ (E d))).mpr rfl
      rw [hbot] at hdim
      omega
    have hr : 0 < subDim W := Nat.pos_of_ne_zero fun h => hW0 ((subDim_eq_zero_iff_bot W).mp h)
    obtain ⟨cW, hcWli, _hzli, hcWmem, hcWspan⟩ :=
      exists_basis_family_int_of_le_lattice Λ hΛfin W hWΛ hW0
    have hcov : latticeCovol W = ‖exteriorPower.ιMulti ℝ (subDim W) cW‖ := by
      rw [show latticeCovol W = latticeCovol (Submodule.span ℤ (Set.range cW)) from
        congrArg _ hcWspan,
        latticeCovol_span (d := d) (r := subDim W) hr cW hcWli]
    rw [hcov]
    -- the comparison through the presentation family, reindexed to `Fin j`
    have hli' : LinearIndependent ℝ (fun i : Fin j => cW (Fin.cast hdim.symm i)) :=
      hcWli.comp (Fin.cast hdim.symm) (Fin.cast_injective hdim.symm)
    have hpos : 0 < cnorm (d := d) hjd (exteriorPower.ιMulti ℝ j
        (fun i : Fin j => cW (Fin.cast hdim.symm i))) :=
      cnorm_pos_of_ne_zero (d := d) hjd _
        (Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent _ hli')
    have hcnorm : cnorm (d := d) hjd (exteriorPower.ιMulti ℝ j
        (fun i : Fin j => cW (Fin.cast hdim.symm i))) =
        cnorm (d := d) (subDim_le_ambient W) (exteriorPower.ιMulti ℝ (subDim W) cW) :=
      Submission.MaxAttainment.cnorm_iMulti_reindex (d := d) hdim.symm cW hjd (subDim_le_ambient W)
    refine le_trans (csInf_le hBdd ⟨fun i : Fin j => cW (Fin.cast hdim.symm i),
      fun i => hcWmem _, hli', rfl⟩) ?_
    rw [hcnorm]
    exact Real.log_le_log (cnorm_pos_of_ne_zero (d := d) (subDim_le_ambient W) _
        (Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent _ hcWli))
      (cnorm_le_norm (d := d) (subDim_le_ambient W) _)

/-! ## The slacked polygons and the successive-minima bound -/

/-- The slacked max-norm data is at most the slacked Euclidean data. -/
lemma maxphiData_le_phiData (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛfin : Module.finrank ℤ Λ = d) (A : ℝ)
    (hBdd : ∀ (j : ℕ) (hjd : j ≤ d), BddBelow (maxRankDataSet (d := d) Λ j hjd))
    {i : ℕ} (hi : i ≤ d) :
    maxphiData (d := d) Λ A i ≤ phiData (d := d) Λ A i := by
  rw [maxphiData, dif_pos hi, phiData]
  have h := maxRankData_le_rankData (d := d) Λ hΛfin hi (hBdd i hi)
  linarith

/-- The slacked max-norm polygon is at most the slacked Euclidean polygon. -/
lemma maxphiPolygon_le_phiPolygon (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (A : ℝ)
    (hBdd : ∀ (j : ℕ) (hjd : j ≤ d), BddBelow (maxRankDataSet (d := d) Λ j hjd))
    {i : ℕ} (hi : i ≤ Module.finrank ℤ Λ) :
    maxphiPolygon (d := d) Λ A i ≤ phiPolygon (d := d) Λ A i := by
  have h := largestConvexMinorant_mono (d := Module.finrank ℤ Λ) (maxphiData (d := d) Λ A)
    (phiData (d := d) Λ A)
    (fun j hj => maxphiData_le_phiData (d := d) Λ hΛfin A hBdd (by rwa [hΛfin] at hj)) hi
  simpa only [maxphiPolygon, phiPolygon] using h

/-- **The flag-member successive-minima bound for max-norm tight members.**  For a full-rank
lattice `Λ ≤ ℝᵈ`, `A ≥ 0` and a nonzero subgroup `V ≤ Λ` which is tight for the *max-norm*
slacked polygon (`maxPhi A V = maxphiPolygon Λ A (subDim V)`), every successive minimum of `V`
with `1 ≤ i ≤ subDim V` is bounded by

`((2^{2d}/v_j) · exp(d(Kconst d + 2A d²) + ½log (choose d j))) · λ_j(Λ)`,

`j = subDim V` — the Euclidean bound of `FlagMemberMinima` with the norm-comparability factor
`exp(½log (choose d j))` absorbed. -/
theorem successiveMinimum_le_of_maxTight_subgroup (Λ V : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ}
    (hA : 0 ≤ A) (hVΛ : V ≤ Λ) (hV0 : V ≠ ⊥)
    (hVtight : maxPhi (d := d) Λ hΛfin A V hVΛ = maxphiPolygon (d := d) Λ A (subDim V))
    (hBdd : ∀ (j : ℕ) (hjd : j ≤ d), BddBelow (maxRankDataSet (d := d) Λ j hjd))
    {i : ℕ} (hi1 : 1 ≤ i) (hij : i ≤ subDim V) :
    successiveMinimum (E := E d) V i ≤
      ((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
        Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
          (1 / 2) * Real.log (Nat.choose d (subDim V))) *
        successiveMinimum (E := E d) Λ (subDim V) := by
  classical
  obtain ⟨cV, hliR, _hzli, _hmemΛ, hVspan⟩ :=
    exists_basis_family_int_of_le_lattice Λ hΛfin V hVΛ hV0
  have hj0 : 0 < subDim V := Nat.pos_of_ne_zero fun h => hV0 ((subDim_eq_zero_iff_bot V).mp h)
  have hjd : subDim V ≤ d := subDim_le_ambient V
  have hd0 : 0 < d := lt_of_lt_of_le hj0 hjd
  have hK : 0 < Kconst d + 2 * A * (d : ℝ) ^ 2 := by
    have h1 : 0 < Kconst d := Prop42Upper.Kconst_pos d
    have h2 : 0 ≤ 2 * A * (d : ℝ) ^ 2 := by positivity
    linarith
  have hneV : (successiveMinimumSet V i).Nonempty := by
    refine successiveMinimumSet_nonempty_of_linearIndependent_real V cV ?_ hliR hij
    intro t
    rw [hVspan]
    exact Submodule.subset_span ⟨t, rfl⟩
  have hge : successiveMinimum (E := E d) Λ i ≤ successiveMinimum (E := E d) V i :=
    sublattice_ge V Λ hVΛ i hneV
  have hneVk : ∀ t : Fin (subDim V), (successiveMinimumSet V (t.val + 1)).Nonempty := by
    intro t
    refine successiveMinimumSet_nonempty_of_linearIndependent_real V cV ?_ hliR (by omega)
    intro s
    rw [hVspan]
    exact Submodule.subset_span ⟨s, rfl⟩
  have hposV : ∀ t : Fin (subDim V), 0 < successiveMinimum (E := E d) V (t.val + 1) := by
    intro t
    have hle := sublattice_ge V Λ hVΛ (t.val + 1) (hneVk t)
    exact lt_of_lt_of_le (positive Λ (t.val + 1) (by omega) (by rw [hΛfin]; omega)) hle
  have hposL : ∀ t : Fin (subDim V), 0 < successiveMinimum (E := E d) Λ (t.val + 1) := by
    intro t
    exact positive Λ (t.val + 1) (by omega) (by rw [hΛfin]; omega)
  have hposLi : 0 < successiveMinimum (E := E d) Λ i := positive Λ i (by omega) (by rw [hΛfin]; omega)
  have hposVi : 0 < successiveMinimum (E := E d) V i := lt_of_lt_of_le hposLi hge
  -- Step 1: Minkowski-2-upper on V
  have hM := minkowski_second_upper_familySpan (d := d) (r := subDim V) hj0 cV hliR
  have hvol : ENNReal.toReal (MeasureTheory.volume (Metric.closedBall (0 : Vf cV) 1)) =
      unitBallVol (subDim V) := by
    dsimp [unitBallVol]
    exact Commons.Analysis.InnerProductSpace.unitBall_volume_eq_dim (E := Vf cV)
      (finrank_Vf cV hliR)
  have hlamEq : ∀ t : Fin (subDim V),
      successiveMinimum (E := E d) (Submodule.span ℤ (Set.range cV)) (t.val + 1) =
      successiveMinimum (E := E d) V (t.val + 1) := by
    intro t
    rw [← hVspan]
  have hcovEq : latticeCovol (Submodule.span ℤ (Set.range cV)) = latticeCovol V := by
    rw [← hVspan]
  rw [hvol, hcovEq] at hM
  rw [show (∏ t : Fin (subDim V), successiveMinimum (E := E d) (Submodule.span ℤ (Set.range cV))
        (t.val + 1)) =
      (∏ t : Fin (subDim V), successiveMinimum (E := E d) V (t.val + 1)) from
    Finset.prod_congr rfl fun t _ => hlamEq t] at hM
  -- Step 2: log form
  have hPRpos : 0 < ∏ t : Fin (subDim V), successiveMinimum (E := E d) V (t.val + 1) :=
    Finset.prod_pos fun t _ => hposV t
  have hcovVpos : 0 < latticeCovol V := latticeCovol_pos Λ V hVΛ hV0
  have hlogM : Real.log (∏ t : Fin (subDim V), successiveMinimum (E := E d) V (t.val + 1)) +
      Real.log (unitBallVol (subDim V)) ≤
      2 * (subDim V : ℝ) * Real.log 2 + Real.log (latticeCovol V) := by
    have h := Real.log_le_log (mul_pos hPRpos (unitBallVol_pos hj0)) hM
    rw [Real.log_mul hPRpos.ne' (unitBallVol_pos hj0).ne',
      Real.log_mul (by positivity) hcovVpos.ne', Real.log_pow] at h
    have h2 : ((2 * subDim V : ℕ) : ℝ) * Real.log 2 = 2 * (subDim V : ℝ) * Real.log 2 := by
      push_cast
      ring
    linarith [h, h2]
  -- Step 3: the log-covolume of V, from max-norm tightness plus the comparability constant
  have hlogV : Real.log (latticeCovol V) ≤ maxphiPolygon Λ A (subDim V) -
      A * ((subDim V : ℝ) * ((d : ℝ) - (subDim V : ℝ))) +
        (1 / 2) * Real.log (Nat.choose d (subDim V)) := by
    have h1 := log_latticeCovol_le_maxCovol_add (d := d) (Λ := Λ) (hΛfin := hΛfin) (X := V)
      (hXΛ := hVΛ)
    have h2 : maxCovol (d := d) Λ hΛfin V hVΛ = maxphiPolygon Λ A (subDim V) -
        A * ((subDim V : ℝ) * ((d : ℝ) - (subDim V : ℝ))) := by
      have h := hVtight
      simp only [maxPhi] at h
      linarith
    linarith
  have hlogVsum : Real.log (∏ t : Fin (subDim V), successiveMinimum (E := E d) V (t.val + 1)) =
      ∑ t : Fin (subDim V), Real.log (successiveMinimum (E := E d) V (t.val + 1)) :=
    Real.log_prod (s := Finset.univ)
      (f := fun t : Fin (subDim V) => successiveMinimum (E := E d) V (t.val + 1))
      (fun t _ => (hposV t).ne')
  -- Step 4: the Λ-side sum (Prop 4(2) slacked + telescoping), with the polygon comparison
  have hPsumPhi : phiPolygon Λ A (subDim V) -
      (subDim V : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) ≤
      ∑ t : Fin (subDim V), Real.log (successiveMinimum (E := E d) Λ (t.val + 1)) := by
    have hterm : ∀ t : Fin (subDim V),
        phiPolygon Λ A (t.val + 1) - phiPolygon Λ A t.val -
            (Kconst d + 2 * A * (d : ℝ) ^ 2) ≤
          Real.log (successiveMinimum (E := E d) Λ (t.val + 1)) := by
      intro t
      have hb := abs_log_successiveMinimum_sub_dslope_phi_le hd0 Λ hΛfin hA (i := t.val + 1)
        (by omega) (by omega)
      have hds : dslope (phiPolygon Λ A) t.val =
          phiPolygon Λ A (t.val + 1) - phiPolygon Λ A t.val := rfl
      have hsub : t.val + 1 - 1 = t.val := by omega
      rw [hsub] at hb
      rw [hds] at hb
      have := (abs_le.mp hb).1
      linarith
    have hsum := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hterm t)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsum
    have htel : (∑ t : Fin (subDim V),
        (phiPolygon Λ A (t.val + 1) - phiPolygon Λ A t.val)) =
        phiPolygon Λ A (subDim V) - phiPolygon Λ A 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun n : ℕ =>
        phiPolygon Λ A (n + 1) - phiPolygon Λ A n) (subDim V)]
      exact Finset.sum_range_sub (fun n : ℕ => phiPolygon Λ A n) (subDim V)
    have h0 : phiPolygon Λ A 0 = 0 := Submission.FlagMemberMinima.phiPolygon_zero Λ A
    rw [htel] at hsum
    linarith [hsum, h0]
  have hPsum : maxphiPolygon Λ A (subDim V) -
      (subDim V : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) ≤
      ∑ t : Fin (subDim V), Real.log (successiveMinimum (E := E d) Λ (t.val + 1)) := by
    have hle := maxphiPolygon_le_phiPolygon Λ hΛfin A hBdd
      (by show subDim V ≤ Module.finrank ℤ Λ; rw [hΛfin]; exact hjd)
    exact le_trans (sub_le_sub_right hle _) hPsumPhi
  -- Step 5: the per-index combination
  have hsign : ∀ t : Fin (subDim V), Real.log (successiveMinimum (E := E d) Λ (t.val + 1)) ≤
      Real.log (successiveMinimum (E := E d) V (t.val + 1)) := by
    intro t
    exact Real.log_le_log (hposL t)
      (sublattice_ge V Λ hVΛ (t.val + 1) (hneVk t))
  set ii : Fin (subDim V) := ⟨i - 1, by omega⟩ with hiidef
  have hiival : ii.val + 1 = i := by simp only [ii]; omega
  have hsplitV : (∑ t : Fin (subDim V), Real.log (successiveMinimum (E := E d) V (t.val + 1))) -
      (∑ t ∈ Finset.univ.erase ii, Real.log (successiveMinimum (E := E d) V (t.val + 1))) =
      Real.log (successiveMinimum (E := E d) V i) := by
    have h := Finset.add_sum_erase Finset.univ
      (fun t : Fin (subDim V) => Real.log (successiveMinimum (E := E d) V (t.val + 1)))
      (Finset.mem_univ ii)
    rw [hiival] at h
    linarith
  have hsplitL : (∑ t : Fin (subDim V), Real.log (successiveMinimum (E := E d) Λ (t.val + 1))) -
      (∑ t ∈ Finset.univ.erase ii, Real.log (successiveMinimum (E := E d) Λ (t.val + 1))) =
      Real.log (successiveMinimum (E := E d) Λ i) := by
    have h := Finset.add_sum_erase Finset.univ
      (fun t : Fin (subDim V) => Real.log (successiveMinimum (E := E d) Λ (t.val + 1)))
      (Finset.mem_univ ii)
    rw [hiival] at h
    linarith
  have herase : (∑ t ∈ Finset.univ.erase ii,
        Real.log (successiveMinimum (E := E d) Λ (t.val + 1))) ≤
      (∑ t ∈ Finset.univ.erase ii,
        Real.log (successiveMinimum (E := E d) V (t.val + 1))) :=
    Finset.sum_le_sum fun t _ => hsign t
  have hkey : Real.log (successiveMinimum (E := E d) V i) ≤
      Real.log (successiveMinimum (E := E d) Λ i) +
        (2 * (d : ℝ) * Real.log 2 - Real.log (unitBallVol (subDim V)) +
          (d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
            (1 / 2) * Real.log (Nat.choose d (subDim V))) := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hjle : (subDim V : ℝ) ≤ (d : ℝ) := by exact_mod_cast hjd
    have hvpos : 0 < unitBallVol (subDim V) := unitBallVol_pos hj0
    have h2 : (∑ t : Fin (subDim V), Real.log (successiveMinimum (E := E d) V (t.val + 1))) ≤
        2 * (subDim V : ℝ) * Real.log 2 + maxphiPolygon Λ A (subDim V) -
          A * ((subDim V : ℝ) * ((d : ℝ) - (subDim V : ℝ))) +
            (1 / 2) * Real.log (Nat.choose d (subDim V)) -
          Real.log (unitBallVol (subDim V)) := by
      rw [hlogVsum] at hlogM
      linarith [hlogV]
    have h3 : (∑ t ∈ Finset.univ.erase ii,
          Real.log (successiveMinimum (E := E d) Λ (t.val + 1))) ≥
        maxphiPolygon Λ A (subDim V) -
          (subDim V : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) -
          Real.log (successiveMinimum (E := E d) Λ i) := by
      linarith [hPsum, hsplitL]
    have h4 := le_trans h3 herase
    have hAj : 0 ≤ A * ((subDim V : ℝ) * ((d : ℝ) - (subDim V : ℝ))) := by
      refine mul_nonneg hA (mul_nonneg (Nat.cast_nonneg _) ?_)
      linarith
    have hKj : (subDim V : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) ≤
        (d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hjle hK.le
    have h2j : 2 * (subDim V : ℝ) * Real.log 2 ≤ 2 * (d : ℝ) * Real.log 2 := by
      nlinarith [hjle, hlog2]
    linarith [hsplitV, h2, h4, hKj, hAj, h2j]
  -- Step 6: exponentiate and use monotonicity of the minima in the index
  have hCnonneg : 0 ≤ (2 : ℝ) ^ (2 * d) / unitBallVol (subDim V) *
      Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
        (1 / 2) * Real.log (Nat.choose d (subDim V))) :=
    mul_nonneg (div_nonneg (by positivity) (unitBallVol_pos hj0).le) (Real.exp_pos _).le
  have hmono : successiveMinimum (E := E d) Λ i ≤ successiveMinimum (E := E d) Λ (subDim V) :=
    successiveMinimum_mono Λ (i := i) (j := subDim V) hij (by rw [hΛfin]; exact hjd)
  have hCpos : 0 < ((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
      Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
        (1 / 2) * Real.log (Nat.choose d (subDim V))) :=
    mul_pos (div_pos (by positivity) (unitBallVol_pos hj0)) (Real.exp_pos _)
  have hlogC : Real.log (((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
      Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
        (1 / 2) * Real.log (Nat.choose d (subDim V)))) =
      (2 * (d : ℝ) * Real.log 2 - Real.log (unitBallVol (subDim V)) +
        (d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
          (1 / 2) * Real.log (Nat.choose d (subDim V))) := by
    have h2d : 0 < (2 : ℝ) ^ (2 * d) := by positivity
    have hvol : 0 < unitBallVol (subDim V) := unitBallVol_pos hj0
    rw [Real.log_mul (ne_of_gt (div_pos h2d hvol)) (Real.exp_pos _).ne',
      Real.log_div (ne_of_gt h2d) (ne_of_gt hvol), Real.log_pow, Real.log_exp]
    push_cast
    ring
  have hstep1 : successiveMinimum (E := E d) V i ≤
      (((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
        Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
          (1 / 2) * Real.log (Nat.choose d (subDim V)))) *
        successiveMinimum (E := E d) Λ i := by
    have hlog : Real.log (successiveMinimum (E := E d) V i) ≤
        Real.log (((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
          Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
            (1 / 2) * Real.log (Nat.choose d (subDim V)))) +
        Real.log (successiveMinimum (E := E d) Λ i) := by
      rw [hlogC]
      linarith [hkey]
    calc successiveMinimum (E := E d) V i
        = Real.exp (Real.log (successiveMinimum (E := E d) V i)) := (Real.exp_log hposVi).symm
      _ ≤ Real.exp (Real.log (((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
            Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
              (1 / 2) * Real.log (Nat.choose d (subDim V)))) +
          Real.log (successiveMinimum (E := E d) Λ i)) := Real.exp_le_exp.mpr hlog
      _ = (((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
            Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
              (1 / 2) * Real.log (Nat.choose d (subDim V)))) *
          successiveMinimum (E := E d) Λ i := by
        rw [Real.exp_add, Real.exp_log hCpos, Real.exp_log hposLi]
  exact le_trans hstep1 (mul_le_mul_of_nonneg_left hmono hCnonneg)


/-! ## Lattice points near prescribed directions in a max-norm tight member -/

/-- The annulus constant of a max-norm tight flag member: the covering constant `C·λ_j(Λ)` of
`FlagAnnulus`, with the norm-comparability factor `exp(½log (choose d j))` absorbed. -/
noncomputable def blockConstMax (d : ℕ) (A : ℝ) (Λ V : Submodule ℤ (E d)) : ℝ :=
  ((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
    Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
      (1 / 2) * Real.log (Nat.choose d (subDim V))) *
    successiveMinimum (E := E d) Λ (subDim V)

/-- **Lattice points near prescribed directions in a max-norm tight member.**  The analogue of
`FlagAnnulus.exists_flagMember_near_direction` for members that are tight for the *max-norm*
slacked polygon: the annulus constant is `blockConstMax d A Λ V` (still a constant times
`λ_{subDim V}(Λ)`). -/
theorem exists_memberPoint_near_direction (Λ V : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ} (hA : 0 ≤ A) (hVΛ : V ≤ Λ)
    (hV0 : V ≠ ⊥)
    (hVtight : maxPhi (d := d) Λ hΛfin A V hVΛ = maxphiPolygon (d := d) Λ A (subDim V))
    (hBdd : ∀ (j : ℕ) (hjd : j ≤ d), BddBelow (maxRankDataSet (d := d) Λ j hjd))
    {u : E d} (hu : u ∈ realSpan V) (hu1 : ‖u‖ = 1) {M : ℝ} (hM : 0 ≤ M) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ v : E d, v ∈ V ∧
      ‖v - M • u‖ ≤ (subDim V : ℝ) * (blockConstMax d A Λ V + ε) ∧
      ‖v‖ ≤ M + (subDim V : ℝ) * (blockConstMax d A Λ V + ε) ∧
      M - (subDim V : ℝ) * (blockConstMax d A Λ V + ε) ≤ ‖v‖ := by
  classical
  obtain ⟨cV, hliR, _hzli, _hmemΛ, hVspan⟩ :=
    exists_basis_family_int_of_le_lattice Λ hΛfin V hVΛ hV0
  have hj0 : 0 < subDim V := Nat.pos_of_ne_zero fun h => hV0 ((subDim_eq_zero_iff_bot V).mp h)
  have hjd : subDim V ≤ d := subDim_le_ambient V
  let L : Submodule ℤ (Vf cV) := familySpanLattice cV hliR
  haveI : DiscreteTopology L := by dsimp [L]; infer_instance
  haveI : IsZLattice ℝ L := by dsimp [L]; infer_instance
  have hLfin : Module.finrank ℤ L = subDim V := by
    dsimp [L]
    exact finrank_familySpanLattice hj0 cV hliR
  have hRealV : realSpan V = Vf cV := by
    have h1 := congrArg (fun W : Submodule ℤ (E d) => realSpan W) hVspan
    rw [realSpan_spanFamily cV] at h1
    exact h1
  have huVf : u ∈ Vf cV := by rw [← hRealV]; exact hu
  let u' : Vf cV := ⟨u, huVf⟩
  have hu'1 : ‖u'‖ = 1 := by simpa [u'] using hu1
  obtain ⟨v', hv1, hv2, hv3⟩ :=
    exists_latticePoint_near_direction L (subDim V) hLfin u' hε hM hu'1
  set w : E d := (((v' : L) : Vf cV) : E d) with hw
  have hwmem : w ∈ V := by
    rw [hVspan]
    rw [hw]
    exact (familySpanLattice_carrier cV hliR ((v' : L) : Vf cV)).mp (v' : L).2
  have hwnorm : ‖w‖ = ‖(v' : L)‖ := by
    rw [hw]
    rfl
  have hwdiff : ‖w - M • u‖ = ‖(v' : L) - M • u'‖ := by
    rw [hw]
    have hMu : (((M : ℝ) • u' : Vf cV) : E d) = M • u := by
      simp [u']
    rw [← hMu]
    rfl
  have heq : successiveMinimum (E := Vf cV) L (subDim V) =
      successiveMinimum (E := E d) V (subDim V) := by
    dsimp only [L]
    rw [← successiveMinimum_familySpanLattice_eq cV hliR (i := subDim V)]
    exact congrArg (fun W : Submodule ℤ (E d) =>
      successiveMinimum (E := E d) W (subDim V)) hVspan.symm
  have hflag := successiveMinimum_le_of_maxTight_subgroup Λ V hΛfin hA hVΛ hV0 hVtight hBdd
    (i := subDim V) (by omega) le_rfl
  have hmono : successiveMinimum (E := E d) V (subDim V) ≤
      ((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
        Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
          (1 / 2) * Real.log (Nat.choose d (subDim V))) *
        successiveMinimum (E := E d) Λ (subDim V) := by
    simpa [mul_assoc] using hflag
  have hmul : (subDim V : ℝ) * (successiveMinimum (E := Vf cV) L (subDim V) + ε) ≤
      (subDim V : ℝ) * (blockConstMax d A Λ V + ε) := by
    have h1 : (subDim V : ℝ) * (successiveMinimum (E := Vf cV) L (subDim V) + ε) ≤
        (subDim V : ℝ) * (successiveMinimum (E := E d) V (subDim V) + ε) := by
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (subDim V))
      rw [heq]
    have h2 : (subDim V : ℝ) * (successiveMinimum (E := E d) V (subDim V) + ε) ≤
        (subDim V : ℝ) * (blockConstMax d A Λ V + ε) := by
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (subDim V))
      simp only [blockConstMax]
      linarith [hmono]
    exact le_trans h1 h2
  refine ⟨w, hwmem, ?_, ?_, ?_⟩
  · rw [hwdiff]
    exact le_trans hv1 hmul
  · rw [hwnorm]
    calc ‖(v' : L)‖ ≤ M + (subDim V : ℝ) * (successiveMinimum (E := Vf cV) L (subDim V) + ε) := hv2
      _ ≤ M + (subDim V : ℝ) * (blockConstMax d A Λ V + ε) := by linarith [hmul]
  · rw [hwnorm]
    calc M - (subDim V : ℝ) * (blockConstMax d A Λ V + ε)
        ≤ M - (subDim V : ℝ) * (successiveMinimum (E := Vf cV) L (subDim V) + ε) := by
          linarith [hmul]
      _ ≤ ‖(v' : L)‖ := hv3


end Submission.MaxFlagMinima

end
