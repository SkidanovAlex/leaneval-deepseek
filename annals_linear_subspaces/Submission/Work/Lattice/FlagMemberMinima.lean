import Mathlib
import Submission.Work.Lattice.PhiPolygonCompare
import Submission.Work.Lattice.FamilySpanMinkowski
import Submission.Work.Lattice.QuotientMinima
import Submission.Work.Lattice.LatticeDataEndpoints
import Submission.Commons.Lattice.SuccessiveMinima.sublattice_ge
import Submission.Commons.Lattice.SuccessiveMinima.positive

/-!
# The flag-member successive-minima bound (P3 input)

For the §3 assembly (Prop 5 of de Saxcé) one needs, for a **flag member** `V ≤ Λ` of the
Harder–Narasimhan filtration (a *tight* saturated subgroup, `φ_A(V) = phiPolygon Λ A (dim V)`)
the bound

    `λᵢ(V) ≤ C · λ_{dim V}(Λ)`   for `1 ≤ i ≤ dim V`,

i.e. "all successive minima of the sublattice `V` are bounded by `λ_{dim V}(Λ)`" — the paper's
sentence "the successive minima of the sublattice `a_t s_x V_{j_s}(ℤ)` are all bounded by
`λ_{j_s}(a_t s_x ℤᵈ)`".

Route (no Prop-4 induction needed):
* Minkowski-2-upper on `V` (a `ℤ`-basis family of `V`): `∏_{k ≤ j} λ_k(V) · v_j ≤ 2^{2j} covol V`,
  and `log covol V = phiPolygon Λ A j − A·j(d−j)` by tightness;
* Prop 4(2) in the slacked form (`PhiPolygonCompare.abs_log_successiveMinimum_sub_dslope_phi_le`)
  for `Λ`: `log λ_k(Λ) ≥ (phiPolygon Λ A k − phiPolygon Λ A (k−1)) − K'`, telescoping to
  `Σ_{k ≤ j} log λ_k(Λ) ≥ phiPolygon Λ A j − jK'`;
* the sublattice inequality `λ_k(Λ) ≤ λ_k(V)` (`Commons...sublattice_ge`) converts the product
  comparison into the *per-index* comparison by dividing by the complementary factors.

All declarations are Mathlib + Submission (PhiPolygonCompare, FamilySpanMinkowski) + Commons.
-/

noncomputable section
open Set Module Real
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Submission.FlagMemberMinima

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.JoinSubmodularity
open Submission.Polygon
open Submission.LatticePolygon
open Submission.PhiSlack
open Submission.PhiPolygon
open Submission.IntrinsicIndex
open Submission.FamilySpanMinkowski
open Submission.UniformBddBelow
open Submission.PhiPolygonCompare
open Submission.QuotientMinima
open Submission.Prop42Upper
open Commons.Lattice.SuccessiveMinima

/-- **The slacked polygon vanishes at `0`.** -/
lemma phiPolygon_zero {d : ℕ} (Λ : Submodule ℤ (E d)) (A : ℝ) :
    phiPolygon Λ A 0 = 0 := by
  have hg : phiData Λ A 0 = 0 := by
    simp only [phiData, rankData_zero]
    ring
  have h := largestConvexMinorant_zero_left (Module.finrank ℤ Λ) (phiData Λ A) hg
  dsimp only [phiPolygon]
  exact h

/-- **The flag-member successive-minima bound.**  For a full-rank lattice `Λ ≤ ℝᵈ`, `A ≥ 0`,
and a nonzero tight subgroup `V ≤ Λ` (`phi A V = phiPolygon Λ A (subDim V)`), every
successive minimum of `V` with `1 ≤ i ≤ subDim V` is bounded by

`C · λ_{subDim V}(Λ)`, `C = (2^{2d} / v_{subDim V}) · exp(d·(Kconst d + 2·A·d²))`. -/
theorem successiveMinimum_le_of_tight_subgroup {d : ℕ} (Λ V : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ}
    (hA : 0 ≤ A) (hVΛ : V ≤ Λ) (hV0 : V ≠ ⊥)
    (hVtight : phi A V = phiPolygon Λ A (subDim V)) {i : ℕ} (hi1 : 1 ≤ i)
    (hij : i ≤ subDim V) :
    successiveMinimum (E := E d) V i ≤
      ((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
        Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2)) *
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
  -- positivity and monotonicity data
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
  -- Step 3: log covol V
  have hlogV : Real.log (latticeCovol V) = phiPolygon Λ A (subDim V) -
      A * ((subDim V : ℝ) * ((d : ℝ) - (subDim V : ℝ))) := by
    have h := hVtight
    simp only [phi] at h
    linarith
  have hlogVsum : Real.log (∏ t : Fin (subDim V), successiveMinimum (E := E d) V (t.val + 1)) =
      ∑ t : Fin (subDim V), Real.log (successiveMinimum (E := E d) V (t.val + 1)) :=
    Real.log_prod (s := Finset.univ)
      (f := fun t : Fin (subDim V) => successiveMinimum (E := E d) V (t.val + 1))
      (fun t _ => (hposV t).ne')
  -- Step 4: the Λ-side sum (Prop 4(2) slacked + telescoping)
  have hPsum : phiPolygon Λ A (subDim V) -
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
    have h0 : phiPolygon Λ A 0 = 0 := phiPolygon_zero Λ A
    rw [htel] at hsum
    linarith [hsum, h0]
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
          (d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2)) := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hjle : (subDim V : ℝ) ≤ (d : ℝ) := by exact_mod_cast hjd
    have hvpos : 0 < unitBallVol (subDim V) := unitBallVol_pos hj0
    have h2 : (∑ t : Fin (subDim V), Real.log (successiveMinimum (E := E d) V (t.val + 1))) ≤
        2 * (subDim V : ℝ) * Real.log 2 + phiPolygon Λ A (subDim V) -
          A * ((subDim V : ℝ) * ((d : ℝ) - (subDim V : ℝ))) -
          Real.log (unitBallVol (subDim V)) := by
      rw [hlogVsum] at hlogM
      linarith [hlogV]
    have h3 : (∑ t ∈ Finset.univ.erase ii,
          Real.log (successiveMinimum (E := E d) Λ (t.val + 1))) ≥
        phiPolygon Λ A (subDim V) -
          (subDim V : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) -
          Real.log (successiveMinimum (E := E d) Λ i) := by
      linarith [hPsum, hsplitL]
    have h4 := le_trans h3 herase
    have hAj : 0 ≤ A * ((subDim V : ℝ) * ((d : ℝ) - (subDim V : ℝ))) := by
      refine mul_nonneg hA (mul_nonneg (Nat.cast_nonneg _) ?_)
      linarith
    have hKj : (subDim V : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) ≤
        (d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hjle hK.le
    have h2j : 2 * (subDim V : ℝ) * Real.log 2 ≤ 2 * (d : ℝ) * Real.log 2 := by
      nlinarith [hjle, hlog2]
    linarith [hsplitV, h2, h4, hKj, hAj, h2j]
  -- Step 6: exponentiate and use monotonicity of the minima in the index
  have hCnonneg : 0 ≤ (2 : ℝ) ^ (2 * d) / unitBallVol (subDim V) *
      Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2)) :=
    mul_nonneg (div_nonneg (by positivity) (unitBallVol_pos hj0).le) (Real.exp_pos _).le
  have hmono : successiveMinimum (E := E d) Λ i ≤ successiveMinimum (E := E d) Λ (subDim V) :=
    successiveMinimum_mono Λ (i := i) (j := subDim V) hij (by rw [hΛfin]; exact hjd)
  have hstep1 : successiveMinimum (E := E d) V i ≤
      ((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
        Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2)) *
        successiveMinimum (E := E d) Λ i := by
    have hexp := Real.exp_le_exp.mpr hkey
    rw [Real.exp_add, Real.exp_add, Real.exp_sub, Real.exp_log hposVi,
      Real.exp_log hposLi, Real.exp_log (unitBallVol_pos hj0)] at hexp
    have h1 : Real.exp (2 * (d : ℝ) * Real.log 2) = (2 : ℝ) ^ (2 * d) := by
      rw [show 2 * (d : ℝ) * Real.log 2 = ((2 * d : ℕ) : ℝ) * Real.log 2 by push_cast; ring]
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [h1] at hexp
    calc successiveMinimum (E := E d) V i
        ≤ successiveMinimum (E := E d) Λ i *
            ((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V) *
              Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2))) := hexp
      _ = ((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
            Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2)) *
            successiveMinimum (E := E d) Λ i := by ring
  exact le_trans hstep1 (mul_le_mul_of_nonneg_left hmono hCnonneg)

end Submission.FlagMemberMinima
