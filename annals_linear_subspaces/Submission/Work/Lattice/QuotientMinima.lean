import Mathlib
import Submission.Work.Lattice.QuotientCovol
import Submission.Work.Lattice.QuotientShort
import Submission.Work.Lattice.FamilySpanMinkowski
import Submission.Work.Lattice.UniformBddBelow
import Submission.Commons.Lattice.SuccessiveMinima.Basic
import Submission.Commons.Analysis.Real.prod_le_div_pow_of_uniform_lower

/-!
# Successive minima of the projected quotient (P2 block layer, steps A4/A5)

For a nested pair `V ≤ W` of tight saturated subgroups of a full-rank lattice `Λ ≤ ℝᵈ`,
the projected quotient lattice `Q := W.map (projMap V) ⊆ (realSpan V)ᗮ` (whose covolume
factors as `latticeCovol W = latticeCovol V · latticeCovol Q`, `QuotientCovol`) has
successive minima controlled from both sides:

* **lower side** (`exp_le_successiveMinimum_map_projMap`): every nonzero vector of `Q` is
  `π w` with `w ∈ W`, `w ∉ realSpan V`, hence `‖π w‖ = ‖w − π_V w‖ ≥ e^{s − A d}` by the
  "no short vector" bound `QuotientShort.log_dist_ge_polygon_slope`, `s` the (block) slope
  of the `φ_A`-polygon.  Successive minima inherit the bound;
* **upper side** (`prod_successiveMinimum_le`): Minkowski's second theorem on the `ℤ`-basis
  family of `Q` gives `∏ μᵢ(Q) · v_b ≤ 2^{2b} covol Q`;
* **consequence** (`successiveMinimum_le_exp`): combining both (and the explicit value of
  `covol Q` through the polygon slopes) gives `μᵢ(Q) ≤ C · e^s` with a constant `C`
  depending only on `d`, `A`.

This is the per-block `log μᵢ = slope + O(1)` statement consumed by Prop 4(1) of the paper.
-/

noncomputable section
open Set Module Real
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

namespace Submission.QuotientMinima

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.JoinSubmodularity
open Submission.AlignedBases
open Submission.IntrinsicIndex
open Submission.PhiSlack
open Submission.PhiPolygon
open Submission.QuotientCovol
open Submission.LatticePolygon
open Submission.QuotientShort
open Submission.FamilySpanMinkowski
open Submission.UniformBddBelow
open Commons.Lattice.SuccessiveMinima

/-! ## 1. Nonemptiness of the successive-minimum set from an `ℝ`-independent family -/

/-- **Nonemptiness of the defining set of `λᵢ`** from an `ℝ`-independent family of `i ≤ N`
members of `L`: the first `i` members of the family are `ℤ`-linearly independent and of
bounded norm. -/
lemma successiveMinimumSet_nonempty_of_linearIndependent_real {d N : ℕ}
    (L : Submodule ℤ (E d)) (Y : Fin N → E d) (hYmem : ∀ j, Y j ∈ L)
    (hli : LinearIndependent ℝ Y) {i : ℕ} (hi : i ≤ N) :
    (successiveMinimumSet L i).Nonempty := by
  classical
  set R : ℝ := ∑ j : Fin N, ‖Y j‖ with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hbnd : ∀ j : Fin N, ‖Y j‖ ≤ R := fun j =>
    Finset.single_le_sum (fun k _ => norm_nonneg _) (Finset.mem_univ j)
  refine successiveMinimumSet_nonempty_of_exists_linearIndependent L i
    (fun k : Fin i => (⟨Y ⟨k.val, lt_of_lt_of_le k.isLt hi⟩, hYmem _⟩ : L)) ?_ R ?_ hR0
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have h1 : (∑ k : Fin i, ((c k : ℤ) : ℝ) • Y ⟨k.val, lt_of_lt_of_le k.isLt hi⟩) = 0 := by
      simpa only [Int.cast_smul_eq_zsmul ℝ] using hc
    have hemb : Function.Injective
        (fun k : Fin i => (⟨k.val, lt_of_lt_of_le k.isLt hi⟩ : Fin N)) := by
      intro k l hkl
      exact Fin.ext (by simpa using congrArg Fin.val hkl)
    have hli' := hli.comp (fun k : Fin i => (⟨k.val, lt_of_lt_of_le k.isLt hi⟩ : Fin N)) hemb
    have h2 := (Fintype.linearIndependent_iff.mp hli') (fun k => ((c k : ℤ) : ℝ)) h1
    intro k
    exact_mod_cast h2 k
  · intro k
    exact hbnd _

/-! ## 2. The lower bound: `e^{s−Ad} ≤ μᵢ(Q)` -/

/-- **No short vector in the projected quotient, successive-minimum form.**  For a
full-rank `Λ`, `A > 0`, and a tight saturated `V ≤ Λ`, the successive minima of
`Q := W.map (projMap V)` (`V ≤ W ≤ Λ`, `W` saturated, `subDim V < subDim W`) are bounded
below by `e^{s − A·d}`, where `s` is the polygon slope of the first step
`phiPolygon Λ A (j+1) − phiPolygon Λ A j` (`j = subDim V`). -/
theorem exp_le_successiveMinimum_map_projMap {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hVΛ : V ≤ Λ) (hWΛ : W ≤ Λ) (hVW : V ≤ W) (hV0 : V ≠ ⊥) (hW0 : W ≠ ⊥)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) {A : ℝ} (hA : 0 < A)
    (hVtight : phi A V = phiPolygon Λ A (subDim V))
    (hrank : subDim V < subDim W)
    {s : ℝ} (hs : phiPolygon Λ A (subDim V + 1) - phiPolygon Λ A (subDim V) = s)
    {i : ℕ} (hi1 : 1 ≤ i) (hib : i ≤ subDim W - subDim V) :
    Real.exp (s - A * (d : ℝ)) ≤ successiveMinimum (E := E d) (W.map (projMap V)) i := by
  classical
  obtain ⟨m, _a, b, u, _x, y, huN, _huxV, huyW, _huxyS, hliRu, _hliRux, hliRuy, _hliRuxy⟩ :=
    exists_aligned_ambient_of_saturated_pair Λ V W hΛfin hVΛ hWΛ hV0 hW0 hVsat hWsat
  have hinf : V ⊓ W = V := inf_eq_left.mpr hVW
  have huV : Submodule.span ℤ (Set.range u) = V := by rw [huN, hinf]
  have hsubV : subDim V = m := by
    rw [← huV]
    exact subDim_span_range_of_linearIndependent u hliRu
  have hsubW : subDim W = m + b := by
    rw [← huyW]
    exact subDim_span_range_of_linearIndependent _ hliRuy
  have hrealV : realSpan V = Submodule.span ℝ (Set.range u) := by
    rw [← huV]
    exact realSpan_span_range u
  set Y : Fin b → E d := fun j => (realSpan V)ᗮ.starProjection (y j) with hY
  have hQ : W.map (projMap V) = Submodule.span ℤ (Set.range Y) :=
    map_projMap_eq_span_starProjection V W u y huV huyW
  have hYli : LinearIndependent ℝ Y := by
    have h := linearIndependent_starProjection u y hliRuy
    simpa only [hY, hrealV] using h
  have hYmem : ∀ j, Y j ∈ W.map (projMap V) := by
    intro j
    rw [hQ]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hnonempty : (successiveMinimumSet (W.map (projMap V)) i).Nonempty :=
    successiveMinimumSet_nonempty_of_linearIndependent_real (W.map (projMap V)) Y hYmem hYli
      (by omega)
  refine successiveMinimum_ge_of_forall_ne_zero_norm_ge (W.map (projMap V))
    (Real.exp (s - A * (d : ℝ))) hi1 hnonempty ?_
  intro q hq
  obtain ⟨w, hwW, hwq⟩ := Submodule.mem_map.mp q.2
  have hqne : (q : E d) ≠ 0 := fun h => hq (Subtype.ext h)
  have hwnot : w ∉ realSpan V := by
    intro hw
    apply hqne
    rw [← hwq, projMap_apply]
    exact starProjection_orthogonal_eq_zero (U := realSpan V) hw
  have hqw : (q : E d) = w - (realSpan V).starProjection w := by
    rw [← hwq, projMap_apply]
    have h := DFunLike.congr_fun (Submodule.starProjection_orthogonal (realSpan V)) w
    rw [sub_apply, ContinuousLinearMap.id_apply] at h
    exact h
  have hlog := log_dist_ge_polygon_slope Λ hΛfin hA V hVsat hV0 hVtight (hWΛ hwW) hwnot
  have hlog' : s - A * (d : ℝ) ≤ Real.log ‖(q : E d)‖ := by
    rw [hqw]
    linarith [hs, hlog]
  rw [← Real.le_log_iff_exp_le (norm_pos_iff.mpr hqne)]
  exact hlog'

/-! ## 3. Covolume of `Q` and the Minkowski product bound -/

/-- **Covolume of the projected quotient as the quotient of covolumes.** -/
theorem latticeCovol_map_projMap_eq_div {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hVΛ : V ≤ Λ) (hWΛ : W ≤ Λ) (hVW : V ≤ W) (hV0 : V ≠ ⊥) (hW0 : W ≠ ⊥)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) (hrank : subDim V < subDim W) :
    latticeCovol (W.map (projMap V)) = latticeCovol W / latticeCovol V := by
  have h := latticeCovol_eq_mul_map_projMap Λ V W hΛfin hVΛ hWΛ hVW hV0 hW0 hVsat hWsat hrank
  have hpos : latticeCovol V ≠ 0 := (latticeCovol_pos Λ V hVΛ hV0).ne'
  rw [h, mul_div_cancel_left₀ _ hpos]

/-- **Minkowski's second theorem on the projected quotient.**  For a nested saturated pair
`V ≤ W` with `subDim V < subDim W`, the product of the successive minima of
`Q := W.map (projMap V)` satisfies `∏ᵢ μᵢ(Q) · v_b ≤ 2^{2b}·covol Q`, `b = subDim W − subDim V`. -/
theorem prod_successiveMinimum_mul_unitBallVol_le {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hVΛ : V ≤ Λ) (hWΛ : W ≤ Λ) (hVW : V ≤ W) (hV0 : V ≠ ⊥) (hW0 : W ≠ ⊥)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) (hrank : subDim V < subDim W) :
    (∏ i : Fin (subDim W - subDim V),
        successiveMinimum (E := E d) (W.map (projMap V)) (i.val + 1)) *
        unitBallVol (subDim W - subDim V) ≤
      (2 : ℝ) ^ (2 * (subDim W - subDim V)) * latticeCovol (W.map (projMap V)) := by
  classical
  obtain ⟨m, _a, b, u, _x, y, huN, _huxV, huyW, _huxyS, hliRu, _hliRux, hliRuy, _hliRuxy⟩ :=
    exists_aligned_ambient_of_saturated_pair Λ V W hΛfin hVΛ hWΛ hV0 hW0 hVsat hWsat
  have hinf : V ⊓ W = V := inf_eq_left.mpr hVW
  have huV : Submodule.span ℤ (Set.range u) = V := by rw [huN, hinf]
  have hsubV : subDim V = m := by
    rw [← huV]
    exact subDim_span_range_of_linearIndependent u hliRu
  have hsubW : subDim W = m + b := by
    rw [← huyW]
    exact subDim_span_range_of_linearIndependent _ hliRuy
  have hrealV : realSpan V = Submodule.span ℝ (Set.range u) := by
    rw [← huV]
    exact realSpan_span_range u
  set Y : Fin b → E d := fun j => (realSpan V)ᗮ.starProjection (y j) with hY
  have hQ : W.map (projMap V) = Submodule.span ℤ (Set.range Y) :=
    map_projMap_eq_span_starProjection V W u y huV huyW
  have hYli : LinearIndependent ℝ Y := by
    have h := linearIndependent_starProjection u y hliRuy
    simpa only [hY, hrealV] using h
  have hb : 0 < b := by omega
  have hbEq : subDim W - subDim V = b := by omega
  rw [hbEq]
  have hM := minkowski_second_upper_familySpan (d := d) (r := b) hb Y hYli
  have hfinV : Module.finrank ℝ (FamilySpanMinkowski.Vf Y) = b :=
    FamilySpanMinkowski.finrank_Vf Y hYli
  have hvol : ENNReal.toReal (MeasureTheory.volume (Metric.closedBall
      (0 : FamilySpanMinkowski.Vf Y) 1)) = unitBallVol b := by
    dsimp [unitBallVol]
    exact Commons.Analysis.InnerProductSpace.unitBall_volume_eq_dim
      (E := FamilySpanMinkowski.Vf Y) hfinV
  rw [hvol] at hM
  rw [← hQ] at hM
  exact hM

/-! ## 4. The upper bound: `μᵢ(Q) ≤ C·e^s` -/

/-- **Per-index upper bound for the projected quotient minima.**  For a nested pair of tight
saturated subgroups `V ≤ W` with `subDim V < subDim W`, with the `φ_A`-polygon affine with
slope `s` on `[subDim V, subDim W]`, every successive minimum of `Q := W.map (projMap V)` is
at most `C·e^s`, `C = (2^{2b}/v_b)·e^{A d² + A d b}` (`b := subDim W − subDim V`). -/
theorem successiveMinimum_le_exp {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hVΛ : V ≤ Λ) (hWΛ : W ≤ Λ) (hVW : V ≤ W) (hV0 : V ≠ ⊥) (hW0 : W ≠ ⊥)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) {A : ℝ} (hA : 0 < A)
    (hVtight : phi A V = phiPolygon Λ A (subDim V))
    (hWtight : phi A W = phiPolygon Λ A (subDim W))
    (hrank : subDim V < subDim W) {s : ℝ}
    (hsaff : ∀ k, subDim V ≤ k → k ≤ subDim W →
      phiPolygon Λ A k = phiPolygon Λ A (subDim V) + ((k : ℝ) - (subDim V : ℝ)) * s)
    (i : Fin (subDim W - subDim V)) :
    successiveMinimum (E := E d) (W.map (projMap V)) (i.val + 1) ≤
      (2 : ℝ) ^ (2 * (subDim W - subDim V)) / unitBallVol (subDim W - subDim V) *
        Real.exp (A * (d : ℝ) ^ 2 + A * (d : ℝ) * ((subDim W : ℝ) - (subDim V : ℝ))) *
        Real.exp s := by
  classical
  obtain ⟨m, _a, b, u, _x, y, huN, _huxV, huyW, _huxyS, hliRu, _hliRux, hliRuy, _hliRuxy⟩ :=
    exists_aligned_ambient_of_saturated_pair Λ V W hΛfin hVΛ hWΛ hV0 hW0 hVsat hWsat
  have hinf : V ⊓ W = V := inf_eq_left.mpr hVW
  have huV : Submodule.span ℤ (Set.range u) = V := by rw [huN, hinf]
  have hsubV : subDim V = m := by
    rw [← huV]
    exact subDim_span_range_of_linearIndependent u hliRu
  have hsubW : subDim W = m + b := by
    rw [← huyW]
    exact subDim_span_range_of_linearIndependent _ hliRuy
  have hb : 0 < b := by omega
  have hbEq : subDim W - subDim V = b := by omega
  have hbcast : ((b : ℕ) : ℝ) = (subDim W : ℝ) - (subDim V : ℝ) := by
    rw [hsubV, hsubW]
    push_cast
    ring
  -- the single-step affine form
  have hstep : phiPolygon Λ A (subDim V + 1) - phiPolygon Λ A (subDim V) = s := by
    have h1 := hsaff (subDim V + 1) (by omega) (by omega)
    have h3 : ((subDim V + 1 : ℕ) : ℝ) - (subDim V : ℝ) = 1 := by push_cast; ring
    rw [h3, one_mul] at h1
    linarith [h1]
  -- lower bounds
  have hlow : ∀ k : Fin b,
      Real.exp (s - A * (d : ℝ)) ≤
        successiveMinimum (E := E d) (W.map (projMap V)) (k.val + 1) := by
    intro k
    have h := exp_le_successiveMinimum_map_projMap Λ V W hΛfin hVΛ hWΛ hVW hV0 hW0 hVsat hWsat
      hA hVtight hrank hstep (i := k.val + 1) (by omega) (by rw [hbEq]; omega)
    simpa using h
  -- the product bound
  have hprod0 := prod_successiveMinimum_mul_unitBallVol_le Λ V W hΛfin hVΛ hWΛ hVW hV0 hW0
    hVsat hWsat hrank
  rw [hbEq] at hprod0
  have hvpos : 0 < unitBallVol b := unitBallVol_pos hb
  have hprod : (∏ k : Fin b, successiveMinimum (E := E d) (W.map (projMap V)) (k.val + 1)) ≤
      (2 : ℝ) ^ (2 * b) * latticeCovol (W.map (projMap V)) / unitBallVol b := by
    rw [le_div_iff₀ hvpos]
    exact hprod0
  -- positivity of the quotient covolume
  have hcovVpos : 0 < latticeCovol V := latticeCovol_pos Λ V hVΛ hV0
  have hcovWpos : 0 < latticeCovol W := latticeCovol_pos Λ W hWΛ hW0
  have hcovQpos : 0 < latticeCovol (W.map (projMap V)) := by
    have h := latticeCovol_eq_mul_map_projMap Λ V W hΛfin hVΛ hWΛ hVW hV0 hW0 hVsat hWsat hrank
    nlinarith [h, hcovVpos, hcovWpos]
  -- the covolume upper bound through the polygon slopes
  have hlogQ : Real.log (latticeCovol (W.map (projMap V))) ≤ (b : ℝ) * s + A * (d : ℝ) ^ 2 := by
    have hdiv := latticeCovol_map_projMap_eq_div Λ V W hΛfin hVΛ hWΛ hVW hV0 hW0 hVsat hWsat hrank
    rw [hdiv, Real.log_div hcovWpos.ne' hcovVpos.ne']
    have htV : Real.log (latticeCovol V) = phiPolygon Λ A (subDim V) -
        A * ((subDim V : ℝ) * ((d : ℝ) - (subDim V : ℝ))) := by
      have h := hVtight
      simp only [phi] at h
      linarith
    have htW : Real.log (latticeCovol W) = phiPolygon Λ A (subDim W) -
        A * ((subDim W : ℝ) * ((d : ℝ) - (subDim W : ℝ))) := by
      have h := hWtight
      simp only [phi] at h
      linarith
    have haff := hsaff (subDim W) (by omega) le_rfl
    have hqV0 : (0 : ℝ) ≤ (subDim V : ℝ) := Nat.cast_nonneg _
    have hqVd : (subDim V : ℝ) ≤ (d : ℝ) := by exact_mod_cast subDim_le_ambient V
    have hqW0 : (0 : ℝ) ≤ (subDim W : ℝ) := Nat.cast_nonneg _
    have hqWd : (subDim W : ℝ) ≤ (d : ℝ) := by exact_mod_cast subDim_le_ambient W
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    have hquadV : (subDim V : ℝ) * ((d : ℝ) - (subDim V : ℝ)) ≤ (d : ℝ) ^ 2 := by
      nlinarith [hqV0, hqVd, hd0]
    have hquadW : (0 : ℝ) ≤ (subDim W : ℝ) * ((d : ℝ) - (subDim W : ℝ)) := by
      nlinarith [hqW0, hqWd]
    have hA0 : 0 ≤ A := le_of_lt hA
    have hquad : A * ((subDim V : ℝ) * ((d : ℝ) - (subDim V : ℝ))) -
        A * ((subDim W : ℝ) * ((d : ℝ) - (subDim W : ℝ))) ≤ A * (d : ℝ) ^ 2 := by
      have h1 : A * ((subDim V : ℝ) * ((d : ℝ) - (subDim V : ℝ))) ≤ A * (d : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hquadV hA0
      have h2 : 0 ≤ A * ((subDim W : ℝ) * ((d : ℝ) - (subDim W : ℝ))) :=
        mul_nonneg hA0 hquadW
      linarith
    have hlogsplit : Real.log (latticeCovol W) - Real.log (latticeCovol V) =
        (phiPolygon Λ A (subDim W) - phiPolygon Λ A (subDim V)) -
          (A * ((subDim W : ℝ) * ((d : ℝ) - (subDim W : ℝ))) -
            A * ((subDim V : ℝ) * ((d : ℝ) - (subDim V : ℝ)))) := by
      rw [htW, htV]
      ring
    have hΦ : phiPolygon Λ A (subDim W) - phiPolygon Λ A (subDim V) = (b : ℝ) * s := by
      rw [haff, hbcast]
      ring
    rw [hlogsplit, hΦ]
    linarith [hquad]
  have hcovle : latticeCovol (W.map (projMap V)) ≤
      Real.exp ((b : ℝ) * s + A * (d : ℝ) ^ 2) := by
    have h := Real.exp_le_exp.mpr hlogQ
    rwa [Real.exp_log hcovQpos] at h
  -- the numerical combination
  have hmpos : 0 < Real.exp (s - A * (d : ℝ)) := Real.exp_pos _
  have hb1 : 1 ≤ b := hb
  have hcastpred : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := Nat.cast_pred hb1
  have hA0 : 0 ≤ A := le_of_lt hA
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  -- the covolume bound in the form needed for the final division
  have hkey2 : latticeCovol (W.map (projMap V)) ≤
      (Real.exp (A * (d : ℝ) ^ 2 + A * (d : ℝ) * (b : ℝ)) * Real.exp s) *
        (Real.exp (s - A * (d : ℝ))) ^ (b - 1) := by
    refine le_trans hcovle ?_
    have hexp : Real.exp ((b : ℝ) * s + A * (d : ℝ) ^ 2) ≤
        Real.exp ((A * (d : ℝ) ^ 2 + A * (d : ℝ) * (b : ℝ)) +
          (s + ((b - 1 : ℕ) : ℝ) * (s - A * (d : ℝ)))) := by
      refine Real.exp_le_exp.mpr ?_
      rw [hcastpred]
      nlinarith [mul_nonneg hA0 hd0]
    refine le_trans hexp (le_of_eq ?_)
    have h1 : Real.exp ((A * (d : ℝ) ^ 2 + A * (d : ℝ) * (b : ℝ)) +
            (s + ((b - 1 : ℕ) : ℝ) * (s - A * (d : ℝ)))) =
        Real.exp (A * (d : ℝ) ^ 2 + A * (d : ℝ) * (b : ℝ)) *
          Real.exp (s + ((b - 1 : ℕ) : ℝ) * (s - A * (d : ℝ))) :=
      Real.exp_add _ _
    have h2 : Real.exp (s + ((b - 1 : ℕ) : ℝ) * (s - A * (d : ℝ))) =
        Real.exp s * (Real.exp (s - A * (d : ℝ))) ^ (b - 1) := by
      rw [Real.exp_add, Real.exp_nat_mul]
    calc Real.exp ((A * (d : ℝ) ^ 2 + A * (d : ℝ) * (b : ℝ)) +
            (s + ((b - 1 : ℕ) : ℝ) * (s - A * (d : ℝ))))
        = Real.exp (A * (d : ℝ) ^ 2 + A * (d : ℝ) * (b : ℝ)) *
            Real.exp (s + ((b - 1 : ℕ) : ℝ) * (s - A * (d : ℝ))) := h1
      _ = Real.exp (A * (d : ℝ) ^ 2 + A * (d : ℝ) * (b : ℝ)) *
            (Real.exp s * (Real.exp (s - A * (d : ℝ))) ^ (b - 1)) := by rw [h2]
      _ = (Real.exp (A * (d : ℝ) ^ 2 + A * (d : ℝ) * (b : ℝ)) * Real.exp s) *
            (Real.exp (s - A * (d : ℝ))) ^ (b - 1) := by ring
  -- the per-index upper bound for the `b`-indexed family
  have hkey : ∀ k : Fin b,
      successiveMinimum (E := E d) (W.map (projMap V)) (k.val + 1) ≤
        (2 : ℝ) ^ (2 * b) / unitBallVol b *
          Real.exp (A * (d : ℝ) ^ 2 + A * (d : ℝ) * (b : ℝ)) * Real.exp s := by
    intro k
    have hlowk := Commons.Analysis.Real.prod_le_div_pow_of_uniform_lower
      (x := fun j : Fin b => successiveMinimum (E := E d) (W.map (projMap V)) (j.val + 1))
      hmpos hlow hprod k
    refine le_trans hlowk ?_
    rw [div_div]
    rw [div_le_iff₀ (mul_pos hvpos (pow_pos hmpos _))]
    have hgoal_eq : (2 : ℝ) ^ (2 * b) / unitBallVol b *
          Real.exp (A * (d : ℝ) ^ 2 + A * (d : ℝ) * (b : ℝ)) * Real.exp s *
          (unitBallVol b * (Real.exp (s - A * (d : ℝ))) ^ (b - 1)) =
        (2 : ℝ) ^ (2 * b) *
          ((Real.exp (A * (d : ℝ) ^ 2 + A * (d : ℝ) * (b : ℝ)) * Real.exp s) *
            (Real.exp (s - A * (d : ℝ))) ^ (b - 1)) := by
      field_simp
      try ring
    rw [hgoal_eq]
    exact mul_le_mul_of_nonneg_left hkey2 (pow_nonneg (by norm_num) _)
  -- transfer back to the ambient index type
  have hkey' := hkey (Fin.cast hbEq i)
  rw [Fin.val_cast] at hkey'
  have hconst : (2 : ℝ) ^ (2 * b) / unitBallVol b *
        Real.exp (A * (d : ℝ) ^ 2 + A * (d : ℝ) * (b : ℝ)) * Real.exp s =
      (2 : ℝ) ^ (2 * (subDim W - subDim V)) / unitBallVol (subDim W - subDim V) *
        Real.exp (A * (d : ℝ) ^ 2 + A * (d : ℝ) * ((subDim W : ℝ) - (subDim V : ℝ))) *
        Real.exp s := by
    rw [hbEq, ← hbcast]
  rwa [hconst] at hkey'

end Submission.QuotientMinima
