import Mathlib
import Submission.Work.Drive.Mono.sweepData_exists_partial
import Submission.Work.Drive.Mono.junctionGenC_of_arcs
import Submission.Work.Drive.Mono.noGraze_witness_gamma_noEdge
import Submission.Work.Drive.Mono.ae_faceCrossReg_of_boxGen
import Submission.Work.Drive.Mono.NoBend
import Submission.Work.Drive.Mono.gammaArcs_exist
import Submission.Work.Drive.Mono.sweepGoodData_aux
import Submission.Work.Drive.Mono.tiltData_window_of_dir_export_axis
import Submission.Work.Drive.Mono.tiltData_window_of_dir_export_param
import Submission.Work.Drive.Mono.ae_faceNoBend
import Submission.Work.Drive.Mono.offK_null
import Submission.Work.Drive.Mono.no_eventOnFace_null
import Submission.Work.Drive.Mono.faceEvent_degen_null
import Submission.Work.Drive.Mono.Band.exists_adapted_basis
import Submission.Work.Drive.Final.GoodSweepData2

/-!
# The partial tilt data of a thin tilted sweep, with the junction bundle

`Work.Drive.Mono.sweepData_exists_partial` produces, at almost every cutting level, the analytic
package of a thin tilted sweep (the tilt data, the seven no-grazing clauses, `SlabCutsBox`, the
window, the face regularity) but **not** the junction bundle `Work.Drive.Mono.JunctionGenC`.

This module strengthens that statement with `Work.Drive.Mono.JunctionGenC` at the same datum.  The
proof repeats the construction of `Work.Drive.Mono.sweepData_exists_partial` — the perturbation of
the robust no-grazing witness to a tilt off the coordinate axes, the window of half-widths and the
exported band data — but replaces the no-grazing witness by the merged witness
`Work.Drive.Mono.noGraze_witness_gamma_noEdge`, which *additionally* controls the two genericity
conditions along the trace arcs of the box sphere, and it obtains the arcs of the box trace from
`Work.Drive.Mono.gammaArcs_exist`.  The junction bundle is then
`Work.Drive.Mono.junctionGenC_of_arcs`, with the exceptional set enlarged by the corner locus of the
box level (finitely many values, by the hypothesis `hcorner`).

The two extra pieces of bookkeeping that the arcs need are

* the half-width `h` is chosen in a window below `m/8`, where `m` is the radius of the arc family
  (`Work.Drive.Mono.gammaArcs_exist`), so that the closed slab of the surface lies in the arcs'
  domain (`|slab| ≤ h` forces the flat coordinate to satisfy `|flat| < m`) and inside the parameter
  range `|t| < η` of the arcs;
* the arcs' derivative is bounded on the compact subinterval `[-η/4, η/4]`, which lets the two arc
  conditions of the witness — stated at the *witness's* tilt — be transported to the perturbed tilt
  `v'` of the exported band data.
-/

open scoped ENNReal Topology RealInnerProductSpace

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set

noncomputable section

set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

/-! ## Helper lemmas for `Work.Drive.Mono.sweepData_exists_partial` -/

/-- **The slab height differs from the height in another direction by the inner product with the
difference of the directions.** -/
private lemma sweepData_slab_diff (v v' x c : R3) :
    inner ℝ v x - inner ℝ v c
      = (inner ℝ v' x - inner ℝ v' c) + inner ℝ (v - v') (x - c) := by
  rw [← inner_sub_right, ← inner_sub_right, ← inner_add_left]
  congr 1
  abel

/-- **The two slab heights differ by at most `εv * R` on a ball of radius `R`.** -/
private lemma sweepData_slab_le {v v' x c : R3} {εv R u : ℝ} (h : ‖v' - v‖ ≤ εv)
    (hx : ‖x - c‖ ≤ R) :
    |inner ℝ v x - (inner ℝ v c + u)| ≤ |inner ℝ v' x - (inner ℝ v' c + u)| + εv * R := by
  have hkey : inner ℝ v x - (inner ℝ v c + u)
      = (inner ℝ v' x - (inner ℝ v' c + u)) + inner ℝ (v - v') (x - c) := by
    have h1 : inner ℝ (v - v') (x - c) = inner ℝ v (x - c) - inner ℝ v' (x - c) :=
      inner_sub_left _ _ _
    have h2 : inner ℝ v (x - c) = inner ℝ v x - inner ℝ v c := inner_sub_right _ _ _
    have h3 : inner ℝ v' (x - c) = inner ℝ v' x - inner ℝ v' c := inner_sub_right _ _ _
    rw [h1, h2, h3]
    ring
  rw [hkey]
  refine le_trans (abs_add_le _ _) ?_
  have hεv0 : 0 ≤ εv := le_trans (norm_nonneg _) h
  refine add_le_add le_rfl ?_
  calc |inner ℝ (v - v') (x - c)| ≤ ‖v - v'‖ * ‖x - c‖ := abs_real_inner_le_norm _ _
    _ = ‖v' - v‖ * ‖x - c‖ := by rw [norm_sub_rev]
    _ ≤ εv * R := mul_le_mul h hx (norm_nonneg _) hεv0

/-- **A vector with two non-zero coordinates is parallel to no coordinate axis.** -/
private theorem sweepData_ne_smul_single {v : R3} {j j' : Fin 3} (hjj : j ≠ j')
    (hj : v j ≠ 0) (hj' : v j' ≠ 0) :
    ∀ i : Fin 3, ∀ a : ℝ, EuclideanSpace.single i (1 : ℝ) ≠ a • v := by
  intro i a hcon
  have hsingle : ∀ m : Fin 3, (EuclideanSpace.single i (1 : ℝ)) m = if m = i then 1 else 0 := by
    intro m; rw [PiLp.single_apply]
  have hai : a * v i = 1 := by
    have h2 := congrArg (fun x : R3 => x i) hcon.symm
    rw [hsingle i, if_pos rfl] at h2
    simpa [PiLp.smul_apply, smul_eq_mul] using h2
  have ha0 : a ≠ 0 := fun h0 => by rw [h0, zero_mul] at hai; norm_num at hai
  have hzero : ∀ m : Fin 3, m ≠ i → v m = 0 := by
    intro m hm
    have h2 := congrArg (fun x : R3 => x m) hcon.symm
    rw [hsingle m, if_neg hm] at h2
    have h3 : a * v m = 0 := by simpa [PiLp.smul_apply, smul_eq_mul] using h2.symm
    exact (mul_eq_zero.mp h3).resolve_left ha0
  rcases eq_or_ne j i with hji | hji
  · exact hj' (hzero j' (fun hc => hjj (by rw [hji, hc])))
  · exact hj (hzero j hji)

/-- **A vector with two non-zero coordinates is not the standard axis vector `e_{σ 2}`.** -/
private theorem sweepData_ne_shiftVσ {v : R3} {σ : Equiv.Perm (Fin 3)} {j j' : Fin 3}
    (hjj : j ≠ j') (hj : v j ≠ 0) (hj' : v j' ≠ 0) : v ≠ Work.BoxShrink.shiftVσ σ 1 := by
  intro hcon
  have hsingle : ∀ m : Fin 3, (Work.BoxShrink.shiftVσ σ 1) m = if m = σ 2 then 1 else 0 := by
    intro m; rw [Work.BoxShrink.shiftVσ_apply]
  have hzero : ∀ m : Fin 3, m ≠ σ 2 → v m = 0 := by
    intro m hm
    have h2 := congrArg (fun x : R3 => x m) hcon
    rw [hsingle m, if_neg hm] at h2
    exact h2
  rcases eq_or_ne j (σ 2) with h1 | h1
  · exact hj' (hzero j' (fun hc => hjj (by rw [h1, hc])))
  · exact hj (hzero j h1)

/-- **A unit vector can be perturbed by at most `ε` to a unit vector off the coordinate axes.** -/
private theorem sweepData_axis_perturb {σ : Equiv.Perm (Fin 3)} {v : R3} (hv : ‖v‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v' : R3, ‖v'‖ = 1 ∧ ‖v' - v‖ ≤ ε ∧
      (∀ i : Fin 3, ∀ a : ℝ, EuclideanSpace.single (σ i) (1 : ℝ) ≠ a • v') ∧
      v' ≠ Work.BoxShrink.shiftVσ σ 1 := by
  classical
  have hsum : ∑ i : Fin 3, (v i) ^ 2 = 1 := by
    have h1 := Work.Drive.Mono.inner_eq_sum v v
    rw [real_inner_self_eq_norm_sq, hv] at h1
    have h2 : ∑ j : Fin 3, v j * v j = ∑ j : Fin 3, (v j) ^ 2 :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [h2] at h1
    simpa using h1.symm
  obtain ⟨m, hm⟩ : ∃ m : Fin 3, v m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : (∑ i : Fin 3, (v i) ^ 2) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hcon i]; ring
    rw [hsum] at h0
    norm_num at h0
  set m' : Fin 3 := if m = 0 then 1 else 0 with hm'def
  have hm'ne : m' ≠ m := by
    rw [hm'def]; split_ifs with h0
    · rw [h0]; decide
    · exact fun hc => h0 hc.symm
  set δ : ℝ := min ε 1 / 2 with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]; exact div_pos (lt_min hε zero_lt_one) (by norm_num)
  have hδle : 2 * δ ≤ ε := by
    rw [hδdef]; have := min_le_left ε 1; linarith
  set t : ℝ := if v m' + δ = 0 then δ / 2 else δ with htdef
  have ht0 : 0 < t := by rw [htdef]; split_ifs <;> linarith
  have htle : t ≤ δ := by rw [htdef]; split_ifs <;> linarith
  have hvt : v m' + t ≠ 0 := by
    rw [htdef]; split_ifs with h1
    · linarith [hδ0]
    · exact h1
  set w : R3 := v + t • EuclideanSpace.single m' (1 : ℝ) with hwdef
  have hwm : w m = v m := by
    rw [hwdef]; simp [hm'ne]
  have hwm' : w m' = v m' + t := by rw [hwdef]; simp
  have hwne : w ≠ 0 := by
    intro h0
    have h1 := congrArg (fun x : R3 => x m) h0
    rw [hwm] at h1
    exact hm h1
  have hwv : ‖w - v‖ ≤ δ := by
    have h1 : w - v = t • EuclideanSpace.single m' (1 : ℝ) := by rw [hwdef]; abel
    rw [h1, norm_smul, PiLp.norm_single 2]
    simp only [Real.norm_eq_abs, norm_one, mul_one]
    rw [abs_of_pos ht0]
    exact htle
  have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hw'm0 : ((‖w‖)⁻¹ • w) m ≠ 0 := by
    rw [PiLp.smul_apply, hwm]
    exact mul_ne_zero (inv_ne_zero (ne_of_gt hwnorm)) hm
  have hw'm1 : ((‖w‖)⁻¹ • w) m' ≠ 0 := by
    rw [PiLp.smul_apply, hwm']
    exact mul_ne_zero (inv_ne_zero (ne_of_gt hwnorm)) hvt
  refine ⟨(‖w‖)⁻¹ • w, ?_, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg w),
      inv_mul_cancel₀ (ne_of_gt hwnorm)]
  · have h1 : ‖(‖w‖)⁻¹ • w - w‖ = |1 - ‖w‖| := by
      have h0 : (‖w‖)⁻¹ • w - w = ((‖w‖)⁻¹ - 1) • w := by rw [sub_smul, one_smul]
      have hs : |((‖w‖)⁻¹ - 1) * ‖w‖| = |(‖w‖)⁻¹ - 1| * ‖w‖ := by
        rw [abs_mul, abs_of_nonneg (norm_nonneg w)]
      rw [h0, norm_smul, Real.norm_eq_abs, ← hs]
      congr 1
      rw [sub_mul, inv_mul_cancel₀ (ne_of_gt hwnorm), one_mul]
    have h2 : |1 - ‖w‖| ≤ ‖w - v‖ := by
      have h3 : |‖w‖ - ‖v‖| ≤ ‖w - v‖ := abs_norm_sub_norm_le w v
      rw [hv] at h3
      rwa [abs_sub_comm] at h3
    have h4 : ‖(‖w‖)⁻¹ • w - v‖ ≤ ‖(‖w‖)⁻¹ • w - w‖ + ‖w - v‖ := by
      have h5 : (‖w‖)⁻¹ • w - v = ((‖w‖)⁻¹ • w - w) + (w - v) := by abel
      rw [h5]; exact norm_add_le _ _
    rw [h1] at h4
    linarith [h4, h2, hwv, hδle]
  · intro i a
    exact sweepData_ne_smul_single (j := m') (j' := m) hm'ne hw'm1 hw'm0 (σ i) a
  · exact sweepData_ne_shiftVσ (j := m') (j' := m) hm'ne hw'm1 hw'm0

/-- **A unit vector orthogonal to `v` can be pushed into `(v')^⊥`, staying close to itself.** -/
private theorem sweepData_orth_near {v v' n : R3} (hv' : ‖v'‖ = 1) (hn : ‖n‖ = 1)
    (hvn : inner ℝ v n = 0) {ε : ℝ} (hv'v : ‖v' - v‖ ≤ ε) (hε : ε ≤ 1 / 4) :
    ∃ n' : R3, ‖n'‖ = 1 ∧ inner ℝ v' n' = 0 ∧ ‖n' - n‖ ≤ 2 * ε := by
  set n'' : R3 := n - (inner ℝ v' n) • v' with hn''def
  have horth : inner ℝ v' n'' = 0 := by
    rw [hn''def, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv']
    ring
  have hclose : ‖n'' - n‖ ≤ ε := by
    have h1 : n'' - n = -((inner ℝ v' n) • v') := by rw [hn''def]; abel
    rw [h1, norm_neg, norm_smul, hv', mul_one, Real.norm_eq_abs]
    have h2 : inner ℝ v' n = inner ℝ (v' - v) n := by rw [inner_sub_left, hvn, sub_zero]
    rw [h2]
    calc |inner ℝ (v' - v) n| ≤ ‖v' - v‖ * ‖n‖ := abs_real_inner_le_norm _ _
      _ = ‖v' - v‖ := by rw [hn, mul_one]
      _ ≤ ε := hv'v
  have hpos : 0 < ‖n''‖ := by
    have h3 : ‖n - n''‖ = ‖n'' - n‖ := norm_sub_rev _ _
    have h4 : ‖n‖ - ‖n''‖ ≤ ‖n - n''‖ := (abs_le.mp (abs_norm_sub_norm_le n n'')).2
    rw [hn, h3] at h4
    linarith [h4, hclose, hε]
  refine ⟨(‖n''‖)⁻¹ • n'', ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg n''),
      inv_mul_cancel₀ (ne_of_gt hpos)]
  · rw [real_inner_smul_right, horth, mul_zero]
  · have h1 : ‖(‖n''‖)⁻¹ • n'' - n''‖ = |1 - ‖n''‖| := by
      have h0 : (‖n''‖)⁻¹ • n'' - n'' = ((‖n''‖)⁻¹ - 1) • n'' := by rw [sub_smul, one_smul]
      have hs : |((‖n''‖)⁻¹ - 1) * ‖n''‖| = |(‖n''‖)⁻¹ - 1| * ‖n''‖ := by
        rw [abs_mul, abs_of_nonneg (norm_nonneg n'')]
      rw [h0, norm_smul, Real.norm_eq_abs, ← hs]
      congr 1
      rw [sub_mul, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
    have h2 : |1 - ‖n''‖| ≤ ‖n'' - n‖ := by
      have h3 : |‖n''‖ - ‖n‖| ≤ ‖n'' - n‖ := abs_norm_sub_norm_le n'' n
      rw [hn] at h3
      rwa [abs_sub_comm] at h3
    have h4 : ‖(‖n''‖)⁻¹ • n'' - n‖ ≤ ‖(‖n''‖)⁻¹ • n'' - n''‖ + ‖n'' - n‖ := by
      have h5 : (‖n''‖)⁻¹ • n'' - n = ((‖n''‖)⁻¹ • n'' - n'') + (n'' - n) := by abel
      rw [h5]; exact norm_add_le _ _
    rw [h1] at h4
    linarith [h4, h2, hclose]



/-! ## The edge margin, the arc bounds and the monotonicity in `exc` -/

/-- **The vertical-edge margin at almost every cutting level.**  If the corner locus of the box
level is finite, then for almost every cutting level `u` the points of the surface on the *vertical*
edge lines of the box keep a positive distance from the flat plane at `u`.  The vertical-edge locus
is contained in the corner locus, whose `σ 2`-coordinates are then finite. -/
theorem pg_ae_edgeMargin (ψ : Submission.Diffeo) {c : R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ}
    (hcorner : {z : R3 | z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧
        ∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
          |z (σ j) - c (σ j)| = Submission.boxSide j * s}.Finite) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∃ mE : ℝ, 0 < mE ∧
        ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
          |z (σ 0) - c (σ 0)| = Submission.boxSide 0 * s →
          |z (σ 1) - c (σ 1)| = Submission.boxSide 1 * s →
          mE ≤ |z (σ 2) - (c (σ 2) + u)| := by
  classical
  set E : Set ℝ := (fun z : R3 => z (σ 2) - c (σ 2)) ''
    {z : R3 | z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧
      |z (σ 0) - c (σ 0)| = Submission.boxSide 0 * s ∧
      |z (σ 1) - c (σ 1)| = Submission.boxSide 1 * s} with hEdef
  have hEfin : E.Finite :=
    (hcorner.subset (fun z hz => ⟨hz.1, 0, 1, by decide, hz.2.1, hz.2.2⟩)).image _
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (hEfin.measure_zero (MeasureTheory.volume : MeasureTheory.Measure ℝ))
  intro u hu
  rw [Set.mem_ofPred_eq] at hu
  push Not at hu
  rw [hEdef, Set.mem_image]
  have hcl : u ∈ closure E := by
    rw [Metric.mem_closure_iff]
    intro eps heps
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt heps
    obtain ⟨z, hzcar, hz0, hz1, hlt⟩ := hu (1 / ((n : ℝ) + 1)) (by positivity)
    refine ⟨z (σ 2) - c (σ 2), ?_, ?_⟩
    · rw [hEdef]; exact ⟨z, ⟨hzcar, hz0, hz1⟩, rfl⟩
    · rw [Real.dist_eq]
      have hrw : u - (z (σ 2) - c (σ 2)) = -(z (σ 2) - (c (σ 2) + u)) := by ring
      rw [hrw, abs_neg]
      exact lt_trans hlt hn
  have hclosed : IsClosed E := hEfin.isClosed
  exact hclosed.closure_subset hcl

/-- **A uniform bound on the derivatives of the trace arcs**: a family of functions `C³` on
`[-η, η]` has derivatives bounded on the compact subinterval `[-η/4, η/4]`. -/
theorem pg_arc_deriv_bound {N : ℕ} {γ : Fin N → ℝ → R3} {η : ℝ} (hη : 0 < η)
    (hγ : ∀ k : Fin N, ContDiffOn ℝ 3 (γ k) (Set.Icc (-η) η)) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ k : Fin N, ∀ t ∈ Set.Icc (-(η / 4)) (η / 4),
      ‖deriv (γ k) t‖ ≤ M := by
  have hsub : Set.Icc (-(η / 4)) (η / 4) ⊆ Set.Ioo (-η) η := by
    intro t ht
    rw [Set.mem_Ioo]
    exact ⟨by linarith [ht.1, hη], by linarith [ht.2, hη]⟩
  have hk : ∀ k : Fin N, ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Set.Icc (-(η / 4)) (η / 4), ‖deriv (γ k) t‖ ≤ C := by
    intro k
    have hopen : ContDiffOn ℝ 3 (γ k) (Set.Ioo (-η) η) :=
      (hγ k).mono (Set.Ioo_subset_Icc_self)
    have huniq : UniqueDiffOn ℝ (Set.Ioo (-η) η) := uniqueDiffOn_Ioo (-η) η
    have hcontW : ContinuousOn (derivWithin (γ k) (Set.Ioo (-η) η))
        (Set.Icc (-(η / 4)) (η / 4)) :=
      (ContDiffOn.continuousOn_derivWithin hopen huniq (by norm_num)).mono hsub
    have hcongr : Set.EqOn (deriv (γ k)) (derivWithin (γ k) (Set.Ioo (-η) η))
        (Set.Icc (-(η / 4)) (η / 4)) :=
      fun t ht => (derivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds (hsub ht))).symm
    have hcont : ContinuousOn (deriv (γ k)) (Set.Icc (-(η / 4)) (η / 4)) :=
      hcontW.congr hcongr
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    exact ⟨max C 0, le_max_right _ _, fun t ht => le_trans (hC t ht) (le_max_left _ _)⟩
  by_cases hN : N = 0
  · subst hN
    exact ⟨1, le_refl 1, fun k => Fin.elim0 k⟩
  · haveI : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero hN⟩⟩
    choose C hC0 hC using hk
    refine ⟨max 1 (Finset.univ.sup' Finset.univ_nonempty C), le_max_left _ _, ?_⟩
    intro k t ht
    exact le_trans (hC k t ht)
      (le_trans (Finset.le_sup' C (Finset.mem_univ k)) (le_max_right _ _))

/-- `Work.Drive.Final.TiltedGenericity` is monotone in the exceptional set. -/
theorem pg_tiltedGenericity_mono_exc {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc exc' : Finset ℝ}
    (hsub : (exc : Set ℝ) ⊆ (exc' : Set ℝ))
    (hgen : Work.Drive.Final.TiltedGenericity ψ s c σ u v h ℓ exc) :
    Work.Drive.Final.TiltedGenericity ψ s c σ u v h ℓ exc' := by
  obtain ⟨h1, h2, h3, h4⟩ := hgen
  refine ⟨?_, ?_, ?_, h4⟩
  · intro lam hlam p hp1 hp2 hp3
    exact h1 lam (fun hmem => hlam (hsub hmem)) p hp1 hp2 hp3
  · intro lam hlam p hp1 hp2 hp3 t
    exact h2 lam (fun hmem => hlam (hsub hmem)) p hp1 hp2 hp3 t
  · intro p hp1 hp2 hp3
    exact ⟨(h3 p hp1 hp2 hp3).1, hsub (h3 p hp1 hp2 hp3).2⟩

/-- **No triple point on a slab face at a level avoiding the corner slab values.**  A triple point
(`Work.Drive.Final.IsTriplePoint`) requires the image of `p` to have two extremal box coordinates and
to lie on the slab face `|slabFn| = h`; if `h` avoids the finitely many slab values of the corner
locus (finite by `hcorner`, see `Work.Drive.Mono.exists_finset_cornerSlabValues_all`), no such point
exists. -/
theorem not_isTriplePoint_of_cornerLevel_avoid {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {h : ℝ}
    (hhavoid : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s) →
      |inner ℝ v z - (inner ℝ v c + u)| ≠ h) :
    ∀ p : ℝ × ℝ, ¬ Work.Drive.Final.IsTriplePoint ψ s c σ u v h p := by
  intro p hp
  obtain ⟨⟨i, j, hij, hi, hj⟩, hslab⟩ := hp
  refine hhavoid (Work.BoxShrink.Pinch.par ψ p) ?_ ⟨i, j, hij, hi, hj⟩ ?_
  · rw [Work.BoxShrink.Pinch.carrier_eq_range]; exact ⟨p, rfl⟩
  · rw [Work.Drive.Final.slabFn_apply] at hslab
    exact hslab

theorem sweepDataGood_exists
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (B : ℕ) (hBG : Work.Drive.Mono.BoxGen ψ c σ s)
    (hcorner : {z : LeanEval.KnotTheory.PardonDistortion.R3 |
        z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧
        ∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
          |z (σ j) - c (σ j)| = Submission.boxSide j * s}.Finite) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      |u| < Submission.eps * r →
      Work.Drive.Mono.CutTransverse K s c σ u →
      (∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
          deriv (fun r : ℝ => (K.curve r) (σ 2)) t = 0 →
          δ ≤ |(K.curve t) (σ 2) - (c (σ 2) + u)|) →
      ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          K.curve t ∈ Submission.PBox s c σ ∧
          (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal) ≤ (B : ENNReal)) →
      ∃ (v : LeanEval.KnotTheory.PardonDistortion.R3) (h R : ℝ)
        (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
        Work.Drive.Mono.TiltData ψ s c σ u v h R ℓ exc lam0 lam1 ∧
        (∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
            h ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|) ∧
        (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
            deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
            h ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|) ∧
        (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
            |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h →
            deriv (fun r : ℝ => ℓ (K.curve r)) t ≠ 0) ∧
        (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
            |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h →
            deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0) ∧
        (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
            |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h →
            ℓ (K.curve t) ∈ (exc : Set ℝ)) ∧
        Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
            K.curve t ∈ Submission.PBox s c σ ∧
            inner ℝ v (K.curve t) = inner ℝ v c + u} ≤ B ∧
        Work.Drive.Mono.SlabCutsBox s c σ (inner ℝ v c + u) h v ∧
        (∀ y ∈ closure (Submission.PBox s c σ), lam0 < ℓ y ∧ ℓ y < lam1) ∧
        (∀ i : Fin 3, ℓ (EuclideanSpace.single (σ i) (1 : ℝ)) ≠ 0) ∧
        (∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
          z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → z ∈ Submission.PBox s c σ →
          |inner ℝ v z - (inner ℝ v c + u)| = h →
          ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
            fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0) ∧
        Work.Drive.Mono.JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1 ∧
        Work.Drive.Final.GoodSweepData2 ψ K s c σ u v h R ℓ exc lam0 lam1 := by
  classical
  have hs : 0 < s := lt_trans hr hrs
  have hs0 : 0 ≤ s := le_of_lt hs
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  -- ## 0. the almost-everywhere geometric facts
  filter_upwards [Work.Drive.Mono.ae_exists_goodV_near K hs c σ (θ := 1 / 16) (by norm_num),
      Work.Drive.Mono.ae_noBendCrossing K (Work.BoxShrink.shiftVσ σ 1) c σ s,
      Work.Drive.Mono.ae_faceCrossReg_of_boxGen ψ c σ s hs hBG,
      Work.Drive.Mono.ae_faceNoBend ψ c σ s,
      pg_ae_edgeMargin (ψ := ψ) (c := c) (σ := σ) (s := s) hcorner] with u hV hBnd hX hFB hedge
  intro hu hcut hflat hcount
  obtain ⟨εg, δg, hεg0, hδg0, _hεgθ, _hδgθ, hnog⟩ := hV
  obtain ⟨δf, hδf0, hδf⟩ := hflat
  obtain ⟨mbox, hmbox0, hmboxmem⟩ := Work.Drive.Mono.exists_margin_boxSphere K c σ hs hcut
  -- ## 1. the trace arcs of the box sphere and their derivative bound
  have hub : |u| < Submission.boxSide 2 * s := by
    have h2 : Submission.eps < Submission.boxSide 2 := by
      have h4 := Submission.one_le_rpow_two_thirds
      rw [Submission.eps, Submission.boxSide_two]
      linarith
    calc |u| < Submission.eps * r := hu
      _ < Submission.eps * s := mul_lt_mul_of_pos_left hrs (by rw [Submission.eps]; norm_num)
      _ < Submission.boxSide 2 * s := mul_lt_mul_of_pos_right h2 hs
  obtain ⟨N, γ, η, m, hη, hm, hγ, hγh, hγβ, harcCover⟩ :=
    Work.Drive.Mono.gammaArcs_exist ψ hs c σ hub hX
  obtain ⟨M, hM1, hMb⟩ := pg_arc_deriv_bound (N := N) (γ := γ) (η := η) hη hγ
  -- ## 2. the numerical constants
  set R1 : ℝ := 5 / 2 * s with hR1def
  have hR1pos : 0 < R1 := by rw [hR1def]; linarith
  have hR1b : ∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R1 := by
    intro y hy; rw [hR1def]; exact Work.Drive.Mono.norm_sub_le_of_mem_PBox hs0 hy
  have hR1cl : ∀ y ∈ closure (Submission.PBox s c σ), ‖y - c‖ ≤ R1 := by
    intro y hy; rw [hR1def]; exact Work.Drive.Mono.norm_sub_le_of_mem_closure_PBox hs0 hy
  set ε₀ : ℝ := min δf (min mbox δg) / 4 with hε₀def
  have hε₀0 : 0 < ε₀ := by
    rw [hε₀def]; exact div_pos (lt_min hδf0 (lt_min hmbox0 hδg0)) (by norm_num)
  have hε₀δf : ε₀ ≤ δf := by
    rw [hε₀def]; have h := min_le_left δf (min mbox δg); linarith
  have hε₀mbox : ε₀ ≤ mbox := by
    rw [hε₀def]; have h := min_le_right δf (min mbox δg); have h2 := min_le_left mbox δg
    linarith
  have hε₀δg : ε₀ ≤ δg := by
    rw [hε₀def]; have h := min_le_right δf (min mbox δg); have h2 := min_le_right mbox δg
    linarith
  have hε₀δg4 : ε₀ ≤ δg / 4 := by
    rw [hε₀def]; have h := min_le_right δf (min mbox δg); have h2 := min_le_right mbox δg
    linarith
  set θ' : ℝ := min (1 / 32) (min (εg / 4) (min ((ε₀ / 4) / (R1 + 1))
      (min (min (1 / (16 * M)) (m / (32 * R1))) (η / (32 * R1))))) with hθ'def
  have hθ'0 : 0 < θ' := by
    rw [hθ'def]
    exact lt_min (by norm_num) (lt_min (by linarith)
      (lt_min (div_pos (by linarith) (by linarith))
        (lt_min (lt_min (div_pos one_pos (by linarith [hM1]))
          (div_pos hm (by linarith [hR1pos]))) (div_pos hη (by linarith [hR1pos])))))
  have hθ'32 : θ' ≤ 1 / 32 := by rw [hθ'def]; exact min_le_left _ _
  have hθ'εg : θ' ≤ εg / 4 := by
    rw [hθ'def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hθ'R1 : θ' * R1 < ε₀ / 4 := by
    have h1 : θ' ≤ (ε₀ / 4) / (R1 + 1) := by
      rw [hθ'def]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have h2 : θ' * R1 ≤ ((ε₀ / 4) / (R1 + 1)) * R1 :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hR1pos)
    have h3 : ((ε₀ / 4) / (R1 + 1)) * R1 < ε₀ / 4 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0 : ℝ) < R1 + 1)]
      nlinarith
    linarith
  have hθ'M : θ' * M ≤ 1 / 16 := by
    have h1 : θ' ≤ 1 / (16 * M) := by
      rw [hθ'def]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_left _ _) (min_le_left _ _))))
    have h2 : θ' * M ≤ (1 / (16 * M)) * M := mul_le_mul_of_nonneg_right h1 (by linarith [hM1])
    have h3 : (1 / (16 * M)) * M = 1 / 16 := by field_simp
    linarith
  have hθ'm : θ' * R1 ≤ m / 32 := by
    have h1 : θ' ≤ m / (32 * R1) := by
      rw [hθ'def]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))))
    have h2 : θ' * R1 ≤ (m / (32 * R1)) * R1 :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hR1pos)
    have h3 : (m / (32 * R1)) * R1 = m / 32 := by field_simp
    linarith
  have hθ'η : θ' * R1 ≤ η / 32 := by
    have h1 : θ' ≤ η / (32 * R1) := by
      rw [hθ'def]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    have h2 : θ' * R1 ≤ (η / (32 * R1)) * R1 :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hR1pos)
    have h3 : (η / (32 * R1)) * R1 = η / 32 := by field_simp
    linarith
  -- ## 3. the no-grazing witness with the arc clauses
  obtain ⟨v, n, hw, ρw, hv1, hn1, hvn, hgood, hθ'v, _hvεg, hhw0, hρw0, hhwsize,
    hcl1, _hcl2, hcl3, _hcl4, harcAll⟩ :=
    Work.Drive.Mono.noGraze_witness_gamma_noEdge ψ K hr hrs hu c σ hcut hεg0 hδg0 hθ'0 hnog hBnd
      hX hFB hedge
  have harcs := harcAll N γ η m hη hm hγ hγh hγβ harcCover
  obtain ⟨harcℓ_w, harcv_w⟩ := harcs
  obtain ⟨ρh, hρh0, hρhgood⟩ := Work.Drive.Mono.Band.heightGood_open ψ hgood
  -- ## 4. the perturbation size
  set εv : ℝ := min (min (ε₀ / (8 * R1)) (hw / (100 * R1)))
      (min (min (ρh / 8) (ρw / 8))
        (min (min (εg / 4) (1 / 128))
          (min (min (1 / (16 * M)) (m / (32 * R1))) (η / (32 * R1))))) with hεvdef
  have hεva : εv ≤ ε₀ / (8 * R1) := by
    rw [hεvdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hεvb : εv ≤ hw / (100 * R1) := by
    rw [hεvdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hεvc : εv ≤ ρh / 8 := by
    rw [hεvdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεvd : εv ≤ ρw / 8 := by
    rw [hεvdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεve : εv ≤ εg / 4 := by
    rw [hεvdef]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hεvf : εv ≤ 1 / 128 := by
    rw [hεvdef]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hεvMle : εv ≤ 1 / (16 * M) := by
    rw [hεvdef]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_left _ _) (min_le_left _ _))))
  have hεvmle : εv ≤ m / (32 * R1) := by
    rw [hεvdef]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_left _ _) (min_le_right _ _))))
  have hεvηle : εv ≤ η / (32 * R1) := by
    rw [hεvdef]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hεv0 : 0 < εv := by
    rw [hεvdef]
    exact lt_min (lt_min (div_pos hε₀0 (by linarith)) (div_pos hhw0 (by linarith)))
      (lt_min (lt_min (div_pos hρh0 (by norm_num)) (div_pos hρw0 (by norm_num)))
        (lt_min (lt_min (div_pos hεg0 (by norm_num)) (by norm_num))
          (lt_min (lt_min (div_pos one_pos (by linarith [hM1]))
            (div_pos hm (by linarith [hR1pos]))) (div_pos hη (by linarith [hR1pos])))))
  have hεvε₀ : εv * R1 ≤ ε₀ / 8 := by
    have h2 : εv * R1 ≤ (ε₀ / (8 * R1)) * R1 := mul_le_mul_of_nonneg_right hεva (le_of_lt hR1pos)
    have h3 : (ε₀ / (8 * R1)) * R1 = ε₀ / 8 := by field_simp
    rwa [h3] at h2
  have hεvhw : εv * R1 ≤ hw / 100 := by
    have h2 : εv * R1 ≤ (hw / (100 * R1)) * R1 := mul_le_mul_of_nonneg_right hεvb (le_of_lt hR1pos)
    have h3 : (hw / (100 * R1)) * R1 = hw / 100 := by field_simp
    rwa [h3] at h2
  have hεvM : εv * M ≤ 1 / 16 := by
    have h2 : εv * M ≤ (1 / (16 * M)) * M := mul_le_mul_of_nonneg_right hεvMle (by linarith [hM1])
    have h3 : (1 / (16 * M)) * M = 1 / 16 := by field_simp
    linarith
  have hεvm : εv * R1 ≤ m / 32 := by
    have h2 : εv * R1 ≤ (m / (32 * R1)) * R1 := mul_le_mul_of_nonneg_right hεvmle (le_of_lt hR1pos)
    have h3 : (m / (32 * R1)) * R1 = m / 32 := by field_simp
    linarith
  have hεvη : εv * R1 ≤ η / 32 := by
    have h2 : εv * R1 ≤ (η / (32 * R1)) * R1 := mul_le_mul_of_nonneg_right hεvηle (le_of_lt hR1pos)
    have h3 : (η / (32 * R1)) * R1 = η / 32 := by field_simp
    linarith
  -- ## 5. the perturbed tilt and the new normal
  obtain ⟨v', hv'1, hv'v, haxis', hv'e0⟩ := sweepData_axis_perturb (σ := σ) hv1 hεv0
  have hv'e_le : ‖v' - Work.BoxShrink.shiftVσ σ 1‖ ≤ θ' + εv := by
    have h1 : v' - Work.BoxShrink.shiftVσ σ 1
        = (v' - v) + (v - Work.BoxShrink.shiftVσ σ 1) := by abel
    calc ‖v' - Work.BoxShrink.shiftVσ σ 1‖
        ≤ ‖v' - v‖ + ‖v - Work.BoxShrink.shiftVσ σ 1‖ := by
          rw [h1]; exact norm_add_le _ _
      _ ≤ εv + θ' := add_le_add hv'v hθ'v
      _ = θ' + εv := by ring
  have hv'e18 : ‖v' - Work.BoxShrink.shiftVσ σ 1‖ ≤ 1 / 8 := by
    linarith [hv'e_le, hθ'32, hεvf]
  have hv'e_eps : ‖v' - Work.BoxShrink.shiftVσ σ 1‖ < εg := by
    linarith [hv'e_le, hθ'εg, hεve, hεg0]
  obtain ⟨n', hn'1, hv'n', hn'close⟩ := sweepData_orth_near hv'1 hn1 hvn hv'v (by linarith [hεvf])
  have hgood' : Work.Drive.Mono.Band.HeightGood ψ n' :=
    hρhgood n' (by linarith [hn'close, hεvc, hρh0])
  have hn'n : ‖n' - n‖ ≤ ρw / 4 := by linarith [hn'close, hεvd, hρw0]
  -- ## 6. the window of half-widths
  set A : ℝ := ‖v' - Work.BoxShrink.shiftVσ σ 1‖ * R1 with hAdef
  have hApos : 0 < A := by
    rw [hAdef]; exact mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hv'e0)) hR1pos
  have hwin0 : ‖v' - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s)
      < boxWidth s σ v' - |u| :=
    Work.Drive.Mono.Band.window_nondegenerate s hs σ hv'e18 hrs hu
  have hA_win : A < boxWidth s σ v' - |u| := by rw [hAdef, hR1def]; exact hwin0
  have hA_hw : A < hw - εv * R1 := by
    have h1 : ‖v' - Work.BoxShrink.shiftVσ σ 1‖ ≤ ‖v - Work.BoxShrink.shiftVσ σ 1‖ + εv := by
      have h1' : v' - Work.BoxShrink.shiftVσ σ 1
          = (v' - v) + (v - Work.BoxShrink.shiftVσ σ 1) := by abel
      calc ‖v' - Work.BoxShrink.shiftVσ σ 1‖
          ≤ ‖v' - v‖ + ‖v - Work.BoxShrink.shiftVσ σ 1‖ := by rw [h1']; exact norm_add_le _ _
        _ ≤ εv + ‖v - Work.BoxShrink.shiftVσ σ 1‖ := by linarith [hv'v]
        _ = ‖v - Work.BoxShrink.shiftVσ σ 1‖ + εv := by ring
    have h2 : A ≤ (‖v - Work.BoxShrink.shiftVσ σ 1‖ + εv) * R1 := by
      rw [hAdef]; exact mul_le_mul_of_nonneg_right h1 (le_of_lt hR1pos)
    have h3 : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R1 < hw / 2 := by
      have h4 := hhwsize
      rw [hR1def]; nlinarith
    nlinarith [h2, h3, hεvhw, hhw0, hεv0, hR1pos]
  have hA_δg : A < δg := by
    have h1 : A ≤ (θ' + εv) * R1 := by
      rw [hAdef]; exact mul_le_mul_of_nonneg_right hv'e_le (le_of_lt hR1pos)
    have h2 : (θ' + εv) * R1 = θ' * R1 + εv * R1 := by ring
    linarith [h1, h2, hθ'R1, hεvε₀, hε₀δg, hε₀0]
  have hAm : A < m / 8 := by
    rw [hAdef]
    calc ‖v' - Work.BoxShrink.shiftVσ σ 1‖ * R1 ≤ (θ' + εv) * R1 :=
          mul_le_mul_of_nonneg_right hv'e_le (le_of_lt hR1pos)
      _ = θ' * R1 + εv * R1 := by ring
      _ ≤ m / 32 + m / 32 := add_le_add hθ'm hεvm
      _ < m / 8 := by linarith [hm]
  have hAmη : A < η / 8 := by
    rw [hAdef]
    calc ‖v' - Work.BoxShrink.shiftVσ σ 1‖ * R1 ≤ (θ' + εv) * R1 :=
          mul_le_mul_of_nonneg_right hv'e_le (le_of_lt hR1pos)
      _ = θ' * R1 + εv * R1 := by ring
      _ ≤ η / 32 + η / 32 := add_le_add hθ'η hεvη
      _ < η / 8 := by linarith [hη]
  set Bm : ℝ := min (hw - εv * R1) (min (boxWidth s σ v' - |u|) δg) with hBmdef
  have hBm_hw : Bm ≤ hw - εv * R1 := by rw [hBmdef]; exact min_le_left _ _
  have hBm_win : Bm ≤ boxWidth s σ v' - |u| := by
    rw [hBmdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hBm_δg : Bm ≤ δg := by
    rw [hBmdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hAB : A < Bm := lt_min hA_hw (lt_min hA_win hA_δg)
  set C : ℝ := min Bm (min (m / 8) (η / 8)) with hCdef
  have hAC : A < C := lt_min hAB (lt_min hAm hAmη)
  obtain ⟨F, hF⟩ := Work.Drive.Mono.exists_finset_cornerSlabValues_all (ψ := ψ) (s := s) (u := u)
    (c := c) (v := v') (σ := σ) hcorner
  obtain ⟨A₂, B₂, hAA₂, hA₂B₂, hB₂C, hAvoid⟩ :=
    Work.Drive.Mono.exists_subwindow_avoiding_finset hAC F
  have hA₂pos : 0 < A₂ := lt_trans hApos hAA₂
  have hB₂win : B₂ ≤ Work.Drive.Mono.boxWidth s σ v' - |u| :=
    le_trans (le_of_lt hB₂C) (le_trans (min_le_left _ _) hBm_win)
  -- ## 6b. the adapted orthonormal basis of `v'^⊥`, and the null bad sets of the event clauses
  obtain ⟨a₀, b₀, ha0, hb0, hab0, hva0, hvb0, hnb0⟩ :=
    Work.Drive.Mono.Band.exists_adapted_basis (v := v') (n := n') hv'1 hn'1 hv'n'
  obtain ⟨ρh', hρh'0, hρh'good⟩ := Work.Drive.Mono.Band.heightGood_open ψ hgood'
  set ρ : ℝ := min (ρw / 4) ρh' with hρdef
  have hρ0 : 0 < ρ := lt_min (by linarith) hρh'0
  have hρρw : ρ ≤ ρw / 4 := min_le_left _ _
  have hρρh : ρ ≤ ρh' := min_le_right _ _
  set Nknot : Set ℝ := {y : ℝ | ∃ t : ℝ,
      deriv (fun r : ℝ => inner ℝ v' (K.curve r)) t = 0 ∧ inner ℝ v' (K.curve t) = y}
    with hNknotdef
  have hNknot : MeasureTheory.volume Nknot = 0 :=
    Work.Drive.Mono.volume_knotCritValues_eq_zero K v'
  -- the four null bad sets of the event clauses of `GoodSweepData2`
  set S₁ : Set (ℝ × ℝ) := {p : ℝ × ℝ | Work.Drive.Mono.Band.HeightGood ψ
        (Work.Drive.Mono.Band.dirOf p.2 a₀ b₀) ∧
      ∃ q : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ q ∈ Submission.PBox s c σ ∧
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
          ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf p.2 a₀ b₀))) q = 0 ∧
        |inner ℝ v' (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v' c + u)| = p.1} with hS₁def
  set S₂ : Set (ℝ × ℝ) := {p : ℝ × ℝ | ¬ (∀ q : ℝ × ℝ, Work.Drive.Final.IsFaceEvent ψ s c σ u v'
          p.1 ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf p.2 a₀ b₀)) q →
          ∃ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
              ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf p.2 a₀ b₀))) q
              = t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v') q ∧
            ∀ w : ℝ × ℝ, w ≠ 0 →
              fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v') q w = 0 →
              (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ =>
                Work.Drive.EpsForm.sweepHeight ψ
                  ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf p.2 a₀ b₀)) q
                  - t * Work.Drive.Final.slabFnPar ψ c u v' q)) q) w w ≠ 0)} with hS₂def
  set S₃ : Set (ℝ × ℝ) := offKBad ψ K s c σ u v' a₀ b₀ with hS₃def
  set S₄ : Set (ℝ × ℝ) := {p : ℝ × ℝ | (inner ℝ v' c + u + p.1) ∈ Nknot ∨
      (inner ℝ v' c + u - p.1) ∈ Nknot} with hS₄def
  have hS₁0 : MeasureTheory.volume S₁ = 0 :=
    Work.Drive.Mono.no_eventOnFace_null ψ s u c σ v' a₀ b₀ ha0 hb0 hab0 hva0 hvb0
  have hS₂0 : MeasureTheory.volume S₂ = 0 :=
    Work.Drive.Mono.faceEvent_degen_null ψ s u c σ v' a₀ b₀ hv'1 ha0 hb0 hab0 hva0 hvb0
  have hS₃0 : MeasureTheory.volume S₃ = 0 :=
    Work.Drive.Mono.volume_offKBad_eq_zero ψ K s c σ u v' a₀ b₀ hv'1 ha0 hb0 hab0 hva0 hvb0
  have hS₄0 : MeasureTheory.volume S₄ = 0 := by
    have h1 : MeasureTheory.volume {h : ℝ | inner ℝ v' c + u + h ∈ Nknot} = 0 :=
      (MeasureTheory.measure_preimage_add (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        (inner ℝ v' c + u) Nknot).trans hNknot
    have h2 : MeasureTheory.volume {h : ℝ | inner ℝ v' c + u - h ∈ Nknot} = 0 := by
      have hmap := MeasureTheory.Measure.map_sub_left_eq_self
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (inner ℝ v' c + u)
      have hle := MeasureTheory.Measure.le_map_apply
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        (f := fun x : ℝ => inner ℝ v' c + u - x)
        (measurable_const.sub measurable_id).aemeasurable Nknot
      rw [hmap, hNknot] at hle
      have hset : {h : ℝ | inner ℝ v' c + u - h ∈ Nknot}
          = (fun x : ℝ => inner ℝ v' c + u - x) ⁻¹' Nknot := rfl
      rw [hset]
      exact le_antisymm hle bot_le
    rw [hS₄def]
    have hset : {p : ℝ × ℝ | (inner ℝ v' c + u + p.1) ∈ Nknot ∨
        (inner ℝ v' c + u - p.1) ∈ Nknot}
        = ({h : ℝ | inner ℝ v' c + u + h ∈ Nknot} ∪
            {h : ℝ | inner ℝ v' c + u - h ∈ Nknot}) ×ˢ (Set.univ : Set ℝ) := by
      ext p; simp
    rw [hset, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
      MeasureTheory.measure_union_null h1 h2, zero_mul]
  set Sbad : Set (ℝ × ℝ) := ((S₁ ∪ S₂) ∪ S₃) ∪ S₄ with hSbaddef
  have hSbad : MeasureTheory.volume Sbad = 0 := by
    rw [hSbaddef]
    exact MeasureTheory.measure_union_null
      (MeasureTheory.measure_union_null (MeasureTheory.measure_union_null hS₁0 hS₂0) hS₃0) hS₄0
  -- ## 7. the exported thin-slab band data
  obtain ⟨h, τ, exc₁, hA₂h, hhB₂, hSavoid, hboxw, hnf_n', hnf1, hv'nf, hnf_coord, hgen₁,
    hfaceReg⟩ :=
    Work.Drive.Mono.tiltData_window_of_dir_export_param ψ s c σ u A₂ B₂ ρ v' n'
      hA₂pos hA₂B₂ hB₂win hρ0 hv'1 hn'1 hv'n' haxis' hgood' a₀ b₀ ha0 hb0 hab0 hva0 hvb0
      hnb0 Sbad hSbad
  set nf : R3 := Work.Drive.Mono.Band.dirOf τ a₀ b₀ with hnfdef
  have hAh : A < h := lt_trans hAA₂ hA₂h
  have hposh : 0 < h := lt_trans hA₂pos hA₂h
  have hhBm : h < Bm := lt_of_lt_of_le hhB₂ (le_trans (le_of_lt hB₂C) (min_le_left _ _))
  have hhm : h < m / 8 :=
    lt_of_lt_of_le hhB₂ (le_trans (le_of_lt hB₂C) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hhη : h < η / 8 :=
    lt_of_lt_of_le hhB₂ (le_trans (le_of_lt hB₂C) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hhwle : h ≤ hw := by
    have h2 : 0 ≤ εv * R1 := mul_nonneg (le_of_lt hεv0) (le_of_lt hR1pos)
    linarith [hhBm, hBm_hw]
  have hhhw : h + εv * R1 < hw := by linarith [hBm_hw, hhBm]
  have hhδg : h < δg := by linarith [hBm_δg, hhBm]
  have hnotF : h ∉ F := fun hmem => hAvoid h hmem ⟨hA₂h, hhB₂⟩
  have hsize : ‖v' - Work.BoxShrink.shiftVσ σ 1‖ * R1 < h := by rw [← hAdef]; exact hAh
  have hnfn : ‖nf - n‖ < ρw := by
    have h1 : ‖nf - n‖ ≤ ‖nf - n'‖ + ‖n' - n‖ := by
      have h2 : nf - n = (nf - n') + (n' - n) := by abel
      rw [h2]; exact norm_add_le _ _
    have h3 : ‖nf - n'‖ < ρw / 4 := lt_of_lt_of_le hnf_n' hρρw
    linarith
  -- ## 8. the face set and the enlarged exceptional sets
  have hderiv_face : ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) ≤ s →
      |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| = h →
      deriv (fun r : ℝ => inner ℝ v' (K.curve r)) t ≠ 0 := by
    intro t hbox hface hd
    by_cases hbs : Submission.boxNorm c σ (K.curve t) = s
    · have h1 := hcl1 t hbs
      have h2 := sweepData_slab_le (u := u) hv'v
        (hR1cl _ (Work.Step2.closedBox_subset_closure_PBox hs c σ (le_of_eq hbs)))
      have h3 : hw ≤ h + εv * R1 := by
        have h4 := le_trans h1 h2
        rwa [hface] at h4
      exact absurd hhhw (not_lt.mpr h3)
    · have hlt : Submission.boxNorm c σ (K.curve t) < s := lt_of_le_of_ne hbox hbs
      have hmem : K.curve t ∈ Submission.PBox s c σ :=
        (Submission.mem_PBox_iff s c σ (K.curve t)).mpr hlt
      have h2 := hnog v' hv'1 hv'e_eps t hmem hd
      rw [hface] at h2
      exact absurd hhδg (not_lt.mpr h2)
  have hfaceF : ({t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) ≤ s ∧
      |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| = h}).Finite :=
    Work.Drive.Mono.finite_facePts_tilted K s c σ u v' h hderiv_face
  set Fex : Finset ℝ := hfaceF.toFinset.image (fun t : ℝ => (innerSL ℝ) nf (K.curve t))
    with hFexdef
  set exc0 : Finset ℝ := exc₁ ∪ Fex with hexc0def
  have hgen : Work.Drive.Final.TiltedGenericity ψ s c σ u v' h ((innerSL ℝ) nf) exc0 := by
    obtain ⟨g1, g2, g3, g4⟩ := hgen₁
    refine ⟨?_, ?_, ?_, g4⟩
    · intro lam hlam p hp1 hp2 hp3
      exact g1 lam (fun hmem => hlam (Finset.mem_union_left Fex hmem)) p hp1 hp2 hp3
    · intro lam hlam p hp1 hp2 hp3 t
      exact g2 lam (fun hmem => hlam (Finset.mem_union_left Fex hmem)) p hp1 hp2 hp3 t
    · intro p hp1 hp2 hp3
      exact ⟨(g3 p hp1 hp2 hp3).1, Finset.mem_union_left Fex (g3 p hp1 hp2 hp3).2⟩
  -- ## 9. the window bookkeeping
  set q : ℝ := |(innerSL ℝ) nf c| + ‖(innerSL ℝ) nf‖ * R1 + 1 with hqdef
  set mw : ℝ := 1 + ∑ t ∈ exc0, |t| with hmwdef
  have hq1 : 1 ≤ q := by
    rw [hqdef]
    nlinarith [abs_nonneg ((innerSL ℝ) nf c), norm_nonneg ((innerSL ℝ) nf), le_of_lt hR1pos]
  have hmw1 : 1 ≤ mw := by
    rw [hmwdef]; linarith [Finset.sum_nonneg (fun t (_ : t ∈ exc0) => abs_nonneg t)]
  have hℓy : ∀ y ∈ closure (Submission.PBox s c σ), |(innerSL ℝ) nf y| ≤ q - 1 := by
    intro y hy
    have h1 : ‖y - c‖ ≤ R1 := hR1cl y hy
    have h2 : (innerSL ℝ) nf y - (innerSL ℝ) nf c = (innerSL ℝ) nf (y - c) := by rw [map_sub]
    have h3 : |(innerSL ℝ) nf (y - c)| ≤ ‖(innerSL ℝ) nf‖ * ‖y - c‖ := by
      have := ContinuousLinearMap.le_opNorm ((innerSL ℝ) nf) (y - c)
      rwa [Real.norm_eq_abs] at this
    have h4 : |(innerSL ℝ) nf y| ≤ |(innerSL ℝ) nf y - (innerSL ℝ) nf c|
        + |(innerSL ℝ) nf c| := by
      have h5 : (innerSL ℝ) nf y = ((innerSL ℝ) nf y - (innerSL ℝ) nf c)
          + (innerSL ℝ) nf c := by ring
      calc |(innerSL ℝ) nf y|
          = |((innerSL ℝ) nf y - (innerSL ℝ) nf c) + (innerSL ℝ) nf c| :=
            congrArg (fun z : ℝ => |z|) h5
        _ ≤ _ := abs_add_le _ _
    rw [h2] at h4
    have h6 : ‖(innerSL ℝ) nf‖ * ‖y - c‖ ≤ ‖(innerSL ℝ) nf‖ * R1 :=
      mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    have h7 : |(innerSL ℝ) nf y| ≤ ‖(innerSL ℝ) nf‖ * R1 + |(innerSL ℝ) nf c| := by
      linarith
    rw [hqdef]
    linarith
  have hexcw : ∀ t ∈ exc0, |t| ≤ mw - 1 := by
    intro t ht
    have h1 : |t| ≤ ∑ t' ∈ exc0, |t'| :=
      Finset.single_le_sum (fun t' (_ : t' ∈ exc0) => abs_nonneg t') ht
    rw [hmwdef]
    linarith
  have hwinJ : ∀ y ∈ closure (Submission.PBox s c σ),
      -(q + mw) < (innerSL ℝ) nf y ∧ (innerSL ℝ) nf y < q + mw := by
    intro y hy
    have h1 := hℓy y hy
    constructor
    · have h2 : -(q - 1) ≤ (innerSL ℝ) nf y := by
        have := neg_abs_le ((innerSL ℝ) nf y)
        linarith
      linarith
    · have h2 : (innerSL ℝ) nf y ≤ |(innerSL ℝ) nf y| := le_abs_self _
      linarith
  have hexc0win : ∀ t ∈ exc0, -(q + mw) < t ∧ t < q + mw := by
    intro t ht
    have h1 := hexcw t ht
    constructor
    · have h2 := neg_abs_le t; linarith
    · have h2 := le_abs_self t; linarith
  -- ## 10. the junction bundle
  obtain ⟨exc1, hsub01, hexc1win, hcornerC⟩ :=
    Work.Drive.Mono.exists_exc_of_cornerLocus_finite (ψ := ψ) (s := s) (u := u) (c := c)
      (σ := σ) (v := v') (h := h) (ℓ := (innerSL ℝ) nf) (exc := exc0)
      (lam0 := -(q + mw)) (lam1 := q + mw) hs hcorner hwinJ hexc0win
  have harcℓ : ∀ k : Fin N, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
      deriv (fun r : ℝ => (innerSL ℝ) nf (γ k r)) t ≠ 0 := by
    intro k t htIoo ht2h
    have hdiff : DifferentiableAt ℝ (γ k) t := by
      have hnhds : Set.Icc (-η) η ∈ 𝓝 t := Icc_mem_nhds htIoo.1 htIoo.2
      exact ((hγ k).contDiffAt hnhds).differentiableAt (by norm_num)
    have hder : deriv (fun r : ℝ => (innerSL ℝ) nf (γ k r)) t
        = inner ℝ nf (deriv (γ k) t) := by
      have h1 : (fun r : ℝ => (innerSL ℝ) nf (γ k r)) = fun r : ℝ => inner ℝ nf (γ k r) := by
        funext r; rw [innerSL_apply_apply]
      rw [h1, deriv_inner_apply ℝ (differentiableAt_const nf) hdiff]
      simp
    rw [hder]
    refine harcℓ_w k t htIoo ?_ nf hnf1 hnfn
    linarith [ht2h, hhwle]
  have harcv : ∀ k : Fin N, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
      (1 / 2 : ℝ) ≤ inner ℝ v' (deriv (γ k) t) := by
    intro k t htIoo ht2h
    have hdiff : DifferentiableAt ℝ (γ k) t := by
      have hnhds : Set.Icc (-η) η ∈ 𝓝 t := Icc_mem_nhds htIoo.1 htIoo.2
      exact ((hγ k).contDiffAt hnhds).differentiableAt (by norm_num)
    have he1 : inner ℝ (Work.BoxShrink.shiftVσ σ 1) (deriv (γ k) t) = 1 := by
      have hder : deriv (fun r : ℝ => (γ k r) (σ 2)) t
          = inner ℝ (Work.BoxShrink.shiftVσ σ 1) (deriv (γ k) t) := by
        have h1 : (fun r : ℝ => (γ k r) (σ 2))
            = fun r : ℝ => inner ℝ (Work.BoxShrink.shiftVσ σ 1) (γ k r) := by
          funext r; rw [Work.Drive.Mono.inner_shiftVσ_one]
        rw [h1, deriv_inner_apply ℝ (differentiableAt_const _) hdiff]
        simp
      rw [← hder]
      have hev : (fun r : ℝ => (γ k r) (σ 2)) =ᶠ[𝓝 t] fun r : ℝ => c (σ 2) + u + r := by
        filter_upwards [isOpen_Ioo.mem_nhds htIoo] with r hr
        exact hγh k r ⟨le_of_lt hr.1, le_of_lt hr.2⟩
      rw [Filter.EventuallyEq.deriv_eq hev]
      simp
    have hMbd : ‖deriv (γ k) t‖ ≤ M := by
      refine hMb k t ?_
      rw [Set.mem_Icc]
      have h2h : |t| ≤ 2 * h := ht2h
      have hb := abs_le.mp h2h
      constructor <;> linarith [hb.1, hb.2, hhη, hη]
    have h2 : inner ℝ v' (deriv (γ k) t)
        = inner ℝ (Work.BoxShrink.shiftVσ σ 1) (deriv (γ k) t)
          + inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (deriv (γ k) t) := by
      rw [← inner_add_left]; congr 1; abel
    rw [h2, he1]
    have h3 : |inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (deriv (γ k) t)|
        ≤ ‖v' - Work.BoxShrink.shiftVσ σ 1‖ * ‖deriv (γ k) t‖ :=
      abs_real_inner_le_norm _ _
    have h4 : ‖v' - Work.BoxShrink.shiftVσ σ 1‖ * ‖deriv (γ k) t‖ ≤ (θ' + εv) * M :=
      mul_le_mul hv'e_le hMbd (norm_nonneg _) (by linarith [hθ'0, hεv0])
    have h5 : (θ' + εv) * M ≤ 1 / 8 := by
      have h6 : (θ' + εv) * M = θ' * M + εv * M := by ring
      linarith [h6, hθ'M, hεvM]
    have h7 := neg_abs_le (inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (deriv (γ k) t))
    linarith
  have hcover : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → |inner ℝ v' z - (inner ℝ v' c + u)| ≤ h →
      (∀ j : Fin 3, j ≠ 2 → ∀ j' : Fin 3, j' ≠ 2 → j ≠ j' →
        ¬ (|z (σ j) - c (σ j)| = Submission.boxSide j * s ∧
           |z (σ j') - c (σ j')| = Submission.boxSide j' * s)) →
      ∃ k, ∃ t ∈ Set.Ioo (-η) η, z = γ k t ∧ |t| ≤ 2 * h := by
    intro z hz hbox hslab hnoedge
    have hzc : ‖z - c‖ ≤ R1 :=
      hR1cl z (Work.Step2.closedBox_subset_closure_PBox hs c σ (le_of_eq hbox))
    have hpert : |inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (z - c)| ≤ A := by
      refine le_trans (abs_real_inner_le_norm _ _) ?_
      rw [hAdef]
      exact mul_le_mul_of_nonneg_left hzc (norm_nonneg _)
    have hflat_eq : z (σ 2) - (c (σ 2) + u)
        = (inner ℝ v' z - (inner ℝ v' c + u))
          - inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (z - c) := by
      have h1 : inner ℝ v' z - (inner ℝ v' c + u) = inner ℝ v' (z - c) - u := by
        rw [inner_sub_right]; ring
      have h2 : inner ℝ v' (z - c)
          = inner ℝ (Work.BoxShrink.shiftVσ σ 1) (z - c)
            + inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (z - c) := by
        rw [← inner_add_left]; congr 1; abel
      rw [h1, h2, Work.Drive.Mono.inner_shiftVσ_one]
      simp only [PiLp.sub_apply]
      ring
    have hflt : |z (σ 2) - (c (σ 2) + u)| ≤ h + A := by
      rw [hflat_eq]
      calc |inner ℝ v' z - (inner ℝ v' c + u)
            - inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (z - c)|
          = |(inner ℝ v' z - (inner ℝ v' c + u))
            + (-(inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (z - c)))| := by
              rw [sub_eq_add_neg]
        _ ≤ |inner ℝ v' z - (inner ℝ v' c + u)|
            + |-(inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (z - c))| := abs_add_le _ _
        _ = |inner ℝ v' z - (inner ℝ v' c + u)|
            + |inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (z - c)| := by rw [abs_neg]
        _ ≤ h + A := add_le_add hslab hpert
    have hflat_lt : |z (σ 2) - (c (σ 2) + u)| < m := by
      have h1 : A < m / 8 := hAm
      have h2 : h < m / 8 := hhm
      linarith [hflt, h1, h2, hm]
    obtain ⟨k, t, htIoo, hzt⟩ := harcCover z hz hbox hflat_lt hnoedge
    refine ⟨k, t, htIoo, hzt, ?_⟩
    have ht_eq : |t| = |z (σ 2) - (c (σ 2) + u)| := by
      rw [hzt, hγh k t (Set.Ioo_subset_Icc_self htIoo)]
      ring_nf
    rw [ht_eq]
    linarith [hflt, hAh, le_of_lt hposh]
  have hnoCornerFace : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → |inner ℝ v' z - (inner ℝ v' c + u)| = h →
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s) → False := by
    intro z hz hbox hslab hext
    have hmem := hF z hz hext
    rw [hslab] at hmem
    exact hnotF hmem
  obtain ⟨exc', hsub1', hexc'win, hJun⟩ :=
    Work.Drive.Mono.junctionGenC_of_arcs ψ hs c σ v' h ((innerSL ℝ) nf) exc1
      (-(q + mw)) (q + mw) hBG hcornerC hnoCornerFace hη hγ hγh hγβ hcover harcℓ harcv
      hwinJ hexc1win
  have hsub0' : (exc0 : Set ℝ) ⊆ (exc' : Set ℝ) := fun t ht => hsub1' t (hsub01 t ht)
  have hFex_sub : (Fex : Set ℝ) ⊆ (exc' : Set ℝ) := fun t ht =>
    hsub0' (Finset.mem_coe.mpr (Finset.mem_union_right exc₁ (Finset.mem_coe.mp ht)))
  have hgen' : Work.Drive.Final.TiltedGenericity ψ s c σ u v' h ((innerSL ℝ) nf) exc' :=
    pg_tiltedGenericity_mono_exc hsub0' hgen
  -- ## 11. the clauses
  have hℓne' : (innerSL ℝ) nf ≠ 0 := by
    intro h0
    have h1 : (innerSL ℝ) nf nf = 0 := by rw [h0]; rfl
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, hnf1] at h1
    norm_num at h1
  have hℓv' : (innerSL ℝ) nf v' = 0 := by
    rw [innerSL_apply_apply, real_inner_comm]; exact hv'nf
  have hTilt' : Work.Drive.Mono.TiltData ψ s c σ u v' h R1 ((innerSL ℝ) nf) exc'
      (-(q + mw)) (q + mw) :=
    ⟨hgen', hv'1, hℓne', hℓv', hsize, hposh, hR1b,
      (fun y hy => (hwinJ y (subset_closure hy)).1),
      (fun y hy => (hwinJ y (subset_closure hy)).2),
      by linarith [hq1, hmw1],
      hexc'win⟩
  have hclause2 : ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
      h ≤ |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| := by
    intro t hbs
    have h1 := hcl1 t hbs
    have h2 := sweepData_slab_le (u := u) hv'v
      (hR1cl _ (Work.Step2.closedBox_subset_closure_PBox hs c σ (le_of_eq hbs)))
    linarith [h1, h2, hhhw]
  have hclause3 : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      deriv (fun r : ℝ => inner ℝ v' (K.curve r)) t = 0 →
      h ≤ |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| := by
    intro t htmem hd
    have h1 := hnog v' hv'1 hv'e_eps t htmem hd
    linarith [h1, hhδg]
  have hclause4 : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| ≤ h →
      deriv (fun r : ℝ => (innerSL ℝ) nf (K.curve r)) t ≠ 0 := by
    intro t htmem hle
    have h1 : |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ hw := by
      have h2 := sweepData_slab_le (u := u) hv'v (hR1b _ htmem)
      linarith [h2, hle, hhhw]
    have h3 := hcl3 nf hnf1 hnfn t htmem h1
    simpa only [innerSL_apply_apply] using h3
  have hclause5 : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| = h →
      deriv (fun r : ℝ => inner ℝ v' (K.curve r)) t ≠ 0 := by
    intro t htmem heq hd
    have h1 := hnog v' hv'1 hv'e_eps t htmem hd
    rw [heq] at h1
    exact absurd hhδg (not_lt.mpr h1)
  have hclause6 : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| = h →
      (innerSL ℝ) nf (K.curve t) ∈ (exc' : Set ℝ) := by
    intro t htmem hface
    obtain ⟨t', ht'I, hKt', _⟩ := Work.Drive.Mono.exists_period_reduce K t
    have hKbox : K.curve t' ∈ Submission.PBox s c σ := by rw [hKt']; exact htmem
    have hlt_s : Submission.boxNorm c σ (K.curve t') < s :=
      (Submission.mem_PBox_iff s c σ (K.curve t')).mp hKbox
    have hface' : |inner ℝ v' (K.curve t') - (inner ℝ v' c + u)| = h := by
      rw [hKt']; exact hface
    rcases lt_or_eq_of_le ht'I.2 with hlt' | heq'
    · have hmem : (innerSL ℝ) nf (K.curve t) ∈ Fex := by
        rw [hFexdef, Finset.mem_image]
        refine ⟨t', ?_, ?_⟩
        · rw [hfaceF.mem_toFinset]
          exact ⟨⟨ht'I.1, hlt'⟩, le_of_lt hlt_s, hface'⟩
        · rw [hKt']
      exact hFex_sub (Finset.mem_coe.mpr hmem)
    · have h0 : K.curve 0 = K.curve t' := by
        rw [heq']; simpa using (K.periodic 0).symm
      have hmem : (innerSL ℝ) nf (K.curve t) ∈ Fex := by
        rw [hFexdef, Finset.mem_image]
        refine ⟨0, ?_, ?_⟩
        · rw [hfaceF.mem_toFinset]
          exact ⟨⟨le_refl 0, hpi⟩, by rw [h0]; exact le_of_lt hlt_s, by rw [h0]; exact hface'⟩
        · rw [h0, hKt']
      exact hFex_sub (Finset.mem_coe.mpr hmem)
  have hclause7 : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ Submission.PBox s c σ ∧
      inner ℝ v' (K.curve t) = inner ℝ v' c + u} ≤ B := by
    refine Work.Drive.Mono.encard_tiltedCrossings_le_flat K hε₀0
      (ENat.toENNReal_le.mp hcount) ?_ ?_ ?_ ?_
    · intro t htmem
      have hconv : inner ℝ v' (K.curve t) - (inner ℝ v' c + u)
          - ((K.curve t) (σ 2) - (c (σ 2) + u))
          = inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (K.curve t - c) := by
        rw [← Work.Drive.Mono.slabHeight_apply K c u v' t,
          ← Work.Drive.Mono.flatHeight_apply K c σ u t]
        exact Work.Drive.Mono.slabHeight_sub_flatHeight K c σ u v' t
      rw [hconv]
      have h2 : |inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (K.curve t - c)|
          ≤ (θ' + εv) * R1 := by
        refine le_trans (abs_real_inner_le_norm _ _) ?_
        exact mul_le_mul hv'e_le (hR1b _ htmem) (norm_nonneg _) (by linarith [hθ'0, hεv0])
      have h3 : (θ' + εv) * R1 < ε₀ := by
        have h4 : (θ' + εv) * R1 = θ' * R1 + εv * R1 := by ring
        linarith [h4, hθ'R1, hεvε₀, hε₀0]
      linarith [h2, h3]
    · intro t htmem hd
      have h1 := hδf t htmem hd
      linarith [h1, hε₀δf]
    · intro t htbox
      have h1 := hmboxmem t htbox
      linarith [h1, hε₀mbox]
    · intro t htmem hlt hd
      have h1 := hnog v' hv'1 hv'e_eps t htmem hd
      have hsplit : inner ℝ v' (K.curve t) - (inner ℝ v' c + u)
          = ((K.curve t) (σ 2) - (c (σ 2) + u))
            + inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (K.curve t - c) := by
        have h2 := Work.Drive.Mono.slabHeight_sub_flatHeight K c σ u v' t
        rw [Work.Drive.Mono.slabHeight_apply, Work.Drive.Mono.flatHeight_apply] at h2
        linarith
      have h3 : |inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (K.curve t - c)|
          ≤ (θ' + εv) * R1 := by
        refine le_trans (abs_real_inner_le_norm _ _) ?_
        exact mul_le_mul hv'e_le (hR1b _ htmem) (norm_nonneg _) (by linarith [hθ'0, hεv0])
      have h4 : (θ' + εv) * R1 < ε₀ := by
        have h5 : (θ' + εv) * R1 = θ' * R1 + εv * R1 := by ring
        linarith [h5, hθ'R1, hεvε₀, hε₀0]
      have h6 : |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| < δg := by
        rw [hsplit]
        have h7 := abs_add_le ((K.curve t) (σ 2) - (c (σ 2) + u))
          (inner ℝ (v' - Work.BoxShrink.shiftVσ σ 1) (K.curve t - c))
        linarith [h7, h3, h4, hlt, hε₀δg4]
      exact absurd h6 (not_lt.mpr h1)
  -- ## 12. the clauses of `GoodSweepData2`
  have hGoodnf : Work.Drive.Mono.Band.HeightGood ψ nf := by
    rw [hnfdef]
    exact hρh'good _ (lt_of_lt_of_le hnf_n' hρρh)
  have hnoEvent : ∀ p : ℝ × ℝ,
      Work.Drive.Final.IsEvent ψ s c σ u v' h ((innerSL ℝ) nf) p →
      |Work.Drive.Final.slabFn c u v' (Work.BoxShrink.Pinch.par ψ p)| < h := by
    intro p hp
    obtain ⟨hpbox, hpslab, hpcrit⟩ := hp
    by_contra hcon
    push_neg at hcon
    have hEq : |inner ℝ v' (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v' c + u)| = h :=
      le_antisymm hpslab hcon
    refine hSavoid (by
      rw [hSbaddef]
      refine Set.mem_union_left S₄ (Set.mem_union_left S₃ (Set.mem_union_left S₂ ?_))
      refine ⟨hGoodnf, p, hpbox, hpcrit, ?_⟩
      rw [show (h, τ).1 = h from rfl]
      exact hEq)
  have hfaceDev : ∀ p : ℝ × ℝ,
      Work.Drive.Final.IsFaceEvent ψ s c σ u v' h ((innerSL ℝ) nf) p →
      ∃ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p =
          t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v') p ∧
        ∀ w : ℝ × ℝ, w ≠ 0 → fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v') p w = 0 →
          (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ =>
            Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf) q
              - t * Work.Drive.Final.slabFnPar ψ c u v' q)) p) w w ≠ 0 := by
    by_contra hcon
    refine hSavoid (by
      rw [hSbaddef]
      exact Set.mem_union_left S₄ (Set.mem_union_left S₃ (Set.mem_union_right S₁ hcon)))
  have hhavoid : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s) →
      |inner ℝ v' z - (inner ℝ v' c + u)| ≠ h := by
    intro z hz hext hc
    exact hnotF (by rw [← hc]; exact hF z hz hext)
  have htriple : ∀ p : ℝ × ℝ,
      Work.Drive.Final.IsTriplePoint ψ s c σ u v' h p →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p ≠ 0 := by
    intro p hp
    exact absurd hp (not_isTriplePoint_of_cornerLevel_avoid hhavoid p)
  have hrob' : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| ≤ h →
      deriv (fun r : ℝ => inner ℝ (Work.Drive.Mono.Band.dirOf τ a₀ b₀) (K.curve r)) t ≠ 0 := by
    intro t ht hle hzero
    refine hclause4 t ht hle ?_
    rwa [show (fun r : ℝ => inner ℝ (Work.Drive.Mono.Band.dirOf τ a₀ b₀) (K.curve r))
        = (fun r : ℝ => (innerSL ℝ) nf (K.curve r)) from by
      funext r; rw [← hnfdef, innerSL_apply_apply]] at hzero
  have hoffK := Work.Drive.Mono.offK_of_notMem_offKBad (ψ := ψ) (K := K) (s := s) (c := c)
    (σ := σ) (u := u) (a₀ := a₀) (b₀ := b₀) (τ := τ) (v := v') (h := h)
    hrob' (fun hmem => hSavoid (by
      rw [hSbaddef]
      exact Set.mem_union_left S₄ (Set.mem_union_right (S₁ ∪ S₂) hmem)))
  have hscb : Work.Drive.Mono.SlabCutsBox s c σ (inner ℝ v' c + u) h v' :=
    Work.Drive.Mono.slabCutsBox_of_width hs hposh hboxw
  have hknotGP : ∀ t : ℝ, |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| = h →
      deriv (fun s : ℝ => inner ℝ v' (K.curve s)) t ≠ 0 := by
    intro t ht hd
    have ha : inner ℝ v' c + u + h ∈ Nknot ∨ inner ℝ v' c + u - h ∈ Nknot := by
      rcases le_or_gt 0 (inner ℝ v' (K.curve t) - (inner ℝ v' c + u)) with hpos | hneg
      · left
        refine ⟨t, hd, ?_⟩
        have hx : inner ℝ v' (K.curve t) - (inner ℝ v' c + u) = h := by
          rw [abs_of_nonneg hpos] at ht
          exact ht
        linarith
      · right
        refine ⟨t, hd, ?_⟩
        have hx : -(inner ℝ v' (K.curve t) - (inner ℝ v' c + u)) = h := by
          rw [abs_of_neg hneg] at ht
          exact ht
        linarith
    refine hSavoid (by
      rw [hSbaddef]
      exact Set.mem_union_right ((S₁ ∪ S₂) ∪ S₃) (by rw [hS₄def]; exact ha))
  have hGoodSweepData2 : Work.Drive.Final.GoodSweepData2 ψ K s c σ u v' h R1
      ((innerSL ℝ) nf) exc' (-(q + mw)) (q + mw) :=
    ⟨⟨hTilt', hscb.1, hscb.2, hoffK, hknotGP⟩,
      hBG, hnf_coord, hnoEvent, hfaceDev, htriple⟩
  -- ## 13. the final datum
  exact ⟨v', h, R1, (innerSL ℝ) nf, -(q + mw), q + mw, exc', hTilt', hclause2, hclause3,
    hclause4, hclause5, hclause6, hclause7,
    Work.Drive.Mono.slabCutsBox_of_width hs hposh hboxw,
    (fun y hy => hwinJ y hy), hnf_coord, hfaceReg, hJun, hGoodSweepData2⟩

end

end Work.Drive.Mono
