import Mathlib
import Submission.Work.Drive.Final.LTypes
import Submission.Work.Drive.Mono.noGraze_witness_arcs
import Submission.Work.Drive.Mono.gammaArcs_exist
import Submission.Work.Drive.Mono.gammaArc_noBend
import Submission.Work.Drive.Mono.edgeFree_of_margin
import Submission.Work.Drive.Mono.Band.exists_adapted_basis
import Submission.Work.Drive.Mono.Band.heightGood_open
import Submission.Work.Drive.Mono.arcFamilyBounds
import Submission.Work.Drive.Mono.junctionGoodAux
import Submission.Work.Drive.Mono.frontier_tiltedLevelRemoved_sphereFace

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set Filter
open scoped ENNReal _root_.Topology RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## Elementary estimates for the perturbation of the tilt direction -/

/-- **The two slab heights differ by the inner product with the difference of the directions.** -/
private lemma wdg_slab_diff (v v' x c : R3) :
    inner ℝ v x - inner ℝ v c
      = (inner ℝ v' x - inner ℝ v' c) + inner ℝ (v - v') (x - c) := by
  rw [← inner_sub_right, ← inner_sub_right, ← inner_add_left]
  congr 1
  abel

/-- **The two slab heights differ by at most `εv * R` on a ball of radius `R`.** -/
private lemma wdg_slab_le {v v' x c : R3} {εv R u : ℝ} (h : ‖v' - v‖ ≤ εv)
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
private theorem wdg_ne_smul_single {v : R3} {j j' : Fin 3} (hjj : j ≠ j')
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
private theorem wdg_ne_shiftVσ {v : R3} {σ : Equiv.Perm (Fin 3)} {j j' : Fin 3}
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
private theorem wdg_axis_perturb {σ : Equiv.Perm (Fin 3)} {v : R3} (hv : ‖v‖ = 1)
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
    exact wdg_ne_smul_single (j := m') (j' := m) hm'ne hw'm1 hw'm0 (σ i) a
  · exact wdg_ne_shiftVσ (j := m') (j' := m) hm'ne hw'm1 hw'm0

/-- **A unit vector orthogonal to `v` can be pushed into `(v')^⊥`, staying close to itself.** -/
private theorem wdg_orth_near {v v' n : R3} (hv' : ‖v'‖ = 1) (hn : ‖n‖ = 1)
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

/-! ## The witness stage of the single-level `Geom3Data` producer -/

theorem geom3_witnessData
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {r s u : ℝ}
    (hr : 0 < r) (hrs : r < s) (hs : s < (1 + Submission.eps) * r)
    (hu : |u| < Submission.eps * r)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (hcut : Work.Drive.Mono.CutTransverse K s c σ u)
    (hFC : Work.Drive.Mono.FaceCrossReg ψ c σ s u)
    (hFB : Work.Drive.Mono.FaceNoBend ψ c σ s u)
    {εg δg : ℝ} (hεg : 0 < εg) (hδg : 0 < δg)
    (hnograz : ∀ v : LeanEval.KnotTheory.PardonDistortion.R3, ‖v‖ = 1 →
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ < εg →
      ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
        δg ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|)
    (hnobend : ∀ t : ℝ, K.curve t ∈ closure (Submission.PBox s c σ) →
      (K.curve t) (σ 2) = c (σ 2) + u →
      Work.Drive.Mono.vertVel K (Work.BoxShrink.shiftVσ σ 1) t = 0 →
      Work.Drive.Mono.vertAcc K (Work.BoxShrink.shiftVσ σ 1) t = 0)
    {mE : ℝ} (hmE : 0 < mE)
    (hhedge : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      |z (σ 0) - c (σ 0)| = Submission.boxSide 0 * s →
      |z (σ 1) - c (σ 1)| = Submission.boxSide 1 * s →
      mE ≤ |z (σ 2) - (c (σ 2) + u)|) :
    ∃ (V n a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3) (ρ A B : ℝ) (N : ℕ)
      (γ : Fin N → ℝ → LeanEval.KnotTheory.PardonDistortion.R3) (η m : ℝ),
      ‖V‖ = 1 ∧
      (∀ (i : Fin 3) (a : ℝ), EuclideanSpace.single (σ i) (1 : ℝ) ≠ a • V) ∧
      ‖V - Work.BoxShrink.shiftVσ σ 1‖ ≤ 1 / 8 ∧
      ‖n‖ = 1 ∧ inner ℝ V n = 0 ∧ Work.Drive.Mono.Band.HeightGood ψ n ∧
      ‖a₀‖ = 1 ∧ ‖b₀‖ = 1 ∧ inner ℝ a₀ b₀ = 0 ∧ inner ℝ V a₀ = 0 ∧ inner ℝ V b₀ = 0 ∧
      n = (Real.sqrt 2)⁻¹ • (a₀ + b₀) ∧
      0 < ρ ∧ 0 < A ∧ A < B ∧
      A = ‖V - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) ∧
      B ≤ Work.Drive.Mono.boxWidth s σ V - |u| ∧
      B ≤ δg ∧ B ≤ mE / 2 ∧ B ≤ (Submission.boxSide 2 * s - |u|) / 2 ∧
      (∀ h ∈ Set.Ioo A B, ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
        h ≤ |Work.Drive.Final.slabFn c u V (K.curve t)|) ∧
      (∀ h ∈ Set.Ioo A B, ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        deriv (fun r : ℝ => inner ℝ V (K.curve r)) t = 0 →
        h ≤ |Work.Drive.Final.slabFn c u V (K.curve t)|) ∧
      (∀ h ∈ Set.Ioo A B, ∀ nn : LeanEval.KnotTheory.PardonDistortion.R3, ‖nn‖ = 1 →
        ‖nn - n‖ < ρ → ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        |Work.Drive.Final.slabFn c u V (K.curve t)| ≤ h →
        deriv (fun r : ℝ => inner ℝ nn (K.curve r)) t ≠ 0) ∧
      (∀ h ∈ Set.Ioo A B, ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        |Work.Drive.Final.slabFn c u V (K.curve t)| = h →
        deriv (fun r : ℝ => inner ℝ V (K.curve r)) t ≠ 0) ∧
      0 < η ∧ 0 < m ∧ B ≤ m / 2 ∧
      (∀ k, ContDiffOn ℝ 3 (γ k) (Set.Icc (-η) η)) ∧
      (∀ k, ∀ t ∈ Set.Icc (-η) η, (γ k t) (σ 2) = c (σ 2) + u + t) ∧
      (∀ k, ∃ i : Fin 3, i ≠ 2 ∧ ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ β : ℝ → ℝ × ℝ,
        ContDiffOn ℝ 3 β (Set.Icc (-η) η) ∧ ∀ t ∈ Set.Icc (-η) η,
          Work.BoxShrink.Pinch.par ψ (β t) = γ k t ∧
          (γ k t) (σ i) = c (σ i) + ε * Submission.boxSide i * s) ∧
      (∀ h ∈ Set.Ioo A B, ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
        z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → Submission.boxNorm c σ z = s →
        |Work.Drive.Final.slabFn c u V z| ≤ h →
        (∀ j : Fin 3, j ≠ 2 → ∀ j' : Fin 3, j' ≠ 2 → j ≠ j' →
          ¬ (|z (σ j) - c (σ j)| = Submission.boxSide j * s ∧
             |z (σ j') - c (σ j')| = Submission.boxSide j' * s)) →
        ∃ k, ∃ t ∈ Set.Ioo (-η) η, z = γ k t ∧ |t| ≤ 2 * h) ∧
      (∀ h ∈ Set.Ioo A B, ∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
        ∀ nn : LeanEval.KnotTheory.PardonDistortion.R3, ‖nn‖ = 1 → ‖nn - n‖ < ρ →
        inner ℝ nn (deriv (γ k) t) ≠ 0) ∧
      (∀ h ∈ Set.Ioo A B, ∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
        (1 / 2 : ℝ) ≤ inner ℝ V (deriv (γ k) t)) := by
  classical
  set e : R3 := Work.BoxShrink.shiftVσ σ 1 with hedef
  -- ## 0. elementary data
  have hs0 : 0 < s := lt_trans hr hrs
  have hs0le : 0 ≤ s := le_of_lt hs0
  have heps0 : (0 : ℝ) < Submission.eps := Submission.eps_pos
  have hu2 : |u| < Submission.boxSide 2 * s := by
    have h1 : Submission.eps * r < Submission.eps * s := mul_lt_mul_of_pos_left hrs heps0
    have he2 : Submission.eps = 2 / 13 := rfl
    have h2 : Submission.eps * s < s := by rw [he2]; nlinarith [hs0]
    have h4 : s ≤ Submission.boxSide 2 * s := by
      have h5 : (1 : ℝ) ≤ Submission.boxSide 2 := Submission.one_le_boxSide 2
      nlinarith [hs0]
    linarith
  have hbs2m2 : 0 < (Submission.boxSide 2 * s - |u|) / 2 := by linarith [hu2]
  -- ## 1. the trace arcs of the box sphere at the cutting level `u`
  obtain ⟨N, γ, η, m, hη0, hm0, hγ, hγh, hbranch, hcover⟩ :=
    Work.Drive.Mono.gammaArcs_exist ψ hs0 c σ hu2 hFC
  have hbend : ∀ k, deriv (γ k) 0 = Work.BoxShrink.shiftVσ σ 1 →
      deriv (deriv (γ k)) 0 = 0 := by
    intro k hk
    obtain ⟨i, hi, ε, hε, β, hβ, hγβ⟩ := hbranch k
    exact Work.Drive.Mono.gammaArc_noBend ψ c σ hFC hFB hη0 hi hε hβ hγβ
      (fun t ht => hγh k t ht) hk
  -- ## 2. the coordinate identity `⟪e, γ'⟫ = 1` on the interior of the parameter interval
  have hcoord_all : ∀ k (t : ℝ), t ∈ Set.Ioo (-η) η → (deriv (γ k) t) (σ 2) = 1 := by
    intro k t ht
    have hIcc : Set.Icc (-η) η ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) (fun r hr => ⟨le_of_lt hr.1, le_of_lt hr.2⟩)
    have hdiff : DifferentiableAt ℝ (γ k) t :=
      ((hγ k).contDiffAt hIcc).differentiableAt (by norm_num)
    have h1 : deriv (fun r : ℝ => (γ k r) (σ 2)) t = (deriv (γ k) t) (σ 2) := by
      have h2 : (fun r : ℝ => (γ k r) (σ 2)) = fun r : ℝ => inner ℝ (unitCoord σ 2) (γ k r) := by
        funext r; rw [inner_unitCoord]
      rw [h2, deriv_inner_apply ℝ (differentiableAt_const _) hdiff, inner_unitCoord]
      simp
    rw [← h1]
    have hEv : (fun r : ℝ => (γ k r) (σ 2)) =ᶠ[𝓝 t] fun r : ℝ => c (σ 2) + u + r := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
      exact hγh k r ⟨le_of_lt hr.1, le_of_lt hr.2⟩
    rw [Filter.EventuallyEq.deriv_eq hEv]
    simp
  -- ## 3. the numerical constants
  obtain ⟨MA1, MA2, MA4, hMA10, hMA20, hMA40, hMAspec⟩ := Work.Drive.Mono.arcFamilyBounds hη0 hγ
  set R1 : ℝ := 5 / 2 * s with hR1def
  have hR1pos : 0 < R1 := by rw [hR1def]; linarith
  set θ' : ℝ :=
    min (min (min (1 / 32) (εg / 3)) (min (1 / (16 * (MA1 + 1))) (δg / (2 * (R1 + 1)))))
      (min (min ((mE / 2) / (2 * (R1 + 1))) (((Submission.boxSide 2 * s - |u|) / 2) / (2 * (R1 + 1))))
        (min ((m / 2) / (2 * (R1 + 1))) ((η / 8) / (2 * (R1 + 1))))) with hθ'def
  have hθ'0 : 0 < θ' := by
    rw [hθ'def]; simp only [lt_min_iff]
    exact ⟨⟨⟨by norm_num, by linarith⟩, ⟨by positivity, by positivity⟩⟩,
      ⟨⟨by positivity, by positivity⟩, ⟨by positivity, by positivity⟩⟩⟩
  have hθ'1 : θ' ≤ 1 / 32 := by rw [hθ'def]; simp
  have hθ'2 : θ' ≤ εg / 3 := by rw [hθ'def]; simp
  have hθ'3 : θ' ≤ 1 / (16 * (MA1 + 1)) := by rw [hθ'def]; simp
  have hθ'4 : θ' ≤ δg / (2 * (R1 + 1)) := by rw [hθ'def]; simp
  have hθ'5 : θ' ≤ (mE / 2) / (2 * (R1 + 1)) := by rw [hθ'def]; simp
  have hθ'6 : θ' ≤ ((Submission.boxSide 2 * s - |u|) / 2) / (2 * (R1 + 1)) := by
    rw [hθ'def]; simp
  have hθ'7 : θ' ≤ (m / 2) / (2 * (R1 + 1)) := by rw [hθ'def]; simp
  have hθ'8 : θ' ≤ (η / 8) / (2 * (R1 + 1)) := by rw [hθ'def]; simp
  -- ## 4. the merged no-grazing witness for the arcs
  obtain ⟨v, n, hw, ρw, hv1, hn1, hvn, hgood, hθ'v, hvεg4, hhw0, hρw0, hhwsize,
    hcl1, hcl2, hcl3, hcl4, harcℓ, harcv⟩ :=
    Work.Drive.Mono.noGraze_witness_arcs ψ K hr hrs hu c σ hcut hεg hδg hθ'0 hnograz hnobend
      hη0 hγ hγh hbend
  rw [← hedef] at hθ'v hvεg4 hhwsize
  rw [← hR1def] at hhwsize
  obtain ⟨ρh, hρh0, hρhgood⟩ := Work.Drive.Mono.Band.heightGood_open ψ hgood
  -- ## 5. the perturbation of the tilt direction
  set εv : ℝ := min θ' (min (hw / (100 * R1)) (min (ρw / 8) (min (ρh / 8) (1 / 4)))) with hεvdef
  have hεv0 : 0 < εv := by
    rw [hεvdef]; simp only [lt_min_iff]
    exact ⟨hθ'0, ⟨by positivity, ⟨by positivity, ⟨by positivity, by norm_num⟩⟩⟩⟩
  have hεvθ : εv ≤ θ' := by rw [hεvdef]; exact min_le_left _ _
  have hεvhw : εv ≤ hw / (100 * R1) := by rw [hεvdef]; simp
  have hεvρw : εv ≤ ρw / 8 := by rw [hεvdef]; simp
  have hεvρh : εv ≤ ρh / 8 := by rw [hεvdef]; simp
  have hεv14 : εv ≤ 1 / 4 := by rw [hεvdef]; simp
  obtain ⟨v', hv'1, hv'v, haxis', hv'e0raw⟩ := wdg_axis_perturb (σ := σ) hv1 hεv0
  obtain ⟨n', hn'1, hv'n', hn'close⟩ := wdg_orth_near hv'1 hn1 hvn hv'v (by linarith [hεv14])
  have hv'ne : v' ≠ e := hv'e0raw
  have hgood' : Work.Drive.Mono.Band.HeightGood ψ n' :=
    hρhgood n' (by linarith [hn'close, hεvρh, hρh0])
  have hn'n : ‖n' - n‖ ≤ ρw / 4 := by linarith [hn'close, hεvρw, hρw0]
  have hv'e_le : ‖v' - e‖ ≤ θ' + εv := by
    have h1 : v' - e = (v' - v) + (v - e) := by abel
    calc ‖v' - e‖ ≤ ‖v' - v‖ + ‖v - e‖ := by rw [h1]; exact norm_add_le _ _
      _ ≤ εv + θ' := add_le_add hv'v hθ'v
      _ = θ' + εv := by ring
  have hv'e18 : ‖v' - e‖ ≤ 1 / 8 := by
    have h1 : εv ≤ 1 / 32 := le_trans hεvθ hθ'1
    linarith [hv'e_le, hθ'1, h1]
  have hv'e_eps : ‖v' - e‖ < εg := by
    have h1 : εv ≤ εg / 3 := le_trans hεvθ hθ'2
    linarith [hv'e_le, hθ'2, h1, hεg]
  -- ## 6. the half-width window `(A, B)`
  set A : ℝ := ‖v' - e‖ * R1 with hAdef
  have hApos : 0 < A := by
    rw [hAdef]
    exact mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hv'ne)) hR1pos
  have hA_le : A ≤ (θ' + εv) * R1 := by
    rw [hAdef]; exact mul_le_mul_of_nonneg_right hv'e_le (le_of_lt hR1pos)
  have key : ∀ c0 : ℝ, 0 < c0 → θ' ≤ c0 / (2 * (R1 + 1)) → (θ' + εv) * R1 < c0 := by
    intro c0 hc0 hc
    have hε' : εv ≤ c0 / (2 * (R1 + 1)) := le_trans hεvθ hc
    have h1 : θ' * R1 ≤ (c0 / (2 * (R1 + 1))) * R1 :=
      mul_le_mul_of_nonneg_right hc (le_of_lt hR1pos)
    have h2 : εv * R1 ≤ (c0 / (2 * (R1 + 1))) * R1 :=
      mul_le_mul_of_nonneg_right hε' (le_of_lt hR1pos)
    have h3 : (θ' + εv) * R1 = θ' * R1 + εv * R1 := by ring
    have h4 : (c0 / (2 * (R1 + 1))) * R1 * 2 < c0 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
        div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (R1 + 1))]
      nlinarith [hc0, hR1pos]
    linarith [h1, h2, h3, h4]
  have hA_δg : A < δg := lt_of_le_of_lt hA_le (key δg hδg hθ'4)
  have hA_mE : A < mE / 2 := lt_of_le_of_lt hA_le (key (mE / 2) (by linarith) hθ'5)
  have hA_bs : A < (Submission.boxSide 2 * s - |u|) / 2 :=
    lt_of_le_of_lt hA_le (key ((Submission.boxSide 2 * s - |u|) / 2) hbs2m2 hθ'6)
  have hA_m : A < m / 2 := lt_of_le_of_lt hA_le (key (m / 2) (by linarith) hθ'7)
  have hA_η : A < η / 8 := lt_of_le_of_lt hA_le (key (η / 8) (by linarith) hθ'8)
  have hA_win : A < Work.Drive.Mono.boxWidth s σ v' - |u| := by
    have h := Work.Drive.Mono.Band.window_nondegenerate s hs0 σ hv'e18 hrs hu
    rw [hAdef]
    exact h
  have hA_hwhw : A < hw - εv * R1 := by
    have hv'' : ‖v' - e‖ ≤ ‖v - e‖ + εv := by
      have h2 : v' - e = (v' - v) + (v - e) := by abel
      calc ‖v' - e‖ ≤ ‖v' - v‖ + ‖v - e‖ := by rw [h2]; exact norm_add_le _ _
        _ ≤ εv + ‖v - e‖ := add_le_add hv'v le_rfl
        _ = ‖v - e‖ + εv := by ring
    have h1 : A ≤ (‖v - e‖ + εv) * R1 := by
      rw [hAdef]; exact mul_le_mul_of_nonneg_right hv'' (le_of_lt hR1pos)
    have h1' : (‖v - e‖ + εv) * R1 = ‖v - e‖ * R1 + εv * R1 := by ring
    have h2 : ‖v - e‖ * R1 < hw / 2 := by linarith [hhwsize]
    have h3 : εv * R1 ≤ hw / 100 := by
      have h4 : εv * R1 ≤ (hw / (100 * R1)) * R1 :=
        mul_le_mul_of_nonneg_right hεvhw (le_of_lt hR1pos)
      have h5 : (hw / (100 * R1)) * R1 = hw / 100 := by field_simp
      linarith [h4, h5]
    linarith [h1, h1', h2, h3]
  set B : ℝ := min (hw - εv * R1)
      (min (Work.Drive.Mono.boxWidth s σ v' - |u|)
        (min δg (min (mE / 2) (min ((Submission.boxSide 2 * s - |u|) / 2) (min (m / 2) (η / 8))))))
    with hBdef
  have hB_hw : B ≤ hw - εv * R1 := by rw [hBdef]; exact min_le_left _ _
  have hB_win : B ≤ Work.Drive.Mono.boxWidth s σ v' - |u| := by rw [hBdef]; simp
  have hB_δg : B ≤ δg := by rw [hBdef]; simp
  have hB_mE : B ≤ mE / 2 := by rw [hBdef]; simp
  have hB_bs : B ≤ (Submission.boxSide 2 * s - |u|) / 2 := by rw [hBdef]; simp
  have hB_m : B ≤ m / 2 := by rw [hBdef]; simp
  have hB_η : B ≤ η / 8 := by rw [hBdef]; simp
  have hAB : A < B := by
    rw [hBdef]
    exact lt_min hA_hwhw (lt_min hA_win (lt_min hA_δg (lt_min hA_mE (lt_min hA_bs
      (lt_min hA_m hA_η)))))
  -- ## 7. the robustness radius
  set ρ : ℝ := ρw / 4 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hρ_close : ρ + ‖n' - n‖ < ρw := by rw [hρdef]; linarith [hn'n, hρw0]
  -- ## 8. the adapted orthonormal basis of `v'^⊥`
  obtain ⟨a₀, b₀, ha₀1, hb₀1, ha₀b₀, hv'a₀, hv'b₀, hn'b⟩ :=
    Work.Drive.Mono.Band.exists_adapted_basis hv'1 hn'1 hv'n'
  -- ## 9. the no-grazing clauses at the perturbed tilt
  have hcl1' : ∀ h ∈ Set.Ioo A B, ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
      h ≤ |Work.Drive.Final.slabFn c u v' (K.curve t)| := by
    intro h hh t hbs
    have hx : ‖K.curve t - c‖ ≤ R1 := by
      rw [hR1def]
      exact Work.Drive.Mono.norm_sub_le_of_mem_closure_PBox hs0le
        (Work.Drive.Mono.mem_closure_PBox_of_boxNorm_le hs0 c σ (le_of_eq hbs))
    have h2 := wdg_slab_le (v := v) (v' := v') (x := K.curve t) (c := c) (εv := εv) (R := R1)
      (u := u) hv'v hx
    have h3 : h + εv * R1 < hw := by
      have h4 : h < B := hh.2
      have h5 : B ≤ hw - εv * R1 := hB_hw
      linarith
    simp only [Work.Drive.Final.slabFn]
    linarith [hcl1 t hbs, h2, h3]
  have hcl2' : ∀ h ∈ Set.Ioo A B, ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      deriv (fun r : ℝ => inner ℝ v' (K.curve r)) t = 0 →
      h ≤ |Work.Drive.Final.slabFn c u v' (K.curve t)| := by
    intro h hh t htmem hd
    have h1 := hnograz v' hv'1 hv'e_eps t htmem hd
    have h2 : h < δg := lt_of_lt_of_le hh.2 hB_δg
    simp only [Work.Drive.Final.slabFn]
    linarith
  have hcl3' : ∀ h ∈ Set.Ioo A B, ∀ nn : R3, ‖nn‖ = 1 → ‖nn - n'‖ < ρ →
      ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |Work.Drive.Final.slabFn c u v' (K.curve t)| ≤ h →
      deriv (fun r : ℝ => inner ℝ nn (K.curve r)) t ≠ 0 := by
    intro h hh nn hnn1 hnnn t htmem hle
    have hx : ‖K.curve t - c‖ ≤ R1 := by
      rw [hR1def]
      exact Work.Drive.Mono.norm_sub_le_of_mem_PBox hs0le htmem
    have h2 := wdg_slab_le (v := v) (v' := v') (x := K.curve t) (c := c) (εv := εv) (R := R1)
      (u := u) hv'v hx
    have hle' : |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| ≤ h := by
      simpa only [Work.Drive.Final.slabFn] using hle
    have h3 : |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ hw := by
      have h4 : h + εv * R1 < hw := by
        have h5 : h < B := hh.2
        have h6 : B ≤ hw - εv * R1 := hB_hw
        linarith
      linarith [h2, hle', h4]
    have h8 : ‖nn - n‖ < ρw := by
      have h9 : nn - n = (nn - n') + (n' - n) := by abel
      have h10 : ‖nn - n‖ ≤ ‖nn - n'‖ + ‖n' - n‖ := by rw [h9]; exact norm_add_le _ _
      have h12 : ρ + ‖n' - n‖ < ρw := hρ_close
      linarith
    exact hcl3 nn hnn1 h8 t htmem h3
  have hcl4' : ∀ h ∈ Set.Ioo A B, ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |Work.Drive.Final.slabFn c u v' (K.curve t)| = h →
      deriv (fun r : ℝ => inner ℝ v' (K.curve r)) t ≠ 0 := by
    intro h hh t htmem heq hd
    have h1 := hnograz v' hv'1 hv'e_eps t htmem hd
    have h2 : h < δg := lt_of_lt_of_le hh.2 hB_δg
    have h3 : |inner ℝ v' (K.curve t) - (inner ℝ v' c + u)| = h := by
      simpa only [Work.Drive.Final.slabFn] using heq
    linarith
  -- ## 10. the cover by the arcs
  have hcover' : ∀ h ∈ Set.Ioo A B, ∀ z : R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → Submission.boxNorm c σ z = s →
      |Work.Drive.Final.slabFn c u v' z| ≤ h →
      (∀ j : Fin 3, j ≠ 2 → ∀ j' : Fin 3, j' ≠ 2 → j ≠ j' →
        ¬ (|z (σ j) - c (σ j)| = Submission.boxSide j * s ∧
           |z (σ j') - c (σ j')| = Submission.boxSide j' * s)) →
      ∃ k, ∃ t ∈ Set.Ioo (-η) η, z = γ k t ∧ |t| ≤ 2 * h := by
    intro h hh z hz hzn hslab hnoext
    have hx : ‖z - c‖ ≤ R1 := by
      rw [hR1def]
      exact Work.Drive.Mono.norm_sub_le_of_mem_closure_PBox hs0le
        (Work.Drive.Mono.mem_closure_PBox_of_boxNorm_le hs0 c σ (le_of_eq hzn))
    have hdiff : |z (σ 2) - (c (σ 2) + u)|
        ≤ |inner ℝ v' z - (inner ℝ v' c + u)| + ‖v' - e‖ * R1 := by
      have h1 := wdg_slab_le (v := e) (v' := v') (x := z) (c := c) (εv := ‖v' - e‖) (R := R1)
        (u := u) (le_refl _) hx
      rwa [Work.Drive.Mono.inner_shiftVσ_one σ z, Work.Drive.Mono.inner_shiftVσ_one σ c] at h1
    have hslab' : |inner ℝ v' z - (inner ℝ v' c + u)| ≤ h := by
      simpa only [Work.Drive.Final.slabFn] using hslab
    have hA' : ‖v' - e‖ * R1 < h := by
      rw [← hAdef]; exact hh.1
    have hle2h : |z (σ 2) - (c (σ 2) + u)| ≤ 2 * h := by linarith [hdiff, hslab', hA']
    have hflat : |z (σ 2) - (c (σ 2) + u)| < m := by
      have h2 : h < m / 2 := lt_of_lt_of_le hh.2 hB_m
      linarith
    obtain ⟨k, t, htIoo, hzt⟩ := hcover z hz hzn hflat hnoext
    refine ⟨k, t, htIoo, hzt, ?_⟩
    have hzt' : z (σ 2) = c (σ 2) + u + t := by
      rw [hzt]; exact hγh k t ⟨le_of_lt htIoo.1, le_of_lt htIoo.2⟩
    have ht_eq : |t| = |z (σ 2) - (c (σ 2) + u)| := by
      rw [hzt', show c (σ 2) + u + t - (c (σ 2) + u) = t by ring]
    rw [ht_eq]
    exact hle2h
  -- ## 11. the arc clauses
  have harc_nn : ∀ h ∈ Set.Ioo A B, ∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
      ∀ nn : R3, ‖nn‖ = 1 → ‖nn - n'‖ < ρ → inner ℝ nn (deriv (γ k) t) ≠ 0 := by
    intro h hh k t htIoo ht2h nn hnn1 hnnn
    have h1 : |t| ≤ 2 * hw := by
      have h2 : h < B := hh.2
      have h3 : B ≤ hw - εv * R1 := hB_hw
      have h4 : 0 < εv * R1 := by positivity
      linarith
    have h3 : ‖nn - n‖ < ρw := by
      have h4 : nn - n = (nn - n') + (n' - n) := by abel
      have h5 : ‖nn - n‖ ≤ ‖nn - n'‖ + ‖n' - n‖ := by rw [h4]; exact norm_add_le _ _
      have h6 : ρ + ‖n' - n‖ < ρw := hρ_close
      linarith
    exact harcℓ k t htIoo h1 nn hnn1 h3
  have harc_slope : ∀ h ∈ Set.Ioo A B, ∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
      (1 / 2 : ℝ) ≤ inner ℝ v' (deriv (γ k) t) := by
    intro h hh k t htIoo ht2h
    have htη : |t| ≤ η / 2 := by
      have h1 : 2 * h < η / 4 := by
        have h2 : h < η / 8 := lt_of_lt_of_le hh.2 hB_η
        linarith
      linarith
    have hM1 : ‖deriv (γ k) t‖ ≤ MA1 := (hMAspec k t htIoo htη).1
    have hcoord : inner ℝ e (deriv (γ k) t) = 1 := by
      rw [Work.Drive.Mono.inner_shiftVσ_one]
      exact hcoord_all k t htIoo
    have hsplit : inner ℝ v' (deriv (γ k) t)
        = inner ℝ e (deriv (γ k) t) + inner ℝ (v' - e) (deriv (γ k) t) := by
      rw [← inner_add_left]; congr 1; abel
    have hbd : |inner ℝ (v' - e) (deriv (γ k) t)| ≤ ‖v' - e‖ * MA1 :=
      le_trans (abs_real_inner_le_norm _ _) (mul_le_mul_of_nonneg_left hM1 (norm_nonneg _))
    have hsmallM : ‖v' - e‖ * MA1 ≤ 1 / 4 := by
      have h1 : ‖v' - e‖ * MA1 ≤ (θ' + εv) * MA1 :=
        mul_le_mul_of_nonneg_right hv'e_le (le_of_lt hMA10)
      have h1' : (θ' + εv) * MA1 = θ' * MA1 + εv * MA1 := by ring
      have h2 : εv * MA1 ≤ θ' * MA1 := mul_le_mul_of_nonneg_right hεvθ (le_of_lt hMA10)
      have h3 : θ' * MA1 ≤ (1 / (16 * (MA1 + 1))) * MA1 :=
        mul_le_mul_of_nonneg_right hθ'3 (le_of_lt hMA10)
      have h4 : (1 / (16 * (MA1 + 1))) * MA1 ≤ 1 / 16 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hMA10]
      linarith
    rw [hsplit, hcoord]
    have h5 := (abs_le.mp hbd).1
    linarith
  -- ## 12. the datum
  refine ⟨v', n', a₀, b₀, ρ, A, B, N, γ, η, m, ?_⟩
  refine ⟨hv'1, haxis', hv'e18, hn'1, hv'n', hgood', ha₀1, hb₀1, ha₀b₀, hv'a₀, hv'b₀,
    hn'b, hρ0, hApos, hAB, ?_, hB_win, hB_δg, hB_mE, hB_bs, hcl1', hcl2', hcl3', hcl4',
    hη0, hm0, hB_m, hγ, hγh, hbranch, hcover', harc_nn, harc_slope⟩
  rw [hAdef, hR1def]

end

end Work.Drive.Mono
