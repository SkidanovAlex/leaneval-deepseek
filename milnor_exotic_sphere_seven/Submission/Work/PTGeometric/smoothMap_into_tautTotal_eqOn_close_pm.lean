import Mathlib
import Submission.Work.PTGeometric.smoothMap_into_tautTotal_eqOn_close
import Submission.Work.PTGeometric.SmoothToTautEqOn
import Submission.Work.PTGeometric.exists_Rmap_lipschitz

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: G2 with the values prescribed on a closed end `S`, the vector part only close,
and the smoothed matrix part returned

This is `Work.PTGeometric.smoothMap_into_tautTotal_eqOn_close` with two additions in the
conclusion: the smoothed matrix part `Pm` is returned together with the bound
`‖Pm x - P x‖ < 1/8`, and the resulting projection is *identified* as `Rmap (Pm x)`.  The proof
is literally the proof of the closeness version: smooth both components with error `δ ≤ 1/8`
(`smoothApprox_eqOn_normedSpace`, keeping the values on `S`), retract the matrix part with the
Riesz projection `Rmap` (applicable because the smoothed matrix is within `1/8 < 1/4` of the
projection `P x`), and re-project the vector part; the Lipschitz hypothesis on `Rmap` controls
`‖v' x - v x‖` by `δ (1 + L ‖v x‖)`, and `δ` is chosen small against the uniform bound on `‖v‖`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

theorem smoothMap_into_tautTotal_eqOn_close_pm (n k : ℕ) (hk : k ≤ n) (hk0 : 0 < k) (M : Type)
    [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [CompactSpace M] [T2Space M]
    (P : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : M → EuclideanSpace ℝ (Fin n))
    (hP : Continuous P) (hv : Continuous v)
    (S : Set M) (hSclosed : IsClosed S)
    (V : Set M) (hVopen : IsOpen V) (hSV : S ⊆ V)
    (hPV : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) P V)
    (hvV : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) v V)
    (hProj : ∀ x : M, P x ∈ Work.PTGeometric.Gr n k)
    (hMem : ∀ x : M, P x (v x) = v x)
    (L : NNReal)
    (hL : ∀ A Q : Work.PTGeometric.EndOp n, Q ∈ Work.PTGeometric.Gr n k →
      ‖A - Q‖ ≤ 1 / 8 → ‖Work.PTGeometric.Rmap A - Q‖ ≤ (L : ℝ) * ‖A - Q‖)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (P' : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (v' : M → EuclideanSpace ℝ (Fin n))
      (Pm : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) P' ∧
      ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) v' ∧
      ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) Pm ∧
      (∀ x : M, ‖Pm x - P x‖ < 1 / 8) ∧
      (∀ x : M, P' x = Work.PTGeometric.Rmap (Pm x)) ∧
      (∀ x : M, P' x ∈ Work.PTGeometric.Gr n k ∧ P' x (v' x) = v' x) ∧
      (∀ x ∈ S, P' x = P x ∧ v' x = v x) ∧
      (∀ x : M, ‖v' x - v x‖ < ε) := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  set B' : ℝ := max B 0 with hB'def
  have hB'0 : 0 ≤ B' := le_max_right B 0
  have hB'mem : ∀ x : M, ‖v x‖ ≤ B' := fun x => le_trans (hB x (mem_univ x)) (le_max_left B 0)
  -- the precision: small enough that `δ * (1 + L * B') < ε`
  set c : ℝ := (L : ℝ) * B' + 1 with hcdef
  have hc : 0 < c := by rw [hcdef]; nlinarith [NNReal.coe_nonneg L, hB'0]
  set δ : ℝ := min (1 / 8) (ε / (2 * c)) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    exact lt_min (by norm_num) (div_pos hε (by linarith))
  have hδ8 : δ ≤ 1 / 8 := by rw [hδdef]; exact min_le_left _ _
  have hδc : δ * c < ε := by
    have hle : δ ≤ ε / (2 * c) := by rw [hδdef]; exact min_le_right _ _
    have hmul : δ * c ≤ (ε / (2 * c)) * c := mul_le_mul_of_nonneg_right hle (le_of_lt hc)
    have hval : (ε / (2 * c)) * c = ε / 2 := by field_simp
    linarith
  -- smooth both components, keeping the values on `S`
  obtain ⟨Pm, hPm_sm, hPm_eq, hPm_close⟩ :=
    smoothApprox_eqOn_normedSpace (k := k) M P hP S hSclosed V hVopen hSV hPV δ hδ
  obtain ⟨vm, hvm_sm, hvm_eq, hvm_close⟩ :=
    smoothApprox_eqOn_normedSpace (k := k) M v hv S hSclosed V hVopen hSV hvV δ hδ
  have hgood : ∀ x : M, Pm x ∈ good n k := by
    intro x
    refine good_of_dist (hProj x) ?_
    have h1 : ‖Pm x - P x‖ < 1 / 8 := lt_of_lt_of_le (hPm_close x) hδ8
    linarith
  -- retract the matrix part with `Rmap` and re-project the vector part
  have hP'_sm : ContMDiff (𝓡∂ ((8 + k) + 1))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun x : M => Rmap (Pm x)) :=
    ContMDiffOn.comp_contMDiff (g := fun A : EndOp n => Rmap A) (t := good n k)
      (contDiffOn_Rmap n k).contMDiffOn hPm_sm hgood
  have hv'_sm : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun x : M => Rmap (Pm x) (vm x)) :=
    hP'_sm.clm_apply hvm_sm
  refine ⟨fun x => Rmap (Pm x), fun x => Rmap (Pm x) (vm x), Pm,
    hP'_sm, hv'_sm, hPm_sm, ?_, ?_, ?_, ?_, ?_⟩
  · -- the smoothed matrix part is within `1/8` of `P`
    intro x
    exact lt_of_lt_of_le (hPm_close x) hδ8
  · -- the matrix part is exactly the retraction of the smoothed part
    intro x
    rfl
  · -- the values lie in the total space of the tautological bundle
    intro x
    have hgr : Rmap (Pm x) ∈ Gr n k := Rmap_mem_Gr_of_mem_good (hgood x)
    exact ⟨hgr, by rw [← mul_apply_eq_comp, hgr.2.1]⟩
  · -- the values on `S` are unchanged
    intro x hx
    have hPmx : Pm x = P x := hPm_eq x hx
    have hvmx : vm x = v x := hvm_eq x hx
    obtain ⟨hb1, hb2, hb3⟩ := hProj x
    refine ⟨?_, ?_⟩
    · show Rmap (Pm x) = P x
      rw [hPmx]
      exact Rmap_eq_self_of_mem_Gr ⟨hb1, hb2, hb3⟩
    · have hrP : Rmap (P x) = P x := Rmap_eq_self_of_mem_Gr ⟨hb1, hb2, hb3⟩
      show Rmap (Pm x) (vm x) = v x
      rw [hPmx, hvmx, hrP]
      exact hMem x
  · -- the vector part is within `ε` of `v`
    intro x
    have hrGr : Rmap (Pm x) ∈ Gr n k := Rmap_mem_Gr_of_mem_good (hgood x)
    have h8 : ‖Pm x - P x‖ ≤ 1 / 8 := le_of_lt (lt_of_lt_of_le (hPm_close x) hδ8)
    have hP'x : ‖Rmap (Pm x) - P x‖ ≤ (L : ℝ) * δ :=
      calc ‖Rmap (Pm x) - P x‖ ≤ (L : ℝ) * ‖Pm x - P x‖ := hL (Pm x) (P x) (hProj x) h8
        _ ≤ (L : ℝ) * δ :=
            mul_le_mul_of_nonneg_left (le_of_lt (hPm_close x)) (NNReal.coe_nonneg L)
    have hA : ‖Rmap (Pm x) (vm x - v x)‖ ≤ δ :=
      calc ‖Rmap (Pm x) (vm x - v x)‖ ≤ ‖Rmap (Pm x)‖ * ‖vm x - v x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * δ := mul_le_mul (norm_le_one_of_mem_Gr hrGr) (le_of_lt (hvm_close x))
            (norm_nonneg _) (by norm_num)
        _ = δ := one_mul δ
    have hBd : ‖Rmap (Pm x) (v x) - v x‖ ≤ (L : ℝ) * δ * B' := by
      have hsub : Rmap (Pm x) (v x) - v x = (Rmap (Pm x) - P x) (v x) := by
        rw [sub_apply, hMem x]
      rw [hsub]
      calc ‖(Rmap (Pm x) - P x) (v x)‖ ≤ ‖Rmap (Pm x) - P x‖ * ‖v x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ((L : ℝ) * δ) * B' := mul_le_mul hP'x (hB'mem x) (norm_nonneg _)
            (by nlinarith [NNReal.coe_nonneg L, hδ])
    have hsplit : Rmap (Pm x) (vm x) - v x
        = Rmap (Pm x) (vm x - v x) + (Rmap (Pm x) (v x) - v x) := by
      rw [map_sub]
      abel
    calc ‖Rmap (Pm x) (vm x) - v x‖
        = ‖Rmap (Pm x) (vm x - v x) + (Rmap (Pm x) (v x) - v x)‖ := by rw [hsplit]
      _ ≤ ‖Rmap (Pm x) (vm x - v x)‖ + ‖Rmap (Pm x) (v x) - v x‖ := norm_add_le _ _
      _ ≤ δ + (L : ℝ) * δ * B' := add_le_add hA hBd
      _ = δ * c := by rw [hcdef]; ring
      _ < ε := hδc

end

end Work.PTGeometric
