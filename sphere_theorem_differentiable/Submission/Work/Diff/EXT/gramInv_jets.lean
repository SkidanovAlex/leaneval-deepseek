import Mathlib
import Submission.Work.Diff.EXT.chartData_step_aux
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv
import Submission.Work.Diff.EXT.gramInv_jets_det

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

theorem gramInv_jets
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E) (k : ℕ)
    (hKt : K ⊆ (extChartAt I x₀).target)
    (hdet : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      c ≤ (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y)).det)
    (hsm : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.GramM G x₀ t
        (pt (I := I) x₀ y') i j) y)
    (hM : ∀ m ≤ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.GramM G x₀ t
          (pt (I := I) x₀ y') i j) y‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ m ≤ k,
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.GramInv G x₀ t
          (pt (I := I) x₀ y') i j) y‖ ≤ C := by
  classical
  obtain ⟨c, hc0, hc⟩ := hdet
  obtain ⟨CM, hCM0, hCM⟩ := exists_uniform_bound_of_le
    (P := fun m C => ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.GramM G x₀ t
        (pt (I := I) x₀ y') i j) y‖ ≤ C)
    (fun m C C' h hle t ht y hy i j => le_trans (h t ht y hy i j) hle) k hM
  set B : ℝ := max 1 CM with hBdef
  have hB0 : 0 ≤ B := le_trans zero_le_one (le_max_left _ _)
  have hCMB : CM ≤ B := le_max_right _ _
  have h1B : (1 : ℝ) ≤ B := le_max_left _ _
  obtain ⟨Cd, hCd0, hCd⟩ := exists_det_jets_bound (E := E) k B hB0
  obtain ⟨Cr, hCr0, hCr⟩ := exists_bound_inv_jets (E := E) k c Cd hc0 hCd0
  -- the smoothness of the determinant and of the adjugate entries
  have hMsm : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => fun r c' : Fin (Module.finrank ℝ E) =>
        Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') r c') y := by
    intro t ht y hy
    rw [contDiffAt_pi]
    intro r
    rw [contDiffAt_pi]
    intro c'
    exact hsm t ht y hy r c'
  have hdet_sm : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y')).det) y := by
    intro t ht y hy
    have h1 := (contDiff_matrix_det_pi (n := Module.finrank ℝ E)).contDiffAt.comp y (hMsm t ht y hy)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y' => ?_)
    show (Matrix.of (fun r c' : Fin (Module.finrank ℝ E) =>
      Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') r c')).det
        = (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y')).det
    have hmat : (Matrix.of (fun r c' : Fin (Module.finrank ℝ E) =>
        Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') r c'))
        = Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') := by
      ext r c'
      rw [Matrix.of_apply]
    rw [hmat]
  have hadj_sm : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => (Work.Diff.GE.GramM G x₀ t
        (pt (I := I) x₀ y')).adjugate i j) y := by
    intro t ht y hy i j
    have h1 := (contDiff_matrix_adjugate_entry_pi (n := Module.finrank ℝ E) i j).contDiffAt.comp y
      (hMsm t ht y hy)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y' => ?_)
    show (Matrix.of (fun r c' : Fin (Module.finrank ℝ E) =>
      Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') r c')).adjugate i j
        = (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y')).adjugate i j
    have hmat : (Matrix.of (fun r c' : Fin (Module.finrank ℝ E) =>
        Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') r c'))
        = Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') := by
      ext r c'
      rw [Matrix.of_apply]
    rw [hmat]
  -- the jet bound for the adjugate entries
  have hAdj : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j : Fin (Module.finrank ℝ E)) (m : ℕ), m ≤ k →
      ‖iteratedFDeriv ℝ m (fun y' : E => (Work.Diff.GE.GramM G x₀ t
        (pt (I := I) x₀ y')).adjugate i j) y‖ ≤ Cd := by
    intro t ht y hy i j m hm
    let A : E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      fun y' => (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y')).updateRow j
        ((Pi.single i (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ))
    have hAentry : ∀ (r c' : Fin (Module.finrank ℝ E)) (y' : E),
        A y' r c' = if r = j then (Pi.single i (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ) c'
          else Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') r c' := by
      intro r c' y'
      change (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y')).updateRow j
        ((Pi.single i (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ)) r c'
        = if r = j then (Pi.single i (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ) c'
          else Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') r c'
      rw [Matrix.updateRow_apply]
    have hid : (fun y' : E => (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y')).adjugate i j)
        = fun y' : E => (A y').det := by
      funext y'
      exact Matrix.adjugate_apply (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y')) i j
    rw [hid]
    refine hCd A y ?_ ?_ m hm
    · intro r c'
      have h2 : (fun y' : E => A y' r c') = fun y' : E =>
          (if r = j then (Pi.single i (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ) c'
            else Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') r c') := by
        funext y'
        exact hAentry r c' y'
      rw [h2]
      by_cases hr : r = j
      · have h3 : (fun y' : E => (if r = j then (Pi.single i (1 : ℝ) :
            Fin (Module.finrank ℝ E) → ℝ) c' else Work.Diff.GE.GramM G x₀ t
              (pt (I := I) x₀ y') r c'))
            = fun _ : E => (Pi.single i (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ) c' := by
          funext y'
          simp only [if_pos hr]
        rw [h3]
        exact contDiffAt_const
      · have h3 : (fun y' : E => (if r = j then (Pi.single i (1 : ℝ) :
            Fin (Module.finrank ℝ E) → ℝ) c' else Work.Diff.GE.GramM G x₀ t
              (pt (I := I) x₀ y') r c'))
            = fun y' : E => Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') r c' := by
          funext y'
          simp only [if_neg hr]
        rw [h3]
        exact hsm t ht y hy r c'
    · intro r c' m' hm'
      have h2 : (fun y' : E => A y' r c') = fun y' : E =>
          (if r = j then (Pi.single i (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ) c'
            else Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') r c') := by
        funext y'
        exact hAentry r c' y'
      rw [h2]
      by_cases hr : r = j
      · have h3 : (fun y' : E => (if r = j then (Pi.single i (1 : ℝ) :
            Fin (Module.finrank ℝ E) → ℝ) c' else Work.Diff.GE.GramM G x₀ t
              (pt (I := I) x₀ y') r c'))
            = fun _ : E => (Pi.single i (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ) c' := by
          funext y'
          simp only [if_pos hr]
        rw [h3]
        by_cases hm0 : m' = 0
        · subst hm0
          rw [norm_iteratedFDeriv_zero]
          have h4 : ‖(Pi.single i (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ) c'‖ ≤ 1 := by
            by_cases hc' : c' = i
            · subst hc'; simp
            · rw [Pi.single_eq_of_ne hc']; simp
          exact le_trans h4 h1B
        · rw [iteratedFDeriv_const_of_ne hm0]
          simpa using hB0
      · have h3 : (fun y' : E => (if r = j then (Pi.single i (1 : ℝ) :
            Fin (Module.finrank ℝ E) → ℝ) c' else Work.Diff.GE.GramM G x₀ t
              (pt (I := I) x₀ y') r c'))
            = fun y' : E => Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') r c' := by
          funext y'
          simp only [if_neg hr]
        rw [h3]
        exact le_trans (hCM m' hm' t ht y hy r c') hCMB

  -- the jet bound for the reciprocal of the determinant
  have hRec : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ m ≤ k,
      ‖iteratedFDeriv ℝ m (fun y' : E => (Work.Diff.GE.GramM G x₀ t
        (pt (I := I) x₀ y')).det⁻¹) y‖ ≤ Cr := by
    intro t ht y hy m hm
    exact hCr _ y (hdet_sm t ht y hy) (hc t ht y hy)
      (fun m' hm' => hCd _ y (fun r c' => hsm t ht y hy r c')
        (fun r c' m'' hm'' => le_trans (hCM m'' hm'' t ht y hy r c') hCMB) m' hm') m hm
  -- the main bound
  set Cfin : ℝ := (2 : ℝ) ^ k * (max Cr Cd) * (max Cr Cd) with hCfindef
  refine ⟨Cfin, ?_, fun t ht y hy m hm i j => ?_⟩
  · rw [hCfindef]; positivity
  · have hid : (fun y' : E => Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y') i j)
        = fun y' : E => (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y')).det⁻¹
            * (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y')).adjugate i j := by
      funext y'
      rw [Work.Diff.GE.GramInv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
      congr 1
      exact congrFun Ring.inverse_eq_inv' _
    rw [hid]
    rw [hCfindef]
    have hrec_sm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => (Work.Diff.GE.GramM G x₀ t
        (pt (I := I) x₀ y')).det⁻¹) y :=
      (hdet_sm t ht y hy).inv (by
        show ((fun y' : E => (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y')).det) y) ≠ 0
        rw [show ((fun y' : E => (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y')).det) y)
            = (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y)).det from rfl]
        exact ne_of_gt (lt_of_lt_of_le hc0 (hc t ht y hy)))
    refine le_trans (norm_iteratedFDeriv_mul_le_at_le (k := m) (m := m) (B := max Cr Cd) le_rfl
      hrec_sm (hadj_sm t ht y hy i j) (le_trans hCr0 (le_max_left _ _))
      (fun m' hm' => le_trans (hRec t ht y hy m' (by omega)) (le_max_left _ _))
      (fun m' hm' => le_trans (hAdj t ht y hy i j m' (by omega)) (le_max_right _ _))) ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (by omega : m ≤ k)) (by positivity))
      (by positivity)


end Work.Diff.EXT
