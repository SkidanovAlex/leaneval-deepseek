import Submission.Work.Stems.Hur2c.Faces3
import Submission.Work.Stems.Hur2c.T_const
import Submission.Work.Stems.Hur2c.T_coord
import Submission.Work.Stems.Hur2.SquareFaces

/-!
# Additivity of `T` along concatenation of paths

`Work.Stems.Hur2c.T_mul : T x₀ i (cubeOfPath (γ₁.trans γ₂)) = T x₀ i (cubeOfPath γ₁) + T x₀ i (cubeOfPath γ₂)`.

The square `Q := square_filling γ₁ γ₂ (γ₁.trans γ₂)` (whose faces are the constant at the start,
`γ₁`, `γ₂` and the composite) gives the `3`-cube `C (u,v,w) := Q (u,w)`.  Its `v`-faces are equal and
cancel, its `u`-faces are the constant at the start and `degenCube 1 (cubeOfPath γ₂)`, and its
`w`-faces are `degenCube 0 (cubeOfPath γ₁)` and `degenCube 0 (cubeOfPath (γ₁.trans γ₂))`.  So `(Y)`
reads `- T x₀ 1 γ₂ = T x₀ 0 γ₁ - T x₀ 0 (γ₁.trans γ₂)`, i.e. `T x₀ 1 γ₂ = T x₀ 0 γ₁ - T x₀ 0 (γ₁·γ₂)`;
`T_coord` (`T x₀ 1 = -T x₀ 0`) turns this into the additivity statement for `i = 0`, and the general
`i` follows by `T_coord` again.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2c

open Work.Stems.Cubical
open Work.Stems.Hur2

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem T_mul (x₀ : X) (i : Fin 2) {a b c : X} (γ₁ : Path a b) (γ₂ : Path b c) :
    T x₀ i (cubeOfPath (γ₁.trans γ₂)) =
      T x₀ i (cubeOfPath γ₁) + T x₀ i (cubeOfPath γ₂) := by
  letI : CommGroup (HomotopyGroup (Fin 2) X x₀) := HomotopyGroup.commGroup
  obtain ⟨Q, hQ00, hQ10, hQ01, hQ11⟩ := square_filling γ₁ γ₂ (γ₁.trans γ₂)
  -- identifications of `pair2`-points with the faces of the square
  have hp0 : ∀ u : unitInterval, pair2 u 0 = faceCM (1 : Fin 2) 0 (fun _ => u) := by
    intro u; ext j; fin_cases j <;>
      simp [pair2_zero, pair2_one, faceCM_apply, faceFun_apply, Fin.succAbove_cases_eq_insertNth,
        Fin.insertNth_apply_same, Fin.insertNth_apply_above, Fin.insertNth_apply_below]
  have hp1 : ∀ u : unitInterval, pair2 u 1 = faceCM (1 : Fin 2) 1 (fun _ => u) := by
    intro u; ext j; fin_cases j <;>
      simp [pair2_zero, pair2_one, faceCM_apply, faceFun_apply, Fin.succAbove_cases_eq_insertNth,
        Fin.insertNth_apply_same, Fin.insertNth_apply_above, Fin.insertNth_apply_below]
  have hq0 : ∀ u : unitInterval, pair2 0 u = faceCM (0 : Fin 2) 0 (fun _ => u) := by
    intro u; ext j; fin_cases j <;>
      simp [pair2_zero, pair2_one, faceCM_apply, faceFun_apply, Fin.succAbove_cases_eq_insertNth,
        Fin.insertNth_apply_same, Fin.insertNth_apply_above, Fin.insertNth_apply_below]
  have hq1 : ∀ u : unitInterval, pair2 1 u = faceCM (0 : Fin 2) 1 (fun _ => u) := by
    intro u; ext j; fin_cases j <;>
      simp [pair2_zero, pair2_one, faceCM_apply, faceFun_apply, Fin.succAbove_cases_eq_insertNth,
        Fin.insertNth_apply_same, Fin.insertNth_apply_above, Fin.insertNth_apply_below]
  let C : C(IC 3, X) :=
    ⟨fun p => Q (pair2 (p 0) (p 2)),
      Q.continuous.comp (continuous_pair2 (by fun_prop) (by fun_prop))⟩
  have hY := Work.Stems.Hur2b.PsiLin_cubD_single x₀ C
  have f0 : faceCube (0 : Fin 3) 0 C = ContinuousMap.const (IC 2) a := by
    ext t
    show Q (pair2 ((faceCM (0 : Fin 3) 0 t) 0) ((faceCM (0 : Fin 3) 0 t) 2)) = a
    rw [faceCM_frozen, faceCM3_0_2, hq0 (t 1)]
    exact hQ00 (fun _ => t 1)
  have f0' : faceCube (0 : Fin 3) 1 C = degenCube 1 (cubeOfPath γ₂) := by
    ext t
    show Q (pair2 ((faceCM (0 : Fin 3) 1 t) 0) ((faceCM (0 : Fin 3) 1 t) 2)) = γ₂ (t 1)
    rw [faceCM_frozen, faceCM3_0_2, hq1 (t 1)]
    exact hQ01 (fun _ => t 1)
  have f1 : faceCube (1 : Fin 3) 0 C = faceCube (1 : Fin 3) 1 C := by
    ext t
    show Q (pair2 ((faceCM (1 : Fin 3) 0 t) 0) ((faceCM (1 : Fin 3) 0 t) 2))
      = Q (pair2 ((faceCM (1 : Fin 3) 1 t) 0) ((faceCM (1 : Fin 3) 1 t) 2))
    rw [faceCM3_1_0, faceCM3_1_2, faceCM3_1_0, faceCM3_1_2]
  have f2 : faceCube (2 : Fin 3) 0 C = degenCube 0 (cubeOfPath γ₁) := by
    ext t
    show Q (pair2 ((faceCM (2 : Fin 3) 0 t) 0) ((faceCM (2 : Fin 3) 0 t) 2)) = γ₁ (t 0)
    rw [faceCM3_2_0, faceCM_frozen, hp0 (t 0)]
    exact hQ10 (fun _ => t 0)
  have f2' : faceCube (2 : Fin 3) 1 C = degenCube 0 (cubeOfPath (γ₁.trans γ₂)) := by
    ext t
    show Q (pair2 ((faceCM (2 : Fin 3) 1 t) 0) ((faceCM (2 : Fin 3) 1 t) 2))
      = (γ₁.trans γ₂) (t 0)
    rw [faceCM3_2_0, faceCM_frozen, hp1 (t 0)]
    exact hQ11 (fun _ => t 0)
  have hchain : cubD 2 X (Finsupp.single C 1)
      = (Finsupp.single (ContinuousMap.const (IC 2) a) 1
          - Finsupp.single (degenCube 1 (cubeOfPath γ₂)) 1)
        + (Finsupp.single (degenCube 0 (cubeOfPath γ₁)) 1
          - Finsupp.single (degenCube 0 (cubeOfPath (γ₁.trans γ₂))) 1) := by
    rw [cubD_single, Fin.sum_univ_three, f0, f0', f1, f2, f2']
    norm_num
  rw [hchain, map_add, map_sub, map_sub] at hY
  rw [PsiLin_single_const_degen x₀ a, zero_sub] at hY
  have h1 : T x₀ 1 (cubeOfPath γ₂)
      = T x₀ 0 (cubeOfPath γ₁) - T x₀ 0 (cubeOfPath (γ₁.trans γ₂)) := by
    have h := hY
    simp only [← T_def] at h
    have h2 : -(T x₀ 1 (cubeOfPath γ₂))
        = -(T x₀ 0 (cubeOfPath γ₁) - T x₀ 0 (cubeOfPath (γ₁.trans γ₂))) := by
      simpa only [zero_sub] using add_eq_zero_iff_eq_neg.mp h
    exact neg_inj.mp h2
  have key0 : T x₀ 0 (cubeOfPath (γ₁.trans γ₂))
      = T x₀ 0 (cubeOfPath γ₁) + T x₀ 0 (cubeOfPath γ₂) := by
    have h := h1
    rw [T_coord x₀ (cubeOfPath γ₂)] at h
    have h' : T x₀ 0 (cubeOfPath (γ₁.trans γ₂))
        = T x₀ 0 (cubeOfPath γ₂) + T x₀ 0 (cubeOfPath γ₁) := by
      rw [← sub_eq_zero] at h ⊢
      rw [show T x₀ 0 (cubeOfPath (γ₁.trans γ₂))
            - (T x₀ 0 (cubeOfPath γ₂) + T x₀ 0 (cubeOfPath γ₁))
          = -T x₀ 0 (cubeOfPath γ₂)
            - (T x₀ 0 (cubeOfPath γ₁) - T x₀ 0 (cubeOfPath (γ₁.trans γ₂))) from by abel]
      exact h
    rw [h']; abel
  fin_cases i
  · exact key0
  · show T x₀ 1 (cubeOfPath (γ₁.trans γ₂)) = T x₀ 1 (cubeOfPath γ₁) + T x₀ 1 (cubeOfPath γ₂)
    rw [T_coord x₀ (cubeOfPath (γ₁.trans γ₂)), key0, T_coord x₀ (cubeOfPath γ₁),
      T_coord x₀ (cubeOfPath γ₂)]
    abel

end

end Work.Stems.Hur2c
