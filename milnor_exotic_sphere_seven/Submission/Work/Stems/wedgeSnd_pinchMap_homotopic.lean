import Mathlib
import Submission.Work.Stems.WedgePinch

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `wedgeSnd ∘ pinchMap` is homotopic to the identity

Mirror of `Submission/Work/Stems/wedgeFst_pinchMap_homotopic.lean` for the second fold.  The cube
description of `wedgeSnd ∘ pinchMap` is

`t ↦ if (t i : ℝ) ≤ 1 / 2 then sphBase else collapseMap (sigmaB i t)`,

and it is homotopic to the identity through

`(s, t) ↦ collapseMap (update t i (projIcc ((2 - s) * t i - (1 - s))))`.
-/

open scoped Topology Topology.Homotopy unitInterval
open ContinuousMap

namespace Work.Stems

noncomputable section

variable {n : ℕ}

/-- The cube level description of `wedgeSnd ∘ pinchMap`: on the second half of the cube it is the
collapse of the reparametrised cube, on the first half it is the base point. -/
theorem wedgeSnd_pinchMap_collapse (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (t : CubeI n) :
    ((wedgeSnd (sphBase n hn)).comp (pinchMap n hn i)) (collapseMap n hn t)
      = if (t i : ℝ) ≤ 1 / 2 then sphBase n hn else collapseMap n hn (sigmaB i t) := by
  rw [ContinuousMap.comp_apply, pinchMap_apply_collapse, pinchRep]
  split_ifs <;> rfl

/-- The cube level homotopy: the `i`-th coordinate is rescaled affinely so that at `s = 0` it is
`2 t i - 1` and at `s = 1` it is `t i`. -/
def homotopyCubeFunS (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (s : I) (t : CubeI n) : sphere n :=
  collapseMap n hn (Function.update t i
    (Set.projIcc (0 : ℝ) 1 zero_le_one (((2 : ℝ) - (s : ℝ)) * (t i : ℝ) - (1 - (s : ℝ)))))

theorem continuous_homotopyCubeFunS (n : ℕ) (hn : 1 ≤ n) (i : Fin n) :
    Continuous (Function.uncurry (homotopyCubeFunS n hn i)) := by
  refine (collapseMap n hn).continuous.comp (continuous_snd.update i ?_)
  exact continuous_projIcc.comp
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))).sub
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)))

/-- The affine rescaling of the `i`-th coordinate keeps the point on the boundary. -/
theorem updateS_projIcc_mem_boundary (n : ℕ) (i : Fin n) (s : I) {t : CubeI n}
    (ht : t ∈ Cube.boundary (Fin n)) :
    Function.update t i (Set.projIcc (0 : ℝ) 1 zero_le_one
      (((2 : ℝ) - (s : ℝ)) * (t i : ℝ) - (1 - (s : ℝ)))) ∈ Cube.boundary (Fin n) := by
  obtain ⟨j, hj | hj⟩ := ht
  · refine ⟨j, Or.inl ?_⟩
    by_cases hji : j = i
    · have hi0 : t i = 0 := by rw [← hji]; exact hj
      rw [Function.update_apply, if_pos hji, hi0]
      rw [show ((0 : I) : ℝ) = 0 from rfl, mul_zero, zero_sub]
      exact projIcc_left_of_le_zero (by linarith [s.2.2])
    · rw [Function.update_apply, if_neg hji, hj]
  · refine ⟨j, Or.inr ?_⟩
    by_cases hji : j = i
    · have hi1 : t i = 1 := by rw [← hji]; exact hj
      rw [Function.update_apply, if_pos hji, hi1]
      rw [show ((1 : I) : ℝ) = 1 from rfl, mul_one, show (2 : ℝ) - (s : ℝ) - (1 - (s : ℝ)) = 1 by ring]
      exact projIcc_right_of_one_le le_rfl
    · rw [Function.update_apply, if_neg hji, hj]

theorem homotopyCubeFunS_mem_boundary (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (s : I) {t : CubeI n}
    (ht : t ∈ Cube.boundary (Fin n)) : homotopyCubeFunS n hn i s t = sphBase n hn := by
  rw [homotopyCubeFunS]
  exact collapseMap_mem_boundary n hn (updateS_projIcc_mem_boundary n i s ht)

/-- At parameter `0` the cube level homotopy is the cube description of `wedgeSnd ∘ pinchMap`. -/
theorem homotopyCubeFunS_zero (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (t : CubeI n) :
    homotopyCubeFunS n hn i 0 t
      = ((wedgeSnd (sphBase n hn)).comp (pinchMap n hn i)) (collapseMap n hn t) := by
  rw [homotopyCubeFunS, wedgeSnd_pinchMap_collapse,
    show ((2 : ℝ) - (((0 : I)) : ℝ)) = 2 from by norm_num,
    show (1 : ℝ) - (((0 : I)) : ℝ) = 1 from by norm_num]
  split_ifs with h
  · refine collapseMap_mem_boundary n hn ⟨i, Or.inl ?_⟩
    rw [Function.update_apply, if_pos rfl]
    exact projIcc_left_of_le_zero (by linarith [h])
  · rw [show (2 : ℝ) * (t i : ℝ) - 1 = 2 * (t i : ℝ) - 1 from rfl]
    rfl

/-- At parameter `1` the cube level homotopy is the collapse itself. -/
theorem homotopyCubeFunS_one (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (t : CubeI n) :
    homotopyCubeFunS n hn i 1 t = collapseMap n hn t := by
  have h2 : Set.projIcc (0 : ℝ) 1 zero_le_one (t i : ℝ) = t i := by
    rw [Set.projIcc_of_mem zero_le_one (t i).2]
  rw [homotopyCubeFunS,
    show ((2 : ℝ) - (((1 : I)) : ℝ)) = 1 from by norm_num,
    show (1 : ℝ) - (((1 : I)) : ℝ) = 0 from by norm_num,
    one_mul, sub_zero, h2, Function.update_eq_self]

theorem wedgeSnd_pinchMap_homotopic (n : ℕ) (hn : 1 ≤ n) (i : Fin n) :
    ContinuousMap.Homotopic ((wedgeSnd (sphBase n hn)).comp (pinchMap n hn i))
      (ContinuousMap.id (sphere n)) := by
  classical
  let Hf : C(I × CubeI n, sphere n) :=
    ⟨Function.uncurry (homotopyCubeFunS n hn i), continuous_homotopyCubeFunS n hn i⟩
  let Hc : C(CubeI n, C(I, sphere n)) := (Hf.comp (Homeomorph.prodComm (CubeI n) I)).curry
  have hHf : ∀ (s : I) (t : CubeI n), Hf (s, t) = homotopyCubeFunS n hn i s t := fun _ _ => rfl
  have hHc : ∀ (t : CubeI n) (s : I), Hc t s = Hf (s, t) := by
    intro t s
    simp [Hc, ContinuousMap.curry_apply, ContinuousMap.comp_apply]
  have hbound : ∀ t ∈ Cube.boundary (Fin n), Hc t = ContinuousMap.const I (sphBase n hn) := by
    intro t ht
    refine ContinuousMap.ext (fun s => ?_)
    rw [hHc t s, hHf s t, ContinuousMap.const_apply]
    exact homotopyCubeFunS_mem_boundary n hn i s ht
  have hfac : Function.FactorsThrough Hc (collapseMap n hn) := by
    intro t t' h
    rcases collapseMap_fiber n hn h with h' | ⟨ht, ht'⟩
    · rw [h']
    · rw [hbound t ht, hbound t' ht']
  let F : C(sphere n, C(I, sphere n)) := (collapseMap_isQuotientMap n hn).lift Hc hfac
  have hF : ∀ t : CubeI n, F (collapseMap n hn t) = Hc t := fun t =>
    congrFun (congrArg (fun (g : C(CubeI n, C(I, sphere n))) => (⇑g))
      (Topology.IsQuotientMap.lift_comp (collapseMap_isQuotientMap n hn) Hc hfac)) t
  let H : C(I × sphere n, sphere n) :=
    (ContinuousMap.uncurry F).comp (Homeomorph.prodComm I (sphere n))
  refine ⟨⟨H, ?_, ?_⟩⟩
  · intro y
    obtain ⟨t, rfl⟩ := (collapseMap_isQuotientMap n hn).surjective y
    show F (collapseMap n hn t) 0
      = ((wedgeSnd (sphBase n hn)).comp (pinchMap n hn i)) (collapseMap n hn t)
    rw [hF t, hHc t 0, hHf 0 t]
    exact homotopyCubeFunS_zero n hn i t
  · intro y
    obtain ⟨t, rfl⟩ := (collapseMap_isQuotientMap n hn).surjective y
    show F (collapseMap n hn t) 1 = (ContinuousMap.id (sphere n)) (collapseMap n hn t)
    rw [hF t, hHc t 1, hHf 1 t]
    exact homotopyCubeFunS_one n hn i t

end

end Work.Stems
