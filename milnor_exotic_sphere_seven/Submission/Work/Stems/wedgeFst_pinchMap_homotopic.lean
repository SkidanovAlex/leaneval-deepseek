import Mathlib
import Submission.Work.Stems.WedgePinch

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `wedgeFst ∘ pinchMap` is homotopic to the identity

The pinch `pinchMap n hn i : Sⁿ → Sⁿ ∨ Sⁿ` sends the first half of the cube to the first
summand of the wedge (via the reparametrisation `sigmaA`) and the second half to the second
summand (via `sigmaB`).  Composing with the first fold `wedgeFst` therefore gives the map whose
cube description is

`t ↦ if (t i : ℝ) ≤ 1 / 2 then collapseMap (sigmaA i t) else sphBase`.

Geometrically this map collapses the closed "second half" of `Sⁿ` (a ball) to the base point and
is the collapse map on the first half; it is homotopic to the identity through the homotopy which
continuously moves the cut point from `1` (at parameter `0`) to `1 / 2` (at parameter `1`):

`(s, t) ↦ collapseMap (update t i (projIcc ((2 - s) * t i)))`.

The homotopy is constant on the fibres of the collapse `Iⁿ → Sⁿ` and therefore descends; as in
`Work.Stems.cubeLift_homotopic_of_homotopicRel` we descend the curried homotopy to a map
`Sⁿ → C(I, Sⁿ)` and then uncurry.
-/

open scoped Topology Topology.Homotopy unitInterval
open ContinuousMap

namespace Work.Stems

noncomputable section

variable {n : ℕ}

/-- The cube level description of `wedgeFst ∘ pinchMap`: on the first half of the cube it is the
collapse of the reparametrised cube, on the second half it is the base point. -/
theorem wedgeFst_pinchMap_collapse (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (t : CubeI n) :
    ((wedgeFst (sphBase n hn)).comp (pinchMap n hn i)) (collapseMap n hn t)
      = if (t i : ℝ) ≤ 1 / 2 then collapseMap n hn (sigmaA i t) else sphBase n hn := by
  rw [ContinuousMap.comp_apply, pinchMap_apply_collapse, pinchRep]
  split_ifs <;> rfl

/-- The cube level homotopy: the `i`-th coordinate is rescaled by `2 - s`, `s ∈ I`. -/
def homotopyCubeFun (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (s : I) (t : CubeI n) : sphere n :=
  collapseMap n hn (Function.update t i
    (Set.projIcc (0 : ℝ) 1 zero_le_one (((2 : ℝ) - (s : ℝ)) * (t i : ℝ))))

theorem continuous_homotopyCubeFun (n : ℕ) (hn : 1 ≤ n) (i : Fin n) :
    Continuous (Function.uncurry (homotopyCubeFun n hn i)) := by
  refine (collapseMap n hn).continuous.comp (continuous_snd.update i ?_)
  exact continuous_projIcc.comp
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)))

/-- Rescaling the `i`-th coordinate keeps the point on the boundary of the cube. -/
theorem update_projIcc_mem_boundary (n : ℕ) (i : Fin n) (s : I) {t : CubeI n}
    (ht : t ∈ Cube.boundary (Fin n)) :
    Function.update t i (Set.projIcc (0 : ℝ) 1 zero_le_one (((2 : ℝ) - (s : ℝ)) * (t i : ℝ)))
      ∈ Cube.boundary (Fin n) := by
  obtain ⟨j, hj | hj⟩ := ht
  · refine ⟨j, Or.inl ?_⟩
    by_cases hji : j = i
    · have hi0 : t i = 0 := by rw [← hji]; exact hj
      rw [Function.update_apply, if_pos hji]
      simp [hi0]
    · rw [Function.update_apply, if_neg hji, hj]
  · refine ⟨j, Or.inr ?_⟩
    by_cases hji : j = i
    · have hi1 : t i = 1 := by rw [← hji]; exact hj
      rw [Function.update_apply, if_pos hji]
      rw [hi1, show (((1 : I) : ℝ)) = 1 from rfl, mul_one]
      exact projIcc_right_of_one_le (by linarith [s.2.2])
    · rw [Function.update_apply, if_neg hji, hj]

/-- The cube level homotopy is constant (equal to the base point) on the boundary. -/
theorem homotopyCubeFun_mem_boundary (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (s : I) {t : CubeI n}
    (ht : t ∈ Cube.boundary (Fin n)) : homotopyCubeFun n hn i s t = sphBase n hn := by
  rw [homotopyCubeFun]
  exact collapseMap_mem_boundary n hn (update_projIcc_mem_boundary n i s ht)

/-- At parameter `0` the cube level homotopy is the cube description of `wedgeFst ∘ pinchMap`. -/
theorem homotopyCubeFun_zero (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (t : CubeI n) :
    homotopyCubeFun n hn i 0 t
      = ((wedgeFst (sphBase n hn)).comp (pinchMap n hn i)) (collapseMap n hn t) := by
  rw [homotopyCubeFun, wedgeFst_pinchMap_collapse,
    show ((2 : ℝ) - (((0 : I)) : ℝ)) = 2 from by norm_num]
  split_ifs with h
  · rw [← sigmaA]
  · refine collapseMap_mem_boundary n hn ⟨i, Or.inr ?_⟩
    rw [Function.update_apply, if_pos rfl]
    exact projIcc_right_of_one_le (by linarith [not_le.mp h])

/-- At parameter `1` the cube level homotopy is the collapse itself. -/
theorem homotopyCubeFun_one (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (t : CubeI n) :
    homotopyCubeFun n hn i 1 t = collapseMap n hn t := by
  have h2 : Set.projIcc (0 : ℝ) 1 zero_le_one (t i : ℝ) = t i := by
    rw [Set.projIcc_of_mem zero_le_one (t i).2]
  rw [homotopyCubeFun, show ((2 : ℝ) - (((1 : I)) : ℝ)) = 1 from by norm_num, one_mul, h2,
    Function.update_eq_self]

theorem wedgeFst_pinchMap_homotopic (n : ℕ) (hn : 1 ≤ n) (i : Fin n) :
    ContinuousMap.Homotopic ((wedgeFst (sphBase n hn)).comp (pinchMap n hn i))
      (ContinuousMap.id (sphere n)) := by
  classical
  -- the cube level homotopy, as a continuous map
  let Hf : C(I × CubeI n, sphere n) :=
    ⟨Function.uncurry (homotopyCubeFun n hn i), continuous_homotopyCubeFun n hn i⟩
  -- its curried form
  let Hc : C(CubeI n, C(I, sphere n)) := (Hf.comp (Homeomorph.prodComm (CubeI n) I)).curry
  have hHf : ∀ (s : I) (t : CubeI n), Hf (s, t) = homotopyCubeFun n hn i s t := fun _ _ => rfl
  have hHc : ∀ (t : CubeI n) (s : I), Hc t s = Hf (s, t) := by
    intro t s
    simp [Hc, ContinuousMap.curry_apply, ContinuousMap.comp_apply]
  -- the curried homotopy is constant on the boundary of the cube
  have hbound : ∀ t ∈ Cube.boundary (Fin n), Hc t = ContinuousMap.const I (sphBase n hn) := by
    intro t ht
    refine ContinuousMap.ext (fun s => ?_)
    rw [hHc t s, hHf s t, ContinuousMap.const_apply]
    exact homotopyCubeFun_mem_boundary n hn i s ht
  -- hence it descends to the sphere
  have hfac : Function.FactorsThrough Hc (collapseMap n hn) := by
    intro t t' h
    rcases collapseMap_fiber n hn h with h' | ⟨ht, ht'⟩
    · rw [h']
    · rw [hbound t ht, hbound t' ht']
  let F : C(sphere n, C(I, sphere n)) := (collapseMap_isQuotientMap n hn).lift Hc hfac
  have hF : ∀ t : CubeI n, F (collapseMap n hn t) = Hc t := fun t =>
    congrFun (congrArg (fun (g : C(CubeI n, C(I, sphere n))) => (⇑g))
      (Topology.IsQuotientMap.lift_comp (collapseMap_isQuotientMap n hn) Hc hfac)) t
  -- uncurrying gives the homotopy on the sphere
  let H : C(I × sphere n, sphere n) :=
    (ContinuousMap.uncurry F).comp (Homeomorph.prodComm I (sphere n))
  refine ⟨⟨H, ?_, ?_⟩⟩
  · intro y
    obtain ⟨t, rfl⟩ := (collapseMap_isQuotientMap n hn).surjective y
    show F (collapseMap n hn t) 0
      = ((wedgeFst (sphBase n hn)).comp (pinchMap n hn i)) (collapseMap n hn t)
    rw [hF t, hHc t 0, hHf 0 t]
    exact homotopyCubeFun_zero n hn i t
  · intro y
    obtain ⟨t, rfl⟩ := (collapseMap_isQuotientMap n hn).surjective y
    show F (collapseMap n hn t) 1 = (ContinuousMap.id (sphere n)) (collapseMap n hn t)
    rw [hF t, hHc t 1, hHf 1 t]
    exact homotopyCubeFun_one n hn i t

end

end Work.Stems
