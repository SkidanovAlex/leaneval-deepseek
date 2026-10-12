import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.Instances.AddCircle.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB7AK.Q2Gram

theorem torus_lift (F : (Fin 3 → ℝ) → ℂ) (hF : Continuous F)
    (hper : ∀ (k : Fin 3 → ℤ) (y : Fin 3 → ℝ), F (y + fun i => (k i : ℝ)) = F y) :
    ∃ P : UnitAddTorus (Fin 3) → ℂ, Continuous P ∧
      ∀ y : Fin 3 → ℝ, P (fun i => (y i : UnitAddCircle)) = F y := by
  -- the quotient map `ℝ³ → UnitAddTorus (Fin 3)`
  let Φ : C(Fin 3 → ℝ, UnitAddTorus (Fin 3)) :=
    ⟨fun y => fun i => (y i : UnitAddCircle), by fun_prop⟩
  let F' : C(Fin 3 → ℝ, ℂ) := ⟨F, hF⟩
  -- `Φ` is the product of the open quotient maps `ℝ → UnitAddCircle`
  have hΦopen : IsOpenMap (⇑Φ) :=
    IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
      (Filter.Eventually.of_forall fun _ => QuotientAddGroup.mk_surjective)
  have hΦsurj : Function.Surjective (⇑Φ) := by
    intro x
    choose y hy using fun i => QuotientAddGroup.mk_surjective (x i)
    exact ⟨y, funext hy⟩
  have hΦ : Topology.IsQuotientMap (⇑Φ) :=
    IsOpenMap.isQuotientMap hΦopen Φ.continuous hΦsurj
  -- `F` is constant on the fibres of `Φ`, by periodicity
  have hfac : Function.FactorsThrough (⇑F') (⇑Φ) := by
    intro x y hxy
    have hxy' : ∀ i, (x i : AddCircle (1 : ℝ)) = (y i : AddCircle (1 : ℝ)) :=
      fun i => congr_fun hxy i
    have hmem : ∀ i, ∃ k : ℤ, x i = y i + (k : ℝ) := by
      intro i
      have h := (QuotientAddGroup.eq_iff_sub_mem).mp (hxy' i)
      rw [AddSubgroup.mem_zmultiples_iff] at h
      obtain ⟨k, hk⟩ := h
      have hk' : (k : ℝ) = x i - y i := by simpa using hk
      exact ⟨k, by rw [hk']; ring⟩
    choose k hk using hmem
    have hx : x = y + fun i => (k i : ℝ) := by
      funext i
      exact hk i
    rw [hx]
    simpa [F'] using hper k y
  refine ⟨⇑(hΦ.lift F' hfac), (hΦ.lift F' hfac).continuous, fun y => ?_⟩
  have hc := congrArg (fun (m : C(Fin 3 → ℝ, ℂ)) => m y) (hΦ.lift_comp F' hfac)
  rw [ContinuousMap.comp_apply] at hc
  exact hc

end Work.BoseB7AK.Q2Gram
