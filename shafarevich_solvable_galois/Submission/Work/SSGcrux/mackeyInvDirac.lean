import Mathlib
import Submission.Work.SSGRoute.coind_res_mackey
import Submission.Work.Sha2Lib.coindValueFormula_singleOrbit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGcrux

/-- **The Mackey inverse of a Dirac is a Dirac.** For a surjection `f : Γ →* Γ'` and a subgroup
`S ≤ Γ'` with `S' = S.comap f`, the inverse Mackey isomorphism `θ` of
`Work.SSGRoute.coind_res_mackey` sends the Dirac element at `x` with value `a` of the coinduced
module `coInd_{S'}^{Γ} (res_{f.subgroupComap S} W)` to the function
`g ↦ if g * (f x)⁻¹ ∈ S then a else 0` on `Γ'`. -/
theorem mackeyInvDirac {Γ Γ' : Type} [Group Γ] [Group Γ'] [Fintype Γ] [Fintype Γ']
    [DecidableEq Γ]
    (f : Γ →* Γ') (hf : Function.Surjective f) (S : Subgroup Γ')
    [DecidablePred (· ∈ S)]
    [DecidableRel (QuotientGroup.rightRel S)] [Fintype (Γ' ⧸ S)]
    [DecidableRel (QuotientGroup.rightRel (S.comap f))] [Fintype (Γ ⧸ S.comap f)]
    (W : Rep.{0} SSGRoute.PTExt.Coeff ↥S)
    (htriv : ∀ (n : ↥S) (x : W.V), W.ρ n x = x)
    (θ : Rep.res f (Rep.coind S.subtype W) ≅
        Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) W))
    (hθ : ∀ (φ : (Rep.coind S.subtype W).V) (x : Γ), (θ.hom.hom φ).1 x = φ.1 (f x))
    (x : Γ) (a : W.V) (g : Γ') :
    (θ.inv.hom (Work.Sha2Lib.diracHom (Rep.res (f.subgroupComap S) W)
        (fun n _ a => htriv (f.subgroupComap S n) a) x a)).1 g
      = if g * (f x)⁻¹ ∈ S then a else 0 := by
  classical
  -- The coinduced element `v` of `coInd_{S'}^Γ (res_{S'} W)` that is transported back by `θ.inv`.
  set v : (Rep.coind (S.comap f).subtype (Rep.res (f.subgroupComap S) W)).V :=
    Work.Sha2Lib.diracHom (Rep.res (f.subgroupComap S) W)
      (fun n _ a => htriv (f.subgroupComap S n) a) x a with hvdef
  -- `θ.inv.hom` and `θ.hom.hom` are mutually inverse linear maps.
  have hcancel : θ.hom.hom (θ.inv.hom v) = v := by
    have h := congrArg (fun (m : (Rep.coind (S.comap f).subtype
        (Rep.res (f.subgroupComap S) W)) ⟶ (Rep.coind (S.comap f).subtype
        (Rep.res (f.subgroupComap S) W))) => (Rep.Hom.hom m) v) θ.inv_hom_id
    simpa only [Rep.hom_comp, Rep.hom_id, Representation.IntertwiningMap.comp_apply,
      Representation.IntertwiningMap.id_apply] using h
  -- Since `f` is surjective, test `θ.inv.hom v` against `θ.hom`, whose formula is `hθ`.
  obtain ⟨y, hy⟩ := hf g
  have hstep : (θ.inv.hom v).1 (f y) = v.1 y := by
    have h := hθ (θ.inv.hom v) y
    rw [hcancel] at h
    exact h.symm
  rw [← hy, hstep]
  -- Now evaluate the Dirac.
  have hvdirac : v = Work.SSGRoute.C6ValueFormula.dirac (S.comap f).subtype
      (Rep.res (f.subgroupComap S) W) (fun n _ a => htriv (f.subgroupComap S n) a) x a := by
    rw [hvdef]; rfl
  rw [hvdirac]
  -- The Dirac is supported on the coset `S' * x`, which corresponds to `f y * (f x)⁻¹ ∈ S`.
  by_cases hmem : ∃ d : ↥(S.comap f), (S.comap f).subtype d * x = y
  · obtain ⟨d, hd⟩ := hmem
    have hval : (Work.SSGRoute.C6ValueFormula.dirac (S.comap f).subtype
        (Rep.res (f.subgroupComap S) W)
        (fun n _ a => htriv (f.subgroupComap S n) a) x a).1 y = a := by
      rw [Work.SSGRoute.C6ValueFormula.dirac_apply_eq (S.comap f).subtype
        (Rep.res (f.subgroupComap S) W)
        (fun n _ a => htriv (f.subgroupComap S n) a) x a hd]
      exact htriv (f.subgroupComap S d) a
    rw [hval]
    have hcond : f y * (f x)⁻¹ ∈ S := by
      have hfy : f y * (f x)⁻¹ = f (d : Γ) := by
        rw [show y = (d : Γ) * x from hd.symm, map_mul]
        group
      rw [hfy]
      exact Subgroup.mem_comap.mp d.2
    rw [if_pos hcond]
  · have hval : (Work.SSGRoute.C6ValueFormula.dirac (S.comap f).subtype
        (Rep.res (f.subgroupComap S) W)
        (fun n _ a => htriv (f.subgroupComap S n) a) x a).1 y = 0 :=
      Work.SSGRoute.C6ValueFormula.dirac_apply_of_not (S.comap f).subtype
        (Rep.res (f.subgroupComap S) W)
        (fun n _ a => htriv (f.subgroupComap S n) a) x a hmem
    rw [hval]
    have hcond : ¬ (f y * (f x)⁻¹ ∈ S) := by
      intro hS
      apply hmem
      refine ⟨⟨y * x⁻¹, ?_⟩, ?_⟩
      · rw [Subgroup.mem_comap, map_mul, map_inv]
        exact hS
      · show (y * x⁻¹) * x = y
        group
    rw [if_neg hcond]

end Work.SSGcrux
