import Mathlib
import Submission.Work.SSS.FibreColDefs
import Submission.Work.SSS.Transgression.vzQuotAux
import Submission.Work.SSS.Transgression.V_mem_of_projQ_zero
import Submission.Work.SSS.Transgression.Bs_boundary_zero
import Submission.Work.SSS.Transgression.exists_wrel_of_mem_V

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


attribute [-instance] AddCommGroup.toIntModule

namespace Work.SSS.Transgression

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **The transgression into the left column.**  For `2 ≤ s`, the `s`-th step
`V_s/V_{s-1} = ↥(VZ ξ t s) ⧸ VZQ ξ t s` of the left column of the filtration is a quotient of the
model `Z^s_{s,t+1} ⧸ B^s_{s,t+1}` (the source `Zs` of the transgression `d_s` modulo the model `Bs`
of its kernel).

Roadmap.  An element of `Zs ⊆ (F_s/F_{s-1})_{t+1}` is the class of some `x ∈ F_s.X (t+1)` with
`d x ∈ F_0` (this is `Wrel ξ s (t+1)`); send it to the class of `d x` in `V_s/V_{s-1}`, where
`V_s = ∂(F_sX_{t+1}) ∩ Z_t(F_0)` and `d x` is a cycle lying in `F_0` (so in `Z_t(F_0)`, hence in
`V_s`).
* Well-defined: replacing the lift `x` by another lift changes it by a chain of `F_{s-1}`, whose
  boundary lies in `∂F_{s-1}X_{t+1} ⊆ V_{s-1}`; and the map vanishes on the kernel of
  `F_sX_{t+1} → (F_s/F_{s-1})_{t+1}` because the projection is the cokernel projection along
  `F_{s-1} ↪ F_s`.
* It kills `Bs`: an element of `Bs` is represented by `∂y` with `y ∈ F_{2s-1}X_{t+2}` and
  `∂y ∈ F_sX_{t+1}`, and `∂(∂y) = 0`.
* Surjective: every element of `V_s/V_{s-1}` is the class of `∂x` for some `x ∈ F_sX_{t+1}` with
  `∂x ∈ Z_t(F_0)`, i.e. of an element of `Zs`. -/
theorem vzQuotSurj {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) (t s : ℕ)
    (hs : 2 ≤ s) :
    ∃ f : (↥(Zs ξ s (t + 1)) ⧸ BsZ ξ s (t + 1)) →ₗ[ℤ] (↥(VZ ξ t s) ⧸ VZQ ξ t s),
      Function.Surjective f := by
  -- write `s = k + 1`, so that `V_{s-1} = V_k` and the quotient by `VZQ ξ t (k+1)` is a quotient
  -- by `VZ ξ t k` definitionally
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  -- a `Wrel`-chain of `F_{k+1}` has its boundary in `F_0`
  have hWrel_mem : ∀ y : (ξ.F.obj (k + 1)).X (t + 1), y ∈ Wrel ξ (k + 1) (t + 1) →
      Cincl ξ (k + 1) t (dFs ξ (k + 1) (t + 1) t y) ∈ Fch ξ 0 t := by
    intro y hy
    have h := hy
    simp only [Wrel, Submodule.mem_comap] at h
    simpa using h
  -- the boundary of a `Wrel`-chain is a cycle of `F_0`
  have hZof : ∀ y : ↥(Wrel ξ (k + 1) (t + 1)),
      Cincl ξ (k + 1) t (dFs ξ (k + 1) (t + 1) t (y : (ξ.F.obj (k + 1)).X (t + 1))) ∈
        Zof ξ t := by
    intro y
    refine Submodule.mem_inf.mpr ⟨?_, hWrel_mem y.1 y.2⟩
    rw [LinearMap.mem_ker, Cincl_dFs_apply]
    exact dC_dC t (Cincl ξ (k + 1) (t + 1) y.1)
  -- the boundary of a `Wrel`-chain lies in `V_{k+1}`
  have hVmem : ∀ y : ↥(Wrel ξ (k + 1) (t + 1)),
      Cincl ξ (k + 1) t (dFs ξ (k + 1) (t + 1) t (y : (ξ.F.obj (k + 1)).X (t + 1))) ∈
        V ξ t (k + 1) := by
    intro y
    refine Submodule.mem_inf.mpr ⟨?_, hZof y⟩
    refine Submodule.mem_map.mpr ⟨Cincl ξ (k + 1) (t + 1) y.1, ?_, ?_⟩
    · rw [mem_Fch]
      exact ⟨y.1, rfl⟩
    · rw [Cincl_dFs_apply]
  -- the transgression on the level of representatives
  let β : ↥(Wrel ξ (k + 1) (t + 1)) →ₗ[ℤ] ↥(VZ ξ t (k + 1)) :=
    { toFun := fun y => ⟨⟨Cincl ξ (k + 1) t (dFs ξ (k + 1) (t + 1) t y.1), hZof y⟩, hVmem y⟩
      map_add' := fun y y' => Subtype.ext (Subtype.ext (by simp))
      map_smul' := fun c y => Subtype.ext (Subtype.ext (by simp)) }
  have hβ : ∀ y : ↥(Wrel ξ (k + 1) (t + 1)),
      ((β y : ↥(VZ ξ t (k + 1))) : C.X t) =
        Cincl ξ (k + 1) t (dFs ξ (k + 1) (t + 1) t y.1) := fun _ => rfl
  -- the projection of the representatives onto `Zs`
  let p : ↥(Wrel ξ (k + 1) (t + 1)) →ₗ[ℤ] ↥(Zs ξ (k + 1) (t + 1)) :=
    ((projQ ξ (k + 1) (t + 1)).comp (Wrel ξ (k + 1) (t + 1)).subtype).codRestrict
      (Zs ξ (k + 1) (t + 1)) (fun y => by
        rw [Zs]
        exact Submodule.mem_map.mpr ⟨y.1, y.2, rfl⟩)
  have hp : Function.Surjective p := by
    intro z
    obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.mp (show z.1 ∈ Zs ξ (k + 1) (t + 1) from z.2)
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    simpa only [p, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply]
      using hyz
  -- the map on the quotient of the representatives
  let φW : ↥(Wrel ξ (k + 1) (t + 1)) →ₗ[ℤ]
      (↥(VZ ξ t (k + 1)) ⧸ VZQ ξ t (k + 1)) :=
    (Submodule.mkQ (VZQ ξ t (k + 1))).comp β
  -- well-definedness: a representative of `0` in `Zs` has boundary in `V_k`
  have hker : LinearMap.ker p ≤ LinearMap.ker φW := by
    intro y hy
    rw [LinearMap.mem_ker] at hy ⊢
    have hy0 : projQ ξ (k + 1) (t + 1) y.1 = 0 := by
      have h := congrArg (fun z : ↥(Zs ξ (k + 1) (t + 1)) => z.1) hy
      simpa only [p, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        Submodule.coe_zero] using h
    have hV : Cincl ξ (k + 1) t (dFs ξ (k + 1) (t + 1) t y.1) ∈ V ξ t k :=
      V_mem_of_projQ_zero ξ t k y.1 y.2 hy0
    have hmem : β y ∈ VZQ ξ t (k + 1) := by
      rw [VZQ, Submodule.mem_comap, VZ, Submodule.mem_comap]
      show Cincl ξ (k + 1) t (dFs ξ (k + 1) (t + 1) t y.1) ∈ V ξ t k
      exact hV
    show (VZQ ξ t (k + 1)).mkQ (β y) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hmem
  -- descend `φW` along the surjection `p`
  let e : (↥(Wrel ξ (k + 1) (t + 1)) ⧸ LinearMap.ker p) ≃ₗ[ℤ] ↥(Zs ξ (k + 1) (t + 1)) :=
    LinearMap.quotKerEquivOfSurjective p hp
  let φZ : ↥(Zs ξ (k + 1) (t + 1)) →ₗ[ℤ] (↥(VZ ξ t (k + 1)) ⧸ VZQ ξ t (k + 1)) :=
    (Submodule.liftQ (LinearMap.ker p) φW hker).comp e.symm.toLinearMap
  have hφZ : ∀ y : ↥(Wrel ξ (k + 1) (t + 1)), φZ (p y) = φW y := by
    intro y
    have h1 : e.symm (p y) = Submodule.Quotient.mk y :=
      LinearMap.quotKerEquivOfSurjective_symm_apply (f := p) hp y
    show (Submodule.liftQ (LinearMap.ker p) φW hker) (e.symm (p y)) = φW y
    rw [h1, Submodule.liftQ_apply]
  -- the map kills the model `B^s` of the kernel of the transgression
  have hB : BsZ ξ (k + 1) (t + 1) ≤ LinearMap.ker φZ := by
    intro z hz
    rw [LinearMap.mem_ker]
    have hzB : z.1 ∈ Bs ξ (k + 1) (t + 1) := hz
    obtain ⟨u, hu, huz⟩ := Submodule.mem_map.mp hzB
    have huW : u ∈ Wrel ξ (k + 1) (t + 1) := by
      have h := Bs_boundary_zero ξ t k u hu
      rw [Wrel, Submodule.mem_comap, Submodule.mem_comap]
      show Cincl ξ (k + 1) t (dFs ξ (k + 1) (t + 1) t u) ∈ Fch ξ 0 t
      rw [h]
      exact Submodule.zero_mem _
    have hzu : p ⟨u, huW⟩ = z := by
      refine Subtype.ext ?_
      simpa only [p, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply]
        using huz
    have hzero : β ⟨u, huW⟩ = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hβ ⟨u, huW⟩]
      simpa using Bs_boundary_zero ξ t k u hu
    rw [← hzu, hφZ ⟨u, huW⟩]
    show (VZQ ξ t (k + 1)).mkQ (β ⟨u, huW⟩) = 0
    rw [hzero]
    exact map_zero _
  refine ⟨Submodule.liftQ (BsZ ξ (k + 1) (t + 1)) φZ hB, ?_⟩
  -- surjectivity: every class in `V_{k+1}/V_k` comes from a `Wrel`-chain
  intro a
  obtain ⟨v, hv⟩ := Submodule.mkQ_surjective (VZQ ξ t (k + 1)) a
  obtain ⟨x, hxW, hxv⟩ :=
    exists_wrel_of_mem_V ξ t (k + 1) ((v : ↥(VZ ξ t (k + 1))) : C.X t) v.2
  have hβv : β ⟨x, hxW⟩ = v := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hβ ⟨x, hxW⟩]
    exact hxv
  refine ⟨Submodule.Quotient.mk (p ⟨x, hxW⟩), ?_⟩
  show (Submodule.liftQ (BsZ ξ (k + 1) (t + 1)) φZ hB)
    (Submodule.Quotient.mk (p ⟨x, hxW⟩)) = a
  rw [Submodule.liftQ_apply, hφZ ⟨x, hxW⟩]
  show (VZQ ξ t (k + 1)).mkQ (β ⟨x, hxW⟩) = a
  rw [Submodule.mkQ_apply, hβv]
  exact hv

end

end Work.SSS.Transgression
