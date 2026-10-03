import Mathlib
import Submission.Work.OROneRel.vertexEta
import Submission.Work.OROneRel.magnusStepNielsenRoute
import Submission.Work.OROneRel.not_isProperPower_of
import Submission.Work.OROneRel.magnusStepData_one_of_freeGroupPresentation

/-!
# The Magnus step for a relator of "conjugation-word" shape

This file proves the Tietze/Nielsen step used in the `u = x₀ * s * x₀⁻¹ * s` family of the
one-relator combinatorics of node N2: if the root `u` of the relator `u ^ l` can be written as
`x₀ * s * x₀⁻¹ * s`, then `⟨α | u ^ l⟩` is an HNN extension of the two-generator one-relator vertex
`⟨a, b | a ^ l⟩` with associated subgroups `A = ⟨b⟩` and `B = Ψ A`, where `Ψ` is the Nielsen
automorphism `Ψ a = a`, `Ψ b = a * b⁻¹`, the stable letter playing the role of `x₀`; the class of `u`
is carried to `HNNExtension.of (mk a)`, and `‖a‖ = 1 < ‖u‖`.

The two maps are exhibited explicitly and checked on generators:
* forward, `x ↦ I (sect x)` where `I a = t` and `I b = of b`;
* backward, induced by `a ↦ mk u`, `b ↦ mk s` on the base and `t ↦ mk x₀`, the compatibility
  `mk x₀ * mk u * (mk s)⁻¹ * (mk x₀)⁻¹ = mk s` coming from `hu`.
-/

namespace Work.OROneRel

universe u

/-- `PresentedGroup.toGroup` evaluated on the class of a free-group element. -/
private lemma conjWordStep_toGroup_mk {α : Type u} {G : Type*} [Group G] {rels : Set (FreeGroup α)}
    {f : α → G} (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (w : FreeGroup α) :
    PresentedGroup.toGroup (rels := rels) (f := f) h (PresentedGroup.mk rels w) =
      FreeGroup.lift f w := rfl

/-- The `Ψ`-image of a subgroup, as a `MulEquiv`. -/
private abbrev conjWordStep_subgroupMapEquiv {G : Type u} [Group G] (Ψ : G ≃* G) (A : Subgroup G) :
    ↥A ≃* ↥(A.map Ψ.toMonoidHom) where
  toFun a := ⟨Ψ a, Subgroup.mem_map.mpr ⟨(a : G), a.2, rfl⟩⟩
  invFun b := ⟨Ψ.symm (b : G), by
    obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp b.2
    have h1 : Ψ.symm ((b : G)) = c := by rw [← hcb]; exact MulEquiv.symm_apply_apply Ψ c
    rw [h1]; exact hc⟩
  left_inv a := Subtype.ext (by simp)
  right_inv b := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [map_mul, Subgroup.coe_mul])

private lemma conjWordStep_subgroupMapEquiv_coe {G : Type u} [Group G] (Ψ : G ≃* G)
    (A : Subgroup G) (a : ↥A) :
    ((conjWordStep_subgroupMapEquiv Ψ A a : ↥(A.map Ψ.toMonoidHom)) : G) = Ψ (a : G) := rfl

/-- **The "conjugation-word" (Tietze) Magnus step.** -/
theorem magnusStepData_of_conjWord {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (x₀ : α) (s : FreeGroup α) (sect : α → FreeGroup (ULift.{u,0} (Fin 2)))
    (hgen : ∀ x : α, FreeGroup.lift (fun i : ULift.{u,0} (Fin 2) =>
        if i = ULift.up (0 : Fin 2) then FreeGroup.of x₀ else s) (sect x) = FreeGroup.of x)
    (hsect : sect x₀ = FreeGroup.of (ULift.up (0 : Fin 2)))
    (hsubst : FreeGroup.lift sect s = FreeGroup.of (ULift.up (1 : Fin 2)))
    (hu : u = FreeGroup.of x₀ * s * (FreeGroup.of x₀)⁻¹ * s)
    (hn : 2 ≤ relatorNorm u) :
    ∃ (β : Type u) (v : FreeGroup β), ¬ IsProperPower v ∧ relatorNorm v < relatorNorm u ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
            c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹ := by
  classical
  -- ### the vertex
  set aV : FreeGroup (ULift.{u,0} (Fin 2)) := FreeGroup.of (ULift.up (0 : Fin 2)) with haV
  set bV : FreeGroup (ULift.{u,0} (Fin 2)) := FreeGroup.of (ULift.up (1 : Fin 2)) with hbV
  obtain ⟨Ψ, hΨ1, hΨ0⟩ := vertexEta l
  -- the two generators of the vertex group are distinct
  have hne01 : ¬ ((ULift.up (1 : Fin 2) : ULift.{u,0} (Fin 2)) = ULift.up (0 : Fin 2)) := by decide
  -- ### the vertex subgroup and the HNN datum
  let A : Subgroup (PresentedGroup ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2))))) :=
    Subgroup.closure {PresentedGroup.of (ULift.up (1 : Fin 2))}
  let B : Subgroup (PresentedGroup ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2))))) :=
    A.map Ψ.toMonoidHom
  let φ : ↥A ≃* ↥B := conjWordStep_subgroupMapEquiv Ψ A
  -- ### the vertex map `fP`
  let fvec : ULift.{u,0} (Fin 2) → PresentedGroup ({u ^ l} : Set (FreeGroup α)) := fun i =>
    if i = ULift.up (0 : Fin 2) then PresentedGroup.mk _ u else PresentedGroup.mk _ s
  have hfPrel : ∀ r ∈ ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2)))),
      FreeGroup.lift fvec r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    rw [haV, map_pow, FreeGroup.lift_apply_of]
    show (if ULift.up (0 : Fin 2) = ULift.up (0 : Fin 2) then PresentedGroup.mk _ u
      else PresentedGroup.mk _ s) ^ l = 1
    rw [if_pos rfl, ← map_pow]
    exact PresentedGroup.one_of_mem (by simp)
  let fP : PresentedGroup ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2)))) →*
      PresentedGroup ({u ^ l} : Set (FreeGroup α)) := PresentedGroup.toGroup hfPrel
  have hfP0 : fP (PresentedGroup.of (ULift.up (0 : Fin 2))) = PresentedGroup.mk _ u := by
    simp [fP, fvec]
  have hfP1 : fP (PresentedGroup.of (ULift.up (1 : Fin 2))) = PresentedGroup.mk _ s := by
    simp [fP, fvec]
  -- ### the compatibility relation
  have hmain : PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u *
        (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) s)⁻¹ *
        PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (FreeGroup.of x₀) =
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (FreeGroup.of x₀) *
        PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) s := by
    have hfg : u * s⁻¹ * FreeGroup.of x₀ = FreeGroup.of x₀ * s := by rw [hu]; group
    have h := congrArg (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))) hfg
    simpa only [map_mul, map_inv] using h
  have hcΨ : ∀ g (hg : g ∈ A),
      PresentedGroup.of x₀ * fP g = fP (Ψ g) * PresentedGroup.of x₀ := by
    intro g hg
    refine Subgroup.closure_induction
      (p := fun g _ => PresentedGroup.of x₀ * fP g = fP (Ψ g) * PresentedGroup.of x₀) ?_ ?_ ?_ ?_ hg
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [hfP1, hΨ1, map_mul, map_inv, hfP0, hfP1]
      simpa only [PresentedGroup.of] using hmain.symm
    · simp
    · intro g₁ g₂ _ _ h₁ h₂
      rw [map_mul, map_mul, map_mul]
      have hkey : ∀ z, PresentedGroup.of x₀ * (fP g₁ * z) =
          fP (Ψ g₁) * (PresentedGroup.of x₀ * z) := by
        intro z
        rw [← mul_assoc, h₁, mul_assoc]
      rw [hkey, h₂, mul_assoc]
    · intro g _ h₁
      have h₂ : fP (Ψ g) =
          PresentedGroup.of x₀ * fP g * (PresentedGroup.of x₀)⁻¹ := by
        have h := congrArg (fun z => z * (PresentedGroup.of x₀)⁻¹) h₁
        simpa only [mul_assoc, mul_inv_cancel, mul_one] using h.symm
      simp only [map_inv]
      rw [h₂]
      group
  -- the compatibility `t * fP (φ a) = fP a * t` of the HNN datum, in the form demanded by
  -- `HNNExtension.lift` (phrased with `φ` rather than `Ψ`, so that the implicit `φ` of
  -- `HNNExtension.lift` is found by unification)
  have hc : ∀ a : ↥A, PresentedGroup.of x₀ *
        fP (a : PresentedGroup ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2))))) =
      fP ((φ a : ↥B) : PresentedGroup ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2))))) *
        PresentedGroup.of x₀ := by
    intro a
    have hcoe : ((φ a : ↥B) : PresentedGroup ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2))))) =
        Ψ (a : PresentedGroup ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2))))) :=
      conjWordStep_subgroupMapEquiv_coe Ψ A a
    rw [hcoe]
    exact hcΨ (a : _) a.2
  -- ### the backward map
  let back : HNNExtension (PresentedGroup ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2))))) A B φ →*
      PresentedGroup ({u ^ l} : Set (FreeGroup α)) :=
    HNNExtension.lift fP (PresentedGroup.of x₀) hc
  -- ### explicit names for the stable letter and the vertex embedding
  let tE : HNNExtension (PresentedGroup ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2))))) A B φ :=
    HNNExtension.t
  let ofE : PresentedGroup ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2)))) →*
      HNNExtension (PresentedGroup ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2))))) A B φ :=
    HNNExtension.of
  -- ### the forward map
  let I : FreeGroup (ULift.{u,0} (Fin 2)) →*
      HNNExtension (PresentedGroup ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2))))) A B φ :=
    FreeGroup.lift (fun i : ULift.{u,0} (Fin 2) =>
      if i = ULift.up (0 : Fin 2) then tE
      else ofE (PresentedGroup.of (ULift.up (1 : Fin 2))))
  have hlift_eq : FreeGroup.lift (fun x : α => I (sect x)) = I.comp (FreeGroup.lift sect) := by
    refine FreeGroup.ext_hom _ _ (fun x => ?_)
    simp [FreeGroup.lift_apply_of]
  have hSubst_u : FreeGroup.lift sect u = aV * bV * aV⁻¹ * bV := by
    show FreeGroup.lift sect u = FreeGroup.of (ULift.up (0 : Fin 2)) *
        FreeGroup.of (ULift.up (1 : Fin 2)) * (FreeGroup.of (ULift.up (0 : Fin 2)))⁻¹ *
        FreeGroup.of (ULift.up (1 : Fin 2))
    rw [hu, map_mul, map_mul, map_mul, map_inv]
    simp only [FreeGroup.lift_apply_of, hsect, hsubst]
    rfl
  have hIaV : I aV = tE := by
    show FreeGroup.lift (fun i : ULift.{u,0} (Fin 2) => if i = ULift.up (0 : Fin 2) then
        HNNExtension.t else HNNExtension.of (PresentedGroup.of (ULift.up (1 : Fin 2))))
      (FreeGroup.of (ULift.up (0 : Fin 2))) = HNNExtension.t
    rw [FreeGroup.lift_apply_of, if_pos rfl]
  have hIbV : I bV = ofE (PresentedGroup.of (ULift.up (1 : Fin 2))) := by
    show FreeGroup.lift (fun i : ULift.{u,0} (Fin 2) => if i = ULift.up (0 : Fin 2) then
        HNNExtension.t else HNNExtension.of (PresentedGroup.of (ULift.up (1 : Fin 2))))
      (FreeGroup.of (ULift.up (1 : Fin 2))) =
        HNNExtension.of (PresentedGroup.of (ULift.up (1 : Fin 2)))
    rw [FreeGroup.lift_apply_of, if_neg hne01]
  have hconj : tE * ofE (PresentedGroup.of (ULift.up (1 : Fin 2))) * tE⁻¹ =
      ofE (PresentedGroup.of (ULift.up (0 : Fin 2)) *
        (PresentedGroup.of (ULift.up (1 : Fin 2)))⁻¹) := by
    have h := HNNExtension.equiv_eq_conj
      (G := PresentedGroup ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2)))))
      (A := A) (B := B) (φ := φ)
      (⟨PresentedGroup.of (ULift.up (1 : Fin 2)), Subgroup.subset_closure (by simp)⟩ : ↥A)
    rw [show ((φ ⟨PresentedGroup.of (ULift.up (1 : Fin 2)),
          Subgroup.subset_closure (by simp)⟩ : ↥B) :
            PresentedGroup ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2))))) =
          PresentedGroup.of (ULift.up (0 : Fin 2)) * (PresentedGroup.of (ULift.up (1 : Fin 2)))⁻¹
        from (conjWordStep_subgroupMapEquiv_coe Ψ A
          ⟨PresentedGroup.of (ULift.up (1 : Fin 2)), Subgroup.subset_closure (by simp)⟩).trans
            hΨ1] at h
    exact h.symm
  have hIu : I (aV * bV * aV⁻¹ * bV) = ofE (PresentedGroup.of (ULift.up (0 : Fin 2))) := by
    rw [map_mul, map_mul, map_mul, map_inv, hIaV, hIbV, hconj, ← map_mul]
    congr 1
    group
  have hkill : ∀ r ∈ ({u ^ l} : Set (FreeGroup α)),
      FreeGroup.lift (fun x : α => I (sect x)) r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    have h1 : FreeGroup.lift (fun x : α => I (sect x)) u =
        ofE (PresentedGroup.of (ULift.up (0 : Fin 2))) := by
      rw [hlift_eq, MonoidHom.comp_apply, hSubst_u, hIu]
    have hpa : ((PresentedGroup.of (ULift.up (0 : Fin 2)) : PresentedGroup
        ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2))))) ^ l) = 1 := by
      rw [show (PresentedGroup.of (ULift.up (0 : Fin 2)) : PresentedGroup
          ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2))))) =
          PresentedGroup.mk ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2)))) aV from rfl]
      rw [← map_pow]
      exact PresentedGroup.one_of_mem (by simp)
    rw [map_pow, h1, ← map_pow, hpa]
    simp
  let fwd : PresentedGroup ({u ^ l} : Set (FreeGroup α)) →*
      HNNExtension (PresentedGroup ({aV ^ l} : Set (FreeGroup (ULift.{u,0} (Fin 2))))) A B φ :=
    PresentedGroup.toGroup (f := fun x : α => I (sect x)) hkill
  -- ### the two compositions
  have hbt : back tE = PresentedGroup.of x₀ := by
    show (HNNExtension.lift fP (PresentedGroup.of x₀) hc) HNNExtension.t = PresentedGroup.of x₀
    exact HNNExtension.lift_t fP (PresentedGroup.of x₀) hc
  have hg1 : (FreeGroup.lift (fun i : ULift.{u,0} (Fin 2) =>
      if i = ULift.up (0 : Fin 2) then FreeGroup.of x₀ else s))
      (FreeGroup.of (ULift.up (1 : Fin 2))) = s := by
    rw [FreeGroup.lift_apply_of, if_neg hne01]
  have hb1 : back (ofE (PresentedGroup.of (ULift.up (1 : Fin 2)))) =
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) s := by
    rw [show back (ofE (PresentedGroup.of (ULift.up (1 : Fin 2)))) =
        (HNNExtension.lift fP (PresentedGroup.of x₀) hc)
          (HNNExtension.of (PresentedGroup.of (ULift.up (1 : Fin 2)))) from rfl]
    simp only [HNNExtension.lift_of, hfP1]
  have hbackI : back.comp I = (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))).comp
      (FreeGroup.lift (fun i : ULift.{u,0} (Fin 2) =>
        if i = ULift.up (0 : Fin 2) then FreeGroup.of x₀ else s)) := by
    refine FreeGroup.ext_hom _ _ (fun i => ?_)
    rcases i with ⟨j⟩
    fin_cases j
    · show back (I (FreeGroup.of (ULift.up (0 : Fin 2)))) =
          PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
            ((FreeGroup.lift (fun i : ULift.{u,0} (Fin 2) =>
              if i = ULift.up (0 : Fin 2) then FreeGroup.of x₀ else s))
                (FreeGroup.of (ULift.up (0 : Fin 2))))
      rw [hIaV, show PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
            ((FreeGroup.lift (fun i : ULift.{u,0} (Fin 2) =>
              if i = ULift.up (0 : Fin 2) then FreeGroup.of x₀ else s))
                (FreeGroup.of (ULift.up (0 : Fin 2)))) = PresentedGroup.of x₀ from by
          rw [FreeGroup.lift_apply_of, if_pos rfl]; rfl]
      exact hbt
    · show back (I (FreeGroup.of (ULift.up (1 : Fin 2)))) =
          PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
            ((FreeGroup.lift (fun i : ULift.{u,0} (Fin 2) =>
              if i = ULift.up (0 : Fin 2) then FreeGroup.of x₀ else s))
                (FreeGroup.of (ULift.up (1 : Fin 2))))
      rw [hIbV, hg1]
      exact hb1
  have h1 : back.comp fwd = MonoidHom.id (PresentedGroup ({u ^ l} : Set (FreeGroup α))) := by
    refine PresentedGroup.ext (fun x => ?_)
    have hx : fwd (PresentedGroup.of x) = I (sect x) := by simp [fwd]
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, hx]
    have h := DFunLike.congr_fun hbackI (sect x)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at h
    rw [h, hgen x]
    rfl
  have hbo : back.comp ofE = fP := by
    refine MonoidHom.ext (fun h => ?_)
    rw [MonoidHom.comp_apply]
    show (HNNExtension.lift fP (PresentedGroup.of x₀) hc) (HNNExtension.of h) = fP h
    exact HNNExtension.lift_of fP (PresentedGroup.of x₀) hc h
  have hfp : fwd.comp fP = ofE := by
    refine PresentedGroup.ext (fun x => ?_)
    rcases x with ⟨j⟩
    fin_cases j
    · show fwd (fP (PresentedGroup.of (ULift.up (0 : Fin 2)))) =
          ofE (PresentedGroup.of (ULift.up (0 : Fin 2)))
      rw [hfP0, conjWordStep_toGroup_mk hkill u]
      rw [hlift_eq, MonoidHom.comp_apply, hSubst_u, hIu]
    · show fwd (fP (PresentedGroup.of (ULift.up (1 : Fin 2)))) =
          ofE (PresentedGroup.of (ULift.up (1 : Fin 2)))
      rw [hfP1, conjWordStep_toGroup_mk hkill s]
      rw [hlift_eq, MonoidHom.comp_apply, hsubst]
      exact hIbV
  have h2 : fwd.comp back = MonoidHom.id _ := by
    refine HNNExtension.hom_ext ?_ ?_
    · rw [MonoidHom.comp_assoc, hbo, hfp, MonoidHom.id_comp]
    · rw [MonoidHom.comp_apply, MonoidHom.id_apply]
      have hx : fwd (PresentedGroup.of x₀) = I (sect x₀) := by simp [fwd]
      rw [hbt, hx, hsect]
      exact hIaV
  -- ### assembly
  refine ⟨ULift.{u,0} (Fin 2), aV, not_isProperPower_of (ULift.up (0 : Fin 2)), ?_, A, B, φ,
    MonoidHom.toMulEquiv fwd back h1 h2, 1, ?_⟩
  · have h1 : relatorNorm aV = 1 := by
      show relatorNorm (FreeGroup.of (ULift.up (0 : Fin 2))) = 1
      exact relatorNorm_freeGroup_of _
    rw [h1]
    omega
  · rw [one_mul, inv_one, mul_one]
    have h1' : fwd (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
        ofE (PresentedGroup.of (ULift.up (0 : Fin 2))) := by
      rw [conjWordStep_toGroup_mk hkill u, hlift_eq, MonoidHom.comp_apply, hSubst_u, hIu]
    rw [MonoidHom.toMulEquiv_apply, h1']
    rfl

end Work.OROneRel
