import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.TensorPower.Basic
import Submission.Work.CohomologicalShrinking.Prop5
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

open scoped TensorProduct

set_option maxHeartbeats 1600000

universe u v

variable {p : ℕ}

/-! ## The identification `F(d)/F(d)^2 ≅ E(d,(1,1))`

We build the canonical map on the `p`-central quotient underlying `squareQuotient p G d` to the
quotient `refinedQuotient p (F(d)) 1 1` underlying `E p G d 1 1`.  It is the "identity" map: at
`(1,1)` both quotients are `P / P^p[P,P]`. -/

/-- The element of `P_0 = P` (the `0`-th term of the `p`-central series, which is `⊤`)
underlying a group element. -/
noncomputable def toTop (p : ℕ) (G : Type*) [Group G] (d : ℕ)
    (z : Work.Shrinking.freeOperatorGroup G d) :
    Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0 :=
  ⟨z, show z ∈ Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0
    from Subgroup.mem_top z⟩

/-- The inclusion `P_0 = P → P_{(1,1)} = P_1`, which is the identity on underlying elements. -/
noncomputable def inclToRefined (p : ℕ) (P : Type*) [Group P] :
    Work.Shrinking.pCentralSeries p P 0 →* refinedTerm p P 1 1 where
  toFun x := ⟨(x : P), by rw [refinedTerm_one (p:=p) (P:=P) 1]; exact x.2⟩
  map_one' := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl

/-- The canonical homomorphism `F(d)/F(d)^2 →* E(d,(1,1))`, induced by the identity on `F(d)`
(the compatibility with the respective normal subgroups is `refinedTerm_one`). -/
noncomputable def eMulTo (p : ℕ) (P : Type*) [Group P] :
    Work.Shrinking.pCentralQuotient p P 0 →* refinedQuotient p P 1 1 :=
  QuotientGroup.lift
    ((Work.Shrinking.pCentralSeries p P 1).subgroupOf (Work.Shrinking.pCentralSeries p P 0))
    ((QuotientGroup.mk'
        ((refinedTerm p P (tauSucc 1 1).1 (tauSucc 1 1).2).subgroupOf (refinedTerm p P 1 1))).comp
      (inclToRefined p P))
    (by
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [tauSucc_of_le (le_refl 1), refinedTerm_one (p:=p) (P:=P) 2]
      exact hx)

@[simp] lemma eMulTo_mk (p : ℕ) (P : Type*) [Group P]
    (x : Work.Shrinking.pCentralSeries p P 0) :
    eMulTo p P (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ (inclToRefined p P x) :=
  QuotientGroup.lift_mk' _ _ x

/-- The additive form of `eMulTo`. -/
noncomputable def eAdd (p : ℕ) (G : Type*) [Group G] (d : ℕ) :
    squareQuotient p G d →+ E p G d 1 1 where
  toFun x := Additive.ofMul (eMulTo p (Work.Shrinking.freeOperatorGroup G d) (Additive.toMul x))
  map_zero' := by rw [toMul_zero, map_one, ofMul_one]
  map_add' := by intro a b; rw [toMul_add, map_mul, ofMul_mul]

/-- The canonical `𝔽_p`-linear isomorphism `F(d)/F(d)^2 ≅ E(d,(1,1))` (up to the fact that
the two sides are only propositionally equal, carried by this explicit map). -/
noncomputable def eLin (p : ℕ) (G : Type*) [Group G] (d : ℕ) :
    squareQuotient p G d →ₗ[ZMod p] E p G d 1 1 :=
  AddMonoidHom.toZModLinearMap p (eAdd p G d)

lemma eLin_mk (p : ℕ) (G : Type*) [Group G] (d : ℕ)
    (x : Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0) :
    eLin p G d (Additive.ofMul (QuotientGroup.mk' _ x)) =
      Additive.ofMul (QuotientGroup.mk' _
        (inclToRefined p (Work.Shrinking.freeOperatorGroup G d) x)) := by
  change Additive.ofMul (eMulTo p (Work.Shrinking.freeOperatorGroup G d)
      (QuotientGroup.mk' _ x)) = _
  rw [eMulTo_mk]

lemma eLin_surjective (p : ℕ) (G : Type*) [Group G] (d : ℕ) :
    Function.Surjective (eLin p G d) := by
  intro z
  obtain ⟨w, rfl⟩ : ∃ w, Additive.ofMul w = z := ⟨Additive.toMul z, ofMul_toMul z⟩
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective _ w
  refine ⟨Additive.ofMul (QuotientGroup.mk' _
      (toTop p G d (y : Work.Shrinking.freeOperatorGroup G d))), ?_⟩
  rw [eLin_mk, ← hy]
  exact congrArg Additive.ofMul (congrArg (QuotientGroup.mk' _) (Subtype.ext rfl))

/-! ## Naturality and equivariance of `eLin` -/

lemma quotMapLin_mk (p : ℕ) (G : Type*) [Group G] {m n : ℕ}
    (ψ : Work.Shrinking.freeOperatorGroup G m →* Work.Shrinking.freeOperatorGroup G n)
    (hψ : Function.Surjective ψ)
    (x : Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G m) 0) :
    quotMapLin p G ψ hψ (Additive.ofMul (QuotientGroup.mk' _ x)) =
      Additive.ofMul (QuotientGroup.mk' _
        (toTop p G n (ψ (x : Work.Shrinking.freeOperatorGroup G m)))) := by
  change Additive.ofMul (pCentralMapMul p ψ hψ 0 (QuotientGroup.mk' _ x)) = _
  rw [pCentralMapMul, QuotientGroup.map_mk', QuotientGroup.mk'_apply]
  congr 1

lemma gradedMapLin_mk (p : ℕ) (G : Type*) [Group G] {m n : ℕ}
    (ψ : Work.Shrinking.freeOperatorGroup G m →* Work.Shrinking.freeOperatorGroup G n)
    (hψ : Function.Surjective ψ)
    (y : refinedTerm p (Work.Shrinking.freeOperatorGroup G m) 1 1) :
    gradedMapLin p ψ hψ 1 1 (Additive.ofMul (QuotientGroup.mk' _ y)) =
      Additive.ofMul (QuotientGroup.mk' _ (refinedMap p ψ hψ 1 1 y)) := by
  change Additive.ofMul (gradedMapMul p ψ hψ 1 1 (QuotientGroup.mk' _ y)) = _
  rw [gradedMapMul_of]

/-- `eLin` is natural along a surjective operator homomorphism. -/
theorem eLin_natural (p : ℕ) (G : Type*) [Group G] {m n : ℕ}
    (ψ : Work.Shrinking.freeOperatorGroup G m →* Work.Shrinking.freeOperatorGroup G n)
    (hψ : Function.Surjective ψ) :
    (eLin p G n).comp (quotMapLin p G ψ hψ) = (gradedMapLin p ψ hψ 1 1).comp (eLin p G m) := by
  apply LinearMap.ext
  intro y
  obtain ⟨w, rfl⟩ : ∃ w, Additive.ofMul w = y := ⟨Additive.toMul y, ofMul_toMul y⟩
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective _ w
  rw [← hx, LinearMap.comp_apply, LinearMap.comp_apply, quotMapLin_mk]
  simp only [eLin_mk]
  rw [gradedMapLin_mk]
  exact congrArg Additive.ofMul (congrArg (QuotientGroup.mk' _) (Subtype.ext rfl))

lemma pCentral_smul_mk (p : ℕ) (G : Type*) [Group G] (d : ℕ) (g : G)
    (x : Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0) :
    (g • (QuotientGroup.mk'
        ((Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) (0 + 1)).subgroupOf
          (Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0)) x)
        : Work.Shrinking.pCentralQuotient p (Work.Shrinking.freeOperatorGroup G d) 0) =
      QuotientGroup.mk'
        ((Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) (0 + 1)).subgroupOf
          (Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0))
        (Work.Shrinking.subAut
        (Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0) g
        (Work.Shrinking.map_pCentralSeries_eq p
          (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G d) g) 0) x) := by
  change Work.Shrinking.quotAut
      (Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0)
      (Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) (0 + 1)) g
      (Work.Shrinking.map_pCentralSeries_eq p
        (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G d) g) 0)
      (Work.Shrinking.map_pCentralSeries_eq p
        (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G d) g) (0 + 1))
      (QuotientGroup.mk'
        ((Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) (0 + 1)).subgroupOf
          (Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0)) x) = _
  rw [Work.Shrinking.quotAut_mk]

lemma refined_smul_mk (p : ℕ) (G : Type*) [Group G] (d : ℕ) (g : G)
    (y : refinedTerm p (Work.Shrinking.freeOperatorGroup G d) 1 1) :
    (g • (QuotientGroup.mk'
        ((refinedTerm p (Work.Shrinking.freeOperatorGroup G d) (tauSucc 1 1).1
          (tauSucc 1 1).2).subgroupOf (refinedTerm p (Work.Shrinking.freeOperatorGroup G d) 1 1)) y)
        : refinedQuotient p (Work.Shrinking.freeOperatorGroup G d) 1 1) =
      QuotientGroup.mk'
        ((refinedTerm p (Work.Shrinking.freeOperatorGroup G d) (tauSucc 1 1).1
          (tauSucc 1 1).2).subgroupOf (refinedTerm p (Work.Shrinking.freeOperatorGroup G d) 1 1))
        (Work.Shrinking.subAut
        (refinedTerm p (Work.Shrinking.freeOperatorGroup G d) 1 1) g
        (map_refinedTerm_eq p
          (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G d) g) 1 1) y) := by
  change Work.Shrinking.quotAut
      (refinedTerm p (Work.Shrinking.freeOperatorGroup G d) 1 1)
      (refinedTerm p (Work.Shrinking.freeOperatorGroup G d) (tauSucc 1 1).1 (tauSucc 1 1).2) g
      (map_refinedTerm_eq p
        (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G d) g) 1 1)
      (map_refinedTerm_eq p
        (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G d) g) (tauSucc 1 1).1 (tauSucc 1 1).2)
      (QuotientGroup.mk' _ y) = _
  rw [Work.Shrinking.quotAut_mk]

lemma smul_ofMul_pCentral (p : ℕ) (G : Type*) [Group G] (d : ℕ) (g : G)
    (a : Work.Shrinking.pCentralQuotient p (Work.Shrinking.freeOperatorGroup G d) 0) :
    g • (Additive.ofMul a : squareQuotient p G d) = Additive.ofMul (g • a) := rfl

lemma smul_ofMul_refined (p : ℕ) (G : Type*) [Group G] (d : ℕ) (g : G)
    (a : refinedQuotient p (Work.Shrinking.freeOperatorGroup G d) 1 1) :
    g • (Additive.ofMul a : E p G d 1 1) = Additive.ofMul (g • a) := rfl

/-- `eLin` is `G`-equivariant. -/
theorem eLin_smul (p : ℕ) (G : Type*) [Group G] (d : ℕ) (g : G) (z : squareQuotient p G d) :
    eLin p G d (g • z) = g • eLin p G d z := by
  obtain ⟨w, rfl⟩ : ∃ w, Additive.ofMul w = z := ⟨Additive.toMul z, ofMul_toMul z⟩
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective _ w
  rw [← hx]
  rw [smul_ofMul_pCentral, pCentral_smul_mk, eLin_mk, eLin_mk, smul_ofMul_refined, refined_smul_mk]
  refine congrArg Additive.ofMul (congrArg (QuotientGroup.mk' _) (Subtype.ext ?_))
  change ((Work.Shrinking.subAut
      (Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0) g
      (Work.Shrinking.map_pCentralSeries_eq p
        (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G d) g) 0) x)
      : Work.Shrinking.freeOperatorGroup G d) =
    (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G d) g)
      (x : Work.Shrinking.freeOperatorGroup G d)
  rw [Work.Shrinking.subAut_coe]

/-! ## The map `θ` and the structure `Prop5Data p G 1 1` -/

/-- The multilinear map `(Fin 1 → F(d)/F(d)^2) → E(d,(1,1))`, `f ↦ eLin (f 0)`: it is the
`1`-fold tensor version of the identity on `F(d)/F(d)^2`. -/
noncomputable def t1Map (p : ℕ) (G : Type*) [Group G] (d : ℕ) :
    MultilinearMap (ZMod p) (fun _ : Fin 1 => squareQuotient p G d) (E p G d 1 1) where
  toFun f := eLin p G d (f 0)
  map_update_add' := by
    intro _ m i x y
    have h1 : Function.update m i (x + y) = (fun _ : Fin 1 => x + y) := by
      funext j; rw [Function.update_apply, if_pos (Subsingleton.elim j i)]
    have h2 : Function.update m i x = (fun _ : Fin 1 => x) := by
      funext j; rw [Function.update_apply, if_pos (Subsingleton.elim j i)]
    have h3 : Function.update m i y = (fun _ : Fin 1 => y) := by
      funext j; rw [Function.update_apply, if_pos (Subsingleton.elim j i)]
    rw [h1, h2, h3]
    exact map_add (eLin p G d) x y
  map_update_smul' := by
    intro _ m i c x
    have h1 : Function.update m i (c • x) = (fun _ : Fin 1 => c • x) := by
      funext j; rw [Function.update_apply, if_pos (Subsingleton.elim j i)]
    have h2 : Function.update m i x = (fun _ : Fin 1 => x) := by
      funext j; rw [Function.update_apply, if_pos (Subsingleton.elim j i)]
    rw [h1, h2]
    exact map_smul (eLin p G d) c x

@[simp] lemma t1Map_apply (p : ℕ) (G : Type*) [Group G] (d : ℕ)
    (f : Fin 1 → squareQuotient p G d) : t1Map p G d f = eLin p G d (f 0) := rfl

/-- The canonical `𝔽_p`-linear map `θ_d : (F(d)/F(d)^2)^{⊗1} → E(d,(1,1))`; by construction it
is the tensor power of the identity on `F(d)/F(d)^2`, transported along `eLin`. -/
noncomputable def theta (p : ℕ) (G : Type*) [Group G] (d : ℕ) :
    (⨂[ZMod p]^1 (squareQuotient p G d)) →ₗ[ZMod p] E p G d 1 1 :=
  PiTensorProduct.lift (t1Map p G d)

lemma theta_tprod (p : ℕ) (G : Type*) [Group G] (d : ℕ)
    (f : Fin 1 → squareQuotient p G d) :
    theta p G d ((PiTensorProduct.tprod (ZMod p)) f) = eLin p G d (f 0) := by
  rw [theta, PiTensorProduct.lift.tprod, t1Map_apply]

theorem theta_surjective (p : ℕ) (G : Type*) [Group G] (d : ℕ) :
    Function.Surjective (theta p G d) := by
  intro z
  obtain ⟨y, hy⟩ := eLin_surjective p G d z
  exact ⟨(PiTensorProduct.tprod (ZMod p)) (fun _ : Fin 1 => y),
    by rw [theta_tprod]; exact hy⟩

theorem theta_natural (p : ℕ) (G : Type*) [Group G] {m n : ℕ}
    (ψ : Work.Shrinking.freeOperatorGroup G m →* Work.Shrinking.freeOperatorGroup G n)
    (hψ : Function.Surjective ψ) :
    (theta p G n).comp (PiTensorProduct.map (fun _ : Fin 1 => quotMapLin p G ψ hψ))
      = (gradedMapLin p ψ hψ 1 1).comp (theta p G m) := by
  rw [theta, theta, PiTensorProduct.lift_comp_map]
  symm
  refine PiTensorProduct.lift.unique ?_
  intro f
  rw [LinearMap.comp_apply, PiTensorProduct.lift.tprod, t1Map_apply]
  change (gradedMapLin p ψ hψ 1 1) (eLin p G m (f 0)) =
    eLin p G n (quotMapLin p G ψ hψ (f 0))
  simpa only [LinearMap.comp_apply] using
    (congrArg (fun L : squareQuotient p G m →ₗ[ZMod p] E p G n 1 1 =>
      L (f 0)) (eLin_natural p G ψ hψ)).symm

theorem theta_smul (p : ℕ) (G : Type*) [Group G] [NeZero p] (d : ℕ) (g : G)
    (x : ⨂[ZMod p]^1 (squareQuotient p G d)) :
    theta p G d (g • x) = g • theta p G d x := by
  have hg : g • x =
      PiTensorProduct.map (fun _ : Fin 1 => Work.Shrinking.actLinear (p := p) g) x := rfl
  have h1 : (PiTensorProduct.lift (t1Map p G d))
        ((PiTensorProduct.map (fun _ : Fin 1 => Work.Shrinking.actLinear (p := p) g)) x)
      = PiTensorProduct.lift ((t1Map p G d).compLinearMap
          (fun _ : Fin 1 => Work.Shrinking.actLinear (p := p) g)) x := by
    have h := LinearMap.congr_fun (PiTensorProduct.lift_comp_map
      (fun _ : Fin 1 => Work.Shrinking.actLinear (p := p) g) (t1Map p G d)) x
    rwa [LinearMap.comp_apply] at h
  have key : PiTensorProduct.lift ((t1Map p G d).compLinearMap
        (fun _ : Fin 1 => Work.Shrinking.actLinear (p := p) g))
      = (Work.Shrinking.actLinear (p := p) g).comp (PiTensorProduct.lift (t1Map p G d)) := by
    symm
    refine PiTensorProduct.lift.unique ?_
    intro f
    rw [LinearMap.comp_apply, PiTensorProduct.lift.tprod, t1Map_apply]
    show (Work.Shrinking.actLinear (p := p) g) (eLin p G d (f 0)) =
      (t1Map p G d).compLinearMap (fun _ : Fin 1 => Work.Shrinking.actLinear (p := p) g) f
    rw [show (t1Map p G d).compLinearMap
          (fun _ : Fin 1 => Work.Shrinking.actLinear (p := p) g) f
        = eLin p G d (Work.Shrinking.actLinear (p := p) g (f 0)) from rfl]
    rw [Work.Shrinking.actLinear_apply]
    exact (eLin_smul p G d g (f 0)).symm
  rw [theta, hg, h1, key, LinearMap.comp_apply, Work.Shrinking.actLinear_apply]

/-- **The case `τ = (1,1)` of Proposition 5.**  The data `Prop5Data p G 1 1` is unconditional:
the graded piece `E(d,(1,1))` is `F(d)/F(d)^2` and `θ` is the canonical identification. -/
theorem nonempty_prop5Data_one_one (p : ℕ) [NeZero p] (G : Type*) [Group G] :
    Nonempty (Work.CohomologicalShrinking.Prop5Data p G 1 1) := by
  refine ⟨fun d => theta p G d, ?_, ?_, ?_⟩
  · intro d g x
    exact theta_smul p G d g x
  · intro d
    exact theta_surjective p G d
  · intro m n ψ hψ hψG
    exact theta_natural p G ψ hψ

end Work.CohomologicalShrinking
