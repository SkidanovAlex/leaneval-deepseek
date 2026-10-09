import Mathlib
import Submission.Work.SSGRoute.ExtChain.subsingleton_ext_fpRegular
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt
open scoped MonoidAlgebra

noncomputable section

set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G]

/-! ## 1. `Ext` transfers along a retract -/

theorem ext2p_subsingleton_of_retract {N F A : Rep.{0} Coeff G}
    (s : N ⟶ F) (r : F ⟶ N) (hsr : s ≫ r = 𝟙 N)
    (hF : Subsingleton (CategoryTheory.Abelian.Ext.{0} F A 2)) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0} N A 2) := by
  refine ⟨fun z w => ?_⟩
  have h1 : (CategoryTheory.Abelian.Ext.mk₀ r).comp z (zero_add 2) =
      (CategoryTheory.Abelian.Ext.mk₀ r).comp w (zero_add 2) := hF.elim _ _
  have h2 := congrArg (fun t : CategoryTheory.Abelian.Ext.{0} F A 2 =>
    (CategoryTheory.Abelian.Ext.mk₀ s).comp t (zero_add 2)) h1
  rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc s r z,
      CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc s r w, hsr,
      CategoryTheory.Abelian.Ext.mk₀_id_comp,
      CategoryTheory.Abelian.Ext.mk₀_id_comp] at h2
  exact h2

/-! ## 2. Plumbing: module structures read off a representation -/

/-- The `DistribMulAction` of `G` on the carrier of a representation, read off from `N.ρ`. -/
def ext2p_repDistribMulAction (N : Rep.{0} Coeff G) : DistribMulAction G N.V where
  smul g v := N.ρ g v
  one_smul v := by show N.ρ 1 v = v; rw [map_one]; rfl
  mul_smul g h v := by show N.ρ (g * h) v = N.ρ g (N.ρ h v); rw [map_mul]; rfl
  smul_zero g := (N.ρ g).map_zero
  smul_add g v w := (N.ρ g).map_add v w

/-- An additive map between `Coeff`-modules is `Coeff`-linear (`Coeff = ULift ℤ`). -/
def ext2p_addHom_coeffLinear {V W : Type} [AddCommGroup V] [AddCommGroup W]
    [Module Coeff V] [Module Coeff W] (f : V →+ W) : V →ₗ[Coeff] W where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    simp only [RingHom.id_apply]
    have h1 : c = ((c.down : ℤ) : Coeff) := by apply ULift.ext; rfl
    rw [h1, Int.cast_smul_eq_zsmul Coeff c.down x,
      Int.cast_smul_eq_zsmul Coeff c.down (f x)]
    exact map_zsmul f c.down x

/-- The `MonoidAlgebra k G`-module structure on a `k`-module with a commuting `G`-action. -/
def ext2p_algModuleOfAction (k : Type) [CommSemiring k] (M : Type) [AddCommGroup M] [Module k M]
    [DistribMulAction G M] [SMulCommClass G k M] : Module (MonoidAlgebra k G) M :=
  Module.compHom M ((Representation.ofDistribMulAction k G M).asAlgebraHom).toRingHom

/-! ## 3. The two-term free resolution of `𝔽_p[G]^{(α)}` -/

theorem ext2p_leftRegularReduceFun_add (x y : MonoidAlgebra Coeff G) :
    leftRegularReduceFun p G (x + y)
      = leftRegularReduceFun p G x + leftRegularReduceFun p G y := by
  ext a
  simp only [leftRegularReduceFun_coeff, MonoidAlgebra.coeff_add, Finsupp.add_apply]
  rw [show (x.coeff a + y.coeff a).down = (x.coeff a).down + (y.coeff a).down from rfl,
    Int.cast_add]

/-- A lift of `𝔽_p[G]` to `ℤ[G]`, coefficientwise (`z ↦ z.val`). -/
def ext2p_liftP (w : MonoidAlgebra (ZMod p) G) : MonoidAlgebra Coeff G :=
  MonoidAlgebra.ofCoeff (Finsupp.mapRange (fun c : ZMod p => ULift.up ((c.val : ℤ)))
    (by rw [ZMod.val_zero]; rfl) w.coeff)

theorem ext2p_liftP_zero : ext2p_liftP (p := p) (G := G) 0 = 0 := by
  simp [ext2p_liftP]

theorem ext2p_liftP_reduce (w : MonoidAlgebra (ZMod p) G) :
    leftRegularReduceFun p G (ext2p_liftP (p := p) (G := G) w) = w :=
  leftRegularReduceFun_mapRange_val p G w

/-- Division by `p` on the coefficients. -/
def ext2p_divP (w : MonoidAlgebra Coeff G) : MonoidAlgebra Coeff G :=
  MonoidAlgebra.ofCoeff (Finsupp.mapRange (fun c : Coeff => ULift.up ((c.down : ℤ) / (p : ℤ)))
    (by rw [ULift.zero_down, Int.zero_ediv]; rfl) w.coeff)

theorem ext2p_divP_zero : ext2p_divP (p := p) (G := G) 0 = 0 := by
  simp [ext2p_divP]

theorem ext2p_divP_smul (w : MonoidAlgebra Coeff G) (hw : leftRegularReduceFun p G w = 0) :
    (p : Coeff) • ext2p_divP (p := p) (G := G) w = w := by
  ext a
  have hw' : ((w.coeff a).down : ZMod p) = 0 := by
    have h := congrArg (fun z : MonoidAlgebra (ZMod p) G => z.coeff a) hw
    simpa [leftRegularReduceFun_coeff] using h
  rw [coeff_smul_leftRegular, ULift.mul_down, ULift.down_natCast]
  simp only [ext2p_divP, MonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply, ULift.down_up]
  exact Int.mul_ediv_cancel' ((ZMod.intCast_zmod_eq_zero_iff_dvd (w.coeff a).down p).mp hw')

/-- The action of `Rep.free Coeff G α` on `α →₀ ℤ[G]` is pointwise. -/
theorem ext2p_free_finsupp_action (α : Type) (g : G) (x : α →₀ MonoidAlgebra Coeff G) :
    ((Rep.free Coeff G α).ρ g) x
      = x.mapRange (((Representation.leftRegular Coeff G) g)) (map_zero _) := by
  change ((Representation.leftRegular Coeff G).finsupp α) g x = _
  induction x using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [map_add, Finsupp.mapRange_add
      (fun u v => (((Representation.leftRegular Coeff G) g)).map_add u v),
      ih, Representation.finsupp_single, Finsupp.mapRange_single]

/-- The regular action on the group algebra is left multiplication. -/
theorem ext2p_leftRegular_eq_mul (g : G) (y : MonoidAlgebra Coeff G) :
    (Representation.leftRegular Coeff G) g y = (MonoidAlgebra.of Coeff G g) * y := by
  rw [← Representation.asAlgebraHom_of (Representation.leftRegular Coeff G) g,
      Representation.asAlgebraHom_ofMulAction_smul_eq_mul]

/-- The reduction is compatible with the regular action. -/
theorem ext2p_leftRegularReduceFun_rho (g : G) (y : MonoidAlgebra Coeff G) :
    leftRegularReduceFun p G ((Representation.leftRegular Coeff G) g y)
      = (Representation.leftRegular (ZMod p) G) g (leftRegularReduceFun p G y) := by
  ext h
  rw [leftRegularReduceFun_coeff, Representation.coeff_ofMulAction, Representation.coeff_ofMulAction,
    leftRegularReduceFun_coeff]

/-- The action of `modRep G (α →₀ 𝔽_p[G])` on `α →₀ 𝔽_p[G]` is pointwise. -/
theorem ext2p_Gaction_pointwise (α : Type) (g : G) (y : α →₀ MonoidAlgebra (ZMod p) G) :
    (modRep G (α →₀ MonoidAlgebra (ZMod p) G)).ρ g y
      = y.mapRange ((Representation.leftRegular (ZMod p) G) g) (map_zero _) := by
  apply Finsupp.ext; intro a
  rw [Finsupp.mapRange_apply]
  rw [show (modRep G (α →₀ MonoidAlgebra (ZMod p) G)).ρ g y
        = (MonoidAlgebra.of (ZMod p) G g) • y from rfl, Finsupp.smul_apply,
      ← Representation.asAlgebraHom_of (Representation.leftRegular (ZMod p) G) g,
      Representation.asAlgebraHom_ofMulAction_smul_eq_mul]
  simp only [smul_eq_mul]

/-- Multiplication by `p` on `α →₀ ℤ[G]`, as a linear map. -/
def ext2p_freeMulLin (α : Type) :
    (α →₀ MonoidAlgebra Coeff G) →ₗ[Coeff] (α →₀ MonoidAlgebra Coeff G) :=
  (p : Coeff) • (LinearMap.id : (α →₀ MonoidAlgebra Coeff G) →ₗ[Coeff]
    (α →₀ MonoidAlgebra Coeff G))

theorem ext2p_freeMulLin_apply (α : Type) (x : α →₀ MonoidAlgebra Coeff G) :
    ext2p_freeMulLin (p := p) (G := G) α x = (p : Coeff) • x := rfl

/-- Multiplication by `p` on `α →₀ ℤ[G]`, as a morphism of `G`-representations. -/
def ext2p_freeMulP (α : Type) : Rep.free Coeff G α ⟶ Rep.free Coeff G α :=
  Rep.ofHom
    { toLinearMap := ext2p_freeMulLin (p := p) (G := G) α
      isIntertwining' := fun g => by
        apply LinearMap.ext; intro x
        show ext2p_freeMulLin (p := p) (G := G) α (((Rep.free Coeff G α).ρ g) x)
           = ((Rep.free Coeff G α).ρ g) (ext2p_freeMulLin (p := p) (G := G) α x)
        rw [ext2p_freeMulLin_apply, ext2p_freeMulLin_apply, map_smul] }

theorem ext2p_freeMulP_hom (α : Type) (x : α →₀ MonoidAlgebra Coeff G) :
    (ext2p_freeMulP (p := p) (G := G) α).hom x = (p : Coeff) • x := rfl

/-- The coefficientwise reduction `α →₀ ℤ[G] → α →₀ 𝔽_p[G]`, as a linear map. -/
def ext2p_freeReduceLin (α : Type) :
    (α →₀ MonoidAlgebra Coeff G) →ₗ[Coeff] (α →₀ MonoidAlgebra (ZMod p) G) :=
  { toFun := fun x => x.mapRange (leftRegularReduceFun p G) (by simp [leftRegularReduceFun])
    map_add' := fun x y =>
      Finsupp.mapRange_add (ext2p_leftRegularReduceFun_add (p := p) (G := G)) x y
    map_smul' := fun c x =>
      Finsupp.mapRange_smul c x (fun y => leftRegularReduceFun_smul p G c y) }

theorem ext2p_freeReduceLin_apply (α : Type) (x : α →₀ MonoidAlgebra Coeff G) :
    ext2p_freeReduceLin (p := p) (G := G) α x
      = x.mapRange (leftRegularReduceFun p G) (by simp [leftRegularReduceFun]) := rfl

/-- The coefficientwise reduction, as a morphism of `G`-representations. -/
def ext2p_freeReduce (α : Type) :
    Rep.free Coeff G α ⟶ modRep G (α →₀ MonoidAlgebra (ZMod p) G) :=
  Rep.ofHom
    { toLinearMap := ext2p_freeReduceLin (p := p) (G := G) α
      isIntertwining' := fun g => by
        apply LinearMap.ext; intro x
        show ext2p_freeReduceLin (p := p) (G := G) α (((Rep.free Coeff G α).ρ g) x)
           = ((modRep G (α →₀ MonoidAlgebra (ZMod p) G)).ρ g)
              (ext2p_freeReduceLin (p := p) (G := G) α x)
        rw [ext2p_free_finsupp_action α g x, ext2p_freeReduceLin_apply,
          ext2p_Gaction_pointwise α g _]
        apply Finsupp.ext; intro a
        simp only [Finsupp.mapRange_apply]
        exact ext2p_leftRegularReduceFun_rho g (x a) }

theorem ext2p_freeReduce_hom (α : Type) (x : α →₀ MonoidAlgebra Coeff G) :
    (ext2p_freeReduce (p := p) (G := G) α).hom x
      = x.mapRange (leftRegularReduceFun p G) (by simp [leftRegularReduceFun]) := rfl

theorem ext2p_mono_freeMulP (α : Type) : Mono (ext2p_freeMulP (p := p) (G := G) α) := by
  rw [Rep.mono_iff_injective]
  intro x y h
  have h3 : (p : Coeff) • (show α →₀ MonoidAlgebra Coeff G from x)
      = (p : Coeff) • (show α →₀ MonoidAlgebra Coeff G from y) := by
    have h4 := h
    rw [ext2p_freeMulP_hom (p := p) (G := G) α,
        ext2p_freeMulP_hom (p := p) (G := G) α] at h4
    exact h4
  apply Finsupp.ext; intro a
  exact smulByP_injective p G (by
    have h5 := congrArg (fun z : α →₀ MonoidAlgebra Coeff G => z a) h3
    rwa [Finsupp.smul_apply, Finsupp.smul_apply] at h5)

theorem ext2p_epi_freeReduce (α : Type) : Epi (ext2p_freeReduce (p := p) (G := G) α) := by
  rw [Rep.epi_iff_surjective]
  intro y
  refine ⟨Finsupp.mapRange (ext2p_liftP (p := p) (G := G)) (ext2p_liftP_zero (p := p) (G := G))
    (show α →₀ MonoidAlgebra (ZMod p) G from y), ?_⟩
  rw [ext2p_freeReduce_hom]
  apply Finsupp.ext; intro a
  rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply]
  exact ext2p_liftP_reduce (p := p) (G := G) _

theorem ext2p_exact_freeReduce (α : Type) {x : α →₀ MonoidAlgebra Coeff G}
    (hx : (ext2p_freeReduce (p := p) (G := G) α).hom x = 0) :
    ∃ y, (ext2p_freeMulP (p := p) (G := G) α).hom y = x := by
  have hx' : ∀ a, leftRegularReduceFun p G (x a) = 0 := fun a => by
    have h0 : x.mapRange (leftRegularReduceFun p G) (by simp [leftRegularReduceFun]) = 0 := by
      have h1 := hx
      rw [ext2p_freeReduce_hom] at h1
      exact h1
    have h := congrArg (fun z : α →₀ MonoidAlgebra (ZMod p) G => z a) h0
    rw [Finsupp.mapRange_apply, Finsupp.zero_apply] at h
    exact h
  refine ⟨Finsupp.mapRange (ext2p_divP (p := p) (G := G)) (ext2p_divP_zero (p := p) (G := G)) x, ?_⟩
  rw [ext2p_freeMulP_hom]
  apply Finsupp.ext; intro a
  simp only [Finsupp.smul_apply, Finsupp.mapRange_apply]
  exact ext2p_divP_smul (p := p) (G := G) (x a) (hx' a)

/-- The two-term free resolution `0 → ℤ[G]^{(α)} --p--> ℤ[G]^{(α)} → 𝔽_p[G]^{(α)} → 0`. -/
def ext2p_freeSES (α : Type) : ShortComplex (Rep.{0, 0, 0} Coeff G) :=
  ShortComplex.mk (ext2p_freeMulP (p := p) (G := G) α) (ext2p_freeReduce (p := p) (G := G) α) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    show (ext2p_freeReduce (p := p) (G := G) α).hom
      ((ext2p_freeMulP (p := p) (G := G) α).hom x) = 0
    rw [ext2p_freeMulP_hom]
    rw [show (ext2p_freeReduce (p := p) (G := G) α).hom ((p : Coeff) • x)
          = (p : Coeff) • (ext2p_freeReduce (p := p) (G := G) α).hom x from map_smul _ _ _]
    rw [ext2p_freeReduce_hom]
    apply Finsupp.ext; intro a
    show (p : Coeff) • (leftRegularReduceFun p G (x a)) = 0
    rw [← leftRegularReduceFun_smul p G (p : Coeff) (x a), leftRegularReduceFun_smulByP])

theorem ext2p_freeSES_shortExact (α : Type) :
    (ext2p_freeSES (p := p) (G := G) α).ShortExact := by
  refine Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise
    (k := Coeff) (G := G) (ext2p_freeSES (p := p) (G := G) α)
    (ext2p_mono_freeMulP (p := p) (G := G) α) (ext2p_epi_freeReduce (p := p) (G := G) α) ?_
  intro x hx
  exact ext2p_exact_freeReduce (p := p) (G := G) α hx

/-- **`Ext^{≥2}` of a free `𝔽_p[G]`-module vanishes.** -/
theorem ext2p_subsingleton_ext_fpFree (α : Type) (A : Rep.{0} Coeff G) (r : ℕ) (hr : 2 ≤ r) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0}
      (modRep G (α →₀ MonoidAlgebra (ZMod p) G)) A r) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  haveI h1 : Projective (ext2p_freeSES (p := p) (G := G) α).X₁ :=
    Rep.free_projective (k := Coeff) (G := G) (α := α)
  haveI h2 : Projective (ext2p_freeSES (p := p) (G := G) α).X₂ :=
    Rep.free_projective (k := Coeff) (G := G) (α := α)
  exact subsingleton_ext_add_two_of_projective (ext2p_freeSES (p := p) (G := G) α)
    (ext2p_freeSES_shortExact (p := p) (G := G) α) A m

/-! ## 4. The retraction onto a free `𝔽_p[H]`-module -/

theorem ext2p_exists_retract (H : Type) [Group H] (hp : p ≠ 2) (hH : Nat.card H = 2)
    (N : Rep.{0} Coeff H) [Finite N.V] (hN : ∀ x : N.V, (p : Coeff) • x = 0) :
    ∃ (s : N ⟶ modRep H (N.V →₀ MonoidAlgebra (ZMod p) H))
      (r : modRep H (N.V →₀ MonoidAlgebra (ZMod p) H) ⟶ N), s ≫ r = 𝟙 N := by
  classical
  haveI : Finite H := (Nat.card_ne_zero.mp (by rw [hH]; norm_num)).2
  haveI : Fintype H := Fintype.ofFinite H
  haveI hNe : NeZero (Nat.card H : ZMod p) := by
    rw [hH]
    refine ⟨fun h => ?_⟩
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hp ((Nat.Prime.dvd_iff_eq (by norm_num) (Fact.out : p.Prime).ne_one).mp h).symm
  letI : DistribMulAction H N.V := ext2p_repDistribMulAction (G := H) N
  haveI : Module (ZMod p) N.V := AddCommGroup.zmodModule (fun x => by
    rw [← Nat.cast_smul_eq_nsmul Coeff p x]; exact hN x)
  haveI : SMulCommClass H (ZMod p) N.V := ⟨fun h a v => by
    show N.ρ h (a • v) = a • (N.ρ h v)
    rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul (ZMod p) a.val v,
        Nat.cast_smul_eq_nsmul (ZMod p) a.val (N.ρ h v), map_nsmul]⟩
  letI : Module (MonoidAlgebra (ZMod p) H) N.V := ext2p_algModuleOfAction (G := H) (ZMod p) N.V
  have key1 : ∀ (g : H) (x : N.V →₀ MonoidAlgebra (ZMod p) H),
      (modRep H (N.V →₀ MonoidAlgebra (ZMod p) H)).ρ g x
        = (MonoidAlgebra.of (ZMod p) H g) • x := fun _ _ => rfl
  have key2 : ∀ (g : H) (y : N.V), N.ρ g y = (MonoidAlgebra.of (ZMod p) H g) • y := by
    intro g y
    change N.ρ g y = ((Representation.ofDistribMulAction (ZMod p) H N.V).asAlgebraHom
      (MonoidAlgebra.of (ZMod p) H g)) y
    rw [Representation.asAlgebraHom_of]
    rfl
  let π : (N.V →₀ MonoidAlgebra (ZMod p) H) →ₗ[MonoidAlgebra (ZMod p) H] N.V :=
    Finsupp.linearCombination (MonoidAlgebra (ZMod p) H) (fun v : N.V => v)
  have hπsurj : Function.Surjective π := by
    intro y
    exact ⟨Finsupp.single y 1, by rw [Finsupp.linearCombination_single]; simp⟩
  -- Maschke: a complement of `ker π`
  obtain ⟨C, hC⟩ := MonoidAlgebra.Submodule.exists_isCompl
    (p := LinearMap.ker π)
  have hCker : ∀ x : C, π (x : N.V →₀ MonoidAlgebra (ZMod p) H) = 0 → x = 0 := by
    intro x hx
    have hmem : (x : N.V →₀ MonoidAlgebra (ZMod p) H) ∈ LinearMap.ker π ⊓ C :=
      ⟨hx, x.2⟩
    rw [hC.1.eq_bot, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  have hCtop : ∀ y : N.V, ∃ x : C, π (x : N.V →₀ MonoidAlgebra (ZMod p) H) = y := by
    intro y
    obtain ⟨z, hz⟩ := hπsurj y
    have hmem : z ∈ LinearMap.ker π ⊔ C := by rw [hC.2.eq_top]; trivial
    rw [Submodule.mem_sup] at hmem
    obtain ⟨a, ha, b, hb, hab⟩ := hmem
    refine ⟨⟨b, hb⟩, ?_⟩
    rw [← hz, ← hab, map_add, ha, zero_add]
  have hbij : Function.Bijective (fun x : C => π (x : N.V →₀ MonoidAlgebra (ZMod p) H)) :=
    ⟨fun x y hxy => sub_eq_zero.mp (hCker (x - y) (by
      have hxy' : π (x : N.V →₀ MonoidAlgebra (ZMod p) H)
          = π (y : N.V →₀ MonoidAlgebra (ZMod p) H) := hxy
      rw [Submodule.coe_sub, map_sub, hxy', sub_self])), hCtop⟩
  let e : C ≃ₗ[MonoidAlgebra (ZMod p) H] N.V :=
    LinearEquiv.ofBijective ((π.comp C.subtype)) hbij
  let h : N.V →ₗ[MonoidAlgebra (ZMod p) H] (N.V →₀ MonoidAlgebra (ZMod p) H) :=
    C.subtype.comp e.symm.toLinearMap
  have hh : π.comp h = LinearMap.id := by
    ext y
    show π (e.symm y : N.V →₀ MonoidAlgebra (ZMod p) H) = y
    have : e (e.symm y) = y := e.apply_symm_apply y
    exact this
  refine ⟨?_, ?_, ?_⟩
  · refine Rep.ofHom (Representation.IntertwiningMap.mk
      (ext2p_addHom_coeffLinear h.toAddMonoidHom) ?_)
    intro g
    apply LinearMap.ext; intro y
    show (ext2p_addHom_coeffLinear h.toAddMonoidHom) (N.ρ g y)
      = (modRep H (N.V →₀ MonoidAlgebra (ZMod p) H)).ρ g
          ((ext2p_addHom_coeffLinear h.toAddMonoidHom) y)
    rw [key2 g y, key1 g ((ext2p_addHom_coeffLinear h.toAddMonoidHom) y)]
    show h ((MonoidAlgebra.of (ZMod p) H g) • y) = (MonoidAlgebra.of (ZMod p) H g) • h y
    rw [map_smul]
  · refine Rep.ofHom (Representation.IntertwiningMap.mk
      (ext2p_addHom_coeffLinear π.toAddMonoidHom) ?_)
    intro g
    apply LinearMap.ext; intro x
    show (ext2p_addHom_coeffLinear π.toAddMonoidHom)
          ((modRep H (N.V →₀ MonoidAlgebra (ZMod p) H)).ρ g x)
      = N.ρ g ((ext2p_addHom_coeffLinear π.toAddMonoidHom) x)
    rw [key1 g x, key2 g ((ext2p_addHom_coeffLinear π.toAddMonoidHom) x)]
    show π ((MonoidAlgebra.of (ZMod p) H g) • x) = (MonoidAlgebra.of (ZMod p) H g) • π x
    rw [map_smul]
  · apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext; intro y
    show (ext2p_addHom_coeffLinear π.toAddMonoidHom)
      ((ext2p_addHom_coeffLinear h.toAddMonoidHom) y) = y
    show π (h y) = y
    have hc := LinearMap.congr_fun hh y
    simpa [LinearMap.comp_apply] using hc

/-! ## 5. The target -/

/-- **Odd-characteristic vanishing of `Ext²` in a `p`-torsion first variable.**  For a group `H` of
order two, a prime `p ≠ 2` and a finite representation `N` on which `p` acts as `0` — i.e. an
`𝔽_p[H]`-module — the second `Ext` group `Ext²_H(N,A)` vanishes for every coefficient `A`.

Because `p` is odd, `𝔽_p[H]` is semisimple: `N` is a direct summand of a free `𝔽_p[H]`-module `F`,
hence of `(𝔽_p[H])^n`; the two-term free resolution `0 → ℤ[H] --p--> ℤ[H] → 𝔽_p[H] → 0` of the
regular module (`ExtChain.subsingleton_ext_fpRegular`) gives `Ext^{≥2}_H(𝔽_p[H],A) = 0`, and
`Ext` is additive in the first variable, so `Ext²_H(N,A) = 0`. -/
theorem ext2_fn_p_odd_proved {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {H : Type} [Group H]
    (hH : Nat.card H = 2) (N : Rep.{0} SSGRoute.PTExt.Coeff H) [Finite N.V]
    (hN : ∀ x : N.V, (p : SSGRoute.PTExt.Coeff) • x = 0) (A : Rep.{0} SSGRoute.PTExt.Coeff H) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0} N A 2) := by
  obtain ⟨s, r, hsr⟩ := ext2p_exists_retract (p := p) H hp hH N hN
  exact ext2p_subsingleton_of_retract (G := H) s r hsr
    (ext2p_subsingleton_ext_fpFree (p := p) (G := H) N.V A 2 le_rfl)

end

end Work.SSGRoute.ExtChain
