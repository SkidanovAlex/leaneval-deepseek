import Mathlib
import Submission.Work.CharPrelim.modular_frobenius_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Auxiliary material for the modular Frobenius fixed point dimension formula

This file collects the module-theoretic infrastructure used in
`Work.CharPrelim.frobenius_finrank_algClosed`.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

open Classical
open scoped MonoidAlgebra Pointwise

namespace Work.CharPrelim

variable {k : Type*} [Field k]

/-! ## Restrictions of representations to invariant subspaces -/

section Basics

variable {L : Type*} [Group L] {W : Type*} [AddCommGroup W] [Module k W]

/-- Restriction of a representation to an invariant submodule. -/
def repRestrict (ρ : Representation k L W) (M : Submodule k W)
    (hM : ∀ g : L, ∀ u ∈ M, ρ g u ∈ M) : Representation k L M where
  toFun g :=
    { toFun := fun u => ⟨ρ g u, hM g u u.2⟩
      map_add' := fun a b => by ext; simp
      map_smul' := fun c a => by ext; simp }
  map_one' := by ext u; simp
  map_mul' g h := by ext u; simp [Module.End.mul_apply]

@[simp] lemma repRestrict_apply (ρ : Representation k L W) (M : Submodule k W)
    (hM : ∀ g : L, ∀ u ∈ M, ρ g u ∈ M) (g : L) (u : M) :
    ((repRestrict ρ M hM g u : M) : W) = ρ g u := rfl

/-- Monotonicity of invariants in the subgroup. -/
lemma invariants_mono (ρ : Representation k L W) {H H' : Subgroup L} (h : H ≤ H') :
    Representation.invariants (ρ.comp H'.subtype) ≤
      Representation.invariants (ρ.comp H.subtype) := by
  intro v hv
  rw [Representation.mem_invariants] at hv ⊢
  intro x
  exact hv ⟨(x : L), h x.2⟩

end Basics

/-! ## Stability, equivariance, simplicity -/

section Stab

variable {L : Type*} [Group L] {W : Type*} [AddCommGroup W] [Module k W]

/-- `U` is stable under the action of the subgroup `K`. -/
abbrev IsStable (ρ : Representation k L W) (K : Subgroup L) (U : Submodule k W) : Prop :=
  ∀ x : ↥K, ∀ u ∈ U, ρ (x : L) u ∈ U

lemma IsStable.bot (ρ : Representation k L W) (K : Subgroup L) : IsStable ρ K ⊥ := by
  intro x u hu
  rw [Submodule.mem_bot] at hu
  rw [hu, map_zero]
  exact Submodule.zero_mem _

lemma IsStable.top (ρ : Representation k L W) (K : Subgroup L) : IsStable ρ K ⊤ :=
  fun _ _ _ => Submodule.mem_top

/-- The action of `K` on a stable subspace. -/
def actOn (ρ : Representation k L W) (K : Subgroup L) {U : Submodule k W}
    (hU : IsStable ρ K U) (x : ↥K) : ↥U →ₗ[k] ↥U where
  toFun u := ⟨ρ (x : L) u, hU x u u.2⟩
  map_add' a b := by ext; simp
  map_smul' c a := by ext; simp

@[simp] lemma actOn_coe (ρ : Representation k L W) (K : Subgroup L) {U : Submodule k W}
    (hU : IsStable ρ K U) (x : ↥K) (u : ↥U) :
    ((actOn ρ K hU x u : ↥U) : W) = ρ (x : L) u := rfl

lemma actOn_one (ρ : Representation k L W) (K : Subgroup L) {U : Submodule k W}
    (hU : IsStable ρ K U) : actOn ρ K hU (1 : ↥K) = 1 := by
  ext u; simp

lemma actOn_mul (ρ : Representation k L W) (K : Subgroup L) {U : Submodule k W}
    (hU : IsStable ρ K U) (x y : ↥K) :
    actOn ρ K hU (x * y) = actOn ρ K hU x * actOn ρ K hU y := by
  ext u; simp [Module.End.mul_apply]

/-- The `K`-representation on a stable subspace. -/
def repOn (ρ : Representation k L W) (K : Subgroup L) {U : Submodule k W}
    (hU : IsStable ρ K U) : Representation k ↥K ↥U where
  toFun := actOn ρ K hU
  map_one' := actOn_one ρ K hU
  map_mul' := actOn_mul ρ K hU

@[simp] lemma repOn_apply (ρ : Representation k L W) (K : Subgroup L) {U : Submodule k W}
    (hU : IsStable ρ K U) (x : ↥K) : repOn ρ K hU x = actOn ρ K hU x := rfl

/-- `K`-equivariance of a linear map between stable subspaces. -/
abbrev IsEquiv (ρ : Representation k L W) (K : Subgroup L) {U U' : Submodule k W}
    (hU : IsStable ρ K U) (hU' : IsStable ρ K U') (f : ↥U →ₗ[k] ↥U') : Prop :=
  ∀ x : ↥K, f.comp (actOn ρ K hU x) = (actOn ρ K hU' x).comp f

lemma IsEquiv.coe_apply (ρ : Representation k L W) (K : Subgroup L) {U U' : Submodule k W}
    {hU : IsStable ρ K U} {hU' : IsStable ρ K U'} {f : ↥U →ₗ[k] ↥U'}
    (hf : IsEquiv ρ K hU hU' f) (x : ↥K) (u : ↥U) :
    ((f (actOn ρ K hU x u) : ↥U') : W) = ρ (x : L) (f u : W) := by
  have h := congrArg (fun (g : ↥U →ₗ[k] ↥U') => g u) (hf x)
  simp only [LinearMap.comp_apply] at h
  exact congrArg (fun w : ↥U' => (w : W)) h

/-- `U` is a simple `K`-module: nonzero with no proper nonzero stable subspace. -/
abbrev IsSimpleStable (ρ : Representation k L W) (K : Subgroup L) (U : Submodule k W) : Prop :=
  IsStable ρ K U ∧ U ≠ ⊥ ∧
    ∀ U' : Submodule k W, U' ≤ U → IsStable ρ K U' → U' ≠ ⊥ → U' = U

lemma IsStable.map_conj (ρ : Representation k L W) {K : Subgroup L} [K.Normal]
    {U : Submodule k W} (hU : IsStable ρ K U) (e : L) : IsStable ρ K (U.map (ρ e)) := by
  intro x v hv
  obtain ⟨u, hu, rfl⟩ := hv
  refine ⟨ρ (e⁻¹ * (x : L) * e) u,
    hU ⟨e⁻¹ * (x : L) * e, (inferInstance : K.Normal).conj_mem' (x : L) x.2 e⟩ u hu, ?_⟩
  show ρ e (ρ (e⁻¹ * (x : L) * e) u) = ρ (x : L) (ρ e u)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 1
  group

lemma IsSimpleStable.map_conj (ρ : Representation k L W) {K : Subgroup L} [K.Normal]
    {U : Submodule k W} (hs : IsSimpleStable ρ K U) (e : L) :
    IsSimpleStable ρ K (U.map (ρ e)) := by
  have hU := hs.1
  refine ⟨IsStable.map_conj ρ hU e, ?_, ?_⟩
  · intro h
    apply hs.2.1
    rw [Submodule.eq_bot_iff]
    intro u hu
    have hmem : ρ e u ∈ U.map (ρ e) := ⟨u, hu, rfl⟩
    rw [h] at hmem
    have h0 : ρ e u = 0 := by simpa using hmem
    calc u = ρ e⁻¹ (ρ e u) := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
      _ = 0 := by rw [h0, map_zero]
  · intro V hle hstab hne
    set U₀ : Submodule k W := V.comap (ρ e) ⊓ U with hU₀
    have hU₀le : U₀ ≤ U := inf_le_right
    have hU₀stab : IsStable ρ K U₀ := by
      intro x u hu
      obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
      have hmem1 : ρ (x : L) u ∈ V.comap (ρ e) := by
        rw [Submodule.mem_comap] at hu1 ⊢
        have hxe : e * (x : L) = (e * (x : L) * e⁻¹) * e := by group
        rw [← Module.End.mul_apply, ← map_mul, hxe, map_mul, Module.End.mul_apply]
        exact hstab ⟨e * (x : L) * e⁻¹, (inferInstance : K.Normal).conj_mem (x : L) x.2 e⟩ _ hu1
      exact Submodule.mem_inf.mpr ⟨hmem1, hU x u hu2⟩
    have hU₀ne : U₀ ≠ ⊥ := by
      intro hbot
      apply hne
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hvU : v ∈ U.map (ρ e) := hle hv
      obtain ⟨u, hu, hvu⟩ := hvU
      have : u ∈ U₀ := by
        refine Submodule.mem_inf.mpr ⟨?_, hu⟩
        rw [Submodule.mem_comap, hvu]
        exact hv
      rw [hbot] at this
      have : u = 0 := by simpa using this
      rw [← hvu, this, map_zero]
    have hU₀U : U₀ = U := hs.2.2 U₀ hU₀le hU₀stab hU₀ne
    have hle' : U.map (ρ e) ≤ V := by
      rintro v ⟨u, hu, rfl⟩
      have : u ∈ U₀ := by rw [hU₀U]; exact hu
      exact (Submodule.mem_inf.mp this).1
    exact le_antisymm hle hle'

/-- Conjugation by `g` as an automorphism of a normal subgroup. -/
def conjMulEquiv {L : Type*} [Group L] (K : Subgroup L) [K.Normal] (g : L) : ↥K ≃* ↥K where
  toFun x := ⟨g * (x : L) * g⁻¹, (inferInstance : K.Normal).conj_mem (x : L) x.2 g⟩
  invFun x := ⟨g⁻¹ * (x : L) * g, (inferInstance : K.Normal).conj_mem' (x : L) x.2 g⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

@[simp] lemma conjMulEquiv_apply {L : Type*} [Group L] (K : Subgroup L) [K.Normal]
    (g : L) (x : ↥K) :
    ((conjMulEquiv K g x : ↥K) : L) = g * (x : L) * g⁻¹ := rfl

end Stab

/-! ## Schur's lemma for simple stable subspaces -/

section Schur

variable {L : Type*} [Group L] {W : Type*} [AddCommGroup W] [Module k W]

/-- The image of the kernel of an equivariant map is stable. -/
lemma IsEquiv.ker_map_stable (ρ : Representation k L W) (K : Subgroup L) {U U' : Submodule k W}
    {hU : IsStable ρ K U} {hU' : IsStable ρ K U'} {f : ↥U →ₗ[k] ↥U'}
    (hf : IsEquiv ρ K hU hU' f) : IsStable ρ K ((LinearMap.ker f).map U.subtype) := by
  intro x w hw
  obtain ⟨v, hv, rfl⟩ := hw
  refine ⟨actOn ρ K hU x v, ?_, rfl⟩
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  change ((f (actOn ρ K hU x v) : ↥U') : W) = (0 : W)
  have h := hf.coe_apply ρ K x v
  have hv0 : ((f v : ↥U') : W) = 0 := by rw [hv]; rfl
  rw [h, hv0, map_zero]

/-- The image of an equivariant map is stable. -/
lemma IsEquiv.range_map_stable (ρ : Representation k L W) (K : Subgroup L) {U U' : Submodule k W}
    {hU : IsStable ρ K U} {hU' : IsStable ρ K U'} {f : ↥U →ₗ[k] ↥U'}
    (hf : IsEquiv ρ K hU hU' f) : IsStable ρ K (f.range.map U'.subtype) := by
  intro x w hw
  obtain ⟨v, hv, rfl⟩ := hw
  obtain ⟨u, rfl⟩ := hv
  exact ⟨f (actOn ρ K hU x u), ⟨actOn ρ K hU x u, rfl⟩, hf.coe_apply ρ K x u⟩

lemma IsEquiv.injective_of_isSimpleStable (ρ : Representation k L W) (K : Subgroup L)
    {U U' : Submodule k W} {hU : IsStable ρ K U} {hU' : IsStable ρ K U'}
    (hs : IsSimpleStable ρ K U) {f : ↥U →ₗ[k] ↥U'} (hf : IsEquiv ρ K hU hU' f) (hne : f ≠ 0) :
    Function.Injective f := by
  rw [← LinearMap.ker_eq_bot]
  by_contra hbot
  have hstab := hf.ker_map_stable ρ K
  have hne' : (LinearMap.ker f).map U.subtype ≠ ⊥ := by
    intro h
    refine hbot ?_
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hmem : (v : W) ∈ (LinearMap.ker f).map U.subtype := ⟨v, hv, rfl⟩
    rw [h] at hmem
    simpa using hmem
  have hUeq : (LinearMap.ker f).map U.subtype = U :=
    hs.2.2 _ (Submodule.map_subtype_le _ _) hstab hne'
  refine hne ?_
  rw [← LinearMap.ker_eq_top]
  rw [Submodule.eq_top_iff']
  intro v
  have hv : (v : W) ∈ (LinearMap.ker f).map U.subtype := by rw [hUeq]; exact v.2
  obtain ⟨w, hw, hwv⟩ := hv
  have hwv' : w = v := Subtype.ext hwv
  rwa [← hwv']

lemma IsEquiv.surjective_of_isSimpleStable (ρ : Representation k L W) (K : Subgroup L)
    {U U' : Submodule k W} {hU : IsStable ρ K U} {hU' : IsStable ρ K U'}
    (hs' : IsSimpleStable ρ K U') {f : ↥U →ₗ[k] ↥U'} (hf : IsEquiv ρ K hU hU' f) (hne : f ≠ 0) :
    Function.Surjective f := by
  have himg : IsStable ρ K (f.range.map U'.subtype) := hf.range_map_stable ρ K
  have hne' : f.range.map U'.subtype ≠ ⊥ := by
    intro h
    refine hne (LinearMap.ext fun u => ?_)
    have hmem : (f u : W) ∈ f.range.map U'.subtype := ⟨f u, ⟨u, rfl⟩, rfl⟩
    rw [h] at hmem
    exact Subtype.ext (by simpa using hmem)
  have heq : f.range.map U'.subtype = U' :=
    hs'.2.2 _ (Submodule.map_subtype_le _ _) himg hne'
  intro v
  have hv : (v : W) ∈ f.range.map U'.subtype := by rw [heq]; exact v.2
  obtain ⟨w, ⟨u, rfl⟩, hwv⟩ := hv
  exact ⟨u, Subtype.ext hwv⟩

lemma IsEquiv.bijective_of_isSimpleStable (ρ : Representation k L W) (K : Subgroup L)
    {U U' : Submodule k W} {hU : IsStable ρ K U} {hU' : IsStable ρ K U'}
    (hs : IsSimpleStable ρ K U) (hs' : IsSimpleStable ρ K U')
    {f : ↥U →ₗ[k] ↥U'} (hf : IsEquiv ρ K hU hU' f) (hne : f ≠ 0) : Function.Bijective f :=
  ⟨hf.injective_of_isSimpleStable ρ K hs hne, hf.surjective_of_isSimpleStable ρ K hs' hne⟩

/-- A simple stable subspace is an irreducible representation of `K`. -/
lemma isSimpleOrder_subrepresentation_of_isSimpleStable (ρ : Representation k L W)
    (K : Subgroup L) {U : Submodule k W} (hs : IsSimpleStable ρ K U) :
    IsSimpleOrder (Subrepresentation (repOn ρ K hs.1)) := by
  have hnt : Nontrivial (Subrepresentation (repOn ρ K hs.1)) := by
    refine ⟨⊥, ⊤, fun h => ?_⟩
    have h2 : (⊥ : Submodule k ↥U) = (⊤ : Submodule k ↥U) :=
      congrArg Subrepresentation.toSubmodule h
    haveI : Nontrivial ↥U := Submodule.nontrivial_iff_ne_bot.mpr hs.2.1
    refine not_subsingleton ↥U ⟨fun a b => ?_⟩
    have ha : a ∈ (⊥ : Submodule k ↥U) := by rw [h2]; exact Submodule.mem_top
    have hb : b ∈ (⊥ : Submodule k ↥U) := by rw [h2]; exact Submodule.mem_top
    rw [Submodule.mem_bot] at ha hb
    rw [ha, hb]
  refine IsSimpleOrder.mk fun a => ?_
  set U' : Submodule k W := a.toSubmodule.map U.subtype with hU'def
  have hle : U' ≤ U := Submodule.map_subtype_le _ _
  have hstab : IsStable ρ K U' := by
    intro x w hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨actOn ρ K hs.1 x v, a.apply_mem_toSubmodule x hv, rfl⟩
  rcases eq_or_ne U' ⊥ with h0 | h0
  · left
    apply Subrepresentation.toSubmodule_injective
    rw [show (⊥ : Subrepresentation (repOn ρ K hs.1)).toSubmodule = ⊥ from rfl]
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hmem : (v : W) ∈ U' := ⟨v, hv, rfl⟩
    rw [h0] at hmem
    simpa using hmem
  · right
    have hUU : U' = U := hs.2.2 U' hle hstab h0
    apply Subrepresentation.toSubmodule_injective
    rw [show (⊤ : Subrepresentation (repOn ρ K hs.1)).toSubmodule = ⊤ from rfl]
    rw [Submodule.eq_top_iff']
    intro v
    have hv : (v : W) ∈ U' := by rw [hUU]; exact v.2
    obtain ⟨w, hw, hwv⟩ := hv
    have hwv' : w = v := Subtype.ext hwv
    rwa [← hwv']

end Schur

/-! ## The conjugates of a simple module are pairwise non-isomorphic -/

section Semilinear

variable {L : Type*} [Group L] {W : Type*} [AddCommGroup W] [Module k W]

lemma rho_mul_apply (ρ : Representation k L W) (a b : L) (w : W) :
    ρ a (ρ b w) = ρ (a * b) w := by
  rw [← Module.End.mul_apply, ← map_mul]

lemma rho_inv_apply (ρ : Representation k L W) (a : L) (w : W) : ρ (a⁻¹) (ρ a w) = w := by
  rw [rho_mul_apply, inv_mul_cancel, map_one]
  rfl

lemma rho_mul_inv_apply (ρ : Representation k L W) (a : L) (w : W) : ρ a (ρ (a⁻¹) w) = w := by
  rw [rho_mul_apply, mul_inv_cancel, map_one]
  rfl

lemma inj_rho (ρ : Representation k L W) (e : L) : Function.Injective (ρ e) := by
  intro a b hab
  have h := congrArg (ρ (e⁻¹)) hab
  simpa [← Module.End.mul_apply, ← map_mul] using h

lemma map_conj_inv_mem (ρ : Representation k L W) {U : Submodule k W} {e : L} {v : W}
    (hv : v ∈ U.map (ρ e)) : ρ e⁻¹ v ∈ U := by
  obtain ⟨u, hu, hvu⟩ := hv
  rw [← hvu, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  simpa using hu

/-- The canonical bijection `U → ρ e U`, `u ↦ ρ e u`. -/
def conjMap (ρ : Representation k L W) (U : Submodule k W) (e : L) :
    ↥U →ₗ[k] ↥(U.map (ρ e)) where
  toFun u := ⟨ρ e u, ⟨u, u.2, rfl⟩⟩
  map_add' a b := by ext; simp
  map_smul' c a := by ext; simp

@[simp] lemma conjMap_apply (ρ : Representation k L W) (U : Submodule k W) (e : L) (u : ↥U) :
    ((conjMap ρ U e u : ↥(U.map (ρ e))) : W) = ρ e u := rfl

/-- The inverse of `conjMap`. -/
def conjMapInv (ρ : Representation k L W) (U : Submodule k W) (e : L) :
    ↥(U.map (ρ e)) →ₗ[k] ↥U where
  toFun v := ⟨ρ e⁻¹ v, map_conj_inv_mem ρ v.2⟩
  map_add' a b := by ext; simp
  map_smul' c a := by ext; simp

@[simp] lemma conjMapInv_apply (ρ : Representation k L W) (U : Submodule k W) (e : L)
    (v : ↥(U.map (ρ e))) : ((conjMapInv ρ U e v : ↥U) : W) = ρ e⁻¹ v := rfl

@[simp] lemma conjMapInv_conjMap (ρ : Representation k L W) (U : Submodule k W) (e : L)
    (u : ↥U) : conjMapInv ρ U e (conjMap ρ U e u) = u := by
  apply Subtype.ext
  simp only [conjMapInv_apply, conjMap_apply]
  simp [← Module.End.mul_apply, ← map_mul]

@[simp] lemma conjMap_conjMapInv (ρ : Representation k L W) (U : Submodule k W) (e : L)
    (v : ↥(U.map (ρ e))) : conjMap ρ U e (conjMapInv ρ U e v) = v := by
  apply Subtype.ext
  simp only [conjMapInv_apply, conjMap_apply]
  simp [← Module.End.mul_apply, ← map_mul]

lemma conjMap_bijective (ρ : Representation k L W) (U : Submodule k W) (e : L) :
    Function.Bijective (conjMap ρ U e) :=
  ⟨fun a b hab => by simpa using congrArg (conjMapInv ρ U e) hab,
   fun v => ⟨conjMapInv ρ U e v, by simp⟩⟩

/-- The `K`-actions on `U` and on `ρ e U` are intertwined by `conjMap`. -/
lemma IsEquiv.conj_comm (ρ : Representation k L W) (K : Subgroup L) [K.Normal]
    {U : Submodule k W} (hU : IsStable ρ K U) {e : L} (x : ↥K) (u : ↥U) :
    actOn ρ K (IsStable.map_conj ρ hU e)
        ⟨e * (x : L) * e⁻¹, (inferInstance : K.Normal).conj_mem (x : L) x.2 e⟩
        (conjMap ρ U e u)
      = conjMap ρ U e (actOn ρ K hU x u) := by
  apply Subtype.ext
  simp only [actOn_coe, conjMap_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 1
  group

/-- **The conjugates of a simple `K`-module under a fixed point free `E`-action are pairwise
non-isomorphic.** -/
theorem no_iso_conj {p : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (ρ : Representation k L W) [Fintype L] [FiniteDimensional k W]
    {K : Subgroup L} [K.Normal] {E : Subgroup L} (hinf : K ⊓ E = ⊥)
    (hcent : ∀ h ∈ K, h ≠ 1 → Subgroup.centralizer ({h} : Set L) ≤ K)
    (hcop : ¬ p ∣ Nat.card ↥K)
    {U : Submodule k W} (hs : IsSimpleStable ρ K U)
    (hUK : ∀ u ∈ U, (∀ x : ↥K, ρ (x : L) u = u) → u = 0)
    {e e' : L} (he : e ∈ E) (he' : e' ∈ E) (hne : e ≠ e')
    {f : ↥(U.map (ρ e)) →ₗ[k] ↥(U.map (ρ e'))}
    (hf : IsEquiv ρ K (IsStable.map_conj ρ hs.1 e) (IsStable.map_conj ρ hs.1 e') f)
    (hfbij : Function.Bijective f) : False := by
  haveI : (repOn ρ K hs.1).IsIrreducible :=
    isSimpleOrder_subrepresentation_of_isSimpleStable ρ K hs
  let ψ : ↥U →ₗ[k] ↥U := (conjMapInv ρ U e').comp (f.comp (conjMap ρ U e))
  have hψapp : ∀ u : ↥U, ψ u = conjMapInv ρ U e' (f (conjMap ρ U e u)) := fun u => rfl
  have hψbij : Function.Bijective ψ := by
    constructor
    · intro a b hab
      have h1 : conjMapInv ρ U e' (f (conjMap ρ U e a)) = conjMapInv ρ U e' (f (conjMap ρ U e b)) := by
        rw [← hψapp a, ← hψapp b]; exact hab
      have h2 : f (conjMap ρ U e a) = f (conjMap ρ U e b) := by
        have := congrArg (conjMap ρ U e') h1
        simpa using this
      exact (conjMap_bijective ρ U e).1 (hfbij.1 h2)
    · intro v
      obtain ⟨z, hz⟩ := hfbij.2 (conjMap ρ U e' v)
      obtain ⟨u, hu⟩ := (conjMap_bijective ρ U e).2 z
      refine ⟨u, ?_⟩
      rw [hψapp u, hu, hz]
      simp
  have hnt : (repOn ρ K hs.1).invariants = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    apply Subtype.ext
    apply hUK (v : W) v.2
    intro x
    have h := (Representation.mem_invariants _ _).mp hv x
    have h2 := congrArg (fun w : ↥U => (w : W)) h
    simpa [repOn_apply, actOn_coe] using h2
  have hfpf : ∀ x : ↥K, conjMulEquiv K (e'⁻¹ * e) x = x → x = 1 := by
    intro x hx
    by_contra hx1
    have hcomm : (e'⁻¹ * e) * (x : L) = (x : L) * (e'⁻¹ * e) := by
      have h := congrArg (fun y : ↥K => (y : L)) hx
      simp only [conjMulEquiv_apply] at h
      have h2 := congrArg (fun t : L => t * (e'⁻¹ * e)) h
      simpa [mul_assoc] using h2
    have hmem : e'⁻¹ * e ∈ Subgroup.centralizer ({(x : L)} : Set L) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcomm.symm
    have hK : e'⁻¹ * e ∈ K := hcent (x : L) x.2 (fun hx1' => hx1 (Subtype.ext hx1')) hmem
    have hE : e'⁻¹ * e ∈ E := E.mul_mem (E.inv_mem he') he
    have hbot := Subgroup.mem_inf.mpr ⟨hK, hE⟩
    rw [hinf] at hbot
    have h1 : e'⁻¹ * e = 1 := Subgroup.mem_bot.mp hbot
    apply hne
    calc e = e' * (e'⁻¹ * e) := by group
      _ = e' * 1 := by rw [h1]
      _ = e' := mul_one e'
  have hψσ : ∀ (x : ↥K) (u : ↥U),
      ψ ((repOn ρ K hs.1) x u) = (repOn ρ K hs.1) (conjMulEquiv K (e'⁻¹ * e) x) (ψ u) := by
    intro x u
    apply Subtype.ext
    change ((ψ (actOn ρ K hs.1 x u) : ↥U) : W)
      = ρ (((conjMulEquiv K (e'⁻¹ * e) x : ↥K)) : L) ((ψ u : ↥U) : W)
    rw [hψapp (actOn ρ K hs.1 x u), hψapp u]
    simp only [conjMapInv_apply]
    rw [show conjMap ρ U e (actOn ρ K hs.1 x u)
        = actOn ρ K (IsStable.map_conj ρ (show IsStable ρ K U from hs.1) e)
            ⟨e * (x : L) * e⁻¹, (inferInstance : K.Normal).conj_mem (x : L) x.2 e⟩
            (conjMap ρ U e u) from
      (IsEquiv.conj_comm ρ K (show IsStable ρ K U from hs.1) x u).symm]
    rw [hf.coe_apply ρ K
      ⟨e * (x : L) * e⁻¹, (inferInstance : K.Normal).conj_mem (x : L) x.2 e⟩ (conjMap ρ U e u)]
    simp only [conjMulEquiv_apply]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 1
    group
  exact no_isFixedPointFree_semilinear_bijective (repOn ρ K hs.1) hnt hcop
    (conjMulEquiv K (e'⁻¹ * e)) hfpf ψ hψbij hψσ

end Semilinear

/-! ## Equivariant retractions and the directness of the Frobenius orbit -/

section Orbit

variable {L : Type*} [Group L] {W : Type*} [AddCommGroup W] [Module k W]

/-- **Equivariant retraction.**  Averaging a linear retraction over `K` produces a `K`-equivariant
retraction onto a stable subspace. -/
theorem exists_equivariant_retraction (ρ : Representation k L W) (K : Subgroup L) [Fintype ↥K]
    {U : Submodule k W} (hU : IsStable ρ K U) (hcard : (Fintype.card ↥K : k) ≠ 0) :
    ∃ π : W →ₗ[k] ↥U,
      (∀ u : ↥U, π u = u) ∧ ∀ (x : ↥K) (w : W), π (ρ (x : L) w) = actOn ρ K hU x (π w) := by
  obtain ⟨π₀, hπ₀⟩ := LinearMap.exists_leftInverse_of_injective U.subtype
    (LinearMap.ker_eq_bot.mpr Subtype.coe_injective)
  have hπ₀' : ∀ v : ↥U, π₀ (v : W) = v := by
    intro v
    have h := congrArg (fun (g : ↥U →ₗ[k] ↥U) => g v) hπ₀
    simpa using h
  refine ⟨(Fintype.card ↥K : k)⁻¹ •
    ∑ x : ↥K, (actOn ρ K hU x).comp (π₀.comp (ρ ((x : L)⁻¹))), ?_, ?_⟩
  · intro u
    have h1 : ∀ x : ↥K,
        ((actOn ρ K hU x).comp (π₀.comp (ρ ((x : L)⁻¹)))) u = u := by
      intro x
      have hx : π₀ ((ρ ((x : L)⁻¹)) (u : W)) = (actOn ρ K hU (x⁻¹) u : ↥U) :=
        hπ₀' (actOn ρ K hU (x⁻¹) u)
      show actOn ρ K hU x (π₀ ((ρ ((x : L)⁻¹)) (u : W))) = u
      rw [hx]
      apply Subtype.ext
      simp only [actOn_coe, Subgroup.coe_inv, rho_mul_inv_apply]
    rw [LinearMap.smul_apply, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul k]
    rw [smul_smul, inv_mul_cancel₀ hcard, one_smul]
  · intro x w
    have h1 : (∑ y : ↥K, (actOn ρ K hU y).comp (π₀.comp (ρ ((y : L)⁻¹))) (ρ (x : L) w))
        = ∑ y : ↥K, actOn ρ K hU (x * y) ((π₀.comp (ρ ((y : L)⁻¹))) w) := by
      have hA : ∀ y : ↥K,
          (actOn ρ K hU y).comp (π₀.comp (ρ ((y : L)⁻¹))) (ρ (x : L) w)
            = actOn ρ K hU y (π₀ (ρ (((y : L)⁻¹) * (x : L)) w)) := by
        intro y
        show actOn ρ K hU y (π₀ (ρ ((y : L)⁻¹) (ρ (x : L) w)))
            = actOn ρ K hU y (π₀ (ρ (((y : L)⁻¹) * (x : L)) w))
        rw [rho_mul_apply]
      have hB : ∀ y : ↥K,
          actOn ρ K hU (x * y) ((π₀.comp (ρ ((y : L)⁻¹))) w)
            = actOn ρ K hU (x * y) (π₀ (ρ ((y : L)⁻¹) w)) := fun y => rfl
      rw [Finset.sum_congr rfl (fun y _ => hA y), Finset.sum_congr rfl (fun y _ => hB y)]
      refine Fintype.sum_equiv (Equiv.mulLeft x⁻¹)
        (fun y : ↥K => actOn ρ K hU y (π₀ (ρ (((y : L)⁻¹) * (x : L)) w)))
        (fun z : ↥K => actOn ρ K hU (x * z) (π₀ (ρ (((z : L)⁻¹)) w))) ?_
      intro y
      simp only [Equiv.coe_mulLeft]
      have h1' : x * (x⁻¹ * y) = y := by group
      have h2' : ((((x⁻¹ * y) : ↥K) : L))⁻¹ = ((y : L)⁻¹) * (x : L) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h1', h2']
    have h2 : (∑ y : ↥K, actOn ρ K hU x ((actOn ρ K hU y).comp (π₀.comp (ρ ((y : L)⁻¹))) w))
        = ∑ y : ↥K, actOn ρ K hU (x * y) ((π₀.comp (ρ ((y : L)⁻¹))) w) := by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      have hm := congrArg (fun (g : ↥U →ₗ[k] ↥U) => g ((π₀.comp (ρ ((y : L)⁻¹))) w))
        (actOn_mul ρ K hU x y)
      simpa [Module.End.mul_apply] using hm.symm
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      h1.trans h2.symm, ← map_sum, LinearMap.sum_apply, map_smul]

/-- The conjugate of the projection onto `U` is a projection onto `ρ e U`. -/
def conjProj (ρ : Representation k L W) (U : Submodule k W) (π : W →ₗ[k] ↥U) (e : L) :
    W →ₗ[k] W := ((ρ e).comp (U.subtype.comp π)).comp (ρ (e⁻¹))

lemma conjProj_apply (ρ : Representation k L W) (U : Submodule k W) (π : W →ₗ[k] ↥U)
    (e : L) (w : W) : conjProj ρ U π e w = ρ e (π (ρ (e⁻¹) w)) := rfl

lemma conjProj_mem (ρ : Representation k L W) (U : Submodule k W) (π : W →ₗ[k] ↥U) (e : L)
    (w : W) : conjProj ρ U π e w ∈ U.map (ρ e) :=
  ⟨π (ρ (e⁻¹) w), (π (ρ (e⁻¹) w)).2, rfl⟩

/-- The conjugate projection fixes `ρ e U`. -/
lemma conjProj_self (ρ : Representation k L W) {U : Submodule k W} {π : W →ₗ[k] ↥U}
    (hfix : ∀ u : ↥U, π u = u) (e : L) (u : ↥U) :
    conjProj ρ U π e (ρ e (u : W)) = ρ e (u : W) := by
  rw [conjProj_apply, rho_inv_apply, hfix]

/-- The conjugate projection is `K`-equivariant. -/
lemma conjProj_equivariant (ρ : Representation k L W) (K : Subgroup L) [K.Normal]
    {U : Submodule k W} {π : W →ₗ[k] ↥U} {hU : IsStable ρ K U}
    (heq : ∀ (x : ↥K) (w : W), π (ρ (x : L) w) = actOn ρ K hU x (π w)) (e : L) (x : ↥K) (w : W) :
    conjProj ρ U π e (ρ (x : L) w) = ρ (x : L) (conjProj ρ U π e w) := by
  rw [conjProj_apply, conjProj_apply]
  have hy : (e⁻¹ * (x : L) * e) ∈ K := (inferInstance : K.Normal).conj_mem' (x : L) x.2 e
  have harg : ρ (e⁻¹) (ρ (x : L) w)
      = ρ (e⁻¹ * (x : L) * e) (ρ (e⁻¹) w) := by
    rw [rho_mul_apply]
    rw [show e⁻¹ * (x : L) = (e⁻¹ * (x : L) * e) * e⁻¹ by group]
    rw [← rho_mul_apply]
    congr 1
    group
  rw [harg]
  have h2' : ((π (ρ (e⁻¹ * (x : L) * e) (ρ (e⁻¹) w)) : ↥U) : W)
      = ρ (e⁻¹ * (x : L) * e) ((π (ρ (e⁻¹) w) : ↥U) : W) := by
    have h := heq ⟨e⁻¹ * (x : L) * e, hy⟩ (ρ (e⁻¹) w)
    have h' := congrArg (fun v : ↥U => (v : W)) h
    simpa [actOn_coe, Subgroup.coe_mk] using h'
  rw [h2']
  rw [rho_mul_apply, rho_mul_apply]
  congr 1
  group

/-- The restricted conjugate projection, as a map on the conjugate subspace. -/
def conjProjMap (ρ : Representation k L W) (U : Submodule k W) (π : W →ₗ[k] ↥U) (e e' : L) :
    ↥(U.map (ρ e)) →ₗ[k] ↥(U.map (ρ e')) where
  toFun v := ⟨conjProj ρ U π e' (v : W), conjProj_mem ρ U π e' (v : W)⟩
  map_add' a b := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_mk]
    exact map_add (conjProj ρ U π e') (a : W) (b : W)
  map_smul' c a := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, Submodule.coe_mk]
    exact map_smul (conjProj ρ U π e') c (a : W)

lemma conjProjMap_equivariant (ρ : Representation k L W) (K : Subgroup L) [K.Normal]
    {U : Submodule k W} {π : W →ₗ[k] ↥U} {hU : IsStable ρ K U}
    (heq : ∀ (x : ↥K) (w : W), π (ρ (x : L) w) = actOn ρ K hU x (π w)) (e e' : L) :
    IsEquiv ρ K (IsStable.map_conj ρ hU e) (IsStable.map_conj ρ hU e') (conjProjMap ρ U π e e') := by
  intro x
  ext v
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  exact conjProj_equivariant ρ K heq e' x (v : W)

/-- If `U` is simple with `U^K = 0` and `e ≠ e'` in `E`, then the conjugate projection onto
`ρ e' U` kills `ρ e U`. -/
theorem conjProjMap_eq_zero {p : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (ρ : Representation k L W) [Fintype L] [FiniteDimensional k W]
    {K : Subgroup L} [K.Normal] [Fintype ↥K] {E : Subgroup L} (hinf : K ⊓ E = ⊥)
    (hcent : ∀ h ∈ K, h ≠ 1 → Subgroup.centralizer ({h} : Set L) ≤ K)
    (hcop : ¬ p ∣ Nat.card ↥K)
    {U : Submodule k W} (hs : IsSimpleStable ρ K U)
    (hUK : ∀ u ∈ U, (∀ x : ↥K, ρ (x : L) u = u) → u = 0)
    {π : W →ₗ[k] ↥U} {hU : IsStable ρ K U}
    (heq : ∀ (x : ↥K) (w : W), π (ρ (x : L) w) = actOn ρ K hU x (π w))
    {e e' : L} (he : e ∈ E) (he' : e' ∈ E) (hne : e ≠ e') :
    conjProjMap ρ U π e e' = 0 := by
  by_contra hne0
  have hequiv := conjProjMap_equivariant ρ K heq e e'
  have hbij := hequiv.bijective_of_isSimpleStable ρ K (IsSimpleStable.map_conj ρ hs e)
    (IsSimpleStable.map_conj ρ hs e') hne0
  exact no_iso_conj ρ hinf hcent hcop hs hUK he he' hne hequiv hbij

/-- **Directness of the Frobenius orbit.**  For `U` a simple `K`-module with `U^K = 0` and
`e ∈ E`, the sum of the conjugates `ρ e U` is direct. -/
theorem sum_eq_zero_of_conj {p : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (ρ : Representation k L W) [Fintype L] [FiniteDimensional k W]
    {K : Subgroup L} [K.Normal] {E : Subgroup L} [Fintype ↥E] (hinf : K ⊓ E = ⊥)
    (hcent : ∀ h ∈ K, h ≠ 1 → Subgroup.centralizer ({h} : Set L) ≤ K)
    (hcop : ¬ p ∣ Nat.card ↥K)
    {U : Submodule k W} (hs : IsSimpleStable ρ K U)
    (hUK : ∀ u ∈ U, (∀ x : ↥K, ρ (x : L) u = u) → u = 0)
    {π : W →ₗ[k] ↥U} {hU : IsStable ρ K U} (hfix : ∀ u : ↥U, π u = u)
    (heq : ∀ (x : ↥K) (w : W), π (ρ (x : L) w) = actOn ρ K hU x (π w))
    (v : ↥E → W) (hv : ∀ e : ↥E, v e ∈ U.map (ρ (e : L)))
    (hsum : ∑ e : ↥E, v e = 0) : ∀ e : ↥E, v e = 0 := by
  intro e₀
  have h := congrArg (conjProj ρ U π (e₀ : L)) hsum
  rw [map_sum, map_zero] at h
  rw [Finset.sum_eq_single e₀] at h
  · obtain ⟨u, hu, hvu⟩ := hv e₀
    rw [← hvu, conjProj_self ρ hfix (e₀ : L) ⟨u, hu⟩] at h
    simpa [hvu] using h
  · intro e _ hne
    have hne' : (e : L) ≠ (e₀ : L) := fun h' => hne (Subtype.ext h')
    have hzero : conjProjMap ρ U π (e : L) (e₀ : L) = 0 :=
      conjProjMap_eq_zero ρ hinf hcent hcop hs hUK heq e.2 e₀.2 hne'
    have h2 : ((conjProjMap ρ U π (e : L) (e₀ : L)) ⟨v e, hv e⟩ : W) = 0 := by
      rw [hzero]
      rfl
    simpa [conjProjMap] using h2
  · intro hmem; exact absurd (Finset.mem_univ e₀) hmem

end Orbit

/-! ## Existence of simple stable subspaces -/

section SimpleExists

variable {L : Type*} [Group L] {W : Type*} [AddCommGroup W] [Module k W]

/-- Every nonzero finite-dimensional module for a group has a simple stable submodule. -/
theorem exists_isSimpleStable (ρ : Representation k L W) (K : Subgroup L)
    [FiniteDimensional k W] [Nontrivial W] :
    ∃ U : Submodule k W, IsSimpleStable ρ K U := by
  classical
  have hSne : ({n : ℕ |
      ∃ U : Submodule k W, IsStable ρ K U ∧ U ≠ ⊥ ∧ Module.finrank k ↥U = n} : Set ℕ).Nonempty := by
    refine ⟨Module.finrank k W, ⊤, IsStable.top ρ K, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := exists_ne (0 : W)
      intro h
      have hmem : x ∈ (⊥ : Submodule k W) := by rw [← h]; trivial
      exact hx (by simpa using hmem)
    · exact LinearEquiv.finrank_eq Submodule.topEquiv
  obtain ⟨U, hUstab, hUne, hUfin⟩ := Nat.sInf_mem hSne
  refine ⟨U, hUstab, hUne, ?_⟩
  intro U' hle hstab hne
  have hmem : Module.finrank k ↥U' ∈ {n : ℕ |
      ∃ U : Submodule k W, IsStable ρ K U ∧ U ≠ ⊥ ∧ Module.finrank k ↥U = n} :=
    ⟨U', hstab, hne, rfl⟩
  have h1 : sInf {n : ℕ | ∃ U : Submodule k W, IsStable ρ K U ∧ U ≠ ⊥ ∧
      Module.finrank k ↥U = n} ≤ Module.finrank k ↥U' := Nat.sInf_le hmem
  have h2 : Module.finrank k ↥U' ≤ sInf {n : ℕ | ∃ U : Submodule k W, IsStable ρ K U ∧
      U ≠ ⊥ ∧ Module.finrank k ↥U = n} := by
    rw [← hUfin]; exact Submodule.finrank_mono hle
  have heq : Module.finrank k ↥U' = Module.finrank k ↥U := by rw [le_antisymm h2 h1, hUfin]
  exact Submodule.eq_of_le_of_finrank_eq hle heq

end SimpleExists

/-! ## The fixed points of the regular module -/

section Regular

variable {E : Type*} [Group E] [Fintype E]

/-- The left regular representation of a subgroup on functions. -/
def leftRegularRep (E₀ : Subgroup E) (U : Type*) [AddCommGroup U] [Module k U] :
    Representation k ↥E₀ (E → U) where
  toFun h :=
    { toFun := fun f => fun e => f (((h⁻¹ : ↥E₀) : E) * e)
      map_add' := fun f g => by ext e; simp
      map_smul' := fun c f => by ext e; simp }
  map_one' := by
    ext f e
    simp
  map_mul' h h' := LinearMap.ext fun f => by
    funext e
    show f ((((h * h')⁻¹ : ↥E₀) : E) * e) = f (((h'⁻¹ : ↥E₀) : E) * (((h⁻¹ : ↥E₀) : E) * e))
    rw [show (((h * h')⁻¹ : ↥E₀) : E) = ((h'⁻¹ : ↥E₀) : E) * ((h⁻¹ : ↥E₀) : E) by
      rw [Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
        mul_inv_rev], mul_assoc]

lemma mem_invariants_leftRegular {E₀ : Subgroup E} {U : Type*} [AddCommGroup U] [Module k U]
    {f : E → U} :
    f ∈ (leftRegularRep (k := k) E₀ U).invariants ↔ ∀ (h : ↥E₀) (e : E), f ((h : E) * e) = f e := by
  rw [Representation.mem_invariants]
  constructor
  · intro hf h e
    have h2 : f (((((h⁻¹ : ↥E₀))⁻¹ : ↥E₀) : E) * e) = f e := congrFun (hf h⁻¹) e
    simpa using h2
  · intro hf h
    ext e
    exact hf h⁻¹ e

/-- The `E₀`-fixed functions are the functions on the right-coset quotient. -/
noncomputable def invariantsEquivFun (E₀ : Subgroup E) (U : Type*) [AddCommGroup U] [Module k U] :
    ↥(leftRegularRep (k := k) E₀ U).invariants ≃ₗ[k]
      (Quotient (QuotientGroup.rightRel E₀) → U) where
  toFun f := fun q => (f : E → U) (Quotient.out q)
  map_add' f g := by ext q; rfl
  map_smul' c f := by ext q; rfl
  invFun g := ⟨fun e => g ⟦e⟧, by
    rw [mem_invariants_leftRegular]
    intro h e
    have hrel : QuotientGroup.rightRel E₀ ((h : E) * e) e := by
      rw [QuotientGroup.rightRel_apply]
      have : e * ((h : E) * e)⁻¹ = (h : E)⁻¹ := by group
      rw [this]
      exact E₀.inv_mem h.2
    exact congrArg g (Quotient.sound hrel)⟩
  left_inv f := by
    ext e
    have hrel : QuotientGroup.rightRel E₀ (Quotient.out ⟦e⟧) e := Quotient.mk_out e
    have hinv : ∀ (a b : E), QuotientGroup.rightRel E₀ a b → (f : E → U) b = (f : E → U) a := by
      intro a b hab
      rw [QuotientGroup.rightRel_apply] at hab
      have hb : b = (b * a⁻¹) * a := by group
      rw [hb, (mem_invariants_leftRegular.mp f.2) ⟨b * a⁻¹, hab⟩ a]
    exact (hinv _ _ hrel).symm
  right_inv g := by
    ext q
    show g ⟦Quotient.out q⟧ = g q
    rw [Quotient.out_eq]

/-- Inversion identifies the right- and left-coset quotients. -/
noncomputable def rightRelLeftRelEquiv (E₀ : Subgroup E) :
    Quotient (QuotientGroup.rightRel E₀) ≃ Quotient (QuotientGroup.leftRel E₀) :=
  Quotient.congr (Equiv.inv E) (fun a b => by
    rw [QuotientGroup.rightRel_apply, QuotientGroup.leftRel_apply]
    constructor
    · intro h
      have := E₀.inv_mem h
      simpa using this
    · intro h
      have := E₀.inv_mem h
      simpa using this)

lemma card_rightRel_quotient (E₀ : Subgroup E) :
    Nat.card (Quotient (QuotientGroup.rightRel E₀)) = E₀.index := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (rightRelLeftRelEquiv E₀)

/-- **Dimension of the fixed points of the regular module.** -/
theorem finrank_invariants_leftRegular (E₀ : Subgroup E) (U : Type*) [AddCommGroup U]
    [Module k U] [FiniteDimensional k U] :
    Module.finrank k ↥(leftRegularRep (k := k) E₀ U).invariants
      = E₀.index * Module.finrank k U := by
  haveI : Finite (Quotient (QuotientGroup.rightRel E₀)) := Quotient.finite _
  haveI : Fintype (Quotient (QuotientGroup.rightRel E₀)) := Fintype.ofFinite _
  rw [LinearEquiv.finrank_eq (invariantsEquivFun (k := k) E₀ U), Module.finrank_pi_fintype]
  have hcard : Fintype.card (Quotient (QuotientGroup.rightRel E₀)) = E₀.index := by
    rw [← Nat.card_eq_fintype_card, card_rightRel_quotient]
  rw [Finset.sum_const, Finset.card_univ, hcard]
  exact nsmul_eq_mul E₀.index (Module.finrank k U)

end Regular

/-! ## The Frobenius orbit module and its fixed points -/

section OrbitDim

variable {L : Type*} [Group L] {W : Type*} [AddCommGroup W] [Module k W]

/-- The submodule generated by the `E`-conjugates of `U`. -/
abbrev orbitModule (ρ : Representation k L W) (E : Subgroup L) (U : Submodule k W) :
    Submodule k W :=
  ⨆ e : ↥E, U.map (ρ (e : L))

lemma le_orbitModule (ρ : Representation k L W) (E : Subgroup L) (U : Submodule k W) (e : ↥E) :
    U.map (ρ (e : L)) ≤ orbitModule ρ E U := le_iSup (fun e : ↥E => U.map (ρ (e : L))) e

lemma orbitModule_map_E (ρ : Representation k L W) (E : Subgroup L) (U : Submodule k W)
    {g : L} (hg : g ∈ E) :
    Submodule.map (ρ g) (orbitModule ρ E U) ≤ orbitModule ρ E U := by
  change Submodule.map (ρ g) (⨆ e : ↥E, U.map (ρ (e : L))) ≤ _
  rw [Submodule.map_iSup]
  refine iSup_le fun e => ?_
  refine le_iSup_of_le (⟨g * (e : L), E.mul_mem hg e.2⟩ : ↥E) ?_
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hx
  obtain ⟨u, hu, hyu⟩ := hy
  refine ⟨u, hu, ?_⟩
  rw [← hxy, ← hyu, ← Module.End.mul_apply, ← map_mul]

lemma orbitModule_map_K (ρ : Representation k L W) {K E : Subgroup L} [K.Normal]
    {U : Submodule k W} (hU : IsStable ρ K U) {k : L} (hk : k ∈ K) :
    Submodule.map (ρ k) (orbitModule ρ E U) ≤ orbitModule ρ E U := by
  change Submodule.map (ρ k) (⨆ e : ↥E, U.map (ρ (e : L))) ≤ _
  rw [Submodule.map_iSup]
  refine iSup_le fun e => ?_
  refine le_iSup_of_le e ?_
  intro x hx
  obtain ⟨u, hu, rfl⟩ := hx
  exact (IsStable.map_conj ρ hU (e : L)) ⟨k, hk⟩ u hu

/-- The orbit module is stable under all of `L`. -/
theorem orbitModule_stable (ρ : Representation k L W) {K E : Subgroup L} [K.Normal]
    (hsup : K ⊔ E = ⊤) {U : Submodule k W} (hU : IsStable ρ K U) :
    ∀ g : L, ∀ w ∈ orbitModule ρ E U, ρ g w ∈ orbitModule ρ E U := by
  intro g w hw
  have hg' : g ∈ K ⊔ E := by rw [hsup]; trivial
  obtain ⟨k, hk, e, he, hke⟩ :=
    (Subgroup.mem_sup_of_normal_left.mp hg' : ∃ k ∈ K, ∃ e ∈ E, k * e = g)
  rw [← hke, map_mul, Module.End.mul_apply]
  exact (orbitModule_map_K ρ hU hk) ⟨ρ e w, (orbitModule_map_E ρ E U he) ⟨w, hw, rfl⟩, rfl⟩

/-- The coordinate map `(↥E → ↥U) → orbitModule`. -/
def orbitCoord (ρ : Representation k L W) (E : Subgroup L) [Fintype ↥E] (U : Submodule k W) :
    (↥E → ↥U) →ₗ[k] ↥(orbitModule ρ E U) where
  toFun f := ⟨∑ e : ↥E, ρ (e : L) (f e : W), by
    refine Submodule.sum_mem _ fun e _ => ?_
    exact Submodule.mem_iSup_of_mem e ⟨f e, (f e).2, rfl⟩⟩
  map_add' f g := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c f := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

@[simp] lemma orbitCoord_apply (ρ : Representation k L W) (E : Subgroup L) [Fintype ↥E]
    (U : Submodule k W) (f : ↥E → ↥U) :
    ((orbitCoord ρ E U f : ↥(orbitModule ρ E U)) : W) = ∑ e : ↥E, ρ (e : L) (f e : W) := rfl

lemma orbitCoord_injective (ρ : Representation k L W) (E : Subgroup L) [Fintype ↥E]
    (U : Submodule k W)
    (hdirect : ∀ (v : ↥E → W), (∀ e : ↥E, v e ∈ U.map (ρ (e : L))) →
      ∑ e : ↥E, v e = 0 → ∀ e : ↥E, v e = 0) :
    Function.Injective (orbitCoord ρ E U) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro f hf
  have h0 : ∑ e : ↥E, ρ (e : L) (f e : W) = 0 := by
    have h := congrArg (fun (x : ↥(orbitModule ρ E U)) => (x : W)) hf
    simpa using h
  have hv : ∀ e : ↥E, ρ (e : L) (f e : W) ∈ U.map (ρ (e : L)) := fun e => ⟨f e, (f e).2, rfl⟩
  have hall := hdirect (fun e => ρ (e : L) (f e : W)) hv h0
  ext e
  have he := hall e
  have h2 : (ρ (e : L)) ((f e : W)) = (ρ (e : L)) 0 := by simpa using he
  simpa using inj_rho ρ (e : L) h2

lemma orbitCoord_surjective (ρ : Representation k L W) (E : Subgroup L) [Fintype ↥E]
    (U : Submodule k W) : Function.Surjective (orbitCoord ρ E U) := by
  rw [← LinearMap.range_eq_top]
  have hle : orbitModule ρ E U ≤ (LinearMap.range (orbitCoord ρ E U)).map
      (Submodule.subtype (orbitModule ρ E U)) := by
    change (⨆ e : ↥E, U.map (ρ (e : L))) ≤ _
    refine iSup_le fun e => ?_
    intro x hx
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨(orbitCoord ρ E U
      (fun e' => if h : e' = e then (⟨u, hu⟩ : ↥U) else 0) : ↥(orbitModule ρ E U)),
      ⟨_, rfl⟩, ?_⟩
    show ((orbitCoord ρ E U
        (fun e' => if h : e' = e then (⟨u, hu⟩ : ↥U) else 0) : ↥(orbitModule ρ E U)) : W)
          = ρ (e : L) u
    rw [orbitCoord_apply]
    have hterm : ∀ x : ↥E,
        ρ (x : L) (((if h : x = e then (⟨u, hu⟩ : ↥U) else 0 : ↥U)) : W)
          = (if x = e then ρ (e : L) u else 0) := by
      intro x
      split_ifs with hx
      · subst hx; rfl
      · rw [Submodule.coe_zero, map_zero]
    simp only [hterm]
    rw [Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_univ e)]
  rw [Submodule.eq_top_iff']
  intro x
  have hx : (x : W) ∈ (LinearMap.range (orbitCoord ρ E U)).map
      (Submodule.subtype (orbitModule ρ E U)) := hle x.2
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := Subtype.ext hyx
  rwa [← this]

theorem orbitCoord_bijective (ρ : Representation k L W) (E : Subgroup L) [Fintype ↥E]
    (U : Submodule k W)
    (hdirect : ∀ (v : ↥E → W), (∀ e : ↥E, v e ∈ U.map (ρ (e : L))) →
      ∑ e : ↥E, v e = 0 → ∀ e : ↥E, v e = 0) :
    Function.Bijective (orbitCoord ρ E U) :=
  ⟨orbitCoord_injective ρ E U hdirect, orbitCoord_surjective ρ E U⟩

/-- The coordinate equivalence. -/
noncomputable def orbitEquiv (ρ : Representation k L W) (E : Subgroup L) [Fintype ↥E]
    (U : Submodule k W)
    (hdirect : ∀ (v : ↥E → W), (∀ e : ↥E, v e ∈ U.map (ρ (e : L))) →
      ∑ e : ↥E, v e = 0 → ∀ e : ↥E, v e = 0) :
    (↥E → ↥U) ≃ₗ[k] ↥(orbitModule ρ E U) :=
  LinearEquiv.ofBijective (orbitCoord ρ E U) (orbitCoord_bijective ρ E U hdirect)

lemma orbitEquiv_apply (ρ : Representation k L W) (E : Subgroup L) [Fintype ↥E]
    (U : Submodule k W) (hdirect : _) (f : ↥E → ↥U) :
    orbitEquiv ρ E U hdirect f = orbitCoord ρ E U f := rfl

/-- The orbit module has dimension `|E| * dim U`. -/
theorem finrank_orbitModule (ρ : Representation k L W) (E : Subgroup L) [Fintype ↥E]
    (U : Submodule k W) [FiniteDimensional k W] [FiniteDimensional k ↥U]
    (hdirect : ∀ (v : ↥E → W), (∀ e : ↥E, v e ∈ U.map (ρ (e : L))) →
      ∑ e : ↥E, v e = 0 → ∀ e : ↥E, v e = 0) :
    Module.finrank k ↥(orbitModule ρ E U) = Nat.card ↥E * Module.finrank k ↥U := by
  rw [← LinearEquiv.finrank_eq (orbitEquiv ρ E U hdirect), Module.finrank_pi_fintype]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact nsmul_eq_mul (Nat.card ↥E) (Module.finrank k ↥U)

/-- The orbit coordinates intertwine the left regular action on functions with the action on the
orbit module. -/
lemma orbitCoord_leftRegular (ρ : Representation k L W) (E : Subgroup L) [Fintype ↥E]
    (U : Submodule k W) {E₀ : Subgroup ↥E} (f : ↥E → ↥U) (h : ↥E₀) :
    ((orbitCoord ρ E U (leftRegularRep (k := k) E₀ ↥U h f) : ↥(orbitModule ρ E U)) : W)
      = ρ (((h : ↥E₀) : ↥E) : L) ((orbitCoord ρ E U f : ↥(orbitModule ρ E U)) : W) := by
  rw [orbitCoord_apply, orbitCoord_apply, map_sum]
  rw [show ((leftRegularRep (k := k) E₀ ↥U h) f)
      = fun e => f (((h⁻¹ : ↥E₀) : ↥E) * e) from rfl]
  have hR : (∑ x : ↥E, ρ (((h : ↥E₀) : ↥E) : L) (ρ (x : L) (f x)))
      = ∑ x : ↥E, ρ ((((h : ↥E₀) : ↥E) : L) * (x : L)) (f x) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact rho_mul_apply ρ _ _ _
  rw [hR]
  refine (Fintype.sum_equiv (Equiv.mulLeft (h : ↥E))
    (fun y : ↥E => ρ ((((h : ↥E₀) : ↥E) : L) * (y : L)) (f y))
    (fun y : ↥E => ρ (y : L) (f (((h⁻¹ : ↥E₀) : ↥E) * y))) ?_).symm
  intro y
  show ρ ((((h : ↥E₀) : ↥E) : L) * (y : L)) (f y)
    = ρ ((((h : ↥E₀) : ↥E) * y : ↥E) : L)
        (f (((h⁻¹ : ↥E₀) : ↥E) * (((h : ↥E₀) : ↥E) * y)))
  rw [Subgroup.coe_mul]
  congr 1
  rw [Subgroup.coe_inv]
  group

/-- **The fixed points of the orbit module.**  Under the coordinates, the `E₀`-fixed vectors of
the orbit module correspond to the `E₀`-fixed functions on `E`. -/
theorem finrank_invariants_orbitModule (ρ : Representation k L W) (E : Subgroup L) [Fintype ↥E]
    {K : Subgroup L} [K.Normal] (hsup : K ⊔ E = ⊤) {U : Submodule k W} (hU : IsStable ρ K U)
    [FiniteDimensional k W] [FiniteDimensional k ↥U]
    (hdirect : ∀ (v : ↥E → W), (∀ e : ↥E, v e ∈ U.map (ρ (e : L))) →
      ∑ e : ↥E, v e = 0 → ∀ e : ↥E, v e = 0)
    (E₀ : Subgroup ↥E) :
    Module.finrank k ↥(Representation.invariants
        ((repRestrict ρ (orbitModule ρ E U) (orbitModule_stable ρ hsup hU)).comp
          ((Subgroup.subtype E).comp E₀.subtype)))
      = E₀.index * Module.finrank k ↥U := by
  have hM := orbitModule_stable ρ hsup hU
  haveI : FiniteDimensional k ↥(orbitModule ρ E U) := inferInstance
  have hmaps : (Submodule.map (orbitCoord ρ E U)
      (Representation.invariants (leftRegularRep (k := k) E₀ ↥U)))
      = Representation.invariants ((repRestrict ρ (orbitModule ρ E U) hM).comp
          ((Subgroup.subtype E).comp E₀.subtype)) := by
    ext v
    constructor
    · rintro ⟨f, hf, rfl⟩
      rw [Representation.mem_invariants]
      intro h
      have hf' : leftRegularRep (k := k) E₀ ↥U h f = f :=
        (Representation.mem_invariants _ _).mp hf h
      apply Subtype.ext
      change ((repRestrict ρ (orbitModule ρ E U) hM) ((h : ↥E₀) : ↥E)
          (orbitCoord ρ E U f) : W) = ((orbitCoord ρ E U f : ↥(orbitModule ρ E U)) : W)
      rw [repRestrict_apply, ← orbitCoord_leftRegular (E₀ := E₀) ρ E U f h, hf']
    · intro hv
      obtain ⟨f, hfv⟩ := orbitCoord_surjective ρ E U v
      refine ⟨f, ?_, hfv⟩
      refine (Representation.mem_invariants _ _).mpr ?_
      intro h
      apply orbitCoord_injective ρ E U hdirect
      apply Subtype.ext
      have hv' : ((repRestrict ρ (orbitModule ρ E U) hM) ((h : ↥E₀) : ↥E) v) = v :=
        (Representation.mem_invariants _ _).mp hv h
      have hv'' : ρ (((h : ↥E₀) : ↥E) : L) ((v : ↥(orbitModule ρ E U)) : W) = (v : W) := by
        have h2 := congrArg (fun w : ↥(orbitModule ρ E U) => (w : W)) hv'
        simpa [repRestrict_apply] using h2
      rw [orbitCoord_leftRegular (E₀ := E₀) ρ E U f h, hfv]
      exact hv''
  rw [← hmaps]
  rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (orbitCoord ρ E U)
    (orbitCoord_injective ρ E U hdirect)
    (Representation.invariants (leftRegularRep (k := k) E₀ ↥U)))]
  exact finrank_invariants_leftRegular E₀ ↥U

end OrbitDim

end Work.CharPrelim
