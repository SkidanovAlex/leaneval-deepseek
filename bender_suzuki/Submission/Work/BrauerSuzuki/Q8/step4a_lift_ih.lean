import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Lifting the `Q₈` induction hypothesis across universes

The induction hypothesis in Glauberman's step `(4)(a)` is a statement about *all* finite groups
of smaller order than the ambient group `G`.  When it is formalised it is natural to write it as
a quantifier over `H : Type`, i.e. over groups in the *smallest* universe only.  The point of this
file is that this costs nothing: every finite group is isomorphic to a group carried by `Type`
(namely, its image under the left regular representation, transported to `Fin n`), so the
hypothesis for small groups implies it for groups in an arbitrary universe.

The main result is `Work.BrauerSuzuki.Q8.step4a_lift_ih`.
-/

namespace Work.BrauerSuzuki.Q8

/-- `O(G)` is carried by group isomorphisms. -/
theorem step4a_oddCore_map_mulEquiv {K L : Type*} [Group K] [Finite K] [Group L] [Finite L]
    (σ : K ≃* L) :
    Subgroup.map σ.toMonoidHom (Submission.Blueprint.oddCore K) =
      Submission.Blueprint.oddCore L := by
  have hdir : (Submission.Blueprint.oddCore K).map σ.toMonoidHom ≤
      Submission.Blueprint.oddCore L := by
    refine Work.BrauerSuzuki.OddCore.le_of_normal_odd
      (Subgroup.Normal.map inferInstance σ.toMonoidHom σ.surjective) ?_
    rw [Subgroup.card_map_of_injective σ.injective]
    exact Work.BrauerSuzuki.OddCore.oddCard_oddCore
  have hrev : (Submission.Blueprint.oddCore L).map σ.symm.toMonoidHom ≤
      Submission.Blueprint.oddCore K := by
    refine Work.BrauerSuzuki.OddCore.le_of_normal_odd
      (Subgroup.Normal.map inferInstance σ.symm.toMonoidHom σ.symm.surjective) ?_
    rw [Subgroup.card_map_of_injective σ.symm.injective]
    exact Work.BrauerSuzuki.OddCore.oddCard_oddCore
  refine le_antisymm hdir ?_
  calc Submission.Blueprint.oddCore L
      = ((Submission.Blueprint.oddCore L).map σ.symm.toMonoidHom).map σ.toMonoidHom := by
        rw [Subgroup.map_map,
          show σ.toMonoidHom.comp σ.symm.toMonoidHom = MonoidHom.id L from by ext x; simp,
          Subgroup.map_id]
    _ ≤ (Submission.Blueprint.oddCore K).map σ.toMonoidHom := Subgroup.map_mono hrev

/-- **Lifting the induction hypothesis across universes.**  If the `Q₈`-induction hypothesis holds
for all finite groups carried by `Type` of order `< Nat.card G`, then it holds for every finite
group `K` (in any universe) of order `< Nat.card G`: `K` is isomorphic to a subgroup of the
permutation group `Equiv.Perm (Fin (Nat.card K))`, which lives in `Type`. -/
theorem step4a_lift_ih {G : Type*} [Group G] [Finite G]
    (h0 : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G →
      ∀ (T : Sylow 2 H) (e : Work.BrauerSuzuki.GenQuaternionData ↥T), e.n = 2 →
      ∀ y : H, y ∈ (T : Subgroup H) → orderOf y = 4 →
      ∀ k : H, y ^ 2 * k * (y ^ 2)⁻¹ * k⁻¹ ∈ Submission.Blueprint.oddCore H)
    (K : Type*) [Group K] [Finite K] (hcard : Nat.card K < Nat.card G)
    (T : Sylow 2 K) (e : Work.BrauerSuzuki.GenQuaternionData ↥T) (he : e.n = 2)
    (y : K) (hy : y ∈ (T : Subgroup K)) (hy4 : orderOf y = 4) (k : K) :
    y ^ 2 * k * (y ^ 2)⁻¹ * k⁻¹ ∈ Submission.Blueprint.oddCore K := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- a model of `K` carried by `Type`
  let φ : K ≃ Fin (Nat.card K) := Fintype.equivFinOfCardEq (by rw [Nat.card_eq_fintype_card])
  have hψ_apply : ∀ g x, ((Equiv.permCongr φ) (MulAction.toPermHom K K g)) x =
      φ (g * φ.symm x) := by
    intro g x
    rw [Equiv.permCongr_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply, smul_eq_mul]
  let ψ : K →* Equiv.Perm (Fin (Nat.card K)) :=
    { toFun := fun g => (Equiv.permCongr φ) (MulAction.toPermHom K K g)
      map_one' := by
        ext x
        rw [hψ_apply]
        simp
      map_mul' := by
        intro a b
        ext x
        rw [Equiv.Perm.mul_apply, hψ_apply, hψ_apply, hψ_apply]
        simp [mul_assoc] }
  have hψ : ∀ g x, (ψ g) x = φ (g * φ.symm x) := hψ_apply
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : (ψ a) (φ 1) = (ψ b) (φ 1) := by rw [hab]
    rw [hψ, hψ] at h1
    simp only [Equiv.symm_apply_apply, mul_one] at h1
    exact φ.injective h1
  let H : Type := ↥(ψ.range)
  let eM : K ≃* H := MonoidHom.ofInjective hψinj
  have hHK : Nat.card H = Nat.card K := Nat.card_congr eM.toEquiv.symm
  have hHcard : Nat.card H < Nat.card G := by rw [hHK]; exact hcard
  -- the Sylow `2`-subgroup of the model, with `Q₈` data
  let TH : Sylow 2 H := Sylow.mapSurjective (p := 2) (f := (eM : K →* H)) eM.surjective T
  have hTH : (TH : Subgroup H) = (T : Subgroup K).map (eM : K →* H) :=
    Sylow.coe_mapSurjective eM.surjective T
  have eIso : ↥T ≃* ↥TH :=
    (Subgroup.equivMapOfInjective (T : Subgroup K) (eM : K →* H) eM.injective).trans
      (MulEquiv.subgroupCongr hTH.symm)
  let eH : Work.BrauerSuzuki.GenQuaternionData ↥TH :=
    { n := e.n
      hn := e.hn
      tau := eIso e.tau
      rho := eIso e.rho
      tau_order := by rw [MulEquiv.orderOf_eq, e.tau_order]
      rho_conj := by
        have hc := congrArg eIso e.rho_conj
        simpa [map_mul, map_inv] using hc
      rho_sq := by rw [← map_pow, ← map_pow, e.rho_sq]
      closure_eq_top := by
        have h1 : ({eIso e.tau, eIso e.rho} : Set ↥TH) =
            (eIso : ↥T →* ↥TH) '' ({e.tau, e.rho} : Set ↥T) := by ext q; simp
        have h2 : ((Subgroup.closure ({e.tau, e.rho} : Set ↥T)).map (eIso : ↥T →* ↥TH)) =
            ⊤ := by
          rw [e.closure_eq_top, Subgroup.map_top]
          exact MonoidHom.range_eq_top.mpr eIso.surjective
        rw [h1, ← MonoidHom.map_closure (eIso : ↥T →* ↥TH)]
        exact h2 }
  have heH : eH.n = 2 := he
  -- the corresponding element and the induction hypothesis at the model
  have hyH_mem : eM y ∈ (TH : Subgroup H) := by
    rw [hTH, Subgroup.mem_map]
    exact ⟨y, hy, rfl⟩
  have hyH4 : orderOf (eM y) = 4 := by rw [MulEquiv.orderOf_eq]; exact hy4
  have hkey := h0 H hHcard TH eH heH (eM y) hyH_mem hyH4 (eM k)
  -- transport the conclusion back along `eM`
  have heq : (eM y) ^ 2 * (eM k) * ((eM y) ^ 2)⁻¹ * (eM k)⁻¹ =
      eM (y ^ 2 * k * (y ^ 2)⁻¹ * k⁻¹) := by
    simp only [map_mul, map_pow, map_inv]
  rw [heq, ← step4a_oddCore_map_mulEquiv eM] at hkey
  obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp hkey
  rwa [eM.injective hwe] at hw

end Work.BrauerSuzuki.Q8
