import Mathlib
import Submission.Work.CORE4.Case2K1_ne_bot
import Submission.Work.CORE4.Case2CountSetup

namespace Work.CORE4

open Work.GW2 Subgroup

set_option linter.style.haveILetI false

/-- If `g` and `g⁻¹` both conjugate `X` into itself then `g` normalizes `X`. -/
private lemma mem_normalizer_of_conj {G : Type} [Group G] {X : Subgroup G} {g : G}
    (h1 : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (h2 : ∀ x ∈ X, g⁻¹ * x * g ∈ X) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have h := h2 (g * x * g⁻¹) hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h

/-- **Bender 1981, §4: `s ∉ S₀`.**

`S₀` is cyclic and contains the involution `t`, so it has a *unique* element of order two;
hence if the involution `s ∈ S` lay in `S₀`, it would have to be `t`.  But then
`B₀ = C_{U∩M}(s) = (U ∩ M) ∩ C_G(t) = U ∩ M`, because `U = O(H) ≤ H = C_G(t)`, while
`K = I_{U∩M}(s)`; for an involution acting on the odd order group `U ∩ M` Bender's `1.5(ii)`
(`I.toolkit.c15`) gives `|K| · |B₀| = |U ∩ M|`, so `|K| = 1`, i.e. `K = ⊥`.  This contradicts
`Case2K1_ne_bot`, which says `F(U) ∩ K ≠ ⊥`.

(Equivalently: `s ∈ S₀` forces `s = t` to centralize `U ∩ M`, which is incompatible with `s`
inverting the non-trivial group `K = I_{U∩M}(s)`.) -/
theorem Case2SNotMemS0 (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (hbc : Work.GW2.BenderCtx G) (h : Work.GW2.Case2Ctx B) :
    h.D.s ∉ B.S0 := by
  intro hs
  -- `S₀` is cyclic and contains `t`, so its involution is unique: `s = t`.
  haveI : IsCyclic ↥B.S0 := B.S0_cyclic
  have hs_eq : h.D.s = B.t := by
    have h2 : (⟨h.D.s, hs⟩ : ↥B.S0) = ⟨B.t, B.t_mem⟩ :=
      eq_orderOf_eq_two_of_isCyclic
        (a := (⟨h.D.s, hs⟩ : ↥B.S0)) (b := (⟨B.t, B.t_mem⟩ : ↥B.S0))
        (by rw [Subgroup.orderOf_mk]; exact h.D.s_order)
        (by rw [Subgroup.orderOf_mk]; exact B.t_order)
    exact congrArg Subtype.val h2
  set X : Subgroup G := B.U ⊓ h.D.M with hX
  -- `t` centralizes `U`, so `B₀ = (U ∩ M) ∩ C(t) = U ∩ M = X`.
  have hXH : X ≤ B.H := by rw [hX]; exact le_trans inf_le_left B.U_le_H
  have hB0 : h.D.B0 = X := by
    rw [h.D.B0_def, hs_eq, hX]
    exact inf_eq_left.mpr (le_trans inf_le_left B.U_le_H)
  -- `X = U ∩ M` has odd order.
  have hXodd : Odd (Nat.card ↥X) := by
    rw [hX]
    exact Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le inf_le_left)
  -- `t` normalizes `U ∩ M` (it lies in `H` and in `M`).
  have htH : B.t ∈ B.H := B.S_le_H B.t_mem_S
  have htM : B.t ∈ h.D.M := layerIn_le h.D.M h.D.t_mem
  have htN : B.t ∈ Subgroup.normalizer (X : Set G) := by
    have hU : ∀ x ∈ B.U, B.t * x * B.t⁻¹ ∈ B.U := fun x hx =>
      (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal x B.t hx htH
    have hM : ∀ x ∈ h.D.M, B.t * x * B.t⁻¹ ∈ h.D.M := fun x hx =>
      h.D.M.mul_mem (h.D.M.mul_mem htM hx) (h.D.M.inv_mem htM)
    have hU' : ∀ x ∈ B.U, B.t⁻¹ * x * B.t ∈ B.U := fun x hx => by
      have h := (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal x B.t⁻¹ hx
        (B.H.inv_mem htH)
      simpa using h
    have hM' : ∀ x ∈ h.D.M, B.t⁻¹ * x * B.t ∈ h.D.M := fun x hx =>
      h.D.M.mul_mem (h.D.M.mul_mem (h.D.M.inv_mem htM) hx) htM
    refine mem_normalizer_of_conj (fun x hx => ?_) (fun x hx => ?_)
    · rw [hX] at hx ⊢
      obtain ⟨hxU, hxM⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨hU x hxU, hM x hxM⟩
    · rw [hX] at hx ⊢
      obtain ⟨hxU, hxM⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨hU' x hxU, hM' x hxM⟩
  -- Bender's `1.5(ii)`: `|I_X(t)| · |C_X(t)| = |X|`.
  have hcard := (I.toolkit.c15 G I.toolkit.ft X B.t B.t_order hXodd htN).2.1
  have hXinfH : X ⊓ Subgroup.centralizer ({B.t} : Set G) = X := inf_eq_left.mpr hXH
  rw [hXinfH] at hcard
  haveI : Nonempty ↥X := ⟨⟨1, X.one_mem⟩⟩
  have hXpos : 0 < Nat.card ↥X := Nat.card_pos
  have hIcard : (invSet X B.t).ncard = 1 :=
    Nat.mul_right_cancel hXpos (by simpa using hcard)
  -- `K = I_{U∩M}(s)` has cardinality one, hence is trivial.
  have hKset : (h.D.K : Set G) = invSet X B.t := by
    rw [h.D.K_def, hs_eq, hX]
  have hKcard : Nat.card ↥h.D.K = 1 := by
    rw [show Nat.card ↥h.D.K = (h.D.K : Set G).ncard from
      Nat.card_coe_set_eq (h.D.K : Set G), hKset]
    exact hIcard
  have hKbot : h.D.K = ⊥ := Subgroup.card_eq_one.mp hKcard
  -- contradicting Bender's `K₁ ≠ 1`.
  exact Case2K1_ne_bot I hbc h (by rw [hKbot, inf_bot_eq])

end Work.CORE4
