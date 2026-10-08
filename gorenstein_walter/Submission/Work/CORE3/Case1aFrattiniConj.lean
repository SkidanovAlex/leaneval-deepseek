import Mathlib
import Submission.Work.CORE3.Case1aFrattiniApi
import Submission.Work.CORE3.Case1aFrattini

/-!
# The Frattini conjugation step of Bender 1981 §3 (subcase (1a))

With `D : Case1aData B`, `P = O_p(U)` and `P₂` a Sylow `p`-subgroup of `C_U(S)`, put
`P₁ = P · P₂`, a Sylow `p`-subgroup of `C_G(V₁)`, `V₁ = ⟨t,t₁⟩` (`P1SylowIn B D P₂`).

This file proves that some element `n` of the normalizer of `P₁` conjugates the central
involution `t` of `S` to the reflection `t₁`:

`∃ n ∈ N_G(P₁), n * t * n⁻¹ = t₁`.

The argument: all involutions of the four-group `V₁` are conjugate in `G`, and in fact
`t` is conjugated to `t₁` by an element `g ∈ N_G(V₁)` (involution fusion, `T.fus`).
Then `g P₁ g⁻¹` is again a Sylow `p`-subgroup of `C_G(V₁)`, so by Sylow conjugacy inside
`C_G(V₁)` there is `c ∈ C_G(V₁)` with `c (g P₁ g⁻¹) c⁻¹ = P₁`; then `n = c g` normalizes
`P₁` and `n t n⁻¹ = c t₁ c⁻¹ = t₁` because `c` centralizes `V₁ ∋ t₁`.
-/

open scoped MatrixGroups Pointwise

namespace Work.CORE3

open Work.GW2
open Subgroup

set_option linter.style.haveILetI false
set_option linter.dupNamespace false

/-! ## Elementary conjugation lemmas -/

/-- Membership in the image of a subgroup under conjugation. -/
lemma mem_map_conj_iff {G : Type} [Group G] (P : Subgroup G) (n z : G) :
    z ∈ P.map (MulAut.conj n).toMonoidHom ↔ n⁻¹ * z * n ∈ P := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxz⟩
    rw [← hxz]
    change n⁻¹ * (MulAut.conj n) x * n ∈ P
    rw [MulAut.conj_apply]
    have h : n⁻¹ * (n * x * n⁻¹) * n = x := by group
    rw [h]
    exact hx
  · intro hz
    refine ⟨n⁻¹ * z * n, hz, ?_⟩
    change (MulAut.conj n) (n⁻¹ * z * n) = z
    rw [MulAut.conj_apply]
    group

/-- Conjugating a subgroup of `C_G(V)` by an element of `N_G(V)` keeps it inside `C_G(V)`. -/
lemma map_conj_le_centralizer {G : Type} [Group G] (V P : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hP : P ≤ Subgroup.centralizer (V : Set G)) :
    P.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (V : Set G) := by
  rintro y ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvg : g⁻¹ * v * g ∈ V := ((Subgroup.mem_normalizer_iff''.mp hg) v).mp hv
  have hcx : x * (g⁻¹ * v * g) = (g⁻¹ * v * g) * x :=
    ((Subgroup.mem_centralizer_iff.mp (hP hx)) (g⁻¹ * v * g) hvg).symm
  change v * (MulAut.conj g) x = (MulAut.conj g) x * v
  rw [MulAut.conj_apply]
  calc v * (g * x * g⁻¹) = g * (g⁻¹ * v * g) * x * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [hcx]; group
    _ = (g * x * g⁻¹) * v := by group

/-- An element of `C_G(V)` fixes every element of `V` by conjugation. -/
lemma conj_eq_self_of_mem_centralizer {G : Type} [Group G] (V : Subgroup G) {c x : G}
    (hc : c ∈ Subgroup.centralizer (V : Set G)) (hx : x ∈ V) : c * x * c⁻¹ = x := by
  have h : x * c = c * x := (Subgroup.mem_centralizer_iff.mp hc) x hx
  calc c * x * c⁻¹ = x * c * c⁻¹ := by rw [h]
    _ = x := by group

/-! ## Sylow conjugacy inside a subgroup -/

/-- **Sylow conjugacy inside a subgroup.**  If `P ≤ H` is a Sylow `p`-subgroup of `H`
(`IsPGroup p P` together with `¬ p ∣ P.relIndex H`) and `Q ≤ H` is a `p`-subgroup of `H`
with `|Q| = |P|`, then `Q` is conjugate to `P` by an element of `H`. -/
theorem ConjSylowOfSubgroup {G : Type} [Group G] [Finite G] (p : ℕ) (hp : p.Prime)
    (H P Q : Subgroup G) (hP : P ≤ H) (hQ : Q ≤ H) (hPg : IsPGroup p P)
    (hQg : IsPGroup p Q) (hcard : Nat.card ↥P = Nat.card ↥Q) (hPrel : ¬ p ∣ P.relIndex H) :
    ∃ h ∈ H, ∀ x : G, x ∈ Q ↔ h * x * h⁻¹ ∈ P := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- Transport `P` and `Q` into the subgroup `H`.
  set P' : Subgroup ↥H := P.subgroupOf H with hP'def
  set Q' : Subgroup ↥H := Q.subgroupOf H with hQ'def
  have hP'p : IsPGroup p P' := by
    have h := hPg.comap_of_injective H.subtype H.subtype_injective
    rwa [Subgroup.comap_subtype] at h
  have hQ'p : IsPGroup p Q' := by
    have h := hQg.comap_of_injective H.subtype H.subtype_injective
    rwa [Subgroup.comap_subtype] at h
  -- Cardinalities of the transported subgroups.
  have hcardP : Nat.card ↥P' = Nat.card ↥P := by
    have h := Subgroup.card_map_of_injective (K := P') (f := H.subtype) H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hP] at h
    exact h.symm
  have hcardQ : Nat.card ↥Q' = Nat.card ↥Q := by
    have h := Subgroup.card_map_of_injective (K := Q') (f := H.subtype) H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hQ] at h
    exact h.symm
  have hcard' : Nat.card ↥P' = Nat.card ↥Q' := hcardP.trans (hcard.trans hcardQ.symm)
  -- The index of `P'` in `↥H` is `P.relIndex H`.
  have hP'index : P'.index = P.relIndex H := by
    have h := Subgroup.relIndex_subgroupOf (H := P) (K := H) (L := H) le_rfl
    rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right] at h
    exact h
  have hP'notdvd : ¬ p ∣ P'.index := by rw [hP'index]; exact hPrel
  -- `Q'` has the same index, by comparing cardinalities.
  have hQ'index : Q'.index = P'.index := by
    have hpos : 0 < Nat.card ↥P' := by
      haveI : Nonempty ↥P' := ⟨⟨1, P'.one_mem⟩⟩
      exact Nat.card_pos
    have h1 := Subgroup.card_mul_index P'
    have h2 := Subgroup.card_mul_index Q'
    have hmain : Nat.card ↥P' * P'.index = Nat.card ↥P' * Q'.index := by
      rw [h1, ← h2, ← hcard']
    exact (Nat.mul_left_cancel hpos hmain).symm
  have hQ'notdvd : ¬ p ∣ Q'.index := by rw [hQ'index]; exact hP'notdvd
  -- Sylow objects and Sylow conjugacy inside `↥H`.
  let S₁ : Sylow p ↥H := hP'p.toSylow hP'notdvd
  let S₂ : Sylow p ↥H := hQ'p.toSylow hQ'notdvd
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (M := ↥H) S₂ S₁
  have hsmul : MulAut.conj c • Q' = P' := by
    have h := congrArg (fun S : Sylow p ↥H => (S : Subgroup ↥H)) hc
    rw [Sylow.coe_subgroup_smul] at h
    exact h
  refine ⟨(c : G), c.2, ?_⟩
  intro x
  constructor
  · intro hx
    have hm : MulAut.conj c • (⟨x, hQ hx⟩ : ↥H) ∈ MulAut.conj c • Q' :=
      Subgroup.smul_mem_pointwise_smul (⟨x, hQ hx⟩ : ↥H) (MulAut.conj c) Q'
        (Subgroup.mem_subgroupOf.mpr hx)
    rw [hsmul] at hm
    have hm' : ((MulAut.conj c • (⟨x, hQ hx⟩ : ↥H) : ↥H) : G) ∈ P :=
      Subgroup.mem_subgroupOf.mp hm
    simpa [MulAut.conj_apply] using hm'
  · intro hx
    have hxH : c * x * c⁻¹ ∈ H := hP hx
    have hm : (⟨c * x * c⁻¹, hxH⟩ : ↥H) ∈ MulAut.conj c • Q' := by
      rw [hsmul]
      exact Subgroup.mem_subgroupOf.mpr hx
    obtain ⟨s, hsQ', hs⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hm
    have hsG : (s : G) = x := by
      have h2 := congrArg (fun z : ↥H => (z : G)) hs
      simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul] at h2
      exact mul_left_cancel (mul_right_cancel h2)
    rw [← hsG]
    exact Subgroup.mem_subgroupOf.mp hsQ'

/-! ## Involution fusion in `V₁ = ⟨t,t₁⟩` -/

/-- The involutions of the four-group `V₁ = ⟨t,t₁⟩` are conjugate in `N_G(V₁)`: in particular
some `g ∈ N_G(V₁)` conjugates `t` to `t₁`.  This is Bender's involution fusion
(`InvolutionFusionProp`), applied to `S` and to the four-group `V₁`. -/
theorem FusionNormalizerV1 (G : Type) [Group G] [Finite G] (T : LocalToolkit)
    (hBc : BenderCtx G) (B : BenderSetup G) (D : Case1aData B) :
    ∃ g ∈ Subgroup.normalizer ((V1 B D : Subgroup G) : Set G), g * B.t * g⁻¹ = D.t1 := by
  obtain ⟨n, hn2, hdih⟩ := SylowDihedral G hBc B
  -- `G` has no normal subgroup of index two (simplicity and non-abelianness).
  have hnoindex : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
    intro N hN hN2
    haveI := hN
    rcases hBc.simple.eq_bot_or_eq_top_of_normal N with h | h
    · -- `N = ⊥` forces `|G| = 2`, hence `G` abelian.
      exfalso
      have hidx : (⊥ : Subgroup G).index = 2 := by rw [← h]; exact hN2
      have hcardG : Nat.card G = 2 := by
        have h1 := Subgroup.card_mul_index (⊥ : Subgroup G)
        rw [hidx, Subgroup.card_bot] at h1
        simpa using h1.symm
      have hcomm : ∀ a b : G, a * b = b * a := by
        have hsq : ∀ a : G, a ^ 2 = 1 := by
          intro a
          have hdvd : orderOf a ∣ 2 := hcardG ▸ orderOf_dvd_natCard a
          rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h1 | h1
          · rw [orderOf_eq_one_iff.mp h1, one_pow]
          · rw [← h1]; exact pow_orderOf_eq_one a
        intro a b
        have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq a)
        have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq b)
        have hab : (a * b)⁻¹ = a * b :=
          inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq (a * b))
        have hba : b * a = a * b := by
          rw [mul_inv_rev, ha, hb] at hab
          exact hab
        exact hba.symm
      obtain ⟨a, b, hab⟩ := hBc.nonab
      exact hab (hcomm a b)
    · -- `N = ⊤` has index one.
      rw [h, Subgroup.index_top] at hN2
      exact absurd hN2 (by norm_num)
  -- Both `t` and `t₁` are nontrivial elements of the four-group `V₁`.
  have hV4 : IsFourGroup (V1 B D) := _root_.Work.CORE3.Work.CORE3.fourGroup_V1 hBc B D
  have ht : B.t ≠ 1 := by
    intro h1
    have h2 : orderOf B.t = 1 := by rw [h1]; exact orderOf_one
    rw [B.t_order] at h2
    exact absurd h2 (by norm_num)
  have ht1 : D.t1 ≠ 1 := by
    intro h1
    have h2 : orderOf D.t1 = 1 := by rw [h1]; exact orderOf_one
    rw [D.t1_order] at h2
    exact absurd h2 (by norm_num)
  exact (T.fus G B.S n hn2 hdih hnoindex).2 (V1 B D) hV4 B.t
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t)) D.t1
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t1)) ht ht1

/-! ## The main theorem -/

/-- **The Frattini conjugation step.**  With `P₁ = O_p(U)·P₂` a Sylow `p`-subgroup of
`C_G(V₁)`, some `n ∈ N_G(P₁)` conjugates `t` to `t₁`. -/
theorem Case1aFrattiniConj (G : Type) [Group G] [Finite G] (T : Work.GW2.LocalToolkit) (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case1aData B) (P2 : Subgroup G) (hsyl : Work.CORE3.P1SylowIn B D P2) : ∃ n ∈ Subgroup.normalizer ((Work.GW2.pCoreIn D.p B.U ⊔ P2 : Subgroup G) : Set G), n * B.t * n⁻¹ = D.t1 := by
  classical
  obtain ⟨hP1le, hP1grp, hP1rel⟩ := hsyl
  obtain ⟨n0, hn0N, hn0t⟩ := FusionNormalizerV1 G T hBc B D
  set P1 : Subgroup G := (pCoreIn D.p B.U ⊔ P2 : Subgroup G) with hP1def
  set H : Subgroup G := Subgroup.centralizer ((V1 B D : Subgroup G) : Set G) with hHdef
  have hP1leH : P1 ≤ H := hP1le
  -- the conjugate `Q = n₀ P₁ n₀⁻¹` is again a Sylow `p`-subgroup of `C_G(V₁)`
  set Q : Subgroup G := P1.map (MulAut.conj n0).toMonoidHom with hQdef
  have hQH : Q ≤ H := map_conj_le_centralizer (V1 B D) P1 n0 hn0N hP1leH
  have hQgrp : IsPGroup D.p Q := hP1grp.map (MulAut.conj n0).toMonoidHom
  have hcard : Nat.card ↥P1 = Nat.card ↥Q := by
    have h := Subgroup.card_map_of_injective (K := P1) (f := (MulAut.conj n0).toMonoidHom)
      (MulAut.conj n0).injective
    exact h.symm
  obtain ⟨c, hcH, hcQ⟩ :=
    ConjSylowOfSubgroup D.p D.hp H P1 Q hP1leH hQH hP1grp hQgrp hcard hP1rel
  -- `c ∈ C_G(V₁)`, hence `c` fixes `t₁`, and `c` conjugates `Q` back onto `P₁`
  have hfix : ∀ x : G, (c * n0) * x * (c * n0)⁻¹ = c * (n0 * x * n0⁻¹) * c⁻¹ := by
    intro x; group
  have hct : c * D.t1 * c⁻¹ = D.t1 :=
    conj_eq_self_of_mem_centralizer (V1 B D) hcH
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t1))
  refine ⟨c * n0, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hfix x]
      refine (hcQ _).mp ?_
      rw [hQdef]
      change (MulAut.conj n0) x ∈ P1.map (MulAut.conj n0).toMonoidHom
      exact Subgroup.mem_map_of_mem (MulAut.conj n0).toMonoidHom hx
    · intro hx
      have h2 : c * (n0 * x * n0⁻¹) * c⁻¹ ∈ P1 := by rw [← hfix x]; exact hx
      have h1 : n0 * x * n0⁻¹ ∈ Q := (hcQ _).mpr h2
      rw [hQdef, mem_map_conj_iff] at h1
      have hconj : n0⁻¹ * (n0 * x * n0⁻¹) * n0 = x := by group
      rwa [hconj] at h1
  · calc (c * n0) * B.t * (c * n0)⁻¹ = c * (n0 * B.t * n0⁻¹) * c⁻¹ := hfix B.t
      _ = c * D.t1 * c⁻¹ := by rw [hn0t]
      _ = D.t1 := hct

end Work.CORE3
