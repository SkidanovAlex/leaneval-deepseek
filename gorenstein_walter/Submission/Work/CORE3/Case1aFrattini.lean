import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.SylowLeCentralizer
import Submission.Work.ASM.CyclicSylow
import Submission.Work.CORE3.Case1aFrattiniApi
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.OutsideS0OrderTwo
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.CORE2A.normalizer_eq_of_coatom
import Submission.Work.CORE2A.exists_mul_of_mem_sup_of_normal
import Submission.Work.CORE2A.bswHyps2_of_config2
import Submission.Work.CORE2A.thm26_aux
import Submission.Work.CORE2A.exists_mul_of_mem_involutionSet_H
import Submission.Work.CORE2A.exists_mul_of_notMem_of_relIndex_eq_two
import Submission.Work.CORE2A.mul_mem_involutionSet_H
import Submission.Work.CORE3.Case1aSetup
import Submission.Work.CORE3.Case1aP_ne_bot
import Submission.Work.CORE3.Case1aPpart
import Submission.Work.CORE3.Case1aP1Sylow

namespace Work.CORE3

namespace Work.CORE3

open Work.GW2
open Subgroup
open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

theorem sact_reflection {G : Type} [Group G] [Finite G] (hBc : BenderCtx G)
    (B : BenderSetup G) (h1 : Case1 B) {x : G} (hxS : x ∈ (B.S : Subgroup G))
    (hxS0 : x ∉ B.S0) {u : G} (hu : u ∈ B.U) :
    u⁻¹ * (x * u * x⁻¹) ∈ fittingIn B.U := by
  obtain ⟨n, hn2, hdih⟩ := Work.CORE3.SylowDihedral G hBc B
  have hxord : orderOf x = 2 := Work.CORE3.OutsideS0OrderTwo G hBc B n hn2 hdih x hxS hxS0
  have hx2 : x * x = 1 := by
    have h : x ^ 2 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
    simpa [pow_two] using h
  obtain ⟨Ix, hIxc, hHallx⟩ := h1.1 x hxS hxS0
  -- `x` normalizes `U`, so `u⁻¹ * (x * u * x⁻¹) ∈ U`
  have hxU : x ∈ Subgroup.normalizer (B.U : Set G) :=
    Work.CORE2A.bender_s_mem_normalizer_U B hxS
  have hmemU : u⁻¹ * (x * u * x⁻¹) ∈ B.U :=
    B.U.mul_mem (B.U.inv_mem hu) ((Subgroup.mem_normalizer_iff.mp hxU u).mp hu)
  -- and `x` inverts it, so it lies in `I_U(x) ⊆ F(U)`
  have hinv : x * (u⁻¹ * (x * u * x⁻¹)) * x⁻¹ = (u⁻¹ * (x * u * x⁻¹))⁻¹ :=
    Work.CORE3.c1aInverted_of_sq_eq_one hx2
  refine hHallx.1 ?_
  show u⁻¹ * (x * u * x⁻¹) ∈ (Ix : Set G)
  rw [hIxc]
  exact Work.CORE2A.mem_invSet.mpr ⟨hmemU, hinv⟩


theorem sact_conj {G : Type} [Group G] [Finite G] (B : BenderSetup G) {x : G}
    (hxS : x ∈ (B.S : Subgroup G)) {z : G} (hz : z ∈ fittingIn B.U) :
    x * z * x⁻¹ ∈ fittingIn B.U := by
  have hxU : x ∈ Subgroup.normalizer (B.U : Set G) :=
    Work.CORE2A.bender_s_mem_normalizer_U B hxS
  have hxU' : x⁻¹ ∈ Subgroup.normalizer (B.U : Set G) :=
    (Subgroup.normalizer (B.U : Set G)).inv_mem hxU
  have hFs : conjSub x⁻¹ (fittingIn B.U) = fittingIn B.U :=
    Work.CORE3.c1aConjSub_fittingIn_eq_self hxU'
  have hz' : z ∈ conjSub x⁻¹ (fittingIn B.U) := by rw [hFs]; exact hz
  exact (Work.CORE2A.mem_conjSub_iff' (g := x) (K := fittingIn B.U) (x := z)).mp hz'


private theorem sact_aux (hFT : FeitThompsonProp)
    (T : LocalToolkit) (hBc : BenderCtx G) (B : BenderSetup G)
    (h1 : Case1 B) : SActsTriviallyModFitting B := by
  intro s hsS u hu
  by_cases hs0 : s ∈ B.S0
  · -- `s ∈ S₀` is a product of two reflections `x`, `y` of `S − S₀`
    obtain ⟨y, hyS, hyS0⟩ := Work.CORE2A.bSetup_exists_mem_S_not_mem_S0 B
    set x : G := s * y⁻¹ with hxdef
    have hxS : x ∈ (B.S : Subgroup G) := by
      rw [hxdef]
      exact (B.S : Subgroup G).mul_mem hsS ((B.S : Subgroup G).inv_mem hyS)
    have hxS0 : x ∉ B.S0 := by
      intro hx
      refine hyS0 ?_
      have h : s⁻¹ * x ∈ B.S0 := B.S0.mul_mem (B.S0.inv_mem hs0) hx
      rw [hxdef, ← mul_assoc, inv_mul_cancel, one_mul] at h
      simpa using B.S0.inv_mem h
    have hs_eq : s = x * y := by rw [hxdef]; group
    have hA : u⁻¹ * (x * u * x⁻¹) ∈ fittingIn B.U :=
      sact_reflection hBc B h1 hxS hxS0 hu
    have hB' : u⁻¹ * (y * u * y⁻¹) ∈ fittingIn B.U :=
      sact_reflection hBc B h1 hyS hyS0 hu
    have hC : x * (u⁻¹ * (y * u * y⁻¹)) * x⁻¹ ∈ fittingIn B.U :=
      sact_conj B hxS hB'
    have hD : (u⁻¹ * (x * u * x⁻¹)) * (x * (u⁻¹ * (y * u * y⁻¹)) * x⁻¹) ∈ fittingIn B.U :=
      (fittingIn B.U).mul_mem hA hC
    rw [hs_eq]
    convert hD using 1
    group
  · -- `s ∈ S − S₀` is a reflection
    exact sact_reflection hBc B h1 hsS hs0 hu



/-! ## Elementary conjugation lemmas -/

/-- Membership in the image of a subgroup under conjugation. -/
lemma cj_mem_map_conj_iff {G : Type} [Group G] (P : Subgroup G) (n z : G) :
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
lemma cj_map_conj_le_centralizer {G : Type} [Group G] (V P : Subgroup G) (g : G)
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
lemma cj_conj_eq_self_of_mem_centralizer {G : Type} [Group G] (V : Subgroup G) {c x : G}
    (hc : c ∈ Subgroup.centralizer (V : Set G)) (hx : x ∈ V) : c * x * c⁻¹ = x := by
  have h : x * c = c * x := (Subgroup.mem_centralizer_iff.mp hc) x hx
  calc c * x * c⁻¹ = x * c * c⁻¹ := by rw [h]
    _ = x := by group

/-! ## Sylow conjugacy inside a subgroup -/

/-- **Sylow conjugacy inside a subgroup.**  If `P ≤ H` is a Sylow `p`-subgroup of `H`
(`IsPGroup p P` together with `¬ p ∣ P.relIndex H`) and `Q ≤ H` is a `p`-subgroup of `H`
with `|Q| = |P|`, then `Q` is conjugate to `P` by an element of `H`. -/
theorem cj_ConjSylowOfSubgroup {G : Type} [Group G] [Finite G] (p : ℕ) (hp : p.Prime)
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
theorem cj_FusionNormalizerV1 (G : Type) [Group G] [Finite G] (T : LocalToolkit)
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
  have hV4 : IsFourGroup (V1 B D) := fourGroup_V1 hBc B D
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
private theorem conj_aux (G : Type) [Group G] [Finite G] (T : LocalToolkit) (hBc : BenderCtx G) (B : BenderSetup G) (D : Case1aData B) (P2 : Subgroup G) (hsyl : Work.CORE3.P1SylowIn B D P2) : ∃ n ∈ Subgroup.normalizer ((Work.GW2.pCoreIn D.p B.U ⊔ P2 : Subgroup G) : Set G), n * B.t * n⁻¹ = D.t1 := by
  classical
  obtain ⟨hP1le, hP1grp, hP1rel⟩ := hsyl
  obtain ⟨n0, hn0N, hn0t⟩ := cj_FusionNormalizerV1 G T hBc B D
  set P1 : Subgroup G := (pCoreIn D.p B.U ⊔ P2 : Subgroup G) with hP1def
  set H : Subgroup G := Subgroup.centralizer ((V1 B D : Subgroup G) : Set G) with hHdef
  have hP1leH : P1 ≤ H := hP1le
  -- the conjugate `Q = n₀ P₁ n₀⁻¹` is again a Sylow `p`-subgroup of `C_G(V₁)`
  set Q : Subgroup G := P1.map (MulAut.conj n0).toMonoidHom with hQdef
  have hQH : Q ≤ H := cj_map_conj_le_centralizer (V1 B D) P1 n0 hn0N hP1leH
  have hQgrp : IsPGroup D.p Q := hP1grp.map (MulAut.conj n0).toMonoidHom
  have hcard : Nat.card ↥P1 = Nat.card ↥Q := by
    have h := Subgroup.card_map_of_injective (K := P1) (f := (MulAut.conj n0).toMonoidHom)
      (MulAut.conj n0).injective
    exact h.symm
  obtain ⟨c, hcH, hcQ⟩ :=
    cj_ConjSylowOfSubgroup D.p D.hp H P1 Q hP1leH hQH hP1grp hQgrp hcard hP1rel
  -- `c ∈ C_G(V₁)`, hence `c` fixes `t₁`, and `c` conjugates `Q` back onto `P₁`
  have hfix : ∀ x : G, (c * n0) * x * (c * n0)⁻¹ = c * (n0 * x * n0⁻¹) * c⁻¹ := by
    intro x; group
  have hct : c * D.t1 * c⁻¹ = D.t1 :=
    cj_conj_eq_self_of_mem_centralizer (V1 B D) hcH
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
      rw [hQdef, cj_mem_map_conj_iff] at h1
      have hconj : n0⁻¹ * (n0 * x * n0⁻¹) * n0 = x := by group
      rwa [hconj] at h1
  · calc (c * n0) * B.t * (c * n0)⁻¹ = c * (n0 * B.t * n0⁻¹) * c⁻¹ := hfix B.t
      _ = c * D.t1 * c⁻¹ := by rw [hn0t]
      _ = D.t1 := hct


/-- Bender 1981 §3, p. 222, second step.  Deliverable `Work.GW2.Case1aFrattiniProp`, with the
area's six inputs bundled in `I : Case1Inputs`.

With `D : Case1aData B` and `P₂ ∈ Syl_p(C_U(S))` (`P₂ ≤ U ⊓ C_G(S)`, `IsPGroup D.p P₂`,
`¬ p ∣ P₂.relIndex (U ⊓ C_G(S))`), put `P = O_p(U) = pCoreIn D.p B.U` and `P₁ = P P₂`.
Then `P₁ ∈ Syl_p(C_G(⟨t,t₁⟩))`.  The involutions of `V₁ = ⟨t,t₁⟩` are conjugate in `G`
(toolkit `InvolutionFusionProp`, `I.T.fus`), and conjugating `t` to `t₁` moves `P₁` to another
Sylow `p`-subgroup of `C_G(V₁)`, so the Frattini argument conjugates `t` to `t₁` inside `N_G(P₁)`.
If `N_G(P₁) ≤ H = C_G(t)` we would get `t₁ = t`, contradicting `t₁ ∉ S₀ ∋ t`; hence
`N_G(P₁) ⊄ H`, and consequently `P₁ ≠ P` and `P₂ ≠ 1` (else `H ≤ N_G(P)` and maximality of
`Ĥ = H` makes `P ⊴ G`, impossible in the simple group `G`). -/
theorem Case1aFrattini (I : Case1Inputs) : Case1aFrattiniProp := by
  intro G hG hFin hFT hBc B h1 hH D P2 hP2le hP2grp hP2syl
  haveI : IsSimpleGroup G := hBc.simple
  -- Step 1: `S` acts trivially on `U/F(U)` (Bender §3, p. 222).
  have hSAct : SActsTriviallyModFitting B := sact_aux hFT I.T hBc B h1
  -- Step 2: the `p`-part of `C_U(t₁)` is `|O_p(U)| · |C_U(S)|_p`.
  have hppart : PpartProp B D := Work.CORE3.Case1aPpart G hFT I.T hBc B D hSAct
  -- Step 3: `P₁ = O_p(U)·P₂` is a Sylow `p`-subgroup of `C_G(V₁)`.
  have hP1 : P1SylowIn B D P2 := Work.CORE3.Case1aP1Sylow G hFT I.T hBc B D P2 hP2le hP2grp hP2syl hppart
  -- Step 4: the Frattini argument conjugates `t` to `t₁` inside `N_G(P₁)`.
  have hconj : ∃ n ∈ Subgroup.normalizer ((pCoreIn D.p B.U ⊔ P2 : Subgroup G) : Set G),
      n * B.t * n⁻¹ = D.t1 := conj_aux G I.T hBc B D P2 hP1
  -- Step 5: `O_p(U) ≠ 1`.
  have hPne : pCoreIn D.p B.U ≠ ⊥ := Work.CORE3.Case1aP_ne_bot G B D
  have hP_le_H : pCoreIn D.p B.U ≤ B.H :=
    le_trans (Work.CORE3.c1aPcoreIn_le_self D.p B.U) (Work.CORE2A.bSetup_U_le_H B)
  have hH_le_normP : B.H ≤ Subgroup.normalizer (pCoreIn D.p B.U : Set G) := by
    haveI : Fact D.p.Prime := ⟨D.hp⟩
    exact H_le_normalizer_P B D.p
  -- `N_G(P₁) ⊄ H`: an element of `N_G(P₁)` conjugates `t` to `t₁`, which is impossible in
  -- `H = C_G(t)`.
  have hnotle : ¬ Subgroup.normalizer ((pCoreIn D.p B.U ⊔ P2 : Subgroup G) : Set G) ≤ B.H := by
    intro hle
    obtain ⟨n, hn, hconjn⟩ := hconj
    have hnH : n ∈ B.H := hle hn
    have hfix : n * B.t * n⁻¹ = B.t := by
      have hmem : n ∈ Subgroup.centralizer ({B.t} : Set G) := hnH
      have := (Subgroup.mem_centralizer_iff.mp hmem) B.t (by simp)
      rw [← this]; group
    exact D.t1_nmem (by rw [← hconjn, hfix]; exact B.t_mem)
  -- `P₁ ≠ P`: otherwise `H ≤ N_G(P)` and maximality of `Ĥ = H` makes `P` normal in the
  -- simple group `G`.
  have hne : (pCoreIn D.p B.U ⊔ P2 : Subgroup G) ≠ pCoreIn D.p B.U := by
    intro heq
    have hnotleP : ¬ Subgroup.normalizer (pCoreIn D.p B.U : Set G) ≤ B.H := fun hleP =>
      hnotle (by rw [heq]; exact hleP)
    have hleHhat : B.Hhat ≤ Subgroup.normalizer (pCoreIn D.p B.U : Set G) := hH ▸ hH_le_normP
    have hlt : B.Hhat < Subgroup.normalizer (pCoreIn D.p B.U : Set G) := by
      refine lt_of_le_of_ne hleHhat ?_
      intro hcontra
      have h1 : B.Hhat ≤ B.H := le_of_eq hH
      rw [hcontra] at h1
      exact hnotleP h1
    have htop : Subgroup.normalizer (pCoreIn D.p B.U : Set G) = ⊤ :=
      (B.Hhat_coatom.lt_iff).mp hlt
    haveI hPn : Subgroup.Normal (pCoreIn D.p B.U) := Subgroup.normalizer_eq_top_iff.mp htop
    rcases Subgroup.Normal.eq_bot_or_eq_top (pCoreIn D.p B.U) with hbot | htopP
    · exact hPne hbot
    · refine B.Hhat_coatom.ne_top (top_le_iff.mp ?_)
      rw [← htopP]
      exact hP_le_H.trans (le_of_eq hH.symm)
  have hP2ne : P2 ≠ ⊥ := fun hbot => hne (by rw [hbot, sup_bot_eq])
  exact ⟨hnotle, hne, hP2ne⟩


end Work.CORE3

open Work.GW2

/-- The same lemma, mirrored at the namespace of the file path, so that it can be cited both as
`Work.CORE3.Case1aFrattini` (the name the CORE3 assembly uses) and as
`Work.CORE3.Work.CORE3.Case1aFrattini` (the skeleton's namespace layout). -/
theorem Case1aFrattini (I : Case1Inputs) : Case1aFrattiniProp :=
  _root_.Work.CORE3.Work.CORE3.Case1aFrattini I

end Work.CORE3
