import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1aFrattini
import Submission.Work.CORE3.Case1aAbelian
import Submission.Work.CORE3.Case1aFrattiniApi
import Submission.Work.CORE3.Case1aFrattiniSAct
import Submission.Work.CORE3.relIndex_of_factorization_eq
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot
import Submission.Work.CORE3.A7V18.NP2Defs
import Submission.Work.CORE3.A7V18.PpartT2
import Submission.Work.CORE3.A7V18.CentralizerV2
import Submission.Work.CORE3.A7V18.FusionV2

/-!
# CORE3 / A7V18: `N_G(P₂) ⋬ H` (Bender 1981, §3, p. 222)

Deliverable `Work.CORE3.A7V18.NP2NotH`: in the subcase `Ĥ = H`, for `P₂ ∈ Syl_p(C_U(S))` the
normalizer `N_G(P₂)` is not contained in `H = C_G(t)`.

This is the `(t₂, P₂)`-side twin of the leaf `Work.CORE3.Case1aFrattini` (Bender's
"Then the Frattini argument forces the involutions in `Vᵢ` to be conjugate in `N_G(Pᵢ)`",
applied with `V₂ := ⟨t, t₂⟩` and `P₂` in place of `V₁ := ⟨t, t₁⟩` and `P₁ := O_p(U)·P₂`):

* `P₂ ≤ C_U(S)` is centralized by `S ∋ t, t₂` and lies in `U = O(H) ≤ H = C_G(t)`, so
  `V₂ ≤ C_G(P₂)` and `P₂ ≤ C_G(V₂)`;
* `|C_U(t₂)|_p = |C_U(S)|_p` — the `t₂`-analogue of `Work.CORE3.PpartProp` (`PpartT2`): the
  factor `|O_p(U)|` of the `t₁`-computation disappears because `t₂` *inverts* `O_p(U)`.
  With `C_G(V₂) = (U ⊓ C_G(t₂)) ⊔ V₂` (`CentralizerV2`) and `|V₂| = 4` this gives
  `P₂ ∈ Syl_p(C_G(V₂))` (`P2_sylow_centralizer_V2`);
* all involutions of `G` are conjugate and `N_G(V)` is transitive on `V#` for every four-group
  `V` (`LocalToolkit.fus`), so some `g ∈ N_G(V₂)` conjugates `t` to `t₂` (`FusionV2`);
* `P₂` conjugated by `g` is again a Sylow `p`-subgroup of `C_G(V₂)`, so some `c ∈ C_G(V₂)`
  conjugates it back to `P₂`; then `n := g c ∈ N_G(P₂)` and `n t n⁻¹ = t₂`, so
  `n ∉ H = C_G(t)` because `t ≠ t₂`.

Note that the argument does not use `Case1aFrattiniProp`, `Case1aAbelianProp` or `Ĥ = H`: it is
Bender's Frattini argument in the `(t₂, P₂)` direction, so `NP2NotH` is proved without them.
-/

open scoped MatrixGroups

namespace Work.CORE3.A7V18

open Subgroup
open Work.GW2

variable {G : Type} [Group G] [Finite G]

/-! ## The prime `D.p` is odd -/

/-- `D.p` is odd: `D.p ∈ π(F(U))` and `|F(U)|` divides the odd number `|U|`. -/
theorem odd_p (B : BenderSetup G) (D : Case1aData B) : Odd D.p := by
  have hpF : D.p ∣ Nat.card ↥(fittingIn B.U) := (Nat.mem_primeFactors.mp D.p_mem).2.1
  have hFdvd : Nat.card ↥(fittingIn B.U) ∣ Nat.card ↥B.U := by
    have h := Subgroup.relIndex_mul_card (fittingIn B.U) B.U
    rw [inf_eq_left.mpr (Work.CORE3.c1aFittingIn_le B.U)] at h
    exact ⟨(fittingIn B.U).relIndex B.U, h.symm.trans (mul_comm _ _)⟩
  exact Odd.of_dvd_nat (Work.CORE2A.bSetup_U_odd B) (hpF.trans hFdvd)

/-- `D.p ∤ 4`: `D.p` is odd, so it is not `2`. -/
theorem not_dvd_four (B : BenderSetup G) (D : Case1aData B) : ¬ D.p ∣ 4 := by
  intro h
  have hp2 : D.p ∣ 2 := by
    have h' : D.p ∣ 2 ^ 2 := by simpa using h
    exact Nat.Prime.dvd_of_dvd_pow D.hp h'
  have hpe : D.p = 2 := ((Nat.dvd_prime Nat.prime_two).mp hp2).resolve_left D.hp.ne_one
  have hpodd := odd_p B D
  rw [hpe] at hpodd
  exact (Odd.not_two_dvd_nat hpodd) (dvd_refl 2)

/-! ## `P₂` inside the centralizer of `V₂ = ⟨t, t₂⟩` -/

/-- `P₂ ≤ C_U(S)` is centralized by `S ∋ t, t₂` and lies in `U = O(H) ≤ H = C_G(t)`; hence
`P₂ ≤ C_G(V₂)`. -/
theorem P2_le_centralizer_V2 (B : BenderSetup G) (D : Case1aData B) {P2 : Subgroup G}
    (hP2le : P2 ≤ CUS B) :
    P2 ≤ Subgroup.centralizer ((V2 B D : Subgroup G) : Set G) := by
  rw [V2, Subgroup.centralizer_sup]
  refine le_inf ?_ ?_
  · rw [Work.CORE3.Work.CORE3.centralizer_zpowers_eq B.t]
    exact (hP2le.trans inf_le_left).trans (Work.CORE2A.bSetup_U_le_H B)
  · rw [Work.CORE3.Work.CORE3.centralizer_zpowers_eq D.t2]
    exact (hP2le.trans inf_le_right).trans (Subgroup.centralizer_le (by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact D.t2_mem))

/-! ## The `p`-part of `P₂` is that of `C_U(S)` -/

/-- A Sylow `p`-subgroup `P₂` of `C_U(S) = B.U ⊓ C_G(B.S)` has the same `p`-part of its order
as `C_U(S)` itself. -/
theorem factorization_P2_eq_CUS (B : BenderSetup G) (D : Case1aData B) {P2 : Subgroup G}
    (hP2le : P2 ≤ CUS B) (hP2syl : ¬ D.p ∣ P2.relIndex (CUS B)) :
    (Nat.card ↥P2).factorization D.p = (Nat.card ↥(CUS B)).factorization D.p := by
  have hrel : P2.relIndex (CUS B) * Nat.card ↥P2 = Nat.card ↥(CUS B) := by
    have h := Subgroup.relIndex_mul_card P2 (CUS B)
    rwa [inf_eq_left.mpr hP2le] at h
  have hne1 : P2.relIndex (CUS B) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hrel
    haveI : Nonempty ↥(CUS B) := ⟨⟨1, (CUS B).one_mem⟩⟩
    exact Nat.card_pos.ne' hrel.symm
  have hne2 : Nat.card ↥P2 ≠ 0 := by
    haveI : Nonempty ↥P2 := ⟨⟨1, P2.one_mem⟩⟩
    exact Nat.card_pos.ne'
  rw [← hrel, Nat.factorization_mul hne1 hne2]
  simp only [Finsupp.add_apply]
  rw [Nat.factorization_eq_zero_of_not_dvd hP2syl, zero_add]

/-! ## `V₂` normalizes `U ⊓ C_G(t₂)` and conjugates it inside `C_G(V₂)` -/

/-- `V₂ ≤ S ≤ H ≤ N_G(U)` and `V₂` centralizes `t₂`, hence `V₂` normalizes `U ⊓ C_G(t₂)`. -/
theorem V2_le_normalizer_inf_centralizer_t2 (B : BenderSetup G) (D : Case1aData B) :
    V2 B D ≤ Subgroup.normalizer
      ((B.U ⊓ Subgroup.centralizer ({D.t2} : Set G) : Subgroup G) : Set G) := by
  have hV2S : V2 B D ≤ (B.S : Subgroup G) := by
    rw [V2]
    exact sup_le (Subgroup.zpowers_le.mpr (B.S0_le B.t_mem))
      (Subgroup.zpowers_le.mpr D.t2_mem)
  have hV2H : V2 B D ≤ B.H := hV2S.trans (Work.CORE2A.bSetup_S_le_H B)
  have hV2C : V2 B D ≤ Subgroup.centralizer ({D.t2} : Set G) := by
    rw [V2]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ((Subgroup.mem_centralizer_iff.mp
        (Work.CORE2A.bSetup_S_le_H B D.t2_mem)) B.t (by simp)).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rfl
  have hNU : V2 B D ≤ Subgroup.normalizer (B.U : Set G) :=
    hV2H.trans (Work.CORE3.Work.CORE3.H_le_normalizer_U B)
  have hNC : V2 B D ≤ Subgroup.normalizer (Subgroup.centralizer ({D.t2} : Set G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    exact (Subgroup.centralizer ({D.t2} : Set G)).mul_mem
      ((Subgroup.centralizer ({D.t2} : Set G)).mul_mem (hV2C hx) hy)
      ((Subgroup.centralizer ({D.t2} : Set G)).inv_mem (hV2C hx))
  have hNinf : Subgroup.normalizer (B.U : Set G) ⊓
      Subgroup.normalizer (Subgroup.centralizer ({D.t2} : Set G) : Set G) ≤
      Subgroup.normalizer
        ((B.U ⊓ Subgroup.centralizer ({D.t2} : Set G) : Subgroup G) : Set G) := by
    intro x hx
    obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_normalizer_iff] at hxA hxB ⊢
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · intro hy
      exact ⟨(hxA y).mp hy.1, (hxB y).mp hy.2⟩
    · intro hy
      exact ⟨(hxA y).mpr hy.1, (hxB y).mpr hy.2⟩
  exact le_trans (le_inf hNU hNC) hNinf

/-! ## `|C_G(V₂)|_p = |C_U(t₂)|_p` -/

/-- Since `|V₂| = 4` is prime to the odd prime `p`, the subgroup `V₂` contributes nothing to the
`p`-part of `C_G(V₂) = (U ⊓ C_G(t₂)) ⊔ V₂`. -/
theorem factorization_centralizer_V2 (T : LocalToolkit) (hBc : BenderCtx G) (B : BenderSetup G)
    (D : Case1aData B) :
    (Nat.card ↥(Subgroup.centralizer ((V2 B D : Subgroup G) : Set G))).factorization D.p
      = (Nat.card ↥(B.U ⊓ Subgroup.centralizer ({D.t2} : Set G))).factorization D.p := by
  have hcen : Subgroup.centralizer ((V2 B D : Subgroup G) : Set G)
      = (B.U ⊓ Subgroup.centralizer ({D.t2} : Set G)) ⊔ V2 B D := CentralizerV2 G T hBc B D
  have hV2S : V2 B D ≤ (B.S : Subgroup G) := by
    rw [V2]
    exact sup_le (Subgroup.zpowers_le.mpr (B.S0_le B.t_mem))
      (Subgroup.zpowers_le.mpr D.t2_mem)
  have hinf : (B.U ⊓ Subgroup.centralizer ({D.t2} : Set G)) ⊓ V2 B D = ⊥ := by
    rw [inf_comm]
    refine le_bot_iff.mp ?_
    calc V2 B D ⊓ (B.U ⊓ Subgroup.centralizer ({D.t2} : Set G))
        ≤ V2 B D ⊓ B.U := le_inf inf_le_left (inf_le_right.trans inf_le_left)
      _ ≤ (B.S : Subgroup G) ⊓ B.U := le_inf (inf_le_left.trans hV2S) inf_le_right
      _ = ⊥ := by rw [inf_comm]; exact Work.CORE2A.inf_U_S_eq_bot B
  have hcard := Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot
    (H := B.U ⊓ Subgroup.centralizer ({D.t2} : Set G)) (K := V2 B D)
    (V2_le_normalizer_inf_centralizer_t2 B D) hinf
  have hV2fac : (Nat.card ↥(V2 B D)).factorization D.p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    have hdvdS : D.p ∣ Nat.card ↥(B.S : Subgroup G) :=
      hdvd.trans (Subgroup.card_dvd_of_le hV2S)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp B.S.isPGroup'
    have hp2 : D.p ∣ 2 := Nat.Prime.dvd_of_dvd_pow D.hp (hk ▸ hdvdS)
    have hpodd := odd_p B D
    rw [((Nat.dvd_prime Nat.prime_two).mp hp2).resolve_left D.hp.ne_one] at hpodd
    exact (Odd.not_two_dvd_nat hpodd) (dvd_refl 2)
  have hneA : Nat.card ↥(B.U ⊓ Subgroup.centralizer ({D.t2} : Set G)) ≠ 0 := by
    haveI : Nonempty ↥(B.U ⊓ Subgroup.centralizer ({D.t2} : Set G)) :=
      ⟨⟨1, (B.U ⊓ Subgroup.centralizer ({D.t2} : Set G)).one_mem⟩⟩
    exact Nat.card_pos.ne'
  have hneV : Nat.card ↥(V2 B D) ≠ 0 := by
    haveI : Nonempty ↥(V2 B D) := ⟨⟨1, (V2 B D).one_mem⟩⟩
    exact Nat.card_pos.ne'
  rw [hcen, hcard, Nat.factorization_mul hneA hneV]
  simp only [Finsupp.add_apply]
  rw [hV2fac, add_zero]

/-! ## `P₂ ∈ Syl_p(C_G(V₂))` -/

/-- The `p`-part of `P₂` is that of `C_G(V₂)`: chaining `factorization_P2_eq_CUS`,
`PpartT2` and `factorization_centralizer_V2`. -/
theorem P2_sylow_centralizer_V2 (T : LocalToolkit) (hFT : FeitThompsonProp)
    (hBc : BenderCtx G) (B : BenderSetup G) (D : Case1aData B) {P2 : Subgroup G}
    (hSAct : SActsTriviallyModFitting B) (hP2le : P2 ≤ CUS B)
    (hP2syl : ¬ D.p ∣ P2.relIndex (CUS B)) :
    ¬ D.p ∣ P2.relIndex (Subgroup.centralizer ((V2 B D : Subgroup G) : Set G)) := by
  refine Work.CORE3.relIndex_of_factorization_eq P2
    (Subgroup.centralizer ((V2 B D : Subgroup G) : Set G)) (P2_le_centralizer_V2 B D hP2le)
    D.p D.hp ?_
  calc (Nat.card ↥P2).factorization D.p
      = (Nat.card ↥(CUS B)).factorization D.p := factorization_P2_eq_CUS B D hP2le hP2syl
    _ = (Nat.card ↥(B.U ⊓ Subgroup.centralizer ({D.t2} : Set G))).factorization D.p :=
        (PpartT2 G hFT T hBc B D hSAct).symm
    _ = (Nat.card ↥(Subgroup.centralizer ((V2 B D : Subgroup G) : Set G))).factorization D.p :=
        (factorization_centralizer_V2 T hBc B D).symm

/-! ## The Frattini argument: `N_G(P₂)` contains an element conjugating `t` to `t₂` -/

/-- **The Frattini step.**  Some `n ∈ N_G(P₂)` conjugates `t` to `t₂`: transport `P₂` by the
fusion element `g ∈ N_G(V₂)` (`FusionV2`), which is again a Sylow `p`-subgroup of `C_G(V₂)`,
and move it back with an element of `C_G(V₂)` (`cj_ConjSylowOfSubgroup`). -/
theorem exists_normalizer_conj (T : LocalToolkit) (hBc : BenderCtx G) (B : BenderSetup G)
    (D : Case1aData B) {P2 : Subgroup G} (hP2le : P2 ≤ CUS B) (hP2grp : IsPGroup D.p P2)
    (hP2sylV2 : ¬ D.p ∣ P2.relIndex (Subgroup.centralizer ((V2 B D : Subgroup G) : Set G))) :
    ∃ n ∈ Subgroup.normalizer (P2 : Set G), n * B.t * n⁻¹ = D.t2 := by
  classical
  haveI : Fact D.p.Prime := ⟨D.hp⟩
  obtain ⟨g, hgN, hgt⟩ := FusionV2 G T hBc B D
  set V : Subgroup G := (V2 B D : Subgroup G) with hV
  set H : Subgroup G := Subgroup.centralizer (V : Set G) with hH
  have hP2leH : P2 ≤ H := P2_le_centralizer_V2 B D hP2le
  set Q : Subgroup G := P2.map (MulAut.conj g).toMonoidHom with hQ
  have hQH : Q ≤ H := Work.CORE3.Work.CORE3.cj_map_conj_le_centralizer V P2 g hgN hP2leH
  have hQgrp : IsPGroup D.p Q := hP2grp.map (MulAut.conj g).toMonoidHom
  have hcard : Nat.card ↥P2 = Nat.card ↥Q := by
    have h := Subgroup.card_map_of_injective (K := P2) (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective
    exact h.symm
  obtain ⟨c, hcH, hcQ⟩ := Work.CORE3.Work.CORE3.cj_ConjSylowOfSubgroup D.p D.hp H P2 Q
    hP2leH hQH hP2grp hQgrp hcard hP2sylV2
  have hfix : ∀ x : G, (c * g) * x * (c * g)⁻¹ = c * (g * x * g⁻¹) * c⁻¹ := by
    intro x; group
  have hct : c * D.t2 * c⁻¹ = D.t2 :=
    Work.CORE3.Work.CORE3.cj_conj_eq_self_of_mem_centralizer V hcH
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t2))
  refine ⟨c * g, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hfix x]
      refine (hcQ _).mp ?_
      rw [hQ]
      change (MulAut.conj g) x ∈ P2.map (MulAut.conj g).toMonoidHom
      exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
    · intro hx
      have h2 : c * (g * x * g⁻¹) * c⁻¹ ∈ P2 := by rw [← hfix x]; exact hx
      have h1 : g * x * g⁻¹ ∈ Q := (hcQ _).mpr h2
      rw [hQ, Work.CORE3.Work.CORE3.cj_mem_map_conj_iff] at h1
      have hconj : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rwa [hconj] at h1
  · calc (c * g) * B.t * (c * g)⁻¹ = c * (g * B.t * g⁻¹) * c⁻¹ := hfix B.t
      _ = c * D.t2 * c⁻¹ := by rw [hgt]
      _ = D.t2 := hct

/-! ## The deliverable -/

theorem NP2NotH (I : Work.CORE3.Case1Inputs) (hFr : Work.GW2.Case1aFrattiniProp)
    (hAb : Work.GW2.Case1aAbelianProp) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case1 B → B.Hhat = B.H → ∀ D : Work.GW2.Case1aData B, ∀ P2 : Subgroup G,
        P2 ≤ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
        ¬ D.p ∣ P2.relIndex (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) →
        ∃ n ∈ Subgroup.normalizer (P2 : Set G), n ∉ B.H := by
  intro G _instG _finG hFT hBc B h1 _hHH D P2 hP2le hP2grp hP2syl
  haveI hpprime : Fact D.p.Prime := ⟨D.hp⟩
  -- `S` acts trivially on `U/F(U)` (Case (1) of Theorem 2.10)
  have hSAct : SActsTriviallyModFitting B :=
    Work.CORE3.Case1aFrattiniSAct G hFT I.T hBc B h1
  -- `P₂` is a Sylow `p`-subgroup of `C_G(V₂)`
  have hP2sylV2 := P2_sylow_centralizer_V2 I.T hFT hBc B D hSAct hP2le hP2syl
  -- Frattini: some `n ∈ N_G(P₂)` conjugates `t` to `t₂`
  obtain ⟨n, hnN, hnt⟩ := exists_normalizer_conj I.T hBc B D hP2le hP2grp hP2sylV2
  refine ⟨n, hnN, fun hnH => ?_⟩
  -- `n ∈ H = C_G(t)` would force `t = n t n⁻¹ = t₂`, but `t ∈ S₀` and `t₂ ∉ S₀`
  have hfix : n * B.t * n⁻¹ = B.t := by
    refine Work.CORE3.Work.CORE3.cj_conj_eq_self_of_mem_centralizer (Subgroup.zpowers B.t)
      ?_ (Subgroup.mem_zpowers B.t)
    rw [Work.CORE3.Work.CORE3.centralizer_zpowers_eq B.t]
    exact hnH
  have htne : B.t ≠ D.t2 := fun h => D.t2_nmem (h ▸ B.t_mem)
  exact htne (hfix.symm.trans hnt)

end Work.CORE3.A7V18
