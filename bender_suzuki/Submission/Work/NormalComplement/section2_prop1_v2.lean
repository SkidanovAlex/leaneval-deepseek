import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Prelim
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.case1_normalizer_le
import Submission.Work.NormalComplement.KsetFacts
import Submission.Work.NormalComplement.case2_normalizer_le_v2
import Submission.Work.NormalComplement.pcontrol_prod_v2
import Submission.Work.NormalComplement.prop2b_conj_into_centD
import Submission.Work.NormalComplement.appI_five_c_prime
import Submission.Work.NormalComplement.appI_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-! ## Auxiliary Sylow facts for `IsSylowIn` (self-contained copies)

These are the ambient-`G` versions of standard Sylow facts for `IsSylowIn` (a `p`-subgroup of
index prime to `p`).  They are proved here because the module that originally exposed them
(`pcontrol_criterion`) is being reworked. -/

section Aux

variable {G : Type} [Group G] [Finite G]

/-- `|H.subgroupOf Y| = |H|` for `H ≤ Y`. -/
lemma aux_card_subgroupOf_eq (H Y : Subgroup G) (h : H ≤ Y) :
    Nat.card ↥(H.subgroupOf Y) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

variable {p : ℕ} [Fact p.Prime]

/-- A `p`-subgroup of `X` has order dividing the order of a `p`-Sylow of `X`. -/
lemma aux_card_dvd_card_of_isPGroup_of_isSylowIn {U P X : Subgroup G} (hUX : U ≤ X)
    (hU : IsPGroup p U) (hP : IsSylowIn p P X) : Nat.card U ∣ Nat.card P := by
  have h1 : Nat.card U ∣ Nat.card X := by
    rw [← aux_card_subgroupOf_eq U X hUX]
    exact Subgroup.card_subgroup_dvd_card (U.subgroupOf X)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
  have h2 : Nat.card X = (P.subgroupOf X).index * Nat.card P := by
    rw [← Subgroup.index_mul_card (P.subgroupOf X), aux_card_subgroupOf_eq P X hP.2.1]
  have h3 : p ^ k ∣ Nat.card P * (P.subgroupOf X).index := by
    rw [mul_comm (Nat.card P), ← h2, ← hk]
    exact h1
  have h4 : Nat.Coprime (p ^ k) (P.subgroupOf X).index :=
    Nat.Coprime.pow_left _ ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hP.2.2)
  rw [hk]
  exact h4.dvd_of_dvd_mul_right h3

/-- Every `p`-subgroup of `X` is contained in a `p`-Sylow of `X`. -/
lemma aux_exists_isSylowIn_ge {T X : Subgroup G} (hTX : T ≤ X) (hT : IsPGroup p T) :
    ∃ S : Subgroup G, T ≤ S ∧ IsSylowIn p S X := by
  have hT' : IsPGroup p (T.subgroupOf X) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
  obtain ⟨S', hS'⟩ := hT'.exists_le_sylow
  refine ⟨(S' : Subgroup ↥X).map X.subtype, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hTX hx⟩, hS' (by simpa [Subgroup.mem_subgroupOf] using hx),
      rfl⟩
  · exact S'.isPGroup'.map X.subtype
  · exact Subgroup.map_subtype_le (S' : Subgroup ↥X)
  · intro hdiv
    have hle : (S' : Subgroup ↥X) ≤ ((S' : Subgroup ↥X).map X.subtype).subgroupOf X := by
      intro x hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    exact (Sylow.not_dvd_index S') (dvd_trans hdiv (Subgroup.index_dvd_of_le hle))

/-- Two `p`-Sylows of the same subgroup have the same order. -/
lemma aux_card_eq_of_isSylowIn_of_isSylowIn {A B X : Subgroup G} (hA : IsSylowIn p A X)
    (hB : IsSylowIn p B X) : Nat.card A = Nat.card B :=
  le_antisymm (Nat.le_of_dvd (Nat.card_pos)
      (aux_card_dvd_card_of_isPGroup_of_isSylowIn hA.2.1 hA.1 hB))
    (Nat.le_of_dvd (Nat.card_pos)
      (aux_card_dvd_card_of_isPGroup_of_isSylowIn hB.2.1 hB.1 hA))

/-- Two `p`-Sylows of the same subgroup are conjugate. -/
lemma aux_exists_conj_eq_of_isSylowIn_of_isSylowIn {A B X : Subgroup G}
    (hA : IsSylowIn p A X) (hB : IsSylowIn p B X) :
    ∃ g ∈ X, A.map (MulAut.conj g).toMonoidHom = B := by
  have hA' : IsPGroup p (A.subgroupOf X) :=
    hA.1.comap_of_injective X.subtype (fun a b h => Subtype.ext h)
  have hB' : IsPGroup p (B.subgroupOf X) :=
    hB.1.comap_of_injective X.subtype (fun a b h => Subtype.ext h)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥X)
    (IsPGroup.toSylow hA' hA.2.2) (IsPGroup.toSylow hB' hB.2.2)
  have hsmul : MulAut.conj g • (A.subgroupOf X) = B.subgroupOf X := by
    have hcoe : (↑(g • IsPGroup.toSylow hA' hA.2.2) : Subgroup ↥X) =
        ↑(IsPGroup.toSylow hB' hB.2.2) := congrArg _ hg
    simpa [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using hcoe
  refine ⟨(g : G), g.2, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    have h1 : (⟨u, hA.2.1 hu⟩ : ↥X) ∈ A.subgroupOf X := by
      simpa [Subgroup.mem_subgroupOf] using hu
    have h2 : (MulAut.conj g) (⟨u, hA.2.1 hu⟩ : ↥X) ∈ B.subgroupOf X := by
      rw [← hsmul]
      exact ⟨_, h1, rfl⟩
    have h3 : ((MulAut.conj g) (⟨u, hA.2.1 hu⟩ : ↥X) : G) = (g : G) * u * (g : G)⁻¹ := by
      rw [MulAut.conj_apply]; simp
    rw [Subgroup.mem_subgroupOf] at h2
    rwa [h3] at h2
  · rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective,
      aux_card_eq_of_isSylowIn_of_isSylowIn hA hB]

/-- Cyclicity is preserved by conjugation. -/
lemma aux_isCyclic_map_conj_iff (A : Subgroup G) (g : G) :
    IsCyclic A ↔ IsCyclic (A.map (MulAut.conj g).toMonoidHom) :=
  MulEquiv.isCyclic (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective)

/-- Conjugating a `p`-Sylow gives a `p`-Sylow of the conjugate. -/
lemma aux_isSylowIn_map_conj {A X : Subgroup G} (hA : IsSylowIn p A X) (g : G) :
    IsSylowIn p (A.map (MulAut.conj g).toMonoidHom) (X.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨hA.1.map _, Subgroup.map_mono hA.2.1, ?_⟩
  have h : ((A.map (MulAut.conj g).toMonoidHom).subgroupOf
      (X.map (MulAut.conj g).toMonoidHom)).index = (A.subgroupOf X).index := by
    rw [← Subgroup.relIndex, ← Subgroup.relIndex]
    exact Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) A X
      (MulAut.conj g).injective
  rw [h]
  exact hA.2.2

end Aux

variable {G : Type} [Group G] [Finite G]

/-! ## Case 3: cyclicity and transport into `V = C_D(t)`

Peterfalvi I Ch. III §2, case 3: a `p`-subgroup of `D = H ⊓ H^t` which fixes at least three points
and acts fixed-point-freely on `K = J(D,t)` is cyclic.  The proof transports it into
`V = C_D(t) ∩ D` by Ch. II §4 Prop. 2(b) — which needs the `≥ 3` fixed points — keeping the
fixed-point-freeness by `KInvariantUnderD`, and then applies App. I (5)(c)
(`Work.NormalComplement.appI_five_c_prime`). -/

/-- App. I (5)(c) in the form needed here: a non-trivial `p`-subgroup of `V = C_D(t)` acting
fixed-point-freely on `K = J(D,t)` is cyclic.  (Public, for `section2_prop1_v3`.) -/
lemma cyclic_of_fpf_on_centD (hS : Situation G) {H : Subgroup G}
    (hH : IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    (hFT : FeitThompsonProp) {p : ℕ} (hp : p.Prime) {U : Subgroup G}
    (hUV : U ≤ centD H t) (hUp : IsPGroup p U) (hUne : U ≠ ⊥)
    (hfpf : ∀ x ∈ U, x ≠ 1 → ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1) :
    IsCyclic U := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hDodd : Odd (Nat.card ↥(twoPoint H t)) := hH.2.2 t htH
  have hK2 : 2 ≤ (Kset (twoPoint H t) t).ncard := by
    rw [ncard_Kset_eq_involutions hH ht htH]
    exact two_le_ncard_involutions hS hH
  have hcop : Nat.Coprime (Nat.card ↥(twoPoint H t)) 2 := Nat.coprime_two_right.mpr hDodd
  have hsolv : Group.IsSolvable ↥(twoPoint H t) := hFT ↥(twoPoint H t) hDodd
  have hKapp : Kapp t (twoPoint H t) = Kset (twoPoint H t) t :=
    ((appI_one (d := 2) Nat.prime_two ht (fun x hx => normalize_twoPoint ht hx) hcop).2 rfl).1
  have hUc : U ≤ Subgroup.centralizer ({t} : Set G) ⊓ twoPoint H t :=
    le_inf (hUV.trans inf_le_right) (hUV.trans inf_le_left)
  have hfpfK : ∀ x ∈ U, x ≠ 1 → ∀ k ∈ Kapp t (twoPoint H t), x * k * x⁻¹ = k → k = 1 := by
    intro x hx hx1 k hk
    rw [hKapp] at hk
    exact hfpf x hx hx1 k hk
  have hUodd : Odd (Nat.card ↥U) := by
    have hdvd : Nat.card ↥U ∣ Nat.card ↥(twoPoint H t) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hUV.trans inf_le_left)).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨c, hc⟩ := hdvd
    exact hDodd.of_dvd_nat ⟨c, hc⟩
  exact (appI_five_c_prime (d := 2) Nat.prime_two ht (fun x hx => normalize_twoPoint ht hx) hcop hsolv hp
    hUc hUp).2 hUne (hKapp ▸ hK2) hfpfK hUodd

/-- Peterfalvi I Ch. III §2 Prop. 1, case 3: a `p`-subgroup `U ≤ D = H ⊓ H^t` fixing at least three
points and acting fixed-point-freely on `K = J(D,t)` is cyclic. -/
theorem case3_cyclic_v2 (G : Type) [Group G] [Finite G]
    (hS : Situation G) (hBP : BenderPrelimProp) (hC4 : ChIIFourProp) (hFT : FeitThompsonProp)
    {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    (hKinv : KInvariantUnderD H t) {p : ℕ} (hp : p.Prime) {U : Subgroup G}
    (hUD : U ≤ twoPoint H t) (hUp : IsPGroup p U) (hUne : U ≠ ⊥)
    (h3 : 3 ≤ (fixedPts H U).ncard)
    (hfpf : ∀ x ∈ U, x ≠ 1 → ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1) :
    IsCyclic U := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hdD, hdU⟩ := prop2b_conj_into_centD G hS hBP hC4 hH ht htH hUD h3
  have hdDinv : d⁻¹ ∈ twoPoint H t := (twoPoint H t).inv_mem hdD
  have hfpf' : ∀ x ∈ U.map (MulAut.conj d).toMonoidHom, x ≠ 1 →
      ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1 := by
    intro x hx hx1 k hk hkx
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp hx
    have hu1 : u ≠ 1 := by
      intro h0
      rw [h0] at hux
      exact hx1 (by rw [← hux]; simp)
    have hdkinv : d⁻¹ * k * d ∈ Kset (twoPoint H t) t := by
      simpa using hKinv d⁻¹ hdDinv k hk
    have hfix : u * (d⁻¹ * k * d) * u⁻¹ = d⁻¹ * k * d := by
      have h1 : (MulAut.conj d).toMonoidHom u = d * u * d⁻¹ := MulAut.conj_apply d u
      rw [← hux, h1] at hkx
      have h3' : u * (d⁻¹ * k * d) * u⁻¹ =
          d⁻¹ * (d * u * d⁻¹ * k * (d * u * d⁻¹)⁻¹) * d := by group
      rw [h3', hkx]
    have hkd : d⁻¹ * k * d = 1 := hfpf u hu hu1 _ hdkinv hfix
    calc k = d * (d⁻¹ * k * d) * d⁻¹ := by group
      _ = 1 := by rw [hkd]; group
  have hne : U.map (MulAut.conj d).toMonoidHom ≠ ⊥ :=
    fun h => hUne ((Subgroup.map_eq_bot_iff_of_injective U (MulAut.conj d).injective).mp h)
  have hcyc : IsCyclic (U.map (MulAut.conj d).toMonoidHom) :=
    cyclic_of_fpf_on_centD hS hH ht htH hFT hp hdU (hUp.map _) hne hfpf'
  exact (aux_isCyclic_map_conj_iff U d).mpr hcyc

/-- Peterfalvi I Ch. III §2 Prop. 1, case 3: a `p`-Sylow `P₀` of `E = W ⊓ D` fixing at least three
points and acting fixed-point-freely on `K` admits a `p`-Sylow `P` of `E` with `P ≤ V = C_D(t)`
still acting fixed-point-freely on `K`. -/
theorem case3_sylow_le_centD_v2 (G : Type) [Group G] [Finite G]
    (hS : Situation G) (hBP : BenderPrelimProp) (hC4 : ChIIFourProp)
    {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    {W : Subgroup G} (hW : W ≤ H) (hn : H ≤ Subgroup.normalizer (W : Set G))
    (hKinv : KInvariantUnderD H t) {p : ℕ} (hp : p.Prime) {P₀ : Subgroup G}
    (hP₀ : IsSylowIn p P₀ (W ⊓ twoPoint H t))
    (h3 : 3 ≤ (fixedPts H P₀).ncard)
    (hfpf : ∀ x ∈ P₀, x ≠ 1 → ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1) :
    ∃ P : Subgroup G, IsSylowIn p P (W ⊓ twoPoint H t) ∧ P ≤ centD H t ∧
      (∀ x ∈ P, x ≠ 1 → ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hP₀D : P₀ ≤ twoPoint H t := hP₀.2.1.trans inf_le_right
  obtain ⟨d, hdD, hdP⟩ := prop2b_conj_into_centD G hS hBP hC4 hH ht htH hP₀D h3
  have hdH : d ∈ H := hdD.1
  have hdDinv : d⁻¹ ∈ twoPoint H t := (twoPoint H t).inv_mem hdD
  have hdW : d ∈ Subgroup.normalizer (W : Set G) := hn hdH
  have hEd : (W ⊓ twoPoint H t).map (MulAut.conj d).toMonoidHom = W ⊓ twoPoint H t := by
    rw [Subgroup.map_inf _ _ (MulAut.conj d).toMonoidHom (MulAut.conj d).injective]
    have h1 : W.map (MulAut.conj d).toMonoidHom = W :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hdW
    have h2 : (twoPoint H t).map (MulAut.conj d).toMonoidHom = twoPoint H t :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hdD)
    rw [h1, h2]
  have hfpf' : ∀ x ∈ P₀.map (MulAut.conj d).toMonoidHom, x ≠ 1 →
      ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1 := by
    intro x hx hx1 k hk hkx
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp hx
    have hu1 : u ≠ 1 := by
      intro h0
      rw [h0] at hux
      exact hx1 (by rw [← hux]; simp)
    have hdkinv : d⁻¹ * k * d ∈ Kset (twoPoint H t) t := by
      simpa using hKinv d⁻¹ hdDinv k hk
    have hfix : u * (d⁻¹ * k * d) * u⁻¹ = d⁻¹ * k * d := by
      have h1 : (MulAut.conj d).toMonoidHom u = d * u * d⁻¹ := MulAut.conj_apply d u
      rw [← hux, h1] at hkx
      have h3' : u * (d⁻¹ * k * d) * u⁻¹ =
          d⁻¹ * (d * u * d⁻¹ * k * (d * u * d⁻¹)⁻¹) * d := by group
      rw [h3', hkx]
    have hkd : d⁻¹ * k * d = 1 := hfpf u hu hu1 _ hdkinv hfix
    calc k = d * (d⁻¹ * k * d) * d⁻¹ := by group
      _ = 1 := by rw [hkd]; group
  refine ⟨P₀.map (MulAut.conj d).toMonoidHom, ?_, hdP, hfpf'⟩
  have := aux_isSylowIn_map_conj hP₀ d
  rwa [hEd] at this

/-- **Peterfalvi I Ch. III §2 Proposition 1** (p.175), in the form the area needs: with
`H` strongly embedded, `t ∉ H` an involution, `D = H ∩ H^t`, `W ⊴ H` with `H = W·D` and
`E = W ∩ D`, and `p ∣ |E|`: either `E` is `p`-control in `W`, or `E` has a `p`-Sylow `P ⊆ V`
acting fixed-point-freely on `K = J(D,t)` and cyclic.

`Section2Prop` carries `KInvariantUnderD H t` as an explicit hypothesis (its proof needs it in
case 3, to transport fixed-point-freeness to a `D`-conjugate inside `V`); the proof uses Ch. II §4
Prop. 3 with a *subnormal* `Y` (`ChIIFourP3SubnormalProp`, which supersedes `P3NormalProp`),
`BenderPrelimProp` and `ChIIFourProp`.

Route (pp. 175–176).  Let `E := W ⊓ D`, `V := centD H t`, `K := Kset D t`, and let `U` be a
`p`-subgroup of `E` (so `U ≤ D ≤ H ⊓ conj t H`, whence both points `1` and `t` of `G ⧸ H` are
fixed by `U`):
* **Case 1 (`(fixedPts H U).ncard = 2`).**  Then `fixedPts H U = {1, t}`; `N_W(U)` permutes it and
  fixes `1`, hence fixes `t`, so `N_W(U) ≤ H ⊓ conj t H = D` and `N_W(U) ⊆ W`, i.e.
  `N_W(U) = N_E(U)` (`Work.NormalComplement.case1_normalizer_le`, sorry-free).
* **Case 2 (`3 ≤ (fixedPts H U).ncard` and some `1 ≠ U₁ ≤ U` with a nontrivial `k ∈ K`
  centralising it).**  `ChIIFourProp` P1(b) plus P2(a) and `hBP` give Ch. II §4 Prop. 2(b): `U` is
  `D`-conjugate into `V`; `hP3` applied to that conjugate with the subnormal `U₁` gives
  `N_H(U) = S ⋊ N_D(U)` with `S` the 2-Sylow of `F ∩ H`, `F = O^{2'}(C_G(U))`; `|H:W|` is odd hence
  `S ≤ W`, so `N_W(U) = S ⋊ N_E(U)` (`Work.NormalComplement.case2_normalizer_le`,
  `Work.NormalComplement.case2_prop3b`).
* **Case 3 (`3 ≤ (fixedPts H U).ncard` and `U` acts fixed-point-freely on `K`).**  `U` is cyclic by
  App. I (5)(c) (`Work.NormalComplement.case3_isCyclic`); to conclude the second alternative of
  `Section2Prop` one conjugates a `p`-Sylow of `E` into `V` (Ch. II §4 Prop. 2(b)) and uses
  `KInvariantUnderD` to keep fixed-point-freeness (`Work.NormalComplement.case3_sylow_le_centD`).

Take `P` a `p`-Sylow of `E`.  If `P` falls in case 3, we are in the second alternative of
`Section2Prop`.  Otherwise `P` and every non-cyclic `U ≤ P` fall in cases 1 or 2 (a non-cyclic `U`
cannot fall in case 3, since case 3 forces cyclicity), which verify the two normaliser hypotheses of
`Work.NormalComplement.pcontrol_criterion_prod`, so `E` is `p`-control in `W` — the first
alternative. -/
theorem section2_prop1_v2 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hBP : Work.NormalComplement.BenderPrelimProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp) :
    Work.NormalComplement.Section2Prop := by
  intro G instG finG hSit H hH t ht htH W hWH hHn hsup hKinv p hp hpE
  haveI : Fact p.Prime := ⟨hp⟩
  -- Any subgroup of `D = H ⊓ H^t` fixes the two distinct points `1` and `t` of `G ⧸ H`.
  have two_le : ∀ {U : Subgroup G}, U ≤ twoPoint H t → 2 ≤ (fixedPts H U).ncard := by
    intro U hU
    have h1mem : ((1 : G) : G ⧸ H) ∈ fixedPts H U := by
      rw [fixedPts]; intro u hu
      change ((u * 1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
      rw [QuotientGroup.eq]
      simpa using H.inv_mem (hU hu).1
    have htmem : ((t : G) : G ⧸ H) ∈ fixedPts H U := by
      rw [fixedPts]; intro u hu
      change ((u * t : G) : G ⧸ H) = ((t : G) : G ⧸ H)
      rw [QuotientGroup.eq]
      have hu2 : t⁻¹ * u * t ∈ H := by
        obtain ⟨h, hh, hhu⟩ := Subgroup.mem_map.mp (hU hu).2
        have hkey : t⁻¹ * u * t = h := by
          rw [← hhu]
          change t⁻¹ * (t * h * t⁻¹) * t = h
          group
        rw [hkey]; exact hh
      have hkey2 : (u * t)⁻¹ * t = (t⁻¹ * u * t)⁻¹ := by group
      rw [hkey2]; exact H.inv_mem hu2
    have hne : ((1 : G) : G ⧸ H) ≠ ((t : G) : G ⧸ H) := by
      intro hcon
      rw [QuotientGroup.eq] at hcon
      exact htH (by simpa using hcon)
    have hsub : (insert ((1 : G) : G ⧸ H) {((t : G) : G ⧸ H)} : Set (G ⧸ H)) ⊆ fixedPts H U := by
      intro ω hω
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hω
      rcases hω with rfl | rfl
      · exact h1mem
      · exact htmem
    have hcard : (insert ((1 : G) : G ⧸ H) {((t : G) : G ⧸ H)} : Set (G ⧸ H)).ncard = 2 := by
      rw [Set.ncard_insert_of_notMem (by simpa using hne), Set.ncard_singleton]
    have := Set.ncard_le_ncard hsub
    omega
  -- a Sylow `p`-subgroup `P₀` of `E = W ⊓ D`
  obtain ⟨P₀, -, hP₀syl⟩ :=
    aux_exists_isSylowIn_ge (p := p) (T := ⊥) (X := W ⊓ twoPoint H t) bot_le
      (IsPGroup.of_bot (p := p))
  have hP₀E : P₀ ≤ W ⊓ twoPoint H t := hP₀syl.2.1
  have hP₀p : IsPGroup p P₀ := hP₀syl.1
  have eq_of_le1 : ∀ {U : Subgroup G}, U ≤ W ⊓ twoPoint H t → (fixedPts H U).ncard = 2 →
      Subgroup.normalizer (U : Set G) ⊓ W =
        pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
          (Subgroup.normalizer (U : Set G) ⊓ (W ⊓ twoPoint H t)) := by
    intro U hUE h2
    have hle := case1_normalizer_le G hH ht htH hWH hUE h2
    have hNE : Subgroup.normalizer (U : Set G) ⊓ (W ⊓ twoPoint H t) =
        Subgroup.normalizer (U : Set G) ⊓ W :=
      le_antisymm (inf_le_inf_left _ inf_le_left) (le_inf inf_le_left hle)
    rw [hNE]
    exact (sup_eq_right.mpr ((Subgroup.map_subtype_le _).trans
      (inf_le_inf (Subgroup.centralizer_le_normalizer (s := (U : Set G))) (le_refl W)))).symm
  have eq_of_case2 : ∀ {U : Subgroup G}, U ≤ W ⊓ twoPoint H t → IsPGroup p U →
      3 ≤ (fixedPts H U).ncard →
      (∃ U₁ : Subgroup G, U₁ ≤ U ∧ U₁ ≠ ⊥ ∧
        ∃ k ∈ Kset (twoPoint H t) t, k ≠ 1 ∧ ∀ u ∈ U₁, k * u = u * k) →
      Subgroup.normalizer (U : Set G) ⊓ W =
        pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
          (Subgroup.normalizer (U : Set G) ⊓ (W ⊓ twoPoint H t)) := by
    intro U hUE hUp h3 hcase2
    have hle := case2_normalizer_le_v2 G hSit hBP hC4 hP3 hH ht htH hWH hHn hsup hKinv hp
      hUE hUp h3 hcase2
    refine le_antisymm hle (sup_le ?_ ?_)
    · exact (Subgroup.map_subtype_le _).trans
        (inf_le_inf (Subgroup.centralizer_le_normalizer (s := (U : Set G))) (le_refl W))
    · exact inf_le_inf_left _ inf_le_left
  have key : ∀ {U : Subgroup G}, U ≤ W ⊓ twoPoint H t →
      ¬ (∀ x ∈ U, x ≠ 1 → ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1) →
      ∃ U₁ : Subgroup G, U₁ ≤ U ∧ U₁ ≠ ⊥ ∧
        ∃ k ∈ Kset (twoPoint H t) t, k ≠ 1 ∧ ∀ u ∈ U₁, k * u = u * k := by
    intro U hUE hnf
    push_neg at hnf
    obtain ⟨x, hxU, hx1, k, hkK, hkx, hk1⟩ := hnf
    refine ⟨Subgroup.zpowers x, Subgroup.zpowers_le.mpr hxU, ?_, k, hkK, hk1, ?_⟩
    · rw [Subgroup.zpowers_ne_bot]; exact hx1
    · have hxk : x * k = k * x := by
        have h := congrArg (fun y => y * x) hkx
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
      intro u hu
      have hmem : u ∈ Subgroup.centralizer ({k} : Set G) :=
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxk)) hu
      exact (Subgroup.mem_centralizer_singleton_iff.mp hmem).symm
  -- `P₀` is nontrivial (it is a Sylow of `E` and `p ∣ |E|`)
  have hP₀ne : P₀ ≠ ⊥ := by
    have hpP₀ : p ∣ Nat.card ↥P₀ := by
      have hE : Nat.card ↥(W ⊓ twoPoint H t) =
          (P₀.subgroupOf (W ⊓ twoPoint H t)).index * Nat.card ↥P₀ := by
        rw [← Subgroup.index_mul_card (P₀.subgroupOf (W ⊓ twoPoint H t)),
          aux_card_subgroupOf_eq P₀ (W ⊓ twoPoint H t) hP₀E]
      rw [hE] at hpE
      exact (hp.dvd_mul.mp hpE).resolve_left hP₀syl.2.2
    intro hbot
    rw [hbot] at hpP₀
    have h1 : Nat.card ↥(⊥ : Subgroup G) = 1 := by simp
    rw [h1] at hpP₀
    exact hp.ne_one (Nat.dvd_one.mp hpP₀)
  by_cases hcase3 : 3 ≤ (fixedPts H P₀).ncard ∧
      (∀ x ∈ P₀, x ≠ 1 → ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1)
  · -- The Sylow falls in case 3: the second alternative of `Section2Prop`.
    obtain ⟨h3, hfpf⟩ := hcase3
    obtain ⟨P, hPsyl, hPV, hPfpf⟩ :=
      case3_sylow_le_centD_v2 G hSit hBP hC4 hH ht htH hWH hHn hKinv hp hP₀syl h3 hfpf
    have hcyc₀ : IsCyclic P₀ :=
      case3_cyclic_v2 G hSit hBP hC4 hFT hH ht htH hKinv hp
        (hP₀E.trans inf_le_right) hP₀p hP₀ne h3 hfpf
    obtain ⟨g, -, hgP⟩ := aux_exists_conj_eq_of_isSylowIn_of_isSylowIn (p := p) hP₀syl hPsyl
    have hcyc : IsCyclic P := by
      rw [← hgP]
      exact (aux_isCyclic_map_conj_iff P₀ g).mp hcyc₀
    exact Or.inr ⟨P, hPsyl, hPV, hPfpf, hcyc⟩
  · -- Otherwise the two normaliser hypotheses of the `p`-control criterion hold.
    left
    refine pcontrol_prod_v2 (p := p) (E := W ⊓ twoPoint H t) (W := W)
      inf_le_left hpE hP₀syl ?_ ?_
    · rcases eq_or_lt_of_le (two_le (hP₀E.trans inf_le_right)) with h2eq | h2lt
      · exact eq_of_le1 hP₀E h2eq.symm
      · have hnf : ¬ (∀ x ∈ P₀, x ≠ 1 →
            ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1) :=
          fun hf => hcase3 ⟨by omega, hf⟩
        exact eq_of_case2 hP₀E hP₀p (by omega) (key hP₀E hnf)
    · intro U hUP hUnotcyc
      have hUE : U ≤ W ⊓ twoPoint H t := le_trans hUP hP₀E
      have hUp : IsPGroup p U := hP₀p.to_le hUP
      have hUne : U ≠ ⊥ := fun h => hUnotcyc (by rw [h]; infer_instance)
      rcases eq_or_lt_of_le (two_le (hUE.trans inf_le_right)) with h2eq | h2lt
      · exact eq_of_le1 hUE h2eq.symm
      · have hnf : ¬ (∀ x ∈ U, x ≠ 1 →
            ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1) :=
          fun hf => hUnotcyc
            (case3_cyclic_v2 G hSit hBP hC4 hFT hH ht htH hKinv hp
              (hUE.trans inf_le_right) hUp hUne (by omega) hf)
        exact eq_of_case2 hUE hUp (by omega) (key hUE hnf)

end Work.NormalComplement
