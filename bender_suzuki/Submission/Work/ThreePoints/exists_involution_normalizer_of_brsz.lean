import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.ch1_lem2
import Submission.Work.ThreePoints.sec3_lemma2
import Submission.Work.ThreePoints.odd_card_of_fixes_three
import Submission.Work.ThreePoints.prop1a_even_card_centralizer
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.ThreePoints.exists_prime_index_normal
import Submission.Work.ThreePoints.exists_descent_odd_solvable
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_nofour
import Submission.Work.ThreePoints.prop1b_assembly
import Submission.Work.DoubleTransitivity.Sec4.prop2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

open scoped Pointwise

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

variable {G : Type} [Group G] [Finite G]

/-! ## Auxiliary facts for the induction of Ch. II §4 Prop. 1 (a) -/

/-- Every element lies in the normaliser of the trivial subgroup. -/
theorem mem_normalizer_bot (u : G) : u ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp

/-- **Ch. II §4 Prop. 1 (b)**, in the form used in the induction: the evenness hypothesis is only
needed at the fixed points `conj g' H ⊇ Y` of `Y`, not for arbitrary subgroups `X'`.  This is
`Work.ThreePoints.stronglyEmbedded_subgroupOf_inf_conj_of_even_card` with the hypothesis `hEV`
weakened. -/
theorem isStronglyEmbedded_inf_conj_of_even_for_fixed {H Y F₀ : Subgroup G} {g : G}
    (hH : IsStronglyEmbedded H) (hY3 : 3 ≤ (fixedPts H Y).ncard)
    (hFY : involutions (Subgroup.centralizer (Y : Set G) : Set G) ⊆ F₀)
    (hg : Y ≤ conj g H)
    (hEV : ∀ g' : G, Y ≤ conj g' H →
      Even (Nat.card (conj g' H ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G))) :
    IsStronglyEmbedded ((F₀ ⊓ conj g H).subgroupOf F₀) := by
  have hM : IsStronglyEmbedded (conj g H) := conj_stronglyEmbedded hH g
  have hev : Even (Nat.card (F₀ ⊓ conj g H : Subgroup G)) :=
    even_card_inf_of_even_card_inf_centralizer (hEV g hg) hFY
  have hproper : (F₀ ⊓ conj g H).subgroupOf F₀ ≠ ⊤ := by
    obtain ⟨g', hfix, hne_pt⟩ := exists_mk_fixedPts_ne (H := H) (X := Y) (g := g) hY3
    have hYg' : Y ≤ conj g' H := by
      rw [← stabilizer_mk H g']
      exact mem_fixedPts_iff_le_stabilizer.mp hfix
    have hconjne : conj g H ≠ conj g' H := by
      intro heq
      exact hne_pt (mk_eq_of_conj_eq hH heq.symm)
    obtain ⟨u, hu, hu2⟩ := exists_mem_orderOf_eq_two_of_even_card (hEV g' hYg')
    have huF : u ∈ F₀ := hFY ⟨hu.2, hu2⟩
    have huNotM : u ∉ conj g H := by
      intro huM
      have huinf : u ∈ conj g H ⊓ conj g' H := ⟨huM, hu.1⟩
      have hdvd : Nat.card (Subgroup.zpowers u : Subgroup G) ∣
          Nat.card (conj g H ⊓ conj g' H : Subgroup G) :=
        Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr huinf)
      rw [Nat.card_zpowers, hu2] at hdvd
      exact Nat.not_even_iff_odd.mpr (card_inf_conj_odd hH hconjne)
        (even_iff_two_dvd.mpr hdvd)
    intro htop
    have hmem : u ∈ F₀ ⊓ conj g H := by
      refine ⟨huF, ?_⟩
      have h' : (⟨u, huF⟩ : F₀) ∈ (F₀ ⊓ conj g H).subgroupOf F₀ := by rw [htop]; trivial
      exact (Subgroup.mem_subgroupOf.mp h').2
    exact huNotM hmem.2
  exact IsStronglyEmbedded.subgroupOf_inf hM hproper hev

/-- An element of `K` normalising the subgroup `Q.subgroupOf K` of `K` normalises `Q`. -/
theorem mem_normalizer_of_mem_normalizer_subgroupOf {K Q : Subgroup G} (hQK : Q ≤ K)
    {v : G} (hv : v ∈ K)
    (hv' : (⟨v, hv⟩ : ↥K) ∈ Subgroup.normalizer (Q.subgroupOf K : Set ↥K)) :
    v ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hv' ⊢
  have hv'' : (Q.subgroupOf K).map (MulAut.conj (⟨v, hv⟩ : ↥K)).toMonoidHom
      = Q.subgroupOf K := hv'
  calc Q.map (MulAut.conj v).toMonoidHom
      = (Q.subgroupOf K).map ((MulAut.conj v).toMonoidHom.comp K.subtype) := by
          conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hQK]
          exact Subgroup.map_map _ _ _
    _ = (Q.subgroupOf K).map
          (K.subtype.comp (MulAut.conj (⟨v, hv⟩ : ↥K)).toMonoidHom) := by
          congr 1
    _ = ((Q.subgroupOf K).map (MulAut.conj (⟨v, hv⟩ : ↥K)).toMonoidHom).map K.subtype :=
          (Subgroup.map_map _ _ _).symm
    _ = (Q.subgroupOf K).map K.subtype := by rw [hv'']
    _ = Q := Subgroup.map_subgroupOf_eq_of_le hQK

/-- Conjugating a subgroup by an element of `F` and intersecting with `F`: this is conjugation
inside `↥F`. -/
theorem subgroupOf_conj_of_mem {F A : Subgroup G} {t : G} (ht : t ∈ F) :
    (conj t A).subgroupOf F
      = ((A ⊓ F).subgroupOf F).map (MulAut.conj (⟨t, ht⟩ : ↥F)).toMonoidHom := by
  ext x
  constructor
  · intro hx
    -- `x` is conjugated by `t` into `A`; the conjugating element lies in `F`
    have hxA : (x : G) ∈ conj t A := hx
    rw [mem_conj_iff] at hxA
    have hmem : t⁻¹ * (x : G) * t ∈ A ⊓ F :=
      ⟨hxA, F.mul_mem (F.mul_mem (F.inv_mem ht) x.2) ht⟩
    refine Subgroup.mem_map.mpr ⟨⟨t⁻¹ * (x : G) * t, hmem.2⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hmem
    · apply Subtype.ext
      show t * (t⁻¹ * (x : G) * t) * t⁻¹ = (x : G)
      group
  · rintro ⟨y, hy, rfl⟩
    have hyA : (y : G) ∈ A := (Subgroup.mem_subgroupOf.mp hy).1
    show t * (y : G) * t⁻¹ ∈ conj t A
    rw [mem_conj_iff]
    have h : t⁻¹ * (t * (y : G) * t⁻¹) * t = (y : G) := by group
    rw [h]
    exact hyA

/-- **The `Ξ` bookkeeping of Ch. II §4 Prop. 1 (a)**: two distinct conjugates of `H` containing `Y`
have distinct intersections with `F`. -/
theorem eq_conj_of_inf_conj_subgroupOf_eq {H Y F : Subgroup G} {g₀ g₁ : G}
    (hH : IsStronglyEmbedded H) (hY0 : Y ≤ conj g₀ H) (hY1 : Y ≤ conj g₁ H)
    (hF0 : involutions (Subgroup.centralizer (Y : Set G) : Set G) ⊆ F)
    (hEV : ∀ g : G, Y ≤ conj g H →
      Even (Nat.card (conj g H ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G)))
    (heq : (F ⊓ conj g₀ H).subgroupOf F = (F ⊓ conj g₁ H).subgroupOf F) :
    conj g₀ H = conj g₁ H := by
  by_contra hne
  have heven0 : Even (Nat.card (F ⊓ conj g₀ H : Subgroup G)) :=
    even_card_inf_of_even_card_inf_centralizer (hEV g₀ hY0) hF0
  have hle : (F ⊓ conj g₀ H : Subgroup G) ≤ (conj g₀ H ⊓ conj g₁ H : Subgroup G) := by
    intro x hx
    refine ⟨hx.2, ?_⟩
    have hx' : (⟨x, hx.1⟩ : ↥F) ∈ (F ⊓ conj g₀ H).subgroupOf F :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [heq] at hx'
    exact (Subgroup.mem_subgroupOf.mp hx').2
  exact Nat.not_even_iff_odd.mpr (card_inf_conj_odd hH hne)
    (even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp heven0)
      (Subgroup.card_dvd_of_le hle)))

/-- **The `Ξ` bookkeeping of Ch. II §4 Prop. 1 (a)**: for two distinct conjugates `conj g₀ H`,
`conj g₁ H` of `H` containing `Y`, the intersections with `F` are conjugate inside `↥F`. -/
theorem exists_conj_inf_conj_subgroupOf_eq {H Y F : Subgroup G} {g₀ g₁ : G}
    (hH : IsStronglyEmbedded H) (hY0 : Y ≤ conj g₀ H) (hY1 : Y ≤ conj g₁ H)
    (hF0 : involutions (Subgroup.centralizer (Y : Set G) : Set G) ⊆ F)
    (hEV : ∀ g : G, Y ≤ conj g H →
      Even (Nat.card (conj g H ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G)))
    (hne : conj g₀ H ≠ conj g₁ H) :
    ∃ f : ↥F, (F ⊓ conj g₁ H).subgroupOf F
      = ((F ⊓ conj g₀ H).subgroupOf F).map (MulAut.conj f).toMonoidHom := by
  have heven0 : Even (Nat.card (F ⊓ conj g₀ H : Subgroup G)) :=
    even_card_inf_of_even_card_inf_centralizer (hEV g₀ hY0) hF0
  have heven1 : Even (Nat.card (F ⊓ conj g₁ H : Subgroup G)) :=
    even_card_inf_of_even_card_inf_centralizer (hEV g₁ hY1) hF0
  obtain ⟨t, ht, htconj⟩ := exists_involution_conj_of_even_card_inf hH hne heven0 heven1
  refine ⟨⟨t, ht.1⟩, ?_⟩
  have hFt : conj t F = F := conj_eq_self_of_mem ht.1
  have hkey : F ⊓ conj g₁ H = conj t (F ⊓ conj g₀ H) := by
    rw [← htconj, conj_inf, hFt]
  rw [hkey]
  simpa [inf_comm, inf_left_comm, inf_assoc] using subgroupOf_conj_of_mem (F := F) (A := F ⊓ conj g₀ H) ht.1

/-- Elements of `N_G(Y)` normalise `C_G(Y)`; consequently `C_G(Y) ⊴ F` for every `F ≤ N_G(Y)`.
Not in Mathlib. -/
theorem normalizer_le_normalizer_centralizer {Y : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (Y : Set G) : Set G) := by
  have hginv : g⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normalizer (Y : Set G)).inv_mem hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    have hcomm : ∀ h ∈ Y, h * c = c * h := fun h hh =>
      (Subgroup.mem_centralizer_iff.mp hc) h hh
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : g⁻¹ * y * g ∈ Y := by
      simpa using (Subgroup.mem_normalizer_iff.mp hginv y).mp hy
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm _ hy']
      _ = (g * c * g⁻¹) * y := by group
  · intro hc
    have hcomm : ∀ h ∈ Y, h * (g * c * g⁻¹) = (g * c * g⁻¹) * h := fun h hh =>
      (Subgroup.mem_centralizer_iff.mp hc) h hh
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : g * y * g⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hg y).mp hy
    calc y * c = g⁻¹ * ((g * y * g⁻¹) * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * (g * y * g⁻¹)) * g := by rw [hcomm _ hy']
      _ = c * y := by group

/-- An element of `F` normalising a subgroup `Q₀ ≤ ↥F` normalises `Q₀.map F.subtype ≤ G`. -/
theorem mem_normalizer_map_subtype_of_mem_normalizer {F : Subgroup G} {Q₀ : Subgroup ↥F} {y : G}
    (hy : y ∈ F) (hy' : (⟨y, hy⟩ : ↥F) ∈ Subgroup.normalizer (Q₀ : Set ↥F)) :
    y ∈ Subgroup.normalizer (Q₀.map F.subtype : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hy' ⊢
  intro z
  constructor
  · intro hz
    obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.mp hz
    refine Subgroup.mem_map.mpr ⟨(⟨y, hy⟩ : ↥F) * q * (⟨y, hy⟩ : ↥F)⁻¹, (hy' q).mp hq, ?_⟩
    show y * (q : G) * y⁻¹ = y * z * y⁻¹
    rw [show (q : G) = z from hqy]
  · intro hz
    obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.mp hz
    refine Subgroup.mem_map.mpr ⟨(⟨y, hy⟩ : ↥F)⁻¹ * q * (⟨y, hy⟩ : ↥F), ?_, ?_⟩
    · have h := ((Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (Q₀ : Set ↥F)).inv_mem hy')) q).mp hq
      simpa using h
    · show y⁻¹ * (q : G) * y = z
      rw [show (q : G) = y * z * y⁻¹ from hqy]
      group

/-- **Ch. I §4 Prop. 2 with the Brauer–Suzuki black box**, in the form used here: for a strongly
embedded subgroup `K` of a finite group `F` and a `p`-subgroup `Q ≤ K` (`p ≠ 2` a prime) which is
maximal among the `p`-subgroups of `K` with at least three fixed points of `F ⧸ K`, the normaliser
`N_K(Q)` has even order.

No hypothesis on the 2-rank of `F` is needed: this is the second conclusion of
`Work.DoubleTransitivity.Sec4.prop2` (`hBrSz`-conditional Ch. I §4 Prop. 2, pp. 156–157, proved
there through Ch. I §4 Lemma 2 and Prop. 1), together with the identification
`N_K(Q) ≅ N_F(Q) ⊓ K` of `Work.ThreePoints.card_normalizer_subgroupOf_eq_card_inf`. -/
theorem prop2_of_brsz {F : Type} [Group F] [Finite F]
    (hBrSz : BrauerSuzukiProp) (hA : ThmAProp) {K : Subgroup F}
    (hK : IsStronglyEmbedded K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup F}
    (hQK : Q ≤ K) (hQp : IsPGroup p Q) (hQ3 : 3 ≤ (fixedPts K Q).ncard)
    (hQmax : ∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
      3 ≤ (fixedPts K R).ncard → R = Q) :
    Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)) := by
  have hmax : Work.DoubleTransitivity.MaxFixesThreeIn p K Q :=
    ⟨hQp, hQK, hQ3, fun R hRp hRK hR3 hQR => le_of_eq (hQmax R hQR hRK hRp hR3)⟩
  have h : Even (Nat.card ↥(Subgroup.normalizer (Q : Set F) ⊓ K)) :=
    (Work.DoubleTransitivity.Sec4.prop2 hBrSz hK hp hp2 hmax).2
  rw [card_normalizer_subgroupOf_eq_card_inf hQK, inf_comm]
  exact h

/-- **Peterfalvi I Ch. II §4 Prop. 1 (a), the heart, with Brauer–Suzuki as a hypothesis**: under (B0)–(B2) (`hS : Situation G`), for a strongly embedded `H ≤ G` and a subgroup `X ≤ M = H^g` fixing at least three points of `Ω = G ⧸ H`, there is an involution `u ∈ M` normalising `X`.  With `hC` this yields Prop. 1(a) (`Work.ThreePoints.prop1a_of_involution_normalizing`), and `hBrSz : BrauerSuzukiProp` is exactly the black box its source proof consumes (Ch. I §3 Prop. 1, Case 2, p. 154: "`M/O_{2'}(M)` has a unique involution" for `M = N_G(P)` of 2-rank 1).  So this is the `hBrSz`-conditional form of the open crux `Work.ThreePoints.exists_involution_mem_normalizer_of_fixes_three` (in `even_card_centralizer_of_fixes_three.lean`), and the only hypothesis that separates it from an unconditional proof of Ch. II §4 Prop. 1(a).

Source proof (Ch. II §4 Prop. 1 (a), pp. 168–169): induction on `|X|`.  `X = 1`: any involution of `M` works (`|M|` is even because `M = H^g` is strongly embedded).  Otherwise `|X|` is odd (`Work.ThreePoints.odd_card_of_fixes_three`), hence solvable by `hFT`; choose a prime `p` and `Y := O^p(X) ⊊ X` (take a maximal normal subgroup `N ⊊ X`; its index is a prime `p` and `O^p(X) ≤ N`), let `P` be a `p`-Sylow of `X` (so `X = Y·P`, `p` odd) and put `F₁ := C_G(Y)·P ≤ N_G(Y)` (as `Y ⊴ X`).  The induction hypothesis for `Y` (with `|Ω_Y| ≥ |Ω_X| ≥ 3`) together with `Work.ThreePoints.prop1a_of_involution_normalizing` supplies the evenness hypothesis of `Work.ThreePoints.stronglyEmbedded_subgroupOf_inf_conj_of_even_card` for `F := F₁` and `X := Y` (note `Inv C_G(Y) ⊆ C_G(Y) ⊆ F₁`), so `F₁ ⊓ M'` is strongly embedded in `F₁` for every `M' ∈ Ω_Y`; `Work.ThreePoints.ch1_lem2` (and the evenness just obtained) shows `M' ↦ F₁ ⊓ M'` is injective, giving a bijection from `Ω_Y` onto a class `Ξ` of proper Bender subgroups of `F₁`.  Let `Q` be a maximal `p`-subgroup of `F₁ ⊓ M` with at least three fixed points of `Ξ`, containing `P`.  Then `K := F₁ ⊓ M` is strongly embedded in `F₁`, `Q ≤ K` is maximal among the `p`-subgroups of `K` with `≥ 3` fixed points, and `Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup` (Ch. I §4 Prop. 2, consumed with `hBrSz`) yields an involution `u ∈ N_{F₁}(Q) ⊓ K ⊆ F₁ ⊓ M`.  Theorem C (`hC`, `hS`, with the two points `M ∈ Ω_Q` and a second point `M₂ = M^g ∈ Ω_Q`, `g ∉ M`) makes `u` centralise `Q ⊇ P`; since `u ∈ F₁` and `|F₁ : C_G(Y)|` is a power of `p` (odd), `u ∈ C_G(Y)`, so `u ∈ C_M(Y) ∩ C_M(P) = C_M(X)`, and a fortiori `u` normalises `X`. -/
theorem exists_involution_normalizer_of_brsz {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X M : Subgroup G}
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (hM : ∃ g : G, M = Submission.Blueprint.conj g H) (hXM : X ≤ M) :
    ∃ u : G, u ∈ M ∧ u ∈ Subgroup.normalizer (X : Set G) ∧ orderOf u = 2 := by
  classical
  suffices key : ∀ n : ℕ, ∀ X M : Subgroup G, Nat.card X = n →
      3 ≤ (fixedPts H X).ncard → (∃ g : G, M = conj g H) → X ≤ M →
      ∃ u : G, u ∈ M ∧ u ∈ Subgroup.normalizer (X : Set G) ∧ orderOf u = 2 from
    key (Nat.card X) X M rfl hX3 hM hXM
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X M hcard hX3 hM hXM
    by_cases hXbot : X = ⊥
    · -- `X = ⊥`: any involution of `M` works
      obtain ⟨g, hg⟩ := hM
      have hstrong : IsStronglyEmbedded M := hg ▸ conj_stronglyEmbedded hH g
      obtain ⟨u, huM, hu2⟩ :=
        exists_mem_orderOf_eq_two_of_even_card (IsStronglyEmbedded.even_card hstrong)
      exact ⟨u, huM, by rw [hXbot]; exact mem_normalizer_bot u, hu2⟩
    · -- the induction step
      have hodd : Odd (Nat.card X) := odd_card_of_fixes_three hH hX3
      have hsol : Group.IsSolvable ↥X := hFT ↥X hodd
      -- descent data: `p`, `Y ⊴ X` with `Y ≠ X`, and `P ≤ X` a `p`-subgroup with `Y ⊔ P = X`
      obtain ⟨p, Y, P, hpprime, hp2, hYX, hYN, hYne, hPp, hPX, hsup⟩ :=
        exists_descent_odd_solvable hXbot hodd hsol
      have hY3 : 3 ≤ (fixedPts H Y).ncard :=
        le_trans hX3 (Set.ncard_le_ncard (fixedPts_mono hYX))
      have hYM : Y ≤ M := le_trans hYX hXM
      have hlt : Nat.card Y < n := by
        rw [← hcard]
        rw [show Nat.card Y = (Y : Set G).ncard from Nat.card_coe_set_eq (Y : Set G),
            show Nat.card X = (X : Set G).ncard from Nat.card_coe_set_eq (X : Set G)]
        exact Set.ncard_lt_ncard ⟨fun y hy => hYX hy,
          fun hcontra => hYne (le_antisymm hYX hcontra)⟩
      -- the induction hypothesis for `Y`
      have ihY : ∀ g' : G, Y ≤ conj g' H → ∃ u : G, u ∈ conj g' H ∧
          u ∈ Subgroup.normalizer (Y : Set G) ∧ orderOf u = 2 :=
        fun g' hg' => ih (Nat.card Y) hlt Y (conj g' H) rfl hY3 ⟨g', rfl⟩ hg'
      -- evenness of `|C_{M'}(Y)|` (Prop. 1 (a) for `Y`, via Theorem C)
      have hEV : ∀ g' : G, Y ≤ conj g' H →
          Even (Nat.card (conj g' H ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G)) :=
        fun g' hg' => prop1a_of_involution_normalizing hC hS hH hY3 ⟨g', rfl⟩ hg' (ihY g' hg')
      obtain ⟨g₀, hg₀⟩ := hM
      -- `F = C_G(Y)·P` and `K = F ⊓ M = F ⊓ conj g₀ H`
      set F : Subgroup G := Subgroup.centralizer (Y : Set G) ⊔ P with hFdef
      have hCGF : Subgroup.centralizer (Y : Set G) ≤ F := le_sup_left
      have hPF : P ≤ F := le_sup_right
      have hInvF : involutions (Subgroup.centralizer (Y : Set G) : Set G) ⊆ F :=
        fun x hx => hCGF hx.1
      have hXNY : X ≤ Subgroup.normalizer (Y : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mp hYN
      have hPNY : P ≤ Subgroup.normalizer (Y : Set G) := le_trans hPX hXNY
      have hFNY : F ≤ Subgroup.normalizer (Y : Set G) :=
        sup_le (Subgroup.centralizer_le_normalizer (Y : Set G)) hPNY
      set K : Subgroup ↥F := (F ⊓ M).subgroupOf F with hKdef
      -- `K` is strongly embedded in `↥F` (Prop. 1 (b))
      have hKstrong : IsStronglyEmbedded K := by
        rw [hKdef, hg₀]
        refine isStronglyEmbedded_inf_conj_of_even_for_fixed (H := H) (Y := Y) (F₀ := F)
          (g := g₀) hH hY3 hInvF ?_ ?_
        · rw [← hg₀]; exact hYM
        · intro g' hg'; exact hEV g' hg'
      set P' : Subgroup ↥F := P.subgroupOf F with hP'def
      have hP'K : P' ≤ K := by
        intro x hx
        have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
        rw [hKdef]
        exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hXM (hPX hxP)⟩
      -- The three fixed points of `X` (among them `M = conj g₀ H`) give three distinct fixed
      -- points of `P'` in `↥F ⧸ K`: for `X ≤ conj g H`, `exists_conj_inf_conj_subgroupOf_eq`
      -- gives `f : ↥F` with `(F ⊓ conj g H).subgroupOf F =
      -- ((F ⊓ conj g₀ H).subgroupOf F).map (MulAut.conj f)`, and `P' ≤ (F ⊓ conj g H).subgroupOf F`
      -- because `P ≤ X ≤ conj g H`; distinct `conj g H` give distinct such `f`-conjugates
      -- (`eq_conj_of_inf_conj_subgroupOf_eq`), hence three distinct fixed points.
      have hXg₀ : X ≤ conj g₀ H := by rw [← hg₀]; exact hXM
      -- PARTIALLY DONE (this session): the three fixed points of `X` are extracted below together
      -- with the transports `f₂, f₃ : ↥F` (`exists_conj_inf_conj_subgroupOf_eq`) and the proofs
      -- that `((1 : ↥F) : ↥F ⧸ K)` and `(f₂ : ↥F ⧸ K)` and `(f₃ : ↥F ⧸ K)` are fixed by `P'`
      -- (`stabilizer_mk` plus `change P' ≤ K.map (MulAut.conj fᵢ)` before rewriting with
      -- `hconjᵢ : ((F ⊓ conj g₀ H).subgroupOf F).map (MulAut.conj fᵢ) = (F ⊓ conj gᵢ H).subgroupOf F`).
      -- What remains is the pairwise DISTINCTNESS of these three points:
      -- `f ↦ (f : ↥F ⧸ K)` is injective on the conjugates of `K` because `N_{↥F}(K) = K`, so
      -- equal points ⟹ equal stabilisers ⟹ `(K)^f = (K)^g` ⟹ equal `F ⊓ conj g H` ⟹
      -- `conj g H = conj g' H` (`eq_conj_of_inf_conj_subgroupOf_eq`), contradicting `hne₀₂` etc.;
      -- then `Set.ncard_le_ncard` on the three-element set
      -- `{((1 : ↥F) : ↥F ⧸ K), (f₂ : ↥F ⧸ K), (f₃ : ↥F ⧸ K)}` (`Set.ncard_insert_of_notMem`,
      -- `Set.ncard_singleton`) gives `3 ≤ (fixedPts K P').ncard`.
      have hP'3 : 3 ≤ (fixedPts K P').ncard := by
        -- the point of `Ω` belonging to `M = conj g₀ H`, plus two further fixed points of `X`
        have hmem₀ : ((g₀ : G) : G ⧸ H) ∈ fixedPts H X := by
          rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk H g₀, ← hg₀]
          exact hXM
        have h2c : 1 < ((fixedPts H X) \ {((g₀ : G) : G ⧸ H)}).ncard := by
          have h := Set.ncard_sdiff_singleton_add_one hmem₀
          omega
        obtain ⟨ω₂, hω₂, ω₃, hω₃, hω₂₃⟩ :=
          (Set.one_lt_ncard (s := (fixedPts H X) \ {((g₀ : G) : G ⧸ H)})).mp h2c
        obtain ⟨g₂, hg₂⟩ := QuotientGroup.mk_surjective ω₂
        obtain ⟨g₃, hg₃⟩ := QuotientGroup.mk_surjective ω₃
        have hg₂' : ω₂ = ((g₂ : G) : G ⧸ H) := hg₂.symm
        have hg₃' : ω₃ = ((g₃ : G) : G ⧸ H) := hg₃.symm
        have hXg₂ : X ≤ conj g₂ H := by
          have h := mem_fixedPts_iff_le_stabilizer.mp hω₂.1
          rwa [← hg₂, stabilizer_mk H g₂] at h
        have hXg₃ : X ≤ conj g₃ H := by
          have h := mem_fixedPts_iff_le_stabilizer.mp hω₃.1
          rwa [← hg₃, stabilizer_mk H g₃] at h
        have hYg₀ : Y ≤ conj g₀ H := le_trans hYX hXg₀
        have hYg₂ : Y ≤ conj g₂ H := le_trans hYX hXg₂
        have hYg₃ : Y ≤ conj g₃ H := le_trans hYX hXg₃
        have hne₀₂ : conj g₀ H ≠ conj g₂ H := fun heq =>
          hω₂.2 (hg₂'.trans (mk_eq_of_conj_eq hH heq).symm)
        have hne₀₃ : conj g₀ H ≠ conj g₃ H := fun heq =>
          hω₃.2 (hg₃'.trans (mk_eq_of_conj_eq hH heq).symm)
        have hne₂₃ : conj g₂ H ≠ conj g₃ H := fun heq =>
          hω₂₃ (hg₂'.trans ((mk_eq_of_conj_eq hH heq).trans hg₃'.symm))
        -- the `↥F`-conjugates of `K` corresponding to `conj g₂ H` and `conj g₃ H`
        obtain ⟨f₂, hf₂⟩ := exists_conj_inf_conj_subgroupOf_eq (H := H) (Y := Y) (F := F)
          hH hYg₀ hYg₂ hInvF hEV hne₀₂
        obtain ⟨f₃, hf₃⟩ := exists_conj_inf_conj_subgroupOf_eq (H := H) (Y := Y) (F := F)
          hH hYg₀ hYg₃ hInvF hEV hne₀₃
        have hK₀ : K = (F ⊓ conj g₀ H).subgroupOf F := by rw [hKdef, hg₀]
        have hconj₂ : ((F ⊓ conj g₀ H).subgroupOf F).map (MulAut.conj f₂).toMonoidHom
            = (F ⊓ conj g₂ H).subgroupOf F := hf₂.symm
        have hconj₃ : ((F ⊓ conj g₀ H).subgroupOf F).map (MulAut.conj f₃).toMonoidHom
            = (F ⊓ conj g₃ H).subgroupOf F := hf₃.symm
        -- `P'` lies in all three conjugates, so all three points are fixed by `P'`
        have hP'le₂ : P' ≤ (F ⊓ conj g₂ H).subgroupOf F := fun x hx =>
          Subgroup.mem_subgroupOf.mpr
            ⟨x.2, hXg₂ (hPX (Subgroup.mem_subgroupOf.mp hx))⟩
        have hP'le₃ : P' ≤ (F ⊓ conj g₃ H).subgroupOf F := fun x hx =>
          Subgroup.mem_subgroupOf.mpr
            ⟨x.2, hXg₃ (hPX (Subgroup.mem_subgroupOf.mp hx))⟩
        have hfix₀ : ((1 : ↥F) : ↥F ⧸ K) ∈ fixedPts K P' := by
          rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk K (1 : ↥F), conj_one]
          exact hP'K
        have hfix₂ : ((f₂ : ↥F) : ↥F ⧸ K) ∈ fixedPts K P' := by
          rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk K f₂]
          change P' ≤ Subgroup.map (MulAut.conj f₂).toMonoidHom K
          rw [hK₀, hconj₂]
          exact hP'le₂
        have hfix₃ : ((f₃ : ↥F) : ↥F ⧸ K) ∈ fixedPts K P' := by
          rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk K f₃]
          change P' ≤ Subgroup.map (MulAut.conj f₃).toMonoidHom K
          rw [hK₀, hconj₃]
          exact hP'le₃
        -- distinctness of the three points: equal points have equal stabilisers, i.e. equal
        -- `K`-conjugates; rewriting `K` as `(F ⊓ conj g₀ H).subgroupOf F` and using the transport
        -- `hconjᵢ` shows that two of the `F ⊓ conj g H` coincide, contradicting `hne`.
        have key₂₀ : ((f₂ : ↥F) : ↥F ⧸ K) ≠ ((1 : ↥F) : ↥F ⧸ K) := by
          intro h
          have h1 := congrArg (MulAction.stabilizer ↥F) h
          rw [stabilizer_mk K f₂, stabilizer_mk K (1 : ↥F), conj_one] at h1
          rw [hK₀] at h1
          have hconj : (F ⊓ conj g₂ H).subgroupOf F = (F ⊓ conj g₀ H).subgroupOf F := by
            rw [← hconj₂]
            exact h1
          exact hne₀₂ (eq_conj_of_inf_conj_subgroupOf_eq hH hYg₂ hYg₀ hInvF hEV hconj).symm
        have key₃₀ : ((f₃ : ↥F) : ↥F ⧸ K) ≠ ((1 : ↥F) : ↥F ⧸ K) := by
          intro h
          have h1 := congrArg (MulAction.stabilizer ↥F) h
          rw [stabilizer_mk K f₃, stabilizer_mk K (1 : ↥F), conj_one] at h1
          rw [hK₀] at h1
          have hconj : (F ⊓ conj g₃ H).subgroupOf F = (F ⊓ conj g₀ H).subgroupOf F := by
            rw [← hconj₃]
            exact h1
          exact hne₀₃ (eq_conj_of_inf_conj_subgroupOf_eq hH hYg₃ hYg₀ hInvF hEV hconj).symm
        have key₂₃ : ((f₂ : ↥F) : ↥F ⧸ K) ≠ ((f₃ : ↥F) : ↥F ⧸ K) := by
          intro h
          have h1 := congrArg (MulAction.stabilizer ↥F) h
          rw [stabilizer_mk K f₂, stabilizer_mk K f₃] at h1
          have hconj : (F ⊓ conj g₂ H).subgroupOf F = (F ⊓ conj g₃ H).subgroupOf F := by
            calc (F ⊓ conj g₂ H).subgroupOf F
                = ((F ⊓ conj g₀ H).subgroupOf F).map (MulAut.conj f₂).toMonoidHom := hconj₂.symm
              _ = Subgroup.map (MulAut.conj f₂).toMonoidHom K := by rw [hK₀]
              _ = Subgroup.map (MulAut.conj f₃).toMonoidHom K := h1
              _ = ((F ⊓ conj g₀ H).subgroupOf F).map (MulAut.conj f₃).toMonoidHom := by rw [hK₀]
              _ = (F ⊓ conj g₃ H).subgroupOf F := hconj₃
          exact hne₂₃ (eq_conj_of_inf_conj_subgroupOf_eq hH hYg₂ hYg₃ hInvF hEV hconj)
        -- the three-element set of fixed points
        have hsubset : ({((1 : ↥F) : ↥F ⧸ K), ((f₂ : ↥F) : ↥F ⧸ K), ((f₃ : ↥F) : ↥F ⧸ K)} :
            Set (↥F ⧸ K)) ⊆ fixedPts K P' := by
          intro x hx
          rcases hx with hx | hx | hx
          · rw [hx]; exact hfix₀
          · rw [hx]; exact hfix₂
          · rw [hx]; exact hfix₃
        have hcard : ({((1 : ↥F) : ↥F ⧸ K), ((f₂ : ↥F) : ↥F ⧸ K), ((f₃ : ↥F) : ↥F ⧸ K)} :
            Set (↥F ⧸ K)).ncard = 3 := by
          rw [Set.ncard_insert_of_notMem (by
                simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
                exact ⟨fun h => key₂₀ h.symm, fun h => key₃₀ h.symm⟩),
              Set.ncard_insert_of_notMem (by simpa [Set.mem_singleton_iff] using key₂₃),
              Set.ncard_singleton]
        calc 3 = _ := hcard.symm
          _ ≤ _ := Set.ncard_le_ncard hsubset
      -- Choose `Q'`: maximal among the `p`-subgroups of `K` with `≥ 3` fixed points, `Q' ⊇ P'`
      obtain ⟨Q', hP'Q', hQ'K, hQ'p, hQ'3, hQ'max⟩ : ∃ Q' : Subgroup ↥F, P' ≤ Q' ∧ Q' ≤ K ∧
          IsPGroup p Q' ∧ 3 ≤ (fixedPts K Q').ncard ∧
          (∀ R : Subgroup ↥F, Q' ≤ R → R ≤ K → IsPGroup p R →
            3 ≤ (fixedPts K R).ncard → R = Q') := by
        have hP'p : IsPGroup p P' := by
          rw [hP'def]
          exact hPp.comap_of_injective F.subtype Subtype.coe_injective
        let S : Set (Subgroup ↥F) :=
          {R | P' ≤ R ∧ R ≤ K ∧ IsPGroup p R ∧ 3 ≤ (fixedPts K R).ncard}
        have hSne : S.Nonempty := ⟨P', le_rfl, hP'K, hP'p, hP'3⟩
        obtain ⟨Q', hQ'S, hQ'max⟩ := (Set.toFinite S).toFinset.exists_max_image
          (fun R => Nat.card ↥R) (by simpa using hSne)
        have hQ'Smem : Q' ∈ S := by simpa using hQ'S
        refine ⟨Q', hQ'Smem.1, hQ'Smem.2.1, hQ'Smem.2.2.1, hQ'Smem.2.2.2, ?_⟩
        intro R hQ'R hRK hRp hR3
        have hRS : R ∈ S := ⟨le_trans hQ'Smem.1 hQ'R, hRK, hRp, hR3⟩
        exact (Subgroup.eq_of_le_of_card_ge hQ'R
          (by simpa using hQ'max R (by simpa using hRS))).symm
      -- Prop. 2 (Ch. I §4) gives an involution of `N_K(Q')`
      obtain ⟨v, hvN, hv2⟩ := exists_mem_orderOf_eq_two_of_even_card
        (prop2_of_brsz hBrSz hA hKstrong hpprime hp2 hQ'K hQ'p hQ'3 hQ'max)
      -- its image `u ∈ G` normalises `Q := Q'.map F.subtype`
      set Q : Subgroup G := Q'.map F.subtype with hQdef
      set u : G := (((v : ↥K) : ↥F) : G) with hudef
      have hv0K : ((v : ↥K) : ↥F) ∈ K := (v : ↥K).2
      have huM : u ∈ M := (Subgroup.mem_subgroupOf.mp hv0K).2
      have hu2 : orderOf u = 2 := by
        rw [hudef, Subgroup.orderOf_coe (((v : ↥K) : ↥F)),
          Subgroup.orderOf_coe (v : ↥K)]
        exact hv2
      -- `u` normalises `Q`
      have huNQ : u ∈ Subgroup.normalizer (Q : Set G) := by
        have h1 : ((v : ↥K) : ↥F) ∈ Subgroup.normalizer (Q' : Set ↥F) :=
          mem_normalizer_of_mem_normalizer_subgroupOf hQ'K (v : ↥K).2 hvN
        have h2 : ((((v : ↥K) : ↥F)) : G) ∈ Subgroup.normalizer (Q'.map F.subtype : Set G) :=
          mem_normalizer_map_subtype_of_mem_normalizer (((v : ↥K) : ↥F).2) h1
        rwa [hudef, hQdef]
      -- Theorem C: `u` centralises `Q` (the two fixed points `M` and `M₂` of `Q`)
      have huCQ : u ∈ Subgroup.centralizer (Q : Set G) := by
        -- the base point is fixed by `Q'` (as `Q' ≤ K`), and there is a second fixed point
        have hbase : ((1 : ↥F) : ↥F ⧸ K) ∈ fixedPts K Q' := by
          rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk K (1 : ↥F), conj_one]
          exact hQ'K
        have h2 : 1 < (fixedPts K Q').ncard := by omega
        obtain ⟨ω, hω, hωne⟩ := Set.exists_ne_of_one_lt_ncard h2 ((1 : ↥F) : ↥F ⧸ K)
        obtain ⟨f, hf⟩ := QuotientGroup.mk_surjective ω
        have hf' : ω = ((f : ↥F) : ↥F ⧸ K) := hf.symm
        have hQ'ω : Q' ≤ (K : Subgroup ↥F).map (MulAut.conj f).toMonoidHom := by
          have h := mem_fixedPts_iff_le_stabilizer.mp hω
          rwa [hf', stabilizer_mk K f] at h
        -- transport: `(K)^f` is the part of `F` lying in `conj g M`, for `g = (f : G)`
        set g : G := ((f : ↥F) : G) with hg
        have hconjK : (K : Subgroup ↥F).map (MulAut.conj f).toMonoidHom
            = (F ⊓ conj g M).subgroupOf F := by
          have h := subgroupOf_conj_of_mem (F := F) (A := F ⊓ M) ((f : ↥F).2)
          rw [conj_inf, conj_eq_self_of_mem ((f : ↥F).2)] at h
          rw [show (((F ⊓ M) ⊓ F) : Subgroup G) = F ⊓ M from by
                ext x; simp only [Subgroup.mem_inf]; tauto] at h
          rw [hg]
          simpa [hKdef] using h.symm
        -- `Q ≤ M ⊓ conj g M`
        have hmapK : (K : Subgroup ↥F).map F.subtype = F ⊓ M := by
          rw [hKdef, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
        have hQle : Q ≤ M ⊓ conj g M := by
          refine le_inf ?_ ?_
          · calc Q = (Q' : Subgroup ↥F).map F.subtype := rfl
              _ ≤ (K : Subgroup ↥F).map F.subtype := Subgroup.map_mono hQ'K
              _ = F ⊓ M := hmapK
              _ ≤ M := inf_le_right
          · calc Q = (Q' : Subgroup ↥F).map F.subtype := rfl
              _ ≤ ((K : Subgroup ↥F).map (MulAut.conj f).toMonoidHom).map F.subtype :=
                  Subgroup.map_mono hQ'ω
              _ = ((F ⊓ conj g M).subgroupOf F).map F.subtype := by rw [hconjK]
              _ = F ⊓ conj g M := Subgroup.map_subgroupOf_eq_of_le inf_le_left
              _ ≤ conj g M := inf_le_right
        -- `g ∉ M`: otherwise `f ∈ K` and `ω` would be the base point
        have hgM : g ∉ M := by
          intro hgM'
          have hfK : f ∈ K := by
            rw [hKdef]
            exact Subgroup.mem_subgroupOf.mpr ⟨f.2, hg ▸ hgM'⟩
          have h1 : ((f : ↥F) : ↥F ⧸ K) = ((1 : ↥F) : ↥F ⧸ K) := by
            rw [QuotientGroup.eq]
            simpa using K.inv_mem hfK
          exact hωne (hf'.trans h1)
        -- Theorem C
        have hMstrong : IsStronglyEmbedded M := hg₀ ▸ conj_stronglyEmbedded hH g₀
        have hcent := hC G hS M hMstrong g hgM u ⟨huM, hu2⟩ Q hQle huNQ
        exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hcent x hx).symm
      have hPQ : P ≤ Q := by
        intro q hq
        exact Subgroup.mem_map.mpr ⟨⟨q, hPF hq⟩, hP'Q' (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
      -- the promotion step: `u ∈ C_G(Y)`
      have huCY : u ∈ Subgroup.centralizer (Y : Set G) := by
        have huCP : u ∈ Subgroup.centralizer (P : Set G) :=
          Subgroup.centralizer_le (fun x hx => hPQ hx) huCQ
        set Z : Subgroup ↥F := (Subgroup.centralizer (Y : Set G)).subgroupOf F with hZdef
        set P₂ : Subgroup ↥F := P.subgroupOf F with hP₂def
        have hZn : Z.Normal := by
          rw [hZdef]
          exact (Subgroup.normal_subgroupOf_iff_le_normalizer hCGF).mpr
            (fun g hg => normalizer_le_normalizer_centralizer (hFNY hg))
        haveI := hZn
        have hsupZP : Z ⊔ P₂ = ⊤ := by
          rw [hZdef, hP₂def, ← Subgroup.subgroupOf_sup hCGF hPF, ← hFdef]
          exact Subgroup.subgroupOf_self F
        have huF : u ∈ F := (((v : ↥K) : ↥F)).2
        obtain ⟨c', hc', p', hp', hcp⟩ : ∃ c' ∈ Z, ∃ p' ∈ P₂, c' * p' = (⟨u, huF⟩ : ↥F) := by
          have hmem : (⟨u, huF⟩ : ↥F) ∈ ((Z : Set ↥F) * (P₂ : Set ↥F)) := by
            rw [show ((Z : Set ↥F) * (P₂ : Set ↥F)) = ↑(Z ⊔ P₂) from
                  (Subgroup.normal_mul Z P₂).symm, hsupZP]
            trivial
          exact Set.mem_mul.mp hmem
        have hcY : (c' : G) ∈ Subgroup.centralizer (Y : Set G) := Subgroup.mem_subgroupOf.mp hc'
        have hpP : (p' : G) ∈ P := Subgroup.mem_subgroupOf.mp hp'
        have hu_eq : u = (c' : G) * (p' : G) := by
          have h := congrArg (fun x : ↥F => (x : G)) hcp
          rw [Subgroup.coe_mul] at h
          exact h.symm
        have hup : u * (p' : G) = (p' : G) * u :=
          (Subgroup.mem_centralizer_iff.mp huCP (p' : G) hpP).symm
        have hccomm : (c' : G) * (p' : G) = (p' : G) * (c' : G) := by
          have h2 : ((c' : G) * (p' : G)) * (p' : G) = ((p' : G) * (c' : G)) * (p' : G) := by
            calc ((c' : G) * (p' : G)) * (p' : G)
                = u * (p' : G) := by rw [hu_eq]
              _ = (p' : G) * u := hup
              _ = (p' : G) * ((c' : G) * (p' : G)) := by rw [hu_eq]
              _ = ((p' : G) * (c' : G)) * (p' : G) := by group
          exact mul_right_cancel h2
        have hpu : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
        have hp2mem : (p' : G) ^ 2 ∈ Subgroup.centralizer (Y : Set G) := by
          have h5 : ((c' : G) * (p' : G)) ^ 2 = 1 := by rw [← hu_eq]; exact hpu
          have h6 : ((c' : G) ^ 2) * ((p' : G) ^ 2) = 1 := by
            rw [← Commute.mul_pow hccomm 2]
            exact h5
          have hp2eq : (p' : G) ^ 2 = ((c' : G) ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h6
          rw [hp2eq]
          exact (Subgroup.centralizer (Y : Set G)).inv_mem (Subgroup.pow_mem _ hcY 2)
        obtain ⟨n, hn⟩ := hPp ⟨(p' : G), hpP⟩
        have hdvd : orderOf (⟨(p' : G), hpP⟩ : ↥P) ∣ p ^ n := orderOf_dvd_of_pow_eq_one hn
        have hpodd : Odd (orderOf (p' : G)) := by
          rw [Subgroup.orderOf_coe (⟨(p' : G), hpP⟩ : ↥P)]
          exact Work.ThreePoints.Odd.of_dvd hdvd (Odd.pow (hpprime.odd_of_ne_two hp2))
        obtain ⟨k, hk⟩ := hpodd
        have hp_pow : (p' : G) = ((p' : G) ^ 2) ^ (k + 1) := by
          rw [← pow_mul]
          have hk' : 2 * (k + 1) = orderOf (p' : G) + 1 := by rw [hk]; ring
          rw [hk', pow_succ, pow_orderOf_eq_one, one_mul]
        have hpY : (p' : G) ∈ Subgroup.centralizer (Y : Set G) := by
          rw [hp_pow]
          exact Subgroup.pow_mem _ hp2mem (k + 1)
        rw [hu_eq]
        exact (Subgroup.centralizer (Y : Set G)).mul_mem hcY hpY
      have huCX : u ∈ Subgroup.centralizer (X : Set G) := by
        have hYc : Y ≤ Subgroup.centralizer ({u} : Set G) := fun y hy =>
          Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp huCY y hy)
        have hPc : P ≤ Subgroup.centralizer ({u} : Set G) := fun q hq =>
          Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp huCQ q (hPQ hq))
        rw [← hsup]
        exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
          Subgroup.mem_centralizer_singleton_iff.mp (sup_le hYc hPc hx)
      exact ⟨u, huM, Subgroup.centralizer_le_normalizer _ huCX, hu2⟩

end Work.ThreePoints
