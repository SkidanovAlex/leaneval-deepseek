import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.ch1_lem2
import Submission.Work.ThreePoints.odd_card_of_fixes_three
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_source
import Submission.Work.ThreePoints.exists_descent_odd_solvable
import Submission.Work.ThreePoints.prop1a_descent_aux
import Submission.Work.ThreePoints.prop1a_three_fixedPts

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.ThreePoints

open LeanEval.GroupTheory.Defs

variable {G : Type} [Group G]

/-- Cauchy's theorem in the form used below: a subgroup of even order contains an involution. -/
theorem exists_mem_orderOf_two_of_even_card {H : Subgroup G} [Finite H]
    (h : Even (Nat.card H)) :
    ∃ x : G, x ∈ H ∧ orderOf x = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp h)
  exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

/-- An element normalising `Y'` normalises the centraliser `C_G(Y')`. -/
theorem le_normalizer_centralizer {Y' P' : Subgroup G}
    (h : P' ≤ Subgroup.normalizer (Y' : Set G)) :
    P' ≤ Subgroup.normalizer (Subgroup.centralizer (Y' : Set G) : Set G) := by
  intro p hp
  have hpN : p ∈ Subgroup.normalizer (Y' : Set G) := h hp
  have hpinvN : p⁻¹ ∈ Subgroup.normalizer (Y' : Set G) := Subgroup.inv_mem _ hpN
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have hpy : p⁻¹ * y * p ∈ Y' := by
      have h1 := (Subgroup.mem_normalizer_iff.mp hpinvN y).mp hy
      simpa using h1
    calc y * (p * c * p⁻¹) = p * ((p⁻¹ * y * p) * c) * p⁻¹ := by group
      _ = p * (c * (p⁻¹ * y * p)) * p⁻¹ := by rw [hc (p⁻¹ * y * p) hpy]
      _ = (p * c * p⁻¹) * y := by group
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have hpy : p * y * p⁻¹ ∈ Y' := (Subgroup.mem_normalizer_iff.mp hpN y).mp hy
    have hcomm := hc (p * y * p⁻¹) hpy
    calc y * c = p⁻¹ * ((p * y * p⁻¹) * (p * c * p⁻¹)) * p := by group
      _ = p⁻¹ * ((p * c * p⁻¹) * (p * y * p⁻¹)) * p := by rw [hcomm]
      _ = c * y := by group

/-- **Peterfalvi I Ch. II §4 Prop. 1(a), the induction step** (p. 168).

(This is the same statement as the existing `Work.ThreePoints.prop1a_of_induction_step` in
`Submission/Work/ThreePoints/prop1a_of_induction_step.lean`, `by hole`; its earlier prover
declared it `false` only because at that time the input it needs was not yet proved.)

Let `H` be strongly embedded in the finite group `G` in situation (B0)–(B2), let `X ≤ M = H^g`
fix at least three points of `Ω = G ⧸ H`, `X ≠ ⊥`, and assume the induction hypothesis

`IH : ∀ X' M', |X'| < |X| → 3 ≤ |Ω_{X'}| → M' = H^{g'} → X' ≤ M' → Even |C_{M'}(X')|`.

Then `|C_M(X)|` is even.

Source (p. 168).  `X` has odd order (`Work.ThreePoints.odd_card_of_fixes_three`, available), so by
`hFT` it is solvable, and there are a prime `p` and a normal `Y ◁ X` with `X/Y` of order `p`
(take a maximal normal subgroup; `p` is odd since `X` is odd).  Put `P :=` a `p`-Sylow of `X`
(so `X = Y·P`) and `F₁ := C_G(Y) ⊔ P`.

*Step 1 (Prop. 1(b) for `Y`).*  `IH` applied to `Y ∈ Ω_Y` gives `Even |C_{M'}(Y)|` for every
`M' ∈ Ω_Y`; by Ch. I §1 (6) and Ch. I §2 Lemma 2 (`Work.ThreePoints.ch1_lem2`), the map
`M' ↦ F₁ ⊓ M'` is a bijection of `Ω_Y` onto the class `Ξ` of `F₁`-conjugates of `K := F₁ ⊓ M`, and
`K` is a proper Bender group of `F₁`.  (This is the source's "`(a)` implies `(b)`" and must be
proved here.)

*Step 2 (the `p`-subgroup `Q`).*  `Ω_X ⊆ Ω_Y ⊓ Ω_P`, since `X ≤ M'` implies `P ≤ M'`; hence every
`M' ∈ Ω_X` has `P ≤ F₁ ⊓ M'`, so `Ξ_P` has at least three points.  Let `Q` be a maximal
`p`-subgroup of `K` with `|Ξ_Q| ≥ 3` and `P ≤ Q`.

*Step 3 (Ch. I §4 Prop. 2 inside `F₁`).*  `K` is strongly embedded in `F₁` and `Q` is maximal among
the `p`-subgroups of `K` with `≥ 3` fixed points of `F₁ ⧸ K`; apply
`Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_source` (the source form: no `2`-rank
hypothesis is needed, because its Case 1 obtains 2-transitivity from §4 Prop. 1) to get an
involution `u ∈ F₁ ⊓ M` normalising `Q`.

*Step 4 (Theorem C).*  `Q` fixes at least two points of `Ξ`, i.e. `Q ≤ M ⊓ M₂` for
`M₂ ∈ Ω_Y`, `M₂ ≠ M`; `hC` applied to the strongly embedded `M` then gives `u ∈ C_G(Q)`, and
`P ≤ Q` gives `u ∈ C_G(P)`.

*Step 5 (the `p`-group quotient step).*  `u ∈ F₁ = C_G(Y)·P` with `|F₁ : C_G(Y)|` a power of `p`
(odd) and `u² = 1` force `u ∈ C_G(Y)`: if `u ∉ C_G(Y)`, then `u·C_G(Y)` is the unique element of
order `2` of the `p`-group `F₁/C_G(Y)`, impossible for odd `p`.

Hence `u ∈ C_M(Y) ⊓ C_M(P) = C_M(X)` is an involution, so `|C_M(X)|` is even. -/
theorem prop1a_descent {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X M : Subgroup G}
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (hM : ∃ g : G, M = Submission.Blueprint.conj g H) (hXM : X ≤ M)
    (IH : ∀ {X' M' : Subgroup G}, Nat.card X' < Nat.card X →
      3 ≤ (Submission.Blueprint.fixedPts H X').ncard →
      (∃ g : G, M' = Submission.Blueprint.conj g H) → X' ≤ M' →
      Even (Nat.card (M' ⊓ Subgroup.centralizer (X' : Set G) : Subgroup G)))
    (hXne : X ≠ ⊥) :
    Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) := by
  classical
  -- (1) `X` has odd order.
  have hoddX : Odd (Nat.card X) := odd_card_of_fixes_three hH hX3
  -- (2) `X` is solvable.
  have hsolX : Group.IsSolvable ↥X := hFT ↥X hoddX
  -- (3) descent data: `p` odd prime, `Y ◁ X`, `Y ≠ X`, `P` a `p`-subgroup, `X = Y ⊔ P`.
  obtain ⟨p, Y, P, hp, hp2, hYX, hYn, hYne, hPp, hPX, hYP⟩ :=
    exists_descent_odd_solvable hXne hoddX hsolX
  -- (4) `F₁ = C_G(Y) ⊔ P`.
  set F1 : Subgroup G := Subgroup.centralizer (Y : Set G) ⊔ P with hF1def
  have hCYF1 : Subgroup.centralizer (Y : Set G) ≤ F1 := le_sup_left
  have hPF1 : P ≤ F1 := le_sup_right
  have hYM : Y ≤ M := le_trans hYX hXM
  have hPM : P ≤ M := le_trans hPX hXM
  have hPY : P ≤ Subgroup.normalizer (Y : Set G) :=
    le_trans hPX ((Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mp hYn)
  -- (5) `F₁ ⊓ M'` has even order for every conjugate `M' ⊇ X` of `H`.
  have hYXlt : Nat.card Y < Nat.card X :=
    lt_of_le_of_ne (Subgroup.card_le_of_le hYX)
      (fun h => hYne (Subgroup.eq_of_le_of_card_ge hYX (le_of_eq h.symm)))
  have hY3 : 3 ≤ (Submission.Blueprint.fixedPts H Y).ncard :=
    le_trans hX3 (Set.ncard_le_ncard (fixedPts_mono hYX))
  have hevF1 : ∀ {M' : Subgroup G}, (∃ g' : G, M' = Submission.Blueprint.conj g' H) →
      X ≤ M' → Even (Nat.card (F1 ⊓ M' : Subgroup G)) := by
    intro M' hM' hXM'
    have hYM' : Y ≤ M' := le_trans hYX hXM'
    have h1 : Even (Nat.card (M' ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G)) :=
      IH hYXlt hY3 hM' hYM'
    refine even_card_of_le ?_ h1
    exact le_inf (le_trans inf_le_right le_sup_left) inf_le_left
  -- (6) `K = F₁ ⊓ M` is strongly embedded in `F₁` (Ch. I §1 (6) / §2 Lemma 2).
  obtain ⟨g, hg⟩ := hM
  obtain ⟨ω₂, hω₂, hω₂ne⟩ := Set.exists_ne_of_one_lt_ncard
    (show 1 < (Submission.Blueprint.fixedPts H X).ncard by omega) (g : G ⧸ H)
  obtain ⟨g₂, hg₂⟩ := QuotientGroup.mk_surjective ω₂
  have hXM2 : X ≤ Submission.Blueprint.conj g₂ H := by
    rw [← Work.ThreePoints.stabilizer_mk H g₂, hg₂]
    exact mem_fixedPts_iff_le_stabilizer.mp hω₂
  have hne : Submission.Blueprint.conj g H ≠ Submission.Blueprint.conj g₂ H := by
    intro heq
    exact hω₂ne (hg₂ ▸ (mk_eq_of_conj_eq hH heq)).symm
  have hXM' : X ≤ Submission.Blueprint.conj g H := by rw [← hg]; exact hXM
  set K : Subgroup ↥F1 := (F1 ⊓ M).subgroupOf F1 with hKdef
  have hKstrong : IsStronglyEmbedded K := by
    have hraw := (ch1_lem2 hH hne (hevF1 ⟨g, rfl⟩ hXM') (hevF1 ⟨g₂, rfl⟩ hXM2)).2.1
    rwa [← hg] at hraw
  -- (7) `P` fixes at least three points of `↥F₁ ⧸ K`.
  have hP'3 : 3 ≤ (Submission.Blueprint.fixedPts K (P.subgroupOf F1)).ncard :=
    prop1a_three_fixedPts hH ⟨g, hg⟩ hXM hX3 hPF1 hPX hevF1
  -- (8) a maximal such `p`-subgroup `Q ≤ K`.
  have hP'p : IsPGroup p (P.subgroupOf F1) := by
    have h := IsPGroup.comap_of_injective (p := p) hPp F1.subtype Subtype.coe_injective
    rwa [Subgroup.comap_subtype] at h
  have hP'leK : P.subgroupOf F1 ≤ K := by
    intro q hq
    rw [Subgroup.mem_subgroupOf] at hq ⊢
    exact ⟨hPF1 hq, hPM hq⟩
  obtain ⟨Q, hQK, hQp, hQP', hQ3, hQmax⟩ : ∃ Q : Subgroup ↥F1, Q ≤ K ∧ IsPGroup p Q ∧
      P.subgroupOf F1 ≤ Q ∧ 3 ≤ (Submission.Blueprint.fixedPts K Q).ncard ∧
      (∀ R : Subgroup ↥F1, Q ≤ R → R ≤ K → IsPGroup p R →
        3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) := by
    haveI : Nonempty {Q : Subgroup ↥F1 // Q ≤ K ∧ IsPGroup p Q ∧ P.subgroupOf F1 ≤ Q ∧
        3 ≤ (Submission.Blueprint.fixedPts K Q).ncard} :=
      ⟨⟨P.subgroupOf F1, hP'leK, hP'p, le_rfl, hP'3⟩⟩
    obtain ⟨Q₀, hQ₀max⟩ := Finite.exists_max
      (fun Q : {Q : Subgroup ↥F1 // Q ≤ K ∧ IsPGroup p Q ∧ P.subgroupOf F1 ≤ Q ∧
        3 ≤ (Submission.Blueprint.fixedPts K Q).ncard} => Nat.card Q.1)
    refine ⟨Q₀.1, Q₀.2.1, Q₀.2.2.1, Q₀.2.2.2.1, Q₀.2.2.2.2, ?_⟩
    intro R hQR hRK hRp hR3
    have := hQ₀max ⟨R, hRK, hRp, le_trans Q₀.2.2.2.1 hQR, hR3⟩
    exact (Subgroup.eq_of_le_of_card_ge hQR this).symm
  -- (9) Ch. I §4 Prop. 2 inside `F₁`: an involution of `K` normalising `Q`.
  have hEven : Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)) :=
    even_card_normalizer_of_maximal_p_subgroup_source hKstrong hp hp2 hQK hQp hQ3 hQmax
  obtain ⟨z, hzN, hz2⟩ := exists_mem_orderOf_two_of_even_card hEven
  obtain ⟨u, huK, huN, huord, huordG⟩ :
      ∃ u : ↥F1, u ∈ K ∧ u ∈ Subgroup.normalizer (Q : Set ↥F1) ∧ orderOf u = 2 ∧
        orderOf (u : G) = 2 := by
    have h1 : (Subgroup.normalizer (Q : Set ↥F1)).subgroupOf K =
        Subgroup.normalizer (Q.subgroupOf K : Set K) :=
      Subgroup.subgroupOf_normalizer_eq hQK
    rw [← h1] at hzN
    refine ⟨(z : ↥F1), z.2, Subgroup.mem_subgroupOf.mp hzN, ?_, ?_⟩
    · exact (Subgroup.orderOf_coe (H := K) z).trans hz2
    · exact ((Subgroup.orderOf_coe (H := F1) (z : ↥F1)).trans
        (Subgroup.orderOf_coe (H := K) z)).trans hz2
  -- (10) Theorem C: `u` centralises `Q`.
  obtain ⟨ω, hω, hωne⟩ := Set.exists_ne_of_one_lt_ncard
    (show 1 < (Submission.Blueprint.fixedPts K Q).ncard by omega)
    (((1 : ↥F1) : ↥F1 ⧸ K))
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective ω
  have hQx : Q ≤ Submission.Blueprint.conj x K := by
    rw [← Work.ThreePoints.stabilizer_mk K x, hx]
    exact mem_fixedPts_iff_le_stabilizer.mp hω
  have hxK : x ∉ K := by
    intro hmem
    have h1 : x ∈ MulAction.stabilizer (↥F1) (((1 : ↥F1)) : ↥F1 ⧸ K) := by
      rw [Work.ThreePoints.stabilizer_mk K 1, conj_one]
      exact hmem
    have h2 : x • (((1 : ↥F1)) : ↥F1 ⧸ K) = (((1 : ↥F1)) : ↥F1 ⧸ K) :=
      MulAction.mem_stabilizer_iff.mp h1
    rw [Work.ThreePoints.smul_mk, mul_one] at h2
    exact hωne (hx.symm.trans h2)
  set M₂ : Subgroup G := Submission.Blueprint.conj (x : G) M with hM₂def
  have hxNotM : (x : G) ∉ M := fun hmem => hxK ⟨x.2, hmem⟩
  have hconjK : Submission.Blueprint.conj x K = (F1 ⊓ M₂).subgroupOf F1 := by
    rw [hKdef]
    exact conj_subgroupOf_inf (M' := M₂) rfl
  have hQGM₂ : Subgroup.map F1.subtype Q ≤ M₂ := by
    have h1 : Subgroup.map F1.subtype Q ≤
        Subgroup.map F1.subtype (Submission.Blueprint.conj x K) := Subgroup.map_mono hQx
    rw [hconjK, map_subtype_subgroupOf_inf] at h1
    exact le_trans h1 inf_le_right
  have hQGleM : Subgroup.map F1.subtype Q ≤ M := by
    have h1 : Subgroup.map F1.subtype Q ≤ Subgroup.map F1.subtype K := Subgroup.map_mono hQK
    rw [show K = (F1 ⊓ M).subgroupOf F1 from hKdef, map_subtype_subgroupOf_inf] at h1
    exact le_trans h1 inf_le_right
  have huM : (u : G) ∈ M := by
    have h1 : (u : ↥F1) ∈ (F1 ⊓ M : Subgroup G).subgroupOf F1 := by
      rw [← hKdef]; exact huK
    exact (Subgroup.mem_subgroupOf.mp h1).2
  have huNG : (u : G) ∈ Subgroup.normalizer (Subgroup.map F1.subtype Q : Set G) :=
    (prop1a_norm_map (F := F1) (Q := Q) (x := u)).mpr huN
  have hMstrong : IsStronglyEmbedded M := by rw [hg]; exact conj_stronglyEmbedded hH g
  have hcentQ : ∀ w ∈ Subgroup.map F1.subtype Q, (u : G) * w = w * (u : G) :=
    hC G hS M hMstrong (x : G) hxNotM (u : G) ⟨huM, huordG⟩
      (Subgroup.map F1.subtype Q) (le_inf hQGleM hQGM₂) huNG
  -- (11) the `p`-group quotient step: `u ∈ C_G(Y)`.
  have hu2 : u ^ 2 = 1 := by rw [← huord]; exact pow_orderOf_eq_one u
  have hCnorm : ((Subgroup.centralizer (Y : Set G)).subgroupOf F1).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCYF1).mpr
      (sup_le Subgroup.le_normalizer (le_normalizer_centralizer hPY))
  have hsup : (Subgroup.centralizer (Y : Set G)).subgroupOf F1 ⊔ P.subgroupOf F1 = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hCYF1 hPF1]
    exact Subgroup.subgroupOf_self F1
  have huCY : (u : G) ∈ Subgroup.centralizer (Y : Set G) :=
    Subgroup.mem_subgroupOf.mp (prop1a_p_quotient hp hp2 hCnorm hsup hP'p hu2)
  -- (12) `P ≤ Q` turns `u ∈ C_G(Q)` into `u ∈ C_G(P)`.
  have huCP : (u : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyF1 : y ∈ F1 := hPF1 hy
    have hyQ : y ∈ Subgroup.map F1.subtype Q :=
      Subgroup.mem_map.mpr ⟨⟨y, hyF1⟩, hQP' (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
    exact (hcentQ y hyQ).symm
  -- (13) `u ∈ C_G(X)`.
  have huCX : (u : G) ∈ Subgroup.centralizer (X : Set G) := by
    have hYc : Y ≤ Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G) :=
      Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr huCY)
    have hPc : P ≤ Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G) :=
      Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr huCP)
    have hXc : X ≤ Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G) := by
      rw [← hYP]; exact sup_le hYc hPc
    exact (Subgroup.le_centralizer_iff.mp hXc) (Subgroup.mem_zpowers (u : G))
  -- (14) assemble.
  refine even_iff_two_dvd.mpr ?_
  have humem : (u : G) ∈ (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := ⟨huM, huCX⟩
  have hdvd := orderOf_dvd_natCard
    (⟨(u : G), humem⟩ : ↥(M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G))
  have hord : orderOf (⟨(u : G), humem⟩ :
      ↥(M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) = 2 := by
    rw [Subgroup.orderOf_mk]; exact huordG
  rwa [hord] at hdvd

end Work.ThreePoints
