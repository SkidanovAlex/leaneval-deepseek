import Mathlib
import Submission.Work.DoubleTransitivity.Sec4.Defs
import Submission.Work.DoubleTransitivity.Sec5.Defs
import Submission.Work.DoubleTransitivity.Sec4.prop1
import Submission.Work.DoubleTransitivity.Sec4.prop2
import Submission.Work.DoubleTransitivity.Sec3.prop1
import Submission.Work.DoubleTransitivity.Sec2.prop2
import Submission.Work.DoubleTransitivity.Sec2.lemma1
import Submission.Work.DoubleTransitivity.Sec1.unique_fixed
import Submission.Work.DoubleTransitivity.Sec1.restrict
import Submission.Work.DoubleTransitivity.Sec5.lemma1
import Submission.Work.DoubleTransitivity.Sec4.RpDefs
import Submission.Work.DoubleTransitivity.Sec4.lemma2_part1
import Submission.Work.DoubleTransitivity.Sec4.not_rp_twoTransitive
import Submission.Work.DoubleTransitivity.Sec4.rp_no_two_fixed_pts
import Submission.Work.DoubleTransitivity.Sec4.RpHelpers
import Submission.Work.DoubleTransitivity.App2.app2_1
import Submission.Work.DoubleTransitivity.App2.app2_5
import Submission.Work.DoubleTransitivity.Sec1.sylow_of_sylowIn
import Submission.Work.Reductions.stronglyEmbedded_subgroupOf
import Submission.Work.Reductions.stronglyEmbedded_index_odd
import Submission.Work.Reductions.hasFourGroup_quotient
import Submission.Work.Reductions.Quotient
import Submission.Work.ThreePoints.FourGroupCoprime
import Submission.Work.ThreePoints.isStronglyEmbedded_map_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec5.inductionStep`

Peterfalvi, *Le théorème de Bender–Suzuki I*, Ch. I §5, **Proposition 1** (p. 158):

> If `D = H ∩ H^t` has a normal subgroup `A ≠ 1` normalised by `t` and by an involution of `H`,
> then `G` acts `2`-transitively on `Ω = G ⧸ H`.

This is the only place in the proof of Theorem A where the induction hypothesis (A2)
(`Work.DoubleTransitivity.ThmAForBelow`) is used.

Two cases are treated.

* If `N_G(A) = ⊤` (so `A ⊴ G`), then `A` has odd order and `A ≤ H`, so `H/A` is strongly embedded
  in `G/A` (`Work.ThreePoints.isStronglyEmbedded_map_quotient`), `G/A` has a four-group
  (`Work.Reductions.hasFourGroup_quotient`), and `|G/A| < |G|`.  The induction hypothesis gives
  the double transitivity of `G/A` on `(G/A) ⧸ (H/A)`, which transfers back to `G` on `G ⧸ H`
  (`isMultiplyPretransitive_quotient`).

* If `N_G(A) ≠ ⊤`, let `N = N_G(A)`.  Then `N ⊓ H` is strongly embedded in `N`
  (`Work.Reductions.stronglyEmbedded_subgroupOf`), `N` contains a four-group (all involutions of
  `H` lie in `N`, because `D` is transitive on `Inv H` and `D ≤ N`), and `|N| < |G|`.  Applying
  the induction hypothesis to `N` gives that `N` acts `2`-transitively on `N ⧸ (N ⊓ H)`.
  Peterfalvi Ch. I §4 Lemma 3 (`sec4_lemma3`), applied inside `N`, then shows that the `p`-Sylow
  `P` of `D` supplied by Ch. I §5 Lemma 1 is a `p`-Sylow of `N`.  Finally, if `|Ω_P| ≥ 3`, a
  maximal `p`-subgroup `S ≤ H` with `≥ 3` fixed points containing `P` has an involution
  `u ∈ N_H(S)` (Ch. I §4 Prop. 2); since `Inv(H) ⊆ N`, `u` normalises both `S` and `N`, hence
  `S ⊓ N = P`, so `u ∈ N_H(P)`, contradicting the oddness of `|N_H(P)|`.  Hence `|Ω_P| = 2`, and
  Ch. I §4 Prop. 1 finishes the proof.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Pointwise

namespace Work.DoubleTransitivity.Sec5

open Submission.Blueprint
open LeanEval.GroupTheory.Defs

section Helpers

variable {G : Type} [Group G] [Finite G]

/-! ## 1. Auxiliary lemmas about subgroups -/

/-- Conjugation inside a subgroup is conjugation in the ambient group: for `t ∈ N`,
`twoPoint (H.subgroupOf N) t = (twoPoint H t).subgroupOf N`. -/
theorem twoPoint_subgroupOf {H N : Subgroup G} {t : G} (htN : t ∈ N) :
    twoPoint (H.subgroupOf N) ⟨t, htN⟩ = (twoPoint H t).subgroupOf N := by
  show H.subgroupOf N ⊓ Submission.Blueprint.conj ⟨t, htN⟩ (H.subgroupOf N)
      = (H ⊓ Submission.Blueprint.conj t H).subgroupOf N
  rw [Work.DoubleTransitivity.Sec1.conj_subgroupOf (H := H) (X := N) ⟨t, htN⟩]
  show H.comap N.subtype ⊓ (Submission.Blueprint.conj t H).comap N.subtype
      = (H ⊓ Submission.Blueprint.conj t H).comap N.subtype
  rw [Subgroup.comap_inf]

/-- A Sylow `p`-subgroup of `D` restricts to a Sylow `p`-subgroup of `D` inside any subgroup
`N ≥ D`. -/
theorem isSylowSubgroupOf_subgroupOf {p : ℕ} {P D N : Subgroup G} (hDN : D ≤ N)
    (h : IsSylowSubgroupOf p P D) :
    IsSylowSubgroupOf p (P.subgroupOf N) (D.subgroupOf N) := by
  obtain ⟨hPD, hPp, hidx⟩ := h
  have hPN : P ≤ N := hPD.trans hDN
  have hcP : Nat.card ↥(P.subgroupOf N) = Nat.card ↥P := by
    rw [← Subgroup.card_map_of_injective (f := N.subtype) (K := P.subgroupOf N)
        N.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hPN]
  have hcPd : Nat.card ↥(P.subgroupOf D) = Nat.card ↥P := by
    rw [← Subgroup.card_map_of_injective (f := D.subtype) (K := P.subgroupOf D)
        D.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hPD]
  have hcD : Nat.card ↥(D.subgroupOf N) = Nat.card ↥D := by
    rw [← Subgroup.card_map_of_injective (f := N.subtype) (K := D.subgroupOf N)
        N.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hDN]
  have hcPD : Nat.card ↥((P.subgroupOf N).subgroupOf (D.subgroupOf N))
      = Nat.card ↥(P.subgroupOf D) := by
    have hkey : Nat.card ↥(((P.subgroupOf N).subgroupOf (D.subgroupOf N)).map
        (D.subgroupOf N).subtype)
        = Nat.card ↥((P.subgroupOf N).subgroupOf (D.subgroupOf N)) :=
      Subgroup.card_map_of_injective (D.subgroupOf N).subtype_injective
    rw [← hkey, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (Subgroup.subgroupOf_mono N hPD), hcP, hcPd]
  refine ⟨fun x hx => hPD hx, hPp.comap_subtype, ?_⟩
  intro hdvd
  apply hidx
  rw [Subgroup.index_eq_card_div (P.subgroupOf D), ← hcD, ← hcPD,
    ← Subgroup.index_eq_card_div ((P.subgroupOf N).subgroupOf (D.subgroupOf N))]
  exact hdvd

/-- A `p`-subgroup of `D` containing a Sylow `p`-subgroup of `D` equals it. -/
theorem eq_of_isSylowSubgroupOf_le {p : ℕ} [Fact p.Prime] {P Q D : Subgroup G}
    (hP : IsSylowSubgroupOf p P D) (hQp : IsPGroup p Q) (hPQ : P ≤ Q) (hQD : Q ≤ D) :
    Q = P := by
  have hPg : IsPGroup p (P.subgroupOf D) := hP.2.1.comap_subtype
  have hQg : IsPGroup p (Q.subgroupOf D) := hQp.comap_subtype
  have hmax : Q.subgroupOf D = P.subgroupOf D :=
    (hPg.toSylow hP.2.2).is_maximal' hQg (Subgroup.subgroupOf_mono D hPQ)
  calc Q = (Q.subgroupOf D).map D.subtype := (Subgroup.map_subgroupOf_eq_of_le hQD).symm
    _ = (P.subgroupOf D).map D.subtype := by rw [hmax]
    _ = P := Subgroup.map_subgroupOf_eq_of_le hP.1

/-- The `H`-normaliser of `P` inside a subgroup `N ≥ P` injects into the `H`-normaliser of `P`;
in particular oddness transfers. -/
theorem odd_card_normalizer_subgroupOf {P H N : Subgroup G} (hPN : P ≤ N)
    (hodd : Odd (Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓ H))) :
    Odd (Nat.card ↥(Subgroup.normalizer (P.subgroupOf N : Set ↥N) ⊓ H.subgroupOf N)) := by
  have hle : ((Subgroup.normalizer (P.subgroupOf N : Set ↥N) ⊓ H.subgroupOf N).map N.subtype)
      ≤ Subgroup.normalizer (P : Set G) ⊓ H := by
    rintro y ⟨x, hx, rfl⟩
    have hx1 : x ∈ Subgroup.normalizer (P.subgroupOf N : Set ↥N) := hx.1
    have hx2 : (x : G) ∈ H := hx.2
    rw [Subgroup.mem_normalizer_iff] at hx1
    refine ⟨?_, hx2⟩
    show ∀ n : G, n ∈ P ↔ (x : G) * n * (x : G)⁻¹ ∈ P
    intro n
    constructor
    · intro hn
      exact (hx1 ⟨n, hPN hn⟩).mp hn
    · intro hn
      have hnN : n ∈ N := by
        have hz' : (x : G)⁻¹ * ((x : G) * n * (x : G)⁻¹) * (x : G) = n := by group
        rw [← hz']
        exact N.mul_mem (N.mul_mem (N.inv_mem x.2) (hPN hn)) x.2
      exact (hx1 ⟨n, hnN⟩).mpr hn
  have hcard : Nat.card ↥(Subgroup.normalizer (P.subgroupOf N : Set ↥N) ⊓ H.subgroupOf N)
      = Nat.card ↥((Subgroup.normalizer (P.subgroupOf N : Set ↥N) ⊓ H.subgroupOf N).map
          N.subtype) :=
    (Subgroup.card_map_of_injective N.subtype_injective).symm
  rw [hcard]
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hle)

/-- A maximal member of the `p`-subgroups of `H` with at least three fixed points, containing a
given subgroup. -/
theorem exists_maxFixesThreeIn_le {p : ℕ} {H Q₀ : Subgroup G}
    (h : ∃ Q : Subgroup G, IsPGroup p Q ∧ Q ≤ H ∧ Work.DoubleTransitivity.FixesThree H Q ∧
      Q₀ ≤ Q) :
    ∃ Q : Subgroup G, Q₀ ≤ Q ∧ Q ≤ H ∧ Work.DoubleTransitivity.MaxFixesThreeIn p H Q := by
  classical
  obtain ⟨Q, hQp, hQH, hQ3, hQ₀Q⟩ := h
  set φ : ℕ → Prop := fun m => ∃ Q : Subgroup G, Q₀ ≤ Q ∧ Q ≤ H ∧ IsPGroup p Q ∧
      Work.DoubleTransitivity.FixesThree H Q ∧ Nat.card ↥Q = m with hφ
  have hcard_le : ∀ R : Subgroup G, Nat.card ↥R ≤ Nat.card G := by
    intro R
    have hdvd : Nat.card ↥R ∣ Nat.card G := by
      have h1 := Subgroup.card_dvd_of_le (show R ≤ (⊤ : Subgroup G) from le_top)
      rwa [Subgroup.card_top] at h1
    exact Nat.le_of_dvd Nat.card_pos hdvd
  obtain ⟨Q₁, hQ₀Q₁, hQ₁H, hQ₁p, hQ₁3, hQ₁card⟩ :=
    Nat.findGreatest_spec (P := φ) (hcard_le Q) ⟨Q, hQ₀Q, hQH, hQp, hQ3, rfl⟩
  refine ⟨Q₁, hQ₀Q₁, hQ₁H, hQ₁p, hQ₁H, hQ₁3, ?_⟩
  intro Q₂ hQ₂p hQ₂H hQ₂3 hQ₁Q₂
  have hle : Nat.card ↥Q₂ ≤ Nat.card ↥Q₁ := by
    have hnotlt : ¬ Nat.card ↥Q₂ > Nat.findGreatest φ (Nat.card G) :=
      fun hlt => Nat.findGreatest_is_greatest hlt (hcard_le Q₂)
        ⟨Q₂, le_trans hQ₀Q₁ hQ₁Q₂, hQ₂H, hQ₂p, hQ₂3, rfl⟩
    rw [hQ₁card]
    omega
  exact (Subgroup.eq_of_le_of_card_ge hQ₁Q₂ hle).ge

/-! ## 2. A four-group inside a strongly embedded subgroup -/

/-- A strongly embedded subgroup of a finite group of `2`-rank `≥ 2` contains two distinct
commuting involutions (a four-group of the ambient group lies inside it). -/
theorem involution_pair_mem_of_stronglyEmbedded {H : Subgroup G}
    (hH : IsStronglyEmbedded H) (hfour : HasFourGroup G) :
    ∃ a b : G, a ∈ H ∧ b ∈ H ∧ orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ a * b = b * a := by
  classical
  obtain ⟨a₀, b₀, ha₀, hb₀, hne₀, hcomm₀⟩ := hfour
  have ha₀_mul : a₀ * a₀ = 1 := by
    have h := pow_orderOf_eq_one a₀; rw [ha₀] at h; simpa [pow_two] using h
  have hb₀_mul : b₀ * b₀ = 1 := by
    have h := pow_orderOf_eq_one b₀; rw [hb₀] at h; simpa [pow_two] using h
  let V : Subgroup G := Subgroup.closure ({a₀, b₀} : Set G)
  have hVmem : ∀ x ∈ V, x = 1 ∨ x = a₀ ∨ x = b₀ ∨ x = a₀ * b₀ :=
    fun x hx => Work.ThreePoints.closure_pair_mem_four ha₀_mul hb₀_mul hcomm₀ x hx
  have hsq : ∀ x ∈ V, x ^ 2 = 1 := by
    intro x hx
    rcases hVmem x hx with h | h | h | h
    · rw [h]; simp
    · rw [h, pow_two]; exact ha₀_mul
    · rw [h, pow_two]; exact hb₀_mul
    · rw [h]
      calc (a₀ * b₀) ^ 2 = a₀ * (b₀ * (a₀ * b₀)) := by rw [pow_two, mul_assoc]
        _ = a₀ * ((b₀ * a₀) * b₀) := by rw [mul_assoc b₀ a₀ b₀]
        _ = a₀ * ((a₀ * b₀) * b₀) := by rw [hcomm₀]
        _ = a₀ * (a₀ * (b₀ * b₀)) := by rw [mul_assoc a₀ b₀ b₀]
        _ = (a₀ * a₀) * (b₀ * b₀) := by rw [← mul_assoc a₀ a₀ (b₀ * b₀)]
        _ = 1 := by rw [ha₀_mul, hb₀_mul, mul_one]
  have hVpg : IsPGroup 2 V := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro y
    refine ⟨1, ?_⟩
    rw [pow_one, ← Subgroup.orderOf_coe y, orderOf_dvd_iff_pow_eq_one]
    exact hsq (y : G) y.2
  obtain ⟨S, hSH⟩ := Work.Reductions.stronglyEmbedded_exists_sylow_le hH
  obtain ⟨T, hVT⟩ := hVpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have key : ∀ v ∈ V, (MulAut.conj g⁻¹) v ∈ H := by
    intro v hv
    have hsm : v ∈ MulAut.conj g • (S : Set G) := by
      rw [← Sylow.coe_smul, hg]
      exact hVT hv
    rw [Set.mem_smul_set] at hsm
    obtain ⟨s, hs, hsv⟩ := hsm
    rw [MulAut.smul_def, MulAut.conj_apply] at hsv
    have hconj : (MulAut.conj g⁻¹) v = s := by rw [MulAut.conj_apply, ← hsv]; group
    rw [hconj]
    exact hSH hs
  refine ⟨(MulAut.conj g⁻¹) a₀, (MulAut.conj g⁻¹) b₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact key a₀ (Subgroup.subset_closure (by simp))
  · exact key b₀ (Subgroup.subset_closure (by simp))
  · rw [(MulAut.conj g⁻¹).orderOf_eq a₀]; exact ha₀
  · rw [(MulAut.conj g⁻¹).orderOf_eq b₀]; exact hb₀
  · intro h
    apply hne₀
    have := congrArg (MulAut.conj g) h
    simpa using this
  · rw [← map_mul, ← map_mul, hcomm₀]

/-! ## 3. Two-transitivity transfers through a quotient -/

/-- If `A ⊴ N`, `A ≤ H` and `N/A` acts `2`-transitively on `(N/A) ⧸ (H/A)`, then `N` acts
`2`-transitively on `N ⧸ H`. -/
theorem isMultiplyPretransitive_quotient {N₀ : Type} [Group N₀] (A H : Subgroup N₀) [A.Normal]
    (hAH : A ≤ H)
    (h2 : MulAction.IsMultiplyPretransitive (N₀ ⧸ A)
      ((N₀ ⧸ A) ⧸ (H.map (QuotientGroup.mk' A))) 2) :
    MulAction.IsMultiplyPretransitive N₀ (N₀ ⧸ H) 2 := by
  classical
  rw [MulAction.is_two_pretransitive_iff] at h2 ⊢
  intro a b c d hab hcd
  let f : N₀ → (N₀ ⧸ A) := fun x => QuotientGroup.mk x
  have hwell : ∀ x y : N₀, QuotientGroup.leftRel H x y →
      QuotientGroup.leftRel (H.map (QuotientGroup.mk' A)) (f x) (f y) := by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy
    rw [QuotientGroup.leftRel_apply]
    show (QuotientGroup.mk' A x)⁻¹ * QuotientGroup.mk' A y ∈ H.map (QuotientGroup.mk' A)
    rw [← map_inv, ← map_mul]
    exact Subgroup.mem_map.mpr ⟨x⁻¹ * y, hxy, rfl⟩
  let ψ : (N₀ ⧸ H) → ((N₀ ⧸ A) ⧸ (H.map (QuotientGroup.mk' A))) := Quotient.map' f hwell
  have hψ : ∀ x : N₀, ψ (QuotientGroup.mk x) = QuotientGroup.mk (f x) :=
    fun x => Quotient.map'_mk'' f hwell x
  have hinj : Function.Injective ψ := by
    intro p q hpq
    revert hpq
    refine Quotient.inductionOn' p (fun x => ?_)
    refine Quotient.inductionOn' q (fun y => ?_)
    intro hpq
    simp only [hψ] at hpq
    rw [QuotientGroup.eq] at hpq
    rw [QuotientGroup.eq]
    have hmem : QuotientGroup.mk' A (x⁻¹ * y) ∈ H.map (QuotientGroup.mk' A) := by
      have h2 : f x = QuotientGroup.mk' A x := rfl
      have h3 : f y = QuotientGroup.mk' A y := rfl
      rw [h2, h3, ← map_inv, ← map_mul] at hpq
      exact hpq
    rw [Subgroup.mem_map] at hmem
    obtain ⟨z, hz, hzx⟩ := hmem
    rw [QuotientGroup.mk'_eq_mk'] at hzx
    obtain ⟨w, hw, hwz⟩ := hzx
    rw [← hwz]
    exact H.mul_mem hz (hAH hw)
  have heq : ∀ (g : N₀) (x : N₀ ⧸ H), ψ (g • x) = QuotientGroup.mk' A g • ψ x := by
    intro g x
    refine Quotient.inductionOn' x (fun y => ?_)
    show ψ (QuotientGroup.mk (g * y)) = QuotientGroup.mk' A g • ψ (QuotientGroup.mk y)
    rw [hψ, hψ]
    show (QuotientGroup.mk (QuotientGroup.mk (g * y)) :
        (N₀ ⧸ A) ⧸ (H.map (QuotientGroup.mk' A)))
      = QuotientGroup.mk (QuotientGroup.mk' A g * QuotientGroup.mk' A y)
    rw [← map_mul]
    rfl
  have hne1 : ψ a ≠ ψ b := fun h => hab (hinj h)
  have hne2 : ψ c ≠ ψ d := fun h => hcd (hinj h)
  obtain ⟨f₀, hf1, hf2⟩ := h2 hne1 hne2
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective A f₀
  refine ⟨g, ?_, ?_⟩
  · have : ψ (g • a) = ψ c := by rw [heq g a, hf1]
    exact hinj this
  · have : ψ (g • b) = ψ d := by rw [heq g b, hf2]
    exact hinj this

/-! ## 4. Peterfalvi Ch. I §4 Lemma 3 (p. 157) -/

/-- **Peterfalvi Ch. I §4 Lemma 3** (p. 157): if `G` acts `2`-transitively on `Ω = G ⧸ H`,
`t ∉ H` is an involution, `P` is a `p`-Sylow of `D = H ∩ H^t` (with `p ≠ 2`) and `|N_H(P)|` is
odd, then `P` is a `p`-Sylow of `G`. -/
theorem sec4_lemma3 (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {H : Subgroup G} (hH : IsStronglyEmbedded H)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h2tr : MulAction.IsMultiplyPretransitive G (G ⧸ H) 2)
    {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    {P : Subgroup G} (hP : IsSylowSubgroupOf p P (twoPoint H t))
    (hodd : Odd (Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓ H))) :
    IsSylowSub p P := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hp2' : 2 < p := by have h := hp.two_le; omega
  have hPD : P ≤ twoPoint H t := hP.1
  have hPleH : P ≤ H := hPD.trans inf_le_left
  -- the point `pt H` and the point `mk t` are fixed by `P` (and are distinct)
  have hpt : (pt H : G ⧸ H) ∈ fixedPts H P := by
    rw [Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux,
      Work.DoubleTransitivity.Sec4.stabilizer_pt_eq]
    exact hPleH
  have hstab : MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H) = conj t H := by
    rw [show (QuotientGroup.mk t : G ⧸ H) = t • (pt H : G ⧸ H) from
      (Work.DoubleTransitivity.smul_pt t H).symm,
      MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      Work.DoubleTransitivity.Sec4.stabilizer_pt_eq]
  have hmt : (QuotientGroup.mk t : G ⧸ H) ∈ fixedPts H P := by
    rw [Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux, hstab]
    exact hPD.trans inf_le_right
  have hne : (pt H : G ⧸ H) ≠ (QuotientGroup.mk t : G ⧸ H) := by
    intro h
    exact htH (Work.DoubleTransitivity.mk_one_eq_iff.mp h.symm)
  have hsubpair : ({pt H, (QuotientGroup.mk t : G ⧸ H)} : Set (G ⧸ H)) ⊆ fixedPts H P := by
    intro ω hω
    rcases hω with rfl | rfl
    · exact hpt
    · exact hmt
  have h2le : 2 ≤ (fixedPts H P).ncard :=
    (Set.ncard_pair hne).symm.trans_le (Set.ncard_le_ncard hsubpair)
  by_cases h3 : 3 ≤ (fixedPts H P).ncard
  · -- `P` is maximal among the `p`-subgroups of `H` with `≥ 3` fixed points
    exfalso
    have hmaxIn : Work.DoubleTransitivity.MaxFixesThreeIn p H P := by
      refine ⟨hP.2.1, hPleH, h3, ?_⟩
      intro Q hQp hQH hQ3 hPQ
      have hQ3' : 3 ≤ (fixedPts H Q).ncard := hQ3
      -- two distinct fixed points of `Q`
      obtain ⟨ω₁, hω₁, -⟩ :=
        Set.exists_ne_of_one_lt_ncard (s := fixedPts H Q) (by omega) (pt H)
      obtain ⟨ω₂, hω₂, hω₂ne⟩ :=
        Set.exists_ne_of_one_lt_ncard (s := fixedPts H Q) (by omega) ω₁
      have hQle : Q ≤ MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂ :=
        le_inf (Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux.mp hω₁)
          (Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux.mp hω₂)
      -- the two-point stabiliser of `(ω₁,ω₂)` is a conjugate of `D = Stab(pt H) ⊓ Stab(mk t)`
      obtain ⟨g, hg1, hg2⟩ :=
        (MulAction.is_two_pretransitive_iff.mp h2tr) hne hω₂ne.symm
      have hDconj : MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂
          = conj g (twoPoint H t) := by
        rw [Work.DoubleTransitivity.App2.stabilizer_inf_conj hg1 hg2,
          Work.DoubleTransitivity.Sec4.stabilizer_pt_eq, hstab]
      -- `P` is a Sylow of that two-point stabiliser
      have hPsyl' : IsSylowSubgroupOf p P
          (MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂) := by
        have hconjP : IsSylowSubgroupOf p (conj g P)
            (MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂) := by
          rw [hDconj]
          exact Work.DoubleTransitivity.App2.isSylowSubgroupOf_conj hP g
        exact Work.DoubleTransitivity.App2.isSylowSubgroupOf_of_le_conj hconjP
          (hPQ.trans hQle) hP.2.1
      exact le_of_eq (eq_of_isSylowSubgroupOf_le hPsyl' hQp hPQ hQle)
    obtain ⟨-, hEven⟩ := Work.DoubleTransitivity.Sec4.prop2 hBrSz hH hp hp2 hmaxIn
    exact (Nat.not_even_iff_odd.mpr hodd) hEven
  · -- `|Ω_P| = 2`: Appendix II (1) gives a `p`-Sylow `Q ⊇ P` of `H` with the same fixed points
    have hle2 : (fixedPts H P).ncard ≤ 2 := by omega
    have hfixpair : ({pt H, (QuotientGroup.mk t : G ⧸ H)} : Set (G ⧸ H)) = fixedPts H P := by
      refine Set.eq_of_subset_of_ncard_le hsubpair ?_
      rw [Set.ncard_pair hne]
      exact hle2
    have hfix : fixedBySub P = ({pt H, (QuotientGroup.mk t : G ⧸ H)} : Set (G ⧸ H)) :=
      hfixpair.symm
    obtain ⟨Q, hPQ, hQsyl, hfixQ, hQsylG⟩ :=
      Work.DoubleTransitivity.App2.app2_1 hP.2.1 hne hfix
    have hQg : IsSylowSub p Q := hQsylG hp2'
    have hQstab : Q ≤ MulAction.stabilizer G (pt H) := hQsyl.1
    rw [Work.DoubleTransitivity.Sec4.stabilizer_pt_eq] at hQstab
    have hQD : Q ≤ twoPoint H t := by
      refine le_inf hQstab ?_
      rw [← hstab]
      have hb : (QuotientGroup.mk t : G ⧸ H) ∈ fixedBySub Q := by
        rw [hfixQ]; simp
      exact fun q hq => MulAction.mem_stabilizer_iff.mpr ((mem_fixedBySub.mp hb) q hq)
    have hPQeq : P = Q := (eq_of_isSylowSubgroupOf_le hP hQg.1 hPQ hQD).symm
    rwa [hPQeq]

end Helpers

/-- **Peterfalvi Ch. I §5 Proposition 1** (p. 158). -/
theorem inductionStep {G : Type} [Group G] [Finite G]
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (h4 : Submission.Blueprint.HasFourGroup G)
    (hInd : Work.DoubleTransitivity.ThmAForBelow (Nat.card G))
    {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    {A : Subgroup G} (hAne : A ≠ ⊥) (hAle : A ≤ Submission.Blueprint.twoPoint H t)
    (hAn : Submission.Blueprint.twoPoint H t ≤ Subgroup.normalizer (A : Set G))
    (hAt : t ∈ Subgroup.normalizer (A : Set G))
    (hu : ∃ u ∈ Submission.Blueprint.involutions (H : Set G),
      u ∈ Subgroup.normalizer (A : Set G)) :
    Submission.Blueprint.IsTwoTransitiveOn H := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  -- Ch. I §5 Lemma 1: an odd prime `p` with `(D,H) ∉ 𝓡_p`
  obtain ⟨-, p, hp, hp2, hpreg⟩ := lemma1 hH h4 ht htH
  haveI : Fact p.Prime := ⟨hp⟩
  -- a `p`-Sylow `P` of `D = H ∩ H^t`
  obtain ⟨P, hPsyl⟩ :=
    Work.DoubleTransitivity.Sec4.exists_isSylowSubgroupOf_of_subgroup (p := p)
      (Submission.Blueprint.twoPoint H t)
  have hPleD : P ≤ Submission.Blueprint.twoPoint H t := hPsyl.1
  have hPp : IsPGroup p P := hPsyl.2.1
  have hPleH : P ≤ H := hPleD.trans inf_le_left
  have hoddP : Odd (Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓ H)) := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    exact hpreg ⟨P, hPsyl, hev⟩
  by_cases hNtop : Subgroup.normalizer (A : Set G) = ⊤
  · -- ## Case 1: `A ⊴ G`.  Apply the induction hypothesis to `G ⧸ A`.
    have hAN : A.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    haveI : A.Normal := hAN
    have hAleH : A ≤ H := hAle.trans inf_le_left
    have hDodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) := hH.2.2 t htH
    have hAodd : Odd (Nat.card ↥A) := Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le hAle)
    have hcard : Nat.card (G ⧸ A) < Nat.card G := Work.Reductions.card_quotient_lt A hAne
    have hfourQ : HasFourGroup (G ⧸ A) := Work.Reductions.hasFourGroup_quotient A h4 hAodd
    have hse : IsStronglyEmbedded (H.map (QuotientGroup.mk' A)) :=
      Work.ThreePoints.isStronglyEmbedded_map_quotient A hAodd hAleH hH
    have h2tr := hInd (G ⧸ A) hcard hfourQ (H.map (QuotientGroup.mk' A)) hse
    exact isMultiplyPretransitive_quotient A H hAleH h2tr
  · -- ## Case 2: `N = N_G(A)` is proper.  Apply the induction hypothesis to `N`.
    let N : Subgroup G := Subgroup.normalizer (A : Set G)
    have htN : t ∈ N := hAt
    have hDleN : Submission.Blueprint.twoPoint H t ≤ N := hAn
    have hPleN : P ≤ N := hPleD.trans hDleN
    -- `|N| < |G|`
    have hNlt : Nat.card ↥N < Nat.card G := by
      have hlt : N < ⊤ := lt_top_iff_ne_top.mpr
        (fun h => hNtop (show Subgroup.normalizer (A : Set G) = ⊤ from h))
      simpa using Subgroup.card_lt_of_lt hlt
    -- every involution of `H` lies in `N`
    have hInvH : ∀ v ∈ Submission.Blueprint.involutions (H : Set G), v ∈ N := by
      intro v hv
      obtain ⟨u, hu, huN⟩ := hu
      have hbender : Work.DoubleTransitivity.IsBender H :=
        (Work.DoubleTransitivity.isStronglyEmbedded_iff H).mp hH |>.2
      obtain ⟨htrans, -, -⟩ := Work.DoubleTransitivity.Sec2.prop2 hbender hH.1 ht htH
      obtain ⟨d, hdD, hd⟩ := htrans u v hu hv
      rw [← hd]
      exact N.mul_mem (N.mul_mem (N.inv_mem (hDleN hdD)) huN) (hDleN hdD)
    -- `H ⊓ N` is strongly embedded in `N`
    have hHN : IsStronglyEmbedded (H.subgroupOf N) := by
      have hsub : (H ⊓ N).subgroupOf N = H.subgroupOf N := by
        ext x
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
      have hne : H ⊓ N ≠ N := by
        intro h
        have htt : t ∈ H ⊓ N := by rw [h]; exact htN
        exact htH htt.1
      have hev : Even (Nat.card ↥(H ⊓ N)) := by
        obtain ⟨u, hu, huN⟩ := hu
        have huord : orderOf (⟨u, ⟨hu.1, huN⟩⟩ : ↥(H ⊓ N)) = 2 := by
          rw [← Subgroup.orderOf_coe]; exact hu.2
        have hdvd := orderOf_dvd_natCard (G := ↥(H ⊓ N)) (⟨u, ⟨hu.1, huN⟩⟩ : ↥(H ⊓ N))
        rw [huord] at hdvd
        exact even_iff_two_dvd.mpr hdvd
      rw [← hsub]
      exact Work.Reductions.stronglyEmbedded_subgroupOf hH hne hev
    -- `N` contains a four-group
    have hFourN : HasFourGroup ↥N := by
      obtain ⟨a, b, haH, hbH, ha2, hb2, habne, habcomm⟩ :=
        involution_pair_mem_of_stronglyEmbedded hH h4
      exact Work.Reductions.HasFourGroupIn.to_subgroup
        ⟨a, b, hInvH a ⟨haH, ha2⟩, hInvH b ⟨hbH, hb2⟩, ha2, hb2, habne, habcomm⟩
    -- the induction hypothesis in `N`
    have h2tr : MulAction.IsMultiplyPretransitive ↥N (↥N ⧸ H.subgroupOf N) 2 :=
      hInd ↥N hNlt hFourN (H.subgroupOf N) hHN
    -- Ch. I §4 Lemma 3 in `N`: `P` is a `p`-Sylow of `N`
    have hPsylN : IsSylowSub p (P.subgroupOf N) := by
      refine sec4_lemma3 (G := ↥N) (H := H.subgroupOf N) hBrSz hHN hp hp2 h2tr
        (t := ⟨t, htN⟩) ?_ ?_ ?_ ?_
      · rw [← Subgroup.orderOf_coe]; exact ht
      · intro h
        exact htH (Subgroup.mem_subgroupOf.mp h)
      · rw [twoPoint_subgroupOf htN]
        exact isSylowSubgroupOf_subgroupOf hDleN hPsyl
      · exact odd_card_normalizer_subgroupOf hPleN hoddP
    -- `|Ω_P| = 2`
    have hfixed2 : (fixedPts H P).ncard = 2 := by
      have h2le : 2 ≤ (fixedPts H P).ncard := by
        have hpt : (pt H : G ⧸ H) ∈ fixedPts H P := by
          rw [Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux,
            Work.DoubleTransitivity.Sec4.stabilizer_pt_eq]
          exact hPleH
        have hstab : MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H) = conj t H := by
          rw [show (QuotientGroup.mk t : G ⧸ H) = t • (pt H : G ⧸ H) from
            (Work.DoubleTransitivity.smul_pt t H).symm,
            MulAction.stabilizer_smul_eq_stabilizer_map_conj,
            Work.DoubleTransitivity.Sec4.stabilizer_pt_eq]
        have hmt : (QuotientGroup.mk t : G ⧸ H) ∈ fixedPts H P := by
          rw [Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux, hstab]
          exact hPleD.trans inf_le_right
        have hne : (pt H : G ⧸ H) ≠ (QuotientGroup.mk t : G ⧸ H) := by
          intro h
          exact htH (Work.DoubleTransitivity.mk_one_eq_iff.mp h.symm)
        have hsub : ({pt H, (QuotientGroup.mk t : G ⧸ H)} : Set (G ⧸ H)) ⊆ fixedPts H P := by
          intro ω hω
          rcases hω with rfl | rfl
          · exact hpt
          · exact hmt
        exact (Set.ncard_pair hne).symm.trans_le (Set.ncard_le_ncard hsub)
      have hnot3 : ¬ 3 ≤ (fixedPts H P).ncard := by
        intro h3
        -- a maximal `p`-subgroup `S ≤ H` with `≥ 3` fixed points containing `P`
        obtain ⟨S, hPS, hSH, hSIn⟩ :=
          exists_maxFixesThreeIn_le (p := p) (H := H) (Q₀ := P) ⟨P, hPp, hPleH, h3, le_rfl⟩
        obtain ⟨-, hEven⟩ := Work.DoubleTransitivity.Sec4.prop2 hBrSz hH hp hp2 hSIn
        -- an involution `u ∈ N_G(S) ⊓ H`
        obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card'
          (G := ↥(Subgroup.normalizer (S : Set G) ⊓ H)) 2 (even_iff_two_dvd.mp hEven)
        have huG : orderOf ((u : G)) = 2 := (Subgroup.orderOf_coe u).trans hu
        have huNormS : (u : G) ∈ Subgroup.normalizer (S : Set G) := u.2.1
        have huH : (u : G) ∈ H := u.2.2
        have huN : (u : G) ∈ N := hInvH _ ⟨huH, huG⟩
        -- `S ⊓ N = P`
        have hSN : S ⊓ N = P := by
          have hR : IsPGroup p ((S ⊓ N).subgroupOf N) :=
            hSIn.1.to_inf_left.comap_subtype
          have hle : P.subgroupOf N ≤ (S ⊓ N).subgroupOf N :=
            Subgroup.subgroupOf_mono N (le_inf hPS hPleN)
          have hmax : (S ⊓ N).subgroupOf N = P.subgroupOf N :=
            (hPsylN.1.toSylow hPsylN.2).is_maximal' hR hle
          calc S ⊓ N = ((S ⊓ N).subgroupOf N).map N.subtype :=
                (Subgroup.map_subgroupOf_eq_of_le inf_le_right).symm
            _ = (P.subgroupOf N).map N.subtype := by rw [hmax]
            _ = P := Subgroup.map_subgroupOf_eq_of_le hPleN
        -- `u` normalises `P`, contradicting the oddness of `|N_H(P)|`
        have huNormP : (u : G) ∈ Subgroup.normalizer (P : Set G) := by
          rw [← hSN]
          rw [Subgroup.mem_normalizer_iff]
          intro z
          rw [Subgroup.mem_normalizer_iff] at huNormS
          constructor
          · intro hz
            have hz1 : z ∈ S := hz.1
            have hz2 : z ∈ N := hz.2
            exact ⟨(huNormS z).mp hz1,
              N.mul_mem (N.mul_mem huN hz2) (N.inv_mem huN)⟩
          · intro hz
            have hz1 : (u : G) * z * (u : G)⁻¹ ∈ S := hz.1
            have hz2 : (u : G) * z * (u : G)⁻¹ ∈ N := hz.2
            have hzN : z ∈ N := by
              have hz' : (u : G)⁻¹ * ((u : G) * z * (u : G)⁻¹) * (u : G) = z := by group
              rw [← hz']
              exact N.mul_mem (N.mul_mem (N.inv_mem huN) hz2) huN
            exact ⟨(huNormS z).mpr hz1, hzN⟩
        have h2dvd : 2 ∣ Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓ H) := by
          have hmem : (u : G) ∈ Subgroup.normalizer (P : Set G) ⊓ H := ⟨huNormP, huH⟩
          have hord : orderOf (⟨(u : G), hmem⟩ :
              ↥(Subgroup.normalizer (P : Set G) ⊓ H)) = 2 := by
            rw [← Subgroup.orderOf_coe]; exact huG
          have h := orderOf_dvd_natCard (G := ↥(Subgroup.normalizer (P : Set G) ⊓ H))
            (⟨(u : G), hmem⟩ : ↥(Subgroup.normalizer (P : Set G) ⊓ H))
          rwa [hord] at h
        exact (Nat.not_even_iff_odd.mpr hoddP) (even_iff_two_dvd.mpr h2dvd)
      exact le_antisymm (by omega) h2le
    -- Ch. I §4 Prop. 1: a `p`-subgroup with exactly two fixed points makes `G` `2`-transitive
    have hRp : ¬ Work.DoubleTransitivity.Sec4.Rp p H := fun hRp =>
      (Work.DoubleTransitivity.Sec4.rp_no_two_fixed_pts hBrSz hH hp hp2
        (Work.DoubleTransitivity.Sec4.lemma2_part1 hBrSz hH hp hp2)) hRp P hPp hfixed2
    exact Work.DoubleTransitivity.Sec4.not_rp_twoTransitive hBrSz hH hp hp2
      (Work.DoubleTransitivity.Sec4.lemma2_part1 hBrSz hH hp hp2) hRp

end Work.DoubleTransitivity.Sec5
