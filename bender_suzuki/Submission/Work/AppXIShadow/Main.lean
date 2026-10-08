import Mathlib
import Submission.Work.AppXIShadow.Defs
import Submission.Work.AppXIShadow.Basic
import Submission.Work.AppXIShadow.AppII7
import Submission.Work.AppXIShadow.FixPSet
import Submission.Work.AppXIShadow.app3_regular_normal
import Submission.Work.AppXIShadow.CGP_stronglyEmbedded_coatom
import Submission.Work.AppXIShadow.s_mul_t_mem_R
import Submission.Work.AppXIShadow.orderOf_s_mul_t_prime_v2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.AppXIShadow.Main` — App. XI Prop. 1 in the standing context of Ch. V §3

The assembly of `Work.AppXIShadow.NearFieldAppXIPropPlus` (= App. XI Prop. 1's shadow plus the
`[R,R] ≤ N` clause of App. III (2)) from

* A1/A2 (`AppII7`): `C_Q(P)` is regular on `fixP H P ∖ {∞}`, and the kernel of the action of
  `C_G(P)` on `fixP H P` is `Ker H Q P t`;
* A3 (`app3_regular_normal`) applied to `F = C_G(P)`, `Ω = fixP H P`, which produces the normal
  subgroup `R ⊴ C_G(P)` containing the kernel, abelian modulo the kernel, meeting the point
  stabiliser in the kernel, and transitive;
* A4 (`CGP_stronglyEmbedded_coatom`): hypothesis check for A3;
* `s_mul_t_mem_R` and `orderOf_s_mul_t_prime_v2`: `st ∈ R` and the numeric clauses
  `|C_Q(P)| + 1 = o(st)^m`, `|R| = |Ker| · o(st)^m`, `o(st)` prime.

The final clause `y x y⁻¹ x⁻¹ ∈ N → y = 1` for `y ∈ C_Q(P)` and `x ∈ R ∖ N` uses the freeness of
the `C_Q(P)`-action on `fixP H P ∖ {∞}` (`FixPSet`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.AppXIShadow

open Work.ThmF.ChV3 Work.ThmF

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}

/-- The image of the subgroup `R ≤ ↥(C_G(P))` inside `G`. -/
abbrev mapCentP (P : Subgroup G) (R : Subgroup ↥(centP P)) : Subgroup G :=
  R.map (centP P).subtype

/-- **App. XI Prop. 1 (the near-field shadow) in the standing context of Ch. V §3**, proved from
Feit–Thompson, Brauer–Suzuki, Ch. II §4 and Thompson–Frobenius. -/
theorem nearFieldAppXIPropPlus_of (hFT : FeitThompsonProp) (hBrSz : BrauerSuzukiProp)
    (hC4 : ChIIFourProp) (hTh : ThompsonFrobeniusProp) : NearFieldAppXIPropPlus := by
  intro G _ _ H Q t s r P c
  -- ## A4: the hypotheses of A3 for `F = C_G(P)` acting on `fixP H P`
  have hSE : IsStronglyEmbedded (fixPStab c) := by
    rw [fixPStab_eq c]; exact (CGP_stronglyEmbedded_coatom c).1
  have hCA : IsCoatom (fixPStab c) := by
    rw [fixPStab_eq c]; exact (CGP_stronglyEmbedded_coatom c).2
  -- ## A3
  obtain ⟨R, hRn, hker, hder, hstab_le, htr⟩ :=
    app3_regular_normal (fixPBaseC c) (isPretransitive_fixP c) (by simpa using hSE)
      (by simpa using hCA) c.F1 hBrSz hFT
  have hKle : KerIn H Q P t ≤ R := fun g hg => hker g ((mem_KerIn_iff c).mp hg)
  have hRK : ⁅R, R⁆ ≤ KerIn H Q P t := by
    rw [Subgroup.commutator_le]
    exact fun x hx y hy => (mem_KerIn_iff c).mpr (hder x hx y hy)
  have hstab : R ⊓ fixPStab c = KerIn H Q P t := by
    refine le_antisymm ?_ (le_inf hKle (KerIn_le_fixPStab c))
    intro x hx
    exact (mem_KerIn_iff c).mpr (hstab_le x hx.1 (MulAction.mem_stabilizer_iff.mp hx.2))
  -- ## A5
  have hst : sMulT c ∈ R := s_mul_t_mem_R c R hRn hKle hRK hstab htr
  obtain ⟨hprime, m, hm, hcq, hcard⟩ :=
    orderOf_s_mul_t_prime_v2 c R hRn hKle hRK hstab htr hst
  -- ## the cardinality of `Ker` inside `C_G(P)`
  have hcardK : Nat.card ↥(KerIn H Q P t) = Nat.card ↥(Ker H Q P t) := by
    rw [← Subgroup.card_map_of_injective (centP P).subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Ker_le_CGP c)]
  refine ⟨m, R.map (centP P).subtype, Ker H Q P t, rfl, hm, hprime, ?_, ?_, ?_, ?_, ?_, hcq,
    ?_, ?_⟩
  · -- `Ker H Q P t ≤ R.map (C_G(P)).subtype`
    intro x hx
    exact ⟨⟨x, Ker_le_CGP c hx⟩, hKle hx, rfl⟩
  · -- `R.map (C_G(P)).subtype ≤ C_G(P)`
    rintro x ⟨x₀, -, rfl⟩
    exact x₀.2
  · -- `C_G(P) ≤ N_G(R.map (C_G(P)).subtype)`
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨x₀, hx₀, rfl⟩
      exact ⟨(⟨g, hg⟩ * x₀ * ⟨g, hg⟩⁻¹ : ↥(centP P)), hRn.conj_mem x₀ hx₀ ⟨g, hg⟩, rfl⟩
    · rintro ⟨x₀, hx₀, hx₀eq⟩
      have hx₀eq' : (x₀ : G) = g * x * g⁻¹ := hx₀eq
      refine ⟨(⟨g, hg⟩ : ↥(centP P))⁻¹ * x₀ * (⟨g, hg⟩ : ↥(centP P)), ?_, ?_⟩
      · simpa using hRn.conj_mem x₀ hx₀ ((⟨g, hg⟩ : ↥(centP P))⁻¹)
      · show (g : G)⁻¹ * (x₀ : G) * (g : G) = x
        rw [hx₀eq']; group
  · -- `C_G(P) ≤ N_G(Ker H Q P t)`
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact Subgroup.mem_subgroupOf.mp ((KerIn_normal c).conj_mem
        (⟨x, Ker_le_CGP c hx⟩ : ↥(centP P)) hx ⟨g, hg⟩)
    · intro hx
      have hx' : (⟨g * x * g⁻¹, Ker_le_CGP c hx⟩ : ↥(centP P)) ∈ KerIn H Q P t := hx
      have h2 : g⁻¹ * (g * x * g⁻¹) * g ∈ Ker H Q P t := by
        have h3 := Subgroup.mem_subgroupOf.mp
          ((KerIn_normal c).conj_mem (⟨g * x * g⁻¹, Ker_le_CGP c hx⟩ : ↥(centP P)) hx'
            ((⟨g, hg⟩ : ↥(centP P))⁻¹))
        simpa using h3
      have heq : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [heq]
      exact h2
  · -- `|R.map (C_G(P)).subtype| = |Ker| · o(st)^m`
    rw [Subgroup.card_map_of_injective (centP P).subtype_injective, ← hcardK]
    exact hcard
  · -- the fixed-point-free clause
    rintro x ⟨x₀, hx₀R, rfl⟩ hxKer y hy hyK
    by_contra hy1
    have hXK : x₀ ∉ KerIn H Q P t := fun h => hxKer (Subgroup.mem_subgroupOf.mp h)
    have hωne : (x₀ • fixPBaseC c : ↥(fixP H P)) ≠ fixPBaseC c := by
      intro hcon
      exact hXK (hstab ▸ ⟨hx₀R, MulAction.mem_stabilizer_iff.mpr hcon⟩)
    let Y : ↥(centP P) := ⟨y, CQ_le_CGP c hy⟩
    have hYfix : Y • fixPBaseC c = fixPBaseC c := by
      exact Subtype.ext (by
        rw [fixP_smul_coe, fixPBase_coe, Work.ThreePoints.smul_mk, QuotientGroup.eq]
        simpa using H.inv_mem (CQ_le_H c hy))
    let K : ↥(centP P) := ⟨y * x₀ * y⁻¹ * x₀⁻¹, Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (CQ_le_CGP c hy) x₀.2)
        (Subgroup.inv_mem _ (CQ_le_CGP c hy))) (Subgroup.inv_mem _ x₀.2)⟩
    have hKK : K ∈ KerIn H Q P t := hyK
    have hYX : Y * x₀ = K * x₀ * Y := by
      refine Subtype.ext ?_
      show y * (x₀ : G) = (y * (x₀ : G) * y⁻¹ * (x₀ : G)⁻¹) * (x₀ : G) * y
      group
    have hfixω : Y • (x₀ • fixPBaseC c) = x₀ • fixPBaseC c :=
      calc Y • (x₀ • fixPBaseC c) = (Y * x₀) • fixPBaseC c := by rw [mul_smul]
        _ = (K * x₀ * Y) • fixPBaseC c := by rw [hYX]
        _ = K • (x₀ • (Y • fixPBaseC c)) := by rw [mul_smul, mul_smul]
        _ = K • (x₀ • fixPBaseC c) := by rw [hYfix]
        _ = x₀ • fixPBaseC c := (mem_KerIn_iff c).mp hKK _
    have hY1 : Y = 1 := by
      by_contra hne1
      have hne1' : y ≠ 1 := fun h => hne1 (Subtype.ext h)
      have hfixG : y • ((x₀ • fixPBaseC c : ↥(fixP H P)) : G ⧸ H)
          = ((x₀ • fixPBaseC c : ↥(fixP H P)) : G ⧸ H) := by
        simpa using congrArg Subtype.val hfixω
      have hωneG : ((x₀ • fixPBaseC c : ↥(fixP H P)) : G ⧸ H) ≠ ((1 : G) : G ⧸ H) := by
        intro hcon
        exact hωne (Subtype.ext (hcon.trans (fixPBase_coe H P (P_le_H c)).symm))
      exact hne1' (CQ_free_on_fixP c hy (x₀ • fixPBaseC c).2 hωneG hfixG)
    exact hy1 (by simpa [Y] using congrArg Subtype.val hY1)
  · -- `[R.map (C_G(P)).subtype, ...] ≤ Ker H Q P t`
    rintro x ⟨x₀, hx₀, rfl⟩ y ⟨y₀, hy₀, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (Subgroup.commutator_le.mp hRK x₀ hx₀ y₀ hy₀)

end Work.AppXIShadow
