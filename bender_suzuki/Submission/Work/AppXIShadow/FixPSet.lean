import Mathlib
import Submission.Work.AppXIShadow.Basic
import Submission.Work.AppXIShadow.AppII7

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.AppXIShadow.FixPSet` — the `C_G(P)`-set `fixP H P` and the regular subgroup `C_Q(P)`

Auxiliary API for the assembly `Work.AppXIShadow.nearFieldAppXIPropPlus_of`: the description of
`fixP H P` as `{∞} ∪ C_Q(P) • (t • ∞)` (A1), the freeness of the `C_Q(P)`-action away from `∞`,
transitivity of `C_G(P)`, and the description of `KerIn H Q P t` as the kernel of the action on
`fixP H P` (A2).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.AppXIShadow

open Work.ThmF.ChV3 Work.ThmF
open Work.ZassenhausTwoGroup.IsTIQ

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}

/-- For `y ∈ C_Q(P)`, the point `y • (t • ∞)` is fixed by `P`. -/
theorem CQ_smul_t_mem_fixP (c : CtxF H Q t s r P) {y : G} (hy : y ∈ CQ Q P) :
    y • ((t : G) : G ⧸ H) ∈ fixP H P := by
  intro x hx
  have hyx : x * y = y * x := Subgroup.mem_centralizer_iff.mp hy.2 x hx
  rw [← mul_smul, hyx, mul_smul, smul_t_eq_t c hx]

/-- `fixP H P` is `{∞}` together with the `C_Q(P)`-translates of `t • ∞` (A1). -/
theorem fixP_eq_base_or_exists (c : CtxF H Q t s r P) {ω : G ⧸ H} (hω : ω ∈ fixP H P) :
    ω = ((1 : G) : G ⧸ H) ∨ ∃ y ∈ CQ Q P, y • ((t : G) : G ⧸ H) = ω := by
  by_cases h : ω = ((1 : G) : G ⧸ H)
  · exact Or.inl h
  · obtain ⟨⟨y, hy⟩, hyω, -⟩ := (CQ_regular_on_fixP c).2 ω hω h
    exact Or.inr ⟨y, hy, hyω⟩

/-- `C_Q(P)` acts freely on `fixP H P ∖ {∞}` (A1, uniqueness). -/
theorem CQ_free_on_fixP (c : CtxF H Q t s r P) {y : G} (hy : y ∈ CQ Q P) {ω : G ⧸ H}
    (hω : ω ∈ fixP H P) (hωa : ω ≠ ((1 : G) : G ⧸ H)) (hfix : y • ω = ω) : y = 1 := by
  rcases fixP_eq_base_or_exists c hω with h | ⟨y', hy', hy'ω⟩
  · exact absurd h hωa
  have hne : y' • ((t : G) : G ⧸ H) ≠ ((1 : G) : G ⧸ H) := by rw [hy'ω]; exact hωa
  obtain ⟨u, hu, huniq⟩ :=
    (CQ_regular_on_fixP c).2 (y' • ((t : G) : G ⧸ H)) (CQ_smul_t_mem_fixP c hy') hne
  have h₂ : ((⟨y * y', (CQ Q P).mul_mem hy hy'⟩ : ↥(CQ Q P)) : G) •
      ((t : G) : G ⧸ H) = y' • ((t : G) : G ⧸ H) := by
    show (y * y') • ((t : G) : G ⧸ H) = y' • ((t : G) : G ⧸ H)
    rw [mul_smul, hy'ω, hfix]
  have h₃ : (⟨y * y', (CQ Q P).mul_mem hy hy'⟩ : ↥(CQ Q P)) = ⟨y', hy'⟩ :=
    (huniq _ h₂).trans (huniq ⟨y', hy'⟩ rfl).symm
  have h₄ : y * y' = y' := congrArg Subtype.val h₃
  exact mul_right_cancel (by rw [h₄, one_mul])

/-- Every fixed point of `P` is a translate of the base point by an element of `C_G(P)`. -/
theorem exists_centP_smul_base (c : CtxF H Q t s r P) (ω : ↥(fixP H P)) :
    ∃ g : ↥(centP P), g • fixPBaseC c = ω := by
  by_cases h : (ω : G ⧸ H) = ((1 : G) : G ⧸ H)
  · refine ⟨1, Subtype.ext ?_⟩
    rw [one_smul]
    exact (fixPBase_coe H P (P_le_H c)).trans h.symm
  · rcases fixP_eq_base_or_exists c ω.2 with h0 | ⟨y, hy, hyω⟩
    · exact absurd h0 h
    · refine ⟨⟨y * t, Subgroup.mul_mem _ (CQ_le_CGP c hy) (t_mem_centP c)⟩, Subtype.ext ?_⟩
      rw [fixP_smul_coe, fixPBase_coe]
      show (y * t : G) • ((1 : G) : G ⧸ H) = (ω : G ⧸ H)
      rw [mul_smul, Work.ThreePoints.smul_mk, mul_one]
      exact hyω

/-- `C_G(P)` is transitive on `fixP H P`. -/
theorem isPretransitive_fixP (c : CtxF H Q t s r P) :
    MulAction.IsPretransitive ↥(centP P) ↥(fixP H P) := by
  refine ⟨fun ω ω' => ?_⟩
  obtain ⟨g, hg⟩ := exists_centP_smul_base c ω
  obtain ⟨g', hg'⟩ := exists_centP_smul_base c ω'
  have h1 : g⁻¹ • ω = fixPBaseC c := by
    rw [← hg, inv_smul_smul]
  exact ⟨g' * g⁻¹, by rw [mul_smul, h1, hg']⟩

/-- `KerIn H Q P t ≤ fixPStab c`: the kernel fixes the base point. -/
theorem KerIn_le_fixPStab (c : CtxF H Q t s r P) : KerIn H Q P t ≤ fixPStab c := by
  intro x hx
  rw [MulAction.mem_stabilizer_iff]
  refine Subtype.ext ?_
  rw [fixP_smul_coe, fixPBase_coe]
  show (x : G) • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
  rw [Work.ThreePoints.smul_mk, QuotientGroup.eq]
  have hxH : (x : G) ∈ H := (Ker_le_twoPoint c (Subgroup.mem_subgroupOf.mp hx)).1
  simpa using H.inv_mem hxH

/-- `KerIn H Q P t` is the kernel of the action of `C_G(P)` on `fixP H P` (A2). -/
theorem mem_KerIn_iff (c : CtxF H Q t s r P) {g : ↥(centP P)} :
    g ∈ KerIn H Q P t ↔ ∀ ω : ↥(fixP H P), g • ω = ω := by
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hg ω
    refine Subtype.ext ?_
    exact (fixP_kernel_iff c g.2).mpr hg ω.1 ω.2
  · intro hg
    exact (fixP_kernel_iff c g.2).mp (fun ω hω => congrArg Subtype.val (hg ⟨ω, hω⟩))

/-- `KerIn H Q P t` is normal in `C_G(P)`. -/
theorem KerIn_normal (c : CtxF H Q t s r P) : (KerIn H Q P t).Normal := by
  refine Subgroup.Normal.mk fun n hn g => ?_
  rw [mem_KerIn_iff c] at hn ⊢
  intro ω
  have h1 : n • (g⁻¹ • ω) = g⁻¹ • ω := hn (g⁻¹ • ω)
  calc (g * n * g⁻¹) • ω = g • (n • (g⁻¹ • ω)) := by rw [mul_smul, mul_smul]
    _ = g • (g⁻¹ • ω) := by rw [h1]
    _ = ω := by rw [← mul_smul, mul_inv_cancel, one_smul]

end Work.AppXIShadow
