/-
# `Work.NormalComplement.Sec5Fix.P2a.Nq`

The group `𝒩 ⧸ KK` (`𝒩 = N_G(V)`, `KK` the kernel of the action of `𝒩` on `Ω_V = fixedPts H V`)
to which Appendix III is applied in the proof of Peterfalvi I Ch. III §5 Prop. 2 (a), together with
the basic API: the kernel `KKg` as a subgroup of the ambient group, its normality, the
identification of the point stabiliser, faithfulness and transitivity of the action.
-/
import Mathlib
import Submission.Work.NormalComplement.Sec5Fix.P2a.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement.Sec5Fix
namespace P2a

variable {G : Type} [Group G] [Finite G]

/-- `𝒩 = N_G(V)`. -/
noncomputable abbrev NNg (H : Subgroup G) (t : G) : Subgroup G := Sec5f.NN H t

/-- The kernel of the action of `𝒩` on `Ω_V`, as a subgroup of `↥𝒩`. -/
noncomputable abbrev KK (H : Subgroup G) (t : G) : Subgroup ↥(NNg H t) := Sec5f.KK H t

/-- `𝒩 ⧸ KK`. -/
noncomputable abbrev Nq (H : Subgroup G) (t : G) : Type := ↥(NNg H t) ⧸ KK H t

/-- The kernel of the action of `𝒩` on `Ω_V`, as a subgroup of the ambient group `G`. -/
noncomputable abbrev KKg (H : Subgroup G) (t : G) : Subgroup G :=
  (KK H t).map (NNg H t).subtype

theorem KKg_le_NN (H : Subgroup G) (t : G) : KKg H t ≤ NNg H t :=
  Subgroup.map_subtype_le _

theorem KKg_le_twoPoint (H : Subgroup G) (t : G) : KKg H t ≤ twoPoint H t :=
  Sec5f.KK_map_le_twoPoint

theorem KKg_le_H (H : Subgroup G) (t : G) : KKg H t ≤ H :=
  (KKg_le_twoPoint H t).trans inf_le_left

/-- Membership in `KKg`: an element of `𝒩` acting trivially on `Ω_V`. -/
theorem mem_KKg {H : Subgroup G} {t : G} {x : G} :
    x ∈ KKg H t ↔ x ∈ NNg H t ∧ ∀ ω ∈ Om H t, x • ω = ω := by
  rw [KKg, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    intro ω hω
    have hpermeq := MonoidHom.mem_ker.mp hy
    have h1 : MulAction.toPermHom ↥(NNg H t) ↥(Om H t) y (⟨ω, hω⟩ : ↥(Om H t)) =
        (⟨ω, hω⟩ : ↥(Om H t)) := by rw [hpermeq]; rfl
    have h2 : (((MulAction.toPermHom ↥(NNg H t) ↥(Om H t) y) ⟨ω, hω⟩ : ↥(Om H t)) : G ⧸ H) =
        (ω : G ⧸ H) := congrArg Subtype.val h1
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, Sec5f.coe_smul] at h2
    exact h2
  · rintro ⟨hx, hfix⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    show (⟨x, hx⟩ : ↥(NNg H t)) ∈ (MulAction.toPermHom ↥(NNg H t) ↥(Om H t)).ker
    rw [MonoidHom.mem_ker]
    ext ω
    show ((⟨x, hx⟩ : ↥(NNg H t)) : G) • (ω : G ⧸ H) = (ω : G ⧸ H)
    exact hfix (ω : G ⧸ H) ω.2

/-- Conjugation by an element of `𝒩` preserves `KKg`. -/
theorem conj_mem_KKg {H : Subgroup G} {t : G} {g x : G} (hg : g ∈ NNg H t)
    (hx : x ∈ KKg H t) : g * x * g⁻¹ ∈ KKg H t := by
  rw [mem_KKg] at hx ⊢
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hx.1) (Subgroup.inv_mem _ hg), ?_⟩
  intro ω hω
  have hg' : g⁻¹ ∈ NNg H t := Subgroup.inv_mem _ hg
  have h1 : g⁻¹ • ω ∈ Om H t := Sec5f.smul_mem_omega g⁻¹ hg' hω
  rw [mul_smul, mul_smul, hx.2 _ h1, smul_inv_smul]

/-- `KKg` is normalised by `𝒩`. -/
theorem NNg_le_normalizer_KKg (H : Subgroup G) (t : G) :
    NNg H t ≤ Subgroup.normalizer (KKg H t : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact conj_mem_KKg hg
  · intro hz
    have hg' : g⁻¹ ∈ NNg H t := Subgroup.inv_mem _ hg
    have h := conj_mem_KKg (H := H) (t := t) hg' hz
    convert h using 1
    group

/-- The point stabiliser in `𝒩 ⧸ KK` of the base point `V`-fixed coset `H`. -/
theorem stabilizer_ptV_Nq (H : Subgroup G) (t : G) :
    MulAction.stabilizer (Nq H t) (Sec5f.ptV H t) =
      ((NNg H t ⊓ H).subgroupOf (NNg H t)).map (QuotientGroup.mk' (KK H t)) :=
  Sec5f.stabilizer_ptV_quot (H := H) (t := t)

/-- The action of `𝒩 ⧸ KK` on `Ω_V` is faithful. -/
theorem faithful_Nq (H : Subgroup G) (t : G) :
    ∀ g : Nq H t, (∀ ω : ↥(Om H t), g • ω = ω) → g = 1 := by
  intro g hfix
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (KK H t) g
  have hy : y ∈ KK H t := by
    show y ∈ (MulAction.toPermHom ↥(NNg H t) ↥(Om H t)).ker
    rw [MonoidHom.mem_ker]
    ext ω
    show (y : G) • (ω : G ⧸ H) = (ω : G ⧸ H)
    have h := hfix ω
    rw [Sec5f.quotient_smul_mk y ω] at h
    exact congrArg (fun z : ↥(Om H t) => (z : G ⧸ H)) h
  rw [← QuotientGroup.ker_mk' (KK H t)] at hy
  exact MonoidHom.mem_ker.mp hy

end P2a
end Work.NormalComplement.Sec5Fix
