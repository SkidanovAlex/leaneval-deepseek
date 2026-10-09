import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

-- The `haveI`/`letI` below are deliberate: these are instances, not plain local hypotheses.
set_option linter.style.haveILetI false

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- **The quotient of a finite `G`-module by a copy of `𝔽_p` is strictly smaller.** For a short
exact sequence `S : 0 → S.X₁ --S.f--> S.X₂ --S.g--> S.X₃ → 0` in `Rep Coeff G` with `S.X₁` of
cardinality a prime `p` and `S.X₂` finite, the quotient `S.X₃` has strictly smaller cardinality.
This is the cardinality bookkeeping of the dévissage `0 → 𝔽_p → M → M₂ → 0` (there
`|S.X₂| = p · |S.X₃|`), needed to apply the induction hypothesis to `S.X₃`. -/
theorem natCard_cokernel_lt {G : Type} [Group G] {S : ShortComplex (Rep.{0} Coeff G)}
    (hS : S.ShortExact) [Finite S.X₁] [Finite S.X₂] {p : ℕ} [Fact p.Prime]
    (hX₁ : Nat.card S.X₁ = p) : Nat.card S.X₃ < Nat.card S.X₂ := by
  -- `S.g` is surjective, so `S.X₃` is a quotient of the finite type `S.X₂`.
  have hg : Function.Surjective S.g.hom := (Rep.epi_iff_surjective S.g).1 hS.epi_g
  haveI : Finite S.X₃ := Finite.of_surjective _ hg
  -- `S.f` is injective, and `S.g ∘ S.f = 0` since `S` is a short complex.
  have hf : Function.Injective S.f.hom := (Rep.mono_iff_injective S.f).1 hS.mono_f
  have hzero : ∀ a : S.X₁, S.g.hom (S.f.hom a) = 0 := by
    intro a
    have h : (S.f ≫ S.g) a = (0 : S.X₁ ⟶ S.X₃) a :=
      congrArg (fun φ : S.X₁ ⟶ S.X₃ => φ a) S.zero
    rw [Rep.comp_apply] at h
    simpa using h
  -- Hence `S.g` is not injective: `S.X₁` is nontrivial because `Nat.card S.X₁ = p ≥ 2`,
  -- so there are `a ≠ b` in `S.X₁`, whose images under the injective `S.f` are distinct
  -- elements of `S.X₂` with the same image under `S.g`.
  have hnotinj : ¬ Function.Injective S.g.hom := by
    intro hinj
    have hsub : Subsingleton S.X₁ :=
      ⟨fun a b => hf (hinj (by rw [hzero a, hzero b]))⟩
    letI : Fintype S.X₁ := Fintype.ofFinite S.X₁
    have hle : Fintype.card S.X₁ ≤ 1 := Fintype.card_le_one_iff_subsingleton.2 hsub
    have hcard : Fintype.card S.X₁ = p := by
      rw [← Nat.card_eq_fintype_card]
      exact hX₁
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  -- A surjective, non-injective map between finite types strictly decreases cardinality.
  letI : Fintype S.X₂ := Fintype.ofFinite S.X₂
  letI : Fintype S.X₃ := Fintype.ofFinite S.X₃
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_surjective_not_injective _ hg hnotinj

end Work.SSGRoute
