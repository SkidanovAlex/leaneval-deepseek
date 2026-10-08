import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `D = K · V`: the decomposition of the two-point stabiliser

Peterfalvi, *Le théorème de Bender–Suzuki I*, Appendix I (1)(b) (p. 200), applied to the
two-point stabiliser `D = H ∩ H^t` of a split rank-one group and its involution `t ∉ H`:
if `X` is a subgroup of odd order normalised by the involution `t`, then the multiplication map

`C_X(t) × J(X,t) → X`,   `(v, k) ↦ v * k`

is a bijection, where `J(X,t) = {x ∈ X | t x t⁻¹ = x⁻¹}`.  The other order works as well, so
`X = J(X,t) · C_X(t) = C_X(t) · J(X,t)`; the statement proved here is the form needed
downstream: every `d ∈ D` is a product `k * v` with `k ∈ K = J(D,t) = Kset H t` and
`v ∈ V = C_D(t) = centD H t`.

The two halves of Appendix I (1)(b) are already in the library
(`Work.ThmF.Bender.mul_invertedBy_centralizer_injective` and
`Work.ThmF.Bender.cardInvertedMulCardCentralizer`); here they are combined with
`Function.Injective.bijective_of_nat_card_le` (injectivity plus equality of the two finite
cardinalities gives bijectivity), and the resulting `v * k`-decomposition of `d⁻¹` is
inverted, using that `Kset H t` and `centD H t` are closed under inversion.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PSU3.StageA

open Submission.Blueprint

/-- **Appendix I (1)(b) for the two-point stabiliser.**  For split rank-one data
(`IsSplitRankOneData`, i.e. `H = Q ⋊ D` with `D = H ∩ H^t` of odd order and `t` an involution
outside `H`), every `d ∈ D = twoPoint H t` factors as `d = k * v` with
`k ∈ Kset H t = J(D,t)` (an element inverted by `t`) and `v ∈ centD H t = C_D(t)`. -/
theorem twoPoint_eq_Kset_mul_centD_of_data {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G} (h : Work.ThmF.IsSplitRankOneData G H Q t) :
    ∀ d ∈ Submission.Blueprint.twoPoint H t, ∃ k ∈ Work.ThmF.Kset H t,
      ∃ v ∈ Submission.Blueprint.centD H t, d = k * v := by
  classical
  have hodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
    Work.ThmF.odd_card_twoPoint_of_data h
  -- The multiplication map `C × J → D`, `(c, k) ↦ c * k`.
  let φ : ↥(Submission.Blueprint.centD H t) × ↥(Work.ThmF.Kset H t) →
      ↥(Submission.Blueprint.twoPoint H t) :=
    fun p => ⟨(p.1 : G) * (p.2 : G),
      (Submission.Blueprint.twoPoint H t).mul_mem
        (Work.ThmF.centD_le_twoPoint t p.1.2)
        (Work.ThmF.Kset_subset H t p.2.2)⟩
  -- It is injective (Appendix I (1)) …
  have hinj : Function.Injective φ := by
    rintro ⟨c₁, k₁⟩ ⟨c₂, k₂⟩ heq
    have hval : (c₁ : G) * (k₁ : G) = (c₂ : G) * (k₂ : G) := by
      simpa [φ] using
        congrArg (fun z : ↥(Submission.Blueprint.twoPoint H t) => (z : G)) heq
    obtain ⟨hc, hk⟩ := Work.ThmF.Bender.mul_invertedBy_centralizer_injective
      (X := Submission.Blueprint.twoPoint H t) hodd
      (c₁ : G) (c₂ : G) (k₁ : G) (k₂ : G)
      (Subgroup.mem_inf.mp c₁.2).2 (Subgroup.mem_inf.mp c₁.2).1 k₁.2
      (Subgroup.mem_inf.mp c₂.2).2 (Subgroup.mem_inf.mp c₂.2).1 k₂.2 hval
    exact Prod.ext (Subtype.ext hc) (Subtype.ext hk)
  -- … and its domain and codomain have the same cardinality (Appendix I (1)(a)),
  have hcard : Nat.card (↥(Submission.Blueprint.centD H t) × ↥(Work.ThmF.Kset H t)) =
      Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
    rw [Nat.card_prod, Nat.card_coe_set_eq]
    exact Work.ThmF.card_centD_mul_card_Kset h
  -- … so it is bijective.
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le (le_of_eq hcard.symm)
  intro d hd
  -- Factor `d⁻¹ = c * k` with `c ∈ C`, `k ∈ J`; then `d = k⁻¹ * c⁻¹`.
  obtain ⟨⟨c, k⟩, hck⟩ := hbij.2 ⟨d⁻¹, (Submission.Blueprint.twoPoint H t).inv_mem hd⟩
  have hval : (c : G) * (k : G) = d⁻¹ := by
    simpa [φ] using congrArg (fun z : ↥(Submission.Blueprint.twoPoint H t) => (z : G)) hck
  obtain ⟨hkD, hkinv⟩ := k.2
  have hk1 : (k : G)⁻¹ ∈ Work.ThmF.Kset H t := by
    refine ⟨(Submission.Blueprint.twoPoint H t).inv_mem hkD, ?_⟩
    rw [show t * (k : G)⁻¹ * t⁻¹ = (t * (k : G) * t⁻¹)⁻¹ from by group, hkinv, inv_inv]
  have hc1 : (c : G)⁻¹ ∈ Submission.Blueprint.centD H t :=
    (Submission.Blueprint.centD H t).inv_mem c.2
  refine ⟨(k : G)⁻¹, hk1, (c : G)⁻¹, hc1, ?_⟩
  have hd' : d = ((c : G) * (k : G))⁻¹ := by rw [hval, inv_inv]
  rw [hd', mul_inv_rev]

theorem twoPoint_eq_Kset_mul_centD {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    ∀ d ∈ Submission.Blueprint.twoPoint H t, ∃ k ∈ Work.ThmF.Kset H t,
      ∃ v ∈ Submission.Blueprint.centD H t, d = k * v :=
  twoPoint_eq_Kset_mul_centD_of_data (Work.ThmF.IsSplitRankOne.toData h)

end Work.PSU3.StageA
