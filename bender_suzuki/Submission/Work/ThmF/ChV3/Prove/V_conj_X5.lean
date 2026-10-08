import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `V_conj_X5`: `V = C_D(t)` normalises `X = ⟨Q₀, K, t⟩`

This is the `X = ⟨Q₀,K,t⟩` half of Peterfalvi II, Ch. V §3, step (15) (`W_V_on_L`):
if `v ∈ V = centD H t = C_D(t)` then conjugation by `v` maps `X5 H t = ⟨Q₀, K, t⟩` onto itself.

The proof is generatorwise.  Let `v ∈ V`.  Then `v ∈ H`, `v ∈ H^t` and `t v = v t`, and

* `Q₀ = Inv(H) ∪ {1}` is preserved: conjugation by an element of `H` restricts to an automorphism
  of `H` and preserves `orderOf`, so it permutes the involutions of `H` (`cj_mem_Q0`);
* `K = J(D,t) = {x ∈ D | t x t⁻¹ = x⁻¹}` is preserved (`cj_mem_Kset`): for `x ∈ K`,
  `v x v⁻¹ ∈ H` because `v, x ∈ H`, and `v x v⁻¹ ∈ t H t⁻¹` because
  `t (v x⁻¹ v⁻¹) t⁻¹ = (t v t⁻¹)(t x⁻¹ t⁻¹)(t v t⁻¹)⁻¹ = v x v⁻¹` (using `t v t⁻¹ = v`, which
  follows from `t v = v t`, and `t x t⁻¹ = x⁻¹`); finally
  `t (v x v⁻¹) t⁻¹ = v x⁻¹ v⁻¹ = (v x v⁻¹)⁻¹`;
* `t` is fixed, `v t v⁻¹ = t`.

Hence `v` maps the generating set `Q₀ ∪ K ∪ {t}` of `X` onto itself, and since conjugation is a
bijection, `MonoidHom.map_closure` gives `v X v⁻¹ = X`.

The standing hypothesis `h : IsSplitRankOne H Q t` is not used: the statement only needs
`v ∈ centD H t` (i.e. `v ∈ H ∩ H^t` with `t v = v t`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

open Work.ThmF

/-- Conjugation by an element of `H` preserves `Q₀ = Inv(H) ∪ {1}`. -/
theorem cj_mem_Q0 {G : Type} [Group G] {H : Subgroup G} {v x : G} (hv : v ∈ H)
    (hx : x ∈ Q0 H) : v * x * v⁻¹ ∈ Q0 H := by
  rw [Work.ThmF.mem_Q0_iff] at hx ⊢
  rcases hx with ⟨hxH, hx2⟩ | hx1
  · left
    refine ⟨H.mul_mem (H.mul_mem hv hxH) (H.inv_mem hv), ?_⟩
    have h1 := MulEquiv.orderOf_eq (MulAut.conj v) x
    rw [MulAut.conj_apply, hx2] at h1
    exact h1
  · right
    rw [hx1]
    group

/-- Conjugation by `v ∈ H` with `t * v = v * t` preserves `K = J(D,t)`. -/
theorem cj_mem_Kset {G : Type} [Group G] {H : Subgroup G} {t v x : G} (hvH : v ∈ H)
    (hvt : t * v = v * t) (hx : x ∈ Kset H t) : v * x * v⁻¹ ∈ Kset H t := by
  rw [Work.ThmF.mem_Kset_iff] at hx ⊢
  obtain ⟨hxD, hxinv⟩ := hx
  obtain ⟨hxH, _⟩ := Subgroup.mem_inf.mp hxD
  have htv : t * v * t⁻¹ = v := by rw [hvt, mul_assoc, mul_inv_cancel, mul_one]
  have htx : t * x * t⁻¹ = x⁻¹ := hxinv
  have htxinv : t * x⁻¹ * t⁻¹ = x := by
    calc t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
      _ = (x⁻¹)⁻¹ := by rw [hxinv]
      _ = x := by rw [inv_inv]
  refine ⟨?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hvH hxH) (H.inv_mem hvH), ?_⟩
    rw [Submission.Blueprint.conj, Subgroup.mem_map]
    refine ⟨v * x⁻¹ * v⁻¹, H.mul_mem (H.mul_mem hvH (H.inv_mem hxH)) (H.inv_mem hvH), ?_⟩
    show t * (v * x⁻¹ * v⁻¹) * t⁻¹ = v * x * v⁻¹
    rw [show t * (v * x⁻¹ * v⁻¹) * t⁻¹
        = (t * v * t⁻¹) * (t * x⁻¹ * t⁻¹) * (t * v * t⁻¹)⁻¹ by group]
    rw [htv, htxinv]
  · have h2 : t * (v * x * v⁻¹) * t⁻¹
        = (t * v * t⁻¹) * (t * x * t⁻¹) * (t * v * t⁻¹)⁻¹ := by group
    rw [h2, htv, htx]
    group

/-- `v ∈ H` with `t * v = v * t` maps the generating set `Q₀ ∪ K ∪ {t}` of `X5 H t` into itself. -/
theorem cj_mem_gen {G : Type} [Group G] {H : Subgroup G} {t v x : G} (hvH : v ∈ H)
    (hvt : t * v = v * t) (hx : x ∈ (Q0 H ∪ Kset H t ∪ {t} : Set G)) :
    v * x * v⁻¹ ∈ (Q0 H ∪ Kset H t ∪ {t} : Set G) := by
  rw [Set.mem_union] at hx
  rcases hx with hxAB | hxt
  · rw [Set.mem_union] at hxAB
    rcases hxAB with hxQ | hxK
    · exact Or.inl (Or.inl (cj_mem_Q0 hvH hxQ))
    · exact Or.inl (Or.inr (cj_mem_Kset hvH hvt hxK))
  · rw [Set.mem_singleton_iff] at hxt
    rw [hxt, show v * t * v⁻¹ = t by rw [← hvt, mul_assoc, mul_inv_cancel, mul_one]]
    exact Or.inr rfl

theorem V_conj_X5 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    ∀ v ∈ Submission.Blueprint.centD H t,
      Work.ThmF.ChV3.cj v (Work.ThmF.Lemma5.X5 H t) = Work.ThmF.Lemma5.X5 H t := by
  intro v hv
  obtain ⟨hvD, hvc⟩ := Subgroup.mem_inf.mp hv
  obtain ⟨hvH, _⟩ := Subgroup.mem_inf.mp hvD
  have hvt : t * v = v * t := Subgroup.mem_centralizer_iff.mp hvc t (Set.mem_singleton t)
  -- conjugation by `v` maps the generating set of `X5` into itself
  have hsub : (MulAut.conj v).toMonoidHom '' (Q0 H ∪ Kset H t ∪ {t} : Set G)
      ⊆ (Q0 H ∪ Kset H t ∪ {t} : Set G) := by
    rintro y ⟨x, hx, rfl⟩
    change v * x * v⁻¹ ∈ (Q0 H ∪ Kset H t ∪ {t} : Set G)
    exact cj_mem_gen hvH hvt hx
  -- and, being a bijection, onto
  have hsup : (Q0 H ∪ Kset H t ∪ {t} : Set G)
      ⊆ (MulAut.conj v).toMonoidHom '' (Q0 H ∪ Kset H t ∪ {t} : Set G) := by
    intro x hx
    obtain ⟨hvD', hvc'⟩ := Subgroup.mem_inf.mp (Subgroup.inv_mem _ hv)
    obtain ⟨hvH', _⟩ := Subgroup.mem_inf.mp hvD'
    have hvt' : t * v⁻¹ = v⁻¹ * t :=
      Subgroup.mem_centralizer_iff.mp hvc' t (Set.mem_singleton t)
    refine ⟨v⁻¹ * x * v, ?_, ?_⟩
    · simpa using cj_mem_gen hvH' hvt' hx
    · change v * (v⁻¹ * x * v) * v⁻¹ = x
      group
  have hset : (MulAut.conj v).toMonoidHom '' (Q0 H ∪ Kset H t ∪ {t} : Set G)
      = (Q0 H ∪ Kset H t ∪ {t} : Set G) := Set.Subset.antisymm hsub hsup
  rw [Work.ThmF.ChV3.cj]
  change Subgroup.map (MulAut.conj v).toMonoidHom (Subgroup.closure (Q0 H ∪ Kset H t ∪ {t}))
      = Subgroup.closure (Q0 H ∪ Kset H t ∪ {t})
  rw [MonoidHom.map_closure, hset]

end Work.ThmF.ChV3.Prove
