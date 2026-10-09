/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The shrinking lemmas at every level `m ≥ m₀`

The paper states its shrinking results (Proposition 6, Proposition 7) in the form

> there is `m₀ ≥ n` such that for **all** `m ≥ m₀`: given `x₁, …, x_t` at level `m` there is a
> surjective `G`-operator homomorphism `F(m) ⇢ F(n)` killing them,

and the proof of Proposition 7 (i) and step 4 of the proof of Theorem 15 use exactly this shape:
the level `m` is chosen by the user (as large as needed), and the shrinking map is then found.

The proofs of `Shrinking.lean`, `Corollaries.lean`, `Models.lean` and `Prop7Uncond.lean` deliver
the same statement only at the levels `m = r·n` (`_of_mult` in their names), because Proposition 2
of the paper (`Work.Shrinking.exists_forall_foldMap_rTensor_tensorPower_eq_zero`) is applied to
`M^r` with `M = F(n)/F(n)²` and hence produces maps out of `F(r·n)`.

This file removes that restriction.  If the classes at a level `m` are to be killed, first apply
*any* surjective `G`-operator homomorphism `F(m) ⇢ F(r₀·n)` (which exists because `r₀·n ≤ m`, see
`OperatorMap.ofLe` / `exists_operatorMap_of_le`), then use the `r₀·n`-version of the shrinking
lemma on the images, and compose.  The composition law for the induced maps is
`operator.hm1Map_comp` (resp. `operator.h1Map_comp`).

Thus every shrinking statement of the chapter is available in the paper's own "for all `m ≥ m₀`"
form; the names `exists_shrinking_Hm1`, `exists_shrinking_Hm2IG`, `exists_shrinking_H2IG`,
`exists_shrinking_H1` of this file are the *primary* interface.

## Main results

* `Work.CohomologicalShrinking.exists_shrinking_Hm1` : Proposition 6, `k = -1`, all levels.
* `Work.CohomologicalShrinking.exists_shrinking_Hm2IG` : Proposition 6, `k = -2`
  (`A_{-2} = I_G`), all levels.
* `Work.CohomologicalShrinking.exists_shrinking_H2IG` : Proposition 6, `k = 2`
  (`A_2 = I_G^{-3}`), all levels.
* `Work.CohomologicalShrinking.exists_shrinking_H1` : Proposition 7 (ii), all levels.
* `Work.CohomologicalShrinking.exists_shrinking_Hm2_of_shift`,
  `Work.CohomologicalShrinking.exists_shrinking_H2_of_shift` : the cases `k = -2`, `k = 2` with a
  *generic* dimension-shifting isomorphism as an explicit hypothesis, all levels.

Everything here is proved from `Prop5Data` (Proposition 5) only; see `NOTES.md`.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Shrinking
import Submission.Work.CohomologicalShrinking.Models
import Submission.Work.CohomologicalShrinking.Prop7Uncond
import Submission.Work.CohomologicalShrinking.OperatorMap
import Submission.Work.CohomologicalShrinking.Corollaries
import Submission.Work.CohomologicalShrinking.operator.hm1Map_comp
import Submission.Work.CohomologicalShrinking.operator.h1Map_comp
import Submission.Work.CohomologicalShrinking.operator.hm2Map_comp
import Submission.Work.CohomologicalShrinking.operator.h2Map_comp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

set_option maxHeartbeats 1600000

open scoped TensorProduct

universe u v w

variable {p : ℕ}

/-- **Proposition 6 of Schmidt–Wingberg, case `k = -1`, at every level `m ≥ m₀`.**

Let `G` be finite, `p` a prime, `τ = (i,j)` with `j ≥ 1`, `N` a finitely generated
`𝔽_p[G]`-module, `t ∈ ℕ` and `n ≥ 1`.  Then there is `m₀ ≥ n` such that for all `m ≥ m₀` and all
`x₁, …, x_t ∈ Ĥ⁻¹(G, E(m,τ) ⊗ N)` there is a surjective `G`-equivariant `Φ : F(m) → F(n)`
killing all the `x_i`.

This is the paper's form (`m` arbitrary), obtained from the level-`r·n` form
`exists_shrinking_Hm1_of_mult` by first retracting `F(m) ⇢ F(r₀·n)`. -/
theorem exists_shrinking_Hm1 (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (N : Type*) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [Module.Finite (ZMod p) N]
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m ≥ m₀,
      ∀ x : Fin t → Work.Tate.Hm1 G (E p G m i j ⊗[ZMod p] N),
      ∃ Φ : OperatorMap G m n, ∀ k : Fin t, (Φ.hm1Map p G N) (x k) = 0 := by
  obtain ⟨r₀, hr₀⟩ := exists_shrinking_Hm1_of_mult (p := p) G hj D N t hn
  refine ⟨max n (r₀ * n), le_max_left _ _, fun m hm x => ?_⟩
  have hle : r₀ * n ≤ m := le_trans (le_max_right _ _) hm
  obtain ⟨Φ₁⟩ := exists_operatorMap_of_le G hle
  obtain ⟨Φ₂, hΦ₂⟩ := hr₀ r₀ le_rfl (fun k => Φ₁.hm1Map p G N (x k))
  refine ⟨Φ₂.comp Φ₁, fun k => ?_⟩
  have hcomp := operator.hm1Map_comp p G i j N Φ₁ Φ₂
  rw [hcomp, AddMonoidHom.comp_apply]
  exact hΦ₂ k

/-- **Proposition 6 of Schmidt–Wingberg, case `k = -2`** (the model `Ĥ⁻²(G, X) ≅
Ĥ⁻¹(G, X ⊗ I_G)`), at every level `m ≥ m₀`.

Let `G` be finite, `p` a prime, `τ = (i,j)` with `j ≥ 1` and `T` a finitely generated
`𝔽_p[G]`-module.  Then there is `m₀ ≥ n` such that for all `m ≥ m₀` and all classes
`x₁, …, x_t ∈ Ĥ⁻¹(G, E(m,τ) ⊗ (T ⊗ I_G))` there is a surjective `G`-equivariant `Φ : F(m) → F(n)`
killing all the `x_i`.

This is the `k = -2` case used in the proof of Proposition 7 and in step 4 of Theorem 15;
unconditional apart from `Prop5Data`. -/
theorem exists_shrinking_Hm2IG (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m ≥ m₀,
      ∀ x : Fin t → Work.Tate.Hm1 G
        (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G)),
      ∃ Φ : OperatorMap G m n, ∀ k : Fin t,
        (Φ.hm1Map p G (T ⊗[ZMod p] augIdeal p G)) (x k) = 0 := by
  obtain ⟨r₀, hr₀⟩ := exists_shrinking_Hm2IG_of_mult (p := p) G hj D T t hn
  refine ⟨max n (r₀ * n), le_max_left _ _, fun m hm x => ?_⟩
  have hle : r₀ * n ≤ m := le_trans (le_max_right _ _) hm
  obtain ⟨Φ₁⟩ := exists_operatorMap_of_le G hle
  obtain ⟨Φ₂, hΦ₂⟩ := hr₀ r₀ le_rfl
    (fun k => Φ₁.hm1Map p G (T ⊗[ZMod p] augIdeal p G) (x k))
  refine ⟨Φ₂.comp Φ₁, fun k => ?_⟩
  have hcomp := operator.hm1Map_comp p G i j (T ⊗[ZMod p] augIdeal p G) Φ₁ Φ₂
  rw [hcomp, AddMonoidHom.comp_apply]
  exact hΦ₂ k

/-- **Proposition 6 of Schmidt–Wingberg, case `k = 2`** (the model `Ĥ²(G, X) ≅
Ĥ⁻¹(G, X ⊗ A₂)`, `A₂ = I_G^{-3}`), at every level `m ≥ m₀`.

Let `G` be finite, `p` a prime, `τ = (i,j)` with `j ≥ 1` and `T` a finitely generated
`𝔽_p[G]`-module.  Then there is `m₀ ≥ n` such that for all `m ≥ m₀` and all classes
`x₁, …, x_t ∈ Ĥ⁻¹(G, E(m,τ) ⊗ (T ⊗ A₂))` there is a surjective `G`-equivariant `Φ : F(m) → F(n)`
killing all the `x_i`.

This is the `k = 2` case used in steps 1 and 3 of Theorem 15; unconditional apart from
`Prop5Data`. -/
theorem exists_shrinking_H2IG (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m ≥ m₀,
      ∀ x : Fin t → Work.Tate.Hm1 G
        (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G)),
      ∃ Φ : OperatorMap G m n, ∀ k : Fin t,
        (Φ.hm1Map p G (T ⊗[ZMod p] A2 p G)) (x k) = 0 := by
  obtain ⟨r₀, hr₀⟩ := exists_shrinking_H2IG_of_mult (p := p) G hj D T t hn
  refine ⟨max n (r₀ * n), le_max_left _ _, fun m hm x => ?_⟩
  have hle : r₀ * n ≤ m := le_trans (le_max_right _ _) hm
  obtain ⟨Φ₁⟩ := exists_operatorMap_of_le G hle
  obtain ⟨Φ₂, hΦ₂⟩ := hr₀ r₀ le_rfl
    (fun k => Φ₁.hm1Map p G (T ⊗[ZMod p] A2 p G) (x k))
  refine ⟨Φ₂.comp Φ₁, fun k => ?_⟩
  have hcomp := operator.hm1Map_comp p G i j (T ⊗[ZMod p] A2 p G) Φ₁ Φ₂
  rw [hcomp, AddMonoidHom.comp_apply]
  exact hΦ₂ k

/-- **Proposition 7 (ii) of Schmidt–Wingberg**, at every level `m ≥ m₀`.

Let `G` be finite, `p` a prime, `τ = (i,j)` with `j ≥ 1` and `T` a finitely generated
`𝔽_p[G]`-module.  Then there is `m₀ ≥ n` such that for all `m ≥ m₀` and all
`x₁, …, x_t ∈ Ĥ^{-2}(F(m)/ν, E(m,τ) ⊗ T) = F(m)/F(m)² ⊗ E(m,τ) ⊗ T` there is a surjective
`G`-equivariant `Φ : F(m) → F(n)` whose induced map kills all the `x_i`.

Unconditional apart from `Prop5Data` (Proposition 5); the surjection `σ` of the paper's proof is
constructed in `prop7.exists_h1Sigma`. -/
theorem exists_shrinking_H1 (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m ≥ m₀,
      ∀ x : Fin t → squareQuotient p G m ⊗[ZMod p] (E p G m i j ⊗[ZMod p] T),
      ∃ Φ : OperatorMap G m n, ∀ k : Fin t, Φ.h1Map p G T (x k) = 0 := by
  obtain ⟨r₀, hr₀⟩ := exists_shrinking_H1_of_mult (p := p) G hj D T t hn
  refine ⟨max n (r₀ * n), le_max_left _ _, fun m hm x => ?_⟩
  have hle : r₀ * n ≤ m := le_trans (le_max_right _ _) hm
  obtain ⟨Φ₁⟩ := exists_operatorMap_of_le G hle
  obtain ⟨Φ₂, hΦ₂⟩ := hr₀ r₀ le_rfl (fun k => Φ₁.h1Map p G T (x k))
  refine ⟨Φ₂.comp Φ₁, fun k => ?_⟩
  have hcomp := operator.h1Map_comp p G i j T Φ₁ Φ₂
  rw [hcomp, LinearMap.comp_apply]
  exact hΦ₂ k

/-! ## The `k = ±2` cases with a *generic* dimension-shifting isomorphism, at every level -/

/-- **Proposition 6, case `k = -2`, at every level `m ≥ m₀`**, with the dimension-shifting
isomorphism `Ĥ⁻²(G, X) ≅ Ĥ⁻¹(G, X ⊗ A_{-2})` taken as an explicit hypothesis (as in
`exists_shrinking_Hm2_of_shift_mult`); this is the version to use when the user's model of
`Ĥ⁻²` is not the `I_G`-model of `Models.lean`. -/
theorem exists_shrinking_Hm2_of_shift (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (A : Type*) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
    [SMulCommClass G (ZMod p) A] [Module.Finite (ZMod p) A]
    (shift : ∀ m : ℕ, Work.Tate.Hm2 G (E p G m i j ⊗[ZMod p] T) ≃+
      Work.Tate.Hm1 G (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] A)))
    (hshift : ∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n),
      (Φ.hm1Map p G (T ⊗[ZMod p] A)).comp (shift m).toAddMonoidHom
        = (shift n).toAddMonoidHom.comp (Φ.hm2Map p G T))
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m ≥ m₀,
      ∀ x : Fin t → Work.Tate.Hm2 G (E p G m i j ⊗[ZMod p] T),
      ∃ Φ : OperatorMap G m n, ∀ k : Fin t, Φ.hm2Map p G T (x k) = 0 := by
  obtain ⟨r₀, hr₀⟩ :=
    exists_shrinking_Hm2_of_shift_mult (p := p) G hj D T A shift hshift t hn
  refine ⟨max n (r₀ * n), le_max_left _ _, fun m hm x => ?_⟩
  have hle : r₀ * n ≤ m := le_trans (le_max_right _ _) hm
  obtain ⟨Φ₁⟩ := exists_operatorMap_of_le G hle
  obtain ⟨Φ₂, hΦ₂⟩ := hr₀ r₀ le_rfl (fun k => Φ₁.hm2Map p G T (x k))
  refine ⟨Φ₂.comp Φ₁, fun k => ?_⟩
  have hcomp := operator.hm2Map_comp p G i j T Φ₁ Φ₂
  rw [hcomp, AddMonoidHom.comp_apply]
  exact hΦ₂ k

/-- **Proposition 6, case `k = 2`, at every level `m ≥ m₀`**, with the dimension-shifting
isomorphism `Ĥ²(G, X) ≅ Ĥ⁻¹(G, X ⊗ A₂)` taken as an explicit hypothesis (as in
`exists_shrinking_H2_of_shift_mult`). -/
theorem exists_shrinking_H2_of_shift (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (A : Type*) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
    [SMulCommClass G (ZMod p) A] [Module.Finite (ZMod p) A]
    (shift : ∀ m : ℕ, GroupCohomology.H2 G (E p G m i j ⊗[ZMod p] T) ≃+
      Work.Tate.Hm1 G (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] A)))
    (hshift : ∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n),
      (Φ.hm1Map p G (T ⊗[ZMod p] A)).comp (shift m).toAddMonoidHom
        = (shift n).toAddMonoidHom.comp (Φ.h2Map p G T))
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m ≥ m₀,
      ∀ x : Fin t → GroupCohomology.H2 G (E p G m i j ⊗[ZMod p] T),
      ∃ Φ : OperatorMap G m n, ∀ k : Fin t, Φ.h2Map p G T (x k) = 0 := by
  obtain ⟨r₀, hr₀⟩ :=
    exists_shrinking_H2_of_shift_mult (p := p) G hj D T A shift hshift t hn
  refine ⟨max n (r₀ * n), le_max_left _ _, fun m hm x => ?_⟩
  have hle : r₀ * n ≤ m := le_trans (le_max_right _ _) hm
  obtain ⟨Φ₁⟩ := exists_operatorMap_of_le G hle
  obtain ⟨Φ₂, hΦ₂⟩ := hr₀ r₀ le_rfl (fun k => Φ₁.h2Map p G T (x k))
  refine ⟨Φ₂.comp Φ₁, fun k => ?_⟩
  have hcomp := operator.h2Map_comp p G i j T Φ₁ Φ₂
  rw [hcomp, AddMonoidHom.comp_apply]
  exact hΦ₂ k

end Work.CohomologicalShrinking
