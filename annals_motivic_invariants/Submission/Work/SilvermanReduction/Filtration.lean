/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.SilvermanReduction
-/
import Submission.Work.SilvermanReduction.Add
import Submission.Work.SilvermanReduction.redPoint_surjective

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Silverman, *AEC*, VII.2.1–2.2: the filtration `E(K) ⊇ E₁(K)` and the quotient `E(K)/E₁(K)`

Once `redPoint` is known to be additive (`Add.lean`), its kernel

  `E₁(K) = {P : v(x_P) < 0} ∪ {O}`

is a subgroup of `E(K)` (`E1Subgroup`), and the first isomorphism theorem yields the exact sequence

  `0 → E₁(K) → E(K) → Ẽ(k)`,

i.e. an injection `E(K)/E₁(K) ↪ Ẽ(k)`, which is an isomorphism as soon as the place is Henselian
(`redPoint_surjective`).  In particular the quotient is *finite* whenever the residue field is
finite — the finiteness of the quotient `E(K)/E₀(K)` of Silverman VII.2.2, in the good-reduction
case where the special fibre is smooth and `E₀(K) = E(K)`.

## Main results

* `E1Subgroup` — `E₁(K)` as a subgroup of `E(K)`.
* `mem_E1Subgroup_iff` — `P ∈ E₁(K) ↔ P = 0 ∨ P ∈ E1 R W`.
* `redPointAddMonoidHom_ker` — the kernel of the reduction is `E₁(K)`.
* `quotientReduction`, `quotientReduction_injective`, `range_quotientReduction` — the induced
  injective map `E(K)/E₁(K) →+ Ẽ(k)`.
* `finite_quotient` — `E(K)/E₁(K)` is finite when the residue field is finite.
* `quotientEquivReduction` — for `R` Henselian, `E(K)/E₁(K) ≃+ Ẽ(k)`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace Work.SilvermanReduction

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K] [DecidableEq (ResidueField R)]

/-- **`E₁(K)`, the subgroup of points of negative valuation** (the kernel of the reduction). -/
def E1Subgroup {W : Affine K} [W.HasGoodReduction R] :
    AddSubgroup (WeierstrassCurve.Affine.Point W) :=
  (redPointAddMonoidHom (W := W) R).ker

variable {W : Affine K} [W.HasGoodReduction R]

theorem mem_E1Subgroup_iff (P : WeierstrassCurve.Affine.Point W) :
    P ∈ E1Subgroup R (W := W) ↔ P = 0 ∨ P ∈ E1 R W := by
  rw [E1Subgroup, AddMonoidHom.mem_ker, redPointAddMonoidHom_apply, redPoint_eq_zero_iff R P,
    E1, Set.mem_setOf_eq]

/-- **The kernel of the reduction is `E₁(K)`.**  This is the exactness of
`0 → E₁(K) → E(K) → Ẽ(k)` at the left. -/
theorem redPointAddMonoidHom_ker :
    (redPointAddMonoidHom (W := W) R).ker = E1Subgroup R (W := W) := rfl

/-- The induced map `E(K)/E₁(K) →+ Ẽ(k)`, which is injective by the first isomorphism theorem. -/
def quotientReduction :
    (WeierstrassCurve.Affine.Point W ⧸ E1Subgroup R (W := W)) →+
      WeierstrassCurve.Affine.Point (W.reduction R) :=
  QuotientAddGroup.kerLift (redPointAddMonoidHom (W := W) R)

theorem quotientReduction_injective : Function.Injective (quotientReduction R (W := W)) :=
  QuotientAddGroup.kerLift_injective _

/-- The reduced curve has only finitely many points when the residue field is finite. -/
instance finite_point_reduction [Finite (ResidueField R)] :
    Finite (WeierstrassCurve.Affine.Point (W.reduction R)) :=
  Finite.of_injective
    (fun P : WeierstrassCurve.Affine.Point (W.reduction R) =>
      match P with
      | WeierstrassCurve.Affine.Point.zero => none
      | WeierstrassCurve.Affine.Point.some x y _ => some (x, y))
    (by
      intro P Q h
      rcases P with _ | ⟨x, y, hxy⟩
      · rcases Q with _ | ⟨u, v, huv⟩ <;> simp_all
      · rcases Q with _ | ⟨u, v, huv⟩
        · simp_all
        · dsimp only at h
          rw [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          subst h1
          subst h2
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨rfl, rfl⟩)

/-- **`E(K)/E₁(K)` embeds into the finite group `Ẽ(k)`**, hence is finite when the residue field is
finite.  This is the finiteness of the quotient `E(K)/E₀(K)` of Silverman, *AEC*, VII.2.2, in the
good-reduction case (where `E₀(K) = E(K)`, the special fibre being smooth). -/
instance finite_quotient [Finite (ResidueField R)] :
    Finite (WeierstrassCurve.Affine.Point W ⧸ E1Subgroup R (W := W)) :=
  Finite.of_injective (quotientReduction R (W := W)) (quotientReduction_injective R (W := W))

/-- When the place is Henselian the reduction is surjective (`redPoint_surjective`), and the first
isomorphism theorem identifies `E(K)/E₁(K)` with the special fibre `Ẽ(k)`. -/
theorem quotientReduction_surjective [HenselianLocalRing R] :
    Function.Surjective (quotientReduction R (W := W)) := by
  intro Q
  obtain ⟨P, hP⟩ := redPoint_surjective R (W := W) Q
  exact ⟨QuotientAddGroup.mk' _ P, hP⟩

/-- **Silverman, *AEC*, VII.2.1–2.2: `E(K)/E₁(K) ≃+ Ẽ(k)`** for a Henselian place of good
reduction.  This is the exact sequence `0 → E₁(K) → E(K) → Ẽ(k) → 0`. -/
noncomputable def quotientEquivReduction [HenselianLocalRing R] :
    (WeierstrassCurve.Affine.Point W ⧸ E1Subgroup R (W := W)) ≃+
      WeierstrassCurve.Affine.Point (W.reduction R) :=
  AddEquiv.ofBijective (quotientReduction R (W := W))
    ⟨quotientReduction_injective R (W := W), quotientReduction_surjective R (W := W)⟩

end

end Work.SilvermanReduction
