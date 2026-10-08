import Mathlib
import Submission.Work.Models.Abstract.ModelData
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.Models.Port.PSL2Model
import Submission.Work.Models.Abstract.involutions_subset_U

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.ModelData.pSL2ModelData` — the model data of `PSL(2, 2ⁿ)`

We assemble the `ModelData` record of `PSL(2, 2ⁿ)` (`n ≥ 2`) on top of the rank-one
`(B,N)`-pair `Submission.PSL2.pSL2BenderPair`: the Borel subgroup `B` is the stabilizer of the
point `pt0` of the projective line, the unipotent radical `U` is the image of
`unipotentPSLHom`, the torus `T` is the diagonal torus `(diagPSLHom K).range`, and the Weyl
element is `weylPSL K`.  The extra model-specific data of `ModelData` is

* `K₀ := (diagPSLHom K).range = T`, inverted by the Weyl element `weylPSL`,
* `T` is abelian (an image of the commutative group `Kˣ`),
* `weylPSL K` is an involution,
* `K₀` is cyclic (an image of the cyclic group `Kˣ`),
* `|K₀| = #involution(B) = 2ⁿ - 1`,
* `|K₀| ≥ 2`,
* every involution of `U` is central in `U` (`U` is elementary abelian: an image of
  `(K, +)` in characteristic two).
-/

set_option linter.style.haveILetI false

namespace Work.Models.ModelData

open Matrix LeanEval.GroupTheory.Defs

/-- The unipotent subgroup of `PSL(2, 2ⁿ)` is elementary abelian: the image of the underlying
additive group `(K, +)` of a field of characteristic two, in which `x + x = 0`. -/
theorem psl2UnipotentSqOne (n : ℕ) :
    ∀ u ∈ (Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n)).range, u * u = 1 := by
  intro u hu
  obtain ⟨a, rfl⟩ := hu
  have ha : a * a = 1 := by
    rw [show a * a = Multiplicative.ofAdd (a.toAdd + a.toAdd) from rfl,
      CharTwo.add_self_eq_zero]
    rfl
  rw [← map_mul, ha, map_one]

/-- The diagonal torus of `PSL(2, 2ⁿ)` is abelian: it is the image of the commutative group
`Kˣ`. -/
theorem psl2DiagComm (n : ℕ) :
    ∀ x ∈ (Submission.PSL2.diagPSLHom (GaloisField 2 n)).range,
      ∀ y ∈ (Submission.PSL2.diagPSLHom (GaloisField 2 n)).range, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [← map_mul, mul_comm, map_mul]

/-- The unipotent subgroup of `PSL(2, 2ⁿ)` is abelian: it is the image of the commutative
group `(K, +)`. -/
theorem psl2UnipotentComm (n : ℕ) :
    ∀ u ∈ (Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n)).range,
      ∀ v ∈ (Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n)).range, u * v = v * u := by
  intro u hu v hv
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  rw [← map_mul, mul_comm, map_mul]

/-- The Weyl element inverts the diagonal torus: `invertedBy T w = T` for
`T = (diagPSLHom K).range` and `w = weylPSL K`. -/
theorem psl2InvertedByDiag (n : ℕ) :
    (((Submission.PSL2.diagPSLHom (GaloisField 2 n)).range : Subgroup (PSL2Model n)) :
        Set (PSL2Model n))
      = Submission.Blueprint.invertedBy ((Submission.PSL2.diagPSLHom (GaloisField 2 n)).range)
          (Submission.PSL2.weylPSL (GaloisField 2 n)) := by
  ext x
  constructor
  · intro hx
    refine ⟨hx, ?_⟩
    obtain ⟨a, rfl⟩ := hx
    rw [Submission.PSL2.weylPSL_conj_diagPSLHom, map_inv]
  · intro hx
    exact hx.1

/-- The diagonal torus of `PSL(2, 2ⁿ)` is cyclic: it is the image of the cyclic group `Kˣ`. -/
theorem psl2IsCyclicDiag (n : ℕ) :
    IsCyclic ((Submission.PSL2.diagPSLHom (GaloisField 2 n)).range : Subgroup (PSL2Model n)) := by
  haveI : IsCyclic ((GaloisField 2 n)ˣ) := inferInstance
  exact isCyclic_of_surjective
    (MonoidHom.rangeRestrict (Submission.PSL2.diagPSLHom (GaloisField 2 n)))
    (MonoidHom.rangeRestrict_surjective _)

/-- The diagonal torus of `PSL(2, 2ⁿ)` has at least two elements for `n ≥ 2`:
`|T| = 2ⁿ - 1 ≥ 3`. -/
theorem psl2K0two (n : ℕ) (hn : 2 ≤ n) :
    2 ≤ Nat.card ↥((Submission.PSL2.diagPSLHom (GaloisField 2 n)).range) := by
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  rw [Submission.PSL2.card_diagPSLHom_range,
    GaloisField.card (p := 2) (n := n) (by omega)]
  have h3 : 3 ≤ 2 ^ n := by
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

/-- The Borel subgroup `B` of `PSL(2, 2ⁿ)` (the stabilizer of a point of the projective line)
has exactly `2ⁿ - 1` involutions.

`B = U ⋊ T` with `U` the unipotent radical (elementary abelian of order `2ⁿ`) and `T` the
diagonal torus (of odd order).  Every involution of `B` lies in `U`
(`Work.Models.Abstract.involutions_subset_U`, from `B/U ≅ T` of odd order), and every
non-identity element of `U` is an involution, so the involutions of `B` are exactly the
non-identity elements of `U`: `2ⁿ - 1` of them. -/
theorem psl2NcardInvolutionsStab (n : ℕ) (hn : 2 ≤ n) :
    (Submission.Blueprint.involutions
      ((MulAction.stabilizer (PSL2Model n) (Submission.PSL2.pt0 (GaloisField 2 n)) :
        Subgroup (PSL2Model n)) : Set (PSL2Model n))).ncard = 2 ^ n - 1 := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  set P := Submission.PSL2.pSL2BenderPair n hn with hP
  have hB : P.B = MulAction.stabilizer (PSL2Model n) (Submission.PSL2.pt0 (GaloisField 2 n)) :=
    rfl
  have hU : P.U = (Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n)).range := rfl
  have hsq : ∀ u ∈ (P.U : Set (PSL2Model n)), u * u = 1 := by
    intro u hu
    rw [hU] at hu
    exact psl2UnipotentSqOne n u hu
  have hset : Submission.Blueprint.involutions (P.B : Set (PSL2Model n))
      = (P.U : Set (PSL2Model n)) \ {1} := by
    ext x
    constructor
    · intro hx
      refine ⟨Work.Models.Abstract.involutions_subset_U P hx, ?_⟩
      rintro rfl
      exact absurd hx.2 (by simp)
    · rintro ⟨hxU, hx1⟩
      refine ⟨P.U_le_B hxU, ?_⟩
      rw [orderOf_eq_prime_iff]
      exact ⟨by rw [pow_two]; exact hsq x hxU, hx1⟩
  rw [← hB, hset,
    Set.ncard_sdiff (by simp : ({1} : Set (PSL2Model n)) ⊆ (P.U : Set (PSL2Model n))),
    Set.ncard_singleton]
  have h1 : ((P.U : Set (PSL2Model n))).ncard = Nat.card ↥P.U := rfl
  rw [h1, hU, Submission.PSL2.card_unipotentPSLHom_range n (by omega)]

theorem pSL2ModelData (n : ℕ) (hn : 2 ≤ n) :
    Nonempty (Work.Models.ModelData (LeanEval.GroupTheory.Defs.PSL2Model n)) := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hK0card : Nat.card ↥((Submission.PSL2.diagPSLHom (GaloisField 2 n)).range)
      = (Submission.Blueprint.involutions
          ((Submission.PSL2.pSL2BenderPair n hn).B : Set (PSL2Model n))).ncard := by
    change Nat.card ↥((Submission.PSL2.diagPSLHom (GaloisField 2 n)).range)
      = (Submission.Blueprint.involutions
          ((MulAction.stabilizer (PSL2Model n) (Submission.PSL2.pt0 (GaloisField 2 n)) :
            Subgroup (PSL2Model n)) : Set (PSL2Model n))).ncard
    rw [psl2NcardInvolutionsStab n hn,
      Submission.PSL2.card_diagPSLHom_range,
      GaloisField.card (p := 2) (n := n) (by omega)]
  refine ⟨{ Submission.PSL2.pSL2BenderPair n hn with
    K0 := (Submission.PSL2.diagPSLHom (GaloisField 2 n)).range
    hTab := psl2DiagComm n
    hww := Submission.PSL2.weylPSL_mul_self
    hK0 := psl2InvertedByDiag n
    hK0cyc := psl2IsCyclicDiag n
    hK0card := hK0card
    hK0two := psl2K0two n hn
    hUinv := fun u hu _ v hv => psl2UnipotentComm n u hu v hv }⟩

end Work.Models.ModelData
