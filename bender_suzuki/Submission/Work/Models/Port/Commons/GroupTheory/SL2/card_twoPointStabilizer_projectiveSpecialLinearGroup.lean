import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Submission.Work.Models.Port.Commons.LinearAlgebra.Matrix.card_PSL2_charTwo
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.isMultiplyPretransitive_projectiveSpecialLinearGroup_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped LinearAlgebra.Projectivization

set_option linter.style.haveILetI false

namespace Commons.GroupTheory.SL2

/-- Orbit-stabilizer theorem, stated with `Nat.card`: for an action of a group `G` on `X`
and any point `x : X`, the product of the cardinalities of the orbit and the stabilizer of `x`
equals the cardinality of `G`. -/
theorem natCard_orbit_mul_natCard_stabilizer {G X : Type*} [Group G] [MulAction G X] (x : X) :
    Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) = Nat.card G := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G x)

/-- In characteristic two, the stabilizer in `PSL(2,K)` of two distinct points of the projective
line `ℙ K (Fin 2 → K)` has `Nat.card K - 1` elements: the pointwise stabilizer of a pair of
points of the projective line is the split torus of order `q - 1`. -/
theorem card_twoPointStabilizer_projectiveSpecialLinearGroup {K : Type*} [Field K] [Fintype K]
    (hchar : CharP K 2) (hcard : 2 ≤ Nat.card K)
    (a b : Projectivization K (Fin 2 → K)) (hab : a ≠ b) :
    Nat.card ((MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) a ⊓
      MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) b :
        Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))) = Nat.card K - 1 := by
  classical
  let G := Matrix.ProjectiveSpecialLinearGroup (Fin 2) K
  let α := Projectivization K (Fin 2 → K)
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype G := Fintype.ofFinite G
  haveI : CharP K 2 := hchar
  change Nat.card ((MulAction.stabilizer G a ⊓ MulAction.stabilizer G b : Subgroup G)) =
    Nat.card K - 1
  -- The embedding `Fin 2 ↪ α` given by the distinct pair `(a, b)`.
  let e : Fin 2 ↪ α := Function.Embedding.embFinTwo hab
  -- Fixing `e` pointwise is the same as fixing both `a` and `b`.
  have hstab : MulAction.stabilizer G e =
      (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b : Subgroup G) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
      MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have h0 := congrArg (fun f : Fin 2 ↪ α => f 0) h
        simpa [e, Function.Embedding.embFinTwo_apply_zero] using h0
      · have h1 := congrArg (fun f : Fin 2 ↪ α => f 1) h
        simpa [e, Function.Embedding.embFinTwo_apply_one] using h1
    · rintro ⟨h0, h1⟩
      ext i
      fin_cases i
      · simpa [e, Function.Embedding.embFinTwo_apply_zero] using h0
      · simpa [e, Function.Embedding.embFinTwo_apply_one] using h1
  -- The action is 2-transitive, so the orbit of `e` is all of `Fin 2 ↪ α`.
  have hmult : MulAction.IsMultiplyPretransitive G α 2 :=
    isMultiplyPretransitive_projectiveSpecialLinearGroup_two (K := K)
  have horbit : MulAction.orbit G e = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [MulAction.mem_orbit_iff]
    exact hmult.exists_smul_eq e x
  -- The projective line has `q + 1` points.
  have hcard_α : Nat.card α = Nat.card K + 1 := by
    rw [show α = Projectivization K (Fin 2 → K) from rfl]
    rw [Projectivization.card_of_finrank_two K (Fin 2 → K) (Module.finrank_fin_fun K (n := 2))]
  -- Hence the orbit has `q * (q + 1)` elements.
  have hcard_orbit : Nat.card (MulAction.orbit G e) = Nat.card K * (Nat.card K + 1) := by
    rw [horbit, Nat.card_congr (Equiv.Set.univ (Fin 2 ↪ α))]
    rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin]
    rw [← Nat.card_eq_fintype_card, hcard_α]
    rw [Nat.descFactorial_succ, Nat.descFactorial_one]
    simp
  have hcard_stab : Nat.card (MulAction.stabilizer G e) =
      Nat.card (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b : Subgroup G) := by
    rw [hstab]
  -- `|PSL(2,K)| = q (q² - 1)` in characteristic two.
  have hcard_PSL : Nat.card G = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [show G = Matrix.ProjectiveSpecialLinearGroup (Fin 2) K from rfl]
    rw [Commons.LinearAlgebra.Matrix.card_PSL2_charTwo (F := K)]
    simp [Nat.card_eq_fintype_card]
  -- Orbit-stabilizer: `q (q + 1) * |Stab| = q (q² - 1)`.
  have hos := natCard_orbit_mul_natCard_stabilizer (G := G) e
  rw [hcard_orbit, hcard_stab, hcard_PSL] at hos
  -- Cancel the common factor `q (q + 1)`.
  have hqpos : 0 < Nat.card K * (Nat.card K + 1) := by
    have : 0 < Nat.card K := by omega
    positivity
  have hsq : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
    simpa using Nat.sq_sub_sq (Nat.card K) 1
  rw [hsq] at hos
  rw [← mul_assoc] at hos
  exact Nat.mul_left_cancel hqpos hos

end Commons.GroupTheory.SL2