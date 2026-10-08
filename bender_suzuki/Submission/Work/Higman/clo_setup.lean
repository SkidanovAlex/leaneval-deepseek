import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.powSub_C_eq_of_cover
import Submission.Work.Higman.Fq_structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The group-theoretic reduction for Higman's Lemma 8: the squaring map `C/A → Ω₁(P)`

Let `P` be a Suzuki 2-group, `A` a `ξ`-invariant abelian normal subgroup (`2 ^ e` its exponent)
and `C` a normal `ξ`-subgroup with `C ^ (2) ≤ A` and `⁅C,C⁆ = A` (the hypotheses of Higman's
Lemma 8).

The map `s : C/A → Ω₁(P)`, `uA ↦ u ^ (2 ^ e)`, together with its polar form
`B : C/A × C/A → Ω₁(P)` (the commutator pairing) and the bracket pairing
`β : C/A × Ω₁(P) → Ω₁(P)`, is the data fed into the algebraic core
(`Submission/Work/Higman/clo_core.lean`).  This file collects the *elementwise* facts those maps
need: the definition makes sense (`u ^ 2 ^ e ∈ Ω₁`), it is well defined modulo `A`
(unipotence: `(u a) ^ 2 = u ^ 2 · (⁅u⁻¹,a⁆ · a²)` with `a² ∈ A²` and `⁅u⁻¹,a⁆ ∈ A²`) and
`ξ`-equivariant.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- For `x ∈ A` (with `2 ^ e` the exponent of the homocyclic group `A`) the power
`x ^ 2 ^ (e-1)` is an involution. -/
theorem mem_omega1_pow_two_pow_sub_one (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A) {e : ℕ} (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) (he : 1 ≤ e)
    {x : P} (hx : x ∈ A) : x ^ 2 ^ (e - 1) ∈ omega1 P := by
  rw [h.mem_omega1, ← pow_mul,
    show 2 ^ (e - 1) * 2 = 2 ^ e from by rw [← pow_succ]; congr 1; omega]
  exact he1 x hx

/-- For `u ∈ C` the `2 ^ e`-th power of `u` lies in `Ω₁(P)`: this is the map
`s : C/A → Ω₁(P)` on representatives. -/
theorem pow_two_pow_mem_omega1 (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : IsXiAbelNormal h A) (hC2 : powSub C 2 ≤ A) {e : ℕ}
    (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) (he : 1 ≤ e) {u : P} (hu : u ∈ C) :
    u ^ 2 ^ e ∈ omega1 P := by
  have hsq : u ^ 2 ∈ A := hC2 (pow_mem_powSub hu)
  have hpow : u ^ 2 ^ e = (u ^ 2) ^ 2 ^ (e - 1) := by
    rw [← pow_mul,
      show 2 * 2 ^ (e - 1) = 2 ^ e from by rw [← pow_succ']; congr 1; omega]
  rw [hpow]
  exact mem_omega1_pow_two_pow_sub_one h hA he1 he hsq

/-- **Well-definedness of `s`.**  For `u ∈ C` and `a ∈ A` the `2 ^ e`-th powers of `u` and
`u * a` agree: `(u * a) ^ 2 ^ e = u ^ 2 ^ e`. -/
theorem pow_two_pow_mul_mem (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : IsXiAbelNormal h A) (hC2 : powSub C 2 ≤ A) {e : ℕ}
    (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) (he : 1 ≤ e) {u : P} (hu : u ∈ C) {a : P} (ha : a ∈ A) :
    (u * a) ^ 2 ^ e = u ^ 2 ^ e := by
  have hmul : ∀ x : P, x ^ 2 ^ e = (x ^ 2) ^ 2 ^ (e - 1) := by
    intro x
    rw [← pow_mul,
      show 2 * 2 ^ (e - 1) = 2 ^ e from by rw [← pow_succ']; congr 1; omega]
  have hmemA : ⁅u⁻¹, a⁆ ∈ powSub A 2 := commutator_mem_powSub_two h hA u⁻¹ a ha
  have hc : (u * a) ^ 2 = u ^ 2 * (⁅u⁻¹, a⁆ * a ^ 2) := by
    rw [commutatorElement_def]
    simp only [pow_two]
    group
  have hcA2 : ⁅u⁻¹, a⁆ * a ^ 2 ∈ powSub A 2 :=
    Subgroup.mul_mem _ hmemA (pow_mem_powSub ha)
  obtain ⟨d, hdA, hd⟩ := (mem_powSub_iff hA.abelian).mp hcA2
  have hmem1 : u ^ 2 ∈ A := hC2 (pow_mem_powSub hu)
  have hcomm : Commute (u ^ 2) d := hA.abelian _ hmem1 _ hdA
  have hstep : (u ^ 2 * d ^ 2) ^ 2 ^ (e - 1) =
      (u ^ 2) ^ 2 ^ (e - 1) * (d ^ 2) ^ 2 ^ (e - 1) := by
    rw [pow_two d]
    exact (hcomm.mul_right hcomm).mul_pow _
  rw [hmul (u * a), hmul u, hc, ← hd, hstep, ← hmul d, he1 d hdA, mul_one]

/-- `ξ` commutes with the `2 ^ e`-th power map (equivariance of `s`). -/
theorem pow_two_pow_xi (h : IsSuzuki2Grp P) {e : ℕ} {u : P} :
    h.xi (u ^ 2 ^ e) = (h.xi u) ^ 2 ^ e := by
  rw [map_pow]

/-- **(d) `ξ` is transitive on the non-identity elements of `Ω₁(P)`.**  The non-identity elements
of `Ω₁(P)` are exactly the involutions, on which `ξ` is transitive by definition of a Suzuki
2-group. -/
theorem xi_trans_omega1 (h : IsSuzuki2Grp P) {x y : P}
    (hx : x ∈ omega1 P) (hy : y ∈ omega1 P) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ k : ℕ, (h.xi ^ k) x = y := by
  have hx2 : orderOf x = 2 := by
    have hd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (h.mem_omega1.mp hx)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h2
  have hy2 : orderOf y = 2 := by
    have hd : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (h.mem_omega1.mp hy)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hy1
    · exact h2
  exact h.trans x y hx2 hy2


end Work.Higman
