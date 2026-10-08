/-
Feit--Thompson Lemma 7.2 (3): elementary utilities for the conjugaion action on `F/Φ(F)`.

* `Work.LocalPrelim.frattiniQuotConj_eq_one_of_mem` : elements of `F` act trivially on
  `↥F ⧸ Φ(↥F)` (inner automorphisms are trivial on the abelian quotient `F/Φ(F)`);
* `Work.LocalPrelim.fact_pow_eq_one_of_exponent_dvd` : an abelian group of exponent dividing `p`
  has all `p`-th powers equal to `1`;
* `Work.LocalPrelim.isMulCommutative_sylow_two_of_odd_card` : in a group of odd order every
  Sylow `2`-subgroup is abelian (it is trivial).
-/
import Mathlib
import Submission.Work.PGroup.All
import Submission.Work.LocalPrelim.Ft72Rep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise commutatorElement IsMulCommutative

namespace Work.LocalPrelim

variable {X : Type*} [Group X]

/-- Elements of `F` act trivially on the Frattini quotient `↥F ⧸ Φ(↥F)`: `F/Φ(F)` is abelian,
so inner automorphisms of `F` are trivial on it. -/
lemma frattiniQuotConj_eq_one_of_mem {p : ℕ} (hp : p.Prime) {F : Subgroup X} [F.Normal]
    [Finite ↥F] (hFp : IsPGroup p ↥F) {y : X} (hy : y ∈ F) :
    frattiniQuotConj F y = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H z =>
    rw [frattiniQuotConj_apply_mk, MulAut.one_apply, QuotientGroup.eq]
    have hyz : (MulAut.conjNormal y z)⁻¹ * z = ⁅(⟨y, hy⟩ : ↥F), z⁻¹⁆ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply,
        commutatorElement_def]
      group
    rw [hyz]
    have hmem : ⁅(⟨y, hy⟩ : ↥F), z⁻¹⁆ ∈ commutator ↥F := by
      rw [show commutator ↥F = ⁅(⊤ : Subgroup ↥F), ⊤⁆ from rfl]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    exact Work.PGroup.commutator_le_frattini hp hFp hmem

/-- An abelian group of exponent dividing `p` has all `p`-th powers equal to `1`. -/
lemma fact_pow_eq_one_of_exponent_dvd {H : Type*} [Monoid H] {p : ℕ}
    (h : Monoid.exponent H ∣ p) : Fact (∀ x : H, x ^ p = 1) :=
  ⟨(Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h)⟩

/-- In a finite group of odd order, every Sylow `2`-subgroup is trivial, hence abelian. -/
theorem isMulCommutative_sylow_two_of_odd_card {G : Type*} [Group G] [Finite G]
    (h : Odd (Nat.card G)) (Q : Sylow 2 G) : IsMulCommutative ↥(Q : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card ↥(Q : Subgroup G)) :=
    Odd.of_dvd_nat h (Subgroup.card_subgroup_dvd_card (Q : Subgroup G))
  have hk : Nat.card ↥(Q : Subgroup G) = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
    have hodd' : Odd (2 ^ k) := by rw [← hk]; exact hodd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr (dvd_pow_self 2 hk0))
    rw [hk, hk0, pow_zero]
  have hbot : (Q : Subgroup G) = ⊥ := Subgroup.card_eq_one.mp hk
  haveI : Subsingleton ↥(Q : Subgroup G) := by rw [hbot]; infer_instance
  exact isMulCommutative_iff.mpr fun a b => Subsingleton.elim _ _

end Work.LocalPrelim
