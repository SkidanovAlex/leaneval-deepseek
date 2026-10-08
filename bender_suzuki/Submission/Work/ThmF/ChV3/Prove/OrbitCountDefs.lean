import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Vocabulary for the orbit count of `orbit_count_101`

`Work.ThmF.ChV3.Prove.orbit_count_101` counts the `N_G(R)`-orbit of `P` in the case (10-1) of
Peterfalvi II Ch. V §3 step (12).  The orbit is `orb P (NG R)`, and the set counted against
`C_Q(P)` is `AT R T P` (the subgroups of `R` of order `|P|` not contained in `T` and different
from `P`, the `𝒜` of the source's orbit count).

The `cj_*` lemmas below are the basic bookkeeping for the conjugation action `cj g A = gAg⁻¹`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.ThmF.ChV3.Prove

open Work.ThmF.ChV3

variable {G : Type} [Group G]

/-- The orbit of the subgroup `P` under conjugation by the subgroup `S`. -/
def orb (P S : Subgroup G) : Set (Subgroup G) := {A | ∃ g ∈ S, A = cj g P}

/-- The set of subgroups `A ≤ R` with `Nat.card A = Nat.card P`, `A ⊄ T` and `A ≠ P`. -/
def AT (R T P : Subgroup G) : Set (Subgroup G) :=
  {A | A ≤ R ∧ Nat.card A = Nat.card P ∧ ¬ A ≤ T ∧ A ≠ P}

@[simp] lemma cj_one (A : Subgroup G) : cj 1 A = A := by
  have h1 : cj (1 : G) A = ConjAct.toConjAct (1 : G) • A := rfl
  rw [h1, ConjAct.toConjAct_one, one_smul]

lemma cj_mul (a b : G) (A : Subgroup G) : cj (a * b) A = cj a (cj b A) := by
  have h1 : cj (a * b) A = ConjAct.toConjAct (a * b) • A := rfl
  have h2 : cj a (cj b A) = ConjAct.toConjAct a • (ConjAct.toConjAct b • A) := rfl
  rw [h1, h2, ConjAct.toConjAct_mul, mul_smul]

lemma cj_inv_cj (a : G) (A : Subgroup G) : cj a⁻¹ (cj a A) = A := by
  rw [← cj_mul, inv_mul_cancel, cj_one]

lemma cj_cj_inv (a : G) (A : Subgroup G) : cj a (cj a⁻¹ A) = A := by
  rw [← cj_mul, mul_inv_cancel, cj_one]

lemma card_cj (a : G) (A : Subgroup G) : Nat.card ↥(cj a A) = Nat.card ↥A := by
  rw [cj]
  exact Subgroup.card_map_of_injective (MulAut.conj a).injective

lemma cj_mono {A B : Subgroup G} (h : A ≤ B) (a : G) : cj a A ≤ cj a B := Subgroup.map_mono h

lemma cj_eq_self_iff (a : G) (H : Subgroup G) : cj a H = H ↔ a ∈ NG H := by
  have h1 : cj a H = ConjAct.toConjAct a • H := rfl
  rw [h1, Subgroup.conjAct_pointwise_smul_iff]

lemma mem_cj_iff (a : G) (A : Subgroup G) (y : G) : y ∈ cj a A ↔ a⁻¹ * y * a ∈ A := by
  rw [cj, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hx'⟩
    have hx'' : x = a⁻¹ * y * a := by
      rw [← hx']
      simp [MulAut.conj_apply, mul_assoc]
    rw [hx''] at hx
    exact hx
  · intro hy
    exact ⟨a⁻¹ * y * a, hy, by simp [MulAut.conj_apply, mul_assoc]⟩

end Work.ThmF.ChV3.Prove
