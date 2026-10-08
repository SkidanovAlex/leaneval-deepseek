/-
The Borel subgroup of `Sz(2^(2n+1))`: the Suzuki 2-group and the maximal torus.

The root (Suzuki) 2-group `U = {u(a,b)}` (of order `|F|^2`) and the diagonal torus
`T = {t(x)}` (isomorphic to `Fˣ`) generate the Borel subgroup `B = U ⋊ T ≤ SzModel n`.
This file records the action of `T` on `U` by conjugation,
`t(x) u(a,b) t(x)⁻¹ = u(x·a, x^(2^(n+1))·b)`, and the consequences.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Sz.Basic
import Submission.Work.Models.Port.Sz.TwoGroup
import Submission.Work.Models.Port.Sz.Torus
import Submission.Work.Models.Port.Commons.GroupTheory.Suzuki.szT_mul_szU

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end


set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Submission.Sz

/-- The Suzuki 2-group and the torus meet trivially: a matrix that is simultaneously
upper unitriangular and diagonal is the identity. -/
lemma szTwoGroup_inf_range_szTgHom (n : ℕ) :
    szTwoGroup n ⊓ (szTgHom n).range = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨hu, hT⟩ := hA
  obtain ⟨a, b, rfl⟩ := hu
  obtain ⟨x, hx⟩ := hT
  have hmat : szT n x = szU n a b := by
    have h := congrArg (fun u : GL (Fin 4) (SzField n) =>
      ((u : Matrix (Fin 4) (Fin 4) (SzField n)))) hx
    simpa [szTgHom_apply] using h
  have h01 := congrFun (congrFun hmat 0) 1
  have h02 := congrFun (congrFun hmat 0) 2
  simp only [szT_eq_diagonal, szU, Matrix.diagonal, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_two] at h01 h02
  simp at h01 h02
  rw [← h01, ← h02, szUg_zero]


/-- Scaled commutation of the torus with a root element:
`t(x)·u(a,b) = u(x·a, x^(2^(n+1)+1)·b)·t(x)`. -/
lemma szTg_mul_szUg (n : ℕ) (x : (SzField n)ˣ) (a b : SzField n) :
    szTg n x * szUg n a b =
      szUg n ((x : SzField n) * a) ((x : SzField n) ^ (1 + 2 ^ (n + 1)) * b) * szTg n x := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul, szUg_coe, szTg_coe]
  exact Commons.GroupTheory.Suzuki.szT_mul_szU n x a b

/-- Conjugation action of the torus on the Suzuki 2-group:
`t(x)·u(a,b)·t(x)⁻¹ = u(x·a, x^(2^(n+1)+1)·b)`. -/
lemma szTg_conj_szUg (n : ℕ) (x : (SzField n)ˣ) (a b : SzField n) :
    szTg n x * szUg n a b * (szTg n x)⁻¹ =
      szUg n ((x : SzField n) * a) ((x : SzField n) ^ (1 + 2 ^ (n + 1)) * b) := by
  rw [szTg_mul_szUg, mul_assoc, mul_inv_cancel, mul_one]

/-- The torus normalizes the Suzuki 2-group. -/
lemma szTgHom_range_le_normalizer (n : ℕ) :
    (szTgHom n).range ≤ Subgroup.normalizer (szTwoGroup n : Set (GL (Fin 4) (SzField n))) := by
  intro t ht
  obtain ⟨x, rfl⟩ := ht
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hx : (x : SzField n) ≠ 0 := Units.ne_zero x
  apply le_antisymm
  · rintro y ⟨A, hA, haeq⟩
    rw [← haeq]
    obtain ⟨a, b, rfl⟩ := hA
    change szTg n x * szUg n a b * (szTg n x)⁻¹ ∈ szTwoGroup n
    exact ⟨(x : SzField n) * a, (x : SzField n) ^ (1 + 2 ^ (n + 1)) * b,
      szTg_conj_szUg n x a b⟩
  · rintro y ⟨a, b, rfl⟩
    have h1 : (x : SzField n) * ((x : SzField n)⁻¹ * a) = a := by
      rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
    have h2 : (x : SzField n) ^ (1 + 2 ^ (n + 1))
        * (((x : SzField n) ^ (1 + 2 ^ (n + 1)))⁻¹ * b) = b := by
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx), one_mul]
    exact ⟨szUg n ((x : SzField n)⁻¹ * a) (((x : SzField n) ^ (1 + 2 ^ (n + 1)))⁻¹ * b),
      ⟨(x : SzField n)⁻¹ * a, ((x : SzField n) ^ (1 + 2 ^ (n + 1)))⁻¹ * b, rfl⟩,
      by
        change szTg n x
          * szUg n ((x : SzField n)⁻¹ * a) (((x : SzField n) ^ (1 + 2 ^ (n + 1)))⁻¹ * b)
          * (szTg n x)⁻¹ = szUg n a b
        rw [szTg_conj_szUg, h1, h2]⟩

/-- The Borel subgroup `B = U ⋊ T ≤ SzModel n` of the Suzuki group: the Suzuki
`2`-group together with the maximal torus. -/
noncomputable def szBorel (n : ℕ) : Subgroup (GL (Fin 4) (SzField n)) :=
  szTwoGroup n ⊔ (szTgHom n).range

lemma szBorel_le_szModel (n : ℕ) : szBorel n ≤ SzModel n :=
  sup_le (szTwoGroup_le_szModel n) (szTgHom_range_le_szModel n)


/-! ## The order of the Borel subgroup -/

lemma card_range_szTgHom (n : ℕ) :
    Nat.card (szTgHom n).range = Nat.card (SzField n) - 1 := by
  have h := Nat.card_congr (MonoidHom.ofInjective (szTgHom_injective n)).toEquiv
  rw [Nat.card_units] at h
  exact h.symm

/-- The Borel subgroup of `Sz(2^(2n+1))` has order `q^2 (q-1)` where `q = |F|`. -/
lemma card_szBorel (n : ℕ) :
    Nat.card (szBorel n) = Nat.card (SzField n) ^ 2 * (Nat.card (SzField n) - 1) := by
  have hcardU : Nat.card (szTwoGroup n) = Nat.card (SzField n) ^ 2 := card_szTwoGroup n
  have hcardT : Nat.card (szTgHom n).range = Nat.card (SzField n) - 1 := card_range_szTgHom n
  have hf : Function.Bijective
      (fun p : szTwoGroup n × (szTgHom n).range =>
        (⟨(p.1 : GL (Fin 4) (SzField n)) * (p.2 : GL (Fin 4) (SzField n)),
          Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
            (Subgroup.mem_sup_right p.2.2)⟩ : szBorel n)) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨u₁, t₁⟩ ⟨u₂, t₂⟩ h
      have h' : (u₁ : GL (Fin 4) (SzField n)) * t₁ = (u₂ : GL (Fin 4) (SzField n)) * t₂ :=
        Subtype.ext_iff.mp h
      have hmid : ((u₂ : GL (Fin 4) (SzField n))⁻¹ * u₁) * t₁ = (t₂ : GL (Fin 4) (SzField n)) := by
        rw [mul_assoc, h', inv_mul_cancel_left]
      have hU : (u₂ : GL (Fin 4) (SzField n))⁻¹ * u₁ ∈ szTwoGroup n :=
        mul_mem (inv_mem u₂.2) u₁.2
      have hT : (u₂ : GL (Fin 4) (SzField n))⁻¹ * u₁ ∈ (szTgHom n).range := by
        have hthis : (u₂ : GL (Fin 4) (SzField n))⁻¹ * u₁ =
            (t₂ : GL (Fin 4) (SzField n)) * (t₁ : GL (Fin 4) (SzField n))⁻¹ := by
          rw [← hmid, mul_assoc, mul_inv_cancel, mul_one]
        rw [hthis]; exact mul_mem t₂.2 (inv_mem t₁.2)
      have hbot : (u₂ : GL (Fin 4) (SzField n))⁻¹ * u₁ ∈ (⊥ : Subgroup _) := by
        rw [← szTwoGroup_inf_range_szTgHom n]; exact ⟨hU, hT⟩
      rw [Subgroup.mem_bot] at hbot
      have hu : u₁ = u₂ := Subtype.ext (inv_mul_eq_one.mp hbot).symm
      have ht : t₁ = t₂ := by
        have h2 : (u₁ : GL (Fin 4) (SzField n)) * t₁ =
            (u₁ : GL (Fin 4) (SzField n)) * t₂ := by rw [h', hu]
        exact Subtype.ext (mul_left_cancel h2)
      exact Prod.ext hu ht
    · intro A
      have hA : (A : GL (Fin 4) (SzField n)) ∈
          ((szTwoGroup n : Set (GL (Fin 4) (SzField n))) *
            ((szTgHom n).range : Set (GL (Fin 4) (SzField n)))) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left (szTwoGroup n) (szTgHom n).range
          (szTgHom_range_le_normalizer n)]
        exact A.2
      obtain ⟨u, hu, t, ht, hut⟩ := hA
      exact ⟨(⟨u, hu⟩, ⟨t, ht⟩), Subtype.ext hut⟩
  calc Nat.card (szBorel n)
      = Nat.card (szTwoGroup n × (szTgHom n).range) :=
        (Nat.card_congr (Equiv.ofBijective _ hf)).symm
    _ = Nat.card (szTwoGroup n) * Nat.card (szTgHom n).range := Nat.card_prod _ _
    _ = Nat.card (SzField n) ^ 2 * (Nat.card (SzField n) - 1) := by rw [hcardU, hcardT]


/-- The Borel subgroup of `Sz(2^(2n+1))` has order `2^(4n+2) * (2^(2n+1) - 1)`. -/
lemma card_szBorel_eq (n : ℕ) :
    Nat.card (szBorel n) = 2 ^ (4 * n + 2) * (2 ^ (2 * n + 1) - 1) := by
  rw [card_szBorel, card_szField, ← pow_mul]
  congr 1
  ring

end Submission.Sz
