import Mathlib
import Submission.Work.BSLit.Defs
import Submission.Work.BSLit.Wielandt.TIInfBot
import Submission.Work.BSLit.Wielandt.NormalOfNorm
import Submission.Work.BSLit.Wielandt.IsComplementOf
import Submission.Work.BSLit.Wielandt.EqOfMulEqMul
import Submission.Work.BSLit.Wielandt.ConjExistUnique

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.BSLit.Wielandt

open Classical

variable {F : Type*} [Group F] [Fintype F]

/-! ## Coefficient extraction in the integral group algebra

The auxiliary lemmas below compute the coefficients (in the group algebra `ℤ[F]`) of
`groupSum` and of `conjSum`.  Everything else is reduction to the counting statement
`Work.BSLit.Wielandt.conjSum_coeff`. -/

/-- The coefficient of `1_H = Σ_{h ∈ H} h` at `g`. -/
lemma groupSum_coeff (H : Subgroup F) (g : F) :
    (groupSum H).coeff g = if g ∈ H then (1 : ℤ) else 0 := by
  classical
  rw [groupSum]
  rw [MonoidAlgebra.coeff_sum]
  rw [Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_single]
  by_cases hg : g ∈ H
  · rw [if_pos hg]
    rw [Finset.sum_eq_single (⟨g, hg⟩ : H)]
    · rw [Finsupp.single_eq_same]
    · intro b _ hb
      rw [Finsupp.single_eq_of_ne]
      intro hcon
      exact hb (Subtype.ext hcon.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hg]
    apply Finset.sum_eq_zero
    intro b _
    rw [Finsupp.single_eq_of_ne]
    intro hcon
    exact hg (hcon ▸ b.2)

/-- A sum of the indicators of a predicate which holds for exactly one element. -/
lemma sum_ite_one_of_unique {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (h : ∃! x, p x) : (∑ x : α, (if p x then (1 : ℤ) else 0)) = 1 := by
  obtain ⟨c, hc, huniq⟩ := h
  have hcongr : ∀ x : α, (if p x then (1 : ℤ) else 0) = (if x = c then (1 : ℤ) else 0) := by
    intro x
    by_cases hx : p x
    · rw [if_pos hx, if_pos (huniq x hx)]
    · rw [if_neg hx, if_neg (fun h : x = c => hx (h.symm ▸ hc))]
  calc (∑ x : α, (if p x then (1 : ℤ) else 0))
      = ∑ x : α, (if x = c then (1 : ℤ) else 0) := Finset.sum_congr rfl (fun x _ => hcongr x)
    _ = 1 := by rw [Finset.sum_ite_eq']; simp

/-- A sum of the indicators of a constant proposition. -/
lemma sum_ite_const {α : Type*} [Fintype α] (c : Prop) [Decidable c] :
    (∑ _ : α, (if c then (1 : ℤ) else 0)) = if c then (Nat.card α : ℤ) else 0 := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]
    simp [Finset.sum_const, Nat.card_eq_fintype_card]
  · rw [if_neg hc, if_neg hc]
    simp

/-- **The coefficient of `conjSum`.** Writing `g = k q` for the (unique) decomposition of `g`
as a product of an element of `K` and an element of `P`, the coefficient of `Σ_{x ∈ K} 1_{xPx⁻¹}`
at `g` counts the `x ∈ K` with `x q x⁻¹ = g`.  For `q ≠ 1` there is exactly one such `x`
(`Work.BSLit.Wielandt.ConjExistUnique`), while for `q = 1` (i.e. `g ∈ K`) the condition becomes
`g = 1` and all `|K|` elements of `K` contribute. -/
lemma conjSum_coeff (K P : Subgroup F) (hsup : K ⊔ P = ⊤)
    (hnorm : ∀ g ∈ P, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hTI : ∀ k ∈ K, k ≠ 1 → P ⊓ P.map (MulAut.conj k⁻¹) = ⊥) (g : F) :
    (conjSum K P).coeff g
      = if g ∈ K then (if g = 1 then (Nat.card K : ℤ) else 0) else 1 := by
  classical
  have hdisj : K ⊓ P = ⊥ := TIInfBot K P hTI
  have hcompl : Subgroup.IsComplement' K P := IsComplementOf K P hsup hnorm hdisj
  obtain ⟨x0, hx0, huniq⟩ := Subgroup.IsComplement.existsUnique hcompl g
  set kg : K := x0.1 with hkg
  set qg : P := x0.2 with hqg
  have hg : (kg : F) * (qg : F) = g := hx0
  -- the coefficient is the sum of the indicators of `x qg x⁻¹ = g`
  have hcoeff : (conjSum K P).coeff g
      = ∑ x : K, (if (x : F) * (qg : F) * (x : F)⁻¹ = g then (1 : ℤ) else 0) := by
    rw [conjSum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [groupSum_coeff]
    have hiff : g ∈ P.map (MulAut.conj (x : F)) ↔ (x : F) * (qg : F) * (x : F)⁻¹ = g := by
      constructor
      · intro h
        obtain ⟨p, hpP, hp⟩ := Subgroup.mem_map.mp h
        have hp' : (x : F) * p * (x : F)⁻¹ = g := by
          have hp'' : (MulAut.conj (x : F)) p = g := hp
          rw [MulAut.conj_apply] at hp''
          exact hp''
        have hmem : (x : F) * p * (x : F)⁻¹ * p⁻¹ ∈ K := by
          have h1 : p * (x : F) * p⁻¹ ∈ K := hnorm p hpP (x : F) x.2
          have h2 : (p * (x : F) * p⁻¹)⁻¹ ∈ K := K.inv_mem h1
          have h3 : (x : F) * (p * (x : F) * p⁻¹)⁻¹ ∈ K := K.mul_mem x.2 h2
          convert h3 using 1
          group
        have hsp : (↑(⟨(x : F) * p * (x : F)⁻¹ * p⁻¹, hmem⟩ : K) : F) * (↑(⟨p, hpP⟩ : P) : F)
            = (kg : F) * (qg : F) := by
          rw [hg, ← hp']
          group
        have hpe : (↑(⟨p, hpP⟩ : P) : F) = (qg : F) :=
          congrArg Subtype.val (EqOfMulEqMul K P hdisj hsp).2
        rw [← hp', ← hpe]
      · intro h
        exact Subgroup.mem_map.mpr ⟨(qg : F), qg.2, by
          show (MulAut.conj (x : F)) (qg : F) = g
          rw [MulAut.conj_apply]; exact h⟩
    by_cases h : g ∈ P.map (MulAut.conj (x : F))
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc : (x : F) * (qg : F) * (x : F)⁻¹ = g => h (hiff.mpr hc))]
  rw [hcoeff]
  by_cases hq1 : (qg : F) = 1
  · -- `qg = 1`, i.e. `g = kg ∈ K`: value `|K|` or `0`
    have hg' : g = (kg : F) := by rw [← hg, hq1, mul_one]
    have hval : (∑ x : K, (if (x : F) * (qg : F) * (x : F)⁻¹ = g then (1 : ℤ) else 0))
        = if g = 1 then (Nat.card K : ℤ) else 0 := by
      have hcongr : ∀ x : K,
          (if (x : F) * (qg : F) * (x : F)⁻¹ = g then (1 : ℤ) else 0)
            = (if g = 1 then (1 : ℤ) else 0) := by
        intro x
        have hiff : ((x : F) * (qg : F) * (x : F)⁻¹ = g) ↔ g = 1 := by
          rw [hq1, mul_one, mul_inv_cancel, eq_comm]
        by_cases hx : (x : F) * (qg : F) * (x : F)⁻¹ = g
        · rw [if_pos hx, if_pos (hiff.mp hx)]
        · rw [if_neg hx, if_neg (fun hc : g = 1 => hx (hiff.mpr hc))]
      rw [Finset.sum_congr rfl (fun x _ => hcongr x), sum_ite_const]
    rw [hval]
    have hgK : g ∈ K := by rw [hg']; exact kg.2
    rw [if_pos hgK]
  · -- `qg ≠ 1`, i.e. `g ∉ K`: value `1`
    have hval : (∑ x : K, (if (x : F) * (qg : F) * (x : F)⁻¹ = g then (1 : ℤ) else 0)) = 1 := by
      have huniq' : ∃! x : K, (x : F) * (qg : F) * (x : F)⁻¹ = g := by
        obtain ⟨x, hx, hux⟩ := ConjExistUnique K P hnorm hTI qg hq1 kg
        exact ⟨x, by rw [← hg]; exact hx, fun y hy => hux y (by rw [hg]; exact hy)⟩
      exact sum_ite_one_of_unique _ huniq'
    rw [hval]
    have hgK : g ∉ K := by
      intro hk
      have hsp : (kg : F) * (qg : F)
          = (↑(⟨g, hk⟩ : K) : F) * (↑(⟨(1 : F), P.one_mem⟩ : P) : F) := by
        rw [hg, mul_one]
      have h2 := (EqOfMulEqMul K P hdisj hsp).2
      exact hq1 (by rw [h2])
    rw [if_neg hgK]

/-- **The Frobenius relation in the integral group algebra.** Let `F` be a finite group with subgroups `K`, `P` such that `F = K ⊔ P`, `P` normalises `K`, and `P ⊓ P ^ k = ⊥` for every `k ∈ K^#`. Then, in `ℤ[F]`, `Σ_{x ∈ K} 1_{xPx⁻¹} + 1_K = 1_F + |K| · 1`, where `1_H = Σ_{h ∈ H} h` (`Work.BSLit.groupSum`). Route: `K ⊓ P = ⊥` follows from the TI hypothesis (a nontrivial `x ∈ K ⊓ P` gives `P ^ x = P`, i.e. `x ∈ P ⊓ P * x`); so `F = K ⋊ P` and `|F| = |K| * |P|`; the `|K|` sets `(P^x)^#` are pairwise disjoint, all lie in `F ∖ K`, and their union has `|K| * (|P| - 1) = |F| - |K|` elements, hence it is all of `F ∖ K`; compare coefficients in `ℤ[F]`. -/
theorem FrobeniusRelation {F : Type*} [Group F] [Fintype F] (K P : Subgroup F)
    (hsup : K ⊔ P = ⊤)
    (hnorm : ∀ g ∈ P, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hTI : ∀ k ∈ K, k ≠ 1 → P ⊓ P.map (MulAut.conj k⁻¹) = ⊥) :
    conjSum K P + groupSum K = groupSum (⊤ : Subgroup F) + (Nat.card K : ℤ) • 1 := by
  classical
  apply MonoidAlgebra.ext
  ext g
  rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_add, Finsupp.add_apply]
  rw [conjSum_coeff K P hsup hnorm hTI g, groupSum_coeff K g,
    groupSum_coeff (⊤ : Subgroup F) g]
  simp only [Subgroup.mem_top, if_true]
  rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  rw [zsmul_eq_mul]
  by_cases hK : g ∈ K
  · rw [if_pos hK, if_pos hK]
    by_cases h1 : g = 1
    · rw [if_pos h1, if_pos h1.symm]; simp only [Int.cast_id]; ring
    · rw [if_neg h1, if_neg (fun h => h1 h.symm)]; simp only [Int.cast_id]; ring
  · rw [if_neg hK, if_neg hK]
    have h1 : g ≠ 1 := fun h => hK (h ▸ K.one_mem)
    rw [if_neg (fun h : (1 : F) = g => h1 h.symm)]; simp only [Int.cast_id]; ring

end Work.BSLit.Wielandt
