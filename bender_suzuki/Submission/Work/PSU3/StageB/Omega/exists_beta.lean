import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.GaloisField.card_SZ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.PSU3.StageB.Omega

open Work.PSU3
open Classical

variable {n : ℕ}

/-! ## The additive Artin–Schreier map on the fixed field

We prove that the map `T ↦ T*T + T` of `E n = GF(2^{2n})` attains every value of the fixed
field `F = E n^{σE} = GF(2^n)`.  The argument is elementary: `Q : a ↦ a*a + a` is an additive
map of `F` with kernel `{0,1}`, so `Q(F)` is a subgroup of index `2` of `F`.  If `w₀ + σE w₀ = 1`
then `Q(w₀) = w₀*w₀ + w₀ ∉ Q(F)`, hence `F = Q(F) ∪ (Q(w₀) + Q(F))`; and both pieces are values
of `T ↦ T*T + T` on `E n` (`T = a` resp. `T = w₀ + a`). -/

/-- The fixed field `E n^{σE}` as an additive subgroup of `E n`. -/
noncomputable def Fadd (n : ℕ) : AddSubgroup (E n) where
  carrier := {x | σE x = x}
  zero_mem' := map_zero σE
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, ha, hb]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_neg, ha]

/-- The Artin–Schreier map `x ↦ x * x + x` on the fixed field, as an additive homomorphism. -/
noncomputable def QF (n : ℕ) : Fadd n →+ Fadd n where
  toFun a := ⟨(a : E n) * (a : E n) + (a : E n), by
    have ha : σE (a : E n) = (a : E n) := a.2
    show σE ((a : E n) * (a : E n) + (a : E n)) = (a : E n) * (a : E n) + (a : E n)
    rw [map_add, map_mul, ha]⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' a b := by
    apply Subtype.ext
    show ((a : E n) + (b : E n)) * ((a : E n) + (b : E n)) + ((a : E n) + (b : E n))
      = ((a : E n) * (a : E n) + (a : E n)) + ((b : E n) * (b : E n) + (b : E n))
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

lemma card_Fadd (hn : 1 ≤ n) : Nat.card (Fadd n) = 2 ^ n := by
  have h := Work.PSU3.GaloisField.fixedField_card n hn
  have e : ↥(Fadd n) ≃ {x : E n // iterateFrobenius (GaloisField 2 (2 * n)) 2 n x = x} :=
    Equiv.subtypeEquivRight (fun x => by rw [Fadd]; rfl)
  rw [Nat.card_congr e, h]

/-- The kernel of `x ↦ x * x + x` on the fixed field is `{0,1}`. -/
lemma QF_ker_card (n : ℕ) : Nat.card ↥((QF n).ker) = 2 := by
  rw [Nat.card_eq_two_iff]
  have hx0 : (⟨(0 : E n), by simp [Fadd]⟩ : ↥(Fadd n)) ∈ (QF n).ker := by
    rw [AddMonoidHom.mem_ker, Subtype.ext_iff]
    show (0 : E n) * 0 + 0 = 0
    ring
  have hx1 : (⟨(1 : E n), by simp [Fadd]⟩ : ↥(Fadd n)) ∈ (QF n).ker := by
    rw [AddMonoidHom.mem_ker, Subtype.ext_iff]
    show (1 : E n) * 1 + 1 = 0
    rw [one_mul, CharTwo.add_self_eq_zero]
  refine ⟨⟨⟨0, by simp [Fadd]⟩, hx0⟩, ⟨⟨1, by simp [Fadd]⟩, hx1⟩, ?_, ?_⟩
  · intro h
    have := congrArg (fun z : ↥((QF n).ker) => (((z : ↥(Fadd n)) : E n))) h
    simp at this
  · ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    have hzk : (QF n) z.1 = 0 := AddMonoidHom.mem_ker.mp z.2
    have hzv : (((z.1 : ↥(Fadd n)) : E n)) * (((z.1 : ↥(Fadd n)) : E n))
        + (((z.1 : ↥(Fadd n)) : E n)) = 0 := by
      have := congrArg (fun y : ↥(Fadd n) => (y : E n)) hzk
      simpa [QF] using this
    have hmul : (((z.1 : ↥(Fadd n)) : E n)) * ((((z.1 : ↥(Fadd n)) : E n)) + 1) = 0 := by
      rw [mul_add, mul_one, hzv]
    rcases mul_eq_zero.mp hmul with h0 | h1
    · left
      exact Subtype.ext (Subtype.ext h0)
    · right
      have hv1 : (((z.1 : ↥(Fadd n)) : E n)) = 1 := by
        have hh : (((z.1 : ↥(Fadd n)) : E n)) - 1 = 0 := by
          rw [sub_eq_add_neg, CharTwo.neg_eq]
          exact h1
        exact sub_eq_zero.mp hh
      exact Subtype.ext (Subtype.ext hv1)

/-- The range of `QF` has index `2` in the fixed field. -/
lemma QF_range_index (hn : 1 ≤ n) : ((QF n).range).index = 2 := by
  have hker : Nat.card ↥((QF n).ker) = 2 := QF_ker_card n
  have hkidx : (QF n).ker.index = Nat.card ↥((QF n).range) := AddSubgroup.index_ker (QF n)
  have hcard : Nat.card ↥((QF n).ker) * (QF n).ker.index = Nat.card ↥(Fadd n) :=
    AddSubgroup.card_mul_index (QF n).ker
  have hF : Nat.card ↥(Fadd n) = 2 ^ n := card_Fadd hn
  have hmain : 2 * Nat.card ↥((QF n).range) = 2 ^ n := by
    have := hcard
    rw [hker, hkidx, hF] at this
    exact this
  have hcard2 : Nat.card ↥((QF n).range) * ((QF n).range).index = 2 ^ n := by
    have := AddSubgroup.card_mul_index (QF n).range
    rw [hF] at this
    exact this
  have hpos : 0 < Nat.card ↥((QF n).range) := Nat.card_pos
  have h2 : Nat.card ↥((QF n).range) * ((QF n).range).index
      = Nat.card ↥((QF n).range) * 2 := by
    rw [hcard2, ← hmain, Nat.mul_comm]
  exact Nat.mul_left_cancel hpos h2

/-- There is an element of `E n` of trace `1` (`x + x^q = 1`). -/
lemma exists_tr_one (hn : 1 ≤ n) : ∃ w : E n, w + σE w = 1 := by
  obtain ⟨t, ht⟩ := Work.PSU3.GaloisField.exists_iterateFrobenius_ne_self n hn
  exact Work.PSU3.GaloisField.trace_surjective_of_exists_ne_fixed (E n)
    ⟨t, show σE t ≠ t from ht⟩ 1 (map_one σE)

/-- **Artin–Schreier solvability on the fixed field.**  Every `σE`-fixed element of `E n` is of
the form `T * T + T`. -/
lemma artin_schreier_fixed' (hn : 1 ≤ n) {c : E n} (hc : σE c = c) :
    ∃ T : E n, T * T + T = c := by
  obtain ⟨w, hw⟩ := exists_tr_one hn
  have hsw : σE w = w + 1 := by
    rw [← hw, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hn0mem : σE (w * w + w) = w * w + w := by
    have hww : w * w + w = w * σE w := by rw [hsw]; ring
    rw [hww, map_mul, σE_σE]
    ring
  let n0 : Fadd n := ⟨w * w + w, hn0mem⟩
  have hselfzero : ∀ x : ↥(Fadd n), x + x = 0 := by
    intro x
    apply Subtype.ext
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_zero]
    exact CharTwo.add_self_eq_zero (x : E n)
  have hn0notin : n0 ∉ (QF n).range := by
    rw [AddMonoidHom.mem_range]
    rintro ⟨a, ha⟩
    have haval : (a : E n) * (a : E n) + (a : E n) = w * w + w := by
      have := congrArg (fun y : ↥(Fadd n) => (y : E n)) ha
      simpa [QF, n0] using this
    have key : w * w + (a : E n) * (a : E n) = w + (a : E n) := by
      have h0 : (a : E n) * (a : E n) + w * w + ((a : E n) + w) = 0 := by
        rw [show (a : E n) * (a : E n) + w * w + ((a : E n) + w)
            = ((a : E n) * (a : E n) + (a : E n)) + (w * w + w) from by ring,
          haval, CharTwo.add_self_eq_zero]
      rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h0
      rw [show w * w + (a : E n) * (a : E n) = (a : E n) * (a : E n) + w * w from by ring,
        h0]
      ring
    have hsq : (w + (a : E n)) * (w + (a : E n)) = w + (a : E n) := by
      rw [show (w + (a : E n)) * (w + (a : E n)) = w * w + (a : E n) * (a : E n) from by
        ring_nf
        simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero], key]
    have hroot : (w + (a : E n)) = 0 ∨ (w + (a : E n)) = 1 := by
      have hmul : (w + (a : E n)) * ((w + (a : E n)) - 1) = 0 := by
        rw [mul_sub, mul_one, hsq, sub_self]
      rcases mul_eq_zero.mp hmul with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (sub_eq_zero.mp h1)
    have hwF : σE w = w := by
      rcases hroot with h0 | h1
      · have hwa : w = - (a : E n) := eq_neg_of_add_eq_zero_left h0
        rw [hwa, map_neg, a.2, CharTwo.neg_eq]
      · have hwa : w = 1 - (a : E n) := eq_sub_of_add_eq h1
        rw [hwa, map_sub, map_one, a.2]
    have h10 : (1 : E n) = 0 := add_left_cancel (a := w) (by rw [add_zero]; exact hsw.symm.trans hwF)
    exact one_ne_zero h10
  have hindex : ((QF n).range).index = 2 := QF_range_index hn
  obtain ⟨a0, ha0⟩ := AddSubgroup.index_eq_two_iff.mp hindex
  have hn0a0 : n0 + a0 ∈ (QF n).range := by
    have := ha0 n0
    rw [xor_def] at this
    rcases this with ⟨h, _⟩ | ⟨hn, _⟩
    · exact h
    · exact absurd hn hn0notin
  have hcxor := ha0 (⟨c, hc⟩ : Fadd n)
  rw [xor_def] at hcxor
  rcases hcxor with ⟨hca_in, hc_notin⟩ | ⟨hc_in, _⟩
  · have hcn0mem : (⟨c, hc⟩ : Fadd n) + n0 ∈ (QF n).range := by
      have hsum : ((⟨c, hc⟩ : Fadd n) + a0) + (n0 + a0) = (⟨c, hc⟩ : Fadd n) + n0 := by
        rw [show ((⟨c, hc⟩ : Fadd n) + a0) + (n0 + a0)
            = ((⟨c, hc⟩ : Fadd n) + n0) + (a0 + a0) from by abel,
          hselfzero a0, add_zero]
      rw [← hsum]
      exact AddSubgroup.add_mem _ hca_in hn0a0
    rw [AddMonoidHom.mem_range] at hcn0mem
    obtain ⟨a, ha⟩ := hcn0mem
    refine ⟨w + (a : E n), ?_⟩
    have haval : (a : E n) * (a : E n) + (a : E n) = c + (w * w + w) := by
      have := congrArg (fun y : ↥(Fadd n) => (y : E n)) ha
      simpa [QF, n0] using this
    have key : (w + (a : E n)) * (w + (a : E n)) + (w + (a : E n))
        = (w * w + w) + ((a : E n) * (a : E n) + (a : E n)) := by
      ring_nf
      simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]
    rw [key, haval, ← add_assoc, add_comm (w * w + w) c, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  · rw [AddMonoidHom.mem_range] at hc_in
    obtain ⟨a, ha⟩ := hc_in
    refine ⟨(a : E n), ?_⟩
    have := congrArg (fun y : ↥(Fadd n) => (y : E n)) ha
    simpa [QF] using this

theorem exists_beta {n : ℕ} (hn : 1 ≤ n) (α : Work.PSU3.E n) (hα : σE α = α) :
    ∃ β : Work.PSU3.E n, β ≠ 0 ∧ β + β⁻¹ = α ∧ (σE β = β⁻¹ ∨ σE β = β) := by
  rcases eq_or_ne α 0 with h0 | hα0
  · subst h0
    exact ⟨1, one_ne_zero, by rw [inv_one, CharTwo.add_self_eq_zero], Or.inr (map_one σE)⟩
  · have hinv : σE α⁻¹ = α⁻¹ := by rw [map_inv₀, hα]
    have hc : σE (α⁻¹ * α⁻¹) = α⁻¹ * α⁻¹ := by rw [map_mul, hinv]
    obtain ⟨T, hT⟩ := artin_schreier_fixed' hn hc
    have hTne : T ≠ 0 := by
      intro h
      rw [h, mul_zero, zero_add] at hT
      exact mul_ne_zero (inv_ne_zero hα0) (inv_ne_zero hα0) hT.symm
    set β : E n := α * T with hβdef
    have hβne : β ≠ 0 := by rw [hβdef]; exact mul_ne_zero hα0 hTne
    have hβroot : β * β + α * β + 1 = 0 := by
      rw [hβdef]
      have hαα : α * α * (α⁻¹ * α⁻¹) = 1 := by
        rw [← mul_inv, mul_inv_cancel₀ (mul_ne_zero hα0 hα0)]
      rw [show (α * T) * (α * T) + α * (α * T) + 1 = α * α * (T * T + T) + 1 from by ring,
        hT, hαα, CharTwo.add_self_eq_zero]
    have hβsum : β + β⁻¹ = α := by
      have h2 : β * β + 1 = α * β := by
        have key : (β * β + 1) + α * β = 0 := by
          rw [show (β * β + 1) + α * β = β * β + α * β + 1 from by ring]
          exact hβroot
        rw [add_eq_zero_iff_eq_neg] at key
        rwa [CharTwo.neg_eq] at key
      have hmul : β * (β + β⁻¹) = β * α := by
        rw [mul_add, mul_inv_cancel₀ hβne, h2, mul_comm]
      exact mul_left_cancel₀ hβne hmul
    have hσcond : σE β = β⁻¹ ∨ σE β = β := by
      have hσroot : (σE β) * (σE β) + α * (σE β) + 1 = 0 := by
        simpa only [map_add, map_mul, map_one, map_zero, hα] using congrArg σE hβroot
      have hfac : (σE β + β) * (σE β + β⁻¹) = 0 := by
        rw [show (σE β + β) * (σE β + β⁻¹)
            = (σE β) * (σE β) + (σE β) * (β + β⁻¹) + β * β⁻¹ from by ring,
          hβsum, mul_inv_cancel₀ hβne]
        rw [mul_comm (σE β) α]
        exact hσroot
      rcases mul_eq_zero.mp hfac with h | h
      · right
        rw [add_eq_zero_iff_eq_neg] at h
        rwa [CharTwo.neg_eq] at h
      · left
        rw [add_eq_zero_iff_eq_neg] at h
        rwa [CharTwo.neg_eq] at h
    exact ⟨β, hβne, hβsum, hσcond⟩

end Work.PSU3.StageB.Omega
