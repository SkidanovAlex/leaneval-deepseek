import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_le_pow
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_compl

namespace Commons.LinearAlgebra.Submodule

set_option linter.style.haveILetI false

open Module

/-- The total number of submodules of a finite vector space `M` over a finite field `K` is at
most `|K| ^ (r * (r + 1))` where `r = finrank K M`.

Proof: split the submodules according to their dimension.  For each `i ≤ r` the number of
`i`-dimensional submodules is at most `|K| ^ (i * (r - i) + i) ≤ |K| ^ (r * r)` by
`card_submodule_finrank_le_pow`, and summing over the `r + 1` possible dimensions and using
`r + 1 ≤ |K| ^ r` gives the claim. -/
theorem card_submodule_le_pow {K : Type*} [Field K] [Fintype K]
    {M : Type*} [AddCommGroup M] [Module K M] [Finite M] :
    Nat.card (Submodule K M) ≤ Nat.card K ^ (Module.finrank K M * (Module.finrank K M + 1)) := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  set r := Module.finrank K M with hr
  have hfin : ∀ S : Submodule K M, Module.finrank K S ≤ r := by
    intro S; rw [hr]; exact Submodule.finrank_le S
  let f : Submodule K M → Σ i : Fin (r+1), {S : Submodule K M // Module.finrank K S = i.val} :=
    fun S => ⟨⟨Module.finrank K S, by have := hfin S; omega⟩, ⟨S, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro S T h
    exact congrArg (fun x => x.2.1) h
  have hcard : Nat.card (Submodule K M) ≤
      Nat.card (Σ i : Fin (r+1), {S : Submodule K M // Module.finrank K S = i.val}) :=
    Nat.card_le_card_of_injective f hinj
  rw [Nat.card_sigma] at hcard
  set q := Nat.card K with hq
  have hq2 : 2 ≤ q := by
    have h := Fintype.one_lt_card (α := K)
    rw [← Nat.card_eq_fintype_card] at h
    omega
  have hqpos : 0 < q := by omega
  have hexp : ∀ i : Fin (r+1), i.val * (r - i.val) + i.val ≤ r * r := by
    intro i
    have hi : i.val ≤ r := by have := i.isLt; omega
    rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · rw [h0]; simp
    · have hri : r - i.val + 1 ≤ r := by omega
      calc i.val * (r - i.val) + i.val = i.val * (r - i.val + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
        _ ≤ r * r := Nat.mul_le_mul hi hri
  have hbound : (∑ i : Fin (r+1),
        Nat.card {S : Submodule K M // Module.finrank K S = i.val}) ≤ (r+1) * q ^ (r*r) := by
    calc (∑ i : Fin (r+1), Nat.card {S : Submodule K M // Module.finrank K S = i.val})
        ≤ ∑ _i : Fin (r+1), q ^ (r*r) := by
          apply Finset.sum_le_sum
          intro i _
          calc Nat.card {S : Submodule K M // Module.finrank K S = i.val}
              ≤ q ^ (i.val * (r - i.val) + i.val) :=
                card_submodule_finrank_le_pow (K := K) (V := M) i.val
            _ ≤ q ^ (r*r) := Nat.pow_le_pow_right hqpos (hexp i)
      _ = (r+1) * q ^ (r*r) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  have hr1 : r + 1 ≤ q ^ r := by
    have h1 : r + 1 ≤ 2 ^ r := by
      have := Nat.lt_pow_self (show 1 < 2 by norm_num) (n := r); omega
    have h2 : 2 ^ r ≤ q ^ r := Nat.pow_le_pow_left hq2 r
    omega
  calc Nat.card (Submodule K M) ≤ (r+1) * q ^ (r*r) := le_trans hcard hbound
    _ ≤ q ^ r * q ^ (r*r) := Nat.mul_le_mul_right _ hr1
    _ = q ^ (r + r*r) := by rw [pow_add]
    _ = q ^ (r * (r + 1)) := by
          congr 1
          rw [Nat.mul_add, Nat.mul_one]; ring

theorem card_submodule_pair_le_pow (n m d : ℕ) (X : Matrix (Fin n) (Fin m) (ZMod 2))
    (hX : X.rank ≤ d) :
    Nat.card {p : Submodule (ZMod 2) (Fin n → ZMod 2) × Submodule (ZMod 2) (Fin m → ZMod 2) //
      p.1 ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ p.2 ∧
      Module.finrank (ZMod 2) p.1 + (m - Module.finrank (ZMod 2) p.2) ≤ d}
      ≤ 2 ^ (10 * d ^ 2) := by
  classical
  set R : Submodule (ZMod 2) (Fin n → ZMod 2) := LinearMap.range X.mulVecLin with hR
  set K : Submodule (ZMod 2) (Fin m → ZMod 2) := LinearMap.ker X.mulVecLin with hK
  -- Step 1: an injection into the product of the two single-submodule counting sets.
  let f : {p : Submodule (ZMod 2) (Fin n → ZMod 2) × Submodule (ZMod 2) (Fin m → ZMod 2) //
        p.1 ≤ R ∧ K ≤ p.2 ∧
        Module.finrank (ZMod 2) p.1 + (m - Module.finrank (ZMod 2) p.2) ≤ d} →
      ({p : Submodule (ZMod 2) (Fin n → ZMod 2) // p ≤ R} ×
       {q : Submodule (ZMod 2) (Fin m → ZMod 2) // K ≤ q}) :=
    fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2.1⟩)
  have hinj : Function.Injective f := by
    rintro ⟨⟨a, b⟩, h⟩ ⟨⟨a', b'⟩, h'⟩ heq
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at heq
    exact Subtype.ext (Prod.ext heq.1 heq.2)
  have hstep1 : Nat.card {p : Submodule (ZMod 2) (Fin n → ZMod 2) ×
        Submodule (ZMod 2) (Fin m → ZMod 2) //
        p.1 ≤ R ∧ K ≤ p.2 ∧
        Module.finrank (ZMod 2) p.1 + (m - Module.finrank (ZMod 2) p.2) ≤ d} ≤
      Nat.card ({p : Submodule (ZMod 2) (Fin n → ZMod 2) // p ≤ R} ×
        {q : Submodule (ZMod 2) (Fin m → ZMod 2) // K ≤ q}) :=
    Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod] at hstep1
  -- Step 2: identify each factor with the submodules of `R`, resp. of `W ⧸ K`.
  have hA : Nat.card {p : Submodule (ZMod 2) (Fin n → ZMod 2) // p ≤ R} =
      Nat.card (Submodule (ZMod 2) R) :=
    (Nat.card_congr (Submodule.MapSubtype.orderIso R).toEquiv).symm
  have hB : Nat.card {q : Submodule (ZMod 2) (Fin m → ZMod 2) // K ≤ q} =
      Nat.card (Submodule (ZMod 2) ((Fin m → ZMod 2) ⧸ K)) :=
    (Nat.card_congr (Submodule.comapMkQRelIso K).toEquiv).symm
  -- Step 3: dimensions.
  have hXr : Module.finrank (ZMod 2) R ≤ d := by
    rw [hR]; simpa [Matrix.rank] using hX
  have hQfin : Module.finrank (ZMod 2) ((Fin m → ZMod 2) ⧸ K) ≤ d := by
    have heq : Module.finrank (ZMod 2) ((Fin m → ZMod 2) ⧸ K) = Module.finrank (ZMod 2) R := by
      rw [hK, hR]
      exact LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange X.mulVecLin)
    rw [heq]; exact hXr
  -- Step 4: bounds for each factor.
  have hAcard : Nat.card {p : Submodule (ZMod 2) (Fin n → ZMod 2) // p ≤ R} ≤
      2 ^ (d * (d + 1)) := by
    rw [hA]
    have h := card_submodule_le_pow (K := ZMod 2) (M := R)
    rw [show Nat.card (ZMod 2) = 2 from Nat.card_zmod 2] at h
    exact le_trans h (Nat.pow_le_pow_right (by norm_num)
      (by nlinarith [hXr, Nat.zero_le (Module.finrank (ZMod 2) R)]))
  have hBcard : Nat.card {q : Submodule (ZMod 2) (Fin m → ZMod 2) // K ≤ q} ≤
      2 ^ (d * (d + 1)) := by
    rw [hB]
    have h := card_submodule_le_pow (K := ZMod 2) (M := (Fin m → ZMod 2) ⧸ K)
    rw [show Nat.card (ZMod 2) = 2 from Nat.card_zmod 2] at h
    exact le_trans h (Nat.pow_le_pow_right (by norm_num)
      (by nlinarith [hQfin, Nat.zero_le (Module.finrank (ZMod 2) ((Fin m → ZMod 2) ⧸ K))]))
  -- Step 5: combine.
  have hexp : 2 * (d * (d + 1)) ≤ 10 * d ^ 2 := by
    rcases d with _ | k
    · simp
    · nlinarith
  calc Nat.card {p : Submodule (ZMod 2) (Fin n → ZMod 2) ×
          Submodule (ZMod 2) (Fin m → ZMod 2) //
          p.1 ≤ R ∧ K ≤ p.2 ∧
          Module.finrank (ZMod 2) p.1 + (m - Module.finrank (ZMod 2) p.2) ≤ d}
      ≤ Nat.card {p : Submodule (ZMod 2) (Fin n → ZMod 2) // p ≤ R} *
        Nat.card {q : Submodule (ZMod 2) (Fin m → ZMod 2) // K ≤ q} := hstep1
    _ ≤ 2 ^ (d * (d + 1)) * 2 ^ (d * (d + 1)) := Nat.mul_le_mul hAcard hBcard
    _ = 2 ^ (2 * (d * (d + 1))) := by rw [← pow_add]; congr 1; ring
    _ ≤ 2 ^ (10 * d ^ 2) := Nat.pow_le_pow_right (by norm_num) hexp

end Commons.LinearAlgebra.Submodule