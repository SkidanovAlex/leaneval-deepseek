import Mathlib
import Submission.Commons.NumberTheory.ZMod.card_int_abs_le_dvd_sq_add_pow4
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_Ad_eq_sum_c

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

theorem X2Y4_Ad_sub_Md_eq_fract (x d : ℕ) (hd : 1 ≤ d) (hx : 1 ≤ x) :
    (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
      - (∑ c ∈ Finset.Icc (-((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)))
            ((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)),
          ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
            2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))
      = - ∑ c ∈ Finset.Icc (-((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)))
            ((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)),
          ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
            (Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) - (β : ℝ)) / (d : ℝ)) - 1 / 2
              + (Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) + (β : ℝ)) / (d : ℝ)) - 1 / 2)) := by
  classical
  let N : ℕ := ⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊
  let J : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let L : ℤ → ℝ := fun c => Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)
  let F : ℤ → Finset ℕ :=
    fun c => (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4))
  let X : ℤ → ℕ → ℝ := fun c _ => 2 * L c / (d : ℝ)
  let Y : ℤ → ℕ → ℝ := fun c β =>
    Int.fract ((L c - (β : ℝ)) / (d : ℝ)) - 1 / 2
      + (Int.fract ((L c + (β : ℝ)) / (d : ℝ)) - 1 / 2)
  let inner : ℤ → ℕ := fun c =>
    (Finset.filter (fun a : ℤ => |(a : ℝ)| ≤ L c ∧ ((d : ℤ) ∣ a ^ 2 + (c : ℤ) ^ 4))
      (Finset.Icc (-(⌊L c⌋₊ + 1 : ℤ)) (⌊L c⌋₊ + 1 : ℤ))).card
  let A : ℕ := ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard
  show (A : ℝ) - (∑ c ∈ J, ∑ β ∈ F c, X c β) = - (∑ c ∈ J, ∑ β ∈ F c, Y c β)
  have hper : ∀ (c : ℤ) (β : ℕ),
      ((⌊(L c - (β : ℝ)) / (d : ℝ)⌋ : ℝ) + (⌊(L c + (β : ℝ)) / (d : ℝ)⌋ : ℝ) + 1)
        = X c β - Y c β := by
    intro c β
    have h1 : ((⌊(L c - (β : ℝ)) / (d : ℝ)⌋ : ℤ) : ℝ)
        + Int.fract ((L c - (β : ℝ)) / (d : ℝ)) = (L c - (β : ℝ)) / (d : ℝ) :=
      Int.floor_add_fract _
    have h2 : ((⌊(L c + (β : ℝ)) / (d : ℝ)⌋ : ℤ) : ℝ)
        + Int.fract ((L c + (β : ℝ)) / (d : ℝ)) = (L c + (β : ℝ)) / (d : ℝ) :=
      Int.floor_add_fract _
    have h12 : (L c - (β : ℝ)) / (d : ℝ) + (L c + (β : ℝ)) / (d : ℝ) = 2 * L c / (d : ℝ) := by
      ring
    simp only [X, Y]
    linarith
  have hA : (A : ℤ) = ∑ c ∈ J, (inner c : ℤ) := X2Y4_Ad_eq_sum_c x d hd hx
  have hAr : (A : ℝ) = ∑ c ∈ J, (inner c : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hA
    push_cast at h
    simpa using h
  have hc4 : ∀ c : ℤ, ((c.natAbs : ℤ)) ^ 4 = c ^ 4 := by
    intro c
    have h1 : ((c.natAbs : ℤ)) = |c| := (Int.abs_eq_natAbs c).symm
    rw [h1, ← abs_pow, abs_of_nonneg (by positivity : (0 : ℤ) ≤ c ^ 4)]
  have hterm : ∀ c ∈ J, (inner c : ℝ) = ∑ β ∈ F c, (X c β - Y c β) := by
    intro c _
    have hc1 := Commons.NumberTheory.ZMod.card_int_abs_le_dvd_sq_add_pow4 d c.natAbs hd (L c) (Real.sqrt_nonneg _)
    rw [hc4 c] at hc1
    have hcR : (inner c : ℝ)
        = ∑ β ∈ F c, (((⌊(L c - (β : ℝ)) / (d : ℝ)⌋ : ℤ) : ℝ)
            + ((⌊(L c + (β : ℝ)) / (d : ℝ)⌋ : ℤ) : ℝ) + 1) := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) hc1
      push_cast at h
      simpa [inner, F, L] using h
    rw [hcR]
    exact Finset.sum_congr rfl (fun β _ => hper c β)
  have hbridge : (A : ℝ) = (∑ c ∈ J, ∑ β ∈ F c, X c β) - (∑ c ∈ J, ∑ β ∈ F c, Y c β) := by
    calc (A : ℝ) = ∑ c ∈ J, (inner c : ℝ) := hAr
      _ = ∑ c ∈ J, ∑ β ∈ F c, (X c β - Y c β) := Finset.sum_congr rfl hterm
      _ = ∑ c ∈ J, (∑ β ∈ F c, X c β - ∑ β ∈ F c, Y c β) := by
            refine Finset.sum_congr rfl (fun c _ => ?_)
            rw [Finset.sum_sub_distrib]
      _ = (∑ c ∈ J, ∑ β ∈ F c, X c β) - (∑ c ∈ J, ∑ β ∈ F c, Y c β) :=
            Finset.sum_sub_distrib _ _
  linarith

end Commons.NumberTheory.FriedlanderIwaniec
