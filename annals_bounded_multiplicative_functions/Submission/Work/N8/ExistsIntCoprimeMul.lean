import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- If `A` and `B` are coprime natural numbers and `X` is a real number such that
both `A * X` and `B * X` are integers, then `X` itself is an integer.
This is Bézout's identity: writing `1 = u * A + v * B` with `u, v ∈ ℤ`, one gets
`X = 1 * X = u * (A * X) + v * (B * X)`, an integer combination of `p` and `q`. -/
theorem ExistsIntCoprimeMul {A B : ℕ} (hcop : Nat.Coprime A B) {X : ℝ}
    (hA : ∃ p : ℤ, (A : ℝ) * X = (p : ℝ)) (hB : ∃ q : ℤ, (B : ℝ) * X = (q : ℝ)) :
    ∃ m : ℤ, X = (m : ℝ) := by
  obtain ⟨p, hp⟩ := hA
  obtain ⟨q, hq⟩ := hB
  have hgcd : ((Nat.gcd A B : ℕ) : ℤ) = 1 := by exact_mod_cast hcop
  have hbez : (Nat.gcdA A B) * (A:ℤ) + (Nat.gcdB A B) * (B:ℤ) = 1 := by
    have h := Nat.gcd_eq_gcd_ab A B
    rw [hgcd] at h
    linarith
  refine ⟨(Nat.gcdA A B) * p + (Nat.gcdB A B) * q, ?_⟩
  have h1 : ((Nat.gcdA A B : ℝ) * (A:ℝ) + (Nat.gcdB A B : ℝ) * (B:ℝ)) = 1 := by
    exact_mod_cast hbez
  have h2 : ((Nat.gcdA A B : ℝ) * (p:ℝ) + (Nat.gcdB A B : ℝ) * (q:ℝ))
      = (((Nat.gcdA A B) * p + (Nat.gcdB A B) * q : ℤ) : ℝ) := by
    push_cast; ring
  calc X = ((Nat.gcdA A B : ℝ) * (A:ℝ) + (Nat.gcdB A B : ℝ) * (B:ℝ)) * X := by
        rw [h1, one_mul]
    _ = (Nat.gcdA A B : ℝ) * ((A:ℝ) * X) + (Nat.gcdB A B : ℝ) * ((B:ℝ) * X) := by ring
    _ = (Nat.gcdA A B : ℝ) * (p:ℝ) + (Nat.gcdB A B : ℝ) * (q:ℝ) := by rw [hp, hq]
    _ = (((Nat.gcdA A B) * p + (Nat.gcdB A B) * q : ℤ) : ℝ) := h2

end Work.N8
