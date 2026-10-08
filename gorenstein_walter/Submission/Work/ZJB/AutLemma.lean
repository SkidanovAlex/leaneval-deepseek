import Submission.Work.ZJB.Defs

/-!
# ZJB — Glauberman 1968, Lemma 5.3

The paper (p. 1120) proves, for `P ⊴ S` with `S` a finite `p`-group and `A = Aut(S)`:

> `C_A(P) ∩ C_A(S/P)` is a `p`-group,

by showing for `α` in that intersection and `n = |P|` that `α ^ n = 1`.  The sharp statement
`α ^ |P| = 1` is proved here; it needs no hypothesis on `S` (the `p`-group hypothesis in the
paper serves only to conclude that `|P|`, the exponent, is a power of `p`).

The proof is the paper's: for `y ∈ S` put `h := α y * y⁻¹ ∈ P` (triviality of `α` on `S/P`;
`P ⊴ S` is what makes this an element of `P` rather than of a coset).  Then `α y = h * y` and `α`
fixes every element of `P`, so `α^i y = h^i * y` by induction; `h ^ |P| = 1` by Lagrange in the
group `↥P`.  Hence `α ^ |P|` fixes every `y`, i.e. `α ^ |P| = 1` in `MulAut S`.
-/

namespace Work.ZJB

/-- **Glauberman 1968, Lemma 5.3** (sharp form).  If `P ⊴ S` is finite and `α ∈ Aut(S)` is
trivial on `P` and on `S/P`, then `α ^ |P| = 1`.  For `P` a `p`-group this exhibits
`C_A(P) ∩ C_A(S/P)` as a `p`-group. -/
theorem aut_pow_card_eq_one {S : Type*} [Group S] [Finite S] (P : Subgroup S) [P.Normal]
    (α : MulAut S) (hfix : ∀ x ∈ P, α x = x) (hquot : ∀ x : S, α x * x⁻¹ ∈ P) :
    α ^ Nat.card P = 1 := by
  refine MulEquiv.ext fun y => ?_
  set h : S := α y * y⁻¹ with hh
  have hhP : h ∈ P := hquot y
  have hfixh : α h = h := hfix h hhP
  have hαy : α y = h * y := by
    rw [hh]
    group
  have hfixpow : ∀ i : ℕ, α (h ^ i) = h ^ i := by
    intro i
    rw [map_pow, hfixh]
  have hkey : ∀ i : ℕ, (α ^ i) y = h ^ i * y := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc (α ^ (i + 1)) y = α ((α ^ i) y) := by rw [pow_succ', MulAut.mul_apply]
        _ = α (h ^ i * y) := by rw [ih]
        _ = α (h ^ i) * α y := by rw [map_mul]
        _ = h ^ i * (h * y) := by rw [hfixpow i, hαy]
        _ = h ^ (i + 1) * y := by rw [pow_add, pow_one, ← mul_assoc]
  have hcard : h ^ Nat.card P = 1 := by
    haveI : Fintype ↥P := Fintype.ofFinite ↥P
    have h1 : (⟨h, hhP⟩ : ↥P) ^ Fintype.card ↥P = 1 := pow_card_eq_one
    have h2 : h ^ Fintype.card ↥P = 1 := by
      have h3 : P.subtype ((⟨h, hhP⟩ : ↥P) ^ Fintype.card ↥P)
          = h ^ Fintype.card ↥P := by
        rw [map_pow]
        rfl
      rw [h1, map_one] at h3
      exact h3.symm
    rwa [Nat.card_eq_fintype_card]
  simp only [MulAut.one_apply]
  rw [hkey (Nat.card P), hcard, one_mul]

end Work.ZJB
