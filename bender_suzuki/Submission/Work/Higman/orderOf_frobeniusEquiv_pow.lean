import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- The monoid homomorphism from the ring-automorphism group of `R` to the permutation group of
`R`, forgetting the ring structure.  It is injective, hence preserves `orderOf`. -/
def ringEquivToPerm (R : Type*) [Mul R] [Add R] : (R ≃+* R) →* Equiv.Perm R where
  toFun e := e.toEquiv
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

/-- The monoid homomorphism from the `K`-algebra-automorphism group of `R` to the permutation
group of `R`, forgetting the algebra structure.  It is injective, hence preserves `orderOf`. -/
def algEquivToPerm (K R : Type*) [CommSemiring K] [Semiring R] [Algebra K R] :
    (R ≃ₐ[K] R) →* Equiv.Perm R where
  toFun e := e.toEquiv
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

lemma ringEquivToPerm_injective (R : Type*) [Mul R] [Add R] :
    Function.Injective (ringEquivToPerm R) := by
  intro a b h
  have h2 : (a.toEquiv : R → R) = (b.toEquiv : R → R) :=
    congrArg (fun e : Equiv.Perm R => (e : R → R)) h
  exact RingEquiv.ext (fun x => congrFun h2 x)

lemma algEquivToPerm_injective (K R : Type*) [CommSemiring K] [Semiring R] [Algebra K R] :
    Function.Injective (algEquivToPerm K R) := by
  intro a b h
  have h2 : (a.toEquiv : R → R) = (b.toEquiv : R → R) :=
    congrArg (fun e : Equiv.Perm R => (e : R → R)) h
  exact AlgEquiv.ext (fun x => congrFun h2 x)

/-- The `r`-th power of the Frobenius automorphism `x ↦ x ^ 2` of `GF(2 ^ n)` (`n > 0`) has
order `n / gcd n r`.  (The order of `frobeniusEquiv (GaloisField 2 n) 2` is `n` because both it
and `FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) (GaloisField 2 n)` are the function
`x ↦ x ^ 2` and the latter has order `Module.finrank (ZMod 2) (GaloisField 2 n) = n`; then
`orderOf_pow`.) -/
theorem orderOf_frobeniusEquiv_pow (n r : ℕ) (hn : 0 < n) :
    orderOf ((frobeniusEquiv (GaloisField 2 n) 2) ^ r) = n / n.gcd r := by
  have hn' : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  -- The order of `frobeniusEquiv (GaloisField 2 n) 2` equals the order of the `ZMod 2`-algebra
  -- Frobenius `x ↦ x ^ 2`: both are the same permutation of `GaloisField 2 n`.
  have horder_eq : orderOf (frobeniusEquiv (GaloisField 2 n) 2) =
      orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) (GaloisField 2 n)) := by
    have hφ := orderOf_injective (ringEquivToPerm (GaloisField 2 n))
      (ringEquivToPerm_injective _) (frobeniusEquiv (GaloisField 2 n) 2)
    have hψ := orderOf_injective (algEquivToPerm (ZMod 2) (GaloisField 2 n))
      (algEquivToPerm_injective _ _)
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) (GaloisField 2 n))
    rw [← hφ, ← hψ]
    congr 1
  have hψn : orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) (GaloisField 2 n)) = n := by
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, GaloisField.finrank 2 hn']
  have horder : orderOf (frobeniusEquiv (GaloisField 2 n) 2) = n := horder_eq.trans hψn
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp only [pow_zero, orderOf_one, Nat.gcd_zero_right]
    exact (Nat.div_self hn).symm
  · rw [orderOf_pow' _ (Nat.pos_iff_ne_zero.mp hr), horder]

end Work.Higman
