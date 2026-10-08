import Mathlib

namespace Work.BSW.Cases.Order

/-- In a finite group with at least one involution, the number of involutions is odd.

The key input is Mathlib's `Equiv.Perm.card_fixedPoints_modEq`, which says that the number
of fixed points of an involution on a finite set has the same parity as the cardinality of
the set.  Applied to the inversion map `x ↦ x⁻¹` it shows that
`{x | x⁻¹ = x} = {1} ∪ {x | orderOf x = 2}` has the same parity as `|G|`, which is even
because `orderOf u = 2` divides `|G|`.  Hence the set of involutions, obtained from the
above set by removing the identity, has odd cardinality. -/
theorem invOdd {G : Type} [Group G] [Finite G] (hex : ∃ u : G, orderOf u = 2) :
    Odd {x : G | orderOf x = 2}.ncard := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  set T : Set G := {x : G | orderOf x = 2} with hTdef
  set S : Set G := {x : G | x⁻¹ = x} with hSdef
  change Odd T.ncard
  -- `|G|` is even, since `orderOf u = 2` divides it.
  have hGeven : Even (Nat.card G) := by
    obtain ⟨u, hu⟩ := hex
    exact even_iff_two_dvd.mpr (hu ▸ orderOf_dvd_natCard u)
  -- The inversion map is an involution of `G`; its fixed points have the same parity as `|G|`.
  set f : Function.End G := fun x => x⁻¹ with hf_def
  have hf : f ^ 2 ^ 1 = 1 := by
    have h2 : (2 : ℕ) ^ 1 = 2 := by norm_num
    rw [h2, pow_two, Function.End.mul_def, Function.End.one_def]
    funext x
    simp [hf_def]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1)
    (hp := ⟨Nat.prime_two⟩) hf
  have hSfp : Function.fixedPoints f = S := by
    rw [hSdef]
    ext x
    rw [Function.mem_fixedPoints]
    simp [Function.IsFixedPt]
  have key : Fintype.card ↑(Function.fixedPoints f) = S.ncard := by
    rw [← Nat.card_eq_fintype_card]
    rw [Nat.card_coe_set_eq]
    rw [hSfp]
  have key2 : Fintype.card G = Nat.card G := (Nat.card_eq_fintype_card).symm
  have hmodS : Nat.card G ≡ S.ncard [MOD 2] := by
    rw [key2, key] at hmod
    exact hmod
  -- `S` consists of the identity together with the elements of order two.
  have hST : S = insert 1 T := by
    rw [hSdef, hTdef]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_ofPred_eq]
    constructor
    · intro hx
      have hx2 : x ^ 2 = 1 := (pow_two x).trans ((inv_eq_iff_mul_eq_one (a := x) (b := x)).mp hx)
      have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact Or.inl (orderOf_eq_one_iff.mp h)
      · exact Or.inr h
    · rintro (hx | hx)
      · simp [hx]
      · have hp2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
        exact (inv_eq_iff_mul_eq_one (a := x) (b := x)).mpr ((pow_two x).symm.trans hp2)
  have h1notin : (1 : G) ∉ T := by
    rw [hTdef]
    simp [Set.mem_ofPred_eq, orderOf_one]
  have hEvenS : Even S.ncard := by
    rw [Nat.even_iff]
    have hmod'' : Nat.card G % 2 = S.ncard % 2 := hmodS
    rw [← hmod'']
    exact Nat.even_iff.mp hGeven
  have hS_card : S.ncard = T.ncard + 1 := by
    rw [hST, Set.ncard_insert_of_notMem h1notin]
  have hEvenT : Even (T.ncard + 1) := by rw [← hS_card]; exact hEvenS
  exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hEvenT)

end Work.BSW.Cases.Order
