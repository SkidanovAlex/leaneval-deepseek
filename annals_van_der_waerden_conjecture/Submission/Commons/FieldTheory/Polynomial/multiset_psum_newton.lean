import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

open MvPolynomial

namespace Commons.FieldTheory.Polynomial

/-- Every multiset `s` of cardinality `n` admits an enumeration `f : Fin n → α` such that
`(Finset.univ : Finset (Fin n)).val.map f = s`. -/
lemma multiset_exists_enum {α : Type*} (s : Multiset α) :
    ∃ f : Fin s.card → α, (Finset.univ : Finset (Fin s.card)).val.map f = s := by
  refine ⟨fun i => s.toList.get (Fin.cast (Multiset.length_toList s).symm i), ?_⟩
  have hcongr : (List.ofFn (List.get s.toList)) =
      (List.ofFn fun i : Fin s.card =>
        s.toList.get (Fin.cast (Multiset.length_toList s).symm i)) :=
    List.ofFn_congr (Multiset.length_toList s) (List.get s.toList)
  have h2 : (List.ofFn fun i : Fin s.card =>
      s.toList.get (Fin.cast (Multiset.length_toList s).symm i)) = s.toList := by
    rw [← hcongr, List.ofFn_get]
  rw [show (Finset.univ : Finset (Fin s.card)).val =
        (↑(List.finRange s.card) : Multiset (Fin s.card)) from rfl,
    Multiset.map_coe, ← List.ofFn_eq_map, h2, Multiset.coe_toList]

/-- Specialization of the power sum `MvPolynomial.psum` under `aeval`: evaluating
`psum α F m` at a tuple `f` gives the sum of the `m`-th powers of the entries of `f`. -/
lemma aeval_psum_eq {F : Type*} [Field F] {α : Type*} [Fintype α] (f : α → F) (m : ℕ) :
    MvPolynomial.aeval f (MvPolynomial.psum α F m) = ∑ i, f i ^ m := by
  simp only [MvPolynomial.psum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_pow, MvPolynomial.aeval_X]

/-- **Newton's identities** for a multiset of field elements: for `1 ≤ j ≤ s.card`,
the power sum `p_j = ∑ x ∈ s, x ^ j` is determined by the elementary symmetric
functions `e_i = s.esymm i` via
`p_j = (-1) ^ (j + 1) * j * e_j - ∑ i ∈ Icc 1 (j - 1), (-1) ^ i * e_i * p_{j - i}`. -/
theorem multiset_psum_newton {F : Type*} [Field F] (s : Multiset F) (j : ℕ)
    (h1 : 1 ≤ j) (h2 : j ≤ s.card) :
    (s.map (· ^ j)).sum =
      (-1) ^ (j + 1) * (j : F) * s.esymm j
        - ∑ i ∈ Finset.Icc 1 (j - 1), (-1) ^ i * s.esymm i * (s.map (· ^ (j - i))).sum := by
  have _ : j ≤ s.card := h2
  obtain ⟨f, hf⟩ := multiset_exists_enum s
  rw [← hf]
  have hj : 0 < j := by omega
  have hkey := MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin s.card) F j hj
  have hkey2 := congrArg (MvPolynomial.aeval f) hkey
  have hpsum : ∀ m, MvPolynomial.aeval f (MvPolynomial.psum (Fin s.card) F m)
      = ((Finset.univ.val.map f).map (· ^ m)).sum := by
    intro m
    rw [aeval_psum_eq, Multiset.map_map]
    rfl
  have hesymm : ∀ m, MvPolynomial.aeval f (MvPolynomial.esymm (Fin s.card) F m)
      = (Finset.univ.val.map f).esymm m := by
    intro m
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
  simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, map_sum,
    hpsum, hesymm] at hkey2
  have hT : (Finset.HasAntidiagonal.antidiagonal j).filter (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 j)
      = (Finset.Icc 1 (j - 1)).image (fun i => (i, j - i)) := by
    ext a
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Set.mem_Ioo,
      Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨hsum, h0, hlt⟩
      exact ⟨a.1, ⟨by omega, by omega⟩, Prod.ext rfl (by omega)⟩
    · rintro ⟨i, ⟨hi1, hile⟩, hp⟩
      have hp1 : i = a.1 := congrArg Prod.fst hp
      have hp2 : j - i = a.2 := congrArg Prod.snd hp
      exact ⟨by omega, by omega, by omega⟩
  rw [hT, Finset.sum_image] at hkey2
  · exact hkey2
  · intro i _ k _ h
    simpa using congrArg Prod.fst h

end Commons.FieldTheory.Polynomial