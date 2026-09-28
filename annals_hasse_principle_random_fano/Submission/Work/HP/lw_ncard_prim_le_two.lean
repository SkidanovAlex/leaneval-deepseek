import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.Lat.prim_bezout

/-!
# At most two primitive vectors below the second successive minimum

For an integral lattice `L ⊆ ℤ^ι` and a radius `r < lam L 2`, the set

`{a ∈ L : a primitive, 0 < ‖a‖ ≤ r}`

has at most two elements.  Indeed, if `a` and `b` are two such vectors with `b ≠ ±a`, then
(by primitivity, via Bézout) `a` and `b` are `ℤ`-linearly independent, so the successive-minimum
bound `lam L 2 ≤ max ‖a‖ ‖b‖ ≤ r` contradicts `r < lam L 2`.  Hence all elements of the set are
`±a` for any one of them.

The auxiliary facts are `IsPrim.ne_zero` (a primitive vector is nonzero) and
`prim_pair_linIndep` (two primitive vectors not equal up to sign are `ℤ`-linearly independent).
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP

/-- A primitive integer vector is nonzero: the gcd of the all-zero vector is `0 ≠ 1`. -/
lemma IsPrim.ne_zero {ι : Type*} [Fintype ι] {a : ι → ℤ} (ha : IsPrim a) : a ≠ 0 := by
  intro hzero
  have h1 := ha
  rw [hzero] at h1
  simp only [IsPrim] at h1
  have hz : Finset.univ.gcd (0 : ι → ℤ) = 0 := Finset.gcd_eq_zero_iff.mpr (by simp)
  rw [hz] at h1
  exact zero_ne_one h1

/-- Two primitive integer vectors that are not equal up to sign are `ℤ`-linearly independent.

This is the arithmetic heart of the counting lemma: if `c • a = b` for some `c : ℤ`, then Bézout
for `b` gives `1 = ∑ᵢ vᵢ bᵢ = c · ∑ᵢ vᵢ aᵢ`, so `c = ±1` and `b = ±a`. -/
theorem prim_pair_linIndep {ι : Type*} [Fintype ι] {a b : ι → ℤ}
    (ha : IsPrim a) (hb : IsPrim b) (hab : b ≠ a) (hba : b ≠ -a) :
    LinearIndependent ℤ ![a, b] := by
  have hb0 : b ≠ 0 := hb.ne_zero
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hcoord : ∀ i, s * a i + t * b i = 0 := fun i => by
    have h := congr_fun hst i
    simpa using h
  by_cases hs : s = 0
  · subst hs
    refine ⟨rfl, ?_⟩
    have htb : t • b = 0 := by
      have h := hst
      rw [zero_smul, zero_add] at h
      exact h
    rcases smul_eq_zero.mp htb with h | h
    · exact h
    · exact absurd h hb0
  · exfalso
    obtain ⟨u, hu⟩ := Lat.prim_bezout a ha
    obtain ⟨v, hv⟩ := Lat.prim_bezout b hb
    have hsumid : ∀ (w : ι → ℤ) (c d : ℤ),
        ∑ i, w i * (c * a i + d * b i)
          = c * (∑ i, w i * a i) + d * (∑ i, w i * b i) := by
      intro w c d
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h2 : t = -s * (∑ i, v i * a i) := by
      have hz : ∑ i, v i * (s * a i + t * b i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [hcoord i, mul_zero]
      rw [hsumid v s t, hv, mul_one] at hz
      linarith
    have h1 : s = -t * (∑ i, u i * b i) := by
      have hz : ∑ i, u i * (s * a i + t * b i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [hcoord i, mul_zero]
      rw [hsumid u s t, hu, mul_one] at hz
      linarith
    have hs_eq : s = s * ((∑ i, v i * a i) * (∑ i, u i * b i)) := by
      calc s = -t * (∑ i, u i * b i) := h1
        _ = -(-s * (∑ i, v i * a i)) * (∑ i, u i * b i) := by rw [h2]
        _ = s * ((∑ i, v i * a i) * (∑ i, u i * b i)) := by ring
    have hs_eq2 : s * ((∑ i, v i * a i) * (∑ i, u i * b i)) = s * 1 := by
      rw [mul_one]; exact hs_eq.symm
    have hAB : (∑ i, v i * a i) * (∑ i, u i * b i) = 1 :=
      mul_left_cancel₀ hs hs_eq2
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hAB with hA | hA
    · have ht : t = -s := by rw [hA] at h2; ring_nf at h2; exact h2
      have hab_eq : a = b := by
        funext i
        have h := hcoord i
        rw [ht] at h
        have h1' : s * (a i - b i) = 0 := by linear_combination h
        rcases mul_eq_zero.mp h1' with h' | h'
        · exact absurd h' hs
        · exact sub_eq_zero.mp h'
      exact hab hab_eq.symm
    · have ht : t = s := by rw [hA] at h2; ring_nf at h2; exact h2
      have hab_eq : a = -b := by
        funext i
        have h := hcoord i
        rw [ht] at h
        have h1' : s * (a i + b i) = 0 := by linear_combination h
        rcases mul_eq_zero.mp h1' with h' | h'
        · exact absurd h' hs
        · exact eq_neg_of_add_eq_zero_left h'
      have hb_eq : b = -a := by rw [hab_eq]; simp
      exact hba hb_eq

theorem lw_ncard_prim_le_two {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) {r : ℝ} (h : r < lam L 2) :
    (({a : ι → ℤ | a ∈ L ∧ IsPrim a ∧ 0 < eNorm a ∧ eNorm a ≤ r} : Set (ι → ℤ)).ncard : ℝ) ≤ 2 := by
  classical
  set S : Set (ι → ℤ) := {a | a ∈ L ∧ IsPrim a ∧ 0 < eNorm a ∧ eNorm a ≤ r} with hSdef
  have key : ∀ a ∈ S, ∀ b ∈ S, b = a ∨ b = -a := by
    intro a ha b hb
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hb1, hb2⟩ := hcon
    have hLI : LinearIndependent ℤ ![a, b] := prim_pair_linIndep ha.2.1 hb.2.1 hb1 hb2
    have hlam : lam L 2 ≤ max (eNorm a) (eNorm b) := lam_two_le_max L ha.1 hb.1 hLI
    have har : eNorm a ≤ r := ha.2.2.2
    have hbr : eNorm b ≤ r := hb.2.2.2
    have hmax : max (eNorm a) (eNorm b) ≤ r := max_le har hbr
    linarith
  by_cases hne : S.Nonempty
  · obtain ⟨a, ha⟩ := hne
    have hsub : S ⊆ {a, -a} := by
      intro b hb
      rcases key a ha b hb with hh | hh
      · simp [hh]
      · simp [hh]
    have h2 : S.ncard ≤ ({a, -a} : Set (ι → ℤ)).ncard := Set.ncard_le_ncard hsub
    have h3 : ({a, -a} : Set (ι → ℤ)).ncard ≤ 2 := by
      rcases eq_or_ne a (-a) with hh | hh
      · have hset : ({a, -a} : Set (ι → ℤ)) = {a} := by rw [← hh]; simp
        rw [hset, Set.ncard_singleton]; norm_num
      · rw [Set.ncard_pair hh]
    have h4 : S.ncard ≤ 2 := le_trans h2 h3
    exact_mod_cast h4
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne]

end Work.HP
