/-
L3 (part 1): the "crack detour" lemma.  Through a tangent pair of an orbit
quadruple, the crack family contains an orbit quadruple in which the pair is
joined by a circle whose curvature is coprime to the product of the pair —
the key ingredient for refining a tangency edge into a coprime path
(`tangent_copath`).

Canonical form: the pair sits at indices 0 and 1 (always odd in the orbit).
-/
import Submission.Apollo.OrbitFacts
import Submission.Apollo.MakeCoprime
import Submission.Apollo.Relabel
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open scoped Pointwise
open LocalGlobalApollonianCirclePackings

namespace Apollo

/-- the complement of the pair (0,1) contains an odd coordinate whenever the
product of the pair is even (true because the orbit has exactly two odd
coordinates). -/
lemma hpar_orbit {w : Fin 4 → ℤ} (hw : w ∈ apOrbit) :
    2 ∣ w 0 * w 1 → ¬ 2 ∣ w 2 ∨ ¬ 2 ∣ w 3 := by
  intro h2
  -- indices 0 and 1 are odd in the orbit, so the hypothesis is impossible:
  have ho0 : ¬ 2 ∣ w 0 := orbit_odd_zero w hw
  have ho1 : ¬ 2 ∣ w 1 := orbit_odd_one w hw
  rcases h2 with ⟨t, ht⟩
  -- w0*w1 = 2t: w0*w1 is even, contradicting both factors odd
  have h01 : (2 : ℤ) ∣ w 0 * w 1 := ⟨t, ht⟩
  -- if a product is even then one factor is even
  have : 2 ∣ w 0 ∨ 2 ∣ w 1 := by
    -- elementary: use Int.Prime.dvd_mul
    exact (Int.prime_two.dvd_mul).1 h01
  rcases this with h | h
  · exact False.elim (ho0 h)
  · exact False.elim (ho1 h)

/-- an even natural x is of the form 2n; an odd one of the form 2n+1. -/
lemma two_mul_or_two_mul_add_one (x : ℕ) :
    (∃ n : ℕ, x = 2 * n) ∨ ∃ n : ℕ, x = 2 * n + 1 := by
  by_cases hx : x % 2 = 0
  · left
    refine ⟨x / 2, ?_⟩
    omega
  · right
    refine ⟨x / 2, ?_⟩
    have hx1 : x % 2 = 1 := by omega
    omega

/-- Canonical crack detour through the pair at indices 0,1 of an orbit
quadruple: some crack member keeps the pair and adds a circle coprime to the
product of the pair. -/
theorem crack_pair_coprime_exists (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) :
    ∃ u : Fin 4 → ℤ, u ∈ apOrbit ∧ u 0 = w 0 ∧ u 1 = w 1 ∧
      ∃ z : ℤ, z.gcd (w 0 * w 1) = 1 ∧ ∃ k : Fin 4, (k = 2 ∨ k = 3) ∧ u k = z := by
  -- make_coprime on the canonical pair:
  have hD := apOrbit_descarates w hw
  have hg := apOrbit_gcd_one w hw
  have hz : w 0 * w 1 ≠ 0 :=
    mul_ne_zero (orbit_value_ne_zero w hw 0) (orbit_value_ne_zero w hw 1)
  rcases make_coprime w hD hg hz (hpar_orbit hw) with ⟨x, hx⟩
  -- place x on an even or odd crack value:
  rcases two_mul_or_two_mul_add_one x with ⟨n, hx2⟩ | ⟨n, hx2⟩
  · refine ⟨crackSeq w n, ?_, crackSeq_fix0 w n, crackSeq_fix1 w n, ?_⟩
    · exact crackSeq_mem_apOrbit w hw n
    · refine ⟨crackSeq w n 2, ?_, 2, Or.inl rfl, ?_⟩
      · -- gcd (crackPoly w (2n)) (w0*w1) = 1: crackSeq23: crackSeq w n 2 = crackPoly w (2n)
        have h23 := (crackSeq23 w n).1
        -- hx : gcd (crackPoly w x) (w0·w1) = 1 ; x = 2n:
        simpa [h23, hx2] using hx
      · rfl
  · refine ⟨crackSeq w n, ?_, crackSeq_fix0 w n, crackSeq_fix1 w n, ?_⟩
    · exact crackSeq_mem_apOrbit w hw n
    · refine ⟨crackSeq w n 3, ?_, 3, Or.inr rfl, ?_⟩
      · have h23 := (crackSeq23 w n).2
        simpa [h23, hx2] using hx
      · rfl


/-- a Fin 4 index not equal to 0 or 1 is 2 or 3. -/
lemma fin_not01 {k : Fin 4} (h : ¬ (k = 0 ∨ k = 1)) : k = 2 ∨ k = 3 := by
  fin_cases k
  · exfalso; exact h (Or.inl rfl)
  · exfalso; exact h (Or.inr rfl)
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- a Fin 4 index not equal to 2 or 3 is 0 or 1. -/
lemma fin_not23 {k : Fin 4} (h : ¬ (k = 2 ∨ k = 3)) : k = 0 ∨ k = 1 := by
  fin_cases k
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exfalso; exact h (Or.inl rfl)
  · exfalso; exact h (Or.inr rfl)

/-- if neither σ 2 nor σ 3 lands in {0,1}, then σ0 and σ1 both land in {0,1}. -/
lemma images01 {σ : Equiv.Perm (Fin 4)}
    (hs2 : ¬ (σ 2 = 0 ∨ σ 2 = 1)) (hs3 : ¬ (σ 3 = 0 ∨ σ 3 = 1)) :
    (σ 0 = 0 ∨ σ 0 = 1) ∧ (σ 1 = 0 ∨ σ 1 = 1) := by
  rcases (σ.surjective (0 : Fin 4)) with ⟨k0, hk0⟩
  rcases (σ.surjective (1 : Fin 4)) with ⟨k1, hk1⟩
  have k0ne23 : ¬ (k0 = 2 ∨ k0 = 3) := by
    intro h
    rcases h with h | h
    · subst k0; exact hs2 (Or.inl hk0)
    · subst k0; exact hs3 (Or.inl hk0)
  have k1ne23 : ¬ (k1 = 2 ∨ k1 = 3) := by
    intro h
    rcases h with h | h
    · subst k1; exact hs2 (Or.inr hk1)
    · subst k1; exact hs3 (Or.inr hk1)
  have k0in : k0 = 0 ∨ k0 = 1 := fin_not23 k0ne23
  have k1in : k1 = 0 ∨ k1 = 1 := fin_not23 k1ne23
  have k0ne1 : k0 ≠ k1 := by
    intro h
    subst k1
    have : (0 : Fin 4) = 1 := hk0.symm.trans hk1
    norm_num at this
  constructor
  · rcases k0in with k00 | k01
    · subst k0
      exact Or.inl hk0
    · subst k0
      have k10 : k1 = 0 := by
        rcases k1in with h | h
        · exact h
        · exfalso; exact k0ne1 h.symm
      subst k1
      exact Or.inr hk1
  · rcases k1in with k10 | k11
    · subst k1
      have k01 : k0 = 1 := by
        rcases k0in with h0 | h1
        · exfalso; exact k0ne1 h0
        · exact h1
      subst k0
      exact Or.inl hk0
    · subst k1
      exact Or.inr hk1

/-- the product of two odd integers is odd. -/
lemma odd_mul_int {a b : ℤ} (ha : ¬ 2 ∣ a) (hb : ¬ 2 ∣ b) : ¬ 2 ∣ a * b := by
  intro h
  rcases (Int.prime_two.dvd_mul.mp h) with h | h
  · exact ha h
  · exact hb h

/-- the parity hypothesis of make_coprime for a relabelled orbit quadruple. -/
lemma hpar_perm (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) (σ : Equiv.Perm (Fin 4)) :
    2 ∣ (w ∘ σ) 0 * (w ∘ σ) 1 → ¬ 2 ∣ (w ∘ σ) 2 ∨ ¬ 2 ∣ (w ∘ σ) 3 := by
  intro h2
  by_contra hne
  push_neg at hne
  have hv2 : 2 ∣ w (σ 2) := by simpa using hne.1
  have hv3 : 2 ∣ w (σ 3) := by simpa using hne.2
  have hs2 : ¬ (σ 2 = 0 ∨ σ 2 = 1) := by
    intro h
    have ho : ¬ 2 ∣ w (σ 2) := (coord_odd_iff w hw (σ 2)).2 h
    exact ho hv2
  have hs3 : ¬ (σ 3 = 0 ∨ σ 3 = 1) := by
    intro h
    have ho : ¬ 2 ∣ w (σ 3) := (coord_odd_iff w hw (σ 3)).2 h
    exact ho hv3
  rcases (images01 (σ := σ) hs2 hs3) with ⟨s0, s1⟩
  have hv0 : ¬ 2 ∣ w (σ 0) := by
    rcases s0 with h | h
    · simpa [h] using orbit_odd_zero w hw
    · simpa [h] using orbit_odd_one w hw
  have hv1 : ¬ 2 ∣ w (σ 1) := by
    rcases s1 with h | h
    · simpa [h] using orbit_odd_zero w hw
    · simpa [h] using orbit_odd_one w hw
  exact (odd_mul_int hv0 hv1) h2



/-- crack detour through any tangent pair (σ 0, σ 1) of an orbit quadruple:
some crack member keeps the pair and adds a circle coprime to the product. -/
theorem crack_pair_coprime_exists_at (w : Fin 4 → ℤ) (hw : w ∈ apOrbit)
    (σ : Equiv.Perm (Fin 4)) :
    ∃ u : Fin 4 → ℤ, u ∈ apOrbit ∧ (∃ n : ℕ, u = relabelCrack σ w n) ∧
      u (σ 0) = w (σ 0) ∧ u (σ 1) = w (σ 1) ∧
      ∃ z : ℤ, z.gcd (w (σ 0) * w (σ 1)) = 1 ∧ ∃ k : Fin 4, (k = σ 2 ∨ k = σ 3) ∧ u k = z := by
  let v : Fin 4 → ℤ := w ∘ σ
  have hDv : (∑ j : Fin 4, v j) ^ 2 = 2 * ∑ j : Fin 4, (v j) ^ 2 := by
    dsimp [v]
    exact descartes_perm w (apOrbit_descarates w hw) σ
  have hgv : Finset.univ.gcd v = 1 := by
    dsimp [v]
    change Finset.univ.gcd (fun j : Fin 4 => w (σ j)) = 1
    rw [gcd_perm w σ]
    exact apOrbit_gcd_one w hw
  have hzv : v 0 * v 1 ≠ 0 := by
    dsimp [v]
    exact mul_ne_zero (orbit_value_ne_zero w hw (σ 0)) (orbit_value_ne_zero w hw (σ 1))
  rcases make_coprime v hDv hgv hzv (hpar_perm w hw σ) with ⟨x, hx⟩
  rcases two_mul_or_two_mul_add_one x with ⟨n, hx2⟩ | ⟨n, hx2⟩
  · refine ⟨relabelCrack σ w n, ?_, ⟨n, rfl⟩, relabelCrack_fix0 σ w n,
      relabelCrack_fix1 σ w n, ?_⟩
    · exact relabelCrack_mem_apOrbit σ w hw n
    · refine ⟨relabelCrack σ w n (σ 2), ?_, σ 2, Or.inl rfl, ?_⟩
      · have hm := (relabelCrack_moved σ w n).1
        have hx' : (crackPoly v x).gcd (v 0 * v 1) = 1 := hx
        simpa [v, hm, hx2, mul_comm] using hx'
      · rfl
  · refine ⟨relabelCrack σ w n, ?_, ⟨n, rfl⟩, relabelCrack_fix0 σ w n,
      relabelCrack_fix1 σ w n, ?_⟩
    · exact relabelCrack_mem_apOrbit σ w hw n
    · refine ⟨relabelCrack σ w n (σ 3), ?_, σ 3, Or.inr rfl, ?_⟩
      · have hm := (relabelCrack_moved σ w n).2
        have hx' : (crackPoly v x).gcd (v 0 * v 1) = 1 := hx
        simpa [v, hm, hx2, mul_comm] using hx'
      · rfl

end Apollo
