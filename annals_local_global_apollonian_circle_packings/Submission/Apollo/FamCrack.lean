/-
The crack detour for the family orbit: through any tangent pair of an orbit
quadruple of famQuad t, the crack family contains an orbit quadruple in which
the pair is joined by a circle coprime to the product of the pair.

(Family analogue of CrackCopath.crack_pair_coprime_exists_at.)
-/
import Submission.Apollo.FamOrbit
import Submission.Apollo.FamQForms
import Submission.Apollo.MakeCoprime
import Submission.Apollo.Relabel
import Submission.Apollo.CrackCopath
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

/-- σ-crack families stay in the family orbit. -/
theorem relabelCrack_mem_famOrbit (t : ℕ) (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ)
    (hv : v ∈ orbitOf (famQuad t)) (n : ℕ) : relabelCrack σ v n ∈ orbitOf (famQuad t) := by
  induction n with
  | zero => simpa [relabelCrack] using hv
  | succ n ih =>
      have h1 : gen (σ 2) • relabelCrack σ v n ∈ orbitOf (famQuad t) :=
        famOrbit_gen t (relabelCrack σ v n) ih (σ 2)
      simpa [relabelCrack] using famOrbit_gen t (gen (σ 2) • relabelCrack σ v n) h1 (σ 3)

/-- the parity hypothesis of make_coprime for a relabelled family-orbit
quadruple. -/
lemma hpar_fam_perm (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t))
    (σ : Equiv.Perm (Fin 4)) :
    2 ∣ (w ∘ σ) 0 * (w ∘ σ) 1 → ¬ 2 ∣ (w ∘ σ) 2 ∨ ¬ 2 ∣ (w ∘ σ) 3 := by
  intro h2
  by_contra hne
  push_neg at hne
  have hv2 : 2 ∣ w (σ 2) := by simpa using hne.1
  have hv3 : 2 ∣ w (σ 3) := by simpa using hne.2
  have hs2 : ¬ (σ 2 = 0 ∨ σ 2 = 1) := by
    intro h
    have ho : ¬ 2 ∣ w (σ 2) := (famOrbit_coord_odd_iff t w hw (σ 2)).2 h
    exact ho hv2
  have hs3 : ¬ (σ 3 = 0 ∨ σ 3 = 1) := by
    intro h
    have ho : ¬ 2 ∣ w (σ 3) := (famOrbit_coord_odd_iff t w hw (σ 3)).2 h
    exact ho hv3
  rcases (images01 (σ := σ) hs2 hs3) with ⟨s0, s1⟩
  have hv0 : ¬ 2 ∣ w (σ 0) := by
    rcases s0 with h | h
    · simpa [h] using (famOrbit_parity t w hw).1
    · simpa [h] using (famOrbit_parity t w hw).2.1
  have hv1 : ¬ 2 ∣ w (σ 1) := by
    rcases s1 with h | h
    · simpa [h] using (famOrbit_parity t w hw).1
    · simpa [h] using (famOrbit_parity t w hw).2.1
  exact (odd_mul_int hv0 hv1) h2

/-- crack detour through any tangent pair (σ 0, σ 1) of a family-orbit
quadruple: some crack member keeps the pair and adds a circle coprime to the
product. -/
theorem crack_pair_coprime_exists_at_fam (t : ℕ) (w : Fin 4 → ℤ)
    (hw : w ∈ orbitOf (famQuad t)) (σ : Equiv.Perm (Fin 4)) :
    ∃ u : Fin 4 → ℤ, u ∈ orbitOf (famQuad t) ∧ (∃ n : ℕ, u = relabelCrack σ w n) ∧
      u (σ 0) = w (σ 0) ∧ u (σ 1) = w (σ 1) ∧
      ∃ z : ℤ, z.gcd (w (σ 0) * w (σ 1)) = 1 ∧ ∃ k : Fin 4, (k = σ 2 ∨ k = σ 3) ∧ u k = z := by
  let v : Fin 4 → ℤ := w ∘ σ
  have hDv : (∑ j : Fin 4, v j) ^ 2 = 2 * ∑ j : Fin 4, (v j) ^ 2 := by
    dsimp [v]
    exact descartes_perm w (famOrbit_desc t w hw) σ
  have hgv : Finset.univ.gcd v = 1 := by
    dsimp [v]
    change Finset.univ.gcd (fun j : Fin 4 => w (σ j)) = 1
    rw [gcd_perm w σ]
    exact famOrbit_gcd_one t w hw
  have hzv : v 0 * v 1 ≠ 0 := by
    dsimp [v]
    exact mul_ne_zero (famOrbit_ne_zero t w hw (σ 0)) (famOrbit_ne_zero t w hw (σ 1))
  rcases make_coprime v hDv hgv hzv (hpar_fam_perm t w hw σ) with ⟨x, hx⟩
  rcases two_mul_or_two_mul_add_one x with ⟨n, hx2⟩ | ⟨n, hx2⟩
  · refine ⟨relabelCrack σ w n, ?_, ⟨n, rfl⟩, relabelCrack_fix0 σ w n,
      relabelCrack_fix1 σ w n, ?_⟩
    · exact relabelCrack_mem_famOrbit t σ w hw n
    · refine ⟨relabelCrack σ w n (σ 2), ?_, σ 2, Or.inl rfl, ?_⟩
      · have hm := (relabelCrack_moved σ w n).1
        have hx' : (crackPoly v x).gcd (v 0 * v 1) = 1 := hx
        simpa [v, hm, hx2, mul_comm] using hx'
      · rfl
  · refine ⟨relabelCrack σ w n, ?_, ⟨n, rfl⟩, relabelCrack_fix0 σ w n,
      relabelCrack_fix1 σ w n, ?_⟩
    · exact relabelCrack_mem_famOrbit t σ w hw n
    · refine ⟨relabelCrack σ w n (σ 3), ?_, σ 3, Or.inr rfl, ?_⟩
      · have hm := (relabelCrack_moved σ w n).2
        have hx' : (crackPoly v x).gcd (v 0 * v 1) = 1 := hx
        simpa [v, hm, hx2, mul_comm] using hx'
      · rfl

/-- crack sequences stay in the family orbit. -/
theorem crackSeq_mem_famOrbit (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t)) (n : ℕ) :
    crackSeq w n ∈ orbitOf (famQuad t) := by
  induction n with
  | zero => simpa [crackSeq] using hw
  | succ n ih =>
      have h1 : gen 2 • crackSeq w n ∈ orbitOf (famQuad t) :=
        famOrbit_gen t (crackSeq w n) ih 2
      simpa [crackSeq] using famOrbit_gen t (gen 2 • crackSeq w n) h1 3


/-- canonical crack detour through the pair at indices 0,1 of a family-orbit
quadruple. -/
theorem crack_pair_coprime_exists_fam (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t)) :
    ∃ u : Fin 4 → ℤ, u ∈ orbitOf (famQuad t) ∧ u 0 = w 0 ∧ u 1 = w 1 ∧
      ∃ z : ℤ, z.gcd (w 0 * w 1) = 1 ∧ ∃ k : Fin 4, (k = 2 ∨ k = 3) ∧ u k = z := by
  have hD := famOrbit_desc t w hw
  have hg := famOrbit_gcd_one t w hw
  have hz : w 0 * w 1 ≠ 0 :=
    mul_ne_zero (famOrbit_ne_zero t w hw 0) (famOrbit_ne_zero t w hw 1)
  rcases make_coprime w hD hg hz (hpar_fam_perm t w hw (1 : Equiv.Perm (Fin 4))) with ⟨x, hx⟩
  rcases two_mul_or_two_mul_add_one x with ⟨n, hx2⟩ | ⟨n, hx2⟩
  · refine ⟨crackSeq w n, ?_, crackSeq_fix0 w n, crackSeq_fix1 w n, ?_⟩
    · exact crackSeq_mem_famOrbit t w hw n
    · refine ⟨crackSeq w n 2, ?_, 2, Or.inl rfl, ?_⟩
      · have h23 := (crackSeq23 w n).1
        simpa [h23, hx2] using hx
      · rfl
  · refine ⟨crackSeq w n, ?_, crackSeq_fix0 w n, crackSeq_fix1 w n, ?_⟩
    · exact crackSeq_mem_famOrbit t w hw n
    · refine ⟨crackSeq w n 3, ?_, 3, Or.inr rfl, ?_⟩
      · have h23 := (crackSeq23 w n).2
        simpa [h23, hx2] using hx
      · rfl

end Apollo
