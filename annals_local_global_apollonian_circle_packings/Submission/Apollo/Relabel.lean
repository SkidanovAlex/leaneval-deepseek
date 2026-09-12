/-
Coordinate relabelings and crack families through an arbitrary tangent pair.

A permutation σ : Fin 4 ≃ Fin 4 reorders the coordinates of a quadruple.
The key equivariance: moving the σ(i)-coordinate of the relabelled vector is
the same as relabelling the result of moving the i-coordinate
(`relabel_move`).  Pushing the canonical crack family (fixed pair of indices
0,1; moves at 2 then 3) through such a relabelling gives the crack family
`relabelCrack σ v` with the fixed pair at indices σ 0, σ 1 and moves
alternating at σ 2 and σ 3 (first σ 2, then σ 3).
-/
import Submission.Apollo.Crack
import Submission.Apollo.Parity
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

/-- The sum over the coordinates other than i equals the total sum minus v i. -/
lemma sum_others (v : Fin 4 → ℤ) (i : Fin 4) :
    (∑ k : Fin 4, if k = i then 0 else v k) = (∑ k : Fin 4, v k) - v i := by
  fin_cases i <;> simp [Fin.sum_univ_four] <;> ring

/-- Relabelling commutes with S-moves:  gen (σ i) applied to the relabelled
vector equals the relabelling of gen i applied to the original vector. -/
theorem relabel_move (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ) (i : Fin 4) :
    gen (σ i) • (v ∘ σ.symm) = (gen i • v) ∘ σ.symm := by
  ext j
  rw [gen_smul_apply]
  change (if j = σ i then -(v ∘ σ.symm) (σ i) + 2 * (∑ k : Fin 4, if k = σ i then 0 else (v ∘ σ.symm) k)
      else (v ∘ σ.symm) j) = (gen i • v) (σ.symm j)
  rw [gen_smul_apply]
  by_cases h : j = σ i
  · have h' : σ.symm j = i := by
      rw [h]
      simp
    simp [h, h', sum_others]
    rw [Equiv.sum_comp]
  · have h' : σ.symm j ≠ i := by
      intro hj
      apply h
      exact (Equiv.apply_symm_apply σ j).symm.trans (congrArg σ hj)
    simp [h, h']

/-- the σ-crack family: fixed pair at indices σ 0, σ 1; alternating moves at
σ 2 (first) and σ 3. -/
def relabelCrack (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ) : ℕ → Fin 4 → ℤ
  | 0 => v
  | n + 1 => gen (σ 3) • (gen (σ 2) • relabelCrack σ v n)

/-- relabelCrack equals the canonical crack family of the relabelled vector,
mapped back to the original coordinates. -/
theorem relabelCrack_eq (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ) (n : ℕ) :
    relabelCrack σ v n = (crackSeq (v ∘ σ) n) ∘ σ.symm := by
  induction n with
  | zero =>
      ext k
      simp [relabelCrack, crackSeq, Equiv.symm_apply_apply]
  | succ n ih =>
      rw [relabelCrack]
      -- relabelCrack σ v (n+1) = gen (σ 3) • (gen (σ 2) • relabelCrack σ v n)
      rw [ih]
      -- show: gen (σ 3) • (gen (σ 2) • (crackSeq (v∘σ) n ∘ σ.symm)) = (crackSeq (v∘σ) (n+1)) ∘ σ.symm
      have h2 : gen (σ 2) • (crackSeq (v ∘ σ) n ∘ σ.symm) = (gen 2 • crackSeq (v ∘ σ) n) ∘ σ.symm := by
        exact relabel_move σ (crackSeq (v ∘ σ) n) 2
      have h3 : gen (σ 3) • ((gen 2 • crackSeq (v ∘ σ) n) ∘ σ.symm) = (gen 3 • (gen 2 • crackSeq (v ∘ σ) n)) ∘ σ.symm := by
        exact relabel_move σ (gen 2 • crackSeq (v ∘ σ) n) 3
      rw [h2, h3]
      rfl

/-- The pair at σ 0, σ 1 is fixed along the σ-crack. -/
theorem relabelCrack_fix0 (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ) (n : ℕ) :
    relabelCrack σ v n (σ 0) = v (σ 0) := by
  rw [relabelCrack_eq]
  change crackSeq (v ∘ σ) n (σ.symm (σ 0)) = v (σ 0)
  simp [Equiv.symm_apply_apply, crackSeq_fix0]

theorem relabelCrack_fix1 (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ) (n : ℕ) :
    relabelCrack σ v n (σ 1) = v (σ 1) := by
  rw [relabelCrack_eq]
  change crackSeq (v ∘ σ) n (σ.symm (σ 1)) = v (σ 1)
  simp [Equiv.symm_apply_apply, crackSeq_fix1]

/-- the coordinates at σ 2 and σ 3 follow the quadratic crackPoly (v∘σ). -/
theorem relabelCrack_moved (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ) (n : ℕ) :
    relabelCrack σ v n (σ 2) = crackPoly (v ∘ σ) (2 * (n : ℤ)) ∧
      relabelCrack σ v n (σ 3) = crackPoly (v ∘ σ) (2 * (n : ℤ) + 1) := by
  rw [relabelCrack_eq]
  constructor
  · change crackSeq (v ∘ σ) n (σ.symm (σ 2)) = crackPoly (v ∘ σ) (2 * (n : ℤ))
    simp [Equiv.symm_apply_apply]
    exact (crackSeq23 (v ∘ σ) n).1
  · change crackSeq (v ∘ σ) n (σ.symm (σ 3)) = crackPoly (v ∘ σ) (2 * (n : ℤ) + 1)
    simp [Equiv.symm_apply_apply]
    exact (crackSeq23 (v ∘ σ) n).2

/-- Descartes quadruples stay Descartes along the σ-crack. -/
theorem relabelCrack_descarates (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ)
    (hv : (∑ j : Fin 4, v j) ^ 2 = 2 * ∑ j : Fin 4, (v j) ^ 2) (n : ℕ) :
    (∑ j : Fin 4, relabelCrack σ v n j) ^ 2 = 2 * ∑ j : Fin 4, (relabelCrack σ v n j) ^ 2 := by
  rw [relabelCrack_eq]
  have hσ : (∑ j : Fin 4, (crackSeq (v ∘ σ) n ∘ σ.symm) j) = ∑ j : Fin 4, crackSeq (v ∘ σ) n j := by
    change (∑ j : Fin 4, crackSeq (v ∘ σ) n (σ.symm j)) = ∑ j : Fin 4, crackSeq (v ∘ σ) n j
    simpa using (Equiv.sum_comp σ.symm (fun k : Fin 4 => crackSeq (v ∘ σ) n k))
  have hsq : (∑ j : Fin 4, ((crackSeq (v ∘ σ) n ∘ σ.symm) j) ^ 2) = ∑ j : Fin 4, (crackSeq (v ∘ σ) n j) ^ 2 := by
    change (∑ j : Fin 4, (crackSeq (v ∘ σ) n (σ.symm j)) ^ 2) = ∑ j : Fin 4, (crackSeq (v ∘ σ) n j) ^ 2
    simpa using (Equiv.sum_comp σ.symm (fun k : Fin 4 => (crackSeq (v ∘ σ) n k) ^ 2))
  have hper : (∑ j : Fin 4, (v ∘ σ) j) ^ 2 = 2 * ∑ j : Fin 4, ((v ∘ σ) j) ^ 2 := by
    -- Descartes is invariant under relabelling
    have h1 : (∑ j : Fin 4, (v ∘ σ) j) = ∑ j : Fin 4, v j := by
      simpa using (Equiv.sum_comp σ v)
    have h2 : (∑ j : Fin 4, ((v ∘ σ) j) ^ 2) = ∑ j : Fin 4, (v j) ^ 2 := by
      simpa using (Equiv.sum_comp σ (fun k : Fin 4 => (v k) ^ 2))
    rw [h1, h2]
    exact hv
  have hc := crackSeq_descarates (v ∘ σ) hper n
  rw [hσ]
  rw [hsq]
  exact hc

/-- σ-crack families stay in the orbit. -/
theorem relabelCrack_mem_apOrbit (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ)
    (hv : v ∈ apOrbit) (n : ℕ) : relabelCrack σ v n ∈ apOrbit := by
  induction n with
  | zero => simpa [relabelCrack] using hv
  | succ n ih =>
      have h1 : gen (σ 2) • relabelCrack σ v n ∈ apOrbit :=
        gen_smul_mem_apOrbit (relabelCrack σ v n) ih (σ 2)
      simpa [relabelCrack] using gen_smul_mem_apOrbit (gen (σ 2) • relabelCrack σ v n) h1 (σ 3)


/-- the Descartes equation is invariant under relabelling the coordinates. -/
theorem descartes_perm (v : Fin 4 → ℤ)
    (hv : (∑ j : Fin 4, v j) ^ 2 = 2 * ∑ j : Fin 4, (v j) ^ 2) (σ : Equiv.Perm (Fin 4)) :
    (∑ j : Fin 4, (v ∘ σ) j) ^ 2 = 2 * ∑ j : Fin 4, ((v ∘ σ) j) ^ 2 := by
  have h1 : (∑ j : Fin 4, (v ∘ σ) j) = ∑ j : Fin 4, v j := by
    simpa using (Equiv.sum_comp σ v)
  have h2 : (∑ j : Fin 4, ((v ∘ σ) j) ^ 2) = ∑ j : Fin 4, (v j) ^ 2 := by
    simpa using (Equiv.sum_comp σ (fun k : Fin 4 => (v k) ^ 2))
  rw [h1, h2]
  exact hv

/-- nonnegative integers equal when they divide each other. -/
lemma eq_of_dvd_of_dvd_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h1 : a ∣ b)
    (h2 : b ∣ a) : a = b := by
  have h1' : a.natAbs ∣ b.natAbs := Int.natAbs_dvd_natAbs.mpr h1
  have h2' : b.natAbs ∣ a.natAbs := Int.natAbs_dvd_natAbs.mpr h2
  have hnat : a.natAbs = b.natAbs := Nat.dvd_antisymm h1' h2'
  have ha' : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg ha
  have hb' : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg hb
  have hz : ((a.natAbs : ℕ) : ℤ) = ((b.natAbs : ℕ) : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) hnat
  rwa [ha', hb'] at hz

/-- the gcd of the coordinates is invariant under relabelling. -/
theorem gcd_perm (v : Fin 4 → ℤ) (σ : Equiv.Perm (Fin 4)) :
    Finset.univ.gcd (fun j : Fin 4 => v (σ j)) = Finset.univ.gcd v := by
  apply eq_of_dvd_of_dvd_nonneg
  · exact (Finset.Int.finsetGcd_nonneg (s := (Finset.univ : Finset (Fin 4))) (f := (fun j : Fin 4 => v (σ j))))
  · exact (Finset.Int.finsetGcd_nonneg (s := (Finset.univ : Finset (Fin 4))) (f := v))
  · rw [Finset.dvd_gcd_iff]
    intro k hk
    have hd : (Finset.univ.gcd (fun j : Fin 4 => v (σ j)) : ℤ) ∣ v (σ (σ.symm k)) :=
      Finset.gcd_dvd (Finset.mem_univ (σ.symm k))
    simpa [Equiv.apply_symm_apply] using hd
  · rw [Finset.dvd_gcd_iff]
    intro k hk
    exact Finset.gcd_dvd (Finset.mem_univ (σ k))

end Apollo
