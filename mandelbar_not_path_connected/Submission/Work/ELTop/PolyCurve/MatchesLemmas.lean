/-
# Reading the cyclic lift off the list of pairs

`CycLift.Matches D ps` says that the `i`-th pair of the list `ps` is the pair of index
`i + m q` of the lift `D`.  This module extracts from it the two facts needed downstream:

* the canonical values `D.A i = (ps.get i).a`, `D.B i = (ps.get i).b`, `D.Y i = (ps.get i).y`,
  hence the landing data of every pair of the lift;
* the converse: every index `k : ℤ` is the lift of one of the pairs of `ps`, so that every ray
  piece of the lift is one of the ray pieces of `ps`.
-/
import Mathlib
import Submission.Work.ELTop.PolyCurve.Defs
import Submission.Work.ELTop.PolyCurve.Blocks

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

variable {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}

namespace CycLift

variable {D : CycLift hN} {ps : List (Work.EL.CoPair hN)}

theorem Matches.m_eq (hM : D.Matches ps) : D.m = ps.length := hM.1

theorem Matches.A_get (hM : D.Matches ps) (i : Fin ps.length) : D.A (i : ℤ) = (ps.get i).a := by
  obtain ⟨k, q, hk, hA, -, -⟩ := hM.2 i
  have hcast : (ps.length : ℤ) * q = (D.m : ℤ) * q := by rw [hM.m_eq]
  have hk' : k = (i : ℤ) + (D.m : ℤ) * q := by
    simpa only [hcast] using hk
  have h1 : D.A k = D.A (i : ℤ) + (q : ℝ) := by rw [hk', D.A_shift]
  linarith

theorem Matches.B_get (hM : D.Matches ps) (i : Fin ps.length) : D.B (i : ℤ) = (ps.get i).b := by
  obtain ⟨k, q, hk, -, hB, -⟩ := hM.2 i
  have hcast : (ps.length : ℤ) * q = (D.m : ℤ) * q := by rw [hM.m_eq]
  have hk' : k = (i : ℤ) + (D.m : ℤ) * q := by
    simpa only [hcast] using hk
  have h1 : D.B k = D.B (i : ℤ) + (q : ℝ) := by rw [hk', D.B_shift]
  linarith

theorem Matches.Y_get (hM : D.Matches ps) (i : Fin ps.length) : D.Y (i : ℤ) = (ps.get i).y := by
  obtain ⟨k, q, hk, -, -, hY⟩ := hM.2 i
  have hcast : (ps.length : ℤ) * q = (D.m : ℤ) * q := by rw [hM.m_eq]
  have hk' : k = (i : ℤ) + (D.m : ℤ) * q := by
    simpa only [hcast] using hk
  have h1 : D.Y k = D.Y (i : ℤ) := by rw [hk', D.Y_shift]
  rw [h1] at hY
  exact hY

/-- The rays of the `i`-th pair of the lift land at `Y i`. -/
theorem Matches.landsN_get (hM : D.Matches ps) (i : Fin ps.length) :
    Work.EL.LandsN hN (D.A (i : ℤ)) (D.Y (i : ℤ)) ∧
      Work.EL.LandsN hN (D.B (i : ℤ)) (D.Y (i : ℤ)) := by
  rw [hM.A_get i, hM.B_get i, hM.Y_get i]
  exact ⟨(ps.get i).lands_a, (ps.get i).lands_b⟩

/-- Every index `k` of the lift is the lift of one of the pairs of the list, at a shift `q`. -/
theorem Matches.exists_of_mem (hM : D.Matches ps) (k : ℤ) :
    ∃ i : Fin ps.length, ∃ q : ℤ,
      D.A k = (ps.get i).a + (q : ℝ) ∧ D.B k = (ps.get i).b + (q : ℝ) ∧ D.Y k = (ps.get i).y := by
  have hm : 0 < ps.length := by
    rw [← hM.m_eq]
    exact D.hm
  have hpos : 0 < (ps.length : ℤ) := by exact_mod_cast hm
  have hnn : 0 ≤ k % (ps.length : ℤ) := Int.emod_nonneg k (by omega)
  have hlt : k % (ps.length : ℤ) < (ps.length : ℤ) := Int.emod_lt_of_pos k hpos
  have hlt' : (k % (ps.length : ℤ)).toNat < ps.length := by
    have h2 : ((k % (ps.length : ℤ)).toNat : ℤ) < (ps.length : ℤ) := by
      rw [Int.toNat_of_nonneg hnn]; exact hlt
    exact_mod_cast h2
  obtain ⟨i, hi⟩ : ∃ i : Fin ps.length, (i : ℤ) = k % (ps.length : ℤ) :=
    ⟨⟨(k % (ps.length : ℤ)).toNat, hlt'⟩, by rw [Int.toNat_of_nonneg hnn]⟩
  have key : (i : ℤ) + (D.m : ℤ) * (k / (ps.length : ℤ)) = k := by
    have h1 : (i : ℤ) + (ps.length : ℤ) * (k / (ps.length : ℤ)) = k := by
      rw [hi]
      exact Int.emod_add_mul_ediv k (ps.length : ℤ)
    have hcast : (ps.length : ℤ) * (k / (ps.length : ℤ)) = (D.m : ℤ) * (k / (ps.length : ℤ)) := by
      rw [hM.m_eq]
    rw [hcast] at h1
    exact h1
  refine ⟨i, k / (ps.length : ℤ), ?_, ?_, ?_⟩
  · conv_lhs => rw [← key]
    rw [D.A_shift, hM.A_get i]
  · conv_lhs => rw [← key]
    rw [D.B_shift, hM.B_get i]
  · conv_lhs => rw [← key]
    rw [D.Y_shift, hM.Y_get i]

end CycLift

end Work.ELTop
