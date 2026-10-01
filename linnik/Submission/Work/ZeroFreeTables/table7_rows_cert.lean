import Mathlib
import Submission.Work.ZeroFreeTables.HBTable7_defs
import Submission.Work.ZeroFreeTables.T7Cert
import Submission.Work.ZeroFreeTables.T7Row01
import Submission.Work.ZeroFreeTables.T7Row02
import Submission.Work.ZeroFreeTables.T7Row03
import Submission.Work.ZeroFreeTables.T7Row04
import Submission.Work.ZeroFreeTables.T7Row05
import Submission.Work.ZeroFreeTables.T7Row06
import Submission.Work.ZeroFreeTables.T7Row07
import Submission.Work.ZeroFreeTables.T7Row08
import Submission.Work.ZeroFreeTables.T7Row09
import Submission.Work.ZeroFreeTables.T7Row10
import Submission.Work.ZeroFreeTables.T7Row11
import Submission.Work.ZeroFreeTables.T7Row12
import Submission.Work.ZeroFreeTables.T7Row13
import Submission.Work.ZeroFreeTables.T7Row14
import Submission.Work.ZeroFreeTables.T7Row15
import Submission.Work.ZeroFreeTables.T7Row16
import Submission.Work.ZeroFreeTables.T7Row17

namespace Work.ZeroFreeTables

open scoped Real BigOperators

/-- The seventeen rows of Heath-Brown's Table 7, each certified by the strict
failure of HB (8.11) at the parameters listed in `T7Cert`. -/
theorem table7_rows_cert : ∀ p ∈ tableR hbTable7, ∃ (k lam ε : ℝ), CertRow p.1 p.2 k lam ε := by
  intro p hp
  simp only [tableR, hbTable7, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨a, ha, rfl⟩
  rcases ha with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨965/1000, 9758/10000, 0, ?_⟩
    convert T7Row01 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨962/1000, 9624/10000, 0, ?_⟩
    convert T7Row02 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨959/1000, 9497/10000, 0, ?_⟩
    convert T7Row03 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨956/1000, 9395/10000, 0, ?_⟩
    convert T7Row04 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨953/1000, 9281/10000, 0, ?_⟩
    convert T7Row05 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨950/1000, 9187/10000, 0, ?_⟩
    convert T7Row06 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨9425/10000, 8942/10000, 0, ?_⟩
    convert T7Row07 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨935/1000, 8725/10000, 0, ?_⟩
    convert T7Row08 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨9275/10000, 8514/10000, 0, ?_⟩
    convert T7Row09 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨92/100, 8331/10000, 0, ?_⟩
    convert T7Row10 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨9125/10000, 8164/10000, 0, ?_⟩
    convert T7Row11 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨905/1000, 7988/10000, 0, ?_⟩
    convert T7Row12 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨8975/10000, 7848/10000, 0, ?_⟩
    convert T7Row13 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨89/100, 7677/10000, 0, ?_⟩
    convert T7Row14 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨8825/10000, 7516/10000, 0, ?_⟩
    convert T7Row15 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨875/1000, 7371/10000, 0, ?_⟩
    convert T7Row16 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨8682/10000, 726/1000, 0, ?_⟩
    convert T7Row17 using 1 <;> norm_num

end Work.ZeroFreeTables
