import Mathlib
import Submission.Work.WilG4c.ChartRescaleDefs
import Submission.Work.WilG5.Basic

namespace Work.WilG4c

open WilkiesDesign

/-- The `Ω`-bookkeeping for the "rescale the value of a family member" operation.

`crSet m K c A` is (by `crSet_eq_liftLast`) the intersection of the lift of `A` to the
trailing `m+1` coordinates with the zero set of the single degree-`2` polynomial `crQ m K c`.
Hence

* `liftLast (m+1) A ∈ S.Ω (F0 + (m+1)) D (2(m+1))` (cost `m+1` formats),
* the zero set of `crQ` is in `S.Ω (2(m+1)) 2 (2(m+1))` (`hyp` + `CrQ_totalDegree_le`),
* their intersection costs one more format and adds `2` to the degree,
* projecting the `m+1` fresh coordinates away costs `m+1` more formats.

The total format cost is therefore a constant depending on `m` only (`4*(m+1)+4` is a safe
bound), and the degree cost is exactly `2`. -/
theorem CrSetMem (S : WilkiesDesign.SOMin) (m : ℕ) :
    ∃ K₀ : ℕ, ∀ (K : ℕ) (c : ℝ) (F0 D : ℕ) (A : Set (Fin (m + 1) → ℝ)),
      A ∈ S.Ω F0 D (m + 1) →
      Work.WilG5.projN (m + 1) (Work.WilG4c.crSet m K c A) ∈
        S.Ω (F0 + K₀) (D + 2) (m + 1) := by
  refine ⟨4 * (m + 1) + 4, ?_⟩
  intro K c F0 D A hA
  -- The lift of `A` to the trailing `m+1` coordinates (the `u`-block).
  have hLift : Work.WilG5.liftLast (m + 1) A ∈
      S.Ω (F0 + (m + 1)) D ((m + 1) + (m + 1)) :=
    Work.WilG5.liftLast_mem (S := S) (m + 1) F0 D hA
  -- The zero set of the degree-`2` relation `crQ`.
  have hQ : {v : Fin ((m + 1) + (m + 1)) → ℝ |
      MvPolynomial.eval v (crQ m K c) = 0} ∈
      S.Ω ((m + 1) + (m + 1)) 2 ((m + 1) + (m + 1)) :=
    Work.WilG5.mem_mono (S := S) (S.hyp ((m + 1) + (m + 1)) (crQ m K c))
      ((m + 1) + (m + 1)) 2 le_rfl (CrQ_totalDegree_le m K c)
  -- Intersect: one extra format, degrees add.
  have hInt := Work.WilkG4c.Omega_inter S hLift hQ
  have hcr : crSet m K c A =
      Work.WilG5.liftLast (m + 1) A ∩ {v | MvPolynomial.eval v (crQ m K c) = 0} :=
    crSet_eq_liftLast m K c A
  have hInt' : crSet m K c A ∈
      S.Ω (max (F0 + (m + 1)) ((m + 1) + (m + 1)) + 1) (D + 2) ((m + 1) + (m + 1)) := by
    rw [hcr]; exact hInt
  -- Project the fresh `m+1` coordinates away: `m+1` more formats.
  have hproj := Work.WilG5.projN_mem (S := S) (n := m + 1) (m + 1)
    (max (F0 + (m + 1)) ((m + 1) + (m + 1)) + 1) (D + 2) hInt'
  refine Work.WilG5.mem_mono (S := S) hproj (F0 + (4 * (m + 1) + 4)) (D + 2) ?_ le_rfl
  have hmax : max (F0 + (m + 1)) ((m + 1) + (m + 1)) ≤ F0 + 2 * (m + 1) :=
    max_le (by omega) (by omega)
  omega

end Work.WilG4c
