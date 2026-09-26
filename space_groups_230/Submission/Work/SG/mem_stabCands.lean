import Mathlib
import Submission.Work.SG.Data.SellCheck

namespace Work.SG

open Work.SG.Data

/-! # Membership in `stabCands`

`Work.SG.Data.stabCands V : List Work.SG.Data.M3` (in `Submission/Work/SG/Data/SellCheck.lean`)
enumerates all column triples `(c₀,c₁,c₂) ∈ V³` and keeps `A = ofCols c₀ c₁ c₂` when
`det A = ±1` and `V.all (fun y => V.contains (M3.mulV A y))`.  The claim is that membership is
equivalent to the flat conditions below.  Note `ofCols (M3.cols A) = A` and
`M3.cols (ofCols c₀ c₁ c₂) = [c₀,c₁,c₂]`, so "the columns of `A` lie in `V`" is exactly the
enumeration condition, and `V.contains z = true ↔ z ∈ V` by `List.contains_iff_mem` (which
needs no `Nodup`).  Also `(M3.det A == 1 || M3.det A == -1) = true ↔ M3.det A = 1 ∨
M3.det A = -1` by `beq_iff_eq`/`Bool.or_eq_true_iff`. -/

private lemma cols_ofCols (u v w : V3) : M3.cols (M3.ofCols u v w) = [u, v, w] := by
  cases u; cases v; cases w; rfl

private lemma ofCols_cols (A : M3) :
    M3.ofCols ((M3.cols A).getD 0 V3.zero) ((M3.cols A).getD 1 V3.zero)
      ((M3.cols A).getD 2 V3.zero) = A := by
  cases A; rfl

/-- Flat characterisation of `stabCands` membership: the columns lie in `V`, `det = ±1`, and
`V` is closed under `A`. -/
private lemma mem_stabCands_iff (V : List V3) (A : M3) :
    A ∈ stabCands V ↔
      (∀ k : Fin 3, (M3.cols A).getD k.val V3.zero ∈ V) ∧
      (M3.det A == 1 || M3.det A == -1) = true ∧
      V.all (fun y => V.contains (M3.mulV A y)) = true := by
  constructor
  · intro h
    rw [stabCands, List.mem_flatMap] at h
    obtain ⟨c0, hc0, h⟩ := h
    rw [List.mem_flatMap] at h
    obtain ⟨c1, hc1, h⟩ := h
    rw [List.mem_filterMap] at h
    obtain ⟨c2, hc2, h⟩ := h
    simp only at h
    by_cases hc : (M3.det (M3.ofCols c0 c1 c2) == 1 || M3.det (M3.ofCols c0 c1 c2) == -1) &&
        V.all (fun y => V.contains (M3.mulV (M3.ofCols c0 c1 c2) y))
    · rw [ite_eq_left hc] at h
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨?_, ?_, ?_⟩
      · intro k
        rw [cols_ofCols]
        fin_cases k <;> simp [hc0, hc1, hc2]
      · exact (Bool.and_eq_true_iff.mp hc).1
      · exact (Bool.and_eq_true_iff.mp hc).2
    · rw [ite_eq_right hc] at h
      exact absurd h (by simp)
  · intro ⟨hcol, hdet, hall⟩
    have hof := ofCols_cols A
    rw [stabCands, List.mem_flatMap]
    refine ⟨(M3.cols A).getD 0 V3.zero, hcol ⟨0, by decide⟩, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨(M3.cols A).getD 1 V3.zero, hcol ⟨1, by decide⟩, ?_⟩
    rw [List.mem_filterMap]
    refine ⟨(M3.cols A).getD 2 V3.zero, hcol ⟨2, by decide⟩, ?_⟩
    simp only
    rw [ite_eq_left ?_]
    · rw [hof]
    · rw [Bool.and_eq_true_iff]
      exact ⟨by rwa [← hof] at hdet, by rwa [← hof] at hall⟩

theorem mem_stabCands {V : List Work.SG.Data.V3} {A : Work.SG.Data.M3} :
    A ∈ Work.SG.Data.stabCands V ↔
      (Work.SG.Data.M3.det A = 1 ∨ Work.SG.Data.M3.det A = -1) ∧
      (∀ k : Fin 3, (Work.SG.Data.M3.cols A).getD k.val Work.SG.Data.V3.zero ∈ V) ∧
      (∀ y ∈ V, Work.SG.Data.M3.mulV A y ∈ V) := by
  rw [mem_stabCands_iff]
  constructor
  · rintro ⟨hcol, hdet, hall⟩
    refine ⟨?_, hcol, ?_⟩
    · rw [Bool.or_eq_true_iff, beq_iff_eq, beq_iff_eq] at hdet
      exact hdet
    · intro y hy
      have hy' := (List.all_eq_true.mp hall) y hy
      rwa [List.contains_iff_mem] at hy'
  · rintro ⟨hdet, hcol, hall⟩
    refine ⟨hcol, ?_, ?_⟩
    · rw [Bool.or_eq_true_iff, beq_iff_eq, beq_iff_eq]
      exact hdet
    · rw [List.all_eq_true]
      intro y hy
      rw [List.contains_iff_mem]
      exact hall y hy

end Work.SG
