import Mathlib
import Submission.Work.L2F.Props.oddsub.CommonEigenvectorAux

namespace Work.L2F.Props.oddsub

theorem isScalar_sq_of_swapping_eigenlines {F : Type*} [Field F] {A : Matrix (Fin 2) (Fin 2) F}
    {v u : Fin 2 → F} {c d : F}
    (hv : v ≠ 0) (huv : u ∉ Submodule.span F ({v} : Set (Fin 2 → F)))
    (hlv : Matrix.mulVec A v = c • u) (hlu : Matrix.mulVec A u = d • v) :
    ∃ e : F, A * A = e • (1 : Matrix (Fin 2) (Fin 2) F) := by
  -- `v` and `u` are linearly independent: `u` is not a multiple of the nonzero vector `v`.
  have hli : LinearIndependent F ![v, u] := by
    rw [LinearIndependent.pair_iff' hv]
    intro a ha
    exact huv (by rw [Submodule.mem_span_singleton]; exact ⟨a, ha⟩)
  -- hence they span the two-dimensional space `F²`.
  have hspan : Submodule.span F (Set.range ![v, u]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  -- Let `M = A * A - (c * d) • 1`.  It suffices to show `M = 0`.
  set M : Matrix (Fin 2) (Fin 2) F := A * A - (c * d) • 1 with hM
  -- `A * A` acts on `v` by `c * d`:  `A (A v) = A (c u) = c (A u) = c (d v)`.
  have hMv : Matrix.mulVec M v = 0 := by
    rw [hM, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hmul : Matrix.mulVec (A * A) v = (c * d) • v := by
      rw [← Matrix.mulVec_mulVec v A A, hlv, Matrix.mulVec_smul, hlu, smul_smul]
    rw [hmul, sub_self]
  -- similarly `A * A` acts on `u` by `c * d`.
  have hMu : Matrix.mulVec M u = 0 := by
    rw [hM, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hmul : Matrix.mulVec (A * A) u = (c * d) • u := by
      rw [← Matrix.mulVec_mulVec u A A, hlu, Matrix.mulVec_smul, hlv, smul_smul, mul_comm]
    rw [hmul, sub_self]
  -- Since `v` and `u` span, `M` annihilates every vector.
  have hzero : ∀ w ∈ Submodule.span F (Set.range ![v, u]), Matrix.mulVec M w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        fin_cases i
        · simpa using hMv
        · simpa using hMu
    | zero => simp
    | add x y _ _ ihx ihy => rw [Matrix.mulVec_add, ihx, ihy, add_zero]
    | smul a x _ ih => rw [Matrix.mulVec_smul, ih, smul_zero]
  have hzero_all : ∀ w : Fin 2 → F, Matrix.mulVec M w = 0 := fun w =>
    hzero w (by rw [hspan]; exact Submodule.mem_top)
  have hMzero : M = 0 := by
    ext i j
    have h := hzero_all (Pi.single j (1 : F))
    rw [Matrix.mulVec_single_one] at h
    have h2 := congrFun h i
    simpa [Matrix.col_apply] using h2
  exact ⟨c * d, sub_eq_zero.mp (hM ▸ hMzero)⟩

end Work.L2F.Props.oddsub
