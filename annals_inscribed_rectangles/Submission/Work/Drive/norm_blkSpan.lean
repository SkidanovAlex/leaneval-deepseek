import Mathlib
import Submission.Work.Drive.chartShiftHsurj

namespace Work.Drive

/-- The `j`-th coordinate of the `k`-th block of `ℝ¹²`, packaged as a `Fin 4`, is the reduced
representative of the `12`-index modulo `4`. -/
lemma blkSpan_ofLp_apply (k : Fin 3) (z : EuclideanSpace ℝ (Fin 4)) (i : Fin 12) :
    (blkSpan k z).ofLp i
      = if i.val / 4 = k.val then z.ofLp ⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩ else 0 := by
  rw [blkSpan, WithLp.ofLp_toLp]

/-- **The block-spanning vector has the same norm as the vector it realises.**  `Work.Drive.blkSpan k z`
is the vector of the `12`-dimensional design parameter whose `k`-th block is `z` and whose other two
blocks vanish, so its Euclidean norm is that of `z`.  This is the normalisation that lets a small move
of one block's parameter (`t₀ + blkSpan k σ`) be a small move of the full design parameter. -/
theorem norm_blkSpan (k : Fin 3) (z : EuclideanSpace ℝ (Fin 4)) :
    ‖Work.Drive.blkSpan k z‖ = ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  -- only the `k`-th block of `blkSpan k z` is nonzero, and there it reproduces `z`
  have hterm : ∀ i : Fin 12, ‖(blkSpan k z).ofLp i‖ ^ 2
      = (if i.val / 4 = k.val then
          ‖z.ofLp ⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩‖ ^ 2 else 0) := by
    intro i
    rw [blkSpan_ofLp_apply]
    by_cases h : i.val / 4 = k.val <;> simp [h]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [← Finset.sum_filter]
  -- the surviving indices are exactly the four of the `k`-th block
  refine Finset.sum_bij (fun (a : Fin 12)
      (_ : a ∈ Finset.univ.filter (fun i : Fin 12 => i.val / 4 = k.val)) =>
    ⟨a.val % 4, Nat.mod_lt _ (by norm_num)⟩) ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_univ _
  · intro a1 ha1 a2 ha2 heq
    have h1 : a1.val / 4 = k.val := (Finset.mem_filter.mp ha1).2
    have h2 : a2.val / 4 = k.val := (Finset.mem_filter.mp ha2).2
    have hmod : a1.val % 4 = a2.val % 4 := congrArg Fin.val heq
    have e1 := Nat.div_add_mod a1.val 4
    have e2 := Nat.div_add_mod a2.val 4
    exact Fin.ext (by omega)
  · intro b _
    refine ⟨blkIdx k b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, blkIdx_div k b⟩, ?_⟩
    ext
    show (blkIdx k b).val % 4 = b.val
    rw [blkIdx, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]
  · intro a _
    rfl

end Work.Drive
