import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Final.iterDerivNorm_comp_smul
import Submission.Work.CR.Flat.Holder.holderNorm_le_ofReal_inv_pow_mul_comp_smul
import Submission.Work.CR.Flat.Polydisc.setOf_smul_mem_polydisc

namespace Work.NN.Newton.ThinLocal

open scoped NNReal ENNReal
open Set

/-- **Scaling of the `C^{2,α}` norm for `α < 1`, in the direction that costs `1/s³`.**

The dilation `ζ ↦ s • ζ` maps the polydisc of radius `2` onto the polydisc of radius `2s`
(`setOf_smul_mem_polydisc`), and the exact scaling identity for the within-derivatives
(`Work.NN.Final.iterDerivNorm_comp_smul`) says that on the preimage of `Ω`,
`iterDerivNorm i (f ∘ (s • ·)) = s^i · iterDerivNorm i f Ω` and
`holderSeminorm i α (f ∘ (s • ·)) = s^{i+α} · holderSeminorm i α f Ω`.
Hence for `0 < s ≤ 1` the norm of the blown-up function is the small quantity
`s^{i+α} · (norm of f)` (times the inverse on the other side), and since `i + α ≤ 2 + α ≤ 3`
for `i ≤ 2`, the loss is at most `s^{-3}`: this is
`Work.CR.Flat.Holder.holderNorm_le_ofReal_inv_pow_mul_comp_smul` with `k = 2`, `α ≤ 1`. -/
theorem scalingU {n : ℕ} {α : ℝ} (hα1 : α < 1) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (h : (Fin n → ℂ) → ℂ) :
    Work.CR.Flat.holderNorm 2 α h (Work.CR.Flat.polydisc 0 (fun _ => 2 * s)) ≤
      ENNReal.ofReal (1 / s ^ 3) *
        Work.CR.Flat.holderNorm 2 α (fun ζ => h (s • ζ))
          (Work.CR.Flat.polydisc 0 (fun _ => 2)) := by
  have hset : {z : Fin n → ℂ | s • z ∈ Work.CR.Flat.polydisc 0 (fun _ => 2 * s)}
      = Work.CR.Flat.polydisc 0 (fun _ => 2) := by
    have h1 := Work.CR.Flat.Polydisc.setOf_smul_mem_polydisc (s := s) hs0 (0 : Fin n → ℂ)
      (fun _ : Fin n => 2)
    simpa using h1
  have hkey := Work.CR.Flat.Holder.holderNorm_le_ofReal_inv_pow_mul_comp_smul
    (X := Fin n → ℂ) (k := 2) (α := α) hα1.le hs0 hs1 h
    (Work.CR.Flat.isOpen_polydisc (0 : Fin n → ℂ) (fun _ : Fin n => 2 * s))
  rw [hset] at hkey
  simpa using hkey

end Work.NN.Newton.ThinLocal
