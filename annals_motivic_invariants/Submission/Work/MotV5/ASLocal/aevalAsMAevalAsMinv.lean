import Mathlib
import Submission.Work.MotAS.asM_mul_asMinv
import Submission.Work.MotAS.asMinv_mul_asM
import Submission.Work.MotAS.Ker4.asKleinIdeal4_finrank_ge

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `aeval (asM w) ∘ aeval (asMinv w) = id`

The mirror image of `Work.MotAS.Ker4.aeval_asMinv_aeval_asM`: the Galois-coordinate substitution
with matrix `asM w i j = (w+i)^j` is a *left* inverse of the Lagrange substitution with matrix
`asMinv w j i = δ_{j,0} - (w+i)^{4-j}`.

Both substitutions are `Kb 𝕜`-algebra endomorphisms of `MvPolynomial (Fin 5) (Kb 𝕜)`; by
`MvPolynomial.algHom_ext` it suffices to compare them on the generators `X i`, where the
computation reduces to the matrix identity `asMinv w * asM w = 1`
(`Work.MotAS.asMinv_mul_asM`).
-/

namespace Work.MotV5.ASLocal

theorem aevalAsMAevalAsMinv {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (w : Work.MotV.Kb 𝕜)
    (p : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)) :
    MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j)
      (MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asMinv w i j) * MvPolynomial.X j) p) = p := by
  have h5 : (5 : Work.MotV.Kb 𝕜) = 0 := CharP.cast_eq_zero (Work.MotV.Kb 𝕜) 5
  have hcomp : (MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j)).comp
      (MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asMinv w i j) * MvPolynomial.X j))
      = AlgHom.id (Work.MotV.Kb 𝕜) (MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply, MvPolynomial.aeval_X]
    have hterm : ∀ x : Fin 5, MvPolynomial.C (Work.MotAS.asMinv w i x) *
        (∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asM w x j) * MvPolynomial.X j)
        = ∑ j : Fin 5,
            MvPolynomial.C (Work.MotAS.asMinv w i x * Work.MotAS.asM w x j) * MvPolynomial.X j := by
      intro x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← mul_assoc, ← map_mul]
    rw [show MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
          MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j)
        (∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asMinv w i j) * MvPolynomial.X j)
        = ∑ x : Fin 5, MvPolynomial.C (Work.MotAS.asMinv w i x) *
            (∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asM w x j) * MvPolynomial.X j) from ?_]
    · rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_comm]
      have hj : ∀ j : Fin 5, (∑ x : Fin 5,
            MvPolynomial.C (Work.MotAS.asMinv w i x * Work.MotAS.asM w x j) * MvPolynomial.X j)
          = MvPolynomial.C ((Work.MotAS.asMinv w * Work.MotAS.asM w) i j) * MvPolynomial.X j := by
        intro j
        rw [← Finset.sum_mul, ← map_sum, Matrix.mul_apply]
      rw [Finset.sum_congr rfl (fun j _ => hj j), Work.MotAS.asMinv_mul_asM h5 w]
      rw [Finset.sum_eq_single i]
      · rw [Matrix.one_apply_eq, map_one, one_mul]
      · intro j _ hjne
        rw [Matrix.one_apply_ne (Ne.symm hjne), map_zero, zero_mul]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  exact congrArg (fun f => f p) hcomp

end Work.MotV5.ASLocal
