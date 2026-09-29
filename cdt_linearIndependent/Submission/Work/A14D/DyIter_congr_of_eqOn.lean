import Mathlib
import Submission.Work.A14.defs

namespace Work.A14D

theorem DyIter_congr_of_eqOn {S : Set ℂ} (hSo : IsOpen S) {f g : ℂ → ℂ}
    (h : ∀ w ∈ S, f w = g w) :
    ∀ k : ℕ, ∀ w ∈ S, Work.A14D.DyIter k f w = Work.A14D.DyIter k g w := by
  intro k
  induction k with
  | zero => intro w hw; simpa [DyIter] using h w hw
  | succ k ih =>
      intro w hw
      -- the two `k`-fold iterates agree on all of `S`, hence near `w` since `S` is open
      have heq : DyIter k f =ᶠ[nhds w] DyIter k g :=
        Filter.eventually_of_mem (hSo.mem_nhds hw) ih
      have hderiv : deriv (DyIter k f) w = deriv (DyIter k g) w := heq.deriv_eq
      have hdf : DyIter (k + 1) f = Dy (DyIter k f) := by
        simp only [DyIter]
        exact Function.iterate_succ_apply' Dy k f
      have hdg : DyIter (k + 1) g = Dy (DyIter k g) := by
        simp only [DyIter]
        exact Function.iterate_succ_apply' Dy k g
      rw [hdf, hdg]
      simp only [Dy, hderiv]

end Work.A14D
