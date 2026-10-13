import Mathlib
import Submission.Work.WilG4c.Engine

open scoped Topology

namespace Work.WilG4c

/-- `Work.WilkG4c.iterDir L G z` is the iterated Fréchet derivative of `G` at `z` evaluated on
the list of direction vectors `Pi.single (L.get k) 1`.  Proved by induction on the list: the head
of `L` is the outermost derivative, so it is peeled off with
`DifferentiableAt.iteratedFDeriv_succ_apply_left'`/`iteratedFDeriv_succ_apply_left`, which requires
`iteratedFDeriv ℝ L'.length G` to be differentiable at `z` — supplied by `ContDiffAt`.

The smoothness hypothesis is needed only in the inductive step, where the induction hypothesis is
used on a whole neighbourhood of `z` (the direction list of the tail is shorter, and the tail
function agrees with an evaluated `iteratedFDeriv` near `z`; the `fderiv` of two functions that
agree near `z` coincide). -/
theorem iterDir_eq_iteratedFDeriv {m : ℕ} (L : List (Fin m)) (G : (Fin m → ℝ) → ℝ)
    (z : Fin m → ℝ) (hG : ContDiffAt ℝ L.length G z) :
    Work.WilkG4c.iterDir L G z =
      iteratedFDeriv ℝ L.length G z (fun k => Pi.single (L.get k) 1) := by
  revert G z
  induction L with
  | nil =>
    intro G z _
    simp [Work.WilkG4c.iterDir_nil, iteratedFDeriv_zero_apply]
  | cons i L' ih =>
    intro G z hG
    simp only [Work.WilkG4c.iterDir_cons]
    -- `G` is `C^{|L'|+1}` near `z`, hence `C^{|L'|}` near `z`: the induction hypothesis applies
    -- on a whole neighbourhood of `z`.
    have hev : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ (L'.length) G w := by
      have hne : ((L'.length + 1 : ℕ) : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
      have h1 := hG.eventually hne
      filter_upwards [show ∀ᶠ y in 𝓝 z, ContDiffAt ℝ (L'.length + 1) G y from by
        simpa using h1] with w hw
      exact hw.of_le (by exact_mod_cast Nat.le_succ L'.length :
        (L'.length : WithTop ℕ∞) ≤ ((L'.length + 1 : ℕ) : WithTop ℕ∞))
    have heq : Work.WilkG4c.iterDir L' G =ᶠ[𝓝 z]
        (fun w => iteratedFDeriv ℝ (L'.length) G w (fun k => Pi.single (L'.get k) 1)) := by
      filter_upwards [hev] with w hw
      exact ih G w hw
    rw [heq.fderiv_eq]
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ (L'.length) G) z :=
      hG.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self L'.length)
    rw [fderiv_continuousMultilinear_apply_const_apply (c := iteratedFDeriv ℝ (L'.length) G)
          hdiff (fun k => Pi.single (L'.get k) 1) (Pi.single i 1)]
    change (((fderiv ℝ (iteratedFDeriv ℝ L'.length G) z) (Pi.single i 1))
        (fun k => Pi.single (L'.get k) 1)) =
      (iteratedFDeriv ℝ (L'.length + 1) G z) (fun k => Pi.single ((i :: L').get k) 1)
    rw [iteratedFDeriv_succ_apply_left (f := G) (x := z) (n := L'.length)]
    rfl

end Work.WilG4c
