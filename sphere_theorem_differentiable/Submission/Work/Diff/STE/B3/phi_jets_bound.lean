import Mathlib
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv
import Submission.Work.Diff.STE.flat.compact_iteratedFDeriv_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-- **A global jet bound for a smooth function whose `tsupport` lies in a ball.**

Let `φ : (Fin n → ℝ) → ℝ` be `C^∞` with `tsupport φ ⊆ Metric.closedBall 0 R`.  Then the
`pdVec`-jets (`Work.Diff.STE.pdVec`) of its complexification are bounded on *all* of `Fin n → ℝ` up
to any fixed order `k`, by a constant independent of the order, the multi-index and the point.

ROUTE (both reviewers; there is a working scratch proof in
`Submission/Work/Diff/STE/B3/MyScratch/chk_api.lean`, lemma `phi_jets_bound`, that only fails in the
`z ∉ closedBall 0 R` branch).
* `ψ := fun y => ((φ y : ℝ) : ℂ)` is `C^∞` (`Complex.ofRealCLM.contDiff.comp hφsm`).
* For `z ∈ Metric.closedBall 0 R`, bound
  `‖pdVec m β ψ z‖ ≤ ‖iteratedFDeriv ℝ m ψ z‖` (`Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv`
  — add its import — plus `ContinuousMultilinearMap.le_opNorm`), and bound the latter uniformly by
  `Work.Diff.STE.flat.compact_iteratedFDeriv_bound ψ isOpen_univ hψ.contDiffOn
  (isCompact_closedBall 0 R) (Set.subset_univ _) k`.
* For `z ∉ Metric.closedBall 0 R` we have `z ∉ tsupport φ`, so `ψ` vanishes on a neighbourhood of
  `z`; hence `iteratedFDeriv ℝ m ψ z = 0`.  (The scratch proof's `𝓝[univ]`/`𝓝` mismatch is fixed by
  `Filter.EventuallyEq.iteratedFDerivWithin` on `Set.univ` together with
  `iteratedFDerivWithin_univ`, and the last goal `‖(0 : ContinuousMultilinearMap …) …‖ = 0` needs
  `ContinuousMultilinearMap.zero_apply` or `simp`.)
* `Mφ := C` (the bound of the second bullet) works, since `0 ≤ C`.

The real-valued analogue already exists as `jet_bound_of_tsupport`; do not import that module if it is
under construction. -/
theorem phi_jets_bound {n : ℕ} (φ : (Fin n → ℝ) → ℝ)
    (hφsm : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ)
    {R : ℝ} (hR : tsupport φ ⊆ Metric.closedBall 0 R) (k : ℕ) :
    ∃ Mφ : ℝ, 0 ≤ Mφ ∧ ∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin n) (z : Fin n → ℝ),
      ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((φ y : ℝ) : ℂ)) z‖ ≤ Mφ := by
  have hψ : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (fun y : Fin n → ℝ => ((φ y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hφsm
  obtain ⟨C, hCnn, hCb⟩ := Work.Diff.STE.flat.compact_iteratedFDeriv_bound
    (fun y : Fin n → ℝ => ((φ y : ℝ) : ℂ)) isOpen_univ hψ.contDiffOn
    (isCompact_closedBall (0 : Fin n → ℝ) R) (Set.subset_univ _) k
  refine ⟨C, hCnn, fun m hm β z => ?_⟩
  by_cases hz : z ∈ Metric.closedBall 0 R
  · have h1 : ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((φ y : ℝ) : ℂ)) z‖
        ≤ ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => ((φ y : ℝ) : ℂ)) z‖ := by
      rw [Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv m _ hψ z β]
      have h := ContinuousMultilinearMap.le_opNorm (𝕜 := ℝ)
        (f := iteratedFDeriv ℝ m (fun y : Fin n → ℝ => ((φ y : ℝ) : ℂ)) z)
        (m := fun j => Pi.single (β j) (1 : ℝ))
      simpa [Pi.norm_single] using h
    exact le_trans h1 (hCb z hz m hm)
  · have hz' : z ∉ tsupport φ := fun h => hz (hR h)
    have h2 : iteratedFDeriv ℝ m (fun y : Fin n → ℝ => ((φ y : ℝ) : ℂ)) z = 0 := by
      have hev : (fun y : Fin n → ℝ => ((φ y : ℝ) : ℂ))
          =ᶠ[nhdsWithin z Set.univ] fun _ => (0 : ℂ) := by
        rw [nhdsWithin_univ]
        filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hz'] with y hy
        simp only [Set.mem_compl_iff] at hy
        simp [image_eq_zero_of_notMem_tsupport (f := φ) hy]
      have h3 := hev.iteratedFDerivWithin (𝕜 := ℝ) m
      rw [iteratedFDerivWithin_univ, iteratedFDerivWithin_univ, nhdsWithin_univ] at h3
      rw [h3.eq_of_nhds]
      simp
    rw [Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv m _ hψ z β, h2]
    simpa using hCnn

end Work.Diff.STE.B3
