import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Vero.lamR_witness

namespace Work.HP.HP3


/-- The two sets whose `sInf` define `lam Λ i` and `lamR (realify Λ) i` are literally the same
set: push a `ℤ`-independent family of integer vectors of `Λ` forward along `intCastPi` (this is
`ℝ`-independent by base change along the faithful `ℤ → ℝ`, and preserves the Euclidean norm), and
conversely pull a `ℝ`-independent family of vectors of `realify Λ` back to `Λ` (each vector of
`realify Λ` is the realification of an integer vector of `Λ`). -/
lemma lamSet_eq {ι : Type*} [Fintype ι] (Λ : Submodule ℤ (ι → ℤ)) (i : ℕ) :
    {r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (ι → ℤ),
        (∀ j, f j ∈ Λ) ∧ LinearIndependent ℤ f ∧ ∀ j, eNorm (f j) ≤ r}
      = {r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (ι → ℝ),
        (∀ j, f j ∈ realify Λ) ∧ LinearIndependent ℝ f ∧ ∀ j, rNorm (f j) ≤ r} := by
  refine Set.Subset.antisymm ?_ (Work.HP.Vero.realify_subset_lamSet Λ i)
  rintro r ⟨hr0, f, hfL, hfI, hfr⟩
  refine ⟨hr0, fun j => intCastPi (f j), fun j => Submodule.mem_map_of_mem (hfL j), ?_, ?_⟩
  · have heq : (fun j => intCastPi (f j)) = (fun j => ⇑(algebraMap ℤ ℝ) ∘ f j) := by
      funext j k
      simp [intCastPi]
    rw [heq]
    exact linearIndependent_algebraMap_comp_iff.mpr hfI
  · intro j
    rw [← Work.HP.Vero.eNorm_eq_rNorm_intCastPi]
    exact hfr j

/-- The successive minima of an integral lattice computed with `eNorm` on `ℤ^ι` agree with those
computed with `rNorm` on its realification.  The two defining `sInf` sets are literally the same
set of radii (push a family forward along the injective `intCastPi`; `eNorm v = rNorm (toR v)`;
`ℤ`-independence of integer vectors is equivalent to `ℝ`-independence). -/
theorem lam_eq_lamR {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℤ) (r : ℕ) :
    lam (latOrth c) r = lamR (realify (latOrth c)) r := by
  rw [lam, lamR]
  exact congrArg sInf (lamSet_eq (latOrth c) r)

end Work.HP.HP3
