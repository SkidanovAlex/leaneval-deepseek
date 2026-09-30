import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.Free.large_sieve_poly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- The polynomial large sieve, ported into a module that can be imported together with
`Submission.Work.BMF.SD.tk_short`.

The statement is *verbatim* the statement of `Work.BMF.large_sieve_poly`
(`Submission/Work/BMF/large_sieve_poly.lean`, proved), and indeed the fastest way to *think* about
it is to copy that proof.  But the deliverable is different from a restatement: this declaration
must be importable in the presence of `Submission.Work.BMF.SD.tk_short`, and today it is not, for a
purely syntactic reason.  The import closure of `Submission.Work.BMF.large_sieve_poly` contains
`Submission.Work.BMF.SD.weyl_inverse` and `Submission.Work.BMF.SD.a_one_bound`, which declare
`Work.BMF.SD.eC_add'`, `Work.BMF.SD.norm_eC'`, `Work.BMF.SD.eC_mul_nat` (weyl_inverse) and
`Work.BMF.SD.norm_eC`, `Work.BMF.SD.eC_int` (a_one_bound); four of these are also declared by the
closure of `Submission.Work.BMF.SD.tk_short` (`SD/tk_short.lean`, `MSD/dirichlet_kernel.lean`)
with *different* argument orders, so Lean rejects the second import at load time with
`environment already contains ...` (verified: a file importing both `SD/tk_short` and
`SD/weyl_inverse` fails to elaborate).

So the task is a port, not a new proof: reproduce `Work.BMF.large_sieve_poly` as
`Work.BMF.SD.large_sieve_poly_free` in the import-light world of
`Submission.Work.BMF.SD.tk_short`.  The mechanism used here (nothing existing may be edited) is
to copy the modules of `large_sieve_poly`'s closure that are *downstream of* the conflicting
declarations into new files under `Submission/Work/BMF/Free/`, placing them in *fresh namespaces*
so that the conflicting declarations (`Work.BMF.SD.eC_add'`, `Work.BMF.SD.norm_eC'`,
`Work.BMF.SD.eC_mul_nat`, `Work.BMF.SD.eC_int`, `Work.BMF.SD.norm_eC`, ...) receive fresh fully
qualified names (`Work.BMF.SD.FreeA.eC_int`, `Work.BMF.SD.FreeW.eC_add'`, ...), and adjusting the
`import` lines of the copies; every other name is left untouched, and the modules of the closure
that declare no conflicting name (e.g. `descent_coeff`, `beta_pinning`, `abel_geom_bound`,
`pin_lemma`, ...) are imported from the originals unchanged.  The proof itself is the copied proof
of `Work.BMF.large_sieve_poly` (now `Work.BMF.FreeLS.large_sieve_polyF`).

Consequences: this file imports nothing that (transitively) brings in the *original*
`weyl_inverse`/`weyl_structure`/`large_sieve_poly` names. -/
theorem large_sieve_poly_free (k : ℕ) (η' C₀ : ℝ) (hη' : 0 < η') (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, C₀ ≤ C ∧ ∃ K : ℕ, ∀ (N : ℕ) (f : ℕ → ℂ) (x₀ H : ℝ) (xs Ls : Fin N → ℝ)
      (Ps : Fin N → Polynomial ℝ),
      (∀ n, ‖f n‖ ≤ 1) → 1 ≤ H →
      (∀ i, 1 ≤ xs i) →
      (∀ i, Ls i ≤ C₀ * H ∧ H ≤ C₀ * Ls i ∧ |xs i - x₀| ≤ C₀ * H) →
      (∀ i, Ps i ∈ Polynomial.degreeLE ℝ (k : WithBot ℕ)) →
      (∀ i, η' * Ls i ≤ ‖Work.BMF.corr f (Ps i) (xs i) (Ls i)‖) →
      K ≤ N → ∃ i j : Fin N, i ≠ j ∧ Work.BMF.PolyRel k C 1 (xs i) (Ls i) (Ps i) (xs j) (Ls j) (Ps j) :=
  Work.BMF.FreeLS.large_sieve_polyF k η' C₀ hη' hC₀

end Work.BMF.SD
