import Mathlib
import Submission.Work.OROneRel.NoZeroDefs
import Submission.Work.OROneRel.KMSDefs
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.eps_eq_toAdd_sigma
import Submission.Work.OROneRel.exists_cyclicallyReduced_conjugate
import Submission.Work.OROneRel.exists_two_mem_relatorLetters_ne
import Submission.Work.OROneRel.magnus_step_root_eps_zero_v2
import Submission.Work.OROneRel.kmsRoot_of_subst
import Submission.Work.OROneRel.kmsRoot_subst_image
import Submission.Work.OROneRel.kmsAux.Core.kmsCore

namespace Work.OROneRel

universe u

/-- **The exponent-sum-zero Magnus step, in the raw-HNN form of the toolbox.**  This is
`Work.OROneRel.magnus_step_root_eps_zero_v2` with the conclusion rewritten as
`Work.OROneRel.kmsAux.Core.MagData u l (relatorNorm u)`, i.e. the witness root is compared with
`relatorNorm u` — exactly the quantity the strong induction on the relator norm descends. -/
theorem kmsAux_magData_epsZero {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l) (t : α)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (ht : t ∈ Work.OROneRel.relatorLetters u)
    (he : Work.OROneRel.eps t u = 0) :
    Work.OROneRel.kmsAux.Core.MagData u l (Work.OROneRel.relatorNorm u) :=
  magnus_step_root_eps_zero_v2 u l hl t hu hcyc ht he

/-- **The inductive step of the root-tracked Karrass--Magnus--Solitar theorem.**  Assume the
statement for every root of relator norm strictly smaller than `relatorNorm u` (at the same exponent
`l`); then it holds for `u`, provided `u` is not a proper power.

The case analysis is the classical one:

* `relatorNorm u ≤ 1`: `u` is a single letter (or trivial, which is excluded by `¬ IsProperPower u`)
  — the base case `kmsRoot_of_relatorNorm_le_one`;
* `u` is not cyclically reduced: pass to the cyclically reduced conjugate `cyclicReduction u`, whose
  relator norm is strictly smaller, and transport back (`kmsAux.Core.kmsRoot_of_conj`);
* `u` cyclically reduced and some letter `t` of `u` has vanishing exponent sum: the
  Magnus--Moldavanskii step `magnus_step_root_eps_zero_v2` exhibits `⟨α | u ^ l⟩` as an HNN extension
  of a shorter one-relator group with the class of `u` conjugate to the class of the shorter root, so
  `kmsRoot_of_hnn` and the induction hypothesis give the result;
* `u` cyclically reduced and all exponent sums non-zero: pick two distinct letters `t ≠ x` of `u` and
  apply the Magnus/Putman substitution `ψ = subst t x (σ_x u) (σ_t u)`, which kills the exponent sum
  of `t` and has a Magnus rewriting strictly shorter than `u`.  The induction hypothesis applies to
  the substituted root (`kmsRoot_subst_image`), and the statement transports back along the (injective)
  map `⟨α | u ^ l⟩ →* ⟨α | (ψ u) ^ l⟩` (`kmsRoot_of_subst`). -/
theorem kmsRoot_step {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    (IH : ∀ {β : Type u} (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v →
      Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm u → Work.OROneRel.KMSRoot v l) :
    Work.OROneRel.KMSRoot u l := by
  by_cases hsmall : Work.OROneRel.relatorNorm u ≤ 1
  · exact Work.OROneRel.kmsRoot_of_relatorNorm_le_one l hl hu hsmall
  · have h2 : 2 ≤ Work.OROneRel.relatorNorm u := by omega
    by_cases hcyc : Work.OROneRel.IsCyclicallyReducedRelator u
    · by_cases hz : ∃ t ∈ Work.OROneRel.relatorLetters u, Work.OROneRel.eps t u = 0
      · -- the exponent-sum-zero Magnus step
        obtain ⟨t, ht, he⟩ := hz
        refine Work.OROneRel.kmsAux.Core.kmsRoot_of_magData
          (kmsAux_magData_epsZero u l hl t hu hcyc ht he) ?_
        intro β v hpp hlt
        exact IH v hpp hlt
      · -- all exponent sums are non-zero: substitute
        push Not at hz
        obtain ⟨x, hx, y, hy, hxy⟩ := Work.OROneRel.exists_two_mem_relatorLetters_ne u h2 hu
        refine Work.OROneRel.kmsRoot_of_subst u l hl hxy.symm hcyc hy (hz y hy) ?_
        exact Work.OROneRel.kmsRoot_subst_image u l hl hxy.symm hcyc hu hx hy (hz y hy)
          (fun v hpp hlt => IH v hpp hlt)
    · -- reduce cyclically
      have hlt : Work.OROneRel.relatorNorm (Work.OROneRel.cyclicReduction u)
          < Work.OROneRel.relatorNorm u := Work.OROneRel.kmsAux.Core.relatorNorm_cyclicReduction_lt hcyc
      refine Work.OROneRel.kmsAux.Core.kmsRoot_of_conj
        ⟨Work.OROneRel.cyclicConjugator u,
          Work.OROneRel.cyclicConjugator_mul_cyclicReduction_mul_inv u⟩ ?_
      exact IH (Work.OROneRel.cyclicReduction u)
        (Work.OROneRel.kmsAux.Core.not_isProperPower_cyclicReduction hu) hlt

/-- **Karrass--Magnus--Solitar for every root presentation, by strong induction on the relator
norm.**  For `u : FreeGroup α` which is not a proper power and `1 ≤ l`, the class of `u` in
`⟨α | u ^ l⟩` has order exactly `l`, and every element of finite order in `⟨α | u ^ l⟩` is conjugate
to a power of that class.  The bound `N` on the relator norm is the induction parameter. -/
theorem kmsRoot_all (N : ℕ) :
    ∀ {α : Type u} (u : FreeGroup α) (l : ℕ), 1 ≤ l → ¬ Work.OROneRel.IsProperPower u →
      Work.OROneRel.relatorNorm u ≤ N → Work.OROneRel.KMSRoot u l := by
  induction N with
  | zero =>
      intro α u l hl hu hN
      exact Work.OROneRel.kmsRoot_of_relatorNorm_le_one l hl hu (by omega)
  | succ N ih =>
      intro α u l hl hu hN
      rcases lt_or_eq_of_le hN with hLt | hEq
      · exact ih u l hl hu (Nat.lt_succ_iff.mp hLt)
      · exact kmsRoot_step u l hl hu (fun v hpp hlt => ih v l hl hpp (by omega))

end Work.OROneRel
