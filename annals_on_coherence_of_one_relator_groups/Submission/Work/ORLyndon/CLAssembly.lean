import Mathlib
import Submission.Work.ORLyndon.CLStepA
import Submission.Work.ORLyndon.isCyclicallyReducedRelator_rootW
import Submission.Work.ORLyndon.lyndonIndependence_conj

/-!
# The Cohen--Lyndon induction, and the reduction of `lyndon_independence_of_pow` to the Magnus steps

`Work.ORLyndon.lyndon_independence_of_pow` (the module form of Lyndon's identity theorem / the
Cohen--Lyndon theorem) is reduced here to a *single* named input about the one-relator Magnus step,
split into its two cases.

## The induction

The induction is a strong induction on `relatorNorm u`, over all types of generators, proving
`Work.ORLyndon.CLInvariant K (u ^ l) u l` for roots `u` which are cyclically reduced and not proper
powers:

* `relatorNorm u ≤ 1` -- `Work.ORLyndon.CLInvariant_of_relatorNorm_le_one`;
* some letter `t` of `u` has exponent sum zero -- the exponent-sum-zero Magnus step, whose base is the
  decorated root `Work.OROneRel.rootW t u l hcyc he hl` (strictly shorter by
  `Work.OROneRel.relatorNorm_rootW_lt`, again not a proper power, and again cyclically reduced by
  `Work.ORLyndon.isCyclicallyReducedRelator_rootW`); this is `Work.ORLyndon.CaseAInput`;
* all letters of `u` have non-zero exponent sum -- node N2's Case-2 Magnus step, `Case2Input`.

`Work.ORLyndon.lyndon_independence_of_pow_of_step` then derives
`Work.ORLyndon.LyndonIndependence K r u` for an *arbitrary* root `u`: any root is first replaced by
its cyclic reduction (`Work.OROneRel.cyclicReduction`), where the induction applies, and
`Work.ORLyndon.lyndonIndependence_conj` transports the statement back.

## The two inputs

`Work.ORLyndon.CaseAInput K` and `Work.ORLyndon.Case2Input K` are stated at the level of the
invariant `Work.ORLyndon.CLInvariantWith` *with its exempted set exposed*: the producer must handle
an arbitrary exempted set `Tv` of the shorter root (satisfying the cardinality bound), and must
produce an exempted set `Tu` for the longer one together with the invariant.  This is exactly the
shape which makes the strong induction go through, and it is also the shape in which the
exponent-sum-zero transport is proved in `Submission/Work/ORLyndon/CLStepA.lean`.

## The remaining gap

The exponent-sum-zero branch is *proved* in this directory for the exempted sets produced by the
induction, **modulo one combinatorial condition**: `Work.ORLyndon.UnblockedInput` -- the exempted set
of the Magnus base leaves at least one *unblocked* letter, i.e. a letter `x ≠ t` of `u` whose top
decorated symbol is not exempted.  Given that, `Work.ORLyndon.CaseAInput` holds
(`Work.ORLyndon.caseAInput_of_unblocked`), and hence so does the whole reduction
(`Work.ORLyndon.stepInput_of_unblocked`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

universe u v

namespace Work.ORLyndon

open MonoidAlgebra

/-- **The exponent-sum-zero branch of the induction step.**  For every cyclically reduced root `u`
which is not a proper power, of relator norm `≥ 2`, with a letter `t` of exponent sum zero: if the
invariant holds at the Magnus base `⟨mmBeta t (u^l) | mmW t (u^l)⟩` with root
`rootW t u l hcyc he hl`, then it holds at `u`.

The hypothesis is stated at the level of the *existence* of an exempted set of the base -- which is
exactly what the strong induction supplies -- and not, as in a first attempt, for *every* bounded
exempted set: the latter is not provable (an exempted set of the base can block every letter of `u`;
see `Work.ORLyndon.UnblockedBase` and §24 of the notes).  The transport is proved for any exempted set
of the base (`Work.ORLyndon.CLInvariantWith_of_epsZero`); what this *branch* adds is the existence of
a base witness for which the transfer goes through. -/
def CaseAInput (K : Type v) [Field K] : Prop :=
  ∀ {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (t : α) (ht : t ∈ Work.OROneRel.relatorLetters u) (he : Work.OROneRel.eps t u = 0),
    (∃ Tv : Set (Work.OROneRel.mmBeta t (u ^ l)),
        Tv.Finite ∧
        Tv.ncard ≤ Work.OROneRel.relatorNorm (Work.OROneRel.rootW t u l hcyc he hl) ∧
        (@CLInvariantWith (Work.OROneRel.mmBeta t (u ^ l))
            (Work.OROneRel.mmBetaDecidableEq t (u ^ l)) K _
            (Work.OROneRel.mmW t (u ^ l)) (Work.OROneRel.rootW t u l hcyc he hl) l Tv)) →
      ∃ Tu : Set α, Tu.Finite ∧ Tu.ncard ≤ Work.OROneRel.relatorNorm u ∧
        CLInvariantWith K (u ^ l) u l Tu

/-- **The Case-2 branch of the induction step** (node N2's Magnus step).  For every cyclically
reduced root `u` which is not a proper power, of relator norm `≥ 2`, none of whose letters has
vanishing exponent sum, there is a strictly shorter cyclically reduced one-relator presentation
(`r' = w ^ l` with `w` cyclically reduced and not a proper power, `relatorNorm w < relatorNorm u`)
which transports the invariant with *any* exempted set `Tv`. -/
def Case2Input (K : Type v) [Field K] : Prop :=
  ∀ {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (hbad : ∀ x ∈ Work.OROneRel.relatorLetters u, Work.OROneRel.eps x u ≠ 0),
    ∃ (β : Type u) (w r' : FreeGroup β),
      ¬ Work.OROneRel.IsProperPower w ∧ r' = w ^ l ∧
        Work.OROneRel.IsCyclicallyReducedRelator w ∧
        Work.OROneRel.relatorNorm w < Work.OROneRel.relatorNorm u ∧
        ∀ (Tv : Set β), Tv.Finite → Tv.ncard ≤ Work.OROneRel.relatorNorm w →
          (@CLInvariantWith β (Classical.decEq β) K _ r' w l Tv →
            ∃ Tu : Set α, Tu.Finite ∧ Tu.ncard ≤ Work.OROneRel.relatorNorm u ∧
              CLInvariantWith K (u ^ l) u l Tu)

/-- **The step input of the Cohen--Lyndon induction**: the two Magnus steps, in the invariant
transport form. -/
def StepInput (K : Type v) [Field K] : Prop := CaseAInput.{u, v} K ∧ Case2Input.{u, v} K

/-- **The strong induction on `relatorNorm` proving the invariant.**  Assuming the step input, the
invariant holds for every cyclically reduced root which is not a proper power. -/
theorem CLInvariant_of_step {K : Type v} [Field K] (h : StepInput.{u, v} (K := K)) :
    ∀ (n : ℕ) {α : Type u} [DecidableEq α] (r u : FreeGroup α) (l : ℕ),
      (hl : 1 ≤ l) → (hpow : r = u ^ l) → (hpp : ¬ Work.OROneRel.IsProperPower u) →
      (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u) → Work.OROneRel.relatorNorm u ≤ n →
      CLInvariant K r u l := by
  intro n
  induction n with
  | zero =>
      intro α _ r u l hl hpow hpp hcyc hn
      exact CLInvariant_of_relatorNorm_le_one hl hpow hpp (by omega)
  | succ n ih =>
      intro α _ r u l hl hpow hpp hcyc hn
      classical
      by_cases h1 : Work.OROneRel.relatorNorm u ≤ 1
      · exact CLInvariant_of_relatorNorm_le_one hl hpow hpp h1
      · by_cases hA : ∃ t, t ∈ Work.OROneRel.relatorLetters u ∧ Work.OROneRel.eps t u = 0
        · obtain ⟨t, ht, he⟩ := hA
          rw [hpow]
          have hwpp : ¬ Work.OROneRel.IsProperPower (Work.OROneRel.rootW t u l hcyc he hl) :=
            Work.OROneRel.not_isProperPower_rootW t u l hpp hcyc he hl
          have hwcyc : Work.OROneRel.IsCyclicallyReducedRelator
              (Work.OROneRel.rootW t u l hcyc he hl) :=
            isCyclicallyReducedRelator_rootW t u l hcyc he hl
          have hwpow : Work.OROneRel.mmW t (u ^ l) =
              (Work.OROneRel.rootW t u l hcyc he hl) ^ l :=
            (Work.OROneRel.rootW_pow t u l hcyc he hl).symm
          have hwlt : Work.OROneRel.relatorNorm (Work.OROneRel.rootW t u l hcyc he hl) <
              Work.OROneRel.relatorNorm u :=
            Work.OROneRel.relatorNorm_rootW_lt t u l hcyc he hl ht
          have hwn : Work.OROneRel.relatorNorm (Work.OROneRel.rootW t u l hcyc he hl) ≤ n := by
            omega
          obtain ⟨Tv, hTvfin, hTvcard, hTvIH⟩ :=
            ih (Work.OROneRel.mmW t (u ^ l)) (Work.OROneRel.rootW t u l hcyc he hl) l hl hwpow
              hwpp hwcyc hwn
          exact h.1 u l hl hpp hcyc (by omega) t ht he ⟨Tv, hTvfin, hTvcard, hTvIH⟩
        · push_neg at hA
          rw [hpow]
          obtain ⟨β, w, r', hpp', hr', hcyc', hlt', htrans⟩ :=
            h.2 u l hl hpp hcyc (by omega) (fun x hx => hA x hx)
          have hwn : Work.OROneRel.relatorNorm w ≤ n := by omega
          obtain ⟨Tv, hTvfin, hTvcard, hTvIH⟩ := ih r' w l hl hr' hpp' hcyc' hwn
          exact htrans Tv hTvfin hTvcard hTvIH

/-- **The Cohen--Lyndon theorem (module form), from the step input.**  Any root `u` is replaced by
its cyclic reduction, where the induction `Work.ORLyndon.CLInvariant_of_step` applies and gives the
invariant; the invariant yields `Work.ORLyndon.LyndonIndependence` for the cyclically reduced pair
(`Work.ORLyndon.lyndon_independence_of_rootVec_inj`), which
`Work.ORLyndon.lyndonIndependence_conj` transports back to `(r, u)`. -/
theorem lyndon_independence_of_pow_of_stepInput {K : Type v} [Field K]
    (h : StepInput.{u, v} (K := K))
    {X : Type u} [DecidableEq X] (r u : FreeGroup X) (l : ℕ) (hl : 1 ≤ l) (hpow : r = u ^ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) : LyndonIndependence K r u := by
  classical
  set s : FreeGroup X := Work.OROneRel.cyclicReduction u with hs
  set c : FreeGroup X := Work.OROneRel.cyclicConjugator u with hc
  have hcs : c * s * c⁻¹ = u := Work.OROneRel.cyclicConjugator_mul_cyclicReduction_mul_inv u
  have hconj : c * s ^ l * c⁻¹ = (c * s * c⁻¹) ^ l := by
    rw [← MulAut.conj_apply c (s ^ l), map_pow, MulAut.conj_apply c s]
  have hspow : (c * s * c⁻¹) ^ l = r := by rw [hcs, hpow]
  have hspp : ¬ Work.OROneRel.IsProperPower s := by
    rw [hs]; exact Work.OROneRel.not_isProperPower_cyclicReduction hpp
  have hscyc : Work.OROneRel.IsCyclicallyReducedRelator s := by
    rw [hs]; exact Work.OROneRel.isCyclicallyReducedRelator_cyclicReduction u
  obtain ⟨T, hTfin, hTcard, hord, hI, -⟩ :=
    CLInvariant_of_step (K := K) h (Work.OROneRel.relatorNorm s) (s ^ l) s l hl rfl hspp hscyc
      le_rfl
  have hLI : LyndonIndependence K (s ^ l) s :=
    lyndon_independence_of_rootVec_inj (s ^ l) s l hl rfl hord hI
  have hconjLI := lyndonIndependence_conj (s ^ l) s c hLI
  rw [hpow]
  simpa only [hconj, hcs] using hconjLI

/-- **The unblocked-letter input.**  The exempted set `Tv` of the Magnus base never blocks *all* the
letters of `u`: for some letter `x ≠ t` of `u`, the top decorated symbol of `x` is not in `Tv`.

**Sufficient, possibly stronger than needed.**  This quantifies over *every* bounded exempted set `Tv`
of the base carrying the invariant, whereas the induction only ever feeds the exempted sets that its
own branches produce (the empty set at the base case, `insert t (symLetter '' T)` at the steps).  A
"bad" exempted set can block every letter of `u`, so `UnblockedInput` may well be stronger than the
`Work.ORLyndon.CaseAInput` it is used to prove; it is stated here because it is the form in which the
transfer is applied.  What *is* unconditional is the case `Tv = ∅`
(`Work.ORLyndon.CLInvariant_of_epsZero_empty`), i.e. the first Magnus step of every chain. -/
def UnblockedInput (K : Type v) [Field K] : Prop :=
  ∀ {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (t : α) (ht : t ∈ Work.OROneRel.relatorLetters u) (he : Work.OROneRel.eps t u = 0)
    (Tv : Set (Work.OROneRel.mmBeta t (u ^ l))),
    Tv.Finite →
    Tv.ncard ≤ Work.OROneRel.relatorNorm (Work.OROneRel.rootW t u l hcyc he hl) →
    (@CLInvariantWith (Work.OROneRel.mmBeta t (u ^ l))
        (Work.OROneRel.mmBetaDecidableEq t (u ^ l)) K _
        (Work.OROneRel.mmW t (u ^ l)) (Work.OROneRel.rootW t u l hcyc he hl) l Tv →
      ∃ (x : α) (hxt : x ≠ t), x ∈ Work.OROneRel.relatorLetters u ∧
        mmTopSym t u l x hxt ∉ Tv)

/-- **The exponent-sum-zero branch of the induction, from the unblocked-letter input.**  This is the
formal content of the `σ_t = 0` half of Cohen--Lyndon: the transport of
`Work.ORLyndon.CLInvariantWith_of_epsZero`, with the cardinality bound
(`Work.ORLyndon.ncard_insert_symLetter_image_le`) and the unblocked-letter condition discharged by
`Work.ORLyndon.UnblockedInput`. -/
theorem caseAInput_of_unblocked {K : Type v} [Field K] (hU : UnblockedInput.{u, v} (K := K)) :
    CaseAInput.{u, v} (K := K) := by
  intro α _ u l hl hpp hcyc hn t ht he ⟨Tv, hTvfin, hTvcard, hTvIH⟩
  have hcard : (insert t (symLetter '' Tv)).ncard ≤ Work.OROneRel.relatorNorm u := by
    have h1 := ncard_insert_symLetter_image_le Tv hTvfin t
    have h2 := Work.OROneRel.relatorNorm_rootW_lt t u l hcyc he hl ht
    omega
  exact ⟨insert t (symLetter '' Tv), (hTvfin.image symLetter).insert t, hcard,
    CLInvariantWith_of_epsZero t u l hl hpp hcyc hn ht he hTvIH
      (hU u l hl hpp hcyc hn t ht he Tv hTvfin hTvcard hTvIH)⟩

/-- **The step input, from the unblocked-letter input and node N2's Case-2 Magnus step.** -/
theorem stepInput_of_unblocked {K : Type v} [Field K] (hU : UnblockedInput.{u, v} (K := K))
    (h2 : Case2Input.{u, v} (K := K)) : StepInput.{u, v} (K := K) :=
  ⟨caseAInput_of_unblocked hU, h2⟩

end Work.ORLyndon
