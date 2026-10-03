import Mathlib
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.lyndonIndependence_of_relatorNorm_le_one
import Submission.Work.OROneRel.magnus_step_root

/-!
# The Cohen--Lyndon induction: reduction of `lyndon_independence_of_pow` to the Magnus-step input

**Superseded (2026-09-30).**  The reduction in this file uses the invariant `Work.ORLyndon.CLInv`
(full component-wise regularity of the root Fox vector), whose transport hypothesis turns out **not**
to be instantiable in the `σ_t = 0` case (the framing letter is not exempted).  The current reduction
is `Work.ORLyndon.lyndon_independence_of_pow_of_stepInput` in `Submission/Work/ORLyndon/CLAssembly`,
which uses the exempted-set invariant `Work.ORLyndon.CLInvariantWith`; see §22--§25 of
`NOTES_lyndon_independence_of_pow.md`.  The two lemmas of this file that the rest of the directory
still uses are `Work.ORLyndon.regular_of_isUnit` and `Work.ORLyndon.mem_relatorLetters_letterPow`.

`Work.ORLyndon.lyndon_independence_of_pow` (the module-form Cohen--Lyndon theorem, the single
classical input of the whole `ORLyndon` chapter) is proved here **from a single cross-node
hypothesis**, packaged below as the hypothesis `hStep` of
`Work.ORLyndon.lyndon_independence_of_pow_of_step`: the one-relator Magnus step as a *transport of
the inductive invariant*.

> for every root `u` of relator norm `≥ 2` which is not a proper power, and every `l ≥ 1`, there is a
> strictly shorter one-relator presentation (`r' = w ^ l`, `w` not a proper power,
> `relatorNorm w < relatorNorm u`) whose invariant implies the invariant at `u`.

The invariant, `Work.ORLyndon.CLInv`, is

* the order statement `orderOf (presentRho r u) = l` (Karrass--Magnus--Solitar, nodes N2/N4),
* triviality of the annihilator of the root Fox vector `(∂u/∂x)_x` in `K[⟨α | r⟩]^α` (Lyndon's
  identity theorem),
* componentwise right regularity of the root Fox vector at the letters of the root.

`CLInv ⟹ LyndonIndependence` is immediate from `Work.ORLyndon.lyndon_independence_of_rootVec_inj`
(the first two conjuncts), and the induction below reduces `CLInv` for all roots to the base case
`relatorNorm u ≤ 1` (proved here) and to the step hypothesis.

## Where the step input comes from (cross-node bookkeeping)

* **The `σ_t = 0` half is proved in this directory** — see
  `Work.ORLyndon.lyndon_independence_of_pow_eps_zero_mm` and `..._bot` (and the batched
  `..._extremal`), built on the connector `Work.ORLyndon.mmBaseHom_comp_mk`,
  `Work.ORLyndon.mmBaseHom_injective`, the chain rule
  `Work.ORLyndon.mapDomainRingHom_mmBaseHom_rootVec_eq`, the transport
  `Work.ORLyndon.mmBaseHom_transport` and the leading/trailing level transfers
  `Work.ORLyndon.ann_rootVec_of_level_decomp` / `..._bot`.  These give the Case-A instantiation of
  the step at the base `w = rootW t u l …`, `r' = mmW t (u^l)`, *provided* the base invariant supplies
  the regularity of the extremal component used; the residual cases (the component at the framing
  letter `t` itself, and the extremal decorated symbols whose exponent sum in the base vanishes) are
  documented in `NOTES_lyndon_independence_of_pow.md` §§13–17.
* **The Case-2 half (roots none of whose letters has vanishing exponent sum) is node N2's
  `ℤ`-domain/Bass--Serre construction**, `Submission/Work/OROneRel/` (currently the `sorry` of
  `magnus_step_root_no_eps_zero`).
* **The order statement** is `Work.OROneRel.kms_torsion_at` (nodes N2/N4).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

universe u v

namespace Work.ORLyndon

open MonoidAlgebra

/-- A unit is a right non-zero-divisor. -/
theorem regular_of_isUnit {R : Type*} [Ring R] {x : R} (h : IsUnit x) :
    ∀ c : R, c * x = 0 → c = 0 := by
  rintro c hc
  obtain ⟨u, rfl⟩ := h
  have h1 : (c * (u : R)) * (↑u⁻¹ : R) = 0 := by rw [hc, zero_mul]
  rwa [mul_assoc, Units.mul_inv, mul_one] at h1

/-- **Componentwise right regularity of the root Fox vector** in the one-relator presentation
`⟨α | r⟩`: multiplication by the component `(∂u/∂q)_q` at a letter `q` of the root is injective. -/
def CLComp {α : Type u} [DecidableEq α] (K : Type v) [Field K] (r u : FreeGroup α) : Prop :=
  ∀ q ∈ Work.OROneRel.relatorLetters u,
    ∀ c : MonoidAlgebra K (OneRelatorGroup r), c * rootVec K r u q = 0 → c = 0

/-- **The invariant of the Cohen--Lyndon induction.** -/
def CLInv {α : Type u} [DecidableEq α] (K : Type v) [Field K] (r u : FreeGroup α)
    (l : ℕ) : Prop :=
  orderOf (presentRho r u) = l ∧
    (∀ b : MonoidAlgebra K (OneRelatorGroup r), b • rootVec K r u = 0 → b = 0) ∧
    CLComp K r u

/-- Membership in the letters of a one-letter root. -/
theorem mem_relatorLetters_letterPow {α : Type*} [DecidableEq α] (a q : α) (s : Bool)
    (h : q ∈ Work.OROneRel.relatorLetters (Work.OROneRel.letterPow a s)) : q = a := by
  classical
  have h' : ∃ b : Bool, (q, b) ∈ FreeGroup.toWord (Work.OROneRel.letterPow a s) := h
  obtain ⟨b, hb⟩ := h'
  cases s
  · rw [Work.OROneRel.letterPow_false, FreeGroup.toWord_inv, FreeGroup.toWord_of] at hb
    simp [FreeGroup.invRev] at hb
    exact hb.1
  · rw [Work.OROneRel.letterPow_true, FreeGroup.toWord_of] at hb
    simp at hb
    exact hb.1

/-- **The base case of the induction**: `relatorNorm u ≤ 1`. -/
theorem CLInv_of_relatorNorm_le_one {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    {r u : FreeGroup α} {l : ℕ} (hl : 1 ≤ l) (hpow : r = u ^ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) (hn : Work.OROneRel.relatorNorm u ≤ 1) :
    CLInv K r u l := by
  rcases Work.OROneRel.eq_one_or_exists_letterPow_of_relatorNorm_le_one hn with h1 | ⟨a, s, hle⟩
  · exact absurd (h1.symm ▸ Work.OROneRel.isProperPower_one) hpp
  · subst hle
    subst hpow
    refine ⟨?_, ?_, ?_⟩
    · simpa using (Work.OROneRel.kmsRoot_of_letterPow a s l hl).1
    · intro b hb
      exact ann_rootVec_of_component _ _ a
        (regular_of_isUnit (isUnit_rootVec_letterPow _ a s)) b hb
    · intro q hq
      have hqa : q = a := mem_relatorLetters_letterPow a q s hq
      rw [hqa]
      exact regular_of_isUnit (isUnit_rootVec_letterPow _ a s)

/-- **The Cohen--Lyndon induction.**  Assuming the Magnus-step input, the invariant holds for every
root of relator norm `≤ n`. -/
theorem CLInv_of_step {K : Type v} [Field K]
    (hStep : ∀ {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ), 1 ≤ l →
      ¬ Work.OROneRel.IsProperPower u → 2 ≤ Work.OROneRel.relatorNorm u →
      ∃ (β : Type u) (w : FreeGroup β) (r' : FreeGroup β),
        ¬ Work.OROneRel.IsProperPower w ∧ r' = w ^ l ∧
          Work.OROneRel.relatorNorm w < Work.OROneRel.relatorNorm u ∧
          (@CLInv β (Classical.decEq β) K _ r' w l → CLInv K (u ^ l) u l)) :
    ∀ (n : ℕ) {α : Type u} [DecidableEq α] (r u : FreeGroup α) (l : ℕ),
      (hl : 1 ≤ l) → (hpow : r = u ^ l) → (hpp : ¬ Work.OROneRel.IsProperPower u) →
      Work.OROneRel.relatorNorm u ≤ n → CLInv K r u l := by
  intro n
  induction n with
  | zero =>
    intro α _ r u l hl hpow hpp hn
    exact CLInv_of_relatorNorm_le_one hl hpow hpp (by omega)
  | succ n ih =>
    intro α _ r u l hl hpow hpp hn
    classical
    by_cases h1 : Work.OROneRel.relatorNorm u ≤ 1
    · exact CLInv_of_relatorNorm_le_one hl hpow hpp h1
    · obtain ⟨β, w, r', hwpp, hr', hlt, hstep⟩ := hStep (u := u) l hl hpp (by omega)
      rw [hpow]
      exact hstep (ih r' w l hl hr' hwpp (by omega))

/-- **The Cohen--Lyndon theorem (module form), from the Magnus-step input.** -/
theorem lyndon_independence_of_pow_of_step {K : Type v} [Field K]
    (hStep : ∀ {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ), 1 ≤ l →
      ¬ Work.OROneRel.IsProperPower u → 2 ≤ Work.OROneRel.relatorNorm u →
      ∃ (β : Type u) (w : FreeGroup β) (r' : FreeGroup β),
        ¬ Work.OROneRel.IsProperPower w ∧ r' = w ^ l ∧
          Work.OROneRel.relatorNorm w < Work.OROneRel.relatorNorm u ∧
          (@CLInv β (Classical.decEq β) K _ r' w l → CLInv K (u ^ l) u l))
    {X : Type u} [DecidableEq X] (r u : FreeGroup X) (l : ℕ) (hl : 1 ≤ l) (hpow : r = u ^ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) : LyndonIndependence K r u := by
  classical
  obtain ⟨hord, hI, _⟩ :=
    CLInv_of_step hStep (Work.OROneRel.relatorNorm u) r u l hl hpow hpp le_rfl
  exact Work.ORLyndon.lyndon_independence_of_rootVec_inj r u l hl hpow hord hI

end Work.ORLyndon
