import Mathlib
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero_mm
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero_mm_bot
import Submission.Work.ORLyndon.lyndonIndependence_of_pow_of_step

/-!
# The induction invariant of the Cohen--Lyndon theorem, with an exempted set of letters

The strong induction on the relator norm that proves `Work.ORLyndon.LyndonIndependence` cannot use
component-wise regularity of the root Fox vector at *every* letter: the exponent-sum-zero Magnus step
(`Work.ORLyndon.lyndon_independence_of_pow_eps_zero_mm`) transfers regularity only for the letters
`q ≠ t` of the root, where `t` is the framing letter of the step (the decorated alphabet of the
Magnus base omits `t`, so the component `(∂u/∂t)_t` has no base-side counterimage), and a letter can
also be blocked by the *base's* exempted symbols.

The invariant therefore records a set `T` of exempted letters:

* `Work.ORLyndon.CLRegOff K r u l T` -- right regularity of the root Fox vector at every letter of
  the root outside `T`;
* `Work.ORLyndon.CLInvariantWith K r u l T` -- the invariant `(O) ∧ (I) ∧ CLRegOff T`, where `(O)` is
  the Karrass--Magnus--Solitar order statement and `(I)` the triviality of the annihilator of the root
  Fox vector;
* `Work.ORLyndon.CLInvariant K r u l` -- `∃ T`, contained in the letters of the root, of cardinality
  at most the relator norm (the bound preserved by the Magnus step, see
  `Work.ORLyndon.CLInvariantWith_of_epsZero`), satisfying the invariant.

This file also contains the *per-letter* form of the exponent-sum-zero step, which is what the
induction consumes: the assembled step `Work.ORLyndon.lyndon_independence_of_pow_eps_zero_mm`
concludes `LyndonIndependence`, whereas the induction needs the component-wise statement at the
chosen letter, together with the fact that the base's exempted symbols can be avoided
(`Work.ORLyndon.mmTopSym_notMem`).

## Main definitions

* `Work.ORLyndon.symLetter`, `Work.ORLyndon.CLRegOff`, `Work.ORLyndon.CLInvariantWith`,
  `Work.ORLyndon.CLInvariant`.

## Main results

* `Work.ORLyndon.mmTopSym_notMem` -- the top decorated symbol of a letter `x` of `u` is not exempted
  at the Magnus base as soon as no exempted base symbol has underlying letter `x`;
* `Work.ORLyndon.regular_rootVec_epsZero_top`, `Work.ORLyndon.regular_rootVec_epsZero_bot` -- the
  per-letter form of the `σ_t = 0` step at the top resp. bottom decorated symbol of the base.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ORLyndon

open MonoidAlgebra

universe u v

/-- The underlying generator of a decorated symbol (an element of the occurring decorated alphabet
`mmBeta t r`, which is a subtype of `{a // a ≠ t} × ℤ`). -/
def symLetter {α : Type u} {t : α} {r : FreeGroup α}
    (q : Work.OROneRel.mmBeta t r) : α :=
  ((q : Work.OROneRel.MMAlpha t).1 : {a : α // a ≠ t}).1

/-- The underlying generator of the top decorated symbol of `x` is `x`. -/
theorem symLetter_mmTopSym {α : Type u} [DecidableEq α] (t : α) (u : FreeGroup α) (l : ℕ)
    (x : α) (hxt : x ≠ t) : symLetter (mmTopSym t u l x hxt) = x := rfl

/-- The underlying generator of the bottom decorated symbol of `x` is `x`. -/
theorem symLetter_mmBotSym {α : Type u} [DecidableEq α] (t : α) (u : FreeGroup α) (l : ℕ)
    (x : α) (hxt : x ≠ t) : symLetter (mmBotSym t u l x hxt) = x := rfl

/-- **The base's exempted symbols can be avoided at a letter `x`.**  If no exempted symbol of the
base root has underlying letter `x`, then the top decorated symbol of `x` is not exempted. -/
theorem mmTopSym_notMem {α : Type u} [DecidableEq α] (t : α) (u : FreeGroup α) (l : ℕ)
    (x : α) (hxt : x ≠ t) {Tv : Set (Work.OROneRel.mmBeta t (u ^ l))}
    (h : ∀ s ∈ Tv, symLetter s ≠ x) : mmTopSym t u l x hxt ∉ Tv := by
  intro hmem
  exact h _ hmem (symLetter_mmTopSym t u l x hxt)

/-- **The base's exempted symbols can be avoided at a letter `x`** (bottom form). -/
theorem mmBotSym_notMem {α : Type u} [DecidableEq α] (t : α) (u : FreeGroup α) (l : ℕ)
    (x : α) (hxt : x ≠ t) {Tv : Set (Work.OROneRel.mmBeta t (u ^ l))}
    (h : ∀ s ∈ Tv, symLetter s ≠ x) : mmBotSym t u l x hxt ∉ Tv := by
  intro hmem
  exact h _ hmem (symLetter_mmBotSym t u l x hxt)

/-- **Right regularity of the root Fox vector at every letter of the root outside `T`.** -/
def CLRegOff {α : Type u} [DecidableEq α] (K : Type v) [Field K] (r u : FreeGroup α) (l : ℕ)
    (T : Set α) : Prop :=
  ∀ q ∈ Work.OROneRel.relatorLetters u, q ∉ T →
    ∀ c : MonoidAlgebra K (OneRelatorGroup r), c * rootVec K r u q = 0 → c = 0

/-- **The invariant of the Cohen--Lyndon induction**, relative to a prescribed set `T` of exempted
letters: `(O) ∧ (I) ∧ CLRegOff T`. -/
def CLInvariantWith {α : Type u} [DecidableEq α] (K : Type v) [Field K] (r u : FreeGroup α)
    (l : ℕ) (T : Set α) : Prop :=
  orderOf (presentRho r u) = l ∧
    (∀ b : MonoidAlgebra K (OneRelatorGroup r), b • rootVec K r u = 0 → b = 0) ∧
    CLRegOff K r u l T

/-- **The invariant of the Cohen--Lyndon induction.**  The exempted set is existentially quantified
and has at most `relatorNorm u` elements -- the bound that the Magnus step preserves (one exempted
symbol of the base contributes at most one exempted letter, and the framing letter contributes one
more, see `Work.ORLyndon.CLInvariantWith_of_epsZero`). -/
def CLInvariant {α : Type u} [DecidableEq α] (K : Type v) [Field K] (r u : FreeGroup α)
    (l : ℕ) : Prop :=
  ∃ T : Set α, T.Finite ∧ T.ncard ≤ Work.OROneRel.relatorNorm u ∧ CLInvariantWith K r u l T

/-- **The per-letter exponent-sum-zero Magnus step, top decorated symbol.**  This is the body of
`Work.ORLyndon.lyndon_independence_of_pow_eps_zero_mm`, stopped at the component-wise statement: if
the base induction hypothesis supplies right regularity of the base root's Fox vector at the *top*
decorated symbol `mmTopSym t u l x hxt` of a letter `x ≠ t` of `u`, then the `x`-component of the
root Fox vector of `u` is right regular. -/
theorem regular_rootVec_epsZero_top {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    (t : α) (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (ht : t ∈ Work.OROneRel.relatorLetters u) (he : Work.OROneRel.eps t u = 0)
    (x : α) (hxt : x ≠ t) (hx : x ∈ Work.OROneRel.relatorLetters u)
    (hIH : ∀ c : MonoidAlgebra K (Work.OROneRel.mmH t (u ^ l)),
      c * rootVec K (Work.OROneRel.mmW t (u ^ l))
        (Work.OROneRel.rootW t u l hcyc he hl) (mmTopSym t u l x hxt) = 0 → c = 0) :
    ∀ b : MonoidAlgebra K (OneRelatorGroup (u ^ l)), b * rootVec K (u ^ l) u x = 0 → b = 0 := by
  classical
  have hσ : Work.OROneRel.sigma t u = 1 :=
    (Work.OROneRel.eps_eq_zero_iff_sigma_eq_one t u).mp he
  have hm : Function.Injective (Work.OROneRel.mmBaseHom (t := t) (r := u ^ l)
      (Work.ORLyndon.mmEpsPow t u l he)) :=
    mmBaseHom_injective t u l hl hpp hcyc ht he
  have hdec : ∀ j : ℤ, Work.OROneRel.mmHi t (u ^ l) ⟨x, hxt⟩ < j →
      foxD (K := K) (X := MagnusBeta t) ((⟨x, hxt⟩ : {a : α // a ≠ t}), j)
        (Work.OROneRel.magRewRel t u) = 0 := by
    intro j hj
    refine foxD_eq_zero_of_notMem_relatorLetters (K := K) _ _ fun hmemj => ?_
    have hle := (mmHi_mem_relatorLetters t u ⟨x, hxt⟩ hx).2 j hmemj
    rw [Work.OROneRel.mmHi_pow t u hcyc he l hl ⟨x, hxt⟩] at hj
    omega
  have hbase := hbase_of_ih_mm (K := K) t u l hcyc he hl (mmTopSym t u l x hxt) hm hIH
  exact fun b hb => ann_rootVec_of_magnusRewriting (K := K) t x hxt (u ^ l) u l rfl hσ
    (Work.OROneRel.mmHi t (u ^ l) ⟨x, hxt⟩) hdec (fun c _ hcE => hbase c hcE) b hb

/-- **The per-letter exponent-sum-zero Magnus step, bottom decorated symbol.**  The companion of
`Work.ORLyndon.regular_rootVec_epsZero_top`, using the mirrored transfer
`Work.ORLyndon.ann_rootVec_of_magnusRewriting_bot` at the *bottom* decorated symbol. -/
theorem regular_rootVec_epsZero_bot {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    (t : α) (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (ht : t ∈ Work.OROneRel.relatorLetters u) (he : Work.OROneRel.eps t u = 0)
    (x : α) (hxt : x ≠ t) (hx : x ∈ Work.OROneRel.relatorLetters u)
    (hIH : ∀ c : MonoidAlgebra K (Work.OROneRel.mmH t (u ^ l)),
      c * rootVec K (Work.OROneRel.mmW t (u ^ l))
        (Work.OROneRel.rootW t u l hcyc he hl) (mmBotSym t u l x hxt) = 0 → c = 0) :
    ∀ b : MonoidAlgebra K (OneRelatorGroup (u ^ l)), b * rootVec K (u ^ l) u x = 0 → b = 0 := by
  classical
  have hσ : Work.OROneRel.sigma t u = 1 :=
    (Work.OROneRel.eps_eq_zero_iff_sigma_eq_one t u).mp he
  have hm : Function.Injective (Work.OROneRel.mmBaseHom (t := t) (r := u ^ l)
      (Work.ORLyndon.mmEpsPow t u l he)) :=
    mmBaseHom_injective t u l hl hpp hcyc ht he
  have hdec : ∀ j : ℤ, j < Work.OROneRel.mmLo t (u ^ l) ⟨x, hxt⟩ →
      foxD (K := K) (X := MagnusBeta t) ((⟨x, hxt⟩ : {a : α // a ≠ t}), j)
        (Work.OROneRel.magRewRel t u) = 0 := by
    intro j hj
    refine foxD_eq_zero_of_notMem_relatorLetters (K := K) _ _ fun hmemj => ?_
    have hle := mmLo_le_of_mem_relatorLetters t u ⟨x, hxt⟩ hmemj
    rw [Work.OROneRel.mmLo_pow t u hcyc he l hl ⟨x, hxt⟩] at hj
    omega
  have hbase := hbase_of_ih_mm (K := K) t u l hcyc he hl (mmBotSym t u l x hxt) hm hIH
  exact fun b hb => ann_rootVec_of_magnusRewriting_bot (K := K) t x hxt (u ^ l) u l rfl hσ
    (Work.OROneRel.mmLo t (u ^ l) ⟨x, hxt⟩) hdec (fun c _ hcE => hbase c hcE) b hb

end Work.ORLyndon
