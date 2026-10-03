import Mathlib
import Submission.Work.ORLyndon.mmConnDefs
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero_mm
import Submission.Work.ORLyndon.ann_rootVec_of_level_bot
import Submission.Work.ORLyndon.level_ge_of_foxD_eq_zero
import Submission.Work.ORLyndon.mmBaseHom_injective
import Submission.Work.ORLyndon.mmBaseHom_comp_mk
import Submission.Work.ORLyndon.mapDomainRingHom_mmBaseHom_rootVec_eq
import Submission.Work.OROneRel.magnus_step_root

/-!
# The exponent-sum-zero Magnus step, at the *bottom* decorated symbol

This is the companion of `Work.ORLyndon.lyndon_independence_of_pow_eps_zero_mm`
(`Submission/Work/ORLyndon/lyndonIndependence_eps_zero_mm.lean`).  The leading-level transfer can be
run with the *maximum* level of the `x`-component of the root Fox vector (giving the top decorated
symbol `mmTopSym`) or — by the mirrored transfer `Work.ORLyndon.ann_rootVec_of_level_bot` — with the
*minimum* level (giving the bottom decorated symbol `mmBotSym`).

Having both is what makes the `σ_t = 0` step applicable in the induction independently of which
decorated symbol the base induction hypothesis happens to cover: for a letter `x ≠ t` the two
symbols `mmTopSym t u l x hxt` and `mmBotSym t u l x hxt` of `mmBeta t (u^l)` can be chosen, and for a
root with at least two letters outside `t` the top symbols already give distinct candidates.

* `Work.ORLyndon.mmBotSym` -- the bottom decorated symbol `(x, mmLo t (u^l) x)`.
* `Work.ORLyndon.ann_rootVec_of_level_bot_base` -- the bottom transfer with `hE0` derived from `hbase`.
* `Work.ORLyndon.ann_rootVec_of_magnusRewriting_bot` -- the bottom transfer for the Magnus rewriting.
* `Work.ORLyndon.lyndon_independence_of_pow_eps_zero_mm_bot` -- the assembled bottom step.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ORLyndon

open MonoidAlgebra

variable {α : Type*} [DecidableEq α] {K : Type*} [Field K]

/-- **The bottom decorated symbol of a letter.**  For a letter `x ≠ t`, the symbol
`(x, mmLo t (u^l) x)` of the occurring decorated alphabet `mmBeta t (u ^ l)`: the occurrence of `x`
with the smallest `t`-exponent-sum decoration. -/
noncomputable def mmBotSym (t : α) (u : FreeGroup α) (l : ℕ) (x : α) (hxt : x ≠ t) :
    Work.OROneRel.mmBeta t (u ^ l) :=
  ⟨((⟨x, hxt⟩ : {a : α // a ≠ t}), Work.OROneRel.mmLo t (u ^ l) ⟨x, hxt⟩),
    Work.OROneRel.mmLo_mem_decSet t (u ^ l) ⟨x, hxt⟩⟩

@[simp] theorem mmBotSym_val (t : α) (u : FreeGroup α) (l : ℕ) (x : α) (hxt : x ≠ t) :
    ((mmBotSym t u l x hxt : Work.OROneRel.mmBeta t (u ^ l)) : Work.OROneRel.MMAlpha t) =
      ((⟨x, hxt⟩ : {a : α // a ≠ t}), Work.OROneRel.mmLo t (u ^ l) ⟨x, hxt⟩) := rfl

/-- **The bottom-level transfer with `hE0` derived.**  The top-level analogue is
`Work.ORLyndon.ann_rootVec_of_level_base`. -/
theorem ann_rootVec_of_level_bot_base (t x : α) (hxt : x ≠ t) (r u : FreeGroup α) (l : ℕ)
    (hpow : r = u ^ l) (hσ : Work.OROneRel.sigma t u = 1) (i : ℤ)
    (E : MonoidAlgebra K (OneRelatorGroup r))
    (hEbase : ∀ g ∈ E.coeff.support, levelOf t r u l hpow hσ g = 1)
    (hDecomp : levelPart t r u l hpow hσ i (rootVec K r u x) =
      E * MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ i))
    (hDbound : ∀ g ∈ (rootVec K r u x).coeff.support,
      i ≤ (levelOf t r u l hpow hσ g).toAdd)
    (hbase : ∀ c : MonoidAlgebra K (OneRelatorGroup r),
      (∀ g ∈ c.coeff.support, levelOf t r u l hpow hσ g = 1) → c * E = 0 → c = 0)
    (b : MonoidAlgebra K (OneRelatorGroup r)) (hb : b * rootVec K r u x = 0) : b = 0 := by
  classical
  have hE0 : E ≠ 0 := by
    intro hEz
    have h1 : (1 : MonoidAlgebra K (OneRelatorGroup r)) = 0 := by
      refine hbase 1 ?_ (by rw [hEz, mul_zero])
      intro g hg
      have hsub := Finsupp.support_single_subset (a := (1 : OneRelatorGroup r)) (b := (1 : K))
      rw [MonoidAlgebra.one_def] at hg
      rw [Finset.mem_singleton.mp (hsub hg), map_one]
    exact one_ne_zero h1
  exact ann_rootVec_of_level_bot t x hxt r u l hpow hσ i E hEbase hE0 hDecomp hDbound hbase b hb

/-- **The bottom-level transfer for the Magnus rewriting.**  Given the vanishing of the Fox
derivatives below the level `i` and the base regularity for the image of `∂v/∂(x,i)`, the
`x`-component of the root Fox vector is right regular. -/
theorem ann_rootVec_of_magnusRewriting_bot (t x : α) (hxt : x ≠ t) (r u : FreeGroup α) (l : ℕ)
    (hpow : r = u ^ l) (hσ : Work.OROneRel.sigma t u = 1) (i : ℤ)
    (hdec : ∀ j : ℤ, j < i →
      foxD (K := K) (X := MagnusBeta t) ((⟨x, hxt⟩ : {a : α // a ≠ t}), j)
        (Work.OROneRel.magRewRel t u) = 0)
    (hbase : ∀ c : MonoidAlgebra K (OneRelatorGroup r),
      (∀ g ∈ c.coeff.support, levelOf t r u l hpow hσ g = 1) →
      c * MonoidAlgebra.mapDomainRingHom K ((presentRho r).comp (Work.OROneRel.zeta t))
            (foxD (K := K) (X := MagnusBeta t) ((⟨x, hxt⟩ : {a : α // a ≠ t}), i)
              (Work.OROneRel.magRewRel t u)) = 0 → c = 0)
    (b : MonoidAlgebra K (OneRelatorGroup r)) (hb : b * rootVec K r u x = 0) : b = 0 := by
  have hEbase : ∀ g ∈ (MonoidAlgebra.mapDomainRingHom K ((presentRho r).comp (Work.OROneRel.zeta t))
      (foxD (K := K) (X := MagnusBeta t) ((⟨x, hxt⟩ : {a : α // a ≠ t}), i)
        (Work.OROneRel.magRewRel t u))).coeff.support,
      levelOf t r u l hpow hσ g = 1 :=
    levelOf_support_mapDomainRingHom_zeta t r u l hpow hσ _
  refine ann_rootVec_of_level_bot_base t x hxt r u l hpow hσ i _ hEbase ?_
    (level_ge_of_foxD_eq_zero (K := K) (r := r) (u := u) (l := l) (hpow := hpow) (hσ := hσ)
      hxt hdec) hbase b hb
  rw [levelPart_rootVec_eq_base t x hxt r u l hpow hσ i]

/-- **The exponent-sum-zero Magnus step, bottom decorated symbol.**  Same statement as
`Work.ORLyndon.lyndon_independence_of_pow_eps_zero_mm`, but the base induction hypothesis is
consumed at the bottom decorated symbol `mmBotSym t u l x hxt` instead of the top one. -/
theorem lyndon_independence_of_pow_eps_zero_mm_bot (t : α) (u : FreeGroup α) (l : ℕ)
    (hl : 1 ≤ l) (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (ht : t ∈ Work.OROneRel.relatorLetters u) (he : Work.OROneRel.eps t u = 0)
    (x : α) (hxt : x ≠ t) (hx : x ∈ Work.OROneRel.relatorLetters u)
    (hIH : ∀ c : MonoidAlgebra K (Work.OROneRel.mmH t (u ^ l)),
      c * rootVec K (Work.OROneRel.mmW t (u ^ l))
        (Work.OROneRel.rootW t u l hcyc he hl) (mmBotSym t u l x hxt) = 0 → c = 0)
    (hIHord : orderOf (presentRho (Work.OROneRel.mmW t (u ^ l))
      (Work.OROneRel.rootW t u l hcyc he hl)) = l) :
    LyndonIndependence K (u ^ l) u := by
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
  have hann : ∀ b : MonoidAlgebra K (OneRelatorGroup (u ^ l)),
      b * rootVec K (u ^ l) u x = 0 → b = 0 :=
    fun b hb => ann_rootVec_of_magnusRewriting_bot (K := K) t x hxt (u ^ l) u l rfl hσ
      (Work.OROneRel.mmLo t (u ^ l) ⟨x, hxt⟩) hdec (fun c _ hcE => hbase c hcE) b hb
  have hord : orderOf (presentRho (u ^ l) u) = l :=
    orderOf_of_mmBaseHom t u l hl hpp hcyc ht he hIHord
  exact lyndon_independence_of_rootVec_inj (u ^ l) u l hl rfl hord
    (ann_rootVec_of_component (u ^ l) u x hann)

end Work.ORLyndon

namespace Work.ORLyndon

open MonoidAlgebra

variable {α : Type*} [DecidableEq α] {K : Type*} [Field K]

/-- **The `σ_t = 0` step with the extremal symbol chosen by the caller.**  The base induction
hypothesis may be supplied at the top symbol `mmTopSym t u l x hxt` *or* at the bottom symbol
`mmBotSym t u l x hxt` of `x`; either suffices.  This is the form in which the strong induction on
`relatorNorm` consumes the step (the two symbols are the two candidates for a symbol not exempted by
the base induction hypothesis). -/
theorem lyndon_independence_of_pow_eps_zero_mm_extremal (t : α) (u : FreeGroup α) (l : ℕ)
    (hl : 1 ≤ l) (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (ht : t ∈ Work.OROneRel.relatorLetters u) (he : Work.OROneRel.eps t u = 0)
    (x : α) (hxt : x ≠ t) (hx : x ∈ Work.OROneRel.relatorLetters u)
    (hIH : (∀ c : MonoidAlgebra K (Work.OROneRel.mmH t (u ^ l)),
        c * rootVec K (Work.OROneRel.mmW t (u ^ l))
          (Work.OROneRel.rootW t u l hcyc he hl) (mmTopSym t u l x hxt) = 0 → c = 0) ∨
      (∀ c : MonoidAlgebra K (Work.OROneRel.mmH t (u ^ l)),
        c * rootVec K (Work.OROneRel.mmW t (u ^ l))
          (Work.OROneRel.rootW t u l hcyc he hl) (mmBotSym t u l x hxt) = 0 → c = 0))
    (hIHord : orderOf (presentRho (Work.OROneRel.mmW t (u ^ l))
      (Work.OROneRel.rootW t u l hcyc he hl)) = l) :
    LyndonIndependence K (u ^ l) u :=
  hIH.elim
    (fun h => lyndon_independence_of_pow_eps_zero_mm t u l hl hpp hcyc ht he x hxt hx h hIHord)
    (fun h => lyndon_independence_of_pow_eps_zero_mm_bot t u l hl hpp hcyc ht he x hxt hx h hIHord)

end Work.ORLyndon
