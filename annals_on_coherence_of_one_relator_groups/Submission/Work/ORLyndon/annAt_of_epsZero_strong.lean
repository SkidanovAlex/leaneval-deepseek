import Mathlib
import Submission.Work.ORLyndon.annAtDefs
import Submission.Work.ORLyndon.ann_rootVec_of_level_set
import Submission.Work.ORLyndon.joint_annihilator_transport
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero_mm
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero
import Submission.Work.ORLyndon.mmBaseHom_injective
import Submission.Work.ORLyndon.mmBaseHom_transport
import Submission.Work.ORLyndon.mapDomainRingHom_mmBaseHom_rootVec_eq
import Submission.Work.ORLyndon.mmTopSym_mem_relatorLetters
import Submission.Work.ORLyndon.powDefs

/-!
# The exponent-sum-zero Magnus step of the Cohen--Lyndon descent, in set-indexed form

`Work.ORLyndon.annAt_of_epsZero_strong` is the transfer of the set-indexed annihilator statement
`Work.ORLyndon.annAt` through the exponent-sum-zero Magnus step of the Cohen--Lyndon induction.

Let `u` be a cyclically reduced root with `eps t u = 0` in a framing letter `t ∈ relatorLetters u`,
let `v = rootW t u l hcyc he hl` be the Magnus rewriting of `u` in the *occurring* decorated
alphabet `mmBeta t (u ^ l)` (`v ^ l = mmW t (u ^ l)`), and let `Em` be a set of letters `≠ t`.  The
theorem

`annAt K (mmW t (u^l)) v (mmTopSym t u l '' Em)  →  annAt K (u^l) u (Subtype.val '' Em)`

transfers the statement at the *top decorated symbols* of the letters of `Em` in the Magnus base
`⟨mmBeta t (u^l) | mmW t (u^l)⟩` to the statement at the letters themselves in `G = ⟨α | u ^ l⟩`.

## Proof

Write `G = ⟨α | u^l⟩`, `B = ⟨β | mmW t (u^l)⟩` (`β = mmBeta t (u^l)`), `Φ = mapDomainRingHom K
(mmBaseHom …) : K[B] → K[G]` and let `q_y = mmTopSym t u l y.1 y.2` be the top decorated symbol of
`y ∈ Em`, `E_y = Φ (rootVec K (mmW t (u^l)) v q_y)`.

1. **Transport to `K[G]`** (`Work.ORLyndon.joint_annihilator_transport`, the set-indexed form of
   `Work.ORLyndon.base_regularity_transport`, which removes the support restriction on `c`): the
   hypothesis `h`, read as the triviality of the *joint* annihilator of the family `rootVec … q_y`
   in `K[B]`, gives the triviality of the joint annihilator of the family `E_y` in `K[G]`.

2. **Leading level** (`Work.ORLyndon.ann_rootVec_of_level_set`): `σ_t` descends to
   `levelOf : G →* Multiplicative ℤ` with kernel the Magnus base.  Writing
   `τ = presentRho (u^l) (of t)`, the group algebra is the twisted Laurent ring
   `K[G] = ⊕_k K[B] τ^k` and the top level of the `y.1`-component of the root Fox vector is at
   `i_y = mmHi t (u^l) ⟨y.1, y.2⟩`, where it equals `E_y τ^{i_y}`
   (`Work.ORLyndon.levelPart_rootVec_eq_base`).  For `b ≠ 0` with `b * rootVec K (u^l) u y.1 = 0`
   for all `y ∈ Em`, the top level part `levelPart N b` (`N` the maximal level occurring in `b`)
   satisfies `levelPart N b * E_y = 0` for every `y ∈ Em`, and `τ^{-N} · levelPart N b` is supported
   on the base, so step 1 forces `levelPart N b = 0` — a contradiction.

3. The **decoration bookkeeping** (`Work.ORLyndon.mmTopSym_fst`, `Work.ORLyndon.foxD_mmHi_lt`,
   `Work.OROneRel.mmHi_pow`, `Work.ORLyndon.level_le_of_foxD_eq_zero`) supplies the level bound of
   step 2 for *every* letter `≠ t`: above the largest decoration `mmHi t (u^l) x` of `x` the Fox
   derivative of the Magnus rewriting vanishes *because no such decoration occurs*.  In particular
   no hypothesis `x ∈ relatorLetters u` on the letters of `Em` is needed, and none is present in the
   statement.

The identification `E_y = Φ (rootVec K (mmW t (u^l)) v q_y)` of step 1 with the base element of the
chain rule of step 2 is `Work.ORLyndon.mapDomainRingHom_mmBaseHom_rootVec_eq`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

open MonoidAlgebra

/-- The underlying decorated letter of the top symbol `mmTopSym t u l x hxt`. -/
theorem mmTopSym_fst {α : Type*} [DecidableEq α] (t : α) (u : FreeGroup α) (l : ℕ) (x : α)
    (hxt : x ≠ t) :
    (Work.ORLyndon.mmTopSym t u l x hxt).1 =
      ((⟨x, hxt⟩ : {a : α // a ≠ t}), Work.OROneRel.mmHi t (u ^ l) ⟨x, hxt⟩) := rfl

/-- **The Fox derivative of the Magnus rewriting vanishes above the largest decoration.**  If
`j > mmHi t u x` then the decoration `j` does not occur on `x` in the Magnus rewriting of `u`, so the
`(x, j)`-component of its Fox derivative vanishes. -/
theorem foxD_mmHi_lt {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) (u : FreeGroup α) (x : {a : α // a ≠ t}) :
    ∀ j : ℤ, Work.OROneRel.mmHi t u x < j →
      foxD (K := K) (X := ({a : α // a ≠ t} × ℤ)) (x, j)
        (Work.OROneRel.magRewRel t u) = 0 := by
  intro j hj
  refine foxD_eq_zero_of_notMem_relatorLetters (K := K) _ _ fun hmem => ?_
  rw [mem_relatorLetters_magRewRel_iff t u x j] at hmem
  rw [Work.OROneRel.mmHi, dif_pos ⟨j, hmem⟩] at hj
  exact absurd (Finset.le_max' _ _ hmem) (not_le.mpr hj)

theorem annAt_of_epsZero_strong {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (ht : t ∈ Work.OROneRel.relatorLetters u) (he : Work.OROneRel.eps t u = 0)
    (Em : Set {x : α // x ≠ t}) (hEm : Em.Nonempty)
    (h : Work.ORLyndon.annAt K (Work.OROneRel.mmW t (u ^ l))
          (Work.OROneRel.rootW t u l hcyc he hl)
          ((fun x : {x : α // x ≠ t} => Work.ORLyndon.mmTopSym t u l x.1 x.2) '' Em)) :
    Work.ORLyndon.annAt K (u ^ l) u (Subtype.val '' Em) := by
  classical
  intro b hb
  have hσ : Work.OROneRel.sigma t u = 1 :=
    (Work.OROneRel.eps_eq_zero_iff_sigma_eq_one t u).mp he
  -- ## Step 1: the joint annihilator of the base vectors is trivial in the base group algebra
  have hreg : ∀ c : MonoidAlgebra K (Work.OROneRel.mmH t (u ^ l)),
      (∀ y : Em, c * Work.ORLyndon.rootVec K (Work.OROneRel.mmW t (u ^ l))
        (Work.OROneRel.rootW t u l hcyc he hl)
        (Work.ORLyndon.mmTopSym t u l (y : Em).1.1 (y : Em).1.2) = 0) → c = 0 := by
    intro c hc
    refine h c ?_
    rintro q ⟨y, hy, rfl⟩
    exact hc ⟨y, hy⟩
  -- ## Step 1': transport along the canonical map from the Magnus base
  have htrans : ∀ c : MonoidAlgebra K (OneRelatorGroup (u ^ l)),
      (∀ y : Em, c * MonoidAlgebra.mapDomainRingHom K
        (Work.OROneRel.mmBaseHom (t := t) (r := u ^ l) (Work.ORLyndon.mmEpsPow t u l he))
        (Work.ORLyndon.rootVec K (Work.OROneRel.mmW t (u ^ l))
          (Work.OROneRel.rootW t u l hcyc he hl)
          (Work.ORLyndon.mmTopSym t u l (y : Em).1.1 (y : Em).1.2)) = 0) → c = 0 := by
    intro c hc
    refine joint_annihilator_transport
      (Work.OROneRel.mmBaseHom (t := t) (r := u ^ l) (Work.ORLyndon.mmEpsPow t u l he))
      (mmBaseHom_injective t u l hl hpp hcyc ht he)
      (Set.range fun y : Em => Work.ORLyndon.rootVec K (Work.OROneRel.mmW t (u ^ l))
        (Work.OROneRel.rootW t u l hcyc he hl)
        (Work.ORLyndon.mmTopSym t u l (y : Em).1.1 (y : Em).1.2)) ?_ c ?_
    · intro d hd
      exact hreg d fun y => hd _ ⟨y, rfl⟩
    · intro Y hY
      obtain ⟨y, rfl⟩ := hY
      exact hc y
  -- ## Step 1'': the base hypothesis of the leading-level transfer
  have hbase : ∀ c : MonoidAlgebra K (OneRelatorGroup (u ^ l)),
      (∀ g ∈ c.coeff.support, Work.ORLyndon.levelOf t (u ^ l) u l rfl hσ g = 1) →
      (∀ y : Em, c * MonoidAlgebra.mapDomainRingHom K
        ((Work.ORLyndon.presentRho (u ^ l)).comp (Work.OROneRel.zeta t))
        (foxD (K := K) (X := ({a : α // a ≠ t} × ℤ))
          ((Work.ORLyndon.mmTopSym t u l (y : Em).1.1 (y : Em).1.2).1)
          (Work.OROneRel.magRewRel t u)) = 0) → c = 0 := by
    intro c _ hc
    refine htrans c fun y => ?_
    rw [Work.ORLyndon.mapDomainRingHom_mmBaseHom_rootVec_eq t u l hcyc he hl
      (Work.ORLyndon.mmTopSym t u l (y : Em).1.1 (y : Em).1.2)]
    exact hc y
  -- ## Step 3: the level decomposition, the level bound and the support of the base elements
  have hEbase : ∀ y : Em, ∀ g ∈ (MonoidAlgebra.mapDomainRingHom K
        ((Work.ORLyndon.presentRho (u ^ l)).comp (Work.OROneRel.zeta t))
        (foxD (K := K) (X := ({a : α // a ≠ t} × ℤ))
          ((Work.ORLyndon.mmTopSym t u l (y : Em).1.1 (y : Em).1.2).1)
          (Work.OROneRel.magRewRel t u))).coeff.support,
      Work.ORLyndon.levelOf t (u ^ l) u l rfl hσ g = 1 := by
    intro y g hg
    exact Work.ORLyndon.levelOf_support_mapDomainRingHom_zeta t (u ^ l) u l rfl hσ _ g hg
  have hDecomp : ∀ y : Em, Work.ORLyndon.levelPart t (u ^ l) u l rfl hσ
        (Work.OROneRel.mmHi t (u ^ l) (⟨(y : Em).1.1, (y : Em).1.2⟩ : {a : α // a ≠ t}))
        (Work.ORLyndon.rootVec K (u ^ l) u ((y : Em).1.1)) =
      MonoidAlgebra.mapDomainRingHom K
        ((Work.ORLyndon.presentRho (u ^ l)).comp (Work.OROneRel.zeta t))
        (foxD (K := K) (X := ({a : α // a ≠ t} × ℤ))
          ((Work.ORLyndon.mmTopSym t u l (y : Em).1.1 (y : Em).1.2).1)
          (Work.OROneRel.magRewRel t u)) *
      MonoidAlgebra.of K (OneRelatorGroup (u ^ l))
        ((Work.ORLyndon.presentRho (u ^ l) (FreeGroup.of t)) ^
          (Work.OROneRel.mmHi t (u ^ l) (⟨(y : Em).1.1, (y : Em).1.2⟩ : {a : α // a ≠ t}))) := by
    intro y
    rw [Work.ORLyndon.mmTopSym_fst]
    exact Work.ORLyndon.levelPart_rootVec_eq_base t (y : Em).1.1 (y : Em).1.2 (u ^ l) u l rfl hσ
      (Work.OROneRel.mmHi t (u ^ l) ⟨(y : Em).1.1, (y : Em).1.2⟩)
  have hDbound : ∀ y : Em,
      ∀ g ∈ (Work.ORLyndon.rootVec K (u ^ l) u ((y : Em).1.1)).coeff.support,
      (Work.ORLyndon.levelOf t (u ^ l) u l rfl hσ g).toAdd ≤
        Work.OROneRel.mmHi t (u ^ l) (⟨(y : Em).1.1, (y : Em).1.2⟩ : {a : α // a ≠ t}) := by
    intro y g hg
    refine Work.ORLyndon.level_le_of_foxD_eq_zero (K := K) (t := t) (r := u ^ l) (u := u) (l := l)
      (hpow := rfl) (hσ := hσ) (x := (y : Em).1.1) (hxt := (y : Em).1.2)
      (i := Work.OROneRel.mmHi t (u ^ l) ⟨(y : Em).1.1, (y : Em).1.2⟩) ?_ g hg
    intro j hj
    refine foxD_mmHi_lt (K := K) t u ⟨(y : Em).1.1, (y : Em).1.2⟩ j ?_
    rwa [← Work.OROneRel.mmHi_pow t u hcyc he l hl ⟨(y : Em).1.1, (y : Em).1.2⟩]
  -- ## Step 2: the leading-level transfer
  exact Work.ORLyndon.ann_rootVec_of_level_set t (u ^ l) u l rfl hσ
    (fun y : Em => (y : Em).1.1) (fun y : Em => (y : Em).1.2)
    (fun y : Em => Work.OROneRel.mmHi t (u ^ l)
      (⟨(y : Em).1.1, (y : Em).1.2⟩ : {a : α // a ≠ t}))
    (fun y : Em => MonoidAlgebra.mapDomainRingHom K
      ((Work.ORLyndon.presentRho (u ^ l)).comp (Work.OROneRel.zeta t))
      (foxD (K := K) (X := ({a : α // a ≠ t} × ℤ))
        ((Work.ORLyndon.mmTopSym t u l (y : Em).1.1 (y : Em).1.2).1)
        (Work.OROneRel.magRewRel t u)))
    hEbase hDecomp hDbound hbase b
    (fun y : Em => hb ((y : Em).1.1) ⟨(y : Em).1, (y : Em).2, rfl⟩)

end Work.ORLyndon
