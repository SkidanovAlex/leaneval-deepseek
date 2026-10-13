/-
  WilC5 — **the vocabulary of the one-point step of vdDMM §4** (Lemmas 4.2, 4.3, 4.4).

  The one-element step `Work.WilC5.S4OnePoint` is stated purely in the *language* `LRc` of the
  `rexp`-reduct: its domains are `LRc`-substructures of a model `K ⊨ TE` satisfying `S4Dom`
  (`Dcl`-closed in the `rexp`-reduct and closed under the definable logarithm), and its embeddings
  are `LRc`-embeddings of the `rexp`-reducts.  The three lemmas of van den Dries–Macintyre–Marker
  §4, however, are *value-theoretic*: their hypotheses and their case distinctions use the standard
  real valuation `v` of the ambient ordered field — `v(x) = v(b)` (`SameArch`), "`x` is
  *value-new* over the domain", "the domain is closed under the exponential".

  This module puts that vocabulary on top of the `S4` language-setting, by fixing the canonical
  ordered-field structure of the `rexp`-reduct: for `[LEc.Structure K]` and `hK : K ⊨ TE`, the
  `LRc`-structure on `K` is the reduct `reductStruct K` (`S4Dom`, `LogPreserving` and `S4Pair` all
  use it), it models `TR` (`Work.WilC5.reduct_model_TR`), and hence carries

  * a `Field` structure (`Work.WilC5.trField`), a `LinearOrder` structure whose order is the
    ring-definable order `leEL` (`Work.WilC5.trLinearOrder`), the instance `IsStrictOrderedRing`
    (`Work.WilC5.tr_isStrictOrderedRing`) and `Ring.CompatibleRing`
    (`FirstOrder.Field.compatibleRingOfModelField`),

  all four derived from that same `LRc`-structure, so that they are coherent with the `LRc`
  operations by construction.  (This is the "canonical setting" of area C2, see
  `Submission/Work/WilC5/TRCanon.lean`, `LRcReduct.lean`.)

  On top of it we define the two *value-theoretic* predicates used by the case split of §4:

  * `Work.WilC5.SameVal K hK b x` — `b` and `x` lie in the same archimedean class
    (`Work.WilC5.SameArch`, i.e. `v(b) = v(x)`);
  * `Work.WilC5.ValueNew K hK B x` — the archimedean class of `x` is *new* over the domain `B`
    (`v(x) ∉ v(B^×)`), the hypothesis under which vdDMM's Lemma 4.4 (and Lemma 4.3) operate.

  The three extension lemmas are stated in the companion files `S4StepNoNew.lean` (4.2),
  `S4StepExp.lean` (4.3) and `S4StepNew.lean` (4.4); `S4OnePoint_general_proved.lean` assembles
  them into `Work.WilC5.S4OnePoint_general` by running them at a *maximal* member of the Zorn
  poset `Work.WilC5.S4Pair` of partial extensions (`S4Setup.lean`, `S4SubTE_of_S4OnePoint.lean`),
  which is where the hypotheses ("no new value", "closed under exp", "no immediate extension")
  come from.
-/
import Mathlib
import Submission.Work.WilC5.S4SubTE_of_S4OnePoint
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.valIneq_span
import Submission.Work.WilC5.decomposition_of_same_value
import Submission.Work.WilC5.realizes_cut
import Submission.Work.WilC5.dmm42_cut_extend
import Submission.Work.WilC5.logFun_mul
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.expE_of_logFun_preserving
import Submission.Work.WilC5.model_TR_of_dcl_closed

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

attribute [local instance] Work.WilC5.reductStruct

/-! ## 1. The canonical ordered-field structure of the `rexp`-reduct of a model of `TE` -/

/-- **`K ⊨ TR` for the `rexp`-reduct `reductStruct K` of a model of `TE`.** -/
theorem reductTR {K : Type} [LEc.Structure K] (hK : K ⊨ TE) :
    @FirstOrder.Language.Theory.Model LRc K (reductStruct K) TR :=
  @reduct_model_TR K inferInstance hK

/-- **The canonical `Field` structure of a model of `TE`**, derived from its `rexp`-reduct
(`Work.WilC5.trField` at `Work.WilC5.reductTR`). -/
noncomputable def cField (K : Type) [LEc.Structure K] (hK : K ⊨ TE) : Field K :=
  letI : LRc.Structure K := reductStruct K
  trField K (reductTR hK)

/-- **The canonical `LinearOrder` structure of a model of `TE`** (its order is the ring-definable
order `leEL` of the `rexp`-reduct). -/
noncomputable def cLin (K : Type) [LEc.Structure K] (hK : K ⊨ TE) : LinearOrder K :=
  letI : LRc.Structure K := reductStruct K
  trLinearOrder K (reductTR hK)

/-- **Same value**: `b` and `x` lie in the same archimedean class of the canonical ordered field
structure of a model of `TE` (`Work.WilC5.SameArch`, i.e. `v(b) = v(x)` in vdDMM (1.1)). -/
def SameVal (K : Type) [LEc.Structure K] (hK : K ⊨ TE) (b x : K) : Prop :=
  letI : LRc.Structure K := reductStruct K
  letI : Field K := cField K hK
  letI : LinearOrder K := cLin K hK
  SameArch b x

/-- **Value-new**: no element of the `LRc`-substructure `B` lies in the archimedean class of `x` —
i.e. `v(x) ∉ v(B^×)`, the hypothesis "`v(F₀(x)^×) ≠ v(F₀^×)`" of vdDMM Lemmas 4.3/4.4.
(For `x ≠ 0` the case `b = 0` is vacuous, since `SameArch 0 x` forces `x = 0`.) -/
def ValueNew (K : Type) [LEc.Structure K] (hK : K ⊨ TE) (B : LRc.Substructure K) (x : K) : Prop :=
  ∀ b : ↥B, ¬ SameVal K hK (b : K) x

/-- **The value of `x` is already in `v(B^×)`** — the "no new value" hypothesis of vdDMM
Lemma 4.2, in the form in which the decomposition `w = z(1+ε)` of its proof is available: some
element of `B` has the same value as `x`. -/
def ValueOld (K : Type) [LEc.Structure K] (hK : K ⊨ TE) (B : LRc.Substructure K) (x : K) : Prop :=
  ∃ b : ↥B, SameVal K hK (b : K) x

theorem not_valueOld_iff_valueNew (K : Type) [LEc.Structure K] (hK : K ⊨ TE)
    (B : LRc.Substructure K) (x : K) :
    (¬ ValueOld K hK B x) ↔ ValueNew K hK B x := by
  simp [ValueOld, ValueNew]

end Work.WilC5
