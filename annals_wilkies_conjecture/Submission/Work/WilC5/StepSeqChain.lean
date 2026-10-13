import Mathlib
import Submission.Work.WilC5.ValueOrder
import Submission.Work.WilC5.StepSeq
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.ValuesLemmas

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG

/-! Auxiliary lemmas for `Work.WilC5.StepSeqChain`.

The chain of vdDMM Lemma 4.4 records `log xₙ = βₙ ± x_{n+1}`; the two facts proved here are the
"min rule" consequences of the value-new hypothesis `¬ SameArch βₙ x_{n+1}` that the chain consumes:

* `vle_log_of_rel`: `log xₙ = βₙ ± x_{n+1}` and `v(βₙ) ≠ v(x_{n+1})` force `log xₙ` to dominate `βₙ`
  (`VLe (log xₙ) βₙ`) — otherwise `βₙ` would dominate `log xₙ` and the min rule would make
  `x_{n+1} = ±(log xₙ - βₙ)` have the value of `βₙ ∈ B`;
* `vle_chain_of_rel`: once `log xₙ` dominates `βₙ`, the relation `|x_{n+1}| = |log xₙ - βₙ|` bounds
  `x_{n+1}` by a multiple of `log xₙ`, so `VLe xₙ x_{n+1}` follows from `VLe xₙ (log xₙ)`. -/

namespace StepSeqChainAux

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `SameArch` is symmetric (it is an equality of values). -/
lemma SameArch_symm {x y : K} (h : SameArch x y) : SameArch y x := by
  obtain ⟨N, h1, h2⟩ := h
  exact ⟨N, h2, h1⟩

/-- `SameArch` is invariant under a sign change of its first argument. -/
lemma SameArch_neg_left (x y : K) : SameArch (-x) y ↔ SameArch x y := by
  unfold SameArch
  rw [abs_neg]

/-- **The min-rule step of the chain.**  If `log x = β ± x'` and `β` and `x'` do *not* have the same
value, then `log x` dominates `β`.

Indeed, if `β` dominated `log x` strictly, then `β - log x = ∓ x'` would have the value of `β` by the
min rule (`SameArch_sub_of_VLe_of_not`), contradicting `¬ SameArch β x'`. -/
lemma vle_log_of_rel {L b y : K} (hrel : L = b + y ∨ L = b - y)
    (hnew : ¬ SameArch b y) : VLe L b := by
  by_contra hcon
  have hbL : VLe b L := (VLe_total L b).resolve_left hcon
  have hSA : SameArch (b - L) b := SameArch_sub_of_VLe_of_not hbL hcon
  have hby : SameArch b y := by
    rcases hrel with h | h
    · have h1 : b - L = -y := by rw [h]; ring
      rw [h1] at hSA
      exact SameArch_symm ((SameArch_neg_left y b).mp hSA)
    · have h1 : b - L = y := by rw [h]; ring
      rw [h1] at hSA
      exact SameArch_symm hSA
  exact hnew hby

/-- **The chain step.**  If `log x = β ± x'`, `log x` dominates `β`, and `x` dominates `log x`,
then `x` dominates `x'`.

This is the identity `|x'| = |log x - β| ≤ |log x| + |β|` together with `VLe_trans`. -/
lemma vle_chain_of_rel {L b y x : K} (hLb : VLe L b) (hrel : L = b + y ∨ L = b - y)
    (hxL : VLe x L) : VLe x y := by
  obtain ⟨C, hC⟩ := hLb
  have hy : |y| = |L - b| := by
    rcases hrel with h | h
    · have h1 : L - b = y := by rw [h]; ring
      rw [h1]
    · have h1 : L - b = -y := by rw [h]; ring
      rw [h1, abs_neg]
  have hbound : |y| ≤ (((C + 1 : ℕ) : K) + 1) * |L| := by
    rw [hy]
    have h1 : |L - b| ≤ |L| + |b| := by
      have := abs_sub_le L 0 b
      simpa using this
    calc |L - b| ≤ |L| + |b| := h1
      _ ≤ |L| + (((C : K) + 1) * |L|) := by linarith [hC]
      _ = ((((C + 1 : ℕ)) : K) + 1) * |L| := by push_cast; ring
  exact VLe_trans hxL ⟨C + 1, hbound⟩

end StepSeqChainAux

theorem StepSeqChain
    {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE]
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (B : WilkiesDesign.CG.LRc.Substructure K)
    (S : Work.WilC5.StepSeq B)
    (hnew : Work.WilC5.StepSeq.ValueNewAll S)
    (hdom : Work.WilC5.StepSeq.LogDominated S) :
    (∀ n : ℕ, Work.WilC5.VLe (Work.WilC5.logFun (S.xs n)) (S.beta n : K)) ∧
      (∀ n : ℕ, Work.WilC5.VLe (S.xs n) (S.xs (n + 1))) := by
  have hTE : K ⊨ WilkiesDesign.CG.TE := inferInstance
  have hsub : ∀ x y : K, Work.WilC5.subE x y = x - y :=
    fun x y => Work.WilC5.S4ExpF.subE_eq_sub hTE hadd x y
  -- dissect `log xₙ = βₙ ± x_{n+1}` from the data of the sequence
  have hrel_n : ∀ n : ℕ, Work.WilC5.logFun (S.xs n) = (S.beta n : K) + S.xs (n + 1) ∨
      Work.WilC5.logFun (S.xs n) = (S.beta n : K) - S.xs (n + 1) := by
    intro n
    rw [S.hrel n]
    cases hb : S.pos n with
    | false => exact Or.inr (hsub _ _)
    | true => exact Or.inl (hadd _ _)
  -- `log xₙ` dominates `βₙ`: `βₙ ∈ B` is never of the value of the new `x_{n+1}`
  have hA : ∀ n : ℕ, Work.WilC5.VLe (Work.WilC5.logFun (S.xs n)) (S.beta n : K) := by
    intro n
    exact StepSeqChainAux.vle_log_of_rel (hrel_n n) (hnew (n + 1) (S.beta n))
  refine ⟨hA, ?_⟩
  -- `xₙ` dominates `x_{n+1}`: `|x_{n+1}| = |log xₙ - βₙ| ≤ |log xₙ| + |βₙ| ≤ C |log xₙ| ≤ C' |xₙ|`
  intro n
  exact StepSeqChainAux.vle_chain_of_rel (hA n) (hrel_n n) (hdom n).1

end Work.WilC5
