import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mixedMul_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mixed_le_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_le_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbAux.SlotPriceAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.summand_le_easy
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.qDzLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.HardDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowMulSupAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# `rowMulSup`: the sup-priced `A · f` row of the level-six `N`-pairing

The Leibniz expansion of `mixed b a (A · f)` pairs each summand
`ρ · (D_z^i D_θ^j A) · (D_z^{b-i} D_θ^{a-j} f) · (D_z^b D_θ^a f)` either

* in the *guard* case `1 ≤ a - j ∨ ρ = leafEta ∨ ρ = leafOne`, where the first `f`-slot is
  priced by `HkIntegrand α 6 f` under the leaf weight `ρ` and the `A`-slot is pointwise bounded
  by `2000 · KA` (`WlInf α 6 A ≤ KA` plus the `σ^{-α/5}/(α+σ)`-gain of the flat norm), or
* in the *mismatch* case `ρ = leafGam α ∧ j = a` (all angular derivatives on `A`), where the
  first `f`-slot is the pure `D_z^{b-i} f` and the `σ`-gain of the flat norm together with the
  two-weight angular Hardy `qDzLe` (whose `α^{-2}` is exactly cancelled by the `α` of the
  gain) closes the estimate.
-/

/-- The product measure of the two restricted Lebesgue measures; this is the measure under
which all the level-six slot estimates of the `T6Gen`/`N6TP` family are stated. -/
abbrev mu : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- Integrability of a finite sum of integrable functions. -/
lemma integrable_finset_sum {ι : Type*} (s : Finset ι) {φ : ι → ℝ × ℝ → ℝ}
    (h : ∀ i ∈ s, Integrable (φ i) mu) : Integrable (fun p => ∑ i ∈ s, φ i p) mu := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (integrable_zero (α := ℝ × ℝ) (μ := mu))
  | insert a s ha ih =>
      have h1 : Integrable (φ a) mu := h a (Finset.mem_insert_self a s)
      have h2 : Integrable (fun p => ∑ i ∈ s, φ i p) mu :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have h3 : Integrable (fun p => φ a p + ∑ i ∈ s, φ i p) mu := h1.add h2
      have h4 : (fun p : ℝ × ℝ => ∑ i ∈ insert a s, φ i p)
          = fun p => φ a p + ∑ i ∈ s, φ i p := by
        funext p
        rw [Finset.sum_insert ha]
      rw [h4]
      exact h3

/-- The slot pairing is the product-measure integral of its integrand. -/
lemma slotPairing_eq_prod {ρ : ℝ → ℝ → ℝ} {a b : ℕ} {u v : Fn}
    (h : Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed b a u p.1 p.2
        * Work.Spaces.mixed b a v p.1 p.2) mu) :
    Work.FTS.TransportS.slotPairing ρ a b u v
      = ∫ p, ρ p.1 p.2 * Work.Spaces.mixed b a u p.1 p.2
          * Work.Spaces.mixed b a v p.1 p.2 ∂mu := by
  rw [Work.FTS.TransportS.slotPairing]
  exact (MeasureTheory.integral_prod _ h).symm

/-- The Leibniz expansion of `mixed b a (A · f)`, a.e. for the product measure. -/
lemma mixedMul_ae' {A f : ℝ → ℝ → ℝ} {a b : ℕ}
    (hA : ContDiffOn ℝ 6 (Function.uncurry A) Work.FTS.EllipticEst.Q0)
    (hf : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hab : a + b ≤ 6) :
    (fun p : ℝ × ℝ => Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) p.1 p.2) =ᵐ[mu]
      (fun p : ℝ × ℝ => ∑ i ∈ Finset.range (b + 1), ∑ j ∈ Finset.range (a + 1),
        ((b.choose i : ℝ) * (a.choose j : ℝ))
          * (Work.Spaces.mixed i j A p.1 p.2
              * Work.Spaces.mixed (b - i) (a - j) f p.1 p.2)) := by
  refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ1 hθ2 => ?_)
  show Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) z θ
      = ∑ i ∈ Finset.range (b + 1), ∑ j ∈ Finset.range (a + 1),
        ((b.choose i : ℝ) * (a.choose j : ℝ))
          * (Work.Spaces.mixed i j A z θ * Work.Spaces.mixed (b - i) (a - j) f z θ)
  rw [Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mixedMul_cd6 hA hf b a (by omega) z θ
    hz hθ1 hθ2]

/-- **The guard Leibniz summand.**  If the first `f`-slot carries an angular derivative
(`1 ≤ a - j`) or the leaf weight is `η` or σ-free, then the summand is integrable and bounded
by `C · KA · (1 + HkSq α 6 f)`: the `A`-slot is pointwise bounded by `2000 · KA`
(`slotPrice_of_WlInf`) and the two `f`-slots are each dominated by `HkIntegrand α 6 f` under
the leaf weight, so the AM–GM inequality closes. -/
lemma guardSummand : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : ℝ → ℝ → ℝ) (KA : ℝ) (i j a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
      Work.Spaces.WlInf α 6 A ≤ KA →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      a + b ≤ 6 → j ≤ a → i ≤ b → Work.FTS.TransportS.IsLeafW α a ρ →
      (1 ≤ a - j ∨ ρ = Work.FTS.TransportS.leafEta
        ∨ ρ = Work.FTS.TransportS.leafOne) →
      Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed i j A p.1 p.2
          * Work.Spaces.mixed (b - i) (a - j) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2) mu ∧
      |∫ p, ρ p.1 p.2 * Work.Spaces.mixed i j A p.1 p.2
          * Work.Spaces.mixed (b - i) (a - j) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2 ∂mu|
        ≤ C * KA * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨Ce, hCepos, heasy⟩ := Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.summand_le_easy
  refine ⟨2000 * Ce + 1, by positivity, ?_⟩
  intro α hα A f KA i j a b ρ hA hAm hAb hfsm hfm hab hja hib hleaf hgj
  obtain ⟨hα0, hα1⟩ := hα
  have hαmem : α ∈ Set.Ioc 0 1 := ⟨hα0, hα1⟩
  have hprice : Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbAux.SlotPrice (2000 * KA) A :=
    Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbAux.slotPrice_of_WlInf hα0 hα1
      (hA.forall 6) hAm hAb
  have hKA0 : 0 ≤ KA := le_trans (Work.Spaces.WlInf_nonneg α 6 A hAm) hAb
  have hSq0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  obtain ⟨hint, hbd⟩ := heasy α hαmem (fun z θ => Work.Spaces.mixed i j A z θ) f (a - j) (b - i)
    a b ρ (2000 * KA) (hA.mixed i j) (by positivity)
    (fun z θ hz hθ hθ2 => hprice i j (by omega) z θ hz hθ hθ2)
    hfsm hfm (by omega) hab hleaf hgj
  refine ⟨hint, ?_⟩
  refine hbd.trans ?_
  have hkey : Ce * (2000 * KA) * Work.Spaces.HkSq α 6 f
      ≤ (2000 * Ce + 1) * KA * (1 + Work.Spaces.HkSq α 6 f) := by
    nlinarith [hCepos, hKA0, hSq0]
  linarith [hkey]


end Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowMulSupAux
