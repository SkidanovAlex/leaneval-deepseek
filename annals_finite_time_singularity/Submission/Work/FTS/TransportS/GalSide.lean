/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `g`-side hypotheses of `T2S`/`T3S_Dz` are supplied by `GalClass`

`VocabO.T2Clause`/`T3Clause` (and the frozen statements `T2S`, `T3S_Dz`) ask of the test
function `g` the hypotheses `RegQ α 4 g`, `HkMem α 5 g`, `DecayAll 4 g`.  The Galerkin
profiles (and the perturbation along the a-priori argument) lie in
`Work.FTS.Nonlin.GalClass α g`, whose `reg` field is `RegQ α 6 g` and whose `decay` field is
`DecayAll 6 g`.  This file records the monotonicity that converts the order `6` data into the
order `4`/`5` data the transport clauses consume; it is the `galClass_T2_side` "child" of the
design note (`ELL_H2_LEAD.md` §B3, "Row side conditions").

The proof is `GalerkinFix.RegQ.regQ_mono` (decay of `RegQ` in the order, via
`HkMem_mono_Q`) plus the elementary monotonicity of `DecayAll`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## `DecayAll` is monotone in the order -/

/-- `DecayAll` descends in the order (both `DecayInZ` and `DecayMixed` are conjunctions over
the pairs `a + b ≤ n`). -/
theorem decayAll_mono {n n' : ℕ} (hn : n' ≤ n) {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.DecayAll n f) : Work.Spaces.DecayAll n' f :=
  ⟨fun j i hij => h.1 j i (le_trans hij hn), fun a b hab => h.2 a b (le_trans hab hn)⟩

/-- `HkMem` descends in the order inside the class `SmoothQuad`. -/
theorem hkMem_mono_of_smoothQuad {α : ℝ} {k k' : ℕ} (hk : k' ≤ k) {f : ℝ → ℝ → ℝ}
    (hs : Work.FTS.LocData.SmoothQuad f) (h : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k' f := by
  induction k with
  | zero =>
    obtain rfl : k' = 0 := Nat.le_zero.mp hk
    exact h
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hk with hEq | hLt
    · subst hEq; exact h
    · exact ih (Nat.lt_succ_iff.mp hLt) (Work.GalerkinFix.RegQ.HkMem_mono_Q hs h)

/-- **`galClass_T2_side`**: the Galerkin class supplies the `g`-side of the transport
clauses.  `RegQ α 6 g → RegQ α 4 g`, `HkMem α 6 g → HkMem α 5 g`, and
`DecayAll 6 g → DecayAll 4 g`. -/
theorem galClass_T2_side {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.GalClass α g) :
    Work.FTS.Nonlin.RegQ α 4 g ∧ Work.Spaces.HkMem α 5 g ∧ Work.Spaces.DecayAll 4 g := by
  have h5 : Work.FTS.Nonlin.RegQ α 5 g :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hg.reg (by norm_num)
  exact ⟨Work.FTS.GalerkinFix.RegQ.regQ_mono hg.reg (by norm_num), h5.2.1,
    decayAll_mono (by norm_num : (4 : ℕ) ≤ 6) hg.decay⟩

/-- The same for the *coercivity* class `CoerAdm` (used by the `D_z`-self-pairing rows). -/
theorem coerAdm_T2_side {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.CoerAdm α g) :
    Work.FTS.Nonlin.RegQ α 4 g ∧ Work.Spaces.HkMem α 4 g :=
  ⟨Work.FTS.GalerkinFix.RegQ.regQ_mono hg.reg (by norm_num), by
    have h4 := Work.FTS.GalerkinFix.RegQ.regQ_mono hg.reg (by norm_num : (4 : ℕ) ≤ 5)
    exact h4.2.1⟩

end Work.FTS.TransportS
