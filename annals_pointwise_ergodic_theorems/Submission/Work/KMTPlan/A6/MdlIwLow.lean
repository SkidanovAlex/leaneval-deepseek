/-
# The Ionescu--Wainger minor-arc condition in the finite cyclic model (`ℤ/Qℤ`)

This small, self-contained module fixes the vocabulary in which the arithmetic input of the
large-scale (`§8`) model estimate of Krause--Mirek--Tao, *Pointwise ergodic theorems for
non-conventional bilinear polynomial averages*, Annals 195 (2022), is stated -- namely the
*correct* minor-arc hypothesis of the paper's Theorem `bile`:

> `ℱ_Ẑ f` vanishes on `(ℚ/ℤ)_{≤ l}`,

in the finite model `ℤ/Qℤ` of `Submission/Work/Analysis/Paraproduct/ArithBilinear.lean`.

* `iwLowFreqs ρ l Q` -- the frequencies of `ℤ/Qℤ` of Ionescu--Wainger height at most `2^l`, the
  finite model of the major arcs `ℳ_{≤l}`;
* `MdlIwMinorArc ρ l Q f` -- the minor-arc condition: the discrete Fourier transform of `f`
  vanishes on `iwLowFreqs ρ l Q`;
* `MdlIwMinorArc.toMinorArcSupport` -- Appendix A's inclusion `[2^l] ⊆ P_{≤l}`
  (`Work.Analysis.IonescuWainger.iwPconcrete_contains_range`) shows that the *naive* dyadic arcs
  are contained in the Ionescu--Wainger arcs, so the *Ionescu--Wainger* minor-arc condition
  implies the naive one `Work.Analysis.Paraproduct.MinorArcSupport`.

Consequence: the arithmetic bilinear estimates stated with the *naive* hypothesis
(`Work.KMTPlan.A6.BileTwoOfImprov`, `Work.KMTPlan.A6.ArithBilinearEstimateOfImprov`) apply to
data that only satisfy the *Ionescu--Wainger* hypothesis -- which is the condition produced by the
exact-height Ionescu--Wainger packets (`mdlF`), whose Fourier support sits at Ionescu--Wainger
height exactly `2^l` and in general does *not* avoid the naive dyadic arcs.

Nothing in this module depends on the (changing) model-operator definitions, so it is stable.
-/
import Mathlib
import Submission.Work.Analysis.IonescuWainger.iwPconcrete_contains_range
import Submission.Work.Analysis.Concentration.Bilinear
import Submission.Work.Analysis.Paraproduct.CrtFactor

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.KMTPlan.A6

open Work.Analysis.IonescuWainger

noncomputable section

def iwLowFreqs (ρ : ℝ) (l Q : ℕ) [NeZero Q] : Finset (ZMod Q) :=
  Finset.univ.filter (fun ξ : ZMod Q => ∃ q ∈ iwP ρ l, q • ξ = 0)
def MdlIwMinorArc (ρ : ℝ) (l Q : ℕ) [NeZero Q] (f : ZMod Q → ℂ) : Prop :=
  ∀ ξ ∈ iwLowFreqs ρ l Q, ZMod.dft f ξ = 0
theorem iwP_of_le_two_pow (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l q : ℕ}
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2 ^ l) : q ∈ iwP ρ l := by
  rw [Work.Analysis.IonescuWainger.mem_iwP]
  by_cases h : l ≤ Work.Analysis.IonescuWainger.iwC0 ρ
  · exact Or.inl ⟨h, hq1, hq2⟩
  · push Not at h
    exact Or.inr ⟨h, Work.Analysis.IonescuWainger.iwPconcrete_contains_range hρ hρ1 h.le hq1 hq2⟩
theorem addOrderOf_mem_iwLowFreqs (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l Q : ℕ) [NeZero Q]
    (ξ : ZMod Q) (hξ : addOrderOf ξ ≤ 2 ^ l) : ξ ∈ iwLowFreqs ρ l Q := by
  rw [iwLowFreqs, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, addOrderOf ξ,
    iwP_of_le_two_pow ρ hρ hρ1 (Nat.succ_le_of_lt (addOrderOf_pos ξ)) hξ, ?_⟩
  exact addOrderOf_nsmul_eq_zero ξ
end

end Work.KMTPlan.A6
