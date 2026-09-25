import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.memLp_scaled_bump
import Submission.Work.BourgainPlan.Maximal.mikhlin_conditions_scaled_bump
import Submission.Work.BourgainPlan.Maximal.level_l2_mst_large_n_aux_defs
import Submission.Commons.Analysis.Maximal.real_maximal_weak_type

/-!
# The *wide* bump `ϱ_s` and the wide level model `Ω^s_{2^k}` of MST Theorem 1

This module contains the vocabulary of the large-scale half of the level-`s` `ℓʳ` estimate
(`Work.Maximal.mst_level_lr_large`, MST arXiv:1512.07518 Theorem 8).  The *narrow* level bump of the
model is `mstEta d χ η s ξ = η (2^{s(d−χ)} iwRep ξ)` (supported in a ball of radius `2^{−s(d−χ)}/2`);
the replacement used for the large scales is the *wide* bump

`mstWideBump P χ η s ξ = η (mstWideC P s · iwRep ξ)`,  `mstWideC P s = (mstQ' s)^{3 d}`,

which is *wider* than the narrow bump (its radius `1/(2 c_s)` is `≫ 2^{−s(d−χ)}`) but still much
narrower than the separation of the level-`(s+1)` arcs and than `iwEps (mstRho l) ((s+1)^l)`.

The two facts that the route uses repeatedly are

* `mstWideBump_narrow`: `ϱ_s` vanishes outside the ball of radius `1/(2 mstWideC P s)`, so in
  particular outside the Ionescu–Wainger ball `iwEps (mstRho l) ((s+1)^l)` (the *narrowness*
  hypothesis of `iwRangeBound`/`IWSupersetBoundLift`), and
* the Mikhlin data of `circleLift ϱ_s` are those of the original bump `η`
  (`mikhlin_conditions_scaled_bump`), so the multiplier-norm hypothesis `IWMult` for `ϱ_s` holds
  with a constant independent of `s`.

The wide model symbol is MST's `Ω^s_N = Σ_{β ∈ 𝒰(s+1)∖𝒰(s)} G(β) Φ_N(·−β) ϱ_s(·−β)`; the single
weighted multiplier of MST's (79) is `mstWidePiG`, and the unweighted arc sum is `mstWidePi`.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-- The **wide scale** `c_s = (Q_s)^{3d}` of the large-scale half of the level estimate, where
`Q_s = mstQ' s` is the level denominator bound (the factorial of `⌈exp((s+1)^{1/10})⌉`) and
`d = P.natDegree`.  The choice `3d` (i.e. MST's `3dA` with `A = 1`) gives
`c_s ≥ Q_s^{d+1} 2^{2d+2}` (the Nyquist condition for the `Q_s`-sublattice sampling) and
`c_s ≥ 2 exp((s+1)^{1/10})` (so that the wide bump is narrower than `iwEps`). -/
def mstWideC (P : Polynomial ℤ) (s : ℕ) : ℝ :=
  ((Work.BourgainPlan.Maximal.mstQ' s : ℕ) : ℝ) ^ (3 * P.natDegree)

/-- The Hardy–Littlewood maximal function `Commons.Analysis.Maximal.hlMax` of a function
`f : ℝ → ℝ≥0∞`, re-exported under a name in this namespace so that the sampling lemmas of this
development can be stated against `Work.Maximal` vocabulary only. -/
noncomputable def mstHlMax (f : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  Commons.Analysis.Maximal.hlMax f x

@[simp] theorem mstHlMax_apply (f : ℝ → ℝ≥0∞) (x : ℝ) :
    mstHlMax f x = Commons.Analysis.Maximal.hlMax f x := rfl

/-- The **wide bump** `ϱ_s(ξ) = η(c_s · iwRep ξ)`.  Unlike the level bump `mstEta`, its scale does
not depend on `s` through the exponent `d − χ` but through the level denominator bound `Q_s`. -/
def mstWideBump (P : Polynomial ℤ) (_χ : ℝ) (η : ℝ → ℂ) (s : ℕ) : Circ → ℂ :=
  fun ξ => η (mstWideC P s * Work.BourgainPlan.Maximal.iwRep ξ)

@[simp] theorem mstWideBump_apply (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) (ξ : Circ) :
    mstWideBump P χ η s ξ = η (mstWideC P s * Work.BourgainPlan.Maximal.iwRep ξ) := rfl

/-- `mstWideC P s ≥ 1` (so the scaled-bump lemmas apply, and `c_s ≥ Q_s`). -/
theorem one_le_mstWideC (P : Polynomial ℤ) (s : ℕ) : 1 ≤ mstWideC P s := by
  rw [mstWideC]
  exact one_le_pow₀ (by
    have h : (1 : ℕ) ≤ Work.BourgainPlan.Maximal.mstQ' s :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Work.BourgainPlan.Maximal.mstQ'_pos s))
    exact_mod_cast h)

/-- The **annulus** of the level-`s` model: `𝒰(s+1) ∖ 𝒰(s)` (with the `𝒰(0) = ∅` convention). -/
def mstAnnulus (l : ℕ) (s : ℕ) : Finset Circ :=
  Work.BourgainPlan.Maximal.mstLevel l (s + 1) \ Work.BourgainPlan.Maximal.mstLevel l s

/-- **The wide level model symbol** `Ω^s_{2^k} = Σ_{β ∈ annulus} star (G β) · (star Φ_{2^k}) (·−β)
· ϱ_s(·−β)` (MST's `Ω^s_N` with `N = 2^k`, in the conjugated sign convention of the corpus). -/
def mstWideModel (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (k s : ℕ) : Circ → ℂ :=
  Work.BourgainPlan.Maximal.mstModelFn (fun β => star (Work.BourgainPlan.Maximal.mstG P β))
    (fun ζ => star (Work.BourgainPlan.Maximal.mstProf P (2 ^ k) ζ))
    (mstWideBump P χ η s) (mstAnnulus l s)

/-- The **unweighted wide arc sum** `Π̃_s = Σ_{β ∈ annulus} ϱ_s(·−β)` (MST's `Π̃_s`, the symbol
whose `ℓʳ` bound is Ionescu–Wainger's Theorem 3). -/
def mstWidePi (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) : Circ → ℂ :=
  Work.BourgainPlan.IonescuWainger.arcSymbol (mstWideBump P χ η s) (mstAnnulus l s)

/-- The **weighted wide arc sum** `Π̃^G_s = Σ_{β ∈ annulus} star (G β) ϱ_s(·−β)` (MST's (79)). -/
def mstWidePiG (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) : Circ → ℂ :=
  Work.BourgainPlan.Maximal.mstModelFn (fun β => star (Work.BourgainPlan.Maximal.mstG P β))
    (fun _ => 1) (mstWideBump P χ η s) (mstAnnulus l s)

@[simp] theorem mstWideModel_apply (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (k s : ℕ)
    (ξ : Circ) :
    mstWideModel P l χ η k s ξ
      = ∑ β ∈ mstAnnulus l s,
          star (Work.BourgainPlan.Maximal.mstG P β)
            * (star (Work.BourgainPlan.Maximal.mstProf P (2 ^ k) (ξ - β))
                * mstWideBump P χ η s (ξ - β)) := by
  simp only [mstWideModel, Work.BourgainPlan.Maximal.mstModelFn_apply]

@[simp] theorem mstWidePi_apply (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ)
    (ξ : Circ) :
    mstWidePi P l χ η s ξ = ∑ β ∈ mstAnnulus l s, mstWideBump P χ η s (ξ - β) := by
  simp only [mstWidePi, Work.BourgainPlan.IonescuWainger.arcSymbol_apply]

@[simp] theorem mstWidePiG_apply (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ)
    (ξ : Circ) :
    mstWidePiG P l χ η s ξ
      = ∑ β ∈ mstAnnulus l s,
          star (Work.BourgainPlan.Maximal.mstG P β) * mstWideBump P χ η s (ξ - β) := by
  simp only [mstWidePiG, Work.BourgainPlan.Maximal.mstModelFn_apply, one_mul]

/-- **`MemLp` and narrowness of the wide bump** (the two facts `memLp_scaled_bump` provides for the
scaled bump `η(c_s ·)`): `ϱ_s` is a.e. bounded, and it vanishes outside the ball of radius
`1/(2 c_s)`. -/
theorem mstWideBump_memLp_and_narrow (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ)
    (hηc : Continuous η) (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) (s : ℕ) :
    MemLp (mstWideBump P χ η s) ⊤ haarT ∧
      (∀ ξ : Circ, 1 / (2 * mstWideC P s) < ‖ξ‖ → mstWideBump P χ η s ξ = 0) := by
  have hc1 : (1 : ℝ) ≤ |mstWideC P s| := by
    have h := one_le_mstWideC P s
    rwa [abs_of_nonneg (le_trans zero_le_one h)]
  have h := Work.BourgainPlan.Maximal.memLp_scaled_bump (η := η) (c := mstWideC P s) hc1
    hηc hηsup
  have hcabs : |mstWideC P s| = mstWideC P s :=
    abs_of_nonneg (le_trans zero_le_one (one_le_mstWideC P s))
  rw [hcabs] at h
  exact h

/-- **The Mikhlin data of the wide bump** (`mikhlin_conditions_scaled_bump`): the fundamental-domain
lift of `ϱ_s` is `C²` with the Mikhlin constants of the original bump `η` (in particular uniform in
the level `s`), which is what `mikhlin_multiplier_lift` consumes to produce the multiplier-norm
hypothesis `IWMult`. -/
theorem mstWideBump_mikhlin (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hηc : ContDiff ℝ 2 η) (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) (s : ℕ) :
    ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstWideBump P χ η s)) ∧
      (∀ x : ℝ, ‖Work.BourgainPlan.Thm52.circleLift (mstWideBump P χ η s) x‖ ≤ M) ∧
      (∀ x : ℝ, |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift (mstWideBump P χ η s)) x‖
        ≤ M) ∧
      (∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2
        (Work.BourgainPlan.Thm52.circleLift (mstWideBump P χ η s)) x‖ ≤ M) := by
  have hc1 : (1 : ℝ) ≤ |mstWideC P s| := by
    have h := one_le_mstWideC P s
    rwa [abs_of_nonneg (le_trans zero_le_one h)]
  have h := Work.BourgainPlan.Maximal.mikhlin_conditions_scaled_bump (η := η) (M := M)
    (c := mstWideC P s) hM hc1 hηc hηbd hder1 hder2 hηsup
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- The `L^∞(𝕋)`-class of the wide level model symbol. -/
def mstWideModelCls (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (k s : ℕ)
    (h : MemLp (mstWideModel P l χ η k s) ⊤ haarT) : Lp ℂ ⊤ haarT :=
  h.toLp (mstWideModel P l χ η k s)

theorem mstWideModelCls_coeFn (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (k s : ℕ)
    (h : MemLp (mstWideModel P l χ η k s) ⊤ haarT) :
    (mstWideModelCls P l χ η k s h : Circ → ℂ) =ᵐ[haarT] mstWideModel P l χ η k s :=
  MemLp.coeFn_toLp _

/-- The `L^∞(𝕋)`-class of the weighted wide arc sum. -/
def mstWidePiGCls (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ)
    (h : MemLp (mstWidePiG P l χ η s) ⊤ haarT) : Lp ℂ ⊤ haarT :=
  h.toLp (mstWidePiG P l χ η s)

theorem mstWidePiGCls_coeFn (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ)
    (h : MemLp (mstWidePiG P l χ η s) ⊤ haarT) :
    (mstWidePiGCls P l χ η s h : Circ → ℂ) =ᵐ[haarT] mstWidePiG P l χ η s :=
  MemLp.coeFn_toLp _

/-- The `L^∞(𝕋)`-class of the unweighted wide arc sum. -/
def mstWidePiCls (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ)
    (h : MemLp (mstWidePi P l χ η s) ⊤ haarT) : Lp ℂ ⊤ haarT :=
  h.toLp (mstWidePi P l χ η s)

theorem mstWidePiCls_coeFn (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ)
    (h : MemLp (mstWidePi P l χ η s) ⊤ haarT) :
    (mstWidePiCls P l χ η s h : Circ → ℂ) =ᵐ[haarT] mstWidePi P l χ η s :=
  MemLp.coeFn_toLp _

end

end Work.Maximal
