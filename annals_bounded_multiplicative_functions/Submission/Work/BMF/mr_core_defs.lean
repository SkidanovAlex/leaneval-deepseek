import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.goodSet_E1_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.mrCore` — parameters and the good/bad sets of the `k = 0` core

This module fixes the vocabulary for the proof of `Work.BMF.CoreInput` (the critical regime of
`Work.BMF.mr_dirichlet_L2_direct`).

Two interval systems are used, exactly as in Matomäki–Radziwiłł (Annals 2016):

* the **fine** system `[P_f,Q_f]`, a power of `log Y`, with resolution `K_f = 200/ε`.  It defines
  the *good set* `𝒯₁` (the set of `t` where every polynomial `Q_{j,K_f}` is small) and, through
  `le:Rupest`, it bounds the number of well-spaced points of the bad set;
* the **coarse** system `[P_c,Q_c]`, with `log P_c = (log Y)^{47/48}`, ratio `logQ_c/logP_c = e^{B²/16}`
  and resolution `K_c = (log Y)^{1/48}`.  The ratio being a *constant* (not a power of `log Y`) is
  forced by the complex-valued case: the remainder bound `remPointwise_le` needs the sieve loss
  `Σ_{p ∈ [P_c,Q_c]} 1/p ≤ B²/8`.

The bad set `𝓤` is the complement of `𝒯₁` inside `[-S,S]`.
-/

set_option autoImplicit false

namespace Work.BMF

open MeasureTheory intervalIntegral
open scoped BigOperators

noncomputable section

/-- The logarithmic Dirichlet polynomial `Σ_{Y ≤ n ≤ 3Y} a n · n^{-(1+it)}`. -/
def dirPolyD (a : ℕ → ℂ) (Y t : ℝ) : ℂ :=
  ∑ n ∈ natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(1 + Complex.I * t))

/-- **The critical regime.**  For a constant `C₀` (the one furnished by the mean value theorem
`mv_sharp_dirichlet`), this is the Matomäki–Radziwiłł input in the range
`Y/H ≤ T ≤ (2C₀/ε)·(Y/H)` where the trivial mean value bound is insufficient:
`(Y/H)/T · ∫_{|t| ≤ 2T} ‖A(t)‖² ≤ ε/2`. -/
def CoreInput (θ C₀ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B C X₀ : ℝ, 0 < B ∧ 0 < C ∧ 1 ≤ X₀ ∧
    ∀ (g : ℕ → ℂ), g 1 = 1 →
    (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) → (∀ n, ‖g n‖ ≤ 1) →
    ∀ (Y H T : ℝ), X₀ ≤ Y → Y ^ θ ≤ H → H ≤ Y →
    (∀ u : ℝ, |u| ≤ C * Y / H →
      B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y) →
    Y / H ≤ T → T ≤ 2 * C₀ / ε * (Y / H) →
    (Y / H) / T * (∫ t in -(2 * T)..(2 * T), ‖dirPolyD g Y t‖ ^ 2) ≤ ε / 2

end

namespace mrCore

open MeasureTheory intervalIntegral
open scoped BigOperators

noncomputable section

/-- Matomäki–Radziwiłł's parameter `η` for the good set (kept for the exponent `α` below). -/
def etaF : ℝ := 1 / 48

/-- The exponent `α = 1/4 - 3η/2` of the good set (`α₁` of MR, with `j = 1`). -/
def alphaF : ℝ := 1 / 4 - 3 * etaF / 2

/-- `log P_f = 384 log log Y` (so `P_f = (log Y)^{384}`, MR's requirement `P_f ≥ (log M)^{8/η}`). -/
def logPf (Y : ℝ) : ℝ := 384 * Real.log (Real.log Y)

/-- The lower end of the fine interval: `P_f = (log Y)^{384}`. -/
def Pf (Y : ℝ) : ℝ := Real.exp (logPf Y)

/-- The ratio of the fine interval: `log Q_f / log P_f = (log Y)^{1/8}/ε`.

It is *Y-dependent* (a power of `log Y`, hence tending to infinity), which is what makes the
Buchstab error `(S+X₂)/X₁ · log P_f/log Q_f` vanish as `Y → ∞` — a quantity of the form
`ε/200` would be a genuine positive constant that no choice of `X₀` can dominate. -/
def Af (ε Y : ℝ) : ℝ := (Real.log Y) ^ (1 / 8 : ℝ) / ε

/-- The resolution of the fine system: `K_f = (log Y)^{1/4}/ε` (again tending to infinity). -/
def Kf (ε Y : ℝ) : ℝ := (Real.log Y) ^ (1 / 4 : ℝ) / ε

/-- `log Q_f = A_f · log P_f`. -/
def logQf (ε Y : ℝ) : ℝ := Af ε Y * logPf Y

/-- The upper end of the fine interval. -/
def Qf (ε Y : ℝ) : ℝ := Real.exp (logQf ε Y)

/-- `log P_c = (log Y)^{47/48}`. -/
def logPc (Y : ℝ) : ℝ := (Real.log Y) ^ (47 / 48 : ℝ)

/-- The lower end of the coarse interval. -/
def Pc (Y : ℝ) : ℝ := Real.exp (logPc Y)

/-- The coarse ratio `log Q_c / log P_c = e^{B²/64}` (a constant, so that the sieve losses
`Σ_{p ∈ [P_c,Q_c]} 1/p = log(logQ_c/logP_c) + O(1) = B²/64 + O(1) ≤ B²/16` stay under control,
while `Q_c = Y^{o(1)}` keeps the remainder ranges long enough for `remPointwise_le`). -/
def Ac (B : ℝ) : ℝ := Real.exp (B ^ 2 / 64)

/-- `log Q_c = A_c · log P_c`. -/
def logQc (B Y : ℝ) : ℝ := Ac B * logPc Y

/-- The upper end of the coarse interval. -/
def Qc (B Y : ℝ) : ℝ := Real.exp (logQc B Y)

/-- The resolution `K_c = (log Y)^{1/48}` of the coarse system. -/
def Kc (Y : ℝ) : ℝ := (Real.log Y) ^ (1 / 48 : ℝ)

/-- The good/bad threshold `Θ = (log Y)^{-100}`. -/
def Theta (Y : ℝ) : ℝ := (Real.log Y) ^ (-(100 : ℝ))

/-- The **good set** `𝒯₁`: the set of `t ∈ [-S,S]` where every fine polynomial is small. -/
def goodSet (ε : ℝ) (g : ℕ → ℂ) (Y S : ℝ) : Set ℝ :=
  Set.Icc (-S) S ∩ ⋂ j ∈ mrDirect.indexSet (Kf ε Y) (Pf Y) (Qf ε Y),
    {t : ℝ | ‖mrDirect.primePoly g (Kf ε Y) j t‖ ≤
      Real.exp (-(alphaF * (j : ℝ) / Kf ε Y))}

/-- The **bad set** `𝓤 = [-S,S] \ 𝒯₁`. -/
def badSet (ε : ℝ) (g : ℕ → ℂ) (Y S : ℝ) : Set ℝ :=
  Set.Icc (-S) S ∩ (goodSet ε g Y S)ᶜ

lemma measurableSet_goodSet (ε : ℝ) (g : ℕ → ℂ) (Y S : ℝ) :
    MeasurableSet (goodSet ε g Y S) := by
  unfold goodSet
  refine MeasurableSet.inter measurableSet_Icc ?_
  refine MeasurableSet.biInter (Finset.countable_toSet _) fun j _ => ?_
  exact (isClosed_le (Work.BMF.mr_direct.continuous_primePoly g (Kf ε Y) j).norm
    continuous_const).measurableSet

lemma measurableSet_badSet (ε : ℝ) (g : ℕ → ℂ) (Y S : ℝ) :
    MeasurableSet (badSet ε g Y S) := by
  unfold badSet
  exact measurableSet_Icc.inter (measurableSet_goodSet ε g Y S).compl

lemma badSet_subset_Icc (ε : ℝ) (g : ℕ → ℂ) (Y S : ℝ) :
    badSet ε g Y S ⊆ Set.Icc (-S) S := by
  intro t ht
  exact ht.1

lemma mem_goodSet_iff (ε : ℝ) (g : ℕ → ℂ) (Y S : ℝ) (t : ℝ) :
    t ∈ goodSet ε g Y S ↔ t ∈ Set.Icc (-S) S ∧
      ∀ j ∈ mrDirect.indexSet (Kf ε Y) (Pf Y) (Qf ε Y),
        ‖mrDirect.primePoly g (Kf ε Y) j t‖ ≤ Real.exp (-(alphaF * (j : ℝ) / Kf ε Y)) := by
  simp [goodSet]

lemma mem_badSet_iff (ε : ℝ) (g : ℕ → ℂ) (Y S : ℝ) (t : ℝ) :
    t ∈ badSet ε g Y S ↔ t ∈ Set.Icc (-S) S ∧ ¬ (∀ j ∈ mrDirect.indexSet (Kf ε Y) (Pf Y) (Qf ε Y),
        ‖mrDirect.primePoly g (Kf ε Y) j t‖ ≤ Real.exp (-(alphaF * (j : ℝ) / Kf ε Y))) := by
  unfold badSet
  rw [Set.mem_inter_iff, Set.mem_compl_iff, mem_goodSet_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ⟨h1, h⟩⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 h.2⟩

end

end mrCore

end Work.BMF
