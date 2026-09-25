import Mathlib
import Submission.Work.BourgainPlan.Maximal.iw_superset

/-!
# The MST §2–§3 vocabulary: level sets `𝒰(n)`, the level bumps `η_n`, the arc symbol `Ξ_n`

`Submission/Work/BourgainPlan/Maximal/MST_ROUTE.md` §2 fixes the parameters of the
Mirek–Stein–Trojan §4 route:

* `ρ = 1/(10 l)` for a large natural `l` (so the level sets have size `≤ e^{C n^{1/10}}`);
* the level sets `𝒰(n) := Σ_{n^l} = Σ_{≤k}(taoSetS ρ (n^l))` — Tao's Ionescu–Wainger superset at
  the scale `N = n^l` (`iwSigma (mstRho l) (n ^ l)`);
* the level bump `η_n(ξ) := η(2^{n(d−χ)} ξ)` of width `2^{−n(d−χ)}` (`χ ∈ (0,1/10)`), with `η` the
  fixed smooth bump equal to `1` on `[−1/4,1/4]` and supported in `[−1/2,1/2]`;
* the arc symbol `Ξ_n(ξ) := Σ_{β ∈ 𝒰(n)} η_n(ξ − β)` (`mstXi`), i.e. the multiplier of the
  *major-arc projection* at level `n`.

The point of `𝒰(n)` is that it is **nested** (`sigmaN_nested`) and covers every Farey fraction of
denominator `≤ n^l` (`sigmaN_contains_farey`), that its points are `exp(−2 n^{1/10})`-separated
(`sigmaN_separated`), and that its cardinality and denominators are `≤ exp(n^{1/10})`
(`sigmaN_card_le`, `sigmaN_denom_le`).  Consequently the bump supports `η_n(· − β)` are pairwise
disjoint and `Ξ_n` equals `1` on the `2^{−n(d−χ)}/4`-neighbourhood of `𝒰(n)`.

The operators of the route are then

* the **minor-arc** multiplier `m_{2^n}(1 − Ξ_n)` (§3), where `m_N` is the Weyl kernel
  (`polyWeylKernel P N`, or the `ℤ`-multiplier class `khatZMult P N`);
* the **major-arc model** `ν_n = Σ_{β = a/q ∈ 𝒰(n)} G(a/q) Φ_{2^n}(ξ − β) η_n(ξ − β)` (§4),
  with `G = polyWeight`, `Φ_N = polyProfile`;
* its **level pieces** `ν_n^s` over `𝒰(s+1) ∖ 𝒰(s)` (§5).

The single analytic input is `Work.BourgainPlan.Maximal.IWSupersetBound` (the Mikhlin form of Tao's
`main` over `Σ_N`); `hstep3_msw` discharges the step-3 hypothesis of `main_real_of_inputs`, which
is how that `Prop` is to be derived.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- The MST level parameter `ρ = 1/(10 l)`. -/
def mstRho (l : ℕ) : ℝ := 1 / (10 * (l : ℝ))

/-- The MST level sets `𝒰(n) := Σ_{n^l} = Σ_{≤k}(taoSetS ρ (n^l))` with `ρ = 1/(10 l)`. -/
def mstU (l : ℕ) (n : ℕ) : Finset Work.BourgainPlan.IonescuWainger.Circle :=
  iwSigma (mstRho l) (n ^ l)

/-- The MST level bump `η_n(ξ) = η(2^{n(d−χ)} ξ)`, read on the circle through the canonical lift
`iwRep` (the bump is supported in a ball of radius `< 1/2`, so the lift is unambiguous there). -/
def mstEta (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ) :
    Work.BourgainPlan.IonescuWainger.Circle → ℂ :=
  fun ξ => η ((2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - χ)) * iwRep ξ)

/-- The MST arc symbol `Ξ_n(ξ) = Σ_{β ∈ 𝒰(n)} η_n(ξ − β)`: the multiplier of the level-`n`
major-arc projection. -/
def mstXi (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ) :
    Work.BourgainPlan.IonescuWainger.Circle → ℂ :=
  arcSymbol (mstEta d χ η n) (mstU l n)

@[simp] theorem mstXi_apply (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (ξ : Work.BourgainPlan.IonescuWainger.Circle) :
    mstXi l d χ η n ξ = ∑ β ∈ mstU l n, mstEta d χ η n (ξ - β) := rfl

@[simp] theorem mstEta_apply (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (ξ : Work.BourgainPlan.IonescuWainger.Circle) :
    mstEta d χ η n ξ = η ((2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - χ)) * iwRep ξ) := rfl

@[simp] theorem mstU_apply (l n : ℕ) :
    mstU l n = iwSigma (mstRho l) (n ^ l) := rfl

end

end Work.BourgainPlan.Maximal
