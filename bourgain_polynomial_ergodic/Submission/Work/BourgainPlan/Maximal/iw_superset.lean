import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataCompDefs
import Submission.Work.BourgainPlan.IonescuWainger.TaoDefs
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs

/-!
# The one new analytic input of the MST route: Tao's `main` over the Ionescu–Wainger superset

`Submission/Work/BourgainPlan/Maximal/MST_ROUTE.md` (project lead, session 24) replaces the KMSZ
canonical-fraction route by **Mirek–Stein–Trojan §4**, in the scalar one-dimensional form, keeping
**Tao's set** `S_N = taoSetS ρ N` (Lemma `iwac`) and the major-arc set

`Σ_N := Σ_{≤k}(S_N) = sigmaLeFinset (taoSetS ρ N) k`,  `k = iwK ρ = ⌊2/ρ⌋ + 1`,

which *nests* in `N` and contains every Farey fraction of denominator `≤ N`
(`farey_cover_by_taoSetS`).  Everything else in that route is already in the corpus; the single new
analytic input is Tao's `main` (the Ionescu–Wainger multiplier theorem over `Σ_N`) with a **general
symbol** `m = Θ · η(·/ε)`: an arbitrary `L^{2r}(ℝ)`-bounded multiplier `Θ` times a bump of width
`ε ≤ ε_N = exp(−N^ρ)`.

## The interface (restated, session 28, owner H3-L53)

Three `Prop`s are exposed here, in decreasing strength/naturalness for the consumer:

* **`iwEndpoint2r`** — the *endpoint* case `p = 2r` (`r ≥ 2`) of the bound, with the hypotheses in
  the shape in which the Ionescu–Wainger theorem is actually available: the symbol is
  narrow (`supp ⊆ B(0,ε)`) and its **`ℝ`-multiplier norm at the exponent `2r`** is `≤ A` (both for
  the symbol and for its conjugate, the latter being what duality consumes).  This is the case that
  `Work.BourgainPlan.Maximal.hstep3_msw`/`main_real_of_inputs` prove (Tao's `main`).

* **`iwRangeBound`** — the same, for the whole range `p ∈ [(2r)', 2r]`, obtained from the endpoint
  by duality (the adjoint of `opArc ψ hψ E` is `opArc (star ∘ ψ) hψ E`, `KPWW.opArcLM_pairing`) and
  Riesz–Thorin (`Maximal.ellp_interpolation`); exactly the reduction "it suffices to prove
  `p = 2r`" of KMSZ §3.1, in the shape already implemented for the canonical family by
  `Work.BourgainPlan.KPWW.thm19_of_thm19At2r`.

* **`IWSupersetBound`** — the consumer-facing form: for **every** `p ∈ (1,∞)` the bound over `Σ_N`
  with a constant uniform in `N`, from **Mikhlin conditions** (the three `L^∞`-bounds
  `‖ψ‖, |x|‖ψ'‖, |x|²‖ψ''‖ ≤ A` for the fundamental-domain lift `circleLift ψ`, which
  `mikhlin_multiplier_lift` converts into the multiplier-norm hypothesis).  The exponent at which
  the multiplier norm is needed is `2 · max 2 (iwR p)`, and
  `2 · iwR p ≥ max (p, p')`, so the conclusion covers `p`.

A previous (unconsumed) version of `IWSupersetBound` stated the Mikhlin conditions for the
*periodisation* `x ↦ ψ (x : Circle)` and had no smoothness hypothesis; the present version states
them for the compactly supported lift `circleLift ψ` together with `ContDiff ℝ 2`, which is what the
Mikhlin multiplier theorem (`rescaled_mikhlin_multiplier_lp`) consumes.  The two are equivalent
given the narrowness of `ψ` (`ε ≤ 1/4` makes the periodisation and the lift agree).

This module contains only the interface: the parameters, the symbol, and the three `Prop`s.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- The depth `k = ⌊2/ρ⌋ + 1` of Tao's set `taoSetS ρ N` (Lemma `iwac`). -/
def iwK (ρ : ℝ) : ℕ := ⌊2 / ρ⌋₊ + 1

/-- The endpoint exponent of the Ionescu–Wainger theorem used by the MST route:
`r = max (⌈p/2⌉, ⌈p' / 2⌉)` with `p' = p/(p−1)`, so that `2r ≥ p` and `2r ≥ p'`. -/
def iwR (p : ℝ) : ℕ := max ⌈p / 2⌉₊ ⌈(p / (p - 1)) / 2⌉₊

/-- The small parameter `ε_N = exp(−N^ρ)` of Tao's Lemma `iwac`: for `N ≥ N₁(ρ,r)` the
tuple `(1, k, S_N, ε)` is `(r, 1/2)`-good for every `ε ≤ ε_N`. -/
def iwEps (ρ : ℝ) (N : ℕ) : ℝ := Real.exp (-((N : ℝ) ^ ρ))

/-- **The canonical real representative** of a circle point, in `Ioc (-1/2) (1/2]` (the lift used to
evaluate the `ℝ`-functions `Θ` and `η` at differences of circle points). -/
def iwRep : Work.BourgainPlan.IonescuWainger.Circle → ℝ :=
  AddCircle.liftIoc (1 : ℝ) (-(1/2)) (fun x : ℝ => x)

/-- **Tao's Ionescu–Wainger superset** `Σ_N = Σ_{≤k}(taoSetS ρ N)` as a `Finset` of the circle:
the union of the torsion subgroups `𝕋[Q_A]` over the `A ⊆ S_N` with `|A| ≤ k`. -/
def iwSigma (ρ : ℝ) (N : ℕ) : Finset Work.BourgainPlan.IonescuWainger.Circle :=
  sigmaLeFinset (taoSetS ρ N) (iwK ρ)

/-- **The symbol of the Ionescu–Wainger superset operator with a general multiplier**:
`ξ ↦ Σ_{β ∈ Σ_N} Θ(ξ − β) η((ξ − β)/ε)` — a sum of the *same* fine bump `η(·/ε)` over the arcs of
`Σ_N`, weighted by an arbitrary `ℝ`-multiplier `Θ`.  With `Θ ≡ 1` this is Tao's `main` for the
bump `η(·/ε)`; with `Θ` a bump it is the projection symbol of the KMSZ/MST decomposition. -/
def iwSymbol (ρ : ℝ) (N : ℕ) (Θ η : ℝ → ℂ) (ε : ℝ) :
    Work.BourgainPlan.IonescuWainger.Circle → ℂ :=
  fun ξ => ∑ β ∈ iwSigma ρ N,
    Θ (iwRep (ξ - β)) * η (iwRep (ξ - β) / ε)

/-- The symbol as an `L^∞(𝕋)`-class, given its a.e.-boundedness. -/
def iwSymbolLp (ρ : ℝ) (N : ℕ) (Θ η : ℝ → ℂ) (ε : ℝ)
    (h : MemLp (iwSymbol ρ N Θ η ε) ⊤ (AddCircle.haarAddCircle (T := 1))) :
    Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)) :=
  h.toLp (iwSymbol ρ N Θ η ε)

/-- **The `ℝ`-multiplier norm hypothesis (at the exponent `2r`) of Tao's `main`.**  The symbol `ψ`
on the circle, prolonged as the compactly supported lift `circleLift ψ`, is `L^{2r}(ℝ)`-bounded with
constant `A`.  This is the hypothesis shape of `Maximal.hstep3_msw`. -/
def IWMult (r : ℕ) (ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ) (A : ℝ) : Prop :=
  ∀ (g : ℝ → ℂ), MeasureTheory.Integrable g →
    ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
        (fun ξ : ℝ => Work.BourgainPlan.Thm52.circleLift ψ ξ
          * FourierTransform.fourier g ξ) x‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.volume
      ≤ ENNReal.ofReal (A ^ (2 * (r : ℝ)))
        * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.volume

/-- **The endpoint case `p = 2r` of Tao's `main` over `Σ_N`** (`r ≥ 2`): for a narrow symbol `ψ`
whose `ℝ`-multiplier norm at the exponent `2r` is `≤ A` — and likewise for its conjugate — the arc
multiplier over `Σ_N` is `ℓ^{2r}`-bounded with constant `C A`, uniformly in `N`. -/
def iwEndpoint2r : Prop :=
  ∀ (ρ : ℝ), 0 < ρ → ∀ r : ℕ, 2 ≤ r →
    ∃ C : ℝ, 0 < C ∧ ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ∀ (ε : ℝ), 0 < ε → ε ≤ iwEps ρ N →
      ∀ (ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
        (hψ : MeasureTheory.MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1))),
        (∀ (ξ : Work.BourgainPlan.IonescuWainger.Circle), ε < ‖ξ‖ → ψ ξ = 0) →
      ∀ (A : ℝ), 0 ≤ A → IWMult r ψ A → IWMult r (fun ξ => star (ψ ξ)) A →
      ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
        ∫⁻ n : ℤ, ‖Work.BourgainPlan.IonescuWainger.opArc ψ hψ (iwSigma ρ N) f hf n‖ₑ
            ^ (2 * (r : ℝ)) ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((C * A) ^ (2 * (r : ℝ)))
            * ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.Measure.count

/-- **The full range `p ∈ [(2r)', 2r]` of Tao's `main` over `Σ_N`** (`r ≥ 2`), the form obtained
from `iwEndpoint2r` by duality and Riesz–Thorin (KMSZ §3.1). -/
def iwRangeBound : Prop :=
  ∀ (ρ : ℝ), 0 < ρ → ∀ r : ℕ, 2 ≤ r →
    ∃ C : ℝ, 0 < C ∧ ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ∀ (ε : ℝ), 0 < ε → ε ≤ iwEps ρ N →
      ∀ (ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
        (hψ : MeasureTheory.MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1))),
        (∀ (ξ : Work.BourgainPlan.IonescuWainger.Circle), ε < ‖ξ‖ → ψ ξ = 0) →
      ∀ (A : ℝ), 0 ≤ A → IWMult r ψ A → IWMult r (fun ξ => star (ψ ξ)) A →
      ∀ p : ℝ, (2 * (r : ℝ)) / (2 * (r : ℝ) - 1) ≤ p → p ≤ 2 * (r : ℝ) →
      ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
        ∫⁻ n : ℤ, ‖Work.BourgainPlan.IonescuWainger.opArc ψ hψ (iwSigma ρ N) f hf n‖ₑ ^ p
            ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((C * A) ^ p)
            * ∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂MeasureTheory.Measure.count

/-- **The one new analytic input of the MST route** (Tao's `main`, arXiv:2008.05066, over the
supersets `Σ_N = Σ_{≤⌊2/ρ⌋+1}(S_N)` of Lemma `iwac`), in the real/`ℓᵖ(ℤ)` form, for narrow symbols
satisfying Mikhlin conditions: for every `ρ > 0` and `p ∈ (1, ∞)` there is `C = C_{p,ρ}` such that,
for all sufficiently large `N` and every symbol `ψ` supported in the ball of radius
`ε ≤ exp(−N^ρ)` whose compactly supported lift satisfies the Mikhlin conditions with constant `A`,
the arc multiplier over `Σ_N` obeys the `ℓᵖ`-bound with constant `C·A`.

Derivation: `iwEndpoint2r` (Tao's `main` at the endpoint `2r := 2 · max 2 (iwR p)`), then
`iwRangeBound` (duality + interpolation), with the multiplier-norm hypotheses produced from the
Mikhlin conditions by `mikhlin_multiplier_lift`. -/
def IWSupersetBound : Prop :=
  ∀ (ρ : ℝ), 0 < ρ → ∀ p : ℝ, 1 < p →
    ∃ C : ℝ, 0 < C ∧ ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ∀ (ε : ℝ), 0 < ε → ε ≤ iwEps ρ N →
      ∀ (ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
        (hψ : MeasureTheory.MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1))),
        (∀ (ξ : Work.BourgainPlan.IonescuWainger.Circle), ε < ‖ξ‖ → ψ ξ = 0) →
      ∀ (A : ℝ), 0 ≤ A →
        ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift ψ) →
        (∀ x : ℝ, ‖Work.BourgainPlan.Thm52.circleLift ψ x‖ ≤ A) →
        (∀ x : ℝ, |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift ψ) x‖ ≤ A) →
        (∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 (Work.BourgainPlan.Thm52.circleLift ψ) x‖ ≤ A) →
      ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
        ∫⁻ n : ℤ, ‖Work.BourgainPlan.IonescuWainger.opArc ψ hψ
            (iwSigma ρ N) f hf n‖ₑ ^ p ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((C * A) ^ p)
            * ∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂MeasureTheory.Measure.count

end

end Work.BourgainPlan.Maximal
