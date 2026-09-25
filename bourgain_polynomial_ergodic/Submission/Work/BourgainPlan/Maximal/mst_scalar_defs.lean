import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.polyKernelZDefs
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.discAvgZC_multiplier_z
import Submission.Work.BourgainPlan.Maximal.opMul_sub
import Submission.Work.BourgainPlan.Maximal.major_arc_model
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs

/-!
# The scalar MST §3–§6 vocabulary (Mirek–Stein–Trojan §4, one-dimensional, scalar form)

`Submission/Work/BourgainPlan/Maximal/MST_ROUTE.md` and `MST_H3_CLAIMS.md` describe the route.  This
module holds the *objects* of the analytic chapter (the estimates themselves are stated and proved
in the sibling modules):

* `mstWeyl P N : 𝕋 → ℂ` — the density symbol `m_N` read on the circle through the canonical lift,
  `ξ ↦ polyWeylKernel P N (iwRep ξ)`.  By `khatZMult_coeFn_star_mstWeyl` (companion module) the
  `L^∞`-class of the density average `discAvgZC P N` takes the values `star (mstWeyl P N ξ)` a.e.
  (the conjugation is the sign convention of `khatZMult`, which is a sum of `fourierLp (-j)`).
* `mstProf P N : 𝕋 → ℂ` — the oscillatory profile `Φ_N` read on the circle,
  `ζ ↦ polyProfile P N (iwRep ζ)`.  A *lift* (and not `‖·‖`) is required: `Φ_N` is not even in its
  argument (only `Φ_N(-θ) = star (Φ_N θ)` holds), and the major-arc approximation compares the two
  values.
* `mstModelFn G Φ ψ Es` — the symbol of MST's major-arc model at one level,
  `ξ ↦ Σ_{β ∈ Es} G β · Φ (ξ - β) · ψ (ξ - β)` (KMSZ's weighted multifrequency extension
  `⟦G | Φ ψ⟧`, here written as an `arcSymbol` of the product function).
* `mstMinorCls` / `mstMinorOp` — the *minor-arc* operator `A_{2^n} - A_{2^n} Π_n` as the single
  multiplier with symbol `khatZMult P (2^n) · (1 - Ξ_n)`.

The companion files `mst_weyl_polylog`, `minor_arc_mst`, `major_to_levels_mst`, `level_l2_mst`,
`level_lr_*_mst` and `mst_assembly` state and prove the estimates.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-- The density symbol `m_N = N⁻¹ Σ_{n<N} e(· P(n))` (the Weyl kernel `polyWeylKernel`) read on
the circle through the canonical lift `iwRep`.  The a.e. value of the class `khatZMult P N` is its
conjugate (`khatZMult_coeFn_star_mstWeyl`). -/
def mstWeyl (P : Polynomial ℤ) (N : ℕ) : Work.BourgainPlan.IonescuWainger.Circle → ℂ :=
  fun ξ => polyWeylKernel P N (iwRep ξ)

@[simp] theorem mstWeyl_apply (P : Polynomial ℤ) (N : ℕ)
    (ξ : Work.BourgainPlan.IonescuWainger.Circle) :
    mstWeyl P N ξ = polyWeylKernel P N (iwRep ξ) := rfl

/-- The oscillatory profile `Φ_N(β) = ∫_0^1 e(β P(N s)) ds` (`polyProfile`) read on the circle
through the canonical lift `iwRep`. -/
def mstProf (P : Polynomial ℤ) (N : ℕ) : Work.BourgainPlan.IonescuWainger.Circle → ℂ :=
  fun ζ => polyProfile P N (iwRep ζ)

@[simp] theorem mstProf_apply (P : Polynomial ℤ) (N : ℕ)
    (ζ : Work.BourgainPlan.IonescuWainger.Circle) :
    mstProf P N ζ = polyProfile P N (iwRep ζ) := rfl

/-- **The symbol of the major-arc model at one level** (MST's `ν`, KMSZ's weighted multifrequency
extension `⟦G | Φ ψ⟧_Σ`): over the arc set `Es`, the weight `G β` times a profile `Φ` and a bump
`ψ`, both shifted by `β`.  With `Φ = mstProf P (2^n)`, `ψ = mstEta d χ η s` and
`Es = mstU l (s+1) \ mstU l s` this is MST's `ν^s_{2^n}`. -/
def mstModelFn (G : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (Φ ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (Es : Finset Work.BourgainPlan.IonescuWainger.Circle) :
    Work.BourgainPlan.IonescuWainger.Circle → ℂ :=
  arcSymbolW (fun β : Work.BourgainPlan.IonescuWainger.Circle => β) G Es
    (fun ζ => Φ ζ * ψ ζ)

@[simp] theorem mstModelFn_apply (G Φ ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (Es : Finset Work.BourgainPlan.IonescuWainger.Circle)
    (ξ : Work.BourgainPlan.IonescuWainger.Circle) :
    mstModelFn G Φ ψ Es ξ = ∑ β ∈ Es, G β * (Φ (ξ - β) * ψ (ξ - β)) := by
  simp only [mstModelFn, arcSymbolW_apply]

theorem mstModelFn_empty (G Φ ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ) :
    mstModelFn G Φ ψ ∅ = 0 := by
  funext ξ
  simp only [mstModelFn_apply, Finset.sum_empty, Pi.zero_apply]

/-- **The minor-arc symbol class**: the `L^∞`-class of `khatZMult P (2^n) · (1 - Ξ_n)`, i.e. of the
difference between the density average `A_{2^n}` and its level-`n` major-arc projection. -/
def mstMinorCls (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (hη : MemLp (mstEta d χ η n) ⊤ haarT) : Lp ℂ ⊤ haarT :=
  khatZMult P (2 ^ n) - khatZMult P (2 ^ n) • arcSymbolLp (mstEta d χ η n) hη (mstU l n)

/-- **The minor-arc operator** `A_{2^n} - A_{2^n} Π_n` as a single multiplier. -/
def mstMinorOp (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (hη : MemLp (mstEta d χ η n) ⊤ haarT) (g : ℤ → ℂ) (hg : Memℓp g 2) : ℤ → ℂ :=
  opMul (mstMinorCls P l d χ η n hη) g hg

/-- **The minor-arc operator is the difference of the density average and its projection**:
`A_{2^n} g - A_{2^n} (opArc η_n 𝒰(n) g)`. -/
theorem mstMinorOp_eq (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (hη : MemLp (mstEta d χ η n) ⊤ haarT) (g : ℤ → ℂ) (hg : Memℓp g 2) :
    mstMinorOp P l d χ η n hη g hg
      = discAvgZC P (2 ^ n) g
        - discAvgZC P (2 ^ n) (opArc (mstEta d χ η n) hη (mstU l n) g hg) := by
  unfold mstMinorOp mstMinorCls
  rw [(Work.BourgainPlan.IonescuWainger.opMul_sub (khatZMult P (2 ^ n))
        (khatZMult P (2 ^ n) • arcSymbolLp (mstEta d χ η n) hη (mstU l n)) g hg).symm]
  rw [opMul_khatZMult_eq_discAvgZC, discAvgZC_opArc_eq_opMul_smul]

/-- The minor-arc operator is `ℓ²`-valued. -/
theorem mstMinorOp_memℓp (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (hη : MemLp (mstEta d χ η n) ⊤ haarT) (g : ℤ → ℂ) (hg : Memℓp g 2) :
    Memℓp (mstMinorOp P l d χ η n hη g hg) 2 :=
  opMul_memℓp _ g hg

/-! ## The corrected Ionescu–Wainger input

`Work.BourgainPlan.Maximal.IWSupersetBound` (`Maximal/iw_superset.lean`) states its Mikhlin
hypotheses for the **periodisation** `x ↦ ψ (x : 𝕋)`, i.e. for a `1`-periodic function.  Those
hypotheses are unsatisfiable for a non-constant symbol: the derivative of a `1`-periodic function is
`1`-periodic, so `|x| ‖ψ' x‖` is unbounded unless `ψ' ≡ 0`, and then the support condition
`ε < ‖ξ‖ → ψ ξ = 0` forces `ψ = 0`.  (`Thm52/CircleLiftDefs.eq_zero_of_forall_notMem_Icc_neg_coe`
is the corpus's own vacuity lemma for this situation.)  Consequently the *only* symbols satisfying
`IWSupersetBound` are the zero ones, and the input gives no bound for a genuine bump.

The correct object is the fundamental-domain lift `Thm52.circleLift ψ`
(`x ↦ ψ (-(x : 𝕋))` on `Ioc (-1/2) (1/2]`, `0` outside), which is exactly the symbol against which
the hypotheses of the A-form of Tao's `main` (`hstep3_msw`, `main_real_of_inputs`) are phrased.
`IWSupersetBoundLift` below is that corrected form; every estimate of this chapter is stated
against it. -/

/-- **The Ionescu–Wainger bound over Tao's supersets `Σ_N`, corrected form.**  For every `ρ > 0`
and `p ∈ (1,∞)` there is `C` such that, for large `N`, every circle symbol `ψ` supported in the ball
of radius `ε ≤ exp(−N^ρ)`, whose fundamental-domain lift is `C²` with Mikhlin bounds of size `A`,
is an `ℓᵖ`-multiplier over `Σ_N = iwSigma ρ N` with constant `C·A`.

This is Tao's `main` (arXiv:2008.05066) in the form consumed by the MST route; it is the corrected
replacement of `Work.BourgainPlan.Maximal.IWSupersetBound` (see the section comment above). -/
def IWSupersetBoundLift : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ p : ℝ, 1 < p →
    ∃ C : ℝ, 0 < C ∧ ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ∀ {ε : ℝ}, 0 < ε → ε ≤ Real.exp (-(N : ℝ) ^ ρ) →
      ∀ (ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
        (hψ : MemLp ψ ⊤ haarT),
        ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift ψ) →
        ∀ {A : ℝ}, 0 ≤ A →
        (∀ x : ℝ, ‖Work.BourgainPlan.Thm52.circleLift ψ x‖ ≤ A) →
        (∀ x : ℝ, |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift ψ) x‖ ≤ A) →
        (∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2
          (Work.BourgainPlan.Thm52.circleLift ψ) x‖ ≤ A) →
        (∀ ξ : Work.BourgainPlan.IonescuWainger.Circle, ε < ‖ξ‖ → ψ ξ = 0) →
        ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
          ∫⁻ n : ℤ, ‖opArc ψ hψ (iwSigma ρ N) f hf n‖ₑ ^ p
              ∂MeasureTheory.Measure.count
            ≤ ENNReal.ofReal ((C * A) ^ p) *
                ∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂MeasureTheory.Measure.count

/-- **Weyl's inequality with a logarithmic loss** (the classical sharp Weyl inequality, with the
`N^{ε}` loss of `Commons.Analysis.ExponentialSums.weyl_inequality` improved to a polylogarithmic
one *at the same exponent* `2^{1−k}`): for a real polynomial of degree `k ≥ 2` whose leading
coefficient is within `1/q²` of the reduced rational `a/q`,

  `‖Σ_{x<N} e (f (M + x))‖ ≤ C (1 + log N)^c N (1/q + 1/N + 1/N^{k−1} + q/N^k)^{2^{1−k}}`.

This is the input that makes MST §4.1 work.  Notes on the exponent, in the light of an earlier
attempt at this very statement:

* the corpus's `weyl_inequality` has the *same* base and the *same* exponent `2^{1−k}` but carries
  the loss `N^{1+ε}`; in the regime where the bracket `1/q + 1/N + q/N^k` is only
  polylogarithmically small (which `q` up to `n^{−β}N^k` produces, and which the minor-arc
  estimate must cover) an exponential loss against a polylog decay is fatal, so the `N^{1+ε}` form
  cannot be used;
* the exponent must **not** be strengthened to MST's own `1/(2k²−2k+1)` (their eq. (13)): that is
  Wooley's Vinogradov-mean-value refinement (arXiv:1101.0574, Thm 1.5), which is *stronger* than
  Weyl for `k ≥ 8` (`1/113 > 1/128 = 2^{1−8}`) and is not derivable from Weyl differencing;
* the polylog loss at the classical exponent is what the classical proof of Weyl's inequality
  gives: the only place where `weyl_inequality` uses its `ε` is the absorption of the divisor
  factors (`card_divisors_le_rpow`, through `rho_sum_le`), and the sums that actually occur,
  `Σ_{m ≤ M} d(m)^{k−1}/m`, are `≲ (log M)^{2^{k−1}}` — polylogarithmic — even though `d(m)`
  itself has no polylog bound.  That divisor-sum estimate is the one new ingredient of the proof. -/
def MSTWeylBound : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∃ (C c : ℝ), 0 < C ∧ 0 < c ∧
    ∀ (M : ℤ) (N : ℕ) (a q : ℤ) (f : Polynomial ℝ),
      1 ≤ N → 1 ≤ q → Int.gcd a q = 1 → f.natDegree = k →
      |f.leadingCoeff - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      ‖∑ x ∈ Finset.range N,
          Complex.exp (↑(2 * Real.pi * f.eval ((M : ℝ) + (x : ℝ))) * Complex.I)‖
        ≤ C * (1 + Real.log (N : ℝ)) ^ c * (N : ℝ) *
            (1 / (q : ℝ) + 1 / (N : ℝ) + 1 / (N : ℝ) ^ (k - 1) + (q : ℝ) / (N : ℝ) ^ k) ^
              ((2 : ℝ) ^ (1 - (k : ℝ)))

end

end Work.BourgainPlan.Maximal
