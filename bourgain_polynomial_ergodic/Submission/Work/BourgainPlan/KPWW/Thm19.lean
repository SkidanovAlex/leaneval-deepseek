import Mathlib
import Submission.Work.BourgainPlan.Maximal.canonical_arcs

/-!
# KMSZ Theorem 1.9 in the corpus's vocabulary (the target of the `KPWW` chapter)

Source: D. Kosz, M. Mirek, W. Słomian, J. Zhang, arXiv:2606.12663, Theorem 1.9 (`_lit2/k.txt`):

> Fix `r ∈ ℤ₊`.  There is `C_IW(r) ∈ ℝ₊` such that for every `N ≥ 10`, every
> `0 < ε ≤ (4rN^{2r})^{−1}`, every `m : ℝ → L(H₁,H₂)` supported on `εQ` with continuous
> multiplier bound `A_{2r}`, and every Ionescu–Wainger weight `G`,
> `‖T_ℤ[J_G|mK_{R_{≤N}}]f‖_{ℓᵖ} ≲_{d,r} N^{C_IW(r)/log log N} C_G(R_{≤N}) A_{2r}‖f‖_{ℓᵖ}`
> for `(2r)/(2r−1) ≤ p ≤ 2r`.

The qualitative consequence used by the KMSZ lane is `KPWW.Thm19`, below: for `d = 1`, `G ≡ 1`
(so `C_G = 1`), and a **bump** symbol `φ` (so that the discrete multiplier is `opArc φ hφ E`,
`E = canonicalFinset N`, with `T_ℤ[J_1|φK_E]`), the bound holds with the factor
`N^{C/log log N}·A`, where `A` is the continuous `Lᵖ(ℝ)` norm of the multiplier with symbol the
periodisation lift of `φ`.

Two comments.

* The hypothesis `hA` (the continuous bound) is **essential**: it is the `A_{2r}` of the source,
  and for an `L^∞`-bump it is *not* automatic (a sharp arc has the sinc kernel
  `sin(2πεx)/(πx) ∉ L¹(ℝ)`).  For the KMSZ bump `η_{≤m}` the source's `A_{2r}` is
  `‖𝓕⁻¹η‖_{L¹}`, **uniform in the dilation scale `m`**; see §5 of `KPWW/PLAN.md`.
  It is taken at the **endpoint exponent `2r`** — not at the exponent `p` of the conclusion — and
  is required for the bump and for its conjugate.  This is what the source uses (`A_{2r}`) and it is
  what makes the reduction "by duality and interpolation it suffices to prove `p = 2r`" of KMSZ
  §3.1 implementable; with the exponent `p` in place of `2r` the dual step is not available, since
  `‖T_ℝ[m]‖_{L^{(2r)'}}` is not controlled by `‖T_ℝ[m]‖_{L^{2r}}` (see `ASSEMBLY_MAP.md`).
* The exponent loss is recorded in the split form `∃ C, ∃ D` used by
  `Work.BourgainPlan.Maximal.IWProjectionBound`: `N^{C/log log N} ≤ D·2^{Cγl}` for `N = 2^l` and
  any `γ > 0` (the `D` absorbs the scales where `log log N` is not yet large); this is exactly the
  conversion performed in the KMSZ lane.
-/

open MeasureTheory
open scoped ENNReal BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.KPWW

/-- **KMSZ Theorem 1.9**, `d = 1`, unweighted (`G ≡ 1`), bump symbol, in the `opArc` vocabulary:
for every `r ≥ 1`, every `p ∈ [(2r)', 2r]`, every `N ≥ 10`, every bump `φ` of the circle supported
in the ball of radius `ε ≤ (4rN^{2r})^{−1}` whose continuous (periodised) multiplier is `L^p(ℝ)`-
bounded by `A`, and every finitely `ℓ²`-summable `f`,

`∫⁻_ℤ ‖opArc φ hφ (canonicalFinset N) f ‖^p ≤ (C·N^{C/log log N}·A)^p ∫⁻_ℤ ‖f‖^p`. -/
def Thm19 : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∃ C : ℝ, 0 < C ∧
    ∀ p : ℝ, (2 * (r : ℝ)) / (2 * (r : ℝ) - 1) ≤ p → p ≤ 2 * (r : ℝ) →
    ∀ N : ℕ, 10 ≤ N →
    ∀ ε : ℝ, 0 < ε → ε ≤ (4 * (r : ℝ) * (N : ℝ) ^ (2 * (r : ℝ)))⁻¹ →
    ∀ (φ : AddCircle (1 : ℝ) → ℂ)
      (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))),
      (∀ ξ : AddCircle (1 : ℝ), ε < ‖ξ‖ → φ ξ = 0) →
      ∀ (A : ℝ), 0 ≤ A →
      (∀ g : ℝ → ℂ, Integrable g →
        ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
            (fun ξ : ℝ => (φ (ξ : AddCircle (1 : ℝ)) : ℂ) * FourierTransform.fourier g ξ) x‖ₑ
              ^ (2 * (r : ℝ))
          ∂volume
          ≤ ENNReal.ofReal (A ^ (2 * (r : ℝ)))
              * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2 * (r : ℝ)) ∂volume) →
      (∀ g : ℝ → ℂ, Integrable g →
        ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
            (fun ξ : ℝ => (star (φ (ξ : AddCircle (1 : ℝ))) : ℂ) * FourierTransform.fourier g ξ) x‖ₑ
              ^ (2 * (r : ℝ))
          ∂volume
          ≤ ENNReal.ofReal (A ^ (2 * (r : ℝ)))
              * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2 * (r : ℝ)) ∂volume) →
      ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
        ∫⁻ n : ℤ, ‖Work.BourgainPlan.IonescuWainger.opArc φ hφ
            (Work.BourgainPlan.Maximal.canonicalFinset N) f hf n‖ₑ ^ p ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((C * (N : ℝ) ^ (C / Real.log (Real.log (N : ℝ))) * A) ^ p)
              * ∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂MeasureTheory.Measure.count

/-- **The endpoint case `p = 2r` of the Ionescu–Wainger bound** (KMSZ (1.11) at `p = 2r`, the
only case their §3.1 proves): the same statement as `Thm19` with the conclusion at the exponent
`2 * r`.  It is *weaker* than `Thm19` (which is `Thm19` instantiated at `p = 2r`), and KMSZ §3.1
shows the converse — "by duality and interpolation it suffices to prove `p = 2r`" — so
`Thm19At2r` is the honest target of the §3 chapter; see `ASSEMBLY_MAP.md`. -/
def Thm19At2r : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 10 ≤ N →
    ∀ ε : ℝ, 0 < ε → ε ≤ (4 * (r : ℝ) * (N : ℝ) ^ (2 * (r : ℝ)))⁻¹ →
    ∀ (φ : AddCircle (1 : ℝ) → ℂ)
      (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))),
      (∀ ξ : AddCircle (1 : ℝ), ε < ‖ξ‖ → φ ξ = 0) →
      ∀ (A : ℝ), 0 ≤ A →
      (∀ g : ℝ → ℂ, Integrable g →
        ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
            (fun ξ : ℝ => (φ (ξ : AddCircle (1 : ℝ)) : ℂ) * FourierTransform.fourier g ξ) x‖ₑ
              ^ (2 * (r : ℝ))
          ∂volume
          ≤ ENNReal.ofReal (A ^ (2 * (r : ℝ)))
              * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2 * (r : ℝ)) ∂volume) →
      (∀ g : ℝ → ℂ, Integrable g →
        ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
            (fun ξ : ℝ => (star (φ (ξ : AddCircle (1 : ℝ))) : ℂ) * FourierTransform.fourier g ξ) x‖ₑ
              ^ (2 * (r : ℝ))
          ∂volume
          ≤ ENNReal.ofReal (A ^ (2 * (r : ℝ)))
              * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2 * (r : ℝ)) ∂volume) →
      ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
        ∫⁻ n : ℤ, ‖Work.BourgainPlan.IonescuWainger.opArc φ hφ
            (Work.BourgainPlan.Maximal.canonicalFinset N) f hf n‖ₑ ^ (2 * (r : ℝ))
          ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((C * (N : ℝ) ^ (C / Real.log (Real.log (N : ℝ))) * A) ^ (2 * (r : ℝ)))
              * ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.Measure.count

/-- **The derivable (faithful) form of KMSZ (6.11)**: the ℓᵖ bound for the dyadic Ionescu–Wainger
projections over the canonical fractions, for a *family* of bumps of scales `2^{m}/4 … 2^{m}/2`
(the dilations of a fixed smooth bump `η` with `1_{[-1/4,1/4]} ≤ η ≤ 1_{(-1/2,1/2)}`, cf.
`KPWW.exists_real_bump` and `KPWW.family_bound_of_thm19`).

This is the version of `Work.BourgainPlan.Maximal.IWProjectionBound` that is a consequence of
`KPWW.Thm19`; the two differ in that `IWProjectionBound` quantifies over an *arbitrary* `L^∞` bump
with `‖φ‖ ≤ 1` and a support condition — a class for which the continuous norm `A_{2r}` of
Theorem 1.9 need not be finite (`KPWW/PLAN.md` §5 and §C).  Every consumer of `IWProjectionBound`
in the KMSZ lane instantiates the bump with the KMSZ bump `η_{≤m}`, so porting them to this Prop is
a pure re-pointing.  The extra `= 1` on the inner ball `2^{m}/4` is the property used by
(6.15)/(6.22) (`arcSymbol_canonical_eq_one` and the insertion `opArc_opArc`). -/
def IWFamilyBound : Prop :=
  ∀ p : ℝ, 1 < p → ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, 0 < γ → ∃ D : ℝ, 0 < D ∧
    ∃ (φ : ℕ → ℤ → AddCircle (1 : ℝ) → ℂ)
      (hφ : ∀ l m, MemLp (φ l m) ⊤ (AddCircle.haarAddCircle (T := 1))),
      (∀ l m ξ, ‖φ l m ξ‖ ≤ 1) ∧
      (∀ l m ξ, (2 : ℝ) ^ (m : ℤ) / 2 < ‖ξ‖ → φ l m ξ = 0) ∧
      (∀ l m ξ, ‖ξ‖ ≤ (2 : ℝ) ^ (m : ℤ) / 4 → φ l m ξ = 1) ∧
      ∀ l : ℕ, ∀ m : ℤ, (m : ℝ) ≤ -(6 * max p (p / (p - 1)) * ((l : ℝ) + 1)) →
      ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
        ∫⁻ n : ℤ, ‖Work.BourgainPlan.IonescuWainger.opArc (φ l m) (hφ l m)
            (Work.BourgainPlan.Maximal.canonicalFinset (2 ^ l)) f hf n‖ₑ ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((D * (2 : ℝ) ^ (C * γ * (l : ℝ))) ^ p)
            * ∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂MeasureTheory.Measure.count

end Work.BourgainPlan.KPWW
