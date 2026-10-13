/-
`Kop` of a compactly supported smooth function is a continuous function with compact support.

For `χ` a `C^∞` cut-off with `tsupport χ ⊆ U`, `U` open, and a `C^∞` function `tt` which
agrees with `tan (· 1)` on `U`, the function `x ↦ Kop (χ · φc) x` is a genuine continuous
function: on the open set `U` it agrees with the globally continuous expression in which the
multiplier `tan (· 1)` is replaced by `tt` (so that the pole of `tan` is never seen), while
off the (closed) topological support of `χ` it vanishes identically on a neighbourhood.  Its
topological support is therefore contained in the compact set `tsupport χ`.

This is the step which produces the compactly supported continuous representative `K` of
`Kop (χ · φc)` used to transport the localized distributional equation.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.EllipticEst.InteriorRegularity.Strip
import Submission.Work.EllipticEst.InteriorRegularity.LocalEquationAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `Kop` with the multiplier `tan (· 1)` replaced by an arbitrary multiplier `tt`. -/
def KopWith (tt ψ : E2 → ℂ) : E2 → ℂ := fun x =>
  - d0 (d0 ψ) x - d1 (d1 ψ) x - 5 * d0 ψ x + tt x * d1 ψ x + (tt x ^ 2 - 5) * ψ x

/-- `KopWith tt ψ` is continuous as soon as `ψ` together with its first and second directional
derivatives is continuous, and `tt` is continuous. -/
theorem continuous_kopWith {tt ψ : E2 → ℂ} (hψ : Continuous ψ)
    (hd0ψ : Continuous (d0 ψ)) (hd1ψ : Continuous (d1 ψ))
    (hd0d0ψ : Continuous (d0 (d0 ψ))) (hd1d1ψ : Continuous (d1 (d1 ψ)))
    (htt : Continuous tt) : Continuous (KopWith tt ψ) := by
  unfold KopWith
  have hA : Continuous (fun x : E2 => -d0 (d0 ψ) x - d1 (d1 ψ) x - 5 * d0 ψ x) :=
    (hd0d0ψ.neg.sub hd1d1ψ).sub (hd0ψ.const_mul 5)
  have hB : Continuous (fun x : E2 => tt x * d1 ψ x) := htt.mul hd1ψ
  have hC : Continuous (fun x : E2 => (tt x ^ 2 - 5) * ψ x) :=
    ((htt.pow 2).sub continuous_const).mul hψ
  exact (hA.add hB).add hC

theorem kopRepresentative {χ φc tt : Work.EllipticEst.InteriorRegularity.E2 → ℂ}
    {U : Set Work.EllipticEst.InteriorRegularity.E2} (hU : IsOpen U)
    (hχc : HasCompactSupport χ) (htsU : tsupport χ ⊆ U)
    (hχs : ∀ n : ℕ, ContDiff ℝ n χ) (hφs : ∀ n : ℕ, ContDiff ℝ n φc)
    (htts : ∀ n : ℕ, ContDiff ℝ n tt)
    (htt1 : ∀ x ∈ U, tt x = (Real.tan (x 1) : ℂ)) :
    ∃ K : Work.EllipticEst.InteriorRegularity.E2 → ℂ,
      Continuous K ∧ HasCompactSupport K ∧
        ∀ x, Work.EllipticEst.InteriorRegularity.Kop (fun y => χ y * φc y) x = K x := by
  have hψsm : ∀ n : ℕ, ContDiff ℝ n (fun y : E2 => χ y * φc y) :=
    fun n => (hχs n).mul (hφs n)
  have hψc : Continuous (fun y : E2 => χ y * φc y) := (hψsm 0).continuous
  have hd0ψc : Continuous (d0 (fun y : E2 => χ y * φc y)) := (Loc.contDiff_d0 hψsm 0).continuous
  have hd1ψc : Continuous (d1 (fun y : E2 => χ y * φc y)) := (Loc.contDiff_d1 hψsm 0).continuous
  have hd0d0ψc : Continuous (d0 (d0 (fun y : E2 => χ y * φc y))) :=
    (Loc.contDiff_d0 (fun n => Loc.contDiff_d0 hψsm n) 0).continuous
  have hd1d1ψc : Continuous (d1 (d1 (fun y : E2 => χ y * φc y))) :=
    (Loc.contDiff_d1 (fun n => Loc.contDiff_d1 hψsm n) 0).continuous
  have httc : Continuous tt := (htts 0).continuous
  have hKcontW : Continuous (KopWith tt (fun y : E2 => χ y * φc y)) :=
    continuous_kopWith hψc hd0ψc hd1ψc hd0d0ψc hd1d1ψc httc
  -- `Kop ψ` vanishes identically off the topological support of `χ`
  have hKzero : ∀ x : E2, x ∉ tsupport χ → Kop (fun y : E2 => χ y * φc y) x = 0 := by
    intro x hx
    have hW : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
    have hχ0W : ∀ y ∈ (tsupport χ)ᶜ, χ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
    have hψev : (fun y : E2 => χ y * φc y) =ᶠ[𝓝 x] 0 :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hx)
        (fun y hy => by simp [hχ0W y hy])
    have hψx : χ x * φc x = 0 := by rw [hχ0W x hx, zero_mul]
    have hd0 : d0 (fun y : E2 => χ y * φc y) x = 0 :=
      Loc.d0_eq_zero_of_eventuallyEq_zero hψev
    have hd1 : d1 (fun y : E2 => χ y * φc y) x = 0 :=
      Loc.d1_eq_zero_of_eventuallyEq_zero hψev
    have hd0ev : d0 (fun y : E2 => χ y * φc y) =ᶠ[𝓝 x] 0 :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hx)
        (fun y hy => Loc.d0_eq_zero_of_eventuallyEq_zero
          (Filter.eventuallyEq_of_mem (hW.mem_nhds hy) (fun z hz => by simp [hχ0W z hz])))
    have hd1ev : d1 (fun y : E2 => χ y * φc y) =ᶠ[𝓝 x] 0 :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hx)
        (fun y hy => Loc.d1_eq_zero_of_eventuallyEq_zero
          (Filter.eventuallyEq_of_mem (hW.mem_nhds hy) (fun z hz => by simp [hχ0W z hz])))
    have hd0d0 : d0 (d0 (fun y : E2 => χ y * φc y)) x = 0 :=
      Loc.d0_eq_zero_of_eventuallyEq_zero hd0ev
    have hd1d1 : d1 (d1 (fun y : E2 => χ y * φc y)) x = 0 :=
      Loc.d1_eq_zero_of_eventuallyEq_zero hd1ev
    have eK : Kop (fun y : E2 => χ y * φc y) x
        = - d0 (d0 (fun y : E2 => χ y * φc y)) x - d1 (d1 (fun y : E2 => χ y * φc y)) x
          - 5 * d0 (fun y : E2 => χ y * φc y) x
          + (Real.tan (x 1) : ℂ) * d1 (fun y : E2 => χ y * φc y) x
          + (((Real.tan (x 1)) ^ 2 - 5 : ℝ) : ℂ) * (χ x * φc x) := by
      rw [show Kop (fun y : E2 => χ y * φc y) = fun z : E2 =>
          - d0 (d0 (fun y : E2 => χ y * φc y)) z - d1 (d1 (fun y : E2 => χ y * φc y)) z
            - 5 * d0 (fun y : E2 => χ y * φc y) z
            + (Real.tan (z 1) : ℂ) * d1 (fun y : E2 => χ y * φc y) z
            + (((Real.tan (z 1)) ^ 2 - 5 : ℝ) : ℂ) * (χ z * φc z) from rfl]
    rw [eK, hd0d0, hd1d1, hd0, hd1, hψx]
    ring
  have hKsub : tsupport (Kop (fun y : E2 => χ y * φc y)) ⊆ tsupport χ := by
    show closure (Function.support (Kop (fun y : E2 => χ y * φc y))) ⊆ tsupport χ
    exact closure_minimal (fun x hx => by
      rw [Function.mem_support] at hx
      by_contra hxn
      exact hx (hKzero x hxn)) (isClosed_tsupport χ)
  have hKcc : HasCompactSupport (Kop (fun y : E2 => χ y * φc y)) :=
    IsCompact.of_isClosed_subset hχc (isClosed_tsupport (Kop (fun y : E2 => χ y * φc y))) hKsub
  -- on `U` the function agrees with the globally continuous `KopWith tt`
  have hKop_eq : ∀ w ∈ U, Kop (fun y : E2 => χ y * φc y) w
      = KopWith tt (fun y : E2 => χ y * φc y) w := by
    intro w hw
    have h1 : tt w = (Real.tan (w 1) : ℂ) := htt1 w hw
    have h2 : (((Real.tan (w 1)) ^ 2 - 5 : ℝ) : ℂ) = ((Real.tan (w 1) : ℂ)) ^ 2 - 5 := by
      push_cast
      ring
    have e1 : Kop (fun y : E2 => χ y * φc y) w
        = - d0 (d0 (fun y : E2 => χ y * φc y)) w - d1 (d1 (fun y : E2 => χ y * φc y)) w
          - 5 * d0 (fun y : E2 => χ y * φc y) w
          + (Real.tan (w 1) : ℂ) * d1 (fun y : E2 => χ y * φc y) w
          + (((Real.tan (w 1)) ^ 2 - 5 : ℝ) : ℂ) * (χ w * φc w) := by
      rw [show Kop (fun y : E2 => χ y * φc y) = fun z : E2 =>
          - d0 (d0 (fun y : E2 => χ y * φc y)) z - d1 (d1 (fun y : E2 => χ y * φc y)) z
            - 5 * d0 (fun y : E2 => χ y * φc y) z
            + (Real.tan (z 1) : ℂ) * d1 (fun y : E2 => χ y * φc y) z
            + (((Real.tan (z 1)) ^ 2 - 5 : ℝ) : ℂ) * (χ z * φc z) from rfl]
    have e2 : KopWith tt (fun y : E2 => χ y * φc y) w
        = - d0 (d0 (fun y : E2 => χ y * φc y)) w - d1 (d1 (fun y : E2 => χ y * φc y)) w
          - 5 * d0 (fun y : E2 => χ y * φc y) w
          + tt w * d1 (fun y : E2 => χ y * φc y) w
          + (tt w ^ 2 - 5) * (χ w * φc w) := by
      rw [show KopWith tt (fun y : E2 => χ y * φc y) = fun z : E2 =>
          - d0 (d0 (fun y : E2 => χ y * φc y)) z - d1 (d1 (fun y : E2 => χ y * φc y)) z
            - 5 * d0 (fun y : E2 => χ y * φc y) z
            + tt z * d1 (fun y : E2 => χ y * φc y) z
            + (tt z ^ 2 - 5) * (χ z * φc z) from rfl]
    rw [e1, e2, h1, ← h2]
  have hKcont : Continuous (Kop (fun y : E2 => χ y * φc y)) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · have hev : Kop (fun y : E2 => χ y * φc y)
          =ᶠ[𝓝 x] KopWith tt (fun y : E2 => χ y * φc y) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hKop_eq
      exact (continuousAt_congr hev).mpr hKcontW.continuousAt
    · have hxn : x ∉ tsupport χ := fun h => hx (htsU h)
      have hev : Kop (fun y : E2 => χ y * φc y) =ᶠ[𝓝 x] (fun _ : E2 => (0 : ℂ)) :=
        Filter.eventuallyEq_of_mem ((isClosed_tsupport χ).isOpen_compl.mem_nhds hxn)
          (fun y hy => hKzero y hy)
      exact hev.continuousAt
  exact ⟨Kop (fun y : E2 => χ y * φc y), hKcont, hKcc, fun x => rfl⟩

end Work.EllipticEst.InteriorRegularity.VT
