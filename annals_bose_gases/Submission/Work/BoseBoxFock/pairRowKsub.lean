import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pairRowGDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowKsub` — the kernel-substitution glue of step (S2) of the `Q₂` row

Step (S2) of `FINDING_PotPairRows_exists.md` replaces the truncated pair kernel `K1exp` by its
limit `K1lim` in the pair blocks of the `Q₂` row.  The mechanics are always the same:

* the block's triple integral is rewritten by `block13_fibre_gen` / `blockTwo3_fibre_gen` /
  `blockII1_fibre_gen` / `slotKernel_fibre_gen` as `∫_w ∫_y K w y · 𝓖 w y` for a fibre function
  `𝓖` supported in the box squared;
* the pairing bound `K1exp_sub_K1lim_pairing_le` (PROVED) applies directly to `𝓖`;
* the fibre `L²` bounds `block13_fibre_L2`, `blockTwo3_fibre_L2`, `blockII1_fibre_L2`,
  `slotRow_fibre_L2` give a bound for `∫∫‖𝓖‖²`.

`int_pairing_sub_le` is the glue turning
`‖∫_{Λ²}(K`-`K')𝓖‖ ≤ ε√(∫_{Λ²}‖𝓖‖²)` into `‖∫∫K𝓖 `-` ∫∫K'𝓖‖ ≤ ε√C`.

Everything here is `sorry`-free.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- For a kernel/fibre pairing whose support lies in the box squared, the unrestricted iterated
integral equals the one restricted to the box twice. -/
theorem integral_integral_eq_iterated_boxL {ℓ : ℝ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E3 → E3 → G}
    (hsupp : Function.support (Function.uncurry f)
      ⊆ Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ)) :
    (∫ w : E3, ∫ y : E3, f w y)
      = ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ y in Work.BoseK15.corpusBox.boxL ℓ, f w y := by
  have hzero : ∀ w : E3, w ∉ Work.BoseK15.corpusBox.boxL ℓ → ∀ y : E3, f w y = 0 := by
    intro w hw y
    exact Function.notMem_support.mp
      (fun h : (w, y) ∈ Function.support (Function.uncurry f) => hw (hsupp h).1)
  have hzero2 : ∀ (w y : E3), y ∉ Work.BoseK15.corpusBox.boxL ℓ → f w y = 0 := by
    intro w y hy
    exact Function.notMem_support.mp
      (fun h : (w, y) ∈ Function.support (Function.uncurry f) => hy (hsupp h).2)
  have hinner : ∀ w : E3, (∫ y : E3, f w y)
      = ∫ y in Work.BoseK15.corpusBox.boxL ℓ, f w y := by
    intro w
    by_cases hw : w ∈ Work.BoseK15.corpusBox.boxL ℓ
    · exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Work.BoseK15.corpusBox.boxL ℓ) (f := fun y => f w y)
        (fun y hy => hzero2 w y hy)).symm
    · have h1 : (∫ y : E3, f w y) = 0 := by
        simp only [hzero w hw]
        simp
      have h2 : (∫ y in Work.BoseK15.corpusBox.boxL ℓ, f w y) = 0 := by
        simp only [hzero w hw]
        simp
      rw [h1, h2]
  rw [show (∫ w : E3, ∫ y : E3, f w y)
      = ∫ w : E3, ∫ y in Work.BoseK15.corpusBox.boxL ℓ, f w y from
    integral_congr_ae (Filter.Eventually.of_forall hinner)]
  exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Work.BoseK15.corpusBox.boxL ℓ)
    (f := fun w => ∫ y in Work.BoseK15.corpusBox.boxL ℓ, f w y)
    (fun w hw => by simp only [hzero w hw]; simp)).symm

/-- **The kernel-substitution bound.**  If the pairing of the kernel difference against the fibre
`𝓖` (supported in the box squared) is `≤ ε√(∫_{Λ²}‖𝓖‖²)` and `∫_{Λ²}‖𝓖‖² ≤ C`, then the two
kernel forms differ by at most `ε√C`. -/
theorem int_pairing_sub_le {ℓ ε C : ℝ} {𝓖 K K' : E3 → E3 → ℂ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hsupp : Function.support (Function.uncurry 𝓖) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ))
    (hPair : ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
               ∫ y in Work.BoseK15.corpusBox.boxL ℓ, (K w y - K' w y) * 𝓖 w y‖
        ≤ ε * Real.sqrt (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
            ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖𝓖 w y‖ ^ 2))
    (hGle : ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
              ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖𝓖 w y‖ ^ 2 ≤ C)
    (hIntK : MeasureTheory.Integrable (Function.uncurry (fun w y : E3 => K w y * 𝓖 w y))
      (volume : Measure (E3 × E3)))
    (hIntK' : MeasureTheory.Integrable (Function.uncurry (fun w y : E3 => K' w y * 𝓖 w y))
      (volume : Measure (E3 × E3))) :
    ‖(∫ w : E3, ∫ y : E3, K w y * 𝓖 w y) - (∫ w : E3, ∫ y : E3, K' w y * 𝓖 w y)‖
      ≤ ε * Real.sqrt C := by
  classical
  have HK : MeasureTheory.Integrable (fun z : E3 × E3 => K z.1 z.2 * 𝓖 z.1 z.2)
      (volume : Measure (E3 × E3)) := hIntK
  have HK' : MeasureTheory.Integrable (fun z : E3 × E3 => K' z.1 z.2 * 𝓖 z.1 z.2)
      (volume : Measure (E3 × E3)) := hIntK'
  have hsuppD : Function.support (Function.uncurry (fun w y : E3 => (K w y - K' w y) * 𝓖 w y))
      ⊆ Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ) := by
    intro z hz
    have h1 : Function.uncurry 𝓖 z ≠ 0 := by
      intro h
      exact hz (by
        show (K z.1 z.2 - K' z.1 z.2) * 𝓖 z.1 z.2 = 0
        rw [show 𝓖 z.1 z.2 = 0 from h, mul_zero])
    exact hsupp (Function.mem_support.mpr h1)
  have HD : MeasureTheory.Integrable (Function.uncurry (fun w y : E3 => (K w y - K' w y) * 𝓖 w y))
      (volume : Measure (E3 × E3)) := by
    have h := HK.sub HK'
    refine h.congr ?_
    refine Filter.Eventually.of_forall fun z => ?_
    simp only [Pi.sub_apply, Function.uncurry]
    ring
  have hsub : (∫ z : E3 × E3, K z.1 z.2 * 𝓖 z.1 z.2)
      - (∫ z : E3 × E3, K' z.1 z.2 * 𝓖 z.1 z.2)
      = ∫ z : E3 × E3, (K z.1 z.2 - K' z.1 z.2) * 𝓖 z.1 z.2 := by
    refine (MeasureTheory.integral_sub HK HK').symm.trans ?_
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply]
    ring
  have hbox : (∫ z : E3 × E3, (K z.1 z.2 - K' z.1 z.2) * 𝓖 z.1 z.2)
      = ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ y in Work.BoseK15.corpusBox.boxL ℓ, (K w y - K' w y) * 𝓖 w y :=
    (MeasureTheory.integral_integral HD).symm.trans
      (integral_integral_eq_iterated_boxL (f := fun w y : E3 => (K w y - K' w y) * 𝓖 w y) hsuppD)
  have key : (∫ w : E3, ∫ y : E3, K w y * 𝓖 w y) - (∫ w : E3, ∫ y : E3, K' w y * 𝓖 w y)
      = ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ y in Work.BoseK15.corpusBox.boxL ℓ, (K w y - K' w y) * 𝓖 w y := by
    rw [MeasureTheory.integral_integral hIntK, MeasureTheory.integral_integral hIntK']
    exact hsub.trans hbox
  rw [key]
  exact le_trans hPair (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hGle) hε)

end Work.BoseBoxFock
