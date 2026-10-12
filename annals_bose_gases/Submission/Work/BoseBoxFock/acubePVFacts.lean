import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.CentreBox
import Submission.Work.BoseBoxFock.slotProj_hasCompactSupport
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.acubePVFacts` — the geometry of the corpus box, for the `PV`-calculus

The mode-projection `PV e a y = Σ_l e l a * conj (e l y)` of `SlotProjDefs` is used in this
chapter against the corpus's *own* localisation data `Work.BoseK15.corpusBox`: the modes `e l`
are supported in FS's box `Λ(ℓ) = ℓ • cell` (`corpusBox.boxL ℓ`) and the slot mean `aPC` averages
over the centred cube `Submission.BoseGases.acube ℓ`.  The two boxes coincide:

* `boxL_eq_acube` — `corpusBox.boxL ℓ = acube ℓ` for `0 < ℓ` (the unit cell of `corpusBox` is
  `[-1/2,1/2]³`, so its dilate is the centred cube);
* `thetaFun_eq_indicator` and the membership forms — FS's `θ = 1_Λ`;
* `PV_eq_zero_of_notMem_boxL` — the kernel vanishes in its second variable outside the box;
* `PV_eq_zero_of_notMem_boxL_fst` — and in its first variable.
-/

noncomputable section

open MeasureTheory Classical

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The box `corpusBox.boxL ℓ` is the centred cube -/

/-- The dilate of FS's unit cell is the centred cube of side `ℓ`. -/
theorem boxL_eq_acube {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Work.BoseK15.corpusBox.boxL ℓ = Submission.BoseGases.acube ℓ := by
  ext y
  rw [Work.BoseB4.BoxData.boxL, Set.mem_smul_set]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Submission.BoseGases.mem_acube_iff]
    intro m
    have hm : |u m| ≤ (1 / 2 : ℝ) := hu m
    have h1 : (ℓ * u m) ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := by
      rw [Set.mem_Icc]
      have hneg : -ℓ / 2 = -(ℓ / 2) := by ring
      constructor
      · rw [hneg]; nlinarith [abs_le.mp hm |>.1, hℓ]
      · nlinarith [abs_le.mp hm |>.2, hℓ]
    exact (by simpa using h1)
  · intro hy
    rw [Submission.BoseGases.mem_acube_iff] at hy
    refine ⟨ℓ⁻¹ • y, ?_, ?_⟩
    · intro m
      have hm : y m ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := hy m
      have habs : |y m| ≤ ℓ / 2 :=
        abs_le.mpr ⟨by linarith [hm.1], hm.2⟩
      have hval : (ℓ⁻¹ • y : Ω) m = ℓ⁻¹ * y m := by simp
      rw [hval, abs_mul, abs_inv, abs_of_pos hℓ]
      rw [inv_mul_le_iff₀ hℓ]
      linarith
    · ext m
      simp [hℓ.ne']

/-- The box is contained in the centred cube. -/
theorem boxL_subset_acube {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Work.BoseK15.corpusBox.boxL ℓ ⊆ Submission.BoseGases.acube ℓ :=
  (boxL_eq_acube hℓ).le

/-- The centred cube is contained in the box. -/
theorem acube_subset_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Submission.BoseGases.acube ℓ ⊆ Work.BoseK15.corpusBox.boxL ℓ :=
  (boxL_eq_acube hℓ).ge

/-- FS's `θ = 1_Λ` is the indicator of the box. -/
theorem thetaFun_apply (ℓ : ℝ) (x : Ω) :
    Work.BoseK15.corpusBox.thetaFun ℓ x = if x ∈ Work.BoseK15.corpusBox.boxL ℓ then 1 else 0 :=
  rfl

/-- `θ` is one on the box. -/
@[simp] theorem thetaFun_eq_one_of_mem {ℓ : ℝ} {x : Ω}
    (hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ) :
    Work.BoseK15.corpusBox.thetaFun ℓ x = 1 := by
  rw [thetaFun_apply, if_pos hx]

/-- `θ` vanishes off the box. -/
@[simp] theorem thetaFun_eq_zero_of_notMem {ℓ : ℝ} {x : Ω}
    (hx : x ∉ Work.BoseK15.corpusBox.boxL ℓ) :
    Work.BoseK15.corpusBox.thetaFun ℓ x = 0 := by
  rw [thetaFun_apply, if_neg hx]

/-! ## 2. The projection kernel vanishes off the box -/

/-- The projection kernel vanishes in its second variable outside the box, as soon as the modes
are supported in the box. -/
theorem PV_eq_zero_of_notMem_boxL {m : ℕ} {e : Fin m → Ω → ℂ} {ℓ : ℝ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {a y : Ω} (hy : y ∉ Work.BoseK15.corpusBox.boxL ℓ) : PV e a y = 0 :=
  PV_eq_zero_of_factors e (fun l => by
    by_contra h
    exact hy (hsupp l (Function.mem_support.mpr h)))

/-- The projection kernel vanishes in its first variable outside the box. -/
theorem PV_eq_zero_of_notMem_boxL_fst {m : ℕ} {e : Fin m → Ω → ℂ} {ℓ : ℝ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {a y : Ω} (ha : a ∉ Work.BoseK15.corpusBox.boxL ℓ) : PV e a y = 0 :=
  PV_eq_zero_of_fst e (fun l => by
    by_contra h
    exact ha (hsupp l (Function.mem_support.mpr h)))

/-- A product of `PV`-kernels over the slots of `U` vanishes unless every fibre coordinate lies
in the box. -/
theorem prod_PV_eq_zero_of_exists_notMem {m N : ℕ} {e : Fin m → Ω → ℂ} {ℓ : ℝ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {U : Finset (Fin N)} {x : Fin N → Ω} {z : (↑U → Ω)}
    (h : ∃ u : ↑U, z u ∉ Work.BoseK15.corpusBox.boxL ℓ) :
    (∏ u : ↑U, PV e (x u.1) (z u)) = 0 := by
  obtain ⟨u, hu⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ u) (PV_eq_zero_of_notMem_boxL hsupp hu)

end Work.BoseBoxFock
