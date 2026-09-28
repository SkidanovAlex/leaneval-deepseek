import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MMDefs
import Submission.Work.HP.MMVec
import Submission.Work.HP.MMReindex
import Submission.Work.HP.DmixAux.Basic
import Submission.Work.HP.DmixAux.FilterSumNeg
import Submission.Work.HP.DmixAux.ZxNeNeg

/-!
# The diagonal subtraction for `D^mix` (node `PerA`)

`NV * NVloc - DeltaMix` is the summand of `D^mix` at a single coefficient vector `a`.  The
identity proved here rewrites it as a sum over *pairs* `(x,y)` with `x ∈ Zx`, `y ∈ Zy`,
`y ≠ ±x`, which is the form needed to reindex `D^mix` as a sum over `Ω_{d,n}(B)`.

Concretely, with `Zf = Zx_finite d n a B`.toFinset`, `Yf = (Zy_finite d n a B).toFinset`,
`α = Real.log B`, `W = bigW (wOf B)`:

* `NV = ½ #Zf`,
  `NVloc = ½ (αW/‖a‖) ∑_{y∈Yf} 1/‖ν(y)‖`,
  `DeltaMix = ½ (αW/‖a‖) ∑_{x∈Zf} 1/‖ν(x)‖`;
* hence `NV * NVloc - DeltaMix = ½(αW/‖a‖) (½ #Zf · Σ_Y − Σ_Z)`;
* for `x ∈ Zx` we have `±x ∈ Zy` (`Zx ⊆ Zy` for `B > 1`, and `Zx` is invariant under `x ↦ -x`),
  `x ≠ -x` (primitivity) and `‖ν(-x)‖ = ‖ν(x)‖`, so the sum over `Yf.filter (y ≠ x ∧ y ≠ -x)`
  is `Σ_Y − 2/‖ν(x)‖`;
* `1/(‖a‖‖ν(y)‖) = (1/‖a‖)(1/‖ν(y)‖)` and a final `ring` step.
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Work.HP.DmixAux

variable (d n : ℕ)

/-! ## Auxiliary facts -/

/-- The double sum over `Zf × (Yf.filter (y ≠ x ∧ y ≠ -x))`, the diagonal `{±x}` removed. -/
lemma sum_sum_filter_neg {β : Type*} [DecidableEq β] [Neg β] (Zf Yf : Finset β) (φ : β → ℝ)
    (hsub : ∀ x ∈ Zf, x ∈ Yf) (hneg : ∀ x ∈ Zf, -x ∈ Yf) (hne : ∀ x ∈ Zf, x ≠ -x)
    (heven : ∀ x ∈ Zf, φ (-x) = φ x) :
    ∑ x ∈ Zf, ∑ y ∈ Yf.filter (fun y => y ≠ x ∧ y ≠ -x), φ y
      = (Zf.card : ℝ) * (∑ y ∈ Yf, φ y) - 2 * ∑ x ∈ Zf, φ x := by
  have h1 : ∀ x ∈ Zf, ∑ y ∈ Yf.filter (fun y => y ≠ x ∧ y ≠ -x), φ y
      = ∑ y ∈ Yf, φ y - 2 * φ x :=
    fun x hx => FilterSumNeg Yf x φ (hsub x hx) (hneg x hx) (hne x hx) (heven x hx)
  calc ∑ x ∈ Zf, ∑ y ∈ Yf.filter (fun y => y ≠ x ∧ y ≠ -x), φ y
      = ∑ x ∈ Zf, (∑ y ∈ Yf, φ y - 2 * φ x) := Finset.sum_congr rfl h1
    _ = ∑ x ∈ Zf, (∑ y ∈ Yf, φ y) - ∑ x ∈ Zf, (2 * φ x) := by
        rw [Finset.sum_sub_distrib]
    _ = (Zf.card : ℝ) * (∑ y ∈ Yf, φ y) - 2 * ∑ x ∈ Zf, φ x := by
        rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]

/-! ## `NV`, `NVloc`, `DeltaMix` as `Finset` sums -/

lemma NV_eq_finset [DecidableEq (Mon d n)] (a : Mon d n → ℤ) (B : ℝ) :
    NV d n a B = (1 / 2) * (((Zx_finite d n a B).toFinset.card : ℕ) : ℝ) := by
  rw [NV]
  congr 1
  have hset : ({x ∈ Xi d n B | formEval d n a x = 0} : Set (Fin (n + 1) → ℤ))
      = ↑((Zx_finite d n a B).toFinset) := by
    ext x
    simp [Work.HP.Zx]
  rw [hset, Set.ncard_coe_finset]

lemma NVloc_eq_finset [DecidableEq (Mon d n)] (a : Mon d n → ℤ) (B : ℝ) :
    NVloc d n a B = (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a) *
      ∑ y ∈ (Zy_finite d n a B).toFinset, 1 / eNorm (veronese d n y) := by
  rw [NVloc]
  congr 1
  change (∑ᶠ y ∈ Zy d n a B, 1 / eNorm (veronese d n y))
      = ∑ y ∈ (Zy_finite d n a B).toFinset, 1 / eNorm (veronese d n y)
  rw [finsum_mem_eq_finite_toFinset_sum _ (Zy_finite d n a B)]

lemma DeltaMix_eq_finset [DecidableEq (Mon d n)] (a : Mon d n → ℤ) (B : ℝ) :
    DeltaMix d n a B = (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a) *
      ∑ x ∈ (Zx_finite d n a B).toFinset, 1 / eNorm (veronese d n x) := by
  rw [DeltaMix]
  congr 1
  change (∑ᶠ x ∈ Zx d n a B, 1 / eNorm (veronese d n x))
      = ∑ x ∈ (Zx_finite d n a B).toFinset, 1 / eNorm (veronese d n x)
  rw [finsum_mem_eq_finite_toFinset_sum _ (Zx_finite d n a B)]

/-! ## The main identity -/

theorem PerA (d n : ℕ) [DecidableEq (Mon d n)] (a : Mon d n → ℤ) (B : ℝ) (hB : 1 < B) :
    NV d n a B * NVloc d n a B - DeltaMix d n a B
      = (Real.log B * (bigW (wOf B) : ℝ) / 4) *
        ∑ x ∈ (Zx_finite d n a B).toFinset,
          ∑ y ∈ ((Zy_finite d n a B).toFinset).filter (fun y => y ≠ x ∧ y ≠ -x),
            1 / (eNorm a * eNorm (veronese d n y)) := by
  classical
  have hNV := NV_eq_finset d n a B
  have hNVl := NVloc_eq_finset d n a B
  have hDM := DeltaMix_eq_finset d n a B
  rw [hNV, hNVl, hDM]
  -- the diagonal subtraction
  have hsub : ∀ x ∈ (Zx_finite d n a B).toFinset, x ∈ (Zy_finite d n a B).toFinset := by
    intro x hx
    exact (Set.Finite.mem_toFinset (Zy_finite d n a B)).mpr
      (Zx_subset_Zy d n a B hB ((Set.Finite.mem_toFinset (Zx_finite d n a B)).mp hx))
  have hneg : ∀ x ∈ (Zx_finite d n a B).toFinset, -x ∈ (Zy_finite d n a B).toFinset := by
    intro x hx
    have hxZ : x ∈ Zx d n a B := (Set.Finite.mem_toFinset (Zx_finite d n a B)).mp hx
    exact (Set.Finite.mem_toFinset (Zy_finite d n a B)).mpr
      (Zx_subset_Zy d n a B hB ((Zx_neg_mem d n a B x).mp hxZ))
  have hne : ∀ x ∈ (Zx_finite d n a B).toFinset, x ≠ -x := by
    intro x hx
    exact ZxNeNeg d n a B ((Set.Finite.mem_toFinset (Zx_finite d n a B)).mp hx)
  have heven : ∀ x ∈ (Zx_finite d n a B).toFinset,
      (fun y : Fin (n + 1) → ℤ => 1 / (eNorm a * eNorm (veronese d n y))) (-x)
        = (fun y : Fin (n + 1) → ℤ => 1 / (eNorm a * eNorm (veronese d n y))) x := by
    intro x _
    show 1 / (eNorm a * eNorm (veronese d n (-x))) = 1 / (eNorm a * eNorm (veronese d n x))
    rw [eNorm_veronese_neg]
  have hkey := sum_sum_filter_neg (Zf := (Zx_finite d n a B).toFinset)
    (Yf := (Zy_finite d n a B).toFinset)
    (φ := fun y : Fin (n + 1) → ℤ => 1 / (eNorm a * eNorm (veronese d n y)))
    hsub hneg hne heven
  rw [hkey]
  -- factor `1/‖a‖` out of the two sums
  have hSY : ∑ y ∈ (Zy_finite d n a B).toFinset, 1 / (eNorm a * eNorm (veronese d n y))
      = (1 / eNorm a) *
        ∑ y ∈ (Zy_finite d n a B).toFinset, 1 / eNorm (veronese d n y) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [one_div, mul_inv, one_div, one_div]
  have hSZ : ∑ x ∈ (Zx_finite d n a B).toFinset, 1 / (eNorm a * eNorm (veronese d n x))
      = (1 / eNorm a) *
        ∑ x ∈ (Zx_finite d n a B).toFinset, 1 / eNorm (veronese d n x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [one_div, mul_inv, one_div, one_div]
  rw [hSY, hSZ]
  ring

end Work.HP.DmixAux
