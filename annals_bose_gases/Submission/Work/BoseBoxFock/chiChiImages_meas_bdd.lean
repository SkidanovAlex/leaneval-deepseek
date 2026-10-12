import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Submission.Work.BoseBoxFock.kernelImage_le
import Submission.Work.BoseBoxFock.pairRowS2Row
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiChiImages_meas_bdd`

**The lemma.**  For `0 < ℓ` and `W : ℝ³ → ℂ` measurable, bounded and compactly supported, the
lattice-image kernel

    chiChiImages ℓ W w y = χ_ℓ(w) χ_ℓ(y) Σ'_{m ≠ 0} W(w − y + ℓ•latVec m)

is measurable as a function of `(w,y)` and globally bounded.

**Why it is true.**  `W` has compact support, say `tsupport W ⊆ closedBall 0 R`.  If the term of
the sum at the lattice vector `m` does not vanish, then `χ_ℓ(w) ≠ 0` and `χ_ℓ(y) ≠ 0` force
`‖w‖, ‖y‖ ≤ ℓ/2`, hence `‖w − y‖ ≤ ℓ`, while `W(w − y + ℓ•latVec m) ≠ 0` forces
`‖w − y + ℓ•latVec m‖ ≤ R`.  Therefore `‖ℓ•latVec m‖ ≤ R + ℓ`, i.e. `‖latVec m‖ ≤ R/ℓ + 1`: the
sum is supported in the finite set `S = {m : ∀ i, m i ∈ [−(⌈R/ℓ+1⌉₊), ⌈R/ℓ+1⌉₊]}` of lattice
vectors of norm at most `⌈R/ℓ+1⌉₊`, *independently of `(w,y)`*.  So the `tsum` equals a finite sum
over the fixed `S` (`tsum_eq_sum`), which is measurable (each summand is a composition of the
continuous bump with `(w,y) ↦ w − y`) and bounded by `#S · chiSup² · max CW 0`.

Everything here is elementary; the only corpus inputs are the support estimate
`BoseGases.chiScale_support_le` and the pointwise sup-bound `BoseGases.abs_chiScale_le_chiSup`.
-/

namespace Work.BoseBoxFock

open MeasureTheory
open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem chiChiImages_meas_bdd {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hWm : Measurable W) (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : HasCompactSupport W) :
    Measurable (Function.uncurry (Work.BoseBoxFock.chiChiImages ℓ W))
      ∧ ∃ C : ℝ, ∀ w y : EuclideanSpace ℝ (Fin 3),
          ‖Work.BoseBoxFock.chiChiImages ℓ W w y‖ ≤ C := by
  -- the support radius of `W`
  obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport W ⊆ Metric.closedBall (0 : E3) R := by
    have hb : Bornology.IsBounded (tsupport W) :=
      (show IsCompact (tsupport W) from hWs).isBounded
    exact hb.subset_closedBall 0
  -- the (fixed!) finite set of lattice vectors that can contribute
  set S : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ : Fin 3 =>
    Finset.Icc (-(⌈R / ℓ + 1⌉₊ : ℤ)) ((⌈R / ℓ + 1⌉₊ : ℤ))) with hSdef
  -- every lattice vector outside `S` gives a vanishing term, uniformly in `(w,y)`
  have hterm_zero : ∀ (w y : E3) (m : Fin 3 → ℤ), m ∉ S →
      ((chiScale ℓ w : ℝ) : ℂ) * ((chiScale ℓ y : ℝ) : ℂ)
        * (if m = 0 then (0:ℂ) else W (w - y + ℓ • latVec m)) = 0 := by
    intro w y m hmS
    by_cases hm0 : m = 0
    · rw [if_pos hm0, mul_zero]
    rw [if_neg hm0]
    by_cases hχw : chiScale ℓ w = 0
    · rw [hχw]; simp
    by_cases hχy : chiScale ℓ y = 0
    · rw [hχy]; simp
    suffices h : W (w - y + ℓ • latVec m) = 0 by rw [h, mul_zero]
    by_contra hWne
    have hmem : w - y + ℓ • latVec m ∈ tsupport W :=
      subset_tsupport W (Function.mem_support.mpr hWne)
    have hz : ‖w - y + ℓ • latVec m‖ ≤ R := by
      have h := hR hmem
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
      exact h
    have hw : ‖w‖ ≤ ℓ/2 := chiScale_support_le hℓ hχw
    have hy : ‖y‖ ≤ ℓ/2 := chiScale_support_le hℓ hχy
    have hwy : ‖w - y‖ ≤ ℓ := by
      have h1 := norm_sub_le w y
      linarith
    have hlat : ‖latVec m‖ ≤ R / ℓ + 1 := by
      have h1 : ℓ * ‖latVec m‖ ≤ R + ℓ := by
        calc ℓ * ‖latVec m‖ = ‖(ℓ : ℝ) • latVec m‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
            _ = ‖(w - y + ℓ • latVec m) - (w - y)‖ := by congr 1; abel
            _ ≤ ‖w - y + ℓ • latVec m‖ + ‖w - y‖ := norm_sub_le _ _
            _ ≤ R + ℓ := by linarith
      have h2 : ‖latVec m‖ ≤ (R + ℓ) / ℓ := (le_div_iff₀ hℓ).mpr (by linarith)
      have h3 : (R + ℓ) / ℓ = R / ℓ + 1 := by field_simp
      linarith
    have hcoor : ∀ i : Fin 3,
        m i ∈ Finset.Icc (-(⌈R / ℓ + 1⌉₊ : ℤ)) ((⌈R / ℓ + 1⌉₊ : ℤ)) := by
      intro i
      rw [Finset.mem_Icc]
      have h1 : |((m i : ℤ) : ℝ)| ≤ ((⌈R / ℓ + 1⌉₊ : ℕ) : ℝ) := by
        have h2 : ‖(latVec m).ofLp i‖ ≤ ‖latVec m‖ := PiLp.norm_apply_le (latVec m) i
        rw [latVec_apply, Real.norm_eq_abs] at h2
        have h4 : R / ℓ + 1 ≤ ((⌈R / ℓ + 1⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
        linarith
      have h1' := abs_le.mp h1
      constructor
      · exact_mod_cast (show -((⌈R/ℓ+1⌉₊ : ℤ) : ℝ) ≤ ((m i : ℤ) : ℝ) by
          push_cast at h1' ⊢; linarith [h1'.1])
      · exact_mod_cast (show ((m i : ℤ) : ℝ) ≤ ((⌈R/ℓ+1⌉₊ : ℤ) : ℝ) by
          push_cast at h1' ⊢; linarith [h1'.2])
    exact hmS (by rw [hSdef, Fintype.mem_piFinset]; exact hcoor)
  -- hence the `tsum` is the finite sum over `S`, as functions of `(w,y)`
  have hfin_eq : (fun p : E3 × E3 =>
      ((chiScale ℓ p.1 : ℝ) : ℂ) * ((chiScale ℓ p.2 : ℝ) : ℂ)
        * (∑' m : Fin 3 → ℤ, if m = 0 then (0:ℂ) else W (p.1 - p.2 + ℓ • latVec m)))
      = fun p : E3 × E3 =>
        ∑ m ∈ S, ((chiScale ℓ p.1 : ℝ) : ℂ) * ((chiScale ℓ p.2 : ℝ) : ℂ)
          * (if m = 0 then (0:ℂ) else W (p.1 - p.2 + ℓ • latVec m)) := by
    funext p
    obtain ⟨w, y⟩ := p
    rw [← tsum_mul_left]
    refine tsum_eq_sum (fun m hmS => hterm_zero w y m hmS)
  have huncurry : Function.uncurry (chiChiImages ℓ W) = fun p : E3 × E3 =>
      ((chiScale ℓ p.1 : ℝ) : ℂ) * ((chiScale ℓ p.2 : ℝ) : ℂ)
        * (∑' m : Fin 3 → ℤ, if m = 0 then (0:ℂ) else W (p.1 - p.2 + ℓ • latVec m)) := by
    funext p
    rfl
  -- the finite sum is measurable
  have hmeas : Measurable (fun p : E3 × E3 =>
      ∑ m ∈ S, ((chiScale ℓ p.1 : ℝ) : ℂ) * ((chiScale ℓ p.2 : ℝ) : ℂ)
        * (if m = 0 then (0:ℂ) else W (p.1 - p.2 + ℓ • latVec m))) := by
    refine Finset.measurable_sum _ fun m _ => ?_
    have hχ1 : Measurable (fun p : E3 × E3 => ((chiScale ℓ p.1 : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp ((chiScale_continuous ℓ).measurable.comp measurable_fst)
    have hχ2 : Measurable (fun p : E3 × E3 => ((chiScale ℓ p.2 : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp ((chiScale_continuous ℓ).measurable.comp measurable_snd)
    refine (hχ1.mul hχ2).mul ?_
    have hbase : Measurable (fun p : E3 × E3 => W (p.1 - p.2 + ℓ • latVec m)) :=
      hWm.comp ((continuous_fst.sub continuous_snd).add continuous_const).measurable
    by_cases hm0 : m = 0
    · have hthis : (fun p : E3 × E3 => if m = 0 then (0 : ℂ)
            else W (p.1 - p.2 + ℓ • latVec m)) = fun _ : E3 × E3 => (0 : ℂ) := by
        funext p; rw [if_pos hm0]
      rw [hthis]; exact measurable_const
    · have hthis : (fun p : E3 × E3 => if m = 0 then (0 : ℂ)
            else W (p.1 - p.2 + ℓ • latVec m))
          = fun p : E3 × E3 => W (p.1 - p.2 + ℓ • latVec m) := by
        funext p; rw [if_neg hm0]
      rw [hthis]; exact hbase
  constructor
  · rw [huncurry, hfin_eq]; exact hmeas
  · -- and bounded, by `#S · chiSup² · max CW 0`
    obtain ⟨CW, hCW⟩ := hWb
    refine ⟨(S.card : ℝ) * (chiSup * chiSup * max CW 0), fun w y => ?_⟩
    have hsplit : chiChiImages ℓ W w y
        = ∑ m ∈ S, ((chiScale ℓ w : ℝ) : ℂ) * ((chiScale ℓ y : ℝ) : ℂ)
            * (if m = 0 then (0:ℂ) else W (w - y + ℓ • latVec m)) := by
      have h1 := congrFun hfin_eq (w, y)
      simpa [Function.uncurry, chiChiImages] using h1
    rw [hsplit]
    have hbase : ∀ m : Fin 3 → ℤ,
        ‖((chiScale ℓ w : ℝ) : ℂ) * ((chiScale ℓ y : ℝ) : ℂ)
          * (if m = 0 then (0:ℂ) else W (w - y + ℓ • latVec m))‖
        ≤ chiSup * chiSup * max CW 0 := by
      intro m
      have h1 : ‖((chiScale ℓ w : ℝ) : ℂ)‖ ≤ chiSup := by
        simpa using abs_chiScale_le_chiSup ℓ w
      have h2 : ‖((chiScale ℓ y : ℝ) : ℂ)‖ ≤ chiSup := by
        simpa using abs_chiScale_le_chiSup ℓ y
      have h3 : ‖(if m = 0 then (0:ℂ) else W (w - y + ℓ • latVec m))‖ ≤ max CW 0 := by
        by_cases hm : m = 0
        · rw [if_pos hm, norm_zero]; exact le_max_right _ _
        · rw [if_neg hm]; exact le_trans (hCW _) (le_max_left _ _)
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) chiSup_pos.le) h3 (norm_nonneg _)
        (mul_nonneg chiSup_pos.le chiSup_pos.le)
    calc ‖∑ m ∈ S, ((chiScale ℓ w : ℝ) : ℂ) * ((chiScale ℓ y : ℝ) : ℂ)
            * (if m = 0 then (0:ℂ) else W (w - y + ℓ • latVec m))‖
        ≤ ∑ m ∈ S, ‖((chiScale ℓ w : ℝ) : ℂ) * ((chiScale ℓ y : ℝ) : ℂ)
            * (if m = 0 then (0:ℂ) else W (w - y + ℓ • latVec m))‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ S, (chiSup * chiSup * max CW 0) := Finset.sum_le_sum fun m _ => hbase m
      _ = (S.card : ℝ) * (chiSup * chiSup * max CW 0) := by
          rw [Finset.sum_const, nsmul_eq_mul]

end Work.BoseBoxFock
