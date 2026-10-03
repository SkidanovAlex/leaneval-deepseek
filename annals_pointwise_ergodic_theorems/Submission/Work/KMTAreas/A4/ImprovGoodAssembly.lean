/-
# Assembling the good-major-arc form of `improv` from its two halves

Krause--Mirek--Tao prove Theorem `improv` by two separate chains, (i) (the `f`-minor-arc case,
§5.1) and (ii) (the `g`-minor-arc case, §5.2), both in the regime of *good* major arcs.  This
module assembles the two halves into the single predicate `ImprovGood` of
`Submission/Work/KMTAreas/A4/ImprovGoodDefs.lean`:

* the two halves are stated for the integer-shift average `AhalfZ N P f g` (`ℤ`-language, in which
  the whole of §5 is proved), while `ImprovGood` asks for the ergodic-theoretic average
  `AhalfR TZ N X P f g`, which is the reflection `x ↦ -x` of `AhalfZ` with the reflected inputs
  `f ∘ neg`, `g ∘ neg` (`eLpNorm_ahalfR_eq` of `A4/eLpNorm_ahalfR_eq`);
* the minor-arc hypothesis of `ImprovGood` is `Π_{≤l,≤k} f = 0`, and one passes it to the reflected
  input by `kmtProj_reflect` of `A4/kmtProj_reflect`;
* the two rates `c₁, c₂` are combined into `min c₁ c₂` and the two good-arc constants into
  `max Cρ₁ (deg P · Cρ₂)` (the second halved case is stated at the rescaled height
  `deg P · (l - Log N)`, which follows from `GoodMajorArcs` at the `l`-height times `deg P`).

## Main results

* `Work.KMTAreas.A4.eLpNorm_reflect`, `Work.KMTAreas.A4.memLp_reflect` — reflection invariance of
  the `ℓ^p` norm and of `MemLp` for the counting measure on `ℤ`;
* `Work.KMTAreas.A4.improvGood_of_Z` — the assembly.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.ImprovGoodDefs
import Submission.Work.KMTAreas.A4.kmtProj_reflect
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems

namespace Work.KMTAreas.A4

open Work.Analysis.IonescuWainger
open Work.Analysis.InverseTheory
open Work.Analysis.EndVar
open Work.KMTContract

/-! ## Reflection invariance of the `ℓ^p` norm on `(ℤ, counting measure)` -/

/-- The `ℓ^p` seminorm of a function on `ℤ` is invariant under the reflection `x ↦ -x`. -/
theorem eLpNorm_reflect (f : ℤ → ℂ) {p : ENNReal} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) :
    MeasureTheory.eLpNorm (fun x : ℤ => f (-x)) p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpt,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpt]
  congr 1
  rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count]
  exact (Equiv.neg ℤ).tsum_eq (fun x : ℤ => ‖f x‖ₑ ^ p.toReal)

/-- `MemLp` for the counting measure on `ℤ` is invariant under the reflection `x ↦ -x`. -/
theorem memLp_reflect {f : ℤ → ℂ} {p : ENNReal} (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (hf : MeasureTheory.MemLp f p (MeasureTheory.Measure.count : Measure ℤ)) :
    MeasureTheory.MemLp (fun x : ℤ => f (-x)) p
      (MeasureTheory.Measure.count : Measure ℤ) := by
  have hae : AEStronglyMeasurable (fun x : ℤ => f (-x))
      (MeasureTheory.Measure.count : Measure ℤ) :=
    (measurable_of_countable fun x : ℤ => f (-x)).aestronglyMeasurable
  have h2 : MeasureTheory.eLpNorm (fun x : ℤ => f (-x)) p
      (MeasureTheory.Measure.count : Measure ℤ) < ∞ := by
    rw [eLpNorm_reflect f hp0 hpt]
    exact hf.eLpNorm_lt_top
  exact MeasureTheory.memLp_iff.mpr h2

/-! ## The assembly -/

/-- **`ImprovGood` from the two halves of Theorem `improv`.**

The two hypotheses are the conclusions of the §5.1 chain (part (i), the `f`-minor-arc case) and of
the §5.2 chain (part (ii), the `g`-minor-arc case), both in the good-major-arc regime and in the
`ℤ`-language (`AhalfZ`, `kmtProj`).  The extra hypotheses `hReflect` and `hProjReflect` are the
elementary transfers between the ergodic-theoretic average `AhalfR TZ` of `ImprovGood` and the
integer-shift average `AhalfZ`:

* `hReflect` — the `ℓ^p` norm of `AhalfR TZ N X P f g` equals that of `AhalfZ N P (f ∘ neg)
  (g ∘ neg)` (the two averages differ by the reflection `x ↦ -x`, which preserves the counting
  measure);
* `hProjReflect` — a vanishing Ionescu--Wainger projection of `f` implies the same vanishing for
  the reflected `f ∘ neg` (the symbol of `kmtProj` is even). -/
theorem improvGood_of_Z (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree)
    (hReflect : ∀ (N : ℕ) (f g : ℤ → ℂ) (p : ENNReal),
      MeasureTheory.eLpNorm (fun x : ℤ => AhalfR TZ (N : NNReal) X P f g x) p
          (MeasureTheory.Measure.count : Measure ℤ)
        = MeasureTheory.eLpNorm (fun x : ℤ =>
            AhalfZ N P (fun t : ℤ => f (-t)) (fun t : ℤ => g (-t)) x) p
            (MeasureTheory.Measure.count : Measure ℤ))
    (hProjReflect : ∀ (ρ : ℝ) (l : ℕ) (k : ℤ) (f : ℤ → ℂ),
      MeasureTheory.MemLp f 2 (MeasureTheory.Measure.count : Measure ℤ) →
      kmtProj ρ l k f = 0 → kmtProj ρ l k (fun x : ℤ => f (-x)) = 0)
    (hOne : ∃ c : ℝ, 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
      ∀ (N l : ℕ) (f g : ℤ → ℂ), 1 ≤ N →
        MeasureTheory.MemLp f 2 (MeasureTheory.Measure.count : Measure ℤ) →
        MeasureTheory.MemLp g 2 (MeasureTheory.Measure.count : Measure ℤ) →
        GoodMajorArcs ρ Cρ l ((l : ℤ) - logN N) →
        kmtProj ρ l ((l : ℤ) - logN N) f = 0 →
        MeasureTheory.eLpNorm (fun x : ℤ => AhalfZ N P f g x) 1
            (MeasureTheory.Measure.count : Measure ℤ)
          ≤ ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ)))) *
              MeasureTheory.eLpNorm f 2 (MeasureTheory.Measure.count : Measure ℤ) *
              MeasureTheory.eLpNorm g 2 (MeasureTheory.Measure.count : Measure ℤ))
    (hTwo : ∃ c : ℝ, 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
      ∀ (N l : ℕ) (f g : ℤ → ℂ), 1 ≤ N →
        MeasureTheory.MemLp f 2 (MeasureTheory.Measure.count : Measure ℤ) →
        MeasureTheory.MemLp g 2 (MeasureTheory.Measure.count : Measure ℤ) →
        GoodMajorArcs ρ Cρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) →
        kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) g = 0 →
        MeasureTheory.eLpNorm (fun x : ℤ => AhalfZ N P f g x) 1
            (MeasureTheory.Measure.count : Measure ℤ)
          ≤ ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ)))) *
              MeasureTheory.eLpNorm f 2 (MeasureTheory.Measure.count : Measure ℤ) *
              MeasureTheory.eLpNorm g 2 (MeasureTheory.Measure.count : Measure ℤ)) :
    ImprovGood P := by
  obtain ⟨c₁, hc₁, H₁⟩ := hOne
  obtain ⟨c₂, hc₂, H₂⟩ := hTwo
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨Cρ₁, hCρ₁, C₁, hC₁, H₁'⟩ := H₁ ρ hρ hρ1
  obtain ⟨Cρ₂, hCρ₂, C₂, hC₂, H₂'⟩ := H₂ ρ hρ hρ1
  refine ⟨max Cρ₁ ((P.natDegree : ℝ) * Cρ₂), max C₁ C₂ + 1,
    lt_of_lt_of_le hCρ₁ (le_max_left _ _), by positivity, ?_⟩
  intro N l f g hN hf hg hgood hdisj
  have hd1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by
    have : 1 ≤ P.natDegree := le_trans (by norm_num) hP
    exact_mod_cast this
  have hpw : (0 : ℝ) < (2 : ℝ) ^ (ρ * (l : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  -- the two good-major-arc hypotheses at the smaller constants
  have hgoodr : (l : ℝ) - (logN N : ℝ)
      ≤ -max Cρ₁ ((P.natDegree : ℝ) * Cρ₂) * (2 : ℝ) ^ (ρ * (l : ℝ)) := by
    have h := hgood
    simp only [GoodMajorArcs] at h
    push_cast at h
    exact h
  have hgood₁ : GoodMajorArcs ρ Cρ₁ l ((l : ℤ) - logN N) := by
    simp only [GoodMajorArcs]
    push_cast
    have hle : Cρ₁ ≤ max Cρ₁ ((P.natDegree : ℝ) * Cρ₂) := le_max_left _ _
    nlinarith [hgoodr, hpw, hle]
  have hgood₂ : GoodMajorArcs ρ Cρ₂ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) := by
    simp only [GoodMajorArcs]
    push_cast
    have h0 := mul_le_mul_of_nonneg_left hgoodr (by positivity : (0 : ℝ) ≤ (P.natDegree : ℝ))
    have hle : (P.natDegree : ℝ) * Cρ₂ ≤ max Cρ₁ ((P.natDegree : ℝ) * Cρ₂) := le_max_right _ _
    have h1 := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ (P.natDegree : ℝ))
    have hsq : (1 : ℝ) ≤ (P.natDegree : ℝ) * (P.natDegree : ℝ) := by nlinarith [hd1]
    have key2 : Cρ₂ ≤ (P.natDegree : ℝ) * max Cρ₁ ((P.natDegree : ℝ) * Cρ₂) := by
      nlinarith [h1, hsq, hCρ₂]
    nlinarith [h0, key2, hpw, hCρ₂]
  have hcoe : ENNReal.ofReal (C₁ : ℝ) ≤ (↑(max C₁ C₂ + 1) : ENNReal) := by
    rw [← ENNReal.ofReal_coe_nnreal (p := max C₁ C₂ + 1)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (C₁ : ℝ) ≤ ((max C₁ C₂ + 1 : NNReal) : ℝ) := by
      rw [NNReal.coe_add, NNReal.coe_one, NNReal.coe_max]
      linarith [le_max_left (C₁ : ℝ) (C₂ : ℝ)]
    exact h1
  have hcoe₂ : ENNReal.ofReal (C₂ : ℝ) ≤ (↑(max C₁ C₂ + 1) : ENNReal) := by
    rw [← ENNReal.ofReal_coe_nnreal (p := max C₁ C₂ + 1)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (C₂ : ℝ) ≤ ((max C₁ C₂ + 1 : NNReal) : ℝ) := by
      rw [NNReal.coe_add, NNReal.coe_one, NNReal.coe_max]
      linarith [le_max_right (C₁ : ℝ) (C₂ : ℝ)]
    exact h1
  have hexp : (2 : ℝ) ^ (-(c₁ * (l : ℝ))) ≤ (2 : ℝ) ^ (-((min c₁ c₂) * (l : ℝ))) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    have hcl : min c₁ c₂ ≤ c₁ := min_le_left _ _
    nlinarith
  have hexp₂ : (2 : ℝ) ^ (-(c₂ * (l : ℝ))) ≤ (2 : ℝ) ^ (-((min c₁ c₂) * (l : ℝ))) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    have hcl : min c₁ c₂ ≤ c₂ := min_le_right _ _
    nlinarith
  rcases hdisj with hf0 | hg0
  · -- #### case (i): `f` has no major-arc content
    have hf0' : kmtProj ρ l ((l : ℤ) - logN N) f = 0 := by
      rw [show -(logN N) + (l : ℤ) = (l : ℤ) - logN N from by ring] at hf0
      exact hf0
    have key := H₁' N l (fun t : ℤ => f (-t)) (fun t : ℤ => g (-t)) hN
      (memLp_reflect (by norm_num) (by norm_num) hf)
      (memLp_reflect (by norm_num) (by norm_num) hg) hgood₁
      (hProjReflect ρ l ((l : ℤ) - logN N) f hf hf0')
    rw [eLpNorm_reflect f (by norm_num) (by norm_num),
      eLpNorm_reflect g (by norm_num) (by norm_num)] at key
    calc MeasureTheory.eLpNorm (fun x : ℤ => AhalfR TZ (N : NNReal) X P f g x) 1
          (MeasureTheory.Measure.count : Measure ℤ)
        = MeasureTheory.eLpNorm (fun x : ℤ => AhalfZ N P (fun t : ℤ => f (-t))
            (fun t : ℤ => g (-t)) x) 1 (MeasureTheory.Measure.count : Measure ℤ) :=
          hReflect N f g 1
      _ ≤ ENNReal.ofReal (C₁ : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c₁ * (l : ℝ)))) *
            MeasureTheory.eLpNorm f 2 (MeasureTheory.Measure.count : Measure ℤ) *
            MeasureTheory.eLpNorm g 2 (MeasureTheory.Measure.count : Measure ℤ) := key
      _ ≤ (↑(max C₁ C₂ + 1) : ENNReal) *
            ENNReal.ofReal ((2 : ℝ) ^ (-((min c₁ c₂) * (l : ℝ)))) *
            MeasureTheory.eLpNorm f 2 (MeasureTheory.Measure.count : Measure ℤ) *
            MeasureTheory.eLpNorm g 2 (MeasureTheory.Measure.count : Measure ℤ) := by
          refine mul_le_mul' (mul_le_mul' (mul_le_mul' ?_ ?_) le_rfl) le_rfl
          · exact hcoe
          · exact ENNReal.ofReal_le_ofReal hexp
  · -- #### case (ii): `g` has no major-arc content
    have hg0' : kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) g = 0 := by
      rw [show -(logN N) + (l : ℤ) = (l : ℤ) - logN N from by ring] at hg0
      exact hg0
    have key := H₂' N l (fun t : ℤ => f (-t)) (fun t : ℤ => g (-t)) hN
      (memLp_reflect (by norm_num) (by norm_num) hf)
      (memLp_reflect (by norm_num) (by norm_num) hg) hgood₂
      (hProjReflect ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) g hg hg0')
    rw [eLpNorm_reflect f (by norm_num) (by norm_num),
      eLpNorm_reflect g (by norm_num) (by norm_num)] at key
    calc MeasureTheory.eLpNorm (fun x : ℤ => AhalfR TZ (N : NNReal) X P f g x) 1
          (MeasureTheory.Measure.count : Measure ℤ)
        = MeasureTheory.eLpNorm (fun x : ℤ => AhalfZ N P (fun t : ℤ => f (-t))
            (fun t : ℤ => g (-t)) x) 1 (MeasureTheory.Measure.count : Measure ℤ) :=
          hReflect N f g 1
      _ ≤ ENNReal.ofReal (C₂ : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c₂ * (l : ℝ)))) *
            MeasureTheory.eLpNorm f 2 (MeasureTheory.Measure.count : Measure ℤ) *
            MeasureTheory.eLpNorm g 2 (MeasureTheory.Measure.count : Measure ℤ) := key
      _ ≤ (↑(max C₁ C₂ + 1) : ENNReal) *
            ENNReal.ofReal ((2 : ℝ) ^ (-((min c₁ c₂) * (l : ℝ)))) *
            MeasureTheory.eLpNorm f 2 (MeasureTheory.Measure.count : Measure ℤ) *
            MeasureTheory.eLpNorm g 2 (MeasureTheory.Measure.count : Measure ℤ) := by
          refine mul_le_mul' (mul_le_mul' (mul_le_mul' ?_ ?_) le_rfl) le_rfl
          · exact hcoe₂
          · exact ENNReal.ofReal_le_ofReal hexp₂

/-! ## The vanishing of the projection is inherited by the reflected function -/

/-- The minor-arc hypothesis of `ImprovGood` passes to the reflected function `f ∘ neg`: this is
the form in which `improvGood_of_Z` consumes it (it is the direct consequence of
`A4.kmtProj_reflect`). -/
theorem kmtProj_reflect_zero (ρ : ℝ) (l : ℕ) (k : ℤ) (f : ℤ → ℂ)
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.Measure.count : Measure ℤ))
    (h : kmtProj ρ l k f = 0) : kmtProj ρ l k (fun x : ℤ => f (-x)) = 0 := by
  rw [kmtProj_reflect ρ l k f hf, h]
  rfl


end Work.KMTAreas.A4
