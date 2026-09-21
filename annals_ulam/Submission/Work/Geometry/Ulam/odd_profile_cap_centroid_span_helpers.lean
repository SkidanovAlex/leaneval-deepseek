import Mathlib
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_integrals_even
import Submission.Commons.Geometry.Ulam.odd_floating_of_family

namespace Commons.Geometry.Ulam

open MeasureTheory Set Filter
open scoped Topology Interval ContDiff RealInnerProductSpace BigOperators

set_option autoImplicit false

lemma mem_span_e0_elast {d : ℕ} [NeZero d] (hd : 2 ≤ d) (s lam : ℝ) {v : EuclideanSpace ℝ (Fin d)}
    (h0 : v 0 = -s * lam) (hlast : v (lastFin d) = lam)
    (hmiddle : ∀ i, i ≠ 0 → i ≠ lastFin d → v i = 0) :
    v ∈ ℝ ∙ ((-s) • (EuclideanSpace.single (0 : Fin d) (1:ℝ)) + (EuclideanSpace.single (lastFin d) (1:ℝ))) := by
  have hlast_ne : lastFin d ≠ 0 := by
    dsimp [lastFin]
    exact Fin.ne_of_val_ne (by simp; omega)
  rw [Submodule.mem_span_singleton]
  refine ⟨lam, ?_⟩
  ext i
  change (lam • ((-s) • (EuclideanSpace.single (0 : Fin d) (1:ℝ)) + (EuclideanSpace.single (lastFin d) (1:ℝ)))).ofLp i = v.ofLp i
  by_cases hi0 : i = 0
  · subst i
    simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.single_apply, h0]
    rw [if_neg (Ne.symm hlast_ne)]
    simp
    ring
  · by_cases hilast : i = lastFin d
    · subst i
      simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.single_apply, hlast]
      rw [if_neg hi0]
      simp
    · have hv := hmiddle i hi0 hilast
      rw [hv]
      simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.single_apply]
      rw [if_neg hi0, if_neg hilast]
      simp

lemma integral_id_apply {d : ℕ} [NeZero d] (K : Set (EuclideanSpace ℝ (Fin d))) (i : Fin d)
    (hK_meas : MeasurableSet K) (hK_bdd : Bornology.IsBounded K) :
    (∫ x in K, x) i = ∫ x in K, x i := by
  let L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i
  have hInt : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) (volume.restrict K) :=
    (integrableOn_id_bounded_measurable (d := d) hK_meas hK_bdd).integrable
  have h := ContinuousLinearMap.integral_comp_comm L hInt
  simpa [L, PiLp.proj_apply] using h.symm

lemma setAverage_id_apply {d : ℕ} [NeZero d] (K : Set (EuclideanSpace ℝ (Fin d))) (i : Fin d)
    (hK_meas : MeasurableSet K) (hK_bdd : Bornology.IsBounded K) :
    ((⨍ x in K, x) i) = ⨍ x in K, (x i) := by
  rw [setAverage_eq, setAverage_eq]
  rw [PiLp.smul_apply]
  rw [integral_id_apply K i hK_meas hK_bdd]

-- Odd centroid moment relation


lemma odd_inner_integral_min_eq_max {f L : ℝ} {φ : ℝ → ℝ}
    (hφ_zero : ∀ z ∈ Set.Icc (min f L) (-f), φ z = 0) :
    (∫ z in (-f)..(min f L), φ z) = ∫ z in (-f)..(max (-f) (min f L)), φ z := by
  by_cases hle : min f L ≤ -f
  · have hmax : max (-f) (min f L) = -f := max_eq_left hle
    rw [hmax]
    have hba : (∫ z in (-f)..(min f L), φ z) = -∫ z in Set.Ioc (min f L) (-f), φ z := by
      rw [intervalIntegral.integral_of_ge hle]
    have hzero : (∫ z in Set.Ioc (min f L) (-f), φ z) = 0 := by
      apply setIntegral_eq_zero_of_ae_eq_zero
      filter_upwards [Measure.ae_ne volume (-f)] with z hzne hzmem
      have hzIcc : z ∈ Set.Icc (min f L) (-f) := Set.Ioc_subset_Icc_self hzmem
      exact hφ_zero z hzIcc
    rw [hba, hzero]
    simp
  · have hmax : max (-f) (min f L) = min f L := max_eq_right (le_of_lt (lt_of_not_ge hle))
    rw [hmax]



/-- Support conversion for the arbitrary-endpoint body-of-revolution lemmas:
`Icc A B` is the same as `Icc (- -A) B`. -/
lemma support_subset_Icc_neg_neg {f : ℝ → ℝ} {A B : ℝ}
    (hf : Function.support f ⊆ Set.Icc A B) :
    Function.support f ⊆ Set.Icc (- -A) B := by
  simpa [neg_neg] using hf

lemma concaveOn_Icc_neg_neg {f : ℝ → ℝ} {A B : ℝ}
    (hf : ConcaveOn ℝ (Set.Icc A B) f) :
    ConcaveOn ℝ (Set.Icc (- -A) B) f := by
  simpa [neg_neg] using hf

lemma eq_zero_neg_neg {f : ℝ → ℝ} {A : ℝ} (hf : f A = 0) : f (- -A) = 0 := by
  simpa [neg_neg] using hf


/-- Support-size bound: every `t ∈ Icc A B` satisfies `|t| ≤ max |A| |B|`. -/
lemma abs_le_max_abs_of_mem_Icc {A B t : ℝ} (ht : t ∈ Set.Icc A B) :
    |t| ≤ max |A| |B| := by
  rw [abs_le]
  constructor
  · have hA_le : A ≤ t := ht.1
    have hnegT_le_A : -max |A| |B| ≤ A := by
      have h1 : -max |A| |B| ≤ -|A| := neg_le_neg (le_max_left |A| |B|)
      have h2 : -|A| ≤ A := neg_abs_le A
      linarith
    linarith
  · have htB : t ≤ B := ht.2
    have hB_le_T : B ≤ max |A| |B| := le_trans (le_abs_self B) (le_max_right |A| |B|)
    linarith

end Commons.Geometry.Ulam
