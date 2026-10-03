/-
# `Work.FIArea3.JointCount.polarBox_lattice_count_sharp` — lattice points of a coset in the
polar box (sharp form)

For Gaussian integers `z₀, g₁, g₂` with `|det (g₁, g₂)| = c ≥ 1`, the number of Gaussian
integers `z` in the polar box (5.14) with `z - z₀ ∈ ℤ g₁ + ℤ g₂` is at most
`π u² / c + 16 u (√|g₁|² + √|g₂|²) / c + 1`, where `u = θ√N`.

The lattice `Λ = ℤ g₁ + ℤ g₂` has covolume `c`.  The polar box is contained in the annular
sector `R = {√N < |z| ≤ √((1+θ)N), φ < arg z ≤ φ + 2πθ}` of area `π u²` and diameter `≤ 7u`.
Blichfeldt's argument (together with a Steiner-type bound for the Minkowski sum of `R` with a
fundamental parallelogram `F` of `Λ`) gives `#·c ≤ area(R + F) ≤ area(R) + 16u(|g₁|+|g₂|) + c`.
-/
import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.JointCount.polarBox_lattice_count
import Submission.Work.FIArea3.JointCount.sharp_defs
import Submission.Work.FIArea3.JointCount.annSector_add_area_le
import Submission.Work.FIArea4.polarBox_card_le

namespace Work.FIArea3.JointCount

open MeasureTheory Finset
open scoped ENNReal BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The polar-box points of `Pa, φ`, as a set of complex numbers, lie in the annular sector. -/
lemma polarBoxFinset_toComplex_subset (Pa : Work.FITop.Params) (φ : ℝ) :
    {z : ℂ | ∃ z0 : GaussianInt, z0 ∈ Work.FIArea3.polarBoxFinset Pa φ ∧ z = z0.toComplex}
      ⊆ annSector (Real.sqrt Pa.N) (Real.sqrt ((1 + Pa.θ) * Pa.N)) φ (2 * Real.pi * Pa.θ) := by
  rintro z ⟨z0, hz0, rfl⟩
  have hbox : Work.FITop3.InPolarBox Pa φ z0 :=
    (Work.FIArea3.mem_polarBoxFinset.mp hz0).2
  obtain ⟨-, hlo, hhi, harglo, hargle⟩ := hbox
  have hnorm : ‖z0.toComplex‖ = Real.sqrt ((Work.FIPlan.gnorm z0 : ℕ) : ℝ) :=
    Work.FIArea4.norm_toComplex_eq_sqrt_gnorm z0
  refine ⟨?_, ?_, harglo, hargle⟩
  · rw [hnorm]; exact Real.sqrt_lt_sqrt (by linarith [Pa.hN1]) hlo
  · rw [hnorm]; exact Real.sqrt_le_sqrt hhi

/-! ## Blichfeldt, region form -/

/-- **Blichfeldt's argument, region form.**  If `W` is a finite set of points of the lattice
`ℤu + ℤv` (with `|det (u,v)| = c > 0`) all lying in a measurable set `R`, and `F` is the
fundamental parallelogram `Llc u v '' uCell` of covolume `c`, then
`#W · c ≤ area(R + F)`. -/
lemma card_mul_c_le_volume_add (u v : ℂ) (c : ℝ)
    (hdet : |u.re * v.im - v.re * u.im| = c) (hcpos : 0 < c)
    (W : Finset ℂ) (hWlat : ∀ w ∈ W, w ∈ latte u v)
    (R : Set ℂ) (hWR : ∀ w ∈ W, w ∈ R) :
    ENNReal.ofReal ((W.card : ℝ) * c)
      ≤ volume (Set.image2 (· + ·) R (Llc u v '' uCell)) := by
  have hδ : u.re * v.im - v.re * u.im ≠ 0 := by
    have h := hcpos; rw [← hdet] at h; exact abs_pos.mp h
  have hdetL : LinearMap.det (Llc u v) ≠ 0 := by rw [Llc_det]; exact hδ
  have hinj : Function.Injective (Llc u v) := Llc_injective hδ
  set F : Set ℂ := Llc u v '' uCell with hF
  have hFmeas : MeasurableSet F := by
    rw [hF]; exact measurableSet_image_Llc u v hdetL uCell measurableSet_uCell
  have hFvol : volume F = ENNReal.ofReal c := by
    rw [hF, MeasureTheory.Measure.addHaar_image_linearMap volume (Llc u v) uCell,
      volume_uCell, mul_one, Llc_det, hdet]
  have hdisj : (↑W : Set ℂ).Pairwise (Function.onFun Disjoint (fun w => tsh w F)) := by
    intro w₁ hw₁ w₂ hw₂ hne
    rw [hF]
    exact disjoint_tsh_latte u v hinj w₁ w₂ (hWlat w₁ hw₁) (hWlat w₂ hw₂) hne
  have hmeas : ∀ b ∈ W, MeasurableSet (tsh b F) := fun b _ => measurableSet_tsh hFmeas b
  have hvolunion : volume (⋃ w ∈ W, tsh w F) = ENNReal.ofReal (c * W.card) := by
    rw [measure_biUnion_finset hdisj hmeas]
    simp only [volume_tsh, hFvol]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul hcpos.le]
  have hsub : (⋃ w ∈ W, tsh w F) ⊆ Set.image2 (· + ·) R F := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨w, hwW, hx⟩ := hx
    rw [mem_tsh] at hx
    obtain ⟨f, hfF, rfl⟩ := hx
    exact ⟨w, hWR w hwW, f, hfF, rfl⟩
  rw [show ENNReal.ofReal ((W.card : ℝ) * c) = ENNReal.ofReal (c * W.card) by rw [mul_comm],
    ← hvolunion]
  exact measure_mono hsub

/-! ## θ ≤ 1 -/

lemma params_theta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  have hlog : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    have h1 : Real.log 3 ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (by norm_num) hx3
    linarith
  have hA'0 : (0 : ℝ) ≤ Pa.A' := by
    have h : (2 : ℝ) ^ (20 : ℕ) ≤ Pa.A' := by linarith [Pa.hA', Pa.hA]
    positivity
  rw [Pa.hθ]
  exact Real.rpow_le_one_of_one_le_of_nonpos hlog (by linarith)

/-! ## The sharp count -/

theorem polarBox_lattice_count_sharp (Pa : Work.FITop.Params) (φ : ℝ) (z₀ g₁ g₂ : GaussianInt) (c : ℕ)
    (hc : (g₁.re * g₂.im - g₁.im * g₂.re).natAbs = c) (hcpos : 1 ≤ c) :
    (({z : GaussianInt | z ∈ Work.FIArea3.polarBoxFinset Pa φ ∧
        ∃ a b : ℤ, z - z₀ = (a : GaussianInt) * g₁ + (b : GaussianInt) * g₂}).ncard : ℝ)
      ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 / (c : ℝ)
        + 16 * (Pa.θ * Real.sqrt Pa.N)
            * (Real.sqrt ((Work.FIPlan.gnorm g₁ : ℝ)) + Real.sqrt ((Work.FIPlan.gnorm g₂ : ℝ)))
          / (c : ℝ)
        + 1 := by
  set Fs : Finset GaussianInt := (Work.FIArea3.polarBoxFinset Pa φ).filter
      (fun z => ∃ a b : ℤ, z - z₀ = (a : GaussianInt) * g₁ + (b : GaussianInt) * g₂) with hFsdef
  have hset : {z : GaussianInt | z ∈ Work.FIArea3.polarBoxFinset Pa φ ∧
        ∃ a b : ℤ, z - z₀ = (a : GaussianInt) * g₁ + (b : GaussianInt) * g₂}
      = (↑Fs : Set GaussianInt) := by
    ext z; simp [hFsdef, Finset.mem_filter]
  rw [hset, Set.ncard_coe_finset]
  set u : ℂ := g₁.toComplex with hu
  set v : ℂ := g₂.toComplex with hv
  set F : Set ℂ := Llc u v '' uCell with hFdef
  set R'' : Set ℂ := {z : ℂ | ∃ z0' : GaussianInt,
      z0' ∈ Work.FIArea3.polarBoxFinset Pa φ ∧ z = z0'.toComplex} with hR''def
  set R : Set ℂ := tsh (- z₀.toComplex) R'' with hRdef
  set W : Finset ℂ := Fs.image (fun z => z.toComplex - z₀.toComplex) with hWdef
  have hWcard : W.card = Fs.card := by
    rw [hWdef]
    refine Finset.card_image_of_injective Fs ?_
    intro a b hab
    exact toComplex_injective (sub_left_inj.mp hab)
  have hdet : |u.re * v.im - v.re * u.im| = (c : ℝ) := by
    rw [hu, hv, det_toComplex_natAbs, hc]
  have hcpos' : (0 : ℝ) < (c : ℝ) := by
    have : 0 < c := by omega
    exact_mod_cast this
  have hWmem : ∀ w ∈ W, w ∈ latte u v := by
    intro w hw
    rw [hWdef, Finset.mem_image] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    have hz' := hz
    rw [hFsdef, Finset.mem_filter] at hz'
    obtain ⟨_, a, b, hzab⟩ := hz'
    refine ⟨a, b, ?_⟩
    have h := congrArg GaussianInt.toComplex hzab
    simp only [map_sub, map_add, map_mul, map_intCast] at h
    rw [hu, hv]
    exact h
  have hWR : ∀ w ∈ W, w ∈ R := by
    intro w hw
    rw [hWdef, Finset.mem_image] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    have hz' := hz
    rw [hFsdef, Finset.mem_filter] at hz'
    refine mem_tsh.mpr ⟨z.toComplex, ?_, by ring⟩
    exact ⟨z, hz'.1, rfl⟩
  have hcount := card_mul_c_le_volume_add u v (c : ℝ) hdet hcpos' W hWmem R hWR
  -- the angular sector (in the geometric parametrisation) containing the box
  set S : Set ℂ := annSector (Real.sqrt Pa.N) (Real.sqrt Pa.N * Real.sqrt (1 + Pa.θ)) φ
      (2 * Real.pi * Pa.θ) with hSdef
  have hb : Real.sqrt ((1 + Pa.θ) * Pa.N) = Real.sqrt Pa.N * Real.sqrt (1 + Pa.θ) := by
    rw [Real.sqrt_mul (by linarith [Pa.hθ0]), mul_comm]
  have hsub_ann : R'' ⊆ S := by
    have h := polarBoxFinset_toComplex_subset Pa φ
    rw [hb] at h
    exact h
  have hvol_le : volume (Set.image2 (· + ·) R F) ≤ volume (Set.image2 (· + ·) S F) := by
    have hsub : Set.image2 (· + ·) R F
        ⊆ tsh (- z₀.toComplex) (Set.image2 (· + ·) S F) := by
      rintro x ⟨r, hr, f, hf, rfl⟩
      rw [hRdef, mem_tsh] at hr
      obtain ⟨r'', hr'', heq⟩ := hr
      refine ⟨r'' + f, ⟨r'', hsub_ann hr'', f, hf, rfl⟩, ?_⟩
      rw [← heq]; ring
    calc volume (Set.image2 (· + ·) R F)
        ≤ volume (tsh (- z₀.toComplex) (Set.image2 (· + ·) S F)) := measure_mono hsub
      _ = volume (Set.image2 (· + ·) S F) := volume_tsh _ _
  have hfin : volume (Set.image2 (· + ·) S F) ≠ ⊤ := by
    have hbd : Set.image2 (· + ·) S F ⊆ Metric.closedBall 0
        (Real.sqrt Pa.N * Real.sqrt (1 + Pa.θ) + (‖u‖ + ‖v‖) / 2) := by
      rintro x ⟨s, hs, f, hf, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [hSdef, annSector] at hs
      obtain ⟨-, hs2, -, -⟩ := hs
      have hf1 : ‖f‖ ≤ (‖u‖ + ‖v‖) / 2 := by
        rw [hFdef] at hf
        obtain ⟨zc, hzc, rfl⟩ := hf
        rw [Llc_apply]
        calc ‖zc.re • u + zc.im • v‖ ≤ ‖zc.re • u‖ + ‖zc.im • v‖ := norm_add_le _ _
          _ = |zc.re| * ‖u‖ + |zc.im| * ‖v‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ (1/2) * ‖u‖ + (1/2) * ‖v‖ := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_right
                  (abs_le.mpr ⟨by linarith [(mem_uCell zc).mp hzc |>.1],
                               by linarith [(mem_uCell zc).mp hzc |>.2.1]⟩) (norm_nonneg _)
              · exact mul_le_mul_of_nonneg_right
                  (abs_le.mpr ⟨by linarith [(mem_uCell zc).mp hzc |>.2.2.1],
                               by linarith [(mem_uCell zc).mp hzc |>.2.2.2]⟩) (norm_nonneg _)
          _ = (‖u‖ + ‖v‖) / 2 := by ring
      calc ‖s + f‖ ≤ ‖s‖ + ‖f‖ := norm_add_le _ _
        _ ≤ Real.sqrt Pa.N * Real.sqrt (1 + Pa.θ) + (‖u‖ + ‖v‖) / 2 := add_le_add hs2 hf1
    refine ne_top_of_le_ne_top ?_ (measure_mono hbd)
    rw [Complex.volume_closedBall]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.coe_ne_top
  -- the geometric bound
  have hdet2 : |u.re * v.im - u.im * v.re| = (c : ℝ) := by
    rw [show u.re * v.im - u.im * v.re = u.re * v.im - v.re * u.im by ring]; exact hdet
  have hgeo := annSector_add_area_le (Real.sqrt Pa.N) Pa.θ φ u v (c : ℝ)
      (Real.sqrt_pos.mpr (by linarith [Pa.hN1]))
      (le_of_lt Pa.hθ0) (params_theta_le_one Pa) (by positivity) hdet2
  have h1 : (W.card : ℝ) * c ≤ (volume (Set.image2 (· + ·) S F)).toReal := by
    have h2 := ENNReal.toReal_mono hfin (le_trans hcount hvol_le)
    rw [ENNReal.toReal_ofReal (by positivity)] at h2
    simpa [mul_comm] using h2
  have h3 : (W.card : ℝ) * c ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
      + 16 * (Pa.θ * Real.sqrt Pa.N)
          * (Real.sqrt ((Work.FIPlan.gnorm g₁ : ℝ)) + Real.sqrt ((Work.FIPlan.gnorm g₂ : ℝ)))
      + (c : ℝ) := by
    refine h1.trans (hgeo.trans ?_)
    have hnu : ‖u‖ = Real.sqrt ((Work.FIPlan.gnorm g₁ : ℝ)) := by
      rw [hu]; exact Work.FIArea4.norm_toComplex_eq_sqrt_gnorm g₁
    have hnv : ‖v‖ = Real.sqrt ((Work.FIPlan.gnorm g₂ : ℝ)) := by
      rw [hv]; exact Work.FIArea4.norm_toComplex_eq_sqrt_gnorm g₂
    rw [hnu, hnv]
  rw [hWcard] at h3
  have hZ : Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 / (c : ℝ)
      + 16 * (Pa.θ * Real.sqrt Pa.N)
          * (Real.sqrt ((Work.FIPlan.gnorm g₁ : ℝ)) + Real.sqrt ((Work.FIPlan.gnorm g₂ : ℝ)))
        / (c : ℝ) + 1
      = (Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
          + 16 * (Pa.θ * Real.sqrt Pa.N)
              * (Real.sqrt ((Work.FIPlan.gnorm g₁ : ℝ)) + Real.sqrt ((Work.FIPlan.gnorm g₂ : ℝ)))
          + (c : ℝ)) / (c : ℝ) := by
    field_simp
  rw [hZ, le_div_iff₀ hcpos']
  linarith [h3]

end

end Work.FIArea3.JointCount
