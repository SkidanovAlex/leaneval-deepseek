import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndexGeom

/-!
# The continuous square root of a closed plane curve of even winding number

A continuous nowhere vanishing `2π`-periodic curve `f : ℝ → ℂ` of winding number `2m` about the
origin admits a continuous `2π`-periodic square root `η` (`η t * η t = f t`) of winding number
`m`.  The "half argument" is obtained from the lift `Λ` of `f` through `Complex.exp` on one
period: `Λ 1 - Λ 0 = 2m * 2πi`, so half the lift closes up after the full period, and the
resulting function descends to the circle `ℝ ⧸ 2πℤ`.
-/

noncomputable section

open Set

namespace Work.Smooth.SphereJordan

/-- `exp (n * 2πi) = 1` for every integer `n`. -/
lemma exp_int_mul_two_pi_I (n : ℤ) :
    Complex.exp ((n : ℂ) * (2 * ↑Real.pi * Complex.I)) = 1 :=
  Complex.exp_eq_one_iff.mpr ⟨n, rfl⟩

theorem exists_sqrt_curve_of_even_windNumber {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) {z : ℂ} (hz : ∀ t : ℝ, γ t ≠ z) {m : ℤ}
    (hW : Work.Smooth.SphereJordan.windNumber γ hγ z = 2 * m) :
    ∃ η : C(ℝ, ℂ), (∀ t : ℝ, η t * η t = γ t - z) ∧ (∀ t : ℝ, η t ≠ 0) ∧
      Function.Periodic (fun t : ℝ => η t) (2 * Real.pi) ∧
      Work.Smooth.SphereJordan.windNumber (fun t : ℝ => η t) η.continuous 0 = m := by
  haveI : Fact ((0 : ℝ) < 2 * Real.pi) := ⟨by positivity⟩
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have h01 : ((0 : ℝ) ≤ 1) := zero_le_one
  -- The closed loop traced by `γ - z` over one period.
  set c : C(unitInterval, ℂ) := curveLoop (fun t : ℝ => γ t - z) (hγ.sub continuous_const) with hc
  have hcne : ∀ t : unitInterval, c t ≠ 0 := by
    intro t
    rw [hc]
    exact sub_ne_zero.mpr (hz _)
  have hcloop : c 0 = c 1 := by
    rw [hc]
    show γ (2 * Real.pi * ((0 : unitInterval) : ℝ)) - z
      = γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) - z
    have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by norm_num
    have h1 : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by norm_num
    have h1' : γ (2 * Real.pi) = γ 0 := by simpa using hper 0
    rw [h0, h1, h1']
  have hWc : loopIndex c = 2 * m := by
    rw [hc]
    exact hW
  -- A lift of the argument of the loop, and its increment over one period.
  obtain ⟨Λ, hΛ, -, -⟩ := argChangeLift c hcne
  have hspec := loopIndex_spec c hcne hcloop Λ hΛ
  have hinc : Λ 1 - Λ 0 = (m : ℂ) * (4 * ↑Real.pi * Complex.I) := by
    rw [hspec, hWc]
    push_cast
    ring
  have hΛ1 : Λ (1 : unitInterval) = Λ (0 : unitInterval) + (m : ℂ) * (4 * ↑Real.pi * Complex.I) := by
    linear_combination hinc
  -- Half of the lift, as a function on `ℝ`.
  set g : ℝ → ℂ := fun σ => Complex.exp (Λ (Set.projIcc (0 : ℝ) 1 h01 (σ / (2 * Real.pi))) / 2)
    with hg
  have hgc : Continuous g := by
    rw [hg]
    refine Complex.continuous_exp.comp (Continuous.div_const ?_ 2)
    exact Λ.continuous.comp (continuous_projIcc.comp (continuous_id.div_const _))
  have hg0 : g 0 = Complex.exp (Λ (0 : unitInterval) / 2) := by
    have e : Set.projIcc (0 : ℝ) 1 h01 ((0 : ℝ) / (2 * Real.pi)) = (0 : unitInterval) := by
      rw [show (0 : ℝ) / (2 * Real.pi) = 0 by simp]
      rw [Set.projIcc_of_mem h01 (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)]
      exact Subtype.ext rfl
    show Complex.exp (Λ (Set.projIcc (0 : ℝ) 1 h01 ((0 : ℝ) / (2 * Real.pi))) / 2)
      = Complex.exp (Λ (0 : unitInterval) / 2)
    rw [e]
  have hgπ : g (2 * Real.pi) = Complex.exp (Λ (1 : unitInterval) / 2) := by
    have e : Set.projIcc (0 : ℝ) 1 h01 ((2 * Real.pi) / (2 * Real.pi)) = (1 : unitInterval) := by
      rw [show (2 * Real.pi) / (2 * Real.pi) = 1 by field_simp]
      rw [Set.projIcc_of_mem h01 (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)]
      exact Subtype.ext rfl
    show Complex.exp (Λ (Set.projIcc (0 : ℝ) 1 h01 ((2 * Real.pi) / (2 * Real.pi))) / 2)
      = Complex.exp (Λ (1 : unitInterval) / 2)
    rw [e]
  -- Halving the increment, the half-lift returns to its starting value: it descends to the circle.
  have hg01 : g 0 = g (2 * Real.pi) := by
    have hkey : Λ (1 : unitInterval) / 2 =
        Λ (0 : unitInterval) / 2 + (m : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      rw [hΛ1]; ring
    rw [hg0, hgπ, hkey, Complex.exp_add, exp_int_mul_two_pi_I m, mul_one]
  let G : AddCircle (2 * Real.pi) → ℂ := AddCircle.liftIco (2 * Real.pi) 0 g
  have hGc : Continuous G :=
    AddCircle.liftIco_zero_continuous (p := 2 * Real.pi) hg01 hgc.continuousOn
  let η : C(ℝ, ℂ) :=
    ⟨fun τ : ℝ => G (τ : AddCircle (2 * Real.pi)), hGc.comp continuous_quotient_mk'⟩
  have hηper : Function.Periodic (fun t : ℝ => η t) (2 * Real.pi) := by
    intro t
    show G (((t + 2 * Real.pi : ℝ)) : AddCircle (2 * Real.pi))
      = G ((t : ℝ) : AddCircle (2 * Real.pi))
    rw [AddCircle.coe_add_period]
  -- The decomposition of a real number into its residue class mod `2π`.
  have huIco : ∀ t : ℝ, toIcoMod h2π 0 t ∈ Set.Ico 0 (2 * Real.pi) := by
    intro t
    have h := toIcoMod_mem_Ico h2π 0 t
    rwa [zero_add] at h
  have huty : ∀ t : ℝ, t = toIcoMod h2π 0 t + (toIcoDiv h2π 0 t : ℝ) * (2 * Real.pi) := by
    intro t
    have h := toIcoMod_add_toIcoDiv_zsmul h2π 0 t
    rw [zsmul_eq_mul] at h
    linarith [h]
  have hgval : ∀ σ : ℝ, σ ∈ Set.Ico 0 (2 * Real.pi) → η σ = g σ := by
    intro σ hσ
    show G ((σ : ℝ) : AddCircle (2 * Real.pi)) = g σ
    exact AddCircle.liftIco_zero_coe_apply hσ
  -- The square-root property.
  have hηsq : ∀ t : ℝ, η t * η t = γ t - z := by
    intro t
    set u : ℝ := toIcoMod h2π 0 t with hu
    have huI : u ∈ Set.Ico 0 (2 * Real.pi) := by rw [hu]; exact huIco t
    have hut : t = u + (toIcoDiv h2π 0 t : ℝ) * (2 * Real.pi) := by rw [hu]; exact huty t
    have hηu : η t = η u := by
      rw [hut]
      exact (hηper.int_mul (toIcoDiv h2π 0 t)) u
    have htu : γ t = γ u := by
      rw [hut]
      exact (hper.int_mul (toIcoDiv h2π 0 t)) u
    have hu2 : 2 * Real.pi * (u / (2 * Real.pi)) = u := by
      rw [mul_comm, div_mul_cancel₀ u (ne_of_gt h2π)]
    have hmem1 : u / (2 * Real.pi) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg huI.1 h2π.le, by rw [div_le_one h2π]; exact huI.2.le⟩
    have hgexp : g u = Complex.exp (Λ (⟨u / (2 * Real.pi), hmem1⟩ : unitInterval) / 2) := by
      show Complex.exp (Λ (Set.projIcc (0 : ℝ) 1 h01 (u / (2 * Real.pi))) / 2)
        = Complex.exp (Λ (⟨u / (2 * Real.pi), hmem1⟩ : unitInterval) / 2)
      rw [Set.projIcc_of_mem h01 hmem1]
    have hcurlift : Complex.exp (Λ (⟨u / (2 * Real.pi), hmem1⟩ : unitInterval)) = γ u - z := by
      have h := hΛ (⟨u / (2 * Real.pi), hmem1⟩ : unitInterval)
      rw [hc] at h
      simpa [curveLoop, hu2] using h
    have hsq : Complex.exp (Λ (⟨u / (2 * Real.pi), hmem1⟩ : unitInterval) / 2)
        * Complex.exp (Λ (⟨u / (2 * Real.pi), hmem1⟩ : unitInterval) / 2)
        = Complex.exp (Λ (⟨u / (2 * Real.pi), hmem1⟩ : unitInterval)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [hηu, hgval u huI, hgexp, hsq, hcurlift, htu]
  have hηne : ∀ t : ℝ, η t ≠ 0 := by
    intro t ht
    have h := hηsq t
    rw [ht, mul_zero] at h
    exact hz t (sub_eq_zero.mp h.symm)
  -- The winding number of the square root is half the winding number of the loop.
  have hηwind : Work.Smooth.SphereJordan.windNumber (fun t : ℝ => η t) η.continuous 0 = m := by
    set u : C(unitInterval, ℂ) :=
      curveLoop (fun t : ℝ => η t - 0) (η.continuous.sub continuous_const) with hu
    have hune : ∀ t, u t ≠ 0 := by
      intro t
      rw [hu]
      exact sub_ne_zero.mpr (by simpa using hηne (2 * Real.pi * (t : ℝ)))
    have huloop : u 0 = u 1 := by
      rw [hu]
      show η (2 * Real.pi * ((0 : unitInterval) : ℝ)) - 0
        = η (2 * Real.pi * ((1 : unitInterval) : ℝ)) - 0
      have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by norm_num
      have h1 : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by norm_num
      have hper0 : η 0 = η (2 * Real.pi) := by simpa using (hηper 0).symm
      rw [h0, h1, sub_zero, sub_zero]
      exact hper0
    have hprod : ∀ t : unitInterval, (u * u) t = c t := by
      intro t
      rw [ContinuousMap.mul_apply, hu, hc]
      show (η (2 * Real.pi * (t : ℝ)) - 0) * (η (2 * Real.pi * (t : ℝ)) - 0)
        = γ (2 * Real.pi * (t : ℝ)) - z
      rw [sub_zero]
      exact hηsq _
    have hmul := loopIndex_mul u u hune hune huloop huloop
    have huloop' : (u * u) 0 = (u * u) 1 := by
      simp only [ContinuousMap.mul_apply]
      rw [huloop]
    have hcongr := loopIndex_congr hprod (fun t => mul_ne_zero (hune t) (hune t)) hcne
      huloop' hcloop
    have htwo : loopIndex u + loopIndex u = 2 * m := by rw [← hmul, hcongr, hWc]
    have hwind : Work.Smooth.SphereJordan.windNumber (fun t : ℝ => η t) η.continuous 0
        = loopIndex u := rfl
    rw [hwind]
    omega
  exact ⟨η, hηsq, hηne, hηper, hηwind⟩

end Work.Smooth.SphereJordan
