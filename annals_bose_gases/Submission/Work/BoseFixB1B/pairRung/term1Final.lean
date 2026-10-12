import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B.pairRung

theorem term1Final {N : ℕ} {Ks a PM X S c V Kc δ I : ℝ}
    (hV : 0 < V) (hc : 0 < c) (hKs : 0 < Ks) (ha : 0 < a) (hPM : 0 < PM) (hX : 0 ≤ X)
    (hI0 : 0 ≤ I) (hS : S ≤ (N : ℝ)) (hS0 : 0 ≤ S) (hc3 : c ^ 3 * V ≤ Kc) (hKc : 0 ≤ Kc)
    (hδ : 8 * Ks + 2 * Ks * a * Kc / (3 * Real.pi ^ 2 * PM) ≤ 1 + δ)
    (hI : I ≤ c ^ 3 * Ks * a / (3 * Real.pi ^ 2 * V) + 4 * ((N : ℝ) + 1) * Ks * PM / V ^ 2) :
    S * X * I ≤ (1 / 2) * (1 + δ) * PM * (((N : ℝ) + 1) * (N : ℝ) / V ^ 2) * X := by
  have hV2 : (0:ℝ) < V ^ 2 := by positivity
  have hKsa : (0:ℝ) ≤ Ks * a := by positivity
  have hNn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  -- The "arithmetic budget" `Θ` collects the two admissible pieces of `I`,
  -- and `E = (1 + δ) PM / 2` is half of the δ-hypothesis' right-hand side.
  set Θ : ℝ := Ks * a * Kc / (3 * Real.pi ^ 2) with hΘ
  set E : ℝ := (1 + δ) * PM / 2 with hE
  -- `hδ` cleared of the `PM`-denominator.
  have hδPM : 8 * Ks * PM + 2 * Θ ≤ (1 + δ) * PM := by
    have h := mul_le_mul_of_nonneg_right hδ hPM.le
    have e : (8 * Ks + 2 * Ks * a * Kc / (3 * Real.pi ^ 2 * PM)) * PM
        = 8 * Ks * PM + 2 * Θ := by
      rw [hΘ]; field_simp
    rwa [e] at h
  have h8 : 8 * Ks ≤ 1 + δ := by
    have h2 : 0 ≤ 2 * Ks * a * Kc / (3 * Real.pi ^ 2 * PM) := by positivity
    linarith
  -- `4 Ks PM ≤ E`
  have hii : 4 * Ks * PM ≤ E := by
    rw [hE]
    have hm := mul_le_mul_of_nonneg_right h8 (show (0:ℝ) ≤ PM / 2 by positivity)
    linarith
  have hEpos : 0 < E := by
    have h : 0 < 4 * Ks * PM := by positivity
    linarith
  -- `Θ + 4 Ks PM ≤ E`
  have hi : Θ + 4 * Ks * PM ≤ E := by rw [hE]; linarith
  -- The `N`-dependent budget bound: `Θ + 4 (N+1) Ks PM ≤ E (N+1)`.
  have hmain : Θ + 4 * ((N:ℝ) + 1) * Ks * PM ≤ E * ((N:ℝ) + 1) := by
    have hm := mul_le_mul_of_nonneg_left hii hNn
    nlinarith [hi, hm]
  -- Step 1: the `c^3 V ≤ Kc` substitution.
  have h1 : c ^ 3 * Ks * a / (3 * Real.pi ^ 2 * V) ≤ Ks * a * Kc / (3 * Real.pi ^ 2 * V ^ 2) := by
    have hstep : (c ^ 3 * V) * (Ks * a) ≤ Kc * (Ks * a) := mul_le_mul_of_nonneg_right hc3 hKsa
    have hdiv := div_le_div_of_nonneg_right hstep (show (0:ℝ) ≤ 3 * Real.pi^2 * V^2 by positivity)
    have e1 : (c^3 * V) * (Ks*a) / (3 * Real.pi^2 * V^2) = c^3 * Ks * a / (3 * Real.pi^2 * V) := by
      field_simp
    have e2 : Kc * (Ks*a) / (3 * Real.pi^2 * V^2) = Ks * a * Kc / (3 * Real.pi^2 * V^2) := by ring
    rwa [e1, e2] at hdiv
  -- Step 2: `I ≤ (Θ + 4 (N+1) Ks PM) / V^2`.
  have hI1 : I ≤ (Θ + 4 * ((N:ℝ) + 1) * Ks * PM) / V ^ 2 := by
    have h2 : I ≤ Ks * a * Kc / (3 * Real.pi ^ 2 * V ^ 2) + 4 * ((N:ℝ)+1) * Ks * PM / V ^ 2 := by
      linarith [hI, h1]
    have e : Ks * a * Kc / (3 * Real.pi ^ 2 * V ^ 2) + 4 * ((N:ℝ)+1) * Ks * PM / V ^ 2
        = (Θ + 4 * ((N:ℝ)+1) * Ks * PM) / V ^ 2 := by
      rw [hΘ]; field_simp
    rwa [e] at h2
  have hI1' : I * V^2 ≤ Θ + 4 * ((N:ℝ)+1) * Ks * PM := by
    have h := mul_le_mul_of_nonneg_right hI1 hV2.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hV2)] at h
  -- Step 3: multiply through by `S X V^2` and use `S ≤ N`.
  have hfinal : S * X * I * V^2 ≤ (1/2)*(1+δ)*PM*(((N:ℝ)+1)*(N:ℝ))*X := by
    have hSX : 0 ≤ S * X := mul_nonneg hS0 hX
    have hA0 : 0 ≤ Θ + 4 * ((N:ℝ)+1) * Ks * PM := by
      have h1 : 0 ≤ Θ := by rw [hΘ]; positivity
      have h2 : 0 ≤ 4 * ((N:ℝ)+1) * Ks * PM := by positivity
      linarith
    have hstep1 : S * X * (I * V^2) ≤ S * X * (Θ + 4 * ((N:ℝ)+1) * Ks * PM) :=
      mul_le_mul_of_nonneg_left hI1' hSX
    have hstep2 : S * (Θ + 4 * ((N:ℝ)+1) * Ks * PM) ≤ (N:ℝ) * (Θ + 4 * ((N:ℝ)+1) * Ks * PM) :=
      mul_le_mul_of_nonneg_right hS hA0
    have hstep3 : (N:ℝ) * (Θ + 4 * ((N:ℝ)+1) * Ks * PM) ≤ (N:ℝ) * (E * ((N:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hmain hNn
    calc S * X * I * V^2 = S * X * (I * V^2) := by ring
      _ ≤ S * X * (Θ + 4 * ((N:ℝ)+1) * Ks * PM) := hstep1
      _ = (S * (Θ + 4 * ((N:ℝ)+1) * Ks * PM)) * X := by ring
      _ ≤ ((N:ℝ) * (Θ + 4 * ((N:ℝ)+1) * Ks * PM)) * X := mul_le_mul_of_nonneg_right hstep2 hX
      _ ≤ ((N:ℝ) * (E * ((N:ℝ)+1))) * X := mul_le_mul_of_nonneg_right hstep3 hX
      _ = (1/2)*(1+δ)*PM*(((N:ℝ)+1)*(N:ℝ))*X := by rw [hE]; ring
  -- Divide by `V^2 > 0` and rewrite the right-hand side into the requested shape.
  have hrew : (1/2)*(1+δ)*PM*(((N:ℝ)+1)*(N:ℝ)/V^2)*X
      = ((1/2)*(1+δ)*PM*(((N:ℝ)+1)*(N:ℝ))*X)/V^2 := by
    field_simp
  rw [hrew]
  exact (le_div_iff₀ hV2).mpr hfinal

end Work.BoseFixB1B.pairRung
