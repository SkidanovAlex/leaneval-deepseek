import Mathlib.Analysis.Polynomial.MahlerMeasure

open Polynomial

namespace Commons.NumberTheory.Polynomial

/-- The canonical ring homomorphism `ℤ →+* ℂ` is an isometry for the norm on `ℤ`
(given by the absolute value) and the complex modulus. -/
lemma isometry_intCastRingHom_complex : Isometry (Int.castRingHom ℂ) := by
  rw [isometry_iff_dist_eq]
  intro x y
  change dist (x : ℂ) (y : ℂ) = dist x y
  rw [dist_eq_norm, dist_eq_norm]
  have h : ((x : ℂ) - (y : ℂ)) = ((x - y : ℤ) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_intCast, Int.norm_eq_abs]

/-- For a monic integer polynomial of degree `m` and Mahler measure at most `S ≥ 1`, every
coefficient is bounded by `2 ^ m * S` in absolute value.  Consequently the number of such
polynomials is at most `(2 ^ m * S) ^ m`, and the crude estimate `(2 ^ (m + 2) * S) ^ m`
follows. -/
theorem ncard_monic_intpoly_mahler_le (m : ℕ) (S : ℝ) (hS : 1 ≤ S) :
    (({f : Polynomial ℤ | f.Monic ∧ f.natDegree = m ∧
        Polynomial.mapMahlerMeasure f (Int.castRingHom ℂ) ≤ S} : Set (Polynomial ℤ)).ncard : ℝ)
      ≤ ((2 : ℝ) ^ (m + 2) * S) ^ m := by
  have hS0 : (0 : ℝ) ≤ S := le_trans zero_le_one hS
  set T : Set (Polynomial ℤ) :=
    {f : Polynomial ℤ | f.Monic ∧ f.natDegree = m ∧
      Polynomial.mapMahlerMeasure f (Int.castRingHom ℂ) ≤ S} with hT
  set B : ℝ := (2 : ℝ) ^ m * S with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; exact mul_nonneg (by positivity) hS0
  set N : ℤ := ⌊B⌋ with hNdef
  have hN0 : 0 ≤ N := by rw [hNdef]; exact Int.floor_nonneg.mpr hB0
  set n : ℕ := N.toNat with hndef
  have hnN : (n : ℤ) = N := by rw [hndef]; exact Int.toNat_of_nonneg hN0
  have hnfloor : (⌊B⌋ : ℤ) = (n : ℤ) := by rw [← hNdef, ← hnN]
  -- Every coefficient of a polynomial in `T` is bounded by `B = 2^m * S`.
  have hcoeff : ∀ f ∈ T, ∀ i : Fin m, f.coeff (i : ℕ) ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
    intro f hf i
    rw [hT] at hf
    simp only [Set.mem_ofPred_eq] at hf
    obtain ⟨hmon, hdeg, hM⟩ := hf
    have hMnn : 0 ≤ f.mapMahlerMeasure (Int.castRingHom ℂ) := mapMahlerMeasure_nonneg f (Int.castRingHom ℂ)
    have hbound : ‖f.coeff (i : ℕ)‖ ≤ B := by
      have h1 := norm_coeff_le_choose_mul_mapMahlerMeasure (Int.castRingHom ℂ)
        isometry_intCastRingHom_complex (i : ℕ) f
      rw [hdeg] at h1
      refine h1.trans ?_
      have hc : (m.choose (i : ℕ) : ℝ) ≤ (2 : ℝ) ^ m := by
        have := Nat.choose_le_two_pow m (i : ℕ)
        exact_mod_cast this
      rw [hBdef]
      exact mul_le_mul hc hM hMnn (by positivity)
    have hk : |((f.coeff (i : ℕ) : ℤ) : ℝ)| ≤ B := by
      rw [← Int.norm_eq_abs]; exact hbound
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · have hz : ((-(f.coeff (i : ℕ)) : ℤ) : ℝ) ≤ B := by
        push_cast; linarith [(abs_le.mp hk).1]
      have h2 : -(f.coeff (i : ℕ)) ≤ (n : ℤ) := by
        have h3 := Int.le_floor (a := B) (z := -(f.coeff (i : ℕ))).mpr hz
        rwa [hnfloor] at h3
      omega
    · have hup : ((f.coeff (i : ℕ) : ℤ) : ℝ) ≤ B := (abs_le.mp hk).2
      have h3 := Int.le_floor (a := B) (z := f.coeff (i : ℕ)).mpr hup
      rwa [hnfloor] at h3
  -- The coefficient map is injective on `T`.
  have hinj : Set.InjOn (fun f : Polynomial ℤ => fun i : Fin m => f.coeff (i : ℕ)) T := by
    intro f hf g hg h
    rw [hT] at hf hg
    simp only [Set.mem_ofPred_eq] at hf hg
    obtain ⟨hfmon, hfdeg, -⟩ := hf
    obtain ⟨hgmon, hgdeg, -⟩ := hg
    ext k
    rcases lt_trichotomy k m with hlt | heq | hgt
    · have hh := congr_fun h ⟨k, hlt⟩
      simpa using hh
    · have h1 : f.coeff m = 1 := by rw [← hfdeg, coeff_natDegree, hfmon.leadingCoeff]
      have h2 : g.coeff m = 1 := by rw [← hgdeg, coeff_natDegree, hgmon.leadingCoeff]
      rw [heq, h1, h2]
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [hfdeg]; exact hgt),
            coeff_eq_zero_of_natDegree_lt (by rw [hgdeg]; exact hgt)]
  -- The box of coefficient vectors.
  set K : Finset (Fin m → ℤ) :=
    Fintype.piFinset (fun _ : Fin m => Finset.Icc (-(n : ℤ)) (n : ℤ)) with hKdef
  have hKcard : K.card = (2 * n + 1) ^ m := by
    rw [hKdef, Fintype.card_piFinset]
    trans ∏ _i : Fin m, (2 * n + 1)
    · exact Finset.prod_congr rfl (fun i _ => by rw [Int.card_Icc]; omega)
    · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hle : T.ncard ≤ K.card := by
    have hmem : ∀ f ∈ T, (fun i : Fin m => f.coeff (i : ℕ)) ∈ (K : Set (Fin m → ℤ)) := by
      intro f hf
      rw [Finset.mem_coe, hKdef, Fintype.mem_piFinset]
      intro i
      exact hcoeff f hf i
    calc T.ncard ≤ (K : Set (Fin m → ℤ)).ncard :=
          Set.ncard_le_ncard_of_injOn _ hmem hinj (Finset.finite_toSet K)
      _ = K.card := Set.ncard_coe_finset K
  -- Numeric comparison.
  have hn_le_B : (n : ℝ) ≤ B := by
    have h := Int.floor_le B
    rw [← hNdef] at h
    rw [← hnN] at h
    simpa using h
  have h2m : (1 : ℝ) ≤ 2 * ((2 : ℝ) ^ m * S) := by
    have hpow : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := by rw [pow_succ]; ring
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := one_le_pow₀ (by norm_num)
    rw [hpow] at h1
    nlinarith [h1, hS]
  have hfinal : (T.ncard : ℝ) ≤ ((2 : ℝ) ^ (m + 2) * S) ^ m := by
    have hcard : (T.ncard : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) ^ m := by
      have h := hle
      rw [hKcard] at h
      exact_mod_cast h
    have hcast : ((2 * n + 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hcard
    have hBineq : 2 * (n : ℝ) + 1 ≤ (2 : ℝ) ^ (m + 2) * S := by
      have h1 : 2 * (n : ℝ) + 1 ≤ 2 * B + 1 := by linarith [hn_le_B]
      have h2 : 2 * B + 1 ≤ (2 : ℝ) ^ (m + 2) * S := by
        have hpow2 : (2 : ℝ) ^ (m + 2) * S = 4 * ((2 : ℝ) ^ m * S) := by
          rw [pow_add]; ring
        rw [hBdef, hpow2]
        linarith [h2m]
      linarith [h1, h2]
    exact hcard.trans (pow_le_pow_left₀ (by positivity) hBineq m)
  exact hfinal

end Commons.NumberTheory.Polynomial