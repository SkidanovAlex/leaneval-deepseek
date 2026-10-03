import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.Star
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Order.CompletePartialOrder

namespace Commons.Measure.Lattice

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

/-- Minkowski's inequality for the `ℓ²`-expression `x ↦ √(∑ i, x i ^ 2)` on functions. -/
lemma sqrt_sum_sq_add_le {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    Real.sqrt (∑ i, (f i + g i) ^ 2) ≤
      Real.sqrt (∑ i, f i ^ 2) + Real.sqrt (∑ i, g i ^ 2) := by
  have hsum : (∑ i, (f i + g i) ^ 2) =
      (∑ i, f i ^ 2) + 2 * (∑ i, f i * g i) + (∑ i, g i ^ 2) := by
    have h1 : ∀ i, (f i + g i) ^ 2 = f i ^ 2 + 2 * (f i * g i) + g i ^ 2 := fun i => by ring
    simp only [h1]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [show (∑ i, 2 * (f i * g i)) = 2 * (∑ i, f i * g i) from (Finset.mul_sum _ _ _).symm]
  have hA0 : 0 ≤ ∑ i, f i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB0 : 0 ≤ ∑ i, g i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hCS : (∑ i, f i * g i) ^ 2 ≤ (∑ i, f i ^ 2) * (∑ i, g i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hCle : (∑ i, f i * g i) ≤ Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) := by
    have h1 : (∑ i, f i * g i) ≤ |∑ i, f i * g i| := le_abs_self _
    have h2 : |∑ i, f i * g i| = Real.sqrt ((∑ i, f i * g i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    have h3 : Real.sqrt ((∑ i, f i * g i) ^ 2) ≤
        Real.sqrt ((∑ i, f i ^ 2) * (∑ i, g i ^ 2)) := Real.sqrt_le_sqrt hCS
    have h4 : Real.sqrt ((∑ i, f i ^ 2) * (∑ i, g i ^ 2)) =
        Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) := Real.sqrt_mul hA0 _
    linarith
  have hbd : (∑ i, (f i + g i) ^ 2) ≤
      (Real.sqrt (∑ i, f i ^ 2) + Real.sqrt (∑ i, g i ^ 2)) ^ 2 := by
    rw [hsum]
    have e1 := Real.sq_sqrt hA0
    have e2 := Real.sq_sqrt hB0
    nlinarith [hCle, Real.sqrt_nonneg (∑ i, f i ^ 2), Real.sqrt_nonneg (∑ i, g i ^ 2)]
  calc Real.sqrt (∑ i, (f i + g i) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ i, f i ^ 2) + Real.sqrt (∑ i, g i ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hbd
    _ = Real.sqrt (∑ i, f i ^ 2) + Real.sqrt (∑ i, g i ^ 2) :=
        Real.sqrt_sq (by positivity)

/-- Two half-open unit cubes centred at distinct integers are disjoint. -/
lemma Ico_int_disjoint {a b : ℤ} (h : a ≠ b) (x : ℝ)
    (h₁ : x ∈ Set.Ico ((a : ℝ) - 1/2) ((a : ℝ) + 1/2))
    (h₂ : x ∈ Set.Ico ((b : ℝ) - 1/2) ((b : ℝ) + 1/2)) : False := by
  rw [Set.mem_Ico] at h₁ h₂
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hle : a + 1 ≤ b := Int.add_one_le_iff.mpr hlt
    have hleR : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hle
    linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  · have hle : b + 1 ≤ a := Int.add_one_le_iff.mpr hgt
    have hleR : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hle
    linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-- The (ENNReal) volume of the closed Euclidean ball of radius `s` in `ℝ³` is
`(4/3) π s³`. -/
lemma volume_ball_three_ennreal (s : ℝ) (hs : 0 ≤ s) :
    volume {x : Fin 3 → ℝ | Real.sqrt (∑ i : Fin 3, (x i) ^ 2) ≤ s}
      = ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * s ^ 3) := by
  have hset : {x : Fin 3 → ℝ | Real.sqrt (∑ i : Fin 3, (x i) ^ 2) ≤ s}
      = {x : Fin 3 → ℝ | (∑ i : Fin 3, |x i| ^ (2 : ℝ)) ^ ((1 : ℝ) / (2 : ℝ)) ≤ s} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [show (∑ i : Fin 3, |x i| ^ (2 : ℝ)) = ∑ i : Fin 3, (x i) ^ 2 from by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.rpow_two, sq_abs]]
    rw [← Real.sqrt_eq_rpow]
  rw [hset, MeasureTheory.volume_sum_rpow_le (Fin 3) (by norm_num : (1 : ℝ) ≤ 2) s]
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  have hgamma : (2 * Real.Gamma (1 / (2 : ℝ) + 1)) ^ 3 / Real.Gamma ((3 : ℝ) / 2 + 1)
      = 4 * Real.pi / 3 := by
    have h1 : Real.Gamma (1 / (2 : ℝ) + 1) = Real.sqrt Real.pi / 2 := by
      rw [Real.Gamma_add_one (by norm_num : (1 / (2 : ℝ)) ≠ 0), Real.Gamma_one_half_eq]
      ring
    have h2 : Real.Gamma ((3 : ℝ) / 2 + 1) = 3 * Real.sqrt Real.pi / 4 := by
      rw [show (3 : ℝ) / 2 + 1 = (1 / (2 : ℝ) + 1) + 1 by norm_num,
        Real.Gamma_add_one (by norm_num : (1 / (2 : ℝ) + 1) ≠ 0), h1]
      ring
    rw [h2, h1]
    have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_nonneg
    have hne : Real.sqrt Real.pi ≠ 0 := by positivity
    rw [show 2 * (Real.sqrt Real.pi / 2) = Real.sqrt Real.pi by ring]
    rw [pow_succ, hsq]
    field_simp
  rw [hgamma, ← ENNReal.ofReal_pow hs,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ s ^ 3)]
  congr 1
  ring

/-- The real volume of the closed Euclidean ball of radius `s` in `ℝ³` is `(4/3) π s³`. -/
lemma volume_real_ball_three (s : ℝ) (hs : 0 ≤ s) :
    volume.real {x : Fin 3 → ℝ | Real.sqrt (∑ i : Fin 3, (x i) ^ 2) ≤ s}
      = (4 / 3 : ℝ) * Real.pi * s ^ 3 := by
  rw [MeasureTheory.measureReal_def, volume_ball_three_ennreal s hs,
    ENNReal.toReal_ofReal (by positivity)]

theorem card_int_lattice_le_volume_ball_three {N : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hNR : R ≤ (N : ℝ)) :
    ((((Finset.univ : Finset (Fin 3 → Fin (2 * N + 1))).filter
        (fun k => Real.sqrt (∑ i : Fin 3, ((((k i : ℕ) : ℤ) - (N : ℤ) : ℤ) : ℝ) ^ 2) ≤ R)).card : ℕ) : ℝ)
      ≤ (4 / 3 : ℝ) * Real.pi * (R + Real.sqrt 3) ^ 3 := by
  classical
  set p : (Fin 3 → Fin (2 * N + 1)) → (Fin 3 → ℝ) :=
    fun k i => ((((k i : ℕ) : ℤ) - (N : ℤ) : ℤ) : ℝ) with hp
  set S : Finset (Fin 3 → Fin (2 * N + 1)) :=
    (Finset.univ : Finset (Fin 3 → Fin (2 * N + 1))).filter
      (fun k => Real.sqrt (∑ i : Fin 3, ((((k i : ℕ) : ℤ) - (N : ℤ) : ℤ) : ℝ) ^ 2) ≤ R) with hS
  set cube : (Fin 3 → Fin (2 * N + 1)) → Set (Fin 3 → ℝ) :=
    fun k => Set.univ.pi (fun i : Fin 3 => Set.Ico (p k i - 1/2) (p k i + 1/2)) with hcube
  have hmem : ∀ k, k ∈ S ↔ Real.sqrt (∑ i : Fin 3, (p k i) ^ 2) ≤ R := by
    intro k
    rw [hS, Finset.mem_filter]
    constructor
    · rintro ⟨_, h⟩; simpa only [hp] using h
    · rintro h; exact ⟨Finset.mem_univ _, by simpa only [hp] using h⟩
  have hcubevol : ∀ k, volume (cube k) = 1 := by
    intro k
    have hpt : ∀ i : Fin 3, volume (Set.Ico (p k i - 1/2) (p k i + 1/2)) = 1 := by
      intro i
      rw [Real.volume_Ico]
      have : (p k i + 1/2) - (p k i - 1/2) = 1 := by ring
      rw [this, ENNReal.ofReal_one]
    simp only [hcube]
    rw [volume_pi_pi]
    rw [Finset.prod_congr rfl (fun i _ => hpt i)]
    simp
  have hmeas : ∀ k, MeasurableSet (cube k) := by
    intro k
    simp only [hcube]
    exact MeasurableSet.univ_pi (fun i => measurableSet_Ico)
  have hdisj : (↑S : Set (Fin 3 → Fin (2 * N + 1))).PairwiseDisjoint cube := by
    intro k hk k' hk' hne
    change Disjoint (cube k) (cube k')
    rw [Set.disjoint_left]
    intro x hxk hxk'
    simp only [hcube] at hxk hxk'
    rw [Set.mem_univ_pi] at hxk hxk'
    obtain ⟨i, hi⟩ : ∃ i, k i ≠ k' i := by
      by_contra hcon
      exact hne (funext (by simpa using hcon))
    have hjne : (((k i : ℕ) : ℤ) - (N : ℤ)) ≠ (((k' i : ℕ) : ℤ) - (N : ℤ)) := by
      intro hcontra
      apply hi
      have hz : ((k i : ℕ) : ℤ) = ((k' i : ℕ) : ℤ) := by linarith [hcontra]
      exact Fin.ext (by exact_mod_cast hz)
    exact Ico_int_disjoint (a := ((k i : ℕ) : ℤ) - (N : ℤ))
      (b := ((k' i : ℕ) : ℤ) - (N : ℤ)) hjne (x i)
      (by simpa only [hp] using hxk i) (by simpa only [hp] using hxk' i)
  have hsub : (⋃ k ∈ S, cube k) ⊆
      {x : Fin 3 → ℝ | Real.sqrt (∑ i : Fin 3, (x i) ^ 2) ≤ R + Real.sqrt 3 / 2} := by
    intro x hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨k, hk, hxk⟩ := hx
    simp only [hcube] at hxk
    rw [Set.mem_univ_pi] at hxk
    have hkR : Real.sqrt (∑ i : Fin 3, (p k i) ^ 2) ≤ R := (hmem k).mp hk
    have hkey := sqrt_sum_sq_add_le (p k) (fun i => x i - p k i)
    have hleft : Real.sqrt (∑ i : Fin 3, (p k i + (x i - p k i)) ^ 2)
        = Real.sqrt (∑ i : Fin 3, (x i) ^ 2) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hd : Real.sqrt (∑ i : Fin 3, (x i - p k i) ^ 2) ≤ Real.sqrt 3 / 2 := by
      have hstep : ∀ i : Fin 3, (x i - p k i) ^ 2 ≤ (1/2 : ℝ) ^ 2 := by
        intro i
        have hi := hxk i
        rw [Set.mem_Ico] at hi
        exact sq_le_sq' (by linarith [hi.1]) (by linarith [hi.2])
      have hsum : (∑ i : Fin 3, (x i - p k i) ^ 2) ≤ (3 : ℝ) * (1/2 : ℝ) ^ 2 := by
        calc (∑ i : Fin 3, (x i - p k i) ^ 2) ≤ ∑ _i : Fin 3, (1/2 : ℝ) ^ 2 :=
              Finset.sum_le_sum (fun i _ => hstep i)
          _ = 3 * (1/2 : ℝ) ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
      have h3 : (3 : ℝ) * (1/2 : ℝ) ^ 2 = (Real.sqrt 3 / 2) ^ 2 := by
        rw [show (Real.sqrt 3 / 2) ^ 2 = 3 / 4 by
          rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num]
        norm_num
      rw [h3] at hsum
      calc Real.sqrt (∑ i : Fin 3, (x i - p k i) ^ 2)
          ≤ Real.sqrt ((Real.sqrt 3 / 2) ^ 2) := Real.sqrt_le_sqrt hsum
        _ = Real.sqrt 3 / 2 := Real.sqrt_sq (by positivity)
    calc Real.sqrt (∑ i : Fin 3, (x i) ^ 2)
        = Real.sqrt (∑ i : Fin 3, (p k i + (x i - p k i)) ^ 2) := hleft.symm
      _ ≤ Real.sqrt (∑ i : Fin 3, (p k i) ^ 2)
            + Real.sqrt (∑ i : Fin 3, (x i - p k i) ^ 2) := hkey
      _ ≤ R + Real.sqrt 3 / 2 := by linarith
  have hunionvol : volume (⋃ k ∈ S, cube k) = (S.card : ENNReal) := by
    rw [MeasureTheory.measure_biUnion_finset hdisj (fun b _ => hmeas b)]
    rw [Finset.sum_congr rfl (fun b _ => hcubevol b)]
    simp
  have hle : (S.card : ENNReal) ≤
      ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * (R + Real.sqrt 3 / 2) ^ 3) := by
    rw [← hunionvol, ← volume_ball_three_ennreal (R + Real.sqrt 3 / 2) (by positivity)]
    exact measure_mono hsub
  have hreal : (S.card : ℝ) ≤ (4 / 3 : ℝ) * Real.pi * (R + Real.sqrt 3 / 2) ^ 3 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at h
  calc (S.card : ℝ) ≤ (4 / 3 : ℝ) * Real.pi * (R + Real.sqrt 3 / 2) ^ 3 := hreal
    _ ≤ (4 / 3 : ℝ) * Real.pi * (R + Real.sqrt 3) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        linarith [Real.sqrt_nonneg 3]

end Commons.Measure.Lattice