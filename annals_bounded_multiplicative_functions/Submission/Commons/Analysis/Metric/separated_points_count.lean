import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Order.CompletePartialOrder

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set Metric
open scoped ENNReal

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.Analysis.Metric

noncomputable section

/-- The real (`Measure.real`) volume of a ball in the Euclidean space `ℝ^(Fin k)`
(`k ≥ 1`) of radius `ρ ≥ 0` is `ρ ^ k * (√π ^ k / Γ (k/2 + 1))`. -/
private lemma spc_ball_measure (k : ℕ) (hk : 1 ≤ k)
    (x : EuclideanSpace ℝ (Fin k)) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (volume : Measure (EuclideanSpace ℝ (Fin k))).real (Metric.ball x ρ)
      = ρ ^ k * ((Real.sqrt Real.pi) ^ k / Real.Gamma ((k : ℝ) / 2 + 1)) := by
  let γ : ℝ := (Real.sqrt Real.pi) ^ k / Real.Gamma ((k : ℝ) / 2 + 1)
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [Measure.real]
  rw [EuclideanSpace.volume_ball (Fin k) x ρ]
  simp only [Fintype.card_fin]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_pow]
  rw [ENNReal.toReal_ofReal hρ]
  have hγ0 : 0 ≤ γ := by
    dsimp [γ]
    have hgpos : 0 < Real.Gamma ((k : ℝ) / 2 + 1) := by
      apply Real.Gamma_pos_of_pos
      have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
      nlinarith
    positivity
  rw [ENNReal.toReal_ofReal hγ0]

/-- The `k ≥ 1` case of `separated_points_count`: balls of radius `r/2` around the
`r`-separated points are pairwise disjoint open balls of a Euclidean space; they are
all contained in the ball of radius `(m + 1/2) r` around `x`, so comparing real
volumes (`vol (ball ρ) = ρ^k · γ`, a fixed positive multiple of `ρ^k`) gives
`card ι ≤ (2m+1)^k ≤ 3^k (m+1)^k`. -/
private lemma spc_pos (k : ℕ) (hk : 1 ≤ k) {ι : Type*} [Fintype ι] {r : ℝ}
    (hr : 0 < r) (c : ι → EuclideanSpace ℝ (Fin k))
    (x : EuclideanSpace ℝ (Fin k)) (m : ℕ)
    (hsep : ∀ i j : ι, i ≠ j → r ≤ ‖c i - c j‖)
    (hball : ∀ i : ι, ‖c i - x‖ ≤ (m : ℝ) * r) :
    (Fintype.card ι : ℝ) ≤ (3 : ℝ) ^ k * ((m : ℝ) + 1) ^ k := by
  classical
  let μ : Measure (EuclideanSpace ℝ (Fin k)) := volume
  let r0 : ℝ := r / 2
  let R : ℝ := (m : ℝ) * r + r / 2
  let γ : ℝ := (Real.sqrt Real.pi) ^ k / Real.Gamma ((k : ℝ) / 2 + 1)
  have hr0 : 0 < r0 := by
    dsimp [r0]
    positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hγpos : 0 < γ := by
    dsimp [γ]
    have hgpos : 0 < Real.Gamma ((k : ℝ) / 2 + 1) := by
      apply Real.Gamma_pos_of_pos
      have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
      nlinarith
    positivity
  have hbmeas : ∀ (y : EuclideanSpace ℝ (Fin k)) (ρ : ℝ), 0 ≤ ρ →
      μ.real (Metric.ball y ρ) = ρ ^ k * γ := by
    intro y ρ hρ
    dsimp [μ, γ]
    exact spc_ball_measure k hk y ρ hρ
  -- the open balls of radius `r/2` around the points are pairwise disjoint
  have hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      (fun i : ι => Metric.ball (c i) r0) := by
    intro i _hi j _hj hij
    change Disjoint (Metric.ball (c i) r0) (Metric.ball (c j) r0)
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hzic : ‖z - c i‖ < r0 := by
      have hd := Metric.mem_ball.mp hzi
      simpa [dist_eq_norm] using hd
    have hzcj : ‖z - c j‖ < r0 := by
      have hd := Metric.mem_ball.mp hzj
      simpa [dist_eq_norm] using hd
    have htri : ‖c i - c j‖ ≤ ‖c i - z‖ + ‖z - c j‖ := by
      simpa [dist_eq_norm] using (dist_triangle (c i) z (c j))
    have hlt : ‖c i - c j‖ < r := by
      have h1 : ‖c i - z‖ < r0 := by simpa [norm_sub_rev] using hzic
      have h2r : 2 * r0 = r := by dsimp [r0]; ring
      nlinarith [htri, h1, hzcj, h2r]
    have hge : r ≤ ‖c i - c j‖ := hsep i j hij
    linarith
  -- and all lie inside the big ball of radius `(m + 1/2) r` around `x`
  have hsub : (⋃ i ∈ (Finset.univ : Finset ι), Metric.ball (c i) r0) ⊆
      Metric.ball x R := by
    intro z hz
    simp only [Set.mem_iUnion, exists_prop] at hz
    rcases hz with ⟨i, _hi, hzi⟩
    have hzic : ‖z - c i‖ < r0 := by
      have hd := Metric.mem_ball.mp hzi
      simpa [dist_eq_norm] using hd
    have hcix : ‖c i - x‖ ≤ (m : ℝ) * r := hball i
    have htri : ‖z - x‖ ≤ ‖z - c i‖ + ‖c i - x‖ := by
      simpa [dist_eq_norm] using (dist_triangle z (c i) x)
    have hlt : ‖z - x‖ < R := by
      have hsum : ‖z - c i‖ + ‖c i - x‖ < (m : ℝ) * r + r / 2 := by
        have hlt0 : ‖z - c i‖ + ‖c i - x‖ < r / 2 + (m : ℝ) * r := by
          dsimp [r0] at hzic
          exact add_lt_add_of_lt_of_le hzic hcix
        nlinarith
      dsimp [R]
      nlinarith [htri, hsum]
    simp [Metric.mem_ball, dist_eq_norm, hlt]
  -- measure-theoretic packing
  have hmeas := MeasureTheory.measureReal_biUnion_finset (μ := μ) (s := Finset.univ)
    (f := fun i : ι => Metric.ball (c i) r0) hdisj
    (fun b _hb => measurableSet_ball) (fun b _hb => by finiteness)
  have hmono := MeasureTheory.measureReal_mono (μ := μ) hsub
  have hvolr0 : ∀ i : ι, μ.real (Metric.ball (c i) r0) = r0 ^ k * γ := by
    intro i
    exact hbmeas (c i) r0 (le_of_lt hr0)
  have hle : (∑ i : ι, μ.real (Metric.ball (c i) r0)) ≤
      μ.real (Metric.ball x R) := by
    calc
      (∑ i : ι, μ.real (Metric.ball (c i) r0))
          = μ.real (⋃ i ∈ (Finset.univ : Finset ι), Metric.ball (c i) r0) := by
            simpa using hmeas.symm
      _ ≤ μ.real (Metric.ball x R) := hmono
  have hvolR : μ.real (Metric.ball x R) = R ^ k * γ := hbmeas x R hR
  have hle2 : (Fintype.card ι : ℝ) * (r0 ^ k * γ) ≤ R ^ k * γ := by
    have hrewrite :
        (∑ i : ι, μ.real (Metric.ball (c i) r0)) =
          (∑ _i : ι, r0 ^ k * γ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hvolr0 i
    have hsum : (∑ _i : ι, r0 ^ k * γ) =
        (Fintype.card ι : ℝ) * (r0 ^ k * γ) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hrewrite, hsum] at hle
    calc
      (Fintype.card ι : ℝ) * (r0 ^ k * γ) ≤ μ.real (Metric.ball x R) := hle
      _ = R ^ k * γ := hvolR
  have hposvol : 0 < r0 ^ k * γ := mul_pos (pow_pos hr0 k) hγpos
  have hdiv : (Fintype.card ι : ℝ) ≤ (R ^ k * γ) / (r0 ^ k * γ) := by
    have hdiv' : (Finset.univ.card : ℝ) ≤ (R ^ k * γ) / (r0 ^ k * γ) :=
      (le_div_iff₀ hposvol).2 hle2
    simpa using hdiv' 
  have hratio : (R ^ k * γ) / (r0 ^ k * γ) = (2 * (m : ℝ) + 1) ^ k := by
    have hr0ne : r0 ≠ 0 := ne_of_gt hr0
    have hγne : γ ≠ 0 := ne_of_gt hγpos
    have hrne : r ≠ 0 := ne_of_gt hr
    have hA : R / r0 = 2 * (m : ℝ) + 1 := by
      dsimp [R, r0]
      field_simp [hrne]
    have hR' : R = r0 * (2 * (m : ℝ) + 1) := by
      calc
        R = (R / r0) * r0 := by field_simp [hr0ne]
        _ = (2 * (m : ℝ) + 1) * r0 := by rw [hA]
        _ = r0 * (2 * (m : ℝ) + 1) := by ring
    rw [hR']
    rw [mul_pow]
    field_simp [hγne, pow_ne_zero k hr0ne]
  have hmain : (Fintype.card ι : ℝ) ≤ (2 * (m : ℝ) + 1) ^ k := by
    rw [hratio] at hdiv
    exact hdiv
  have hlepow : (2 * (m : ℝ) + 1) ^ k ≤ (3 * ((m : ℝ) + 1)) ^ k := by
    apply pow_le_pow_left₀
    · have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
      nlinarith
    · have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
      nlinarith
  calc
    (Fintype.card ι : ℝ) ≤ (2 * (m : ℝ) + 1) ^ k := hmain
    _ ≤ (3 * ((m : ℝ) + 1)) ^ k := hlepow
    _ = (3 : ℝ) ^ k * ((m : ℝ) + 1) ^ k := by rw [mul_pow]

/-- Any finite set of points in a Euclidean space of dimension `k` that is `r`-separated
and contained in the ball of radius `m·r` around `x` has cardinality bounded by a
constant (depending only on `k`) times `(m + 1)^k`. -/
theorem separated_points_count (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] {r : ℝ}, 0 < r →
      ∀ (c : ι → EuclideanSpace ℝ (Fin k)) (x : EuclideanSpace ℝ (Fin k)) (m : ℕ),
        (∀ i j : ι, i ≠ j → r ≤ ‖c i - c j‖) →
        (∀ i : ι, ‖c i - x‖ ≤ (m : ℝ) * r) →
        (Fintype.card ι : ℝ) ≤ C * ((m : ℝ) + 1) ^ k := by
  by_cases hk0 : k = 0
  · subst k
    refine ⟨1, by norm_num, ?_⟩
    intro ι _ι r hr c x m hsep hball
    -- In dimension 0 every two points are equal, so the hypotheses force `ι` to
    -- have at most one element.
    have hall_eq : ∀ i j : ι, i = j := by
      intro i j
      by_contra hne
      have hge : r ≤ ‖c i - c j‖ := hsep i j hne
      have hceq : c i = c j := by
        apply PiLp.ext
        intro a
        nomatch a
      have hz : ‖c i - c j‖ = 0 := by simp [hceq]
      linarith
    have hcard : Fintype.card ι ≤ 1 := Fintype.card_le_one_iff.mpr hall_eq
    rw [pow_zero, mul_one]
    exact_mod_cast hcard
  · have hk1 : 1 ≤ k := by omega
    refine ⟨3 ^ k, pow_pos (by norm_num) k, ?_⟩
    intro ι _ι r hr c x m hsep hball
    exact spc_pos k hk1 hr c x m hsep hball

end

end Commons.Analysis.Metric