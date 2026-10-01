import Mathlib
import Submission.Work.LinnikAreas.DhK.XiAux

namespace Work.LinnikAreas.FarRepel

open scoped Classical BigOperators
open Metric

set_option maxHeartbeats 0

namespace xiEg

private lemma Xi_ne_zero : Work.LinnikAreas.DhK.Xi ≠ 0 := by
  intro h
  exact Work.LinnikAreas.DhK.Xi_zero_ne (congrFun h 0)

/-- The divisor coefficient of `Ξ` at a zero inside the closed ball is at least `1`. -/
private lemma zeroCoeff_ge_one {B : ℝ} {z : ℂ} (hzB : ‖z‖ ≤ B)
    (hz0 : Work.LinnikAreas.DhK.Xi z = 0) :
    (1 : ℤ) ≤
      (MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall (0 : ℂ) B)) z := by
  have hzK : z ∈ Metric.closedBall (0 : ℂ) B := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzB
  have hnz : MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall (0 : ℂ) B) z ≠ 0 :=
    Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero
      Work.LinnikAreas.DhK.Xi_differentiable Xi_ne_zero hzK hz0
  have hnn : (0 : ℤ) ≤
      MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall (0 : ℂ) B) z :=
    Work.LinnikAreas.DhK.Xi_divisor_nonneg B z
  omega

/-- The zero set of `Ξ` in a closed ball is finite. -/
private lemma zeroSet_finite (B : ℝ) :
    ({u : ℂ | Work.LinnikAreas.DhK.Xi u = 0 ∧ ‖u‖ ≤ B} : Set ℂ).Finite := by
  refine (Work.LinnikAreas.DhK.Xi_divisor_support_finite B).subset ?_
  intro z hz
  rw [Function.mem_support]
  exact Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero
    Work.LinnikAreas.DhK.Xi_differentiable Xi_ne_zero
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz.2) hz.1

/-- The cardinality of the finite zero set of `Ξ` inside `closedBall 0 B` is at most the
(sum over all `u` of the) divisor coefficients of `Ξ` on that ball. -/
private lemma zeroCard_le_divisorFinsum (B : ℝ) :
    let Z : Set ℂ := {u : ℂ | Work.LinnikAreas.DhK.Xi u = 0 ∧ ‖u‖ ≤ B}
    ∀ hZ : Z.Finite,
      ((hZ.toFinset.card : ℝ) ≤
        ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
          (Metric.closedBall (0 : ℂ) B)) u : ℤ) : ℝ)) := by
  intro Z hZ
  let coeff : ℂ → ℤ := fun u =>
    MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall (0 : ℂ) B) u
  have hcoeff_nonneg (u : ℂ) : (0 : ℤ) ≤ coeff u := by
    exact Work.LinnikAreas.DhK.Xi_divisor_nonneg B u
  have hsupFin : (Function.support coeff).Finite := by
    simpa [coeff] using (Work.LinnikAreas.DhK.Xi_divisor_support_finite B)
  let Zfin : Finset ℂ := hZ.toFinset
  let supp : Finset ℂ := hsupFin.toFinset
  have hmem_Zfin (z : ℂ) : z ∈ Zfin ↔ z ∈ Z := by
    dsimp [Zfin]
    exact hZ.mem_toFinset
  have hmem_supp (z : ℂ) : z ∈ supp ↔ z ∈ Function.support coeff := by
    dsimp [supp]
    exact hsupFin.mem_toFinset
  have hZsub_supp : Zfin ⊆ supp := by
    intro z hz
    rw [hmem_supp]
    have hzZ : z ∈ Z := (hmem_Zfin z).1 hz
    have hmem : z ∈ Function.support coeff := by
      rw [Function.mem_support]
      dsimp [coeff]
      have hge : (1 : ℤ) ≤
          (MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall (0 : ℂ) B)) z :=
        zeroCoeff_ge_one hzZ.2 hzZ.1
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) hge)
    exact hmem
  have hsum_Zfin : (Zfin.card : ℝ) ≤ ∑ z ∈ Zfin, ((coeff z : ℤ) : ℝ) := by
    calc
      (Zfin.card : ℝ) = ∑ z ∈ Zfin, (1 : ℝ) := by
        exact_mod_cast (Finset.card_eq_sum_ones Zfin)
      _ ≤ ∑ z ∈ Zfin, ((coeff z : ℤ) : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro z hz
        have hge : (1 : ℤ) ≤ coeff z := by
          have hzZ : z ∈ Z := (hmem_Zfin z).1 hz
          exact zeroCoeff_ge_one hzZ.2 hzZ.1
        exact_mod_cast hge
  have hsum_le_supp : (∑ z ∈ Zfin, ((coeff z : ℤ) : ℝ)) ≤
      ∑ z ∈ supp, ((coeff z : ℤ) : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hZsub_supp ?_
    intro z hz _hznot
    exact_mod_cast hcoeff_nonneg z
  have hsupp_eq_finsum : (∑ z ∈ supp, ((coeff z : ℤ) : ℝ)) =
      ∑ᶠ u : ℂ, (((coeff u : ℤ) : ℝ)) := by
    refine (finsum_eq_finsetSum_of_support_subset (f := fun u : ℂ => ((coeff u : ℤ) : ℝ))
      (s := supp) ?_).symm
    intro u hu
    have huS : u ∈ Function.support coeff := by
      rw [Function.mem_support] at hu ⊢
      dsimp at hu
      exact_mod_cast hu
    exact (hmem_supp u).2 huS
  calc
    ((hZ.toFinset.card : ℝ)) = (Zfin.card : ℝ) := rfl
    _ ≤ ∑ z ∈ Zfin, ((coeff z : ℤ) : ℝ) := hsum_Zfin
    _ ≤ ∑ z ∈ supp, ((coeff z : ℤ) : ℝ) := hsum_le_supp
    _ = ∑ᶠ u : ℂ, (((coeff u : ℤ) : ℝ)) := hsupp_eq_finsum
    _ = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
          (Metric.closedBall (0 : ℂ) B)) u : ℤ) : ℝ) := by
      simp [coeff]

end xiEg

/-- **Good radius for `Ξ`.** (module `Submission.Work.LinnikAreas.FarRepel.xiE_goodRadius`; declare in `namespace Work.LinnikAreas.FarRepel`; import `Submission.Work.LinnikAreas.DhK.XiAux`.)

There is `A₀ > 0` such that for every `A ≥ A₀` there is `T` with `A ≤ T ≤ 2A` such that the circle
`|z| = T` stays at distance at least `1/(xiL A)²` from every zero `u` of
`Ξ = 1/2 + (1/2)·s(s-1)·Λ₀(s)`, i.e. `(xiL A)² * |‖u‖ - T| ≥ 1`. -/
theorem xiE_goodRadius :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      ∃ T : ℝ, A ≤ T ∧ T ≤ 2 * A ∧
        ∀ u : ℂ, Work.LinnikAreas.DhK.Xi u = 0 → (Work.LinnikAreas.DhK.xiL A) ^ 2 * |‖u‖ - T| ≥ 1 := by
  classical
  rcases Work.LinnikAreas.DhK.Xi_zeroCount_L with ⟨c0, _hc0nn, hc0⟩
  let c : ℝ := max c0 1
  have hc0le : c0 ≤ c := le_max_left c0 1
  have hcge1 : (1 : ℝ) ≤ c := le_max_right c0 1
  have hcge0 : 0 ≤ c := by linarith
  have hc_bound : ∀ R : ℝ, 2 ≤ R →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
          (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ)) ≤
        c * R * Work.LinnikAreas.DhK.xiL R := by
    intro R hR
    have hR0 : 0 ≤ R := by linarith
    have hℓR0 : 0 ≤ Work.LinnikAreas.DhK.xiL R := by
      rw [Work.LinnikAreas.DhK.xiL]
      have h1 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
      linarith
    exact le_trans (hc0 R hR)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc0le hR0) hℓR0)
  refine ⟨max 2 (Real.exp (12 * c + 10)), ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  · intro A hA₀le
    let L : ℝ := Work.LinnikAreas.DhK.xiL A
    let B : ℝ := 2 * A + 2
    have hA2 : 2 ≤ A := le_trans (le_max_left _ _) hA₀le
    have hApos : 0 < A := by linarith
    have hLbig : 12 * c + 1 ≤ L := by
      dsimp [L, Work.LinnikAreas.DhK.xiL]
      have h1 : Real.log (Real.exp (12 * c + 10)) ≤ Real.log (A + 2) := by
        refine Real.log_le_log ?_ ?_
        · positivity
        · calc
            Real.exp (12 * c + 10) ≤ max 2 (Real.exp (12 * c + 10)) := le_max_right _ _
            _ ≤ A := hA₀le
            _ ≤ A + 2 := by linarith
      rw [Real.log_exp] at h1
      nlinarith
    have hLpos : 0 < L := by nlinarith
    have hL1 : 1 ≤ L := by nlinarith
    have hL2pos : 0 < L ^ 2 := sq_pos_of_pos hLpos
    have hB2 : 2 ≤ B := by dsimp [B]; nlinarith
    have hB0 : 0 ≤ B := by dsimp [B]; nlinarith
    have hB3 : B ≤ 3 * A := by dsimp [B]; nlinarith
    let Z : Set ℂ := {u : ℂ | Work.LinnikAreas.DhK.Xi u = 0 ∧ ‖u‖ ≤ B}
    have hZfin : Z.Finite := xiEg.zeroSet_finite B
    let Zfin : Finset ℂ := hZfin.toFinset
    let centres : Finset ℝ := Zfin.image (fun u : ℂ => ‖u‖)
    have hcentres_le : (centres.card : ℝ) ≤ (Zfin.card : ℝ) := by
      dsimp [centres]
      exact_mod_cast (Finset.card_image_le : (Zfin.image (fun u : ℂ => ‖u‖)).card ≤ Zfin.card)
    have hcardZ : (Zfin.card : ℝ) ≤
        ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
          (Metric.closedBall (0 : ℂ) B)) u : ℤ) : ℝ) := by
      simpa [Zfin, Z] using (xiEg.zeroCard_le_divisorFinsum B hZfin)
    let ℓB : ℝ := Real.log (B + 2) + 2
    have hℓB0 : 0 ≤ ℓB := by
      dsimp [ℓB]
      have h1 : 0 ≤ Real.log (B + 2) := Real.log_nonneg (by dsimp [B]; linarith)
      linarith
    have hℓB2 : ℓB ≤ 2 * L := by
      dsimp [ℓB, L, Work.LinnikAreas.DhK.xiL]
      have hlogB : Real.log (B + 2) ≤ Real.log (A + 2) + 1 := by
        have hEq : B + 2 = 2 * A + 4 := by dsimp [B]; ring
        rw [hEq]
        exact Commons.NumberTheory.Linnik.grg_log_two_mul_add_four hApos
      have hlogAp2 : 0 ≤ Real.log (A + 2) := Real.log_nonneg (by linarith)
      nlinarith
    have hmainAux : (centres.card : ℝ) * 2 < A * L ^ 2 := by
      have h1 : (centres.card : ℝ) ≤ c * B * ℓB := by
        calc
          (centres.card : ℝ) ≤ (Zfin.card : ℝ) := hcentres_le
          _ ≤ ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
                (Metric.closedBall (0 : ℂ) B)) u : ℤ) : ℝ) := hcardZ
          _ ≤ c * B * ℓB := by
            simpa [ℓB, Work.LinnikAreas.DhK.xiL] using hc_bound B hB2
      calc
        (centres.card : ℝ) * 2 ≤ c * B * ℓB * 2 := by
          exact mul_le_mul_of_nonneg_right h1 (by norm_num)
        _ ≤ c * (3 * A) * (2 * L) * 2 := by
          gcongr
        _ = 12 * c * A * L := by ring
        _ < A * L ^ 2 := by
          exact Commons.NumberTheory.Linnik.grg_poly_lt hcge0 hApos hLbig
    have hcard' : (centres.card : ℝ) * (2 / L ^ 2) < A := by
      rw [← mul_div_assoc]
      rw [div_lt_iff₀ hL2pos]
      simpa [mul_assoc] using hmainAux
    have hcard'' : (centres.card : ℝ) * (2 / L ^ 2) < 2 * A - A := by
      nlinarith [hcard']
    have hw : 0 < 2 / L ^ 2 := div_pos (by norm_num) hL2pos
    have hab : A ≤ 2 * A := by linarith
    rcases Commons.NumberTheory.Linnik.grg_exists_good_point_of_small_measure hab hw centres hcard''
      with ⟨T, hT1, hT2, hgood⟩
    have hw2 : (2 / L ^ 2) / 2 = (1 : ℝ) / L ^ 2 := by
      have hLne : L ≠ 0 := ne_of_gt hLpos
      field_simp [hLne]
    have hgood' : ∀ z ∈ centres, (1 : ℝ) / L ^ 2 ≤ |T - z| := by
      intro z hz
      rw [← hw2]
      exact hgood z hz
    refine ⟨T, hT1, hT2, ?_⟩
    intro u hu0
    have hdist : (1 : ℝ) / L ^ 2 ≤ |‖u‖ - T| := by
      by_cases huB : ‖u‖ ≤ B
      · have hmem : ‖u‖ ∈ centres := by
          dsimp [centres]
          refine Finset.mem_image.mpr ?_
          refine ⟨u, ?_, rfl⟩
          dsimp [Zfin]
          exact (hZfin.mem_toFinset).2 ⟨hu0, huB⟩
        have hd := hgood' (‖u‖) hmem
        simpa [abs_sub_comm] using hd
      · have hBlt : B < ‖u‖ := lt_of_not_ge huB
        have hbig : (2 : ℝ) ≤ ‖u‖ - T := by
          have hBT : (2 : ℝ) ≤ B - T := by
            dsimp [B]
            nlinarith [hT2]
          have h1 : B - T < ‖u‖ - T := sub_lt_sub_right hBlt T
          linarith
        have hd2 : (1 : ℝ) / L ^ 2 ≤ 2 := by
          have hle1 : (1 : ℝ) / L ^ 2 ≤ 1 :=
            Commons.NumberTheory.Linnik.grg_one_div_sq_le_one hL1
          linarith
        have hle : (1 : ℝ) / L ^ 2 ≤ ‖u‖ - T := le_trans hd2 hbig
        have hnn : 0 ≤ ‖u‖ - T := by linarith
        simpa [abs_of_nonneg hnn] using hle
    have hfin : L ^ 2 * |‖u‖ - T| ≥ 1 := by
      have h2 : 1 ≤ |‖u‖ - T| * L ^ 2 := (div_le_iff₀ hL2pos).mp hdist
      have h3 : (1 : ℝ) ≤ L ^ 2 * |‖u‖ - T| := by
        simpa [mul_comm] using h2
      linarith
    dsimp only [L] at hfin
    exact hfin

end Work.LinnikAreas.FarRepel
