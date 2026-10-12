import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.LatFar
import Submission.Work.BoseRowsFS.LatRiemannDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsL.Row2

open scoped BigOperators

set_option autoImplicit false

/-- The two lattice-vector definitions of the corpus agree definitionally. -/
lemma zvec_eq_vecZ (m : Fin 3 → ℤ) : Work.BoseRowsFS.zvec m = Work.BoseRowsFS.vecZ m := rfl

/-- Pointwise factorisation of the Gaussian weight over the three coordinates. -/
lemma exp_neg_norm_zvec_factor (a : ℝ) (m : Fin 3 → ℤ) :
    Real.exp (-(a * ‖Work.BoseRowsFS.zvec m‖ ^ 2))
      = ∏ i : Fin 3, Real.exp (-(a * (m i : ℝ) ^ 2)) := by
  rw [zvec_eq_vecZ, Work.BoseRowsFS.norm_vecZ_sq, ← Real.exp_sum, Finset.mul_sum,
    ← Finset.sum_neg_distrib]

/-- **The three-dimensional Gaussian lattice sum is bounded by the cube of a bound for the
one-dimensional one.**  If every finite partial sum of `Σ_{n : ℤ} e^{-a n²}` is at most `Z ≥ 0`,
then `Σ_{m : ℤ³} e^{-a‖m‖²} ≤ Z³`. -/
lemma tsum_pi3_zvec_le_cube (a Z : ℝ)
    (hZ : ∀ U : Finset ℤ, ∑ n ∈ U, Real.exp (-(a * (n : ℝ) ^ 2)) ≤ Z) :
    (∑' m : Fin 3 → ℤ, Real.exp (-(a * ‖Work.BoseRowsFS.zvec m‖ ^ 2))) ≤ Z ^ 3 := by
  have hZ0 : 0 ≤ Z := by simpa using hZ ∅
  refine Real.tsum_le_of_sum_le (fun m => (Real.exp_pos _).le) ?_
  intro u
  set U : Finset ℤ := u.biUnion (fun m => Finset.univ.image (fun i : Fin 3 => m i)) with hU
  have hsub : u ⊆ Fintype.piFinset (fun _ : Fin 3 => U) := by
    intro m hm
    rw [Fintype.mem_piFinset]
    intro i
    rw [hU]
    exact Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hstep2 : ∑ m ∈ Fintype.piFinset (fun _ : Fin 3 => U),
        Real.exp (-(a * ‖Work.BoseRowsFS.zvec m‖ ^ 2))
      = ∏ i : Fin 3, ∑ n ∈ U, Real.exp (-(a * (n : ℝ) ^ 2)) := by
    rw [show ∑ m ∈ Fintype.piFinset (fun _ : Fin 3 => U),
          Real.exp (-(a * ‖Work.BoseRowsFS.zvec m‖ ^ 2))
        = ∑ m ∈ Fintype.piFinset (fun _ : Fin 3 => U),
          ∏ i : Fin 3, Real.exp (-(a * (m i : ℝ) ^ 2)) from
      Finset.sum_congr rfl (fun m _ => exp_neg_norm_zvec_factor a m)]
    exact Finset.sum_prod_piFinset U
      (fun (_ : Fin 3) (n : ℤ) => Real.exp (-(a * (n : ℝ) ^ 2)))
  calc ∑ m ∈ u, Real.exp (-(a * ‖Work.BoseRowsFS.zvec m‖ ^ 2))
      ≤ ∑ m ∈ Fintype.piFinset (fun _ : Fin 3 => U),
          Real.exp (-(a * ‖Work.BoseRowsFS.zvec m‖ ^ 2)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => (Real.exp_pos _).le)
    _ = ∏ i : Fin 3, ∑ n ∈ U, Real.exp (-(a * (n : ℝ) ^ 2)) := hstep2
    _ ≤ ∏ _i : Fin 3, Z :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun n _ => (Real.exp_pos _).le))
          (fun i _ => hZ U)
    _ = Z ^ 3 := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `e^{-a} ≤ 1/2` for `a ≥ 1`. -/
lemma exp_neg_le_half {a : ℝ} (ha : 1 ≤ a) : Real.exp (-a) ≤ 1 / 2 := by
  have h1 : Real.exp (-a) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have := one_div_lt_one_div_of_lt (by norm_num : (0:ℝ) < 2) Real.exp_one_gt_two
    rw [one_div] at this
    linarith [this]
  linarith

/-- **Finite partial sums of the one-dimensional lattice Gaussian, for `a ≥ 1`.** -/
lemma coord_sum_le_of_one_le {a : ℝ} (ha : 1 ≤ a) (U : Finset ℤ) :
    ∑ n ∈ U, Real.exp (-(a * (n : ℝ) ^ 2)) ≤ 1 + 4 * Real.exp (-a) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  set g : ℤ → ℝ := fun n => Real.exp (-(a * (n : ℝ) ^ 2)) with hg
  have hsumm : Summable g := Work.BoseRowsFS.summable_int_exp_neg_mul_sq ha0
  have heven : Function.Even g := by
    intro n
    simp only [hg, Int.cast_neg, neg_sq]
  have hu0 : 0 < Real.exp (-a) := Real.exp_pos _
  have hu1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  -- the exact decomposition of the `ℤ`-sum into the `n = 0` term and the two half-lines
  have hpnat : (∑' n : ℕ+, g ↑↑n) = ∑' k : ℕ, g ((k : ℤ) + 1) := by
    have := tsum_pnat_eq_tsum_succ (f := fun k : ℕ => g (k : ℤ))
    simpa only [Nat.cast_add, Nat.cast_one] using this
  have hZeq : (∑' n : ℤ, g n) = 1 + 2 * (∑' k : ℕ, g ((k : ℤ) + 1)) := by
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsumm, hpnat, hg]
    norm_num
  -- the tail is dominated by the geometric series of ratio `e^{-a}`
  have hgeo : Summable (fun k : ℕ => Real.exp (-a) * Real.exp (-a) ^ k) :=
    (summable_geometric_of_lt_one hu0.le hu1).mul_left _
  have hpt : ∀ k : ℕ, g ((k : ℤ) + 1) ≤ Real.exp (-a) * Real.exp (-a) ^ k := by
    intro k
    have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hsq : ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 2 := by
      nlinarith [mul_nonneg hk (by linarith : (0:ℝ) ≤ (k:ℝ))]
    have h1 : g ((k : ℤ) + 1) ≤ Real.exp (-(a * ((k : ℝ) + 1))) := by
      have hcast : (((k : ℤ) + 1 : ℤ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      simp only [hg, hcast]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hsq ha0.le]
    have h2 : Real.exp (-a) * Real.exp (-a) ^ k = Real.exp (-(a * ((k : ℝ) + 1))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    linarith [h1, h2.le, h2.ge]
  have htail : (∑' k : ℕ, g ((k : ℤ) + 1))
      ≤ Real.exp (-a) / (1 - Real.exp (-a)) := by
    have hLsum : Summable (fun k : ℕ => g ((k : ℤ) + 1)) :=
      Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) hpt hgeo
    have hgeo_eq : (∑' k : ℕ, Real.exp (-a) * Real.exp (-a) ^ k)
        = Real.exp (-a) * (1 - Real.exp (-a))⁻¹ := by
      rw [tsum_mul_left (a := Real.exp (-a)) (f := fun k : ℕ => Real.exp (-a) ^ k),
        tsum_geometric_of_lt_one hu0.le hu1]
    calc (∑' k : ℕ, g ((k : ℤ) + 1))
        ≤ ∑' k : ℕ, Real.exp (-a) * Real.exp (-a) ^ k :=
          Summable.tsum_le_tsum hpt hLsum hgeo
      _ = Real.exp (-a) * (1 - Real.exp (-a))⁻¹ := hgeo_eq
      _ = Real.exp (-a) / (1 - Real.exp (-a)) := by rw [div_eq_mul_inv]
  have hmain : ∑ n ∈ U, g n ≤ 1 + 2 * (Real.exp (-a) / (1 - Real.exp (-a))) := by
    have h := hsumm.sum_le_tsum U (fun n _ => (Real.exp_pos _).le)
    rw [hZeq] at h
    linarith
  have hu2 : Real.exp (-a) ≤ 1 / 2 := exp_neg_le_half ha
  have htail2 : 2 * (Real.exp (-a) / (1 - Real.exp (-a))) ≤ 4 * Real.exp (-a) := by
    have hden : (1:ℝ) / 2 ≤ 1 - Real.exp (-a) := by linarith
    have h1 : Real.exp (-a) / (1 - Real.exp (-a)) ≤ Real.exp (-a) / (1/2) :=
      div_le_div_of_nonneg_left hu0.le (by norm_num) hden
    have h2 : Real.exp (-a) / (1/2) = 2 * Real.exp (-a) := by ring
    linarith [h1, h2.le, h2.ge]
  rw [hg]
  linarith [hmain, htail2]

theorem lattice_gauss_sum :
    (∀ a : ℝ, 1 ≤ a → ∑' m : Fin 3 → ℤ, Real.exp (-(a * ‖Work.BoseRowsFS.zvec m‖ ^ 2))
        ≤ 1 + 75 * Real.exp (-a))
      ∧ (∀ a : ℝ, 1 / 16 ≤ a → a ≤ 1 →
          ∑' m : Fin 3 → ℤ, Real.exp (-(a * ‖Work.BoseRowsFS.zvec m‖ ^ 2)) ≤ 33000) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    have hu0 : 0 < Real.exp (-a) := Real.exp_pos _
    have hu2 : Real.exp (-a) ≤ 1 / 2 := exp_neg_le_half ha
    have hcube := tsum_pi3_zvec_le_cube a (1 + 4 * Real.exp (-a))
      (fun U => coord_sum_le_of_one_le ha U)
    have harith : (1 + 4 * Real.exp (-a)) ^ 3 ≤ 1 + 75 * Real.exp (-a) := by
      nlinarith [hu0, hu2, sq_nonneg (Real.exp (-a) - 1/2), sq_nonneg (Real.exp (-a))]
    linarith
  · intro a ha16 ha1
    have ha0 : 0 < a := by linarith
    have h := Work.BoseRowsFS.tsum_pi3_exp_neg_mul_normSq_le (c := a) ha0
    rw [show (∑' m : Fin 3 → ℤ, Real.exp (-(a * ‖Work.BoseRowsFS.zvec m‖ ^ 2)))
        = (∑' m : Fin 3 → ℤ, Real.exp (-(a * ‖Work.BoseRowsFS.vecZ m‖ ^ 2))) from
      tsum_congr (fun m => by rw [zvec_eq_vecZ])]
    refine h.trans ?_
    have hsqrt : (1:ℝ) / 4 ≤ Real.sqrt a := by
      have h16 : Real.sqrt (1/16 : ℝ) = 1/4 := by
        rw [show (1/16 : ℝ) = (1/4)^2 by norm_num, Real.sqrt_sq_eq_abs]
        norm_num
      have := Real.sqrt_le_sqrt ha16
      rwa [h16] at this
    have h1 : 1 / Real.sqrt a ≤ 4 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/4) hsqrt
      have h4 : (1:ℝ) / (1/4) = 4 := by norm_num
      rwa [h4] at h
    have h2 : 2 * (1 + 1 / Real.sqrt a) ≤ 10 := by linarith
    have h3 : (2 * (1 + 1 / Real.sqrt a)) ^ 3 ≤ 10 ^ 3 :=
      pow_le_pow_left₀ (by positivity) h2 3
    linarith [h3]

end Work.BoseRowsL.Row2
