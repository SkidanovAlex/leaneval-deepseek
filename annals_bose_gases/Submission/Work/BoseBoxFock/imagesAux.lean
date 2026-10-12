import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.chiScale_image_le
import Submission.Work.BoseBoxFock.qmqDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imagesAux` — the `χ`-images kernel is `L¹`-small in the column variable

This is the analytic core of `Work.BoseBoxFock.imagesWordLe`.  The `χχ`-images kernel
(`Work.BoseBoxFock.imgKernel`) is

    `imgKernel ℓ W w y = χ_ℓ(w)·(Σ'_{m ≠ 0}W(w − y + ℓ•m))·χ_ℓ(y)`,

and the point is that **the two `χ`-factors are both small wherever an image term does not
vanish**: if `W(w − y + ℓ•m) ≠ 0` with `m ≠ 0` and `W` is supported in `ball 0 R`, then `w` and
`y` are within `R` of the boundary of the support of `χ_ℓ`, so
`χ_ℓ(w)χ_ℓ(y) ≤ chiImgC K·(R/ℓ)^K` by the corpus's flatness lemma
(`Work.BoseBoxFock.chiScale_image_le`, whose constant is transcribed here with the *explicit*,
box-side-independent constant `chiImgC K := (chi_boundary_taylor K).choose ^ 2 + 1`).

Consequently the images kernel is bounded by `(R/ℓ)^K` times the *bare* images sum
`Σ'_{m≠0}|W(w − y + ℓ•m)|`, and integrating that sum over one variable costs only `‖W‖_{L¹}`
(at most `26` images can contribute).  This is what makes the kernel usable at the honest weights
`W1fun`/`W1omegaFun`, which are `L¹` but *not* bounded (FINDING §9.2).

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The **explicit** flatness constant of the `χ`-image bound at exponent `K`.  It is
independent of the box side `ℓ` and of `R` (the only dependence is on `K`, through the corpus's
`Work.BoseFixB1.chi_boundary_taylor`), which is what makes the constant of the final
`errKafz`-arithmetic uniform in `μ`. -/
noncomputable def chiImgC (K : ℕ) : ℝ := (Work.BoseFixB1.chi_boundary_taylor K).choose ^ 2 + 1

theorem chiImgC_pos (K : ℕ) : 0 < chiImgC K := by
  have h := (Work.BoseFixB1.chi_boundary_taylor K).choose_spec.1
  rw [chiImgC]
  positivity

theorem chiImgC_nonneg (K : ℕ) : 0 ≤ chiImgC K := (chiImgC_pos K).le

/-! ## The pair bound with the explicit constant -/

/-- A nonzero integer vector has norm at least `1`. -/
private lemma intVec_norm_ge_one (m : Fin 3 → ℤ) (hm : m ≠ 0) : (1 : ℝ) ≤ ‖latVec m‖ := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (funext fun j => h j)
  have h1 : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
  have h2 : (1 : ℝ) ≤ |((m i : ℤ) : ℝ)| := by exact_mod_cast h1
  have h3 : (latVec m).ofLp i = ((m i : ℤ) : ℝ) := rfl
  have h4 : ‖(latVec m).ofLp i‖ ≤ ‖latVec m‖ := PiLp.norm_apply_le (latVec m) i
  rw [h3, Real.norm_eq_abs] at h4
  linarith

/-- Elementary arithmetic: `a·b ≤ u` when `a,b ≥ 0`, `a + b ≤ u ≤ 1`. -/
private lemma mul_le_of_add_le {a b u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b ≤ u)
    (hu : u ≤ 1) : a * b ≤ u := by
  have hu0 : 0 ≤ u := le_trans (add_nonneg ha hb) h
  have h1 : a * b ≤ ((a + b) / 2) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have h2 : ((a + b) / 2) ^ 2 ≤ (u / 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h3 : (u / 2) ^ 2 ≤ u := by nlinarith [hu0, hu]
  linarith

/-- **The `χ`-images flatness bound**, with the explicit constant `chiImgC K`: if `x − y` is
within `R` of the nonzero lattice vector `ℓ•m`, then `χ_ℓ(x)χ_ℓ(y) ≤ chiImgC K·(R/ℓ)^K`.

(This is `Work.BoseBoxFock.chiScale_image_le` with the `Classical.choose`d constant exposed, so
that it can be used at a *variable* box side.) -/
theorem chiScale_pair_image_le {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hRℓ : R ≤ ℓ) (K : ℕ)
    {x y : E3} (hm : ∃ m : Fin 3 → ℤ, m ≠ 0 ∧ ‖x - y - ℓ • latVec m‖ ≤ R) :
    Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ y
      ≤ chiImgC K * (R / ℓ) ^ K := by
  set CK : ℝ := (Work.BoseFixB1.chi_boundary_taylor K).choose with hCKdef
  have hCKpos : 0 < CK := (Work.BoseFixB1.chi_boundary_taylor K).choose_spec.1
  have hCK : ∀ z : E3, ‖z‖ ≤ 1 / 2 → Submission.BoseGases.chi z ≤ CK * (1 / 2 - ‖z‖) ^ K :=
    (Work.BoseFixB1.chi_boundary_taylor K).choose_spec.2
  have hCKeq : chiImgC K = CK ^ 2 + 1 := by rw [chiImgC, hCKdef]
  have hRl_nn : 0 ≤ R / ℓ := div_nonneg hR hℓ.le
  have hRl_le_one : R / ℓ ≤ 1 := (div_le_one hℓ).mpr hRℓ
  have hbase : 0 ≤ (R / ℓ) ^ K := pow_nonneg hRl_nn K
  by_cases h1 : ‖(ℓ⁻¹ : ℝ) • x‖ < 1 / 2
  · by_cases h2 : ‖(ℓ⁻¹ : ℝ) • y‖ < 1 / 2
    · obtain ⟨m, hm0, hmR⟩ := hm
      set M : E3 := latVec m with hM
      set zx : E3 := (ℓ⁻¹ : ℝ) • x with hzx
      set zy : E3 := (ℓ⁻¹ : ℝ) • y with hzy
      have hzx_le : ‖zx‖ ≤ 1 / 2 := h1.le
      have hzy_le : ‖zy‖ ≤ 1 / 2 := h2.le
      have hM1 : (1 : ℝ) ≤ ‖M‖ := by rw [hM]; exact intVec_norm_ge_one m hm0
      have hmR' : ‖x - y - ℓ • M‖ ≤ R := by rw [hM]; exact hmR
      have hdist : ‖zx - zy - M‖ ≤ R / ℓ := by
        have hdiff : zx - zy - M = (ℓ⁻¹ : ℝ) • (x - y - ℓ • M) := by
          rw [hzx, hzy, hM, smul_sub, smul_sub, smul_smul]
          rw [inv_mul_cancel₀ (ne_of_gt hℓ), one_smul]
        rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hℓ.le),
          div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left hmR' (inv_nonneg.mpr hℓ.le)
      have hsum : (1 / 2 - ‖zx‖) + (1 / 2 - ‖zy‖) ≤ R / ℓ := by
        have h4 : ‖zx - zy‖ ≤ ‖zx‖ + ‖zy‖ := norm_sub_le zx zy
        have h5 : ‖M‖ - ‖zx - zy - M‖ ≤ ‖zx - zy‖ := by
          have h6 := norm_sub_le (zx - zy) (zx - zy - M)
          have hsub : (zx - zy) - (zx - zy - M) = M := by abel
          rw [hsub] at h6
          linarith
        linarith
      have ha_nn : 0 ≤ 1 / 2 - ‖zx‖ := by linarith
      have hb_nn : 0 ≤ 1 / 2 - ‖zy‖ := by linarith
      have hprod : Submission.BoseGases.chi zx * Submission.BoseGases.chi zy
          ≤ CK ^ 2 * ((1 / 2 - ‖zx‖) * (1 / 2 - ‖zy‖)) ^ K := by
        have haK : 0 ≤ (1 / 2 - ‖zx‖) ^ K := pow_nonneg ha_nn K
        have hbm := mul_le_mul (hCK zx hzx_le) (hCK zy hzy_le) (Submission.BoseGases.chi_nonneg zy)
          (mul_nonneg hCKpos.le haK)
        calc Submission.BoseGases.chi zx * Submission.BoseGases.chi zy
            ≤ (CK * (1 / 2 - ‖zx‖) ^ K) * (CK * (1 / 2 - ‖zy‖) ^ K) := hbm
          _ = CK ^ 2 * ((1 / 2 - ‖zx‖) ^ K * (1 / 2 - ‖zy‖) ^ K) := by ring
          _ = CK ^ 2 * ((1 / 2 - ‖zx‖) * (1 / 2 - ‖zy‖)) ^ K := by rw [mul_pow]
      have hab : (1 / 2 - ‖zx‖) * (1 / 2 - ‖zy‖) ≤ R / ℓ :=
        mul_le_of_add_le ha_nn hb_nn hsum hRl_le_one
      have hpow : ((1 / 2 - ‖zx‖) * (1 / 2 - ‖zy‖)) ^ K ≤ (R / ℓ) ^ K :=
        pow_le_pow_left₀ (mul_nonneg ha_nn hb_nn) hab K
      have hmain : Submission.BoseGases.chi zx * Submission.BoseGases.chi zy
          ≤ CK ^ 2 * (R / ℓ) ^ K :=
        le_trans hprod (mul_le_mul_of_nonneg_left hpow (sq_nonneg CK))
      have hscale : Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ y
          = Submission.BoseGases.chi zx * Submission.BoseGases.chi zy := by
        simp only [Submission.BoseGases.chiScale, hzx, hzy]
      rw [hscale, hCKeq]
      nlinarith [hmain, hbase]
    · have hy0 : Submission.BoseGases.chiScale ℓ y = 0 := by
        simp only [Submission.BoseGases.chiScale]
        exact Submission.BoseGases.chi_eq_zero_of_half_le_norm _ (not_lt.mp h2)
      rw [hy0, mul_zero]
      rw [hCKeq]
      exact mul_nonneg (by positivity) hbase
  · have hx0 : Submission.BoseGases.chiScale ℓ x = 0 := by
      simp only [Submission.BoseGases.chiScale]
      exact Submission.BoseGases.chi_eq_zero_of_half_le_norm _ (not_lt.mp h1)
    rw [hx0, zero_mul]
    rw [hCKeq]
    exact mul_nonneg (by positivity) hbase

/-! ## The pointwise finite-sum bound -/

/-- The set of (at most 26) nonzero lattice vectors of sup-norm at most `1`. -/
noncomputable def latImgSet : Finset (Fin 3 → ℤ) :=
  (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1 : ℤ) 1)).erase 0

lemma latImgSet_card : latImgSet.card = 26 := by decide

lemma zero_notMem_latImgSet : (0 : Fin 3 → ℤ) ∉ latImgSet := by
  simp [latImgSet]

lemma mem_latImgSet_iff {m : Fin 3 → ℤ} :
    m ∈ latImgSet ↔ (∀ i, m i ∈ Finset.Icc (-1 : ℤ) 1) ∧ m ≠ 0 := by
  simp [latImgSet, Fintype.mem_piFinset, and_comm]

/-- **The images kernel is bounded by the flatness factor times the bare finite images sum.**
Only the (at most `26`) lattice vectors of sup-norm `≤ 1` can contribute, and on the support of
each of them the pair `(x,y)` is `R`-close along the lattice, so the two `χ`-factors are
`≤ chiImgC K·(R/ℓ)^K`. -/
theorem imgKernel_abs_le_finsum {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hRℓ : R ≤ ℓ / 2) (K : ℕ)
    {W : E3 → ℝ} (hWs : ∀ u : E3, R ≤ ‖u‖ → W u = 0) (x y : E3) :
    |imgKernel ℓ W x y| ≤ chiImgC K * (R / ℓ) ^ K
      * ∑ m ∈ latImgSet, |W (x - y + ℓ • latVec m)| := by
  have hbase : 0 ≤ chiImgC K * (R / ℓ) ^ K :=
    mul_nonneg (chiImgC_nonneg K) (pow_nonneg (div_nonneg hR hℓ.le) K)
  have hsum0 : 0 ≤ ∑ m ∈ latImgSet, |W (x - y + ℓ • latVec m)| :=
    Finset.sum_nonneg fun m _ => abs_nonneg _
  by_cases hx : Submission.BoseGases.chiScale ℓ x = 0
  · rw [imgKernel, hx]
    simp only [zero_mul, abs_zero]
    exact mul_nonneg hbase hsum0
  by_cases hy : Submission.BoseGases.chiScale ℓ y = 0
  · rw [imgKernel, hy]
    simp only [mul_zero, abs_zero]
    exact mul_nonneg hbase hsum0
  have hxnn : 0 ≤ Submission.BoseGases.chiScale ℓ x := Submission.BoseGases.chi_nonneg _
  have hynn : 0 ≤ Submission.BoseGases.chiScale ℓ y := Submission.BoseGases.chi_nonneg _
  have hxlt : ‖x‖ < ℓ / 2 := by
    have h1 : ‖(ℓ⁻¹ : ℝ) • x‖ < 1 / 2 := by
      by_contra hcon
      exact hx (Submission.BoseGases.chi_eq_zero_of_half_le_norm _ (le_of_not_gt hcon))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ), inv_mul_eq_div] at h1
    have h3 := (div_lt_iff₀ hℓ).mp h1
    linarith
  have hylt : ‖y‖ < ℓ / 2 := by
    have h1 : ‖(ℓ⁻¹ : ℝ) • y‖ < 1 / 2 := by
      by_contra hcon
      exact hy (Submission.BoseGases.chi_eq_zero_of_half_le_norm _ (le_of_not_gt hcon))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ), inv_mul_eq_div] at h1
    have h3 := (div_lt_iff₀ hℓ).mp h1
    linarith
  -- the terms outside `latImgSet` vanish
  have hvan : ∀ m : Fin 3 → ℤ, m ∉ latImgSet →
      (if m = 0 then (0 : ℝ) else W (x - y + ℓ • latVec m)) = 0 := by
    intro m hm
    by_cases hm0 : m = 0
    · rw [if_pos hm0]
    · rw [if_neg hm0]
      refine hWs _ ?_
      -- some coordinate of `m` has absolute value at least `2`
      have hnot : ¬ ∀ i : Fin 3, m i ∈ Finset.Icc (-1 : ℤ) 1 := by
        intro h
        exact hm (mem_latImgSet_iff.mpr ⟨h, hm0⟩)
      push Not at hnot
      obtain ⟨i, hi⟩ := hnot
      have h2 : (2 : ℤ) ≤ |m i| := by
        have h2' : ¬ (-(1 : ℤ) ≤ m i ∧ m i ≤ 1) := by simpa only [Finset.mem_Icc] using hi
        have hlt : m i < -1 ∨ 1 < m i := by omega
        rcases hlt with hh | hh
        · exact le_trans (by omega : (2 : ℤ) ≤ -(m i)) (neg_le_abs (m i))
        · exact le_trans (by omega : (2 : ℤ) ≤ m i) (le_abs_self (m i))
      have hnorm : (2 : ℝ) ≤ ‖latVec m‖ := by
        have h1 : ‖(latVec m).ofLp i‖ ≤ ‖latVec m‖ := PiLp.norm_apply_le (latVec m) i
        rw [latVec_apply, Real.norm_eq_abs] at h1
        have h2' : (2 : ℝ) ≤ |((m i : ℤ) : ℝ)| := by exact_mod_cast h2
        linarith
      have hsmul : (2 : ℝ) * ℓ ≤ ‖ℓ • latVec m‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
        nlinarith [hnorm, hℓ]
      have hsub : ‖x - y‖ < ℓ := by
        have := norm_sub_le x y
        linarith
      have hkey : ‖ℓ • latVec m‖ - ‖x - y‖ ≤ ‖x - y + ℓ • latVec m‖ := by
        have h6 := abs_norm_sub_norm_le (ℓ • latVec m) (x - y + ℓ • latVec m)
        have hsub6 : ℓ • latVec m - (x - y + ℓ • latVec m) = -(x - y) := by abel
        rw [hsub6, norm_neg] at h6
        have h7 := (abs_le.mp h6).2
        linarith
      have : R ≤ ‖x - y + ℓ • latVec m‖ := by
        have : ℓ ≤ ‖x - y + ℓ • latVec m‖ := by linarith
        linarith
      exact this
  -- reduce the tsum to the finite sum
  have htsum : (∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ) else W (x - y + ℓ • latVec m)))
      = ∑ m ∈ latImgSet, W (x - y + ℓ • latVec m) := by
    rw [tsum_eq_sum hvan]
    rfl
  -- the per-term flatness bound
  have hper : ∀ m ∈ latImgSet,
      Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ y
        * |W (x - y + ℓ • latVec m)| ≤ chiImgC K * (R / ℓ) ^ K * |W (x - y + ℓ • latVec m)| := by
    intro m hm
    by_cases hW0 : W (x - y + ℓ • latVec m) = 0
    · rw [hW0, abs_zero, mul_zero, mul_zero]
    · have hm0 : m ≠ 0 := fun h => zero_notMem_latImgSet (h ▸ hm)
      have hlt : ‖x - y + ℓ • latVec m‖ < R := by
        by_contra hcon
        exact hW0 (hWs _ (le_of_not_gt hcon))
      have hpair : Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ y
          ≤ chiImgC K * (R / ℓ) ^ K :=
        chiScale_pair_image_le hℓ hR (by linarith) K
          ⟨-m, neg_ne_zero.mpr hm0, by
            have hneg : latVec (-m) = -latVec m := by
              ext i; simp [latVec]
            rw [hneg, smul_neg]
            have h2 : x - y - -(ℓ • latVec m) = x - y + ℓ • latVec m := by abel
            rw [h2]
            exact hlt.le⟩
      exact mul_le_mul_of_nonneg_right hpair (abs_nonneg _)
  calc |imgKernel ℓ W x y|
      = Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ y
          * |∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ) else W (x - y + ℓ • latVec m))| := by
        rw [imgKernel, abs_mul, abs_mul, abs_of_nonneg hxnn, abs_of_nonneg hynn]
        ring
    _ = Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ y
          * |∑ m ∈ latImgSet, W (x - y + ℓ • latVec m)| := by rw [htsum]
    _ ≤ Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ y
          * ∑ m ∈ latImgSet, |W (x - y + ℓ • latVec m)| := by
        refine mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (mul_nonneg hxnn hynn)
    _ = ∑ m ∈ latImgSet, Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ y
          * |W (x - y + ℓ • latVec m)| := by
        rw [Finset.mul_sum]
    _ ≤ ∑ m ∈ latImgSet, chiImgC K * (R / ℓ) ^ K * |W (x - y + ℓ • latVec m)| :=
        Finset.sum_le_sum hper
    _ = chiImgC K * (R / ℓ) ^ K * ∑ m ∈ latImgSet, |W (x - y + ℓ • latVec m)| := by
        rw [Finset.mul_sum]

end Work.BoseBoxFock
