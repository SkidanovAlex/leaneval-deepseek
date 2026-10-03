import Mathlib
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.LvalStripSharpClean
import Submission.Work.FIArea6Hecke.R.LvalStripContAux
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.LvalHalfPlaneClean
import Submission.Work.FIArea6Hecke.R.NoCompletionPrimaryAux

namespace Work.FIArea6Hecke.R

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 8000000

/-! This file assembles the Cauchy-estimate derivative bound `‖Lval' s‖ ≪ d^{K(1-re s)} log^k`
on the strip `1/2 ≤ re s ≤ 1` out of the three *clean* value bounds for `Lval`:

* `LvalStripSharpClean`  — the sharp convexity bound on `1/2 ≤ re z ≤ 1`,
* `LvalStripContAux`     — the polynomial continuation bound on `3/8 ≤ re z ≤ 1`,
* `LvalHalfPlaneClean`   — the polylogarithmic bound on `1 ≤ re z`,

together with `NoCompletionPrimaryAux`, which shows that the branch in which `χ` is trivial on the
primary units is vacuous (there the agreed continuation `Lam` cannot exist, so the bound is
automatic).  The construction is self-contained and does not touch the (broken) `RAux.emBound`
module. -/

/-- The sharp strip bound on `1/2 ≤ re z ≤ 1`, uniform in the data. -/
def CleanStripSharpData (C K k : ℝ) : Prop :=
  ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
    Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
    (∀ z : GaussianInt, chi z = star (chi z)) →
    (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
    (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1) →
    ∀ (Lam : ℂ → ℂ), AnalyticOn ℂ Lam Set.univ →
    (∀ s : ℂ, 1 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
        Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
    ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 1 →
      ‖Lval d 0 Lam z‖
        ≤ C * ((d : ℝ) * (2 + |z.im|)) ^ (K * (1 - z.re))
            * (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ k

/-- The polynomial continuation bound on `3/8 ≤ re z ≤ 1`, uniform in the data. -/
def CleanStripWeakData (D : ℝ) : Prop :=
  ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
    Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
    (∀ z : GaussianInt, chi z = star (chi z)) →
    (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
    (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1) →
    ∀ (Lam : ℂ → ℂ), AnalyticOn ℂ Lam Set.univ →
    (∀ s : ℂ, 1 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
        Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
    ∀ z : ℂ, 3 / 8 ≤ z.re → z.re ≤ 1 →
      ‖Lval d 0 Lam z‖ ≤ D * (d : ℝ) ^ (10 : ℕ) * (1 + |z.im|) ^ (10 : ℕ)

/-- The polylogarithmic bound on `1 ≤ re z`, uniform in the data. -/
def CleanStripHalfData (E k : ℝ) : Prop :=
  ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
    Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
    (∀ z : GaussianInt, chi z = star (chi z)) →
    (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
    (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1) →
    ∀ (Lam : ℂ → ℂ), AnalyticOn ℂ Lam Set.univ →
    (∀ s : ℂ, 1 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
        Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
    ∀ z : ℂ, 1 ≤ z.re →
      ‖Lval d 0 Lam z‖ ≤ E * (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ k

def cleanStripM (C₀ K₀ k₀ D E k₁ : ℝ) : ℝ :=
  max (max (C₀ * 2 ^ K₀ * Real.exp (K₀ / 4) * 2 ^ k₀) (D * 2 ^ 10 + 1)) (E * 2 ^ k₁ + 1)

lemma clean_differentiable_Lval0 {d : ℕ} (hd : 1 ≤ d) {Lam : ℂ → ℂ} (hAn : AnalyticOn ℂ Lam Set.univ) :
    Differentiable ℂ (fun z : ℂ => Lval d 0 Lam z) := by
  have hdiffL : Differentiable ℂ Lam := differentiableOn_univ.mp hAn.differentiableOn
  rw [show (fun z : ℂ => Lval d 0 Lam z) = Work.FIArea5.S16Hecke.Lcont d Lam 0 from
    funext (fun z => by
      simp [Lval, Work.FIArea5.S16Hecke.Lcont, Work.FIArea5.S16Hecke.completeDenom,
        Work.FITop4.Bridge.heckeArch])]
  exact Work.FIArea5.S16Hecke.differentiable_Lcont hd hdiffL 0

lemma clean_abs_im_sub_le {z s : ℂ} {R : ℝ} (h : ‖z - s‖ ≤ R) : |z.im - s.im| ≤ R := by
  have h1 : |(z - s).im| ≤ ‖z - s‖ := Complex.abs_im_le_norm _
  have h2 : (z - s).im = z.im - s.im := by simp
  rw [h2] at h1
  linarith

lemma clean_abs_re_sub_le {z s : ℂ} {R : ℝ} (h : ‖z - s‖ ≤ R) : |z.re - s.re| ≤ R := by
  have h1 : |(z - s).re| ≤ ‖z - s‖ := Complex.abs_re_le_norm _
  have h2 : (z - s).re = z.re - s.re := by simp
  rw [h2] at h1
  linarith

lemma clean_rpow_le_rpow_exp {x y z : ℝ} (hx : 1 ≤ x) (h : y ≤ z) : x ^ y ≤ x ^ z :=
  Real.rpow_le_rpow_of_exponent_le hx h

theorem clean_deriv_bound_of_strip_data
    {C₀ K₀ k₀ D E k₁ : ℝ}
    (hC₀ : 0 < C₀) (hK₀ : 0 ≤ K₀) (hk₀ : 0 ≤ k₀) (hD : 0 < D) (hE : 0 < E) (hk₁ : 0 ≤ k₁)
    (hsharp : CleanStripSharpData C₀ K₀ k₀) (hweak : CleanStripWeakData D) (hhalf : CleanStripHalfData E k₁) :
    ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      (∀ z : GaussianInt, chi z = star (chi z)) →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
        Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1) →
      ∀ (Lam : ℂ → ℂ), AnalyticOn ℂ Lam Set.univ →
      (∀ s : ℂ, 1 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
          Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
      ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 →
        ‖deriv (fun z : ℂ => Lval d 0 Lam z) s‖
          ≤ 4 * cleanStripM C₀ K₀ k₀ D E k₁ * ((d : ℝ) * (2 + |s.im|)) ^ (max K₀ 27 * (1 - s.re))
              * (Real.log (4 * (d : ℝ) * (2 + |s.im|))) ^ (max k₀ k₁ + 1) := by
  set M : ℝ := cleanStripM C₀ K₀ k₀ D E k₁ with hM
  set K : ℝ := max K₀ 27 with hKdef
  set k : ℝ := max k₀ k₁ + 1 with hkdef
  have hKgt : K₀ ≤ K := le_max_left _ _
  have hK27 : (27 : ℝ) ≤ K := le_max_right _ _
  have hMpos : 0 < M := by rw [hM, cleanStripM]; positivity
  have hM1 : C₀ * 2 ^ K₀ * Real.exp (K₀ / 4) * 2 ^ k₀ ≤ M := by
    rw [hM, cleanStripM]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hM2 : D * 2 ^ 10 + 1 ≤ M := by
    rw [hM, cleanStripM]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hM3 : E * 2 ^ k₁ + 1 ≤ M := by rw [hM, cleanStripM]; exact le_max_right _ _
  intro d hd chi hchi hreal hb hnt Lam hAn hagr s hs1 hs2
  have hsharp' := hsharp d hd chi hchi hreal hb hnt Lam hAn hagr
  have hweak' := hweak d hd chi hchi hreal hb hnt Lam hAn hagr
  have hhalf' := hhalf d hd chi hchi hreal hb hnt Lam hAn hagr
  clear hsharp hweak hhalf
  set σ : ℝ := s.re with hσ
  set t : ℝ := s.im with ht
  set Ls : ℝ := Real.log (4 * (d : ℝ) * (2 + |t|)) with hLs
  set R : ℝ := 1 / (4 * Ls) with hR
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have ht0 : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h4d8 : (8 : ℝ) ≤ 4 * (d : ℝ) * (2 + |t|) := by nlinarith [hd1, ht0]
  have hLspos : 0 < Ls := Real.log_pos (by linarith)
  have hLs2 : (2 : ℝ) ≤ Ls := by
    have h1 : Real.log 8 ≤ Ls := by
      rw [hLs]; exact Real.log_le_log (by norm_num) h4d8
    have h2 : (2 : ℝ) < Real.log 8 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast
      linarith [Real.log_two_gt_d9]
    linarith
  have hLs1 : (1 : ℝ) ≤ Ls := by linarith
  have hRpos : 0 < R := by rw [hR]; positivity
  have hRle : R ≤ 1 / 8 := by
    rw [hR, div_le_iff₀ (by positivity : (0:ℝ) < 4 * Ls)]; linarith
  have hdiff : Differentiable ℂ (fun z : ℂ => Lval d 0 Lam z) := clean_differentiable_Lval0 hd hAn
  set Bt : ℝ := (d : ℝ) * (2 + |t|) with hBt
  have hBt1 : 1 ≤ Bt := by rw [hBt]; nlinarith [hd1, ht0]
  have hBtpos : (0:ℝ) < Bt := lt_of_lt_of_le zero_lt_one hBt1
  have hBt2 : 2 * Bt ≤ 4 * (d : ℝ) * (2 + |t|) := by rw [hBt]; nlinarith [hd1, ht0]
  have hRt : R * Ls = 1 / 4 := by rw [hR]; field_simp
  have hs1' : 1 / 2 ≤ σ := hs1
  have hs2' : σ ≤ 1 := hs2
  have hsphere : ∀ z ∈ Metric.sphere s R,
      ‖Lval d 0 Lam z‖ ≤ M * Bt ^ (K * (1 - σ)) * Ls ^ (max k₀ k₁) := by
    intro z hz
    have hzs : ‖z - s‖ = R := by rw [← dist_eq_norm]; exact Metric.mem_sphere.mp hz
    have hzim : |z.im - t| ≤ R := by simpa [ht] using clean_abs_im_sub_le (le_of_eq hzs)
    have hzre : |z.re - σ| ≤ R := by simpa [hσ] using clean_abs_re_sub_le (le_of_eq hzs)
    have hzre_low : σ - R ≤ z.re := by
      have := (abs_le.mp hzre).1; linarith
    have hzre_high : z.re ≤ σ + R := by
      have := (abs_le.mp hzre).2; linarith
    have hzim_abs : |z.im| ≤ |t| + R := by
      have h1 : |z.im| - |t| ≤ |z.im - t| := abs_sub_abs_le_abs_sub z.im t
      linarith
    have h2im : 2 + |z.im| ≤ 2 * (2 + |t|) := by linarith [hzim_abs, hRle, ht0]
    have hBz1 : (1 : ℝ) ≤ (d : ℝ) * (2 + |z.im|) := by nlinarith [hd1, abs_nonneg z.im]
    have hBz : (d : ℝ) * (2 + |z.im|) ≤ 2 * Bt := by
      rw [hBt]; nlinarith [h2im, hd1]
    -- the log comparison, avoiding `log 2` completely
    have hlogz : Real.log (4 * (d : ℝ) * (2 + |z.im|)) ≤ 2 * Ls := by
      have h5 : 4 * (d : ℝ) * (2 + |z.im|) ≤ (4 * (d : ℝ) * (2 + |t|)) ^ (2 : ℕ) := by
        have h6 : 4 * (d : ℝ) * (2 + |z.im|) ≤ 8 * (d : ℝ) * (2 + |t|) := by
          nlinarith [h2im, hd1]
        have h7 : 8 * (d : ℝ) * (2 + |t|) ≤ (4 * (d : ℝ) * (2 + |t|)) ^ (2 : ℕ) := by
          nlinarith [h4d8, hd1, ht0, sq_nonneg (4 * (d : ℝ) * (2 + |t|))]
        linarith
      calc Real.log (4 * (d : ℝ) * (2 + |z.im|))
          ≤ Real.log ((4 * (d : ℝ) * (2 + |t|)) ^ (2 : ℕ)) :=
            Real.log_le_log (by nlinarith [hd1, abs_nonneg z.im]) h5
        _ = 2 * Ls := by
            rw [hLs, Real.log_pow]
            norm_num
    have hlogz0 : 0 ≤ Real.log (4 * (d : ℝ) * (2 + |z.im|)) :=
      Real.log_nonneg (by nlinarith [hd1, abs_nonneg z.im])
    have hlogk : (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ k₀ ≤ 2 ^ k₀ * Ls ^ (max k₀ k₁) := by
      have h1 : (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ k₀ ≤ (2 * Ls) ^ k₀ :=
        Real.rpow_le_rpow hlogz0 hlogz hk₀
      have h2 : (2 * Ls) ^ k₀ = 2 ^ k₀ * Ls ^ k₀ := Real.mul_rpow (by norm_num) hLspos.le
      rw [h2] at h1
      have h3 : Ls ^ k₀ ≤ Ls ^ (max k₀ k₁) :=
        clean_rpow_le_rpow_exp hLs1 (le_max_left _ _)
      calc (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ k₀ ≤ 2 ^ k₀ * Ls ^ k₀ := h1
        _ ≤ 2 ^ k₀ * Ls ^ (max k₀ k₁) := mul_le_mul_of_nonneg_left h3 (by positivity)
    have hlogk1 : (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ k₁ ≤ 2 ^ k₁ * Ls ^ (max k₀ k₁) := by
      have h1 : (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ k₁ ≤ (2 * Ls) ^ k₁ :=
        Real.rpow_le_rpow hlogz0 hlogz hk₁
      have h2 : (2 * Ls) ^ k₁ = 2 ^ k₁ * Ls ^ k₁ := Real.mul_rpow (by norm_num) hLspos.le
      rw [h2] at h1
      have h3 : Ls ^ k₁ ≤ Ls ^ (max k₀ k₁) :=
        clean_rpow_le_rpow_exp hLs1 (le_max_right _ _)
      calc (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ k₁ ≤ 2 ^ k₁ * Ls ^ k₁ := h1
        _ ≤ 2 ^ k₁ * Ls ^ (max k₀ k₁) := mul_le_mul_of_nonneg_left h3 (by positivity)
    have hLspow_nonneg : (0:ℝ) ≤ Ls ^ (max k₀ k₁) := Real.rpow_nonneg (by linarith) _
    have hBtpow_nonneg : (0:ℝ) ≤ Bt ^ (K * (1 - σ)) := Real.rpow_nonneg hBtpos.le _
    by_cases hz1 : 1 ≤ z.re
    · -- the half-plane `re z ≥ 1`
      have h1 := hhalf' z hz1
      have h6 : (1:ℝ) ≤ Bt ^ (K * (1 - σ)) := Real.one_le_rpow hBt1 (by nlinarith [hK27, hs1'])
      have hEE : E * (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ k₁ ≤ E * (2 ^ k₁ * Ls ^ (max k₀ k₁)) :=
        mul_le_mul_of_nonneg_left hlogk1 hE.le
      have hE2 : E * (2 ^ k₁ * Ls ^ (max k₀ k₁)) ≤ M * Ls ^ (max k₀ k₁) := by
        have h5 : E * 2 ^ k₁ ≤ M := by linarith [hM3]
        calc E * (2 ^ k₁ * Ls ^ (max k₀ k₁)) = (E * 2 ^ k₁) * Ls ^ (max k₀ k₁) := by ring
          _ ≤ M * Ls ^ (max k₀ k₁) := mul_le_mul_of_nonneg_right h5 hLspow_nonneg
      have hMM : M * Ls ^ (max k₀ k₁) ≤ M * Bt ^ (K * (1 - σ)) * Ls ^ (max k₀ k₁) := by
        have h8 : M ≤ M * Bt ^ (K * (1 - σ)) := by nlinarith [hMpos, h6]
        calc M * Ls ^ (max k₀ k₁) ≤ (M * Bt ^ (K * (1 - σ))) * Ls ^ (max k₀ k₁) :=
              mul_le_mul_of_nonneg_right h8 hLspow_nonneg
          _ = M * Bt ^ (K * (1 - σ)) * Ls ^ (max k₀ k₁) := by ring
      linarith
    · have hz1' : z.re ≤ 1 := le_of_lt (lt_of_not_ge hz1)
      by_cases hz2 : 1 / 2 ≤ z.re
      · -- the sharp strip
        have h1 := hsharp' z hz2 hz1'
        have hBzp : ((d : ℝ) * (2 + |z.im|)) ^ (K₀ * (1 - z.re))
            ≤ 2 ^ K₀ * Real.exp (K₀ / 4) * Bt ^ (K * (1 - σ)) := by
          have hexp1 : K₀ * (1 - z.re) ≤ K₀ * (1 - σ + R) := by
            nlinarith [hK₀, hzre_low, hzre_high]
          have hstep1 : ((d : ℝ) * (2 + |z.im|)) ^ (K₀ * (1 - z.re))
              ≤ (2 * Bt) ^ (K₀ * (1 - σ + R)) := by
            have ha : ((d : ℝ) * (2 + |z.im|)) ^ (K₀ * (1 - z.re))
                ≤ (2 * Bt) ^ (K₀ * (1 - z.re)) :=
              Real.rpow_le_rpow (le_of_lt (lt_of_lt_of_le zero_lt_one hBz1)) hBz
                (by nlinarith [hK₀, hz2, hz1'])
            have hb : (2 * Bt) ^ (K₀ * (1 - z.re)) ≤ (2 * Bt) ^ (K₀ * (1 - σ + R)) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith [hBtpos])
                (by nlinarith [hK₀, hzre_low, hzre_high])
            exact le_trans ha hb
          have hsplit : (2 * Bt) ^ (K₀ * (1 - σ + R))
              = (2 * Bt) ^ (K₀ * (1 - σ)) * (2 * Bt) ^ (K₀ * R) := by
            rw [← Real.rpow_add (by linarith [hBtpos])]
            congr 1
            ring
          have hstep2 : (2 * Bt) ^ (K₀ * (1 - σ)) ≤ 2 ^ K₀ * Bt ^ (K * (1 - σ)) := by
            have hA : (2 * Bt) ^ (K₀ * (1 - σ)) = 2 ^ (K₀ * (1 - σ)) * Bt ^ (K₀ * (1 - σ)) :=
              Real.mul_rpow (by norm_num) hBtpos.le
            rw [hA]
            have hB : (2 : ℝ) ^ (K₀ * (1 - σ)) ≤ (2 : ℝ) ^ K₀ :=
              clean_rpow_le_rpow_exp (by norm_num) (by nlinarith [hK₀, hs1'])
            have hC : Bt ^ (K₀ * (1 - σ)) ≤ Bt ^ (K * (1 - σ)) :=
              clean_rpow_le_rpow_exp hBt1 (by nlinarith [hKgt, hs1'])
            exact mul_le_mul hB hC (Real.rpow_nonneg hBtpos.le _)
              (Real.rpow_nonneg (by norm_num) _)
          have hstep3 : (2 * Bt) ^ (K₀ * R) ≤ Real.exp (K₀ / 4) := by
            have hlog2Bt : Real.log (2 * Bt) ≤ Ls := by
              rw [hLs]
              refine Real.log_le_log (by linarith [hBtpos]) ?_
              rw [hBt]; nlinarith [hd1, ht0]
            have hKR : Ls * (K₀ * R) = K₀ / 4 := by
              calc Ls * (K₀ * R) = K₀ * (R * Ls) := by ring
                _ = K₀ * (1 / 4) := by rw [hRt]
                _ = K₀ / 4 := by ring
            calc (2 * Bt) ^ (K₀ * R) = Real.exp (Real.log (2 * Bt) * (K₀ * R)) :=
                  Real.rpow_def_of_pos (by linarith [hBtpos]) (K₀ * R)
              _ ≤ Real.exp (Ls * (K₀ * R)) :=
                  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hlog2Bt (by nlinarith [hK₀, hRpos]))
              _ = Real.exp (K₀ / 4) := by rw [hKR]
          calc ((d : ℝ) * (2 + |z.im|)) ^ (K₀ * (1 - z.re))
              ≤ (2 * Bt) ^ (K₀ * (1 - σ + R)) := hstep1
            _ = (2 * Bt) ^ (K₀ * (1 - σ)) * (2 * Bt) ^ (K₀ * R) := hsplit
            _ ≤ (2 ^ K₀ * Bt ^ (K * (1 - σ))) * Real.exp (K₀ / 4) :=
                mul_le_mul hstep2 hstep3 (Real.rpow_nonneg (by linarith [hBtpos]) _)
                  (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
                    (Real.rpow_nonneg hBtpos.le _))
            _ = 2 ^ K₀ * Real.exp (K₀ / 4) * Bt ^ (K * (1 - σ)) := by ring
        have h3 : C₀ * (((d : ℝ) * (2 + |z.im|)) ^ (K₀ * (1 - z.re))
              * (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ k₀)
            ≤ C₀ * ((2 ^ K₀ * Real.exp (K₀ / 4) * Bt ^ (K * (1 - σ)))
                * (2 ^ k₀ * Ls ^ (max k₀ k₁))) := by
          refine mul_le_mul_of_nonneg_left ?_ hC₀.le
          exact mul_le_mul hBzp hlogk (Real.rpow_nonneg hlogz0 _)
            (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_pos _).le)
              hBtpow_nonneg)
        have h4 : C₀ * ((2 ^ K₀ * Real.exp (K₀ / 4) * Bt ^ (K * (1 - σ)))
              * (2 ^ k₀ * Ls ^ (max k₀ k₁)))
            = (C₀ * 2 ^ K₀ * Real.exp (K₀ / 4) * 2 ^ k₀)
              * (Bt ^ (K * (1 - σ)) * Ls ^ (max k₀ k₁)) := by ring
        have h5 : (C₀ * 2 ^ K₀ * Real.exp (K₀ / 4) * 2 ^ k₀)
            * (Bt ^ (K * (1 - σ)) * Ls ^ (max k₀ k₁))
            ≤ M * (Bt ^ (K * (1 - σ)) * Ls ^ (max k₀ k₁)) :=
          mul_le_mul_of_nonneg_right hM1 (mul_nonneg hBtpow_nonneg hLspow_nonneg)
        have h6 : M * (Bt ^ (K * (1 - σ)) * Ls ^ (max k₀ k₁))
            = M * Bt ^ (K * (1 - σ)) * Ls ^ (max k₀ k₁) := by ring
        calc ‖Lval d 0 Lam z‖
            ≤ C₀ * ((d : ℝ) * (2 + |z.im|)) ^ (K₀ * (1 - z.re))
              * (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ k₀ := h1
          _ = C₀ * (((d : ℝ) * (2 + |z.im|)) ^ (K₀ * (1 - z.re))
              * (Real.log (4 * (d : ℝ) * (2 + |z.im|))) ^ k₀) := by ring
          _ ≤ C₀ * ((2 ^ K₀ * Real.exp (K₀ / 4) * Bt ^ (K * (1 - σ)))
                * (2 ^ k₀ * Ls ^ (max k₀ k₁))) := h3
          _ = (C₀ * 2 ^ K₀ * Real.exp (K₀ / 4) * 2 ^ k₀)
              * (Bt ^ (K * (1 - σ)) * Ls ^ (max k₀ k₁)) := h4
          _ ≤ M * (Bt ^ (K * (1 - σ)) * Ls ^ (max k₀ k₁)) := h5
          _ = M * Bt ^ (K * (1 - σ)) * Ls ^ (max k₀ k₁) := h6
      · -- the weak continuation region `3/8 ≤ re z < 1/2`
        have hz38 : 3 / 8 ≤ z.re := by linarith [hzre_low, hs1', hRle]
        have h1 := hweak' z hz38 hz1'
        have hsig : (10 : ℝ) ≤ K * (1 - σ) := by
          have hlt : z.re < 1 / 2 := lt_of_not_ge hz2
          have hσle : σ ≤ z.re + R := by
            have := (abs_le.mp hzre).2; linarith
          have h1s : 1 - σ ≥ 3 / 8 := by linarith [hσle, hlt, hRle]
          nlinarith [hK27, h1s]
        have h3 : (1 + |z.im| : ℝ) ^ (10 : ℕ) ≤ (2 * (2 + |t|)) ^ (10 : ℕ) := by
          apply pow_le_pow_left₀ (by positivity)
          linarith [h2im]
        have h4 : (2 * (2 + |t|)) ^ (10 : ℕ) = 2 ^ 10 * (2 + |t|) ^ (10 : ℕ) := by
          rw [mul_pow]
        have h5 : (d : ℝ) ^ (10 : ℕ) * (1 + |z.im|) ^ (10 : ℕ) ≤ 2 ^ 10 * Bt ^ (10 : ℝ) := by
          have h6 : (d : ℝ) ^ (10 : ℕ) * (1 + |z.im|) ^ (10 : ℕ)
              ≤ (d : ℝ) ^ (10 : ℕ) * (2 ^ 10 * (2 + |t|) ^ (10 : ℕ)) :=
            mul_le_mul_of_nonneg_left (le_trans h3 (le_of_eq h4)) (by positivity)
          have h7 : (d : ℝ) ^ (10 : ℕ) * (2 ^ 10 * (2 + |t|) ^ (10 : ℕ))
              = 2 ^ 10 * Bt ^ (10 : ℝ) := by
            rw [hBt, show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
              mul_pow]
            ring
          calc (d : ℝ) ^ (10 : ℕ) * (1 + |z.im|) ^ (10 : ℕ)
              ≤ (d : ℝ) ^ (10 : ℕ) * (2 ^ 10 * (2 + |t|) ^ (10 : ℕ)) := h6
            _ = 2 ^ 10 * Bt ^ (10 : ℝ) := h7
        have h8 : Bt ^ (10 : ℝ) ≤ Bt ^ (K * (1 - σ)) := clean_rpow_le_rpow_exp hBt1 hsig
        have h9 : D * (d : ℝ) ^ (10 : ℕ) * (1 + |z.im|) ^ (10 : ℕ)
            ≤ (D * 2 ^ 10) * Bt ^ (K * (1 - σ)) := by
          have h10 : D * ((d : ℝ) ^ (10 : ℕ) * (1 + |z.im|) ^ (10 : ℕ))
              ≤ D * (2 ^ 10 * Bt ^ (10 : ℝ)) :=
            mul_le_mul_of_nonneg_left h5 hD.le
          have h11 : D * (2 ^ 10 * Bt ^ (10 : ℝ)) = (D * 2 ^ 10) * Bt ^ (10 : ℝ) := by ring
          have h12 : (D * 2 ^ 10) * Bt ^ (10 : ℝ) ≤ (D * 2 ^ 10) * Bt ^ (K * (1 - σ)) :=
            mul_le_mul_of_nonneg_left h8 (by positivity)
          linarith [h10, h11, h12]
        have h10 : D * 2 ^ 10 ≤ M := by linarith [hM2]
        have h11 : (1 : ℝ) ≤ Ls ^ (max k₀ k₁) := Real.one_le_rpow hLs1 (by positivity)
        have h12 : M * Bt ^ (K * (1 - σ)) ≤ M * Bt ^ (K * (1 - σ)) * Ls ^ (max k₀ k₁) := by
          have h13 : (1:ℝ) ≤ Ls ^ (max k₀ k₁) := h11
          calc M * Bt ^ (K * (1 - σ)) = M * Bt ^ (K * (1 - σ)) * 1 := by ring
            _ ≤ M * Bt ^ (K * (1 - σ)) * Ls ^ (max k₀ k₁) :=
                mul_le_mul_of_nonneg_left h13 (mul_nonneg hMpos.le hBtpow_nonneg)
        calc ‖Lval d 0 Lam z‖
            ≤ D * (d : ℝ) ^ (10 : ℕ) * (1 + |z.im|) ^ (10 : ℕ) := h1
          _ ≤ (D * 2 ^ 10) * Bt ^ (K * (1 - σ)) := h9
          _ ≤ M * Bt ^ (K * (1 - σ)) := mul_le_mul_of_nonneg_right h10 hBtpow_nonneg
          _ ≤ M * Bt ^ (K * (1 - σ)) * Ls ^ (max k₀ k₁) := h12
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := s) (R := R)
    (C := M * Bt ^ (K * (1 - σ)) * Ls ^ (max k₀ k₁)) hRpos
    hdiff.diffContOnCl hsphere
  have hRinv : (M * Bt ^ (K * (1 - σ)) * Ls ^ (max k₀ k₁)) / R
      = 4 * M * Bt ^ (K * (1 - σ)) * Ls ^ k := by
    rw [hR, hkdef, Real.rpow_add hLspos]
    have hLsnz : Ls ≠ 0 := ne_of_gt hLspos
    field_simp
    rw [Real.rpow_one]
  have hgoal : (4 * M * Bt ^ (K * (1 - σ)) * Ls ^ k)
      = 4 * M * ((d : ℝ) * (2 + |s.im|)) ^ (K * (1 - s.re))
          * (Real.log (4 * (d : ℝ) * (2 + |s.im|))) ^ k := by
    rw [← hσ, ← ht, hBt, hLs]
  rw [← hgoal, ← hRinv]
  exact hcauchy

/-- **The derivative bound on the strip `1/2 ≤ re s ≤ 1`.**  Assembled from the three clean value
bounds by Cauchy's estimate on the circle of radius `1/(4 log(4d(2+|Im s|)))`; in the branch in
which `χ` is trivial on the primary units the hypothesis on `Lam` is contradictory
(`NoCompletionPrimaryAux`), so the bound is vacuous. -/
theorem LvalDerivBoundClean :
    ∃ C K k : ℝ, 0 < C ∧ 0 ≤ K ∧ 0 ≤ k ∧
      ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        (∀ z : GaussianInt, chi z = star (chi z)) →
        (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
        ∀ (Lam : ℂ → ℂ), AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
        ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 →
          ‖deriv (fun z : ℂ => Work.FIArea6Hecke.Lval d 0 Lam z) s‖
            ≤ C * ((d : ℝ) * (2 + |s.im|)) ^ (K * (1 - s.re))
                * (Real.log (4 * (d : ℝ) * (2 + |s.im|))) ^ k := by
  obtain ⟨C₀, K₀, k₀, hC₀, hK₀, hk₀, hs⟩ := LvalStripSharpClean
  obtain ⟨D, hD, hw⟩ := LvalStripContAux
  obtain ⟨E, k₁, hE, hk₁, hh⟩ := LvalHalfPlaneClean
  refine ⟨4 * cleanStripM C₀ K₀ k₀ D E k₁, max K₀ 27, max k₀ k₁ + 1, ?_, ?_, ?_, ?_⟩
  · rw [cleanStripM]; positivity
  · positivity
  · positivity
  · intro d hd chi hchi hreal hb Lam hAn hagr s hs1 hs2
    by_cases hnt : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
        Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1
    · exact clean_deriv_bound_of_strip_data hC₀ hK₀ hk₀ hD hE hk₁
        (fun d' hd' chi' hchi' hreal' hb' hnt' Lam' hAn' hagr' z hz1 hz2 =>
          hs d' hd' chi' hchi' hreal' hb' hnt' Lam' hAn' hagr' z hz1 hz2)
        (fun d' hd' chi' hchi' hreal' hb' hnt' Lam' hAn' hagr' z hz1 hz2 =>
          hw d' hd' chi' hchi' hnt' Lam' hAn' hagr' z hz1 hz2)
        (fun d' hd' chi' hchi' hreal' hb' hnt' Lam' hAn' hagr' z hz1 =>
          hh d' hd' chi' hchi' hnt' Lam' hAn' hagr' z hz1)
        d hd chi hchi hreal hb hnt Lam hAn hagr s hs1 hs2
    · push_neg at hnt
      exact absurd ⟨Lam, hAn, hagr⟩ (NoCompletionPrimaryAux d chi hd hchi hnt)

end

end Work.FIArea6Hecke.R
