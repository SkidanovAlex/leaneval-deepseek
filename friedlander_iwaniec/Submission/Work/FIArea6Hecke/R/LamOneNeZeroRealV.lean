import Mathlib
import Submission.Work.FIArea6Hecke.R.NoCompletionPrimaryAux
import Submission.Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq
import Submission.Work.FIArea6Hecke.R.AxisLogDefs
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts
import Submission.Work.FIArea5.S16Hecke.hecke_prod_coeff_nonneg
import Submission.Work.FIArea6Hecke.R.estermann_L_one_lower
import Submission.Work.FIArea6Hecke.R.heckeLSeries_one_eq_zeta_mul_chi4
import Submission.Work.FIArea6Hecke.R.LamOneNeZeroDefs

/-!
# `Submission.Work.FIArea6Hecke.R.LamOneNeZeroRealV`

`Lam 1 ≠ 0` for an entire completion `Lam` of the Hecke `L`-function of a **real** strict
character `χ` mod `4d` — the real case of the classical non-vanishing `L(1,χ) ≠ 0`.

The proof copies the Landau/singularity argument of
`Submission.Work/FIArea6Hecke/R/lamOneNeZeroReal.lean` (that module does not build because its
`maxHeartbeats` budget is too small; here we raise it), and adds the exceptional case in which `χ`
is trivial on the primary units mod `4d`: there the completion cannot exist at all
(`NoCompletionPrimaryAux`), so the claim holds vacuously.
-/

namespace Work.FIArea6Hecke.R

open scoped BigOperators ComplexOrder

set_option maxHeartbeats 40000000

noncomputable section

/-! ## Elementary auxiliary lemmas -/

/-- The Hecke eigenvalue sequence depends only on the values of the character. -/
lemma heckeLam_congr_funV {f g : GaussianInt → ℂ} (h : ∀ z, f z = g z) (k : ℤ) (n : ℕ) :
    Work.FIArea5.S16Hecke.heckeLam f k n = Work.FIArea5.S16Hecke.heckeLam g k n := by
  classical
  unfold Work.FIArea5.S16Hecke.heckeLam
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Work.FIArea5.S16Hecke.psi]
  rw [h z]

/-- The Hecke `L`-series depends only on the values of the character. -/
lemma heckeLSeries_congr_funV {f g : GaussianInt → ℂ} (h : ∀ z, f z = g z) (k : ℤ) :
    Work.FIArea5.S16Hecke.heckeLSeries f k = Work.FIArea5.S16Hecke.heckeLSeries g k := by
  funext s
  simp only [Work.FIArea5.S16Hecke.heckeLSeries]
  exact LSeries_congr (fun {n} _ => heckeLam_congr_funV h k n) s

/-- `LSeries f s` as an explicit `tsum` (valid for `s ≠ 0`, where the `n = 0` term vanishes). -/
lemma LSeries_eq_tsum_mulV {f : ℕ → ℂ} {s : ℂ} (hs : s ≠ 0) :
    LSeries f s = ∑' n : ℕ, f n * (n : ℂ) ^ (-s) := by
  rw [LSeries]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_def]
    simp [Complex.zero_cpow (neg_ne_zero.mpr hs)]
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

/-- `riemannZeta₁ s = (s-1)·ζ(s)` away from `s = 1`. -/
lemma riemannZeta₁_eq_sub_mulV (s : ℂ) (hs : s ≠ 1) :
    riemannZeta₁ s = (s - 1) * riemannZeta s := by
  have h := riemannZeta_eq_inv_sub_mul (s := s) hs
  have h' : (s - 1) * riemannZeta s = riemannZeta₁ s := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]
  exact h'.symm

/-- `riemannZeta₁ (-2) = 0` (the trivial zero of `ζ` at `-2`). -/
lemma riemannZeta₁_neg_twoV : riemannZeta₁ (-2) = 0 := by
  have hz : riemannZeta (-2 : ℂ) = 0 := by
    have h := riemannZeta_neg_two_mul_nat_add_one 0
    simpa using h
  have h := riemannZeta_eq_inv_sub_mul (s := (-2 : ℂ)) (by norm_num)
  rw [hz] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (inv_ne_zero (by norm_num))

/-- The cancellation `A · (E/A) = E` inside a square, the only algebraic step of the main
argument. -/
lemma sq_cancelV (A B C Dg E : ℂ) (hA : A ≠ 0) :
    (A * B * C * Dg * (E / A)) ^ 2 = (B * C * Dg * E) ^ 2 := by
  have h : A * (E / A) = E := by
    field_simp
  calc (A * B * C * Dg * (E / A)) ^ 2 = ((B * C * Dg) * (A * (E / A))) ^ 2 := by ring
    _ = ((B * C * Dg) * E) ^ 2 := by rw [h]
    _ = (B * C * Dg * E) ^ 2 := by ring

end

/-! ## The main argument (case in which a witness on the primary units exists) -/

theorem lamOneNeZeroReal_aux {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hreal : ∀ z : GaussianInt, chi z = star (chi z))
    (_hnt : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧ Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
      chi z ≠ 1)
    {Lam : ℂ → ℂ} (hAn : AnalyticOn ℂ Lam Set.univ)
    (hagr : ∀ s : ℂ, 1 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d 0 s * Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) :
    Lam 1 ≠ 0 := by
  classical
  -- suppose the value at `1` vanishes
  intro h0
  set Lc : ℂ → ℂ := Lcont d Lam with hLc
  set D : ℂ → ℂ := dslope Lc 1 with hD
  set F : ℂ → ℂ :=
    fun s => (riemannZeta₁ s * DirichletCharacter.LFunction chi4C s *
      (1 - (2 : ℂ) ^ (-s)) * D s) ^ 2 with hF
  -- ### `Lc = L(·,χ)` is entire and vanishes at `1`
  have hLam_diff : Differentiable ℂ Lam := differentiableOn_univ.mp hAn.differentiableOn
  have hLc_diff : Differentiable ℂ Lc := hLc ▸ Lcont_differentiable hd hLam_diff
  have hLc_one : Lc 1 = 0 := by
    rw [hLc, Lcont_one_eq, h0, zero_mul]
  have hLc_agree : ∀ s : ℂ, 1 < s.re → Lc s = Work.FIArea5.S16Hecke.heckeLSeries chi 0 s := by
    intro s hs
    have hne : Work.FITop4.Bridge.heckeArch d 0 s ≠ 0 :=
      Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd 0 (by linarith)
    rw [hLc, Lcont_eq_div, hagr s hs]
    exact mul_div_cancel_left₀ _ hne
  -- ### the nonnegative coefficient series of `L(1)²·L(χ)²`
  obtain ⟨a, ha1, hapos, habsc, hser⟩ :=
    Work.FIArea6Hecke.R.estermann_coeff_facts (chi₁ := fun _ => (1 : ℂ)) (chi₂ := chi)
      rfl hchi.1.1 (fun z => by simp) hreal (fun z w => by ring) hchi.1.2.1
      (fun z => by simp) hchi.1.2.2.1
  -- ### the auxiliary functions are entire
  have hD_diff : Differentiable ℂ D := by
    rw [hD]
    exact differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope (s := Set.univ) (c := 1) Filter.univ_mem).mpr
        hLc_diff.differentiableOn)
  have hF_diff : Differentiable ℂ F := by
    rw [hF]
    have hZ : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁
    have hP : Differentiable ℂ (DirichletCharacter.LFunction chi4C) :=
      DirichletCharacter.differentiable_LFunction chi4C_ne_one
    have hQ : Differentiable ℂ (fun s : ℂ => 1 - (2 : ℂ) ^ (-s)) :=
      (differentiable_const (c := (1 : ℂ))).sub
        (Differentiable.const_cpow (f := fun s : ℂ => -s) (c := (2 : ℂ))
          differentiable_id.neg (Or.inl (by norm_num)))
    exact (((hZ.mul hP).mul hQ).mul hD_diff).pow 2
  -- ### the L-series identity on `re s > 2`
  have hEqOn : Set.EqOn F (LSeries fun n : ℕ => (a n : ℂ)) {s : ℂ | (2 : ℝ) < s.re} := by
    intro s hs
    have hs2 : (2 : ℝ) < s.re := hs
    have hs1 : 1 < s.re := by linarith
    have hs0 : s ≠ 0 := by intro h; rw [h] at hs1; norm_num at hs1
    have hs1ne : s ≠ 1 := by intro h; rw [h] at hs1; norm_num at hs1
    have hlast : Work.FIArea5.S16Hecke.heckeLSeries
        (fun z : GaussianInt => (fun _ => (1 : ℂ)) z * chi z) 0 s
        = Work.FIArea5.S16Hecke.heckeLSeries chi 0 s := by
      rw [heckeLSeries_congr_funV (f := fun z : GaussianInt => (fun _ => (1 : ℂ)) z * chi z)
        (g := chi) (fun z => by simp) 0]
    have hDval : D s = Lc s / (s - 1) := by
      rw [hD, dslope_of_ne _ hs1ne, slope_def_module, smul_eq_mul, hLc_one]
      ring
    have hZval : riemannZeta₁ s = (s - 1) * riemannZeta s := riemannZeta₁_eq_sub_mulV s hs1ne
    have hPval : DirichletCharacter.LFunction chi4C s
        = LSeries Work.FIArea6Hecke.R.axisChi4 s :=
      (LSeries_axisChi4_eq_LFunction hs1).symm
    rw [LSeries_eq_tsum_mulV hs0, hser s hs1, hlast, ← hLc_agree s hs1,
      heckeLSeries_one_eq_zeta_mul_chi4 hs1, hF]
    simp only []
    rw [hZval, hPval, hDval]
    rw [sq_cancelV (s - 1) (riemannZeta s) (LSeries Work.FIArea6Hecke.R.axisChi4 s)
      (1 - (2 : ℂ) ^ (-s)) (Lc s) (sub_ne_zero.mpr hs1ne)]
    ring
  -- ### positivity contradicts the trivial zero at `-2`
  have hFneg : F (-2) = 0 := by
    rw [hF]
    simp only []
    rw [riemannZeta₁_neg_twoV]
    ring
  have ha0 : (0 : ℕ → ℂ) ≤ fun n : ℕ => ((a n : ℝ) : ℂ) := by
    intro n
    show (0 : ℂ) ≤ ((a n : ℝ) : ℂ)
    rw [Complex.nonneg_iff, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨hapos n, rfl⟩
  have ha1' : (0 : ℂ) < ((a 1 : ℝ) : ℂ) := by
    rw [ha1, Complex.lt_def, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨by norm_num, rfl⟩
  have hx : LSeries.abscissaOfAbsConv (fun n : ℕ => ((a n : ℝ) : ℂ)) ≤ ((2 : ℝ) : EReal) :=
    le_of_lt habsc
  have hpos : (0 : ℂ) < F (-2) := by
    -- the lemma's conclusion is at `((-2 : ℝ) : ℂ)`; convert by an explicit rewrite rather
    -- than by defeq (which unfolds the real numbers and hangs)
    have h := @LSeries.positive_of_differentiable_of_eqOn (fun n : ℕ => ((a n : ℝ) : ℂ))
      ha0 ha1' F hF_diff (2 : ℝ) hx hEqOn (-2)
    have hc : (((-2 : ℝ)) : ℂ) = (-2 : ℂ) := by push_cast; rfl
    rwa [hc] at h
  rw [hFneg] at hpos
  exact lt_irrefl (0 : ℂ) hpos

/-! ## The requested statement -/

theorem LamOneNeZeroRealV {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hre : ∀ z : GaussianInt, chi z = star (chi z))
    {Lam : ℂ → ℂ} (hAn : AnalyticOn ℂ Lam Set.univ)
    (hagr : ∀ s : ℂ, 1 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d 0 s * Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) :
    Lam 1 ≠ 0 := by
  by_cases hexc : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d z → chi z = 1
  · -- `χ` is trivial on the primary units: the completion cannot exist at all
    exact absurd ⟨Lam, hAn, hagr⟩ (NoCompletionPrimaryAux d chi hd hchi hexc)
  · -- otherwise pick a witness and run the Landau argument
    push Not at hexc
    obtain ⟨z, hz1, hz2, hz3⟩ := hexc
    exact lamOneNeZeroReal_aux hd hchi hre ⟨z, hz1, hz2, hz3⟩ hAn hagr

end Work.FIArea6Hecke.R
