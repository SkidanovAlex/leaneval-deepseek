import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Cert.Defs
import Submission.Work.FTS.EllipticEst.Cert.HkIntegrand_radial_sin
import Submission.Work.FTS.EllipticEst.OpenQAng
import Submission.Work.FTS.EllipticEst.OpenQAux
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Elliptic.PsiStar_ode
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Elliptic.L12Iterate
import Submission.Work.Elliptic.L12_eq_radial
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.EllipticEst.Cert.L12Aux.L12_moment_eq
import Submission.Work.FTS.EllipticEst.TT.L12Sin_mem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

/-! ## Bridge lemmas -/

/-- `radIter` is the one-variable operator `z∂_z` iterated: `radIter R i z = (D_z^i R)(z)`. -/
theorem radIter_eq_DzdIter (R : ℝ → ℝ) (i : ℕ) (z : ℝ) :
    Work.FTS.EllipticEst.radIter R i z = Work.Elliptic.DzdIter i R z := by
  induction i generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [Work.FTS.EllipticEst.radIter_succ, Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd]
      congr 1
      exact Filter.EventuallyEq.deriv_eq (Eventually.of_forall fun z' => ih z')

/-- The angular moment `Qang g j z = ∫_θ K(θ)·(D_z^j g) dθ` is three times the
`sinθcos²θ`-moment of `D_z^j g`. -/
theorem Qang_eq_three_Fstar (g : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    Work.Elliptic.Qang g j z = 3 * Work.Elliptic.Fstar (Work.Spaces.DzIter j g) z := by
  rw [Work.Elliptic.Qang, Work.Elliptic.Fstar]
  have h : (fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ)
      = fun θ : ℝ => 3 * (Work.Spaces.DzIter j g z θ * Work.Elliptic.sinCos2 θ) := by
    funext θ
    rw [Work.Elliptic.Ktheta, Work.Elliptic.sinCos2]
    ring
  rw [h, MeasureTheory.integral_const_mul]

/-- The angular weight `sin(2θ)^{2-η}` (the `angZ` of `Cert/Defs`) is nonnegative on `Iθ`. -/
theorem angZ_nonneg' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ angZ θ := by
  unfold angZ
  exact Real.rpow_nonneg (FstarHkOpen.sin_two_nonneg hθ) _

/-- `angZ θ ≤ 1` on `Iθ`. -/
theorem angZ_le_one' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : angZ θ ≤ 1 := by
  unfold angZ
  exact Real.rpow_le_one (FstarHkOpen.sin_two_nonneg hθ) (FstarHkOpen.sin_two_le_one θ)
    (by rw [Work.Spaces.eta]; norm_num)

/-- `angZ` is continuous. -/
theorem continuous_angZ' : Continuous angZ := by
  unfold angZ
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
    (fun θ => Or.inr (by rw [Work.Spaces.eta]; norm_num))

/-- `angZ` is integrable on `Iθ`. -/
theorem integrableOn_angZ' : MeasureTheory.IntegrableOn angZ Work.Spaces.Iθ :=
  FstarHkOpen.integrableOn_Iθ_of_abs_le
    ((continuous_angZ'.continuousOn).aestronglyMeasurable measurableSet_Icc)
    (fun θ hθ => by rw [abs_of_nonneg (angZ_nonneg' hθ)]; exact angZ_le_one' hθ)

/-- `angA α i` is nonnegative on `Iθ`. -/
theorem angA_nonneg' (α : ℝ) (i : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ angA α i θ := by
  unfold angA
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (FstarHkOpen.sin_two_nonneg hθ) _)

/-- `angA α i` is continuous on the open interval. -/
theorem continuousOn_angA' (α : ℝ) (i : ℕ) :
    ContinuousOn (fun θ => angA α i θ) (Set.Ioo 0 (π / 2)) := by
  have hsp : ContinuousOn (fun θ => Work.FTS.EllipticEst.sinProf i θ) (Set.Ioo 0 (π / 2)) :=
    (FstarHkOpen.smoothSlice_sinProf i).continuousOn.mono
      (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)
  have hpow : ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Set.Ioo 0 (π / 2)) := by
    refine ContinuousOn.rpow_const ?_ (fun θ hθ => Or.inl ?_)
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))
  unfold angA
  exact (hsp.pow 2).mul hpow

/-- `angA α i` is bounded by the angular constant `angK i` of `FstarHkOpen` on `Iθ`, for
`0 < α ≤ 1`. -/
theorem angA_le_angK' (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : angA α i θ ≤ FstarHkOpen.angK i := by
  have hγ1 : 1 ≤ Work.Spaces.gam α := (Work.Spaces.one_lt_gam hα).le
  have hγ2 : Work.Spaces.gam α ≤ 2 := by
    rw [Work.Spaces.gam]; linarith
  unfold angA
  exact FstarHkOpen.angK_bound i (Work.Spaces.gam α) hγ1 hγ2 hθ

/-- `angA α i` is integrable on `Iθ` for `0 < α ≤ 1`. -/
theorem integrableOn_angA' (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ) :
    MeasureTheory.IntegrableOn (angA α i) Work.Spaces.Iθ := by
  refine FstarHkOpen.integrableOn_Iθ_of_abs_le (f := angA α i)
    (C := FstarHkOpen.angK i) ?_ ?_
  · have h1 : MeasureTheory.AEStronglyMeasurable (angA α i)
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
      (continuousOn_angA' α i).aestronglyMeasurable measurableSet_Ioo
    rw [show (volume.restrict Work.Spaces.Iθ : Measure ℝ)
        = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) from ?_]
    · exact h1
    · rw [Work.Spaces.Iθ]
      exact (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  · intro θ hθ
    rw [abs_of_nonneg (angA_nonneg' α i hθ)]
    exact angA_le_angK' α hα hα1 i hθ

/-- A single weighted `D_z`-summand of the `ℋ^k`-integrand is dominated by the whole integrand
(pointwise, for every angle). -/
theorem slice_DzIter_mul_w_sq_le_HkIntegrand (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α k g) (j : ℕ) (hj : j ≤ k)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ * Work.Spaces.w z) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ := by
  have hw0 : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    have hfun : (fun θ : ℝ => (Work.Spaces.DzIter j g 0 θ * Work.Spaces.w 0) ^ 2)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ; rw [hw0]; ring
    rw [hfun, integral_zero]
    exact integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k g 0 θ
  · have hleS : ∀ θ : ℝ, (Work.Spaces.DzIter j g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α k g z θ :=
      fun θ => Work.Spaces.sq_le_HkIntegrand_z α k g z θ j hj
    -- a.e. domination of the `w`-weighted summand by the `sin`-weighted one
    have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.DzIter j g z θ * Work.Spaces.w z) ^ 2
          ≤ (Work.Spaces.DzIter j g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      have hmeas : (volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) : Measure ℝ)
          = volume.restrict Work.Spaces.Iθ := by
        rw [Work.Spaces.Iθ]
        exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
      rw [← hmeas]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
      have hsin_pos : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      have hsin_le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hpow_pos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
        Real.rpow_pos_of_pos hsin_pos _
      have hpow_sq_le : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 ≤ 1 := by
        have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
            = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hsin_pos.le]
          norm_num
        rw [h1]
        exact Real.rpow_le_one hsin_pos.le hsin_le (le_of_lt Work.Spaces.eta_pos)
      set x : ℝ := Work.Spaces.DzIter j g z θ with hx
      have hkey : x * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
          = (x * Work.Spaces.w z) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by ring
      rw [hkey, div_pow]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (x * Work.Spaces.w z), hpow_sq_le]
    have hmeas2 : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ =>
        (Work.Spaces.DzIter j g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := by
      refine Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.DzIter j g p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) ?_ hzpos
      refine ContinuousOn.pow ?_ 2
      refine ContinuousOn.mul ?_ Work.FTS.EllipticEst.continuousOn_wdivsin_Q0
      have hsub : Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) ⊆ Work.Spaces.nbhU := by
        rintro ⟨a, b⟩ ⟨ha, hb⟩
        have ha' : (0 : ℝ) < a := ha
        have hb1 : (0 : ℝ) < b := hb.1
        have hb2 : b < π / 2 := hb.2
        simp only [Work.Spaces.nbhU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
        exact ⟨by linarith, by linarith, by linarith [Real.pi_pos]⟩
      exact ((Work.Elliptic.contDiffOn_uncurry_DzIter_nbhU hsm j).continuousOn).mono hsub
    have hInt2 : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter j g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iθ :=
      Integrable.mono' (hmem.1 z hz) hmeas2 (Eventually.of_forall fun θ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hleS θ)
    have h1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ * Work.Spaces.w z) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
      MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
        hInt2 hae
    have h2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ :=
      MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
        (hmem.1 z hz) (Eventually.of_forall hleS)
    exact le_trans h1 h2

/-! ## Continuity of the angular moments -/

/-- The angular moment `Qang g j` is continuous on `(0,∞)`: it is the parametric integral of
the smooth family `D_z^j g` against the continuous angular weight `K(θ)`. -/
theorem continuousOn_Qang (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g) (j : ℕ) :
    ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi 0) := by
  intro z hz
  have hz0 : (0 : ℝ) < z := hz
  have hz1 : (-1 : ℝ) < z := by linarith
  have hsmj : Work.Spaces.SmoothNbhd (Work.Spaces.DzIter j g) :=
    Work.Elliptic.smoothNbhd_DzIter hsm j
  have hK : ContinuousOn Work.Elliptic.Ktheta (Set.Icc 0 (π / 2)) := by
    unfold Work.Elliptic.Ktheta
    exact ((continuous_const.mul Real.continuous_sin).mul
      (Real.continuous_cos.pow 2)).continuousOn
  have hd := Work.Elliptic.hasDerivAt_integral_Iθ (Work.Spaces.DzIter j g)
    Work.Elliptic.Ktheta hsmj hK hz1
  have hfun : (fun z' => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.DzIter j g z' θ * Work.Elliptic.Ktheta θ)
      = fun z' => Work.Elliptic.Qang g j z' := by
    funext z'
    rw [Work.Elliptic.Qang]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)
  rw [hfun] at hd
  exact hd.continuousAt.continuousWithinAt

/-! ## The assembly -/

/-- The proof of `L12Sin_mem`, given the three analytic inputs
(`L12_moment_eq`, `L12_dzdIter_eq`, `L12_radial_bound`). -/
theorem continuousOn_w' :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := by
  have h2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
  rw [h2]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

/-- The angular factor `angA α i` is continuous on the open quadrant. -/
theorem continuousOn_angA_quad (α : ℝ) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => angA α i p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) :=
  (continuousOn_angA' α i).comp continuousOn_snd (fun p hp => hp.2)

/-- **The `ℋ^k`-integrand of a separated function is continuous on the open quadrant.** -/
theorem continuousOn_HkIntegrand_radialSin (α : ℝ) (k : ℕ) (R : ℝ → ℝ)
    (hcont : ∀ i : ℕ, i ≤ k →
      ContinuousOn (fun z => Work.FTS.EllipticEst.radIter R i z) (Set.Ioi 0)) :
    ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α k (fun z θ => R z * Real.sin (2 * θ)) p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := by
  set Q : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) with hQ
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q := by
    rw [hQ]; exact continuousOn_w'
  have hRad : ∀ i : ℕ, i ≤ k →
      ContinuousOn (fun p : ℝ × ℝ => (Work.FTS.EllipticEst.radIter R i p.1) ^ 2) Q :=
    fun i hi => ((hcont i hi).comp continuousOn_fst (fun p hp => hp.1)).pow 2
  have hZ : ContinuousOn (fun p : ℝ × ℝ => angZ p.2) Q :=
    (continuous_angZ'.comp continuous_snd).continuousOn
  have hAq : ∀ i : ℕ, ContinuousOn (fun p : ℝ × ℝ => angA α i p.2) Q :=
    fun i => (continuousOn_angA' α i).comp continuousOn_snd (fun p hp => hp.2)
  have hsplit : ContinuousOn (fun p : ℝ × ℝ =>
      (∑ i ∈ Finset.range (k + 1), (Work.FTS.EllipticEst.radIter R i p.1) ^ 2
          * (Work.Spaces.w p.1) ^ 2 * angZ p.2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Work.FTS.EllipticEst.radIter R j p.1) ^ 2
              * (Work.Spaces.w p.1) ^ 2 * angA α i p.2 else 0)) Q := by
    refine ContinuousOn.add (continuousOn_finsetSum _ fun i hi => ?_)
      (continuousOn_finsetSum _ fun i hi => continuousOn_finsetSum _ fun j hj => ?_)
    · exact (((hRad i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).mul (hw.pow 2))).mul hZ
    · by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · have hf : (fun p : ℝ × ℝ => if 1 ≤ i ∧ i + j ≤ k then
            (Work.FTS.EllipticEst.radIter R j p.1) ^ 2 * (Work.Spaces.w p.1) ^ 2
              * angA α i p.2 else 0)
            = fun p : ℝ × ℝ => (Work.FTS.EllipticEst.radIter R j p.1) ^ 2
              * (Work.Spaces.w p.1) ^ 2 * angA α i p.2 := by
          funext p; rw [ite_eq_left hc]
        rw [hf]
        exact (((hRad j (by omega)).mul (hw.pow 2))).mul (hAq i)
      · have hf : (fun p : ℝ × ℝ => if 1 ≤ i ∧ i + j ≤ k then
            (Work.FTS.EllipticEst.radIter R j p.1) ^ 2 * (Work.Spaces.w p.1) ^ 2
              * angA α i p.2 else 0) = fun _ : ℝ × ℝ => (0 : ℝ) := by
          funext p; rw [ite_eq_right hc]
        rw [hf]
        exact continuousOn_const
  refine hsplit.congr ?_
  intro p hp
  have hθI : p.2 ∈ Work.Spaces.Iθ := ⟨hp.2.1.le, hp.2.2.le⟩
  have hbeta : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k
      (fun z θ => R z * Real.sin (2 * θ)) p.1 p.2) p
      = Work.Spaces.HkIntegrand α k (fun z θ => R z * Real.sin (2 * θ)) p.1 p.2 := rfl
  rw [hbeta, Work.Spaces.HkIntegrand]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => ?_)
    (Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_)
  · rw [Work.FTS.EllipticEst.DzIter_fstarSin_eq]
    exact Work.FTS.EllipticEst.FstarHkOpen.zTerm_eq_on
      (Work.FTS.EllipticEst.radIter R i p.1) p.1 p.2 hθI
  · by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [ite_eq_left hc, ite_eq_left hc, Work.FTS.EllipticEst.mixed_fstarSin_eq]
      exact Work.FTS.EllipticEst.FstarHkOpen.mixedTerm_eq_on α
        (Work.FTS.EllipticEst.radIter R j p.1) p.1 (Work.FTS.EllipticEst.sinProf i) p.2 hθI
    · rw [ite_eq_right hc, ite_eq_right hc]

/-- **Membership in `ℋ^k` of a separated function `R(z)·sin 2θ`.**  If the radial iterates of
`R` are continuous on `(0,∞)` and `w(z)²·Σ_{i≤k}(radIter R i z)²` is dominated by an integrable
majorant `N`, then `R(z)·sin 2θ ∈ ℋ^k`. -/
theorem HkMem_radialSin_of_bound (α : ℝ) (k : ℕ) (R N : ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hN : MeasureTheory.IntegrableOn N Work.Spaces.Iz)
    (hNnn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ N z)
    (hcont : ∀ i : ℕ, i ≤ k →
      ContinuousOn (fun z => Work.FTS.EllipticEst.radIter R i z) (Set.Ioi 0))
    (hbound : ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2 *
        (∑ i ∈ Finset.range (k + 1), (Work.FTS.EllipticEst.radIter R i z) ^ 2) ≤ N z) :
    Work.Spaces.HkMem α k (fun z θ => R z * Real.sin (2 * θ)) := by
  set A : ℝ → ℝ := fun θ => angZ θ + ∑ i ∈ Finset.range (k + 1), angA α i θ with hA
  set M : ℝ → ℝ → ℝ := fun z θ => N z * A θ with hM
  have hAI : MeasureTheory.IntegrableOn A Work.Spaces.Iθ :=
    integrableOn_angZ'.add (MeasureTheory.integrable_finsetSum (Finset.range (k + 1))
      (fun i _ => integrableOn_angA' α hα hα1 i))
  refine Work.FTS.LocData.HkMem_of_majorant (α := α) (k := k)
    (f := fun z θ => R z * Real.sin (2 * θ)) (M := M)
    (continuousOn_HkIntegrand_radialSin α k R hcont) ?_ ?_ ?_
  · -- the `θ`-slices of the majorant are integrable
    intro z hz
    rw [hM]
    exact hAI.const_mul (N z)
  · -- the slice integral of the majorant is integrable
    have hfun : (fun z => ∫ θ in Work.Spaces.Iθ, M z θ)
        = fun z => N z * (∫ θ in Work.Spaces.Iθ, A θ) := by
      funext z
      rw [hM]
      exact MeasureTheory.integral_const_mul (N z) A
    rw [hfun]
    exact hN.mul_const _
  · -- the pointwise domination
    intro z hz θ hθ
    set P : ℝ := ∑ i ∈ Finset.range (k + 1), (Work.FTS.EllipticEst.radIter R i z) ^ 2 with hP
    set S : ℝ := ∑ i ∈ Finset.range (k + 1), angA α i θ with hS
    set w2 : ℝ := (Work.Spaces.w z) ^ 2 with hw2
    have hPnn : 0 ≤ P := by
      rw [hP]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hSnn : 0 ≤ S := by
      rw [hS]; exact Finset.sum_nonneg fun i _ => angA_nonneg' α i hθ
    have hw2nn : 0 ≤ w2 := by rw [hw2]; exact sq_nonneg _
    have hAnn : 0 ≤ A θ := by
      rw [hA]; exact add_nonneg (angZ_nonneg' hθ) hSnn
    have hkey : P * w2 ≤ N z := by
      have h := hbound z hz
      rw [← hP, ← hw2, mul_comm] at h
      exact h
    have hZle : angZ θ ≤ A θ := by
      rw [hA]; exact le_add_of_nonneg_right hSnn
    have hSle : S ≤ A θ := by
      rw [hA, hS]; exact le_add_of_nonneg_left (angZ_nonneg' hθ)
    rw [Work.FTS.EllipticEst.Cert.HkIntegrand_radial_sin α k R z θ hθ]
    rw [Work.FTS.EllipticEst.Cert.HkExp, hM]
    change (∑ i ∈ Finset.range (k + 1), (Work.FTS.EllipticEst.radIter R i z) ^ 2
          * (Work.Spaces.w z) ^ 2 * angZ θ)
        + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 * angA α i θ
            else 0)) ≤ N z * A θ
    have hsum1 : (∑ i ∈ Finset.range (k + 1),
        (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 * angZ θ)
        = P * (w2 * angZ θ) := by
      have e1 : (∑ i ∈ Finset.range (k + 1),
            (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 * angZ θ)
          = (∑ i ∈ Finset.range (k + 1),
              (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2) * angZ θ :=
        (Finset.sum_mul _ _ _).symm
      have e2 : (∑ i ∈ Finset.range (k + 1),
              (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2)
          = (∑ i ∈ Finset.range (k + 1),
              (Work.FTS.EllipticEst.radIter R i z) ^ 2) * (Work.Spaces.w z) ^ 2 :=
        (Finset.sum_mul _ _ _).symm
      rw [e1, e2, ← hP, ← hw2]
      ring
    have hsum2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 * angA α i θ
        else 0)) ≤ P * (w2 * S) := by
      have hle : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2
              * angA α i θ else 0))
          ≤ (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (Work.FTS.EllipticEst.radIter R j z) ^ 2
                * ((Work.Spaces.w z) ^ 2 * angA α i θ)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          split_ifs with hc
          · exact le_of_eq (by ring)
          · exact mul_nonneg (sq_nonneg _) (mul_nonneg hw2nn (angA_nonneg' α i hθ))
      have h2eq : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (Work.FTS.EllipticEst.radIter R j z) ^ 2
              * ((Work.Spaces.w z) ^ 2 * angA α i θ)) = P * (w2 * S) := by
        have e1 : ∀ i : ℕ, (∑ j ∈ Finset.range (k + 1),
              (Work.FTS.EllipticEst.radIter R j z) ^ 2
                * ((Work.Spaces.w z) ^ 2 * angA α i θ))
            = (∑ j ∈ Finset.range (k + 1),
                (Work.FTS.EllipticEst.radIter R j z) ^ 2)
              * ((Work.Spaces.w z) ^ 2 * angA α i θ) :=
          fun i => (Finset.sum_mul _ _ _).symm
        rw [Finset.sum_congr rfl (fun i _ => e1 i)]
        have e2 : (∑ i ∈ Finset.range (k + 1),
              (∑ j ∈ Finset.range (k + 1),
                (Work.FTS.EllipticEst.radIter R j z) ^ 2)
              * ((Work.Spaces.w z) ^ 2 * angA α i θ))
            = (∑ j ∈ Finset.range (k + 1),
                (Work.FTS.EllipticEst.radIter R j z) ^ 2)
              * (∑ i ∈ Finset.range (k + 1), ((Work.Spaces.w z) ^ 2 * angA α i θ)) :=
          (Finset.mul_sum _ _ _).symm
        rw [e2]
        have e3 : (∑ i ∈ Finset.range (k + 1), ((Work.Spaces.w z) ^ 2 * angA α i θ))
            = (Work.Spaces.w z) ^ 2 * S := by
          rw [hS]
          exact (Finset.mul_sum _ _ _).symm
        rw [e3, ← hP, ← hw2]
      exact le_trans hle (le_of_eq h2eq)
    have hgrp : P * (w2 * angZ θ) + P * (w2 * S) = P * w2 * A θ := by
      rw [hA, hS]
      ring
    calc (∑ i ∈ Finset.range (k + 1), (Work.FTS.EllipticEst.radIter R i z) ^ 2
            * (Work.Spaces.w z) ^ 2 * angZ θ)
          + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then
                (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2
                  * angA α i θ
              else 0))
        ≤ P * (w2 * angZ θ) + P * (w2 * S) := by
          rw [hsum1]; exact add_le_add le_rfl hsum2
      _ = P * w2 * A θ := hgrp
      _ ≤ N z * A θ := mul_le_mul_of_nonneg_right hkey hAnn

/-! ## The target theorem -/

theorem L12Sin_mem_of_data (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ)
    (hmom : ∀ z : ℝ, 0 < z → Work.Elliptic.L12 F z
        = 15 * α * Work.Elliptic.Fstar Ψ z
          + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z)
    (hdzd : ∀ i : ℕ, i ≤ k + 1 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.L12 F z) z
        = 5 * α * Work.Elliptic.Qang Ψ i z + α ^ 2 * Work.Elliptic.Qang Ψ (i + 1) z)
    (hK : ∃ K : ℝ, 0 < K ∧ ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2 * (∑ i ∈ Finset.range (k + 1),
          (Work.FTS.EllipticEst.radIter (fun z => Work.Elliptic.L12 F z) i z) ^ 2)
        ≤ K * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ))) :
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.L12 F z * Real.sin (2 * θ)) := by
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨K, hKpos, hKbd⟩ := hK
  set Z2 : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ with hZ2
  set N : ℝ → ℝ := fun z => K * ((∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k Ψ z θ)
      + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Z2 z θ)
      + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)) with hN
  have hNint : MeasureTheory.IntegrableOn N Work.Spaces.Iz := by
    rw [hN]
    have hZ2u : Z2 = fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ := hZ2
    rw [hZ2u]
    exact ((h.memPsi.2.add h.memZ2.2).add h.memF.2).const_mul K
  have hNnn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ N z := by
    intro z hz
    rw [hN]
    refine mul_nonneg hKpos.le ?_
    have h1 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ :=
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k Ψ z θ
    have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Z2 z θ :=
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k Z2 z θ
    have h3 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ :=
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ
    linarith
  have hcontR : ∀ i : ℕ, i ≤ k → ContinuousOn
      (fun z => Work.FTS.EllipticEst.radIter (fun z => Work.Elliptic.L12 F z) i z)
      (Set.Ioi 0) := by
    intro i hi
    have hsum : ContinuousOn (fun z => 5 * α * Work.Elliptic.Qang Ψ i z
        + α ^ 2 * Work.Elliptic.Qang Ψ (i + 1) z) (Set.Ioi 0) :=
      ((continuousOn_Qang Ψ h.smoothNbhd i).const_mul (5 * α)).add
        ((continuousOn_Qang Ψ h.smoothNbhd (i + 1)).const_mul (α ^ 2))
    refine hsum.congr ?_
    intro z hz
    show Work.FTS.EllipticEst.radIter (fun z => Work.Elliptic.L12 F z) i z
      = 5 * α * Work.Elliptic.Qang Ψ i z + α ^ 2 * Work.Elliptic.Qang Ψ (i + 1) z
    rw [radIter_eq_DzdIter]
    exact hdzd i (by omega) z hz
  refine HkMem_radialSin_of_bound α k (fun z => Work.Elliptic.L12 F z) N hα hα1 hNint hNnn
    hcontR ?_
  intro z hz
  have hbd := hKbd z hz
  rw [hN, hZ2]
  exact hbd

theorem L12Sin_mem (k : ℕ) : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 / 4 → Work.FTS.EllipticEst.EllHyp α k F Ψ →
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.L12 F z * Real.sin (2 * θ)) :=
  Work.FTS.EllipticEst.TT.L12Sin_mem k

end Work.FTS.EllipticEst.Cert
