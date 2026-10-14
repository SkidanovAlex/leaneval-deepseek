import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.TransportS.T2Sup.PairBnd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The exceptional term bounded by the radial integration by parts** (open / a.e.-trace
form). -/
theorem flux_bound_open {α Mf q : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ} {k : Fin 5}
    (hMf : 0 ≤ Mf)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f)
    (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hm4 : Work.Spaces.HkMem α 4 g) (hm5 : Work.Spaces.HkMem α 5 g)
    (hk : k.val = a) (hab : a + b = 4) (hq : q ≤ Work.FTS.TransportS.T3SlotAux.qOf α a)
    (hρeq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ = Work.FTS.TransportS.SlotT2.canonW q z θ)
    (hfb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ Mf)
    (hDfb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Dz f z θ| ≤ Mf)
    (htr : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0)) :
    |∫ p, ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
      ≤ 2 * Mf * Work.Spaces.HkSq α 4 g := by
  set r : ℝ := Work.FTS.TransportS.T3SlotAux.qOf α a - q with hr
  set h : ℝ → ℝ → ℝ := fun z θ => (Real.sin (2 * θ)) ^ r * f z θ with hh
  have hrnn : 0 ≤ r := by rw [hr]; linarith
  have hsh : Work.FTS.EllipticEst.SmoothOpen h :=
    Work.FTS.TransportS.T3SlotAux.smoothOpen_sin_rpow_mul hsf r
  -- the coefficient bounds
  have hbnd' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |h z θ| ≤ Mf := by
    intro z hz θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hrp : (Real.sin (2 * θ)) ^ r ≤ 1 := Real.rpow_le_one hs0 hs1 hrnn
    rw [hh]
    calc |(Real.sin (2 * θ)) ^ r * f z θ|
        = (Real.sin (2 * θ)) ^ r * |f z θ| := by
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0 r)]
      _ ≤ 1 * Mf := mul_le_mul hrp (hfb z hz θ hθ) (abs_nonneg _) (by positivity)
      _ = Mf := one_mul Mf
  have hDbnd' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Dz h z θ| ≤ Mf := by
    by_cases hr0 : r = 0
    · have heq : h = f := by
        funext z' θ'
        simp only [hh, hr0, Real.rpow_zero, one_mul]
      intro z hz θ hθ
      rw [heq]
      exact hDfb z hz θ hθ
    · intro z hz θ hθ
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | h0
      · subst h0
        rw [hh, Work.Spaces.Dz]
        simp only [zero_mul, abs_zero]
        exact hMf
      · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
        · subst hθ0
          rw [hh, Work.Spaces.Dz, Work.Spaces.pz]
          have hzero : (fun z' => Real.sin (2 * 0) ^ r * f z' 0) = fun _ => (0 : ℝ) := by
            funext z'
            rw [show Real.sin (2 * 0) = 0 by simp, Real.zero_rpow hr0, zero_mul]
          rw [hzero, deriv_const]
          simp only [mul_zero, abs_zero]
          exact hMf
        · rcases eq_or_lt_of_le hθ.2 with hθ2 | hθ2
          · subst hθ2
            rw [hh, Work.Spaces.Dz, Work.Spaces.pz]
            have hzero : (fun z' => Real.sin (2 * (Real.pi / 2)) ^ r * f z' (Real.pi / 2))
                = fun _ => (0 : ℝ) := by
              funext z'
              rw [show Real.sin (2 * (Real.pi / 2)) = 0 by
                rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi], Real.zero_rpow hr0,
                zero_mul]
            rw [hzero, deriv_const]
            simp only [mul_zero, abs_zero]
            exact hMf
          · have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ
            have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
            have hrp : (Real.sin (2 * θ)) ^ r ≤ 1 := Real.rpow_le_one hs0 hs1 hrnn
            have hdiff : DifferentiableAt ℝ (fun z' => f z' θ) z :=
              ((hsf.curry_z (show θ ∈ Set.Ioo 0 (π / 2) from ⟨hθ0, hθ2⟩)).differentiableOn
                (by simp)).differentiableAt (isOpen_Ioi.mem_nhds h0)
            have hDz : Work.Spaces.Dz h z θ
                = (Real.sin (2 * θ)) ^ r * Work.Spaces.Dz f z θ := by
              rw [hh]
              simp only [Work.Spaces.Dz, Work.Spaces.pz]
              rw [deriv_const_mul ((Real.sin (2 * θ)) ^ r) hdiff]
              ring
            rw [hDz, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0 r)]
            calc (Real.sin (2 * θ)) ^ r * |Work.Spaces.Dz f z θ|
                ≤ 1 * Mf := mul_le_mul hrp (hDfb z hz θ hθ) (abs_nonneg _) (by positivity)
              _ = Mf := one_mul Mf
  -- the a.e. identification with `gK α h g k`
  have hae : (fun p : ℝ × ℝ => ρ p.1 p.2 * f p.1 p.2
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2)
      =ᵐ[(MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)]
        (fun p : ℝ × ℝ => Work.FTS.TransportS.gK α h g k p.1 p.2) :=
    Work.FTS.TransportS.ae_of_forall_Qd fun z θ hz hθ hθ' =>
      Work.FTS.TransportS.T3SlotAux.flux_ident (α := α) (q := q) (r := r) (f := f) (g := g)
        (a := a) (b := b) (ρ := ρ) (k := k) hk hab (by rw [hr]) hρeq hz ⟨hθ, hθ'⟩
  rw [MeasureTheory.integral_congr_ae hae]
  -- the radial integration by parts
  have hprod := slot_prod_le_open (α := α) (Mf := Mf) (f := h) (g := g)
    k hMf hsh hsg hm4 hm5 hbnd' hDbnd' htr
  refine hprod.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by linarith : (0:ℝ) ≤ 2 * Mf)
  calc (∫ p, (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ≤ ∫ p, Work.Spaces.HkIntegrand α 4 g p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
        MeasureTheory.integral_mono_ae
          (integrable_Xz_sq_open hsg hm4 k)
          (integrable_HkIntegrand_prod_open hsg hm4).1
          (Work.FTS.TransportS.ae_of_forall_Qd fun z θ _ _ _ =>
            Work.FTS.TransportS.Xz_sq_le_HkIntegrand4 α g k z θ)
    _ = Work.Spaces.HkSq α 4 g := (integrable_HkIntegrand_prod_open hsg hm4).2

/-- Product-integrability of the exceptional term (open form), from `integrable_gK_open` and
the a.e. identification `flux_ident`. -/
theorem flux_integrable_open {α Mf q r : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    {k : Fin 5}
    (hMf : 0 ≤ Mf)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f)
    (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hm5 : Work.Spaces.HkMem α 5 g)
    (hk : k.val = a) (hab : a + b = 4) (hr : r = Work.FTS.TransportS.T3SlotAux.qOf α a - q)
    (hq : q ≤ Work.FTS.TransportS.T3SlotAux.qOf α a)
    (hρeq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ = Work.FTS.TransportS.SlotT2.canonW q z θ)
    (hfb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |f z θ| ≤ Mf) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  set h : ℝ → ℝ → ℝ := fun z θ => (Real.sin (2 * θ)) ^ r * f z θ with hh
  have hrnn : 0 ≤ r := by rw [hr]; linarith
  have hsh : Work.FTS.EllipticEst.SmoothOpen h :=
    Work.FTS.TransportS.T3SlotAux.smoothOpen_sin_rpow_mul hsf r
  have hbnd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |h z θ| ≤ Mf := by
    intro z θ hz hθ0 hθ1
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hrp : (Real.sin (2 * θ)) ^ r ≤ 1 := Real.rpow_le_one hs0 hs1 hrnn
    rw [hh]
    calc |(Real.sin (2 * θ)) ^ r * f z θ|
        = (Real.sin (2 * θ)) ^ r * |f z θ| := by
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0 r)]
      _ ≤ 1 * Mf := mul_le_mul hrp (hfb z θ hz hθ0 hθ1) (abs_nonneg _) (by positivity)
      _ = Mf := one_mul Mf
  have hae : (fun p : ℝ × ℝ => ρ p.1 p.2 * f p.1 p.2
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2)
      =ᵐ[(MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)]
        (fun p : ℝ × ℝ => Work.FTS.TransportS.gK α h g k p.1 p.2) :=
    Work.FTS.TransportS.ae_of_forall_Qd fun z θ hz hθ hθ' =>
      Work.FTS.TransportS.T3SlotAux.flux_ident (α := α) (q := q) (r := r) (f := f) (g := g)
        (a := a) (b := b) (ρ := ρ) (k := k) hk hab (by rw [hr]) hρeq hz ⟨hθ, hθ'⟩
  exact (integrable_gK_open hsh hsg hm5 hMf hbnd k).congr hae.symm

end Work.FTS.StrongPersist.N6Trans.Hon
