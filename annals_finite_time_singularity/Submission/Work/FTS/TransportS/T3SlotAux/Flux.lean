/-
Copyright: work module for the Elgindi finite-time singularity project.

# `T3SlotAux/Flux`: the exceptional (all-derivatives-on-`g`) term of the slot pairing

For the slot `(a,b)` with `a + b = 4` and the leaf weight `ρ = canonW q` (`q ≤ qOf α a`), the
exceptional Leibniz term of the pairing is

`∫∫ ρ · f · D_z(D_z^bD_θ^a g) · (D_z^bD_θ^a g)`,

i.e. the top (order-five) term of the slot, which cannot be bounded pointwise.  Writing
`ρ = w² sin(2θ)^{-q}` and `sin(2θ)^r · w² sin(2θ)^{-qOf α a} = ρ` with `r := qOf α a - q ≥ 0`,
the integrand *is* the `k`-th summand `gK α h g k` of `Hhard`, with the coefficient
`h = sin(2θ)^r · f`, so `Work.FTS.TransportS.T3BadAux.slot_prod_le` (the radial integration by
parts, with the boundary terms killed by the `BdryTraces` of `g`) applies verbatim.

All declarations are `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.T3SlotAux.Pointwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T3SlotAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Smoothness of the `sin(2θ)^r` factor -/

theorem contDiffOn_sin_rpow_Q0 (r : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ r) Work.FTS.EllipticEst.Q0 := by
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
    ((Real.contDiff_sin.contDiffOn).comp (contDiffOn_const.mul contDiffOn_snd)
      (fun p _ => Set.mem_univ _)).of_le le_top
  refine hsmooth.rpow contDiffOn_const fun p hp => ?_
  have hp' : 0 < p.2 ∧ p.2 < Real.pi / 2 := by
    have h := hp
    simp only [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at h
    exact h.2
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp'.1])
    (by linarith [hp'.2, Real.pi_pos]))

/-- The product of a `SmoothOpen` function with the smooth factor `sin(2θ)^r` is `SmoothOpen`
on the open quadrant. -/
theorem smoothOpen_sin_rpow_mul {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (r : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => (Real.sin (2 * θ)) ^ r * f z θ) := by
  have h1 := contDiffOn_sin_rpow_Q0 r
  have h2 : Function.uncurry (fun z θ => (Real.sin (2 * θ)) ^ r * f z θ)
      = fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ r * Function.uncurry f p := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h2]
  exact h1.mul hf

/-- `sghard α k θ = sin(2θ)^{-qOf α a}` for `k.val = a`. -/
theorem sghard_eq_rpow {α : ℝ} {k : Fin 5} {a : ℕ} (hk : k.val = a) (θ : ℝ) :
    Work.FTS.H2.sghard α k θ = (Real.sin (2 * θ)) ^ (-(qOf α a)) := by
  rcases eq_or_ne a 0 with ha0 | ha
  · subst ha0
    have hk' : k = 0 := Fin.ext hk
    subst hk'
    rw [Work.FTS.H2.sghard_apply_zero, qOf_zero]
  · have hkv : k.val ≠ 0 := by rw [hk]; exact ha
    rw [Work.FTS.H2.sghard_apply_ne α k hkv θ, qOf_of_ne ha]

/-! ## The identification of the exceptional term with `gK` -/

/-- The exceptional term of the slot `(a,b) = (a, 4-a)` with the leaf weight `ρ = canonW q`
is the `k`-th summand `gK α h g k` of `Hhard`, with `h = sin(2θ)^{qOf α a - q} · f`. -/
theorem flux_ident {α q r : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ} {k : Fin 5}
    (hk : k.val = a) (hab : a + b = 4) (hr : r = qOf α a - q)
    (hρeq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ = Work.FTS.TransportS.SlotT2.canonW q z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ρ z θ * f z θ * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
        * Work.Spaces.mixed b a g z θ
      = Work.FTS.TransportS.gK α (fun z θ => (Real.sin (2 * θ)) ^ r * f z θ) g k z θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsub : 4 - k.val = b := by rw [hk]; omega
  have hThard : Work.FTS.H2.Thard g k = Work.Spaces.mixed b a g := by
    rw [Work.FTS.H2.Thard_eq_mixed]
    funext z' θ'
    rw [hsub, hk]
  have hcomb : (Real.sin (2 * θ)) ^ r * (Real.sin (2 * θ)) ^ (-(qOf α a))
      = (Real.sin (2 * θ)) ^ (-q) := by
    rw [hr, ← Real.rpow_add hs]
    congr 1
    ring
  have hw : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
      = ((Real.sin (2 * θ)) ^ r * (Real.sin (2 * θ)) ^ (-(qOf α a)))
        * (Work.Spaces.w z) ^ 2 := by
    rw [hcomb]
    ring
  rw [hρeq z θ hz hθ.1 hθ.2, Work.FTS.TransportS.SlotT2.canonW,
    Work.FTS.TransportS.gK, hThard, sghard_eq_rpow hk θ]
  simp only [Work.Spaces.Dz]
  rw [hw]
  ring

/-! ## The bound on the exceptional term -/

/-- **The exceptional term bounded by the radial integration by parts.** -/
theorem flux_bound {α Mf q : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ} {k : Fin 5}
    (hMf : 0 ≤ Mf)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f)
    (hsg : Work.FTS.LocData.SmoothQuad g)
    (hm4 : Work.Spaces.HkMem α 4 g) (hm5 : Work.Spaces.HkMem α 5 g)
    (hk : k.val = a) (hab : a + b = 4) (hq : q ≤ qOf α a)
    (hρeq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ = Work.FTS.TransportS.SlotT2.canonW q z θ)
    (hfb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ Mf)
    (hDfb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Dz f z θ| ≤ Mf)
    (htr : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0)) :
    |∫ p, ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
      ≤ 2 * Mf * Work.Spaces.HkSq α 4 g := by
  set r : ℝ := qOf α a - q with hr
  set h : ℝ → ℝ → ℝ := fun z θ => (Real.sin (2 * θ)) ^ r * f z θ with hh
  have hrnn : 0 ≤ r := by rw [hr]; linarith
  have hsh : Work.FTS.EllipticEst.SmoothOpen h := smoothOpen_sin_rpow_mul hsf r
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
      flux_ident (α := α) (q := q) (r := r) (f := f) (g := g) (a := a) (b := b) (ρ := ρ)
        (k := k) hk hab (by rw [hr]) hρeq hz ⟨hθ, hθ'⟩
  rw [MeasureTheory.integral_congr_ae hae]
  -- the radial integration by parts
  have hprod := Work.FTS.TransportS.T3BadAux.slot_prod_le (α := α) (Mf := Mf) (f := h) (g := g)
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
          (Work.FTS.TransportS.integrable_Xz_sq hsg hm4 k)
          (Work.FTS.TransportS.integrable_HkIntegrand_prod hsg hm4).1
          (Work.FTS.TransportS.ae_of_forall_Qd fun z θ _ _ _ =>
            Work.FTS.TransportS.Xz_sq_le_HkIntegrand4 α g k z θ)
    _ = Work.Spaces.HkSq α 4 g := (Work.FTS.TransportS.integrable_HkIntegrand_prod hsg hm4).2

/-- Product-integrability of the exceptional term, from `integrable_gK` and the a.e.
identification `flux_ident`. -/
theorem flux_integrable {α Mf q r : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ} {k : Fin 5}
    (hMf : 0 ≤ Mf)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f)
    (hsg : Work.FTS.LocData.SmoothQuad g)
    (hm5 : Work.Spaces.HkMem α 5 g)
    (hk : k.val = a) (hab : a + b = 4) (hr : r = qOf α a - q) (hq : q ≤ qOf α a)
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
  have hsh : Work.FTS.EllipticEst.SmoothOpen h := smoothOpen_sin_rpow_mul hsf r
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
      flux_ident (α := α) (q := q) (r := r) (f := f) (g := g) (a := a) (b := b) (ρ := ρ)
        (k := k) hk hab (by rw [hr]) hρeq hz ⟨hθ, hθ'⟩
  exact (Work.FTS.TransportS.integrable_gK hsh hsg hm5 hMf hbnd k).congr hae.symm

end Work.FTS.TransportS.T3SlotAux
