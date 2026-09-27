import Mathlib
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.HeteroGerm
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.germC_facts

/-! ## The heteroclinic data of the real connection

Given a real heteroclinic connection `Γ` of the equichordal relation, this file extracts the
backward branch step `Rpt (Γ (λ⁻¹ t)) = invBranch a true (Rpt (Γ t))` and the injectivity of `Γ`,
which are the two real-dynamics inputs of the complex-chain construction. -/

namespace Work.EQ

open Complex Filter _root_.Topology

noncomputable section

theorem bsq_subO2_Rpt_ne {a : ℝ} {z : ℂ} (hz : 0 < z.im) :
    bsq (subO2 a (Rpt z)) ≠ 0 := by
  rw [subO2_Rpt, bsq_ofReal]
  simp only [Complex.ofReal_eq_zero, ne_eq]
  positivity

/-- **The backward branch step of the connection.** -/
theorem gamma_backward_step {a : ℝ} {h : ℂ → ℂ} {r : ℝ} {Γ : ℝ → ℂ}
    (hlam0 : 0 < eqLam a) (hlamne : eqLam a ≠ 0)
    (hfun : ∀ t : ℝ, 0 < t → eqU a (Γ t) = Γ (eqLam a * t))
    (him : ∀ t : ℝ, 0 < t → 0 < (Γ t).im) (t : ℝ) (ht : 0 < t) :
    Rpt (Γ ((eqLam a)⁻¹ * t)) = invBranch a true (Rpt (Γ t)) := by
  have ht' : 0 < (eqLam a)⁻¹ * t := by positivity
  have heq : eqU a (Γ ((eqLam a)⁻¹ * t)) = Γ t := by
    have h := hfun ((eqLam a)⁻¹ * t) ht'
    rw [← mul_assoc, mul_inv_cancel₀ hlamne, one_mul] at h
    exact h
  have hfwd : Rpt (Γ t) = fwdC a (Rpt (Γ ((eqLam a)⁻¹ * t))) := by
    rw [← heq, Rpt_eqU]
  have hrel : EqRelC a (Rpt (Γ ((eqLam a)⁻¹ * t))) (Rpt (Γ t)) := by
    rw [hfwd]
    exact eqRelC_fwdC (bsq_subO2_Rpt_ne (by simpa using him ((eqLam a)⁻¹ * t) ht'))
  have hP1 : ((Rpt (Γ ((eqLam a)⁻¹ * t))).1).im = 0 := by simp
  have hP2 : ((Rpt (Γ ((eqLam a)⁻¹ * t))).2).im = 0 := by simp
  have hPpos : 0 < ((Rpt (Γ ((eqLam a)⁻¹ * t))).2).re := by
    rw [Rpt, Prod.snd, Complex.ofReal_re]
    exact him ((eqLam a)⁻¹ * t) ht'
  have hQ : 0 < (Γ t).im := him t ht
  exact (eqRelC_preimage_upper (P := Rpt (Γ ((eqLam a)⁻¹ * t))) (z := Γ t) hQ hP1 hP2
    hPpos hrel).1

/-- Near `0`, `h (λ u) ≠ h u` (the denominator of the germ has a simple zero at the origin). -/
theorem h_lam_ne {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → h ((eqLam a : ℂ) * (t : ℂ)) ≠ h (t : ℂ) := by
  obtain ⟨hr, han, h0, hderiv, hreal, hFE⟩ := hh
  have hder : HasDerivAt h (-1) 0 := by
    have h' := (han 0 (by simp [Metric.mem_ball, hr])).differentiableAt.hasDerivAt
    rwa [hderiv] at h'
  have hcomp : HasDerivAt (fun v : ℂ => h ((eqLam a : ℂ) * v)) ((eqLam a : ℂ) * (-1)) 0 := by
    have hc : HasDerivAt (fun v : ℂ => (eqLam a : ℂ) * v) ((eqLam a : ℂ) * 1) 0 :=
      (hasDerivAt_id (0 : ℂ)).const_mul (eqLam a : ℂ)
    have hcc := HasDerivAt.comp (0 : ℂ)
      (show HasDerivAt h (-1) ((eqLam a : ℂ) * 0) by simpa using hder) hc
    convert hcc using 1
    · ext v; rfl
    · ring
  have hsub : HasDerivAt (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v)
      ((eqLam a : ℂ) * (-1) - (-1)) 0 := hcomp.sub hder
  have hD0 : dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 0 = 1 - (eqLam a : ℂ) := by
    rw [dslope_same, hsub.deriv]; ring
  have hDne : dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 0 ≠ 0 := by
    rw [hD0]
    have hlt : eqLam a < 1 := eqLam_lt_one' ha0 ha1
    have : (eqLam a : ℂ) ≠ 1 := by exact_mod_cast (ne_of_lt hlt)
    exact sub_ne_zero.mpr (Ne.symm this)
  have hcont : ContinuousAt (dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0) 0 :=
    continuousAt_dslope_same.mpr hsub.differentiableAt
  obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhds_iff.mp (hcont.eventually_ne hDne)
  refine ⟨δ, hδ, fun t ht htd => ?_⟩
  intro hcon
  have hkey : t * dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 (t : ℂ)
      = h ((eqLam a : ℂ) * (t : ℂ)) - h (t : ℂ) := by
    have h := sub_smul_dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) (0 : ℂ) (t : ℂ)
    simp only [sub_zero, smul_eq_mul] at h
    rw [h]
    simp [h0]
  have : t * dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 (t : ℂ) = 0 := by
    rw [hkey, hcon, sub_self]
  have htz : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  have hx : (t : ℂ) ∈ Metric.ball (0 : ℂ) δ := by
    rw [Metric.mem_ball, Complex.dist_eq, sub_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht]
    exact htd
  exact hδ' hx ((mul_eq_zero.mp this).resolve_left htz)

/-- **Injectivity of the connection.** -/
theorem gamma_injective {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ} {Γ : ℝ → ℂ}
    (hh : IsStableGerm a h r) (hΓ : IsHeteroclinic a h r Γ) :
    Set.InjOn Γ (Set.Ioi 0) := by
  obtain ⟨hr, han, h0, hderiv, hreal, hFE⟩ := hh
  obtain ⟨-, _, him, hfun, ⟨ε, hε, hgerm⟩, -⟩ := hΓ
  obtain ⟨ρ, hρ, hanC, hC0, hreg, hinjC, hderivC⟩ := germC_facts ha0 ha1
    ⟨hr, han, h0, hderiv, hreal, hFE⟩
  obtain ⟨δ, hδ, hδne⟩ := h_lam_ne ha0 ha1 ⟨hr, han, h0, hderiv, hreal, hFE⟩
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hlamne : eqLam a ≠ 0 := ne_of_gt hlam0
  have key : ∀ t₁ t₂ : ℝ, 0 < t₁ → 0 < t₂ → t₁ < t₂ → Γ t₁ = Γ t₂ → False := by
    intro t₁ t₂ ht₁ ht₂ hlt heq
    have hiter : ∀ n : ℕ, Γ (eqLam a ^ n * t₁) = Γ (eqLam a ^ n * t₂) := by
      intro n
      induction n with
      | zero => simpa using heq
      | succ n ih =>
          have hp1 : 0 < eqLam a ^ n * t₁ := by positivity
          have hp2 : 0 < eqLam a ^ n * t₂ := by positivity
          have h1 := hfun (eqLam a ^ n * t₁) hp1
          have h2 := hfun (eqLam a ^ n * t₂) hp2
          have e1 : eqLam a ^ (n + 1) * t₁ = eqLam a * (eqLam a ^ n * t₁) := by ring
          have e2 : eqLam a ^ (n + 1) * t₂ = eqLam a * (eqLam a ^ n * t₂) := by ring
          rw [e1, e2, ← h1, ← h2, ih]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, eqLam a ^ n * t₂ < min ε (min ρ (min r δ)) := by
      have hlim : Tendsto (fun n : ℕ => eqLam a ^ n * t₂) atTop (𝓝 0) := by
        have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1).mul_const t₂
        simpa using h
      exact (hlim.eventually (eventually_lt_nhds (by positivity))).exists
    have hb : eqLam a ^ n * t₂ < min ρ (min r δ) := lt_of_lt_of_le hn (min_le_right _ _)
    have hn2ε : eqLam a ^ n * t₂ < ε := lt_of_lt_of_le hn (le_trans (min_le_left _ _) le_rfl)
    have hn2ρ : eqLam a ^ n * t₂ < ρ := lt_of_lt_of_le hn (le_trans (min_le_right _ _) (min_le_left _ _))
    have hn2r : eqLam a ^ n * t₂ < r := lt_of_lt_of_le hn (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hn2δ : eqLam a ^ n * t₂ < δ := lt_of_lt_of_le hn (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hn1 : eqLam a ^ n * t₁ < min ε (min ρ (min r δ)) :=
      lt_of_lt_of_le (by nlinarith [pow_pos hlam0 n, hlt]) (le_of_lt hn)
    have hn1ε : eqLam a ^ n * t₁ < ε := lt_of_lt_of_le hn1 (le_trans (min_le_left _ _) le_rfl)
    have hn1ρ : eqLam a ^ n * t₁ < ρ := lt_of_lt_of_le hn1 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hn1r : eqLam a ^ n * t₁ < r := lt_of_lt_of_le hn1 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hn1δ : eqLam a ^ n * t₁ < δ := lt_of_lt_of_le hn1 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hp1 : 0 < eqLam a ^ n * t₁ := by positivity
    have hp2 : 0 < eqLam a ^ n * t₂ := by positivity
    have heqn := hiter n
    have e1 : germPt a h (eqLam a ^ n * t₁) = germPt a h (eqLam a ^ n * t₂) := by
      rw [← hgerm _ hp1 hn1ε, heqn, hgerm _ hp2 hn2ε]
    -- reality of `h` at the relevant points
    have hre (s : ℝ) (hs0 : 0 < s) (hsr : s < r) (hsr2 : eqLam a * s < r) :
        (h (s : ℂ)).im = 0 ∧ (h ((eqLam a : ℂ) * (s : ℂ))).im = 0 := by
      refine ⟨?_, ?_⟩
      · exact hreal s (by rw [abs_of_pos hs0]; exact hsr)
      · have h := hreal (eqLam a * s) (by rw [abs_of_pos (by positivity)]; exact hsr2)
        simpa [Complex.ofReal_mul] using h
    have hr1 := hre (eqLam a ^ n * t₁) hp1 hn1r (by
      have h1 := mul_lt_mul_of_pos_left hn1r hlam0
      have h2 : eqLam a * r < r := by nlinarith
      linarith [h1, h2])
    have hr2 := hre (eqLam a ^ n * t₂) hp2 hn2r (by
      have h1 := mul_lt_mul_of_pos_left hn2r hlam0
      have h2 : eqLam a * r < r := by nlinarith
      linarith [h1, h2])
    have hden1 : h ((eqLam a : ℂ) * ((eqLam a ^ n * t₁ : ℝ) : ℂ))
        ≠ h ((eqLam a ^ n * t₁ : ℝ) : ℂ) :=
      hδne _ hp1 hn1δ
    have hden2 : h ((eqLam a : ℂ) * ((eqLam a ^ n * t₂ : ℝ) : ℂ))
        ≠ h ((eqLam a ^ n * t₂ : ℝ) : ℂ) :=
      hδne _ hp2 hn2δ
    have hy : (germC a h ((eqLam a ^ n * t₁ : ℝ) : ℂ)).2
        = (germC a h ((eqLam a ^ n * t₂ : ℝ) : ℂ)).2 := by
      rw [germC_real (a := a) (h := h) h0 (by positivity) hr1.1 hr1.2 hden1,
        germC_real (a := a) (h := h) h0 (by positivity) hr2.1 hr2.2 hden2]
      simpa [Rpt] using congrArg (fun z : ℂ => z.im) e1
    have hmem1 : ((eqLam a ^ n * t₁ : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hp1]
      exact hn1ρ
    have hmem2 : ((eqLam a ^ n * t₂ : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hp2]
      exact hn2ρ
    have hEq : ((eqLam a ^ n * t₁ : ℝ) : ℂ) = ((eqLam a ^ n * t₂ : ℝ) : ℂ) := hinjC hmem1 hmem2 hy
    have : eqLam a ^ n * t₁ = eqLam a ^ n * t₂ := by exact_mod_cast hEq
    exact absurd this (by
      have hpos : 0 < eqLam a ^ n := pow_pos hlam0 n
      nlinarith)
  intro t₁ ht₁ t₂ ht₂ heq
  rcases lt_trichotomy t₁ t₂ with hlt | heq' | hgt
  · exact absurd (key t₁ t₂ ht₁ ht₂ hlt heq) (fun h => h)
  · exact heq'
  · exact absurd (key t₂ t₁ ht₂ ht₁ hgt heq.symm) (fun h => h)

theorem Rpt_inj {z w : ℂ} (h : Rpt z = Rpt w) : z = w := by
  have h1 : (Rpt z).1 + (Rpt z).2 * Complex.I = (Rpt w).1 + (Rpt w).2 * Complex.I := by rw [h]
  rwa [Rpt_toCplx, Rpt_toCplx] at h1

/-- **The unstable-germ tail of the connection.** -/
theorem gamma_tail {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ} {Γ : ℝ → ℂ}
    (hh : IsStableGerm a h r) (hΓ : IsHeteroclinic a h r Γ) :
    ∃ (ε : ℝ) (s : ℝ → ℝ), 0 < ε ∧ (∀ t, 0 < t → 0 < s t) ∧
      (∀ t, 0 < t → Γ (s t) = -(starRingEnd ℂ (Γ t))) ∧
      (∀ t, 0 < t → s ((eqLam a)⁻¹ * t) = eqLam a * s t) ∧
      (∀ t, 0 < t → ∀ n : ℕ, (eqLam a) ^ n * s t < ε →
        Rpt (Γ ((eqLam a)⁻¹ ^ n * t)) = ugermC a h ((eqLam a : ℂ) ^ n * (s t : ℂ))) := by
  have hinj : Set.InjOn Γ (Set.Ioi 0) := gamma_injective ha0 ha1 hh hΓ
  obtain ⟨hr, han, h0, hderiv, hreal, hFE⟩ := hh
  obtain ⟨-, _, him, hfun, ⟨ε₀, hε₀, hgerm⟩, hmir⟩ := hΓ
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hlamne : eqLam a ≠ 0 := ne_of_gt hlam0
  obtain ⟨δ, hδ, hδne⟩ := h_lam_ne ha0 ha1 ⟨hr, han, h0, hderiv, hreal, hFE⟩
  -- the mirror parameter
  have hex : ∀ t : ℝ, ∃ s0 : ℝ, (0 < t → 0 < s0 ∧ Γ s0 = -(starRingEnd ℂ (Γ t))) := by
    intro t
    by_cases ht : 0 < t
    · obtain ⟨s0, hs0⟩ := hmir t ht
      exact ⟨s0, fun _ => hs0⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose s hs using hex
  have hs_pos : ∀ t, 0 < t → 0 < s t := fun t ht => (hs t ht).1
  have hs_eq : ∀ t, 0 < t → Γ (s t) = -(starRingEnd ℂ (Γ t)) := fun t ht => (hs t ht).2
  -- the mirrored point is the backward-step orbit
  have hY : ∀ u : ℝ, 0 < u →
      Rpt (-(starRingEnd ℂ (Γ ((eqLam a)⁻¹ * u))))
        = fwdC a (Rpt (-(starRingEnd ℂ (Γ u)))) := by
    intro u hu
    have hstep := gamma_backward_step (a := a) (h := h) (r := r) (Γ := Γ) hlam0 hlamne hfun him u hu
    have e1 : Rpt (-(starRingEnd ℂ (Γ ((eqLam a)⁻¹ * u))))
        = eqMirror (Rpt (Γ ((eqLam a)⁻¹ * u))) := Rpt_neg_conj _
    have e2 : eqMirror (Rpt (Γ ((eqLam a)⁻¹ * u))) = eqMirror (invBranch a true (Rpt (Γ u))) := by
      rw [hstep]
    have e3 : eqMirror (invBranch a true (Rpt (Γ u))) = fwdC a (eqMirror (Rpt (Γ u))) :=
      (fwdC_mirror a (Rpt (Γ u))).symm
    have e4 : eqMirror (Rpt (Γ u)) = Rpt (-(starRingEnd ℂ (Γ u))) := (Rpt_neg_conj _).symm
    rw [e1, e2, e3, e4]
  -- iteration of the backward step
  have hiter : ∀ (n : ℕ) (u : ℝ), 0 < u →
      Rpt (-(starRingEnd ℂ (Γ ((eqLam a)⁻¹ ^ n * u))))
        = (fwdC a)^[n] (Rpt (-(starRingEnd ℂ (Γ u)))) := by
    intro n
    induction n with
    | zero => intro u hu; simp
    | succ n ih =>
        intro u hu
        have hupos : 0 < (eqLam a)⁻¹ * u := by positivity
        rw [show (eqLam a)⁻¹ ^ (n + 1) * u = (eqLam a)⁻¹ ^ n * ((eqLam a)⁻¹ * u) by ring]
        rw [ih ((eqLam a)⁻¹ * u) hupos]
        rw [hY u hu]
        exact (Function.iterate_succ_apply (fwdC a) n (Rpt (-(starRingEnd ℂ (Γ u))))).symm
  -- the forward orbit of any point
  have hfwd : ∀ (n : ℕ) (u : ℝ), 0 < u →
      Rpt (Γ (eqLam a ^ n * u)) = (fwdC a)^[n] (Rpt (Γ u)) := by
    intro n
    induction n with
    | zero => intro u hu; simp
    | succ n ih =>
        intro u hu
        have hpos : 0 < eqLam a ^ n * u := by positivity
        rw [show eqLam a ^ (n + 1) * u = eqLam a * (eqLam a ^ n * u) by ring]
        rw [← hfun _ hpos]
        rw [Rpt_eqU]
        rw [ih u hu]
        exact (Function.iterate_succ_apply' (fwdC a) n (Rpt (Γ u))).symm
  -- the recursion for `s`
  have hrec : ∀ t, 0 < t → s ((eqLam a)⁻¹ * t) = eqLam a * s t := by
    intro t ht
    have ht' : 0 < (eqLam a)⁻¹ * t := by positivity
    have e1 : Rpt (Γ (s ((eqLam a)⁻¹ * t))) = Rpt (Γ (eqLam a * s t)) := by
      calc Rpt (Γ (s ((eqLam a)⁻¹ * t)))
          = Rpt (-(starRingEnd ℂ (Γ ((eqLam a)⁻¹ * t)))) := by rw [hs_eq _ ht']
        _ = fwdC a (Rpt (-(starRingEnd ℂ (Γ t)))) := hY t ht
        _ = fwdC a (Rpt (Γ (s t))) := by rw [hs_eq t ht]
        _ = Rpt (Γ (eqLam a * s t)) := by
              rw [← Rpt_eqU, hfun _ (hs_pos t ht)]
    have h2 := Rpt_inj e1
    exact hinj (hs_pos _ ht') (mul_pos hlam0 (hs_pos t ht)) h2
  -- `s (λ⁻ⁿ t) = λⁿ s t`
  have hsn_all : ∀ (n : ℕ) (t : ℝ), 0 < t → s ((eqLam a)⁻¹ ^ n * t) = eqLam a ^ n * s t := by
    intro n
    induction n with
    | zero => intro t ht; simp
    | succ n ih =>
        intro t ht
        have hk : 0 < (eqLam a)⁻¹ ^ n * t := by positivity
        have hstep : s ((eqLam a)⁻¹ * ((eqLam a)⁻¹ ^ n * t))
            = eqLam a * s ((eqLam a)⁻¹ ^ n * t) := hrec _ hk
        have hih := ih t ht
        rw [show (eqLam a)⁻¹ ^ (n + 1) * t = (eqLam a)⁻¹ * ((eqLam a)⁻¹ ^ n * t) by ring]
        rw [hstep, hih]
        ring
  -- the tail
  refine ⟨min δ (min ε₀ r), s, lt_min hδ (lt_min hε₀ hr), hs_pos, hs_eq, hrec, ?_⟩
  intro t ht n hn
  have hsn := hsn_all n t ht
  have hδ'' : (eqLam a) ^ n * s t < δ := lt_of_lt_of_le hn (min_le_left _ _)
  have hε₀' : (eqLam a) ^ n * s t < ε₀ :=
    lt_of_lt_of_le hn (le_trans (min_le_right _ _) (min_le_left _ _))
  have hr' : (eqLam a) ^ n * s t < r :=
    lt_of_lt_of_le hn (le_trans (min_le_right _ _) (min_le_right _ _))
  have hspos : 0 < (eqLam a) ^ n * s t := mul_pos (pow_pos hlam0 n) (hs_pos t ht)
  have habsr : |(eqLam a ^ n * s t : ℝ)| < r := by rw [abs_of_pos hspos]; exact hr'
  have habsr2 : |(eqLam a * (eqLam a ^ n * s t) : ℝ)| < r := by
    rw [abs_of_pos (mul_pos hlam0 (mul_pos (pow_pos hlam0 n) (hs_pos t ht)))]
    have h1 : eqLam a * (eqLam a ^ n * s t) < eqLam a * r := mul_lt_mul_of_pos_left hr' hlam0
    have h2 : eqLam a * r < r := by nlinarith
    linarith
  have hre1 : (h ((eqLam a ^ n * s t : ℝ) : ℂ)).im = 0 := hreal _ habsr
  have hre2 : (h ((eqLam a : ℂ) * ((eqLam a ^ n * s t : ℝ) : ℂ))).im = 0 := by
    have h := hreal (eqLam a * (eqLam a ^ n * s t)) habsr2
    simpa [Complex.ofReal_mul] using h
  have hden : h ((eqLam a : ℂ) * ((eqLam a ^ n * s t : ℝ) : ℂ))
      ≠ h ((eqLam a ^ n * s t : ℝ) : ℂ) := by
    simpa [Complex.ofReal_mul] using hδne _ hspos hδ''
  -- the two iterated identities
  have h1 : Rpt (-(starRingEnd ℂ (Γ ((eqLam a)⁻¹ ^ n * t))))
      = (fwdC a)^[n] (Rpt (-(starRingEnd ℂ (Γ t)))) := hiter n t ht
  have h3 : Rpt (-(starRingEnd ℂ (Γ ((eqLam a)⁻¹ ^ n * t)))) = Rpt (Γ (eqLam a ^ n * s t)) := by
    rw [h1, ← hs_eq t ht, hfwd n (s t) (hs_pos t ht)]
  have hy : -(starRingEnd ℂ (Γ ((eqLam a)⁻¹ ^ n * t))) = Γ (eqLam a ^ n * s t) := Rpt_inj h3
  have step1 : Rpt (Γ ((eqLam a)⁻¹ ^ n * t))
      = eqMirror (Rpt (-(starRingEnd ℂ (Γ ((eqLam a)⁻¹ ^ n * t))))) := by
    rw [← Rpt_neg_conj (z := -(starRingEnd ℂ (Γ ((eqLam a)⁻¹ ^ n * t))))]
    congr 1
    simp
  rw [step1, hy, hgerm _ hspos hε₀']
  show eqMirror (Rpt (germPt a h (eqLam a ^ n * s t)))
      = eqMirror (germC a h (((eqLam a : ℂ) ^ n) * ((s t : ℝ) : ℂ)))
  rw [← germC_real (a := a) (h := h) h0 (ne_of_gt hspos) hre1 hre2 hden]
  rw [show ((eqLam a ^ n * s t : ℝ) : ℂ) = ((eqLam a : ℂ) ^ n) * ((s t : ℝ) : ℂ) by push_cast; ring]

end

end Work.EQ
