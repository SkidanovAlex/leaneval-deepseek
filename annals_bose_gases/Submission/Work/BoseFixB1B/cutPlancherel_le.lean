import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseFixB1B.CutFibreForms
import Submission.Work.BoseFixB1B.integral_prod_eq_iterated_of_ae_fibre_integrable
import Submission.Work.BoseFixB1B.peel_slot_abox_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal ContDiff FourierTransform

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## Elementary support facts for the window `χ` -/

private lemma cutPlancherel_chi_vanish {L : ℝ} {χ : E3 → ℝ}
    (htsupp : tsupport χ ⊆ Submission.BoseGases.acube L) :
    ∀ z : E3, z ∉ Submission.BoseGases.acube L → χ z = 0 := by
  intro z hz
  by_contra h
  exact hz (htsupp (subset_tsupport χ (Function.mem_support.mpr h)))

private lemma cutPlancherel_fibre_tsupport {n : ℕ} {χ : E3 → ℝ}
    {Φ : Submission.BoseGases.X (n+1) → ℝ} (i : Fin (n+1)) (r : Submission.BoseGases.X n) :
    tsupport (fun z : E3 => χ z * Φ (Submission.BoseGases.kcInsN n i (z, r))) ⊆ tsupport χ := by
  refine closure_mono ?_
  intro z hz
  simp only [Function.mem_support, ne_eq] at hz ⊢
  exact fun h => hz (by simp [h])

private lemma cutPlancherel_fibre_hcs {n : ℕ} {L : ℝ} (hL : 0 < L) {χ : E3 → ℝ}
    (htsupp : tsupport χ ⊆ Submission.BoseGases.acube L)
    {Φ : Submission.BoseGases.X (n+1) → ℝ} (i : Fin (n+1)) (r : Submission.BoseGases.X n) :
    HasCompactSupport (fun z : E3 => χ z * Φ (Submission.BoseGases.kcInsN n i (z, r))) :=
  IsCompact.of_isClosed_subset (Submission.BoseGases.acube_compact hL) (isClosed_tsupport _)
    (fun z hz => htsupp (cutPlancherel_fibre_tsupport i r hz))

/-! ## The slot peel

`(L³)⁻¹ ∫_{abox (n+1) L} ‖tBamp χ p Φ i x‖² = ∫_{abox n L} ‖kinFT (χ·Φ(·ᵢ←·)) p‖²`.
No continuity of `Φ` is needed: the amplitude is constant along the peeled slot. -/

private lemma cutPlancherel_peel {n : ℕ} {L : ℝ} (hL : 0 < L) {χ : E3 → ℝ}
    {Φ : Submission.BoseGases.X (n+1) → ℝ} (i : Fin (n+1)) (p : E3) :
    (L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) L,
        ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2
      = ∫ r in Submission.BoseGases.abox n L,
          ‖Submission.BoseGases.kinFT (fun z : E3 =>
            (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 := by
  have hind : ∀ (r : Submission.BoseGases.X n) (y y' : E3),
      (fun x : Submission.BoseGases.X (n+1) => ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)
          (Submission.BoseGases.kcInsN n i (y, r))
        = (fun x : Submission.BoseGases.X (n+1) => ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)
          (Submission.BoseGases.kcInsN n i (y', r)) := by
    intro r y y'
    show ‖Work.SmallBoxTBWord.tBamp χ p Φ i (Submission.BoseGases.kcInsN n i (y, r))‖ ^ 2
        = ‖Work.SmallBoxTBWord.tBamp χ p Φ i (Submission.BoseGases.kcInsN n i (y', r))‖ ^ 2
    rw [Work.SmallBoxTBWord.tBamp_kcInsN_indep i p r y y']
  rw [peel_slot_abox_ae hL i hind]
  refine integral_congr_ae (Eventually.of_forall (fun r => ?_))
  simp only [Work.SmallBoxTBWord.tBamp_kcInsN_eq_kinFT i p r 0]

/-! ## A uniform bound on the fibre Fourier transform

On the box, `‖kinFT (χ·Φ(·ᵢ←·)) p‖` is bounded independently of `r` and `p`. -/

private lemma cutPlancherel_KinFTBound {n : ℕ} {L : ℝ} (hL : 0 < L) {χ : E3 → ℝ}
    (hχ : Continuous χ) (htsupp : tsupport χ ⊆ Submission.BoseGases.acube L)
    {Φ : Submission.BoseGases.X (n+1) → ℝ} {B : ℝ}
    (hB : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |Φ x| ≤ B) (i : Fin (n+1)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ r ∈ Submission.BoseGases.abox n L, ∀ p : E3,
      ‖Submission.BoseGases.kinFT (fun z : E3 => (χ z : ℂ) *
        (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ≤ c := by
  obtain ⟨Cχ, hCχ⟩ := (Submission.BoseGases.acube_compact hL).exists_bound_of_continuousOn
    hχ.continuousOn
  have hχ0 : ∀ z : E3, z ∉ Submission.BoseGases.acube L → χ z = 0 :=
    cutPlancherel_chi_vanish htsupp
  have hCχ0 : 0 ≤ Cχ := by
    have h0 : (0 : E3) ∈ Submission.BoseGases.acube L :=
      Submission.BoseGases.mem_acube_of_norm_le hL.le (by simp; positivity)
    exact le_trans (norm_nonneg _) (hCχ 0 h0)
  refine ⟨Cχ * max B 0 * L ^ 3,
    mul_nonneg (mul_nonneg hCχ0 (le_max_right B 0)) (by positivity), fun r hr p => ?_⟩
  have hvol : (volume : Measure E3) (Submission.BoseGases.acube L) < ⊤ := by
    rw [Submission.BoseGases.acube_volume L hL.le]
    exact ENNReal.ofReal_lt_top
  have hreal : (volume : Measure E3).real (Submission.BoseGases.acube L) = L ^ 3 := by
    rw [Measure.real, Submission.BoseGases.acube_volume L hL.le,
      ENNReal.toReal_ofReal (by positivity)]
  have hmem : ∀ z ∈ Submission.BoseGases.acube L,
      Submission.BoseGases.kcInsN n i (z, r) ∈ Submission.BoseGases.abox (n + 1) L := by
    intro z hz j
    by_cases hj : j = i
    · subst hj
      rwa [Submission.BoseGases.kc_insN_apply_same]
    · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
      rw [Submission.BoseGases.kc_insN_apply_succ]
      exact hr j'
  have hbound : ∀ z ∈ Submission.BoseGases.acube L,
      ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        ((χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ))‖ ≤ Cχ * max B 0 := by
    intro z hz
    have h1 : ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have h2 : ‖(χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)‖
        = ‖χ z‖ * ‖Φ (Submission.BoseGases.kcInsN n i (z, r))‖ := by
      rw [norm_mul]
      simp
    have h3 : ‖Φ (Submission.BoseGases.kcInsN n i (z, r))‖ ≤ max B 0 := by
      rw [Real.norm_eq_abs]
      exact le_trans (hB _ (hmem z hz)) (le_max_left _ _)
    rw [norm_mul, h1, one_mul, h2]
    exact mul_le_mul (hCχ z hz) h3 (norm_nonneg _) hCχ0
  rw [Submission.BoseGases.kinFT]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Submission.BoseGases.acube L)
    (f := fun z : E3 => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
      ((χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)))
    (fun z hz => by rw [hχ0 z hz, Complex.ofReal_zero, zero_mul, mul_zero])]
  refine le_trans (norm_setIntegral_le_of_norm_le_const hvol hbound) ?_
  rw [hreal]

/-! ## Integrability of the (unweighted) fibre `p`-energy -/

private lemma cutPlancherel_massIntegrable {n : ℕ} {L : ℝ} (hL : 0 < L) {χ : E3 → ℝ}
    (htsupp : tsupport χ ⊆ Submission.BoseGases.acube L)
    {Φ : Submission.BoseGases.X (n+1) → ℝ} (i : Fin (n+1)) (r : Submission.BoseGases.X n)
    (hfib : ContDiff ℝ (⊤ : ENat) (fun z : E3 =>
      χ z * Φ (Submission.BoseGases.kcInsN n i (z, r)))) :
    Integrable (fun p : E3 => ‖Submission.BoseGases.kinFT (fun z : E3 => (χ z : ℂ) *
          (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2) volume := by
  have hcs : HasCompactSupport (fun z : E3 => χ z * Φ (Submission.BoseGases.kcInsN n i (z, r))) :=
    cutPlancherel_fibre_hcs hL htsupp i r
  let F : SchwartzMap E3 ℂ := (hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hfib)
  have hF_coe : (F : E3 → ℂ) = fun z : E3 =>
      ((χ z * Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℝ) : ℂ) := rfl
  have hIntξ : Integrable (fun ξ : E3 => ‖(𝓕 F) ξ‖ ^ 2) := by
    have hm : MemLp ((𝓕 F : SchwartzMap E3 ℂ) : E3 → ℂ) 2 (volume : Measure E3) :=
      SchwartzMap.memLp _ 2 (volume : Measure E3)
    rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable] at hm
    exact hm
  have hInt2 : Integrable (fun p : E3 => ‖(𝓕 F) (((2 * Real.pi)⁻¹ : ℝ) • p)‖ ^ 2) :=
    hIntξ.comp_smul (R := (2 * Real.pi)⁻¹) (by positivity)
  have hkft : ∀ p : E3, Submission.BoseGases.kinFT (fun z : E3 =>
        ((χ z * Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℝ) : ℂ)) p
      = (𝓕 F) ((((2 * Real.pi)⁻¹ : ℝ)) • p) := by
    intro p
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
    have hfun : (fun z : E3 => ((χ z * Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℝ) : ℂ))
        = ⇑F := by
      funext z
      rw [hF_coe]
    rw [hfun, SchwartzMap.fourier_coe]
  have harg : (fun z : E3 => (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ))
      = (fun z : E3 => ((χ z * Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℝ) : ℂ)) := by
    funext z
    rw [Complex.ofReal_mul]
  refine hInt2.congr (Eventually.of_forall (fun p => ?_))
  simp only [harg, hkft]

/-! ## Joint a.e. strong measurability of the fibre kinetic integrand -/

private lemma cutPlancherel_jointAESM {n : ℕ} {L : ℝ} {χ : E3 → ℝ} (hχ : Measurable χ)
    {Φ : Submission.BoseGases.X (n+1) → ℝ}
    (hΦ : AEMeasurable Φ (volume : Measure (Submission.BoseGases.X (n+1)))) (i : Fin (n+1))
    (F : E3 → ℝ) (hF : Continuous F) :
    AEStronglyMeasurable (fun q : E3 × Submission.BoseGases.X n => F q.1 *
        ‖Submission.BoseGases.kinFT (fun z : E3 => (χ z : ℂ) *
          (Φ (Submission.BoseGases.kcInsN n i (z, q.2)) : ℂ)) q.1‖ ^ 2)
      ((volume : Measure E3).prod
        ((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n L))) := by
  classical
  set ν : Measure (Submission.BoseGases.X n) :=
    (volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n L) with hν
  -- The inserted configuration is a.e. measurable, jointly in `(z, r)`.
  have hins : AEMeasurable (fun q : E3 × Submission.BoseGases.X n =>
      Φ (Submission.BoseGases.kcInsN n i (q.1, q.2)))
      ((volume : Measure E3).prod (volume : Measure (Submission.BoseGases.X n))) := by
    have h := hΦ.comp_quasiMeasurePreserving
      (Submission.BoseGases.kc_mp_insN n i).quasiMeasurePreserving
    rwa [MeasureTheory.Measure.volume_eq_prod E3 (Submission.BoseGases.X n)] at h
  have hins' : AEMeasurable (fun q : E3 × Submission.BoseGases.X n =>
      Φ (Submission.BoseGases.kcInsN n i (q.1, q.2))) ((volume : Measure E3).prod ν) :=
    hins.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  -- The reindexing map `(p,r,z) ↦ (z,r)` is quasi-measure-preserving.
  have hT : Measure.QuasiMeasurePreserving
      (fun qz : (E3 × Submission.BoseGases.X n) × E3 => (qz.2, qz.1.2))
      (((volume : Measure E3).prod ν).prod (volume : Measure E3))
      ((volume : Measure E3).prod ν) := by
    have h1 : Measure.QuasiMeasurePreserving
        (Prod.map (Prod.snd : E3 × Submission.BoseGases.X n → Submission.BoseGases.X n)
          (id : E3 → E3))
        (((volume : Measure E3).prod ν).prod (volume : Measure E3))
        (ν.prod (volume : Measure E3)) :=
      MeasureTheory.QuasiMeasurePreserving.prodMap Measure.quasiMeasurePreserving_snd
        (MeasureTheory.Measure.QuasiMeasurePreserving.id (volume : Measure E3))
    have h2 : Measure.QuasiMeasurePreserving
        (Prod.swap : Submission.BoseGases.X n × E3 → E3 × Submission.BoseGases.X n)
        (ν.prod (volume : Measure E3)) ((volume : Measure E3).prod ν) :=
      (Measure.measurePreserving_swap : MeasurePreserving
        (Prod.swap : Submission.BoseGases.X n × E3 → E3 × Submission.BoseGases.X n)
        (ν.prod (volume : Measure E3)) ((volume : Measure E3).prod ν)).quasiMeasurePreserving
    have h3 := h2.comp h1
    have hfun : (fun qz : (E3 × Submission.BoseGases.X n) × E3 => (qz.2, qz.1.2))
        = Prod.swap ∘ Prod.map
            (Prod.snd : E3 × Submission.BoseGases.X n → Submission.BoseGases.X n)
            (id : E3 → E3) := by
      funext qz
      rfl
    rw [hfun]
    exact h3
  have hjoint : AEMeasurable (fun qz : (E3 × Submission.BoseGases.X n) × E3 =>
      Φ (Submission.BoseGases.kcInsN n i (qz.2, qz.1.2)))
      (((volume : Measure E3).prod ν).prod (volume : Measure E3)) :=
    hins'.comp_quasiMeasurePreserving hT
  -- The integrand of the parametric integral is a.e. strongly measurable.
  have hexp : Continuous (fun qz : (E3 × Submission.BoseGases.X n) × E3 =>
      Complex.exp (-(Complex.I * (inner ℝ qz.1.1 qz.2 : ℂ)))) := by fun_prop
  have hchi : AEStronglyMeasurable (fun qz : (E3 × Submission.BoseGases.X n) × E3 =>
      (χ qz.2 : ℂ)) (((volume : Measure E3).prod ν).prod (volume : Measure E3)) :=
    (Complex.measurable_ofReal.comp (hχ.comp measurable_snd)).aestronglyMeasurable
  have hPhi : AEStronglyMeasurable (fun qz : (E3 × Submission.BoseGases.X n) × E3 =>
      (Φ (Submission.BoseGases.kcInsN n i (qz.2, qz.1.2)) : ℂ))
      (((volume : Measure E3).prod ν).prod (volume : Measure E3)) :=
    (Complex.measurable_ofReal.comp_aemeasurable hjoint).aestronglyMeasurable
  have hInt : AEStronglyMeasurable (fun qz : (E3 × Submission.BoseGases.X n) × E3 =>
      Complex.exp (-(Complex.I * (inner ℝ qz.1.1 qz.2 : ℂ))) *
        ((χ qz.2 : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (qz.2, qz.1.2)) : ℂ)))
      (((volume : Measure E3).prod ν).prod (volume : Measure E3)) :=
    hexp.aestronglyMeasurable.mul (hchi.mul hPhi)
  -- Integrate out `z`: the parametrised amplitude is a.e. strongly measurable.
  have hParam : AEStronglyMeasurable (fun q : E3 × Submission.BoseGases.X n =>
      ∫ z : E3, Complex.exp (-(Complex.I * (inner ℝ q.1 z : ℂ))) *
        ((χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, q.2)) : ℂ)))
      ((volume : Measure E3).prod ν) :=
    hInt.integral_prod_right'
  rw [show (fun q : E3 × Submission.BoseGases.X n => F q.1 *
        ‖Submission.BoseGases.kinFT (fun z : E3 => (χ z : ℂ) *
          (Φ (Submission.BoseGases.kcInsN n i (z, q.2)) : ℂ)) q.1‖ ^ 2)
      = (fun q : E3 × Submission.BoseGases.X n => F q.1 *
        ‖∫ z : E3, Complex.exp (-(Complex.I * (inner ℝ q.1 z : ℂ))) *
          ((χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, q.2)) : ℂ))‖ ^ 2) from by
    funext q
    rw [Submission.BoseGases.kinFT]]
  exact (hF.comp continuous_fst).aestronglyMeasurable.mul (hParam.norm.pow 2)

/-! ## The generic assembly -/

private lemma cutPlancherel_assembly {n : ℕ} {L : ℝ} (hL : 0 < L) {χ : E3 → ℝ}
    (hχm : Measurable χ)
    {Φ : Submission.BoseGases.X (n+1) → ℝ}
    (hΦm : AEMeasurable Φ (volume : Measure (Submission.BoseGases.X (n+1)))) (i : Fin (n+1))
    (hpeel : ∀ p : E3, (L ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox (n + 1) L,
        ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)
      = ∫ r in Submission.BoseGases.abox n L,
          ‖Submission.BoseGases.kinFT (fun z : E3 =>
            (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2)
    (Fw : E3 → ℝ) (hFc : Continuous Fw) (hFnn : ∀ p, 0 ≤ Fw p)
    (pos : Submission.BoseGases.X n → ℝ)
    (hpl : ∀ r ∈ Submission.BoseGases.abox n L, ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : E3, Fw p * ‖Submission.BoseGases.kinFT (fun z : E3 =>
          (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 = pos r)
    (hint_p : ∀ r ∈ Submission.BoseGases.abox n L, Integrable (fun p : E3 => Fw p *
        ‖Submission.BoseGases.kinFT (fun z : E3 =>
          (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2) volume)
    {c : ℝ} (hc : 0 ≤ c)
    (hbdd : ∀ r ∈ Submission.BoseGases.abox n L, ∀ p : E3,
        ‖Submission.BoseGases.kinFT (fun z : E3 =>
          (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ≤ c) :
    ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, Fw p *
        ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
      = ∫ r in Submission.BoseGases.abox n L, pos r := by
  classical
  set ν : Measure (Submission.BoseGases.X n) :=
    (volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n L) with hν
  haveI : IsFiniteMeasure ν :=
    ⟨by rw [hν, Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top n L hL.le⟩
  set H : E3 × Submission.BoseGases.X n → ℝ := fun q => Fw q.1 *
    ‖Submission.BoseGases.kinFT (fun z : E3 =>
      (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, q.2)) : ℂ)) q.1‖ ^ 2 with hH
  have hHval : ∀ (p : E3) (r : Submission.BoseGases.X n), H (p, r) = Fw p *
      ‖Submission.BoseGases.kinFT (fun z : E3 =>
        (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 :=
    fun p r => rfl
  -- Step 1: peel and move the weight inside the `r`-integral.
  have hstep1 : (∫ p : E3, Fw p * ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) L,
        ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
      = ∫ p : E3, ∫ r, H (p, r) ∂ν := by
    refine integral_congr_ae (Eventually.of_forall (fun p => ?_))
    show Fw p * ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) L,
        ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2) = ∫ r, H (p, r) ∂ν
    rw [hpeel p]
    exact (MeasureTheory.integral_const_mul (Fw p)
      (fun r : Submission.BoseGases.X n => ‖Submission.BoseGases.kinFT (fun z : E3 =>
        (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2)).symm
  have hHmeas : AEStronglyMeasurable H ((volume : Measure E3).prod ν) :=
    cutPlancherel_jointAESM hχm hΦm i Fw hFc
  have hHnn : 0 ≤ H := fun q => mul_nonneg (hFnn q.1) (sq_nonneg _)
  -- a.e. strong measurability of the `r`-sections
  have hsec : ∀ᵐ p ∂(volume : Measure E3), AEStronglyMeasurable (fun r => H (p, r)) ν := by
    filter_upwards [MeasureTheory.Measure.ae_ae_eq_curry_of_prod hHmeas.ae_eq_mk] with p hp
    refine ⟨Function.curry hHmeas.mk p, ?_, hp⟩
    exact hHmeas.stronglyMeasurable_mk.comp_measurable (measurable_prodMk_left (x := p))
  -- integrability of the `r`-sections, from the uniform bound and the finiteness of `ν`
  have hint_r : ∀ᵐ p ∂(volume : Measure E3), Integrable (fun r => H (p, r)) ν := by
    filter_upwards [hsec] with p hp
    refine Integrable.of_bound hp (Fw p * c ^ 2) ?_
    filter_upwards [ae_restrict_mem (Submission.BoseGases.abox_measurable n L)] with r hr
    have h1 : H (p, r) = Fw p * ‖Submission.BoseGases.kinFT (fun z : E3 =>
        (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 := hHval p r
    have h2 : 0 ≤ Fw p * ‖Submission.BoseGases.kinFT (fun z : E3 =>
        (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 :=
      mul_nonneg (hFnn p) (sq_nonneg _)
    rw [h1, Real.norm_of_nonneg h2]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hbdd r hr p) 2) (hFnn p)
  -- integrability of the `p`-sections
  have hint_p' : ∀ᵐ r ∂ν, Integrable (fun p : E3 => H (Prod.swap (r, p)))
      (volume : Measure E3) := by
    rw [hν, ae_restrict_iff' (Submission.BoseGases.abox_measurable n L)]
    exact Eventually.of_forall (fun r hr => (hint_p r hr).congr
      (Eventually.of_forall (fun p => (hHval p r).symm)))
  -- Fubini, direction `p`-then-`r`
  have hFub1 := integral_prod_eq_iterated_of_ae_fibre_integrable
    (μ := (volume : Measure E3)) (ν := ν) hHmeas (Eventually.of_forall hHnn) hint_r
  -- Fubini, direction `r`-then-`p`, via the measure-preserving swap
  have hswap_mp : MeasurePreserving
      (Prod.swap : Submission.BoseGases.X n × E3 → E3 × Submission.BoseGases.X n)
      (ν.prod (volume : Measure E3)) ((volume : Measure E3).prod ν) :=
    Measure.measurePreserving_swap
  have hHmeas_swap : AEStronglyMeasurable (fun q : Submission.BoseGases.X n × E3 => H q.swap)
      (ν.prod (volume : Measure E3)) :=
    hHmeas.comp_measurePreserving hswap_mp
  have hFub2 := integral_prod_eq_iterated_of_ae_fibre_integrable
    (μ := ν) (ν := (volume : Measure E3)) hHmeas_swap
    (Eventually.of_forall (fun q => hHnn q.swap)) hint_p'
  have hswap_int : (∫ q : Submission.BoseGases.X n × E3, H q.swap
        ∂(ν.prod (volume : Measure E3)))
      = ∫ q : E3 × Submission.BoseGases.X n, H q ∂((volume : Measure E3).prod ν) :=
    hswap_mp.integral_comp (MeasurableEquiv.prodComm.measurableEmbedding) H
  have hswap' : ∀ (r : Submission.BoseGases.X n) (p : E3), H (Prod.swap (r, p)) = H (p, r) :=
    fun r p => rfl
  -- Step 4: the per-`r` Plancherel identity, with the prefactor moved onto the fibre.
  have hstep2 : (∫ r, ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : E3, H (p, r) ∂(volume : Measure E3)) ∂ν)
      = ∫ r in Submission.BoseGases.abox n L, pos r := by
    rw [hν]
    refine integral_congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' (Submission.BoseGases.abox_measurable n L)]
    refine Eventually.of_forall (fun r hr => ?_)
    rw [show (∫ p : E3, H (p, r) ∂(volume : Measure E3)) = ∫ p : E3, Fw p *
        ‖Submission.BoseGases.kinFT (fun z : E3 =>
          (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 from
      integral_congr_ae (Eventually.of_forall (fun p => hHval p r))]
    exact hpl r hr
  calc ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, Fw p *
        ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ r, ∫ p : E3, H (p, r) ∂(volume : Measure E3) ∂ν) := by
        rw [hstep1, hFub1.symm, hswap_int.symm, hFub2]
        simp only [hswap']
    _ = ∫ r, ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, H (p, r) ∂(volume : Measure E3)) ∂ν :=
        (MeasureTheory.integral_const_mul _ _).symm
    _ = ∫ r in Submission.BoseGases.abox n L, pos r := hstep2

/-! ## The target -/

theorem cutPlancherel_le {n : ℕ} {L : ℝ} (hL : 0 < L) {A : Set (EuclideanSpace ℝ (Fin 3))} {volA : ℝ}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hχ : ContDiff ℝ (⊤ : ENat) χ) (hχcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ Submission.BoseGases.acube L)
    {Ψ : Submission.BoseGases.X (n+1) → ℝ} (i : Fin (n+1))
    (hΦm : AEMeasurable (Work.SmallBoxTBWord.boxQ volA A i Ψ))
    {B : ℝ} (hB : ∀ x ∈ Submission.BoseGases.abox (n+1) L,
      |Work.SmallBoxTBWord.boxQ volA A i Ψ x| ≤ B)
    (hfib : ∀ r ∈ Submission.BoseGases.abox n L, ContDiff ℝ (⊤ : ENat)
      (fun z : EuclideanSpace ℝ (Fin 3) =>
      χ z * Work.SmallBoxTBWord.boxQ volA A i Ψ (Submission.BoseGases.kcInsN n i (z, r)))) :
    (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 *
        ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n+1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Ψ) i x‖ ^ 2)
      ≤ Work.BoseFixB1B.cutFibreDir L A volA χ i Ψ)
    ∧ (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
        ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n+1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Ψ) i x‖ ^ 2)
      ≤ Work.BoseFixB1B.cutFibreMass L A volA χ i Ψ) := by
  classical
  set Φ : Submission.BoseGases.X (n+1) → ℝ := Work.SmallBoxTBWord.boxQ volA A i Ψ with hΦdef
  have hΦm' : AEMeasurable Φ (volume : Measure (Submission.BoseGases.X (n+1))) := hΦm
  have hfib' : ∀ r ∈ Submission.BoseGases.abox n L, ContDiff ℝ (⊤ : ENat)
      (fun z : E3 => χ z * Φ (Submission.BoseGases.kcInsN n i (z, r))) :=
    fun r hr => hfib r hr
  have hpeel : ∀ p : E3, (L ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox (n + 1) L,
        ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)
      = ∫ r in Submission.BoseGases.abox n L,
          ‖Submission.BoseGases.kinFT (fun z : E3 =>
            (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 :=
    fun p => cutPlancherel_peel hL i p
  obtain ⟨c, hc, hbdd⟩ := cutPlancherel_KinFTBound hL hχ.continuous htsupp hB i
  constructor
  · -- the Dirichlet (first-derivative) form
    rw [cutFibreDir]
    refine le_of_eq (cutPlancherel_assembly hL hχ.continuous.measurable hΦm' i hpeel
      (fun p : E3 => ‖p‖ ^ 2) (continuous_norm.pow 2) (fun p => sq_nonneg _)
      (fun r => ∫ y in Submission.BoseGases.acube L, ∑ k : Fin 3,
        (fderiv ℝ (fun z : E3 => χ z * Φ (Submission.BoseGases.kcInsN n i (z, r)))
          y (Submission.BoseGases.kcStdBasis k)) ^ 2) ?_ ?_ hc (fun r hr p => hbdd r hr p))
    · -- the fibre-wise windowed Plancherel identity
      intro r hr
      have hwin := Work.SmallBoxTBWord.windowPlancherel (a := L)
        (W := fun z : E3 => χ z * Φ (Submission.BoseGases.kcInsN n i (z, r)))
        (ψ := fun _ : E3 => (1 : ℝ)) hL (hfib' r hr)
        (cutPlancherel_fibre_hcs hL htsupp i r)
        (fun z hz => htsupp (cutPlancherel_fibre_tsupport i r hz)) contDiff_const
      simpa only [Complex.ofReal_one, Complex.ofReal_mul, mul_one] using hwin
    · -- integrability of the `p`-energy of the fibre
      intro r hr
      have h := Work.SmallBoxTBWord.kinFT_energy_integrable
        (fun z : E3 => χ z * Φ (Submission.BoseGases.kcInsN n i (z, r))) (hfib' r hr)
        (cutPlancherel_fibre_hcs hL htsupp i r)
      refine h.congr (Eventually.of_forall (fun p => ?_))
      have harg : (fun z : E3 => ((χ z * Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℝ) : ℂ))
          = (fun z : E3 => (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) := by
        funext z
        rw [Complex.ofReal_mul]
      rw [harg]
  · -- the mass form
    rw [cutFibreMass]
    have hpl_mass : ∀ r ∈ Submission.BoseGases.abox n L, ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : E3, (1 : ℝ) * ‖Submission.BoseGases.kinFT (fun z : E3 =>
          (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2
          = ∫ y in Submission.BoseGases.acube L,
              (χ y * Φ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2 := by
      intro r hr
      have hpl := Work.BSKinetic.plancherel_pconv
        (fun z : E3 => χ z * Φ (Submission.BoseGases.kcInsN n i (z, r))) (hfib' r hr)
        (cutPlancherel_fibre_hcs hL htsupp i r)
      have harg : (fun x : E3 => ((χ x * Φ (Submission.BoseGases.kcInsN n i (x, r)) : ℝ) : ℂ))
          = (fun z : E3 => (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) := by
        funext z
        rw [Complex.ofReal_mul]
      have hχ0 : ∀ z : E3, z ∉ Submission.BoseGases.acube L → χ z = 0 :=
        cutPlancherel_chi_vanish htsupp
      simp only [one_mul]
      rw [harg] at hpl
      rw [hpl]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Submission.BoseGases.acube L)
        (f := fun x : E3 => (χ x * Φ (Submission.BoseGases.kcInsN n i (x, r))) ^ 2)
        (fun x hx => by rw [hχ0 x hx]; ring)).symm
    have hint_mass : ∀ r ∈ Submission.BoseGases.abox n L, Integrable (fun p : E3 => (1 : ℝ) *
        ‖Submission.BoseGases.kinFT (fun z : E3 =>
          (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2) volume := by
      intro r hr
      have h := cutPlancherel_massIntegrable hL htsupp i r (hfib' r hr)
      refine h.congr (Eventually.of_forall (fun p => ?_))
      simp only [one_mul]
    have hmain := cutPlancherel_assembly hL hχ.continuous.measurable hΦm' i hpeel
      (fun _ : E3 => (1 : ℝ)) continuous_const (fun p => zero_le_one)
      (fun r => ∫ y in Submission.BoseGases.acube L,
        (χ y * Φ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2) hpl_mass hint_mass hc
      (fun r hr p => hbdd r hr p)
    simpa only [one_mul] using le_of_eq hmain

end Work.BoseFixB1B
