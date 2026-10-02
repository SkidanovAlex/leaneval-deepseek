/-
# `Work.FQC.height_after_pg` — the critical Écalle height after the deformation

Let `θ = principal (muQC d fl hfl.Pg t)` be the principal solution of the invariant Beltrami
coefficient of the MNS deformation, and suppose that `θ` conjugates `T_c` to `T_{c₂}`
(`hconj`), that `θ 0 = 0` (`h0`), and that the phase normalisation
`saw (Re φa (tap)) = 1/2` holds at the first critical-orbit point of the petal (`hphase`).

The transported Écalle data of `d₂` is

* petal `Pa₂ = θ '' Pg` (the image of the `g`-invariant fundamental domain `Pg` of `PetalInput`);
* Fatou coordinate `φa₂ = ℓ_t ∘ φa ∘ θ⁻¹`,

where `ℓ_t` is the MNS twist of the Écalle cylinder.  Its key properties are

* `φa₂` is holomorphic on `Pa₂`: this is MRMT's item M2 (`principal_comp_symm`) applied to the
  composite `ℓ_t ∘ φa` on `Pg`, whose complex dilatation is exactly `muQC d fl hfl.Pg t` there;
  the required almost-everywhere relation is proved below (`ae_dzbar_ell_comp_fatou_pg_aux`):
  off the (null) preimage of the corner lines of the triangle wave, `ℓ_t` is locally real affine
  and the chain rule for the Wirtinger derivatives gives the identity pointwise;
* `φa₂` is antiholomorphically equivariant: `θ` intertwines the half-returns
  `g = (Tantibar c)^[5]`, `g₂ = (Tantibar c₂)^[5]`, and `ℓ_t` commutes with the involution
  `ι w = conj w + 1/2` (`ell_comm_I`);
* every orbit converging to `d₂.z₁` enters `Pa₂`, by transport of `enters_Pg`.

Since `θ` intertwines the critical orbits, the first critical-orbit point inside `Pa₂` is
`θ ((F c)^[n₀] c)`, where `n₀` is the first critical-orbit point inside `Pg`.  Because
`Pg ⊆ fl.Pa`, we have `n₁ ≤ n₀` for the first entry `n₁` into the petal, and the Abel equation
`φa (F z) = φa z + 1` on the petal shows that `φa ((F c)^[n₀] c) = φa ((F c)^[n₁] c) + (n₀ - n₁)`:
the imaginary part — the height — is unchanged, while the `1`-periodicity of `saw` keeps
`saw (Re φa)` equal to `1/2`, so that `ℓ_t` shifts the height by exactly `t/2` (`ell_im`,
`hphase`).
-/
import Mathlib
import Submission.Work.FQC.Defs
import Submission.Work.FQC.Petal
import Submission.Work.FQC.Ell
import Submission.Work.FQC.muQC_admissible_pg
import Submission.Work.FQC.ell_homeo
import Submission.Work.FQC.ell_beltrami
import Submission.Work.FQC.ell_beltrami_conj
import Submission.Work.FQC.saw_add_one
import Submission.Work.FQC.ell_add_one
import Submission.Work.FQC.transfer_parabolic_aux
import Submission.Work.MRMT.AhlforsBers.null_preimage_of_analyticOn
import Submission.Work.MRMT.Wirtinger.dz_comp
import Submission.Work.MRMT.Wirtinger.dzbar_comp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.FQC

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-! ## Auxiliary facts about `saw` and `ℓ_t` -/

/-- `saw` is `1`-periodic, in the form used for iterates of the return map. -/
theorem saw_add_nat (n : ℕ) (x : ℝ) : saw (x + n) = saw x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, ← add_assoc, saw_add_one, ih]

/-- The MNS twist is injective (its explicit inverse is `ellInv`). -/
theorem ell_twist_injective (t : ℝ) : Function.Injective (ell t) := by
  intro w w' h
  have h' := congrArg (ellInv t) h
  rwa [ellInv_ell, ellInv_ell] at h'

/-! ## `ℓ_t ∘ φa` is locally Lipschitz on the fundamental domain -/

theorem locallyLipschitzOn_ell_comp_Pg {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hfl : PetalInput d fl) (t : ℝ) :
    LocallyLipschitzOn hfl.Pg (fun z : ℂ => ell t (fl.φa z)) := by
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hfl.Pg_open z hz
  have hmono : DifferentiableOn ℂ fl.φa (Metric.ball z r) :=
    fl.φa_fatou.1.2.1.mono (fun x hx => hfl.Pg_sub (hball hx))
  have hana : AnalyticOnNhd ℂ fl.φa (Metric.ball z r) := hmono.analyticOnNhd Metric.isOpen_ball
  have hcdℂ : ContDiffOn ℂ 1 fl.φa (Metric.ball z r) :=
    hana.contDiffOn Metric.isOpen_ball.uniqueDiffOn
  have hcdℝ : ContDiffOn ℝ 1 fl.φa (Metric.ball z r) := ContDiffOn.restrict_scalars ℝ hcdℂ
  have hll : LocallyLipschitzOn (Metric.ball z r) fl.φa :=
    ContDiffOn.locallyLipschitzOn (convex_ball z r) hcdℝ
  obtain ⟨K₁, s, hs, hK₁⟩ := hll (Metric.mem_ball_self hr)
  obtain ⟨K₂, hK₂⟩ : ∃ K : NNReal, LipschitzOnWith K (ell t) Set.univ :=
    ⟨_, (lipschitzWith_ell_twist t).lipschitzOnWith (s := Set.univ)⟩
  have hb : Metric.ball z r ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)
  have hp : hfl.Pg ∈ 𝓝 z := hfl.Pg_open.mem_nhds hz
  have heq : (Metric.ball z r : Set ℂ) =ᶠ[𝓝 z] hfl.Pg :=
    Filter.eventuallyEq_of_mem (Filter.inter_mem hb hp)
      (fun x hx => propext ⟨fun _ => hx.2, fun _ => hx.1⟩)
  have hs' : s ∈ 𝓝[hfl.Pg] z := by
    rw [← (nhdsWithin_eq_iff_eventuallyEqSet (s := Metric.ball z r) (t := hfl.Pg)).mpr heq]
    exact hs
  exact ⟨K₂ * K₁, s, hs', hK₂.comp hK₁ (fun x _ => Set.mem_univ _)⟩

/-! ## The complex dilatation of `ℓ_t ∘ φa` on the fundamental domain

The lemmas below supply the hypothesis of MRMT's item M2 (`principal_comp_symm`) for the
composite `ℓ_t ∘ φa` on `Pg`: off the preimage of the corner lines of the triangle wave (a null
set, since `φa` is analytic and non-constant on the petal), `ℓ_t` is locally a real affine map
`a w + b w̄ + c` with `Re a = 1`, and the chain rule for the Wirtinger derivatives gives
`∂̄(ℓ_t ∘ φa) = (beltramiOf ℓ_t ∘ φa) · ∂(ℓ_t ∘ φa)`.  On `Pg` the latter coefficient is
`muQC d fl hfl.Pg t`, which gives the relation `ae_dzbar_ell_comp_fatou_pg_aux` below. -/

/-! ### 1. Germs of `ell t` off the corner lines -/

private theorem exists_affine_germ_ell {t : ℝ} {w : ℂ} (hw : w.re ∉ badRe) :
    ∃ a b c : ℂ, a ≠ 0 ∧ ell t =ᶠ[𝓝 w] fun v : ℂ => a * v + b * star v + c := by
  have h0 : Int.fract (w.re + 1 / 4) ≠ 0 := fun h => hw (mem_badRe_of_fract_zero h)
  have h2 : Int.fract (w.re + 1 / 4) ≠ 1 / 2 := fun h => hw (mem_badRe_of_fract_half h)
  obtain ⟨s, hsabs, hs⟩ := saw_eventually_affine h0 h2
  set a : ℂ := 1 + Complex.I * ((t * s / 2 : ℝ) : ℂ) with ha
  set b : ℂ := Complex.I * ((t * s / 2 : ℝ) : ℂ) with hb
  set c : ℂ := Complex.I * (t : ℂ) * ((saw w.re : ℂ) - (s : ℂ) * (w.re : ℂ)) with hc
  have hcast : ∀ z : ℂ, ((z.re : ℝ) : ℂ) = (z + star z) / 2 := by
    intro z
    rw [show z + star z = ((2 * z.re : ℝ) : ℂ) from Complex.add_conj z]
    push_cast; ring
  have hane : a ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [ha] at hre
    simp only [hb] at hre
    simp at hre
  refine ⟨a, b, c, hane, ?_⟩
  have hs' : saw =ᶠ[𝓝 w.re] (fun y : ℝ => saw w.re + s * (y - w.re)) := hs
  have hcomp : (fun v : ℂ => saw v.re) =ᶠ[𝓝 w] fun v => saw w.re + s * (v.re - w.re) := by
    simpa [Function.comp_def] using hs'.comp_tendsto Complex.continuous_re.continuousAt
  filter_upwards [hcomp] with v hv
  rw [ell_apply, hv]
  simp only [ha, hb, hc]
  push_cast
  rw [hcast v, hcast w]
  ring

private theorem differentiableAt_ell_of_notMem_badRe {t : ℝ} {w : ℂ} (hw : w.re ∉ badRe) :
    DifferentiableAt ℝ (ell t) w := by
  obtain ⟨a, b, c, _, hgerm⟩ := exists_affine_germ_ell (t := t) hw
  exact DifferentiableAt.congr_of_eventuallyEq
    (((a • (1 : ℂ →L[ℝ] ℂ) + b • (Complex.conjCLE : ℂ →L[ℝ] ℂ)).hasFDerivAt.add_const c).differentiableAt)
    hgerm

/-! ## 2. Wirtinger derivatives under eventual equality and along holomorphic maps -/

private theorem dz_eq_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    Work.MRMT.dz f z = Work.MRMT.dz g z := by
  simp only [Work.MRMT.dz, h.fderiv_eq]

private theorem dzbar_eq_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    Work.MRMT.dzbar f z = Work.MRMT.dzbar g z := by
  simp only [Work.MRMT.dzbar, h.fderiv_eq]

private theorem dz_comp_holo' {f g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g (f z))
    (hf : DifferentiableAt ℂ f z) :
    Work.MRMT.dz (fun w => g (f w)) z = Work.MRMT.dz g (f z) * deriv f z := by
  have h := Work.MRMT.Wirtinger.dz_comp (f := f) (g := g) (z := z) hg hf.real_of_complex
  rw [Work.MRMT.Found.dz_eq_deriv hf, Work.MRMT.Wirtinger.dzbar_of_holo hf, star_zero,
    mul_zero, add_zero] at h
  exact h

private theorem dzbar_comp_holo' {f g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g (f z))
    (hf : DifferentiableAt ℂ f z) :
    Work.MRMT.dzbar (fun w => g (f w)) z = Work.MRMT.dzbar g (f z) * star (deriv f z) := by
  have h := Work.MRMT.Wirtinger.dzbar_comp (f := f) (g := g) (z := z) hg hf.real_of_complex
  rw [Work.MRMT.Wirtinger.dzbar_of_holo hf, Work.MRMT.Found.dz_eq_deriv hf, mul_zero,
    zero_add] at h
  exact h

private theorem differentiableAt_φa {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    {z : ℂ} (hz : z ∈ fl.Pa) : DifferentiableAt ℂ fl.φa z :=
  (fl.φa_fatou.1.2.1 z hz).differentiableAt (fl.isOpen_Pa.mem_nhds hz)

/-! ## 3. The pointwise chain rule at good points -/

private theorem dzbar_ell_comp_φa_of_good {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (t : ℝ) {z : ℂ} (hz : z ∈ fl.Pa) (hgood : (fl.φa z).re ∉ badRe) :
    Work.MRMT.dzbar (fun w : ℂ => ell t (fl.φa w)) z =
      pullHolo (Work.MRMT.beltramiOf (ell t)) fl.φa z *
        Work.MRMT.dz (fun w : ℂ => ell t (fl.φa w)) z := by
  obtain ⟨a, b, c, hane, hgerm⟩ := exists_affine_germ_ell (t := t) hgood
  have hφdiff : DifferentiableAt ℂ fl.φa z := differentiableAt_φa d fl hz
  have hellA : DifferentiableAt ℝ (ell t) (fl.φa z) :=
    differentiableAt_ell_of_notMem_badRe hgood
  have hdze : Work.MRMT.dz (ell t) (fl.φa z) = a := by
    rw [dz_eq_of_eventuallyEq hgerm, Work.MRMT.dz_affine_star]
  have hdzbare : Work.MRMT.dzbar (ell t) (fl.φa z) = b := by
    rw [dzbar_eq_of_eventuallyEq hgerm, Work.MRMT.dzbar_affine_star]
  have hdz : Work.MRMT.dz (fun w : ℂ => ell t (fl.φa w)) z = a * deriv fl.φa z := by
    rw [dz_comp_holo' hellA hφdiff, hdze]
  have hdzbar : Work.MRMT.dzbar (fun w : ℂ => ell t (fl.φa w)) z = b * star (deriv fl.φa z) := by
    rw [dzbar_comp_holo' hellA hφdiff, hdzbare]
  rw [hdz, hdzbar, pullHolo, Work.MRMT.beltramiOf, hdze, hdzbare]
  by_cases hD : deriv fl.φa z = 0
  · simp [hD]
  · field_simp

/-! ## 4. `muQC` on the fundamental domain is the pulled-back coefficient -/

private theorem muQC_eq_pullHolo_of_mem_Pg {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hfl : PetalInput d fl) {t : ℝ} {z : ℂ} (hz : z ∈ hfl.Pg) :
    muQC d fl hfl.Pg t z = pullHolo (Work.MRMT.beltramiOf (ell t)) fl.φa z := by
  classical
  have hb : z ∈ basin d hfl.Pg := ⟨0, by simpa using hz⟩
  simp only [basin] at hb
  rw [muQC_of_mem d hb]
  have hfind : Nat.find hb = 0 := by
    rw [Nat.find_eq_zero]
    simpa using hz
  rw [hfind, pullAntiIter_zero]
  simp only [pullHoloOn, pullHolo]
  rw [if_pos hz]

/-! ## 5. The Fatou coordinate is not constant on the petal -/

private theorem phi_a_not_const_on_petal {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) :
    ¬ ∃ a : ℂ, ∀ z ∈ fl.Pa, fl.φa z = a := by
  rintro ⟨a, ha⟩
  obtain ⟨z₀, hz₀⟩ : fl.Pa.Nonempty := ⟨_, nEnter_spec (EcalleData.ofFlower d fl)⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp fl.isOpen_Pa z₀ hz₀
  have hz₂ : z₀ + ((r / 2 : ℝ) : ℂ) ∈ fl.Pa := by
    apply hball
    have h : ‖(((r / 2) : ℝ) : ℂ)‖ = |r| / 2 := by simp
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, h,
      abs_of_pos (by linarith : (0:ℝ) < r)]
    linarith
  have hne : z₀ + ((r / 2 : ℝ) : ℂ) ≠ z₀ := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  exact hne ((fl.φa_fatou.2 hz₀ hz₂ (by rw [ha _ hz₀, ha _ hz₂]))).symm

/-! ## 6. Almost every petal point has a good phase -/

private theorem ae_phi_a_re_not_mem_badRe {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) :
    ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), z ∈ fl.Pa → (fl.φa z).re ∉ badRe := by
  have hana : AnalyticOnNhd ℂ fl.φa fl.Pa := fl.φa_fatou.1.2.1.analyticOnNhd fl.isOpen_Pa
  have hnull : MeasureTheory.volume (fl.φa ⁻¹' {w : ℂ | w.re ∈ badRe} ∩ fl.Pa) = 0 :=
    Work.MRMT.AhlforsBers.null_preimage_of_analyticOn fl.isOpen_Pa fl.isPreconnected_Pa hana
      (phi_a_not_const_on_petal d fl) volume_re_mem_bad
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro z hz
  rw [Set.mem_setOf_eq] at hz
  simp only [not_imp, not_not] at hz
  exact ⟨hz.2, hz.1⟩

/-! ## 7. The a.e. dilatation relation on the fundamental domain -/

private theorem ae_dzbar_ell_comp_fatou_pg_aux {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hfl : PetalInput d fl) (t : ℝ) :
    ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), z ∈ hfl.Pg →
      Work.MRMT.dzbar (fun w : ℂ => ell t (fl.φa w)) z =
        muQC d fl hfl.Pg t z * Work.MRMT.dz (fun w : ℂ => ell t (fl.φa w)) z := by
  rw [ae_iff]
  refine measure_mono_null ?_ (ae_phi_a_re_not_mem_badRe d fl)
  intro z hz
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff] at hz ⊢
  rw [not_imp] at hz
  obtain ⟨hzPg, hzrel⟩ := hz
  rw [not_imp]
  refine ⟨hfl.Pg_sub hzPg, fun hgood => hzrel ?_⟩
  rw [muQC_eq_pullHolo_of_mem_Pg d fl hfl hzPg]
  exact dzbar_ell_comp_φa_of_good d fl t (hfl.Pg_sub hzPg) hgood


/-! ## The height after the deformation -/

theorem height_after_pg {c : ℂ} (d : Work.EL.RootParabolic c) (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁) (hfl : Work.FQC.PetalInput d fl) (t : ℝ) {c₂ : ℂ} (d₂ : Work.EL.RootParabolic c₂) (hconj : ∀ z : ℂ, Work.MRMT.Found.principal (Work.FQC.muQC d fl hfl.Pg t) (LeanEval.ComplexAnalysis.Tantibar c z) = LeanEval.ComplexAnalysis.Tantibar c₂ (Work.MRMT.Found.principal (Work.FQC.muQC d fl hfl.Pg t) z)) (h0 : (Work.MRMT.Found.principal (Work.FQC.muQC d fl hfl.Pg t)) 0 = 0) (hphase : Work.FQC.saw ((fl.φa ((Work.EL.F c)^[Work.FQC.nEnter (Work.FQC.EcalleData.ofFlower d fl)] c)).re) = 1 / 2) : ∃ E₂ : Work.FQC.EcalleData d₂, Work.FQC.critHeightAt d₂ E₂ = Work.FQC.critHeightAt d (Work.FQC.EcalleData.ofFlower d fl) + t / 2 := by
  -- the conjugating homeomorphism, the coefficient and its admissibility
  set θ : ℂ ≃ₜ ℂ := Work.MRMT.Found.principal (muQC d fl hfl.Pg t) with hθdef
  have hconjθ : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z) := fun z => hconj z
  have h0θ : θ 0 = 0 := h0
  have hμ : Work.MRMT.Found.Admissible (muQC d fl hfl.Pg t) := muQC_admissible_pg d fl hfl t
  -- transport of the iterates of `T_c` and of `F c`
  have hT : ∀ n z, θ ((Tantibar c)^[n] z) = (Tantibar c₂)^[n] (θ z) :=
    Work.FQC.theta_iterate θ hconjθ
  have hF : ∀ n z, θ ((F c)^[n] z) = (F c₂)^[n] (θ z) :=
    Work.FQC.theta_iterate_F θ (Work.FQC.conj_F θ hconjθ)
  -- the transported parameter is `θ c` and the transported parabolic point is `θ d.z₁`
  have hc₂ : c₂ = θ c := by
    have h1 := hconjθ 0
    have hT0 : Tantibar c 0 = c := by simp [Work.Landing.Tantibar_apply]
    have hT0' : Tantibar c₂ 0 = c₂ := by simp [Work.Landing.Tantibar_apply]
    rw [hT0, h0θ, hT0'] at h1
    exact h1.symm
  -- the critical orbit of `d₂` and the one of `d` are `θ`-related
  have hkeyF : ∀ m : ℕ, (F c₂)^[m] c₂ = θ ((F c)^[m] c) := by
    intro m
    exact (congrArg (fun x : ℂ => (F c₂)^[m] x) hc₂).trans (hF m c).symm
  have hz₁ : θ d.z₁ = d₂.z₁ := by
    have hseq : (fun n : ℕ => (F c₂)^[n] c₂) = fun n => θ ((F c)^[n] c) :=
      funext hkeyF
    have h1 : Tendsto (fun n : ℕ => (F c₂)^[n] c₂) atTop (nhds (θ d.z₁)) := by
      rw [hseq]
      exact (θ.continuous.tendsto d.z₁).comp d.crit.1
    exact tendsto_nhds_unique h1 d₂.crit.1
  -- the first critical-orbit point inside `Pg`
  set n₀ : ℕ := Nat.find (hfl.enters_Pg c d.crit.1 d.crit.2) with hn₀
  have hn₀mem : (F c)^[n₀] c ∈ hfl.Pg := by
    rw [hn₀]; exact Nat.find_spec (hfl.enters_Pg c d.crit.1 d.crit.2)
  have hn₀min : ∀ m : ℕ, (F c)^[m] c ∈ hfl.Pg → n₀ ≤ m := by
    intro m hm
    rw [hn₀]; exact Nat.find_min' _ hm
  -- membership in `Pa₂ = θ '' Pg` is transported
  have hiff : ∀ m : ℕ, (F c₂)^[m] c₂ ∈ θ '' hfl.Pg ↔ (F c)^[m] c ∈ hfl.Pg := by
    intro m
    constructor
    · rintro ⟨z, hz, hzθ⟩
      have hz' : (F c)^[m] c = z := θ.injective (by rw [← hkeyF m, hzθ])
      rwa [hz']
    · intro hm
      exact ⟨(F c)^[m] c, hm, (hkeyF m).symm⟩
  -- the a.e. complex-dilatation relation on the fundamental domain
  have hrel : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), z ∈ hfl.Pg →
      Work.MRMT.dzbar (fun z : ℂ => ell t (fl.φa z)) z =
        muQC d fl hfl.Pg t z * Work.MRMT.dz (fun z : ℂ => ell t (fl.φa z)) z :=
    ae_dzbar_ell_comp_fatou_pg_aux d fl hfl t
  have hdiff : DifferentiableOn ℂ
      (fun w : ℂ => ell t (fl.φa (θ.symm w))) (θ '' hfl.Pg) := by
    have h := principal_comp_symm hμ hfl.Pg_open (locallyLipschitzOn_ell_comp_Pg d fl hfl t) hrel
    simpa only [Function.comp_def] using h
  -- the transported Écalle data
  -- the five corrected fields of `EcalleData`, transported along `θ`
  have hFθ : ∀ z : ℂ, (F c₂) (θ z) = θ ((F c) z) := by
    intro z
    have h := hF 1 z
    rw [Function.iterate_one, Function.iterate_one] at h
    exact h.symm
  have hpre₂ : IsPreconnected (θ '' hfl.Pg) :=
    hfl.Pg_preconnected.image θ θ.continuous.continuousOn
  have hz₁₂ : d₂.z₁ ∉ θ '' hfl.Pg := by
    rintro ⟨z, hz, hzθ⟩
    have hz_eq : z = d.z₁ := θ.injective (by rw [hzθ, hz₁])
    exact fl.z₀_not_mem (hfl.Pg_sub (hz_eq ▸ hz))
  have hmap₂ : MapsTo (F c₂) (θ '' hfl.Pg) (θ '' hfl.Pg) := by
    rintro w ⟨z, hz, rfl⟩
    refine ⟨(Tantibar c)^[5] ((Tantibar c)^[5] z), ?_, ?_⟩
    · exact hfl.mapsTo_g_Pg ((Tantibar c)^[5] z) (hfl.mapsTo_g_Pg z hz)
    · rw [← comp_self_apply (F := F c) (g := (Tantibar c)^[5]) (ten_eq_five_comp_five c) z]
      exact (hFθ z).symm
  have htend₂ : ∀ w ∈ θ '' hfl.Pg, Tendsto (fun n : ℕ => (F c₂)^[n] w) atTop (nhds d₂.z₁) := by
    rintro w ⟨z, hz, rfl⟩
    have h2 : Tendsto (fun n : ℕ => θ ((F c)^[n] z)) atTop (nhds (θ d.z₁)) :=
      (θ.continuous.tendsto d.z₁).comp (fl.tendsto_Pa z (hfl.Pg_sub hz))
    rw [hz₁] at h2
    exact h2.congr' (Eventually.of_forall fun n => hF n z)
  have hshift₂ : ∀ w ∈ θ '' hfl.Pg,
      (fun w : ℂ => ell t (fl.φa (θ.symm w))) ((F c₂) w) =
        (fun w : ℂ => ell t (fl.φa (θ.symm w))) w + 1 := by
    rintro w ⟨z, hz, rfl⟩
    show ell t (fl.φa (θ.symm ((F c₂) (θ z)))) = ell t (fl.φa (θ.symm (θ z))) + 1
    rw [hFθ z, θ.symm_apply_apply, θ.symm_apply_apply]
    rw [hfl.φa_shift z (hfl.Pg_sub hz)]
    exact ell_add_one t (fl.φa z)
  let E₂ : EcalleData d₂ :=
    { Pa := θ '' hfl.Pg
      φa := fun w : ℂ => ell t (fl.φa (θ.symm w))
      isOpen_Pa := θ.isOpenMap hfl.Pg hfl.Pg_open
      φa_diff := hdiff
      isPreconnected_Pa := hpre₂
      z₁_not_mem_Pa := hz₁₂
      mapsTo_Pa := hmap₂
      tendsto_Pa := htend₂
      φa_shift := hshift₂
      φa_inj := by
        intro w hw w' hw' heq
        obtain ⟨z, hz, rfl⟩ := hw
        obtain ⟨z', hz', rfl⟩ := hw'
        simp only [Homeomorph.symm_apply_apply] at heq
        have h1 : fl.φa z = fl.φa z' := ell_twist_injective t heq
        have h2 : z = z' := fl.φa_fatou.2 (hfl.Pg_sub hz) (hfl.Pg_sub hz') h1
        rw [h2]
      φa_anti := by
        intro w hw
        obtain ⟨z, hz, rfl⟩ := hw
        have h5 : (Tantibar c₂)^[5] (θ z) = θ ((Tantibar c)^[5] z) := (hT 5 z).symm
        rw [h5, θ.symm_apply_apply, θ.symm_apply_apply,
          fl.φa_fatou.1.2.2 z (hfl.Pg_sub hz)]
        exact ell_comm_I t (fl.φa z)
      enters := by
        intro w hconv hne
        have hkey : ∀ n : ℕ, θ.symm ((F c₂)^[n] w) = (F c)^[n] (θ.symm w) := by
          intro n
          rw [congrArg (fun x : ℂ => (F c₂)^[n] x) (θ.apply_symm_apply w).symm,
            (hF n (θ.symm w)).symm, θ.symm_apply_apply]
        have hkeyinv : ∀ n : ℕ, θ ((F c)^[n] (θ.symm w)) = (F c₂)^[n] w := by
          intro n
          rw [← hkey n, θ.apply_symm_apply]
        have hconv' : Tendsto (fun n : ℕ => (F c)^[n] (θ.symm w)) atTop (nhds d.z₁) := by
          have h1 : Tendsto (fun n : ℕ => (F c₂)^[n] w) atTop (nhds (θ d.z₁)) := by
            rw [hz₁]; exact hconv
          have h2 := (θ.symm.continuous.tendsto (θ d.z₁)).comp h1
          rw [Homeomorph.symm_apply_apply] at h2
          refine h2.congr' (Eventually.of_forall fun n => ?_)
          show θ.symm ((F c₂)^[n] w) = (F c)^[n] (θ.symm w)
          exact hkey n
        have hne' : ∀ n : ℕ, (F c)^[n] (θ.symm w) ≠ d.z₁ := by
          intro n hn
          refine hne n ?_
          rw [← hkeyinv n, hn, hz₁]
        obtain ⟨n, hn⟩ := hfl.enters_Pg (θ.symm w) hconv' hne'
        exact ⟨n, (F c)^[n] (θ.symm w), hn, hkeyinv n⟩ }
  refine ⟨E₂, ?_⟩
  -- the first critical-orbit point inside `Pa₂ = θ '' Pg` is `θ` of the one inside `Pg`
  have hnEnter : nEnter E₂ = n₀ := by
    refine le_antisymm ?_ ?_
    · exact nEnter_minimal E₂ ((hiff n₀).mpr hn₀mem)
    · exact hn₀min _ ((hiff (nEnter E₂)).mp (nEnter_spec E₂))
  -- the height is read off at `θ ((F c)^[n₀] c)`
  have hcrit : critHeightAt d₂ E₂ = (ell t (fl.φa ((F c)^[n₀] c))).im := by
    rw [critHeightAt, hnEnter]
    show (ell t (fl.φa (θ.symm ((F c₂)^[n₀] c₂)))).im = _
    rw [hkeyF n₀, Homeomorph.symm_apply_apply]
  -- the first entry `n₁` into the petal is `≤ n₀`, and the Abel equation shifts by the difference
  set n₁ : ℕ := nEnter (EcalleData.ofFlower d fl) with hn₁
  have hn₁mem : (F c)^[n₁] c ∈ fl.Pa := by
    rw [hn₁]; exact nEnter_spec (EcalleData.ofFlower d fl)
  have hn₁le : n₁ ≤ n₀ := by
    have h : nEnter (EcalleData.ofFlower d fl) ≤ n₀ :=
      nEnter_minimal (EcalleData.ofFlower d fl) (hfl.Pg_sub hn₀mem)
    rwa [hn₁]
  have hphase' : saw ((fl.φa ((F c)^[n₁] c)).re) = 1 / 2 := by
    rw [hn₁]; exact hphase
  have hmemF : ∀ k : ℕ, (F c)^[k] ((F c)^[n₁] c) ∈ fl.Pa := by
    intro k
    induction k with
    | zero => simpa using hn₁mem
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact fl.mapsTo_Pa ih
  have hshift : ∀ k : ℕ, fl.φa ((F c)^[k] ((F c)^[n₁] c)) =
      fl.φa ((F c)^[n₁] c) + (k : ℂ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply', hfl.φa_shift _ (hmemF k), ih]
        push_cast; ring
  have hiter : (F c)^[n₀ - n₁] ((F c)^[n₁] c) = (F c)^[n₀] c := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hn₁le]
  have hφ : fl.φa ((F c)^[n₀] c) = fl.φa ((F c)^[n₁] c) + ((n₀ - n₁ : ℕ) : ℂ) := by
    rw [← hiter]
    exact hshift (n₀ - n₁)
  have him : (fl.φa ((F c)^[n₀] c)).im = (fl.φa ((F c)^[n₁] c)).im := by
    rw [hφ]; simp
  have hre : (fl.φa ((F c)^[n₀] c)).re = (fl.φa ((F c)^[n₁] c)).re + ((n₀ - n₁ : ℕ) : ℝ) := by
    rw [hφ]; simp
  have hsaw : saw ((fl.φa ((F c)^[n₀] c)).re) = 1 / 2 := by
    rw [hre, saw_add_nat (n₀ - n₁)]
    exact hphase'
  -- assembly
  calc critHeightAt d₂ E₂ = (ell t (fl.φa ((F c)^[n₀] c))).im := hcrit
    _ = (fl.φa ((F c)^[n₀] c)).im + t * saw ((fl.φa ((F c)^[n₀] c)).re) := by
        rw [ell_im]
    _ = (fl.φa ((F c)^[n₁] c)).im + t * (1 / 2) := by rw [him, hsaw]
    _ = critHeightAt d (EcalleData.ofFlower d fl) + t / 2 := by
        rw [show critHeightAt d (EcalleData.ofFlower d fl) =
          (fl.φa ((F c)^[n₁] c)).im from rfl]
        ring

end Work.FQC

end
