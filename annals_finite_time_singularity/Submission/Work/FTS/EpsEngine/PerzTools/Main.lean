/-
Copyright: work module for the Elgindi finite-time singularity project.

# The interval-integral `ℋ`-membership (per-`z` version): the main estimate

This module proves `intervalIntegral_perz_aux`, the per-`z` version of the interval-integral
`ℋ`-membership: for a family `s ↦ H s` of profiles on the horizon `[0,T]`, all of them smooth on
the open quadrant, each in `ℋ^k` with `HkNorm α k (H s) ≤ B`, jointly measurable, uniformly bounded
in every slot on compacta, and with a uniform-in-`s` per-`z` energy bound `C z`, the interval
integral `∫_a^b H s ds` lies in `ℋ^k` with `HkNorm ≤ B (b-a)`.

The two genuinely analytic inputs — the `(s,θ)`-Carathéodory measurability and the exchange
identity for a restricted order — are the interface hypotheses `CarathTheta` and `ExchMixed`
of `PerzTools/Basic.lean`; see `PerzTools/Exchange.lean` for the reduction.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EpsEngine.PerzTools.Exchange

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.PerzTools

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem intervalIntegral_perz_aux (hcar : CarathTheta) (hexch : ExchMixed)
    {α B : ℝ} {k : ℕ} {T a b : ℝ} {H : ℝ → ℝ → ℝ → ℝ}
    (hab : a ≤ b) (hT : 0 ≤ T) (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmem : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α k (H s))
    (hbd : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α k (H s) ≤ B)
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α k (H p.1) p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))))
    (hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    (hperz : ∀ z ∈ Work.Spaces.Iz, ∃ Cz : ℝ,
      ∀ s ∈ Set.Icc (0 : ℝ) T,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (H s) z θ) ≤ Cz) :
    Work.Spaces.HkMem α k (fun z θ => ∫ s in a..b, H s z θ) ∧
      Work.Spaces.HkNorm α k (fun z θ => ∫ s in a..b, H s z θ) ≤ B * (b - a) := by
  classical
  set G : ℝ → ℝ → ℝ := fun z θ => ∫ s in a..b, H s z θ with hG
  have hab0 : (0 : ℝ) ≤ b - a := by linarith
  -- ## (1) elementary consequences of the hypotheses
  have hB : 0 ≤ B := le_trans (Work.Spaces.HkNorm_nonneg α k (H a)) (hbd a haT)
  have hSq_le : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkSq α k (H s) ≤ B ^ 2 := by
    intro s hs
    have hnn : 0 ≤ Work.Spaces.HkSq α k (H s) :=
      integral_nonneg fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k (H s) z θ
    calc Work.Spaces.HkSq α k (H s) = (Work.Spaces.HkNorm α k (H s)) ^ 2 := by
          rw [Work.Spaces.HkNorm, Real.sq_sqrt hnn]
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α k (H s)) (hbd s hs) 2
  have hsub : Set.uIoc a b ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  -- ## (2) measurability of the primitive's integrand
  have hsliceAESM : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.HkIntegrand α k G z θ)
        (volume.restrict Work.Spaces.Iθ) :=
    fun z hz => aesm_slice_HkIntegrand_primitive hcar hexch haT hbT hab hsm hmeas hsup hz
  have hjointG : AEStronglyMeasurable
      (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k G q.1 q.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    aesm_HkIntegrand_primitive hexch haT hbT hab hsm hmeas hsup
  have houterAESM : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k G z θ)
      (volume.restrict Work.Spaces.Iz) :=
    hjointG.integral_prod_right'
  -- ## (3) the per-`z` energy bound of the primitive's integrand
  have hzFin : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ)) < ⊤ := by
    intro z hz
    obtain ⟨Cz, hCz⟩ := hperz z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0]
      have hzero : (fun θ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k G 0 θ))
          = fun _ : ℝ => (0 : ENNReal) := by
        funext θ
        rw [HkIntegrand_fst_zero α k G θ]
        simp
      rw [hzero]
      simp
    · have hIθ : volume.restrict (Set.Ioo 0 (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ :=
        MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
      have key : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ)
            ≤ ENNReal.ofReal (b - a) * (∫⁻ s in Set.uIoc a b,
                ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)) := by
        rw [← hIθ]
        refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
        have hq : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
          Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ⟩
        have hcv := cv_bound (α := α) hexch haT hbT hab hsm hmeas hsup hq
        have hconv : ∫ s in a..b, Work.Spaces.HkIntegrand α k (H s) z θ
            = ∫ s in Set.uIoc a b, Work.Spaces.HkIntegrand α k (H s) z θ := by
          rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]
        calc ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ)
            ≤ ENNReal.ofReal ((b - a) * ∫ s in a..b, Work.Spaces.HkIntegrand α k (H s) z θ) :=
              ENNReal.ofReal_le_ofReal hcv
          _ = ENNReal.ofReal (b - a)
                * ENNReal.ofReal (∫ s in a..b, Work.Spaces.HkIntegrand α k (H s) z θ) :=
              ENNReal.ofReal_mul hab0
          _ ≤ ENNReal.ofReal (b - a)
                * (∫⁻ s in Set.uIoc a b,
                    ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)) := by
              refine mul_le_mul_right ?_ _
              rw [hconv]
              exact ofReal_integral_le_lintegral_ofReal
                (fun s => Work.Spaces.HkIntegrand_nonneg α k (H s) z θ)
      have step2 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (b - a)
            * (∫⁻ s in Set.uIoc a b, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)))
          = ENNReal.ofReal (b - a) * ∫⁻ s in Set.uIoc a b,
              ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ) := by
        rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        symm
        refine MeasureTheory.lintegral_lintegral_swap
          (μ := volume.restrict (Set.uIoc a b)) (ν := volume.restrict Work.Spaces.Iθ)
          (f := fun s θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)) ?_
        have h3 := perz_aesm_HkIntegrand hcar hsm hmeas hzpos (α := α) (k := k)
        exact ((h3.mono_measure
          (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)).aemeasurable).ennreal_ofReal
      have step3 : (∫⁻ s in Set.uIoc a b,
            ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ))
          ≤ ∫⁻ s in Set.uIoc a b, ENNReal.ofReal Cz := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
        have hsT : s ∈ Set.Icc (0 : ℝ) T := hsub hs
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hmem s hsT).1 z hz)
          (Filter.Eventually.of_forall
            (fun θ => Work.Spaces.HkIntegrand_nonneg α k (H s) z θ))]
        exact ENNReal.ofReal_le_ofReal (hCz s hsT)
      have step4 : (∫⁻ s in Set.uIoc a b, ENNReal.ofReal Cz)
          = ENNReal.ofReal Cz * ENNReal.ofReal (b - a) := by
        rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
          Real.volume_uIoc, abs_of_nonneg hab0]
      refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := b - a))
        (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := Cz))
          (ENNReal.ofReal_lt_top (r := b - a))))
      calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ))
          ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (b - a)
              * (∫⁻ s in Set.uIoc a b,
                  ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)) :=
            lintegral_mono_ae key
        _ = ENNReal.ofReal (b - a) * ∫⁻ s in Set.uIoc a b,
              ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ) := step2
        _ ≤ ENNReal.ofReal (b - a) * ∫⁻ s in Set.uIoc a b, ENNReal.ofReal Cz :=
            mul_le_mul_right step3 _
        _ = ENNReal.ofReal (b - a) * (ENNReal.ofReal Cz * ENNReal.ofReal (b - a)) := by
            rw [step4]
  -- ## (4) the energy bound of the primitive on the whole quadrant
  have hqFin : (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k G q.1 q.2)
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      ≤ ENNReal.ofReal ((b - a) ^ 2 * B ^ 2) := by
    have key : ∀ᵐ q ∂((volume.restrict Work.Spaces.Iz).prod
        (volume.restrict Work.Spaces.Iθ)),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k G q.1 q.2)
          ≤ ENNReal.ofReal (b - a) * (∫⁻ s in Set.uIoc a b,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) q.1 q.2)) := by
      filter_upwards [ae_mem_Q0] with q hq
      have hcv := cv_bound (α := α) hexch haT hbT hab hsm hmeas hsup hq
      have hconv : ∫ s in a..b, Work.Spaces.HkIntegrand α k (H s) q.1 q.2
          = ∫ s in Set.uIoc a b, Work.Spaces.HkIntegrand α k (H s) q.1 q.2 := by
        rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]
      calc ENNReal.ofReal (Work.Spaces.HkIntegrand α k G q.1 q.2)
          ≤ ENNReal.ofReal ((b - a) * ∫ s in a..b,
              Work.Spaces.HkIntegrand α k (H s) q.1 q.2) := ENNReal.ofReal_le_ofReal hcv
        _ = ENNReal.ofReal (b - a)
              * ENNReal.ofReal (∫ s in a..b, Work.Spaces.HkIntegrand α k (H s) q.1 q.2) :=
            ENNReal.ofReal_mul hab0
        _ ≤ ENNReal.ofReal (b - a)
              * (∫⁻ s in Set.uIoc a b,
                  ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) q.1 q.2)) := by
            refine mul_le_mul_right ?_ _
            rw [hconv]
            exact ofReal_integral_le_lintegral_ofReal
              (fun s => Work.Spaces.HkIntegrand_nonneg α k (H s) q.1 q.2)
    have step2 : (∫⁻ x, ENNReal.ofReal (b - a)
          * (∫⁻ s in Set.uIoc a b,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) x.1 x.2))
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
        = ENNReal.ofReal (b - a) * ∫⁻ s in Set.uIoc a b,
            ∫⁻ x, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) x.1 x.2)
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
      rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      symm
      refine MeasureTheory.lintegral_lintegral_swap
        (μ := volume.restrict (Set.uIoc a b))
        (ν := (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
        (f := fun s x => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) x.1 x.2)) ?_
      exact ((hjoint.mono_measure
        (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)).aemeasurable).ennreal_ofReal
    have hsliceEq : ∀ s ∈ Set.Icc (0 : ℝ) T,
        (∫⁻ x, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) x.1 x.2)
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
          = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (H s) z θ) := by
      intro s hsT
      have hprod : AEMeasurable
          (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2))
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
        (Work.Spaces.aesm_of_continuousOn_Qd _
          ((hsm s hsT).continuousOn_HkIntegrand α k)).aemeasurable.ennreal_ofReal
      rw [MeasureTheory.lintegral_prod _ hprod]
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hmem s hsT).1 z hz)
        (Filter.Eventually.of_forall
          (fun θ => Work.Spaces.HkIntegrand_nonneg α k (H s) z θ))).symm
    have step3 : (∫⁻ s in Set.uIoc a b, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (H s) z θ))
        ≤ ∫⁻ s in Set.uIoc a b, ENNReal.ofReal (B ^ 2) := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      have hsT : s ∈ Set.Icc (0 : ℝ) T := hsub hs
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem s hsT).2
        (Filter.Eventually.of_forall (fun z =>
          integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k (H s) z θ))]
      exact ENNReal.ofReal_le_ofReal (hSq_le s hsT)
    have step4 : (∫⁻ s in Set.uIoc a b, ENNReal.ofReal (B ^ 2))
        = ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (b - a) := by
      rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
        Real.volume_uIoc, abs_of_nonneg hab0]
    have hB2 : (0 : ℝ) ≤ B ^ 2 := sq_nonneg B
    calc (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k G q.1 q.2)
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
        ≤ ∫⁻ q, ENNReal.ofReal (b - a) * (∫⁻ s in Set.uIoc a b,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) q.1 q.2))
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
          lintegral_mono_ae key
      _ = ENNReal.ofReal (b - a) * ∫⁻ s in Set.uIoc a b,
            ∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) q.1 q.2)
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := step2
      _ = ENNReal.ofReal (b - a) * ∫⁻ s in Set.uIoc a b,
            ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (H s) z θ) := by
          congr 1
          refine lintegral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
          exact hsliceEq s (hsub hs)
      _ ≤ ENNReal.ofReal (b - a) * ∫⁻ s in Set.uIoc a b, ENNReal.ofReal (B ^ 2) :=
          mul_le_mul_right step3 _
      _ = ENNReal.ofReal ((b - a) ^ 2 * B ^ 2) := by
          rw [step4, ← ENNReal.ofReal_mul hB2, ← ENNReal.ofReal_mul hab0]
          ring_nf
  -- ## (5) the `z`-integral of the primitive's angular energy
  have houterBound : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k G z θ))
      ≤ ENNReal.ofReal ((b - a) ^ 2 * B ^ 2) := by
    have hconv1 : (∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k G q.1 q.2)
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
        = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ) :=
      MeasureTheory.lintegral_prod _ (hjointG.aemeasurable.ennreal_ofReal)
    have hstep : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k G z θ))
        = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        ((MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (hsliceAESM z hz)
            (Filter.Eventually.of_forall
              (fun θ => Work.Spaces.HkIntegrand_nonneg α k G z θ))).mp
          (ne_of_lt (hzFin z hz)))
        (Filter.Eventually.of_forall (fun θ => Work.Spaces.HkIntegrand_nonneg α k G z θ))
    calc (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k G z θ))
        = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ) := hstep
      _ = ∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k G q.1 q.2)
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
          hconv1.symm
      _ ≤ ENNReal.ofReal ((b - a) ^ 2 * B ^ 2) := hqFin
  -- ## (6) assembly
  have hsliceInt : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k G z θ) Work.Spaces.Iθ := by
    intro z hz
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (hsliceAESM z hz)
      (Filter.Eventually.of_forall
        (fun θ => Work.Spaces.HkIntegrand_nonneg α k G z θ))).mp (ne_of_lt (hzFin z hz))
  have houterInt : IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k G z θ)
      Work.Spaces.Iz := by
    refine ⟨houterAESM, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k G z θ))]
    exact lt_of_le_of_lt houterBound ENNReal.ofReal_lt_top
  have hSqG : Work.Spaces.HkSq α k G ≤ (b - a) ^ 2 * B ^ 2 := by
    have h1 : ENNReal.ofReal (Work.Spaces.HkSq α k G)
        = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k G z θ) :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal houterInt
        (Filter.Eventually.of_forall (fun z =>
          integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k G z θ))
    rw [← h1] at houterBound
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) (sq_nonneg B))).mp houterBound
  refine ⟨⟨hsliceInt, houterInt⟩, ?_⟩
  rw [Work.Spaces.HkNorm]
  have h2 : (b - a) ^ 2 * B ^ 2 = ((b - a) * B) ^ 2 := by ring
  calc Real.sqrt (Work.Spaces.HkSq α k G)
      ≤ Real.sqrt (((b - a) * B) ^ 2) := Real.sqrt_le_sqrt (by rw [← h2]; exact hSqG)
    _ = |(b - a) * B| := Real.sqrt_sq_eq_abs _
    _ = (b - a) * B := abs_of_nonneg (mul_nonneg hab0 hB)
    _ = B * (b - a) := by ring

end Work.FTS.EpsEngine.PerzTools
