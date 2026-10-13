/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TransportS/T2Sup/delicateMargInt`: integrability of the delicate radial marginal

The target here is the **integrability** statement accompanying the delegated bound
`Work.FTS.TransportS.T2Sup.delicateBound`: for `0 < α ≤ 1`, `0 ≤ q ≤ γ = gam α`, a coefficient
`f` of the frozen class `T2SF α f` and a test function `g` of the frozen class `T2SG α g`, the
radial marginal

  `z ↦ ∫_θ w(z)² sin(2θ)^{-q} · |D_z³f(z,θ)| · |D_zD_θg(z,θ)| · |D_z³D_θg(z,θ)|`

is integrable on `Iz = [0,∞)`.

## Route

Write `A = D_z³f`, `B = D_zD_θg = mixed 1 1 g`, `C = D_z³D_θg = mixed 3 1 g`, and
`S(z) = sup_{θ∈(0,π/2)}|A(z,θ)|`, `mg(z) = ∫_θ HkIntegrand α 4 g z θ`.

1. `sin(2θ)^{-q} ≤ sin(2θ)^{-γ}` on the open angular interval (here `sin(2θ) > 0`).
2. `|A(z,θ)| ≤ S(z)` for `z > 0`, `θ` interior (`le_csSup` with the boundedness
   `supOpen_slice_bddAbove`), and `∫_z w²S² ≤ C/(γ-1)·HkSq α 4 f` together with its
   integrability is the *proved* `SlotT2.supThetaIntOpen` (`b = 3`).
3. `∫_θ sin(2θ)^{-γ}(B z θ)² ≤ Cang·HkSq α 4 g` **uniformly in `z > 0`**: this is
   `SupDzAux.sup_dz_ang_le` at `b = 1` (whose constant we call `Cang`) combined with the a.e.
   identity `B = sin(2θ)·∂_θ(D_z g)` (`SlotT2.supOpen_mixed_eq_sin_pth`).
4. `∫_θ w²sin(2θ)^{-γ}(C z θ)² ≤ mg(z)` from the summand bound `SlotT2.canonW_mul_mixed_le`
   (`(j,i) = (3,1)`).
5. Cauchy–Schwarz in `θ` on the pair `(sin(2θ)^{-γ/2}|B|, w sin(2θ)^{-γ/2}|C|)` and AM–GM in
   `z` give, for every `z > 0`,

   `∫_θ F z θ ≤ ½·√(Cang·cg)·(w(z)²S(z)² + mg(z))`,

   where `cg = HkSq α 4 g`.  The right-hand side is integrable in `z` (steps 2 and the marginal
   `mg` of `HkMem α 4 g`), and the marginal is a.e. strongly measurable by
   `AEStronglyMeasurable.integral_prod_right'`, so `Integrable.mono'` concludes.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.Defs
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_ang_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

open Work.FTS.TransportS
set_option autoImplicit false

/-! ## Elementary angular facts -/

/-- `sin(2θ) > 0` on the open angular interval. -/
theorem dmi_sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) ≥ 0` on the closed angular interval. -/
theorem dmi_sin_two_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The (nonnegative) target integrand. -/
theorem dmi_Fnonneg (α q : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
      * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
      * |Work.Spaces.mixed 3 1 g z θ| :=
  mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
    (Real.rpow_nonneg (dmi_sin_two_nonneg_of_mem hθ) _)) (abs_nonneg _))
    (abs_nonneg _)) (abs_nonneg _)

/-- Almost every angle of `Iθ` is interior. -/
theorem dmi_ae_mem_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- Almost every radius of `Iz` is strictly positive. -/
theorem dmi_ae_pos_Iz :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iz]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-! ## The angular weight algebra -/

/-- `x ^ 2` as a real power. -/
theorem dmi_natpow_two (x : ℝ) : x ^ (2 : ℕ) = x ^ (2 : ℝ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num]
  exact (Real.rpow_natCast x 2).symm

/-- `σ^{-γ/2}·σ^{-γ/2} = σ^{-γ}`. -/
theorem dmi_rpow_half_mul {γ σ : ℝ} (hσ : 0 < σ) :
    σ ^ (-(γ / 2)) * σ ^ (-(γ / 2)) = σ ^ (-γ) := by
  rw [← Real.rpow_add hσ]
  congr 1
  ring

/-- `(σ^{-γ/2})² = σ^{-γ}`. -/
theorem dmi_rpow_half_sq {γ σ : ℝ} (hσ : 0 < σ) : (σ ^ (-(γ / 2))) ^ 2 = σ ^ (-γ) := by
  rw [dmi_natpow_two (σ ^ (-(γ / 2)))]
  rw [← Real.rpow_mul (le_of_lt hσ)]
  congr 1
  ring

/-- `σ^{-γ}(σX)² = X²σ^{2-γ}` for `σ > 0`. -/
theorem dmi_mul_sq {γ σ X : ℝ} (hσ : 0 < σ) :
    σ ^ (-γ) * (σ * X) ^ 2 = X ^ 2 * σ ^ (2 - γ) := by
  have h1 : (σ * X) ^ 2 = σ ^ (2 : ℝ) * X ^ 2 := by
    rw [mul_pow, dmi_natpow_two σ]
  rw [h1]
  rw [show (2 - γ : ℝ) = (-γ) + 2 from by ring, Real.rpow_add hσ]
  ring

/-- For `σ ∈ (0,1]` and `0 ≤ q ≤ γ` the weights compare: `σ^{-q} ≤ σ^{-γ}`. -/
theorem dmi_rpow_le {q γ σ : ℝ} (hq0 : 0 ≤ q) (hqγ : q ≤ γ) (hσ0 : 0 < σ)
    (hσ1 : σ ≤ 1) : σ ^ (-q) ≤ σ ^ (-γ) := by
  have hγ : 0 ≤ γ := le_trans hq0 hqγ
  rcases eq_or_lt_of_le hq0 with h | h
  · rw [← h, neg_zero, Real.rpow_zero]
    have hstep : σ ^ (0 : ℝ) ≤ σ ^ (-γ) :=
      Real.rpow_le_rpow_of_exponent_ge hσ0 hσ1 (by linarith)
    rwa [Real.rpow_zero] at hstep
  · exact Work.FTS.TransportS.SlotT2.rpow_neg_mono (le_of_lt hσ0) hσ1 h hqγ

/-- The `L²`–`L²` Cauchy–Schwarz inequality in its square-root form for the angular interval. -/
theorem dmi_cs_Iθ {u v : ℝ → ℝ}
    (hu : MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hv : MeasureTheory.MemLp v 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hu0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ u θ) (hv0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ v θ) :
    (∫ θ in Work.Spaces.Iθ, u θ * v θ)
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, u θ ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, v θ ^ 2) := by
  have hsq := Work.Spaces.cs_integral hu hv
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hA : 0 ≤ ∫ θ in Work.Spaces.Iθ, u θ ^ 2 :=
    MeasureTheory.setIntegral_nonneg hIθ (fun θ _ => sq_nonneg _)
  have hL : 0 ≤ ∫ θ in Work.Spaces.Iθ, u θ * v θ :=
    MeasureTheory.setIntegral_nonneg hIθ (fun θ hθ => mul_nonneg (hu0 θ hθ) (hv0 θ hθ))
  calc (∫ θ in Work.Spaces.Iθ, u θ * v θ)
      = Real.sqrt ((∫ θ in Work.Spaces.Iθ, u θ * v θ) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hL]
    _ ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, u θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, v θ ^ 2)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, u θ ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, v θ ^ 2) := Real.sqrt_mul hA _

/-! ## Continuity of the auxiliary multipliers on the open quadrant -/

/-- `(z,θ) ↦ z^…`-free radial weight `w z` is continuous on the open quadrant. -/
theorem dmi_continuousOn_w :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  simp only [Work.Spaces.w]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

/-- `(z,θ) ↦ sin(2θ)^c` is continuous on the open quadrant. -/
theorem dmi_continuousOn_sin_pow (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  refine ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const ?_
  intro p hp
  exact Or.inl (ne_of_gt (dmi_sin_two_pos hp.2))

/-! ## The main statement -/

/-- **Integrability of the delicate radial marginal in the honest class.** -/
theorem delicateMargInt_hon :
    ∀ (α q : ℝ) (f g : ℝ → ℝ → ℝ),
      0 < α → α ≤ 1 → 0 ≤ q → q ≤ Work.Spaces.gam α →
      HonF α f → Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
              * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
              * |Work.Spaces.mixed 3 1 g z θ|)
        Work.Spaces.Iz := by
  intro α q f g hα hα1 hq0 hqγ hsf hSmoG hHk4g
  have hSmoF : Work.FTS.EllipticEst.SmoothOpen f := hsf.1
  have hHk4f : Work.Spaces.HkMem α 4 f := hsf.2.1
  have hgam_pos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hgam_nn : 0 ≤ Work.Spaces.gam α := le_of_lt hgam_pos
  change MeasureTheory.Integrable
    (fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
          * |Work.Spaces.mixed 3 1 g z θ|)
    (MeasureTheory.volume.restrict Work.Spaces.Iz)
  -- notation
  set S : ℝ → ℝ :=
    fun z => sSup {y : ℝ | ∃ θ ∈ Set.Ioo (0 : ℝ) (π / 2), y = |Work.Spaces.DzIter 3 f z θ|}
    with hS
  set mg : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ with hmg
  set cg : ℝ := Work.Spaces.HkSq α 4 g with hcg
  have hcgnn : 0 ≤ cg := by rw [hcg]; exact Work.Spaces.HkSq_nonneg α 4 g
  -- (1) the sup-bound of `supThetaIntOpen`
  obtain ⟨C0, _hC0pos, hC0⟩ := Work.FTS.TransportS.SlotT2.supThetaIntOpen
  obtain ⟨hSint_raw, hSle_raw⟩ := hC0 α f 3 hα hα1 (by norm_num) hSmoF hHk4f
  have hSint : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * S z ^ 2)
      Work.Spaces.Iz := by
    refine hSint_raw.congr ?_
    filter_upwards with z
    have hz : S z
        = sSup {y : ℝ | ∃ θ ∈ Set.Ioo (0 : ℝ) (π / 2), y = |Work.Spaces.DzIter 3 f z θ|} := by
      rw [hS]
    rw [hz]
    ring
  have hSle : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * S z ^ 2)
      ≤ C0 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f := by
    have h := hSle_raw
    rw [show (fun z => sSup {y : ℝ | ∃ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          y = |Work.Spaces.DzIter 3 f z θ|} ^ 2 * (Work.Spaces.w z) ^ 2)
        = fun z => (Work.Spaces.w z) ^ 2 * S z ^ 2 from by
      funext z; rw [hS]; ring] at h
    exact h
  have hSbd : ∀ z : ℝ, 0 < z → BddAbove
      {y : ℝ | ∃ θ ∈ Set.Ioo (0 : ℝ) (π / 2), y = |Work.Spaces.DzIter 3 f z θ|} :=
    fun z hz => Work.FTS.TransportS.SlotT2.supOpen_slice_bddAbove (α := α) (f := f) (b := 3)
      hSmoF hHk4f hα hα1 (by norm_num) hz
  have hAle : ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.mixed 3 0 f z θ| ≤ S z := by
    intro z hz θ hθ
    have h1 : |Work.Spaces.DzIter 3 f z θ|
        ≤ sSup {y : ℝ | ∃ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
            y = |Work.Spaces.DzIter 3 f z θ'|} := le_csSup (hSbd z hz) ⟨θ, hθ, rfl⟩
    have hz' : S z
        = sSup {y : ℝ | ∃ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
            y = |Work.Spaces.DzIter 3 f z θ'|} := by rw [hS]
    rw [Work.Spaces.mixed_zero_right, hz']
    exact h1
  -- (2) the uniform-in-`z` angular bound for the `(1,1)`-slot of `g`
  obtain ⟨Cang, hCangpos, hCang⟩ := Work.FTS.TransportS.SupDzAux.sup_dz_ang_le
  have hBbound : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn
          (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 g z θ) ^ 2) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 g z θ) ^ 2) ≤ Cang * cg := by
    intro z hz
    have hae : (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 1 1 g z θ) ^ 2)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => (Work.Spaces.pth (Work.Spaces.DzIter 1 g) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
      filter_upwards [dmi_ae_mem_Iθ] with θ hθ
      rw [Work.FTS.TransportS.SlotT2.supOpen_mixed_eq_sin_pth hSmoG 1 hz hθ]
      exact dmi_mul_sq (γ := Work.Spaces.gam α)
        (X := Work.Spaces.pth (Work.Spaces.DzIter 1 g) z θ) (dmi_sin_two_pos hθ)
    refine ⟨?_, ?_⟩
    · refine MeasureTheory.Integrable.mono' (hHk4g.1 z (le_of_lt hz)) ?_ ?_
      · refine Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 g p.1 p.2) ^ 2) ?_ hz
        have h1 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)))
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
          refine ((Real.continuous_sin.comp
            (continuous_const.mul continuous_snd)).continuousOn).rpow_const ?_
          intro p hp
          exact Or.inl (ne_of_gt (dmi_sin_two_pos hp.2))
        exact h1.mul ((hSmoG.mixed 1 1).continuousOn.pow 2)
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
        rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (dmi_sin_two_nonneg_of_mem hθ) _)
          (sq_nonneg _))]
        have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ (one_le_w hz)
        have hXn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 g z θ) ^ 2 :=
          mul_nonneg (Real.rpow_nonneg (dmi_sin_two_nonneg_of_mem hθ) _) (sq_nonneg _)
        have hstep : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 1 1 g z θ) ^ 2
            ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 1 1 g z θ) ^ 2 := by
          have h := mul_le_mul_of_nonneg_right hw2 hXn
          simpa [one_mul, mul_assoc] using h
        refine hstep.trans ?_
        exact Work.FTS.TransportS.SlotT2.canonW_mul_mixed_le α g hgam_pos le_rfl hz hθ 1 1
          (by norm_num) (by norm_num)
    · rw [MeasureTheory.integral_congr_ae hae]
      have h := hCang α g 1 hα hα1 hSmoG hHk4g (by norm_num) z hz
      rw [hcg]
      exact h
  -- (3) the angular bound for the `(3,1)`-slot of `g`, in terms of the marginals
  have hCbound : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 3 1 g z θ) ^ 2) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 3 1 g z θ) ^ 2) ≤ mg z := by
    intro z hz
    have hpt : ∀ θ ∈ Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 3 1 g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      fun θ hθ => Work.FTS.TransportS.SlotT2.canonW_mul_mixed_le α g hgam_pos le_rfl hz hθ 3 1
        (by norm_num) (by norm_num)
    have hnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 3 1 g z θ) ^ 2 := fun θ hθ =>
      mul_nonneg (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (dmi_sin_two_nonneg_of_mem hθ) _)) (sq_nonneg _)
    have hint : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 3 1 g z θ) ^ 2) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.mono' (hHk4g.1 z (le_of_lt hz)) ?_ ?_
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 3 1 g p.1 p.2) ^ 2)
          (((dmi_continuousOn_w.pow 2).mul
            (dmi_continuousOn_sin_pow (-(Work.Spaces.gam α)))).mul
            ((hSmoG.mixed 3 1).continuousOn.pow 2)) hz
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
        rw [Real.norm_of_nonneg (hnn θ hθ)]
        exact hpt θ hθ
    refine ⟨hint, ?_⟩
    have h := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hnn)
      (hHk4g.1 z (le_of_lt hz))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
    rw [hmg]
    exact h
  -- (4) the pointwise-in-`z` bound on the marginal
  have hmarg : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
          * |Work.Spaces.mixed 3 1 g z θ|)
        ≤ (1 / 2) * Real.sqrt (Cang * cg) * ((Work.Spaces.w z) ^ 2 * S z ^ 2 + mg z) := by
    intro z hz
    obtain ⟨hBint, hBle⟩ := hBbound z hz
    obtain ⟨hCint, hCle⟩ := hCbound z hz
    have hSnn : 0 ≤ S z := by
      refine le_trans (abs_nonneg _) (hAle z hz (π / 4) ?_)
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hwnn : 0 ≤ Work.Spaces.w z := le_of_lt (w_pos_of_pos hz)
    have hmgnn : 0 ≤ mg z :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
    -- the two `L²`-functions of the Cauchy–Schwarz step
    set u : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
      * |Work.Spaces.mixed 1 1 g z θ| with hu
    set v : ℝ → ℝ := fun θ => Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
      * |Work.Spaces.mixed 3 1 g z θ| with hv
    have hsinnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) :=
      fun θ hθ => Real.rpow_nonneg (dmi_sin_two_nonneg_of_mem hθ) _
    have hu0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ u θ := by
      intro θ hθ; rw [hu]; exact mul_nonneg (hsinnn θ hθ) (abs_nonneg _)
    have hv0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ v θ := by
      intro θ hθ; rw [hv]
      exact mul_nonneg (mul_nonneg hwnn (hsinnn θ hθ)) (abs_nonneg _)
    -- the a.e. shape of `u²` and `v²`
    have hu2ae : (fun θ => u θ ^ 2)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 g z θ) ^ 2) := by
      filter_upwards [dmi_ae_mem_Iθ] with θ hθ
      simp only [hu]
      rw [mul_pow, sq_abs, dmi_rpow_half_sq (dmi_sin_two_pos hθ)]
    have hu2 : (∫ θ in Work.Spaces.Iθ, u θ ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 g z θ) ^ 2 :=
      MeasureTheory.integral_congr_ae hu2ae
    have hv2ae : (fun θ => v θ ^ 2)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 3 1 g z θ) ^ 2) := by
      filter_upwards [dmi_ae_mem_Iθ] with θ hθ
      simp only [hv]
      rw [mul_pow, mul_pow, sq_abs, dmi_rpow_half_sq (dmi_sin_two_pos hθ)]
    have hv2 : (∫ θ in Work.Spaces.Iθ, v θ ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 3 1 g z θ) ^ 2 :=
      MeasureTheory.integral_congr_ae hv2ae
    -- the `L²`-memberships
    have hu_mem : MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine (MeasureTheory.memLp_two_iff_integrable_sq ?_).mpr ?_
      · rw [hu]
        exact Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))
            * |Work.Spaces.mixed 1 1 g p.1 p.2|)
          ((dmi_continuousOn_sin_pow (-(Work.Spaces.gam α / 2))).mul
            ((hSmoG.mixed 1 1).continuousOn.abs)) hz
      · exact hBint.congr hu2ae.symm
    have hv_mem : MeasureTheory.MemLp v 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine (MeasureTheory.memLp_two_iff_integrable_sq ?_).mpr ?_
      · rw [hv]
        exact Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))
            * |Work.Spaces.mixed 3 1 g p.1 p.2|)
          ((dmi_continuousOn_w.mul (dmi_continuousOn_sin_pow (-(Work.Spaces.gam α / 2)))).mul
            ((hSmoG.mixed 3 1).continuousOn.abs)) hz
      · exact hCint.congr hv2ae.symm
    -- the pointwise bound for interior angles
    have hptF : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
            * |Work.Spaces.mixed 3 1 g z θ|
          ≤ (Work.Spaces.w z * S z) * (u θ * v θ) := by
      intro θ hθ
      have hσ := dmi_sin_two_pos hθ
      have hq1 := dmi_rpow_le hq0 hqγ hσ (Real.sin_le_one _)
      have hhalf := dmi_rpow_half_mul (γ := Work.Spaces.gam α) hσ
      have hA := hAle z hz θ hθ
      have h1 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
            * |Work.Spaces.mixed 3 1 g z θ|
          ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * S z * |Work.Spaces.mixed 1 1 g z θ| * |Work.Spaces.mixed 3 1 g z θ| := by
        have h2 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_left hq1 (sq_nonneg _)
        have h3 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
              * |Work.Spaces.mixed 3 0 f z θ|
            ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * S z := by
          have := mul_le_mul h2 hA (abs_nonneg _)
            (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hσ) _))
          simpa [mul_assoc] using this
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (abs_nonneg _))
          (abs_nonneg _)
      have h2 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * S z * |Work.Spaces.mixed 1 1 g z θ| * |Work.Spaces.mixed 3 1 g z θ|
          = (Work.Spaces.w z * S z) * (u θ * v θ) := by
        simp only [hu, hv]
        rw [← hhalf]
        ring
      rw [h2] at h1
      exact h1
    have hptae : (fun θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
          * |Work.Spaces.mixed 3 1 g z θ|)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => (Work.Spaces.w z * S z) * (u θ * v θ)) := by
      filter_upwards [dmi_ae_mem_Iθ] with θ hθ
      exact hptF θ hθ
    have hFnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
        * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
        * |Work.Spaces.mixed 3 1 g z θ| := fun θ hθ => dmi_Fnonneg α q f g z θ hθ
    -- the Cauchy–Schwarz step in `θ`
    have hCS := dmi_cs_Iθ hu_mem hv_mem hu0 hv0
    have huv_int : MeasureTheory.IntegrableOn (fun θ => u θ * v θ) Work.Spaces.Iθ :=
      MeasureTheory.memLp_one_iff_integrable.mp (hu_mem.mul hv_mem)
    have hwS : 0 ≤ Work.Spaces.w z * S z := mul_nonneg hwnn hSnn
    have hsqrt_nn : 0 ≤ Real.sqrt (Cang * cg) := Real.sqrt_nonneg _
    have hFaesm : MeasureTheory.AEStronglyMeasurable
        (fun θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
          * |Work.Spaces.mixed 3 1 g z θ|) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f p.1 p.2| * |Work.Spaces.mixed 1 1 g p.1 p.2|
          * |Work.Spaces.mixed 3 1 g p.1 p.2|)
        ((((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
          ((hSmoF.mixed 3 0).continuousOn.abs)).mul
          ((hSmoG.mixed 1 1).continuousOn.abs)).mul
          ((hSmoG.mixed 3 1).continuousOn.abs)) hz
    have hstep1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
          * |Work.Spaces.mixed 3 1 g z θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z * S z) * (u θ * v θ) :=
      MeasureTheory.integral_mono_of_nonneg
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hFnn)
        (huv_int.const_mul (Work.Spaces.w z * S z)) hptae
    have hstep2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z * S z) * (u θ * v θ))
        = (Work.Spaces.w z * S z) * (∫ θ in Work.Spaces.Iθ, u θ * v θ) :=
      MeasureTheory.integral_const_mul _ _
    have hCS' : (∫ θ in Work.Spaces.Iθ, u θ * v θ)
        ≤ Real.sqrt (Cang * cg) * Real.sqrt (mg z) := by
      refine hCS.trans ?_
      refine mul_le_mul (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      · rw [hu2]; exact hBle
      · rw [hv2]; exact hCle
    have hstep3 : (Work.Spaces.w z * S z) * (Real.sqrt (Cang * cg) * Real.sqrt (mg z))
        ≤ (1 / 2) * Real.sqrt (Cang * cg) * ((Work.Spaces.w z) ^ 2 * S z ^ 2 + mg z) := by
      have hkey : 2 * (Work.Spaces.w z * S z) * Real.sqrt (mg z)
          ≤ (Work.Spaces.w z * S z) ^ 2 + mg z := by
        have h := two_mul_le_add_sq (Real.sqrt ((Work.Spaces.w z * S z) ^ 2)) (Real.sqrt (mg z))
        rw [Real.sq_sqrt (sq_nonneg _), Real.sq_sqrt hmgnn, Real.sqrt_sq_eq_abs,
          abs_of_nonneg hwS] at h
        exact h
      calc (Work.Spaces.w z * S z) * (Real.sqrt (Cang * cg) * Real.sqrt (mg z))
          = Real.sqrt (Cang * cg) * ((Work.Spaces.w z * S z) * Real.sqrt (mg z)) := by ring
        _ ≤ Real.sqrt (Cang * cg)
            * ((1 / 2) * ((Work.Spaces.w z * S z) ^ 2 + mg z)) := by
            refine mul_le_mul_of_nonneg_left ?_ hsqrt_nn
            linarith [hkey]
        _ = (1 / 2) * Real.sqrt (Cang * cg) * ((Work.Spaces.w z) ^ 2 * S z ^ 2 + mg z) := by
            ring
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
          * |Work.Spaces.mixed 3 1 g z θ|)
        ≤ (Work.Spaces.w z * S z) * (∫ θ in Work.Spaces.Iθ, u θ * v θ) := by
          rw [← hstep2]
          exact hstep1
      _ ≤ (Work.Spaces.w z * S z) * (Real.sqrt (Cang * cg) * Real.sqrt (mg z)) :=
          mul_le_mul_of_nonneg_left hCS' hwS
      _ ≤ (1 / 2) * Real.sqrt (Cang * cg) * ((Work.Spaces.w z) ^ 2 * S z ^ 2 + mg z) := hstep3
  -- (5) integrability of the majorant and measurability of the marginal
  have hMint : MeasureTheory.Integrable
      (fun z => (1 / 2) * Real.sqrt (Cang * cg) * ((Work.Spaces.w z) ^ 2 * S z ^ 2 + mg z))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hmgint : MeasureTheory.IntegrableOn mg Work.Spaces.Iz := by
      rw [hmg]
      exact hHk4g.2
    exact ((hSint.add hmgint).const_mul ((1 / 2) * Real.sqrt (Cang * cg)))
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
          * |Work.Spaces.mixed 3 1 g z θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-q) * |Work.Spaces.mixed 3 0 f p.1 p.2|
        * |Work.Spaces.mixed 1 1 g p.1 p.2| * |Work.Spaces.mixed 3 1 g p.1 p.2|)
        ((((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
          ((hSmoF.mixed 3 0).continuousOn.abs)).mul
          ((hSmoG.mixed 1 1).continuousOn.abs)).mul
          ((hSmoG.mixed 3 1).continuousOn.abs)))
  refine MeasureTheory.Integrable.mono' hMint haesm ?_
  filter_upwards [dmi_ae_pos_Iz] with z hz
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
      * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
      * |Work.Spaces.mixed 3 1 g z θ| :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => dmi_Fnonneg α q f g z θ hθ)
  rw [Real.norm_of_nonneg hnn]
  exact hmarg z hz

end Work.FTS.StrongPersist.N6Trans.Hon
