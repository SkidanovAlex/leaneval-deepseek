import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The level-6 `T2` slot: the assembly

`main_bound_core` assembles the three pieces — the Leibniz remainder (`leibR_bound`), the
exceptional term (`main_bound_E`) and the signed radial IBP at the top slot (`fluxSix`, passed in
as `hflux`) — into the bound for the `canonW q`-weighted pairing of
`D_z^bD_θ^a(f·D_z g)` with `D_z^bD_θ^a g`, for `0 ≤ q ≤ γ` and `a + b ≤ 6`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)

set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem main_bound_core {α q Cf Kf Kg Λ : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.HkMem α 6 f)
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (hgm7 : Work.Spaces.HkMem α 7 g) (hgd : Work.Spaces.DecayAll 6 g)
    (hpkg : SupPkg α f g Kf Kg) (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg)
    (hΛ1 : Kf ≤ Λ)
    (hΛ2 : Kg * Work.Spaces.HkNorm α 6 f ≤ Λ * Work.Spaces.HkNorm α 6 g)
    (hΛE1 : Real.sqrt (10 * excC11) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f ≤ Λ)
    (hΛE2 : Real.sqrt (10 * excC02) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f ≤ Λ)
    (hCf0 : 0 ≤ Cf)
    (hflux : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
      ≤ Cf * (Kf * Work.Spaces.HkSq α 6 g))
    (hq0 : 0 ≤ q) (hqγ : q ≤ Work.Spaces.gam α)
    (hqη : a = 0 → q ≤ Work.Spaces.eta) (hab : a + b ≤ 6) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
        * Work.Spaces.mixed b a g z θ|
      ≤ (max Cf 1 + 64 * ((a + 1) * (b + 1) : ℝ) + 1)
        * (Λ * Work.Spaces.HkSq α 6 g) := by
  have hΛ0 : 0 ≤ Λ := le_trans hKf0 hΛ1
  have hH0 : 0 ≤ Work.Spaces.HkSq α 6 g := Work.Spaces.HkSq_nonneg α 6 g
  -- ## the weight substitution `q ↦ q'` (`q' = η` when `q = 0`)
  set q' : ℝ := (if q = 0 then Work.Spaces.eta else q) with hq'def
  have hq'0 : 0 < q' := by
    rw [hq'def]; split_ifs with h
    · exact Work.Spaces.eta_pos
    · exact lt_of_le_of_ne hq0 (Ne.symm h)
  have hq'γ : q' ≤ Work.Spaces.gam α := by
    rw [hq'def]; split_ifs with h
    · have hgam1 : 1 ≤ Work.Spaces.gam α := by
        have := Work.Spaces.gam_sub_one α
        linarith [hα.le]
      linarith [Work.Spaces.eta_lt_one]
    · exact hqγ
  have hq'η : a = 0 → q' ≤ Work.Spaces.eta := by
    intro ha
    rw [hq'def]; split_ifs with h
    · exact le_rfl
    · exact hqη ha
  have hqq' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → canonW q z θ ≤ canonW q' z θ := by
    intro z θ hz hθ hθ2
    rw [hq'def]; split_ifs with h
    · rw [h]
      exact Work.FTS.StrongPersist.N6Trans.SixAux.canonW_zero_le_of_pos
        Work.Spaces.eta_pos hθ hθ2
    · exact le_rfl
  -- ## the Leibniz identity
  have hleib : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
        = f z θ * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ + leibR a b f g z θ := by
    intro z θ hz hθ hθ2
    have h00 : ((a.choose 0 : ℝ) * (b.choose 0 : ℝ))
        * (Work.Spaces.mixed 0 0 f z θ * Work.Spaces.mixed (b - 0 + 1) (a - 0) g z θ)
        = f z θ * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ := by
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
        Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right]
      rfl
    rw [Work.FTS.TransportS.mixed_mul_Dz_open b a f g hfs hgs z θ hz hθ hθ2]
    rw [sum_range_add_zero (fun a1 b1 => ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
      * (Work.Spaces.mixed b1 a1 f z θ * Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ)) a b,
      h00]
    rw [leibR]
    congr 1
    refine Finset.sum_congr rfl fun a1 _ => Finset.sum_congr rfl fun b1 _ => ?_
    by_cases h : a1 + b1 = 0
    · rw [if_pos h, if_pos h]; simp
    · rw [if_neg h, if_neg h]
  -- ## the Leibniz remainder
  obtain ⟨hRint, hRbound⟩ := leibR_bound (Kf := Kf) (Kg := Kg) (q := q') (Λ := Λ)
    hα hα1 hfs hfm hgs hgm hpkg hKf0 hKg0 hΛ1 hΛ2 hΛE1 hΛE2 hq'0 hq'γ hq'η hab
  have hRint' : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q' p.1 p.2
      * (|leibR a b f g p.1 p.2| * |Work.Spaces.mixed b a g p.1 p.2|)) pm := by
    simpa only [mul_assoc] using hRint
  have hRval : (∫ p, canonW q p.1 p.2
        * (|leibR a b f g p.1 p.2| * |Work.Spaces.mixed b a g p.1 p.2|) ∂pm)
      ≤ 64 * ((a + 1) * (b + 1) : ℝ) * (Λ * Work.Spaces.HkSq α 6 g) := by
    refine le_trans (integral_mono_canonW (q := q) (q' := q')
      (T := fun p : ℝ × ℝ => |leibR a b f g p.1 p.2| * |Work.Spaces.mixed b a g p.1 p.2|)
      hqq' (fun p => mul_nonneg (abs_nonneg _) (abs_nonneg _)) hRint') ?_
    simpa only [mul_assoc] using hRbound
  have hRsigned : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * leibR a b f g p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2) pm := by
    refine MeasureTheory.Integrable.mono' hRint' ?_ ?_
    · exact Work.Spaces.aesm_of_continuousOn_Qd _
        (((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
          (leibR_continuousOn hfs hgs)).mul ((hgs.mixed b a).continuousOn))
    · filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
        ‖canonW q p.1 p.2 * leibR a b f g p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2‖
          ≤ canonW q' p.1 p.2 * (|leibR a b f g p.1 p.2|
            * |Work.Spaces.mixed b a g p.1 p.2|))
        (fun z θ hz hθ hθ2 => by
          have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
          change ‖canonW q z θ * leibR a b f g z θ * Work.Spaces.mixed b a g z θ‖
            ≤ canonW q' z θ * (|leibR a b f g z θ| * |Work.Spaces.mixed b a g z θ|)
          have hc : 0 ≤ canonW q z θ := canonW_nonneg hθI
          have hnn : 0 ≤ |leibR a b f g z θ| * |Work.Spaces.mixed b a g z θ| :=
            mul_nonneg (abs_nonneg _) (abs_nonneg _)
          have hpt : canonW q z θ * |leibR a b f g z θ| * |Work.Spaces.mixed b a g z θ|
              ≤ canonW q' z θ * (|leibR a b f g z θ| * |Work.Spaces.mixed b a g z θ|) := by
            calc canonW q z θ * |leibR a b f g z θ| * |Work.Spaces.mixed b a g z θ|
                = canonW q z θ * (|leibR a b f g z θ| * |Work.Spaces.mixed b a g z θ|) := by ring
              _ ≤ canonW q' z θ * (|leibR a b f g z θ| * |Work.Spaces.mixed b a g z θ|) :=
                  mul_le_mul_of_nonneg_right (hqq' z θ hz hθ hθ2) hnn
          simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc] using hpt)] with p hp
      exact hp
  have hRabsval : |∫ p, canonW q p.1 p.2 * leibR a b f g p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2 ∂pm|
      ≤ 64 * ((a + 1) * (b + 1) : ℝ) * (Λ * Work.Spaces.HkSq α 6 g) := by
    refine le_trans (MeasureTheory.abs_integral_le_integral_abs (μ := pm)) ?_
    have h2 : (∫ p, |canonW q p.1 p.2 * leibR a b f g p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2| ∂pm)
        = ∫ p, canonW q p.1 p.2
          * (|leibR a b f g p.1 p.2| * |Work.Spaces.mixed b a g p.1 p.2|) ∂pm := by
      refine MeasureTheory.integral_congr_ae (Work.FTS.TransportS.ae_of_forall_Qd
        (P := fun p : ℝ × ℝ => |canonW q p.1 p.2 * leibR a b f g p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2|
          = canonW q p.1 p.2
            * (|leibR a b f g p.1 p.2| * |Work.Spaces.mixed b a g p.1 p.2|))
        (fun z θ hz hθ hθ2 => by
          change |canonW q z θ * leibR a b f g z θ * Work.Spaces.mixed b a g z θ|
            = canonW q z θ * (|leibR a b f g z θ| * |Work.Spaces.mixed b a g z θ|)
          have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
          have hc : 0 ≤ canonW q z θ := canonW_nonneg hθI
          simp only [abs_mul, abs_of_nonneg hc]
          ring))
    rw [h2]
    exact hRval
  -- ## the exceptional term
  obtain ⟨hEint, hEbound⟩ := main_bound_E (q := q) (Cf := Cf) (Kf := Kf)
    hα hα1 hfs hgs hgm hgm7 hgd
    (fun z θ hz hθ hθ2 => hpkg.fpure 0 (by norm_num) z θ hz hθ hθ2)
    hKf0 hCf0 hflux hq0 hqγ hqη hab
  -- ## integrability of the total integrand
  have htot : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) p.1 p.2
      * Work.Spaces.mixed b a g p.1 p.2) pm := by
    refine (hEint.add hRsigned).congr (Work.FTS.TransportS.ae_of_forall_Qd
      (P := fun p : ℝ × ℝ => canonW q p.1 p.2 * f p.1 p.2
            * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2
          + canonW q p.1 p.2 * leibR a b f g p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2
        = canonW q p.1 p.2
            * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2)
      (fun z θ hz hθ hθ2 => by rw [hleib z θ hz hθ hθ2]; ring))
  -- ## Fubini
  rw [(MeasureTheory.integral_integral (f := fun z θ => canonW q z θ
      * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
      * Work.Spaces.mixed b a g z θ) htot)]
  -- ## the split
  have hprod : (∫ p, canonW q p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2 ∂pm)
      = ∫ p, (canonW q p.1 p.2 * f p.1 p.2
            * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2
          + canonW q p.1 p.2 * leibR a b f g p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2) ∂pm := by
    refine MeasureTheory.integral_congr_ae (Work.FTS.TransportS.ae_of_forall_Qd
      (P := fun p : ℝ × ℝ => canonW q p.1 p.2
            * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2
        = canonW q p.1 p.2 * f p.1 p.2
            * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2
          + canonW q p.1 p.2 * leibR a b f g p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2)
      (fun z θ hz hθ hθ2 => by rw [hleib z θ hz hθ hθ2]; ring))
  rw [hprod]
  rw [MeasureTheory.integral_add hEint hRsigned]
  refine le_trans (abs_add_le _ _) ?_
  have hstep : max Cf 1 * (Kf * Work.Spaces.HkSq α 6 g)
        + 64 * ((a + 1) * (b + 1) : ℝ) * (Λ * Work.Spaces.HkSq α 6 g)
      ≤ (max Cf 1 + 64 * ((a + 1) * (b + 1) : ℝ) + 1)
        * (Λ * Work.Spaces.HkSq α 6 g) := by
    have hKfH : Kf * Work.Spaces.HkSq α 6 g ≤ Λ * Work.Spaces.HkSq α 6 g :=
      mul_le_mul_of_nonneg_right hΛ1 hH0
    have hmax0 : 0 ≤ max Cf 1 := le_trans (by norm_num) (le_max_right Cf 1)
    have hnn : 0 ≤ Λ * Work.Spaces.HkSq α 6 g := mul_nonneg hΛ0 hH0
    have h1 : max Cf 1 * (Kf * Work.Spaces.HkSq α 6 g)
        ≤ max Cf 1 * (Λ * Work.Spaces.HkSq α 6 g) :=
      mul_le_mul_of_nonneg_left hKfH hmax0
    calc max Cf 1 * (Kf * Work.Spaces.HkSq α 6 g)
          + 64 * ((a + 1) * (b + 1) : ℝ) * (Λ * Work.Spaces.HkSq α 6 g)
        ≤ max Cf 1 * (Λ * Work.Spaces.HkSq α 6 g)
          + 64 * ((a + 1) * (b + 1) : ℝ) * (Λ * Work.Spaces.HkSq α 6 g) := by
          linarith [h1]
      _ = (max Cf 1 + 64 * ((a + 1) * (b + 1) : ℝ)) * (Λ * Work.Spaces.HkSq α 6 g) := by
          ring
      _ ≤ (max Cf 1 + 64 * ((a + 1) * (b + 1) : ℝ) + 1)
            * (Λ * Work.Spaces.HkSq α 6 g) :=
          mul_le_mul_of_nonneg_right (by linarith) hnn
  exact le_trans (add_le_add hEbound hRabsval) hstep

end Work.FTS.StrongPersist.N6Trans.SixAux
