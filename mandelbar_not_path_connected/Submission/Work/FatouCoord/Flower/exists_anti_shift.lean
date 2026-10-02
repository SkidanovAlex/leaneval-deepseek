import Mathlib
import Submission.Work.FatouCoord.Flower.PsiData
import Submission.Work.FatouCoord.Petal.repelling_defs
import Submission.Work.FatouCoord.Repelling.defect_lipschitz
import Submission.Work.FatouCoord.Repelling.norm_Lambda_sub_le
import Submission.Work.FatouCoord.Flower.gU_tangent_sq
import Submission.Work.FatouCoord.Flower.periodic_bounded_const
import Submission.Work.FatouCoord.Flower.star_Lambda_sub_le
import Submission.Work.FatouCoord.Flower.norm_Lambda_sub_close
import Submission.Work.FatouCoord.Flower.Z_bounded
import Submission.Work.ELRig.deriv_ne_zero_of_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped Topology
open Set Filter Metric Function

namespace Work.FatouCoord.Flower

open Work.FatouCoord

noncomputable section

/-! ## Basic algebra of the `gW` conjugation -/

/-- `-1 / (-1 / w) = w`. -/
theorem neg_one_div_neg_one_div (w : ℂ) : -1 / (-1 / w) = w := by
  field_simp

/-- The `w`-chart version of an antiholomorphic square root: `gW W = -1 / gU (-1 / W)`. -/
def gWfun (gU : ℂ → ℂ) (W : ℂ) : ℂ := -1 / gU (-1 / W)

theorem gWfun_apply (gU : ℂ → ℂ) (W : ℂ) : gWfun gU W = -1 / gU (-1 / W) := rfl

/-- `star ∘ gU`, the holomorphic conjugate of the antiholomorphic root. -/
def gUc (gU : ℂ → ℂ) (u : ℂ) : ℂ := star (gU u)

theorem gUc_apply (gU : ℂ → ℂ) (u : ℂ) : gUc gU u = star (gU u) := rfl

theorem star_gUc (gU : ℂ → ℂ) (u : ℂ) : star (gUc gU u) = gU u := by
  simp [gUc]

theorem neg_one_div_gWfun (gU : ℂ → ℂ) (W : ℂ) : -1 / gWfun gU W = gU (-1 / W) := by
  rw [gWfun_apply, neg_one_div_neg_one_div]

theorem star_gWfun (gU : ℂ → ℂ) (W : ℂ) : star (gWfun gU W) = -1 / gUc gU (-1 / W) := by
  rw [gWfun_apply, gUc_apply]
  simp

/-- The antiholomorphic square root commutes with its square. -/
theorem gU_comp_self_sq {f gU : ℂ → ℂ} (hgg : gU ∘ gU = f) (z : ℂ) :
    gU (f z) = f (gU z) := by
  have h1 : gU (gU (gU z)) = f (gU z) := congrFun hgg (gU z)
  have h2 : gU (gU (gU z)) = gU (f z) := by
    rw [show gU (gU z) = f z from congrFun hgg z]
  rw [← h2, h1]

/-- `gW` commutes with the chart dynamics `wMap f`. -/
theorem gWfun_wMap {f gU : ℂ → ℂ} (hgg : gU ∘ gU = f) (W : ℂ) :
    gWfun gU (wMap f W) = wMap f (gWfun gU W) := by
  rw [gWfun_apply, wMap_apply, gWfun_apply, wMap_apply]
  rw [neg_one_div_neg_one_div, neg_one_div_neg_one_div]
  rw [gU_comp_self_sq hgg (-1 / W)]

/-- `gW ∘ gW = wMap f`. -/
theorem gWfun_gWfun {f gU : ℂ → ℂ} (hgg : gU ∘ gU = f) (W : ℂ) :
    gWfun gU (gWfun gU W) = wMap f W := by
  rw [gWfun_apply, gWfun_apply, wMap_apply]
  rw [neg_one_div_neg_one_div]
  rw [show gU (gU (-1 / W)) = f (-1 / W) from congrFun hgg (-1 / W)]

/-- The bound on `gW` derived from the second-order tangency of `gU`. -/
theorem gWfun_close {f gU h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A')
    (hgU_anti : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (gU z)) z)
    (hgg : gU ∘ gU = f) (hgU0 : gU 0 = 0) :
    ∃ C ρ : ℝ, 0 < ρ ∧ ∀ W : ℂ, ρ ≤ ‖W‖ → ‖gWfun gU W - star W‖ ≤ C := by
  obtain ⟨C₀, ρ₀, hρ₀, hC₀⟩ := gU_tangent_sq hb hgU_anti hgg hgU0
  set C₁ : ℝ := max C₀ 1 with hC₁
  have hC₁pos : 0 < C₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set ρ : ℝ := max (1 / ρ₀ + 1) (2 * C₁ + 1) with hρ
  refine ⟨2 * C₁, ρ, ?_, ?_⟩
  · have h1 : 0 < 1 / ρ₀ + 1 := by positivity
    rw [hρ]; exact lt_of_lt_of_le h1 (le_max_left _ _)
  · intro W hW
    rw [hρ] at hW
    have hρ₁ : 1 / ρ₀ + 1 ≤ max (1 / ρ₀ + 1) (2 * C₁ + 1) := le_max_left _ _
    have hρ₂ : 2 * C₁ + 1 ≤ max (1 / ρ₀ + 1) (2 * C₁ + 1) := le_max_right _ _
    have hWbig : 1 / ρ₀ < ‖W‖ := lt_of_lt_of_le (by linarith) (le_trans hρ₁ hW)
    have hWbig2 : 2 * C₁ < ‖W‖ := lt_of_lt_of_le (by linarith) (le_trans hρ₂ hW)
    have hWpos : 0 < ‖W‖ := lt_of_lt_of_le (by linarith [hC₁pos]) hW
    set u : ℂ := -1 / W with hu
    have hunorm : ‖u‖ = 1 / ‖W‖ := by simp [hu, norm_div, norm_neg]
    have hunorm_pos : 0 < ‖u‖ := by rw [hunorm]; positivity
    have hu_lt : ‖u‖ < ρ₀ := by
      rw [hunorm, div_lt_iff₀ hWpos]
      rw [div_lt_iff₀ hρ₀] at hWbig
      linarith [hWbig]
    have hCu : ‖gU u - star u‖ ≤ C₁ * ‖u‖ ^ 2 :=
      le_trans (hC₀ u hu_lt) (mul_le_mul_of_nonneg_right (le_max_left C₀ 1) (sq_nonneg _))
    have hu_small : C₁ * ‖u‖ ≤ 1 / 2 := by
      rw [hunorm, mul_one_div, div_le_iff₀ hWpos]
      nlinarith [hWbig2, hC₁pos]
    have he_le : ‖gU u - star u‖ ≤ (1 / 2) * ‖u‖ := by
      calc ‖gU u - star u‖ ≤ C₁ * ‖u‖ ^ 2 := hCu
        _ = (C₁ * ‖u‖) * ‖u‖ := by ring
        _ ≤ (1 / 2) * ‖u‖ := by nlinarith [hu_small, norm_nonneg u]
    have hgU_lower : ‖u‖ / 2 ≤ ‖gU u‖ := by
      have h1 : ‖star u‖ ≤ ‖gU u‖ + ‖gU u - star u‖ := by
        calc ‖star u‖ = ‖gU u - (gU u - star u)‖ := by ring_nf
          _ ≤ ‖gU u‖ + ‖gU u - star u‖ := norm_sub_le _ _
      rw [norm_star] at h1
      linarith
    have hstaru : star u = -1 / star W := by simp [hu]
    have hgu0 : gU u ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hgU_lower
      linarith [hunorm_pos]
    have hsu0 : star u ≠ 0 := by
      intro h0
      have h1 : ‖star u‖ = 0 := by rw [h0, norm_zero]
      rw [norm_star] at h1
      exact hunorm_pos.ne' h1
    have hkey : gWfun gU W - star W = (gU u - star u) / (gU u * star u) := by
      have hgu : gU (-1 / W) = gU u := by rw [hu]
      have hsw : star W = -1 / star u := by
        rw [hstaru]; exact (neg_one_div_neg_one_div (star W)).symm
      rw [gWfun_apply, hgu, hsw]
      field_simp
      ring
    rw [hkey, norm_div, norm_mul]
    have hgUpos : 0 < ‖gU u‖ := by linarith [hunorm_pos]
    have hstarupos : 0 < ‖star u‖ := by rw [norm_star]; exact hunorm_pos
    rw [div_le_iff₀ (by positivity)]
    calc ‖gU u - star u‖ ≤ C₁ * ‖u‖ ^ 2 := hCu
      _ = (2 * C₁) * (‖u‖ / 2 * ‖u‖) := by ring
      _ ≤ (2 * C₁) * (‖gU u‖ * ‖star u‖) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith [hC₁pos])
          rw [norm_star]
          exact mul_le_mul hgU_lower le_rfl hunorm_pos.le (by linarith [hunorm_pos])

/-- `f^[n]` transports through an antiholomorphic square root. -/
theorem gU_iterate {f gU : ℂ → ℂ} (hgg : gU ∘ gU = f) (n : ℕ) (z : ℂ) :
    gU (f^[n] z) = f^[n] (gU z) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (f z), gU_comp_self_sq hgg z]

/-- `Ψ` iterates along the unit shift. -/
theorem Psi_add_nat {f Ψ : ℂ → ℂ} (hΨshift : ∀ w : ℂ, Ψ (w + 1) = f (Ψ w)) (n : ℕ) (w : ℂ) :
    Ψ (w + (n : ℂ)) = f^[n] (Ψ w) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, ← add_assoc, hΨshift, ih, Function.iterate_succ_apply']

/-- `Ψ` is injective on the far left half-plane. -/
theorem Psi_injOn {V Ψ : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hVbd : ∀ w : ℂ, w.re < -R → ‖V w - w‖ ≤ (1 / 2) * ‖w‖)
    (hVinj : Set.InjOn V {w : ℂ | w.re < -R})
    (hΨV : ∀ w : ℂ, w.re < -R → Ψ w = -1 / V w) :
    Set.InjOn Ψ {w : ℂ | w.re < -R} := by
  intro x hx y hy hxy
  have hxnorm : 0 < ‖x‖ := by
    have h1 : R < ‖x‖ := by
      have h2 : R < -x.re := by simp only [Set.mem_ofPred_eq] at hx; linarith
      calc R < -x.re := h2
        _ ≤ ‖x‖ := by
            have := Complex.abs_re_le_norm x
            rw [abs_of_neg (by simp only [Set.mem_ofPred_eq] at hx; linarith)] at this
            linarith
    linarith
  have hynorm : 0 < ‖y‖ := by
    have h1 : R < ‖y‖ := by
      have h2 : R < -y.re := by simp only [Set.mem_ofPred_eq] at hy; linarith
      calc R < -y.re := h2
        _ ≤ ‖y‖ := by
            have := Complex.abs_re_le_norm y
            rw [abs_of_neg (by simp only [Set.mem_ofPred_eq] at hy; linarith)] at this
            linarith
    linarith
  have hVxne : V x ≠ 0 := by
    intro h0
    have h := hVbd x hx
    rw [h0, zero_sub, norm_neg] at h
    linarith [hxnorm, h]
  have hVyne : V y ≠ 0 := by
    intro h0
    have h := hVbd y hy
    rw [h0, zero_sub, norm_neg] at h
    linarith [hynorm, h]
  have hkey : -1 / V x = -1 / V y := by
    rw [← hΨV x hx, ← hΨV y hy]; exact hxy
  have hVeq : V x = V y := by
    have := congrArg (fun z => -1 / z) hkey
    rwa [neg_one_div_neg_one_div, neg_one_div_neg_one_div] at this
  exact hVinj hx hy hVeq

/-- A quantitative smallness consequence of `t ≥ max (256 A²) (16 π A)`. -/
theorem tau_bound {A t : ℝ} (hA : 0 ≤ A) (ht : max (256 * A ^ 2) (16 * Real.pi * A) ≤ t) :
    A * (2 * Real.sqrt t + 2 * Real.pi) ≤ t / 4 := by
  have ht0 : 0 ≤ t := le_trans (le_trans (by positivity) (le_max_left _ _)) ht
  have h1 : 256 * A ^ 2 ≤ t := le_trans (le_max_left _ _) ht
  have h2 : 16 * Real.pi * A ≤ t := le_trans (le_max_right _ _) ht
  have hs : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht0
  have hsnn : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hA16 : 16 * A ≤ Real.sqrt t := by nlinarith [hs, h1, hsnn, hA]
  have h2A : 2 * A * Real.sqrt t ≤ t / 8 := by nlinarith [hs, hA16, hsnn, hA]
  have h2π : 2 * Real.pi * A ≤ t / 8 := by nlinarith [h2, hA]
  have : A * (2 * Real.sqrt t + 2 * Real.pi) = 2 * A * Real.sqrt t + 2 * Real.pi * A := by ring
  rw [this]; linarith

/-! ## The main theorem -/

theorem exists_anti_shift {f gU h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A')
    (hgU_anti : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (gU z)) z)
    (hgg : gU ∘ gU = f) (hgU0 : gU 0 = 0) (ha : star a = a)
    {R : ℝ} (V : ℂ → ℂ) (hRr : 1 / r < R)
    (hVdiff : DifferentiableOn ℂ V {w : ℂ | w.re < -R})
    (hVshift : ∀ w : ℂ, w.re < -R → V (w+1) = Work.FatouCoord.wMap f (V w))
    (hVbd : ∀ w : ℂ, w.re < -R → ‖V w - w‖ ≤ (1/2) * ‖w‖)
    (hVref : ∀ w : ℂ, w.re < -R → ‖V w - w‖ ≤ ‖1 - a‖ * (2 * Real.sqrt ‖w‖ + 2 * Real.pi) + 1/2)
    (hVinj : Set.InjOn V {w : ℂ | w.re < -R})
    (hVinv : ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ Y : ℂ, R₁ ≤ ‖Y‖ →
      (Y - (1 - a) * Work.FatouCoord.Petal.Lambda Y).re < -R₁ →
        ∃ x : ℂ, x.re < -R ∧ V x = Y ∧
          ‖x - (Y - (1 - a) * Work.FatouCoord.Petal.Lambda Y)‖ ≤ 4)
    {Ψ : ℂ → ℂ} (hΨdiff : Differentiable ℂ Ψ) (hΨshift : ∀ w : ℂ, Ψ (w+1) = f (Ψ w))
    (hΨV : ∀ w : ℂ, w.re < -R → Ψ w = -1 / V w) :
    ∃ c : ℂ, star c = -c ∧ ∀ w : ℂ, Ψ ((star w + 1/2) + c) = gU (Ψ (w + c)) := by
  -- ### Step 0: the bound on the correction `Z`
  obtain ⟨Cz, Rz, hRz_pos, hZb'⟩ := Z_bounded hb hRr V hVdiff hVshift hVbd hVref hVinj hVinv
  obtain ⟨R₁, hR₁pos, hVinv'⟩ := hVinv
  obtain ⟨Cg, ρg, hρg_pos, hgWb⟩ := gWfun_close hb hgU_anti hgg hgU0
  set Cz' : ℝ := max Cz 0 with hCz'
  set Cg' : ℝ := max Cg 0 with hCg'
  have hCz'nn : 0 ≤ Cz' := le_max_right _ _
  have hCg'nn : 0 ≤ Cg' := le_max_right _ _
  have hZb'' : ∀ x : ℂ, x.re < -Rz → ‖V x - x - (1 - a) * Petal.Lambda x‖ ≤ Cz' :=
    fun x hx => le_trans (hZb' x hx) (le_max_left _ _)
  have hgWb' : ∀ W : ℂ, ρg ≤ ‖W‖ → ‖gWfun gU W - star W‖ ≤ Cg' :=
    fun W hW => le_trans (hgWb W hW) (le_max_left _ _)
  set A1 : ℝ := ‖1 - a‖ with hA1
  have hA1nn : 0 ≤ A1 := norm_nonneg _
  have hA1sq : (0 : ℝ) ≤ 256 * A1 ^ 2 := by positivity
  have hA1pi : (0 : ℝ) ≤ 16 * Real.pi * A1 := by positivity
  set CE : ℝ := Cz' + Cg' + 4 * Real.pi * A1 with hCE
  have hCEnn : 0 ≤ CE := by rw [hCE]; positivity
  set CΛ : ℝ := 1 + 2 * Real.pi with hCΛ
  set Cs : ℝ := CE + A1 * CΛ with hCs
  have hCsnn : 0 ≤ Cs := by rw [hCs]; positivity
  set CΘ : ℝ := Cs + 4 with hCΘ
  have hCΘnn : 0 ≤ CΘ := by rw [hCΘ]; linarith
  have hRpos : 0 < R := lt_trans (div_pos one_pos hb.hr) hRr
  set Rd : ℝ := Rz + 2 * ρg + 4 * CE + 2 * R₁ + (R₁ + Cs + 1) + 2 + 256 * A1 ^ 2
      + 16 * Real.pi * A1 + (R + 3 + CΘ) + 1 with hRd
  have hRz_le : Rz ≤ Rd := by rw [hRd]; linarith [hρg_pos, hCEnn, hR₁pos, hCsnn, hA1nn, hCΘnn, hRpos]
  have hρg_le : 2 * ρg ≤ Rd := by rw [hRd]; linarith [hRz_pos, hCEnn, hR₁pos, hCsnn, hA1nn, hCΘnn, hRpos]
  have hCE_le : 4 * CE ≤ Rd := by rw [hRd]; linarith [hRz_pos, hρg_pos, hR₁pos, hCsnn, hA1nn, hCΘnn, hRpos]
  have hR1_le : 2 * R₁ ≤ Rd := by rw [hRd]; linarith [hRz_pos, hρg_pos, hCEnn, hCsnn, hA1nn, hCΘnn, hRpos]
  have hR1Cs_le : R₁ + Cs + 1 ≤ Rd := by rw [hRd]; linarith [hRz_pos, hρg_pos, hCEnn, hR₁pos, hA1nn, hCΘnn, hRpos]
  have h2_le : 2 ≤ Rd := by rw [hRd]; linarith [hRz_pos, hρg_pos, hCEnn, hR₁pos, hCsnn, hA1nn, hCΘnn, hRpos]
  have hsq_le : 256 * A1 ^ 2 ≤ Rd := by rw [hRd]; linarith [hRz_pos, hρg_pos, hCEnn, hR₁pos, hCsnn, hA1nn, hCΘnn, hRpos]
  have hpi_le : 16 * Real.pi * A1 ≤ Rd := by rw [hRd]; linarith [hRz_pos, hρg_pos, hCEnn, hR₁pos, hCsnn, hA1nn, hCΘnn, hRpos]
  have hRCΘ_le : R + 3 + CΘ ≤ Rd := by rw [hRd]; linarith [hRz_pos, hρg_pos, hCEnn, hR₁pos, hCsnn, hA1nn, hCΘnn]
  have hRdpos : 0 < Rd := lt_of_lt_of_le (by norm_num) h2_le
  have hR_le_Rd : R ≤ Rd := by linarith [hRCΘ_le, hCΘnn]
  have hxR : ∀ x : ℂ, x.re < -Rd → x.re < -R := fun x hx => lt_of_lt_of_le hx (by linarith)
  -- ### Step 1: the construction of `Θ` on a far left half-plane
  have hex : ∀ x : ℂ, x.re < -Rd → ∃ y : ℂ,
      V y = gWfun gU (V x) ∧ y.re < -R ∧ ‖y - star x‖ ≤ CΘ := by
    intro x hx
    have hnormx_gt : Rd < ‖x‖ := by
      have h2 : -x.re ≤ ‖x‖ := by
        have h3 := Complex.abs_re_le_norm x
        rw [abs_of_neg (by linarith)] at h3
        linarith
      linarith
    have hnormx_pos : 0 < ‖x‖ := lt_trans hRdpos hnormx_gt
    have hnormx_ge1 : 1 ≤ ‖x‖ := by linarith [h2_le]
    have htau : A1 * (2 * Real.sqrt ‖x‖ + 2 * Real.pi) ≤ ‖x‖ / 4 :=
      tau_bound hA1nn (max_le (le_trans hsq_le hnormx_gt.le) (le_trans hpi_le hnormx_gt.le))
    have hVx_bd : ‖V x - x‖ ≤ A1 * (2 * Real.sqrt ‖x‖ + 2 * Real.pi) + 1 / 2 :=
      hVref x (hxR x hx)
    have hVx_bd2 : ‖V x - x‖ ≤ ‖x‖ / 2 := by
      have h1 : (1 : ℝ) / 2 ≤ ‖x‖ / 4 := by linarith [hnormx_ge1]
      linarith
    have hVx_low : ‖x‖ / 2 ≤ ‖V x‖ := by
      have h1 : ‖x‖ ≤ ‖V x‖ + ‖V x - x‖ := by
        calc ‖x‖ = ‖V x - (V x - x)‖ := by ring_nf
          _ ≤ ‖V x‖ + ‖V x - x‖ := norm_sub_le _ _
      linarith
    have hVxg : ρg ≤ ‖V x‖ := by linarith [hρg_le, hnormx_gt, hVx_low]
    have hYc : ‖gWfun gU (V x) - star (V x)‖ ≤ Cg' := hgWb' (V x) hVxg
    have hZxb : ‖V x - x - (1 - a) * Petal.Lambda x‖ ≤ Cz' := hZb'' x (by linarith [hRz_le])
    set Zx : ℂ := V x - x - (1 - a) * Petal.Lambda x with hZxdef
    set θ : ℂ := star (Petal.Lambda x) - Petal.Lambda (star x) with hθdef
    have hθb : ‖θ‖ ≤ 4 * Real.pi := star_Lambda_sub_le x
    set E : ℂ := star Zx + (1 - a) * θ + (gWfun gU (V x) - star (V x)) with hEdef
    have hEb : ‖E‖ ≤ CE := by
      rw [hEdef, hCE]
      have h2 : ‖(1 - a) * θ‖ = A1 * ‖θ‖ := by rw [norm_mul, hA1]
      calc ‖star Zx + (1 - a) * θ + (gWfun gU (V x) - star (V x))‖
          ≤ ‖star Zx + (1 - a) * θ‖ + ‖gWfun gU (V x) - star (V x)‖ := norm_add_le _ _
        _ ≤ (‖star Zx‖ + ‖(1 - a) * θ‖) + ‖gWfun gU (V x) - star (V x)‖ := by
            gcongr; exact norm_add_le _ _
        _ = ‖Zx‖ + A1 * ‖θ‖ + ‖gWfun gU (V x) - star (V x)‖ := by rw [norm_star, h2]
        _ ≤ Cz' + A1 * (4 * Real.pi) + Cg' := by
            have h1 : A1 * ‖θ‖ ≤ A1 * (4 * Real.pi) := mul_le_mul_of_nonneg_left hθb hA1nn
            linarith [hZxb, h1, hYc]
        _ = Cz' + Cg' + 4 * Real.pi * A1 := by ring
    have hYdecomp : gWfun gU (V x) = star x + (1 - a) * Petal.Lambda (star x) + E := by
      have hstar2 : star (1 - a) = 1 - a := by rw [star_sub, star_one, ha]
      have hstarΛ : star (Petal.Lambda x) = Petal.Lambda (star x) + θ := by rw [hθdef]; ring
      have h1 : star (V x) = star x + (1 - a) * Petal.Lambda (star x) + star Zx + (1 - a) * θ := by
        calc star (V x) = star (x + (1 - a) * Petal.Lambda x + Zx) := by rw [hZxdef]; ring_nf
          _ = star x + star ((1 - a) * Petal.Lambda x) + star Zx := by rw [star_add, star_add]
          _ = star x + star (Petal.Lambda x) * (1 - a) + star Zx := by rw [star_mul, hstar2]
          _ = star x + (Petal.Lambda (star x) + θ) * (1 - a) + star Zx := by rw [hstarΛ]
          _ = star x + (1 - a) * Petal.Lambda (star x) + star Zx + (1 - a) * θ := by ring
      rw [hEdef, h1]; ring
    have hΛstarb : ‖Petal.Lambda (star x)‖ ≤ 2 * Real.sqrt ‖x‖ + 2 * Real.pi := by
      have h := Work.FatouCoord.Repelling.norm_Lambda_le (star x) (by rwa [norm_star])
      rwa [norm_star] at h
    have key : A1 * (2 * Real.sqrt ‖x‖ + 2 * Real.pi) + CE ≤ ‖x‖ / 2 := by
      have h4 : CE ≤ ‖x‖ / 4 := by linarith [hCE_le, hnormx_gt]
      linarith [htau]
    have hAux : ‖(1 - a) * Petal.Lambda (star x) + E‖
        ≤ A1 * (2 * Real.sqrt ‖x‖ + 2 * Real.pi) + CE := by
      calc ‖(1 - a) * Petal.Lambda (star x) + E‖
          ≤ ‖(1 - a) * Petal.Lambda (star x)‖ + ‖E‖ := norm_add_le _ _
        _ = A1 * ‖Petal.Lambda (star x)‖ + ‖E‖ := by rw [norm_mul, hA1]
        _ ≤ A1 * (2 * Real.sqrt ‖x‖ + 2 * Real.pi) + CE := by
            have h1 : A1 * ‖Petal.Lambda (star x)‖ ≤ A1 * (2 * Real.sqrt ‖x‖ + 2 * Real.pi) :=
              mul_le_mul_of_nonneg_left hΛstarb hA1nn
            linarith [h1, hEb]
    have hYnorm : R₁ ≤ ‖gWfun gU (V x)‖ := by
      rw [hYdecomp]
      have h1 : ‖star x‖ ≤ ‖star x + (1 - a) * Petal.Lambda (star x) + E‖
          + ‖(1 - a) * Petal.Lambda (star x) + E‖ := by
        calc ‖star x‖ = ‖(star x + (1 - a) * Petal.Lambda (star x) + E)
              - ((1 - a) * Petal.Lambda (star x) + E)‖ := by ring_nf
          _ ≤ _ := norm_sub_le _ _
      rw [norm_star] at h1
      linarith [h1, hAux, key, hR1_le, hnormx_gt]
    have hsplit : gWfun gU (V x) - (1 - a) * Petal.Lambda (gWfun gU (V x))
        = star x + (E + (1 - a) * (Petal.Lambda (star x) - Petal.Lambda (gWfun gU (V x)))) := by
      rw [hYdecomp]; ring
    have hbnd2 : ‖E + (1 - a) * (Petal.Lambda (star x) - Petal.Lambda (gWfun gU (V x)))‖ ≤ Cs := by
      have hne : star x ≠ 0 := by
        intro h0
        have h1 : ‖x‖ = 0 := by rw [← norm_star, h0, norm_zero]
        linarith [hnormx_pos]
      have hsmall : ‖gWfun gU (V x) - star x‖ ≤ ‖star x‖ / 2 := by
        have h1 : ‖gWfun gU (V x) - star x‖ = ‖(1 - a) * Petal.Lambda (star x) + E‖ := by
          rw [hYdecomp]; ring_nf
        rw [h1, norm_star]
        linarith [hAux, key]
      have hΛdiff : ‖Petal.Lambda (star x) - Petal.Lambda (gWfun gU (V x))‖ ≤ CΛ := by
        have h := norm_Lambda_sub_close hne hsmall
        rw [hCΛ]
        have h' : 2 * ‖gWfun gU (V x) - star x‖ / ‖star x‖ ≤ 2 * (‖star x‖ / 2) / ‖star x‖ := by
          gcongr
        have h'' : 2 * (‖star x‖ / 2) / ‖star x‖ + 2 * Real.pi = 1 + 2 * Real.pi := by
          have hpos : ‖star x‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hne)
          field_simp
        calc ‖Petal.Lambda (star x) - Petal.Lambda (gWfun gU (V x))‖
            = ‖Petal.Lambda (gWfun gU (V x)) - Petal.Lambda (star x)‖ := norm_sub_rev _ _
          _ ≤ 2 * ‖gWfun gU (V x) - star x‖ / ‖star x‖ + 2 * Real.pi := h
          _ ≤ 2 * (‖star x‖ / 2) / ‖star x‖ + 2 * Real.pi := by linarith [h']
          _ = 1 + 2 * Real.pi := h''
      rw [hCs]
      have h2 : ‖(1 - a) * (Petal.Lambda (star x) - Petal.Lambda (gWfun gU (V x)))‖
          = A1 * ‖Petal.Lambda (star x) - Petal.Lambda (gWfun gU (V x))‖ := by
        rw [norm_mul, hA1]
      calc ‖E + (1 - a) * (Petal.Lambda (star x) - Petal.Lambda (gWfun gU (V x)))‖
          ≤ ‖E‖ + ‖(1 - a) * (Petal.Lambda (star x) - Petal.Lambda (gWfun gU (V x)))‖ :=
            norm_add_le _ _
        _ = ‖E‖ + A1 * ‖Petal.Lambda (star x) - Petal.Lambda (gWfun gU (V x))‖ := by rw [h2]
        _ ≤ CE + A1 * CΛ := by
            have h3 : A1 * ‖Petal.Lambda (star x) - Petal.Lambda (gWfun gU (V x))‖ ≤ A1 * CΛ :=
              mul_le_mul_of_nonneg_left hΛdiff hA1nn
            linarith [hEb, h3]
    have hYre : ((gWfun gU (V x)) - (1 - a) * Petal.Lambda (gWfun gU (V x))).re < -R₁ := by
      rw [hsplit]
      have h1 : (star x + (E + (1 - a) * (Petal.Lambda (star x) - Petal.Lambda (gWfun gU (V x))))).re
          ≤ x.re + Cs := by
        have h2 : (star x + (E + (1 - a) * (Petal.Lambda (star x)
              - Petal.Lambda (gWfun gU (V x))))).re
            = (star x).re + (E + (1 - a) * (Petal.Lambda (star x)
              - Petal.Lambda (gWfun gU (V x)))).re := Complex.add_re _ _
        rw [h2, show (star x).re = x.re from by simp]
        have h3 := Complex.re_le_norm (E + (1 - a) * (Petal.Lambda (star x)
          - Petal.Lambda (gWfun gU (V x))))
        linarith [hbnd2]
      linarith [h1, hR1Cs_le, hx]
    obtain ⟨y, hy1, hy2, hy3⟩ := hVinv' (gWfun gU (V x)) hYnorm hYre
    refine ⟨y, hy2, hy1, ?_⟩
    have hT : gWfun gU (V x) - (1 - a) * Petal.Lambda (gWfun gU (V x))
        - star x = E + (1 - a) * (Petal.Lambda (star x) - Petal.Lambda (gWfun gU (V x))) := by
      rw [hsplit]; ring
    calc ‖y - star x‖
        ≤ ‖y - (gWfun gU (V x) - (1 - a) * Petal.Lambda (gWfun gU (V x)))‖
          + ‖(gWfun gU (V x) - (1 - a) * Petal.Lambda (gWfun gU (V x))) - star x‖ := by
          calc ‖y - star x‖ = ‖(y - (gWfun gU (V x) - (1 - a) * Petal.Lambda (gWfun gU (V x))))
                + ((gWfun gU (V x) - (1 - a) * Petal.Lambda (gWfun gU (V x))) - star x)‖ := by ring_nf
            _ ≤ _ := norm_add_le _ _
      _ ≤ 4 + Cs := by rw [hT]; linarith [hy3, hbnd2]
      _ = CΘ := by rw [hCΘ]; ring
  set Θ : ℂ → ℂ := fun x => if hx : x.re < -Rd then Classical.choose (hex x hx) else x with hΘ
  have hΘspec : ∀ x : ℂ, (hx : x.re < -Rd) → V (Θ x) = gWfun gU (V x) ∧
      (Θ x).re < -R ∧ ‖Θ x - star x‖ ≤ CΘ := by
    intro x hx
    have hval : Θ x = Classical.choose (hex x hx) := by
      simp only [hΘ]
      exact dite_eq_left hx
    rw [hval]
    exact Classical.choose_spec (hex x hx)
  have hΘbound : ∀ x : ℂ, (hx : x.re < -Rd) → (Θ x).re ≤ x.re + CΘ := by
    intro x hx
    obtain ⟨_, _, hbd⟩ := hΘspec x hx
    have h3 : (Θ x - star x).re ≤ ‖Θ x - star x‖ := Complex.re_le_norm _
    have h4 : (star x).re = x.re := by simp
    have h5 : (Θ x).re = (star x).re + (Θ x - star x).re := by simp [Complex.sub_re]
    rw [h5, h4]
    linarith [h3, hbd]
  -- ### Step 2: `Ψ ∘ Θ = gU ∘ Ψ`
  have hΘΨ : ∀ x : ℂ, (hx : x.re < -Rd) → Ψ (Θ x) = gU (Ψ x) := by
    intro x hx
    obtain ⟨hVΘ, hreΘ, _⟩ := hΘspec x hx
    rw [hΨV (Θ x) hreΘ, hVΘ, neg_one_div_gWfun, ← hΨV x (hxR x hx)]
  -- ### Step 3: `Θ (x+1) = Θ x + 1`
  have hΘadd : ∀ x : ℂ, x.re < -Rd - 1 → Θ (x + 1) = Θ x + 1 := by
    intro x hx
    have hx1 : x.re < -Rd := by linarith
    have hxR1 : x.re < -R := hxR x hx1
    obtain ⟨hVΘx, hreΘx, _⟩ := hΘspec x hx1
    have hx1d : (x + 1).re < -Rd := by
      simp only [Complex.add_re, Complex.one_re]; linarith
    obtain ⟨hVΘx1, hreΘx1, _⟩ := hΘspec (x + 1) hx1d
    have hplus : (Θ x + 1).re < -R := by
      simp only [Complex.add_re, Complex.one_re]
      have := hΘbound x hx1
      linarith [this, hRCΘ_le]
    have hVeq : V (Θ (x + 1)) = V (Θ x + 1) := by
      rw [hVΘx1, hVshift x hxR1, gWfun_wMap hgg, ← hVΘx, ← hVshift (Θ x) hreΘx]
    exact hVinj hreΘx1 hplus hVeq
  -- ### Step 4: `Θ (Θ x) = x + 1`
  have hΘinv : ∀ x : ℂ, x.re < -Rd - CΘ - 1 → Θ (Θ x) = x + 1 := by
    intro x hx
    have hx1 : x.re < -Rd := by linarith
    obtain ⟨hVΘx, hreΘx, hbdΘx⟩ := hΘspec x hx1
    have hΘx_le : (Θ x).re < -Rd := by
      have := hΘbound x hx1
      linarith [this]
    have hxR1 : x.re < -R := hxR x hx1
    have hplusR : (x + 1).re < -R := by
      simp only [Complex.add_re, Complex.one_re]; linarith
    obtain ⟨hVΘΘx, hreΘΘx, _⟩ := hΘspec (Θ x) hΘx_le
    have hVeq : V (Θ (Θ x)) = V (x + 1) := by
      rw [hVΘΘx, hVΘx, gWfun_gWfun hgg, ← hVshift x hxR1]
    exact hVinj hreΘΘx hplusR hVeq
  -- ### Step 5: `star ∘ Θ` is holomorphic
  have hΘdiff : DifferentiableOn ℂ (fun x : ℂ => star (Θ x)) {x : ℂ | x.re < -Rd} := by
    intro x₀ hx₀
    have hLopenR : IsOpen {w : ℂ | w.re < -R} :=
      isOpen_lt Complex.continuous_re continuous_const
    have hx₀R : x₀.re < -R := hxR x₀ hx₀
    obtain ⟨hVΘx₀, hreΘx₀, _⟩ := hΘspec x₀ hx₀
    set y₀ : ℂ := Θ x₀ with hy₀def
    have hy₀R : y₀.re < -R := hreΘx₀
    have hne : deriv V y₀ ≠ 0 :=
      Work.ELRig.deriv_ne_zero_of_injOn hVdiff hLopenR hVinj hy₀R
    have hV_an : AnalyticAt ℂ V y₀ := (hVdiff.analyticOn hLopenR).analyticAt (hLopenR.mem_nhds hy₀R)
    have hstrict : HasStrictDerivAt V (deriv V y₀) y₀ := hV_an.hasStrictDerivAt
    set σ : ℂ → ℂ := HasStrictDerivAt.localInverse V (deriv V y₀) y₀ hstrict hne with hσdef
    have hσ_deriv : HasStrictDerivAt σ (deriv V y₀)⁻¹ (V y₀) := hstrict.to_localInverse hne
    have hσ_diff : DifferentiableAt ℂ σ (V y₀) := hσ_deriv.hasDerivAt.differentiableAt
    have hσ_right : ∀ᶠ z in 𝓝 (V y₀), V (σ z) = z := hstrict.eventually_right_inverse hne
    have hσ_mem : ∀ᶠ z in 𝓝 (V y₀), σ z ∈ {w : ℂ | w.re < -R} := by
      have hσy : σ (V y₀) = y₀ := hstrict.eventually_left_inverse hne |>.self_of_nhds
      have hmem : {w : ℂ | w.re < -R} ∈ 𝓝 (σ (V y₀)) := by
        rw [hσy]; exact hLopenR.mem_nhds hy₀R
      exact hσ_diff.continuousAt.preimage_mem_nhds hmem
    -- `Y = gW ∘ V` is continuous at `x₀`
    set Y : ℂ → ℂ := fun w => gWfun gU (V w) with hYdef
    have hYx₀ : Y x₀ = V y₀ := by rw [hYdef, hy₀def]; exact hVΘx₀.symm
    have hgUc_diff : Differentiable ℂ (gUc gU) := fun z => hgU_anti z
    have hVx₀ne : V x₀ ≠ 0 := by
      intro h0
      have h1 := hVbd x₀ hx₀R
      rw [h0, zero_sub, norm_neg] at h1
      have h2 : 0 < ‖x₀‖ := by
        have h3 : R < ‖x₀‖ := by
          have h4 : R < -x₀.re := by linarith
          calc R < -x₀.re := h4
            _ ≤ ‖x₀‖ := by
                have h5 := Complex.abs_re_le_norm x₀
                rw [abs_of_neg (by linarith)] at h5
                linarith
        linarith
      linarith
    have hYne : Y x₀ ≠ 0 := by
      rw [hYx₀]
      intro h0
      have h1 := hVbd y₀ hy₀R
      rw [h0, zero_sub, norm_neg] at h1
      have h2 : 0 < ‖y₀‖ := by
        have h3 : R < ‖y₀‖ := by
          have h4 : R < -y₀.re := by linarith
          calc R < -y₀.re := h4
            _ ≤ ‖y₀‖ := by
                have h5 := Complex.abs_re_le_norm y₀
                rw [abs_of_neg (by linarith)] at h5
                linarith
        linarith
      linarith
    have hstarY_eq : (fun w => star (Y w)) = fun w => -1 / gUc gU (-1 / (V w)) := by
      funext w; rw [hYdef]; exact star_gWfun gU (V w)
    have hgUcne : gUc gU (-1 / (V x₀)) ≠ 0 := by
      intro h0
      have h1 : star (Y x₀) = 0 := by
        rw [show star (Y x₀) = -1 / gUc gU (-1 / (V x₀)) from star_gWfun gU (V x₀)]
        simp [h0]
      exact hYne (by rw [← star_star (Y x₀), h1, star_zero])
    have hstarY_diff : DifferentiableAt ℂ (fun w => star (Y w)) x₀ := by
      rw [hstarY_eq]
      have h1 : DifferentiableAt ℂ (fun w : ℂ => -1 / (V w)) x₀ :=
        (differentiableAt_const (-1)).div (hVdiff.differentiableAt (hLopenR.mem_nhds hx₀R)) hVx₀ne
      exact (differentiableAt_const (-1)).div ((hgUc_diff _).comp x₀ h1) hgUcne
    have hYcont : ContinuousAt Y x₀ := by
      have h1 : ContinuousAt (fun w => star (Y w)) x₀ := hstarY_diff.continuousAt
      simpa using h1.star
    have hYmem : ∀ᶠ w in 𝓝 x₀, V (σ (Y w)) = Y w ∧ σ (Y w) ∈ {z : ℂ | z.re < -R} :=
      hYcont.eventually (by rw [hYx₀]; exact hσ_right.and hσ_mem)
    have hΘ_eq : (fun w => Θ w) =ᶠ[𝓝 x₀] (fun w => σ (Y w)) := by
      have hopen : ∀ᶠ w in 𝓝 x₀, w.re < -Rd :=
        (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hx₀
      filter_upwards [hopen, hYmem] with w hw hYw
      obtain ⟨hrw, hmw⟩ := hYw
      exact hVinj (hΘspec w hw).2.1 hmw (by rw [(hΘspec w hw).1, hrw])
    have hσ_cc : DifferentiableAt ℂ (fun z : ℂ => star (σ (star z))) (star (Y x₀)) := by
      have h1 : star (Y x₀) = star (V y₀) := by rw [hYx₀]
      rw [h1]
      simpa [Function.comp_def] using hσ_diff.conj_conj
    have hcomp_diff : DifferentiableAt ℂ
        ((fun z : ℂ => star (σ (star z))) ∘ (fun w => star (Y w))) x₀ :=
      hσ_cc.comp x₀ hstarY_diff
    have hmain : (fun w => star (Θ w)) =ᶠ[𝓝 x₀]
        ((fun z : ℂ => star (σ (star z))) ∘ (fun w => star (Y w))) := by
      filter_upwards [hΘ_eq] with w hw
      rw [hw]
      simp
    exact (hcomp_diff.congr_of_eventuallyEq hmain).differentiableWithinAt
  -- ### Step 6: Liouville
  have hDdiff : DifferentiableOn ℂ (fun w : ℂ => star (Θ w) - w) {w : ℂ | w.re < -(Rd + 2)} := by
    refine (hΘdiff.mono ?_).sub differentiableOn_id
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    linarith
  have hDper : ∀ w : ℂ, w.re < -(Rd + 2) → star (Θ (w + 1)) - (w + 1) = star (Θ w) - w := by
    intro w hw
    have hw1 : w.re < -Rd - 1 := by linarith
    rw [hΘadd w hw1, star_add, star_one]
    ring
  have hDbdd : ∀ w : ℂ, w.re < -(Rd + 2) → ‖star (Θ w) - w‖ ≤ CΘ := by
    intro w hw
    have hw' : w.re < -Rd := by linarith
    have h1 : star (Θ w) - w = star (Θ w - star w) := by simp
    rw [h1, norm_star]
    exact (hΘspec w hw').2.2
  obtain ⟨κ', hκ'⟩ := periodic_bounded_const hDdiff hDper hDbdd
  set κ : ℂ := star κ' with hκ
  have hΘaff : ∀ w : ℂ, w.re < -(Rd + 2) → Θ w = star w + κ := by
    intro w hw
    have h1 := hκ' w hw
    have h2 : star (Θ w) = w + κ' := by rw [← h1]; ring
    calc Θ w = star (star (Θ w)) := by simp
      _ = star (w + κ') := by rw [h2]
      _ = star w + κ := by rw [hκ]; simp [map_add]
  -- ### Step 7: the real part of `κ`
  have κsum : star κ + κ = 1 := by
    obtain ⟨x, hx⟩ : ∃ x : ℂ, x.re < -(Rd + CΘ + 3) :=
      ⟨-((Rd + CΘ + 4 : ℝ) : ℂ), by simp; linarith⟩
    have hxT : x.re < -(Rd + 2) := by linarith
    have hx1 : x.re < -Rd := by linarith
    have hx2 : x.re < -Rd - CΘ - 1 := by linarith
    have haff1 := hΘaff x hxT
    have hΘxT : (Θ x).re < -(Rd + 2) := by
      have h := hΘbound x hx1
      linarith
    have haff2 := hΘaff (Θ x) hΘxT
    have hinv := hΘinv x hx2
    have h2 : x + 1 = star (Θ x) + κ := by rw [← hinv, haff2]
    have h3 : star (Θ x) = x + star κ := by rw [haff1, star_add, star_star]
    rw [h3] at h2
    have h4 : x + (star κ + κ) = x + 1 := by rw [h2]; ring
    exact add_left_cancel h4
  have hκre : κ.re = 1 / 2 := by
    have h5 : (star κ + κ).re = 2 * κ.re := by
      have h : (star κ).re = κ.re := by simp
      rw [Complex.add_re, h]; ring
    have h6 : (star κ + κ).re = (1 : ℝ) := by rw [κsum]; norm_num
    rw [h5] at h6
    linarith
  -- ### Step 8: local anti-shift relation
  have hlocal : ∀ x : ℂ, x.re < -(Rd + 2) → Ψ (star x + κ) = gU (Ψ x) := by
    intro x hx
    rw [← hΘaff x hx]
    exact hΘΨ x (by linarith)
  -- ### Step 9: globalise
  have hglob : ∀ x : ℂ, Ψ (star x + κ) = gU (Ψ x) := by
    intro x
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (x - (n : ℂ)).re < -(Rd + 2) := by
      refine ⟨⌈x.re + (Rd + 2)⌉₊ + 1, ?_⟩
      simp only [Complex.sub_re, Complex.natCast_re]
      have h := Nat.le_ceil (x.re + (Rd + 2))
      push_cast
      linarith
    have hstar : star x + κ = star (x - (n : ℂ)) + κ + (n : ℂ) := by
      have h1 : star (x - (n : ℂ)) = star x - (n : ℂ) := by simp
      rw [h1]; ring
    rw [hstar, Psi_add_nat hΨshift n (star (x - (n : ℂ)) + κ), hlocal (x - (n : ℂ)) hn,
      ← gU_iterate hgg n (Ψ (x - (n : ℂ))), ← Psi_add_nat hΨshift n (x - (n : ℂ))]
    rw [sub_add_cancel]
  -- ### Step 10: conclusion
  have hcre : ((κ - 1 / 2) / 2).re = 0 := by
    simp [hκre]
  have hcstar : star ((κ - 1 / 2) / 2) = -((κ - 1 / 2) / 2) := by
    apply Complex.ext
    · have h1 : (star ((κ - 1 / 2) / 2)).re = ((κ - 1 / 2) / 2).re := by simp
      simp only [Complex.neg_re]
      rw [h1, hcre]; ring
    · have h1 : (star ((κ - 1 / 2) / 2)).im = -((κ - 1 / 2) / 2).im := by simp; ring
      simp only [Complex.neg_im]
      rw [h1]
  refine ⟨(κ - 1 / 2) / 2, hcstar, ?_⟩
  intro w
  have hkey : star w + 1 / 2 + (κ - 1 / 2) / 2 = star (w + (κ - 1 / 2) / 2) + κ := by
    have h1 : star (w + (κ - 1 / 2) / 2) = star w + star ((κ - 1 / 2) / 2) := by simp
    rw [h1, hcstar]
    ring
  rw [hkey]
  exact hglob (w + (κ - 1 / 2) / 2)

end

end Work.FatouCoord.Flower
