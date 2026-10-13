/-
# `Work.FTS.PhiStar.Series.eFam_growth` -- the `O(m^{3/2})` growth of the Gegenbauer family

Main part of the proof of `eFam_growth`: the second-order constraint `sec^2 theta_0 <= M` at an
interior maximum of `|eFam m|` (via the sign of `cos theta * f'`), the resulting pointwise bound

  `|eFam m theta| <= sqrt 2 * |(eFam m)'(0)|`   (`eFam_sq_le`),

the size of the initial datum `|(eFam m)'(0)| <= 6 (m+1)^{3/2}` (`deriv_eFam_zero_bound`, from the
ladder relation at `x = 0` and `(gC (2j) 0)^2 <= 4j+3`), and finally `eFam_growth`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.FTS.PhiStar.Series.eFamEneAux
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter Set SignType

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

open Work.FTS.PhiStar.Gegenbauer
/-! ## The constraint `sec²θ₀ ≤ M` at a maximum of `|eFam m|` -/

/-- **The second-order constraint.**  If `θ₀` is an interior point where `|eFam m|` is maximal,
`eFam m θ₀ ≠ 0` and `(eFam m)' θ₀ = 0`, then `1 ≤ eM m · cos²θ₀` (i.e. `sec²θ₀ ≤ M`). -/
lemma eM_mul_cos_sq_ge_one (m : ℕ) {θ₀ : ℝ} (hint : θ₀ ∈ Set.Ioo 0 (Real.pi/2))
    (hnz : eFam m θ₀ ≠ 0) (hder : deriv (eFam m) θ₀ = 0)
    (hmax : ∀ θ ∈ Set.Icc (0:ℝ) (Real.pi/2), |eFam m θ| ≤ |eFam m θ₀|) :
    1 ≤ eM m * (Real.cos θ₀)^2 := by
  by_contra hcon
  rw [not_le] at hcon
  have hcos_pos : 0 < Real.cos θ₀ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hint.1, Real.pi_pos], by linarith [hint.2, Real.pi_pos]⟩
  have hcos_ne : Real.cos θ₀ ≠ 0 := ne_of_gt hcos_pos
  have hπ : 0 < Real.pi/2 - θ₀ := by linarith [hint.2]
  have hc : 0 < 1 / Real.cos θ₀ - eM m * Real.cos θ₀ := by
    have h2 : eM m * Real.cos θ₀ < 1 / Real.cos θ₀ := by
      rw [lt_div_iff₀ hcos_pos]; linarith [hcon]
    linarith
  have hdphi : deriv (fun θ' => Real.cos θ' * deriv (eFam m) θ') θ₀
      = (1 / Real.cos θ₀ - eM m * Real.cos θ₀) * eFam m θ₀ := eFam_ode m θ₀ hcos_ne
  have hphi0 : (fun θ' => Real.cos θ' * deriv (eFam m) θ') θ₀ = 0 := by
    simp [hder]
  rcases lt_trichotomy (eFam m θ₀) 0 with hlt | heq | hgt
  · -- `f θ₀ < 0`: `φ` is negative just to the right of `θ₀`, so `f` decreases strictly there
    have hd : deriv (fun θ' => Real.cos θ' * deriv (eFam m) θ') θ₀ < 0 := by
      rw [hdphi]; exact mul_neg_of_pos_of_neg hc hlt
    have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg hd hphi0
    have hneg : ∀ᶠ x in 𝓝[>] θ₀,
        (fun θ' => Real.cos θ' * deriv (eFam m) θ') x < 0 := by
      filter_upwards [hsign.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hx'
      have h1 : sign (θ₀ - x) = -1 := sign_eq_neg_one_iff.mpr (sub_neg.mpr hx')
      rw [h1] at hx
      exact sign_eq_neg_one_iff.mp hx
    obtain ⟨δ, hδpos, hδsub⟩ :=
      (nhdsGT_basis_of_exists_gt (show ∃ b : ℝ, θ₀ < b from ⟨θ₀ + 1, by linarith⟩)).mem_iff.mp hneg
    set δ₁ : ℝ := min (δ - θ₀) (Real.pi/2 - θ₀) / 2 with hδ₁def
    have hδ₁pos : 0 < δ₁ := by
      rw [hδ₁def]
      have h := lt_min (show (0:ℝ) < δ - θ₀ by linarith) hπ
      linarith
    have hδ₁δ : θ₀ + δ₁ < δ := by
      rw [hδ₁def]; nlinarith [min_le_left (δ - θ₀) (Real.pi/2 - θ₀)]
    have hδ₁π : θ₀ + δ₁ < Real.pi/2 := by
      rw [hδ₁def]; nlinarith [min_le_right (δ - θ₀) (Real.pi/2 - θ₀)]
    have hderneg : ∀ x ∈ Set.Ioo θ₀ (θ₀ + δ₁), deriv (eFam m) x < 0 := by
      intro x hx
      have hxmem : x ∈ Set.Ioo θ₀ δ := ⟨hx.1, by linarith [hx.2, hδ₁δ]⟩
      have hxφ : Real.cos x * deriv (eFam m) x < 0 := hδsub hxmem
      have hcx : 0 < Real.cos x := by
        refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
        · linarith [hx.1, hint.1, Real.pi_pos]
        · linarith [hx.2, hδ₁π]
      nlinarith [hxφ, hcx]
    have hanti : StrictAntiOn (eFam m) (Set.Icc θ₀ (θ₀ + δ₁)) :=
      strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuous_eFam m).continuousOn
        (fun x hx => by rw [interior_Icc] at hx; exact hderneg x hx)
    have hcmp : eFam m (θ₀ + δ₁) < eFam m θ₀ :=
      hanti (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith)) (by linarith)
    have habs : |eFam m θ₀| < |eFam m (θ₀ + δ₁)| := by
      rw [abs_of_neg hlt, abs_of_neg (by linarith [hcmp, hlt])]
      linarith
    have := hmax (θ₀ + δ₁) ⟨by linarith [hint.1, hδ₁pos], by linarith [hδ₁π]⟩
    linarith
  · exact absurd heq hnz
  · -- `f θ₀ > 0`: `φ` is positive just to the right of `θ₀`, so `f` increases strictly there
    have hd : 0 < deriv (fun θ' => Real.cos θ' * deriv (eFam m) θ') θ₀ := by
      rw [hdphi]; exact mul_pos hc hgt
    have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos hd hphi0
    have hpos : ∀ᶠ x in 𝓝[>] θ₀,
        0 < (fun θ' => Real.cos θ' * deriv (eFam m) θ') x := by
      filter_upwards [hsign.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hx'
      have h1 : sign (x - θ₀) = 1 := sign_eq_one_iff.mpr (sub_pos.mpr hx')
      rw [h1] at hx
      exact sign_eq_one_iff.mp hx
    obtain ⟨δ, hδpos, hδsub⟩ :=
      (nhdsGT_basis_of_exists_gt (show ∃ b : ℝ, θ₀ < b from ⟨θ₀ + 1, by linarith⟩)).mem_iff.mp hpos
    set δ₁ : ℝ := min (δ - θ₀) (Real.pi/2 - θ₀) / 2 with hδ₁def
    have hδ₁pos : 0 < δ₁ := by
      rw [hδ₁def]
      have h := lt_min (show (0:ℝ) < δ - θ₀ by linarith) hπ
      linarith
    have hδ₁δ : θ₀ + δ₁ < δ := by
      rw [hδ₁def]; nlinarith [min_le_left (δ - θ₀) (Real.pi/2 - θ₀)]
    have hδ₁π : θ₀ + δ₁ < Real.pi/2 := by
      rw [hδ₁def]; nlinarith [min_le_right (δ - θ₀) (Real.pi/2 - θ₀)]
    have hderpos : ∀ x ∈ Set.Ioo θ₀ (θ₀ + δ₁), 0 < deriv (eFam m) x := by
      intro x hx
      have hxmem : x ∈ Set.Ioo θ₀ δ := ⟨hx.1, by linarith [hx.2, hδ₁δ]⟩
      have hxφ : 0 < Real.cos x * deriv (eFam m) x := hδsub hxmem
      have hcx : 0 < Real.cos x := by
        refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
        · linarith [hx.1, hint.1, Real.pi_pos]
        · linarith [hx.2, hδ₁π]
      nlinarith [hxφ, hcx]
    have hmono : StrictMonoOn (eFam m) (Set.Icc θ₀ (θ₀ + δ₁)) :=
      strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_eFam m).continuousOn
        (fun x hx => by rw [interior_Icc] at hx; exact hderpos x hx)
    have hcmp : eFam m θ₀ < eFam m (θ₀ + δ₁) :=
      hmono (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith)) (by linarith)
    have habs : |eFam m θ₀| < |eFam m (θ₀ + δ₁)| := by
      rw [abs_of_pos hgt, abs_of_pos (by linarith [hcmp, hgt])]
      linarith
    have := hmax (θ₀ + δ₁) ⟨by linarith [hint.1, hδ₁pos], by linarith [hδ₁π]⟩
    linarith

/-! ## The pointwise bound `|eFam m θ| ≤ √2 |(eFam m)'(0)|` -/

/-- **The pointwise bound.**  `|eFam m|` is bounded by `√2 |(eFam m)'(0)|` on `Iθ`; this is the
maximum principle for the Sturm–Liouville equation of `eFam m`. -/
lemma eFam_sq_le (m : ℕ) : ∀ θ ∈ Work.Spaces.Iθ,
    (eFam m θ)^2 ≤ 2 * (deriv (eFam m) 0)^2 := by
  intro θ hθ
  have hmemθ : θ ∈ Set.Icc (0:ℝ) (Real.pi/2) := hθ
  obtain ⟨θ₀, hθ₀mem, hθ₀max⟩ :=
    isCompact_Icc.exists_isMaxOn (s := Set.Icc (0:ℝ) (Real.pi/2))
      ⟨0, ⟨le_rfl, by linarith [Real.pi_pos]⟩⟩ (((continuous_eFam m).abs).continuousOn)
  by_cases hzero : eFam m θ₀ = 0
  · have h1 : |eFam m θ| ≤ 0 := by simpa [hzero] using hθ₀max hmemθ
    have h2 : eFam m θ = 0 := abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    rw [h2]; nlinarith [sq_nonneg (deriv (eFam m) 0)]
  · have hnz : eFam m θ₀ ≠ 0 := hzero
    have hint : θ₀ ∈ Set.Ioo 0 (Real.pi/2) := by
      rcases lt_or_eq_of_le hθ₀mem.1 with h | h
      · rcases lt_or_eq_of_le hθ₀mem.2 with h2 | h2
        · exact ⟨h, h2⟩
        · exact absurd (by rw [h2, eFam_pi_half m]) hzero
      · exact absurd (by rw [h.symm, eFam_zero m]) hzero
    have hder : deriv (eFam m) θ₀ = 0 := by
      have hnb : Set.Icc (0:ℝ) (Real.pi/2) ∈ 𝓝 θ₀ :=
        mem_of_superset (Ioo_mem_nhds hint.1 hint.2) fun x hx => ⟨hx.1.le, hx.2.le⟩
      have hmaxabs : IsLocalMax (fun x => |eFam m x|) θ₀ := hθ₀max.isLocalMax hnb
      rcases lt_trichotomy (eFam m θ₀) 0 with hlt | heq | hgt
      · have heq' : (fun x => |eFam m x|) =ᶠ[𝓝 θ₀] fun x => -eFam m x := by
          filter_upwards [(continuous_eFam m).continuousAt.eventually
            (isOpen_Iio.mem_nhds hlt)] with x hx
          exact abs_of_neg hx
        have hlmax : IsLocalMax (fun x => -eFam m x) θ₀ := heq'.isLocalMax_iff.mp hmaxabs
        have h0 := hlmax.deriv_eq_zero
        have h0' : deriv (fun x => -eFam m x) θ₀ = -deriv (eFam m) θ₀ := by
          simpa using deriv.neg (f := eFam m) (x := θ₀)
        linarith
      · exact absurd heq hzero
      · have heq' : (fun x => |eFam m x|) =ᶠ[𝓝 θ₀] eFam m := by
          filter_upwards [(continuous_eFam m).continuousAt.eventually
            (isOpen_Ioi.mem_nhds hgt)] with x hx
          exact abs_of_pos hx
        have hlmax : IsLocalMax (eFam m) θ₀ := heq'.isLocalMax_iff.mp hmaxabs
        exact hlmax.deriv_eq_zero
    have hcon := eM_mul_cos_sq_ge_one m hint hnz hder (fun θ hθ => hθ₀max hθ)
    have hcrit := eEne_at_critical m hder
    have hle := eEne_le_eEne_zero m hθ₀mem
    have hcoef : (1:ℝ)/2 ≤ eM m * Real.cos θ₀ - 1 / (2 * Real.cos θ₀) := by
      have h1 : 1 ≤ 2 * (eM m * Real.cos θ₀ ^ 2) - 1 := by linarith
      have h2 : Real.cos θ₀ ≤ 1 := Real.cos_le_one θ₀
      have hcp : 0 < Real.cos θ₀ := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hint.1, Real.pi_pos], by linarith [hint.2, Real.pi_pos]⟩
      have h3 : eM m * Real.cos θ₀ - 1 / (2 * Real.cos θ₀)
          = (2 * (eM m * Real.cos θ₀ ^ 2) - 1) / (2 * Real.cos θ₀) := by
        field_simp
      rw [h3, le_div_iff₀ (by positivity)]
      linarith
    have hf2 : (eFam m θ₀)^2 ≤ 2 * eEne m θ₀ := by
      rw [hcrit]
      nlinarith [hcoef, sq_nonneg (eFam m θ₀)]
    calc (eFam m θ)^2 = |eFam m θ|^2 := by rw [sq_abs]
      _ ≤ |eFam m θ₀|^2 := pow_le_pow_left₀ (abs_nonneg _) (hθ₀max hmemθ) 2
      _ = (eFam m θ₀)^2 := by rw [sq_abs]
      _ ≤ 2 * eEne m θ₀ := hf2
      _ ≤ 2 * eEne m 0 := by linarith
      _ = 2 * (deriv (eFam m) 0)^2 := by rw [eEne_at_zero m]

/-! ## The size of `(eFam m)'(0)` -/

/-- The ladder relation at `x = 0`: `(gC (k+1))'(0) = (k+2) gC k 0`. -/
lemma deriv_gC_succ_zero (k : ℕ) : deriv (gC (k + 1)) 0 = ((k : ℝ) + 3) * gC k 0 := by
  have h := Erel_all k 0
  simp only [Erel, Drel, Nat.add_sub_cancel] at h
  push_cast at h
  norm_num at h
  linarith

/-- `(gC (2j) 0)² ≤ 4j+3`, by the three-term recurrence at `x = 0`. -/
lemma gC_even_zero_sq_le (j : ℕ) : (gC (2 * j) 0)^2 ≤ 4 * (j : ℝ) + 3 := by
  induction j with
  | zero => rw [show gC (2 * 0) = gC 0 from rfl,
      show gC 0 = (fun _ : ℝ => 1) from rfl]; norm_num
  | succ j ih =>
    have hrec := gC_rec (2 * j) 0
    have h2j : ((2 * j : ℕ) : ℝ) = 2 * (j : ℝ) := by push_cast; ring
    rw [h2j] at hrec
    have hval : gC (2 * j + 2) 0 = -((2 * (j:ℝ) + 3) / (2 * (j:ℝ) + 2)) * gC (2 * j) 0 := by
      field_simp
      linarith [hrec]
    have hsq : (gC (2 * (j + 1)) 0)^2
        = ((2 * (j:ℝ) + 3) / (2 * (j:ℝ) + 2))^2 * (gC (2 * j) 0)^2 := by
      have h2 : (2 * (j + 1) : ℕ) = 2 * j + 2 := by ring
      rw [h2, hval]; ring
    have hA : ((2 * (j:ℝ) + 3) / (2 * (j:ℝ) + 2))^2 * (4 * (j:ℝ) + 3) ≤ 4 * (j:ℝ) + 7 := by
      rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (2 * (j:ℝ) + 2)]
    rw [hsq]
    have hstep : ((2 * (j:ℝ) + 3) / (2 * (j:ℝ) + 2))^2 * (gC (2 * j) 0)^2
        ≤ 4 * ((j:ℝ) + 1) + 3 :=
      calc ((2 * (j:ℝ) + 3) / (2 * (j:ℝ) + 2))^2 * (gC (2 * j) 0)^2
          ≤ ((2 * (j:ℝ) + 3) / (2 * (j:ℝ) + 2))^2 * (4 * (j:ℝ) + 3) :=
            mul_le_mul_of_nonneg_left ih (sq_nonneg _)
        _ ≤ 4 * (j:ℝ) + 7 := hA
        _ = 4 * ((j:ℝ) + 1) + 3 := by ring
    simpa only [Nat.cast_add, Nat.cast_one] using hstep

/-- The initial-data bound: `|(eFam m)'(0)| ≤ 6 (m+1)^{3/2}`. -/
lemma deriv_eFam_zero_bound (m : ℕ) :
    |deriv (eFam m) 0| ≤ 6 * ((m : ℝ) + 1) ^ ((3 : ℝ) / 2) := by
  have hlad : deriv (eFam m) 0 = (2 * (m:ℝ) + 3) * gC (2 * m) 0 := by
    rw [deriv_eFam_zero m, deriv_gC_succ_zero (2 * m)]
    push_cast; ring
  have hsq := gC_even_zero_sq_le m
  have hg : |gC (2 * m) 0| ≤ Real.sqrt (4 * (m:ℝ) + 3) := by
    have h5 : Real.sqrt ((gC (2 * m) 0)^2) ≤ Real.sqrt ((Real.sqrt (4 * (m:ℝ) + 3))^2) := by
      refine Real.sqrt_le_sqrt ?_
      rw [Real.sq_sqrt (show (0:ℝ) ≤ 4 * (m:ℝ) + 3 by positivity)]
      exact hsq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (by positivity)] at h5
  have hsqrt : Real.sqrt (4 * (m:ℝ) + 3) ≤ 2 * Real.sqrt ((m:ℝ) + 1) := by
    have h1 : Real.sqrt (4 * (m:ℝ) + 3) ≤ Real.sqrt (4 * ((m:ℝ) + 1)) :=
      Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (4 * ((m:ℝ) + 1)) = 2 * Real.sqrt ((m:ℝ) + 1) := by
      rw [show (4:ℝ) * ((m:ℝ) + 1) = (2 * Real.sqrt ((m:ℝ) + 1))^2 by
        rw [mul_pow, Real.sq_sqrt (by positivity)]; ring]
      exact Real.sqrt_sq (by positivity)
    rwa [h2] at h1
  have hrpow : ((m : ℝ) + 1) ^ ((3:ℝ)/2) = ((m:ℝ) + 1) * Real.sqrt ((m:ℝ) + 1) := by
    rw [show ((3:ℝ)/2) = 1 + 1/2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  rw [hlad, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (m:ℝ) + 3), hrpow]
  have hs : 0 ≤ Real.sqrt ((m:ℝ) + 1) := Real.sqrt_nonneg _
  calc (2 * (m:ℝ) + 3) * |gC (2 * m) 0|
      ≤ (2 * (m:ℝ) + 3) * (2 * Real.sqrt ((m:ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (hg.trans hsqrt) (by positivity)
    _ ≤ 6 * (((m:ℝ) + 1) * Real.sqrt ((m:ℝ) + 1)) := by nlinarith

/-! ## The main statement -/

theorem eFam_growth :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
        |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) := by
  refine ⟨9, by norm_num, fun m θ hθ => ?_⟩
  have h1 : (eFam m θ)^2 ≤ 2 * (deriv (eFam m) 0)^2 := eFam_sq_le m θ hθ
  have h2 : (deriv (eFam m) 0)^2 ≤ (6 * ((m:ℝ) + 1)^((3:ℝ)/2))^2 := by
    have hsq : |deriv (eFam m) 0|^2 ≤ (6 * ((m:ℝ) + 1)^((3:ℝ)/2))^2 :=
      pow_le_pow_left₀ (abs_nonneg _) (deriv_eFam_zero_bound m) 2
    rwa [sq_abs] at hsq
  have h3 : |eFam m θ|^2 ≤ (Real.sqrt 2 * 6 * ((m:ℝ) + 1)^((3:ℝ)/2))^2 := by
    have he : (Real.sqrt 2 * 6 * ((m:ℝ) + 1)^((3:ℝ)/2))^2
        = 2 * (6 * ((m:ℝ) + 1)^((3:ℝ)/2))^2 := by
      rw [mul_assoc, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [he, sq_abs]
    linarith
  have h4 : |eFam m θ| ≤ Real.sqrt 2 * 6 * ((m:ℝ) + 1)^((3:ℝ)/2) := by
    have hB : 0 ≤ Real.sqrt 2 * 6 * ((m:ℝ) + 1)^((3:ℝ)/2) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (by norm_num))
        (Real.rpow_nonneg (by positivity) ((3:ℝ)/2))
    have h5 : Real.sqrt ((eFam m θ)^2)
        ≤ Real.sqrt ((Real.sqrt 2 * 6 * ((m:ℝ) + 1)^((3:ℝ)/2))^2) := by
      refine Real.sqrt_le_sqrt ?_
      rw [show (eFam m θ)^2 = |eFam m θ|^2 from (sq_abs _).symm]
      exact h3
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hB] at h5
  have h6 : Real.sqrt 2 * 6 * ((m:ℝ) + 1)^((3:ℝ)/2)
      ≤ 9 * ((m:ℝ) + 1)^((3:ℝ)/2) := by
    have hx : 0 ≤ ((m:ℝ) + 1)^((3:ℝ)/2) := Real.rpow_nonneg (by positivity) _
    have hsq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    have hr : Real.sqrt 2 * 6 ≤ 9 := by
      nlinarith [sq_nonneg ((3/2 : ℝ) - Real.sqrt 2)]
    nlinarith [hr, hx]
  linarith
end Work.FTS.PhiStar.Series
