/-
# `Work.FTS.LocData.ZfarFstar.ZFMaj` — the `𝓗⁴`-majorant for the far part `zfar L F_*`

The target of this module is

  `zfar_Fstar_hk_majorant : ∃ C ≥ 0, ∀ z ∈ Iz, ∀ θ ∈ Iθ,
     HkIntegrand α 4 (zfar L F_*) z θ ≤ C·α²·angMaj α θ/(1+z)²`

for `0 < α ≤ 1` and `L ≥ 1`.  The statement carries a *free* constant: the cut-off
`χ = Real.smoothTransition(2 - ‖·‖)` has a fourth `D_z`-derivative of size `≈1.8·10⁴` in the
middle of its transition annulus, so no universal constant (in particular not `10⁵`) works; see
`Submission/Work/FTS/LocData/HkIntegrand_zfar_Fstar_le.lean`.  With the free constant the proof
is a plain Leibniz expansion:

* on `z ≤ L` the far part vanishes identically, together with all its derivatives, so the
  integrand is `0` (`Work.Stability.HkIntegrand_zfar_eq_zero`);
* on `z > L` (hence `z ≥ 1`) the Leibniz rule `DzIter_mul_smoothQuad` expands the derivatives of
  `(1 - χ(·/L))·F_*` into the (uniformly bounded) derivatives of the cut-off factor times the
  derivatives of `F_*`, which are `O(α·Γ/z)` by `Phi_w_le`; the `θ`-independence of the cut-off
  factor collapses the mixed derivatives to a single term (`mixed_zfar_eq`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocData.ZfarFstar.ZFBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData
namespace ZF

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## `rpow` bookkeeping for the two weights -/

theorem rpow_neg_half_sq (S : ℝ) (hS : 0 ≤ S) (a : ℝ) :
    (S ^ (-(a / 2))) ^ 2 = S ^ (-a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hS]
  congr 1
  push_cast
  ring

/-- `(x·(w/S^{a/2}))² = (x·w)²·S^{-a}`. -/
theorem mul_div_rpow_sq (x w S : ℝ) (hS : 0 ≤ S) (a : ℝ) :
    (x * (w / S ^ (a / 2))) ^ 2 = (x * w) ^ 2 * S ^ (-a) := by
  rw [div_eq_mul_inv]
  have h1 : (S ^ (a / 2))⁻¹ = S ^ (-(a / 2)) := (Real.rpow_neg hS (a / 2)).symm
  rw [h1]
  rw [show x * (w * S ^ (-(a / 2))) = (x * w) * S ^ (-(a / 2)) by ring]
  rw [mul_pow, rpow_neg_half_sq S hS a]

/-- `(x·Wt)² = (x·w)²·sin(2θ)^{-γ}`. -/
theorem mul_Wt_sq (x : ℝ) (z θ : ℝ) (α : ℝ) (hS : 0 ≤ Real.sin (2 * θ)) :
    (x * Work.Spaces.Wt α z θ) ^ 2
      = (x * Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [show x * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))
      = (x * Work.Spaces.w z) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) by ring]
  rw [mul_pow, rpow_neg_half_sq _ hS (Work.Spaces.gam α)]

/-! ## The mixed derivatives of the far part -/

/-- **The mixed derivatives of the far part.**  Since the cut-off factor `1 - χ(z/L)` does not
depend on `θ`, the `θ`-derivatives act on `F_*` alone, and the radial Leibniz expansion collapses
to the single term `b = j` (all higher `D_z`-iterates of the `z`-independent factor vanish). -/
theorem mixed_zfar_eq (α : ℝ) (L : ℝ) (i j : ℕ) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) (θ : ℝ) :
    Work.Spaces.mixed j i (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
      = Work.Spaces.DzIter j
            (fun z _ => (1 - Work.Stability.chi (z / L)) * Work.FM.Fstar z) z θ
          * ((α / Work.Spaces.c α)
              * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) := by
  have h1 : Work.Spaces.DthIter i (Work.Stability.zfar L (Work.Construction.Fstar α))
      = fun z θ => (1 - Work.Stability.chi (z / L))
          * Work.Spaces.DthIter i (Work.Construction.Fstar α) z θ :=
    DthIter_mul_left_z i (fun z => 1 - Work.Stability.chi (z / L))
      (Work.Construction.Fstar α)
  have h2 : Work.Spaces.DthIter i (Work.Construction.Fstar α)
      = fun z θ => (α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ * Work.FM.Fstar z := by
    funext z θ
    rw [congrFun (congrFun (DthIter_Fstar_eq α i) z) θ, DthIter_gamFn_z_indep α i z 0 θ]
    ring
  have h3 : Work.Spaces.DthIter i (Work.Stability.zfar L (Work.Construction.Fstar α))
      = fun z θ => ((1 - Work.Stability.chi (z / L)) * Work.FM.Fstar z)
          * ((α / Work.Spaces.c α)
              * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) := by
    rw [h1, h2]
    funext z θ
    ring
  have h4 := DzIter_mul_smoothQuad (θ := θ) j
    (fun z _ => (1 - Work.Stability.chi (z / L)) * Work.FM.Fstar z)
    (fun _ θ' => (α / Work.Spaces.c α)
      * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ') hz
    (contDiffOn_slice_c_FM L)
    (contDiffOn_const (c := (α / Work.Spaces.c α)
      * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ))
  rw [Work.Spaces.mixed, h3, h4]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    have hlt : b < j := by
      rw [Finset.mem_range] at hb
      omega
    have hge : 1 ≤ j - b := by omega
    rw [show j - b = (j - b - 1) + 1 from (Nat.sub_add_cancel hge).symm]
    rw [DzIter_z_indep_succ (j - b - 1)
      (fun θ' => (α / Work.Spaces.c α)
        * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ')]
    simp
  · intro hj
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self j)) hj

/-! ## The majorant -/

/-- **The pointwise `ℋ⁴`-majorant of the far part** `zfar L F_*`, with a free constant. -/
theorem zfar_Fstar_hk_majorant (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {L : ℝ} (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
        ≤ C * α ^ 2 * angMaj α θ / (1 + z) ^ 2 := by
  obtain ⟨C₀, hC₀⟩ := DzIter_oneSubChi_bound L hL
  refine ⟨(10 : ℝ) ^ 13 * (max C₀ 1 ^ 2 + 1), by positivity, ?_⟩
  intro z hz θ hθ
  have hang0 : 0 ≤ angMaj α θ := angMaj_nonneg hθ
  by_cases hzL : z < L
  · -- the far part vanishes identically for `z < L`
    have h0 : Work.Spaces.HkIntegrand α 4
        (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ = 0 := by
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h | h
      · subst h
        exact Work.Stability.HkIntegrand_zfar_zero_left α 4 _ θ
      · exact Work.Stability.HkIntegrand_zfar_eq_zero (α := α) (k := 4) (Z := L)
          (f := Work.Construction.Fstar α) (by linarith) ⟨h, hzL⟩
    rw [h0]
    positivity
  · -- `L ≤ z`, hence `1 ≤ z`
    have hzL' : L ≤ z := not_lt.mp hzL
    have hz1 : 1 ≤ z := by linarith
    have hzpos : 0 < z := by linarith
    have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
    obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
    have hC₁0 : 0 ≤ max C₀ 1 := le_of_lt (lt_of_lt_of_le one_pos (le_max_right _ _))
    have hC₁b : ∀ b : ℕ, b ≤ 4 →
        |Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ| ≤ max C₀ 1 :=
      fun b hb => le_trans (hC₀ b hb z hz θ) (le_max_left _ _)
    -- the bound on a single radial weight derivative of the far part
    have hrad : ∀ i : ℕ, i ≤ 4 →
        |Work.Spaces.DzIter i (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
            * Work.Spaces.w z|
          ≤ 800 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z) := by
      intro i hi4
      have hLeib : Work.Spaces.DzIter i (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
          = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) *
              (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
                * Work.Spaces.DzIter (i - b) (Work.Construction.Fstar α) z θ) :=
        DzIter_mul_smoothQuad i (fun z _ => 1 - Work.Stability.chi (z / L))
          (Work.Construction.Fstar α) hz (contDiffOn_slice_oneSubChi L)
          (contDiffOn_slice_Fstar α θ)
      rw [hLeib]
      have hcongr : (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) *
            (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
              * Work.Spaces.DzIter (i - b) (Work.Construction.Fstar α) z θ))
            * Work.Spaces.w z
          = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) *
              (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
                * (Work.Spaces.DzIter (i - b) (Work.Construction.Fstar α) z θ
                    * Work.Spaces.w z)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        ring
      rw [hcongr]
      have hterm : ∀ b ∈ Finset.range (i + 1), |(i.choose b : ℝ) *
            (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
              * (Work.Spaces.DzIter (i - b) (Work.Construction.Fstar α) z θ
                  * Work.Spaces.w z))|
          ≤ 16 * (max C₀ 1 * (10 * α * Work.Spaces.Gam α θ / (3 * z))) := by
        intro b hb
        rw [Finset.mem_range] at hb
        have hb4 : b ≤ 4 := by omega
        have hib4 : i - b ≤ 4 := by omega
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        have h16 : (i.choose b : ℝ) ≤ 16 := by
          have h := Nat.choose_le_two_pow i b
          have h2 : 2 ^ i ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hi4
          have h3 : i.choose b ≤ 16 := by omega
          exact_mod_cast h3
        have h1 : |Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ|
            ≤ max C₀ 1 := hC₁b b hb4
        have h2b : |Work.Spaces.DzIter (i - b) (Work.Construction.Fstar α) z θ
            * Work.Spaces.w z| ≤ 10 * α * Work.Spaces.Gam α θ / (3 * z) :=
          DzIter_Fstar_w_le α hα hα1 hib4 hz1 hθ
        exact mul_le_mul h16 (mul_le_mul h1 h2b (abs_nonneg _) hC₁0) (by positivity)
          (by norm_num)
      calc |∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) *
            (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
              * (Work.Spaces.DzIter (i - b) (Work.Construction.Fstar α) z θ
                  * Work.Spaces.w z))|
          ≤ ∑ b ∈ Finset.range (i + 1), |(i.choose b : ℝ) *
              (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
                * (Work.Spaces.DzIter (i - b) (Work.Construction.Fstar α) z θ
                    * Work.Spaces.w z))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _b ∈ Finset.range (i + 1),
              16 * (max C₀ 1 * (10 * α * Work.Spaces.Gam α θ / (3 * z))) :=
            Finset.sum_le_sum hterm
        _ = ((i + 1 : ℕ) : ℝ)
              * (16 * (max C₀ 1 * (10 * α * Work.Spaces.Gam α θ / (3 * z)))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ 800 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z) := by
            have h5 : ((i + 1 : ℕ) : ℝ) ≤ 5 := by
              have : i + 1 ≤ 5 := by omega
              exact_mod_cast this
            have h6 : 0 ≤ 16 * (max C₀ 1 * (10 * α * Work.Spaces.Gam α θ / (3 * z))) := by
              positivity
            have h7 : ((i + 1 : ℕ) : ℝ)
                * (16 * (max C₀ 1 * (10 * α * Work.Spaces.Gam α θ / (3 * z))))
                ≤ 5 * (16 * (max C₀ 1 * (10 * α * Work.Spaces.Gam α θ / (3 * z)))) :=
              mul_le_mul_of_nonneg_right h5 h6
            have h8 : 5 * (16 * (max C₀ 1 * (10 * α * Work.Spaces.Gam α θ / (3 * z))))
                = 800 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z) := by ring
            linarith [h7, h8.le]
    -- the bound on the cut-off factor times `F.M.Fstar`
    have hradj : ∀ j : ℕ, j ≤ 4 → |Work.Spaces.DzIter j
          (fun z _ => (1 - Work.Stability.chi (z / L)) * Work.FM.Fstar z) z θ
          * Work.Spaces.w z| ≤ 80 * max C₀ 1 * (2 / z) := by
      intro j hj4
      have hLeib : Work.Spaces.DzIter j
            (fun z _ => (1 - Work.Stability.chi (z / L)) * Work.FM.Fstar z) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
              (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
                * Work.Spaces.DzIter (j - b) (fun z _ => Work.FM.Fstar z) z θ) :=
        DzIter_mul_smoothQuad j (fun z _ => 1 - Work.Stability.chi (z / L))
          (fun z _ => Work.FM.Fstar z) hz (contDiffOn_slice_oneSubChi L)
          contDiffOn_slice_FM_Fstar
      rw [hLeib]
      have hcongr : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
            (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
              * Work.Spaces.DzIter (j - b) (fun z _ => Work.FM.Fstar z) z θ))
            * Work.Spaces.w z
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
              (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
                * (Work.Spaces.DzIter (j - b) (fun z _ => Work.FM.Fstar z) z θ
                    * Work.Spaces.w z)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        ring
      rw [hcongr]
      have hterm : ∀ b ∈ Finset.range (j + 1), |(j.choose b : ℝ) *
            (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
              * (Work.Spaces.DzIter (j - b) (fun z _ => Work.FM.Fstar z) z θ
                  * Work.Spaces.w z))| ≤ 16 * (max C₀ 1 * (2 / z)) := by
        intro b hb
        rw [Finset.mem_range] at hb
        have hb4 : b ≤ 4 := by omega
        have hjb4 : j - b ≤ 4 := by omega
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        have h16 : (j.choose b : ℝ) ≤ 16 := by
          have h := Nat.choose_le_two_pow j b
          have h2 : 2 ^ j ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hj4
          have h3 : j.choose b ≤ 16 := by omega
          exact_mod_cast h3
        have h1 : |Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ|
            ≤ max C₀ 1 := hC₁b b hb4
        have h2b : |Work.Spaces.DzIter (j - b) (fun z _ => Work.FM.Fstar z) z θ
            * Work.Spaces.w z| ≤ 2 / z := by
          rw [mul_comm, PhiZ_eq (j - b) hjb4 z θ]
          exact Phi_w_le (j - b) hjb4 hz1 θ
        exact mul_le_mul h16 (mul_le_mul h1 h2b (abs_nonneg _) hC₁0) (by positivity)
          (by norm_num)
      calc |∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
            (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
              * (Work.Spaces.DzIter (j - b) (fun z _ => Work.FM.Fstar z) z θ
                  * Work.Spaces.w z))|
          ≤ ∑ b ∈ Finset.range (j + 1), |(j.choose b : ℝ) *
              (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
                * (Work.Spaces.DzIter (j - b) (fun z _ => Work.FM.Fstar z) z θ
                    * Work.Spaces.w z))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _b ∈ Finset.range (j + 1), 16 * (max C₀ 1 * (2 / z)) :=
            Finset.sum_le_sum hterm
        _ = ((j + 1 : ℕ) : ℝ) * (16 * (max C₀ 1 * (2 / z))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ 80 * max C₀ 1 * (2 / z) := by
            have h5 : ((j + 1 : ℕ) : ℝ) ≤ 5 := by
              have : j + 1 ≤ 5 := by omega
              exact_mod_cast this
            have h6 : 0 ≤ 16 * (max C₀ 1 * (2 / z)) := by positivity
            have h7 : ((j + 1 : ℕ) : ℝ) * (16 * (max C₀ 1 * (2 / z)))
                ≤ 5 * (16 * (max C₀ 1 * (2 / z))) := mul_le_mul_of_nonneg_right h5 h6
            have h8 : 5 * (16 * (max C₀ 1 * (2 / z))) = 80 * max C₀ 1 * (2 / z) := by ring
            linarith [h7, h8.le]
    -- the bound on a single mixed derivative
    have hmix : ∀ i j : ℕ, i ≤ 4 → j ≤ 4 →
        |Work.Spaces.mixed j i (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
            * Work.Spaces.w z|
          ≤ 160000 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z) := by
      intro i j hi4 hj4
      have hK : |(α / Work.Spaces.c α)
            * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
          ≤ 200 * (5 / 3) * (α * Work.Spaces.Gam α θ) := by
        have hc : (3 : ℝ) / 5 ≤ Work.Spaces.c α := c_ge_three_fifths α hα hα1
        have hcInv : (Work.Spaces.c α)⁻¹ ≤ (5 : ℝ) / 3 := by
          have h0 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 5) hc
          rw [one_div] at h0
          norm_num at h0
          exact h0
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α / Work.Spaces.c α)]
        rw [DthIter_Gam_Pf α i hi4 0 θ hθ, abs_mul, abs_of_nonneg hG0]
        have hPf : |Pf i (Real.cos (2 * θ)) α| ≤ 200 :=
          Pf_abs_le i hi4 (Real.neg_one_le_cos _) (Real.cos_le_one _) hα.le hα1
        have hstep : α * (Work.Spaces.Gam α θ * |Pf i (Real.cos (2 * θ)) α|)
              * (Work.Spaces.c α)⁻¹
            ≤ (200 * α * Work.Spaces.Gam α θ) * (Work.Spaces.c α)⁻¹ := by
          have h : Work.Spaces.Gam α θ * |Pf i (Real.cos (2 * θ)) α| ≤ Work.Spaces.Gam α θ * 200 :=
            mul_le_mul_of_nonneg_left hPf hG0
          have h2 : α * (Work.Spaces.Gam α θ * |Pf i (Real.cos (2 * θ)) α|)
              ≤ 200 * α * Work.Spaces.Gam α θ := by
            calc α * (Work.Spaces.Gam α θ * |Pf i (Real.cos (2 * θ)) α|)
                ≤ α * (Work.Spaces.Gam α θ * 200) := mul_le_mul_of_nonneg_left h hα.le
              _ = 200 * α * Work.Spaces.Gam α θ := by ring
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
        have hfirst : (α / Work.Spaces.c α)
              * (Work.Spaces.Gam α θ * |Pf i (Real.cos (2 * θ)) α|)
            = α * (Work.Spaces.Gam α θ * |Pf i (Real.cos (2 * θ)) α|)
                * (Work.Spaces.c α)⁻¹ := by ring
        rw [hfirst]
        calc α * (Work.Spaces.Gam α θ * |Pf i (Real.cos (2 * θ)) α|)
              * (Work.Spaces.c α)⁻¹
            ≤ (200 * α * Work.Spaces.Gam α θ) * (Work.Spaces.c α)⁻¹ := hstep
          _ ≤ (200 * α * Work.Spaces.Gam α θ) * (5 / 3) :=
              mul_le_mul_of_nonneg_left hcInv (by positivity)
          _ = 200 * (5 / 3) * (α * Work.Spaces.Gam α θ) := by ring
      have hmixeq := mixed_zfar_eq α L i j hz θ
      rw [hmixeq]
      have hsplit : Work.Spaces.DzIter j
              (fun z _ => (1 - Work.Stability.chi (z / L)) * Work.FM.Fstar z) z θ
            * ((α / Work.Spaces.c α)
                * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
            * Work.Spaces.w z
          = (Work.Spaces.DzIter j
                (fun z _ => (1 - Work.Stability.chi (z / L)) * Work.FM.Fstar z) z θ
              * Work.Spaces.w z)
            * ((α / Work.Spaces.c α)
                * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) := by ring
      rw [hsplit, abs_mul]
      have hprod : |Work.Spaces.DzIter j
            (fun z _ => (1 - Work.Stability.chi (z / L)) * Work.FM.Fstar z) z θ
            * Work.Spaces.w z|
          * |(α / Work.Spaces.c α)
              * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
          ≤ (80 * max C₀ 1 * (2 / z)) * (200 * (5 / 3) * (α * Work.Spaces.Gam α θ)) :=
        mul_le_mul (hradj j hj4) hK (abs_nonneg _) (by positivity)
      refine le_trans hprod ?_
      rw [show (80 * max C₀ 1 * (2 / z)) * (200 * (5 / 3) * (α * Work.Spaces.Gam α θ))
          = 160000 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z) from by ring]
    -- the two sums
    have hsum1 : (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i
          (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 5 * (800 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      have hterm : ∀ i ∈ Finset.range 5, (Work.Spaces.DzIter i
            (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ (800 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        intro i hi
        rw [Finset.mem_range] at hi
        have hi4 : i ≤ 4 := by omega
        rw [mul_div_rpow_sq _ _ _ hS (Work.Spaces.eta)]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hS _)
        have hb := hrad i hi4
        have h2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
        rwa [sq_abs] at h2
      calc (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i
            (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ i ∈ Finset.range 5, (800 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Finset.sum_le_sum hterm
        _ = 5 * (800 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
    have hsum2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ 25 * (160000 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      have hterm : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ (if 1 ≤ i ∧ i + j ≤ 4 then
              (160000 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z)) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) := by
        intro i hi j hj
        rw [Finset.mem_range] at hi hj
        by_cases hc : 1 ≤ i ∧ i + j ≤ 4
        · rw [if_pos hc, if_pos hc]
          have hi4 : i ≤ 4 := by omega
          have hj4 : j ≤ 4 := by omega
          rw [mul_Wt_sq _ _ _ α hS]
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hS _)
          have hb := hmix i j hi4 hj4
          have h2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
          rwa [sq_abs] at h2
        · rw [if_neg hc, if_neg hc]
      have hterm2 : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
              (160000 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z)) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)
          ≤ (160000 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z)) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        intro i hi j hj
        by_cases hc : 1 ≤ i ∧ i + j ≤ 4
        · rw [if_pos hc]
        · rw [if_neg hc]
          positivity
      calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (160000 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z)) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) :=
            Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hterm i hi))
        _ ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              ((160000 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z)) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
            Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hterm2 i hi))
        _ = 25 * (160000 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
    -- the final arithmetic
    rw [Work.Spaces.HkIntegrand]
    refine le_trans (add_le_add hsum1 hsum2) ?_
    have hgam0 : 0 ≤ Work.Spaces.gam α := by
      rw [Work.Spaces.gam]; positivity
    have hS1 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hS _
    have hS2 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hS _
    have hang1 : Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ angMaj α θ := by
      rw [angMaj_apply]
      have h : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_nonneg (sq_nonneg _) hS2
      linarith
    have hang2 : Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ angMaj α θ := by
      rw [angMaj_apply]
      have h : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        mul_nonneg (sq_nonneg _) hS1
      linarith
    have hzsq : 1 / z ^ 2 ≤ 4 / (1 + z) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hz1]
    have hAeq : 5 * (800 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        = 5 * (800 / 3) ^ 2 * ((max C₀ 1) ^ 2 * α ^ 2 * (Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) / z ^ 2) := by ring
    have hBeq : 25 * (160000 * max C₀ 1 * (α * Work.Spaces.Gam α θ) / (3 * z)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = 25 * (160000 / 3) ^ 2 * ((max C₀ 1) ^ 2 * α ^ 2 * (Work.Spaces.Gam α θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) / z ^ 2) := by ring
    rw [hAeq, hBeq]
    have hstep1 : 5 * (800 / 3) ^ 2 * ((max C₀ 1) ^ 2 * α ^ 2 * (Work.Spaces.Gam α θ ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) / z ^ 2)
        ≤ 5 * (800 / 3) ^ 2 * ((max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ / z ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hang1 (by positivity)
    have hstep2 : 25 * (160000 / 3) ^ 2 * ((max C₀ 1) ^ 2 * α ^ 2 * (Work.Spaces.Gam α θ ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) / z ^ 2)
        ≤ 25 * (160000 / 3) ^ 2 * ((max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ / z ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hang2 (by positivity)
    refine le_trans (add_le_add hstep1 hstep2) ?_
    have hcomb : 5 * (800 / 3) ^ 2 * ((max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ / z ^ 2)
          + 25 * (160000 / 3) ^ 2 * ((max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ / z ^ 2)
        = (5 * (800 / 3) ^ 2 + 25 * (160000 / 3) ^ 2)
            * ((max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ / z ^ 2) := by ring
    rw [hcomb]
    have hnum : 5 * (800 / 3) ^ 2 + 25 * (160000 / 3) ^ 2 ≤ (10 : ℝ) ^ 13 / 4 := by norm_num
    have hfinal1 : (5 * (800 / 3) ^ 2 + 25 * (160000 / 3) ^ 2)
          * ((max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ / z ^ 2)
        ≤ ((10 : ℝ) ^ 13 / 4) * ((max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ / z ^ 2) :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    refine le_trans hfinal1 ?_
    have hunit : (max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ / z ^ 2
        ≤ 4 * ((max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ / (1 + z) ^ 2) := by
      have h1 : (max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ / z ^ 2
          = ((max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ) * (1 / z ^ 2) := by ring
      rw [h1]
      have hnn : (0 : ℝ) ≤ (max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ := by positivity
      calc ((max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ) * (1 / z ^ 2)
          ≤ ((max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ) * (4 / (1 + z) ^ 2) :=
            mul_le_mul_of_nonneg_left hzsq hnn
        _ = 4 * ((max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ / (1 + z) ^ 2) := by ring
    refine le_trans (mul_le_mul_of_nonneg_left hunit (by positivity)) ?_
    have hfin : ((10 : ℝ) ^ 13 / 4) * (4 * ((max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ / (1 + z) ^ 2))
        ≤ (10 : ℝ) ^ 13 * (max C₀ 1 ^ 2 + 1) * α ^ 2 * angMaj α θ / (1 + z) ^ 2 := by
      have h1 : ((10 : ℝ) ^ 13 / 4)
            * (4 * ((max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ / (1 + z) ^ 2))
          = (10 : ℝ) ^ 13 * ((max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ / (1 + z) ^ 2) := by ring
      rw [h1]
      have h2 : (max C₀ 1) ^ 2 ≤ max C₀ 1 ^ 2 + 1 := by linarith [sq_nonneg (max C₀ 1)]
      have h3 : (max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ / (1 + z) ^ 2
          ≤ (max C₀ 1 ^ 2 + 1) * α ^ 2 * angMaj α θ / (1 + z) ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity)
      calc (10 : ℝ) ^ 13 * ((max C₀ 1) ^ 2 * α ^ 2 * angMaj α θ / (1 + z) ^ 2)
          ≤ (10 : ℝ) ^ 13 * ((max C₀ 1 ^ 2 + 1) * α ^ 2 * angMaj α θ / (1 + z) ^ 2) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (10 : ℝ) ^ 13 * (max C₀ 1 ^ 2 + 1) * α ^ 2 * angMaj α θ / (1 + z) ^ 2 := by ring
    exact hfin

end ZF
end Work.FTS.LocData
