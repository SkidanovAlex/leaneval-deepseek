import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6.ProdDefs6
import Submission.Work.FTS.StrongPersist.N6.Slots
import Submission.Work.FTS.OpenPkg.ProdOpen.m_sum_bound
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

open Work.Spaces
open Work.FTS.EllipticEst (SmoothOpen Q0 mem_Q0)
open Work.FTS.OpenPkg.ProdOpen (leibniz_open_mixed)

/-
Template (verbatim, level 4, sorry-free): `Work.FTS.OpenPkg.ProdOpen.{m_slot_bound, m_sum_bound}`
(`Submission/Work/FTS/OpenPkg/ProdOpen/m_sum_bound.lean`) — copy with `4 ↦ 6`, the low-order
threshold `2 ↦ 4`, the binomial constants `256 ↦ 4096` (`N6.binom_sq_le_4096`),
`65536 ↦ 16777216`, `(I+1)(J+1) ≤ 25 ↦ ≤ 49`, and a generous final constant.

`m_slot_bound6` (proved below) is: for `A,B` the angular/radial orders on `f` and `D,C` those on
`g` with `1 ≤ A + D` and `A+B+C+D ≤ 6`, the pair `(D_z^B D_θ^A f · D_z^C D_θ^D g · W)²` is
`≤ max CPw 1 * (SInv6 + Texc6)`, closing by
  (a) `1 ≤ D` and `A+B ≤ 4`: `PwAny6` on `f` + the `(C,D)`-slot of `g`;
  (b) `A ≥ 1` and `C+D ≤ 4`: `PwAny6` on `g` + the `(B,A)`-slot of `f`;
  (c) the two exceptional slots `(A,B,C,D) = (0,5,0,1)` and `(1,0,5,0)`, bounded by `Texc6`
      (again as in the level-4 file).

Helpers: `Work.FTS.StrongPersist.N6.{SInv6_nonneg, Texc6_nonneg, mul_inv_mul_le_SInv6_left,
mul_inv_mul_le_SInv6_right, binom_sq_le_4096, gam_sub_one_pos6}` (in `N6/ProdDefs6`);
`Work.FTS.StrongPersist.N6.PwAny6` (in `N6/PwOpen6`); the index-general Leibniz rule
`Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed`.
-/

/-- **The per-Leibniz-term bound.**  For orders `A,B` on `f` and `C,D` on `g` with
`A + D ≥ 1` and `A + B + C + D ≤ 6`,

  `(D_z^B D_θ^A f · D_z^C D_θ^D g · W)² ≤ max CPw 1 · (SInv6 + Texc6)`.

The hypothesis `1 ≤ A + D` is the slot condition `i ≥ 1` of `HkIntegrand`. -/
theorem m_slot_bound6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hF : SmoothOpen f) (hmemF : HkMem α 6 f) (hG : SmoothOpen g) (hmemG : HkMem α 6 g)
    {CPw : ℝ} (hCPw : 0 < CPw)
    (hPw : ∀ (u : ℝ → ℝ → ℝ), SmoothOpen u → HkMem α 6 u → ∀ b a : ℕ, a + b ≤ 4 →
      ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (mixed b a u z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 6 u)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∀ A B C D : ℕ, 1 ≤ A + D → A + B + C + D ≤ 6 →
      (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        ≤ max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) := by
  intro A B C D hAD htot
  have hγ : 0 < gam α - 1 := gam_sub_one_pos6 hα
  have hSl : 0 ≤ SInv6 α f g z θ := SInv6_nonneg hα f g z θ
  have hTl : 0 ≤ Texc6 α f g z θ := Texc6_nonneg α f g z θ
  have hCMpos : 0 < max CPw 1 := lt_of_lt_of_le hCPw (le_max_left _ _)
  have hPwCM : CPw ≤ max CPw 1 := le_max_left _ _
  have h1CM : (1 : ℝ) ≤ max CPw 1 := le_max_right _ _
  -- ### The three closing shapes
  have keyF : (mixed B A f z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 6 f →
      (mixed C D g z θ * Wt α z θ) ^ 2 ≤ HkIntegrand α 6 g z θ →
      (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        ≤ max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) := by
    intro hx hy
    have h1 : (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        = (mixed B A f z θ) ^ 2 * (mixed C D g z θ * Wt α z θ) ^ 2 := by ring
    rw [h1]
    calc (mixed B A f z θ) ^ 2 * (mixed C D g z θ * Wt α z θ) ^ 2
        ≤ (CPw / (gam α - 1) * HkSq α 6 f) * HkIntegrand α 6 g z θ :=
          mul_le_mul hx hy (sq_nonneg _)
            (mul_nonneg (div_nonneg hCPw.le hγ.le) (HkSq_nonneg α 6 f))
      _ = CPw * ((gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 g z θ)) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ CPw * SInv6 α f g z θ :=
          mul_le_mul_of_nonneg_left (mul_inv_mul_le_SInv6_left hα f g z θ) hCPw.le
      _ ≤ max CPw 1 * SInv6 α f g z θ := mul_le_mul_of_nonneg_right hPwCM hSl
      _ ≤ max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hTl) hCMpos.le
  have keyG : (mixed C D g z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 6 g →
      (mixed B A f z θ * Wt α z θ) ^ 2 ≤ HkIntegrand α 6 f z θ →
      (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        ≤ max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) := by
    intro hy hx
    have h1 : (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        = (mixed B A f z θ * Wt α z θ) ^ 2 * (mixed C D g z θ) ^ 2 := by ring
    rw [h1]
    calc (mixed B A f z θ * Wt α z θ) ^ 2 * (mixed C D g z θ) ^ 2
        ≤ HkIntegrand α 6 f z θ * (CPw / (gam α - 1) * HkSq α 6 g) :=
          mul_le_mul hx hy (sq_nonneg _) (HkIntegrand_nonneg α 6 f z θ)
      _ = CPw * ((gam α - 1)⁻¹ * (HkSq α 6 g * HkIntegrand α 6 f z θ)) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ CPw * SInv6 α f g z θ :=
          mul_le_mul_of_nonneg_left (mul_inv_mul_le_SInv6_right hα f g z θ) hCPw.le
      _ ≤ max CPw 1 * SInv6 α f g z θ := mul_le_mul_of_nonneg_right hPwCM hSl
      _ ≤ max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hTl) hCMpos.le
  have keyE : (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2 ≤ Texc6 α f g z θ →
      (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        ≤ max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) := by
    intro hxy
    calc (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2 ≤ Texc6 α f g z θ := hxy
      _ = 1 * Texc6 α f g z θ := by ring
      _ ≤ max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) :=
          mul_le_mul h1CM (le_add_of_nonneg_left hSl) hTl (by linarith)
  -- ### The case analysis
  by_cases hA1 : 1 ≤ A
  · by_cases hD1 : 1 ≤ D
    · -- both angular orders positive: `min (A+B) (C+D) ≤ 3 ≤ 4`
      by_cases hmin : A + B ≤ C + D
      · exact keyF (hPw f hF hmemF B A (by omega) z θ hz hθ)
          (sq_le_HkIntegrand_mixed α 6 g z θ D C hD1 (by omega))
      · exact keyG (hPw g hG hmemG C D (by omega) z θ hz hθ)
          (sq_le_HkIntegrand_mixed α 6 f z θ A B hA1 (by omega))
    · -- `D = 0`: the `g`-factor is a pure `D_z`-slot
      have hDe : D = 0 := by omega
      subst hDe
      by_cases hC4 : C ≤ 4
      · exact keyG (hPw g hG hmemG C 0 (by omega) z θ hz hθ)
          (sq_le_HkIntegrand_mixed α 6 f z θ A B hA1 (by omega))
      · -- exceptional: `A = 1, B = 0, C = 5, D = 0`
        have hAe : A = 1 := by omega
        have hBe : B = 0 := by omega
        have hCe : C = 5 := by omega
        refine keyE ?_
        rw [hAe, hBe, hCe]
        simp only [mixed_zero_left, mixed_zero_right, DthIter_succ, DthIter_zero]
        rw [show (Dth f z θ * DzIter 5 g z θ * Wt α z θ) ^ 2
            = (Dth f z θ * DzIter 5 g z θ) ^ 2 * (Wt α z θ) ^ 2 from by ring, Texc6]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg _)) (sq_nonneg _)
  · -- `A = 0`: the `f`-factor is a pure `D_z`-slot
    have hAe : A = 0 := by omega
    subst hAe
    have hD1 : 1 ≤ D := by omega
    by_cases hB4 : B ≤ 4
    · exact keyF (hPw f hF hmemF B 0 (by omega) z θ hz hθ)
        (sq_le_HkIntegrand_mixed α 6 g z θ D C hD1 (by omega))
    · -- exceptional: `A = 0, B = 5, C = 0, D = 1`
      have hBe : B = 5 := by omega
      have hCe : C = 0 := by omega
      have hDe : D = 1 := by omega
      refine keyE ?_
      rw [hBe, hCe, hDe]
      simp only [mixed_zero_left, mixed_zero_right, DthIter_succ, DthIter_zero]
      rw [show (DzIter 5 f z θ * Dth g z θ * Wt α z θ) ^ 2
          = (DzIter 5 f z θ * Dth g z θ) ^ 2 * (Wt α z θ) ^ 2 from by ring, Texc6]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg _)) (sq_nonneg _)

theorem m_sum_bound6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
    ∀ I J : ℕ, 1 ≤ I → I + J ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ C * (Work.FTS.StrongPersist.N6.SInv6 α f g z θ
            + Work.FTS.StrongPersist.N6.Texc6 α f g z θ) := by
  obtain ⟨CPw, hCPwpos, hPwAny⟩ := PwAny6
  refine ⟨10 ^ 11 * max CPw 1, by positivity, ?_⟩
  intro α f g hα hα1 hF hmemF hG hmemG I J hI hIJ z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hPw : ∀ (u : ℝ → ℝ → ℝ), SmoothOpen u → HkMem α 6 u → ∀ b a : ℕ, a + b ≤ 4 →
      ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (mixed b a u z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 6 u :=
    fun u hu hum b a hab z θ hz hθ' => hPwAny α u b a hα hα1 hu hum hab z hz θ hθ'
  have hMnn : 0 ≤ max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) :=
    mul_nonneg (le_trans hCPwpos.le (le_max_left _ _))
      (add_nonneg (SInv6_nonneg hα f g z θ) (Texc6_nonneg α f g z θ))
  -- ### Leibniz expansion and the two Cauchy–Schwarz steps
  have hlei := leibniz_open_mixed J I f g hF hG z θ hz hθ0 hθ1
  set Y : ℕ → ℕ → ℝ := fun a b => (I.choose a : ℝ) * (J.choose b : ℝ)
    * (mixed b a f z θ * mixed (J - b) (I - a) g z θ * Wt α z θ) with hYdef
  have hYsplit : (mixed J I (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2 := by
    have hkey : (mixed J I (fun z θ => f z θ * g z θ) z θ) * Wt α z θ
        = ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b := by
      rw [hlei, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [hYdef]; ring
    rw [hkey]
  have hper : ∀ a ∈ Finset.range (I + 1), ∀ b ∈ Finset.range (J + 1),
      (Y a b) ^ 2 ≤ 16777216 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ)) := by
    intro a ha b hb
    have haI : a ≤ I := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbJ : b ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hcha : (I.choose a : ℝ) ^ 2 ≤ 4096 := binom_sq_le_4096 I a (by omega) (by omega)
    have hchb : (J.choose b : ℝ) ^ 2 ≤ 4096 := binom_sq_le_4096 J b (by omega) (by omega)
    have hch : (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 16777216 :=
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 4096 * 4096 :=
            mul_le_mul hcha hchb (by positivity) (by norm_num)
        _ = 16777216 := by norm_num
    have hslot := m_slot_bound6 hα hα1 hF hmemF hG hmemG hCPwpos hPw hz hθ a b (J - b) (I - a)
      (by omega) (by omega)
    have hY : (Y a b) ^ 2 = (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
        * (mixed b a f z θ * mixed (J - b) (I - a) g z θ * Wt α z θ) ^ 2 := by
      rw [hYdef]; ring
    rw [hY]
    exact mul_le_mul hch hslot (sq_nonneg _) (by norm_num)
  have hcardI : (((Finset.range (I + 1)).card : ℕ) : ℝ) = (I : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcardJ : (((Finset.range (J + 1)).card : ℕ) : ℝ) = (J : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hIJ49 : ((I : ℝ) + 1) * ((J : ℝ) + 1) ≤ 49 := by
    have hI6 : (I : ℝ) ≤ 6 := by exact_mod_cast (by omega : I ≤ 6)
    have hJ6 : (J : ℝ) ≤ 6 := by exact_mod_cast (by omega : J ≤ 6)
    nlinarith
  have hsum2 : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2
      ≤ ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
          (16777216 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ))) :=
    Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hper a ha b hb
  have hsumconst : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
        (16777216 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ)))
      = ((I : ℝ) + 1) * ((J : ℝ) + 1)
        * (16777216 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ))) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul]
    push_cast; ring
  rw [hYsplit]
  calc (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2
      ≤ ((I : ℝ) + 1) * ∑ a ∈ Finset.range (I + 1),
          ((J : ℝ) + 1) * ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (I + 1))
          (f := fun a => ∑ b ∈ Finset.range (J + 1), Y a b)
        rw [hcardI] at hcs
        refine hcs.trans ?_
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => ?_)) (by positivity)
        have hcs2 := sq_sum_le_card_mul_sum_sq (s := Finset.range (J + 1))
          (f := fun b => Y a b)
        rwa [hcardJ] at hcs2
    _ = ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
              (16777216 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ))) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2
          * (16777216 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ))) := by
        rw [hsumconst]; ring_nf
    _ ≤ 2401 * (16777216 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h0 : (0 : ℝ) ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1) := by positivity
        nlinarith [hIJ49, h0]
    _ = 40282095616 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ)) := by ring
    _ ≤ 10 ^ 11 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hMnn
    _ = 10 ^ 11 * max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) := by ring

end Work.FTS.StrongPersist.N6
