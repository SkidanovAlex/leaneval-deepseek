/-
# `Work.FTS.PhiStar.Honesty.CptApp.cutAngularBound`

The angular cut-off `zetaR n θ = 𝕋 (n θ - 1) · 𝕋 (n (π/2 - θ) - 1)` has `D_θ`-jets bounded
*uniformly in `n`*, at every order.  (`D_θ = sin(2θ) ∂_θ` is the scale-invariant angular
operator of the paper: the factor `n` produced by the chain rule is compensated by the factor
`sin(2θ) ≲ 1/n` on the transition layer.)

This is the all-orders version of `Work.FTS.GalBasis.cc.psiCut_cutB_bound` (which covers the
orders `i ≤ 4` for the same cut-off with `N + 1` in place of `n`).  The argument is the same:

* for `θ`-profiles, `Work.Spaces.DthIter i (fun _ θ' => u θ') z = Work.Spaces.Lop^[i] u`, and
  `D_θ` acts on the recombined product by the Leibniz rule `Lop_iter_mul`;
* in the rescaled variable `u = n θ - 1` (resp. `u = -n θ + (n π/2 - 1)`) the two factors
  `θ ↦ 𝕋 (n θ - 1)` and `θ ↦ 𝕋 (n (π/2 - θ) - 1)` have `Lop`-iterates given by
  `Eiter k (rhoM n) 𝕋` resp. `Eiter k (-rhoM n) 𝕋` (`Lop_iter_affine_st`);
* `Eiter k ρ 𝕋 v` is bounded uniformly in `ρ` by a constant depending only on all-order bounds
  `M` of `ρ` and `B` of `𝕋` on the transition layer `[0,1]` (`Eiter_deriv_bound_all` +
  `Eiter_eq_zero_of_open_const`, packaged here as `cab_eiter_explicit_bound` with the explicit
  constant `max (Cbnd M B k 0) 1`);
* the only input that has to be supplied is the all-order bound
  `|iteratedDeriv m (rhoM n) u| ≤ 4 · 2^m` on `[0,1]`, uniform in `n ≥ 1`
  (`cab_iteratedDeriv_rhoM_bound_all`), from the closed form
  `iteratedDeriv m (rhoM lam) u = lam · (2/lam)^m · sin(2 (u+1)/lam + m π/2)`;
* `n = 0` is degenerate: `zetaR 0 ≡ 0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Defs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EiterEngine
import Submission.Work.FTS.GalBasis.cc.psiCut_cutB_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.EstAux

open Work.FTS.GalBasis.cc

set_option linter.unusedVariables false

/-! ## 1. The iterated derivatives of `sin` -/

/-- `∂^m sin x = sin (x + m π/2)`. -/
theorem cab_iteratedDeriv_sin_eq (m : ℕ) :
    iteratedDeriv m Real.sin = fun x : ℝ => Real.sin (x + (m : ℝ) * (Real.pi / 2)) := by
  induction m with
  | zero => funext x; simp
  | succ m ih =>
    funext x
    rw [iteratedDeriv_succ, ih]
    have h1 : HasDerivAt (fun x : ℝ => Real.sin (x + (m : ℝ) * (Real.pi / 2)))
        (Real.cos (x + (m : ℝ) * (Real.pi / 2)) * 1) x :=
      ((hasDerivAt_id x).add_const _).sin
    rw [h1.deriv, mul_one, ← Real.sin_add_pi_div_two]
    congr 1
    push_cast
    ring

/-! ## 2. The all-order bounds on the rescaled angular coefficient `rhoM lam`

`rhoM lam u = lam · sin (2 (u + 1)/lam)` is the coefficient of the operator `D_θ` in the
rescaled variable `u = lam θ - 1`.  On the transition layer `u ∈ [0,1]` all its derivatives are
bounded by `4 · 2^m`, *uniformly in `lam ≥ 1`*. -/

theorem cab_iteratedDeriv_rhoM_bound_all {lam : ℝ} (hlam : 1 ≤ lam) (m : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) : |iteratedDeriv m (rhoM lam) u| ≤ 4 * 2 ^ m := by
  have hpos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    rw [iteratedDeriv_zero, pow_zero, mul_one]
    have hpt : rhoM lam u = lam * Real.sin (2 * (u + 1) / lam) := by simp only [rhoM]
    rw [hpt, abs_mul, abs_of_pos hpos]
    have htpos : 0 ≤ 2 * (u + 1) / lam := div_nonneg (by linarith [hu.1]) (le_of_lt hpos)
    have hb : |Real.sin (2 * (u + 1) / lam)| ≤ 2 * (u + 1) / lam :=
      le_trans (Real.abs_sin_le_abs (x := 2 * (u + 1) / lam)) (le_of_eq (abs_of_nonneg htpos))
    calc lam * |Real.sin (2 * (u + 1) / lam)| ≤ lam * (2 * (u + 1) / lam) :=
          mul_le_mul_of_nonneg_left hb (le_of_lt hpos)
      _ = 2 * (u + 1) := by field_simp
      _ ≤ 4 := by linarith [hu.2]
  · obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hmpos)
    subst hm'
    have hfun : rhoM lam = fun u : ℝ => lam * Real.sin ((2 / lam) * u + (2 / lam)) := by
      funext u
      simp only [rhoM]
      rw [show 2 * (u + 1) / lam = (2 / lam) * u + (2 / lam) from by field_simp]
    rw [hfun]
    have hconst : iteratedDeriv (m' + 1) (fun u : ℝ => lam * Real.sin ((2 / lam) * u + (2 / lam)))
          u = lam * iteratedDeriv (m' + 1)
            (fun u : ℝ => Real.sin ((2 / lam) * u + (2 / lam))) u :=
      iteratedDeriv_const_mul lam (by fun_prop)
    rw [hconst]
    have hcomp : iteratedDeriv (m' + 1) (fun u : ℝ => Real.sin ((2 / lam) * u + (2 / lam))) u
        = (2 / lam) ^ (m' + 1) * iteratedDeriv (m' + 1) Real.sin ((2 / lam) * u + (2 / lam)) := by
      have hcd : ContDiff ℝ ((m' + 1 : ℕ) : WithTop ℕ∞)
          (fun y : ℝ => Real.sin (y + (2 / lam))) :=
        Real.contDiff_sin.comp (contDiff_id.add contDiff_const)
      have h1 := congrFun (iteratedDeriv_comp_const_mul (n := m' + 1) (c := 2 / lam)
        (f := fun y : ℝ => Real.sin (y + (2 / lam))) hcd) u
      have h2 := congrFun (iteratedDeriv_comp_add_const (m' + 1) Real.sin (2 / lam)) ((2 / lam) * u)
      simp only [h2] at h1
      simpa using h1
    rw [hcomp]
    have hS : |iteratedDeriv (m' + 1) Real.sin ((2 / lam) * u + (2 / lam))| ≤ 1 := by
      rw [cab_iteratedDeriv_sin_eq]
      exact Real.abs_sin_le_one _
    rw [abs_mul, abs_mul, abs_of_pos hpos,
      abs_of_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ 2 / lam) (m' + 1))]
    have h2div : 2 / lam ≤ 2 := by rw [div_le_iff₀ hpos]; linarith
    have hpow2 : (2 / lam) ^ m' ≤ 2 ^ m' := pow_le_pow_left₀ (by positivity) h2div m'
    have hkey : lam * (2 / lam) ^ (m' + 1) = 2 * (2 / lam) ^ m' := by
      rw [pow_succ]
      field_simp
    calc lam * ((2 / lam) ^ (m' + 1)
          * |iteratedDeriv (m' + 1) Real.sin ((2 / lam) * u + (2 / lam))|)
        ≤ lam * ((2 / lam) ^ (m' + 1) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS (pow_nonneg (by positivity) _))
            (le_of_lt hpos)
      _ = 2 * (2 / lam) ^ m' := by rw [mul_one, hkey]
      _ ≤ 2 * 2 ^ m' := mul_le_mul_of_nonneg_left hpow2 (by norm_num)
      _ = 2 ^ (m' + 1) := by rw [pow_succ]; ring
      _ ≤ 4 * 2 ^ (m' + 1) := by
          have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (m' + 1); linarith

/-! ## 3. The abstract iterate bound with an explicit constant

This is `exists_Eiter_smoothTransition_bound` with the witness `K` made explicit: it is
`k ↦ max (Cbnd M B k 0) 1`, which depends only on `M` and `B`, *not* on the coefficient `ρ`. -/

theorem cab_eiter_explicit_bound {ρ : ℝ → ℝ} {M B : ℕ → ℝ}
    (hMnn : ∀ m, 0 ≤ M m) (hBnn : ∀ m, 0 ≤ B m)
    (hρ : ∀ n : ℕ, ContDiff ℝ n ρ)
    (hM : ∀ m : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv m ρ u| ≤ M m)
    (hB : ∀ m : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv m Real.smoothTransition u| ≤ B m) :
    ∀ (k : ℕ) (v : ℝ), |Eiter k ρ Real.smoothTransition v| ≤ max (Cbnd M B k 0) 1 := by
  intro k v
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp only [Eiter_zero]
    have hσ : |Real.smoothTransition v| ≤ 1 := by
      rcases le_or_gt v 0 with hv | hv
      · rw [Real.smoothTransition.zero_of_nonpos hv, abs_zero]
        norm_num
      rcases le_or_gt 1 v with hv1 | hv1
      · rw [Real.smoothTransition.one_of_one_le hv1, abs_one]
      · rw [abs_of_nonneg (Real.smoothTransition.nonneg v)]
        exact Real.smoothTransition.le_one v
    exact le_trans hσ (le_max_right _ _)
  · by_cases hv : v ∈ Set.Icc (0 : ℝ) 1
    · have h := Eiter_deriv_bound_all hMnn hBnn hρ contDiff_smoothTransition hM hB k 0 v hv
      simp only [iteratedDeriv_zero] at h
      exact le_trans h (le_max_left _ _)
    · rw [Set.mem_Icc, not_and_or] at hv
      have hzero : Eiter k ρ Real.smoothTransition v = 0 := by
        rcases hv with hv | hv
        · have hv' : v < 0 := lt_of_not_ge hv
          exact Eiter_eq_zero_of_open_const isOpen_Iio (Set.mem_Iio.mpr hv') (fun w hw => by
            rw [Real.smoothTransition.zero_of_nonpos (le_of_lt hw),
              Real.smoothTransition.zero_of_nonpos (le_of_lt hv')]) k hkpos v
            (Set.mem_Iio.mpr hv')
        · have hv' : 1 < v := lt_of_not_ge hv
          exact Eiter_eq_zero_of_open_const isOpen_Ioi (Set.mem_Ioi.mpr hv') (fun w hw => by
            rw [Real.smoothTransition.one_of_one_le (le_of_lt hw),
              Real.smoothTransition.one_of_one_le (le_of_lt hv')]) k hkpos v
            (Set.mem_Ioi.mpr hv')
      rw [hzero, abs_zero]
      exact le_trans zero_le_one (le_max_right _ _)

/-! ## 4. The degenerate scale `n = 0` -/

/-- All the `D_θ`-iterates of the zero function vanish. -/
theorem cab_DthIter_zero_fun (a : ℕ) : Work.Spaces.DthIter a (0 : ℝ → ℝ → ℝ) = 0 := by
  induction a with
  | zero => rfl
  | succ a ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth, Pi.zero_apply]
      rw [deriv_const, mul_zero]

/-- At scale `0` the angular cut-off vanishes identically. -/
theorem cab_zetaR_zero (z θ : ℝ) : zetaR 0 θ = 0 := by
  have h1 : (↑(0 : ℕ) : ℝ) * θ - 1 ≤ 0 := by norm_num
  have h2 : (↑(0 : ℕ) : ℝ) * (Real.pi / 2 - θ) - 1 ≤ 0 := by norm_num
  simp only [zetaR, cut01]
  rw [Real.smoothTransition.zero_of_nonpos h1, Real.smoothTransition.zero_of_nonpos h2, zero_mul]

/-! ## 5. The main statement -/

theorem estZetaBound : ∃ L : ℕ → ℝ, (∀ a : ℕ, 0 ≤ L a) ∧
    ∀ (n a : ℕ) (z θ : ℝ),
      |Work.Spaces.DthIter a (fun _ θ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ) z θ| ≤ L a := by
  obtain ⟨B, hBnn, hB⟩ := exists_iteratedDeriv_smoothTransition_bound
  set M : ℕ → ℝ := fun m => 4 * 2 ^ m with hMdef
  have hMnn : ∀ m : ℕ, 0 ≤ M m := fun m => by rw [hMdef]; positivity
  have hMbd : ∀ (lam : ℝ), 1 ≤ lam → ∀ m : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv m (rhoM lam) u| ≤ M m := fun lam hlam m u hu => by
    rw [hMdef]; exact cab_iteratedDeriv_rhoM_bound_all hlam m hu
  have heng : ∀ (lam : ℝ) (hlam : 1 ≤ lam) (k : ℕ) (v : ℝ),
      |Eiter k (rhoM lam) Real.smoothTransition v| ≤ max (Cbnd M B k 0) 1 := fun lam hlam k v =>
    cab_eiter_explicit_bound hMnn hBnn (contDiff_rhoM lam) (hMbd lam hlam) hB k v
  have heng' : ∀ (lam : ℝ) (hlam : 1 ≤ lam) (k : ℕ) (v : ℝ),
      |Eiter k (fun u => -(rhoM lam u)) Real.smoothTransition v| ≤ max (Cbnd M B k 0) 1 :=
    fun lam hlam k v => cab_eiter_explicit_bound hMnn hBnn
      (fun n => (contDiff_rhoM lam n).neg) (fun m u hu => by
        change |iteratedDeriv m (-(rhoM lam)) u| ≤ M m
        rw [iteratedDeriv_neg, abs_neg]; exact hMbd lam hlam m u hu) hB k v
  set K : ℕ → ℝ := fun c => max (Cbnd M B c 0) 1 with hKdef
  have hKnn : ∀ c : ℕ, 0 ≤ K c := fun c => le_trans zero_le_one (le_max_right _ _)
  have hLnn : ∀ a : ℕ, 0 ≤ 1 + 2 ^ a * (∑ c ∈ Finset.range (a + 1), K c) ^ 2 := fun a => by
    have h : (0 : ℝ) ≤ 2 ^ a * (∑ c ∈ Finset.range (a + 1), K c) ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    linarith
  refine ⟨fun a => 1 + 2 ^ a * (∑ c ∈ Finset.range (a + 1), K c) ^ 2, hLnn, ?_⟩
  intro n a z θ
  have hL : (1 : ℝ) ≤ 1 + 2 ^ a * (∑ c ∈ Finset.range (a + 1), K c) ^ 2 := by
    have h : (0 : ℝ) ≤ 2 ^ a * (∑ c ∈ Finset.range (a + 1), K c) ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    linarith
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hz0 : (fun _ θ : ℝ => zetaR 0 θ) = (0 : ℝ → ℝ → ℝ) := by
      funext z θ; exact cab_zetaR_zero z θ
    rw [hz0, cab_DthIter_zero_fun a]
    simp only [Pi.zero_apply, abs_zero]
    linarith
  · set lam : ℝ := (n : ℝ) with hlamdef
    have hlam1 : 1 ≤ lam := by rw [hlamdef]; exact_mod_cast hnpos
    have hlamne : lam ≠ 0 := by linarith
    set u : ℝ → ℝ := fun θ' : ℝ => Real.smoothTransition (lam * θ' + (-1)) with hudef
    set v : ℝ → ℝ := fun θ' : ℝ =>
      Real.smoothTransition ((-lam) * θ' + (lam * (Real.pi / 2) - 1)) with hvdef
    have hfun : (fun θ' : ℝ => zetaR n θ') = u * v := by
      funext θ'
      have h1 : (n : ℝ) * θ' - 1 = lam * θ' + (-1) := by rw [← hlamdef]; ring
      have h2 : (n : ℝ) * (Real.pi / 2 - θ') - 1 = (-lam) * θ' + (lam * (Real.pi / 2) - 1) := by
        rw [← hlamdef]; ring
      rw [hudef, hvdef]
      simp only [zetaR, cut01, Pi.mul_apply, h1, h2]
    have hu : ∀ m : ℕ, ContDiff ℝ m u := by
      intro m; rw [hudef]; exact (contDiff_smoothTransition m).comp (contDiff_affine lam (-1) m)
    have hv : ∀ m : ℕ, ContDiff ℝ m v := by
      intro m; rw [hvdef]
      exact (contDiff_smoothTransition m).comp (contDiff_affine (-lam) _ m)
    have hub : ∀ b : ℕ, |Work.Spaces.Lop^[b] u θ| ≤ K b := by
      intro b
      rw [hudef, Lop_iter_affine_st lam (-1) hlamne b θ, coef_affine_eq_rhoM lam]
      exact heng lam hlam1 b (lam * θ + (-1))
    have hvb : ∀ c : ℕ, |Work.Spaces.Lop^[c] v θ| ≤ K c := by
      intro c
      rw [hvdef, Lop_iter_affine_st (-lam) (lam * (Real.pi / 2) - 1) (by simpa using hlamne) c θ,
        coef_affine_eq_neg_rhoM lam hlamne]
      exact heng' lam hlam1 c ((-lam) * θ + (lam * (Real.pi / 2) - 1))
    rw [congrFun (Work.Spaces.DthIter_eq_iterate_Lop a (fun _ θ' : ℝ => zetaR n θ') z) θ, hfun,
      Lop_iter_mul hu hv a θ]
    rw [show (fun a : ℕ => 1 + 2 ^ a * (∑ c ∈ Finset.range (a + 1), K c) ^ 2) a
        = 1 + 2 ^ a * (∑ c ∈ Finset.range (a + 1), K c) ^ 2 from rfl]
    set S : ℝ := ∑ c ∈ Finset.range (a + 1), K c with hSdef
    have hSnn : 0 ≤ S := by rw [hSdef]; exact Finset.sum_nonneg (fun c _ => hKnn c)
    calc |∑ b ∈ Finset.range (a + 1), (a.choose b : ℝ) *
            (Work.Spaces.Lop^[b] u θ * Work.Spaces.Lop^[a - b] v θ)|
        ≤ ∑ b ∈ Finset.range (a + 1), |(a.choose b : ℝ) *
            (Work.Spaces.Lop^[b] u θ * Work.Spaces.Lop^[a - b] v θ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b ∈ Finset.range (a + 1), (a.choose b : ℝ) * (S * S) := by
          apply Finset.sum_le_sum
          intro b hb
          have hb' : b ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
          have hKb : K b ≤ S :=
            Finset.single_le_sum (fun c _ => hKnn c) (Finset.mem_range.mpr (by omega))
          have hKab : K (a - b) ≤ S :=
            Finset.single_le_sum (fun c _ => hKnn c) (Finset.mem_range.mpr (by omega))
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (a.choose b)), abs_mul]
          refine le_trans (mul_le_mul_of_nonneg_left
            (mul_le_mul (hub b) (hvb (a - b)) (abs_nonneg _) (hKnn b)) (Nat.cast_nonneg _)) ?_
          exact mul_le_mul_of_nonneg_left (mul_le_mul hKb hKab (hKnn _) hSnn) (Nat.cast_nonneg _)
      _ = (∑ b ∈ Finset.range (a + 1), (a.choose b : ℝ)) * (S * S) :=
          (Finset.sum_mul (Finset.range (a + 1)) (fun b => (a.choose b : ℝ)) (S * S)).symm
      _ = (2 : ℝ) ^ a * (S * S) := by
          rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      _ = (2 : ℝ) ^ a * S ^ 2 := by ring
      _ ≤ 1 + 2 ^ a * S ^ 2 := by linarith

end Work.FTS.PhiStar.Honesty.CptApp.EstAux
