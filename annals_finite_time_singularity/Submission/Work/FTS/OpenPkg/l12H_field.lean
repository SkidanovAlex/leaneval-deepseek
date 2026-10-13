/-
# `OpenPkg/l12H_field` — the `l12H` field of the primed norm interface `N4Norm'`

`L₁₂(g)(z) = ∫_z^∞ ∫_θ K(θ)·g(r,θ)/r dθ dr` is the radial function of Elgindi's
Prop. `L12H` (tex 1276): for a datum of the **open-quadrant** class
`Work.FTS.VocabO.HQo α 4 g = Work.FTS.EllipticEst.SmoothOpen g ∧ Work.Spaces.HkMem α 4 g`
with vanishing zero mode `L₁₂(g)(0) = 0`, the function `z ↦ L₁₂(g)(z)` (extended constantly in
`θ`) lies in `ℋ⁴` and its `ℋ⁴`-norm is controlled by that of `g`, with a constant independent
of `α ∈ (0,1]` and of `g`.

The delivered interior-class version is `Work.FTS.H2.L12HQ` (hypothesis
`Work.FTS.Nonlin.RegQ α 4 g`, i.e. `SmoothQuad`: `C^∞` on `z > -1`).  `HQo` does not imply
`RegQ` (the whole point of the OpenPkg migration: the real stream functions carry the
homogeneous modes `z^{2m/α}`, `C^∞` only for `z > 0`), so the estimate is re-run in the open
class.  Only the following open-quadrant inputs are needed:

* `Work.FTS.OpenPkg.QangOpen.QangDiff_open` — continuity of the angular moments
  `Qang g j` and `z·(Qang g j)' = Qang g (j+1)` on `z > 0`, hence continuity of the density
  `L₁₂dens g = Qang g 0 / z` (`Work.Elliptic.L12dens_eq_Qang_div`);
* `Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open` — Cauchy–Schwarz in `θ` against
  `K ∈ L²(Iθ)`: `∫_z (Qang g i)² w² ≤ (∫_θ K²)·HkSq α 4 g`;
* `Work.FTS.OpenPkg.l12_open_bundle` — the analytic facts about `L₁₂(g)` itself in the open
  class: differentiability with derivative `-L₁₂dens g` on `(0,∞)`, hence (with the vanishing
  zero mode) the tower `D_z^{k+1} L₁₂(g) = -Qang g k` for `k ≤ 3`, and the weighted Hardy
  inequality of `Work.FTS.H2.L12k0Q` for the `k = 0` slot,
  `∫_z (L₁₂ g)² w² ≤ 107 ∫_z (Qang g 0)² w²`.

Since a function of `z` alone has no angular derivatives, only the pure `D_z`-summands of
`HkIntegrand α 4 (z ↦ L₁₂(g)(z))` survive (`Work.FTS.H2.HkIntegrand_rad'`) and
`HkSq α 4 (z ↦ u z) = (∫_z ∑_{i≤4} (D_z^i u)² w²)·∫_θ sin(2θ)^{-η}`
(`Work.Elliptic.HkSq_rad`).  The summands are transferred to the angular moments slot by slot
(almost everywhere in `z`, the difference being only the null point `z = 0`: `D_z^{i+1} L₁₂(g)
= -Qang g i` for `z > 0`), each bounded by `(∫_θ K²)·HkSq α 4 g`, except the `i = 0` slot
which carries the extra Hardy factor `107`.  This gives

  `HkSq α 4 (z ↦ L₁₂(g)(z)) ≤ 111·(∫_θ K²)·(∫_θ sin(2θ)^{-η})·HkSq α 4 g`

and hence the norm bound with `C = √(111·(∫_θ K²)·(∫_θ sin(2θ)^{-η})) + 1`.  The hypothesis
`L₁₂(g)(0) = 0` is used exactly once, in the Hardy inequality of the `k = 0` slot.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.OpenPkg.l12_open_bundle

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

set_option linter.unusedVariables false

theorem l12H_field :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 4 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
        ≤ C * Work.FTS.Nonlin.Xn α g := by
  -- the two universal constants `∫_θ K²` and `∫_θ sin(2θ)^{-η}`
  set AK : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hAKdef
  set Cθ : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hCθdef
  have hAKnn : 0 ≤ AK := by
    rw [hAKdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hCθnn : 0 ≤ Cθ := by
    rw [hCθdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (Work.Elliptic.sin_two_nonneg_of_mem hθ) _)
  refine ⟨Real.sqrt (111 * AK * Cθ) + 1, ?_, ?_⟩
  · have h := Real.sqrt_nonneg (111 * AK * Cθ)
    linarith
  intro α hαpos hα1 g hg h0
  obtain ⟨hsm, hmem⟩ := hg
  have h0e : Work.Elliptic.L12 g 0 = 0 := by
    rw [← Work.FTS.H2.constructionL12_eq_ellipticL12 g]
    exact h0
  obtain ⟨hgen, hInt0, hBnd0⟩ := l12_open_bundle α g hαpos hα1 hsm hmem h0e
  set u : ℝ → ℝ := fun z => Work.Elliptic.L12 g z with hudef
  have hgen' : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) u z = - Work.Elliptic.Qang g k z := by
    intro k hk z hz
    rw [hudef]
    exact hgen k hk z hz
  -- ## the a.e. transfer `D_z^i (L₁₂ g) = -Qang g (i-1)` on `Iz`, `1 ≤ i ≤ 4`
  have htrans : ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Elliptic.Qang g (i - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2
          = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro i hi hi4
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with z hz0 hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
    have hsub : i - 1 ≤ 3 := by omega
    have key : Work.Elliptic.DzdIter i u z = - Work.Elliptic.Qang g (i - 1) z := by
      have h := hgen' (i - 1) hsub z hzpos
      rwa [show i - 1 + 1 = i by omega] at h
    rw [key, neg_sq]
  -- ## integrability of every weighted slot
  have hInt : ∀ i : ℕ, i ≤ 4 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    intro i hi4
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      simpa only [hudef, Work.Elliptic.DzdIter_zero] using hInt0
    · exact (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open hαpos hα1 hsm hmem
        (i := i - 1) (by omega)).1.congr (htrans i h hi4)
  have hsum_int : ∀ i ∈ Finset.range 5, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => hInt i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  -- ## the bounds of the individual slots
  have hBnd0' : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 107 * (AK * Work.Spaces.HkSq α 4 g) := by
    have hb : (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      simpa only [hudef, Work.Elliptic.DzdIter_zero] using hBnd0
    have hQ := (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open hαpos hα1 hsm hmem
      (i := 0) (by norm_num)).2
    rw [← hAKdef] at hQ
    exact le_trans hb (mul_le_mul_of_nonneg_left hQ (by norm_num))
  have hBndI : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ AK * Work.Spaces.HkSq α 4 g := by
    intro i hi hi4
    rw [hAKdef, ← MeasureTheory.integral_congr_ae (htrans i hi hi4)]
    exact (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open hαpos hα1 hsm hmem
      (i := i - 1) (by omega)).2
  -- ## the sum of the slots
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 111 * (AK * Work.Spaces.HkSq α 4 g) := by
    rw [MeasureTheory.integral_finsetSum (Finset.range 5) hsum_int,
      Finset.sum_range_succ']
    have h4 : (∑ i ∈ Finset.range 4, (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter (i + 1) u z) ^ 2 * (Work.Spaces.w z) ^ 2))
        ≤ ∑ _i ∈ Finset.range 4, AK * Work.Spaces.HkSq α 4 g :=
      Finset.sum_le_sum fun i hi => by
        rw [Finset.mem_range] at hi
        exact hBndI (i + 1) (by omega) (by omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h4
    refine le_trans (add_le_add h4 hBnd0') (le_of_eq ?_)
    ring
  -- ## the energy
  have hHkSq : Work.Spaces.HkSq α 4 (fun z θ => u z)
      = (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
          (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) * Cθ := by
    rw [Work.Elliptic.HkSq_rad, hCθdef]
  have hbound : Work.Spaces.HkSq α 4 (fun z θ => u z)
      ≤ (111 * AK * Cθ) * Work.Spaces.HkSq α 4 g := by
    rw [hHkSq]
    refine le_trans (mul_le_mul_of_nonneg_right hsum_le hCθnn) (le_of_eq ?_)
    ring
  have hXng : 0 ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
  have hXn : Work.FTS.Nonlin.Xn α (fun z θ => u z)
      ≤ Real.sqrt (111 * AK * Cθ) * Work.FTS.Nonlin.Xn α g := by
    have h111 : 0 ≤ 111 * AK * Cθ := by nlinarith
    calc Work.FTS.Nonlin.Xn α (fun z θ => u z)
        = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => u z)) := rfl
      _ ≤ Real.sqrt ((111 * AK * Cθ) * Work.Spaces.HkSq α 4 g) := Real.sqrt_le_sqrt hbound
      _ = Real.sqrt (111 * AK * Cθ) * Work.FTS.Nonlin.Xn α g := by
          rw [Real.sqrt_mul h111]
          rfl
  -- ## membership in `ℋ⁴`
  have hsinI : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have hHkMem : Work.Spaces.HkMem α 4 (fun z θ => u z) := by
    constructor
    · intro z _
      refine MeasureTheory.Integrable.congr (f := fun θ =>
        (∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ?_ ?_
      · exact hsinI.const_mul _
      · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => (Work.FTS.H2.HkIntegrand_rad' α 4 u z hθ).symm)
    · refine MeasureTheory.Integrable.congr (f := fun z =>
        (∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * Cθ) ?_ ?_
      · exact (MeasureTheory.integrable_finsetSum (Finset.range 5) hsum_int).mul_const Cθ
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_)
        simp only [Work.Spaces.Iθ, hCθdef]
        rw [setIntegral_congr_fun (f := fun θ => Work.Spaces.HkIntegrand α 4 (fun z θ => u z) z θ)
          (g := fun θ => (∑ i ∈ Finset.range 5,
              (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          measurableSet_Icc (fun θ hθ => Work.FTS.H2.HkIntegrand_rad' α 4 u z hθ)]
        rw [MeasureTheory.integral_const_mul]
  -- ## back to `Work.Construction.L12`
  have hfun : (fun z (_ : ℝ) => Work.Construction.L12 g z) = (fun z (_ : ℝ) => u z) := by
    funext z θ
    rw [hudef]
    exact congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 g) z
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hHkMem
  · rw [hfun]
    exact le_trans hXn
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hXng)

end Work.FTS.OpenPkg
