import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.OpenPkg.l12H_field
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnLGammaT
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.RadBound

/-- **The radial slot bound for `L₁₂ f`.**

For a datum `f` of the open-quadrant class (`SmoothOpen f`, `HkMem α 4 f`) with vanishing zero
mode `L₁₂(f)(0) = 0`, the sum of the weighted squares of the first five `z∂_z`-iterates of the
radial function `L₁₂(f)` is integrable on `Iz = [0,∞)` and its integral is controlled by the
`ℋ⁴`-energy `HkSq α 4 f`, with a constant independent of `α ∈ (0,1]` and of `f`.

This is the localisation of the `k = 0` part of Elgindi's Prop. `L12H` (tex 1276--1290) to a
single radial slot; it is the open-quadrant (`SmoothOpen`) version of the estimate proved inside
`Work.FTS.OpenPkg.l12H_field` (that file bounds `Xn α (L₁₂ f)`; the underlying sum bound is
re-derived here because the consumer needs the radial sum itself rather than the norm).  The
proof is the same: the `k = 0` slot is the weighted Hardy inequality `∫ (L₁₂ f)² w² ≤ 107 ∫ (Qang f 0)² w²`
and, for `1 ≤ c ≤ 4`, the iterate is the angular moment `D_z^c (L₁₂ f) = -Qang f (c-1)`
(`l12_open_bundle`), whose weighted square integral is bounded by
`(∫_θ K_θ²)·HkSq α 4 f` (`Qang_sq_w_sq_integral_open`).  The constant is `111·∫_θ K_θ² + 1`. -/
theorem L12fSlotLe :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Construction.L12 f 0 = 0 →
      MeasureTheory.IntegrableOn (fun z : ℝ =>
          ∑ c ∈ Finset.range 5, (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ c ∈ Finset.range 5,
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α 4 f := by
  -- the universal constant `∫_θ K_θ²` (independent of `α`)
  set AK : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hAKdef
  have hAKnn : 0 ≤ AK := by
    rw [hAKdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  refine ⟨111 * AK + 1, by linarith, ?_⟩
  intro α hα f hsm hmem h0
  have hαpos : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- the two definitions of `L₁₂` agree, so the hypothesis transfers
  have h0e : Work.Elliptic.L12 f 0 = 0 := by
    rw [← Work.FTS.H2.constructionL12_eq_ellipticL12 f]
    exact h0
  obtain ⟨hgen, hInt0, hBnd0⟩ :=
    Work.FTS.OpenPkg.l12_open_bundle α f hαpos hα1 hsm hmem h0e
  set u : ℝ → ℝ := fun z => Work.Elliptic.L12 f z with hudef
  have hgen' : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) u z = - Work.Elliptic.Qang f k z := by
    intro k hk z hz
    rw [hudef]
    exact hgen k hk z hz
  -- ## the a.e. transfer `D_z^i (L₁₂ f) = -Qang f (i-1)` on `Iz`, `1 ≤ i ≤ 4`
  have htrans : ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Elliptic.Qang f (i - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2
          = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro i hi hi4
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with z hz0 hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
    have hsub : i - 1 ≤ 3 := by omega
    have key : Work.Elliptic.DzdIter i u z = - Work.Elliptic.Qang f (i - 1) z := by
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
      ≤ 107 * (AK * Work.Spaces.HkSq α 4 f) := by
    have hb : (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang f 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      simpa only [hudef, Work.Elliptic.DzdIter_zero] using hBnd0
    have hQ := (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open hαpos hα1 hsm hmem
      (i := 0) (by norm_num)).2
    rw [← hAKdef] at hQ
    exact le_trans hb (mul_le_mul_of_nonneg_left hQ (by norm_num))
  have hBndI : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ AK * Work.Spaces.HkSq α 4 f := by
    intro i hi hi4
    rw [hAKdef, ← MeasureTheory.integral_congr_ae (htrans i hi hi4)]
    exact (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open hαpos hα1 hsm hmem
      (i := i - 1) (by omega)).2
  -- ## the sum of the slots
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 111 * (AK * Work.Spaces.HkSq α 4 f) := by
    rw [MeasureTheory.integral_finsetSum (Finset.range 5) hsum_int,
      Finset.sum_range_succ']
    have h4 : (∑ i ∈ Finset.range 4, (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter (i + 1) u z) ^ 2 * (Work.Spaces.w z) ^ 2))
        ≤ ∑ _i ∈ Finset.range 4, AK * Work.Spaces.HkSq α 4 f :=
      Finset.sum_le_sum fun i hi => by
        rw [Finset.mem_range] at hi
        exact hBndI (i + 1) (by omega) (by omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h4
    refine le_trans (add_le_add h4 hBnd0') (le_of_eq ?_)
    ring
  -- ## integrability of the whole `z`-sum
  have hsumInt : MeasureTheory.IntegrableOn (fun z : ℝ => ∑ i ∈ Finset.range 5,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    MeasureTheory.integrable_finsetSum (Finset.range 5) hsum_int
  -- ## back to `Work.Coercivity.L12f`
  have hfun : Work.Coercivity.L12f f = u := by
    funext z
    have h1 : Work.Coercivity.L12f f = Work.Construction.L12 f := rfl
    rw [hudef, h1]
    exact congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 f) z
  have hcongr : (fun z : ℝ => ∑ c ∈ Finset.range 5,
        (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = (fun z : ℝ => ∑ c ∈ Finset.range 5,
        (Work.Elliptic.DzdIter c u z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    funext z
    rw [hfun]
  constructor
  · rw [hcongr]
    exact hsumInt
  · rw [hcongr]
    refine le_trans hsum_le ?_
    have hknn : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
    nlinarith

end Work.FTS.StrongEps.EpsRLX.RadBound
