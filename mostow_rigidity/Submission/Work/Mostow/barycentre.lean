import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.BusemannRay
import Submission.Work.Mostow.BaryMidpoint
import Submission.Work.Mostow.BaryContinuity
import Submission.Work.Mostow.BaryCoercive
import Submission.Work.Mostow.BaryEquality

/-! Area T4 — `BaryProp n`: barycentre of an atomless probability measure on the boundary sphere. -/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Real ENNReal

noncomputable section

variable {n : ℕ}

theorem integrable_busemann (ν : Measure (E n)) (hν : IsProbabilityMeasure ν)
    (hsupp : ν (Sph n)ᶜ = 0) (u : E n) : Integrable (fun ξ => busemann ξ u) ν := by
  refine Integrable.of_bound (measurable_busemann u).aestronglyMeasurable (hdist 0 u) ?_
  have hae : ∀ᵐ ξ ∂ν, ξ ∈ Sph n := by
    rw [MeasureTheory.ae_iff]
    exact hsupp
  filter_upwards [hae] with ξ hξ
  simpa [Real.norm_eq_abs] using abs_busemann_le_hdist_zero ξ hξ u

/-- a finite set has measure zero for an atomless measure -/
theorem measure_finset_zero (ν : Measure (E n)) (hatom : ∀ ξ : E n, ν {ξ} = 0) (s : Finset (E n)) :
    ν (s : Set (E n)) = 0 := by
  haveI : NullSingletonClass ν := ⟨hatom⟩
  exact (Finset.finite_toSet s).measure_zero ν

/-- convexity of the Busemann function at the midpoint, from the midpoint identity and the
1-Lipschitz bound. -/
theorem convex_midpoint {y z m : E n}
    (hm : ∀ η ∈ Sph n, tpart m - inner ℝ m η =
      ((tpart y - inner ℝ y η) + (tpart z - inner ℝ z η)) / (2 * Real.cosh (hdist y z / 2)))
    (hL : ∀ η ∈ Sph n, |busemann η y - busemann η z| ≤ hdist y z)
    (ξ : E n) (hξ : ξ ∈ Sph n) :
    2 * busemann ξ m ≤ busemann ξ y + busemann ξ z := by
  set d := hdist y z with hd
  set C := Real.cosh d with hC
  set S := Real.sinh d with hS
  set Ay := tpart y - inner ℝ y ξ with hAy
  set Az := tpart z - inner ℝ z ξ with hAz
  set r := Ay / Az with hr
  have hAypos : 0 < Ay := busemann_arg_pos ξ hξ y
  have hAzpos : 0 < Az := busemann_arg_pos ξ hξ z
  have hAye : Real.exp (busemann ξ y) = Ay := exp_busemann ξ hξ y
  have hAze : Real.exp (busemann ξ z) = Az := exp_busemann ξ hξ z
  have hdnn : 0 ≤ d := hdist_nonneg y z
  have hSnn : 0 ≤ S := Real.sinh_nonneg_iff.mpr hdnn
  have hcs : C ^ 2 - S ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq d
  have he1 : Real.exp d = C + S := by rw [hC, hS, Real.cosh_eq, Real.sinh_eq]; ring
  have he2 : Real.exp (-d) = C - S := by rw [hC, hS, Real.cosh_eq, Real.sinh_eq]; ring
  have hle : busemann ξ y - busemann ξ z ≤ d := (abs_le.mp (hL ξ hξ)).2
  have hge : -d ≤ busemann ξ y - busemann ξ z := (abs_le.mp (hL ξ hξ)).1
  have hr1 : r ≤ Real.exp d := by
    have h : Real.exp (busemann ξ y - busemann ξ z) ≤ Real.exp d := Real.exp_le_exp.mpr hle
    rw [Real.exp_sub, hAye, hAze] at h
    simpa [hr] using h
  have hr2 : Real.exp (-d) ≤ r := by
    have h : Real.exp (-d) ≤ Real.exp (busemann ξ y - busemann ξ z) := Real.exp_le_exp.mpr hge
    rw [Real.exp_sub, hAye, hAze] at h
    simpa [hr] using h
  have hrpos : 0 < r := div_pos hAypos hAzpos
  have hkey : (r + 1) ^ 2 ≤ 4 * Real.cosh (d / 2) ^ 2 * r := by
    have hhalf : 4 * Real.cosh (d / 2) ^ 2 = 2 * (1 + C) := by
      have h := Real.cosh_two_mul (d / 2)
      rw [show 2 * (d / 2) = d from by ring, Real.sinh_sq, ← hC] at h
      linarith
    have hs1 : r - C ≤ S := by rw [he1] at hr1; linarith
    have hs2 : -S ≤ r - C := by rw [he2] at hr2; linarith
    have h3 : (r - C) ^ 2 ≤ S ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hSnn]
      exact abs_le.mpr ⟨hs2, hs1⟩
    rw [hhalf]
    nlinarith [h3, hcs]
  have hAzr : Ay = r * Az := by rw [hr]; field_simp
  have hmain : (Ay + Az) ^ 2 ≤ 4 * Real.cosh (d / 2) ^ 2 * (Ay * Az) := by
    rw [hAzr, show (r * Az + Az) ^ 2 = (r + 1) ^ 2 * Az ^ 2 by ring,
      show 4 * Real.cosh (d / 2) ^ 2 * (r * Az * Az) = 4 * Real.cosh (d / 2) ^ 2 * r * Az ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hkey (sq_nonneg Az)
  have hmξ : tpart m - inner ℝ m ξ = (Ay + Az) / (2 * Real.cosh (d / 2)) := by
    have := hm ξ hξ
    simpa [hAy, hAz, hd] using this
  have hexp2 : Real.exp (2 * busemann ξ m) = (tpart m - inner ℝ m ξ) ^ 2 := by
    rw [show (2 : ℝ) * busemann ξ m = busemann ξ m + busemann ξ m from by ring, Real.exp_add,
      exp_busemann ξ hξ m]
    ring
  have hfin : Real.exp (2 * busemann ξ m) ≤ Real.exp (busemann ξ y + busemann ξ z) := by
    rw [hexp2, hmξ, Real.exp_add, hAye, hAze, div_pow]
    rw [div_le_iff₀ (by positivity : 0 < (2 * Real.cosh (d / 2)) ^ 2)]
    nlinarith [hmain]
  linarith [Real.exp_le_exp.mp hfin]

end

end Work.Mostow

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Real ENNReal

noncomputable section

variable {n : ℕ}

/-- key identity: the Minkowski pairing with the null vector `(e^d z - y, e^d tpart z - tpart y)` -/
theorem exp_hdist_mul_tpart_sub_sq (y z : E n) :
    (Real.exp (hdist y z) * tpart z - tpart y) ^ 2 = ‖Real.exp (hdist y z) • z - y‖ ^ 2 := by
  set e := Real.exp (hdist y z) with he
  have hepos : 0 < e := by rw [he]; exact Real.exp_pos _
  have hcosh : Real.cosh (hdist y z) = (e + e⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg, ← he]
  have h2 : 2 * e * Real.cosh (hdist y z) = e ^ 2 + 1 := by
    rw [hcosh, show 2 * e * ((e + e⁻¹) / 2) = e * (e + e⁻¹) by ring, mul_add,
      mul_inv_cancel₀ (ne_of_gt hepos)]
    ring
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos hepos, mul_pow,
    real_inner_smul_left]
  nlinarith [h2, cosh_hdist y z, tpart_sq y, tpart_sq z, real_inner_comm y z]

theorem exp_smul_sub_ne_zero (y z : E n) (hd : 0 < hdist y z) :
    Real.exp (hdist y z) • z - y ≠ 0 := by
  intro h
  have h0 : Real.exp (hdist y z) * tpart z - tpart y = 0 := by
    have h2 := exp_hdist_mul_tpart_sub_sq y z
    rw [h, norm_zero] at h2
    norm_num at h2
    exact h2
  have h3 : Real.exp (hdist y z) * tpart z = tpart y := sub_eq_zero.mp h0
  have hz : (Real.exp (hdist y z)) ^ 2 * tpart z ^ 2 = tpart y ^ 2 := by
    rw [← h3]; ring
  have hy : y = Real.exp (hdist y z) • z := (sub_eq_zero.mp h).symm
  have hnorm : ‖y‖ ^ 2 = (Real.exp (hdist y z)) ^ 2 * ‖z‖ ^ 2 := by
    conv_lhs => rw [hy]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  rw [tpart_sq y, tpart_sq z, hnorm] at hz
  have he2 : (Real.exp (hdist y z)) ^ 2 = 1 := by linarith
  have he1 : Real.exp (hdist y z) = 1 := by nlinarith [he2, Real.exp_pos (hdist y z)]
  have hd0 : hdist y z = 0 := Real.exp_injective (by rw [he1, Real.exp_zero])
  linarith

/-- Busemann functions are 1-Lipschitz, from the ray characterisation -/
theorem busemann_abs_sub_le (htri : ∀ u v w : E n, hdist u w ≤ hdist u v + hdist v w)
    (hsym : ∀ u v : E n, hdist u v = hdist v u)
    (ξ : E n) (hξ : ξ ∈ Sph n) (u v : E n) : |busemann ξ u - busemann ξ v| ≤ hdist u v := by
  have h1 := BusemannRay n ξ hξ u
  have h2 := BusemannRay n ξ hξ v
  have h3 : Filter.Tendsto (fun t : ℝ =>
      |(hdist u (Real.sinh t • ξ) - t) - (hdist v (Real.sinh t • ξ) - t)|) Filter.atTop
      (nhds |busemann ξ u - busemann ξ v|) := (h1.sub h2).abs
  refine le_of_tendsto h3 (Filter.Eventually.of_forall fun t => ?_)
  have hupper : hdist u (Real.sinh t • ξ) - hdist v (Real.sinh t • ξ) ≤ hdist u v := by
    have := htri u v (Real.sinh t • ξ); linarith
  have hlower : -(hdist u v) ≤ hdist u (Real.sinh t • ξ) - hdist v (Real.sinh t • ξ) := by
    have := htri v u (Real.sinh t • ξ); rw [hsym v u] at this; linarith
  rw [show (hdist u (Real.sinh t • ξ) - t) - (hdist v (Real.sinh t • ξ) - t) =
    hdist u (Real.sinh t • ξ) - hdist v (Real.sinh t • ξ) from by ring]
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- a continuous coercive function on `E n` attains its minimum -/
theorem exists_minimiser (f : E n → ℝ) (hcont : Continuous f)
    (hcoer : ∃ R : ℝ, ∀ y : E n, R ≤ hdist 0 y → f 0 < f y)
    (hball : ∀ (u : E n) (r : ℝ), IsCompact {v : E n | hdist u v ≤ r}) :
    ∃ y : E n, ∀ z, f y ≤ f z := by
  obtain ⟨R, hR⟩ := hcoer
  have hne : ({y : E n | hdist 0 y ≤ max R 0}).Nonempty :=
    ⟨0, by simp only [Set.mem_setOf_eq]; rw [hdist_self]; exact le_max_right R 0⟩
  obtain ⟨y₀, -, hy₀min⟩ := (hball 0 (max R 0)).exists_isMinOn hne hcont.continuousOn
  refine ⟨y₀, fun z => ?_⟩
  by_cases hz : hdist 0 z ≤ max R 0
  · exact hy₀min hz
  · push_neg at hz
    have h1 : f 0 < f z := hR z (le_trans (le_max_left R 0) hz.le)
    have h2 : f y₀ ≤ f 0 := hy₀min (by simp only [Set.mem_setOf_eq]; rw [hdist_self]; exact le_max_right R 0)
    linarith

end

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Real ENNReal

noncomputable section

variable {n : ℕ}

/-- uniqueness of the minimiser of `baryFun ν` for an atomless probability measure on the sphere:
the convexity of the Busemann function at the midpoint, together with the fact that equality can
only happen at two points, contradicts atomlessness. -/
theorem minimiser_unique (ν : Measure (E n)) (hν : IsProbabilityMeasure ν) (hsupp : ν (Sph n)ᶜ = 0)
    (hatom : ∀ ξ : E n, ν {ξ} = 0)
    (htri : ∀ u v w : E n, hdist u w ≤ hdist u v + hdist v w)
    (hsym : ∀ u v : E n, hdist u v = hdist v u)
    (hmid_id : ∀ (y z : E n), y ≠ z → ∀ η ∈ Sph n, tpart (hmid y z) - inner ℝ (hmid y z) η =
      ((tpart y - inner ℝ y η) + (tpart z - inner ℝ z η)) / (2 * Real.cosh (hdist y z / 2)))
    (hε : ∀ (y z m : E n), y ≠ z → (∀ η ∈ Sph n, tpart m - inner ℝ m η =
        ((tpart y - inner ℝ y η) + (tpart z - inner ℝ z η)) / (2 * Real.cosh (hdist y z / 2))) →
        ∃ s : Finset (E n),
          ∀ ξ ∈ Sph n, 2 * busemann ξ m = busemann ξ y + busemann ξ z → ξ ∈ (s : Set (E n)))
    {y z : E n} (hy : ∀ w, baryFun ν y ≤ baryFun ν w) (hz : ∀ w, baryFun ν z ≤ baryFun ν w) :
    y = z := by
  by_contra hne
  set d := hdist y z with hd
  set m := hmid y z with hm
  have hmidm : ∀ η ∈ Sph n, tpart m - inner ℝ m η =
      ((tpart y - inner ℝ y η) + (tpart z - inner ℝ z η)) / (2 * Real.cosh (d / 2)) := by
    intro η hη
    have h := hmid_id y z hne η hη
    simpa [hm, hd] using h
  have hL : ∀ η ∈ Sph n, |busemann η y - busemann η z| ≤ d := fun η hη => by
    have h := busemann_abs_sub_le htri hsym η hη y z
    simpa [hd] using h
  have hconv : ∀ η ∈ Sph n, 2 * busemann η m ≤ busemann η y + busemann η z :=
    fun η hη => convex_midpoint hmidm hL η hη
  have hae : ∀ᵐ ξ ∂ν, ξ ∈ Sph n := by rw [MeasureTheory.ae_iff]; exact hsupp
  have hintm := integrable_busemann ν hν hsupp m
  have hinty := integrable_busemann ν hν hsupp y
  have hintz := integrable_busemann ν hν hsupp z
  have hPsiint : Integrable (fun ξ => 2 * busemann ξ m - busemann ξ y - busemann ξ z) ν :=
    ((hintm.const_mul 2).sub hinty).sub hintz
  have hPsineq : ∀ᵐ ξ ∂ν, 2 * busemann ξ m - busemann ξ y - busemann ξ z ≤ 0 := by
    filter_upwards [hae] with ξ hξ
    have := hconv ξ hξ
    linarith
  have hPsiInt : ∫ ξ, (2 * busemann ξ m - busemann ξ y - busemann ξ z) ∂ν
      = 2 * baryFun ν m - baryFun ν y - baryFun ν z := by
    have h1 : Integrable (fun ξ : E n => 2 * busemann ξ m) ν := hintm.const_mul 2
    have h2 : Integrable (fun ξ : E n => 2 * busemann ξ m - busemann ξ y) ν := h1.sub hinty
    calc ∫ ξ, (2 * busemann ξ m - busemann ξ y - busemann ξ z) ∂ν
        = ∫ ξ, ((fun ξ : E n => 2 * busemann ξ m - busemann ξ y) ξ
            - (fun ξ : E n => busemann ξ z) ξ) ∂ν := rfl
      _ = ∫ ξ, (2 * busemann ξ m - busemann ξ y) ∂ν - ∫ ξ, busemann ξ z ∂ν :=
            MeasureTheory.integral_sub h2 hintz
      _ = (∫ ξ, (2 * busemann ξ m) ∂ν - ∫ ξ, busemann ξ y ∂ν) - ∫ ξ, busemann ξ z ∂ν := by
            rw [MeasureTheory.integral_sub h1 hinty]
      _ = (2 * (∫ ξ, busemann ξ m ∂ν) - ∫ ξ, busemann ξ y ∂ν) - ∫ ξ, busemann ξ z ∂ν := by
            rw [MeasureTheory.integral_const_mul]
      _ = 2 * baryFun ν m - baryFun ν y - baryFun ν z := rfl
  have hInt_le : ∫ ξ, (2 * busemann ξ m - busemann ξ y - busemann ξ z) ∂ν ≤ 0 := by
    have h0 : Integrable (fun _ : E n => (0 : ℝ)) ν :=
      Integrable.of_bound aestronglyMeasurable_const 0 (Filter.Eventually.of_forall (by simp))
    have := MeasureTheory.integral_mono_ae hPsiint h0 hPsineq
    simpa using this
  have hInt_ge : 0 ≤ ∫ ξ, (2 * busemann ξ m - busemann ξ y - busemann ξ z) ∂ν := by
    rw [hPsiInt]
    have h1 : baryFun ν y ≤ baryFun ν m := hy m
    have h2 : baryFun ν z ≤ baryFun ν m := hz m
    linarith
  have hInt_zero : ∫ ξ, (2 * busemann ξ m - busemann ξ y - busemann ξ z) ∂ν = 0 :=
    le_antisymm hInt_le hInt_ge
  have hPsi_zero : (fun ξ => 2 * busemann ξ m - busemann ξ y - busemann ξ z) =ᵐ[ν] 0 := by
    have hneg : 0 ≤ᵐ[ν] (fun ξ => -(2 * busemann ξ m - busemann ξ y - busemann ξ z)) := by
      filter_upwards [hPsineq] with ξ h
      simp only [Pi.zero_apply]
      linarith
    have hzero : ∫ ξ, -(2 * busemann ξ m - busemann ξ y - busemann ξ z) ∂ν = 0 := by
      rw [MeasureTheory.integral_neg, hInt_zero, neg_zero]
    have h := (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hneg hPsiint.neg).mp hzero
    filter_upwards [h] with ξ hξ
    simp only [Pi.zero_apply] at hξ ⊢
    linarith
  set B := {ξ : E n | 2 * busemann ξ m - busemann ξ y - busemann ξ z ≠ 0} with hB
  have hbad : ν B = 0 := by
    have h := hPsi_zero
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at h
    simpa [hB] using h
  obtain ⟨s, hs⟩ := hε y z m hne hmidm
  set Z := {ξ : E n | ξ ∈ Sph n ∧ 2 * busemann ξ m - busemann ξ y - busemann ξ z = 0} with hZ
  have hZsub : Z ⊆ (s : Set (E n)) := by
    intro ξ hξ
    exact hs ξ hξ.1 (by linarith [hξ.2])
  have hSph1 : ν (Sph n) = 1 := by
    have hle : ν (Sph n) ≤ ν Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
    have hle2 : ν Set.univ ≤ ν (Sph n) + ν (Sph n)ᶜ := by
      have h := MeasureTheory.measure_union_le (μ := ν) (s := Sph n) (t := (Sph n)ᶜ)
      rwa [Set.union_compl_self] at h
    rw [hsupp, add_zero, MeasureTheory.IsProbabilityMeasure.measure_univ] at hle2
    rw [MeasureTheory.IsProbabilityMeasure.measure_univ] at hle
    exact le_antisymm hle hle2
  have hZ1 : ν Z = 1 := by
    have hsub : Sph n ⊆ Z ∪ B := by
      intro ξ hξ
      by_cases h : 2 * busemann ξ m - busemann ξ y - busemann ξ z = 0
      · exact Or.inl ⟨hξ, h⟩
      · exact Or.inr (by simpa [hB] using h)
    have h1 : ν (Sph n) ≤ ν (Z ∪ B) := MeasureTheory.measure_mono hsub
    have h2 : ν (Z ∪ B) ≤ ν Z + ν B := MeasureTheory.measure_union_le _ _
    have h4 : ν Z ≤ 1 := by
      rw [← MeasureTheory.IsProbabilityMeasure.measure_univ (μ := ν)]
      exact MeasureTheory.measure_mono (Set.subset_univ _)
    have h3 : (1 : ENNReal) ≤ ν Z := by
      have h01 : (1 : ENNReal) = ν (Sph n) := hSph1.symm
      have h34 : ν Z + ν B = ν Z := by rw [hbad, add_zero]
      exact h01.trans_le (h1.trans (h2.trans_eq h34))
    exact le_antisymm h4 h3
  have hszero : ν (s : Set (E n)) = 0 := measure_finset_zero ν hatom s
  have hcontra : ν Z ≤ 0 := by rw [← hszero]; exact MeasureTheory.measure_mono hZsub
  rw [hZ1] at hcontra
  exact absurd hcontra (by simp)

end



open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Real ENNReal

noncomputable section

variable {n : ℕ}

/-- the equality case of the midpoint convexity produces an explicit finite set -/
theorem baryEqualityFinset (n : ℕ) (y z m : E n) (hyz : y ≠ z)
    (hm : ∀ η ∈ Sph n, tpart m - inner ℝ m η =
      ((tpart y - inner ℝ y η) + (tpart z - inner ℝ z η)) / (2 * Real.cosh (hdist y z / 2))) :
    ∃ s : Finset (E n),
      ∀ ξ ∈ Sph n, 2 * busemann ξ m = busemann ξ y + busemann ξ z → ξ ∈ (s : Set (E n)) := by
  refine ⟨{‖Real.exp (hdist y z) • z - y‖⁻¹ • (Real.exp (hdist y z) • z - y),
      -(‖Real.exp (hdist y z) • z - y‖⁻¹ • (Real.exp (hdist y z) • z - y)),
      ‖Real.exp (hdist y z) • y - z‖⁻¹ • (Real.exp (hdist y z) • y - z),
      -(‖Real.exp (hdist y z) • y - z‖⁻¹ • (Real.exp (hdist y z) • y - z))}, ?_⟩
  intro ξ hξ h
  have hW : Real.exp (hdist y z) • z - y ≠ 0 :=
    (Work.Mostow.BaryEq.exp_smul_sub_ne_zero y z).mpr hyz
  rcases BaryEquality n y z m hyz hW hm ξ hξ h with h1 | h1 | h1 | h1 <;> simp [h1]

/-- `bar ν` is a minimiser and the minimiser is unique -/
theorem bary_min (hA : POActionProp n) (hI : HypIsometryProp n)
    (ν : Measure (E n)) (hν : IsProbabilityMeasure ν) (hsupp : ν (Sph n)ᶜ = 0)
    (hatom : ∀ ξ : E n, ν {ξ} = 0) :
    (∀ z, baryFun ν (bar ν) ≤ baryFun ν z) ∧
    (∀ y, (∀ z, baryFun ν y ≤ baryFun ν z) → y = bar ν) := by
  obtain ⟨-, hsym, -, htri, -, hball, -, -, -, -, -, -, -⟩ := hI
  have hcont := BaryContinuity n ν hν hsupp
  have hcoer := BaryCoercive n ν hν hsupp hatom
  have hex := exists_minimiser (baryFun ν) hcont hcoer hball
  have hbarA : ∀ z, baryFun ν (bar ν) ≤ baryFun ν z := by
    intro z
    have hbar : bar ν = hex.choose := by unfold bar; exact dif_pos hex
    rw [hbar]
    exact hex.choose_spec z
  refine ⟨hbarA, fun y hy => ?_⟩
  have hmid_id : ∀ (y z : E n), y ≠ z → ∀ η ∈ Sph n, tpart (hmid y z) - inner ℝ (hmid y z) η =
      ((tpart y - inner ℝ y η) + (tpart z - inner ℝ z η)) / (2 * Real.cosh (hdist y z / 2)) :=
    fun y z hyz => (BaryMidpoint n y z hyz).2.2
  exact minimiser_unique ν hν hsupp hatom htri hsym hmid_id
    (fun y z m hyz hm => baryEqualityFinset n y z m hyz hm) hy hbarA

/-- the barycentre is equivariant: `bar (ν.map (bd g)) = g • bar ν` -/
theorem bar_map_bd (hA : POActionProp n) (hI : HypIsometryProp n)
    (ν : Measure (E n)) (hν : IsProbabilityMeasure ν) (hsupp : ν (Sph n)ᶜ = 0)
    (hatom : ∀ ξ : E n, ν {ξ} = 0)
    (hmin : ∀ z, baryFun ν (bar ν) ≤ baryFun ν z)
    (hstr : ∀ (μ : Measure (E n)), IsProbabilityMeasure μ → μ (Sph n)ᶜ = 0 →
      (∀ ξ : E n, μ {ξ} = 0) → ∀ y : E n, (∀ w, baryFun μ y ≤ baryFun μ w) → y = bar μ)
    (g : PO n 1) : bar (ν.map (bd g)) = g • bar ν := by
  obtain ⟨-, -, -, hone, hmul, -, -, hbd_mem, hbd_one, hbd_mul, -, hbd_meas⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcocy⟩ := hI
  have hSph_meas : MeasurableSet (Sph n) := by
    have h : Sph n = (fun x : E n => dist x 0) ⁻¹' {1} := by
      ext x; simp [Sph, Metric.mem_sphere]
    rw [h]
    exact (measurableSet_singleton 1).preimage
      (continuous_id.dist continuous_const).measurable
  have hprob' : IsProbabilityMeasure (ν.map (bd g)) := ⟨by
    rw [MeasureTheory.Measure.map_apply (hbd_meas g) MeasurableSet.univ]
    simp [MeasureTheory.IsProbabilityMeasure.measure_univ]⟩
  have hsupp' : (ν.map (bd g)) (Sph n)ᶜ = 0 := by
    rw [MeasureTheory.Measure.map_apply (hbd_meas g) hSph_meas.compl]
    exact MeasureTheory.measure_mono_null
      (fun ξ hξ => fun hmem => hξ (hbd_mem g ξ hmem)) hsupp
  have hatom' : ∀ ξ : E n, (ν.map (bd g)) {ξ} = 0 := by
    intro ξ
    rw [MeasureTheory.Measure.map_apply (hbd_meas g) (measurableSet_singleton ξ)]
    refine MeasureTheory.measure_mono_null (t := {bd (g⁻¹) ξ} ∪ (Sph n)ᶜ) ?_ ?_
    · intro w hw
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
      by_cases hwS : w ∈ Sph n
      · left
        have h2 := hbd_mul g⁻¹ g w hwS
        rw [inv_mul_cancel, hbd_one w hwS, hw] at h2
        simpa using h2
      · exact Or.inr hwS
    · rw [MeasureTheory.measure_union_null_iff]
      exact ⟨hatom _, hsupp⟩
  have hint_bd : ∀ u : E n, Integrable (fun ξ => busemann (bd g ξ) (g • u)) ν := by
    intro u
    refine Integrable.of_bound ((measurable_busemann (g • u)).comp (hbd_meas g)).aestronglyMeasurable
      (hdist 0 (g • u)) ?_
    have hae : ∀ᵐ ξ ∂ν, ξ ∈ Sph n := by rw [MeasureTheory.ae_iff]; exact hsupp
    filter_upwards [hae] with ξ hξ
    simpa [Real.norm_eq_abs] using
      abs_busemann_le_hdist_zero (bd g ξ) (hbd_mem g ξ hξ) (g • u)
  set C : ℝ := ∫ ξ, busemann (bd g ξ) (g • (0 : E n)) ∂ν with hC
  have hcoc : ∀ u : E n, baryFun (ν.map (bd g)) (g • u) = baryFun ν u + C := by
    intro u
    have hint2 : Integrable (fun ξ => busemann ξ u) ν := integrable_busemann ν hν hsupp u
    have hint3 : Integrable (fun ξ => busemann (bd g ξ) (g • (0 : E n))) ν := hint_bd 0
    have hae : ∀ᵐ ξ ∂ν,
        busemann (bd g ξ) (g • u) = busemann ξ u + busemann (bd g ξ) (g • 0) := by
      have haeS : ∀ᵐ ξ ∂ν, ξ ∈ Sph n := by rw [MeasureTheory.ae_iff]; exact hsupp
      filter_upwards [haeS] with ξ hξ
      exact hcocy g ξ u hξ
    rw [baryFun, MeasureTheory.integral_map (hbd_meas g).aemeasurable
      ((measurable_busemann (g • u)).aestronglyMeasurable)]
    rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_add hint2 hint3]
    simp only [baryFun]
    rw [hC]
  have hmin' : ∀ w, baryFun (ν.map (bd g)) (g • bar ν) ≤ baryFun (ν.map (bd g)) w := by
    intro w
    have hw : g • (g⁻¹ • w) = w := by rw [← hmul g g⁻¹ w, mul_inv_cancel, hone]
    calc baryFun (ν.map (bd g)) (g • bar ν) = baryFun ν (bar ν) + C := hcoc (bar ν)
      _ ≤ baryFun ν (g⁻¹ • w) + C := by linarith [hmin (g⁻¹ • w)]
      _ = baryFun (ν.map (bd g)) (g • (g⁻¹ • w)) := (hcoc (g⁻¹ • w)).symm
      _ = baryFun (ν.map (bd g)) w := by rw [hw]
  have hbar' := hstr (ν.map (bd g)) hprob' hsupp' hatom' (g • bar ν) hmin'
  exact hbar'.symm

end

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Real ENNReal

noncomputable section

variable {n : ℕ}

/-- `BaryProp` for a fixed atomless probability measure on the sphere -/
theorem bary_general (hA : POActionProp n) (hI : HypIsometryProp n)
    (ν : Measure (E n)) (hν : IsProbabilityMeasure ν) (hsupp : ν (Sph n)ᶜ = 0)
    (hatom : ∀ ξ : E n, ν {ξ} = 0) :
    (∀ z, baryFun ν (bar ν) ≤ baryFun ν z) ∧
    (∀ y, (∀ z, baryFun ν y ≤ baryFun ν z) → y = bar ν) ∧
    ∀ g : PO n 1, bar (ν.map (bd g)) = g • bar ν := by
  obtain ⟨hmin, huniq⟩ := bary_min hA hI ν hν hsupp hatom
  have hstr : ∀ (μ : Measure (E n)), IsProbabilityMeasure μ → μ (Sph n)ᶜ = 0 →
      (∀ ξ : E n, μ {ξ} = 0) → ∀ y : E n, (∀ w, baryFun μ y ≤ baryFun μ w) → y = bar μ :=
    fun μ hμ hsuppμ hatomμ => (bary_min hA hI μ hμ hsuppμ hatomμ).2
  exact ⟨hmin, huniq, fun g => bar_map_bd hA hI ν hν hsupp hatom hmin hstr g⟩

theorem barycentre (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) :
    BaryProp n :=
  fun ν hν hsupp hatom => bary_general hA hI ν hν hsupp hatom

end

end Work.Mostow
