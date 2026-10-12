import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseRowsFS.LatRiemann.Geom
import Submission.Work.BoseRowsFS.LatRiemann.cellIdent
import Submission.Work.BoseRowsFS.LatRiemann.cellRemBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.LatRiemann.cellInvNormDev`

The second-order (centred) estimate for the function `p ↦ 1/‖p‖²` on a *far* half-open cell
of the lattice `h·ℤ³`:

    |∫_{hbox h m} (1/‖p‖² − 1/‖latPt h m‖²)| ≤ 16 h⁵/‖latPt h m‖⁴

under the hypothesis `2√3 h ≤ ‖latPt h m‖` (the cell is far from the origin: its centre is at
distance at least the diagonal `2√3 h` of a cell).  This is Step 3b of the route of
`Submission/Work/BoseRowsFS/FINDING_lattice_riemann_core.md`.

The content is the *centred second-order expansion*

    `1/‖p‖² − 1/a² = −2⟨P, p−P⟩/a⁴ + R(p)`,   `|R(p)| ≤ (88/9)‖p−P‖²/a⁴`   (`a = ‖P‖`),

together with the fact that the *linear* term integrates to zero over the half-open cell
(the cell is centred at `P`), and `∫_{hbox} 1 = h³`.  Since `‖p − P‖ ≤ h√3/2` on the cell,
the total is at most `(88/9)(3h²/4)h³/a⁴ = (22/3) h⁵/a⁴ ≤ 16 h⁵/a⁴`.

The vanishing of the linear term — the *centroid* identity `∫_{hbox} (pᵢ − Pᵢ) = 0` — is
delicate in the half-open case (the box is not exactly invariant under `p ↦ 2P − p`), and is
handled here by transporting the integral to the function space `Fin 3 → ℝ` (where `volume` is
the product measure) and using Fubini for products of functions (`integral_fintype_prod_eq_prod`)
together with the one-dimensional identity `∫_{[a,b)} (t − (a+b)/2) = 0`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseRowsFS.LatRiemann

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. A one-dimensional centred integral -/

/-- `∫_{[a,b)} (t − (a+b)/2) dt = 0`: the first moment of a half-open interval about its
midpoint vanishes. -/
lemma integral_Ico_sub_mid {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Set.Ico a b, (t - (a + b) / 2) = 0 := by
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_comp_sub_right (f := fun t : ℝ => t) ((a + b) / 2)]
  have h1 : a - (a + b) / 2 = -((b - a) / 2) := by ring
  have h2 : b - (a + b) / 2 = (b - a) / 2 := by ring
  rw [h1, h2]
  have h := intervalIntegral.integral_comp_neg (f := fun x : ℝ => x)
      (a := -((b - a) / 2)) (b := (b - a) / 2)
  simp only [neg_neg] at h
  rw [intervalIntegral.integral_neg] at h
  linarith

/-! ## 2. The coordinate first moment of a product box, in the function space -/

/-- Fubini for the product box: the first moment of the `k`-th coordinate about the midpoint
of the interval vanishes. -/
lemma integral_piBox_coord_sub {A B : Fin 3 → ℝ} {k : Fin 3} (hAB : ∀ i, A i ≤ B i) :
    ∫ x : Fin 3 → ℝ,
        (Set.pi Set.univ (fun i : Fin 3 => Set.Ico (A i) (B i))).indicator
          (fun x => x k - (A k + B k) / 2) x = 0 := by
  set f : (i : Fin 3) → ℝ → ℝ := Function.update
      (fun i t => (Set.Ico (A i) (B i)).indicator (fun _ => (1 : ℝ)) t) k
      ((Set.Ico (A k) (B k)).indicator (fun t => t - (A k + B k) / 2)) with hf
  have hpt : ∀ x : Fin 3 → ℝ,
      (Set.pi Set.univ (fun i : Fin 3 => Set.Ico (A i) (B i))).indicator
          (fun x => x k - (A k + B k) / 2) x = ∏ i, f i (x i) := by
    intro x
    by_cases hx : x ∈ Set.pi Set.univ (fun i : Fin 3 => Set.Ico (A i) (B i))
    · rw [Set.indicator_of_mem hx]
      have hxall : ∀ i, x i ∈ Set.Ico (A i) (B i) := fun i => Set.mem_pi.mp hx i (Set.mem_univ i)
      rw [Finset.prod_eq_mul_prod_sdiff_singleton k (fun i => f i (x i)) (by simp)]
      have hfk : f k (x k) = x k - (A k + B k) / 2 := by
        simp only [hf, Function.update_self, Set.indicator_of_mem (hxall k)]
      have hrest : ∏ i ∈ Finset.univ \ {k}, f i (x i) = 1 := by
        refine Finset.prod_eq_one ?_
        intro i hi
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hi
        have hik : i ≠ k := hi.2
        simp only [hf, Function.update_of_ne hik, Set.indicator_of_mem (hxall i)]
      rw [hfk, hrest, mul_one]
    · rw [Set.indicator_of_notMem hx]
      have hnall : ¬ ∀ i, x i ∈ Set.Ico (A i) (B i) := by
        intro h
        exact hx (Set.mem_pi.mpr (fun i _ => h i))
      push Not at hnall
      obtain ⟨j, hj⟩ := hnall
      rw [Finset.prod_eq_zero (Finset.mem_univ j)]
      rcases eq_or_ne j k with rfl | hjk
      · simp only [hf, Function.update_self, Set.indicator_of_notMem hj]
      · simp only [hf, Function.update_of_ne hjk, Set.indicator_of_notMem hj]
  have hprod : ∫ x : Fin 3 → ℝ, ∏ i, f i (x i) = ∏ i, ∫ t, f i t ∂(volume : Measure ℝ) := by
    rw [show (volume : Measure (Fin 3 → ℝ)) = Measure.pi (fun _ : Fin 3 => volume) from rfl]
    exact MeasureTheory.integral_fintype_prod_eq_prod (μ := fun _ => (volume : Measure ℝ)) f
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt), hprod]
  refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
  simp only [hf, Function.update_self]
  rw [MeasureTheory.integral_indicator measurableSet_Ico]
  exact integral_Ico_sub_mid (hAB k)

/-! ## 3. The centroid identity on a half-open cell of the lattice -/

lemma hbox_preimage (h : ℝ) (m : Fin 3 → ℤ) :
    (WithLp.toLp 2 ⁻¹' hbox h m : Set (Fin 3 → ℝ)) =
      Set.pi Set.univ (fun j : Fin 3 => Set.Ico (h * (m j : ℝ) - h / 2) (h * (m j : ℝ) + h / 2)) := by
  ext x
  simp only [Set.mem_preimage, hbox, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
    true_implies, Set.mem_Ico]

/-- **The centroid identity**: `∫_{hbox h m} (pᵢ − (latPt h m)ᵢ) dp = 0`. -/
lemma integral_hbox_coord_sub {h : ℝ} (hh : 0 ≤ h) (m : Fin 3 → ℤ) (i : Fin 3) :
    ∫ p in hbox h m, (p i - (Work.BoseRowsFS.latPt h m) i) = 0 := by
  have hmp := (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
      ((hbox h m).indicator (fun p : ℝ³ => p i - (Work.BoseRowsFS.latPt h m) i))
  rw [← MeasureTheory.integral_indicator (measurableSet_hbox h m), ← hmp]
  have hpt : ∀ x : Fin 3 → ℝ,
      (hbox h m).indicator (fun p : ℝ³ => p i - (Work.BoseRowsFS.latPt h m) i)
          (WithLp.toLp 2 x)
      = (Set.pi Set.univ (fun j : Fin 3 =>
            Set.Ico (h * (m j : ℝ) - h / 2) (h * (m j : ℝ) + h / 2))).indicator
          (fun x => x i - (h * (m i : ℝ) - h / 2 + (h * (m i : ℝ) + h / 2)) / 2) x := by
    intro x
    by_cases hx : WithLp.toLp 2 x ∈ hbox h m
    · rw [Set.indicator_of_mem hx]
      have hx' : x ∈ Set.pi Set.univ (fun j : Fin 3 =>
          Set.Ico (h * (m j : ℝ) - h / 2) (h * (m j : ℝ) + h / 2)) := by
        rw [← hbox_preimage h m]; exact hx
      rw [Set.indicator_of_mem hx']
      have hcoe : (WithLp.toLp 2 x : ℝ³) i = x i := rfl
      have hlat : (Work.BoseRowsFS.latPt h m) i = h * (m i : ℝ) := rfl
      rw [hcoe, hlat]
      ring
    · rw [Set.indicator_of_notMem hx]
      have hx' : x ∉ Set.pi Set.univ (fun j : Fin 3 =>
          Set.Ico (h * (m j : ℝ) - h / 2) (h * (m j : ℝ) + h / 2)) := by
        rw [← hbox_preimage h m]; exact hx
      rw [Set.indicator_of_notMem hx']
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact integral_piBox_coord_sub (A := fun j : Fin 3 => h * (m j : ℝ) - h / 2)
      (B := fun j : Fin 3 => h * (m j : ℝ) + h / 2) (k := i) (fun j => by linarith)

/-! ## 4. Integrability on a cell of a bounded measurable function -/

lemma integrableOn_hbox_of_bound {h : ℝ} {m : Fin 3 → ℤ} {f : ℝ³ → ℝ} {C : ℝ}
    (hm : Measurable f) (hb : ∀ p ∈ hbox h m, |f p| ≤ C) : IntegrableOn f (hbox h m) := by
  refine MeasureTheory.IntegrableOn.of_bound ?hfin hm.aestronglyMeasurable.restrict C ?hbd
  · rw [volume_hbox]
    exact ENNReal.pow_lt_top (n := 3) ENNReal.ofReal_lt_top
  · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_hbox h m)] with p hp
    rw [Real.norm_eq_abs]
    exact hb p hp

/-! ## 5. The coordinate form of the inner product -/

lemma inner_eq_sum_coord (x y : ℝ³) : inner ℝ x y = ∑ i : Fin 3, x i * y i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [RCLike.inner_apply, mul_comm]

/-! ## 6. The algebra of the expansion

The exact second-order expansion (`cellIdent`) and the bound on its remainder (`cellRemBound`)
are proved in the sibling modules `Submission.Work.BoseRowsFS.LatRiemann.cellIdent` and
`Submission.Work.BoseRowsFS.LatRiemann.cellRemBound`, and imported above. -/

/-! ## 7. The cell estimate -/

lemma cellInvNormDev_aux {h : ℝ} (hh : 0 < h) {m : Fin 3 → ℤ} {P : ℝ³}
    (hP : P = Work.BoseRowsFS.latPt h m) (hfar : 2 * Real.sqrt 3 * h ≤ ‖P‖) :
    |∫ p in hbox h m, (1 / ‖p‖ ^ 2 - 1 / ‖P‖ ^ 2)| ≤ 16 * h ^ 5 / ‖P‖ ^ 4 := by
  set a : ℝ := ‖P‖ with ha
  have hfar' : 2 * Real.sqrt 3 * h ≤ a := by rw [ha]; exact hfar
  have hapos : 0 < a := by
    have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith
  -- geometry of the cell
  have hdel : ∀ p ∈ hbox h m, ‖p - P‖ ≤ a / 4 := by
    intro p hp
    have h1 : ‖p - P‖ ≤ h * Real.sqrt 3 / 2 := by
      rw [hP]; exact norm_sub_latPt_le hh hp
    have h2 : h * Real.sqrt 3 / 2 ≤ a / 4 := by
      have he : h * Real.sqrt 3 / 2 = (2 * Real.sqrt 3 * h) / 4 := by ring
      rw [he]; linarith
    linarith
  have hpnorm : ∀ p ∈ hbox h m, 3 * a / 4 ≤ ‖p‖ := by
    intro p hp
    have h1 : |‖p‖ - a| ≤ ‖p - P‖ := by
      have h := abs_norm_sub_norm_le p P
      rwa [← ha] at h
    have h2 := hdel p hp
    have h3 := (abs_le.mp h1).1
    linarith
  have hppos : ∀ p ∈ hbox h m, 0 < ‖p‖ := by
    intro p hp
    have h := hpnorm p hp
    linarith
  have hvol : volume (hbox h m) < ⊤ := by
    rw [volume_hbox]
    exact ENNReal.pow_lt_top (n := 3) ENNReal.ofReal_lt_top
  -- the decomposition `F = L + R`
  set L : ℝ³ → ℝ := fun p => -2 * inner ℝ P (p - P) / a ^ 4 with hLdef
  set R : ℝ³ → ℝ := fun p =>
      (2 * inner ℝ P (p - P) * (‖p‖ ^ 2 - a ^ 2) - a ^ 2 * ‖p - P‖ ^ 2)
        / (a ^ 4 * ‖p‖ ^ 2) with hRdef
  have hident : ∀ p ∈ hbox h m, 1 / ‖p‖ ^ 2 - 1 / a ^ 2 = L p + R p := by
    intro p hp
    simpa only [hLdef, hRdef] using cellIdent ha hapos (hppos p hp)
  have hRemBnd : ∀ p ∈ hbox h m, |R p| ≤ (88 / 9) * ‖p - P‖ ^ 2 / a ^ 4 := by
    intro p hp
    simpa only [hRdef] using cellRemBound ha hapos (hdel p hp)
  have hRemBnd2 : ∀ p ∈ hbox h m, ‖R p‖ ≤ (22 / 3) * h ^ 2 / a ^ 4 := by
    intro p hp
    rw [Real.norm_eq_abs]
    have h1 := hRemBnd p hp
    have h2 : ‖p - P‖ ^ 2 ≤ 3 * h ^ 2 / 4 := by
      have h3 : ‖p - P‖ ≤ h * Real.sqrt 3 / 2 := by
        rw [hP]; exact norm_sub_latPt_le hh hp
      have h4 : (h * Real.sqrt 3 / 2) ^ 2 = 3 * h ^ 2 / 4 := by
        rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
        ring
      nlinarith [norm_nonneg (p - P), h4]
    have h5 : (88 / 9) * ‖p - P‖ ^ 2 ≤ (22 / 3) * h ^ 2 := by nlinarith [h2]
    calc |R p| ≤ (88 / 9) * ‖p - P‖ ^ 2 / a ^ 4 := h1
      _ ≤ (22 / 3) * h ^ 2 / a ^ 4 := div_le_div_of_nonneg_right h5 (by positivity)
  -- integrability
  have hLint : IntegrableOn L (hbox h m) := by
    have hbnd : ∀ p ∈ hbox h m, |L p| ≤ 1 / (2 * a ^ 2) := by
      intro p hp
      have hpos4 : (0 : ℝ) < a ^ 4 := by positivity
      have hinner1 : |inner ℝ P (p - P)| ≤ a * ‖p - P‖ := by
        have h := abs_real_inner_le_norm P (p - P)
        rwa [← ha] at h
      have hstep : a * ‖p - P‖ ≤ a * (a / 4) :=
        mul_le_mul_of_nonneg_left (hdel p hp) (le_of_lt hapos)
      have hb2 : |(-2 : ℝ) * inner ℝ P (p - P)| ≤ 2 * (a * (a / 4)) := by
        rw [abs_mul, abs_neg, abs_two]
        exact mul_le_mul_of_nonneg_left (hinner1.trans hstep) (by norm_num)
      rw [hLdef, abs_div, abs_of_pos hpos4]
      calc |(-2 : ℝ) * inner ℝ P (p - P)| / a ^ 4
          ≤ 2 * (a * (a / 4)) / a ^ 4 := div_le_div_of_nonneg_right hb2 (le_of_lt hpos4)
        _ = 1 / (2 * a ^ 2) := by field_simp; ring
    have hmeas : Measurable L := by rw [hLdef]; fun_prop
    exact integrableOn_hbox_of_bound (f := L) (C := 1 / (2 * a ^ 2)) hmeas hbnd
  have hRint : IntegrableOn R (hbox h m) := by
    have hmeas : Measurable R := by rw [hRdef]; fun_prop
    exact integrableOn_hbox_of_bound (f := R) (C := (22 / 3) * h ^ 2 / a ^ 4) hmeas
      (fun p hp => by simpa only [Real.norm_eq_abs] using hRemBnd2 p hp)
  -- the linear term integrates to zero
  have hinnerZero : ∫ p in hbox h m, inner ℝ P (p - P) = 0 := by
    have hsum : ∀ q : ℝ³, inner ℝ P (q - P) = ∑ i : Fin 3, P i * (q i - P i) := by
      intro q
      rw [inner_eq_sum_coord]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [PiLp.sub_apply]
    simp_rw [hsum]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [MeasureTheory.integral_const_mul]
      rw [hP, integral_hbox_coord_sub (le_of_lt hh) m i, mul_zero]
    · intro i _
      have hmeas : Measurable (fun q : ℝ³ => P i * (q i - P i)) := by fun_prop
      refine integrableOn_hbox_of_bound (f := fun q : ℝ³ => P i * (q i - P i))
        (C := |P i| * (a / 4)) hmeas ?_
      intro q hq
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |(q - P) i| = ‖(q - P) i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖q - P‖ := PiLp.norm_apply_le (q - P) i
        _ ≤ a / 4 := hdel q hq
  have hLzero : ∫ p in hbox h m, L p = 0 := by
    have hform : ∀ p : ℝ³, -2 * inner ℝ P (p - P) / a ^ 4
        = (-2 / a ^ 4) * inner ℝ P (p - P) := by
      intro p; ring
    simp_rw [hLdef, hform]
    rw [MeasureTheory.integral_const_mul, hinnerZero, mul_zero]
  -- the remainder
  have hRbound : |∫ p in hbox h m, R p| ≤ (22 / 3) * h ^ 2 / a ^ 4 * h ^ 3 := by
    have hb := MeasureTheory.norm_setIntegral_le_of_norm_le_const hvol hRemBnd2
    rwa [Real.norm_eq_abs, real_volume_hbox (le_of_lt hh) m] at hb
  -- assembly
  have hFsplit : (∫ p in hbox h m, (1 / ‖p‖ ^ 2 - 1 / a ^ 2))
      = (∫ p in hbox h m, L p) + ∫ p in hbox h m, R p := by
    have hae : (fun p : ℝ³ => 1 / ‖p‖ ^ 2 - 1 / a ^ 2)
        =ᵐ[volume.restrict (hbox h m)] (fun p => L p + R p) := by
      filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_hbox h m)] with p hp
      exact hident p hp
    rw [MeasureTheory.integral_congr_ae hae]
    exact MeasureTheory.integral_add hLint hRint
  calc |∫ p in hbox h m, (1 / ‖p‖ ^ 2 - 1 / a ^ 2)|
      = |(∫ p in hbox h m, L p) + ∫ p in hbox h m, R p| := by rw [hFsplit]
    _ = |∫ p in hbox h m, R p| := by rw [hLzero, zero_add]
    _ ≤ (22 / 3) * h ^ 2 / a ^ 4 * h ^ 3 := hRbound
    _ = (22 / 3) * h ^ 5 / a ^ 4 := by ring
    _ ≤ 16 * h ^ 5 / a ^ 4 := by
        have hpos4 : (0 : ℝ) < a ^ 4 := by positivity
        apply div_le_div_of_nonneg_right _ (le_of_lt hpos4)
        nlinarith [pow_nonneg (le_of_lt hh) 5]

theorem cellInvNormDev {h : ℝ} (hh : 0 < h) (m : Fin 3 → ℤ)
    (hfar : 2 * Real.sqrt 3 * h ≤ ‖Work.BoseRowsFS.latPt h m‖) :
    |∫ p in Work.BoseRowsFS.LatRiemann.hbox h m,
        (1 / ‖p‖ ^ 2 - 1 / ‖Work.BoseRowsFS.latPt h m‖ ^ 2)|
      ≤ 16 * h ^ 5 / ‖Work.BoseRowsFS.latPt h m‖ ^ 4 :=
  cellInvNormDev_aux hh rfl hfar

end Work.BoseRowsFS.LatRiemann
