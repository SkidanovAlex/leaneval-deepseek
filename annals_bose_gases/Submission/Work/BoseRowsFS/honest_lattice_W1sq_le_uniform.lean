import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Commons.Analysis.Fourier.dirichlet_integral
import Submission.Work.BoseBox.LatticeModel.Estimate
import Submission.Work.BoseFixR.Rb5Lin.chiR0_le_one
import Submission.Work.BoseRowsFS.W1_g0_finite
import Submission.Work.BoseRowsFS.free_eq_coulomb
import Submission.Work.BoseRowsFS.small_s_bound
import Submission.Work.BoseRowsFS.sum_exp_div_norm_sq_le
import Submission.Work.BoseRowsFS.summable_exp_div_norm_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.honest_lattice_W1sq_le_uniform`

The uniform honest lattice row: `ℓ⁻³Σ_{Lab N}Ŵ₁(k)²/‖k‖² ≤ C·(2π)⁻³∫Ŵ₁(p)²/(2‖p‖²)`, uniformly
in the box side `ℓ ≥ 1` and the cube size `N`.

The mathematical proof is documented, with all constants, in `FINDING_uniform_lattice_row.md`;
the two halves of the layer cake `1/‖k‖² = ∫_{s>0}e^{-s‖k‖²}ds` are split at `s = 1`:

* `large_s_bound` (here): `∫_{s>1} ≤ M²Σ'_{j≠0}e^{-‖k_j‖²}/‖k_j‖² ≤ 100 ℓ³M²`;
* `small_s_bound` (imported, `Submission.Work.BoseRowsFS.small_s_bound`): the position-space
  (Poisson/theta) representation for `s ≤ 1`;
* the free side `(2π)⁻³∫Ŵ²/(2p²) = (1/8π)∬WW/‖x−y‖` (`free_eq_coulomb`) and the ball lower
  bound `M² ≤ 2R·∬WW/‖x−y‖` (`coulomb_ge_mass`) turn the two into the statement of
  `lattice_row_aux`, whose constant is `10⁸(1+R)⁵`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real Topology BigOperators

namespace Work.BoseRowsFS

set_option autoImplicit false

/-! ## 1. Elementary inputs -/

/-- `chat` is bounded by the `L¹` mass. -/
lemma abs_chat_le_mass {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    (k : EuclideanSpace ℝ (Fin 3)) :
    |Work.BoseFixR.chat W k| ≤ ∫ x, |W x| := by
  rw [Work.BoseB7AK.W1low.chat_eq_integral_cos hW k]
  refine le_trans abs_integral_le_integral_abs ?_
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
    (hW.abs) (Filter.Eventually.of_forall fun y => ?_)
  calc |W y * Real.cos (inner ℝ k y)| = |W y| * |Real.cos (inner ℝ k y)| := abs_mul _ _
    _ ≤ |W y| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
    _ = |W y| := mul_one _

/-- The one-dimensional layer cake: `∫_{s > 0} e^{-w s} ds = 1/w`. -/
lemma layer_cake {w : ℝ} (hw : 0 < w) :
    (∫ s in Set.Ioi (0 : ℝ), Real.exp (-(w * s))) = w⁻¹ :=
  Commons.Analysis.Fourier.exp_neg_Ioi w hw

/-- The layer cake in the commuted form `∫_{s>0}e^{-sw}ds = 1/w`. -/
lemma layer_cake' {w : ℝ} (hw : 0 < w) :
    (∫ s in Set.Ioi (0 : ℝ), Real.exp (-(s * w))) = w⁻¹ := by
  rw [show (∫ s in Set.Ioi (0:ℝ), Real.exp (-(s * w)))
      = ∫ s in Set.Ioi (0:ℝ), Real.exp (-(w * s)) from
    setIntegral_congr_fun measurableSet_Ioi (fun s _ => by congr 1; ring)]
  exact layer_cake hw

/-- **Shifting the set integral `∫_{Ioi 1}` to `∫_{Ioi 0}`**: `∫_{s>1}f s = ∫_{s>0}f(s+1)`. -/
lemma honest_integral_Ioi_one_shift (f : ℝ → ℝ) :
    (∫ s in Set.Ioi (1 : ℝ), f s) = ∫ s in Set.Ioi (0 : ℝ), f (s + 1) := by
  have h₁ : ∀ x : ℝ,
      (Set.Ioi (1:ℝ)).indicator f (x + 1) = (Set.Ioi (0:ℝ)).indicator (fun s => f (s+1)) x := by
    intro x
    simp only [Set.indicator_apply, Set.mem_Ioi]
    by_cases hx : (0:ℝ) < x
    · have hx1 : (1:ℝ) < x + 1 := by linarith
      rw [if_pos hx1, if_pos hx]
    · have hx1 : ¬ ((1:ℝ) < x + 1) := by linarith
      rw [if_neg hx1, if_neg hx]
  calc (∫ s in Set.Ioi (1:ℝ), f s)
      = ∫ x : ℝ, (Set.Ioi (1:ℝ)).indicator f x := (integral_indicator measurableSet_Ioi).symm
    _ = ∫ x : ℝ, (Set.Ioi (1:ℝ)).indicator f (x + 1) := (integral_add_right_eq_self _ 1).symm
    _ = ∫ x : ℝ, (Set.Ioi (0:ℝ)).indicator (fun s => f (s+1)) x := by simp only [h₁]
    _ = ∫ x in Set.Ioi (0:ℝ), f (x + 1) := integral_indicator measurableSet_Ioi

/-- `∫_{s>1}e^{-sw}ds = e^{-w}/w` for `w > 0`. -/
lemma honest_integral_Ioi_one_exp {w : ℝ} (hw : 0 < w) :
    (∫ s in Set.Ioi (1:ℝ), Real.exp (-(s * w))) = Real.exp (-w) * w⁻¹ := by
  have hfun : (fun x : ℝ => Real.exp (-((x + 1) * w)))
      = fun x => Real.exp (-w) * Real.exp (-(w * x)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  rw [honest_integral_Ioi_one_shift, hfun, integral_const_mul, layer_cake hw]

/-- `s ↦ e^{-sw}` is integrable on `(0,∞)` for `w > 0`. -/
lemma honest_integrableOn_Ioi_exp {w : ℝ} (hw : 0 < w) :
    IntegrableOn (fun s : ℝ => Real.exp (-(s * w))) (Set.Ioi (0:ℝ)) := by
  refine (integrableOn_exp_mul_Ioi (a := -w) (by linarith) (0 : ℝ)).congr_fun (fun s _ => ?_)
    measurableSet_Ioi
  show Real.exp (-w * s) = Real.exp (-(s * w))
  rw [show -w * s = -(s * w) by ring]

/-- `s ↦ e^{-sw}` is integrable on `(1,∞)` for `w > 0`. -/
lemma honest_integrableOn_Ioi_one_exp {w : ℝ} (hw : 0 < w) :
    IntegrableOn (fun s : ℝ => Real.exp (-(s * w))) (Set.Ioi (1:ℝ)) :=
  (honest_integrableOn_Ioi_exp hw).mono_set (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))

/-- The summand `e^{-‖k_j‖²}/‖k_j‖²` vanishes at the origin (division by a zero norm). -/
lemma kvec_zero_term (ℓ : ℝ) :
    Real.exp (-(‖kvec ℓ (0 : Fin 3 → ℤ)‖ ^ 2)) / ‖kvec ℓ (0 : Fin 3 → ℤ)‖ ^ 2 = 0 := by
  simp [kvec]

/-- The norms of the box modes of a nonzero lattice vector are positive. -/
lemma kvec_normSq_pos {ℓ : ℝ} (hℓ : 0 < ℓ) {m : Fin 3 → ℤ} (hm : m ≠ 0) :
    0 < ‖kvec ℓ m‖ ^ 2 := by
  have hne : kvec ℓ m ≠ 0 := by
    intro hcon
    have h2 : (2 * Real.pi / ℓ) ≠ 0 := by positivity
    have hz : (2 * Real.pi / ℓ) • vecZ m = 0 := hcon
    rcases smul_eq_zero.mp hz with h | h
    · exact h2 h
    · exact hm ((vecZ_eq_zero_iff m).mp h)
  exact pow_pos (norm_pos_iff.mpr hne) 2

/-! ## 2. The two halves of the layer cake -/

/-- **The `s ≥ 1` half.**  `∫_{s>1}Σ_{m∈S}ĉ(k_m)²e^{-s‖k_m‖²} ≤ M²Σ'_{j≠0}e^{-‖k_j‖²}/‖k_j‖²`
(`≤ 100ℓ³M² ≤ 200M²`). -/
theorem large_s_bound {W : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ : ℝ} (hℓ1 : 1 ≤ ℓ)
    (hW : MeasureTheory.Integrable W) (hW0 : ∀ᵐ x, 0 ≤ W x)
    (S : Finset (Fin 3 → ℤ)) (hS : ∀ m ∈ S, m ≠ 0) :
    ℓ ^ (-(3 : ℝ)) * (∫ s in Set.Ioi (1 : ℝ),
        ∑ m ∈ S, (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2
          * Real.exp (-(s * ‖kvec ℓ m‖ ^ 2)))
      ≤ 200 * (∫ x, W x) ^ 2 := by
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ1
  set M : ℝ := ∫ x, W x with hM
  have hMnn : 0 ≤ M := by
    rw [hM]; exact integral_nonneg_of_ae hW0
  have habs : (∫ x, |W x|) = M := by
    rw [hM]
    exact integral_congr_ae (hW0.mono (fun x hx => abs_of_nonneg hx))
  have hchat : ∀ m : Fin 3 → ℤ, |Work.BoseFixR.chat W (kvec ℓ m)| ≤ M := by
    intro m
    rw [← habs]
    exact abs_chat_le_mass hW _
  have hkpos : ∀ m ∈ S, 0 < ‖kvec ℓ m‖ ^ 2 := fun m hm => kvec_normSq_pos hℓ0 (hS m hm)
  -- pull the integral inside the finite sum
  have hInt : (∫ s in Set.Ioi (1 : ℝ),
        ∑ m ∈ S, (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2 * Real.exp (-(s * ‖kvec ℓ m‖ ^ 2)))
      = ∑ m ∈ S, (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2
          * (Real.exp (-(‖kvec ℓ m‖ ^ 2)) * (‖kvec ℓ m‖ ^ 2)⁻¹) := by
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [integral_const_mul, honest_integral_Ioi_one_exp (hkpos m hm)]
    · intro m hm
      exact (honest_integrableOn_Ioi_one_exp (hkpos m hm)).const_mul _
  rw [hInt, Finset.mul_sum]
  -- full-lattice summability, via the subtype series
  have hsumm : Summable (fun j : Fin 3 → ℤ => Real.exp (-(‖kvec ℓ j‖ ^ 2)) / ‖kvec ℓ j‖ ^ 2) := by
    have h1 : Summable (({j : Fin 3 → ℤ | j ≠ 0} : Set (Fin 3 → ℤ)).indicator
        (fun j : Fin 3 → ℤ => Real.exp (-(‖kvec ℓ j‖ ^ 2)) / ‖kvec ℓ j‖ ^ 2)) :=
      summable_subtype_iff_indicator.mp (summable_exp_div_norm_sq hℓ1)
    refine h1.congr (fun j => ?_)
    rw [Set.indicator_apply]
    by_cases hj : j ∈ ({j : Fin 3 → ℤ | j ≠ 0} : Set (Fin 3 → ℤ))
    · rw [if_pos hj]
    · rw [if_neg hj]
      have hj0 : ¬ (j ≠ 0) := hj
      rw [not_not.mp hj0, kvec_zero_term]
  have htsumeq : (∑' j : Fin 3 → ℤ, Real.exp (-(‖kvec ℓ j‖ ^ 2)) / ‖kvec ℓ j‖ ^ 2)
      = ∑' j : {j : Fin 3 → ℤ // j ≠ 0},
          Real.exp (-(‖kvec ℓ j.1‖ ^ 2)) / ‖kvec ℓ j.1‖ ^ 2 := by
    refine (tsum_subtype_eq_of_support_subset
      (f := fun j : Fin 3 → ℤ => Real.exp (-(‖kvec ℓ j‖ ^ 2)) / ‖kvec ℓ j‖ ^ 2)
      (s := ({j : Fin 3 → ℤ | j ≠ 0} : Set (Fin 3 → ℤ))) ?_).symm
    intro j hj
    by_contra h
    have hj0 : j = 0 := by
      by_contra h'
      exact h h'
    rw [hj0] at hj
    exact hj (kvec_zero_term ℓ)
  have hle100 : (∑ m ∈ S, Real.exp (-(‖kvec ℓ m‖ ^ 2)) / ‖kvec ℓ m‖ ^ 2) ≤ 100 * ℓ ^ 3 :=
    calc ∑ m ∈ S, Real.exp (-(‖kvec ℓ m‖ ^ 2)) / ‖kvec ℓ m‖ ^ 2
        ≤ ∑' j : Fin 3 → ℤ, Real.exp (-(‖kvec ℓ j‖ ^ 2)) / ‖kvec ℓ j‖ ^ 2 :=
          hsumm.sum_le_tsum S (fun i _ => div_nonneg (Real.exp_pos _).le (by positivity))
      _ = ∑' j : {j : Fin 3 → ℤ // j ≠ 0},
            Real.exp (-(‖kvec ℓ j.1‖ ^ 2)) / ‖kvec ℓ j.1‖ ^ 2 := htsumeq
      _ ≤ 100 * ℓ ^ 3 := sum_exp_div_norm_sq_le hℓ1
  -- the termwise bound
  have hstep : ∀ m ∈ S, ℓ ^ (-(3:ℝ)) * ((Work.BoseFixR.chat W (kvec ℓ m)) ^ 2
        * (Real.exp (-(‖kvec ℓ m‖ ^ 2)) * (‖kvec ℓ m‖ ^ 2)⁻¹))
      ≤ ℓ ^ (-(3:ℝ)) * (M ^ 2 * (Real.exp (-(‖kvec ℓ m‖ ^ 2)) / ‖kvec ℓ m‖ ^ 2)) := by
    intro m hm
    have h1 : (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2 ≤ M ^ 2 := by
      have h := hchat m
      nlinarith [abs_nonneg (Work.BoseFixR.chat W (kvec ℓ m)), hMnn,
        sq_abs (Work.BoseFixR.chat W (kvec ℓ m))]
    have h2 : Real.exp (-(‖kvec ℓ m‖ ^ 2)) * (‖kvec ℓ m‖ ^ 2)⁻¹
        = Real.exp (-(‖kvec ℓ m‖ ^ 2)) / ‖kvec ℓ m‖ ^ 2 := by rw [div_eq_mul_inv]
    rw [h2]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right h1 (by positivity)) (Real.rpow_nonneg hℓ0.le _)
  have hsum2 : (∑ m ∈ S, M ^ 2 * (Real.exp (-(‖kvec ℓ m‖ ^ 2)) / ‖kvec ℓ m‖ ^ 2))
      = M ^ 2 * ∑ m ∈ S, (Real.exp (-(‖kvec ℓ m‖ ^ 2)) / ‖kvec ℓ m‖ ^ 2) := by
    rw [Finset.mul_sum]
  calc ∑ m ∈ S, ℓ ^ (-(3:ℝ)) * ((Work.BoseFixR.chat W (kvec ℓ m)) ^ 2
        * (Real.exp (-(‖kvec ℓ m‖ ^ 2)) * (‖kvec ℓ m‖ ^ 2)⁻¹))
      ≤ ∑ m ∈ S, ℓ ^ (-(3:ℝ)) * (M ^ 2 * (Real.exp (-(‖kvec ℓ m‖ ^ 2)) / ‖kvec ℓ m‖ ^ 2)) :=
        Finset.sum_le_sum hstep
    _ = ℓ ^ (-(3:ℝ)) * (M ^ 2 * ∑ m ∈ S, (Real.exp (-(‖kvec ℓ m‖ ^ 2)) / ‖kvec ℓ m‖ ^ 2)) := by
        rw [← Finset.mul_sum, hsum2]
    _ ≤ ℓ ^ (-(3:ℝ)) * (M ^ 2 * (100 * ℓ ^ 3)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle100 (sq_nonneg M))
          (Real.rpow_nonneg hℓ0.le _)
    _ = 100 * M ^ 2 := by
        have h1 : ℓ ^ (-(3:ℝ)) = ((ℓ:ℝ) ^ (3:ℕ))⁻¹ := by
          rw [Real.rpow_neg hℓ0.le 3]
          congr 1
          exact Real.rpow_natCast ℓ 3
        rw [h1]
        have h3 : (ℓ:ℝ) ^ (3:ℕ) ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ0)
        field_simp
    _ ≤ 200 * (∫ x, W x) ^ 2 := by
        rw [hM]; nlinarith [sq_nonneg M]

/-- **Integrability of the pair (Coulomb) kernel of `W₁`.**  The Newtonian self-energy
`∫⁻x ∫⁻y W₁(x)W₁(y)/‖x−y‖` is finite (`Work.BoseRowsFS.W1_g0_finite`), and Tonelli turns that
into the product-measure integrability of the pair integrand. -/
lemma honest_W1_pair_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ) (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixR.W1fun v h ℓ p.1 * Work.BoseFixR.W1fun v h ℓ p.2 / ‖p.1 - p.2‖) := by
  set W : EuclideanSpace ℝ (Fin 3) → ℝ := Work.BoseFixR.W1fun v h ℓ with hWdef
  have hW : MeasureTheory.Integrable W :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hW0 : ∀ᵐ x, 0 ≤ W x :=
    Submission.BoseGases.wScaled_g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hfin : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)) ≠ ⊤ :=
    (Work.BoseRowsFS.W1_g0_finite hR hℓ hv_nonneg hvrad hv_supp h hRℓ).1
  have hWm : AEMeasurable W volume := hW.1.aemeasurable
  have hAEM : AEMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        W z.1 * W z.2 / ‖z.1 - z.2‖) (volume.prod volume) :=
    ((hWm.comp_fst).mul (hWm.comp_snd)).div
      (((measurable_fst.sub measurable_snd).norm).aemeasurable)
  have hAEM2 : AEMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ENNReal.ofReal (W z.1 * W z.2 / ‖z.1 - z.2‖)) (volume.prod volume) :=
    hAEM.ennreal_ofReal
  have hprod : (∫⁻ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (W z.1 * W z.2 / ‖z.1 - z.2‖) ∂(volume.prod volume))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖) :=
    MeasureTheory.lintegral_prod _ hAEM2
  have hlt : (∫⁻ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (W z.1 * W z.2 / ‖z.1 - z.2‖) ∂(volume.prod volume)) < ⊤ := by
    rw [hprod]; exact lt_top_iff_ne_top.mpr hfin
  have hpt : 0 ≤ᵐ[volume.prod volume]
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        W z.1 * W z.2 / ‖z.1 - z.2‖) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hW0,
      Measure.quasiMeasurePreserving_snd.ae hW0] with z h1 h2
    exact div_nonneg (mul_nonneg h1 h2) (norm_nonneg _)
  have hHF : MeasureTheory.HasFiniteIntegral
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        W z.1 * W z.2 / ‖z.1 - z.2‖) (volume.prod volume) :=
    (MeasureTheory.hasFiniteIntegral_iff_ofReal hpt).mpr hlt
  exact ⟨hAEM.aestronglyMeasurable, hHF⟩

/-! ## 3. The free side -/

/-- The Coulomb energy dominates the square of the mass (corpus `coulomb_energy_ge`,
transported from the product measure to the iterated integral). -/
theorem coulomb_ge_mass {W : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hW : MeasureTheory.Integrable W)
    (hW0 : ∀ᵐ x, 0 ≤ W x) (hWs : tsupport W ⊆ Metric.ball 0 R)
    (hcd : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      W p.1 * W p.2 / ‖p.1 - p.2‖)) :
    (∫ x, W x) ^ 2 / (2 * R) ≤ ∫ x, ∫ y, W x * W y / ‖x - y‖ := by
  -- the pointwise nonnegative representative
  set V : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => max (W x) 0 with hV
  have hVnn : 0 ≤ V := fun x => by simp only [hV]; exact le_max_right _ _
  have hae : V =ᵐ[volume] W :=
    hW0.mono (fun x hx => by simp only [hV, max_eq_left hx])
  have hVsupp : tsupport V ⊆ Metric.ball 0 R := by
    have hsub : Function.support V ⊆ Function.support W := by
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro hcon
      exact hx (by simp only [hV, hcon, max_self])
    exact (closure_mono hsub).trans hWs
  have hVint : MeasureTheory.Integrable V := hW.congr hae.symm
  have hVcd : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        V p.1 * V p.2 / ‖p.1 - p.2‖) := by
    refine hcd.congr ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hae,
      Measure.quasiMeasurePreserving_snd.ae hae] with p hp1 hp2
    rw [hp1, hp2]
  have hmain := Submission.BoseGases.coulomb_energy_ge (W := V) (R := R) hR hVnn hVint hVsupp hVcd
  have hM : (∫ x, V x) = ∫ x, W x := integral_congr_ae hae
  have hprod : (∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        V p.1 * V p.2 / ‖p.1 - p.2‖)
      = ∫ x, ∫ y, V x * V y / ‖x - y‖ := MeasureTheory.integral_prod _ hVcd
  have hiter : (∫ x, ∫ y, V x * V y / ‖x - y‖) = ∫ x, ∫ y, W x * W y / ‖x - y‖ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    rw [hx, hy]
  calc (∫ x, W x) ^ 2 / (2 * R) = (∫ x, V x) ^ 2 / (2 * R) := by rw [hM]
    _ ≤ ∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
          V p.1 * V p.2 / ‖p.1 - p.2‖ := hmain
    _ = ∫ x, ∫ y, V x * V y / ‖x - y‖ := hprod
    _ = ∫ x, ∫ y, W x * W y / ‖x - y‖ := hiter

/-! ## 4. The lattice row -/

/-- **The uniform lattice row** for an abstract kernel `W`: the whole analytic content,
assembled from the two halves of the layer cake, the free-side identity and the mass bound. -/
theorem lattice_row_aux {W : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ1 : 1 ≤ ℓ)
    (hRℓ : R ≤ ℓ)
    (hW : MeasureTheory.Integrable W) (hW0 : ∀ᵐ x, 0 ≤ W x) (hWe : ∀ x, W (-x) = W x)
    (hWs : tsupport W ⊆ Metric.ball 0 R)
    (hcd : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      W p.1 * W p.2 / ‖p.1 - p.2‖))
    (S : Finset (Fin 3 → ℤ)) (hS : ∀ m ∈ S, m ≠ 0) :
    ℓ ^ (-(3 : ℝ)) * (∑ m ∈ S, (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2 / ‖kvec ℓ m‖ ^ 2)
      ≤ (10 ^ 8 * (1 + R) ^ 5) * (((2 * Real.pi) ^ 3)⁻¹
          * (∫ p, Work.BoseFixR.chat W p ^ 2 / (2 * ‖p‖ ^ 2))) := by
  have hℓ0 : (0 : ℝ) < ℓ := lt_of_lt_of_le zero_lt_one hℓ1
  have hR0 : (0 : ℝ) ≤ R := le_of_lt hR
  set F : ℝ → ℝ := fun s => ∑ m ∈ S, (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2
    * Real.exp (-(s * ‖kvec ℓ m‖ ^ 2)) with hFdef
  have hkpos : ∀ m ∈ S, 0 < ‖kvec ℓ m‖ ^ 2 := fun m hm => kvec_normSq_pos hℓ0 (hS m hm)
  -- the layer cake
  have hlayer : (∫ s in Set.Ioi (0 : ℝ), F s)
      = ∑ m ∈ S, (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2 / ‖kvec ℓ m‖ ^ 2 := by
    rw [hFdef, integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [integral_const_mul, layer_cake' (hkpos m hm), div_eq_mul_inv]
    · intro m hm
      exact (honest_integrableOn_Ioi_exp (hkpos m hm)).const_mul _
  -- integrability of the whole summand on `Ioi 0`
  have hFint : IntegrableOn F (Set.Ioi (0:ℝ)) := by
    rw [hFdef]
    exact integrable_finset_sum _ (fun m hm => (honest_integrableOn_Ioi_exp (hkpos m hm)).const_mul _)
  -- the split at `s = 1`
  have hsplit : (∫ s in Set.Ioi (0 : ℝ), F s)
      = (∫ s in Set.Ioc (0 : ℝ) 1, F s) + ∫ s in Set.Ioi (1 : ℝ), F s := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)]
    refine MeasureTheory.setIntegral_union ?_ measurableSet_Ioi ?_ ?_
    · rw [Set.disjoint_left]
      intro x hx1 hx2
      exact absurd hx1.2 (not_le.mpr hx2)
    · exact hFint.mono_set (Set.Ioc_subset_Ioi_self)
    · exact hFint.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  -- the two halves
  have hsmall : ℓ ^ (-(3 : ℝ)) * (∫ s in Set.Ioc (0 : ℝ) 1, F s)
      ≤ (10 ^ 6 * (1 + R) ^ 4)
          * ((∫ x, ∫ y, W x * W y / ‖x - y‖) + (∫ x, W x) ^ 2) :=
    small_s_bound hR hℓ1 hRℓ hW hW0 hWe hWs hcd S hS
  have hlarge : ℓ ^ (-(3 : ℝ)) * (∫ s in Set.Ioi (1 : ℝ), F s)
      ≤ 200 * (∫ x, W x) ^ 2 := large_s_bound hℓ1 hW hW0 S hS
  -- the free side and the mass bound
  have hfree := free_eq_coulomb hW hW0 hWe hcd
  have hmass := coulomb_ge_mass hR hW hW0 hWs hcd
  set D : ℝ := ∫ x, ∫ y, W x * W y / ‖x - y‖ with hDdef
  set M : ℝ := ∫ x, W x with hMdef
  have hDnn : 0 ≤ D := by
    rw [hDdef]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hW0] with x hx
    refine integral_nonneg_of_ae ?_
    filter_upwards [hW0] with y hy
    exact div_nonneg (mul_nonneg hx hy) (norm_nonneg _)
  have hM2 : M ^ 2 ≤ 2 * R * D := by
    have h := hmass
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * R)] at h
    exact h.trans_eq (by ring)
  have hRHS : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p, Work.BoseFixR.chat W p ^ 2 / (2 * ‖p‖ ^ 2))
      = (1 / (8 * Real.pi)) * D := by
    rw [hDdef]; exact hfree
  -- the scalar arithmetic
  have hkey : (10 ^ 6 * (1 + R) ^ 4 * (1 + 2 * R) + 400 * R) * D
      ≤ (10 ^ 8 * (1 + R) ^ 5) * ((1 / (8 * Real.pi)) * D) := by
    have hπ : (8 * Real.pi) * ((2 * 10 ^ 6 : ℝ) + 400) ≤ 10 ^ 8 := by
      have h4 : Real.pi ≤ 4 := Real.pi_lt_four.le
      nlinarith [Real.pi_pos, h4]
    have hc1 : (1 : ℝ) ≤ 1 + R := by linarith
    have hp4 : (0 : ℝ) ≤ (1 + R) ^ 4 := by positivity
    have h5 : (1 + R) ^ 5 = (1 + R) ^ 4 * (1 + R) := by ring
    have hc5 : (1 : ℝ) ≤ (1 + R) ^ 5 := one_le_pow₀ hc1
    have h5nn : (0:ℝ) ≤ (1 + R) ^ 5 := by positivity
    have hfac : (10 ^ 6 * (1 + R) ^ 4 * (1 + 2 * R) + 400 * R)
        ≤ (2 * 10 ^ 6 + 400) * (1 + R) ^ 5 := by
      have hA : (1 + 2 * R) ≤ 2 * (1 + R) := by linarith
      have hstep1 : 10 ^ 6 * (1 + R) ^ 4 * (1 + 2 * R) ≤ 2 * 10 ^ 6 * (1 + R) ^ 5 := by
        calc 10 ^ 6 * (1 + R) ^ 4 * (1 + 2 * R)
            ≤ 10 ^ 6 * (1 + R) ^ 4 * (2 * (1 + R)) :=
              mul_le_mul_of_nonneg_left hA (by positivity)
          _ = 2 * 10 ^ 6 * (1 + R) ^ 5 := by rw [h5]; ring
      have hstep2 : 400 * R ≤ 400 * (1 + R) ^ 5 := by
        have hc4 : (1:ℝ) ≤ (1 + R) ^ 4 := one_le_pow₀ hc1
        have hle : (1 + R) ≤ (1 + R) ^ 5 := by
          calc (1 + R) = 1 * (1 + R) := (one_mul _).symm
            _ ≤ (1 + R) ^ 4 * (1 + R) := mul_le_mul_of_nonneg_right hc4 (by linarith)
            _ = (1 + R) ^ 5 := h5.symm
        linarith [hle]
      calc 10 ^ 6 * (1 + R) ^ 4 * (1 + 2 * R) + 400 * R
          ≤ 2 * 10 ^ 6 * (1 + R) ^ 5 + 400 * (1 + R) ^ 5 := add_le_add hstep1 hstep2
        _ = (2 * 10 ^ 6 + 400) * (1 + R) ^ 5 := by ring
    have hfin : (2 * 10 ^ 6 + 400) * (1 + R) ^ 5 * (8 * Real.pi) ≤ 10 ^ 8 * (1 + R) ^ 5 := by
      calc (2 * 10 ^ 6 + 400) * (1 + R) ^ 5 * (8 * Real.pi)
          = ((2 * 10 ^ 6 + 400) * (8 * Real.pi)) * (1 + R) ^ 5 := by ring
        _ = (8 * Real.pi) * (2 * 10 ^ 6 + 400) * (1 + R) ^ 5 := by ring
        _ ≤ 10 ^ 8 * (1 + R) ^ 5 := mul_le_mul_of_nonneg_right hπ h5nn
    have hmain : (10 ^ 6 * (1 + R) ^ 4 * (1 + 2 * R) + 400 * R)
        ≤ 10 ^ 8 * (1 + R) ^ 5 / (8 * Real.pi) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 8 * Real.pi)]
      calc (10 ^ 6 * (1 + R) ^ 4 * (1 + 2 * R) + 400 * R) * (8 * Real.pi)
          ≤ ((2 * 10 ^ 6 + 400) * (1 + R) ^ 5) * (8 * Real.pi) :=
            mul_le_mul_of_nonneg_right hfac (by positivity)
        _ = (2 * 10 ^ 6 + 400) * (1 + R) ^ 5 * (8 * Real.pi) := by ring
        _ ≤ 10 ^ 8 * (1 + R) ^ 5 := hfin
    calc (10 ^ 6 * (1 + R) ^ 4 * (1 + 2 * R) + 400 * R) * D
        ≤ (10 ^ 8 * (1 + R) ^ 5 / (8 * Real.pi)) * D := mul_le_mul_of_nonneg_right hmain hDnn
      _ = (10 ^ 8 * (1 + R) ^ 5) * ((1 / (8 * Real.pi)) * D) := by ring
  calc ℓ ^ (-(3 : ℝ)) * (∑ m ∈ S, (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2 / ‖kvec ℓ m‖ ^ 2)
      = ℓ ^ (-(3 : ℝ)) * (∫ s in Set.Ioi (0 : ℝ), F s) := by rw [hlayer]
    _ = ℓ ^ (-(3 : ℝ)) * ((∫ s in Set.Ioc (0 : ℝ) 1, F s) + ∫ s in Set.Ioi (1 : ℝ), F s) := by
        rw [hsplit]
    _ = ℓ ^ (-(3 : ℝ)) * (∫ s in Set.Ioc (0 : ℝ) 1, F s)
          + ℓ ^ (-(3 : ℝ)) * (∫ s in Set.Ioi (1 : ℝ), F s) := by ring
    _ ≤ (10 ^ 6 * (1 + R) ^ 4) * (D + M ^ 2) + 200 * M ^ 2 := by
        rw [hDdef, hMdef]
        exact add_le_add hsmall hlarge
    _ ≤ (10 ^ 6 * (1 + R) ^ 4 * (1 + 2 * R) + 400 * R) * D := by
        have hA : (0:ℝ) ≤ 10 ^ 6 * (1 + R) ^ 4 := by positivity
        have h1 : (10 ^ 6 * (1 + R) ^ 4) * M ^ 2 ≤ (10 ^ 6 * (1 + R) ^ 4) * (2 * R * D) :=
          mul_le_mul_of_nonneg_left hM2 hA
        have h2 : 200 * M ^ 2 ≤ 200 * (2 * R * D) := by linarith [hM2]
        nlinarith [h1, h2, hDnn]
    _ ≤ (10 ^ 8 * (1 + R) ^ 5) * ((1 / (8 * Real.pi)) * D) := hkey
    _ = (10 ^ 8 * (1 + R) ^ 5) * (((2 * Real.pi) ^ 3)⁻¹
          * (∫ p, Work.BoseFixR.chat W p ^ 2 / (2 * ‖p‖ ^ 2))) := by rw [hRHS]

/-! ## 5. The target -/

theorem honest_lattice_W1sq_le_uniform {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    (R : ℝ) (hR : 0 < R) (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ), 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 → ∀ N : ℕ,
      ℓ ^ (-(3 : ℝ)) *
        (∑ n ∈ (Finset.univ.erase (0 : Work.BoseBoxFock.Lab N)),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (Work.BoseBoxFock.kmomLab ℓ N n)) ^ 2
              / ‖Work.BoseBoxFock.kmomLab ℓ N n‖ ^ 2)
        ≤ C * (((2 * Real.pi) ^ 3)⁻¹
            * (∫ p, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / (2 * ‖p‖ ^ 2))) := by
  refine ⟨10 ^ 8 * (1 + R) ^ 5, by positivity, ?_⟩
  intro ℓ hℓ1 hRℓ N
  have hℓ0 : (0 : ℝ) < ℓ := lt_of_lt_of_le zero_lt_one hℓ1
  have hRℓ' : R ≤ ℓ := by
    calc R ≤ ℓ * Submission.BoseGases.chiR0 := hRℓ
      _ ≤ ℓ * 1 := by
          refine mul_le_mul_of_nonneg_left Work.BoseFixR.Rb5Lin.chiR0_le_one hℓ0.le
      _ = ℓ := mul_one ℓ
  set W : EuclideanSpace ℝ (Fin 3) → ℝ := Work.BoseFixR.W1fun v h ℓ with hWdef
  have hW : MeasureTheory.Integrable W :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ0 hRℓ
  have hW0 : ∀ᵐ x, 0 ≤ W x :=
    Submission.BoseGases.wScaled_g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hWe : ∀ x, W (-x) = W x := Work.BoseFixR.isEven_W1fun h hvrad ℓ
  have hWs : tsupport W ⊆ Metric.ball 0 R := Work.BoseFixR.tsupport_W1fun_subset h hv_supp ℓ
  have hcd : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        W p.1 * W p.2 / ‖p.1 - p.2‖) :=
    honest_W1_pair_integrable hR hℓ0 hv_nonneg hvrad hv_supp hRℓ
  -- the label set of the cube
  set S : Finset (Fin 3 → ℤ) :=
    (Finset.univ.erase (0 : Work.BoseBoxFock.Lab N)).image (Work.BoseBoxFock.labVec N) with hSdef
  have hinj : Function.Injective (Work.BoseBoxFock.labVec N) := Work.BoseFixR.labVec_injective N
  have hSne : ∀ m ∈ S, m ≠ 0 := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have hn0 : n ≠ 0 := (Finset.mem_erase.mp hn).1
    intro hcon
    exact hn0 (hinj (by rw [hcon, Work.BoseRowsFS.labVec_zero]))
  -- the sum rewrites onto the lattice
  have hsum : (∑ n ∈ (Finset.univ.erase (0 : Work.BoseBoxFock.Lab N)),
        (Work.BoseFixR.chat W (Work.BoseBoxFock.kmomLab ℓ N n)) ^ 2
          / ‖Work.BoseBoxFock.kmomLab ℓ N n‖ ^ 2)
      = ∑ m ∈ S, (Work.BoseFixR.chat W (kvec ℓ m)) ^ 2 / ‖kvec ℓ m‖ ^ 2 := by
    rw [hSdef, Finset.sum_image (fun x _ y _ hxy => hinj hxy)]
    exact Finset.sum_congr rfl fun n _ => by
      rw [Work.BoseRowsFS.kmomLab_eq]
      rfl
  rw [hsum]
  exact lattice_row_aux hR hℓ1 hRℓ' hW hW0 hWe hWs hcd S hSne

end Work.BoseRowsFS
