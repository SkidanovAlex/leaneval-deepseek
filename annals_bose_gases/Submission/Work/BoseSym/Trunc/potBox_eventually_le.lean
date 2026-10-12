import Mathlib
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Continuity of the truncated box energy along `L²`-convergent sequences

For a nonnegative interaction `V` integrable on the box `box N L` and a bounded Lipschitz
function `ψ : ℝ → ℝ`, the functional

  `f ↦ ∫ x in box N L, V x * (ψ (f x)) ^ 2`

is continuous at `v` along any sequence `u n → v` in `L²(Conf N)`.  Hence

  `∫ x in box N L, V x * (ψ (u n x)) ^ 2 ≤ ∫ x in box N L, V x * (ψ (v x)) ^ 2 + ε`

eventually in `n`.

The proof is an `ε/2` argument: bounding `|ψ a ^ 2 - ψ b ^ 2|` both by `2 C |a - b|` (Lipschitz)
and by `2 C ^ 2` (boundedness) allows one to split the integrand at a level `M` of `V`; the part
with `V ∧ M` is controlled by the `L¹`-convergence of the representatives (which is `L² ⊂ L¹` on
the finite-measure box) and the part with `(V - M)₊` by the tail estimate for an integrable
function.
-/

namespace Work.BoseSym.Trunc

open MeasureTheory Filter
open scoped Topology ENNReal

set_option autoImplicit false

/-- The box `box N L` has finite Lebesgue measure (for every real `L`). -/
private lemma volume_box_ne_top {N : ℕ} (L : ℝ) :
    (volume : Measure (Work.BoseSym.Conf N)) (BoseGases.box N L) ≠ ⊤ := by
  haveI : IsFiniteMeasureOnCompacts (volume : Measure (Work.BoseSym.Conf N)) := inferInstance
  have hsub : BoseGases.box N L ⊆ BoseGases.box N (max L 1) := by
    intro x hx i k
    exact ⟨(hx i k).1, le_trans (hx i k).2 (le_max_left L 1)⟩
  have hfin : (volume : Measure (Work.BoseSym.Conf N)) (BoseGases.box N (max L 1)) < ⊤ :=
    IsCompact.measure_lt_top (Submission.BoseGases.box_compact (N := N) (by positivity))
  exact ne_of_lt (lt_of_le_of_lt (measure_mono hsub) hfin)

/-- `L²` convergence implies `L¹` convergence of the representatives on the box: if `u n → v` in
`L²(Conf N)`, then `∫ x in box N L, |u n x - v x| → 0`. -/
private lemma tendsto_integral_abs_sub_box {N : ℕ} {L : ℝ} {u : ℕ → Work.BoseSym.L2 N}
    {v : Work.BoseSym.L2 N} (h : Filter.Tendsto u Filter.atTop (nhds v)) :
    Filter.Tendsto
      (fun n => ∫ x in BoseGases.box N L,
        |(u n : Work.BoseSym.Conf N → ℝ) x - (v : Work.BoseSym.Conf N → ℝ) x|)
      Filter.atTop (nhds 0) := by
  have hbox : (volume : Measure (Work.BoseSym.Conf N)) (BoseGases.box N L) ≠ ⊤ :=
    volume_box_ne_top L
  have hnorm : Filter.Tendsto (fun n => ‖u n - v‖) Filter.atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp h
  set K : ℝ := (((volume : Measure (Work.BoseSym.Conf N)) (BoseGases.box N L)).toReal) ^ ((1:ℝ)/2)
    with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  have hcomp : Filter.Tendsto (fun n => ‖u n - v‖ * K) Filter.atTop (nhds 0) := by
    have h1 := hnorm.mul (tendsto_const_nhds (x := K) (f := Filter.atTop))
    simpa using h1
  refine squeeze_zero
    (f := fun n => ∫ x in BoseGases.box N L,
      |(u n : Work.BoseSym.Conf N → ℝ) x - (v : Work.BoseSym.Conf N → ℝ) x|)
    (g := fun n => ‖u n - v‖ * K)
    (fun n => integral_nonneg (fun x => abs_nonneg _)) (fun n => ?_) hcomp
  set μs : Measure (Work.BoseSym.Conf N) :=
    (volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L) with hμs
  have hΔmeas : AEStronglyMeasurable
      (fun x => (u n : Work.BoseSym.Conf N → ℝ) x - (v : Work.BoseSym.Conf N → ℝ) x) μs :=
    ((Lp.aestronglyMeasurable (u n)).sub (Lp.aestronglyMeasurable v)).mono_measure
      Measure.restrict_le_self
  have hμuniv : μs Set.univ = (volume : Measure (Work.BoseSym.Conf N)) (BoseGases.box N L) := by
    rw [hμs, Measure.restrict_apply_univ]
  have hK : (μs Set.univ) ^ ((1:ℝ)/2) = ENNReal.ofReal K := by
    rw [hμuniv, ← ENNReal.ofReal_toReal hbox,
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num : (0:ℝ) ≤ 1/2), hKdef]
  have hintegral : (∫ x in BoseGases.box N L,
        |(u n : Work.BoseSym.Conf N → ℝ) x - (v : Work.BoseSym.Conf N → ℝ) x|)
      = (eLpNorm (fun x => (u n : Work.BoseSym.Conf N → ℝ) x
          - (v : Work.BoseSym.Conf N → ℝ) x) 1 μs).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => abs_nonneg _))
      (by simpa only [Real.norm_eq_abs] using hΔmeas.norm)]
    rw [hμs]
    congr 1
    rw [eLpNorm_one_eq_lintegral_enorm (hΔmeas.mono_measure (le_of_eq hμs.symm))]
    simp only [Real.enorm_eq_ofReal_abs]
  have hexp : (1:ℝ) - 2⁻¹ = 2⁻¹ := by norm_num
  have hle1 : eLpNorm (fun x => (u n : Work.BoseSym.Conf N → ℝ) x
        - (v : Work.BoseSym.Conf N → ℝ) x) 1 μs
      ≤ eLpNorm (fun x => (u n : Work.BoseSym.Conf N → ℝ) x
        - (v : Work.BoseSym.Conf N → ℝ) x) 2 μs * (μs Set.univ) ^ ((1:ℝ)/2) := by
    have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μs) (p := 1) (q := 2)
      (by norm_num) hΔmeas
    simpa [hexp] using h1
  have hle2 : eLpNorm (fun x => (u n : Work.BoseSym.Conf N → ℝ) x
        - (v : Work.BoseSym.Conf N → ℝ) x) 2 μs ≤ ENNReal.ofReal ‖u n - v‖ := by
    calc eLpNorm (fun x => (u n : Work.BoseSym.Conf N → ℝ) x
          - (v : Work.BoseSym.Conf N → ℝ) x) 2 μs
        ≤ eLpNorm (fun x => (u n : Work.BoseSym.Conf N → ℝ) x
          - (v : Work.BoseSym.Conf N → ℝ) x) 2 (volume : Measure (Work.BoseSym.Conf N)) :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = eLpNorm (↑(u n - v) : Work.BoseSym.Conf N → ℝ) 2
            (volume : Measure (Work.BoseSym.Conf N)) :=
          eLpNorm_congr_ae (Lp.coeFn_sub (u n) v).symm
      _ = ENNReal.ofReal ‖u n - v‖ := by
          rw [← ENNReal.ofReal_toReal (ne_of_lt (Lp.eLpNorm_lt_top (u n - v))), ← Lp.norm_def]
  have hbound : eLpNorm (fun x => (u n : Work.BoseSym.Conf N → ℝ) x
        - (v : Work.BoseSym.Conf N → ℝ) x) 1 μs ≤ ENNReal.ofReal (‖u n - v‖ * K) := by
    calc eLpNorm (fun x => (u n : Work.BoseSym.Conf N → ℝ) x
          - (v : Work.BoseSym.Conf N → ℝ) x) 1 μs
        ≤ eLpNorm (fun x => (u n : Work.BoseSym.Conf N → ℝ) x
          - (v : Work.BoseSym.Conf N → ℝ) x) 2 μs * (μs Set.univ) ^ ((1:ℝ)/2) := hle1
      _ ≤ ENNReal.ofReal ‖u n - v‖ * (μs Set.univ) ^ ((1:ℝ)/2) :=
          mul_le_mul_left hle2 _
      _ = ENNReal.ofReal (‖u n - v‖ * K) := by
          rw [hK, ← ENNReal.ofReal_mul (norm_nonneg _)]
  calc (∫ x in BoseGases.box N L,
          |(u n : Work.BoseSym.Conf N → ℝ) x - (v : Work.BoseSym.Conf N → ℝ) x|)
      = (eLpNorm (fun x => (u n : Work.BoseSym.Conf N → ℝ) x
          - (v : Work.BoseSym.Conf N → ℝ) x) 1 μs).toReal := hintegral
    _ ≤ (ENNReal.ofReal (‖u n - v‖ * K)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = ‖u n - v‖ * K := ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg _) hKnn)

/-- Tail estimate: for `V ≥ 0` integrable on the box, the integral of `V - min V M` tends to `0`
as `M → ∞`. -/
private lemma tendsto_integral_sub_min {N : ℕ} {L : ℝ} {V : Work.BoseSym.Conf N → ℝ}
    (hV0 : 0 ≤ V) (hVint : Work.BoseSym.IntOnBox N L V) :
    Filter.Tendsto
      (fun M : ℕ => ∫ x in BoseGases.box N L, (V x - min (V x) (M : ℝ)))
      Filter.atTop (nhds 0) := by
  have hmain : Filter.Tendsto
      (fun M : ℕ => ∫ x, (V x - min (V x) (M : ℝ))
        ∂((volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L)))
      Filter.atTop (nhds (∫ x, (fun _ : Work.BoseSym.Conf N => (0:ℝ)) x
        ∂((volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L)))) :=
    tendsto_integral_of_dominated_convergence
      (μ := (volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L))
      (F := fun M x => V x - min (V x) (M : ℝ)) (f := fun _ => (0:ℝ)) V
      (fun M => hVint.aestronglyMeasurable.sub
        ((AEMeasurable.min hVint.aemeasurable aemeasurable_const).aestronglyMeasurable))
      hVint
      (fun M => Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (min_le_left _ _))]
        exact sub_le_self _ (le_min (hV0 x) (Nat.cast_nonneg M))))
      (Filter.Eventually.of_forall (fun x => by
        obtain ⟨M₀, hM₀⟩ := exists_nat_ge (V x)
        refine tendsto_atTop_of_eventually_const (i₀ := M₀) (fun M hM => ?_)
        rw [min_eq_left (le_trans hM₀ (Nat.cast_le.mpr hM)), sub_self]))
  simpa using hmain

/-- The absolute value of the difference of the representatives of two `L²` functions is
integrable on the box (the box has finite measure, and `L² ⊂ L¹` there). -/
private lemma integrable_abs_sub_box {N : ℕ} {L : ℝ} (u v : Work.BoseSym.L2 N) :
    Integrable (fun x => |(u : Work.BoseSym.Conf N → ℝ) x - (v : Work.BoseSym.Conf N → ℝ) x|)
      ((volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L)) := by
  haveI : IsFiniteMeasure ((volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L)) :=
    isFiniteMeasure_restrict.2 (volume_box_ne_top L)
  have h : MemLp (fun x => (u : Work.BoseSym.Conf N → ℝ) x - (v : Work.BoseSym.Conf N → ℝ) x) 2
      ((volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L)) :=
    ((Lp.memLp u).restrict _).sub ((Lp.memLp v).restrict _)
  have h2 := h.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  simpa only [Real.norm_eq_abs] using h2.norm

/-- `|ψ t ^ 2| ≤ C ^ 2` if `|ψ t| ≤ C`. -/
private lemma psi_sq_bound {ψ : ℝ → ℝ} {C : ℝ} (hψC : ∀ t, |ψ t| ≤ C) (t : ℝ) :
    |ψ t ^ 2| ≤ C ^ 2 := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hψC t) 2

/-- Lipschitz bound for the square of a bounded Lipschitz function:
`|ψ a ^ 2 - ψ b ^ 2| ≤ 2 C |a - b|`. -/
private lemma psi_sq_sub_le {ψ : ℝ → ℝ} {C : ℝ} (hψC : ∀ t, |ψ t| ≤ C)
    (hψlip : ∀ a b, |ψ a - ψ b| ≤ |a - b|) (a b : ℝ) :
    |ψ a ^ 2 - ψ b ^ 2| ≤ 2 * C * |a - b| := by
  have h1 : |ψ a ^ 2 - ψ b ^ 2| = |ψ a - ψ b| * |ψ a + ψ b| := by
    rw [sq_sub_sq, abs_mul, mul_comm]
  rw [h1]
  have h2 : |ψ a + ψ b| ≤ 2 * C := by
    calc |ψ a + ψ b| ≤ |ψ a| + |ψ b| := abs_add_le _ _
      _ ≤ C + C := add_le_add (hψC a) (hψC b)
      _ = 2 * C := by ring
  calc |ψ a - ψ b| * |ψ a + ψ b| ≤ |a - b| * (2 * C) := by
        exact mul_le_mul (hψlip a b) h2 (abs_nonneg _) (le_trans (abs_nonneg _) (hψlip a b))
    _ = 2 * C * |a - b| := by ring

/-- Boundedness of the square: `|ψ a ^ 2 - ψ b ^ 2| ≤ 2 C ^ 2`. -/
private lemma psi_sq_sub_le_const {ψ : ℝ → ℝ} {C : ℝ} (hψC : ∀ t, |ψ t| ≤ C) (a b : ℝ) :
    |ψ a ^ 2 - ψ b ^ 2| ≤ 2 * C ^ 2 := by
  calc |ψ a ^ 2 - ψ b ^ 2| ≤ |ψ a ^ 2| + |ψ b ^ 2| := abs_sub _ _
    _ ≤ C ^ 2 + C ^ 2 := add_le_add (psi_sq_bound hψC a) (psi_sq_bound hψC b)
    _ = 2 * C ^ 2 := by ring

/-- Pointwise split of the difference of the integrands at the level `M` of `V`. -/
private lemma pointwise_le {N : ℕ} {V : Work.BoseSym.Conf N → ℝ} (hV0 : 0 ≤ V) {ψ : ℝ → ℝ}
    {C : ℝ} (hψC : ∀ t, |ψ t| ≤ C) (hψlip : ∀ a b, |ψ a - ψ b| ≤ |a - b|)
    {M : ℝ} (hM : 0 ≤ M) (x : Work.BoseSym.Conf N) (p q : ℝ) :
    |V x * (ψ p) ^ 2 - V x * (ψ q) ^ 2|
      ≤ 2 * C * M * |p - q| + 2 * C ^ 2 * (V x - min (V x) M) := by
  have hVx : 0 ≤ V x := hV0 x
  have step1 : |V x * (ψ p) ^ 2 - V x * (ψ q) ^ 2| = V x * |(ψ p) ^ 2 - (ψ q) ^ 2| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hVx]
  rw [step1]
  have hA : |(ψ p) ^ 2 - (ψ q) ^ 2| ≤ 2 * C * |p - q| := psi_sq_sub_le hψC hψlip p q
  have hB : |(ψ p) ^ 2 - (ψ q) ^ 2| ≤ 2 * C ^ 2 := psi_sq_sub_le_const hψC p q
  have hsplit : V x * |(ψ p)^2 - (ψ q)^2| =
      min (V x) M * |(ψ p)^2 - (ψ q)^2| + (V x - min (V x) M) * |(ψ p)^2 - (ψ q)^2| := by ring
  rw [hsplit]
  refine add_le_add ?_ ?_
  · calc min (V x) M * |(ψ p)^2 - (ψ q)^2| ≤ M * (2 * C * |p - q|) :=
        mul_le_mul (min_le_right _ _) hA (abs_nonneg _) hM
      _ = 2 * C * M * |p - q| := by ring
  · calc (V x - min (V x) M) * |(ψ p)^2 - (ψ q)^2| ≤ (V x - min (V x) M) * (2 * C ^ 2) :=
        mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr (min_le_left _ _))
      _ = 2 * C ^ 2 * (V x - min (V x) M) := by ring

/-- **Core continuity statement.** For `C > 0` the functional `f ↦ ∫_box V · (ψ f)²` is
continuous at `v` along `u n → v` in `L²`. -/
private lemma tendsto_int_mul_psiSq {N : ℕ} {L : ℝ} {V : Work.BoseSym.Conf N → ℝ}
    (hV0 : 0 ≤ V) (hVint : Work.BoseSym.IntOnBox N L V)
    {ψ : ℝ → ℝ} (hψm : Measurable ψ) {C : ℝ} (hC : 0 < C) (hψC : ∀ t, |ψ t| ≤ C)
    (hψlip : ∀ a b, |ψ a - ψ b| ≤ |a - b|)
    {u : ℕ → Work.BoseSym.L2 N} {v : Work.BoseSym.L2 N}
    (h : Filter.Tendsto u Filter.atTop (nhds v)) :
    Filter.Tendsto
      (fun n => ∫ x in BoseGases.box N L, V x * (ψ ((u n : Work.BoseSym.Conf N → ℝ) x)) ^ 2)
      Filter.atTop
      (nhds (∫ x in BoseGases.box N L, V x * (ψ ((v : Work.BoseSym.Conf N → ℝ) x)) ^ 2)) := by
  have hA := tendsto_integral_abs_sub_box (N := N) (L := L) h
  have hB := tendsto_integral_sub_min (N := N) (L := L) hV0 hVint
  rw [Metric.tendsto_atTop]
  intro η hη
  have h4 : 0 < η / (4 * C ^ 2) := by positivity
  have hMev : ∀ᶠ M : ℕ in atTop,
      (∫ x in BoseGases.box N L, (V x - min (V x) (M : ℝ))) < η / (4 * C ^ 2) :=
    hB.eventually (Iio_mem_nhds h4)
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hMev
  have hAev : ∀ᶠ n in atTop,
      2 * C * (M₀ : ℝ) * (∫ x in BoseGases.box N L,
        |(u n : Work.BoseSym.Conf N → ℝ) x - (v : Work.BoseSym.Conf N → ℝ) x|) < η / 2 := by
    have hlim : Filter.Tendsto (fun n => 2 * C * (M₀ : ℝ) * (∫ x in BoseGases.box N L,
        |(u n : Work.BoseSym.Conf N → ℝ) x - (v : Work.BoseSym.Conf N → ℝ) x|))
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := 2 * C * (M₀ : ℝ)) (f := Filter.atTop)).mul hA
    have h2 : (0:ℝ) < η / 2 := by linarith
    exact hlim.eventually (Iio_mem_nhds h2)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hAev
  refine ⟨N₀, fun n hn => ?_⟩
  have hnA := hN₀ n hn
  have hnB : (∫ x in BoseGases.box N L, (V x - min (V x) (M₀ : ℝ))) < η / (4 * C ^ 2) :=
    hM₀ M₀ le_rfl
  have hMnn : (0:ℝ) ≤ (M₀ : ℝ) := Nat.cast_nonneg M₀
  -- measurability of the integrands
  have hψu : AEMeasurable (fun x => ψ ((u n : Work.BoseSym.Conf N → ℝ) x))
      ((volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L)) :=
    hψm.comp_aemeasurable (((Lp.aestronglyMeasurable (u n)).aemeasurable).mono_measure
      Measure.restrict_le_self)
  have hmeas_u : AEStronglyMeasurable (fun x => (ψ ((u n : Work.BoseSym.Conf N → ℝ) x)) ^ 2)
      ((volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L)) :=
    (hψu.pow_const 2).aestronglyMeasurable
  have hψv : AEMeasurable (fun x => ψ ((v : Work.BoseSym.Conf N → ℝ) x))
      ((volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L)) :=
    hψm.comp_aemeasurable (((Lp.aestronglyMeasurable v).aemeasurable).mono_measure
      Measure.restrict_le_self)
  have hmeas_v : AEStronglyMeasurable (fun x => (ψ ((v : Work.BoseSym.Conf N → ℝ) x)) ^ 2)
      ((volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L)) :=
    (hψv.pow_const 2).aestronglyMeasurable
  -- integrability of the integrands
  have hInt_u : Integrable
      (fun x => V x * (ψ ((u n : Work.BoseSym.Conf N → ℝ) x)) ^ 2)
      ((volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L)) := by
    refine Integrable.mono' (hVint.const_mul (C^2)) (hVint.aestronglyMeasurable.mul hmeas_u) ?_
    filter_upwards with x
    have hsq : (ψ ((u n : Work.BoseSym.Conf N → ℝ) x)) ^ 2 ≤ C ^ 2 := by
      have h1 := psi_sq_bound hψC ((u n : Work.BoseSym.Conf N → ℝ) x)
      rwa [abs_of_nonneg (sq_nonneg _)] at h1
    calc ‖V x * (ψ ((u n : Work.BoseSym.Conf N → ℝ) x)) ^ 2‖
        = V x * (ψ ((u n : Work.BoseSym.Conf N → ℝ) x)) ^ 2 := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hV0 x), abs_of_nonneg (sq_nonneg _)]
      _ ≤ V x * C ^ 2 := mul_le_mul_of_nonneg_left hsq (hV0 x)
      _ = C ^ 2 * V x := by ring
  have hInt_v : Integrable
      (fun x => V x * (ψ ((v : Work.BoseSym.Conf N → ℝ) x)) ^ 2)
      ((volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L)) := by
    refine Integrable.mono' (hVint.const_mul (C^2)) (hVint.aestronglyMeasurable.mul hmeas_v) ?_
    filter_upwards with x
    have hsq : (ψ ((v : Work.BoseSym.Conf N → ℝ) x)) ^ 2 ≤ C ^ 2 := by
      have h1 := psi_sq_bound hψC ((v : Work.BoseSym.Conf N → ℝ) x)
      rwa [abs_of_nonneg (sq_nonneg _)] at h1
    calc ‖V x * (ψ ((v : Work.BoseSym.Conf N → ℝ) x)) ^ 2‖
        = V x * (ψ ((v : Work.BoseSym.Conf N → ℝ) x)) ^ 2 := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hV0 x), abs_of_nonneg (sq_nonneg _)]
      _ ≤ V x * C ^ 2 := mul_le_mul_of_nonneg_left hsq (hV0 x)
      _ = C ^ 2 * V x := by ring
  have hInt_abs : Integrable
      (fun x => |V x * (ψ ((u n : Work.BoseSym.Conf N → ℝ) x)) ^ 2
        - V x * (ψ ((v : Work.BoseSym.Conf N → ℝ) x)) ^ 2|)
      ((volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L)) := by
    have h1 := (hInt_u.sub hInt_v).norm
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using h1
  have hInt_min : Integrable (fun x => V x - min (V x) (M₀ : ℝ))
      ((volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L)) := by
    refine Integrable.mono' hVint (hVint.aestronglyMeasurable.sub ?_) ?_
    · exact (hVint.aestronglyMeasurable.aemeasurable.min aemeasurable_const).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (min_le_left _ _))]
      exact sub_le_self _ (le_min (hV0 x) hMnn)
  have h1i : Integrable (fun x => 2 * C * (M₀ : ℝ) *
      |(u n : Work.BoseSym.Conf N → ℝ) x - (v : Work.BoseSym.Conf N → ℝ) x|)
      ((volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L)) :=
    (integrable_abs_sub_box (N := N) (L := L) (u n) v).const_mul _
  have h2i : Integrable (fun x => 2 * C ^ 2 * (V x - min (V x) (M₀ : ℝ)))
      ((volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L)) :=
    hInt_min.const_mul _
  have hInt_bd : Integrable (fun x => 2 * C * (M₀ : ℝ) *
        |(u n : Work.BoseSym.Conf N → ℝ) x - (v : Work.BoseSym.Conf N → ℝ) x|
      + 2 * C ^ 2 * (V x - min (V x) (M₀ : ℝ)))
      ((volume : Measure (Work.BoseSym.Conf N)).restrict (BoseGases.box N L)) := h1i.add h2i
  -- the two error terms
  have hM2 : 2 * C ^ 2 * (∫ x in BoseGases.box N L, (V x - min (V x) (M₀ : ℝ))) < η / 2 := by
    have hpos : 0 < 2 * C ^ 2 := by positivity
    calc 2 * C ^ 2 * (∫ x in BoseGases.box N L, (V x - min (V x) (M₀ : ℝ)))
        < 2 * C ^ 2 * (η / (4 * C ^ 2)) := mul_lt_mul_of_pos_left hnB hpos
      _ = η / 2 := by field_simp; ring
  have hpt : ∀ x, |V x * (ψ ((u n : Work.BoseSym.Conf N → ℝ) x)) ^ 2
        - V x * (ψ ((v : Work.BoseSym.Conf N → ℝ) x)) ^ 2| ≤
      2 * C * (M₀ : ℝ) * |(u n : Work.BoseSym.Conf N → ℝ) x - (v : Work.BoseSym.Conf N → ℝ) x|
        + 2 * C ^ 2 * (V x - min (V x) (M₀ : ℝ)) :=
    fun x => pointwise_le hV0 hψC hψlip hMnn x _ _
  rw [Real.dist_eq]
  calc |(∫ x in BoseGases.box N L, V x * (ψ ((u n : Work.BoseSym.Conf N → ℝ) x)) ^ 2)
        - (∫ x in BoseGases.box N L, V x * (ψ ((v : Work.BoseSym.Conf N → ℝ) x)) ^ 2)|
      = |∫ x in BoseGases.box N L, (V x * (ψ ((u n : Work.BoseSym.Conf N → ℝ) x)) ^ 2
          - V x * (ψ ((v : Work.BoseSym.Conf N → ℝ) x)) ^ 2)| := by
        rw [integral_sub hInt_u hInt_v]
    _ ≤ ∫ x in BoseGases.box N L, |V x * (ψ ((u n : Work.BoseSym.Conf N → ℝ) x)) ^ 2
          - V x * (ψ ((v : Work.BoseSym.Conf N → ℝ) x)) ^ 2| := abs_integral_le_integral_abs
    _ ≤ ∫ x in BoseGases.box N L, (2 * C * (M₀ : ℝ) *
          |(u n : Work.BoseSym.Conf N → ℝ) x - (v : Work.BoseSym.Conf N → ℝ) x|
        + 2 * C ^ 2 * (V x - min (V x) (M₀ : ℝ))) :=
        integral_mono hInt_abs hInt_bd hpt
    _ = 2 * C * (M₀ : ℝ) * (∫ x in BoseGases.box N L,
          |(u n : Work.BoseSym.Conf N → ℝ) x - (v : Work.BoseSym.Conf N → ℝ) x|)
        + 2 * C ^ 2 * (∫ x in BoseGases.box N L, (V x - min (V x) (M₀ : ℝ))) := by
        rw [integral_add h1i h2i, integral_const_mul, integral_const_mul]
    _ < η / 2 + η / 2 := add_lt_add hnA hM2
    _ = η := by ring

theorem potBox_eventually_le {N : ℕ} {L : ℝ} {V : Work.BoseSym.Conf N → ℝ}
    (hV0 : 0 ≤ V) (hVint : Work.BoseSym.IntOnBox N L V)
    {ψ : ℝ → ℝ} (hψm : Measurable ψ) {C : ℝ} (hC : 0 ≤ C) (hψC : ∀ t, |ψ t| ≤ C)
    (hψlip : ∀ a b, |ψ a - ψ b| ≤ |a - b|)
    {u : ℕ → Work.BoseSym.L2 N} {v : Work.BoseSym.L2 N}
    (h : Filter.Tendsto u Filter.atTop (nhds v)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      (∫ x in BoseGases.box N L, V x * (ψ ((u n : Work.BoseSym.Conf N → ℝ) x)) ^ 2)
        ≤ (∫ x in BoseGases.box N L, V x * (ψ ((v : Work.BoseSym.Conf N → ℝ) x)) ^ 2) + ε := by
  by_cases hC0 : C = 0
  · -- `ψ ≡ 0`, both integrals vanish
    have hψ0 : ∀ t, ψ t = 0 := fun t =>
      abs_eq_zero.mp (le_antisymm (by simpa [hC0] using hψC t) (abs_nonneg (ψ t)))
    refine Filter.Eventually.of_forall (fun n => ?_)
    have h1 : (∫ x in BoseGases.box N L, V x * (ψ ((u n : Work.BoseSym.Conf N → ℝ) x)) ^ 2)
        = 0 := by
      have hz : (fun x => V x * (ψ ((u n : Work.BoseSym.Conf N → ℝ) x)) ^ 2) = fun _ => (0:ℝ) := by
        funext x
        rw [hψ0 ((u n : Work.BoseSym.Conf N → ℝ) x), zero_pow (by norm_num : (2:ℕ) ≠ 0),
          mul_zero]
      rw [hz]
      simp
    have h2 : (∫ x in BoseGases.box N L, V x * (ψ ((v : Work.BoseSym.Conf N → ℝ) x)) ^ 2)
        = 0 := by
      have hz : (fun x => V x * (ψ ((v : Work.BoseSym.Conf N → ℝ) x)) ^ 2) = fun _ => (0:ℝ) := by
        funext x
        rw [hψ0 ((v : Work.BoseSym.Conf N → ℝ) x), zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero]
      rw [hz]
      simp
    rw [h1, h2]
    linarith
  · -- `C > 0`: use the continuity of the functional
    have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hcore := tendsto_int_mul_psiSq hV0 hVint hψm hCpos hψC hψlip h
    have hmem : (∫ x in BoseGases.box N L, V x * (ψ ((v : Work.BoseSym.Conf N → ℝ) x)) ^ 2)
        ∈ Set.Iio ((∫ x in BoseGases.box N L, V x * (ψ ((v : Work.BoseSym.Conf N → ℝ) x)) ^ 2)
          + ε) := by
      simp only [Set.mem_Iio]
      linarith
    exact (hcore.eventually (IsOpen.mem_nhds isOpen_Iio hmem)).mono (fun n hn => le_of_lt hn)

end Work.BoseSym.Trunc
