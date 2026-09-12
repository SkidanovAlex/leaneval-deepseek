import ChallengeDeps
import Submission.Metric
import Submission.MetricCont
import Submission.MetricConst
import Submission.ChartArc
import Submission.Rigidity
import Mathlib

/-!
# Uniqueness of locally-linear extensions (ULU)

Theorem: `Submission.locallyLinear_ext_unique`.

Two locally-linear curves of the same speed `c` on the same interval `(a,β)` that agree on a
left subinterval `(a,b)` (`a < b ≤ β`) agree on all of `(a,β)`.
-/

open scoped Manifold ENNReal ContDiff Topology
open Set Filter Metric
open Bundle

namespace Submission

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

/-- If two continuous functions agree on a left-neighbourhood `(a, t₀)` of `t₀`, they agree
at `t₀`. -/
private lemma eq_of_cont_agree_left {M : Type*} [TopologicalSpace M] [T2Space M]
    {γ₁ γ₂ : ℝ → M} {a t₀ : ℝ} (hγ₁ : ContinuousAt γ₁ t₀) (hγ₂ : ContinuousAt γ₂ t₀)
    (ha : a < t₀) (hagree : ∀ u : ℝ, a < u → u < t₀ → γ₁ u = γ₂ u) : γ₁ t₀ = γ₂ t₀ := by
  let F : Filter ℝ := 𝓝[Iio t₀] t₀
  have hmem : Ioo a t₀ ∈ F := by
    dsimp [F]
    rw [nhdsWithin]
    rw [Filter.mem_inf_principal]
    refine Filter.mem_of_superset (isOpen_Ioi.mem_nhds ha) ?_
    intro u hu hlt
    exact ⟨hu, hlt⟩
  have heq : γ₁ =ᶠ[F] γ₂ := by
    refine Filter.mem_of_superset hmem ?_
    intro u hu
    exact hagree u hu.1 hu.2
  have hγ₁F : Tendsto γ₁ F (𝓝 (γ₁ t₀)) := (hγ₁.tendsto).mono_left nhdsWithin_le_nhds
  have hγ₂F₁ : Tendsto γ₂ F (𝓝 (γ₁ t₀)) := hγ₁F.congr' heq
  have hγ₂F₂ : Tendsto γ₂ F (𝓝 (γ₂ t₀)) := (hγ₂.tendsto).mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hγ₂F₁ hγ₂F₂

/-- Local two-sided agreement: two locally linear curves of equal positive speed `c` on
`(a,β)` that agree on the left neighbourhood `(a,t₀)` of an interior point `t₀` agree on a
full two-sided window around `t₀`. -/
private lemma agree_window {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    {a β : ℝ} {c : NNReal} {γ₁ γ₂ : ℝ → M}
    (hγ₁ : Metric.IsLocLinear a β c γ₁) (hγ₂ : Metric.IsLocLinear a β c γ₂)
    (hc : 0 < c) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a β)
    (hagree : ∀ u, a < u → u < t₀ → γ₁ u = γ₂ u) :
    ∃ ε > 0, ∀ u, |u - t₀| < ε → γ₁ u = γ₂ u := by
  classical
  -- p : the common value of both curves at t₀
  let p : M := γ₁ t₀
  have hγ₁cont : ContinuousAt γ₁ t₀ := Submission.Metric.IsLocLinear.continuousAt hγ₁ ht₀
  have hγ₂cont : ContinuousAt γ₂ t₀ := Submission.Metric.IsLocLinear.continuousAt hγ₂ ht₀
  have hpt₀ : γ₂ t₀ = p := by
    dsimp [p]
    exact (eq_of_cont_agree_left hγ₁cont hγ₂cont ht₀.1 hagree).symm
  -- normal-coordinate data at p (arc_rigidity)
  rcases arc_rigidity (I := I) (M := M) p with ⟨ρ₀, hρ₀, ge, hgeC, hgeSymm, hgePos, hgeAgree, hrest⟩
  rcases hrest with ⟨r, hr0, ExpM, S, invM, hExpM0, hSnhds, hS_in, hExpCont, hInj,
    hSurj, hInvS, hInvExp, hRadial, hrest2⟩
  rcases hrest2 with ⟨ρa, hρa0, hρale, hArc, hRigid⟩
  let x₀ : E := extChartAt I p p
  -- Euclidean-vs-metric norm bound
  rcases unit_norm_bound (ge x₀) (hgePos x₀) with ⟨K, hK0, hKbound⟩
  -- windows of the two curves at t₀
  rcases hγ₁ t₀ ht₀ with ⟨δ₁, hδ₁pos, hwin₁⟩
  rcases hγ₂ t₀ ht₀ with ⟨δ₂, hδ₂pos, hwin₂⟩
  let cR : ℝ := (c : ℝ)
  have hcR0 : (0 : ℝ) < cR := by
    simpa [cR] using (show (0 : ℝ) < (c : ℝ) by exact_mod_cast hc)
  have hcRne : cR ≠ 0 := ne_of_gt hcR0
  have hKc0 : 0 < K * cR := mul_pos hK0 hcR0
  have hta : 0 < t₀ - a := sub_pos.mpr ht₀.1
  have htb : 0 < β - t₀ := sub_pos.mpr ht₀.2
  let δ : ℝ := min δ₁ (min δ₂ (min (t₀ - a) (min (β - t₀) (min (ρa / cR) (r / (K * cR))))))
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδ₁pos (lt_min hδ₂pos (lt_min hta (lt_min htb (lt_min (div_pos hρa0 hcR0) (div_pos hr0 hKc0)))))
  have hδ_le₁ : δ ≤ δ₁ := by dsimp [δ]; exact min_le_left _ _
  have hδ_le₂ : δ ≤ δ₂ := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_ta : δ ≤ t₀ - a := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ_tb : δ ≤ β - t₀ := by
    dsimp [δ]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδ_ρa : cR * δ ≤ ρa := by
    have hle : δ ≤ ρa / cR := by
      calc
        δ ≤ min δ₂ (min (t₀ - a) (min (β - t₀) (min (ρa / cR) (r / (K * cR))))) := by
          dsimp [δ]
          exact min_le_right δ₁ (min δ₂ (min (t₀ - a) (min (β - t₀) (min (ρa / cR) (r / (K * cR))))))
        _ ≤ min (t₀ - a) (min (β - t₀) (min (ρa / cR) (r / (K * cR)))) := by
          exact min_le_right δ₂ (min (t₀ - a) (min (β - t₀) (min (ρa / cR) (r / (K * cR)))))
        _ ≤ min (β - t₀) (min (ρa / cR) (r / (K * cR))) := by
          exact min_le_right (t₀ - a) (min (β - t₀) (min (ρa / cR) (r / (K * cR))))
        _ ≤ min (ρa / cR) (r / (K * cR)) := by
          exact min_le_right (β - t₀) (min (ρa / cR) (r / (K * cR)))
        _ ≤ ρa / cR := by
          exact min_le_left (ρa / cR) (r / (K * cR))
    calc
      cR * δ ≤ cR * (ρa / cR) := mul_le_mul_of_nonneg_left hle hcR0.le
      _ = ρa := by field_simp [hcRne]
  have hδ_r : δ * (K * cR) ≤ r := by
    have hle : δ ≤ r / (K * cR) := by
      calc
        δ ≤ min δ₂ (min (t₀ - a) (min (β - t₀) (min (ρa / cR) (r / (K * cR))))) := by
          dsimp [δ]
          exact min_le_right δ₁ (min δ₂ (min (t₀ - a) (min (β - t₀) (min (ρa / cR) (r / (K * cR))))))
        _ ≤ min (t₀ - a) (min (β - t₀) (min (ρa / cR) (r / (K * cR)))) := by
          exact min_le_right δ₂ (min (t₀ - a) (min (β - t₀) (min (ρa / cR) (r / (K * cR)))))
        _ ≤ min (β - t₀) (min (ρa / cR) (r / (K * cR))) := by
          exact min_le_right (t₀ - a) (min (β - t₀) (min (ρa / cR) (r / (K * cR))))
        _ ≤ min (ρa / cR) (r / (K * cR)) := by
          exact min_le_right (β - t₀) (min (ρa / cR) (r / (K * cR)))
        _ ≤ r / (K * cR) := by
          exact min_le_right (ρa / cR) (r / (K * cR))
    calc
      δ * (K * cR) ≤ (r / (K * cR)) * (K * cR) :=
        mul_le_mul_of_nonneg_right hle hKc0.le
      _ = r := by field_simp [ne_of_gt hKc0]
  -- t₀ + u stays inside (a,β) for |u| < δ
  have h_shift_in {u : ℝ} (hu : |u| < δ) : t₀ + u ∈ Ioo a β := by
    constructor
    · have hu1 : -δ < u := (abs_lt.mp hu).1
      have h1 : t₀ - δ < t₀ + u := by linarith
      have h2 : a ≤ t₀ - δ := by
        calc
          a = t₀ - (t₀ - a) := by ring
          _ ≤ t₀ - δ := by linarith [hδ_ta]
      exact lt_of_le_of_lt h2 h1
    · have hu2 : u < δ := (abs_lt.mp hu).2
      have h1 : t₀ + u < t₀ + δ := by linarith
      have h2 : t₀ + δ ≤ β := by
        calc
          t₀ + δ ≤ t₀ + (β - t₀) := by linarith [hδ_tb]
          _ = β := by ring
      exact lt_of_lt_of_le h1 h2
  -- shifted curve exactness: for |s|,|t| < δ the edist identity holds on the δᵢ-window
  have hwin_exact₁ (s t : ℝ) (hs : |s| < δ) (ht : |t| < δ) :
      edist (γ₁ (t₀ + s)) (γ₁ (t₀ + t)) = (c : ℝ≥0∞) * ENNReal.ofReal |t - s| := by
    have hsδ₁ : |s| < δ₁ := lt_of_lt_of_le hs hδ_le₁
    have htδ₁ : |t| < δ₁ := lt_of_lt_of_le ht hδ_le₁
    have hs' : t₀ + s ∈ Ioo (max a (t₀ - δ₁)) (min β (t₀ + δ₁)) := by
      exact (Metric.IsLocLinear.window_mem_iff (s := t₀ + s) (t₀ := t₀) (δ := δ₁)
        (h_shift_in hs) hδ₁pos).mpr ⟨by linarith [(abs_lt.mp hsδ₁).1], by linarith [(abs_lt.mp hsδ₁).2]⟩
    have ht' : t₀ + t ∈ Ioo (max a (t₀ - δ₁)) (min β (t₀ + δ₁)) := by
      exact (Metric.IsLocLinear.window_mem_iff (s := t₀ + t) (t₀ := t₀) (δ := δ₁)
        (h_shift_in ht) hδ₁pos).mpr ⟨by linarith [(abs_lt.mp htδ₁).1], by linarith [(abs_lt.mp htδ₁).2]⟩
    have hw := hwin₁ (t₀ + s) (t₀ + t) hs' ht'
    have hsub : (t₀ + t) - (t₀ + s) = t - s := by ring
    calc
      edist (γ₁ (t₀ + s)) (γ₁ (t₀ + t)) = (c : ℝ≥0∞) * ENNReal.ofReal |(t₀ + t) - (t₀ + s)| := hw
      _ = (c : ℝ≥0∞) * ENNReal.ofReal |t - s| := by rw [hsub]
  have hwin_exact₂ (s t : ℝ) (hs : |s| < δ) (ht : |t| < δ) :
      edist (γ₂ (t₀ + s)) (γ₂ (t₀ + t)) = (c : ℝ≥0∞) * ENNReal.ofReal |t - s| := by
    have hsδ₂ : |s| < δ₂ := lt_of_lt_of_le hs hδ_le₂
    have htδ₂ : |t| < δ₂ := lt_of_lt_of_le ht hδ_le₂
    have hs' : t₀ + s ∈ Ioo (max a (t₀ - δ₂)) (min β (t₀ + δ₂)) := by
      exact (Metric.IsLocLinear.window_mem_iff (s := t₀ + s) (t₀ := t₀) (δ := δ₂)
        (h_shift_in hs) hδ₂pos).mpr ⟨by linarith [(abs_lt.mp hsδ₂).1], by linarith [(abs_lt.mp hsδ₂).2]⟩
    have ht' : t₀ + t ∈ Ioo (max a (t₀ - δ₂)) (min β (t₀ + δ₂)) := by
      exact (Metric.IsLocLinear.window_mem_iff (s := t₀ + t) (t₀ := t₀) (δ := δ₂)
        (h_shift_in ht) hδ₂pos).mpr ⟨by linarith [(abs_lt.mp htδ₂).1], by linarith [(abs_lt.mp htδ₂).2]⟩
    have hw := hwin₂ (t₀ + s) (t₀ + t) hs' ht'
    have hsub : (t₀ + t) - (t₀ + s) = t - s := by ring
    calc
      edist (γ₂ (t₀ + s)) (γ₂ (t₀ + t)) = (c : ℝ≥0∞) * ENNReal.ofReal |(t₀ + t) - (t₀ + s)| := hw
      _ = (c : ℝ≥0∞) * ENNReal.ofReal |t - s| := by rw [hsub]
  -- apply rigidity to each shifted curve
  let γ₁' : ℝ → M := fun u => γ₁ (t₀ + u)
  let γ₂' : ℝ → M := fun u => γ₂ (t₀ + u)
  have hγ₁'0 : γ₁' 0 = p := by simp [γ₁', p]
  have hγ₂'0 : γ₂' 0 = p := by simp [γ₂', p, hpt₀]
  have hρaδ : (c : ℝ) * δ ≤ ρa := by simpa [cR] using hδ_ρa
  rcases hRigid c hc γ₁' δ hγ₁'0 hδpos hρaδ hwin_exact₁ with ⟨v₁, hv₁, hrep₁⟩
  rcases hRigid c hc γ₂' δ hγ₂'0 hδpos hρaδ hwin_exact₂ with ⟨v₂, hv₂, hrep₂⟩
  -- membership of small multiples of vᵢ in the injectivity ball
  have hvball {i : E} (hvi : Real.sqrt ((ge x₀) i i) = (c : ℝ)) {u : ℝ} (hu : |u| < δ) :
      u • i ∈ ball (0 : E) r := by
    rw [mem_ball, dist_eq_norm, sub_zero]
    have hb := unit_norm_bound_all (ge x₀) (hgePos x₀) K hK0.le
      (fun V hV => hKbound V hV) i
    have hle1 : ‖i‖ ≤ K * cR := by
      calc
        ‖i‖ ≤ K * Real.sqrt ((ge x₀) i i) := hb
        _ = K * cR := by simpa [cR] using congrArg (fun z : ℝ => K * z) hvi
    have hlt1 : |u| * ‖i‖ < r := by
      calc
        |u| * ‖i‖ ≤ |u| * (K * cR) := mul_le_mul_of_nonneg_left hle1 (abs_nonneg u)
        _ < δ * (K * cR) := mul_lt_mul_of_pos_right hu hKc0
        _ ≤ r := hδ_r
    have hnorm : ‖u • i‖ = |u| * ‖i‖ := by rw [norm_smul, Real.norm_eq_abs]
    rwa [hnorm]
  -- agreement on a negative point forces v₁ = v₂
  have hneqδ : δ / 2 < δ := by linarith [hδpos]
  have huδ : |-(δ / 2)| < δ := by
    rw [abs_neg]
    rw [abs_of_pos (half_pos hδpos)]
    exact hneqδ
  have hneg_agree : γ₁ (t₀ + (-(δ / 2))) = γ₂ (t₀ + (-(δ / 2))) := by
    refine hagree (t₀ - δ / 2) ?_ ?_
    · linarith [hδ_ta, hδpos]
    · linarith
  have hExp_eq : ExpM ((-(δ / 2)) • v₁) = ExpM ((-(δ / 2)) • v₂) := by
    have hr1 := hrep₁ (-(δ / 2)) huδ
    have hr2 := hrep₂ (-(δ / 2)) huδ
    calc
      ExpM ((-(δ / 2)) • v₁) = γ₁ (t₀ + (-(δ / 2))) := by simpa [γ₁'] using hr1.symm
      _ = γ₂ (t₀ + (-(δ / 2))) := hneg_agree
      _ = ExpM ((-(δ / 2)) • v₂) := by simpa [γ₂'] using hr2
  have hv₁m : (-(δ / 2)) • v₁ ∈ ball (0 : E) r := hvball hv₁ huδ
  have hv₂m : (-(δ / 2)) • v₂ ∈ ball (0 : E) r := hvball hv₂ huδ
  have hsubeq : (⟨(-(δ / 2)) • v₁, hv₁m⟩ : {v : E // v ∈ ball (0 : E) r}) =
      ⟨(-(δ / 2)) • v₂, hv₂m⟩ := by
    exact hInj (by simpa using hExp_eq)
  have hsmul : (-(δ / 2)) • v₁ = (-(δ / 2)) • v₂ := by
    exact congrArg Subtype.val hsubeq
  have hnegne : -(δ / 2) ≠ 0 := by linarith
  have hveq : v₁ = v₂ := by
    have hcancel : v₁ = (-(δ / 2))⁻¹ • ((-(δ / 2)) • v₁) := by
      calc
        v₁ = (1 : ℝ) • v₁ := by simp
        _ = ((-(δ / 2))⁻¹ * (-(δ / 2))) • v₁ := by
          rw [inv_mul_cancel₀ hnegne]
        _ = (-(δ / 2))⁻¹ • ((-(δ / 2)) • v₁) := by rw [smul_smul]
    calc
      v₁ = (-(δ / 2))⁻¹ • ((-(δ / 2)) • v₁) := hcancel
      _ = (-(δ / 2))⁻¹ • ((-(δ / 2)) • v₂) := by rw [hsmul]
      _ = v₂ := by
        have hcancel2 : v₂ = (-(δ / 2))⁻¹ • ((-(δ / 2)) • v₂) := by
          calc
            v₂ = (1 : ℝ) • v₂ := by simp
            _ = ((-(δ / 2))⁻¹ * (-(δ / 2))) • v₂ := by
              rw [inv_mul_cancel₀ hnegne]
            _ = (-(δ / 2))⁻¹ • ((-(δ / 2)) • v₂) := by rw [smul_smul]
        exact hcancel2.symm
  -- conclude two-sided agreement
  refine ⟨δ, hδpos, ?_⟩
  intro u hu
  let s : ℝ := u - t₀
  have hsδ : |s| < δ := by simpa [s] using hu
  have h₁ := hrep₁ s hsδ
  have h₂ := hrep₂ s hsδ
  calc
    γ₁ u = γ₁ (t₀ + s) := by congr 1; dsimp [s]; ring
    _ = ExpM (s • v₁) := by simpa [γ₁'] using h₁
    _ = ExpM (s • v₂) := by rw [hveq]
    _ = γ₂ (t₀ + s) := by simpa [γ₂'] using h₂.symm
    _ = γ₂ u := by congr 1; dsimp [s]; ring

theorem locallyLinear_ext_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    {a b β : ℝ} {c : NNReal} {γ₁ γ₂ : ℝ → M}
    (hab : a < b) (hbβ : b ≤ β)
    (hγ₁ : Metric.IsLocLinear a β c γ₁) (hγ₂ : Metric.IsLocLinear a β c γ₂)
    (hag : ∀ t ∈ Ioo a b, γ₁ t = γ₂ t) :
    ∀ t ∈ Ioo a β, γ₁ t = γ₂ t := by
  classical
  by_cases hc0 : c = 0
  · -- speed zero: both curves are constant on (a,β)
    have hγ₁0 : Metric.IsLocLinear a β 0 γ₁ := by simpa [hc0] using hγ₁
    have hγ₂0 : Metric.IsLocLinear a β 0 γ₂ := by simpa [hc0] using hγ₂
    intro t ht
    have hmid : (a + b) / 2 ∈ Ioo a b := by
      constructor <;> linarith [hab]
    have hmidβ : (a + b) / 2 ∈ Ioo a β := by
      constructor
      · linarith [hab]
      · exact lt_of_lt_of_le (by linarith [hab]) hbβ
    calc
      γ₁ t = γ₁ ((a + b) / 2) := Metric.IsLocLinear.eq_of_speed_zero (a := a) (b := β) hγ₁0 ht hmidβ
      _ = γ₂ ((a + b) / 2) := hag ((a + b) / 2) hmid
      _ = γ₂ t := Metric.IsLocLinear.eq_of_speed_zero (a := a) (b := β) hγ₂0 hmidβ ht
  · -- 0 < c
    have hc : 0 < c := lt_of_le_of_ne c.2 (Ne.symm hc0)
    let X : Type := {x : ℝ // x ∈ Ioo a β}
    letI : PreconnectedSpace X := Subtype.preconnectedSpace (isPreconnected_Ioo (a := a) (b := β))
    let Good : Set X := {x | ∀ u : ℝ, a < u → u ≤ x.1 → γ₁ u = γ₂ u}
    -- Good is nonempty
    have hGood_nonempty : Good.Nonempty := by
      refine ⟨⟨(a + b) / 2, ?_⟩, ?_⟩
      · constructor
        · linarith [hab]
        · exact lt_of_lt_of_le (by linarith [hab]) hbβ
      · intro u hu1 hu2
        apply hag
        constructor
        · exact hu1
        · linarith [hab, hu2]
    -- Good is open
    have hGood_open : IsOpen Good := by
      rw [isOpen_iff_mem_nhds]
      intro x₀ hx₀
      let t₀ : ℝ := x₀.1
      have ht₀ : t₀ ∈ Ioo a β := by simpa [t₀] using x₀.2
      have hagree : ∀ u : ℝ, a < u → u < t₀ → γ₁ u = γ₂ u := by
        intro u hu1 hu2
        exact hx₀ u hu1 (le_of_lt hu2)
      rcases agree_window (I := I) (M := M) hγ₁ hγ₂ hc ht₀ hagree with ⟨ε, hεpos, hwin⟩
      let U : Set X := (fun x : X => x.1) ⁻¹' (ball t₀ ε)
      have hUopen : IsOpen U := IsOpen.preimage continuous_subtype_val isOpen_ball
      have hx₀U : x₀ ∈ U := by
        dsimp [U, t₀]
        rw [mem_preimage, mem_ball, dist_self]
        exact hεpos
      have hUsub : U ⊆ Good := by
        intro y hy u hu1 hu2
        by_cases hut : u ≤ t₀
        · exact hx₀ u hu1 hut
        · have htg : t₀ < u := lt_of_not_ge hut
          have hyε : |y.1 - t₀| < ε := by simpa [U, mem_ball, Real.dist_eq] using hy
          have hnon : 0 ≤ u - t₀ := by linarith
          have h1 : u - t₀ ≤ y.1 - t₀ := by linarith
          have huε : |u - t₀| < ε := by
            rw [abs_of_nonneg hnon]
            exact lt_of_le_of_lt h1 (lt_of_le_of_lt (le_abs_self (y.1 - t₀)) hyε)
          exact hwin u huε
      exact mem_of_superset (hUopen.mem_nhds hx₀U) hUsub
    -- Good is closed
    have hGood_closed : IsClosed Good := by
      apply isClosed_of_closure_subset
      intro x₀ hx₀cl
      let t₀ : ℝ := x₀.1
      have ht₀ : t₀ ∈ Ioo a β := by simpa [t₀] using x₀.2
      have hag_below : ∀ u : ℝ, a < u → u < t₀ → γ₁ u = γ₂ u := by
        intro u hu1 hu2
        let O : Set X := (fun x : X => x.1) ⁻¹' (ball t₀ ((t₀ - u) / 2))
        have hOopen : IsOpen O := IsOpen.preimage continuous_subtype_val isOpen_ball
        have hx₀O : x₀ ∈ O := by
          dsimp [O, t₀]
          rw [mem_preimage, mem_ball, dist_self]
          linarith [hu2]
        rcases mem_closure_iff.mp hx₀cl O hOopen hx₀O with ⟨y, hyO, hyG⟩
        have hyε : |y.1 - t₀| < (t₀ - u) / 2 := by simpa [O, mem_ball, Real.dist_eq] using hyO
        have hyu : u < y.1 := by
          have hylow := (abs_lt.mp hyε).1
          linarith
        exact hyG u hu1 (le_of_lt hyu)
      have heq_t₀ : γ₁ t₀ = γ₂ t₀ := by
        exact eq_of_cont_agree_left (Submission.Metric.IsLocLinear.continuousAt hγ₁ ht₀)
          (Submission.Metric.IsLocLinear.continuousAt hγ₂ ht₀) ht₀.1 hag_below
      -- x₀ ∈ Good
      intro u hu1 hu2
      rcases lt_or_eq_of_le hu2 with hult | heq
      · exact hag_below u hu1 hult
      · rw [heq]
        exact heq_t₀
    -- Good = univ by preconnectedness
    have hGood_clopen : IsClopen Good := ⟨hGood_closed, hGood_open⟩
    have hGood_univ : Good = univ := by
      rcases (isClopen_iff.mp hGood_clopen) with h | h
      · exfalso
        rw [h] at hGood_nonempty
        exact Set.not_nonempty_empty hGood_nonempty
      · exact h
    intro t ht
    have hGood_t : (⟨t, ht⟩ : X) ∈ Good := by
      rw [hGood_univ]
      trivial
    exact hGood_t t ht.1 le_rfl


end Submission
