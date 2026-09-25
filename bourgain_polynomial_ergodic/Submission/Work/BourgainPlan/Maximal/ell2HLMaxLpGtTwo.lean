import Mathlib
import Submission.Commons.Analysis.Maximal.real_maximal_strong_type
import Submission.Commons.Analysis.Maximal.lintegral_rpow_hlMax_le
import Submission.Work.BourgainPlan.Maximal.ell2Maximal
import Submission.Work.BourgainPlan.Maximal.ell2MaxAux
import Submission.Work.BourgainPlan.Maximal.ell2MaxLpGtTwo
import Submission.Work.BourgainPlan.Maximal.lintegral_mul_mul_le

/-!
# The `ℓ²`-valued Hardy--Littlewood maximal inequality on `L^p(ℓ²)` for `p > 2`

Target: for `p > 2`, with a constant uniform in the number `n` of components,

`∫⁻ (Σ_t (hlMax ‖f_t‖)²)^{p/2} ≤ C^p ∫⁻ (Σ_t ‖f_t‖²)^{p/2}`,

where `hlMax` is the corpus's centred Hardy--Littlewood maximal function
(`Commons.Analysis.Maximal.hlMax`).  This is the `p > 2` half of Mirek--Stein--Trojan's input
`(eq:47)` for the *centred* maximal function; the `1 < p < 2` half is `ell2HLMaxLpLtTwo`.

The proof follows the dyadic blueprint of `ell2MaxLpGtTwo` (`p > 2`), i.e. the weighted
Calderón--Zygmund (Cotlar) inequality

`∫ (hlMax ψ)² w ≤ 4 ∫ ψ (hlMax ψ) (hlMax w)`

followed by the bootstrap with the weight `w = (Σ_t (hlMax ‖f_t‖)²)^{(p-2)/2}`.  The weighted
Cotlar inequality is proved from the level-set inequality

`c · ∫_{hlMax ψ > c} w ≤ 4 ∫_{hlMax ψ > c} ψ · hlMax w`

(Vitali covering of the level set by good intervals) plus the layer cake.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

open Commons.Analysis.Maximal (hlMax hlMax_le_of_mem measurable_hlMax)

/-! ### Elementary properties of `hlMax` -/

private lemma ofReal_inv_mul_self_le_one (r : ℝ) : ENNReal.ofReal r⁻¹ * ENNReal.ofReal r ≤ 1 := by
  rcases le_total 0 r with h | h
  · rcases eq_or_ne r 0 with hr | hr
    · subst hr; simp
    · rw [← ENNReal.ofReal_mul (inv_nonneg.mpr h), inv_mul_cancel₀ hr]
      simp
  · rw [ENNReal.ofReal_eq_zero.mpr h, mul_zero]
    exact zero_le_one

private lemma ofReal_mul_ofReal_inv {x : ℝ} (hx : 0 < x) :
    ENNReal.ofReal x * ENNReal.ofReal x⁻¹ = 1 := by
  rw [← ENNReal.ofReal_mul hx.le, mul_inv_cancel₀ hx.ne', ENNReal.ofReal_one]

lemma hlMax_mono {f g : ℝ → ℝ≥0∞} (h : f ≤ g) (x : ℝ) : hlMax f x ≤ hlMax g x := by
  rw [hlMax, hlMax]
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
  exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hab (mul_le_mul_right (lintegral_mono h) _)))

/-- `hlMax φ x ≤ ⨆ y, φ y`. -/
lemma hlMax_le_iSup (φ : ℝ → ℝ≥0∞) (x : ℝ) : hlMax φ x ≤ ⨆ y, φ y := by
  rw [hlMax]
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
  have h2 : ∫⁻ y in Set.Icc a b, (⨆ z, φ z) = (⨆ z, φ z) * ENNReal.ofReal (b - a) := by
    rw [setLIntegral_const, Real.volume_Icc]
  have h1 : ∫⁻ y in Set.Icc a b, φ y ≤ (⨆ z, φ z) * ENNReal.ofReal (b - a) := by
    rw [← h2]; exact lintegral_mono fun y => le_iSup φ y
  calc ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, φ y
      ≤ ENNReal.ofReal (b - a)⁻¹ * ((⨆ z, φ z) * ENNReal.ofReal (b - a)) :=
        mul_le_mul_right h1 _
    _ = (⨆ z, φ z) * (ENNReal.ofReal (b - a)⁻¹ * ENNReal.ofReal (b - a)) := by ring
    _ ≤ (⨆ z, φ z) * 1 := mul_le_mul_right (ofReal_inv_mul_self_le_one (b - a)) _
    _ = ⨆ z, φ z := mul_one _

/-- `hlMax` commutes with the pointwise supremum of a monotone sequence of measurable
functions. -/
lemma hlMax_iSup {ψ : ℕ → ℝ → ℝ≥0∞} (hψ : ∀ N, Measurable (ψ N)) (hmono : Monotone ψ) :
    hlMax (fun y => ⨆ N, ψ N y) = fun x => ⨆ N, hlMax (ψ N) x := by
  funext x
  refine le_antisymm ?_ ?_
  · rw [hlMax]
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    have h1 : ∫⁻ y in Set.Icc a b, (⨆ N, ψ N y) = ⨆ N, ∫⁻ y in Set.Icc a b, ψ N y :=
      lintegral_iSup (fun N => hψ N) hmono
    calc ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, (⨆ N, ψ N y)
        = ENNReal.ofReal (b - a)⁻¹ * (⨆ N, ∫⁻ y in Set.Icc a b, ψ N y) := by rw [h1]
      _ = ⨆ N, ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, ψ N y := ENNReal.mul_iSup _ _
      _ ≤ ⨆ N, hlMax (ψ N) x := iSup_le fun N => le_iSup_of_le N
            (le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hab le_rfl)))
  · exact iSup_le fun N => hlMax_mono (fun y => le_iSup (fun N => ψ N y) N) x

/-- **Strong `(q,q)` type (`q > 1`) of the centred Hardy--Littlewood maximal function,
`ENNReal` form.** -/
theorem hlMaxStrongTypeENNReal {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℝ → ENNReal), Measurable ψ → (∀ x, ψ x ≠ ⊤) →
      ∫⁻ x, (hlMax ψ x) ^ q ≤ ENNReal.ofReal (C ^ q) * ∫⁻ x, ψ x ^ q := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hq1 : 0 < q - 1 := by linarith
  have h2pos : (0 : ℝ) < 2 ^ (q - 1) := Real.rpow_pos_of_pos (by norm_num) _
  set K : ℝ := 8 * q * 2 ^ (q - 1) / (q - 1) with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  refine ⟨K ^ (1 / q), Real.rpow_pos_of_pos hKpos _, fun ψ hψmeas hψfin => ?_⟩
  have hCq : (K ^ (1 / q)) ^ q = K := by
    rw [← Real.rpow_mul hKpos.le, one_div, inv_mul_cancel₀ hq0.ne', Real.rpow_one]
  by_cases htop : ∫⁻ x, ψ x ^ q = ⊤
  · rw [htop, ENNReal.mul_top]
    · exact le_top
    · rw [hCq]
      exact (ENNReal.ofReal_pos.mpr hKpos).ne'
  · have hH : ∫⁻ x, ENNReal.rpow (ψ x) q < ⊤ := lt_top_iff_ne_top.mpr htop
    have h2 := Commons.Analysis.Maximal.lintegral_rpow_hlMax_le hψmeas hψfin hq hH
    calc ∫⁻ x, (hlMax ψ x) ^ q
        ≤ ENNReal.ofReal (8 * q * 2 ^ (q - 1) / (q - 1)) * ∫⁻ x, ENNReal.rpow (ψ x) q := h2
      _ = ENNReal.ofReal ((K ^ (1 / q)) ^ q) * ∫⁻ x, ENNReal.rpow (ψ x) q := by rw [hCq, hK]

/-! ### The `ℓ²`-valued centred maximal function -/

/-- `Σ_t (hlMax (‖f t ·‖ₑ) x)²`, the square of the `ℓ²`-norm of the componentwise centred
maximal function of the family `f`. -/
noncomputable def ell2HLMax {n : ℕ} (f : Fin n → ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∑ t, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)

/-- `(Σ_t (hlMax (‖f t ·‖ₑ) x)²)^{1/2}`. -/
noncomputable def ell2HLF {n : ℕ} (f : Fin n → ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  (ell2HLMax f x) ^ ((1 : ℝ) / 2)

lemma ell2HLMax_measurable {n : ℕ} (f : Fin n → ℝ → ℝ) : Measurable (ell2HLMax f) := by
  unfold ell2HLMax
  refine Finset.measurable_sum _ fun t _ => ?_
  exact (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp (measurable_hlMax _)

lemma ell2HLF_measurable {n : ℕ} (f : Fin n → ℝ → ℝ) : Measurable (ell2HLF f) :=
  (ENNReal.continuous_rpow_const (y := (1 : ℝ) / 2)).measurable.comp (ell2HLMax_measurable f)


/-! ### The weighted level-set (Cotlar) inequality for `hlMax` -/

/-- **The weighted level-set inequality.**  For `c > 0` and any weight `w`, the level set of the
centred maximal function satisfies `c · ∫_{hlMax ψ > c} w ≤ 4 ∫_{hlMax ψ > c} ψ · hlMax w`.

This is the Vitali-covering form of the weighted Calderón--Zygmund (Cotlar) inequality: unlike the
dyadic case, the level set is not a disjoint union of good cells with average `> c` (the uncentred
maximal function's level sets are unions of intervals whose components may have average `< c`), so
the covering lemma replaces the stopping-time decomposition. -/
theorem hlMaxCZ_levelSet {ψ w : ℝ → ENNReal} (hψm : Measurable ψ) (hwm : Measurable w)
    (hψfin : ∫⁻ y, ψ y < ⊤) {c : ℝ} (hc : 0 < c) :
    ENNReal.ofReal c * ∫⁻ x in {x : ℝ | ENNReal.ofReal c < hlMax ψ x}, w x
      ≤ 4 * ∫⁻ x in {x : ℝ | ENNReal.ofReal c < hlMax ψ x}, ψ x * hlMax w x := by
  set Ω : Set ℝ := {x : ℝ | ENNReal.ofReal c < hlMax ψ x} with hΩ
  -- for each point of the level set choose an interval whose average exceeds `c`
  have hch : ∀ x : Ω, ∃ A B : ℝ, A ≤ x.1 ∧ x.1 ≤ B ∧
      ENNReal.ofReal c < ENNReal.ofReal (B - A)⁻¹ * ∫⁻ y in Set.Icc A B, ψ y := by
    intro x
    obtain ⟨a, b, ha, hb, hlt⟩ :=
      (Commons.Analysis.Maximal.hlMax_lt_iff ψ x.1 (ENNReal.ofReal c)).mp x.2
    exact ⟨a, b, ha, hb, hlt⟩
  choose A B hAB using hch
  -- the chosen intervals are nondegenerate
  have hABlt : ∀ x : Ω, A x < B x := by
    intro x
    by_contra hcon
    have hneg : (B x - A x)⁻¹ ≤ 0 := inv_nonpos.mpr (by linarith [not_lt.mp hcon])
    have hzero : ENNReal.ofReal (B x - A x)⁻¹ * (∫⁻ y in Set.Icc (A x) (B x), ψ y) = 0 := by
      rw [ENNReal.ofReal_eq_zero.mpr hneg, zero_mul]
    have hx := hAB x
    rw [hzero] at hx
    exact absurd hx.2.2 (not_lt_of_ge (ENNReal.ofReal_pos.mpr hc).le)
  -- a uniform bound on the lengths of the chosen intervals
  have hlen : ∀ x : Ω, B x - A x ≤ (∫⁻ y, ψ y).toReal / c + 1 := by
    intro x
    have hbdd : ∫⁻ y in Set.Icc (A x) (B x), ψ y ≤ ENNReal.ofReal ((∫⁻ y, ψ y).toReal) := by
      refine (lintegral_mono_set (Set.subset_univ _)).trans ?_
      rw [Measure.restrict_univ]
      exact le_of_eq (ENNReal.ofReal_toReal hψfin.ne).symm
    have hle : ENNReal.ofReal (B x - A x)⁻¹ * ∫⁻ y in Set.Icc (A x) (B x), ψ y
        ≤ ENNReal.ofReal ((B x - A x)⁻¹ * (∫⁻ y, ψ y).toReal) := by
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr (sub_nonneg.mpr (hABlt x).le))]
      exact mul_le_mul_right hbdd _
    have hlt : c < (B x - A x)⁻¹ * (∫⁻ y, ψ y).toReal := by
      refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp ?_
      exact ((hAB x).2.2).trans_le hle
    have hpos : 0 < B x - A x := sub_pos.mpr (hABlt x)
    have h1 : (B x - A x) * c < (∫⁻ y, ψ y).toReal := by
      have h := mul_lt_mul_of_pos_left hlt hpos
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul] at h
      exact h
    have h3 : B x - A x < (∫⁻ y, ψ y).toReal / c := by
      rw [lt_div_iff₀ hc]
      linarith
    linarith
  set P : Ω → ℝ := fun x => (A x + B x) / 2 with hP
  set r : Ω → ℝ := fun x => (B x - A x) / 2 with hr
  have hrpos : ∀ x : Ω, 0 < r x := by
    intro x; rw [hr]; linarith [hABlt x]
  have hrle : ∀ x : Ω, r x ≤ (∫⁻ y, ψ y).toReal / c / 2 + 1 := by
    intro x; rw [hr]; linarith [hlen x]
  obtain ⟨u, husub, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
    (t := Set.univ) P r ((∫⁻ y, ψ y).toReal / c / 2 + 1) (fun a _ => hrle a) 4 (by norm_num)
  have hbal : ∀ x : Ω, Metric.closedBall (P x) (r x) = Set.Icc (A x) (B x) := by
    intro x
    rw [Real.closedBall_eq_Icc]
    simp only [hP, hr]
    congr 1 <;> ring
  have hcount : u.Countable := hdisj.countable_of_nonempty_interior fun i _ =>
    (Metric.nonempty_ball.mpr (hrpos i)).mono Metric.ball_subset_interior_closedBall
  haveI hcount' : Countable (↑u) := hcount.to_subtype
  -- the covering of the level set
  have hcover : Ω ⊆ ⋃ b : u, Metric.closedBall (P b) (4 * r b) := by
    intro x hx
    obtain ⟨b, hbu, hb⟩ := hcov ⟨x, hx⟩ (Set.mem_univ _)
    refine Set.mem_iUnion.mpr ⟨⟨b, hbu⟩, ?_⟩
    refine hb ?_
    rw [hbal ⟨x, hx⟩]
    exact ⟨(hAB ⟨x, hx⟩).1, (hAB ⟨x, hx⟩).2.1⟩
  -- the selected intervals are contained in the level set
  have hunionSub : (⋃ b : u, Set.Icc (A b) (B b)) ⊆ Ω := by
    intro y hy
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hy
    have hle : ENNReal.ofReal (B b - A b)⁻¹ * ∫⁻ z in Set.Icc (A b) (B b), ψ z
        ≤ hlMax ψ y := hlMax_le_of_mem ψ hb.1 hb.2
    exact lt_of_lt_of_le (hAB b).2.2 hle
  have hd : Pairwise (Function.onFun Disjoint fun b : u => Set.Icc (A b) (B b)) := by
    intro b1 b2 hne
    have h := hdisj b1.2 b2.2 (fun hh => hne (Subtype.ext hh))
    rwa [Function.onFun, hbal b1, hbal b2] at h
  -- the estimate on a single selected interval
  have hkey : ∀ b : u, ENNReal.ofReal c * ∫⁻ x in Metric.closedBall (P b) (4 * r b), w x
      ≤ 4 * ∫⁻ x in Set.Icc (A b) (B b), ψ x * hlMax w x := by
    intro b
    have hbpos : 0 < B b - A b := sub_pos.mpr (hABlt b)
    have hsub : Set.Icc (A b) (B b) ⊆ Metric.closedBall (P b) (4 * r b) := by
      rw [Real.closedBall_eq_Icc]
      simp only [hP, hr]
      intro y hy
      constructor <;> linarith [hy.1, hy.2]
    have hvol : volume (Metric.closedBall (P b) (4 * r b)) = ENNReal.ofReal (4 * (B b - A b)) := by
      rw [Real.closedBall_eq_Icc, Real.volume_Icc]
      simp only [hP, hr]
      congr 1
      ring
    have hne0 : ENNReal.ofReal (4 * (B b - A b)) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    have hnet : ENNReal.ofReal (4 * (B b - A b)) ≠ ⊤ := ENNReal.ofReal_ne_top
    -- the good average bound
    have hgood : ENNReal.ofReal c * ENNReal.ofReal (4 * (B b - A b))
        ≤ 4 * ∫⁻ x in Set.Icc (A b) (B b), ψ x := by
      have h1 := Commons.Analysis.Maximal.ofReal_mul_le_of_lt_mul_inv (hABlt b) (hAB b).2.2
      have h4 : ENNReal.ofReal (4 * (B b - A b)) = 4 * ENNReal.ofReal (B b - A b) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4), ENNReal.ofReal_ofNat]
      rw [h4, ← mul_assoc, mul_comm (ENNReal.ofReal c) 4, mul_assoc]
      exact mul_le_mul_right h1 4
    -- the pointwise bound coming from the enlarged interval
    have hpt : ∀ y ∈ Set.Icc (A b) (B b),
        ψ y * (ENNReal.ofReal (4 * (B b - A b))⁻¹ * ∫⁻ x in Metric.closedBall (P b) (4 * r b), w x)
          ≤ ψ y * hlMax w y := by
      intro y hy
      refine mul_le_mul_right ?_ (ψ y)
      have hle := hlMax_le_of_mem w
        (a := P b - 4 * r b) (b := P b + 4 * r b)
        (show P b - 4 * r b ≤ y by simp only [hP, hr]; linarith [hy.1])
        (show y ≤ P b + 4 * r b by simp only [hP, hr]; linarith [hy.2])
      have hvol'' : (P b + 4 * r b) - (P b - 4 * r b) = 4 * (B b - A b) := by
        simp only [hP, hr]; ring
      rwa [hvol'', ← Real.closedBall_eq_Icc] at hle
    have key : ∀ I : ℝ≥0∞, ENNReal.ofReal (4 * (B b - A b)) *
        (ENNReal.ofReal (4 * (B b - A b))⁻¹ * I) = I := by
      intro I
      rw [← mul_assoc, ofReal_mul_ofReal_inv (by linarith : (0:ℝ) < 4 * (B b - A b)), one_mul]
    have hmono : ∫⁻ x in Set.Icc (A b) (B b),
        ψ x * (ENNReal.ofReal (4 * (B b - A b))⁻¹ * ∫⁻ y in Metric.closedBall (P b) (4 * r b), w y)
          ≤ ∫⁻ x in Set.Icc (A b) (B b), ψ x * hlMax w x := by
      rw [← lintegral_indicator measurableSet_Icc
            (fun x => ψ x * (ENNReal.ofReal (4 * (B b - A b))⁻¹ *
              ∫⁻ y in Metric.closedBall (P b) (4 * r b), w y)),
          ← lintegral_indicator measurableSet_Icc (fun x => ψ x * hlMax w x)]
      refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ Set.Icc (A b) (B b)
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
        exact hpt y hy
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
    calc ENNReal.ofReal c * ∫⁻ x in Metric.closedBall (P b) (4 * r b), w x
        = ENNReal.ofReal c * (ENNReal.ofReal (4 * (B b - A b)) *
            (ENNReal.ofReal (4 * (B b - A b))⁻¹ * ∫⁻ x in Metric.closedBall (P b) (4 * r b), w x)) :=
          congrArg (fun t => ENNReal.ofReal c * t)
            (key (∫⁻ x in Metric.closedBall (P b) (4 * r b), w x)).symm
      _ = (ENNReal.ofReal c * ENNReal.ofReal (4 * (B b - A b))) *
            (ENNReal.ofReal (4 * (B b - A b))⁻¹ * ∫⁻ x in Metric.closedBall (P b) (4 * r b), w x) := by
          ring
      _ ≤ (4 * ∫⁻ x in Set.Icc (A b) (B b), ψ x) *
            (ENNReal.ofReal (4 * (B b - A b))⁻¹ * ∫⁻ x in Metric.closedBall (P b) (4 * r b), w x) :=
          mul_le_mul_left hgood _
      _ = 4 * ∫⁻ x in Set.Icc (A b) (B b),
            ψ x * (ENNReal.ofReal (4 * (B b - A b))⁻¹ * ∫⁻ x in Metric.closedBall (P b) (4 * r b), w x) := by
          rw [lintegral_mul_const _ hψm]
          ring
      _ ≤ 4 * ∫⁻ x in Set.Icc (A b) (B b), ψ x * hlMax w x :=
          mul_le_mul_right hmono 4
  calc ENNReal.ofReal c * ∫⁻ x in Ω, w x
      ≤ ENNReal.ofReal c * ∫⁻ x in ⋃ b : u, Metric.closedBall (P b) (4 * r b), w x :=
        mul_le_mul_right (lintegral_mono_set (f := w) hcover) (ENNReal.ofReal c)
    _ ≤ ENNReal.ofReal c * ∑' b : u, ∫⁻ x in Metric.closedBall (P b) (4 * r b), w x :=
        mul_le_mul_right (MeasureTheory.lintegral_iUnion_le (fun b : u => Metric.closedBall (P b) (4 * r b)) w) (ENNReal.ofReal c)
    _ = ∑' b : u, ENNReal.ofReal c * ∫⁻ x in Metric.closedBall (P b) (4 * r b), w x :=
        ENNReal.tsum_mul_left.symm
    _ ≤ ∑' b : u, 4 * ∫⁻ x in Set.Icc (A b) (B b), ψ x * hlMax w x := ENNReal.tsum_le_tsum hkey
    _ = 4 * ∑' b : u, ∫⁻ x in Set.Icc (A b) (B b), ψ x * hlMax w x := ENNReal.tsum_mul_left
    _ = 4 * ∫⁻ x in ⋃ b : u, Set.Icc (A b) (B b), ψ x * hlMax w x := by
        rw [MeasureTheory.lintegral_iUnion (fun b : u => measurableSet_Icc) hd
          (fun x => ψ x * hlMax w x)]
    _ ≤ 4 * ∫⁻ x in Ω, ψ x * hlMax w x :=
        mul_le_mul_right (lintegral_mono_set (f := fun x => ψ x * hlMax w x) hunionSub) 4


/-! ### The weighted Calderón--Zygmund (Cotlar) inequality for `hlMax` -/

/-- **The weighted Calderón--Zygmund inequality** for the centred maximal function:
`∫ (hlMax ψ)² w ≤ 8 ∫ ψ (hlMax ψ) (hlMax w)`.  It is the layer-cake consequence of the
level-set inequality `hlMaxCZ_levelSet`. -/
theorem hlMaxWeightedCZ {ψ w : ℝ → ℝ≥0∞} (hψm : Measurable ψ) (hwm : Measurable w)
    (hψ : ∫⁻ x, ψ x < ⊤) :
    ∫⁻ x, (hlMax ψ x) ^ (2 : ℝ) * w x
      ≤ 8 * ∫⁻ x, ψ x * hlMax ψ x * hlMax w x := by
  have hCZ : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * ∫⁻ x in {x : ℝ | ENNReal.ofReal t < hlMax ψ x}, w x
        ≤ 4 * ∫⁻ x in {x : ℝ | ENNReal.ofReal t < hlMax ψ x}, ψ x * hlMax w x :=
    fun t ht => hlMaxCZ_levelSet hψm hwm hψ ht
  have hgm : Measurable fun x => (hlMax ψ x) ^ (2:ℝ) :=
    (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp (measurable_hlMax ψ)
  have hlayer := lintegral_rpow_enorm_eq_layercake (ν := volume.withDensity w) (p := 2)
    (g := hlMax ψ) (by norm_num) (hg := (measurable_hlMax ψ).aemeasurable)
  have h2 : ∫⁻ x, (hlMax ψ x) ^ (2:ℝ) ∂(volume.withDensity w)
      = 2 * ∫⁻ t in Set.Ioi (0:ℝ),
          (∫⁻ x in {x : ℝ | ENNReal.ofReal t < hlMax ψ x}, w x) * ENNReal.ofReal t := by
    have hh : (∫⁻ x, (hlMax ψ x) ^ (2:ℝ) ∂(volume.withDensity w))
        = ∫⁻ x, (hlMax ψ x).rpow (2:ℝ) ∂(volume.withDensity w) := rfl
    rw [hh, hlayer]
    congr 1
    · norm_num
    · refine lintegral_congr fun t => ?_
      rw [withDensity_apply' w {x : ℝ | ENNReal.ofReal t < hlMax ψ x},
        show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  have h3 : ∫⁻ t in Set.Ioi (0:ℝ),
        (∫⁻ x in {x : ℝ | ENNReal.ofReal t < hlMax ψ x}, w x) * ENNReal.ofReal t
      ≤ ∫⁻ t in Set.Ioi (0:ℝ),
        4 * (∫⁻ x in {x : ℝ | ENNReal.ofReal t < hlMax ψ x}, ψ x * hlMax w x) := by
    rw [← lintegral_indicator measurableSet_Ioi
          (fun t => (∫⁻ x in {x : ℝ | ENNReal.ofReal t < hlMax ψ x}, w x) * ENNReal.ofReal t),
      ← lintegral_indicator measurableSet_Ioi
          (fun t => 4 * ∫⁻ x in {x : ℝ | ENNReal.ofReal t < hlMax ψ x}, ψ x * hlMax w x)]
    refine lintegral_mono fun t => ?_
    by_cases ht : t ∈ Set.Ioi (0:ℝ)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      exact (mul_comm _ _).trans_le (hCZ t ht)
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
  have h4 : ∫⁻ t in Set.Ioi (0:ℝ),
        (∫⁻ x in {x : ℝ | ENNReal.ofReal t < hlMax ψ x}, ψ x * hlMax w x)
      = ∫⁻ x, hlMax ψ x * (ψ x * hlMax w x) := by
    have hstep1 : ∀ t, ∫⁻ x in {x : ℝ | ENNReal.ofReal t < hlMax ψ x}, ψ x * hlMax w x
        = ∫⁻ x, if ENNReal.ofReal t < hlMax ψ x then ψ x * hlMax w x else 0 := by
      intro t
      rw [← lintegral_indicator (measurableSet_lt measurable_const (measurable_hlMax ψ))
        (fun x => ψ x * hlMax w x)]
      refine lintegral_congr fun x => ?_
      by_cases h : ENNReal.ofReal t < hlMax ψ x
      · rw [Set.indicator_of_mem (show x ∈ {x : ℝ | ENNReal.ofReal t < hlMax ψ x} from h),
          if_pos h]
      · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | ENNReal.ofReal t < hlMax ψ x} from h),
          if_neg h]
    have hstep2 : ∫⁻ t in Set.Ioi (0:ℝ),
          (∫⁻ x, if ENNReal.ofReal t < hlMax ψ x then ψ x * hlMax w x else 0)
        = ∫⁻ t, ∫⁻ x, (Set.Ioi (0:ℝ)).indicator
            (fun t => if ENNReal.ofReal t < hlMax ψ x then ψ x * hlMax w x else 0) t := by
      rw [← lintegral_indicator measurableSet_Ioi
        (fun t => ∫⁻ x, if ENNReal.ofReal t < hlMax ψ x then ψ x * hlMax w x else 0)]
      refine lintegral_congr fun t => ?_
      by_cases ht : t ∈ Set.Ioi (0:ℝ)
      · rw [Set.indicator_of_mem ht]
        rw [show (fun x => (Set.Ioi (0:ℝ)).indicator
            (fun t => if ENNReal.ofReal t < hlMax ψ x then ψ x * hlMax w x else 0) t)
            = fun x => (if ENNReal.ofReal t < hlMax ψ x then ψ x * hlMax w x else 0) from by
              funext x
              rw [Set.indicator_of_mem ht]]
      · rw [Set.indicator_of_notMem ht]
        have hzero : (fun x => (Set.Ioi (0:ℝ)).indicator
            (fun t => if ENNReal.ofReal t < hlMax ψ x then ψ x * hlMax w x else 0) t)
            = fun _ => (0:ℝ≥0∞) := by
          funext x
          rw [Set.indicator_of_notMem ht]
        rw [hzero, lintegral_zero]
    have hunc : Measurable (Function.uncurry (fun t x => (Set.Ioi (0:ℝ)).indicator
        (fun t => if ENNReal.ofReal t < hlMax ψ x then ψ x * hlMax w x else 0) t)) := by
      have heq : Function.uncurry (fun t x => (Set.Ioi (0:ℝ)).indicator
          (fun t => if ENNReal.ofReal t < hlMax ψ x then ψ x * hlMax w x else 0) t)
          = fun p : ℝ × ℝ => if p.1 ∈ Set.Ioi (0:ℝ)
              then (if ENNReal.ofReal p.1 < hlMax ψ p.2 then ψ p.2 * hlMax w p.2 else 0)
              else 0 := by
        funext p
        rw [Function.uncurry_apply_pair, Set.indicator_apply]
      rw [heq]
      refine Measurable.ite ?_ ?_ measurable_const
      · exact measurableSet_Ioi.preimage measurable_fst
      · refine Measurable.ite ?_ ?_ measurable_const
        · exact measurableSet_lt (ENNReal.continuous_ofReal.measurable.comp measurable_fst)
            ((measurable_hlMax ψ).comp measurable_snd)
        · exact (hψm.comp measurable_snd).mul ((measurable_hlMax w).comp measurable_snd)
    simp only [hstep1]
    rw [hstep2, lintegral_lintegral_swap hunc.aemeasurable]
    refine lintegral_congr fun x => ?_
    have hpt : ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
        (fun t => if ENNReal.ofReal t < hlMax ψ x then ψ x * hlMax w x else 0) t
        = ∫⁻ t in Set.Ioi (0:ℝ),
          (if ENNReal.ofReal t < hlMax ψ x then ψ x * hlMax w x else 0) :=
      lintegral_indicator measurableSet_Ioi _
    rw [hpt, lintegral_Ioi_if_lt (hlMax ψ x) (ψ x * hlMax w x), mul_comm]
  have h5 : ∫⁻ x, (hlMax ψ x) ^ (2:ℝ) * w x
      = ∫⁻ x, (hlMax ψ x) ^ (2:ℝ) ∂(volume.withDensity w) := by
    rw [lintegral_withDensity_eq_lintegral_mul volume hwm hgm]
    refine lintegral_congr fun x => ?_
    rw [Pi.mul_apply, mul_comm]
  rw [h5, h2]
  calc 2 * ∫⁻ t in Set.Ioi (0:ℝ),
        (∫⁻ x in {x : ℝ | ENNReal.ofReal t < hlMax ψ x}, w x) * ENNReal.ofReal t
      ≤ 2 * ∫⁻ t in Set.Ioi (0:ℝ),
        4 * (∫⁻ x in {x : ℝ | ENNReal.ofReal t < hlMax ψ x}, ψ x * hlMax w x) :=
        mul_le_mul_right h3 2
    _ = 2 * (4 * ∫⁻ t in Set.Ioi (0:ℝ),
        (∫⁻ x in {x : ℝ | ENNReal.ofReal t < hlMax ψ x}, ψ x * hlMax w x)) := by
        rw [lintegral_const_mul' 4 _ (by norm_num)]
    _ = 8 * ∫⁻ x, hlMax ψ x * (ψ x * hlMax w x) := by rw [← h4]; ring
    _ = 8 * ∫⁻ x, ψ x * hlMax ψ x * hlMax w x := by
        congr 1
        refine lintegral_congr fun x => ?_
        ac_rfl


/-! ### Finiteness of the `p`-th moment of the `ℓ²`-valued centred maximal function -/

lemma lintegral_ell2HLMax_lt_top {n : ℕ} {p : ℝ} (hp : 2 < p) {f : Fin n → ℝ → ℝ}
    (hfin : ∀ t, ∫⁻ x, (hlMax (fun y => ‖f t y‖ₑ) x) ^ p < ⊤) :
    ∫⁻ x, (ell2HLMax f x) ^ (p / 2) < ⊤ := by
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hpq : p.HolderConjugate (p / (p - 1)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp1, ?_⟩
    have hpne : (p:ℝ) ≠ 0 := by linarith
    have hp1ne : (p - 1 : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  have hpoint : ∀ x, (ell2HLMax f x) ^ (p / 2)
      ≤ (∑ t : Fin n, (hlMax (fun y => ‖f t y‖ₑ) x) ^ p) * (n : ℝ≥0∞) ^ (p - 1) := by
    intro x
    set a : Fin n → ℝ≥0∞ := fun t => hlMax (fun y => ‖f t y‖ₑ) x with hadef
    have hsq : ∑ t : Fin n, (a t) ^ (2:ℝ) ≤ (∑ t : Fin n, a t) ^ (2:ℝ) := by
      have hmul : (∑ t : Fin n, a t) * (∑ t : Fin n, a t) = ∑ t, ∑ s, a t * a s :=
        Finset.sum_mul_sum Finset.univ Finset.univ a a
      rw [rpow_two_eq_mul, hmul]
      refine Finset.sum_le_sum fun t _ => ?_
      rw [rpow_two_eq_mul]
      exact Finset.single_le_sum (f := fun s => a t * a s) (fun s _ => zero_le) (Finset.mem_univ t)
    have hstep : (∑ t : Fin n, (a t) ^ (2:ℝ)) ^ (p / 2) ≤ (∑ t : Fin n, a t) ^ p := by
      refine (ENNReal.rpow_le_rpow hsq (by positivity)).trans (le_of_eq ?_)
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    have hholder := Commons.Analysis.MeasureTheory.ennreal_finset_sum_mul_le_holder
      (t := Finset.univ) (x := a) (y := fun _ : Fin n => (1 : ℝ≥0∞)) hpq
    have hsum1 : (∑ t : Fin n, a t * 1) = ∑ t : Fin n, a t := by simp
    have hsum2 : (∑ t : Fin n, (1 : ℝ≥0∞) ^ (p / (p - 1))) = (n : ℝ≥0∞) := by simp
    rw [hsum1, hsum2] at hholder
    have hraised : (∑ t : Fin n, a t) ^ p
        ≤ (∑ t : Fin n, (a t) ^ p) * (n : ℝ≥0∞) ^ (p - 1) := by
      have h := ENNReal.rpow_le_rpow hholder hp0.le
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le] at h
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h
      have e1 : (1:ℝ) / p * p = 1 := by
        have hpne : (p:ℝ) ≠ 0 := by linarith
        field_simp
      have e2 : (1:ℝ) / (p / (p - 1)) * p = p - 1 := by
        have hpne : (p:ℝ) ≠ 0 := by linarith
        have hp1ne : (p - 1 : ℝ) ≠ 0 := by linarith
        field_simp
      rw [e1, e2, ENNReal.rpow_one] at h
      exact h
    calc (ell2HLMax f x) ^ (p / 2)
        = (∑ t : Fin n, (a t) ^ (2:ℝ)) ^ (p / 2) := by
          rw [ell2HLMax]
      _ ≤ (∑ t : Fin n, a t) ^ p := hstep
      _ ≤ (∑ t : Fin n, (a t) ^ p) * (n : ℝ≥0∞) ^ (p - 1) := hraised
  have hinner : Measurable fun x => ∑ t : Fin n, (hlMax (fun y => ‖f t y‖ₑ) x) ^ p :=
    Finset.measurable_sum _ fun t _ =>
      (ENNReal.continuous_rpow_const (y := p)).measurable.comp (measurable_hlMax _)
  calc ∫⁻ x, (ell2HLMax f x) ^ (p / 2)
      ≤ ∫⁻ x, (∑ t : Fin n, (hlMax (fun y => ‖f t y‖ₑ) x) ^ p) * (n : ℝ≥0∞) ^ (p - 1) :=
        lintegral_mono hpoint
    _ = (∑ t : Fin n, ∫⁻ x, (hlMax (fun y => ‖f t y‖ₑ) x) ^ p) * (n : ℝ≥0∞) ^ (p - 1) := by
        rw [lintegral_mul_const _ hinner, lintegral_finsetSum]
        intro t _
        exact (ENNReal.continuous_rpow_const (y := p)).measurable.comp (measurable_hlMax _)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.sum_lt_top.mpr fun t _ => hfin t)
        (ENNReal.rpow_lt_top_of_nonneg (by linarith : (0:ℝ) ≤ p - 1) (by simp))



/-! ### The weighted Calderón--Zygmund (Cotlar) inequality for the dyadic maximal function -/



/-! ### The main estimate for bounded families in `L¹` -/

theorem ell2HLMaxLpGtTwo_bdd {p : ℝ} (hp : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ) (B : ℝ), (∀ t, Measurable (f t)) →
      (∀ t y, |f t y| ≤ B) → (∀ t, ∫⁻ y, ‖f t y‖ₑ < ⊤) →
      ∫⁻ x, (ell2HLMax f x) ^ (p / 2) ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, (ell2Sq f x) ^ (p / 2) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  have hp2 : 0 < p - 2 := by linarith
  have hq1 : (1 : ℝ) < p / (p - 2) := by
    rw [lt_div_iff₀ hp2]; linarith
  obtain ⟨K, hKpos, hKbd⟩ := hlMaxStrongTypeENNReal (q := p / (p - 2)) hq1
  obtain ⟨K', hK'pos, hK'bd⟩ := hlMaxStrongTypeENNReal (q := p) hp1
  refine ⟨8 * K, by positivity, ?_⟩
  intro n f B hf hbdd hL1
  have hφbdd : ∀ t y, ‖f t y‖ₑ ≤ ENNReal.ofReal B := fun t y => by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hbdd t y)
  have hφfin : ∀ t y, ‖f t y‖ₑ ≠ ⊤ := fun t y => by
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top
  have hdybdd : ∀ t x, hlMax (fun y => ‖f t y‖ₑ) x ≤ ENNReal.ofReal B := fun t x =>
    (hlMax_le_iSup _ x).trans (iSup_le fun y => hφbdd t y)
  have hdyfin : ∀ t x, hlMax (fun y => ‖f t y‖ₑ) x < ⊤ := fun t x =>
    lt_of_le_of_lt (hdybdd t x) ENNReal.ofReal_lt_top
  -- `φ_t ∈ L^p`, from `φ_t ≤ B` and `φ_t ∈ L^1`
  have hφp : ∀ t, ∫⁻ y, ‖f t y‖ₑ ^ p < ⊤ := by
    intro t
    have h1 : ∀ y, ‖f t y‖ₑ ^ p ≤ ‖f t y‖ₑ * (ENNReal.ofReal B) ^ (p - 1) := by
      intro y
      calc ‖f t y‖ₑ ^ p
          = ‖f t y‖ₑ ^ (1:ℝ) * ‖f t y‖ₑ ^ (p - 1) := by
            conv_lhs => rw [show p = 1 + (p - 1) by ring]
            rw [ENNReal.rpow_add_of_nonneg 1 (p - 1) zero_le_one
              (by linarith : (0:ℝ) ≤ p - 1)]
        _ = ‖f t y‖ₑ * ‖f t y‖ₑ ^ (p - 1) := by rw [ENNReal.rpow_one]
        _ ≤ ‖f t y‖ₑ * (ENNReal.ofReal B) ^ (p - 1) :=
            mul_le_mul_right (ENNReal.rpow_le_rpow (hφbdd t y) (by linarith : (0:ℝ) ≤ p - 1)) _
    calc ∫⁻ y, ‖f t y‖ₑ ^ p
        ≤ ∫⁻ y, ‖f t y‖ₑ * (ENNReal.ofReal B) ^ (p - 1) := lintegral_mono h1
      _ = (∫⁻ y, ‖f t y‖ₑ) * (ENNReal.ofReal B) ^ (p - 1) :=
          lintegral_mul_const _ (hf t).enorm
      _ < ⊤ := ENNReal.mul_lt_top (hL1 t)
          (ENNReal.rpow_lt_top_of_nonneg (by linarith : (0:ℝ) ≤ p - 1) ENNReal.ofReal_ne_top)
  have hdyp : ∀ t, ∫⁻ x, (hlMax (fun y => ‖f t y‖ₑ) x) ^ p < ⊤ := by
    intro t
    exact lt_of_le_of_lt (hK'bd (fun y => ‖f t y‖ₑ) (hf t).enorm (hφfin t))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hφp t))
  have hAfin : ∫⁻ x, (ell2HLMax f x) ^ (p / 2) < ⊤ := lintegral_ell2HLMax_lt_top hp hdyp
  -- boundedness of `ell2HLF`
  have hFF : ∀ x, ell2HLF f x < ⊤ := by
    intro x
    rw [ell2HLF, ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < 1/2)]
    exact ENNReal.sum_lt_top.mpr fun t _ =>
      ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0:ℝ) ≤ 2)
        (ne_of_lt (lt_of_le_of_lt (hdybdd t x) ENNReal.ofReal_lt_top))
  have hFfin : ∀ x, ell2HLF f x ≠ ⊤ := fun x => (hFF x).ne
  -- notation
  set A : ℝ≥0∞ := ∫⁻ x, (ell2HLMax f x) ^ (p / 2) with hA
  set Bs : ℝ≥0∞ := ∫⁻ x, (ell2Sigma f x) ^ p with hBs
  set w : ℝ → ℝ≥0∞ := fun x => (ell2HLF f x) ^ (p - 2) with hw
  have hFmeas : Measurable (ell2HLF f) := ell2HLF_measurable f
  have hσmeas : Measurable (ell2Sigma f) := ell2Sigma_measurable hf
  have hwmeas : Measurable w := by
    rw [hw]; exact (ENNReal.continuous_rpow_const (y := p - 2)).measurable.comp hFmeas
  have hdwmeas : Measurable (hlMax w) := measurable_hlMax w
  have hwfin : ∀ x, w x ≠ ⊤ := by
    intro x
    rw [hw]
    exact ENNReal.rpow_ne_top_of_nonneg (by linarith : (0:ℝ) ≤ p - 2) (hFfin x)
  have hmain : A ≤ 8 * ENNReal.ofReal K * Bs ^ (1/p) * A ^ ((p-1)/p) := by
    have h1 : A = ∫⁻ x, ell2HLMax f x * w x := by
      rw [hA, hw]
      refine lintegral_congr fun x => ?_
      rw [rpow_eq_rpow_mul_rpow_sub (show (0:ℝ) < 1 by norm_num)
        (by linarith : (1:ℝ) ≤ p / 2), ENNReal.rpow_one]
      congr 1
      rw [show p / 2 - 1 = (p - 2) / 2 by ring]
      simp only [ell2HLF]
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    have h2 : ∫⁻ x, ell2HLMax f x * w x
        = ∑ t : Fin n, ∫⁻ x, (hlMax (fun y => ‖f t y‖ₑ) x) ^ (2:ℝ) * w x := by
      have hfun : (fun x => ell2HLMax f x * w x)
          = fun x => ∑ t : Fin n, (hlMax (fun y => ‖f t y‖ₑ) x) ^ (2:ℝ) * w x := by
        funext x
        rw [ell2HLMax, Finset.sum_mul]
      rw [hfun, lintegral_finsetSum]
      intro t _
      exact ((ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp
        (measurable_hlMax _)).mul hwmeas
    have h3 : ∑ t : Fin n, ∫⁻ x, (hlMax (fun y => ‖f t y‖ₑ) x) ^ (2:ℝ) * w x
        ≤ ∑ t : Fin n, 8 * ∫⁻ x, ‖f t x‖ₑ * hlMax (fun y => ‖f t y‖ₑ) x * hlMax w x :=
      Finset.sum_le_sum fun t _ => hlMaxWeightedCZ ((hf t).enorm) hwmeas (hL1 t)
    have h8 : ∑ t : Fin n, 8 * ∫⁻ x, ‖f t x‖ₑ * hlMax (fun y => ‖f t y‖ₑ) x * hlMax w x
        = 8 * ∫⁻ x, (∑ t : Fin n, ‖f t x‖ₑ * hlMax (fun y => ‖f t y‖ₑ) x) * hlMax w x := by
      rw [← Finset.mul_sum, ← lintegral_finsetSum]
      · congr 1
        refine lintegral_congr fun x => ?_
        rw [Finset.sum_mul]
      · intro t _
        exact ((hf t).enorm.mul (measurable_hlMax _)).mul hdwmeas
    have h5 : 8 * ∫⁻ x, (∑ t : Fin n, ‖f t x‖ₑ * hlMax (fun y => ‖f t y‖ₑ) x) * hlMax w x
        ≤ 8 * ∫⁻ x, ell2Sigma f x * ell2HLF f x * hlMax w x := by
      refine mul_le_mul_right ?_ 8
      refine lintegral_mono fun x => ?_
      refine mul_le_mul_left ?_ _
      exact ENNReal_sum_mul_le_sqrt_mul_sqrt (fun t => ‖f t x‖ₑ)
        (fun t => hlMax (fun y => ‖f t y‖ₑ) x)
    have h6 : 8 * ∫⁻ x, ell2Sigma f x * ell2HLF f x * hlMax w x
        ≤ 8 * ((∫⁻ x, (ell2Sigma f x) ^ p) ^ (1/p) * (∫⁻ x, (ell2HLF f x) ^ p) ^ (1/p)
            * (∫⁻ x, (hlMax w x) ^ (p/(p-2))) ^ ((p-2)/p)) :=
      mul_le_mul_right (lintegral_mul_mul_le hp hσmeas.aemeasurable hFmeas.aemeasurable
        hdwmeas.aemeasurable) 8
    -- the weight's `L^{p'}` norm
    have hX : (∫⁻ x, (hlMax w x) ^ (p/(p-2))) ^ ((p-2)/p)
        ≤ ENNReal.ofReal K * (∫⁻ x, (ell2HLF f x) ^ p) ^ ((p-2)/p) := by
      have hKb := hKbd w hwmeas hwfin
      have hwq : ∫⁻ x, w x ^ (p/(p-2)) = ∫⁻ x, (ell2HLF f x) ^ p := by
        refine lintegral_congr fun x => ?_
        rw [hw, ← ENNReal.rpow_mul]
        congr 1
        have hne : (p : ℝ) ≠ 0 := by linarith
        have hne2 : (p - 2 : ℝ) ≠ 0 := by linarith
        field_simp
      have hKq : (ENNReal.ofReal (K ^ (p/(p-2)))) ^ ((p-2)/p) = ENNReal.ofReal K := by
        rw [ENNReal.ofReal_rpow_of_nonneg (x := K ^ (p/(p-2))) (by positivity) (by positivity)]
        congr 1
        rw [← Real.rpow_mul hKpos.le]
        rw [show (p / (p - 2)) * ((p - 2) / p) = 1 by
          have hne : (p : ℝ) ≠ 0 := by linarith
          have hne2 : (p - 2 : ℝ) ≠ 0 := by linarith
          field_simp]
        exact Real.rpow_one K
      calc (∫⁻ x, (hlMax w x) ^ (p/(p-2))) ^ ((p-2)/p)
          ≤ (ENNReal.ofReal (K ^ (p/(p-2))) * ∫⁻ x, w x ^ (p/(p-2))) ^ ((p-2)/p) :=
            ENNReal.rpow_le_rpow hKb (by positivity)
        _ = (ENNReal.ofReal (K ^ (p/(p-2))) * ∫⁻ x, (ell2HLF f x) ^ p) ^ ((p-2)/p) := by
            rw [hwq]
        _ = ENNReal.ofReal K * (∫⁻ x, (ell2HLF f x) ^ p) ^ ((p-2)/p) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hKq]
    have hAeq : (∫⁻ x, (ell2HLF f x) ^ p) = A := by
      rw [hA]
      refine lintegral_congr fun x => ?_
      simp only [ell2HLF]
      exact rpow_half_rpow _ p
    have hAA : A ^ (1/p) * A ^ ((p-2)/p) = A ^ ((p-1)/p) := by
      rw [← ENNReal.rpow_add_of_nonneg (1/p) ((p-2)/p) (by positivity) (by positivity)]
      congr 1
      ring
    calc A = ∫⁻ x, ell2HLMax f x * w x := h1
      _ = ∑ t : Fin n, ∫⁻ x, (hlMax (fun y => ‖f t y‖ₑ) x) ^ (2:ℝ) * w x := h2
      _ ≤ ∑ t : Fin n, 8 * ∫⁻ x, ‖f t x‖ₑ * hlMax (fun y => ‖f t y‖ₑ) x * hlMax w x := h3
      _ = 8 * ∫⁻ x, (∑ t : Fin n, ‖f t x‖ₑ * hlMax (fun y => ‖f t y‖ₑ) x) * hlMax w x := h8
      _ ≤ 8 * ∫⁻ x, ell2Sigma f x * ell2HLF f x * hlMax w x := h5
      _ ≤ 8 * ((∫⁻ x, (ell2Sigma f x) ^ p) ^ (1/p) * (∫⁻ x, (ell2HLF f x) ^ p) ^ (1/p)
            * (∫⁻ x, (hlMax w x) ^ (p/(p-2))) ^ ((p-2)/p)) := h6
      _ ≤ 8 * (Bs ^ (1/p) * A ^ (1/p) * (ENNReal.ofReal K * A ^ ((p-2)/p))) := by
          refine mul_le_mul_right ?_ 8
          rw [← hBs, hAeq]
          rw [hAeq] at hX
          exact mul_le_mul_of_nonneg_left hX (by positivity)
      _ = 8 * ENNReal.ofReal K * Bs ^ (1/p) * A ^ ((p-1)/p) := by
          rw [show 8 * (Bs ^ (1/p) * A ^ (1/p) * (ENNReal.ofReal K * A ^ ((p-2)/p)))
              = 8 * (Bs ^ (1/p) * ENNReal.ofReal K * (A ^ (1/p) * A ^ ((p-2)/p))) by
            ac_rfl]
          rw [hAA]
          ac_rfl
  -- the division
  by_cases hA0 : A = 0
  · rw [hA0]
    positivity
  · have hApos : 0 < A := zero_lt_iff.mpr hA0
    have hAtop : A ≠ ⊤ := lt_top_iff_ne_top.mp (by rw [hA]; exact hAfin)
    have h1p : (0:ℝ) < 1/p := by positivity
    have hpp : (0:ℝ) < (p-1)/p := by positivity
    have hkey : A ^ (1/p) * A ^ ((p-1)/p)
        ≤ (8 * ENNReal.ofReal K * Bs ^ (1/p)) * A ^ ((p-1)/p) := by
      rw [← ENNReal.rpow_add_of_nonneg (1/p) ((p-1)/p) h1p.le hpp.le,
        show (1:ℝ)/p + (p-1)/p = 1 by field_simp; ring, ENNReal.rpow_one]
      exact hmain
    have hvpos : A ^ ((p-1)/p) ≠ 0 := (ENNReal.rpow_pos hApos hAtop).ne'
    have hvt : A ^ ((p-1)/p) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hpp.le hAtop
    have hkey2 : A ^ (1/p) ≤ 8 * ENNReal.ofReal K * Bs ^ (1/p) :=
      (ENNReal.mul_le_mul_iff_left hvpos hvt).mp hkey
    have hraise : (A ^ (1/p)) ^ p ≤ (8 * ENNReal.ofReal K * Bs ^ (1/p)) ^ p :=
      ENNReal.rpow_le_rpow hkey2 hp0.le
    have hL : (A ^ (1/p)) ^ p = A := by
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
    have h8K : (8:ℝ≥0∞) ^ p * (ENNReal.ofReal K) ^ p = ENNReal.ofReal ((8 * K) ^ p) := by
      rw [show (8:ℝ≥0∞) = ENNReal.ofReal 8 by norm_num,
        ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0:ℝ) ≤ 8) hp0.le,
        ENNReal.ofReal_rpow_of_nonneg hKpos.le hp0.le,
        ← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow (by norm_num) hKpos.le]
    have hR : (8 * ENNReal.ofReal K * Bs ^ (1/p)) ^ p = ENNReal.ofReal ((8 * K) ^ p) * Bs := by
      calc (8 * ENNReal.ofReal K * Bs ^ (1/p)) ^ p
          = (8 * ENNReal.ofReal K) ^ p * (Bs ^ (1/p)) ^ p := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        _ = 8 ^ p * (ENNReal.ofReal K) ^ p * Bs := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul,
              one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
        _ = ENNReal.ofReal ((8 * K) ^ p) * Bs := by rw [h8K]
    rw [hL, hR] at hraise
    refine hraise.trans (le_of_eq ?_)
    congr 1
    rw [hBs]
    refine lintegral_congr fun x => ?_
    simp only [ell2Sigma]
    exact rpow_half_rpow _ p



/-! ### Truncation: from bounded families to arbitrary ones -/

lemma ell2HLMax_truncF_mono {n : ℕ} {N M : ℕ} (hNM : N ≤ M) (f : Fin n → ℝ → ℝ) (x : ℝ) :
    ell2HLMax (truncF N f) x ≤ ell2HLMax (truncF M f) x := by
  unfold ell2HLMax
  exact Finset.sum_le_sum fun t _ => ENNReal.rpow_le_rpow
    (hlMax_mono (fun y => truncF_norm_mono hNM f t y) x) (by norm_num)

lemma iSup_ell2HLMax_truncF {n : ℕ} (f : Fin n → ℝ → ℝ) (hf : ∀ t, Measurable (f t))
    (x : ℝ) : ell2HLMax f x = ⨆ N, ell2HLMax (truncF N f) x := by
  have hmono : ∀ t, Monotone fun N => (hlMax (fun y => ‖truncF N f t y‖ₑ) x) ^ (2:ℝ) :=
    fun t a b hab => ENNReal.rpow_le_rpow
      (hlMax_mono (fun y => truncF_norm_mono hab f t y) x) (by norm_num)
  have hsup : ∀ t, (⨆ N, hlMax (fun y => ‖truncF N f t y‖ₑ) x)
      = hlMax (fun y => ‖f t y‖ₑ) x := by
    intro t
    have key := hlMax_iSup (ψ := fun N y => ‖truncF N f t y‖ₑ)
      (fun N => (truncF_measurable N hf t).enorm) (fun a b hab y => truncF_norm_mono hab f t y)
    rw [show (fun y => ⨆ N, ‖truncF N f t y‖ₑ) = fun y => ‖f t y‖ₑ from
      funext fun y => iSup_truncF_norm f t y] at key
    exact congrFun key.symm x
  have hsum : (⨆ N, ell2HLMax (truncF N f) x)
      = ∑ t : Fin n, (hlMax (fun y => ‖f t y‖ₑ) x) ^ (2:ℝ) := by
    have hfun : ∀ N, ell2HLMax (truncF N f) x
        = ∑ t, (hlMax (fun y => ‖truncF N f t y‖ₑ) x) ^ (2:ℝ) := by
      intro N; rw [ell2HLMax]
    simp only [hfun]
    rw [iSup_finset_sum_eq hmono]
    exact Finset.sum_congr rfl fun t _ => by
      rw [← iSup_rpow_eq (fun a b hab => hlMax_mono (fun y => truncF_norm_mono hab f t y) x)
        (by norm_num : (0:ℝ) ≤ 2), hsup t]
  rw [ell2HLMax]
  exact hsum.symm

/-- **The `ℓ²`-valued Hardy--Littlewood maximal inequality on `L^p(ℓ²)` for `p > 2`**, with a
constant uniform in the number of components. -/
theorem ell2HLMaxLpGtTwo {p : ℝ} (hp : 2 < p) : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) → ∫⁻ x, (∑ t, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ (p / 2) ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Sq f x) ^ (p / 2) := by
  obtain ⟨C, hCpos, hC⟩ := ell2HLMaxLpGtTwo_bdd hp
  refine ⟨C, hCpos, fun n f hf => ?_⟩
  show ∫⁻ x, (ell2HLMax f x) ^ (p / 2)
      ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, (ell2Sq f x) ^ (p / 2)
  have hN : ∀ N, ∫⁻ x, (ell2HLMax (truncF N f) x) ^ (p/2)
      ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, (ell2Sq f x) ^ (p/2) := by
    intro N
    refine (hC n (truncF N f) (N:ℝ) (truncF_measurable N hf) (truncF_abs_le N f)
      (lintegral_truncF_norm_lt_top N f)).trans ?_
    refine mul_le_mul_right ?_ _
    exact lintegral_mono fun x => ENNReal.rpow_le_rpow (ell2Sq_truncF_le N f x) (by positivity)
  have hpt : ∀ x, (ell2HLMax f x) ^ (p/2) = ⨆ N, (ell2HLMax (truncF N f) x) ^ (p/2) := by
    intro x
    rw [iSup_ell2HLMax_truncF f hf x, iSup_rpow_eq (fun a b hab => ell2HLMax_truncF_mono hab f x)
      (by positivity)]
  have hmeas : ∀ N, Measurable fun x => (ell2HLMax (truncF N f) x) ^ (p/2) := fun N =>
    (ENNReal.continuous_rpow_const (y := p/2)).measurable.comp (ell2HLMax_measurable _)
  have hmonoN : Monotone fun N => fun x => (ell2HLMax (truncF N f) x) ^ (p/2) :=
    fun a b hab x => ENNReal.rpow_le_rpow (ell2HLMax_truncF_mono hab f x) (by positivity)
  calc ∫⁻ x, (ell2HLMax f x) ^ (p/2)
      = ∫⁻ x, ⨆ N, (ell2HLMax (truncF N f) x) ^ (p/2) := lintegral_congr hpt
    _ = ⨆ N, ∫⁻ x, (ell2HLMax (truncF N f) x) ^ (p/2) := lintegral_iSup hmeas hmonoN
    _ ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, (ell2Sq f x) ^ (p/2) := iSup_le hN

end Work.BourgainPlan.Maximal
