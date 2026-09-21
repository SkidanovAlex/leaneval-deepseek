import Mathlib
import Submission.Work.OddVolterra.Existence.aw_data
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.KvecM_contDiffOn_comp
import Submission.Work.OddVolterra.Existence.awThetaSmoothDefs
import Submission.Work.OddVolterra.Existence.aw_contDiffOn_awGodd
import Submission.Work.OddVolterra.Window.manifest_eq
import Submission.Work.Analysis.Calculus.contDiff_intervalIntegral_param
import Submission.Work.Analysis.Calculus.integral_div_sqrt_eq_integral_sin_sq
import Submission.Commons.Analysis.Calculus.contDiff_parametric_iteratedDeriv_gen

/-!
# Smoothness of the localised odd `Θ`-data

The localised data `awTheta n h s σ z = awChiT s σ z • ThetaM n h s σ z` is the product of the
slope/state cutoffs of `Existence.aw_data` with the manifest `Θ`-data `KernelExt.ThetaM`, whose
last two rows are `-∂_u G2M(u,σ,z)|_{u=s}`.  The manifest average

`G2M(u,σ,z) = ∫_0^1 KvecM(u+τ(σ-u),σ,z) (τ(1-τ))^{-1/2} dτ`

is a singular parametric integral, so `ThetaM` is *not* obviously smooth; the point of this file
is that it nevertheless is, everywhere.

The proof strategy is

* substitute `τ = sin θ ^ 2` (`Analysis.Calculus.integral_div_sqrt_eq_integral_sin_sq`), turning
  the average into a *non*-singular parametric integral over `[0, π/2]`;
* insert an explicit smooth bump `awPsi` (see `awThetaSmoothDefs`) in the slots `(u,σ,z 0,z 1)`
  that carry the Abel radicands; the modified average `awG2Ms` is then `C^∞` on *all* of
  `ℝ × ℝ × St` (`contDiff_intervalIntegral_param` applied to a globally smooth integrand, whose
  smoothness comes from `KernelExt.KvecM_contDiffOn_comp` on the open set `awR` containing the
  closure of the support of the bump);
* the localised `Θ`-data `awThetaMs` built from `awG2Ms` is therefore `C^∞` everywhere;
* on the interior `awGoodT` of the support of the cutoff, `awPsi` is identically `1` near `u = s`,
  so `awThetaMs` agrees there with `ThetaM`, hence `awTheta = awChiT • ThetaM = awChiT • awThetaMs`
  is smooth on the open set `awGoodT`, while off the (closed) support of `awChiT` it vanishes.
  As `univ = awGoodT ∪ (support awChiT)ᶜ`, the local characterisation of `ContDiffOn` finishes.
-/

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

open Work.OddVolterra

noncomputable section

/-! ## A general smoothness-of-products lemma -/

/-- If `f` is `C^∞` on an open set `R` and `g` is `C^∞` everywhere with the closure of its
support contained in `R`, then `f * g` is `C^∞` everywhere. -/
lemma contDiff_mul_of_contDiffOn_of_closure_support_subset {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {R : Set V} (hR : IsOpen R) {f g : V → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f R) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hsupp : closure (Function.support g) ⊆ R) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : V => f x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ R
  · exact (hf.contDiffAt (hR.mem_nhds hx)).mul hg.contDiffAt
  · have hx' : x ∉ closure (Function.support g) := fun h => hx (hsupp h)
    rw [mem_closure_iff] at hx'
    push Not at hx'
    obtain ⟨o, ho, hxo, hdisj⟩ := hx'
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      (Filter.eventually_of_mem (ho.mem_nhds hxo) ?_)
    intro y hy
    have hgy : g y = 0 := by
      by_contra hne
      have hmem : y ∈ o ∩ Function.support g := ⟨hy, Function.mem_support.mpr hne⟩
      rw [hdisj] at hmem
      exact hmem
    show f y * g y = 0
    rw [hgy, mul_zero]

/-! ## Elementary bounds on the ball profile -/

lemma profileX_le_one (s : ℝ) : Commons.Geometry.Ulam.profileX s ≤ 1 := by
  rw [Commons.Geometry.Ulam.profileX, div_le_one (Real.sqrt_pos.mpr (by positivity))]
  exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg s])

/-- On the slope window `[19/40, 41/40]` the ball profile lies in `[17/25, 1]`. -/
lemma profileX_mem_window {σ : ℝ} (hσ : |σ - 3 / 4| ≤ 11 / 40) :
    Commons.Geometry.Ulam.profileX σ ∈ Set.Icc (17 / 25 : ℝ) 1 := by
  have hσ' : |σ| ≤ 21 / 20 := by
    have h := abs_le.mp hσ
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  exact ⟨profileX_ge_17_25 hσ', profileX_le_one σ⟩

/-- On `awSuppT` the two chord endpoints `z 0`, `z 1` lie in `[1/4, 39/20]`, the interval on
which the state bump `awPzeta` equals `1`. -/
lemma z_coord_mem_window {σ : ℝ} {z : St} (hσ : |σ - 3 / 4| ≤ 11 / 40)
    (hz : ‖z - baseState σ‖ ≤ 2 / 5) (i : Fin 4) (hi : i = 0 ∨ i = 1) :
    z i ∈ Set.Icc (1 / 4 : ℝ) (39 / 20) := by
  have hcoord : |z i - baseState σ i| ≤ 2 / 5 := by
    have h := norm_le_pi_norm (z - baseState σ) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact le_trans h hz
  have hbase : baseState σ i = Commons.Geometry.Ulam.profileX σ := by
    rcases hi with rfl | rfl <;> rfl
  rw [hbase] at hcoord
  obtain ⟨hlo, hhi⟩ := profileX_mem_window hσ
  obtain ⟨h1, h2⟩ := abs_le.mp hcoord
  constructor <;> linarith

/-! ## The localising bump is `1` near the support -/

lemma awPsi_eq_one_of_mem_Icc {u σ : ℝ} {z : St}
    (hu : u ∈ Set.Icc (9 / 20 : ℝ) (21 / 20)) (hσ : σ ∈ Set.Icc (9 / 20 : ℝ) (21 / 20))
    (hz0 : z 0 ∈ Set.Icc (1 / 4 : ℝ) (39 / 20)) (hz1 : z 1 ∈ Set.Icc (1 / 4 : ℝ) (39 / 20)) :
    awPsi u σ z = 1 := by
  rw [awPsi, awPbeta_eq_one hu, awPbeta_eq_one hσ, awPzeta_eq_one hz0,
    awPzeta_eq_one hz1, mul_one, mul_one, mul_one]

/-- On `awSuppT` the localising bump equals `1`. -/
lemma awPsi_eq_one_of_mem_awSuppT' {p : ℝ × ℝ × St} (hp : p ∈ awSuppT) :
    awPsi p.1 p.2.1 p.2.2 = 1 := by
  obtain ⟨h1, h2, h3⟩ := hp
  have hb1 := abs_le.mp h1
  have hb2 := abs_le.mp h2
  exact awPsi_eq_one_of_mem_Icc ⟨by linarith [hb1.1], by linarith [hb1.2]⟩
    ⟨by linarith [hb2.1], by linarith [hb2.2]⟩
    (z_coord_mem_window h2 h3 0 (Or.inl rfl)) (z_coord_mem_window h2 h3 1 (Or.inr rfl))

/-- The two chord endpoints lie in `[1/4, 39/20]` as soon as `|σ| ≤ 21/20` and
`‖z - baseState σ‖ ≤ 41/100`. -/
lemma z_coord_mem_window_le {σ : ℝ} {z : St} (hσ : |σ| ≤ 21 / 20)
    (hz : ‖z - baseState σ‖ ≤ 41 / 100) (i : Fin 4) (hi : i = 0 ∨ i = 1) :
    z i ∈ Set.Icc (1 / 4 : ℝ) (39 / 20) := by
  have hcoord : |z i - baseState σ i| ≤ 41 / 100 := by
    have h := norm_le_pi_norm (z - baseState σ) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact le_trans h hz
  have hbase : baseState σ i = Commons.Geometry.Ulam.profileX σ := by
    rcases hi with rfl | rfl <;> rfl
  rw [hbase] at hcoord
  have hlo := profileX_ge_17_25 hσ
  have hhi : Commons.Geometry.Ulam.profileX σ ≤ 1 := profileX_le_one σ
  obtain ⟨h1, h2⟩ := abs_le.mp hcoord
  constructor <;> linarith

/-- The bump is identically `1` in a neighbourhood of a point of `awGoodT` (as a function of the
first variable, the other two being held fixed). -/
lemma eventually_awPsi_eq_one {s σ : ℝ} {z : St} (hs : |s - 3 / 4| < 3 / 10)
    (hσ : |σ - 3 / 4| < 3 / 10) (hz : ‖z - baseState σ‖ < 41 / 100) :
    ∀ᶠ u in 𝓝 s, awPsi u σ z = 1 := by
  have hε : 0 < 3 / 10 - |s - 3 / 4| := by linarith
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds s hε) fun u hu => ?_
  rw [Metric.mem_ball, Real.dist_eq] at hu
  have hul : |u - 3 / 4| ≤ 3 / 10 := by
    have h := abs_sub_le u s (3 / 4)
    rw [abs_sub_comm u s] at h hu
    linarith
  have huI : u ∈ Set.Icc (9 / 20 : ℝ) (21 / 20) := by
    have h := abs_le.mp hul
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hσI : σ ∈ Set.Icc (9 / 20 : ℝ) (21 / 20) := by
    have h := abs_le.mp (le_of_lt hσ)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hs21 : |σ| ≤ 21 / 20 := by
    have h := abs_le.mp (le_of_lt hσ)
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  exact awPsi_eq_one_of_mem_Icc huI hσI
    (z_coord_mem_window_le hs21 (le_of_lt hz) 0 (Or.inl rfl))
    (z_coord_mem_window_le hs21 (le_of_lt hz) 1 (Or.inr rfl))

/-! ## The localising bump and the region `awR` -/

lemma contDiff_awPsi_joint :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => awPsi p.1 p.2.1 p.2.2) := by
  have hb : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (awPbeta : ℝ → ℝ) t) := ContDiffBump.contDiff awPbeta
  have hz : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (awPzeta : ℝ → ℝ) t) := ContDiffBump.contDiff awPzeta
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => (awPbeta : ℝ → ℝ) p.1) :=
    hb.comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => (awPbeta : ℝ → ℝ) p.2.1) :=
    hb.comp (contDiff_fst.comp contDiff_snd)
  have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => (awPzeta : ℝ → ℝ) (p.2.2 0)) :=
    hz.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => p.2.2 0))
  have h4 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => (awPzeta : ℝ → ℝ) (p.2.2 1)) :=
    hz.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => p.2.2 1))
  simpa only [awPsi] using ((h1.mul h2).mul h3).mul h4

lemma isClosed_awRclosed : IsClosed awRclosed := by
  have h1 : Continuous (fun p : ℝ × ℝ × St => p.1) :=
    (continuous_fst : Continuous (fun p : ℝ × ℝ × St => p.1))
  have h2 : Continuous (fun p : ℝ × ℝ × St => p.2.1) :=
    (continuous_fst.comp continuous_snd :
      Continuous (fun p : ℝ × ℝ × St => p.2.1))
  have h3 : Continuous (fun p : ℝ × ℝ × St => |p.2.2 0|) := by
    have h : Continuous (fun p : ℝ × ℝ × St => p.2.2 0) :=
      (continuous_apply (0 : Fin 4)).comp (continuous_snd.comp continuous_snd)
    exact h.abs
  have h4 : Continuous (fun p : ℝ × ℝ × St => |p.2.2 1|) := by
    have h : Continuous (fun p : ℝ × ℝ × St => p.2.2 1) :=
      (continuous_apply (1 : Fin 4)).comp (continuous_snd.comp continuous_snd)
    exact h.abs
  simp only [awRclosed, setOf_and]
  exact (isClosed_le continuous_const h1).inter
    ((isClosed_le h1 continuous_const).inter
    ((isClosed_le continuous_const h2).inter
    ((isClosed_le h2 continuous_const).inter
    ((isClosed_le continuous_const h3).inter
    ((isClosed_le h3 continuous_const).inter
    ((isClosed_le continuous_const h4).inter
     (isClosed_le h4 continuous_const)))))))

lemma awRclosed_subset_awR : awRclosed ⊆ awR := by
  intro p hp
  have hp' : 11 / 25 ≤ p.1 ∧ p.1 ≤ 53 / 50 ∧ 11 / 25 ≤ p.2.1 ∧ p.2.1 ≤ 53 / 50 ∧
      21 / 100 ≤ |p.2.2 0| ∧ |p.2.2 0| ≤ 199 / 100 ∧ 21 / 100 ≤ |p.2.2 1| ∧
      |p.2.2 1| ≤ 199 / 100 := hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hp'
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

lemma support_awPsi_subset_awRclosed {p : ℝ × ℝ × St} (hp : awPsi p.1 p.2.1 p.2.2 ≠ 0) :
    p ∈ awRclosed := by
  show 11 / 25 ≤ p.1 ∧ p.1 ≤ 53 / 50 ∧ 11 / 25 ≤ p.2.1 ∧ p.2.1 ≤ 53 / 50 ∧
      21 / 100 ≤ |p.2.2 0| ∧ |p.2.2 0| ≤ 199 / 100 ∧ 21 / 100 ≤ |p.2.2 1| ∧
      |p.2.2 1| ≤ 199 / 100
  have hb1 : (awPbeta : ℝ → ℝ) p.1 ≠ 0 := fun h0 => hp (by simp [awPsi, h0])
  have hb2 : (awPbeta : ℝ → ℝ) p.2.1 ≠ 0 := fun h0 => hp (by simp [awPsi, h0])
  have hz1 : (awPzeta : ℝ → ℝ) (p.2.2 0) ≠ 0 := fun h0 => hp (by simp [awPsi, h0])
  have hz2 : (awPzeta : ℝ → ℝ) (p.2.2 1) ≠ 0 := fun h0 => hp (by simp [awPsi, h0])
  obtain ⟨h1a, h1b⟩ := awPbeta_ne_zero_bounds hb1
  obtain ⟨h2a, h2b⟩ := awPbeta_ne_zero_bounds hb2
  obtain ⟨h3a, h3b⟩ := awPzeta_ne_zero_bounds hz1
  obtain ⟨h4a, h4b⟩ := awPzeta_ne_zero_bounds hz2
  exact ⟨le_of_lt h1a, le_of_lt h1b, le_of_lt h2a, le_of_lt h2b, le_of_lt h3a, le_of_lt h3b,
    le_of_lt h4a, le_of_lt h4b⟩

lemma closure_support_awPsi_subset_awR :
    closure (Function.support (fun p : ℝ × ℝ × St => awPsi p.1 p.2.1 p.2.2)) ⊆ awR :=
  (closure_minimal (fun _ hp => support_awPsi_subset_awRclosed hp) isClosed_awRclosed).trans
    awRclosed_subset_awR

lemma isOpen_awR : IsOpen awR := by
  have h1 : Continuous (fun p : ℝ × ℝ × St => p.1) :=
    (continuous_fst : Continuous (fun p : ℝ × ℝ × St => p.1))
  have h2 : Continuous (fun p : ℝ × ℝ × St => p.2.1) :=
    (continuous_fst.comp continuous_snd :
      Continuous (fun p : ℝ × ℝ × St => p.2.1))
  have h3 : Continuous (fun p : ℝ × ℝ × St => |p.2.2 0|) := by
    have h : Continuous (fun p : ℝ × ℝ × St => p.2.2 0) :=
      (continuous_apply (0 : Fin 4)).comp (continuous_snd.comp continuous_snd)
    exact h.abs
  have h4 : Continuous (fun p : ℝ × ℝ × St => |p.2.2 1|) := by
    have h : Continuous (fun p : ℝ × ℝ × St => p.2.2 1) :=
      (continuous_apply (1 : Fin 4)).comp (continuous_snd.comp continuous_snd)
    exact h.abs
  simp only [awR, setOf_and]
  exact (isOpen_lt continuous_const h1).inter
    ((isOpen_lt h1 continuous_const).inter
    ((isOpen_lt continuous_const h2).inter
    ((isOpen_lt h2 continuous_const).inter
    ((isOpen_lt continuous_const h3).inter
    ((isOpen_lt h3 continuous_const).inter
    ((isOpen_lt continuous_const h4).inter
     (isOpen_lt h4 continuous_const)))))))

/-! ## Smoothness of the manifest kernel composite on `awR` -/

/-- The manifest kernel `KvecM`, evaluated at the `sin²`-substituted slope `u + sin²θ (σ-u)`,
is `C^∞` on `univ ×ˢ awR`: there the Abel radicands are positive. -/
lemma contDiffOn_kvecM_integrand (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) (i : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × ℝ × St) =>
        (KernelExt.KvecM n h (q.2.1 + Real.sin q.1 ^ 2 * (q.2.2.1 - q.2.1)) q.2.2.1
          (q.2.2.2 0) (q.2.2.2 1) (q.2.2.2 2) (q.2.2.2 3)) i)
      (Set.univ ×ˢ awR) := by
  have hK : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × ℝ × St) =>
        KernelExt.KvecM n h (q.2.1 + Real.sin q.1 ^ 2 * (q.2.2.1 - q.2.1)) q.2.2.1
          (q.2.2.2 0) (q.2.2.2 1) (q.2.2.2 2) (q.2.2.2 3)) (Set.univ ×ˢ awR) := by
    refine KernelExt.KvecM_contDiffOn_comp n hh ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · fun_prop
    · fun_prop
    · fun_prop
    · fun_prop
    · -- positivity at the `-x` endpoint
      intro q hq
      obtain ⟨hu1, hu2, hs1, hs2, hz1, hz2, hz3, hz4⟩ :
          2 / 5 < q.2.1 ∧ q.2.1 < 11 / 10 ∧ 2 / 5 < q.2.2.1 ∧ q.2.2.1 < 11 / 10 ∧
            41 / 200 < |q.2.2.2 0| ∧ |q.2.2.2 0| < 2 ∧ 41 / 200 < |q.2.2.2 1| ∧
            |q.2.2.2 1| < 2 := hq.2
      have hmin : min q.2.1 q.2.2.1 ≤ q.2.1 + Real.sin q.1 ^ 2 * (q.2.2.1 - q.2.1) := by
        have hsin : Real.sin q.1 ^ 2 ≤ 1 := Real.sin_sq_le_one q.1
        rcases le_total q.2.1 q.2.2.1 with hle | hle
        · rw [min_eq_left hle]
          have : 0 ≤ Real.sin q.1 ^ 2 * (q.2.2.1 - q.2.1) :=
            mul_nonneg (sq_nonneg _) (by linarith)
          linarith
        · rw [min_eq_right hle]
          have h1 : 0 ≤ 1 - Real.sin q.1 ^ 2 := by linarith
          have h2 : (1 - Real.sin q.1 ^ 2) * (q.2.1 - q.2.2.1) ≥ 0 :=
            mul_nonneg h1 (by linarith)
          nlinarith
      have hS : 1 / 10 < q.2.2.1 +
          (q.2.1 + Real.sin q.1 ^ 2 * (q.2.2.1 - q.2.1)) := by
        have h2 : 2 / 5 < q.2.1 + Real.sin q.1 ^ 2 * (q.2.2.1 - q.2.1) :=
          lt_of_lt_of_le (lt_min hu1 hs1) hmin
        linarith
      have ht : 1 / 5 ≤ |-(q.2.2.2 0)| := by
        rw [abs_neg]; linarith
      have hkrad := krad_pos_of_add_pos hsupp hsmall (a := q.2.1 + Real.sin q.1 ^ 2 * (q.2.2.1 - q.2.1))
        (σ := q.2.2.1) (t := -(q.2.2.2 0)) hS ht
      rw [Kden_eq_sqrt_krad]
      exact Real.sqrt_pos.mpr hkrad
    · -- positivity at the `y` endpoint
      intro q hq
      obtain ⟨hu1, hu2, hs1, hs2, hz1, hz2, hz3, hz4⟩ :
          2 / 5 < q.2.1 ∧ q.2.1 < 11 / 10 ∧ 2 / 5 < q.2.2.1 ∧ q.2.2.1 < 11 / 10 ∧
            41 / 200 < |q.2.2.2 0| ∧ |q.2.2.2 0| < 2 ∧ 41 / 200 < |q.2.2.2 1| ∧
            |q.2.2.2 1| < 2 := hq.2
      have hmin : min q.2.1 q.2.2.1 ≤ q.2.1 + Real.sin q.1 ^ 2 * (q.2.2.1 - q.2.1) := by
        have hsin : Real.sin q.1 ^ 2 ≤ 1 := Real.sin_sq_le_one q.1
        rcases le_total q.2.1 q.2.2.1 with hle | hle
        · rw [min_eq_left hle]
          have : 0 ≤ Real.sin q.1 ^ 2 * (q.2.2.1 - q.2.1) :=
            mul_nonneg (sq_nonneg _) (by linarith)
          linarith
        · rw [min_eq_right hle]
          have h1 : 0 ≤ 1 - Real.sin q.1 ^ 2 := by linarith
          have h2 : (1 - Real.sin q.1 ^ 2) * (q.2.1 - q.2.2.1) ≥ 0 :=
            mul_nonneg h1 (by linarith)
          nlinarith
      have hS : 1 / 10 < q.2.2.1 +
          (q.2.1 + Real.sin q.1 ^ 2 * (q.2.2.1 - q.2.1)) := by
        have h2 : 2 / 5 < q.2.1 + Real.sin q.1 ^ 2 * (q.2.2.1 - q.2.1) :=
          lt_of_lt_of_le (lt_min hu1 hs1) hmin
        linarith
      have ht : 1 / 5 ≤ |q.2.2.2 1| := by linarith
      have hkrad := krad_pos_of_add_pos hsupp hsmall (a := q.2.1 + Real.sin q.1 ^ 2 * (q.2.2.1 - q.2.1))
        (σ := q.2.2.1) (t := q.2.2.2 1) hS ht
      rw [Kden_eq_sqrt_krad]
      exact Real.sqrt_pos.mpr hkrad
  exact (contDiffOn_pi.mp hK) i

/-- The bump times the manifest kernel composite is `C^∞` on all of `ℝ × (ℝ × ℝ × St)`. -/
lemma contDiff_awG2Ms_integrand (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × ℝ × St) =>
        awPsi q.2.1 q.2.2.1 q.2.2.2 *
          (KernelExt.KvecM n h (q.2.1 + Real.sin q.1 ^ 2 * (q.2.2.1 - q.2.1)) q.2.2.1
            (q.2.2.2 0) (q.2.2.2 1) (q.2.2.2 2) (q.2.2.2 3)) i) := by
  have hpsi : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × ℝ × St) => awPsi q.2.1 q.2.2.1 q.2.2.2) :=
    contDiff_awPsi_joint.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × ℝ × St) => (q.2.1, q.2.2.1, q.2.2.2)))
  have hsupp' : closure (Function.support
      (fun q : ℝ × (ℝ × ℝ × St) => awPsi q.2.1 q.2.2.1 q.2.2.2)) ⊆ Set.univ ×ˢ awR := by
    have hpre : Function.support (fun q : ℝ × (ℝ × ℝ × St) => awPsi q.2.1 q.2.2.1 q.2.2.2) =
        (fun q : ℝ × (ℝ × ℝ × St) => q.2) ⁻¹'
          Function.support (fun p : ℝ × ℝ × St => awPsi p.1 p.2.1 p.2.2) := rfl
    rw [hpre]
    refine ((continuous_snd :
      Continuous (fun q : ℝ × (ℝ × ℝ × St) => q.2)).closure_preimage_subset _).trans ?_
    intro q hq
    exact ⟨trivial, closure_support_awPsi_subset_awR hq⟩
  have key : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × ℝ × St) =>
        (KernelExt.KvecM n h (q.2.1 + Real.sin q.1 ^ 2 * (q.2.2.1 - q.2.1)) q.2.2.1
          (q.2.2.2 0) (q.2.2.2 1) (q.2.2.2 2) (q.2.2.2 3)) i *
          awPsi q.2.1 q.2.2.1 q.2.2.2) :=
    contDiff_mul_of_contDiffOn_of_closure_support_subset
      (V := ℝ × (ℝ × ℝ × St)) (R := Set.univ ×ˢ awR)
      (f := fun q : ℝ × (ℝ × ℝ × St) =>
        (KernelExt.KvecM n h (q.2.1 + Real.sin q.1 ^ 2 * (q.2.2.1 - q.2.1)) q.2.2.1
          (q.2.2.2 0) (q.2.2.2 1) (q.2.2.2 2) (q.2.2.2 3)) i)
      (g := fun q : ℝ × (ℝ × ℝ × St) => awPsi q.2.1 q.2.2.1 q.2.2.2)
      (isOpen_univ.prod isOpen_awR)
      (contDiffOn_kvecM_integrand n hh hsupp hsmall i) hpsi hsupp'
  simpa only [mul_comm] using key

/-! ## Smoothness of the localised average and `Θ`-data -/

/-- The localised `τ`-average is `C^∞`. -/
lemma contDiff_awG2Ms (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => awG2Ms n h p.1 p.2.1 p.2.2 i) := by
  have hF : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × ℝ × St) =>
        2 * awPsi q.2.1 q.2.2.1 q.2.2.2 *
          (KernelExt.KvecM n h (q.2.1 + Real.sin q.1 ^ 2 * (q.2.2.1 - q.2.1)) q.2.2.1
            (q.2.2.2 0) (q.2.2.2 1) (q.2.2.2 2) (q.2.2.2 3)) i) := by
    have := (contDiff_const (c := (2 : ℝ))).mul
      (contDiff_awG2Ms_integrand n hh hsupp hsmall i)
    simpa only [mul_assoc] using this
  rw [contDiff_infty]
  intro m
  exact Work.Analysis.Calculus.contDiff_intervalIntegral_param (ℝ × ℝ × St) m ℝ
    (fun q : ℝ × (ℝ × ℝ × St) =>
      2 * awPsi q.2.1 q.2.2.1 q.2.2.2 *
        (KernelExt.KvecM n h (q.2.1 + Real.sin q.1 ^ 2 * (q.2.2.1 - q.2.1)) q.2.2.1
          (q.2.2.2 0) (q.2.2.2 1) (q.2.2.2 2) (q.2.2.2 3)) i) 0 (Real.pi / 2)
    (hF.of_le (by exact_mod_cast le_top))

lemma contDiff_coord (k : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => p.2.2 k) :=
  (contDiff_pi.mp (contDiff_snd.comp contDiff_snd :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => p.2.2))) k

/-- The localised `Θ`-data is `C^∞` everywhere. -/
lemma contDiff_awThetaMs (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => awThetaMs n h p.1 p.2.1 p.2.2) := by
  have hjoint : ∀ i : Fin 2, ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (ℝ × St) × ℝ => awG2Ms n h q.2 q.1.1 q.1.2 i) := by
    intro i
    have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × St) × ℝ => (q.2, q.1.1, q.1.2)) := by
      fun_prop
    exact (contDiff_awG2Ms n hh hsupp hsmall i).comp hφ
  have hderiv : ∀ i : Fin 2, ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ × St => deriv (fun u : ℝ => awG2Ms n h u p.2.1 p.2.2 i) p.1) := by
    intro i
    have hgen := Commons.Analysis.Calculus.contDiff_parametric_iteratedDeriv_gen
      (P := ℝ × St) (G := fun (r : ℝ × St) (u : ℝ) => awG2Ms n h u r.1 r.2 i) (hjoint i) 1
    have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => ((p.2.1, p.2.2), p.1)) := by
      fun_prop
    have hcomp := hgen.comp hφ
    simpa only [Function.comp_def, iteratedDeriv_one] using hcomp
  rw [contDiff_pi]
  intro i
  fin_cases i
  · show ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => -(p.2.2 2))
    exact (contDiff_coord 2).neg
  · show ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => -(p.2.2 3))
    exact (contDiff_coord 3).neg
  · show ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St =>
      -(deriv (fun u : ℝ => awG2Ms n h u p.2.1 p.2.2 0) p.1))
    exact (hderiv 0).neg
  · show ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St =>
      -(deriv (fun u : ℝ => awG2Ms n h u p.2.1 p.2.2 1) p.1))
    exact (hderiv 1).neg

/-! ## The localised data agrees with the paper's data -/

/-- **The localised average is the bump times the manifest average.**  This is the `sin²`
substitution, together with pulling the constant bump factor out of the `θ`-integral. -/
lemma awG2Ms_eq (n : ℕ) (h : ℝ → ℝ) (u σ : ℝ) (z : St) (i : Fin 2) :
    awG2Ms n h u σ z i =
      awPsi u σ z * (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) i := by
  have hsub := Work.Analysis.Calculus.integral_div_sqrt_eq_integral_sin_sq
    (fun τ : ℝ => (KernelExt.KvecM n h (u + τ * (σ - u)) σ (z 0) (z 1) (z 2) (z 3)) i)
  have hstep : awG2Ms n h u σ z i =
      awPsi u σ z * ∫ θ in (0 : ℝ)..(Real.pi / 2),
        2 * (KernelExt.KvecM n h (u + Real.sin θ ^ 2 * (σ - u)) σ
          (z 0) (z 1) (z 2) (z 3)) i := by
    rw [show awG2Ms n h u σ z i = ∫ θ in (0 : ℝ)..(Real.pi / 2),
        awPsi u σ z * (2 * (KernelExt.KvecM n h (u + Real.sin θ ^ 2 * (σ - u)) σ
          (z 0) (z 1) (z 2) (z 3)) i) from
      intervalIntegral.integral_congr (fun θ _ => by ring)]
    exact intervalIntegral.integral_const_mul _ _
  rw [hstep, KernelExt.G2M]
  congr 1
  exact hsub.symm

/-- On `awGoodT` the localised `Θ`-data is the paper's `ThetaM`. -/
lemma awThetaMs_eq_ThetaM (n : ℕ) {h : ℝ → ℝ} {s σ : ℝ} {z : St}
    (hs : |s - 3 / 4| < 3 / 10) (hσ : |σ - 3 / 4| < 3 / 10)
    (hz : ‖z - baseState σ‖ < 41 / 100) :
    awThetaMs n h s σ z = KernelExt.ThetaM n h s σ z := by
  have hpsi := eventually_awPsi_eq_one hs hσ hz
  have hG : ∀ i : Fin 2, (fun u : ℝ => awG2Ms n h u σ z i) =ᶠ[𝓝 s]
      (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) i) := by
    intro i
    filter_upwards [hpsi] with u hu
    rw [awG2Ms_eq n h u σ z i, hu, one_mul]
  funext i
  fin_cases i
  · simp [awThetaMs, KernelExt.ThetaM]
  · simp [awThetaMs, KernelExt.ThetaM]
  · show -(deriv (fun u : ℝ => awG2Ms n h u σ z 0) s) =
      -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s)
    rw [Filter.EventuallyEq.deriv_eq (hG 0)]
  · show -(deriv (fun u : ℝ => awG2Ms n h u σ z 1) s) =
      -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s)
    rw [Filter.EventuallyEq.deriv_eq (hG 1)]

/-! ## The cutoff and the good region -/

lemma contDiff_baseState_comp' :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => baseState p.2.1) :=
  contDiff_baseState_comp.comp contDiff_snd

/-- The `Θ`-cutoff is `C^∞` everywhere. -/
lemma contDiff_awChiT :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => awChiT p.1 p.2.1 p.2.2) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => (awCs : ℝ → ℝ) p.1) :=
    (ContDiffBump.contDiff awCs).comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => (awCs : ℝ → ℝ) p.2.1) :=
    (ContDiffBump.contDiff awCs).comp (contDiff_fst.comp contDiff_snd)
  have h3 : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ × St => (awCz : St → ℝ) (p.2.2 - baseState p.2.1)) :=
    (ContDiffBump.contDiff awCz).comp
      ((contDiff_snd.comp contDiff_snd).sub contDiff_baseState_comp')
  simpa only [awChiT, mul_assoc] using (h1.mul h2).mul h3

/-- If the `Θ`-cutoff does not vanish, the point lies in the open region `awGoodT`. -/
lemma mem_awGoodT_of_awChiT_ne_zero {s σ : ℝ} {z : St} (h : awChiT s σ z ≠ 0) :
    (s, σ, z) ∈ awGoodT := by
  have h1 : (awCs : ℝ → ℝ) s ≠ 0 := fun h0 => h (by simp [awChiT, h0])
  have h2 : (awCs : ℝ → ℝ) σ ≠ 0 := fun h0 => h (by simp [awChiT, h0])
  have h3 : (awCz : St → ℝ) (z - baseState σ) ≠ 0 := fun h0 => h (by simp [awChiT, h0])
  have hd1 : dist s (3 / 4) < 11 / 40 := by
    by_contra hcon
    exact h1 (ContDiffBump.zero_of_le_dist awCs (by rw [awCs_rOut]; exact not_lt.mp hcon))
  have hd2 : dist σ (3 / 4) < 11 / 40 := by
    by_contra hcon
    exact h2 (ContDiffBump.zero_of_le_dist awCs (by rw [awCs_rOut]; exact not_lt.mp hcon))
  have hd3 : dist (z - baseState σ) 0 < 2 / 5 := by
    by_contra hcon
    exact h3 (ContDiffBump.zero_of_le_dist awCz (by rw [awCz_rOut]; exact not_lt.mp hcon))
  rw [Real.dist_eq] at hd1 hd2
  rw [dist_zero_right] at hd3
  exact ⟨by linarith, by linarith, by linarith⟩

lemma isOpen_awGoodT : IsOpen awGoodT := by
  have h1 : Continuous (fun p : ℝ × ℝ × St => |p.1 - 3 / 4|) := by fun_prop
  have h2 : Continuous (fun p : ℝ × ℝ × St => |p.2.1 - 3 / 4|) := by fun_prop
  have h3 : Continuous (fun p : ℝ × ℝ × St => ‖p.2.2 - baseState p.2.1‖) :=
    ((contDiff_snd.comp contDiff_snd).sub contDiff_baseState_comp').continuous.norm
  simp only [awGoodT, setOf_and]
  exact (isOpen_lt h1 continuous_const).inter
    ((isOpen_lt h2 continuous_const).inter (isOpen_lt h3 continuous_const))

/-! ## The target -/

/-- The localised data vanishes when the slope cutoff vanishes. -/
lemma awTheta_eq_zero_of_le_awCs {n : ℕ} {h : ℝ → ℝ} {s σ : ℝ} {z : St}
    (hs : 11 / 40 ≤ |s - 3 / 4|) : awTheta n h s σ z = 0 := by
  rw [awTheta, awChiT, awCs_eq_zero hs, zero_mul, zero_mul, zero_smul]

/-- The localised data vanishes when the second slope cutoff vanishes. -/
lemma awTheta_eq_zero_of_le_awCs' {n : ℕ} {h : ℝ → ℝ} {s σ : ℝ} {z : St}
    (hs : 11 / 40 ≤ |σ - 3 / 4|) : awTheta n h s σ z = 0 := by
  rw [awTheta, awChiT, awCs_eq_zero hs, mul_zero, zero_mul, zero_smul]

/-- The localised data vanishes when the state cutoff vanishes. -/
lemma awTheta_eq_zero_of_le_awCz {n : ℕ} {h : ℝ → ℝ} {s σ : ℝ} {z : St}
    (hs : 2 / 5 ≤ ‖z - baseState σ‖) : awTheta n h s σ z = 0 := by
  rw [awTheta, awChiT, awCz_eq_zero hs, mul_zero, zero_smul]

theorem aw_contDiffOn_awTheta (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × Work.OddVolterra.St =>
      Work.OddVolterra.Existence.awTheta n h p.1 p.2.1 p.2.2) Set.univ := by
  have hThetaS := contDiff_awThetaMs n hh hsupp hsmall
  have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St =>
      awChiT p.1 p.2.1 p.2.2 • awThetaMs n h p.1 p.2.1 p.2.2) :=
    contDiff_awChiT.smul hThetaS
  -- on `awGoodT` the localised data is the smooth one
  have hE : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ × St => awTheta n h p.1 p.2.1 p.2.2) awGoodT := by
    refine (hprod.contDiffOn.mono (Set.subset_univ _)).congr (fun p hp => ?_)
    have hp' : |p.1 - 3 / 4| < 3 / 10 ∧ |p.2.1 - 3 / 4| < 3 / 10 ∧
        ‖p.2.2 - baseState p.2.1‖ < 41 / 100 := hp
    obtain ⟨h1, h2, h3⟩ := hp'
    rw [awTheta, awThetaMs_eq_ThetaM n h1 h2 h3]
  -- off `awGoodT` the cutoff vanishes on a neighbourhood
  have hzero1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ × St => awTheta n h p.1 p.2.1 p.2.2)
      {q : ℝ × ℝ × St | 11 / 40 < |q.1 - 3 / 4|} :=
    (contDiffOn_const (c := (0 : St))).congr
      (fun q hq => awTheta_eq_zero_of_le_awCs (le_of_lt hq))
  have hzero2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ × St => awTheta n h p.1 p.2.1 p.2.2)
      {q : ℝ × ℝ × St | 11 / 40 < |q.2.1 - 3 / 4|} :=
    (contDiffOn_const (c := (0 : St))).congr
      (fun q hq => awTheta_eq_zero_of_le_awCs' (le_of_lt hq))
  have hzero3 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ × St => awTheta n h p.1 p.2.1 p.2.2)
      {q : ℝ × ℝ × St | 2 / 5 < ‖q.2.2 - baseState q.2.1‖} :=
    (contDiffOn_const (c := (0 : St))).congr
      (fun q hq => awTheta_eq_zero_of_le_awCz (le_of_lt hq))
  refine contDiffOn_of_locally_contDiffOn (fun p _ => ?_)
  by_cases hp : p ∈ awGoodT
  · exact ⟨awGoodT, isOpen_awGoodT, hp, hE.mono Set.inter_subset_right⟩
  · have hp' : ¬(|p.1 - 3 / 4| < 3 / 10 ∧ |p.2.1 - 3 / 4| < 3 / 10 ∧
        ‖p.2.2 - baseState p.2.1‖ < 41 / 100) := hp
    rcases not_and_or.mp hp' with h1 | h23
    · have h1' : 3 / 10 ≤ |p.1 - 3 / 4| := not_lt.mp h1
      have hmem : p ∈ {q : ℝ × ℝ × St | 11 / 40 < |q.1 - 3 / 4|} := by
        show 11 / 40 < |p.1 - 3 / 4|
        linarith
      exact ⟨_, isOpen_lt continuous_const (by fun_prop), hmem,
        hzero1.mono Set.inter_subset_right⟩
    · rcases not_and_or.mp h23 with h2 | h3
      · have h2' : 3 / 10 ≤ |p.2.1 - 3 / 4| := not_lt.mp h2
        have hmem : p ∈ {q : ℝ × ℝ × St | 11 / 40 < |q.2.1 - 3 / 4|} := by
          show 11 / 40 < |p.2.1 - 3 / 4|
          linarith
        exact ⟨_, isOpen_lt continuous_const (by fun_prop), hmem,
          hzero2.mono Set.inter_subset_right⟩
      · have h3' : 41 / 100 ≤ ‖p.2.2 - baseState p.2.1‖ := not_lt.mp h3
        have hmem : p ∈ {q : ℝ × ℝ × St | 2 / 5 < ‖q.2.2 - baseState q.2.1‖} := by
          show 2 / 5 < ‖p.2.2 - baseState p.2.1‖
          linarith
        exact ⟨_, isOpen_lt continuous_const
            (((contDiff_snd.comp contDiff_snd).sub contDiff_baseState_comp').continuous.norm),
          hmem, hzero3.mono Set.inter_subset_right⟩

end

end Work.OddVolterra.Existence
