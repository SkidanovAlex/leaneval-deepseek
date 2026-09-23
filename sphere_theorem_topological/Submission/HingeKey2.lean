import Submission.HingeKey
import Submission.Commons.Geometry.Sphere.modelDist_mono_angle

/-!
# The Key Lemma for the globalisation of the hinge comparison

This file proves the *Key Lemma* (`arXiv:2404.09792` Theorem 4.1.1) in the `VHinge` language of
`Submission/HingeKey.lean`: if the hinge comparison holds at every point of the ball `B_l(p)` for
hinges of size `< (2/3)l`, then there is no violating hinge with one endpoint `p` and of size `< l`.

The proof is by contradiction: from a violating hinge one builds (using `VHinge.step`) a sequence of
violating hinges of non-increasing size and non-increasing associated model distance.  If some size
drops below `l/2` the comparison applies to it directly; otherwise the sizes converge to `r∞` and
the model distances converge to `r∞ ≥ d(p,q)`, while each of them is `< d(p,q)`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow
open Submission.HingeGlobal
open Submission.HingeKey

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.HingeKey2

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## Auxiliary real-analytic facts about the model distance and the model angle -/

lemma modelDist1_zero_eq_abs_sub {a b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) Real.pi)
    (hb : b ∈ Set.Icc (0:ℝ) Real.pi) : modelDist1 0 a b = |a - b| := by
  rw [modelDist1]
  have h1 : Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos 0
      = Real.cos (a - b) := by
    rw [Real.cos_zero, mul_one, Real.cos_sub]
  rw [h1, ← Real.cos_abs]
  apply Real.arccos_cos (abs_nonneg _)
  rw [abs_le]
  exact ⟨by linarith [ha.1, hb.2], by linarith [hb.1, ha.2]⟩

/-- The model distance dominates the difference of the two sides. -/
lemma modelDist1_ge_abs_sub {θ a b : ℝ} (hθ : θ ∈ Set.Icc (0:ℝ) Real.pi)
    (ha : a ∈ Set.Icc (0:ℝ) Real.pi) (hb : b ∈ Set.Icc (0:ℝ) Real.pi) :
    |a - b| ≤ modelDist1 θ a b := by
  rw [← modelDist1_zero_eq_abs_sub ha hb]
  simpa only [modelDist1] using Commons.Geometry.Sphere.modelDist_mono_angle ha.1 ha.2 hb.1 hb.2
    (show (0:ℝ) ∈ Set.Icc (0:ℝ) Real.pi from ⟨le_refl 0, Real.pi_pos.le⟩) hθ hθ.1

/-- The model distance at angle `π` is the sum of the sides. -/
lemma modelDist1_pi_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ Real.pi) :
    modelDist1 Real.pi a b = a + b := by
  rw [modelDist1, Real.cos_pi]
  have h1 : Real.cos a * Real.cos b + Real.sin a * Real.sin b * (-1) = Real.cos (a + b) := by
    rw [Real.cos_add]; ring
  rw [h1, Real.arccos_cos (by linarith) hab]

/-- The model angle of a configuration whose opposite side tends to the sum of the two other
sides, with the two other sides bounded below, tends to `π`. -/
lemma tendsto_modelAngle_pi {w t s : ℕ → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hsin : ∀ᶠ n in atTop, σ ≤ Real.sin (t n) * Real.sin (s n))
    (hw : Tendsto (fun n => w n - (t n + s n)) atTop (𝓝 0)) :
    Tendsto (fun n => modelAngle (w n) (t n) (s n)) atTop (𝓝 Real.pi) := by
  have hnum : Tendsto (fun n => Real.cos (w n) - Real.cos (t n + s n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    have h1 : ∀ n, |Real.cos (w n) - Real.cos (t n + s n)| ≤ |w n - (t n + s n)| := by
      intro n
      have h := Real.lipschitzWith_cos.dist_le_mul (w n) (t n + s n)
      rw [Real.dist_eq, Real.dist_eq] at h
      simpa using h
    have h2 : Tendsto (fun n => |w n - (t n + s n)|) atTop (𝓝 0) := by
      simpa only [Real.norm_eq_abs, norm_zero] using hw.norm
    exact squeeze_zero (fun n => abs_nonneg _) h1 h2
  have hfrac : Tendsto (fun n => (Real.cos (w n) - Real.cos (t n) * Real.cos (s n))
      / (Real.sin (t n) * Real.sin (s n))) atTop (𝓝 (-1)) := by
    have h2 : Tendsto (fun n => (Real.cos (w n) - Real.cos (t n + s n))
        / (Real.sin (t n) * Real.sin (s n))) atTop (𝓝 0) := by
      have hbound : ∀ᶠ n in atTop, |(Real.cos (w n) - Real.cos (t n + s n))
          / (Real.sin (t n) * Real.sin (s n))| ≤ |Real.cos (w n) - Real.cos (t n + s n)| / σ := by
        filter_upwards [hsin] with n hn
        rw [abs_div]
        have hpos : 0 < Real.sin (t n) * Real.sin (s n) := lt_of_lt_of_le hσ hn
        have hs : σ ≤ |Real.sin (t n) * Real.sin (s n)| := by
          rw [abs_of_pos hpos]; exact hn
        exact div_le_div_of_nonneg_left (abs_nonneg _) hσ hs
      have h3 : Tendsto (fun n => |Real.cos (w n) - Real.cos (t n + s n)| / σ) atTop (𝓝 0) := by
        have := hnum.norm
        simpa only [Real.norm_eq_abs, norm_zero, zero_div] using this.div_const σ
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [Real.norm_eq_abs]
      exact squeeze_zero' (Filter.Eventually.of_forall (fun n => abs_nonneg _)) hbound h3
    have h4 : Tendsto (fun n => -1 + (Real.cos (w n) - Real.cos (t n + s n))
        / (Real.sin (t n) * Real.sin (s n))) atTop (𝓝 (-1)) := by
      simpa using tendsto_const_nhds.add h2
    refine h4.congr' ?_
    filter_upwards [hsin] with n hn
    have hs := lt_of_lt_of_le hσ hn
    have hsin_ne : Real.sin (t n) * Real.sin (s n) ≠ 0 := ne_of_gt hs
    rw [Real.cos_add, sub_div, sub_div, div_self hsin_ne]
    ring
  have h := (Real.continuous_arccos.tendsto (-1)).comp hfrac
  rw [show Real.arccos (-1) = Real.pi from Real.arccos_neg_one] at h
  simpa only [modelAngle, Function.comp_def] using h

/-- The model distance in the limit `θ → π` with `a + b → c` tends to `c`. -/
lemma tendsto_modelDist1_pi {θ a b : ℕ → ℝ} {c : ℝ}
    (hθ : Tendsto θ atTop (𝓝 Real.pi))
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (hab : ∀ n, a n + b n ≤ Real.pi)
    (hs : Tendsto (fun n => a n + b n) atTop (𝓝 c))
    (hc : c ∈ Set.Icc (0:ℝ) Real.pi) :
    Tendsto (fun n => modelDist1 (θ n) (a n) (b n)) atTop (𝓝 c) := by
  have hcos : Tendsto (fun n => Real.cos (a n) * Real.cos (b n)
      + Real.sin (a n) * Real.sin (b n) * Real.cos (θ n)) atTop (𝓝 (Real.cos c)) := by
    -- the difference with `cos (a n + b n)` is `sin a sin b (1 + cos θ n)` which tends to 0
    have hdiff : Tendsto (fun n => Real.sin (a n) * Real.sin (b n) * (1 + Real.cos (θ n)))
        atTop (𝓝 0) := by
      have hθ1 : Tendsto (fun n => 1 + Real.cos (θ n)) atTop (𝓝 0) := by
        have := (Real.continuous_cos.tendsto Real.pi).comp hθ
        rw [Real.cos_pi] at this
        have h1 : Tendsto (fun n => (1:ℝ) + Real.cos (θ n)) atTop (𝓝 (1 + (-1))) :=
          tendsto_const_nhds.add this
        simpa using h1
      have hbound : ∀ n, |Real.sin (a n) * Real.sin (b n) * (1 + Real.cos (θ n))|
          ≤ |1 + Real.cos (θ n)| := by
        intro n
        have h1 : |Real.sin (a n)| ≤ 1 := by
          rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (ha n) (by linarith [hab n, hb n]))]
          exact Real.sin_le_one (a n)
        have h2 : |Real.sin (b n)| ≤ 1 := by
          rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (hb n) (by linarith [hab n, ha n]))]
          exact Real.sin_le_one (b n)
        rw [abs_mul, abs_mul]
        calc |Real.sin (a n)| * |Real.sin (b n)| * |1 + Real.cos (θ n)|
            ≤ 1 * 1 * |1 + Real.cos (θ n)| := by
              apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
              exact mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          _ = |1 + Real.cos (θ n)| := by ring
      have h3 : Tendsto (fun n => |1 + Real.cos (θ n)|) atTop (𝓝 0) := by
        simpa only [Real.norm_eq_abs, norm_zero] using hθ1.norm
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [Real.norm_eq_abs]
      exact squeeze_zero (fun n => abs_nonneg _) hbound h3
    have hsum : Tendsto (fun n => Real.cos (a n + b n)) atTop (𝓝 (Real.cos c)) :=
      Real.continuous_cos.continuousAt.tendsto.comp hs
    have h2 : Tendsto (fun n => Real.cos (a n + b n)
        + Real.sin (a n) * Real.sin (b n) * (1 + Real.cos (θ n))) atTop (𝓝 (Real.cos c)) := by
      simpa using hsum.add hdiff
    refine h2.congr' ?_
    filter_upwards with n
    rw [Real.cos_add]
    ring
  have h := (Real.continuous_arccos.tendsto (Real.cos c)).comp hcos
  rw [Real.arccos_cos hc.1 hc.2] at h
  simpa only [modelDist1, Function.comp_def] using h

/-! ## The Key Lemma -/

set_option maxHeartbeats 4000000 in
/-- **The Key Lemma** (`arXiv:2404.09792` Theorem 4.1.1), in the `VHinge` language.  If the hinge
comparison holds at every point of the ball `B_l(p)` for hinges of size `< (2/3)l`, then there is no
violating hinge with one endpoint `p` and of size `< l`. -/
theorem key_lemma
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {l : ℝ} (hl0 : 0 < l) (hlπ : l ≤ Real.pi)
    {p : M} (hcomp : ∀ z : M, Manifold.riemannianEDist I p z < ENNReal.ofReal l →
      GCompHolds (cov := cov) hmet z ((2/3) * l))
    (q : M) : ¬ ∃ K : VHinge (cov := cov) hmet p q, K.tp + K.tq < l := by
  classical
  rintro ⟨K₀, hK₀⟩
  have hball : ∀ K : VHinge (cov := cov) hmet p q, K.tp + K.tq < l →
      Manifold.riemannianEDist I p K.x < ENNReal.ofReal l := by
    intro K hK
    rw [Manifold.riemannianEDist_comm, K.hminp]
    exact (ENNReal.ofReal_lt_ofReal_iff hl0).mpr (by linarith [K.htq, hK])
  let stepF : (K : VHinge (cov := cov) hmet p q) → (hK : K.tp + K.tq < l) →
      (h : l / 2 ≤ K.tp + K.tq) → StepOut (cov := cov) hmet p q l K :=
    fun K hK h => Classical.choice (VHinge.step (cov := cov) hmet htor hpinch hlπ hcomp K
      (hball K hK) hK h)
  let next : (K : VHinge (cov := cov) hmet p q) → (hK : K.tp + K.tq < l) →
      {K' : VHinge (cov := cov) hmet p q // K'.tp + K'.tq < l} :=
    fun K hK =>
      if h : l / 2 ≤ K.tp + K.tq then
        ⟨(stepF K hK h).K', lt_of_le_of_lt (stepF K hK h).hsize hK⟩
      else ⟨K, hK⟩
  let RS : ℕ → {K : VHinge (cov := cov) hmet p q // K.tp + K.tq < l} :=
    Nat.rec ⟨K₀, hK₀⟩ (fun _ ih => next ih.1 ih.2)
  let Ks : ℕ → VHinge (cov := cov) hmet p q := fun n => (RS n).1
  let r : ℕ → ℝ := fun n => (Ks n).tp + (Ks n).tq
  have hrlt : ∀ n, r n < l := fun n => (RS n).2
  -- the two endpoints are at finite distance
  have hdqq : Manifold.riemannianEDist I p q ≤ ENNReal.ofReal (r 0) := by
    show Manifold.riemannianEDist I p q ≤ ENNReal.ofReal ((Ks 0).tp + (Ks 0).tq)
    have h := Manifold.riemannianEDist_triangle (I := I) (x := p) (y := (Ks 0).x) (z := q)
    rw [Manifold.riemannianEDist_comm (I := I) (x := p) (y := (Ks 0).x),
      (Ks 0).hminp, (Ks 0).hminq] at h
    rwa [← ENNReal.ofReal_add (Ks 0).htp.le (Ks 0).htq.le] at h
  have hqfin : Manifold.riemannianEDist I p q ≠ ⊤ :=
    (lt_of_le_of_lt hdqq ENNReal.ofReal_lt_top).ne
  set D : ℝ := (Manifold.riemannianEDist I p q).toReal with hDdef
  have hdqD : Manifold.riemannianEDist I p q = ENNReal.ofReal D := by
    rw [hDdef]; exact (ENNReal.ofReal_toReal hqfin).symm
  have hDle : ∀ n, D ≤ r n := by
    intro n
    show D ≤ (Ks n).tp + (Ks n).tq
    have h := Manifold.riemannianEDist_triangle (I := I) (x := p) (y := (Ks n).x) (z := q)
    rw [Manifold.riemannianEDist_comm (I := I) (x := p) (y := (Ks n).x),
      (Ks n).hminp, (Ks n).hminq] at h
    rw [← ENNReal.ofReal_add (Ks n).htp.le (Ks n).htq.le] at h
    rw [hDdef]
    exact ENNReal.toReal_le_of_le_ofReal (add_nonneg (Ks n).htp.le (Ks n).htq.le) h
  have hlt0 : ENNReal.ofReal
        (modelDist1 (hingeAngle (Ks 0).vp (Ks 0).vq) (Ks 0).tp (Ks 0).tq)
      < ENNReal.ofReal D := by
    rw [← hdqD]; exact (Ks 0).hviol
  have hd0 : modelDist1 (hingeAngle (Ks 0).vp (Ks 0).vq) (Ks 0).tp (Ks 0).tq < D :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (modelDist1_nonneg _ _ _)).mp hlt0
  by_cases hC2 : ∀ n, l / 2 < r n
  · -- Case 2: the sizes never drop below `l/2`
    have hC2le : ∀ n, l / 2 ≤ r n := fun n => (hC2 n).le
    let S : (n : ℕ) → StepOut (cov := cov) hmet p q l (Ks n) :=
      fun n => stepF (Ks n) (RS n).2 (hC2le n)
    let dd : ℕ → ℝ := fun n =>
      modelDist1 (hingeAngle (Ks n).vp (Ks n).vq) (Ks n).tp (Ks n).tq
    have hsucc : ∀ n, Ks (n+1) = (S n).K' := by
      intro n
      show (RS (n+1)).1 = (stepF (Ks n) (RS n).2 (hC2le n)).K'
      rw [show RS (n+1) = next (RS n).1 (RS n).2 from rfl]
      simp only [next]
      rw [dif_pos (hC2le n)]
    have hrmono : ∀ n, r (n+1) ≤ r n := by
      intro n
      show (Ks (n+1)).tp + (Ks (n+1)).tq ≤ (Ks n).tp + (Ks n).tq
      rw [hsucc n]
      exact (S n).hsize
    have hcrit : ∀ n, min (Ks n).tp (Ks n).tq + 3 * (S n).s₁ = l / 2 := fun n => (S n).hcrit
    have hs1eq : ∀ n, (S n).s₁ = (l / 2 - min (Ks n).tp (Ks n).tq) / 3 := by
      intro n
      have h := hcrit n
      show (S n).s₁ = (l / 2 - min (Ks n).tp (Ks n).tq) / 3
      linarith [h]
    have hrel : ∀ n, (S n).w' = min (Ks n).tp (Ks n).tq + (S n).s₁ - (r n - r (n+1)) := by
      intro n
      have h := (S n).hrel
      show (S n).w' = min (Ks n).tp (Ks n).tq + (S n).s₁ - (r n - r (n+1))
      rw [show (S n).K'.tp + (S n).K'.tq = r (n+1) from by rw [← hsucc n]] at h
      exact h
    have hdmono : ∀ n, dd (n+1) ≤ dd n := by
      intro n
      show modelDist1 (hingeAngle (Ks (n+1)).vp (Ks (n+1)).vq) (Ks (n+1)).tp (Ks (n+1)).tq
        ≤ modelDist1 (hingeAngle (Ks n).vp (Ks n).vq) (Ks n).tp (Ks n).tq
      rw [hsucc n]
      exact (S n).hmono
    have hranti : Antitone r := antitone_nat_of_succ_le hrmono
    have hrbdd : BddBelow (Set.range r) :=
      ⟨l / 2, by rintro _ ⟨n, rfl⟩; exact hC2le n⟩
    set rlim : ℝ := ⨅ n, r n with hrlimdef
    have hrconv : Tendsto r atTop (𝓝 rlim) := tendsto_atTop_ciInf hranti hrbdd
    have hrlimle : ∀ n, rlim ≤ r n := fun n =>
      le_of_tendsto hrconv (eventually_atTop.mpr ⟨n, fun m hm => hranti hm⟩)
    have hrlimge : l / 2 ≤ rlim :=
      ge_of_tendsto hrconv (Filter.Eventually.of_forall hC2le)
    have hrlimπ : rlim ≤ Real.pi := le_trans (le_trans (hrlimle 0) (hrlt 0).le) hlπ
    have hdanti : Antitone dd := antitone_nat_of_succ_le hdmono
    have hdbdd : BddBelow (Set.range dd) :=
      ⟨0, by rintro _ ⟨n, rfl⟩; exact modelDist1_nonneg _ _ _⟩
    set dlim : ℝ := ⨅ n, dd n with hdlimdef
    have hdconv : Tendsto dd atTop (𝓝 dlim) := tendsto_atTop_ciInf hdanti hdbdd
    have hdlimle : ∀ n, dlim ≤ dd n := fun n =>
      le_of_tendsto hdconv (eventually_atTop.mpr ⟨n, fun m hm => hdanti hm⟩)
    have hlower : ∀ n, r n - 2 * min (Ks n).tp (Ks n).tq ≤ dd n := by
      intro n
      have ha : (Ks n).tp ∈ Set.Icc (0:ℝ) Real.pi :=
        ⟨(Ks n).htp.le, by linarith [hrlt n, (Ks n).htq]⟩
      have hb : (Ks n).tq ∈ Set.Icc (0:ℝ) Real.pi :=
        ⟨(Ks n).htq.le, by linarith [hrlt n, (Ks n).htp]⟩
      have h1 : |(Ks n).tp - (Ks n).tq| ≤ dd n :=
        modelDist1_ge_abs_sub ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩ ha hb
      have h4 : r n - 2 * min (Ks n).tp (Ks n).tq = max (Ks n).tp (Ks n).tq - min (Ks n).tp (Ks n).tq := by
        have h := max_add_min (Ks n).tp (Ks n).tq
        show (Ks n).tp + (Ks n).tq - 2 * min (Ks n).tp (Ks n).tq = _
        linarith [h]
      rw [h4, max_comm (Ks n).tp (Ks n).tq, min_comm (Ks n).tp (Ks n).tq,
        max_sub_min_eq_abs (Ks n).tq (Ks n).tp]
      exact h1
    have htt0le : ∀ n, (0:ℝ) ≤ min (Ks n).tp (Ks n).tq := fun n => le_min (Ks n).htp.le (Ks n).htq.le
    have httπ2 : ∀ n, min (Ks n).tp (Ks n).tq ≤ Real.pi / 2 := by
      intro n
      have h1 : min (Ks n).tp (Ks n).tq ≤ r n / 2 := by
        show min (Ks n).tp (Ks n).tq ≤ ((Ks n).tp + (Ks n).tq) / 2
        linarith [min_le_left (Ks n).tp (Ks n).tq, min_le_right (Ks n).tp (Ks n).tq]
      have h2 : r n / 2 ≤ l / 2 := by have h := (hrlt n).le; linarith
      have h3 : l / 2 ≤ Real.pi / 2 := by linarith
      linarith [h1, h2, h3]
    by_cases hA : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ min (Ks n).tp (Ks n).tq
    · -- Case A: the near side stays bounded below
      obtain ⟨c, hc0, hc⟩ := hA
      set c' : ℝ := min c 1 with hc'def
      have hc'0 : 0 < c' := lt_min hc0 one_pos
      have hc'le : ∀ᶠ n in atTop, c' ≤ min (Ks n).tp (Ks n).tq :=
        hc.mono (fun n hn => le_trans (min_le_left _ _) hn)
      have hc'π : c' ≤ Real.pi / 2 :=
        le_trans (min_le_right _ _) (by linarith [Real.pi_gt_three])
      set c₁ : ℝ := (l / 2 - r 0 / 2) / 3 with hc₁def
      have hc₁0 : 0 < c₁ := by rw [hc₁def]; have h := hrlt 0; linarith
      have hc₁π : c₁ ≤ Real.pi / 2 := by
        rw [hc₁def]
        have hr0 : 0 < r 0 := by have h := hC2 0; linarith
        have h0 : l / 2 - r 0 / 2 ≤ l / 2 := by linarith
        have h1 : l / 6 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three, hlπ]
        linarith [h0, h1]
      have hs1lo : ∀ n, c₁ ≤ (S n).s₁ := by
        intro n
        have hn : min (Ks n).tp (Ks n).tq ≤ r n / 2 := by
          show min (Ks n).tp (Ks n).tq ≤ ((Ks n).tp + (Ks n).tq) / 2
          linarith [min_le_left (Ks n).tp (Ks n).tq, min_le_right (Ks n).tp (Ks n).tq]
        have hn2 : r n / 2 ≤ r 0 / 2 := by have h := hranti (Nat.zero_le n); linarith
        rw [hs1eq n, hc₁def]
        linarith [hn, hn2]
      have hs1hi : ∀ n, (S n).s₁ ≤ Real.pi / 2 := by
        intro n
        rw [hs1eq n]
        have h1 : (l / 2 - min (Ks n).tp (Ks n).tq) / 3 ≤ l / 6 := by have h := htt0le n; linarith
        have h2 : l / 6 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three, hlπ]
        linarith [h1, h2]
      have hsin : ∀ᶠ n in atTop,
          Real.sin c' * Real.sin c₁ ≤ Real.sin (min (Ks n).tp (Ks n).tq) * Real.sin ((S n).s₁) := by
        filter_upwards [hc'le] with n hn
        have h1 : Real.sin c' ≤ Real.sin (min (Ks n).tp (Ks n).tq) :=
          Real.strictMonoOn_sin.monotoneOn
            ⟨by linarith [Real.pi_gt_three, hc'0], hc'π⟩
            ⟨by linarith [Real.pi_gt_three, htt0le n], httπ2 n⟩ hn
        have h2 : Real.sin c₁ ≤ Real.sin ((S n).s₁) :=
          Real.strictMonoOn_sin.monotoneOn
            ⟨by linarith [Real.pi_gt_three, hc₁0], hc₁π⟩
            ⟨by linarith [Real.pi_gt_three, (S n).hs₁], hs1hi n⟩ (hs1lo n)
        exact mul_le_mul h1 h2 (Real.sin_nonneg_of_nonneg_of_le_pi hc₁0.le (by linarith [hc₁π, Real.pi_gt_three]))
          (Real.sin_nonneg_of_nonneg_of_le_pi (htt0le n) (by linarith [httπ2 n, Real.pi_gt_three]))
      have hwlim : Tendsto (fun n => (S n).w' - (min (Ks n).tp (Ks n).tq + (S n).s₁)) atTop (𝓝 0) := by
        have h1 : ∀ n, (S n).w' - (min (Ks n).tp (Ks n).tq + (S n).s₁) = -(r n - r (n+1)) := by
          intro n; have h := hrel n; linarith
        simp only [h1]
        have h2 : Tendsto (fun n => r n - r (n+1)) atTop (𝓝 (rlim - rlim)) :=
          hrconv.sub (hrconv.comp (Filter.tendsto_add_atTop_nat 1))
        rw [sub_self] at h2
        simpa using h2.neg
      have hαπ : Tendsto (fun n => modelAngle ((S n).w') (min (Ks n).tp (Ks n).tq) ((S n).s₁)) atTop (𝓝 Real.pi) :=
        tendsto_modelAngle_pi
          (mul_pos (Real.sin_pos_of_pos_of_lt_pi hc'0 (by linarith [hc'π, Real.pi_gt_three]))
            (Real.sin_pos_of_pos_of_lt_pi hc₁0 (by linarith [hc₁π, Real.pi_gt_three])))
          hsin hwlim
      have hαle : ∀ n, modelAngle ((S n).w') (min (Ks n).tp (Ks n).tq) ((S n).s₁)
          ≤ hingeAngle (Ks n).vp (Ks n).vq := by
        intro n
        have hcmp' : (S n).w'
            ≤ modelDist1 (hingeAngle (Ks n).vp (Ks n).vq) (min (Ks n).tp (Ks n).tq) (S n).s₁ := (S n).hcmp
        have htπ : min (Ks n).tp (Ks n).tq < Real.pi := lt_of_le_of_lt (httπ2 n) (by linarith [Real.pi_gt_three])
        have hsπ : (S n).s₁ < Real.pi := lt_of_le_of_lt (hs1hi n) (by linarith [Real.pi_gt_three])
        have hhi : (S n).w' ≤ min (Ks n).tp (Ks n).tq + (S n).s₁ := by
          have h := hrel n; have h2 := hrmono n; linarith
        have hwπ : (S n).w' < Real.pi := by
          have h1 : min (Ks n).tp (Ks n).tq + (S n).s₁ ≤ Real.pi / 2 := by
            have h2 : min (Ks n).tp (Ks n).tq ≤ r n / 2 := by
              show min (Ks n).tp (Ks n).tq ≤ ((Ks n).tp + (Ks n).tq) / 2
              linarith [min_le_left (Ks n).tp (Ks n).tq, min_le_right (Ks n).tp (Ks n).tq]
            have h3 : min (Ks n).tp (Ks n).tq + (S n).s₁ = (l / 2 + 2 * min (Ks n).tp (Ks n).tq) / 3 := by rw [hs1eq n]; ring
            have h4 : r n / 2 ≤ l / 2 := by have h := (hrlt n).le; linarith
            rw [h3]
            linarith [h2, h4, hlπ]
          linarith [hhi, h1, Real.pi_pos]
        have hTS : min (Ks n).tp (Ks n).tq + (S n).s₁ ≤ Real.pi / 2 := by
          have h2 : min (Ks n).tp (Ks n).tq ≤ r n / 2 := by
            linarith [min_le_left (Ks n).tp (Ks n).tq, min_le_right (Ks n).tp (Ks n).tq]
          have h4 : r n / 2 ≤ l / 2 := by have h := (hrlt n).le; linarith
          rw [hs1eq n]
          linarith [h2, h4, hlπ]
        have hkey := modelDist1_modelAngle (S n).hw'.le hwπ.le
          (lt_min (Ks n).htp (Ks n).htq) htπ (S n).hs₁ hsπ (S n).hlo
          (by linarith [hTS, Real.pi_gt_three]) hhi
        rw [← hkey] at hcmp'
        exact (modelDist1_le_iff (lt_min (Ks n).htp (Ks n).htq) htπ (S n).hs₁ hsπ
          ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
          ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩).mp hcmp'
      have hθπ : Tendsto (fun n => hingeAngle (Ks n).vp (Ks n).vq) atTop (𝓝 Real.pi) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le hαπ tendsto_const_nhds
          (fun n => hαle n) (fun n => ?_)
        exact (show hingeAngle (Ks n).vp (Ks n).vq ∈ Set.Icc (0:ℝ) Real.pi from
          ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩).2
      have hdd : Tendsto dd atTop (𝓝 rlim) := by
        refine tendsto_modelDist1_pi hθπ (fun n => (Ks n).htp.le) (fun n => (Ks n).htq.le)
          ?_ hrconv ⟨by linarith [hrlimge, hl0], hrlimπ⟩
        intro n
        show (Ks n).tp + (Ks n).tq ≤ Real.pi
        linarith [(hrlt n).le, hlπ]
      have hdlimeq : dlim = rlim := tendsto_nhds_unique hdconv hdd
      have hDlelim : D ≤ rlim := ge_of_tendsto hrconv (Filter.Eventually.of_forall hDle)
      have hdd0 : dlim ≤ dd 0 := hdlimle 0
      rw [hdlimeq] at hdd0
      linarith [hdd0, hd0, hDlelim]
    · -- Case B: the near side is frequently small
      push_neg at hA
      have hfreq : ∀ k : ℕ, ∃ m : ℕ, k ≤ m ∧ min (Ks m).tp (Ks m).tq < 1 / (k + 1) := by
        intro k
        have hpos : (0:ℝ) < 1 / (k + 1) := by positivity
        have hf := hA (1 / (k + 1)) hpos
        rw [Filter.frequently_atTop] at hf
        obtain ⟨m, hm, hlt⟩ := hf k
        exact ⟨m, hm, hlt⟩
      let nk : ℕ → ℕ := fun k => Classical.choose (hfreq k)
      have hnk_ge : ∀ k, k ≤ nk k := fun k => (Classical.choose_spec (hfreq k)).1
      have hnk_tt : ∀ k, min (Ks (nk k)).tp (Ks (nk k)).tq < 1 / (k + 1) := fun k => (Classical.choose_spec (hfreq k)).2
      have hnk_top : Tendsto nk atTop atTop :=
        Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => le_trans ha (hnk_ge a)⟩
      have h3 : Tendsto (fun k => min (Ks (nk k)).tp (Ks (nk k)).tq) atTop (𝓝 0) := by
        refine squeeze_zero (fun k => htt0le (nk k)) (fun k => (hnk_tt k).le) ?_
        have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
          (Filter.tendsto_add_atTop_nat 1)
        simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
      have h1 : Tendsto (fun k => dd (nk k)) atTop (𝓝 dlim) := hdconv.comp hnk_top
      have h2 : Tendsto (fun k => r (nk k) - 2 * min (Ks (nk k)).tp (Ks (nk k)).tq) atTop (𝓝 rlim) := by
        have h := (hrconv.comp hnk_top).sub (h3.const_mul 2)
        simpa using h
      have h4 : ∀ k, r (nk k) - 2 * min (Ks (nk k)).tp (Ks (nk k)).tq ≤ dd (nk k) := fun k => hlower (nk k)
      have h5 : rlim ≤ dlim := le_of_tendsto_of_tendsto h2 h1 (Filter.Eventually.of_forall h4)
      have hDlelim : D ≤ rlim := ge_of_tendsto hrconv (Filter.Eventually.of_forall hDle)
      have hdd0 : dlim ≤ dd 0 := hdlimle 0
      linarith [h5, hDlelim, hdd0, hd0]
  · -- Case 1: some size is at most `l/2`
    push_neg at hC2
    obtain ⟨n, hn⟩ := hC2
    exact VHinge.false_of_size_lt (cov := cov) hmet hcomp (Ks n) (hball _ (hrlt n))
      (by linarith [hn])

/-! ## The payoff of the Key Lemma: the comparison radius can be multiplied by `3/2` -/

/-- **The Key Lemma, usable form.**  If the hinge comparison (in the `GExp` language) holds at
every point of `M` for all hinges of size `< r`, then it holds at every point for all hinges of
size `< (3/2) r`.  This is the bootstrap that, starting from a positive uniform comparison radius,
gives Toponogov's hinge comparison for hinges of size `< π`. -/
theorem gcompHolds_of_key
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {r : ℝ} (hr0 : 0 < r) (hrπ : (3/2) * r ≤ Real.pi)
    (hcomp : ∀ z : M, GCompHolds (cov := cov) hmet z r) :
    ∀ z : M, GCompHolds (cov := cov) hmet z ((3/2) * r) := by
  intro z a b v w ha hb hab hv hw hmina hminb
  set l : ℝ := (3/2) * r with hldef
  have hl0 : 0 < l := by rw [hldef]; linarith
  have hlπ : l ≤ Real.pi := by rw [hldef]; exact hrπ
  by_contra hviol
  have hviol' : ENNReal.ofReal (modelDist1 (hingeAngle v w) a b)
      < Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • v))
        (GExp (cov := cov) hmet z (b • w)) := not_le.mp hviol
  have hball : ∀ y : M, Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • v)) y
      < ENNReal.ofReal l → GCompHolds (cov := cov) hmet y ((2/3) * l) := by
    intro y _
    have h : (2/3) * l = r := by rw [hldef]; ring
    rw [h]; exact hcomp y
  refine key_lemma (cov := cov) hmet htor hpinch hl0 hlπ hball
    (GExp (cov := cov) hmet z (b • w)) ⟨?_, ?_⟩
  · exact ⟨z, a, b, v, w, hv, hw, ha, hb, rfl, rfl, hmina, hminb, hviol'⟩
  · show a + b < (3/2) * r
    exact hab

/-! ## The globalisation: from a uniform local radius to the full hinge comparison -/

/-- `GCompHolds` is monotone in the radius. -/
lemma GCompHolds_mono {hmet : IsMetricCompatible cov} {z : M} {r r' : ℝ} (h : r' ≤ r)
    (H : GCompHolds (cov := cov) hmet z r) : GCompHolds (cov := cov) hmet z r' :=
  fun a b v w ha hb hab hv hw hmina hminb =>
    H a b v w ha hb (lt_of_lt_of_le hab h) hv hw hmina hminb

set_option maxHeartbeats 1000000 in
/-- **The global hinge comparison.**  If the hinge comparison holds at every point of `M` for
hinges of size `< ρ` for one fixed `ρ > 0` (a *uniform* local comparison radius), then it holds at
every point for all hinges of size `< π`.

The proof is the classical bootstrap: the set `S` of radii `r` for which the comparison holds
uniformly is downward closed and stable under `r ↦ 3r/2` as long as `3r/2 ≤ π` (the Key Lemma).
Its supremum `r*` therefore satisfies `min (3r*/2) π ≤ r*`; since `r* > 0` this forces `3r*/2 > π`
and then `π ≤ r*`, so `r* = π`. -/
theorem gcompHolds_pi_of_uniform
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {ρ : ℝ} (hρ0 : 0 < ρ) (h : ∀ z : M, GCompHolds (cov := cov) hmet z ρ) :
    ∀ z : M, GCompHolds (cov := cov) hmet z Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have huni : ∀ {r r' : ℝ}, r' ≤ r → (∀ z, GCompHolds (cov := cov) hmet z r) →
      ∀ z, GCompHolds (cov := cov) hmet z r' :=
    fun hle H z => GCompHolds_mono hle (H z)
  set S : Set ℝ := {r | 0 < r ∧ r ≤ Real.pi ∧ ∀ z, GCompHolds (cov := cov) hmet z r} with hSdef
  have hminS : min ρ Real.pi ∈ S :=
    ⟨lt_min hρ0 hpi, min_le_right _ _, huni (min_le_left _ _) h⟩
  have hne : S.Nonempty := ⟨_, hminS⟩
  have hbdd : BddAbove S := ⟨Real.pi, fun r hr => hr.2.1⟩
  set rlim : ℝ := sSup S with hrlimdef
  have hSle : ∀ r ∈ S, r ≤ rlim := fun r hr => le_csSup hbdd hr
  have hrlim_pos : 0 < rlim := lt_of_lt_of_le (lt_min hρ0 hpi) (hSle _ hminS)
  have hrlim_pi : rlim ≤ Real.pi := csSup_le hne (fun r hr => hr.2.1)
  -- every `r < rlim` is in `S`
  have hmem : ∀ r, 0 < r → r < rlim → r ∈ S := by
    intro r hr0 hrlt
    obtain ⟨r', hr'S, hrr'⟩ := exists_lt_of_lt_csSup hne hrlt
    exact ⟨hr0, le_trans (le_of_lt hrr') hr'S.2.1, huni (le_of_lt hrr') hr'S.2.2⟩
  -- the bootstrap
  have hstep : ∀ r, 0 < r → r < rlim → (3:ℝ) / 2 * r ≤ Real.pi → (3:ℝ) / 2 * r ≤ rlim := by
    intro r hr0 hrlt h3
    have hrS := hmem r hr0 hrlt
    have hkey := gcompHolds_of_key (cov := cov) hmet htor hpinch hr0 h3 hrS.2.2
    exact hSle _ ⟨by linarith, h3, hkey⟩
  have hbig : Real.pi < (3:ℝ) / 2 * rlim := by
    by_contra hcon
    push Not at hcon
    have hr : (0:ℝ) < (3:ℝ) / 2 * rlim / 2 := by linarith
    have hlt : (3:ℝ) / 2 * rlim / 2 < rlim := by linarith
    have h3 : (3:ℝ) / 2 * ((3:ℝ) / 2 * rlim / 2) ≤ Real.pi := by linarith
    have := hstep ((3:ℝ) / 2 * rlim / 2) hr hlt h3
    linarith
  have hge : Real.pi ≤ rlim := by
    have h2 : 2 * Real.pi / 3 < rlim := by linarith [hbig]
    have h3 : (3:ℝ) / 2 * (2 * Real.pi / 3) ≤ Real.pi := by linarith [Real.pi_pos]
    have := hstep (2 * Real.pi / 3) (by linarith [Real.pi_pos]) h2 h3
    linarith
  have hrlim_eq : rlim = Real.pi := le_antisymm hrlim_pi hge
  intro z a b v w ha hb hab hv hw hmina hminb
  have hr : (a + b + rlim) / 2 < rlim := by rw [hrlim_eq]; linarith
  have hr0 : (0:ℝ) < (a + b + rlim) / 2 := by linarith [ha, hb, hrlim_pos]
  have hrS := hmem _ hr0 hr
  exact hrS.2.2 z a b v w ha hb (by linarith [hab, hrlim_eq]) hv hw hmina hminb

end

end Submission.HingeKey2
