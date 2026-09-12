import Submission.Model
import Submission.ModelCore
import Submission.ModelFlowCont
import Submission.ModelJacobi
import Submission.ModelJacLin
import Submission.ModelVarConv
import Mathlib

/-!
# The geodesic flow is differentiable in the initial data (Fréchet)

Task: prove the final theorem `variation_frechet`.

The proof:

1. `flowOnUnitBall` gives a local flow `Φ` on `closedBall z₀ 1` on a time window `Icc (-Tf) Tf`,
   Lipschitz in the initial data uniformly in time.

2. Along the base trajectory `cur := Φ z₀` we build, once and for all, the *canonical* family
   `J w` of solutions of the linearized (Jacobi) equation `J' = (fderiv V (cur ·)) J`, `J 0 = w`,
   on a common time window `Ioo (-Tj) Tj` for **all** `w`.  This is done by solving for each
   vector of a finite basis `b` (they all exist by `linearized_of_pair`, each on its own window;
   intersecting the finitely many windows gives a common one) and extending by linearity:
   `J w u := (b.constr ℝ (fun i => J_i u)) w`.  This is linear in `w` by construction, and it
   solves the linearized equation because it is a linear combination of solutions.

3. A *uniform* (in the direction, over the unit ball) Gateaux estimate is proven directly by the
   same Gronwall/Taylor argument as `ModelVarConv.variation_estimate`, but with all constants
   chosen uniformly for `‖w‖ ≤ 1` and with the canonical family `J` in place of a fresh solution:
       ∀ η > 0, ∃ h₀ > 0, ∀ w, ‖w‖ ≤ 1 → ∀ h ≠ 0, |h| < h₀ →
         z₀ + h • w ∈ closedBall z₀ 1 →
         ∀ t ∈ Icc (-T) T, ‖(1/h) • (Φ (z₀ + h•w) t - Φ z₀ t) - J w t‖ ≤ η.

4. Fix `t`.  The linear map `L t : w ↦ J w t` is linear (step 2) and continuous (finite
   dimension).  The uniform estimate is exactly the little-o condition for
   `HasFDerivAt (fun z => Φ z t) (L t) z₀`: given `v ≠ 0`, take `w := v/‖v‖`, `h := ‖v‖`;
   `J (h • w) t = h • J w t` (linearity) identifies the difference quotient with the derivative
   application.
-/

open ContinuousLinearMap
open scoped ContDiff Topology BigOperators
open Set Metric Module

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- a positive lower bound that is at most `a` and below every member of a finite family of
positive numbers -/
lemma exists_lt_all (ι : Type*) [Fintype ι] (T : ι → ℝ) (hT : ∀ i, 0 < T i) (a : ℝ)
    (ha : 0 < a) : ∃ c : ℝ, 0 < c ∧ c ≤ a ∧ ∀ i : ι, c ≤ T i := by
  classical
  by_cases hι : Nonempty ι
  · rcases hι with ⟨i₀⟩
    let S := (Finset.univ.image T : Finset ℝ)
    have hS : S.Nonempty := by
      refine ⟨T i₀, ?_⟩
      exact Finset.mem_image.mpr ⟨i₀, Finset.mem_univ i₀, rfl⟩
    let c0 := S.min' hS
    have hc0pos : 0 < c0 := by
      have hmem : c0 ∈ S := S.min'_mem hS
      rcases Finset.mem_image.mp hmem with ⟨i, hi, hTmem⟩
      rw [← hTmem]
      exact hT i
    let c := min c0 a
    refine ⟨c, ?_, ?_, ?_⟩
    · exact lt_min hc0pos ha
    · exact min_le_right _ _
    · intro i
      exact le_trans (min_le_left _ _)
        (S.min'_le (T i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  · refine ⟨a, ha, le_rfl, ?_⟩
    intro i
    exact False.elim (hι ⟨i⟩)

/-- Solutions of the linearized (Jacobi) equation along the base trajectory, for *all* initial
data `w`, on one common time window, linear in `w`. -/
lemma canonical_solutions (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) (Tf : ℝ) (hTf : 0 < Tf)
    (Φ : E × E → ℝ → E × E)
    (hΦ₀ : ∀ z ∈ closedBall z₀ 1, Φ z 0 = z ∧
       ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) :
    ∃ Tj : ℝ, 0 < Tj ∧ Tj < Tf ∧ ∃ J : (E × E) → ℝ → (E × E),
      (∀ w : E × E, J w 0 = w) ∧
      (∀ w : E × E, ∀ t ∈ Ioo (-Tj) Tj,
        HasDerivAt (J w) ((fderiv ℝ (odeField g)) (Φ z₀ t) (J w t)) t) ∧
      (∀ t : ℝ, ∀ (a b : E × E), J (a + b) t = J a t + J b t) ∧
      (∀ t : ℝ, ∀ (a : E × E) (c : ℝ), J (c • a) t = c • J a t) := by
  classical
  let ι := Fin (finrank ℝ (E × E))
  let b : Basis ι ℝ (E × E) := finBasis ℝ (E × E)
  let cur : ℝ → E × E := fun t => Φ z₀ t
  have hz₀mem : z₀ ∈ closedBall z₀ 1 := by simp
  have hcur (t : ℝ) (ht : t ∈ Icc (-Tf) Tf) : HasDerivAt cur (odeField g (cur t)) t := by
    simpa [cur] using (hΦ₀ z₀ hz₀mem).2 t ht
  have hcurIoo (t : ℝ) (ht : t ∈ Ioo (-Tf) Tf) : HasDerivAt cur (odeField g (cur t)) t :=
    hcur t (Ioo_subset_Icc_self ht)
  have hper (i : ι) : ∃ T : ℝ, ∃ J : ℝ → E × E,
      0 < T ∧ T < Tf ∧ J 0 = b i ∧
        (∀ t ∈ Ioo (-T) T,
          HasDerivAt J ((fderiv ℝ (odeField g)) (cur t) (J t)) t) := by
    rcases linearized_of_pair g hg hinv (hε := hTf) (z := cur) (w := b i) hcurIoo with
      ⟨T, hT0, hTlt, J, hJ0, hJ⟩
    refine ⟨T, J, hT0, hTlt, hJ0, ?_⟩
    intro t ht
    simpa [cur] using hJ t ht
  let sol (i : ι) : {T : ℝ × (ℝ → E × E) // 0 < T.1 ∧ T.1 < Tf ∧ T.2 0 = b i ∧
        (∀ t ∈ Ioo (-T.1) T.1,
          HasDerivAt (T.2) ((fderiv ℝ (odeField g)) (cur t) (T.2 t)) t)} := by
    let T0 : ℝ := Classical.choose (hper i)
    have hspec : ∃ J : ℝ → E × E, 0 < T0 ∧ T0 < Tf ∧ J 0 = b i ∧
        (∀ t ∈ Ioo (-T0) T0, HasDerivAt J ((fderiv ℝ (odeField g)) (cur t) (J t)) t) :=
      Classical.choose_spec (hper i)
    let J0 : ℝ → E × E := Classical.choose hspec
    have hJ0spec : 0 < T0 ∧ T0 < Tf ∧ J0 0 = b i ∧
        (∀ t ∈ Ioo (-T0) T0, HasDerivAt J0 ((fderiv ℝ (odeField g)) (cur t) (J0 t)) t) :=
      Classical.choose_spec hspec
    exact ⟨(T0, J0), hJ0spec.1, hJ0spec.2.1, hJ0spec.2.2.1, hJ0spec.2.2.2⟩
  let solT : ι → ℝ := fun i => (sol i).1.1
  let solJ : ι → ℝ → E × E := fun i => (sol i).1.2
  have hsolT0 (i : ι) : 0 < solT i := by
    simpa [solT] using (sol i).2.1
  have hsolJ0 (i : ι) : solJ i 0 = b i := by
    simpa [solJ] using (sol i).2.2.2.1
  have hsolJd (i : ι) (t : ℝ) (ht : t ∈ Ioo (-(solT i)) (solT i)) :
      HasDerivAt (solJ i) ((fderiv ℝ (odeField g)) (cur t) (solJ i t)) t := by
    simpa [solJ] using (sol i).2.2.2.2 t ht
  rcases exists_lt_all ι solT hsolT0 (Tf / 2) (by positivity) with ⟨c, hc0, hcTf2, hcT⟩
  let Tj : ℝ := c / 2
  have hTj0 : 0 < Tj := by dsimp [Tj]; positivity
  have hTjTf : Tj < Tf := by
    dsimp [Tj]
    linarith
  have hTjTi (i : ι) : Tj ≤ solT i := by
    dsimp [Tj]
    exact le_trans (by linarith) (hcT i)
  have hsum_repr (f : ι → E × E) (w : E × E) :
      (b.constr ℝ f) w = ∑ i : ι, (b.repr w i) • f i := by
    simp
  let J : (E × E) → ℝ → (E × E) := fun w y => (b.constr ℝ (fun i => solJ i y)) w
  refine ⟨Tj, hTj0, hTjTf, J, ?_, ?_, ?_, ?_⟩
  · intro w
    dsimp [J]
    have hfam : (fun i : ι => solJ i 0) = (fun i : ι => b i) := by
      funext i
      exact hsolJ0 i
    rw [hfam]
    rw [Basis.constr_apply]
    rw [Finsupp.sum_fintype (b.repr w) (fun i a => a • b i) (by intro i; simp)]
    exact b.sum_repr w
  · intro w t ht
    have hder_i (i : ι) : HasDerivAt (fun y : ℝ => (b.repr w i) • solJ i y)
        ((b.repr w i) • ((fderiv ℝ (odeField g)) (cur t) (solJ i t))) t := by
      have hmem : t ∈ Ioo (-(solT i)) (solT i) := by
        constructor
        · exact lt_of_le_of_lt (neg_le_neg (hTjTi i)) ht.1
        · exact lt_of_lt_of_le ht.2 (hTjTi i)
      exact (hsolJd i t hmem).const_smul (b.repr w i)
    have hsum := HasDerivAt.sum (u := (Finset.univ : Finset ι)) (fun i hi => hder_i i)
    have heq : (fun y : ℝ => ∑ i : ι, (b.repr w i) • solJ i y) =ᶠ[𝓝 t]
        (∑ i : ι, fun y => (b.repr w i) • solJ i y) := by
      filter_upwards with y
      simp
    have hmain : HasDerivAt (fun y : ℝ => ∑ i : ι, (b.repr w i) • solJ i y)
        (∑ i : ι, (b.repr w i) • ((fderiv ℝ (odeField g)) (cur t) (solJ i t))) t :=
      hsum.congr_of_eventuallyEq heq
    have hcurve : (fun y : ℝ => (b.constr ℝ (fun i => solJ i y)) w) =ᶠ[𝓝 t]
        (fun y : ℝ => ∑ i : ι, (b.repr w i) • solJ i y) := by
      filter_upwards with y
      rw [hsum_repr]
    have hmain' : HasDerivAt (fun y : ℝ => (b.constr ℝ (fun i => solJ i y)) w)
        (∑ i : ι, (b.repr w i) • ((fderiv ℝ (odeField g)) (cur t) (solJ i t))) t :=
      hmain.congr_of_eventuallyEq hcurve
    have hderA : (fderiv ℝ (odeField g)) (cur t) (∑ i : ι, (b.repr w i) • solJ i t) =
        (∑ i : ι, (b.repr w i) • ((fderiv ℝ (odeField g)) (cur t) (solJ i t))) := by
      calc
        (fderiv ℝ (odeField g)) (cur t) (∑ i : ι, (b.repr w i) • solJ i t)
            = ∑ i : ι, (fderiv ℝ (odeField g)) (cur t) ((b.repr w i) • solJ i t) := by
              simp [map_sum]
        _ = ∑ i : ι, (b.repr w i) • ((fderiv ℝ (odeField g)) (cur t) (solJ i t)) := by
              simp [map_smul]
    have hder : (∑ i : ι, (b.repr w i) • ((fderiv ℝ (odeField g)) (cur t) (solJ i t))) =
        (fderiv ℝ (odeField g)) (cur t) (J w t) := by
      dsimp [J]
      rw [hsum_repr]
      exact hderA.symm
    exact hmain'.congr_deriv hder
  · intro t u v
    dsimp [J]
    exact (b.constr ℝ (fun i => solJ i t)).map_add u v
  · intro t u c
    dsimp [J]
    exact (b.constr ℝ (fun i => solJ i t)).map_smul c u

/-- Uniform-in-direction Gateaux estimate of the flow against the canonical family `J`. -/
lemma uniform_lin_est (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) (Tf : ℝ) (hTf : 0 < Tf)
    (Lf : NNReal) (Φ : (E × E) → ℝ → (E × E))
    (hΦ₀ : ∀ z ∈ closedBall z₀ 1, Φ z 0 = z ∧
       ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    (hLip : ∀ t ∈ Icc (-Tf) Tf, LipschitzOnWith Lf (fun z => Φ z t) (closedBall z₀ 1))
    (Tj : ℝ) (hTj : 0 < Tj) (hTjTf : Tj < Tf)
    (J : (E × E) → ℝ → (E × E))
    (hJ0 : ∀ w : E × E, J w 0 = w)
    (hJd : ∀ w : E × E, ∀ t ∈ Ioo (-Tj) Tj,
        HasDerivAt (J w) ((fderiv ℝ (odeField g)) (Φ z₀ t) (J w t)) t) :
    ∃ T > 0, T < Tf ∧ (∀ η > 0, ∃ h₀ > 0, ∀ w : E × E, ‖w‖ ≤ 1 →
      ∀ h : ℝ, h ≠ 0 → |h| < h₀ → z₀ + h • w ∈ closedBall z₀ 1 →
      ∀ t ∈ Icc (-T) T,
        ‖(1 / h) • (Φ (z₀ + h • w) t - Φ z₀ t) - J w t‖ ≤ η) := by
  let F := E × E
  let V : F → F := odeField g
  let cur : ℝ → F := fun t => Φ z₀ t
  have hz₀mem : z₀ ∈ closedBall z₀ 1 := by simp
  have hcur (t : ℝ) (ht : t ∈ Icc (-Tf) Tf) : HasDerivAt cur (V (cur t)) t := by
    simpa [cur, V] using (hΦ₀ z₀ hz₀mem).2 t ht
  let T : ℝ := Tj / 2
  have hT0 : 0 < T := by dsimp [T]; linarith
  have hTltTj : T < Tj := by dsimp [T]; linarith
  have hTltTf : T < Tf := by dsimp [T]; linarith
  have hTfIcc : Icc (-T) T ⊆ Icc (-Tf) Tf := by
    intro t ht
    constructor
    · exact le_trans (neg_le_neg (le_of_lt hTltTf)) ht.1
    · exact le_trans ht.2 (le_of_lt hTltTf)
  have hTjIoo : Icc (-T) T ⊆ Ioo (-Tj) Tj := by
    intro t ht
    constructor
    · exact lt_of_lt_of_le (neg_lt_neg hTltTj) ht.1
    · exact lt_of_le_of_lt ht.2 hTltTj
  have hcurCont : ContinuousOn cur (Icc (-T) T) := by
    intro t ht
    exact (hcur t (hTfIcc ht)).continuousAt.continuousWithinAt
  have hfdcont : Continuous (fderiv ℝ V) := by
    have hV1 : ContDiff ℝ 1 V := by
      rw [contDiff_iff_contDiffAt]
      intro p
      rcases p with ⟨x, v⟩
      simpa [V] using odeField_contDiffAt g hg hinv x v
    exact hV1.continuous_fderiv (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hnormCont : ContinuousOn (fun t => ‖fderiv ℝ V (cur t)‖) (Icc (-T) T) :=
    hfdcont.norm.comp_continuousOn hcurCont
  have hIccN : (Icc (-T) T).Nonempty := ⟨0, by constructor <;> linarith⟩
  rcases (isCompact_Icc : IsCompact (Icc (-T) T)).exists_isMaxOn hIccN hnormCont with
    ⟨tm, htm, hmaxT⟩
  let K : ℝ := ‖fderiv ℝ V (cur tm)‖
  have hK0 : 0 ≤ K := norm_nonneg _
  have hKb (t : ℝ) (ht : t ∈ Icc (-T) T) : ‖fderiv ℝ V (cur t)‖ ≤ K := by
    simpa [K] using hmaxT ht
  have hTay (ε : ℝ) (hε : 0 < ε) : ∃ δ > 0, ∀ t ∈ Icc (-T) T, ∀ y : F,
      y ∈ closedBall (cur t) δ →
      ‖V y - V (cur t) - (fderiv ℝ V (cur t)) (y - cur t)‖ ≤ ε * ‖y - cur t‖ := by
    have hc0cont : ContinuousOn (fun t : ℝ => (cur t).1) (Icc (-T) T) :=
      (continuous_fst.comp_continuousOn hcurCont)
    have hv0cont : ContinuousOn (fun t : ℝ => (cur t).2) (Icc (-T) T) :=
      (continuous_snd.comp_continuousOn hcurCont)
    rcases odeField_taylor_error g hg hinv hT0 hc0cont hv0cont ε hε with ⟨δ, hδ, hh⟩
    refine ⟨δ, hδ, ?_⟩
    intro t ht y hy
    simpa [V] using hh t ht y hy
  refine ⟨T, hT0, hTltTf, ?_⟩
  intro η hη
  have hgronCont : Continuous (fun ε : ℝ => gronwallBound 0 K ε T) := gronwallBound_continuous_ε 0 K T
  rcases Metric.continuousAt_iff.mp hgronCont.continuousAt η hη with ⟨c₀, hc₀, hc₀bd⟩
  let s : ℝ := (Lf : ℝ)
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  let εt : ℝ := c₀ / (2 * (s + 1))
  have hεt0 : 0 < εt := by dsimp [εt]; positivity
  let c : ℝ := εt * s
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hcclt : c < c₀ := by
    dsimp [c, εt]
    have hpos : 0 < 2 * (s + 1) := by positivity
    calc
      c₀ / (2 * (s + 1)) * s ≤ c₀ / (2 * (s + 1)) * (s + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt (by positivity))
      _ = c₀ / 2 := by field_simp [hpos.ne']
      _ < c₀ := by linarith
  have hc₀ltη : gronwallBound 0 K c T < η := by
    have hdist : dist c 0 < c₀ := by
      simpa [Real.dist_eq, sub_zero, abs_of_nonneg hc0]
    have hb := hc₀bd hdist
    rw [gronwallBound_ε0_δ0] at hb
    have hb' : |gronwallBound 0 K c T| < η := by simpa [Real.dist_eq] using hb
    exact (abs_lt.mp hb').2
  rcases hTay εt hεt0 with ⟨δt, hδt0, hTayδ⟩
  let h₀ : ℝ := δt / (s + 1)
  have hh₀ : 0 < h₀ := by
    dsimp [h₀]
    positivity
  refine ⟨h₀, hh₀, ?_⟩
  intro w hw h hhne hhlt hzmem
  let zh : ℝ → F := fun u => Φ (z₀ + h • w) u
  let q : ℝ → F := fun u => (1 / h) • (zh u - cur u)
  let D : ℝ → F := fun u => q u - J w u
  have hnorm_smul_div (v : F) : ‖(1 / h) • v‖ = ‖v‖ / |h| := by
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_div, abs_one]
    field_simp [abs_ne_zero.mpr hhne]
  have hLips (x : ℝ) (hx : x ∈ Icc (-T) T) : ‖zh x - cur x‖ ≤ s * |h| := by
    have hxTf : x ∈ Icc (-Tf) Tf := hTfIcc hx
    have hLipx : LipschitzOnWith Lf (fun z => Φ z x) (closedBall z₀ 1) := hLip x hxTf
    calc
      ‖zh x - cur x‖ = dist (Φ (z₀ + h • w) x) (Φ z₀ x) := by
        simp [zh, cur, dist_eq_norm]
      _ ≤ (Lf : ℝ) * dist (z₀ + h • w) z₀ :=
        hLipx.dist_le_mul (z₀ + h • w) hzmem z₀ hz₀mem
      _ = (Lf : ℝ) * ‖h • w‖ := by rw [dist_eq_norm]; simp
      _ ≤ (Lf : ℝ) * |h| := by
        rw [norm_smul, Real.norm_eq_abs]
        have hmul : |h| * ‖w‖ ≤ |h| := by
          simpa using mul_le_mul_of_nonneg_left hw (abs_nonneg h)
        exact mul_le_mul_of_nonneg_left hmul (Lf : NNReal).2
      _ = s * |h| := by simp [s]
  have hsδ (x : ℝ) (hx : x ∈ Icc (-T) T) : ‖zh x - cur x‖ ≤ δt := by
    have hb1 : s * |h| ≤ s * h₀ := by
      exact mul_le_mul_of_nonneg_left (le_of_lt hhlt) hs0
    have hb2 : s * h₀ ≤ δt := by
      dsimp [h₀]
      have hpos : 0 < s + 1 := by positivity
      calc
        s * (δt / (s + 1)) = (s * δt) / (s + 1) := by ring
        _ ≤ δt := by
          rw [div_le_iff₀ hpos]
          nlinarith [hδt0.le]
    exact le_trans (hLips x hx) (le_trans hb1 hb2)
  have hper (x : ℝ) (hx : x ∈ Icc (-T) T) :
      ∃ gx : F, HasDerivAt D gx x ∧ ‖gx‖ ≤ K * ‖D x‖ + c := by
    let A : F →L[ℝ] F := fderiv ℝ V (cur x)
    let R : F := V (zh x) - V (cur x) - A (zh x - cur x)
    have hxTf : x ∈ Icc (-Tf) Tf := hTfIcc hx
    have hderzh : HasDerivAt zh (V (zh x)) x := by
      simpa [zh, V] using (hΦ₀ (z₀ + h • w) hzmem).2 x hxTf
    have hdercur : HasDerivAt cur (V (cur x)) x := hcur x hxTf
    have hdq0' : HasDerivAt (fun u : ℝ => (1 / h) • (zh u - cur u))
        ((1 / h) • (V (zh x) - V (cur x))) x :=
      (hderzh.sub hdercur).const_smul (1 / h)
    have hdq0 : HasDerivAt q ((1 / h) • (V (zh x) - V (cur x))) x := by
      simpa [q] using hdq0'
    have hdq : HasDerivAt q (A (q x) + (1 / h) • R) x := by
      apply hdq0.congr_deriv
      have hR : V (zh x) - V (cur x) = A (zh x - cur x) + R := by
        dsimp [R]
        abel
      calc
        (1 / h) • (V (zh x) - V (cur x)) = (1 / h) • (A (zh x - cur x) + R) := by rw [hR]
        _ = (1 / h) • A (zh x - cur x) + (1 / h) • R := by rw [smul_add]
        _ = A ((1 / h) • (zh x - cur x)) + (1 / h) • R := by rw [map_smul]
        _ = A (q x) + (1 / h) • R := rfl
    have hJx : HasDerivAt (J w) ((fderiv ℝ V) (cur x) (J w x)) x := by
      have hJt := hJd w x (hTjIoo hx)
      simpa [V, cur] using hJt
    have hDx : HasDerivAt (fun u : ℝ => q u - J w u)
        ((A (q x) + (1 / h) • R) - A (J w x)) x := (hdq.sub hJx)
    refine ⟨(A (q x) + (1 / h) • R) - A (J w x), ?_, ?_⟩
    · simpa [D] using hDx
    · have hAK : ‖A‖ ≤ K := by
        simpa [A] using hKb x hx
      have hb1 : ‖A (q x) - A (J w x)‖ ≤ K * ‖D x‖ := by
        calc
          ‖A (q x) - A (J w x)‖ = ‖A (q x - J w x)‖ := by rw [map_sub]
          _ ≤ ‖A‖ * ‖q x - J w x‖ := A.le_opNorm (q x - J w x)
          _ ≤ K * ‖q x - J w x‖ := mul_le_mul_of_nonneg_right hAK (norm_nonneg _)
          _ = K * ‖D x‖ := rfl
      have hb2 : ‖(1 / h) • R‖ ≤ c := by
        calc
          ‖(1 / h) • R‖ = ‖R‖ / |h| := hnorm_smul_div R
          _ ≤ (εt * ‖zh x - cur x‖) / |h| := by
            apply div_le_div_of_nonneg_right ?_ (abs_pos.mpr hhne).le
            have hT := hTayδ x hx (zh x) (by
              rw [mem_closedBall, dist_eq_norm]
              exact hsδ x hx)
            simpa [R, A] using hT
          _ ≤ (εt * (s * |h|)) / |h| := by
            apply div_le_div_of_nonneg_right ?_ (abs_pos.mpr hhne).le
            exact mul_le_mul_of_nonneg_left (hLips x hx) (le_of_lt hεt0)
          _ = εt * s := by
            field_simp [abs_ne_zero.mpr hhne]
          _ = c := rfl
      have hdec : (A (q x) + (1 / h) • R) - A (J w x) =
          (A (q x) - A (J w x)) + (1 / h) • R := by abel
      rw [hdec]
      exact le_trans (norm_add_le (A (q x) - A (J w x)) ((1 / h) • R)) (by nlinarith)
  let fp : ℝ → F := fun x => if hx : x ∈ Icc (-T) T then (hper x hx).choose else 0
  have hfp (x : ℝ) (hx : x ∈ Ico 0 T) : HasDerivAt D (fp x) x ∧ ‖fp x‖ ≤ K * ‖D x‖ + c := by
    have hxI : x ∈ Icc (-T) T := ⟨by linarith [hx.1, hT0], le_of_lt hx.2⟩
    rw [show fp x = (hper x hxI).choose by
      unfold fp
      rw [dif_pos hxI]]
    exact (hper x hxI).choose_spec
  have hDcont : ContinuousOn D (Icc 0 T) := by
    intro x hx
    have hxI : x ∈ Icc (-T) T := ⟨by linarith [hx.1, hT0], hx.2⟩
    exact (hper x hxI).choose_spec.1.continuousAt.continuousWithinAt
  have hD0 : D 0 = 0 := by
    dsimp [D, q, zh, cur]
    rw [(hΦ₀ (z₀ + h • w) hzmem).1, (hΦ₀ z₀ hz₀mem).1]
    have hsw : (1 / h) • (h • w) = w := by
      rw [smul_smul]
      have hmul : (1 / h) * h = 1 := by field_simp [hhne]
      rw [hmul, one_smul]
    have hstep : (1 / h) • (z₀ + h • w - z₀) = w := by
      have hz : z₀ + h • w - z₀ = h • w := by abel
      rw [hz]
      exact hsw
    rw [hstep, hJ0 w]
    simp
  have hpos (u : ℝ) (hu : u ∈ Icc 0 T) : ‖D u‖ ≤ gronwallBound 0 K c u := by
    have hderw : ∀ x ∈ Ico 0 T, HasDerivWithinAt D (fp x) (Ici x) x := by
      intro x hx
      exact (hfp x hx).1.hasDerivWithinAt
    have hbndw : ∀ x ∈ Ico 0 T, ‖fp x‖ ≤ K * ‖D x‖ + c := by
      intro x hx
      exact (hfp x hx).2
    have hres := norm_le_gronwallBound_of_norm_deriv_right_le (f := D) (f' := fp)
      (δ := 0) (K := K) (ε := c) (a := 0) (b := T)
      hDcont hderw (by rw [hD0]; simp) hbndw
    simpa using hres u hu
  have hEpIcc (s : ℝ) (hs : s ∈ Icc 0 T) :
      ∃ gx : F, HasDerivAt (fun r => D (-r)) gx s ∧ ‖gx‖ ≤ K * ‖(fun r => D (-r)) s‖ + c := by
    have hxI : -s ∈ Icc (-T) T := ⟨by linarith [hs.2], by linarith [hs.1, hT0]⟩
    rcases hper (-s) hxI with ⟨gx, hder, hbnd⟩
    refine ⟨-(gx), ?_, ?_⟩
    · have hnegd : HasDerivAt (fun r : ℝ => -r) (-1 : ℝ) s := hasDerivAt_neg s
      change HasDerivAt (D ∘ Neg.neg) (-(gx)) s
      simpa using hder.scomp s hnegd
    · simpa [norm_neg] using hbnd
  let gp : ℝ → F := fun s => if hs : s ∈ Icc 0 T then (hEpIcc s hs).choose else 0
  have hgp (s : ℝ) (hs : s ∈ Ico 0 T) :
      HasDerivAt (fun r => D (-r)) (gp s) s ∧ ‖gp s‖ ≤ K * ‖(fun r => D (-r)) s‖ + c := by
    have hsI : s ∈ Icc 0 T := ⟨hs.1, le_of_lt hs.2⟩
    rw [show gp s = (hEpIcc s hsI).choose by
      unfold gp
      rw [dif_pos hsI]]
    exact (hEpIcc s hsI).choose_spec
  have hEcont : ContinuousOn (fun r => D (-r)) (Icc 0 T) := by
    intro s hs
    exact (hEpIcc s hs).choose_spec.1.continuousAt.continuousWithinAt
  have hneg (u : ℝ) (hu : u ∈ Icc (-T) 0) : ‖D u‖ ≤ gronwallBound 0 K c (-u) := by
    have hb1 : ∀ s ∈ Ico 0 T, HasDerivWithinAt (fun r => D (-r)) (gp s) (Ici s) s := by
      intro s hs
      exact (hgp s hs).1.hasDerivWithinAt
    have hb2 : ∀ s ∈ Ico 0 T, ‖gp s‖ ≤ K * ‖(fun r => D (-r)) s‖ + c := by
      intro s hs
      exact (hgp s hs).2
    have hres := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := (fun r => D (-r))) (f' := gp) (δ := 0) (K := K) (ε := c) (a := 0) (b := T)
      hEcont hb1 (by simp [hD0]) hb2
    have huI : -u ∈ Icc 0 T := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have hb := hres (-u) huI
    simpa using hb
  have hDfin (u : ℝ) (hu : u ∈ Icc (-T) T) : ‖D u‖ ≤ η := by
    have hm : Monotone (gronwallBound 0 K c) := gronwallBound_mono (by norm_num) hc0 hK0
    by_cases hu0 : 0 ≤ u
    · have hb := hpos u ⟨hu0, hu.2⟩
      exact le_trans (le_trans hb (hm hu.2)) (le_of_lt hc₀ltη)
    · have hb := hneg u ⟨hu.1, le_of_not_ge hu0⟩
      have hmt : -u ≤ T := by linarith [hu.1]
      exact le_trans (le_trans hb (hm hmt)) (le_of_lt hc₀ltη)
  intro t ht
  simpa [D, q, zh] using hDfin t ht


/-- If `‖r⁻¹ • X - Y‖ ≤ c` then `‖X - r • Y‖ ≤ r * c` (un-scale the estimate). -/
lemma norm_unscale_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {X Y : F} {r c : ℝ} (hr : 0 < r)
    (hb : ‖(r⁻¹) • X - Y‖ ≤ c) : ‖X - r • Y‖ ≤ r * c := by
  have hh : r • ((r⁻¹) • X - Y) = X - r • Y := by
    rw [smul_sub, smul_smul]
    field_simp [ne_of_gt hr]
    simp
  calc
    ‖X - r • Y‖ = ‖r • ((r⁻¹) • X - Y)‖ := by rw [hh]
    _ = r * ‖(r⁻¹) • X - Y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hr)]
    _ ≤ r * c := mul_le_mul_of_nonneg_left hb (le_of_lt hr)

/-- The geodesic flow is Fréchet-differentiable in the initial data at every time. -/
theorem variation_frechet (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ v₀ : E) :
    ∃ T > 0, ∃ Φ : E × E → ℝ → E × E,
      (∀ z ∈ closedBall (x₀, v₀) 1, Φ z 0 = z ∧
         ∀ t ∈ Icc (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
      (∀ t ∈ Icc (-T) T,
         ∃ L : E × E →L[ℝ] E × E,
           HasFDerivAt (fun z => Φ z t) L (x₀, v₀)) := by
  let z₀ : E × E := (x₀, v₀)
  rcases flowOnUnitBall g hg hinv z₀ with ⟨Tf, hTf, Lf, Φ, hΦF, hLipF⟩
  rcases canonical_solutions g hg hinv z₀ Tf hTf Φ hΦF with
    ⟨Tj, hTj0, hTjTf, J, hJ0, hJd, hJadd, hJsmul⟩
  rcases uniform_lin_est g hg hinv z₀ Tf hTf Lf Φ hΦF hLipF Tj hTj0 hTjTf J hJ0 hJd with
    ⟨T, hT0, hTltTf, hEst⟩
  have hΦ₀T : ∀ z ∈ closedBall z₀ 1, Φ z 0 = z ∧
      ∀ t ∈ Icc (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    intro z hz
    constructor
    · exact (hΦF z hz).1
    · intro t ht
      exact (hΦF z hz).2 t (by
        constructor
        · exact le_trans (neg_le_neg (le_of_lt hTltTf)) ht.1
        · exact le_trans ht.2 (le_of_lt hTltTf))
  refine ⟨T, hT0, Φ, hΦ₀T, ?_⟩
  intro t ht
  let L : (E × E) →ₗ[ℝ] (E × E) :=
    { toFun := fun w => J w t
      map_add' := fun a b => hJadd t a b
      map_smul' := fun c a => hJsmul t a c }
  let Lclm : (E × E) →L[ℝ] (E × E) := LinearMap.toContinuousLinearMap L
  refine ⟨Lclm, ?_⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  rcases hEst c hc with ⟨h₀, hh₀, hEst'⟩
  let ρ : ℝ := min h₀ 1
  have hρ : 0 < ρ := by dsimp [ρ]; exact lt_min hh₀ zero_lt_one
  filter_upwards [Metric.ball_mem_nhds (0 : E × E) hρ] with v hv
  have hv_lt : ‖v‖ < ρ := by
    simpa [Real.dist_eq] using (mem_ball.mp hv)
  by_cases hv0 : v = 0
  · subst v
    have hL0 : Lclm 0 = 0 := by
      dsimp [Lclm]
      exact (L : (E × E) →ₗ[ℝ] (E × E)).map_zero
    simp [hL0]
  · have hnorm_ne : ‖v‖ ≠ 0 := by
      intro h
      exact hv0 (norm_eq_zero.mp h)
    have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    let w : E × E := (‖v‖⁻¹) • v
    have hw_norm : ‖w‖ ≤ 1 := by
      dsimp [w]
      have hnw : ‖(‖v‖⁻¹) • v‖ = ‖v‖⁻¹ * ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (le_of_lt hpos)]
      rw [hnw]
      have hc' : ‖v‖⁻¹ * ‖v‖ = 1 := by field_simp [hnorm_ne]
      simpa [hc']
    have hvs : v = (‖v‖ : ℝ) • w := by
      dsimp [w]
      rw [smul_smul]
      have hmul : (‖v‖ : ℝ) * (‖v‖⁻¹) = 1 := by field_simp [hnorm_ne]
      rw [hmul, one_smul]
    have hhlt : |‖v‖| < h₀ := by
      have hle : ‖v‖ < h₀ := by
        exact lt_of_lt_of_le hv_lt (min_le_left h₀ 1)
      simpa [abs_of_nonneg (le_of_lt hpos)] using hle
    have hmem : z₀ + (‖v‖ : ℝ) • w ∈ closedBall z₀ 1 := by
      rw [mem_closedBall, dist_eq_norm]
      have hle1 : ‖(‖v‖ : ℝ) • w‖ ≤ 1 := by
        have hnw : ‖(‖v‖ : ℝ) • w‖ = ‖v‖ * ‖w‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
        rw [hnw]
        have hm : ‖v‖ * ‖w‖ ≤ ‖v‖ * 1 := mul_le_mul_of_nonneg_left hw_norm (le_of_lt hpos)
        have hle2 : ‖v‖ ≤ 1 := by
          exact le_trans (le_of_lt hv_lt) (min_le_right h₀ 1)
        calc
          ‖v‖ * ‖w‖ ≤ ‖v‖ * 1 := hm
          _ = ‖v‖ := by ring
          _ ≤ 1 := hle2
      calc
        ‖(z₀ + (‖v‖ : ℝ) • w) - z₀‖ = ‖(‖v‖ : ℝ) • w‖ := by simp
        _ ≤ 1 := hle1
    have hb := hEst' w hw_norm (‖v‖) hnorm_ne hhlt hmem t ht
    -- hb : ‖(1 / ‖v‖) • (Φ (z₀ + ‖v‖ • w) t - Φ z₀ t) - J w t‖ ≤ c
    have hb0 : ‖(‖v‖⁻¹) • (Φ (z₀ + (‖v‖ : ℝ) • w) t - Φ z₀ t) - J w t‖ ≤ c := by
      simpa [one_div] using hb
    have hb' : ‖Φ (z₀ + (‖v‖ : ℝ) • w) t - Φ z₀ t - (‖v‖ : ℝ) • (J w t)‖ ≤ ‖v‖ * c :=
      norm_unscale_le (X := Φ (z₀ + (‖v‖ : ℝ) • w) t - Φ z₀ t) (Y := J w t)
        (r := ‖v‖) (c := c) hpos hb0
    have hJv : (‖v‖ : ℝ) • (J w t) = J v t := by
      rw [← hJsmul t w (‖v‖)]
      congr 1
      exact hvs.symm
    have hb'' : ‖Φ (z₀ + v) t - Φ z₀ t - J v t‖ ≤ c * ‖v‖ := by
      rw [← hvs] at hb'
      rw [hJv] at hb'
      have hmul : ‖v‖ * c = c * ‖v‖ := by ring
      rwa [hmul] at hb'
    have hLv : Lclm v = J v t := by
      dsimp [L, Lclm]
    simpa [hLv] using hb''
end

end Submission.Model
