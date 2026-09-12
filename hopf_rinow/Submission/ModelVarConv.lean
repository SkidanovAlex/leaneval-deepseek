import Submission.Model
import Submission.ModelCore
import Submission.ModelFlowCont
import Submission.ModelJacobi
import Submission.ModelVarError
import Submission.ModelUniq
import Mathlib

/-!
# Variation lemma: difference quotients of the flow converge to the linearized solution
-/

open ContinuousLinearMap
open scoped ContDiff Topology
open Set Metric Filter

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section
lemma linearized_of_pair (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) {ε : ℝ} (hε : 0 < ε) {z : ℝ → E × E} {w : E × E}
    (hz : ∀ t ∈ Ioo (-ε) ε, HasDerivAt z (odeField g (z t)) t) :
    ∃ T > 0, T < ε ∧ ∃ J : ℝ → E × E,
      J 0 = w ∧
      (∀ t ∈ Ioo (-T) T,
        HasDerivAt J ((fderiv ℝ (odeField g)) (z t) (J t)) t) := by
  let c : ℝ → E := fun t => (z t).1
  let vel : ℝ → E := fun t => (z t).2
  have hc (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : HasDerivAt c (vel t) t := by
    have hzt := hz t ht
    have h1 : HasDerivAt (fun s => (z s).1) (odeField g (z t)).1 t := by
      have hf := hzt.hasFDerivAt.fst.hasDerivAt
      simpa using hf
    simpa [c, vel, odeField] using h1
  have hv (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t := by
    have hzt := hz t ht
    have h2 : HasDerivAt (fun s => (z s).2) (odeField g (z t)).2 t := by
      have hf := hzt.hasFDerivAt.snd.hasDerivAt
      simpa using hf
    simpa [c, vel, odeField] using h2
  rcases linearized_exists g hg hinv hε (w := w) hc hv with ⟨T, hT, hTε, J, hJ0, hJ⟩
  refine ⟨T, hT, hTε, J, hJ0, ?_⟩
  intro t ht
  have hJt := hJ t ht
  simpa [c, vel] using hJt

lemma flowOnUnitBall (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) :
    ∃ T > 0, ∃ L : NNReal, ∃ Φ : (E × E) → ℝ → (E × E),
      (∀ z ∈ closedBall z₀ 1, Φ z 0 = z ∧
         ∀ t ∈ Icc (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
      (∀ t ∈ Icc (-T) T, LipschitzOnWith L (fun z => Φ z t) (closedBall z₀ 1)) := by
  let V : (E × E) → (E × E) := odeField g
  have hV1 : ContDiff ℝ 1 V := by
    rw [contDiff_iff_contDiffAt]
    intro p
    rcases p with ⟨x, v⟩
    simpa [V] using odeField_contDiffAt g hg hinv x v
  have hfcont : Continuous (fderiv ℝ V) := hV1.continuous_fderiv (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hVcont : Continuous V := hV1.continuous
  let S : Set (E × E) := closedBall z₀ 2
  have hScomp : IsCompact S := isCompact_closedBall z₀ 2
  have hSne : S.Nonempty := ⟨z₀, by simp [S]⟩
  have hnormOn : ContinuousOn (fun x => ‖fderiv ℝ V x‖) S := hfcont.norm.continuousOn
  rcases hScomp.exists_isMaxOn hSne hnormOn with ⟨xm, hxm, hmax⟩
  have hVnormOn : ContinuousOn (fun x => ‖V x‖) S := hVcont.norm.continuousOn
  rcases hScomp.exists_isMaxOn hSne hVnormOn with ⟨xL, hxL, hLmax⟩
  let K : NNReal := ⟨‖fderiv ℝ V xm‖, norm_nonneg _⟩
  let Lb : NNReal := ⟨‖V xL‖, norm_nonneg _⟩
  have hKbnd : ∀ x ∈ S, ‖fderiv ℝ V x‖ ≤ (K : ℝ) := by
    intro x hx
    calc
      ‖fderiv ℝ V x‖ ≤ ‖fderiv ℝ V xm‖ := hmax hx
      _ = (K : ℝ) := rfl
  have hLbnd : ∀ x ∈ S, ‖V x‖ ≤ (Lb : ℝ) := by
    intro x hx
    calc
      ‖V x‖ ≤ ‖V xL‖ := hLmax hx
      _ = (Lb : ℝ) := rfl
  have hKbd (x : E × E) (hx : x ∈ closedBall z₀ 2) (y : E × E)
      (hy : y ∈ closedBall z₀ 2) : ‖V y - V x‖ ≤ (K : ℝ) * ‖y - x‖ := by
    have hdiff : ∀ q ∈ S, DifferentiableAt ℝ V q := fun q _ =>
      (hV1.differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0)).differentiableAt
    have hsub := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := V) hdiff hKbnd
      (convex_closedBall z₀ 2) hx hy
    simpa [V, S] using hsub
  have hKbdnn : LipschitzOnWith K V (closedBall z₀ 2) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have := hKbd x hx y hy
    simpa [dist_eq_norm, norm_sub_rev] using this
  let τ : ℝ := 1 / (2 * ((Lb : ℝ) + 1))
  have hτpos : 0 < τ := by positivity
  have hmem0 : (0 : ℝ) ∈ Icc (-τ) τ := by constructor <;> linarith
  have hpl : IsPicardLindelof (fun _ => V) (tmin := -τ) (tmax := τ) ⟨0, hmem0⟩ z₀
      (2 : NNReal) 1 Lb K := by
    refine IsPicardLindelof.mk ?lipschitzOnWith ?continuousOn ?norm_le ?mul_max_le
    · intro t ht
      simpa [V] using hKbdnn
    · intro x hx
      exact continuousOn_const
    · intro t ht x hx
      exact hLbnd x hx
    · dsimp
      norm_num
      have hle : (Lb : ℝ) * τ ≤ 1 := by
        dsimp [τ]
        have hpos : 0 < 2 * ((Lb : ℝ) + 1) := by positivity
        calc
          (Lb : ℝ) * (1 / (2 * ((Lb : ℝ) + 1))) = (Lb : ℝ) / (2 * ((Lb : ℝ) + 1)) := by ring
          _ ≤ 1 := by
            rw [div_le_iff₀ hpos]
            nlinarith [Lb.2]
      exact hle
  rcases hpl.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith with
    ⟨α, hα, L', hLip⟩
  let T : ℝ := τ / 2
  have hTpos : 0 < T := by dsimp [T]; positivity
  refine ⟨T, hTpos, L', α, ?_, ?_⟩
  · intro z hz
    constructor
    · exact (hα z hz).1
    · intro t ht
      have h1 : -T ≤ t := (mem_Icc.mp ht).1
      have h2 : t ≤ T := (mem_Icc.mp ht).2
      have htlo : -τ < t := by dsimp [T] at *; linarith
      have hthi : t < τ := by dsimp [T] at *; linarith
      have htIcc : t ∈ Icc (-τ) τ := by constructor <;> linarith
      exact ((hα z hz).2 t htIcc).hasDerivAt (Icc_mem_nhds htlo hthi)
  · intro t ht
    have h1 : -T ≤ t := (mem_Icc.mp ht).1
    have h2 : t ≤ T := (mem_Icc.mp ht).2
    exact hLip t (by
      dsimp [T] at h1 h2
      constructor <;> linarith)

/-- The main analytic estimate (see `variation_gateaux`). -/
lemma variation_estimate (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) (w : E × E)
    (Tf : ℝ) (hTf : 0 < Tf) (Lf : NNReal) (Φ : (E × E) → ℝ → (E × E))
    (hΦ₀ : ∀ z ∈ closedBall z₀ 1, Φ z 0 = z ∧
       ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    (hLip : ∀ t ∈ Icc (-Tf) Tf, LipschitzOnWith Lf (fun z => Φ z t) (closedBall z₀ 1)) :
    ∃ T > 0, T < Tf ∧ ∃ J : ℝ → E × E,
      J 0 = w ∧
      (∀ t ∈ Ioo (-T) T,
        HasDerivAt J ((fderiv ℝ (odeField g)) (Φ z₀ t) (J t)) t) ∧
      (∀ η > 0, ∃ h₀ > 0, ∀ h : ℝ, h ≠ 0 → |h| < h₀ →
          z₀ + h • w ∈ closedBall z₀ 1 →
          ∀ t ∈ Icc (-T) T,
            ‖(1 / h) • (Φ (z₀ + h • w) t - Φ z₀ t) - J t‖ ≤ η) := by
  let F := E × E
  let V : F → F := odeField g
  let cur : ℝ → F := fun t => Φ z₀ t
  have hz₀mem : z₀ ∈ closedBall z₀ 1 := by simp
  have hcur (t : ℝ) (ht : t ∈ Icc (-Tf) Tf) : HasDerivAt cur (V (cur t)) t := by
    simpa [cur, V] using (hΦ₀ z₀ hz₀mem).2 t ht
  have hcurIoo (t : ℝ) (ht : t ∈ Ioo (-Tf) Tf) : HasDerivAt cur (V (cur t)) t :=
    hcur t (Ioo_subset_Icc_self ht)
  rcases linearized_of_pair g hg hinv (hε := hTf) (z := cur) (w := w) hcurIoo with
    ⟨Tj, hTj0, hTjlt, J, hJ0, hJ⟩
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
  -- K bound for the fderiv along the base trajectory on the final interval
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
  -- first-order Taylor error of V along cur, on Icc(-T) T, for any tolerance ε
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
  refine ⟨T, hT0, hTltTf, J, hJ0, ?_, ?_⟩
  · intro t ht
    have hJt := hJ t (hTjIoo (Ioo_subset_Icc_self ht))
    simpa [V, cur] using hJt
  · intro η hη
    -- ε-parameter for Gronwall via continuity at 0
    have hgronCont : Continuous (fun ε : ℝ => gronwallBound 0 K ε T) := gronwallBound_continuous_ε 0 K T
    rcases Metric.continuousAt_iff.mp hgronCont.continuousAt η hη with ⟨c₀, hc₀, hc₀bd⟩
    let s : ℝ := (Lf : ℝ) * ‖w‖
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
    -- main pointwise facts, uniform in h
    refine ⟨h₀, hh₀, ?_⟩
    intro h hhne hhlt hzmem
    let zh : ℝ → F := fun u => Φ (z₀ + h • w) u
    let q : ℝ → F := fun u => (1 / h) • (zh u - cur u)
    let D : ℝ → F := fun u => q u - J u
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
        _ = (Lf : ℝ) * (|h| * ‖w‖) := by rw [norm_smul, Real.norm_eq_abs]
        _ = s * |h| := by
          dsimp [s]
          ring
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
      have hJx : HasDerivAt J ((fderiv ℝ V) (cur x) (J x)) x := by
        have hJt := hJ x (hTjIoo hx)
        simpa [V, cur] using hJt
      have hDx : HasDerivAt (fun u : ℝ => q u - J u)
          ((A (q x) + (1 / h) • R) - A (J x)) x := (hdq.sub hJx)
      refine ⟨(A (q x) + (1 / h) • R) - A (J x), ?_, ?_⟩
      · simpa [D] using hDx
      · have hAK : ‖A‖ ≤ K := by
          simpa [A] using hKb x hx
        have hb1 : ‖A (q x) - A (J x)‖ ≤ K * ‖D x‖ := by
          calc
            ‖A (q x) - A (J x)‖ = ‖A (q x - J x)‖ := by rw [map_sub]
            _ ≤ ‖A‖ * ‖q x - J x‖ := A.le_opNorm (q x - J x)
            _ ≤ K * ‖q x - J x‖ := mul_le_mul_of_nonneg_right hAK (norm_nonneg _)
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
        have hdec : (A (q x) + (1 / h) • R) - A (J x) =
            (A (q x) - A (J x)) + (1 / h) • R := by abel
        rw [hdec]
        exact le_trans (norm_add_le (A (q x) - A (J x)) ((1 / h) • R)) (by nlinarith)
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
      rw [hstep, hJ0]
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


/-- Gateaux differentiability of the geodesic flow in the initial data: difference quotients in a
fixed direction converge (uniformly in time) to the solution of the linearized equation. -/
theorem variation_gateaux (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ v₀ : E) (w : E × E) :
    ∃ T > 0, ∃ Φ : E × E → ℝ → E × E,
      (∀ z ∈ closedBall (x₀, v₀) 1, Φ z 0 = z ∧
         ∀ t ∈ Icc (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
      (∃ J : ℝ → E × E, J 0 = w ∧
        (∀ t ∈ Ioo (-T) T,
          HasDerivAt J ((fderiv ℝ (odeField g)) (Φ (x₀, v₀) t) (J t)) t) ∧
        (∀ η > 0, ∃ h₀ > 0, ∀ h : ℝ, h ≠ 0 → |h| < h₀ →
          (x₀, v₀) + h • w ∈ closedBall (x₀, v₀) 1 →
          ∀ t ∈ Icc (-T) T,
            ‖(1 / h) • (Φ ((x₀, v₀) + h • w) t - Φ (x₀, v₀) t) - J t‖ ≤ η)) := by
  let z₀ : E × E := (x₀, v₀)
  rcases flowOnUnitBall g hg hinv z₀ with ⟨Tf, hTf, Lf, Φ, hΦF, hLipF⟩
  rcases variation_estimate g hg hinv z₀ w Tf hTf Lf Φ hΦF hLipF with
    ⟨T, hT, hTlt, J, hJ0, hJd, hconv⟩
  refine ⟨T, hT, Φ, ?_, J, hJ0, ?_, ?_⟩
  · intro z hz
    constructor
    · exact (hΦF z hz).1
    · intro t ht
      exact (hΦF z hz).2 t (by
        constructor
        · exact le_trans (neg_le_neg (le_of_lt hTlt)) ht.1
        · exact le_trans ht.2 (le_of_lt hTlt))
  · intro t ht
    have hJt := hJd t ht
    simpa [z₀] using hJt
  · intro η hη
    rcases hconv η hη with ⟨h₀, hh₀, hh⟩
    refine ⟨h₀, hh₀, ?_⟩
    intro h hhne hhlt hzmem t ht
    have hzmem' : z₀ + h • w ∈ closedBall z₀ 1 := by simpa [z₀] using hzmem
    have hb := hh h hhne hhlt hzmem' t ht
    simpa [z₀] using hb

end

end Submission.Model
