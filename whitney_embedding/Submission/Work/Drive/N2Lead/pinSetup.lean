import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.windowChartCoord
import Submission.Work.Drive.N2.windowBallTarget
import Submission.Work.Drive.N2.canonChartOfScaled
import Submission.Work.Drive.N2.modelFlowDefs
import Submission.Work.Drive.N2.im_sq_eq_of_flow_closedODE
import Submission.Work.Drive.N2Lead.pinComplex
import Submission.Work.Drive.N2Lead.saddlePinDefs

/-!
# The chart setup of the saddle pin

`Work.Drive.N2Lead.SaddleChart` bundles, for a `WindowDatum` whose marked chart carries a saddle
sign convention, a chart `φ'` with the same source and model balls as the datum's marked chart and
its complex coordinate `Zc`, with

* the level law `f = f p + Re (Zc ·)²` on the source,
* the relation between `Im (Zc ·)²` and the datum's own `Im (chartZ ·)²` (they agree up to sign),
* the conservation of `Im (Zc ·)²` along traces confined to the datum's ODE region `C j`,
* the chart ODE in the `(1, -1)` convention,
* the fact that the ball of radius `ρ j` lies in `φ'.target`.

The four *pin arcs* are the points of the model chart whose coordinate is `±(I √(ηs - i w))` (the
anchor level) and `±√(ηs + i w)` (the upper level); the file proves their basic rows and the
*classification* of the points of the anchor pin.
-/

set_option maxHeartbeats 1600000

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter
open Work.Drive.N2

/-- The plane vector of a complex number. -/
noncomputable def cplxVec (z : ℂ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![z.re, z.im]

@[simp] lemma cplxVec_zero (z : ℂ) : cplxVec z 0 = z.re := by simp [cplxVec]
@[simp] lemma cplxVec_one (z : ℂ) : cplxVec z 1 = z.im := by simp [cplxVec]

/-- The complex number of a plane vector. -/
lemma cplxVec_chartZ {M : Type*} [TopologicalSpace M]
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (y : M) :
    cplxVec (Work.Drive.N2.chartZ φ y) = φ y := by
  apply WithLp.ofLp_injective
  funext j
  fin_cases j <;> simp [cplxVec, Work.Drive.N2.chartZ]

/-- The complex number of a plane vector, for a bare vector. -/
lemma cplxVec_self (v : EuclideanSpace ℝ (Fin 2)) :
    cplxVec ((v 0 : ℂ) + (v 1 : ℂ) * Complex.I) = v := by
  apply WithLp.ofLp_injective
  funext j
  fin_cases j <;> simp [cplxVec]

lemma norm_cplxVec (z : ℂ) : ‖cplxVec z‖ = ‖z‖ := by
  have h : ‖cplxVec z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [← Work.Drive.N2.norm_uVec (cplxVec z), Complex.sq_norm, Complex.normSq_apply]
    simp only [cplxVec_zero, cplxVec_one, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg (cplxVec z), norm_nonneg z]

lemma norm_chartZ {M : Type*} [TopologicalSpace M]
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (y : M) :
    ‖Work.Drive.N2.chartZ φ y‖ = ‖φ y‖ := by
  rw [← cplxVec_chartZ φ y, norm_cplxVec]

lemma norm_complex_sqrt (z : ℂ) : ‖Complex.sqrt z‖ ^ 2 = ‖z‖ := by
  have h : Complex.sqrt z ^ 2 = z := Work.Drive.N2.complex_sqrt_sq z
  calc ‖Complex.sqrt z‖ ^ 2 = ‖Complex.sqrt z ^ 2‖ := by rw [norm_pow]
    _ = ‖z‖ := by rw [h]

/-- `(z ^ 2).re = z.re ^ 2 - z.im ^ 2`. -/
lemma sq_re (z : ℂ) : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
  rw [pow_two, Complex.mul_re]; ring

lemma re_sq_chart {a b : ℝ} : ((((a : ℂ) + (b : ℂ) * Complex.I) ^ 2).re) = a ^ 2 - b ^ 2 := by
  rw [sq_re]; simp

/-- `(z ^ 2).im = 2 z.re z.im`. -/
lemma sq_im (z : ℂ) : (z ^ 2).im = 2 * z.re * z.im := by
  rw [pow_two, Complex.mul_im]; ring

lemma re_sq_I_mul (z : ℂ) : (((Complex.I * z) ^ 2).re) = -((z ^ 2).re) := by
  rw [pow_two, pow_two, mul_mul_mul_comm, Complex.I_mul_I, neg_one_mul, Complex.neg_re]

lemma im_sq_I_mul (z : ℂ) : (((Complex.I * z) ^ 2).im) = -((z ^ 2).im) := by
  rw [pow_two, pow_two, mul_mul_mul_comm, Complex.I_mul_I, neg_one_mul, Complex.neg_im]

lemma I_mul_neg_I_mul (z : ℂ) : Complex.I * (-(Complex.I * z)) = z := by
  rw [mul_neg, ← mul_assoc, Complex.I_mul_I]
  ring

/-- The squared norm of `ηs - i w` for real `ηs`, `w`. -/
lemma norm_ofReal_mul {r : ℝ} (hr : 0 ≤ r) (c : ℂ) : ‖(r : ℂ) * c‖ = r * ‖c‖ := by
  rw [norm_mul, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hr]

lemma norm_sub_I_mul_sq (ηs w : ℝ) : ‖(ηs : ℂ) - (w : ℂ) * Complex.I‖ ^ 2 = ηs ^ 2 + w ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, Complex.sub_im, zero_sub, neg_mul, neg_neg,
    Complex.mul_im, add_zero]
  ring

/-- The norm of `√(ηs + i w)` (and of `√(ηs - i w)`) is at most `2` for `0 ≤ ηs ≤ 1`, `|w| ≤ 2`. -/
lemma norm_sqrt_le_two {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1) (hw : |w| ≤ 2) :
    ‖Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I)‖ < 2 := by
  have h1 : ‖Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I)‖ ^ 2
      = ‖(ηs : ℂ) + (w : ℂ) * Complex.I‖ := norm_complex_sqrt _
  have h2 : ‖(ηs : ℂ) + (w : ℂ) * Complex.I‖ ≤ 3 := by
    have h3 : ‖(ηs : ℂ) - ((-w : ℝ) : ℂ) * Complex.I‖ ^ 2 = ηs ^ 2 + (-w) ^ 2 :=
      norm_sub_I_mul_sq ηs (-w)
    have h4 : ((ηs : ℂ) - ((-w : ℝ) : ℂ) * Complex.I) = (ηs : ℂ) + (w : ℂ) * Complex.I := by
      push_cast; ring
    rw [h4] at h3
    have h5 : ηs ^ 2 + (-w) ^ 2 ≤ 5 := by
      have : (-w) ^ 2 = w ^ 2 := by ring
      nlinarith [abs_le.mp hw, sq_nonneg ηs, sq_nonneg w, hηs1, hηs]
    have h6 : ‖(ηs : ℂ) + (w : ℂ) * Complex.I‖ ^ 2 ≤ 9 := by
      rw [h3]; nlinarith
    nlinarith [norm_nonneg ((ηs : ℂ) + (w : ℂ) * Complex.I)]
  nlinarith [norm_nonneg (Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I)), h1, h2]

lemma norm_sqrt_sub_le_two {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1) (hw : |w| ≤ 2) :
    ‖Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I)‖ < 2 := by
  have h : ((ηs : ℂ) - (w : ℂ) * Complex.I) = (ηs : ℂ) + ((-w : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h]
  exact norm_sqrt_le_two hηs hηs1 (by simpa using hw)

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The chart setup of the saddle pin.** -/
structure SaddleChart {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) where
  φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))
  Zc : M → ℂ
  source_eq : φ'.source = (D.φ D.j).source
  ball_eq : ∀ r : ℝ, Work.Drive.N2.modelBall φ' r = Work.Drive.N2.modelBall (D.φ D.j) r
  Zc_eq : ∀ y : M, Zc y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I
  level_eq : ∀ y ∈ φ'.source, f y = f p + ((Zc y) ^ 2).re
  im_sq_eq : ∀ y ∈ φ'.source,
    (((Zc y) ^ 2).im) ^ 2 = (((Work.Drive.N2.chartZ (D.φ D.j) y) ^ 2).im) ^ 2
  target_ball : ∀ v : EuclideanSpace ℝ (Fin 2), ‖v‖ < D.ρ D.j → v ∈ φ'.target
  ODE : ∀ (y : M) (t : ℝ),
    (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
    HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 0)
      (Work.Drive.N2.chartMult (D.ρ D.j / 8) (‖φ' (D.Φ (t, y))‖ ^ 2)
        * ((1 : ℝ) * φ' (D.Φ (t, y)) 0)) t ∧
    HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 1)
      (Work.Drive.N2.chartMult (D.ρ D.j / 8) (‖φ' (D.Φ (t, y))‖ ^ 2)
        * ((-1 : ℝ) * φ' (D.Φ (t, y)) 1)) t

namespace SaddleChart

variable {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p}

lemma mem_target (S : SaddleChart D) {v : EuclideanSpace ℝ (Fin 2)}
    (hv : ‖v‖ < D.ρ D.j) : v ∈ S.φ'.target := S.target_ball v hv

lemma symm_apply (S : SaddleChart D) {v : EuclideanSpace ℝ (Fin 2)}
    (hv : ‖v‖ < D.ρ D.j) : S.φ' (S.φ'.symm v) = v :=
  S.φ'.right_inv (S.target_ball v hv)

lemma symm_mem_source (S : SaddleChart D) {v : EuclideanSpace ℝ (Fin 2)}
    (hv : ‖v‖ < D.ρ D.j) : S.φ'.symm v ∈ S.φ'.source :=
  S.φ'.map_target (S.target_ball v hv)

lemma symm_mem_datum (S : SaddleChart D) {v : EuclideanSpace ℝ (Fin 2)}
    (hv : ‖v‖ < D.ρ D.j) : S.φ'.symm v ∈ (D.φ D.j).source := by
  rw [← S.source_eq]; exact S.symm_mem_source hv

lemma Zc_chartZ (S : SaddleChart D) (y : M) :
    S.Zc y = Work.Drive.N2.chartZ S.φ' y := S.Zc_eq y

lemma norm_Zc (S : SaddleChart D) (y : M) : ‖S.Zc y‖ = ‖S.φ' y‖ := by
  rw [S.Zc_chartZ y, norm_chartZ]

/-- The chart norms of `φ'` and of the datum's chart agree on the common source. -/
lemma norm_eq (S : SaddleChart D) {y : M} (hy : y ∈ S.φ'.source) :
    ‖S.φ' y‖ = ‖D.φ D.j y‖ := by
  have hy' : y ∈ (D.φ D.j).source := by rw [← S.source_eq]; exact hy
  have hiff : ∀ r : ℝ, ‖S.φ' y‖ < r ↔ ‖D.φ D.j y‖ < r := by
    intro r
    have h1 : y ∈ Work.Drive.N2.modelBall S.φ' r ↔ y ∈ Work.Drive.N2.modelBall (D.φ D.j) r := by
      rw [S.ball_eq r]
    simp only [Work.Drive.N2.modelBall, Set.mem_ofPred_eq, hy, hy', true_and] at h1
    exact h1
  refine le_antisymm ?_ ?_
  · by_contra hc
    rw [not_le] at hc
    obtain ⟨r, h1, h2⟩ := exists_between hc
    exact absurd ((hiff r).mpr h1) (not_lt.mpr h2.le)
  · by_contra hc
    rw [not_le] at hc
    obtain ⟨r, h1, h2⟩ := exists_between hc
    exact absurd ((hiff r).mp h1) (not_lt.mpr h2.le)

lemma injOn_Zc (S : SaddleChart D) : Set.InjOn S.Zc S.φ'.source := by
  intro x hx y hy hxy
  have h1 : cplxVec (S.Zc x) = cplxVec (S.Zc y) := congrArg cplxVec hxy
  rw [S.Zc_chartZ x, S.Zc_chartZ y, cplxVec_chartZ, cplxVec_chartZ] at h1
  exact S.φ'.injOn hx hy h1

/-- The conservation of `Im (Zc ·)²` along traces confined to the datum's ODE region. -/
lemma im_inv (S : SaddleChart D) (y : M) (t : ℝ)
    (hconf : ∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) :
    ((S.Zc (D.Φ (t, y))) ^ 2).im = ((S.Zc y) ^ 2).im :=
  Work.Drive.N2.im_sq_eq_of_flow_closedODE (S.φ') (S.Zc) (S.Zc_eq) (D.ρ D.j / 8)
    (C := D.C D.j) (S.ODE) D.hΦ0 y t hconf

lemma chartZ_symm (S : SaddleChart D) {v : EuclideanSpace ℝ (Fin 2)}
    (hv : ‖v‖ < D.ρ D.j) :
    S.Zc (S.φ'.symm v) = (v 0 : ℂ) + (v 1 : ℂ) * Complex.I := by
  rw [S.Zc_chartZ, Work.Drive.N2.chartZ_apply, S.symm_apply hv]

/-- The chart-coordinate row for an arc vector. -/
lemma Zc_arcVec (S : SaddleChart D) (c : ℂ) (hc : ‖c‖ < 8) :
    S.Zc (S.φ'.symm (cplxVec (((D.ρ D.j / 8 : ℝ)) * c)))
      = (((D.ρ D.j / 8 : ℝ)) : ℂ) * c := by
  have hvec : ‖(((D.ρ D.j / 8 : ℝ)) * c : ℂ)‖ < D.ρ D.j := by
    have hρ := D.hρ D.j
    rw [norm_mul, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (by positivity)]
    nlinarith
  rw [S.chartZ_symm (by rw [norm_cplxVec]; exact hvec), cplxVec_zero, cplxVec_one]
  exact Complex.re_add_im _

end SaddleChart


/-- **The chart setup exists.**  This is the canonical chart of the saddle
(`Work.Drive.N2.saddleChartData`, re-proved here in the form the pin arguments need: the chart is
the datum's marked chart, or its quarter turn in the `s₁ = -1` case, so that the ball of radius
`ρ j` is known to be in its target). -/
theorem saddleChart_exists {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsgn : D.s₁ D.j = - D.s₂ D.j) : Nonempty (SaddleChart D) := by
  rcases D.hsgn D.j with ⟨h1, h2⟩
  rcases h1 with h1 | h1
  · -- `s₁ = 1`: the datum's chart is already canonical
    have hs2 : D.s₂ D.j = -1 := by linarith [hsgn, h1]
    have hlev : ∀ y ∈ (D.φ D.j).source,
        f y = f p + ((Work.Drive.N2.chartZ (D.φ D.j) y) ^ 2).re := by
      intro y hy
      have hv := D.hval D.j y hy
      rw [D.hxj] at hv
      rw [hv, h1, hs2]
      simp only [Work.Drive.N2.chartQ]
      rw [Work.Drive.N2.chartZ_apply, re_sq_chart]
      ring
    have hODE : ∀ (y : M) (t : ℝ),
        (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
        HasDerivAt (fun σ : ℝ => D.φ D.j (D.Φ (σ, y)) 0)
          (Work.Drive.N2.chartMult (D.ρ D.j / 8) (‖D.φ D.j (D.Φ (t, y))‖ ^ 2)
            * ((1 : ℝ) * D.φ D.j (D.Φ (t, y)) 0)) t ∧
        HasDerivAt (fun σ : ℝ => D.φ D.j (D.Φ (σ, y)) 1)
          (Work.Drive.N2.chartMult (D.ρ D.j / 8) (‖D.φ D.j (D.Φ (t, y))‖ ^ 2)
            * ((-1 : ℝ) * D.φ D.j (D.Φ (t, y)) 1)) t := by
      intro y t h
      obtain ⟨hd0, hd1⟩ := D.hODE D.j y t h
      rw [h1] at hd0
      rw [hs2] at hd1
      exact ⟨hd0, by simpa using hd1⟩
    exact ⟨{ φ' := D.φ D.j, Zc := Work.Drive.N2.chartZ (D.φ D.j), source_eq := rfl, ball_eq := (fun r => rfl), Zc_eq := (fun y => rfl), level_eq := hlev, im_sq_eq := (fun y hy => rfl), target_ball := (fun v hv => Work.Drive.N2.windowBall_subset_target D D.j hv), ODE := hODE }⟩
  · -- `s₁ = -1`: turn the chart by the quarter turn
    have hs2 : D.s₂ D.j = 1 := by linarith [hsgn, h1]
    obtain ⟨φ', hsrc', hball', hsm', hlin⟩ :=
      canonChartOfScaled (D.φ D.j) (fun y => Complex.I * Work.Drive.N2.chartZ (D.φ D.j) y)
        (by norm_num : (1 : ℝ) ≠ 0) (D.hφ D.j) (Or.inr rfl)
        (fun y => by rw [Work.Drive.N2.chartZ_apply]; simp)
    have hlin' : ∀ y ∈ (D.φ D.j).source,
        Work.Drive.N2.chartZ φ' y = Complex.I * Work.Drive.N2.chartZ (D.φ D.j) y := by
      intro y hy
      have h := hlin y hy
      rw [Work.Drive.N2.chartZ_apply, h]
      simp only [Complex.ofReal_one, one_mul]
    have hcoord : ∀ y ∈ (D.φ D.j).source,
        φ' y 0 = -(D.φ D.j y 1) ∧ φ' y 1 = D.φ D.j y 0 := by
      intro y hy
      have h := hlin' y hy
      constructor
      · have := congrArg Complex.re h
        simpa [Work.Drive.N2.chartZ, Complex.mul_re, Complex.mul_im] using this
      · have := congrArg Complex.im h
        simpa [Work.Drive.N2.chartZ, Complex.mul_re, Complex.mul_im] using this
    have hnorm_eq : ∀ y ∈ (D.φ D.j).source, ‖φ' y‖ = ‖D.φ D.j y‖ := by
      intro y hy
      rw [← norm_chartZ φ' y, hlin' y hy, norm_mul, Complex.norm_I, one_mul, norm_chartZ]
    have hlev : ∀ y ∈ (D.φ D.j).source,
        f y = f p + ((Work.Drive.N2.chartZ φ' y) ^ 2).re := by
      intro y hy
      have hv := D.hval D.j y hy
      rw [D.hxj] at hv
      rw [hv, h1, hs2]
      simp only [Work.Drive.N2.chartQ]
      rw [hlin' y hy, re_sq_I_mul, Work.Drive.N2.chartZ_apply, re_sq_chart]
      ring
    have himsq : ∀ y ∈ (D.φ D.j).source,
        (((Work.Drive.N2.chartZ φ' y) ^ 2).im) ^ 2
          = (((Work.Drive.N2.chartZ (D.φ D.j) y) ^ 2).im) ^ 2 := by
      intro y hy
      rw [hlin' y hy, im_sq_I_mul, neg_sq]
    have htarget : ∀ v : EuclideanSpace ℝ (Fin 2), ‖v‖ < D.ρ D.j → v ∈ φ'.target := by
      intro v hv
      -- `φ'` is the quarter turn of the datum's chart
      set z : ℂ := (v 0 : ℂ) + (v 1 : ℂ) * Complex.I with hz
      set w : EuclideanSpace ℝ (Fin 2) := cplxVec (-(Complex.I * z)) with hw
      have hnormw : ‖w‖ = ‖v‖ := by
        have hz' : cplxVec z = v := by rw [hz]; exact cplxVec_self v
        rw [hw, norm_cplxVec, norm_neg, norm_mul, Complex.norm_I, one_mul, ← hz', norm_cplxVec]
      have hwT : w ∈ (D.φ D.j).target :=
        Work.Drive.N2.windowBall_subset_target D D.j (by rw [hnormw]; exact hv)
      have hysrc : (D.φ D.j).symm w ∈ (D.φ D.j).source := (D.φ D.j).map_target hwT
      have hchart : Work.Drive.N2.chartZ (D.φ D.j) ((D.φ D.j).symm w) = -(Complex.I * z) := by
        rw [Work.Drive.N2.chartZ_apply, (D.φ D.j).right_inv hwT, hw, cplxVec_zero, cplxVec_one]
        apply Complex.ext <;> simp
      rw [← φ'.toPartialEquiv.image_source_eq_target]
      refine ⟨(D.φ D.j).symm w, ?_, ?_⟩
      · rw [hsrc']; exact hysrc
      · calc φ' ((D.φ D.j).symm w)
            = cplxVec (Complex.I * Work.Drive.N2.chartZ (D.φ D.j) ((D.φ D.j).symm w)) := by
              rw [← cplxVec_chartZ φ' ((D.φ D.j).symm w), hlin' _ hysrc]
          _ = cplxVec (Complex.I * (-(Complex.I * z))) := by rw [hchart]
          _ = cplxVec z := by rw [I_mul_neg_I_mul]
          _ = v := by rw [hz, cplxVec_self]
    have hODE : ∀ (y : M) (t : ℝ),
        (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
        HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 0)
          (Work.Drive.N2.chartMult (D.ρ D.j / 8) (‖φ' (D.Φ (t, y))‖ ^ 2)
            * ((1 : ℝ) * φ' (D.Φ (t, y)) 0)) t ∧
        HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 1)
          (Work.Drive.N2.chartMult (D.ρ D.j / 8) (‖φ' (D.Φ (t, y))‖ ^ 2)
            * ((-1 : ℝ) * φ' (D.Φ (t, y)) 1)) t := by
      intro y t hconf
      have hsrc_t : D.Φ (t, y) ∈ (D.φ D.j).source :=
        D.hCsub D.j (hconf t ⟨min_le_right _ _, le_max_right _ _⟩)
      have hev : ∀ᶠ σ in 𝓝 t, D.Φ (σ, y) ∈ (D.φ D.j).source :=
        (D.hΦsm.continuous.continuousAt.comp (by fun_prop)).eventually
          ((D.φ D.j).open_source.mem_nhds hsrc_t)
      obtain ⟨hd0, hd1⟩ := D.hODE D.j y t hconf
      rw [h1] at hd0
      rw [hs2] at hd1
      constructor
      · have hbase : HasDerivAt (fun σ : ℝ => -(D.φ D.j (D.Φ (σ, y)) 1))
            (-(Work.Drive.N2.chartMult (D.ρ D.j / 8) (‖D.φ D.j (D.Φ (t, y))‖ ^ 2)
              * (1 * D.φ D.j (D.Φ (t, y)) 1))) t := hd1.neg
        have heq0 : (fun σ : ℝ => φ' (D.Φ (σ, y)) 0)
            =ᶠ[𝓝 t] (fun σ => -(D.φ D.j (D.Φ (σ, y)) 1)) := by
          filter_upwards [hev] with σ hσ
          exact (hcoord _ hσ).1
        have h2 := hbase.congr_of_eventuallyEq heq0
        refine h2.congr_deriv ?_
        rw [hnorm_eq _ hsrc_t, (hcoord _ hsrc_t).1]
        ring
      · have hbase : HasDerivAt (fun σ : ℝ => D.φ D.j (D.Φ (σ, y)) 0)
            (Work.Drive.N2.chartMult (D.ρ D.j / 8) (‖D.φ D.j (D.Φ (t, y))‖ ^ 2)
              * (-1 * D.φ D.j (D.Φ (t, y)) 0)) t := hd0
        have heq1 : (fun σ : ℝ => φ' (D.Φ (σ, y)) 1)
            =ᶠ[𝓝 t] (fun σ => D.φ D.j (D.Φ (σ, y)) 0) := by
          filter_upwards [hev] with σ hσ
          exact (hcoord _ hσ).2
        have h2 := hbase.congr_of_eventuallyEq heq1
        refine h2.congr_deriv ?_
        rw [hnorm_eq _ hsrc_t, (hcoord _ hsrc_t).2]
    exact ⟨{ φ' := φ', Zc := Work.Drive.N2.chartZ φ', source_eq := hsrc', ball_eq := hball', Zc_eq := (fun y => rfl), level_eq := (fun y hy => hlev y (by rw [hsrc'] at hy; exact hy)), im_sq_eq := (fun y hy => himsq y (by rw [hsrc'] at hy; exact hy)), target_ball := htarget, ODE := hODE }⟩

/-! ## The four pin arcs and their rows -/

namespace SaddleChart

open scoped Manifold ContDiff Topology

variable {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p}

/-- The anchor-level upper arc: the point of the model chart with `Zc = λ · I √(ηs - i w)`. -/
noncomputable def arcU (S : SaddleChart D) (ηs w : ℝ) : M :=
  S.φ'.symm (cplxVec (((D.ρ D.j / 8 : ℝ)) * (Complex.I * Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I))))

/-- The anchor-level lower arc: the point of the model chart with `Zc = -λ · I √(ηs - i w)`. -/
noncomputable def arcD (S : SaddleChart D) (ηs w : ℝ) : M :=
  S.φ'.symm (cplxVec (((D.ρ D.j / 8 : ℝ)) * (-(Complex.I * Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I)))))

/-- The upper-level right arc: the point of the model chart with `Zc = λ · √(ηs + i w)`. -/
noncomputable def arcR (S : SaddleChart D) (ηs w : ℝ) : M :=
  S.φ'.symm (cplxVec (((D.ρ D.j / 8 : ℝ)) * Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I)))

/-- The upper-level left arc: the point of the model chart with `Zc = -λ · √(ηs + i w)`. -/
noncomputable def arcL (S : SaddleChart D) (ηs w : ℝ) : M :=
  S.φ'.symm (cplxVec (((D.ρ D.j / 8 : ℝ)) * (-(Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I)))))

/-- The norm of an arc vector. -/
lemma norm_arcVec_lt (S : SaddleChart D) {c : ℂ} (hc : ‖c‖ < 8) :
    ‖cplxVec (((D.ρ D.j / 8 : ℝ)) * c)‖ < D.ρ D.j := by
  rw [norm_cplxVec, norm_ofReal_mul (div_nonneg (le_of_lt (D.hρ D.j)) (by norm_num))]
  have hρ := D.hρ D.j
  nlinarith

/-- The norm of the arc vectors in the `.symm` arguments. -/
lemma arcVec_lt (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) (c : ℂ) (hc : ‖c‖ < 2) :
    ‖cplxVec (((D.ρ D.j / 8 : ℝ)) * c)‖ < D.ρ D.j :=
  S.norm_arcVec_lt (by nlinarith)

lemma arcU_Zc (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) :
    S.Zc (S.arcU ηs w)
      = (((D.ρ D.j / 8 : ℝ)) : ℂ)
          * (Complex.I * Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I)) := by
  unfold arcU
  exact S.Zc_arcVec _ (by rw [norm_mul, Complex.norm_I, one_mul]; nlinarith [norm_sqrt_sub_le_two hηs hηs1 hw])

lemma arcD_Zc (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) :
    S.Zc (S.arcD ηs w)
      = (((D.ρ D.j / 8 : ℝ)) : ℂ)
          * (-(Complex.I * Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I))) := by
  unfold arcD
  exact S.Zc_arcVec _ (by
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
    nlinarith [norm_sqrt_sub_le_two hηs hηs1 hw])

lemma arcR_Zc (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) :
    S.Zc (S.arcR ηs w)
      = (((D.ρ D.j / 8 : ℝ)) : ℂ) * Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I) := by
  unfold arcR
  exact S.Zc_arcVec _ (by nlinarith [norm_sqrt_le_two hηs hηs1 hw])

lemma arcL_Zc (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) :
    S.Zc (S.arcL ηs w)
      = (((D.ρ D.j / 8 : ℝ)) : ℂ) * (-(Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I))) := by
  unfold arcL
  exact S.Zc_arcVec _ (by
    rw [norm_neg]
    nlinarith [norm_sqrt_le_two hηs hηs1 hw])

lemma arcU_source (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) : S.arcU ηs w ∈ S.φ'.source := by
  unfold arcU
  exact S.symm_mem_source (S.arcVec_lt hηs hηs1 hw _ (by
    rw [norm_mul, Complex.norm_I, one_mul]
    nlinarith [norm_sqrt_sub_le_two hηs hηs1 hw]))

lemma arcD_source (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) : S.arcD ηs w ∈ S.φ'.source := by
  unfold arcD
  exact S.symm_mem_source (S.arcVec_lt hηs hηs1 hw _ (by
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
    nlinarith [norm_sqrt_sub_le_two hηs hηs1 hw]))

lemma arcR_source (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) : S.arcR ηs w ∈ S.φ'.source := by
  unfold arcR
  exact S.symm_mem_source (S.arcVec_lt hηs hηs1 hw _ (by
    nlinarith [norm_sqrt_le_two hηs hηs1 hw]))

lemma arcL_source (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) : S.arcL ηs w ∈ S.φ'.source := by
  unfold arcL
  exact S.symm_mem_source (S.arcVec_lt hηs hηs1 hw _ (by
    rw [norm_neg]
    nlinarith [norm_sqrt_le_two hηs hηs1 hw]))

open scoped Classical in
/-- The square of a scaled square root. -/
lemma mul_sq_of_sq {r a b : ℝ} {c : ℂ} (hc : c ^ 2 = (a : ℂ) + (b : ℂ) * Complex.I) :
    ((((r : ℝ)) : ℂ) * c) ^ 2 = ((r ^ 2 * a : ℝ) : ℂ) + ((r ^ 2 * b : ℝ) : ℂ) * Complex.I := by
  rw [mul_pow, ← Complex.ofReal_pow, hc]
  push_cast
  ring

/-- The square of `I √(ηs - i w)` (as a root of `-ηs + i w`). -/
lemma sq_I_sqrt {ηs w : ℝ} :
    (Complex.I * Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I)) ^ 2
      = ((-ηs : ℝ) : ℂ) + ((w : ℝ) : ℂ) * Complex.I := by
  have hsq : Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I) ^ 2
      = (ηs : ℂ) - (w : ℂ) * Complex.I := Work.Drive.N2.complex_sqrt_sq _
  rw [mul_pow, Complex.I_sq, neg_one_mul, hsq]
  push_cast
  ring

/-- The square of `√(ηs + i w)`. -/
lemma sq_sqrt_add {ηs w : ℝ} :
    (Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I)) ^ 2
      = ((ηs : ℝ) : ℂ) + ((w : ℝ) : ℂ) * Complex.I :=
  Work.Drive.N2.complex_sqrt_sq _

/-- The imaginary part of `(Zc ·)²` at `arcU`. -/
lemma arcU_imSq (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) :
    ((S.Zc (S.arcU ηs w)) ^ 2).im = ((D.ρ D.j / 8 : ℝ)) ^ 2 * w := by
  rw [S.arcU_Zc hηs hηs1 hw,
    mul_sq_of_sq (sq_I_sqrt (ηs := ηs) (w := w))]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, add_zero, zero_add]

/-- The real part of `(Zc ·)²` at `arcU` (the anchor level). -/
lemma arcU_reSq (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) :
    ((S.Zc (S.arcU ηs w)) ^ 2).re = -(((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs) := by
  rw [S.arcU_Zc hηs hηs1 hw,
    mul_sq_of_sq (sq_I_sqrt (ηs := ηs) (w := w))]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
  try ring

lemma arcU_level (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) :
    f (S.arcU ηs w) = f p - ((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs := by
  rw [S.level_eq _ (S.arcU_source hηs hηs1 hw), S.arcU_reSq hηs hηs1 hw]
  ring

lemma arcR_reSq (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) :
    ((S.Zc (S.arcR ηs w)) ^ 2).re = ((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs := by
  rw [S.arcR_Zc hηs hηs1 hw, mul_sq_of_sq (sq_sqrt_add (ηs := ηs) (w := w))]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
  try ring

lemma arcR_level (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) :
    f (S.arcR ηs w) = f p + ((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs := by
  rw [S.level_eq _ (S.arcR_source hηs hηs1 hw), S.arcR_reSq hηs hηs1 hw]

lemma arcR_imSq (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) :
    ((S.Zc (S.arcR ηs w)) ^ 2).im = ((D.ρ D.j / 8 : ℝ)) ^ 2 * w := by
  rw [S.arcR_Zc hηs hηs1 hw, mul_sq_of_sq (sq_sqrt_add (ηs := ηs) (w := w))]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, add_zero, zero_add]

lemma arcD_Zc_neg (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) : S.Zc (S.arcD ηs w) = -(S.Zc (S.arcU ηs w)) := by
  rw [S.arcD_Zc hηs hηs1 hw, S.arcU_Zc hηs hηs1 hw]
  ring

lemma arcL_Zc_neg (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) : S.Zc (S.arcL ηs w) = -(S.Zc (S.arcR ηs w)) := by
  rw [S.arcL_Zc hηs hηs1 hw, S.arcR_Zc hηs hηs1 hw]
  ring

lemma neg_sq_im (z : ℂ) : ((-z) ^ 2).im = (z ^ 2).im := by rw [neg_sq]
lemma neg_sq_re (z : ℂ) : ((-z) ^ 2).re = (z ^ 2).re := by rw [neg_sq]

lemma arcD_imSq (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) :
    ((S.Zc (S.arcD ηs w)) ^ 2).im = ((D.ρ D.j / 8 : ℝ)) ^ 2 * w := by
  rw [S.arcD_Zc_neg hηs hηs1 hw, neg_sq_im]
  exact S.arcU_imSq hηs hηs1 hw

lemma arcD_reSq (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) :
    ((S.Zc (S.arcD ηs w)) ^ 2).re = -(((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs) := by
  rw [S.arcD_Zc_neg hηs hηs1 hw, neg_sq_re]
  exact S.arcU_reSq hηs hηs1 hw

lemma arcD_level (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) :
    f (S.arcD ηs w) = f p - ((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs := by
  rw [S.level_eq _ (S.arcD_source hηs hηs1 hw), S.arcD_reSq hηs hηs1 hw]
  ring

lemma arcL_reSq (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) :
    ((S.Zc (S.arcL ηs w)) ^ 2).re = ((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs := by
  rw [S.arcL_Zc_neg hηs hηs1 hw, neg_sq_re]
  exact S.arcR_reSq hηs hηs1 hw

lemma arcL_level (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) :
    f (S.arcL ηs w) = f p + ((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs := by
  rw [S.level_eq _ (S.arcL_source hηs hηs1 hw), S.arcL_reSq hηs hηs1 hw]

lemma arcL_imSq (S : SaddleChart D) {ηs w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hw : |w| ≤ 2) :
    ((S.Zc (S.arcL ηs w)) ^ 2).im = ((D.ρ D.j / 8 : ℝ)) ^ 2 * w := by
  rw [S.arcL_Zc_neg hηs hηs1 hw, neg_sq_im]
  exact S.arcR_imSq hηs hηs1 hw

/-- The imaginary part of `(chartZ (φ j) x)²` is twice the product of the coordinates. -/
lemma chartZ_sq_im_eq (y : M) :
    ((Work.Drive.N2.chartZ (D.φ D.j) y) ^ 2).im
      = 2 * (D.φ D.j y 0) * (D.φ D.j y 1) := by
  rw [Work.Drive.N2.chartZ_apply, sq_im]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]

/-- The absolute value of `(Zc x)².im` is (twice) the pin product. -/
lemma Zc_sq_im_abs (S : SaddleChart D) {y : M} (hy : y ∈ S.φ'.source) :
    |((S.Zc y) ^ 2).im| = |2 * (D.φ D.j y 0) * (D.φ D.j y 1)| := by
  have h := S.im_sq_eq y hy
  rw [chartZ_sq_im_eq] at h
  exact (sq_eq_sq_iff_abs_eq_abs _ _).mp h

/-- The natural parametrisation of the anchor level: the square of the coordinate of `arcU`. -/
lemma arcU_sq (S : SaddleChart D) {ηs w : ℝ} (hw2 : |w| ≤ 2) (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1) :
    (S.Zc (S.arcU ηs w)) ^ 2
      = (((-(D.ρ D.j / 8 : ℝ) ^ 2 * ηs) : ℝ) : ℂ)
          + ((((D.ρ D.j / 8 : ℝ) ^ 2 * w : ℝ)) : ℂ) * Complex.I := by
  rw [S.arcU_Zc hηs hηs1 hw2, mul_pow, mul_pow, Complex.I_sq, neg_one_mul,
    Work.Drive.N2.complex_sqrt_sq, ← Complex.ofReal_pow]
  push_cast
  ring

lemma arcU_mem_pin (S : SaddleChart D) {ηs m w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hm0 : 0 ≤ m) (hm2 : m ≤ 2) (hw : |w| ≤ m) :
    S.arcU ηs w ∈ saddlePin D (f p - ((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs) m := by
  have hw2 : |w| ≤ 2 := le_trans hw hm2
  have hsrc := S.arcU_source hηs hηs1 hw2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← S.source_eq]; exact hsrc
  · rw [← S.norm_eq hsrc, ← S.norm_Zc, S.arcU_Zc hηs hηs1 hw2]
    rw [norm_mul, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self (div_nonneg (le_of_lt (D.hρ D.j)) (by norm_num)),
      norm_mul, Complex.norm_I, one_mul]
    have h2 := norm_sqrt_sub_le_two hηs hηs1 hw2
    have hρ := D.hρ D.j
    nlinarith
  · exact S.arcU_level hηs hηs1 hw2
  · rw [← S.Zc_sq_im_abs hsrc, S.arcU_imSq hηs hηs1 hw2, abs_mul,
      abs_of_nonneg (sq_nonneg _)]
    calc ((D.ρ D.j / 8 : ℝ)) ^ 2 * |w| ≤ ((D.ρ D.j / 8 : ℝ)) ^ 2 * m :=
          mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = m * ((D.ρ D.j / 8 : ℝ)) ^ 2 := by ring

lemma arcR_mem_pin (S : SaddleChart D) {ηs m w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hm0 : 0 ≤ m) (hm2 : m ≤ 2) (hw : |w| ≤ m) :
    S.arcR ηs w ∈ saddlePin D (f p + ((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs) m := by
  have hw2 : |w| ≤ 2 := le_trans hw hm2
  have hsrc := S.arcR_source hηs hηs1 hw2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← S.source_eq]; exact hsrc
  · rw [← S.norm_eq hsrc, ← S.norm_Zc, S.arcR_Zc hηs hηs1 hw2]
    rw [norm_mul, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self (div_nonneg (le_of_lt (D.hρ D.j)) (by norm_num))]
    have h2 := norm_sqrt_le_two hηs hηs1 hw2
    have hρ := D.hρ D.j
    nlinarith
  · exact S.arcR_level hηs hηs1 hw2
  · rw [← S.Zc_sq_im_abs hsrc, S.arcR_imSq hηs hηs1 hw2, abs_mul,
      abs_of_nonneg (sq_nonneg _)]
    calc ((D.ρ D.j / 8 : ℝ)) ^ 2 * |w| ≤ ((D.ρ D.j / 8 : ℝ)) ^ 2 * m :=
          mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = m * ((D.ρ D.j / 8 : ℝ)) ^ 2 := by ring

lemma arcD_mem_pin (S : SaddleChart D) {ηs m w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hm0 : 0 ≤ m) (hm2 : m ≤ 2) (hw : |w| ≤ m) :
    S.arcD ηs w ∈ saddlePin D (f p - ((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs) m := by
  have hw2 : |w| ≤ 2 := le_trans hw hm2
  have hsrc := S.arcD_source hηs hηs1 hw2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← S.source_eq]; exact hsrc
  · rw [← S.norm_eq hsrc, ← S.norm_Zc, S.arcD_Zc hηs hηs1 hw2]
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self (div_nonneg (le_of_lt (D.hρ D.j)) (by norm_num)),
      Complex.norm_I, one_mul]
    have h2 := norm_sqrt_sub_le_two hηs hηs1 hw2
    have hρ := D.hρ D.j
    nlinarith
  · exact S.arcD_level hηs hηs1 hw2
  · rw [← S.Zc_sq_im_abs hsrc, S.arcD_imSq hηs hηs1 hw2, abs_mul,
      abs_of_nonneg (sq_nonneg _)]
    calc ((D.ρ D.j / 8 : ℝ)) ^ 2 * |w| ≤ ((D.ρ D.j / 8 : ℝ)) ^ 2 * m :=
          mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = m * ((D.ρ D.j / 8 : ℝ)) ^ 2 := by ring

lemma arcL_mem_pin (S : SaddleChart D) {ηs m w : ℝ} (hηs : 0 ≤ ηs) (hηs1 : ηs ≤ 1)
    (hm0 : 0 ≤ m) (hm2 : m ≤ 2) (hw : |w| ≤ m) :
    S.arcL ηs w ∈ saddlePin D (f p + ((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs) m := by
  have hw2 : |w| ≤ 2 := le_trans hw hm2
  have hsrc := S.arcL_source hηs hηs1 hw2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← S.source_eq]; exact hsrc
  · rw [← S.norm_eq hsrc, ← S.norm_Zc, S.arcL_Zc hηs hηs1 hw2]
    rw [norm_mul, norm_neg, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self (div_nonneg (le_of_lt (D.hρ D.j)) (by norm_num))]

    have h2 := norm_sqrt_le_two hηs hηs1 hw2
    have hρ := D.hρ D.j
    nlinarith
  · exact S.arcL_level hηs hηs1 hw2
  · rw [← S.Zc_sq_im_abs hsrc, S.arcL_imSq hηs hηs1 hw2, abs_mul,
      abs_of_nonneg (sq_nonneg _)]
    calc ((D.ρ D.j / 8 : ℝ)) ^ 2 * |w| ≤ ((D.ρ D.j / 8 : ℝ)) ^ 2 * m :=
          mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = m * ((D.ρ D.j / 8 : ℝ)) ^ 2 := by ring

/-- **The classification of the anchor pin**: every point of the pin at the anchor level lies on
one of the two arcs `arcU`, `arcD`. -/
lemma pin_eq_arcs (S : SaddleChart D) {ηs m : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1)
    (hm0 : 0 ≤ m) (hm2 : m ≤ 2)
    {x : M} (hx : x ∈ saddlePin D (f p - ((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs) m) :
    ∃ w : ℝ, |w| ≤ m ∧ (x = S.arcU ηs w ∨ x = S.arcD ηs w) := by
  obtain ⟨hxsrc, hxnorm, hxval, hxin⟩ := hx
  have hx' : x ∈ S.φ'.source := by rw [S.source_eq]; exact hxsrc
  have hlam : 0 < (D.ρ D.j / 8 : ℝ) := div_pos (D.hρ D.j) (by norm_num)
  have hlam2 : 0 < ((D.ρ D.j / 8 : ℝ)) ^ 2 := pow_pos hlam 2
  have hre : ((S.Zc x) ^ 2).re = -(((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs) := by
    have h := S.level_eq x hx'
    rw [hxval] at h
    linarith
  set w : ℝ := ((S.Zc x) ^ 2).im / ((D.ρ D.j / 8 : ℝ)) ^ 2 with hwdef
  have hw_eq : ((D.ρ D.j / 8 : ℝ)) ^ 2 * w = ((S.Zc x) ^ 2).im := by
    rw [hwdef, mul_div_cancel₀ _ (ne_of_gt hlam2)]
  have himabs : |((S.Zc x) ^ 2).im| ≤ m * ((D.ρ D.j / 8 : ℝ)) ^ 2 := by
    rw [S.Zc_sq_im_abs hx']
    exact hxin
  have hw : |w| ≤ m := by
    rw [hwdef, abs_div, abs_of_pos hlam2, div_le_iff₀ hlam2]
    exact himabs
  have hsquare : (S.Zc x) ^ 2 = (S.Zc (S.arcU ηs w)) ^ 2 := by
    have h1 := S.arcU_sq (ηs := ηs) (w := w) (le_trans hw hm2) hηs.le hηs1
    have h2 : (S.Zc x) ^ 2
        = (((-(D.ρ D.j / 8 : ℝ) ^ 2 * ηs) : ℝ) : ℂ)
            + ((((S.Zc x) ^ 2).im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, hre]
        try ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
    rw [h1, h2, hw_eq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with h | h
  · exact ⟨w, hw, Or.inl (S.injOn_Zc hx' (S.arcU_source hηs.le hηs1 (le_trans hw hm2)) h)⟩
  · refine ⟨w, hw, Or.inr ?_⟩
    refine S.injOn_Zc hx' (S.arcD_source hηs.le hηs1 (le_trans hw hm2)) ?_
    rw [S.arcD_Zc hηs.le hηs1 (le_trans hw hm2), h,
      S.arcU_Zc hηs.le hηs1 (le_trans hw hm2)]
    ring

end SaddleChart



/-! ## Continuity and injectivity of the arcs -/

namespace SaddleChart

open scoped Manifold ContDiff Topology

variable {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p}

lemma continuous_cplxVec : Continuous cplxVec := by
  have h : Continuous (fun z : ℂ => (![z.re, z.im] : Fin 2 → ℝ)) := by
    rw [continuous_pi_iff]
    intro i
    fin_cases i
    · simpa using Complex.continuous_re
    · simpa using Complex.continuous_im
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp h

/-- `w ↦ √(ηs - i w)` is continuous on the interval (the argument stays in the open right half
plane). -/
lemma continuousOn_sqrtMinus {ηs : ℝ} (hηs : 0 < ηs) :
    ContinuousOn (fun w : ℝ => Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I))
      (Set.Icc (-2) 2) := by
  refine ContinuousOn.comp Complex.continuousOn_sqrt ?_ ?_
  · exact (by fun_prop : Continuous (fun w : ℝ => (ηs : ℂ) - (w : ℂ) * Complex.I)).continuousOn
  · intro w hw
    rw [Complex.mem_slitPlane_iff]
    left
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]
    exact hηs

/-- `w ↦ √(ηs + i w)`. -/
lemma continuousOn_sqrtPlus {ηs : ℝ} (hηs : 0 < ηs) :
    ContinuousOn (fun w : ℝ => Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I))
      (Set.Icc (-2) 2) := by
  refine ContinuousOn.comp Complex.continuousOn_sqrt ?_ ?_
  · exact (by fun_prop : Continuous (fun w : ℝ => (ηs : ℂ) + (w : ℂ) * Complex.I)).continuousOn
  · intro w hw
    rw [Complex.mem_slitPlane_iff]
    left
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    exact hηs

/-- The four vector maps of the arcs are continuous on the interval. -/
lemma continuousOn_arcVecU (S : SaddleChart D) {ηs : ℝ} (hηs : 0 < ηs) :
    ContinuousOn (fun w : ℝ => cplxVec
      (((D.ρ D.j / 8 : ℝ)) *
        (Complex.I * Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I)))) (Set.Icc (-2) 2) := by
  have hg : Continuous (fun z : ℂ =>
      cplxVec (((D.ρ D.j / 8 : ℝ)) * (Complex.I * z))) :=
    continuous_cplxVec.comp (continuous_const.mul (continuous_const.mul continuous_id))
  have hfun : (fun w : ℝ => cplxVec
        (((D.ρ D.j / 8 : ℝ)) * (Complex.I * Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I))))
      = (fun z : ℂ => cplxVec (((D.ρ D.j / 8 : ℝ)) * (Complex.I * z)))
        ∘ (fun w : ℝ => Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I)) := rfl
  rw [hfun]
  exact ContinuousOn.comp hg.continuousOn (continuousOn_sqrtMinus hηs)
    (fun w hw => Set.mem_univ _)

lemma continuousOn_arcVecD (S : SaddleChart D) {ηs : ℝ} (hηs : 0 < ηs) :
    ContinuousOn (fun w : ℝ => cplxVec
      (((D.ρ D.j / 8 : ℝ)) *
        (-(Complex.I * Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I))))) (Set.Icc (-2) 2) := by
  have hg : Continuous (fun z : ℂ =>
      cplxVec (((D.ρ D.j / 8 : ℝ)) * (-(Complex.I * z)))) :=
    continuous_cplxVec.comp (continuous_const.mul
      ((continuous_const.mul continuous_id).neg))
  have hfun : (fun w : ℝ => cplxVec
        (((D.ρ D.j / 8 : ℝ)) *
          (-(Complex.I * Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I)))))
      = (fun z : ℂ => cplxVec (((D.ρ D.j / 8 : ℝ)) * (-(Complex.I * z))))
        ∘ (fun w : ℝ => Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I)) := rfl
  rw [hfun]
  exact ContinuousOn.comp hg.continuousOn (continuousOn_sqrtMinus hηs)
    (fun w hw => Set.mem_univ _)

lemma continuousOn_arcVecR (S : SaddleChart D) {ηs : ℝ} (hηs : 0 < ηs) :
    ContinuousOn (fun w : ℝ => cplxVec
      (((D.ρ D.j / 8 : ℝ)) * Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I)))
      (Set.Icc (-2) 2) := by
  have hg : Continuous (fun z : ℂ => cplxVec (((D.ρ D.j / 8 : ℝ)) * z)) :=
    continuous_cplxVec.comp (continuous_const.mul continuous_id)
  have hfun : (fun w : ℝ => cplxVec
        (((D.ρ D.j / 8 : ℝ)) * Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I)))
      = (fun z : ℂ => cplxVec (((D.ρ D.j / 8 : ℝ)) * z))
        ∘ (fun w : ℝ => Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I)) := rfl
  rw [hfun]
  exact ContinuousOn.comp hg.continuousOn (continuousOn_sqrtPlus hηs)
    (fun w hw => Set.mem_univ _)

lemma continuousOn_arcVecL (S : SaddleChart D) {ηs : ℝ} (hηs : 0 < ηs) :
    ContinuousOn (fun w : ℝ => cplxVec
      (((D.ρ D.j / 8 : ℝ)) *
        (-(Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I))))) (Set.Icc (-2) 2) := by
  have hg : Continuous (fun z : ℂ => cplxVec (((D.ρ D.j / 8 : ℝ)) * (-z))) :=
    continuous_cplxVec.comp (continuous_const.mul continuous_id.neg)
  have hfun : (fun w : ℝ => cplxVec
        (((D.ρ D.j / 8 : ℝ)) * (-(Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I)))))
      = (fun z : ℂ => cplxVec (((D.ρ D.j / 8 : ℝ)) * (-z)))
        ∘ (fun w : ℝ => Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I)) := rfl
  rw [hfun]
  exact ContinuousOn.comp hg.continuousOn (continuousOn_sqrtPlus hηs)
    (fun w hw => Set.mem_univ _)

lemma continuousOn_arcU (S : SaddleChart D) {ηs : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) :
    ContinuousOn (fun w : ℝ => S.arcU ηs w) (Set.Icc (-2) 2) := by
  change ContinuousOn (fun w : ℝ => S.φ'.symm (cplxVec
    (((D.ρ D.j / 8 : ℝ)) *
      (Complex.I * Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I))))) (Set.Icc (-2) 2)
  refine ContinuousOn.comp (S.φ'.continuousOn_symm) (S.continuousOn_arcVecU hηs) ?_
  intro w hw
  have hw2 : |w| ≤ 2 := by rw [abs_le]; exact ⟨hw.1, hw.2⟩
  refine S.target_ball _ (S.norm_arcVec_lt ?_)
  rw [norm_mul, Complex.norm_I, one_mul]
  exact lt_of_lt_of_le (norm_sqrt_sub_le_two (le_of_lt hηs) hηs1 hw2) (by norm_num)

lemma continuousOn_arcD (S : SaddleChart D) {ηs : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) :
    ContinuousOn (fun w : ℝ => S.arcD ηs w) (Set.Icc (-2) 2) := by
  change ContinuousOn (fun w : ℝ => S.φ'.symm (cplxVec
    (((D.ρ D.j / 8 : ℝ)) *
      (-(Complex.I * Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I)))))) (Set.Icc (-2) 2)
  refine ContinuousOn.comp (S.φ'.continuousOn_symm) (S.continuousOn_arcVecD hηs) ?_
  intro w hw
  have hw2 : |w| ≤ 2 := by rw [abs_le]; exact ⟨hw.1, hw.2⟩
  refine S.target_ball _ (S.norm_arcVec_lt ?_)
  rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
  exact lt_of_lt_of_le (norm_sqrt_sub_le_two (le_of_lt hηs) hηs1 hw2) (by norm_num)

lemma continuousOn_arcR (S : SaddleChart D) {ηs : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) :
    ContinuousOn (fun w : ℝ => S.arcR ηs w) (Set.Icc (-2) 2) := by
  change ContinuousOn (fun w : ℝ => S.φ'.symm (cplxVec
    (((D.ρ D.j / 8 : ℝ)) * Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I))))
    (Set.Icc (-2) 2)
  refine ContinuousOn.comp (S.φ'.continuousOn_symm) (S.continuousOn_arcVecR hηs) ?_
  intro w hw
  have hw2 : |w| ≤ 2 := by rw [abs_le]; exact ⟨hw.1, hw.2⟩
  refine S.target_ball _ (S.norm_arcVec_lt ?_)
  exact lt_of_lt_of_le (norm_sqrt_le_two (le_of_lt hηs) hηs1 hw2) (by norm_num)

lemma continuousOn_arcL (S : SaddleChart D) {ηs : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) :
    ContinuousOn (fun w : ℝ => S.arcL ηs w) (Set.Icc (-2) 2) := by
  change ContinuousOn (fun w : ℝ => S.φ'.symm (cplxVec
    (((D.ρ D.j / 8 : ℝ)) * (-(Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I))))))
    (Set.Icc (-2) 2)
  refine ContinuousOn.comp (S.φ'.continuousOn_symm) (S.continuousOn_arcVecL hηs) ?_
  intro w hw
  have hw2 : |w| ≤ 2 := by rw [abs_le]; exact ⟨hw.1, hw.2⟩
  refine S.target_ball _ (S.norm_arcVec_lt ?_)
  rw [norm_neg]
  exact lt_of_lt_of_le (norm_sqrt_le_two (le_of_lt hηs) hηs1 hw2) (by norm_num)

/-- **The anchor arcs are injective in the parameter** (the coordinate `Zc` determines `w`). -/
lemma injOn_arcU (S : SaddleChart D) {ηs : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) :
    Set.InjOn (fun w : ℝ => S.arcU ηs w) (Set.Icc (-2) 2) := by
  have hlamne : (((D.ρ D.j / 8 : ℝ)) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (div_pos (D.hρ D.j) (by norm_num))
  intro w hw w' hw' h
  have hw2 : |w| ≤ 2 := by rw [abs_le]; exact ⟨hw.1, hw.2⟩
  have hw2' : |w'| ≤ 2 := by rw [abs_le]; exact ⟨hw'.1, hw'.2⟩
  have h1 := S.arcU_Zc (le_of_lt hηs) hηs1 hw2
  have h2 := S.arcU_Zc (le_of_lt hηs) hηs1 hw2'
  have h3 : S.Zc (S.arcU ηs w) = S.Zc (S.arcU ηs w') := congrArg S.Zc h
  have hZ : (((D.ρ D.j / 8 : ℝ)) : ℂ) * (Complex.I * Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I))
      = (((D.ρ D.j / 8 : ℝ)) : ℂ) * (Complex.I * Complex.sqrt ((ηs : ℂ) - (w' : ℂ) * Complex.I)) :=
    h1.symm.trans (h3.trans h2)
  have h2 : Complex.I * Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I)
      = Complex.I * Complex.sqrt ((ηs : ℂ) - (w' : ℂ) * Complex.I) :=
    mul_left_cancel₀ hlamne hZ
  have h3 : Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I)
      = Complex.sqrt ((ηs : ℂ) - (w' : ℂ) * Complex.I) :=
    mul_left_cancel₀ Complex.I_ne_zero h2
  have h4 : ((ηs : ℂ) - (w : ℂ) * Complex.I) = ((ηs : ℂ) - (w' : ℂ) * Complex.I) := by
    have := congrArg (fun z : ℂ => z ^ 2) h3
    simpa only [Work.Drive.N2.complex_sqrt_sq] using this
  have him := congrArg Complex.im h4
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_one, zero_add, neg_inj] at him
  linarith [him]

lemma injOn_arcR (S : SaddleChart D) {ηs : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) :
    Set.InjOn (fun w : ℝ => S.arcR ηs w) (Set.Icc (-2) 2) := by
  intro w hw w' hw' h
  have hw2 : |w| ≤ 2 := by rw [abs_le]; exact ⟨hw.1, hw.2⟩
  have hw2' : |w'| ≤ 2 := by rw [abs_le]; exact ⟨hw'.1, hw'.2⟩
  have hlamne : (((D.ρ D.j / 8 : ℝ)) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (div_pos (D.hρ D.j) (by norm_num))
  have h5 := S.arcR_Zc (le_of_lt hηs) hηs1 hw2
  have h6 := S.arcR_Zc (le_of_lt hηs) hηs1 hw2'
  have h7 : S.Zc (S.arcR ηs w) = S.Zc (S.arcR ηs w') := congrArg S.Zc h
  have hZ : (((D.ρ D.j / 8 : ℝ)) : ℂ) * Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I)
      = (((D.ρ D.j / 8 : ℝ)) : ℂ) * Complex.sqrt ((ηs : ℂ) + (w' : ℂ) * Complex.I) :=
    h5.symm.trans (h7.trans h6)
  have hs : Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I)
      = Complex.sqrt ((ηs : ℂ) + (w' : ℂ) * Complex.I) := mul_left_cancel₀ hlamne hZ
  have h4 : ((ηs : ℂ) + (w : ℂ) * Complex.I) = ((ηs : ℂ) + (w' : ℂ) * Complex.I) := by
    have := congrArg (fun z : ℂ => z ^ 2) hs
    simpa only [Work.Drive.N2.complex_sqrt_sq] using this
  have him := congrArg Complex.im h4
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_one, zero_add] at him
  linarith [him]

end SaddleChart

end Work.Drive.N2Lead
