import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddVolterra.Kernel.G2Deriv

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

set_option maxHeartbeats 2000000

namespace Work.OddVolterra.Existence

variable {h : ℝ → ℝ}

/-- The negative endpoint map `σ ↦ -(Z σ 0)`. -/
def tneg (Z : ℝ → Work.OddVolterra.St) : ℝ → ℝ := fun σ => -(Z σ 0)

/-- The positive endpoint map `σ ↦ Z σ 1`. -/
def tpos (Z : ℝ → Work.OddVolterra.St) : ℝ → ℝ := fun σ => Z σ 1

@[simp] lemma tneg_apply (Z : ℝ → Work.OddVolterra.St) (σ : ℝ) : tneg Z σ = -(Z σ 0) := rfl
@[simp] lemma tpos_apply (Z : ℝ → Work.OddVolterra.St) (σ : ℝ) : tpos Z σ = Z σ 1 := rfl

/-- Bound on the state on the slope window. -/
lemma exists_state_bound {Z : ℝ → Work.OddVolterra.St} {s : ℝ}
    (hZ : ContinuousOn Z (Set.Icc s 1)) :
    ∃ M : ℝ, 0 < M ∧ ∀ σ ∈ Set.Icc s 1, ∀ i : Fin 4, |Z σ i| ≤ M := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hZ
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right C 1), fun σ hσ i => ?_⟩
  calc |Z σ i| = ‖Z σ i‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖Z σ‖ := norm_le_pi_norm _ _
    _ ≤ C := hC σ hσ
    _ ≤ max C 1 := le_max_left C 1

/-- `k1ext` is differentiable in its last argument wherever the radicand is positive. -/
lemma differentiableAt_k1ext (n : ℕ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) {σ t a : ℝ}
    (hR : 0 < Work.OddVolterra.krad h σ t a) :
    DifferentiableAt ℝ (fun u : ℝ => Work.OddVolterra.k1ext n h σ t u) a := by
  have hU : IsOpen {q : (ℝ × ℝ) × ℝ | 0 < Work.OddVolterra.krad h q.1.1 q.1.2 q.2} :=
    Work.OddVolterra.isOpen_extGood h hh
  have hdiff : DifferentiableAt ℝ
      (fun q : (ℝ × ℝ) × ℝ => Work.OddVolterra.k1ext n h q.1.1 q.1.2 q.2) ((σ, t), a) :=
    ((Work.OddVolterra.contDiffOn_k1ext n hh).differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds hR)
  have hinner : DifferentiableAt ℝ (fun u : ℝ => ((σ, t), u)) a :=
    (hasFDerivAt_prodMk_right (σ, t) a).differentiableAt
  have := hdiff.comp a hinner
  simpa [Function.comp_def] using this

/-- `k2ext` is differentiable in its last argument wherever the radicand is positive. -/
lemma differentiableAt_k2ext (n : ℕ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) {σ t a : ℝ}
    (hR : 0 < Work.OddVolterra.krad h σ t a) :
    DifferentiableAt ℝ (fun u : ℝ => Work.OddVolterra.k2ext n h σ t u) a := by
  have hU : IsOpen {q : (ℝ × ℝ) × ℝ | 0 < Work.OddVolterra.krad h q.1.1 q.1.2 q.2} :=
    Work.OddVolterra.isOpen_extGood h hh
  have hdiff : DifferentiableAt ℝ
      (fun q : (ℝ × ℝ) × ℝ => Work.OddVolterra.k2ext n h q.1.1 q.1.2 q.2) ((σ, t), a) :=
    ((Work.OddVolterra.contDiffOn_k2ext n hh).differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds hR)
  have hinner : DifferentiableAt ℝ (fun u : ℝ => ((σ, t), u)) a :=
    (hasFDerivAt_prodMk_right (σ, t) a).differentiableAt
  have := hdiff.comp a hinner
  simpa [Function.comp_def] using this

/-- The Abel kernels are differentiable in their first argument off the diagonal, on the
positivity region. -/
lemma differentiableAt_K1 (n : ℕ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) {σ t a : ℝ} (ha : a < σ)
    (hR : 0 < Work.OddVolterra.krad h σ t a) :
    DifferentiableAt ℝ (fun u : ℝ => Work.OddVolterra.K1 n h u σ t) a := by
  have hnhds : {u : ℝ | u < σ ∧ 0 < Work.OddVolterra.krad h σ t u} ∈ 𝓝 a :=
    ((isOpen_lt continuous_id continuous_const).inter
      (isOpen_lt continuous_const (Work.OddVolterra.continuous_krad hh σ t))).mem_nhds
        ⟨ha, hR⟩
  have heq : (fun u : ℝ => Work.OddVolterra.K1 n h u σ t)
      =ᶠ[𝓝 a] (fun u : ℝ => Work.OddVolterra.k1ext n h σ t u) := by
    filter_upwards [hnhds] with u hu
    exact Work.OddVolterra.K1_eq_k1ext hh n hu.1 hu.2
  exact (differentiableAt_k1ext n hh hR).congr_of_eventuallyEq heq

lemma differentiableAt_K2 (n : ℕ) (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h) {σ t a : ℝ}
    (ha : a < σ) (hR : 0 < Work.OddVolterra.krad h σ t a) :
    DifferentiableAt ℝ (fun u : ℝ => Work.OddVolterra.K2 n h u σ t) a := by
  have hnhds : {u : ℝ | u < σ ∧ 0 < Work.OddVolterra.krad h σ t u} ∈ 𝓝 a :=
    ((isOpen_lt continuous_id continuous_const).inter
      (isOpen_lt continuous_const (Work.OddVolterra.continuous_krad hh σ t))).mem_nhds
        ⟨ha, hR⟩
  have heq : (fun u : ℝ => Work.OddVolterra.K2 n h u σ t)
      =ᶠ[𝓝 a] (fun u : ℝ => Work.OddVolterra.k2ext n h σ t u) := by
    filter_upwards [hnhds] with u hu
    exact Work.OddVolterra.K2_eq_k2ext hh n hn hu.1 hu.2
  exact (differentiableAt_k2ext n hh hR).congr_of_eventuallyEq heq

/-- Differentiability of the two-component kernel in its first argument. -/
lemma differentiableAt_Kvec (n : ℕ) (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h) {σ : ℝ}
    (z : Work.OddVolterra.St) {a : ℝ} (ha : a < σ)
    (h1 : 0 < Work.OddVolterra.krad h σ (-(z 0)) a)
    (h2 : 0 < Work.OddVolterra.krad h σ (z 1) a) :
    DifferentiableAt ℝ (fun u : ℝ =>
      Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a := by
  have hd1 := differentiableAt_K1 (h := h) n hh ha h1
  have hd2 := differentiableAt_K2 (h := h) n hn hh ha h1
  have hd3 := differentiableAt_K1 (h := h) n hh ha h2
  have hd4 := differentiableAt_K2 (h := h) n hn hh ha h2
  rw [differentiableAt_pi]
  intro i
  fin_cases i
  · simp only [Work.OddVolterra.Kvec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    exact (((hd1.mul_const (z 2)).add (hd3.mul_const (z 3)))).neg
  · simp only [Work.OddVolterra.Kvec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    exact (((hd2.mul_const (z 2)).add (hd4.mul_const (z 3)))).neg


/-- The region where `K₁`, `K₂` are given by their smooth diagonal extensions, in the
`((a,σ),t)` coordinates: `a < σ` and `krad h σ t a > 0`. -/
def goodRegion (h : ℝ → ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {q : (ℝ × ℝ) × ℝ | q.1.1 < q.1.2 ∧ 0 < Work.OddVolterra.krad h q.1.2 q.2 q.1.1}

lemma isOpen_goodRegion (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    IsOpen (goodRegion h) := by
  have hm : Continuous (fun q : (ℝ × ℝ) × ℝ => ((q.1.2, q.2), q.1.1)) := by fun_prop
  have h1 : IsOpen {q : (ℝ × ℝ) × ℝ | q.1.1 < q.1.2} :=
    isOpen_lt (by fun_prop : Continuous fun q : (ℝ × ℝ) × ℝ => q.1.1)
      (by fun_prop : Continuous fun q : (ℝ × ℝ) × ℝ => q.1.2)
  have h2 : IsOpen ((fun q : (ℝ × ℝ) × ℝ => ((q.1.2, q.2), q.1.1)) ⁻¹' (Work.OddVolterra.extGood h)) :=
    hm.isOpen_preimage _ (Work.OddVolterra.isOpen_extGood h hh)
  have h3 : goodRegion h = {q : (ℝ × ℝ) × ℝ | q.1.1 < q.1.2} ∩
      ((fun q : (ℝ × ℝ) × ℝ => ((q.1.2, q.2), q.1.1)) ⁻¹' (Work.OddVolterra.extGood h)) := rfl
  rw [h3]
  exact h1.inter h2

/-- Continuity of the first-argument derivative of `K₁` on the good region. -/
lemma continuousOn_deriv_K1_region (n : ℕ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
        deriv (fun u : ℝ => Work.OddVolterra.K1 n h u q.1.2 q.2) q.1.1) (goodRegion h) := by
  set V : Set ((ℝ × ℝ) × ℝ) := {q : (ℝ × ℝ) × ℝ | 0 < Work.OddVolterra.krad h q.1.1 q.1.2 q.2}
    with hVdef
  have hV : V = Work.OddVolterra.extGood h := rfl
  have hm : Continuous (fun q : (ℝ × ℝ) × ℝ => ((q.1.2, q.2), q.1.1)) := by fun_prop
  have hExtV : ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
      deriv (fun u : ℝ => Work.OddVolterra.k1ext n h q.1.1 q.1.2 u) q.2) V :=
    (Work.OddVolterra.contDiffOn_deriv_snd_gen (Work.OddVolterra.isOpen_extGood h hh)
      (Work.OddVolterra.contDiffOn_k1ext n hh)).continuousOn
  have hcomp : ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
      deriv (fun u : ℝ => Work.OddVolterra.k1ext n h q.1.2 q.2 u) q.1.1) (goodRegion h) := by
    have hMT : MapsTo (fun q : (ℝ × ℝ) × ℝ => ((q.1.2, q.2), q.1.1)) (goodRegion h) V :=
      fun q hq => hq.2
    have := hExtV.comp hm.continuousOn hMT
    simpa [Function.comp_def] using this
  refine hcomp.congr ?_
  intro q hq
  have hR : 0 < Work.OddVolterra.krad h q.1.2 q.2 q.1.1 := hq.2
  have hlt : q.1.1 < q.1.2 := hq.1
  have hnhds : {u : ℝ | u < q.1.2 ∧ 0 < Work.OddVolterra.krad h q.1.2 q.2 u} ∈ 𝓝 q.1.1 :=
    ((isOpen_lt continuous_id continuous_const).inter
      (isOpen_lt continuous_const (Work.OddVolterra.continuous_krad hh q.1.2 q.2))).mem_nhds
        ⟨hlt, hR⟩
  have heqv : (fun u : ℝ => Work.OddVolterra.K1 n h u q.1.2 q.2) =ᶠ[𝓝 q.1.1]
      (fun u : ℝ => Work.OddVolterra.k1ext n h q.1.2 q.2 u) := by
    filter_upwards [hnhds] with u hu
    exact Work.OddVolterra.K1_eq_k1ext hh n hu.1 hu.2
  exact heqv.deriv_eq

/-- Continuity of the first-argument derivative of `K₂` on the good region. -/
lemma continuousOn_deriv_K2_region (n : ℕ) (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
        deriv (fun u : ℝ => Work.OddVolterra.K2 n h u q.1.2 q.2) q.1.1) (goodRegion h) := by
  set V : Set ((ℝ × ℝ) × ℝ) := {q : (ℝ × ℝ) × ℝ | 0 < Work.OddVolterra.krad h q.1.1 q.1.2 q.2}
    with hVdef
  have hm : Continuous (fun q : (ℝ × ℝ) × ℝ => ((q.1.2, q.2), q.1.1)) := by fun_prop
  have hExtV : ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
      deriv (fun u : ℝ => Work.OddVolterra.k2ext n h q.1.1 q.1.2 u) q.2) V :=
    (Work.OddVolterra.contDiffOn_deriv_snd_gen (Work.OddVolterra.isOpen_extGood h hh)
      (Work.OddVolterra.contDiffOn_k2ext n hh)).continuousOn
  have hcomp : ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
      deriv (fun u : ℝ => Work.OddVolterra.k2ext n h q.1.2 q.2 u) q.1.1) (goodRegion h) := by
    have hMT : MapsTo (fun q : (ℝ × ℝ) × ℝ => ((q.1.2, q.2), q.1.1)) (goodRegion h) V :=
      fun q hq => hq.2
    have := hExtV.comp hm.continuousOn hMT
    simpa [Function.comp_def] using this
  refine hcomp.congr ?_
  intro q hq
  have hR : 0 < Work.OddVolterra.krad h q.1.2 q.2 q.1.1 := hq.2
  have hlt : q.1.1 < q.1.2 := hq.1
  have hnhds : {u : ℝ | u < q.1.2 ∧ 0 < Work.OddVolterra.krad h q.1.2 q.2 u} ∈ 𝓝 q.1.1 :=
    ((isOpen_lt continuous_id continuous_const).inter
      (isOpen_lt continuous_const (Work.OddVolterra.continuous_krad hh q.1.2 q.2))).mem_nhds
        ⟨hlt, hR⟩
  have heqv : (fun u : ℝ => Work.OddVolterra.K2 n h u q.1.2 q.2) =ᶠ[𝓝 q.1.1]
      (fun u : ℝ => Work.OddVolterra.k2ext n h q.1.2 q.2 u) := by
    filter_upwards [hnhds] with u hu
    exact Work.OddVolterra.K2_eq_k2ext hh n hn hu.1 hu.2
  exact heqv.deriv_eq


/-- The region on which the two Abel kernels are given by their smooth diagonal extensions,
in the `(a,σ,z)` coordinates used by `Kvec`. -/
def kvecRegion (h : ℝ → ℝ) : Set ((ℝ × ℝ) × Work.OddVolterra.St) :=
  {p : (ℝ × ℝ) × Work.OddVolterra.St |
    p.1.1 < p.1.2 ∧ 0 < Work.OddVolterra.krad h p.1.2 (-(p.2 0)) p.1.1 ∧
      0 < Work.OddVolterra.krad h p.1.2 (p.2 1) p.1.1}

/-- The first-argument derivative of `Kvec` on the region where the two kernels are given by
their smooth diagonal extensions. -/
lemma deriv_Kvec_eq (n : ℕ) (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h) {σ a : ℝ}
    (z : Work.OddVolterra.St) (ha : a < σ)
    (h1 : 0 < Work.OddVolterra.krad h σ (-(z 0)) a)
    (h2 : 0 < Work.OddVolterra.krad h σ (z 1) a) :
    deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a =
      ![ - (deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (-(z 0))) a * z 2 +
              deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (z 1)) a * z 3),
          - (deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (-(z 0))) a * z 2 +
              deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (z 1)) a * z 3) ] := by
  have hd1 := differentiableAt_K1 (h := h) n hh ha h1
  have hd2 := differentiableAt_K2 (h := h) n hn hh ha h1
  have hd3 := differentiableAt_K1 (h := h) n hh ha h2
  have hd4 := differentiableAt_K2 (h := h) n hn hh ha h2
  have hcomp0 : HasDerivAt (fun u : ℝ =>
      -(Work.OddVolterra.K1 n h u σ (-(z 0)) * z 2 + Work.OddVolterra.K1 n h u σ (z 1) * z 3))
      (-(deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (-(z 0))) a * z 2 +
          deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (z 1)) a * z 3)) a := by
    refine (((hd1.hasDerivAt.mul_const (z 2)).add
      (hd3.hasDerivAt.mul_const (z 3))).neg).congr_deriv ?_
    ring
  have hcomp1 : HasDerivAt (fun u : ℝ =>
      -(Work.OddVolterra.K2 n h u σ (-(z 0)) * z 2 + Work.OddVolterra.K2 n h u σ (z 1) * z 3))
      (-(deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (-(z 0))) a * z 2 +
          deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (z 1)) a * z 3)) a := by
    refine (((hd2.hasDerivAt.mul_const (z 2)).add
      (hd4.hasDerivAt.mul_const (z 3))).neg).congr_deriv ?_
    ring
  have hpi := deriv_pi (𝕜 := ℝ) (x := a)
    (φ := fun u : ℝ => Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
    (fun i => by
      fin_cases i
      · simpa [Work.OddVolterra.Kvec] using hcomp0.differentiableAt
      · simpa [Work.OddVolterra.Kvec] using hcomp1.differentiableAt)
  rw [hpi]
  funext i
  fin_cases i
  · simpa [Work.OddVolterra.Kvec] using hcomp0.deriv
  · simpa [Work.OddVolterra.Kvec] using hcomp1.deriv

/-- **Joint continuity of the first-argument derivative field of `Kvec`.** -/
theorem continuousOn_deriv_Kvec (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContinuousOn (fun p : (ℝ × ℝ) × Work.OddVolterra.St =>
        deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u p.1.2 (p.2 0) (p.2 1) (p.2 2) (p.2 3)) p.1.1)
      (kvecRegion h) := by
  have hmaps0 : Continuous (fun p : (ℝ × ℝ) × Work.OddVolterra.St =>
      ((p.1.1, p.1.2), -(p.2 0))) := by fun_prop
  have hmaps1 : Continuous (fun p : (ℝ × ℝ) × Work.OddVolterra.St =>
      ((p.1.1, p.1.2), p.2 1)) := by fun_prop
  have hc2 : ContinuousOn (fun p : (ℝ × ℝ) × Work.OddVolterra.St => p.2 2) (kvecRegion h) :=
    ((continuous_apply (2 : Fin 4)).comp continuous_snd).continuousOn
  have hc3 : ContinuousOn (fun p : (ℝ × ℝ) × Work.OddVolterra.St => p.2 3) (kvecRegion h) :=
    ((continuous_apply (3 : Fin 4)).comp continuous_snd).continuousOn
  have hA0 : ContinuousOn (fun p : (ℝ × ℝ) × Work.OddVolterra.St =>
      deriv (fun u : ℝ => Work.OddVolterra.K1 n h u p.1.2 (-(p.2 0))) p.1.1) (kvecRegion h) := by
    have hMT : MapsTo (fun p : (ℝ × ℝ) × Work.OddVolterra.St => ((p.1.1, p.1.2), -(p.2 0)))
        (kvecRegion h) (goodRegion h) := fun p hp => ⟨hp.1, hp.2.1⟩
    have := (continuousOn_deriv_K1_region (h := h) n hh).comp hmaps0.continuousOn hMT
    simpa [Function.comp_def] using this
  have hA1 : ContinuousOn (fun p : (ℝ × ℝ) × Work.OddVolterra.St =>
      deriv (fun u : ℝ => Work.OddVolterra.K1 n h u p.1.2 (p.2 1)) p.1.1) (kvecRegion h) := by
    have hMT : MapsTo (fun p : (ℝ × ℝ) × Work.OddVolterra.St => ((p.1.1, p.1.2), p.2 1))
        (kvecRegion h) (goodRegion h) := fun p hp => ⟨hp.1, hp.2.2⟩
    have := (continuousOn_deriv_K1_region (h := h) n hh).comp hmaps1.continuousOn hMT
    simpa [Function.comp_def] using this
  have hB0 : ContinuousOn (fun p : (ℝ × ℝ) × Work.OddVolterra.St =>
      deriv (fun u : ℝ => Work.OddVolterra.K2 n h u p.1.2 (-(p.2 0))) p.1.1) (kvecRegion h) := by
    have hMT : MapsTo (fun p : (ℝ × ℝ) × Work.OddVolterra.St => ((p.1.1, p.1.2), -(p.2 0)))
        (kvecRegion h) (goodRegion h) := fun p hp => ⟨hp.1, hp.2.1⟩
    have := (continuousOn_deriv_K2_region (h := h) n hn hh).comp hmaps0.continuousOn hMT
    simpa [Function.comp_def] using this
  have hB1 : ContinuousOn (fun p : (ℝ × ℝ) × Work.OddVolterra.St =>
      deriv (fun u : ℝ => Work.OddVolterra.K2 n h u p.1.2 (p.2 1)) p.1.1) (kvecRegion h) := by
    have hMT : MapsTo (fun p : (ℝ × ℝ) × Work.OddVolterra.St => ((p.1.1, p.1.2), p.2 1))
        (kvecRegion h) (goodRegion h) := fun p hp => ⟨hp.1, hp.2.2⟩
    have := (continuousOn_deriv_K2_region (h := h) n hn hh).comp hmaps1.continuousOn hMT
    simpa [Function.comp_def] using this
  have hT : ContinuousOn (fun p : (ℝ × ℝ) × Work.OddVolterra.St =>
      ![ - (deriv (fun u : ℝ => Work.OddVolterra.K1 n h u p.1.2 (-(p.2 0))) p.1.1 * p.2 2 +
              deriv (fun u : ℝ => Work.OddVolterra.K1 n h u p.1.2 (p.2 1)) p.1.1 * p.2 3),
          - (deriv (fun u : ℝ => Work.OddVolterra.K2 n h u p.1.2 (-(p.2 0))) p.1.1 * p.2 2 +
              deriv (fun u : ℝ => Work.OddVolterra.K2 n h u p.1.2 (p.2 1)) p.1.1 * p.2 3) ])
      (kvecRegion h) := by
    rw [continuousOn_pi]
    intro i
    fin_cases i
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      exact ((hA0.mul hc2).add (hA1.mul hc3)).neg
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
      exact ((hB0.mul hc2).add (hB1.mul hc3)).neg
  refine hT.congr ?_
  intro p hp
  exact deriv_Kvec_eq n hn hh (p.2) hp.1 hp.2.1 hp.2.2

/-- **Setup for the odd-case Volterra kernel.**  Under the regularity hypothesis on the state
`Z`, there is a positive margin `δ` around the lower slope `s` and a constant `Cm` such that the
denominator radicands `krad` are positive on the trapezium `s - δ ≤ a ≤ σ ≤ 1` and the kernel
`Kvec` together with its first-argument derivative is bounded by `Cm` there. -/
theorem exists_kvec_setup (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {Z : ℝ → Work.OddVolterra.St}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (0:ℝ)))
    {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1)
    (hreg : ∀ σ ∈ Set.Icc s 1, ∀ w ∈ Set.Icc s σ, ∀ t : ℝ, (t = -(Z σ 0) ∨ t = Z σ 1) →
      0 < (t + Work.OddVolterra.hquot h w σ) *
        (Work.OddVolterra.line h σ t + Work.OddVolterra.line h w t)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ Cm : ℝ, 0 < Cm ∧
      (∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Icc (s - δ) σ,
        0 < Work.OddVolterra.krad h σ (-(Z σ 0)) a ∧
          0 < Work.OddVolterra.krad h σ (Z σ 1) a) ∧
      (∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Ico (s - δ) σ,
        ‖Work.OddVolterra.Kvec n h a σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)‖ ≤ Cm) ∧
      (∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Ico (s - δ) σ,
        ‖deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) a‖
          ≤ Cm) := by
  have hs0 : 0 < s := hs.1
  have hs1 : s ≤ 1 := le_of_lt hs.2
  have hZcont : ContinuousOn Z (Set.Icc s 1) :=
    hZ.continuousOn.mono (fun x hx => lt_of_lt_of_le hs0 hx.1)
  obtain ⟨M, hMpos, hM⟩ := exists_state_bound hZcont
  have htneg : ContinuousOn (tneg Z) (Set.Icc s 1) :=
    ((continuous_apply (0 : Fin 4)).comp_continuousOn hZcont).neg
  have htpos : ContinuousOn (tpos Z) (Set.Icc s 1) :=
    (continuous_apply (1 : Fin 4)).comp_continuousOn hZcont
  have hpos1 : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Icc s σ, 0 < Work.OddVolterra.krad h σ (tneg Z σ) a :=
    fun σ hσ a ha => hreg σ hσ a ha (tneg Z σ) (Or.inl rfl)
  have hpos2 : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Icc s σ, 0 < Work.OddVolterra.krad h σ (tpos Z σ) a :=
    fun σ hσ a ha => hreg σ hσ a ha (tpos Z σ) (Or.inr rfl)
  obtain ⟨δ1, hδ1pos, hδ1⟩ := Work.OddVolterra.exists_pos_margin hh hs1 htneg hpos1
  obtain ⟨δ2, hδ2pos, hδ2⟩ := Work.OddVolterra.exists_pos_margin hh hs1 htpos hpos2
  have hδmin : 0 < min δ1 δ2 := lt_min hδ1pos hδ2pos
  have hpos1' : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Icc (s - min δ1 δ2) σ,
      0 < Work.OddVolterra.krad h σ (tneg Z σ) a :=
    fun σ hσ a ha => hδ1 σ hσ a ⟨by linarith [min_le_left δ1 δ2, ha.1], ha.2⟩
  have hpos2' : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Icc (s - min δ1 δ2) σ,
      0 < Work.OddVolterra.krad h σ (tpos Z σ) a :=
    fun σ hσ a ha => hδ2 σ hσ a ⟨by linarith [min_le_right δ1 δ2, ha.1], ha.2⟩
  obtain ⟨C1, hC1pos, hC1⟩ := Work.OddVolterra.K1_K2_deriv_bound n hn hh hδmin htneg hpos1'
  obtain ⟨C2, hC2pos, hC2⟩ := Work.OddVolterra.K1_K2_deriv_bound n hn hh hδmin htpos hpos2'
  have hCmax : 0 < max C1 C2 := lt_of_lt_of_le hC1pos (le_max_left C1 C2)
  have hKvec : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Ico (s - min δ1 δ2) σ,
      ‖Work.OddVolterra.Kvec n h a σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)‖ ≤ 2 * M * max C1 C2 ∧
      ‖deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) a‖
        ≤ 2 * M * max C1 C2 := by
    intro σ hσ a ha
    have haσ : a < σ := ha.2
    obtain ⟨hA1, hA2, hA3, hA4⟩ := hC1 σ hσ a ha
    obtain ⟨hB1, hB2, hB3, hB4⟩ := hC2 σ hσ a ha
    have hz2 : |Z σ 2| ≤ M := hM σ hσ 2
    have hz3 : |Z σ 3| ≤ M := hM σ hσ 3
    have hkrad1 : 0 < Work.OddVolterra.krad h σ (-(Z σ 0)) a :=
      hpos1' σ hσ a ⟨ha.1, le_of_lt haσ⟩
    have hkrad2 : 0 < Work.OddVolterra.krad h σ (Z σ 1) a :=
      hpos2' σ hσ a ⟨ha.1, le_of_lt haσ⟩
    -- componentwise bounds for the value
    have hA1' : ‖Work.OddVolterra.K1 n h a σ (-(Z σ 0))‖ ≤ C1 := by
      simpa only [tneg_apply] using hA1
    have hA2' : ‖Work.OddVolterra.K2 n h a σ (-(Z σ 0))‖ ≤ C1 := by
      simpa only [tneg_apply] using hA2
    have hA3' : ‖deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (-(Z σ 0))) a‖ ≤ C1 := by
      simpa only [tneg_apply] using hA3
    have hA4' : ‖deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (-(Z σ 0))) a‖ ≤ C1 := by
      simpa only [tneg_apply] using hA4
    have hB1' : ‖Work.OddVolterra.K1 n h a σ (Z σ 1)‖ ≤ C2 := by
      simpa only [tpos_apply] using hB1
    have hB2' : ‖Work.OddVolterra.K2 n h a σ (Z σ 1)‖ ≤ C2 := by
      simpa only [tpos_apply] using hB2
    have hB3' : ‖deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (Z σ 1)) a‖ ≤ C2 := by
      simpa only [tpos_apply] using hB3
    have hB4' : ‖deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (Z σ 1)) a‖ ≤ C2 := by
      simpa only [tpos_apply] using hB4
    have hbc : ∀ x y : ℝ, ‖x‖ ≤ max C1 C2 → ‖y‖ ≤ max C1 C2 → |x| ≤ M → |y| ≤ M →
        |x * (0:ℝ) + y * (0:ℝ)| ≤ 2 * M * max C1 C2 := by
      intro x y hx hy _ _
      simp
      positivity
    have key : ∀ d1 d2 c2 c3 : ℝ, ‖d1‖ ≤ max C1 C2 → ‖d2‖ ≤ max C1 C2 →
        |c2| ≤ M → |c3| ≤ M →
        |-(d1 * c2 + d2 * c3)| ≤ 2 * M * max C1 C2 := by
      intro d1 d2 c2 c3 hd1 hd2 hc2 hc3
      have h1 : |d1 * c2| ≤ max C1 C2 * M := by
        rw [abs_mul]
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using hd1) hc2 (abs_nonneg c2)
          (le_trans (norm_nonneg d1) hd1)
      have h2 : |d2 * c3| ≤ max C1 C2 * M := by
        rw [abs_mul]
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using hd2) hc3 (abs_nonneg c3)
          (le_trans (norm_nonneg d2) hd2)
      calc |-(d1 * c2 + d2 * c3)| = |d1 * c2 + d2 * c3| := abs_neg _
        _ ≤ |d1 * c2| + |d2 * c3| := abs_add_le _ _
        _ ≤ max C1 C2 * M + max C1 C2 * M := add_le_add h1 h2
        _ = 2 * M * max C1 C2 := by ring
    have hval0 : |-(Work.OddVolterra.K1 n h a σ (-(Z σ 0)) * Z σ 2
        + Work.OddVolterra.K1 n h a σ (Z σ 1) * Z σ 3)| ≤ 2 * M * max C1 C2 :=
      key _ _ _ _ (le_trans hA1' (le_max_left C1 C2)) (le_trans hB1' (le_max_right C1 C2)) hz2 hz3
    have hval1 : |-(Work.OddVolterra.K2 n h a σ (-(Z σ 0)) * Z σ 2
        + Work.OddVolterra.K2 n h a σ (Z σ 1) * Z σ 3)| ≤ 2 * M * max C1 C2 :=
      key _ _ _ _ (le_trans hA2' (le_max_left C1 C2)) (le_trans hB2' (le_max_right C1 C2)) hz2 hz3
    have hderivval : deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) a
        = ![- (deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (-(Z σ 0))) a * Z σ 2
              + deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (Z σ 1)) a * Z σ 3),
            - (deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (-(Z σ 0))) a * Z σ 2
              + deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (Z σ 1)) a * Z σ 3)] := by
      have hcomp0 : HasDerivAt (fun u : ℝ =>
          -(Work.OddVolterra.K1 n h u σ (-(Z σ 0)) * Z σ 2
            + Work.OddVolterra.K1 n h u σ (Z σ 1) * Z σ 3))
          (-(deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (-(Z σ 0))) a * Z σ 2
            + deriv (fun u : ℝ => Work.OddVolterra.K1 n h u σ (Z σ 1)) a * Z σ 3)) a := by
        refine (((differentiableAt_K1 (h := h) n hh haσ hkrad1).hasDerivAt.mul_const
            (Z σ 2)).add ((differentiableAt_K1 (h := h) n hh haσ hkrad2).hasDerivAt.mul_const
              (Z σ 3))).neg.congr_deriv ?_
        ring
      have hcomp1 : HasDerivAt (fun u : ℝ =>
          -(Work.OddVolterra.K2 n h u σ (-(Z σ 0)) * Z σ 2
            + Work.OddVolterra.K2 n h u σ (Z σ 1) * Z σ 3))
          (-(deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (-(Z σ 0))) a * Z σ 2
            + deriv (fun u : ℝ => Work.OddVolterra.K2 n h u σ (Z σ 1)) a * Z σ 3)) a := by
        refine (((differentiableAt_K2 (h := h) n hn hh haσ hkrad1).hasDerivAt.mul_const
            (Z σ 2)).add ((differentiableAt_K2 (h := h) n hn hh haσ hkrad2).hasDerivAt.mul_const
              (Z σ 3))).neg.congr_deriv ?_
        ring
      have hpi := deriv_pi (𝕜 := ℝ) (x := a)
        (φ := fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3))
        (fun i => by
          fin_cases i
          · simpa [Work.OddVolterra.Kvec] using hcomp0.differentiableAt
          · simpa [Work.OddVolterra.Kvec] using hcomp1.differentiableAt)
      rw [hpi]
      funext i
      fin_cases i
      · simpa [Work.OddVolterra.Kvec] using hcomp0.deriv
      · simpa [Work.OddVolterra.Kvec] using hcomp1.deriv
    refine ⟨?_, ?_⟩
    · rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      fin_cases i
      · simpa [Work.OddVolterra.Kvec, Real.norm_eq_abs] using hval0
      · simpa [Work.OddVolterra.Kvec, Real.norm_eq_abs] using hval1
    · rw [hderivval, pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      fin_cases i
      · simpa [Real.norm_eq_abs] using
          key _ _ _ _ (le_trans hA3' (le_max_left C1 C2)) (le_trans hB3' (le_max_right C1 C2)) hz2 hz3
      · simpa [Real.norm_eq_abs] using
          key _ _ _ _ (le_trans hA4' (le_max_left C1 C2)) (le_trans hB4' (le_max_right C1 C2)) hz2 hz3
  refine ⟨min δ1 δ2, hδmin, 2 * M * max C1 C2, ?_,
    fun σ hσ a ha => ⟨hpos1' σ hσ a ha, hpos2' σ hσ a ha⟩,
    (fun σ hσ a ha => (hKvec σ hσ a ha).1), (fun σ hσ a ha => (hKvec σ hσ a ha).2)⟩
  exact mul_pos (mul_pos (by norm_num) hMpos) hCmax

/-- The vector-valued Abel integrand of the `σ`-derivative of `G₂`. -/
noncomputable def ThetaIntegrand (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (Z : ℝ → Work.OddVolterra.St)
    (σ τ : ℝ) : Fin 2 → ℝ :=
  (Real.sqrt (τ * (1 - τ)))⁻¹ •
    ((1 - τ) • deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3))
      (s + τ * (σ - s)))

/-- Measurability in `τ` of the `σ`-derivative integrand, for fixed `σ`. -/
lemma thetaIntegrand_aestronglyMeasurable (n : ℕ) {h : ℝ → ℝ} {s : ℝ}
    {Z : ℝ → Work.OddVolterra.St} (σ : ℝ) :
    AEStronglyMeasurable (ThetaIntegrand n h s Z σ)
      (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
  have hm : Measurable (fun τ : ℝ => deriv (fun u : ℝ =>
      Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))) :=
    (measurable_deriv (𝕜 := ℝ)
      (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3))).comp
      (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s))
  have hw : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) := by
    have h : Measurable (fun τ : ℝ => Real.sqrt (τ * (1 - τ))) :=
      Work.OddVolterra.measurable_sqrt_real.comp
        (measurable_id.mul (measurable_const.sub measurable_id))
    exact h.inv
  exact (hw.smul ((measurable_const.sub measurable_id).smul hm)).aestronglyMeasurable

/-- **The `σ`-derivative of `G₂` as an Abel-weighted integral** (vector form), with the
hypotheses of the odd-case setup. -/
lemma hasDerivAt_theta (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {Z : ℝ → Work.OddVolterra.St} {s : ℝ} {δ Cm : ℝ}
    (hδ : 0 < δ) (hCm : 0 < Cm)
    (hpos : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Icc (s - δ) σ,
      0 < Work.OddVolterra.krad h σ (-(Z σ 0)) a ∧
        0 < Work.OddVolterra.krad h σ (Z σ 1) a)
    (hbdK : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Ico (s - δ) σ,
      ‖Work.OddVolterra.Kvec n h a σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)‖ ≤ Cm)
    (hbdD : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Ico (s - δ) σ,
      ‖deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) a‖ ≤ Cm)
    {σ : ℝ} (hsσ : s < σ) (hσ1 : σ ≤ 1) :
    HasDerivAt (fun u : ℝ => Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3))
      (∫ τ in (0:ℝ)..1, ThetaIntegrand n h s Z σ τ) s := by
  have hσIcc : σ ∈ Set.Icc s 1 := ⟨le_of_lt hsσ, hσ1⟩
  set δ' : ℝ := min δ ((σ - s) / 2) with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδ (by linarith)
  have hδ'le : δ' ≤ δ := min_le_left _ _
  have hpt : ∀ x ∈ Set.Ioo (s - δ') (s + δ'), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      x + τ * (σ - x) ∈ Set.Ico (s - δ) σ := by
    intro x hx τ hτ
    have hxσ : x < σ := by
      have h2 : δ' ≤ (σ - s) / 2 := min_le_right _ _
      have h3 : x < s + δ' := hx.2
      linarith
    have hτ0 : 0 ≤ τ := hτ.1
    have hτ1 : τ < 1 := hτ.2
    refine ⟨?_, ?_⟩
    · have h1 : x + τ * (σ - x) ≥ x := by
        have : 0 ≤ τ * (σ - x) := mul_nonneg hτ0 (by linarith)
        linarith
      have h2 : s - δ ≤ x := by
        have h3 : s - δ' ≤ x := le_of_lt hx.1
        linarith
      linarith
    · have h1 : τ * (σ - x) < σ - x := by
        have hσx : 0 < σ - x := by linarith
        nlinarith
      linarith
  have hbdK' : ∀ x ∈ Set.Ioo (s - δ') (s + δ'), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      ‖Work.OddVolterra.Kvec n h (x + τ * (σ - x)) σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)‖ ≤ Cm :=
    fun x hx τ hτ => hbdK σ hσIcc _ (hpt x hx τ hτ)
  have hdiff' : ∀ x ∈ Set.Ioo (s - δ') (s + δ'), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      DifferentiableAt ℝ (fun u : ℝ =>
        Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (x + τ * (σ - x)) := by
    intro x hx τ hτ
    have ha := hpt x hx τ hτ
    have haIcc : x + τ * (σ - x) ∈ Set.Icc (s - δ) σ := ⟨ha.1, le_of_lt ha.2⟩
    obtain ⟨hk1, hk2⟩ := hpos σ hσIcc _ haIcc
    exact differentiableAt_Kvec n hn hh (Z σ) ha.2 hk1 hk2
  have hbound' : ∀ x ∈ Set.Ioo (s - δ') (s + δ'), ∀ τ ∈ Set.Icc (0:ℝ) 1,
      ‖(1 - τ) • deriv (fun u : ℝ =>
        Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (x + τ * (σ - x))‖ ≤ Cm := by
    intro x hx τ hτ
    by_cases h1 : τ = 1
    · subst h1
      simp only [sub_self, zero_smul, norm_zero]
      exact hCm.le
    · have hτIco : τ ∈ Set.Ico (0:ℝ) 1 := ⟨hτ.1, lt_of_le_of_ne hτ.2 h1⟩
      have ha := hpt x hx τ hτIco
      have hb := hbdD σ hσIcc _ ha
      calc ‖(1 - τ) • deriv (fun u : ℝ =>
            Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (x + τ * (σ - x))‖
          = |1 - τ| * ‖deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (x + τ * (σ - x))‖ :=
            norm_smul _ _
        _ ≤ 1 * Cm := by
            refine mul_le_mul ?_ hb (norm_nonneg _) (by norm_num)
            have hτ0 : (0:ℝ) ≤ 1 - τ := by linarith [hτ.2]
            rw [abs_of_nonneg hτ0]
            linarith [hτ.1]
        _ = Cm := one_mul _
  have h := Work.OddVolterra.hasDerivAt_G2 (h := h) n hh hsσ (Z σ) hδ'pos hbdK' hdiff' hbound'
  simpa [ThetaIntegrand] using h

/-- **Continuity and bound of the `σ`-derivative of a component of `G₂`** on the slope interval
`(s,1)`, under the hypotheses of the odd-case setup. -/
theorem theta_component_cont_bound (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {Z : ℝ → Work.OddVolterra.St}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (0:ℝ)))
    {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) (i : Fin 2)
    {δ Cm : ℝ} (hδ : 0 < δ) (hCm : 0 < Cm)
    (hpos : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Icc (s - δ) σ,
      0 < Work.OddVolterra.krad h σ (-(Z σ 0)) a ∧
        0 < Work.OddVolterra.krad h σ (Z σ 1) a)
    (hbdK : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Ico (s - δ) σ,
      ‖Work.OddVolterra.Kvec n h a σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)‖ ≤ Cm)
    (hbdD : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Ico (s - δ) σ,
      ‖deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) a‖ ≤ Cm) :
    ContinuousOn (fun σ : ℝ => deriv (fun u : ℝ =>
        (Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) i) s)
      (Set.Ioo s 1) ∧
    (∀ σ ∈ Set.Ioc s 1, ‖deriv (fun u : ℝ =>
        (Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) i) s‖ ≤ Cm * Real.pi) := by
  have hs1 : s < 1 := hs.2
  -- (0) the `HasDerivAt` form of the derivative formula
  have hHas : ∀ σ ∈ Set.Ioc s 1, HasDerivAt (fun u : ℝ =>
        Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3))
      (∫ τ in (0:ℝ)..1, ThetaIntegrand n h s Z σ τ) s :=
    fun σ hσ => hasDerivAt_theta n hn hh hδ hCm hpos hbdK hbdD hσ.1 hσ.2
  -- (1) the derivative is the Abel integral of the integrand
  have hform : ∀ σ ∈ Set.Ioc s 1, deriv (fun u : ℝ =>
        Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) s =
      ∫ τ in (0:ℝ)..1, ThetaIntegrand n h s Z σ τ :=
    fun σ hσ => (hHas σ hσ).deriv
  -- (2) componentwise differentiability
  have hcompdiff : ∀ σ ∈ Set.Ioc s 1, ∀ j : Fin 2, DifferentiableAt ℝ (fun u : ℝ =>
      (Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) j) s := by
    intro σ hσ j
    have hL : HasFDerivAt (fun v : Fin 2 → ℝ => v j)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j)
        ((fun u : ℝ => Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) s) :=
      ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j)
    have hcomp := hL.comp s (hHas σ hσ).hasFDerivAt
    simpa [Function.comp_def, ContinuousLinearMap.proj_apply] using hcomp.differentiableAt
  -- (3) the pointwise bound on the integrand
  have hpoint : ∀ σ ∈ Set.Ioc s 1, ∀ τ ∈ Set.Icc (0:ℝ) 1,
      ‖ThetaIntegrand n h s Z σ τ‖ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * Cm := by
    intro σ hσ τ hτ
    have hσIcc : σ ∈ Set.Icc s 1 := ⟨le_of_lt hσ.1, hσ.2⟩
    have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    by_cases h1 : τ = 1
    · subst h1
      have hz : (Real.sqrt ((1:ℝ) * (1 - 1)))⁻¹ = 0 := by norm_num
      simp [ThetaIntegrand, hz]
    · have hτIco : τ ∈ Set.Ico (0:ℝ) 1 := ⟨hτ.1, lt_of_le_of_ne hτ.2 h1⟩
      have ha : s + τ * (σ - s) ∈ Set.Ico (s - δ) σ := by
        refine ⟨?_, ?_⟩
        · have h2 : 0 ≤ τ * (σ - s) := mul_nonneg hτ.1 (by linarith [hσ.1])
          linarith
        · have hτlt : τ < 1 := lt_of_le_of_ne hτ.2 h1
          have h2 : τ * (σ - s) < σ - s := by nlinarith [hσ.1, hτlt]
          linarith
      have hb := hbdD σ hσIcc _ ha
      have hsm : ‖(1 - τ) • deriv (fun u : ℝ =>
          Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))‖ ≤ Cm := by
        calc ‖(1 - τ) • deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))‖
            = |1 - τ| * ‖deriv (fun u : ℝ =>
                Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))‖ :=
              norm_smul _ _
          _ ≤ 1 * Cm := by
              refine mul_le_mul ?_ hb (norm_nonneg _) (by norm_num)
              have hτ0 : (0:ℝ) ≤ 1 - τ := by linarith [hτ.2]
              rw [abs_of_nonneg hτ0]
              linarith [hτ.1]
          _ = Cm := one_mul _
      calc ‖ThetaIntegrand n h s Z σ τ‖
          = (Real.sqrt (τ * (1 - τ)))⁻¹ * ‖(1 - τ) • deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))‖ := by
            simp only [ThetaIntegrand, norm_smul]
            rw [Real.norm_eq_abs, abs_of_nonneg hw]
        _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * Cm := mul_le_mul_of_nonneg_left hsm hw
  -- (4) the vector-valued bound
  have hbdval : ∀ σ ∈ Set.Ioc s 1, ‖deriv (fun u : ℝ =>
        Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) s‖ ≤ Cm * Real.pi := by
    intro σ hσ
    have hwpi : (∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹) = Real.pi := by
      have hfun : (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) =
          fun τ : ℝ => 1 / Real.sqrt (τ * ((1:ℝ) - τ)) := by
        funext τ
        rw [one_div]
      rw [hfun]
      exact Commons.Geometry.Ulam.integral_one_div_sqrt_tau_one_sub_tau_eq_pi
    have hFmeas : AEStronglyMeasurable (ThetaIntegrand n h s Z σ)
        (volume.restrict (Set.uIoc (0:ℝ) 1)) := thetaIntegrand_aestronglyMeasurable n σ
    have hFaebd : (fun τ : ℝ => ‖ThetaIntegrand n h s Z σ τ‖) ≤ᵐ[volume.restrict (Set.uIoc (0:ℝ) 1)]
        fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * Cm := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
      exact hpoint σ hσ τ ⟨le_of_lt hτ.1, hτ.2⟩
    have hFint : IntervalIntegrable (ThetaIntegrand n h s Z σ) volume (0:ℝ) 1 :=
      (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const Cm).mono_fun' hFmeas hFaebd
    rw [hform σ hσ]
    calc ‖∫ τ in (0:ℝ)..1, ThetaIntegrand n h s Z σ τ‖
        ≤ ∫ τ in (0:ℝ)..1, ‖ThetaIntegrand n h s Z σ τ‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * Cm := by
          refine intervalIntegral.integral_mono_on (by norm_num) hFint.norm
            (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const Cm) ?_
          intro τ hτ
          exact hpoint σ hσ τ hτ
      _ = (∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹) * Cm := by
          rw [intervalIntegral.integral_mul_const]
      _ = Cm * Real.pi := by rw [hwpi]; ring
  -- (5) continuity of the vector-valued derivative by dominated convergence
  have hcontvec : ContinuousOn (fun σ : ℝ => deriv (fun u : ℝ =>
        Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) s) (Set.Ioo s 1) := by
    intro σ₀ hσ₀
    have hmain := intervalIntegral.continuousWithinAt_of_dominated_interval
      (μ := volume) (F := ThetaIntegrand n h s Z) (x₀ := σ₀)
      (bound := fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * Cm)
      (a := (0:ℝ)) (b := 1) (s := Set.Ioo s 1)
      ?hFmeas ?hbound ?hboundint ?hcont
    · refine hmain.congr ?_ (hform σ₀ ⟨hσ₀.1, le_of_lt hσ₀.2⟩)
      intro σ hσ
      exact hform σ ⟨hσ.1, le_of_lt hσ.2⟩
    · exact Filter.Eventually.of_forall (fun σ => thetaIntegrand_aestronglyMeasurable n σ)
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      refine Filter.Eventually.of_forall (fun τ hτ => ?_)
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
      exact hpoint σ ⟨hσ.1, le_of_lt hσ.2⟩ τ ⟨le_of_lt hτ.1, hτ.2⟩
    · exact Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const Cm
    · refine Filter.Eventually.of_forall (fun τ hτ => ?_)
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
      by_cases h1 : τ = 1
      · subst h1
        have hzero : (fun σ : ℝ => ThetaIntegrand n h s Z σ 1) = fun _ => (0 : Fin 2 → ℝ) := by
          funext σ
          have hz : (Real.sqrt ((1:ℝ) * (1 - 1)))⁻¹ = 0 := by norm_num
          simp [ThetaIntegrand, hz]
        rw [hzero]
        exact continuousWithinAt_const
      · have hτIoo : τ ∈ Set.Ioo (0:ℝ) 1 := ⟨hτ.1, lt_of_le_of_ne hτ.2 h1⟩
        have hcomp : ContinuousWithinAt (fun σ : ℝ => ((s + τ * (σ - s), σ), Z σ))
            (Set.Ioo s 1) σ₀ := by
          have h1 : ContinuousWithinAt (fun σ : ℝ => (s + τ * (σ - s), σ)) (Set.Ioo s 1) σ₀ := by
            fun_prop
          have h2 : ContinuousWithinAt Z (Set.Ioo s 1) σ₀ :=
            (hZ.continuousOn.continuousAt (isOpen_Ioi.mem_nhds (lt_trans hs.1 hσ₀.1))).continuousWithinAt
          exact h1.prodMk h2
        have hMT : MapsTo (fun σ : ℝ => ((s + τ * (σ - s), σ), Z σ)) (Set.Ioo s 1) (kvecRegion h) := by
          intro σ hσ
          have hσIcc : σ ∈ Set.Icc s 1 := ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩
          have ha : s + τ * (σ - s) ∈ Set.Icc (s - δ) σ := by
            refine ⟨?_, ?_⟩
            · have h2 : 0 ≤ τ * (σ - s) := mul_nonneg (le_of_lt hτIoo.1) (by linarith [hσ.1])
              linarith
            · have h2 : τ * (σ - s) < σ - s := by nlinarith [hσ.1, hτIoo.2]
              linarith
          obtain ⟨hk1, hk2⟩ := hpos σ hσIcc _ ha
          exact ⟨by nlinarith [hτIoo.2, hσ.1], hk1, hk2⟩
        have hj := (Work.OddVolterra.Existence.continuousOn_deriv_Kvec n hn hh).continuousWithinAt
          (hMT hσ₀)
        have hcomp2 : ContinuousWithinAt (fun σ : ℝ => deriv (fun u : ℝ =>
            Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s)))
            (Set.Ioo s 1) σ₀ := by
          have h := hj.comp (f := fun σ : ℝ => ((s + τ * (σ - s), σ), Z σ)) hcomp hMT
          simpa [Function.comp_def] using h
        have hsm1 : ContinuousWithinAt (fun σ : ℝ => (1 - τ) • deriv (fun u : ℝ =>
            Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s)))
            (Set.Ioo s 1) σ₀ := hcomp2.const_smul (1 - τ)
        have hsm2 : ContinuousWithinAt (fun σ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ • ((1 - τ) •
            deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))))
            (Set.Ioo s 1) σ₀ := hsm1.const_smul ((Real.sqrt (τ * (1 - τ)))⁻¹)
        simpa [ThetaIntegrand] using hsm2
  refine ⟨?_, ?_⟩
  · -- componentwise continuity
    have hcf : ContinuousOn (fun σ : ℝ => (deriv (fun u : ℝ =>
        Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) s) i) (Set.Ioo s 1) :=
      (continuousOn_pi.mp hcontvec) i
    refine hcf.congr ?_
    intro σ hσ
    have hpi := deriv_pi (𝕜 := ℝ) (x := s)
      (φ := fun u : ℝ => Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3))
      (hcompdiff σ ⟨hσ.1, le_of_lt hσ.2⟩)
    have := congrFun hpi i
    simpa using this.symm
  · intro σ hσ
    have hpi := deriv_pi (𝕜 := ℝ) (x := s)
      (φ := fun u : ℝ => Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3))
      (hcompdiff σ hσ)
    have hceq : deriv (fun u : ℝ =>
        (Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) i) s =
        (deriv (fun u : ℝ => Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) s) i := by
      have := congrFun hpi i
      simpa using this.symm
    rw [hceq]
    exact le_trans (norm_le_pi_norm _ _) (hbdval σ hσ)

theorem Theta_integrand_intervalIntegrable (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {Z : ℝ → Work.OddVolterra.St}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (0:ℝ)))
    {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1)
    (hreg : ∀ σ ∈ Set.Icc s 1, ∀ w ∈ Set.Icc s σ, ∀ t : ℝ, (t = -(Z σ 0) ∨ t = Z σ 1) →
      0 < (t + Work.OddVolterra.hquot h w σ) *
        (Work.OddVolterra.line h σ t + Work.OddVolterra.line h w t)) :
    IntervalIntegrable (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Z σ)) volume s 1 := by
  obtain ⟨δ, hδpos, Cm, hCmpos, hpos, hbdK, hbdD⟩ := exists_kvec_setup n hn hh hZ hs hreg
  have hs0 : 0 < s := hs.1
  have hs1 : s ≤ 1 := le_of_lt hs.2
  have hZcont : ContinuousOn Z (Set.Icc s 1) :=
    hZ.continuousOn.mono (fun x hx => lt_of_lt_of_le hs0 hx.1)
  have hmeas_eq : volume.restrict (Set.uIoc s 1) = volume.restrict (Set.Ioo s 1) := by
    rw [Set.uIoc_of_le hs1]
    exact (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm
  have huIoc_lt : volume (Set.uIoc s 1) < ⊤ := by
    rw [Set.uIoc_of_le hs1]
    exact measure_Ioc_lt_top
  have hbound2 := (theta_component_cont_bound n hn hh hZ hs (0 : Fin 2) hδpos hCmpos hpos hbdK hbdD)
  have hbound3 := (theta_component_cont_bound n hn hh hZ hs (1 : Fin 2) hδpos hCmpos hpos hbdK hbdD)
  rw [intervalIntegrable_iff]
  change MeasureTheory.Integrable (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Z σ))
    (volume.restrict (Set.uIoc s 1))
  rw [hmeas_eq, MeasureTheory.integrable_pi_iff]
  intro i
  fin_cases i
  · change MeasureTheory.Integrable (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Z σ) 0)
      (volume.restrict (Set.Ioo s 1))
    have hfun : (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Z σ) 0) =
        fun σ : ℝ => -(Z σ 2) := by
      funext σ
      simp [Work.OddVolterra.Theta]
    rw [hfun, ← hmeas_eq]
    have hc : ContinuousOn (fun σ : ℝ => -(Z σ 2)) (Set.uIcc s 1) := by
      rw [Set.uIcc_of_le hs1]
      exact ((continuous_apply (2 : Fin 4)).comp_continuousOn hZcont).neg
    exact intervalIntegrable_iff.mp hc.intervalIntegrable
  · change MeasureTheory.Integrable (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Z σ) 1)
      (volume.restrict (Set.Ioo s 1))
    have hfun : (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Z σ) 1) =
        fun σ : ℝ => -(Z σ 3) := by
      funext σ
      simp [Work.OddVolterra.Theta]
    rw [hfun, ← hmeas_eq]
    have hc : ContinuousOn (fun σ : ℝ => -(Z σ 3)) (Set.uIcc s 1) := by
      rw [Set.uIcc_of_le hs1]
      exact ((continuous_apply (3 : Fin 4)).comp_continuousOn hZcont).neg
    exact intervalIntegrable_iff.mp hc.intervalIntegrable
  · change MeasureTheory.Integrable (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Z σ) 2)
      (volume.restrict (Set.Ioo s 1))
    have hfun : (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Z σ) 2) =
        fun σ : ℝ => -deriv (fun u : ℝ =>
          (Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) 0) s := by
      funext σ
      simp [Work.OddVolterra.Theta]
    rw [hfun, ← hmeas_eq]
    refine MeasureTheory.IntegrableOn.of_bound huIoc_lt ?_ (Cm * Real.pi) ?_
    · have hc : ContinuousOn (fun σ : ℝ => -deriv (fun u : ℝ =>
          (Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) 0) s)
          (Set.Ioo s 1) := hbound2.1.neg
      have := hc.aestronglyMeasurable (μ := volume) measurableSet_Ioo
      simpa [hmeas_eq] using this
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with σ hσ
      rw [Set.uIoc_of_le hs1] at hσ
      simpa using hbound2.2 σ hσ
  · change MeasureTheory.Integrable (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Z σ) 3)
      (volume.restrict (Set.Ioo s 1))
    have hfun : (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Z σ) 3) =
        fun σ : ℝ => -deriv (fun u : ℝ =>
          (Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) 1) s := by
      funext σ
      simp [Work.OddVolterra.Theta]
    rw [hfun, ← hmeas_eq]
    refine MeasureTheory.IntegrableOn.of_bound huIoc_lt ?_ (Cm * Real.pi) ?_
    · have hc : ContinuousOn (fun σ : ℝ => -deriv (fun u : ℝ =>
          (Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) 1) s)
          (Set.Ioo s 1) := hbound3.1.neg
      have := hc.aestronglyMeasurable (μ := volume) measurableSet_Ioo
      simpa [hmeas_eq] using this
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with σ hσ
      rw [Set.uIoc_of_le hs1] at hσ
      simpa using hbound3.2 σ hσ

end Work.OddVolterra.Existence
