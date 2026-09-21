import Mathlib
import Submission.Work.OddExistence.Manifest
import Submission.Work.OddBridge.J1M_eq_J1
import Submission.Work.Anchor.ThetaM_contDiffOn
import Submission.Work.OddVolterra.Existence.theta_lipschitz_state_ball

/-!
# The manifest odd `Θ`-data: bridge to the `KernelExt` presentation and regularity

`Work.OddExistence.ThetaM` is built from the `Work.OddBridge` presentation of the manifest Abel
kernel (`KvecM`, `G2M`, `J1M`, `J2M`, `RR`), while the regularity machinery of the workspace
(`Work.Anchor.contDiffOn_KvecM_comp`, `Work.OddVolterra.KernelExt.Rnu_contDiff`, ...) is stated
for the `KernelExt` presentation (`KvecM`, `G2M`, `J1M`, `J2M`, `Rnu`).  This file proves that
the two presentations agree pointwise (the recursion `RR` of `OddBridge` is the recursion `Rnu`
of `KernelExt`, `Work.OddBridge.RR_eq_Rnu`), and then transfers the regularity statements.

The main outputs are, for the open set

`GoodM h = {q : ℝ × (ℝ × St) | 0 < krad h q.2.1 (-(q.2.2 0)) q.1 ∧ 0 < krad h q.2.1 (q.2.2 1) q.1}`

(where the Abel denominator of the manifest kernel does not vanish at the two chord endpoints):

* `contDiffOn_KvecM_component_GoodM` — each component of `KvecM` is `C^∞` on `GoodM h`;
* `contDiffOn_deriv_KvecM_component_GoodM` — so is its first-slot derivative;
* `continuousOn_deriv_KvecM_component_GoodM` — hence the latter is continuous there;
* `exists_bound_region` — both are bounded by a common constant on the compact region
  `q.1 ∈ [a,b]`, `q.2.1 ∈ [a,b]`, `q.2.2 ∈ closedBall (baseState q.2.1) ρ` of the target, as soon
  as `KdenPosOn h a b` holds;
* `exists_bound_local` — and on a neighbourhood of any single point of that region.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddExistence.Manifest

open Work.OddVolterra Work.OddBridge

noncomputable section

/-! ## 1. The two presentations of the manifest data agree -/

lemma RRinit_one : Work.OddBridge.RRinit (fun (_ _ _ : ℝ) => (1 : ℝ))
    = (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) := rfl

lemma RRinit_lineSlope (h : ℝ → ℝ) :
    Work.OddBridge.RRinit (fun s _ t : ℝ => Work.OddVolterra.lineSlope h s t)
      = (fun p : ℝ × ℝ × ℝ => Work.OddVolterra.lineSlope h p.1 p.2.2) := rfl

/-- The `OddBridge` recursion `RR` with the constant initial datum is the `KernelExt` recursion
`Rnu` with the corresponding uncurried datum. -/
theorem J1M_eq_KernelExt (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (s σ t : ℝ) :
    Work.OddBridge.J1M n h s σ t = Work.OddVolterra.KernelExt.J1M n h s σ t := by
  rw [Work.OddBridge.J1M, Work.OddVolterra.KernelExt.J1M]
  have hkey := Work.OddBridge.RR_eq_Rnu ((n : ℝ) + 1 / 2) h hh (fun (_ _ _ : ℝ) => (1 : ℝ))
    contDiff_const (n + 1) (s, σ, t)
  rwa [RRinit_one] at hkey

theorem J2M_eq_KernelExt (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (s σ t : ℝ) :
    Work.OddBridge.J2M n h s σ t = Work.OddVolterra.KernelExt.J2M n h s σ t := by
  rw [Work.OddBridge.J2M, Work.OddVolterra.KernelExt.J2M]
  have hinit : ContDiff ℝ (⊤ : ℕ∞)
      (Work.OddBridge.RRinit (fun s _ t : ℝ => Work.OddVolterra.lineSlope h s t)) := by
    rw [RRinit_lineSlope h]
    unfold Work.OddVolterra.lineSlope
    fun_prop
  have hkey := Work.OddBridge.RR_eq_Rnu ((n : ℝ) - 1 / 2) h hh
    (fun s _ t : ℝ => Work.OddVolterra.lineSlope h s t) hinit n (s, σ, t)
  rwa [RRinit_lineSlope h] at hkey

theorem K1M_eq_KernelExt (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (s σ t : ℝ) :
    Work.OddBridge.K1M n h s σ t = Work.OddVolterra.KernelExt.K1M n h s σ t := by
  rw [Work.OddBridge.K1M, Work.OddVolterra.KernelExt.K1M, J1M_eq_KernelExt n hh s σ t]

theorem K2M_eq_KernelExt (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (s σ t : ℝ) :
    Work.OddBridge.K2M n h s σ t = Work.OddVolterra.KernelExt.K2M n h s σ t := by
  rw [Work.OddBridge.K2M, Work.OddVolterra.KernelExt.K2M, J2M_eq_KernelExt n hh s σ t]

theorem KvecM_eq_KernelExt (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (s σ x y x' y' : ℝ) :
    Work.OddBridge.KvecM n h s σ x y x' y'
      = Work.OddVolterra.KernelExt.KvecM n h s σ x y x' y' := by
  funext i
  fin_cases i <;>
    simp only [Work.OddBridge.KvecM, Work.OddVolterra.KernelExt.KvecM,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      K1M_eq_KernelExt n hh, K2M_eq_KernelExt n hh]

theorem G2M_eq_KernelExt (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (s σ x y x' y' : ℝ) :
    Work.OddBridge.G2M n h s σ x y x' y'
      = Work.OddVolterra.KernelExt.G2M n h s σ x y x' y' := by
  funext i
  simp only [Work.OddBridge.G2M, Work.OddVolterra.KernelExt.G2M]
  refine intervalIntegral.integral_congr (fun τ _ => ?_)
  rw [KvecM_eq_KernelExt n hh]

theorem ThetaM_eq_KernelExt (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (s σ : ℝ) (Z : St) :
    Work.OddExistence.ThetaM n h s σ Z = Work.OddVolterra.KernelExt.ThetaM n h s σ Z := by
  have h0 : (fun u : ℝ => Work.OddBridge.G2M n h u σ (Z 0) (Z 1) (Z 2) (Z 3) 0)
      = (fun u : ℝ =>
          Work.OddVolterra.KernelExt.G2M n h u σ (Z 0) (Z 1) (Z 2) (Z 3) 0) := by
    funext u
    exact congrFun (G2M_eq_KernelExt n hh u σ (Z 0) (Z 1) (Z 2) (Z 3)) 0
  have h1 : (fun u : ℝ => Work.OddBridge.G2M n h u σ (Z 0) (Z 1) (Z 2) (Z 3) 1)
      = (fun u : ℝ =>
          Work.OddVolterra.KernelExt.G2M n h u σ (Z 0) (Z 1) (Z 2) (Z 3) 1) := by
    funext u
    exact congrFun (G2M_eq_KernelExt n hh u σ (Z 0) (Z 1) (Z 2) (Z 3)) 1
  simp only [Work.OddExistence.ThetaM, Work.OddVolterra.KernelExt.ThetaM, h0, h1]

/-! ## 2. The open set where the Abel denominator does not vanish -/

/-- The open set of parameters on which the manifest kernel is smooth: both Abel radicands at
the two chord endpoints are positive. -/
def GoodM (h : ℝ → ℝ) : Set (ℝ × (ℝ × St)) :=
  {q | 0 < krad h q.2.1 (-(q.2.2 0)) q.1 ∧ 0 < krad h q.2.1 (q.2.2 1) q.1}

/-- Joint continuity of `krad` in all its arguments, in the `(a, σ, t)` order. -/
lemma continuous_krad_comp {P : Type*} [TopologicalSpace P] {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a σ t : P → ℝ}
    (ha : Continuous a) (hσ : Continuous σ) (ht : Continuous t) :
    Continuous (fun p : P => krad h (σ p) (t p) (a p)) := by
  have hq : Continuous (fun p : P => hquot h (a p) (σ p)) :=
    (Work.OddVolterra.Existence.hquot_contDiff hh).continuous.comp (ha.prodMk hσ)
  have hgs : Continuous (fun p : P => h (σ p)) := hh.continuous.comp hσ
  have hga : Continuous (fun p : P => h (a p)) := hh.continuous.comp ha
  have : (fun p : P => krad h (σ p) (t p) (a p))
      = fun p : P => (t p + hquot h (a p) (σ p)) *
          (line h (σ p) (t p) + line h (a p) (t p)) := by
    funext p; rfl
  rw [this]
  unfold line
  exact (ht.add hq).mul (((hσ.mul ht).add hgs).add ((ha.mul ht).add hga))

lemma isOpen_GoodM {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) : IsOpen (GoodM h) := by
  have hc1 : Continuous (fun q : ℝ × (ℝ × St) => krad h q.2.1 (-(q.2.2 0)) q.1) :=
    continuous_krad_comp hh (by fun_prop) (by fun_prop) (by fun_prop)
  have hc2 : Continuous (fun q : ℝ × (ℝ × St) => krad h q.2.1 (q.2.2 1) q.1) :=
    continuous_krad_comp hh (by fun_prop) (by fun_prop) (by fun_prop)
  exact isOpen_lt continuous_const hc1 |>.inter (isOpen_lt continuous_const hc2)

lemma continuous_baseState' : Continuous (Work.OddVolterra.baseState : ℝ → St) := by
  have hpx : ContDiff ℝ (⊤ : ℕ∞) Commons.Geometry.Ulam.profileX :=
    Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX
  have hdpx : Continuous (deriv Commons.Geometry.Ulam.profileX) := by
    have h := hpx.iterate_deriv 1
    simpa [Function.iterate_one] using h.continuous
  have h1 : Continuous (fun s : ℝ => Commons.Geometry.Ulam.profileX s) := hpx.continuous
  have h2 : Continuous (fun s : ℝ => deriv Commons.Geometry.Ulam.profileX s) := hdpx
  rw [show (Work.OddVolterra.baseState : ℝ → St) = fun s : ℝ =>
      ![Commons.Geometry.Ulam.profileX s, Commons.Geometry.Ulam.profileX s,
        deriv Commons.Geometry.Ulam.profileX s, deriv Commons.Geometry.Ulam.profileX s] from rfl]
  exact continuous_pi (fun i => by fin_cases i <;> simp [h1, h2])


/-! ## 3. Regularity of the manifest kernel and its first-slot derivative

We work on the curried parameter space `ℝ × (ℝ × St)`: the first coordinate is the first slope
slot `a`, the second the second slope slot `σ`, the third the state `z`. -/

lemma contDiffOn_KvecM_component_GoodM (n : ℕ) (j : Fin 2) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × St) =>
        (Work.OddBridge.KvecM n h q.1 q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j)
      (GoodM h) := by
  have hKE : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × St) =>
        Work.OddVolterra.KernelExt.KvecM n h q.1 q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3))
      (GoodM h) :=
    Work.Anchor.contDiffOn_KvecM_comp (n := n) (hh := hh) (B := GoodM h)
      (s := fun q : ℝ × (ℝ × St) => q.1) (σ := fun q => q.2.1)
      (x := fun q => q.2.2 0) (y := fun q => q.2.2 1)
      (x' := fun q => q.2.2 2) (y' := fun q => q.2.2 3)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (fun q hq => hq.1) (fun q hq => hq.2)
  have hcomp := (contDiffOn_pi.mp hKE) j
  refine hcomp.congr (fun q _ => ?_)
  exact congrFun (KvecM_eq_KernelExt n hh q.1 q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j

lemma contDiffOn_deriv_KvecM_component_GoodM (n : ℕ) (j : Fin 2) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × St) =>
        deriv (fun u : ℝ =>
          (Work.OddBridge.KvecM n h u q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j) q.1)
      (GoodM h) :=
  Work.Anchor.contDiffOn_deriv_slice_fst (P := ℝ × St) (U := GoodM h) (isOpen_GoodM hh)
    (contDiffOn_KvecM_component_GoodM n j hh)

lemma continuousOn_deriv_KvecM_component_GoodM (n : ℕ) (j : Fin 2) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContinuousOn (fun q : ℝ × (ℝ × St) =>
        deriv (fun u : ℝ =>
          (Work.OddBridge.KvecM n h u q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j) q.1)
      (GoodM h) :=
  (contDiffOn_deriv_KvecM_component_GoodM n j hh).continuousOn

/-- Continuity, on a closed interval of first arguments, of a component of the manifest kernel
and of its first-slot derivative, in terms of the two radicands. -/
lemma continuousOn_Icc_KvecM (n : ℕ) (j : Fin 2) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {σ u v : ℝ} (z : St)
    (hpos : ∀ x ∈ Set.Icc u v, 0 < krad h σ (-(z 0)) x ∧ 0 < krad h σ (z 1) x) :
    ContinuousOn (fun x : ℝ => (Work.OddBridge.KvecM n h x σ (z 0) (z 1) (z 2) (z 3)) j)
        (Set.Icc u v) ∧
      ContinuousOn (fun x : ℝ =>
        deriv (fun u' : ℝ => (Work.OddBridge.KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) j) x)
        (Set.Icc u v) := by
  have hmap : Continuous (fun x : ℝ => (x, (σ, z))) := by fun_prop
  have hmaps : Set.MapsTo (fun x : ℝ => (x, (σ, z))) (Set.Icc u v) (GoodM h) :=
    fun x hx => hpos x hx
  constructor
  · have := ((contDiffOn_KvecM_component_GoodM n j hh).continuousOn).comp hmap.continuousOn hmaps
    simpa [Function.comp_def] using this
  · have := (continuousOn_deriv_KvecM_component_GoodM n j hh).comp hmap.continuousOn hmaps
    simpa [Function.comp_def] using this

/-- The one-variable slice `x ↦ KvecM n h x σ z` is `C^∞` where the two radicands are positive. -/
lemma contDiffOn_KvecM_slice_one (n : ℕ) (j : Fin 2) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ) (z : St) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : ℝ => (Work.OddBridge.KvecM n h x σ (z 0) (z 1) (z 2) (z 3)) j)
      {x : ℝ | 0 < krad h σ (-(z 0)) x ∧ 0 < krad h σ (z 1) x} := by
  have hcomp := (contDiffOn_KvecM_component_GoodM n j hh).comp
    (by fun_prop : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => (x, (σ, z)))
      {x : ℝ | 0 < krad h σ (-(z 0)) x ∧ 0 < krad h σ (z 1) x})
    (fun x hx => hx)
  simpa only [Function.comp_def] using hcomp

/-- At every point where the two radicands are positive, the manifest kernel is differentiable
in its first slot. -/
lemma differentiableAt_KvecM_component (n : ℕ) (j : Fin 2) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {x₀ σ : ℝ} (z : St)
    (hposx : 0 < krad h σ (-(z 0)) x₀) (hposy : 0 < krad h σ (z 1) x₀) :
    DifferentiableAt ℝ (fun u : ℝ =>
      (Work.OddBridge.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) j) x₀ := by
  have hcd := contDiffOn_KvecM_slice_one n j hh σ z
  have hdiffOn := hcd.differentiableOn (by simp : (((⊤ : ℕ∞) : WithTop ℕ∞)) ≠ 0)
  have hnhds : {x : ℝ | 0 < krad h σ (-(z 0)) x ∧ 0 < krad h σ (z 1) x} ∈ 𝓝 x₀ := by
    have h1 : IsOpen {x : ℝ | 0 < krad h σ (-(z 0)) x} :=
      isOpen_lt continuous_const
        (continuous_krad_comp hh continuous_id continuous_const continuous_const)
    have h2 : IsOpen {x : ℝ | 0 < krad h σ (z 1) x} :=
      isOpen_lt continuous_const
        (continuous_krad_comp hh continuous_id continuous_const continuous_const)
    exact (h1.inter h2).mem_nhds ⟨hposx, hposy⟩
  exact (hdiffOn x₀ ⟨hposx, hposy⟩).differentiableAt hnhds

/-! ## 4. The compact region of the statement and uniform bounds -/

/-- The region of the target, in the curried parameter space. -/
def RcM (a b ρ : ℝ) : Set (ℝ × (ℝ × St)) :=
  {q | q.1 ∈ Set.Icc a b ∧ q.2.1 ∈ Set.Icc a b ∧
    q.2.2 ∈ Metric.closedBall (Work.OddVolterra.baseState q.2.1) ρ}

lemma mem_RcM_facts {a b ρ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hρ1 : ρ ≤ 1 / 2)
    {q : ℝ × (ℝ × St)} (hq : q ∈ RcM a b ρ) :
    (1 / 5 : ℝ) ≤ q.2.2 0 ∧ (1 / 5 : ℝ) ≤ q.2.2 1 ∧ (∀ i : Fin 4, |q.2.2 i| ≤ 2) := by
  obtain ⟨h1, h2, h3⟩ := hq
  have hσ : q.2.1 ∈ Set.Icc a 1 := ⟨h2.1, le_trans h2.2 hb⟩
  exact Work.OddVolterra.Existence.state_ball_box ha (le_trans hab hb) q.2.1 hσ q.2.2
    (Metric.closedBall_subset_closedBall hρ1 h3)

lemma RcM_subset_GoodM {h : ℝ → ℝ} {a b ρ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (hρ1 : ρ ≤ 1 / 2) (hpos : KdenPosOn h a b) : RcM a b ρ ⊆ GoodM h := by
  intro q hq
  obtain ⟨h1, h2, h3⟩ := hq
  obtain ⟨hz0, hz1, _⟩ := mem_RcM_facts ha hab hb hρ1 ⟨h1, h2, h3⟩
  have hz0' : (0 : ℝ) < q.2.2 0 := lt_of_lt_of_le (by norm_num) hz0
  have hz1' : (0 : ℝ) < q.2.2 1 := lt_of_lt_of_le (by norm_num) hz1
  constructor
  · exact Real.sqrt_pos.mp (hpos q.1 h1 q.2.1 h2 (-(q.2.2 0))
      (by simpa [abs_neg, abs_of_pos hz0'] using hz0))
  · exact Real.sqrt_pos.mp (hpos q.1 h1 q.2.1 h2 (q.2.2 1)
      (by simpa [abs_of_pos hz1'] using hz1))

lemma isCompact_RcM {a b ρ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1 / 2) : IsCompact (RcM a b ρ) := by
  have hbox : IsCompact (Set.Icc a b ×ˢ (Set.Icc a b ×ˢ Metric.closedBall (0 : St) 2)) :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_closedBall 0 2))
  have hcont : Continuous (fun q : ℝ × (ℝ × St) => ‖q.2.2 - Work.OddVolterra.baseState q.2.1‖) :=
    ((continuous_snd.comp continuous_snd).sub
      (continuous_baseState'.comp (continuous_fst.comp continuous_snd))).norm
  have hclosed : IsClosed (RcM a b ρ) := by
    have h1 : IsClosed {q : ℝ × (ℝ × St) | q.1 ∈ Set.Icc a b} :=
      isClosed_Icc.preimage continuous_fst
    have h2 : IsClosed {q : ℝ × (ℝ × St) | q.2.1 ∈ Set.Icc a b} :=
      isClosed_Icc.preimage (continuous_fst.comp continuous_snd)
    have h3 : IsClosed {q : ℝ × (ℝ × St) | ‖q.2.2 - Work.OddVolterra.baseState q.2.1‖ ≤ ρ} :=
      isClosed_le hcont continuous_const
    have hEq : RcM a b ρ = {q : ℝ × (ℝ × St) | q.1 ∈ Set.Icc a b} ∩
        {q : ℝ × (ℝ × St) | q.2.1 ∈ Set.Icc a b} ∩
        {q : ℝ × (ℝ × St) | ‖q.2.2 - Work.OddVolterra.baseState q.2.1‖ ≤ ρ} := by
      ext q
      simp only [RcM, Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_eq_norm]
      tauto
    rw [hEq]
    exact (h1.inter h2).inter h3
  refine hbox.of_isClosed_subset hclosed (fun q hq => ?_)
  obtain ⟨h1, h2, h3⟩ := hq
  obtain ⟨hz0, hz1, hz2⟩ := mem_RcM_facts ha hab hb hρ1 ⟨h1, h2, h3⟩
  refine ⟨h1, h2, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (fun i => by
    simpa only [Real.norm_eq_abs] using hz2 i)

/-- **Uniform bound on the compact region.** On the region of the statement both a component of
the manifest kernel and its first-slot derivative are bounded by a common constant. -/
lemma exists_bound_RcM (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {a b ρ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hpos : KdenPosOn h a b) (j : Fin 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ RcM a b ρ,
      ‖(Work.OddBridge.KvecM n h q.1 q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j‖ ≤ C ∧
      ‖deriv (fun u : ℝ =>
        (Work.OddBridge.KvecM n h u q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j) q.1‖ ≤ C := by
  have hsub := RcM_subset_GoodM ha hab hb hρ1 hpos
  have hcomp := isCompact_RcM ha hab hb hρ0 hρ1
  have hc1 : ContinuousOn (fun q : ℝ × (ℝ × St) =>
      (Work.OddBridge.KvecM n h q.1 q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j)
      (RcM a b ρ) := (contDiffOn_KvecM_component_GoodM n j hh).continuousOn.mono hsub
  have hc2 : ContinuousOn (fun q : ℝ × (ℝ × St) =>
      deriv (fun u : ℝ =>
        (Work.OddBridge.KvecM n h u q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j) q.1)
      (RcM a b ρ) := (continuousOn_deriv_KvecM_component_GoodM n j hh).mono hsub
  obtain ⟨C1, hC1⟩ := hcomp.exists_bound_of_continuousOn hc1
  obtain ⟨C2, hC2⟩ := hcomp.exists_bound_of_continuousOn hc2
  refine ⟨max (max C1 C2) 1, by positivity, fun q hq => ⟨?_, ?_⟩⟩
  · exact le_trans (hC1 q hq) (le_max_of_le_left (le_max_left _ _))
  · exact le_trans (hC2 q hq) (le_max_of_le_left (le_max_right _ _))

/-- **Local data.** At every point of the region there is a symmetric neighbourhood of the
first slot on which both radicands stay positive and a component of the manifest kernel together
with its first-slot derivative is bounded by a constant. -/
lemma exists_bound_local (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {a b ρ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hρ1 : ρ ≤ 1 / 2)
    (hpos : KdenPosOn h a b) {q : ℝ × (ℝ × St)} (hq : q ∈ RcM a b ρ) (j : Fin 2) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ x ∈ Set.Icc (q.1 - δ) (q.1 + δ),
        0 < krad h q.2.1 (-(q.2.2 0)) x ∧ 0 < krad h q.2.1 (q.2.2 1) x) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Icc (q.1 - δ) (q.1 + δ),
        ‖(Work.OddBridge.KvecM n h x q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j‖ ≤ C ∧
        ‖deriv (fun u : ℝ =>
          (Work.OddBridge.KvecM n h u q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j) x‖ ≤ C := by
  obtain ⟨h1, h2, h3⟩ := hq
  obtain ⟨hz0, hz1, _⟩ := mem_RcM_facts ha hab hb hρ1 ⟨h1, h2, h3⟩
  have hz0' : (0 : ℝ) < q.2.2 0 := lt_of_lt_of_le (by norm_num) hz0
  have hz1' : (0 : ℝ) < q.2.2 1 := lt_of_lt_of_le (by norm_num) hz1
  have hs0 : 0 < krad h q.2.1 (-(q.2.2 0)) q.1 :=
    Real.sqrt_pos.mp (hpos q.1 h1 q.2.1 h2 (-(q.2.2 0))
      (by simpa [abs_neg, abs_of_pos hz0'] using hz0))
  have hs1 : 0 < krad h q.2.1 (q.2.2 1) q.1 :=
    Real.sqrt_pos.mp (hpos q.1 h1 q.2.1 h2 (q.2.2 1)
      (by simpa [abs_of_pos hz1'] using hz1))
  have hcont0 : ContinuousAt (fun x : ℝ => krad h q.2.1 (-(q.2.2 0)) x) q.1 :=
    (continuous_krad_comp (P := ℝ) hh continuous_id continuous_const continuous_const).continuousAt
  have hcont1 : ContinuousAt (fun x : ℝ => krad h q.2.1 (q.2.2 1) x) q.1 :=
    (continuous_krad_comp (P := ℝ) hh continuous_id continuous_const continuous_const).continuousAt
  obtain ⟨ε0, hε0pos, hε0⟩ :=
    Metric.continuousAt_iff.mp hcont0 (krad h q.2.1 (-(q.2.2 0)) q.1) hs0
  obtain ⟨ε1, hε1pos, hε1⟩ :=
    Metric.continuousAt_iff.mp hcont1 (krad h q.2.1 (q.2.2 1) q.1) hs1
  have hδpos : 0 < min ε0 ε1 / 2 := by positivity
  have hmem : ∀ x ∈ Set.Icc (q.1 - min ε0 ε1 / 2) (q.1 + min ε0 ε1 / 2),
      0 < krad h q.2.1 (-(q.2.2 0)) x ∧ 0 < krad h q.2.1 (q.2.2 1) x := by
    intro x hx
    have hmin0 : min ε0 ε1 ≤ ε0 := min_le_left _ _
    have hmin1 : min ε0 ε1 ≤ ε1 := min_le_right _ _
    have hdist0 : dist x q.1 < ε0 := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2, hmin0, hε0pos]
    have hdist1 : dist x q.1 < ε1 := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2, hmin1, hε1pos]
    have h0 := hε0 hdist0
    have h1' := hε1 hdist1
    rw [Real.dist_eq, abs_lt] at h0 h1'
    exact ⟨by linarith [h0.1], by linarith [h1'.1]⟩
  obtain ⟨hb1, hb2⟩ := continuousOn_Icc_KvecM n j hh q.2.2 hmem
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn hb1
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn hb2
  exact ⟨min ε0 ε1 / 2, hδpos, hmem, max (max C1 C2) 1, by positivity, fun x hx =>
    ⟨le_trans (hC1 x hx) (le_max_of_le_left (le_max_left _ _)),
     le_trans (hC2 x hx) (le_max_of_le_left (le_max_right _ _))⟩⟩

end

end Work.OddExistence.Manifest
