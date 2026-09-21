import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.JetBound
import Submission.Work.OddVolterra.Smooth.E1_E2_regularity
import Submission.Work.OddVolterra.Smooth.Q_regularity
import Submission.Work.OddVolterra.Abel.abel_transform_diff
import Submission.Work.OddVolterra.Existence.abel_deriv_bound
import Submission.Work.OddVolterra.Existence.E1_E2_diff_bounds
import Submission.Work.Analysis.Calculus.parametric_iteratedDeriv_bound
import Submission.Work.OddVolterra.Smooth.E1_E2_continuousOn_Icc

/-!
# `Xi` is continuous at `h = 0` in the `C^{n+2}` topology

The statement `Work.OddVolterra.Existence.xi_close_of_small` says that the `Ξ`-data of the odd
transition-slope system depends continuously on the perturbation `h` in the `C^{n+2}` topology.
Since the first two components of `Ξ` do not depend on `h`, this is a statement about

`Q̃ n h s i = deriv (fun u => ∫_v u..1, (Q n h v) i / √(v-u)) s`,

i.e. about the derivative of the Abel transform of the inhomogeneity `Q n h = (-E₁ + c, -E₂)`.

The proof has three ingredients.

* `E₁` and `E₂` are parametric integrals of iterated `u`-derivatives of the slice
  `u ↦ ψ_h(u,t)^{n+1/2}`, with `ψ_h(u,t) = 1 - t² - (u t + h u)²`; on the box
  `[a/2, 1-τ] × [-1/100, 1/100] × [-√2⁻¹, √2⁻¹]` the model radicand stays strictly positive,
  so the slices are the composites `u ↦ Φ(u, h u, t)` of a *fixed* smooth function `Φ` with the
  graph of `h`, and the parameterised jet bound `exists_bound_comp_pair_sub_param` makes the
  difference `Eᵢ n h v - Eᵢ n 0 v` Lipschitz of size `C δ` in `v`.
* The difference of the two Abel transforms is the Abel transform of `g = Q n h - Q n 0`, which
  vanishes above `1-τ`; `abel_deriv_bound` bounds the derivative of that Abel transform by
  `C' δ`.
* Below the transition window the two Abel transforms already coincide, since `h ≡ 0` there.

The file isolates the analysis into the two lemmas `xiC_E1_E2_bounds` (jet bounds for the
inhomogeneities) and the final assembly.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Existence

open Commons.Geometry.Ulam

noncomputable section

/-! ## The model radicand and the two outer functions -/

/-- The model radicand `1 - t² - (x t + y)²`, where `y` is the value of the perturbation at the
slope `u = x` and `t` is the coordinate along the section. -/
def xiRad (x y t : ℝ) : ℝ := 1 - t ^ 2 - (x * t + y) ^ 2

/-- The `E₁` integrand as a function of the triple `(slope, perturbation value, section)`. -/
def xiPhiF (n : ℕ) (p : ℝ × ℝ × ℝ) : ℝ :=
  xiRad p.1 p.2.1 p.2.2 ^ n * Real.sqrt (xiRad p.1 p.2.1 p.2.2)

/-- The radicand part of the `E₂` integrand as a function of the triple
`(slope, perturbation value, section)`. -/
def xiPhiB (n : ℕ) (p : ℝ × ℝ × ℝ) : ℝ :=
  xiRad p.1 p.2.1 p.2.2 ^ (n - 1) * Real.sqrt (xiRad p.1 p.2.1 p.2.2)

/-- The open set of triples on which the model radicand is positive. -/
def xiUpos : Set (ℝ × ℝ × ℝ) := {p | 0 < xiRad p.1 p.2.1 p.2.2}

lemma xiRad_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => xiRad p.1 p.2.1 p.2.2) := by
  unfold xiRad
  fun_prop

lemma isOpen_xiUpos : IsOpen xiUpos :=
  isOpen_lt continuous_const xiRad_contDiff.continuous

lemma contDiffOn_xiPhiF (n : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xiPhiF n) xiUpos := by
  have hrad : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ × ℝ => xiRad p.1 p.2.1 p.2.2) xiUpos := xiRad_contDiff.contDiffOn
  exact (hrad.pow n).mul (hrad.sqrt (fun p hp => ne_of_gt hp))

lemma contDiffOn_xiPhiB (n : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xiPhiB n) xiUpos := by
  have hrad : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ × ℝ => xiRad p.1 p.2.1 p.2.2) xiUpos := xiRad_contDiff.contDiffOn
  exact (hrad.pow (n - 1)).mul (hrad.sqrt (fun p hp => ne_of_gt hp))

/-! ## Positivity of the model radicand on the box -/

lemma profileX_one_sq' : (profileX 1) ^ 2 = (1 : ℝ) / 2 := by
  simpa using Work.OddVolterra.Smooth.profileX_one_sq

lemma half_lt_profileX_one : (1 : ℝ) / 2 < profileX 1 := by
  have h := profileX_one_sq'
  have hp : (0:ℝ) < profileX 1 := profileX_pos 1 (by norm_num)
  nlinarith

/-- On the box `[c, 1-τ] × [-1/100, 1/100] × [-√2⁻¹, √2⁻¹]` (with `0 < c ≤ 1-τ`) the model
radicand is positive. -/
lemma xi_box_pos {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 - tau)
    {x y t : ℝ} (hx : x ∈ Set.Icc c (1 - tau)) (hy : |y| ≤ 1 / 100)
    (ht : |t| ≤ profileX 1) : 0 < xiRad x y t := by
  have hp : (0:ℝ) < profileX 1 := profileX_pos 1 (by norm_num)
  have hp2 := profileX_one_sq'
  have hphalf := half_lt_profileX_one
  have ht9 : (1 : ℝ) - tau = 9 / 10 := Work.OddVolterra.Smooth.one_sub_tau_eq
  have hx1 : |x| ≤ 1 - tau := by
    rw [abs_le]
    exact ⟨by linarith [hx.1, hc], hx.2⟩
  have hb : |x * t + y| ≤ (1 - tau) * profileX 1 + 1 / 100 := by
    calc |x * t + y| ≤ |x * t| + |y| := abs_add_le _ _
      _ = |x| * |t| + |y| := by rw [abs_mul]
      _ ≤ (1 - tau) * profileX 1 + 1 / 100 := by
          have h1 : |x| * |t| ≤ (1 - tau) * profileX 1 :=
            mul_le_mul hx1 ht (abs_nonneg _) (by linarith [hx.1, hc])
          linarith
  have hkey : (1 - tau) * profileX 1 + 1 / 100 < profileX 1 := by
    rw [ht9]
    nlinarith
  have hsq : (x * t + y) ^ 2 < profileX 1 ^ 2 := by
    rw [sq_lt_sq, abs_of_pos hp]
    exact hb.trans_lt hkey
  have ht2 : t ^ 2 ≤ profileX 1 ^ 2 := by
    rw [sq_le_sq, abs_of_pos hp]
    exact ht
  rw [xiRad, hp2] at *
  linarith

/-! ## The box is contained in the positivity region -/

lemma xi_box_subset_xiUpos {c R p : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 - tau)
    (hR : R ≤ 1 / 100) (hp : p = profileX 1) :
    (Set.Icc c (1 - tau) ×ˢ Set.Icc (-R) R ×ˢ Set.Icc (-p) p : Set (ℝ × ℝ × ℝ))
      ⊆ xiUpos := by
  rintro ⟨x, y, t⟩ ⟨hx, hy, ht⟩
  have hy' : |y| ≤ 1 / 100 := by
    rw [abs_le]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have ht' : |t| ≤ profileX 1 := by
    rw [abs_le]
    exact ⟨by linarith [ht.1, hp], by linarith [ht.2, hp]⟩
  exact xi_box_pos hc hc1 hx hy' ht'

/-! ## The `E₁`/`E₂` integrands as composites of the graph of `h` -/

/-- On the box the model radicand is the genuine radicand `ψ_h`. -/
lemma xi_psi_eq (n : ℕ) {h : ℝ → ℝ} {t : ℝ} (ht : |t| ≤ 1) :
    (fun u : ℝ => psi h semicircle u t ^ n * Real.sqrt (psi h semicircle u t)) =
      fun u : ℝ => xiPhiF n (u, h u, t) := by
  funext u
  rw [Work.OddVolterra.Smooth.psi_eq_quad ht]
  rfl

lemma xi_psi_eq' (n : ℕ) {h : ℝ → ℝ} {t : ℝ} (ht : |t| ≤ 1) :
    (fun u : ℝ => psi h semicircle u t ^ (n - 1) * Real.sqrt (psi h semicircle u t)
        * lineSlope h u t) =
      fun u : ℝ => xiPhiB n (u, h u, t) * lineSlope h u t := by
  funext u
  rw [Work.OddVolterra.Smooth.psi_eq_quad ht]
  rfl

lemma profileX_one_pos' : (0 : ℝ) < profileX 1 := profileX_pos 1 (by norm_num)

lemma abs_le_one_of_mem_uIcc_profileX {t : ℝ}
    (ht : t ∈ Set.uIcc (-(profileX 1)) (profileX 1)) : |t| ≤ 1 := by
  rw [Set.uIcc_of_le (by linarith [profileX_one_pos'])] at ht
  have h1 := Work.OddVolterra.Smooth.profileX_one_le_one
  rw [abs_le]
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- The `E₁` integral as the parametric integral of the graph composite. -/
lemma xi_E1_eq (n : ℕ) (h : ℝ → ℝ) (x : ℝ) :
    E1 n h x = ∫ t in (-(profileX 1))..(profileX 1),
      iteratedDeriv (n + 1) (fun u : ℝ => xiPhiF n (u, h u, t)) x := by
  rw [E1]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [xi_psi_eq n (abs_le_one_of_mem_uIcc_profileX ht)]

/-- The `E₂` integral as the parametric integral of the graph composite. -/
lemma xi_E2_eq (n : ℕ) (h : ℝ → ℝ) (x : ℝ) :
    E2 n h x = ∫ t in (-(profileX 1))..(profileX 1),
      iteratedDeriv n (fun u : ℝ => xiPhiB n (u, h u, t) * lineSlope h u t) x := by
  rw [E2]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [xi_psi_eq' n (abs_le_one_of_mem_uIcc_profileX ht)]

/-! ## Smoothness of the graph composites -/

lemma xi_contDiffAt_PhiF (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {x t : ℝ}
    (hx : (x, h x, t) ∈ xiUpos) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => xiPhiF n (u, h u, t)) x := by
  have hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => (u, h u, t)) x := by
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h x := hh.contDiffAt
    fun_prop
  exact ((contDiffOn_xiPhiF n).contDiffAt (isOpen_xiUpos.mem_nhds hx)).comp x hg

lemma xi_contDiffAt_PhiB (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {x t : ℝ}
    (hx : (x, h x, t) ∈ xiUpos) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => xiPhiB n (u, h u, t)) x := by
  have hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => (u, h u, t)) x := by
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h x := hh.contDiffAt
    fun_prop
  exact ((contDiffOn_xiPhiB n).contDiffAt (isOpen_xiUpos.mem_nhds hx)).comp x hg

/-! ## Uniform bounds for the unperturbed slices -/

/-- Uniform bounds on the ball slices `u ↦ xiPhiB n (u, 0, t)` on the box. -/
lemma xi_ball_slice_bounds (n : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 - tau) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v ∈ Set.Icc c (1 - tau),
      ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
      |iteratedDeriv k (fun u : ℝ => xiPhiB n (u, 0, t)) v| ≤ M := by
  set U : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 < xiRad q.2 0 q.1} with hUdef
  have hU : IsOpen U := by
    rw [hUdef]
    exact isOpen_lt continuous_const (by unfold xiRad; fun_prop)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => xiPhiB n (q.2, 0, q.1)) U := by
    have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => xiRad q.2 0 q.1) U :=
      (by unfold xiRad; fun_prop : ContDiff ℝ (⊤ : ℕ∞)
        (fun q : ℝ × ℝ => xiRad q.2 0 q.1)).contDiffOn
    exact (hcomp.pow (n - 1)).mul (hcomp.sqrt (fun q hq => ne_of_gt hq))
  set K : Set (ℝ × ℝ) := Set.Icc (-(profileX 1)) (profileX 1) ×ˢ Set.Icc c (1 - tau)
    with hKdef
  have hK : IsCompact K := by rw [hKdef]; exact isCompact_Icc.prod isCompact_Icc
  have hKU : K ⊆ U := by
    rintro ⟨t, v⟩ ⟨ht, hv⟩
    have ht' : |t| ≤ profileX 1 := by
      rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
    exact xi_box_pos hc hc1 hv (by norm_num) ht'
  obtain ⟨M, hM⟩ := Work.OddVolterra.Smooth.parametric_iteratedDeriv_bound_smooth
    (F := fun t u : ℝ => xiPhiB n (u, 0, t)) hU hF hK hKU k
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro v hv t ht
  have hmem : (t, v) ∈ K := by
    rw [hKdef]
    exact ⟨⟨by linarith [ht.1], ht.2⟩, hv⟩
  have h1 : |iteratedDeriv k (fun u : ℝ => xiPhiB n (u, 0, t)) v| ≤ M := hM (t, v) hmem
  exact le_trans h1 (le_max_left M 0)

/-! ## The inhomogeneities agree above the transition window -/

lemma xiC_h_eventually_zero {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {v : ℝ}
    (hv : 1 - tau < v) : h =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
  filter_upwards [isOpen_Ioi.mem_nhds hv] with u hu
  exact Work.OddVolterra.Smooth.h_eq_zero_of_gt hsupp hu

lemma xiC_deriv_eventually_zero {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {v : ℝ}
    (hv : 1 - tau < v) : deriv h =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
  filter_upwards [isOpen_Ioi.mem_nhds hv] with u hu
  exact Work.OddVolterra.Smooth.deriv_eq_zero_of_gt hsupp hu

lemma xiC_psi_eventually {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {v t : ℝ}
    (hv : 1 - tau < v) :
    (fun u : ℝ => psi h semicircle u t) =ᶠ[𝓝 v]
      (fun u : ℝ => psi (0 : ℝ → ℝ) semicircle u t) := by
  filter_upwards [xiC_h_eventually_zero hsupp hv] with u hu
  simp only [psi, line, hu, Pi.zero_apply, add_zero]

lemma xiCE1_eventually {n : ℕ} {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {v t : ℝ}
    (hv : 1 - tau < v) :
    (fun u : ℝ => psi h semicircle u t ^ n * Real.sqrt (psi h semicircle u t)) =ᶠ[𝓝 v]
      (fun u : ℝ => psi (0 : ℝ → ℝ) semicircle u t ^ n
        * Real.sqrt (psi (0 : ℝ → ℝ) semicircle u t)) := by
  filter_upwards [xiC_psi_eventually hsupp hv] with u hu
  rw [hu]

lemma xiCE2_eventually {n : ℕ} {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {v t : ℝ}
    (hv : 1 - tau < v) :
    (fun u : ℝ => psi h semicircle u t ^ (n - 1) * Real.sqrt (psi h semicircle u t)
        * lineSlope h u t) =ᶠ[𝓝 v]
      (fun u : ℝ => psi (0 : ℝ → ℝ) semicircle u t ^ (n - 1)
        * Real.sqrt (psi (0 : ℝ → ℝ) semicircle u t) * lineSlope (0 : ℝ → ℝ) u t) := by
  filter_upwards [xiC_psi_eventually (t := t) hsupp hv, xiC_deriv_eventually_zero hsupp hv] with u hu hd
  have hz : deriv (0 : ℝ → ℝ) u = 0 := by simp [deriv_zero]
  simp only [lineSlope, hu, hd, hz, add_zero]

lemma xiC_E1_eq_of_gt (n : ℕ) {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {v : ℝ}
    (hv : 1 - tau < v) : E1 n h v = E1 n 0 v := by
  rw [E1, E1]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  exact Filter.EventuallyEq.iteratedDeriv_eq (n + 1) (xiCE1_eventually hsupp hv)

lemma xiC_E2_eq_of_gt (n : ℕ) {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {v : ℝ}
    (hv : 1 - tau < v) : E2 n h v = E2 n 0 v := by
  rw [E2, E2]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  exact Filter.EventuallyEq.iteratedDeriv_eq n (xiCE2_eventually hsupp hv)

lemma xiC_Q_eq_of_gt (n : ℕ) {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {v : ℝ}
    (hv : 1 - tau < v) : Q n h v = Q n 0 v := by
  funext i
  fin_cases i
  · simp only [Q]
    rw [xiC_E1_eq_of_gt n hsupp hv]
    rfl
  · simp only [Q]
    rw [xiC_E2_eq_of_gt n hsupp hv]
    rfl

lemma xiC_mem_hmid {h : ℝ → ℝ} (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) :
    ∀ s ∈ Set.Ioo (0 : ℝ) 1, ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
      0 < psi h semicircle s t := by
  intro s hs t ht
  exact Work.OddVolterra.Smooth.psi_pos_of_window hsupp hsmall hs.1 hs.2 (abs_le.mpr ht)

lemma xiC_mem_hmid_zero :
    ∀ s ∈ Set.Ioo (0 : ℝ) 1, ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
      0 < psi (0 : ℝ → ℝ) semicircle s t :=
  xiC_mem_hmid (by simp) (by intro t; simp)

/-- `Q n h` and `Q n 0` agree on the closed window `[1-τ, 1]`.  Above the window this is
locality of the derivatives, at `1-τ` itself it follows from continuity of `Q` on `[a', 1]`
together with the vanishing on `(1-τ, 1]`. -/
lemma xiC_Q_eq_of_ge (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) {a' : ℝ} (ha' : 0 < a') (ha't : a' < 1 - tau) :
    ∀ v : ℝ, 1 - tau ≤ v → Q n h v = Q n 0 v := by
  have hmid := xiC_mem_hmid hsupp hsmall
  have hmid0 := xiC_mem_hmid_zero
  have hQh := (Work.OddVolterra.Smooth.Q_regularity n hn hh ha' hsupp hsmall hmid).1
  have hsupp0 : Function.support (0 : ℝ → ℝ) ⊆ Set.Icc (1 - 2 * tau) (1 - tau) := by
    intro x hx
    rw [Function.mem_support] at hx
    exact absurd rfl hx
  have hsmall0 : ∀ t : ℝ, |(0 : ℝ → ℝ) t| ≤ 1 / 100 := by
    intro t
    rw [Pi.zero_apply, abs_zero]
    norm_num
  have hQ0 := (Work.OddVolterra.Smooth.Q_regularity n hn contDiff_const ha'
    hsupp0 hsmall0 hmid0).1
  intro v hv
  rcases lt_or_eq_of_le hv with hlt | heq
  · exact xiC_Q_eq_of_gt n hsupp hlt
  · subst heq
    funext i
    have hgcont : ContinuousOn
        (fun w : ℝ => (Q n h w) i - (Q n 0 w) i) (Set.Icc a' 1) :=
      ((continuous_apply i).comp_continuousOn hQh).sub
        ((continuous_apply i).comp_continuousOn hQ0)
    have hZ : IsClosed (Set.Icc a' 1 ∩
        (fun w : ℝ => (Q n h w) i - (Q n 0 w) i) ⁻¹' {0}) :=
      hgcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hcl : closure (Set.Ioc (1 - tau) 1) ⊆
        Set.Icc a' 1 ∩ (fun w : ℝ => (Q n h w) i - (Q n 0 w) i) ⁻¹' {0} := by
      rw [hZ.closure_subset_iff]
      intro w hw
      refine ⟨⟨le_of_lt (lt_trans ha't hw.1), hw.2⟩, ?_⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      rw [show ((Q n h w) i) = (Q n 0 w) i from congrFun (xiC_Q_eq_of_gt n hsupp hw.1) i,
        sub_self]
    have hmem : (1 - tau) ∈ closure (Set.Ioc (1 - tau) 1) := by
      rw [closure_Ioc (by norm_num [tau]), Set.mem_Icc]
      exact ⟨le_rfl, by norm_num [tau]⟩
    have h0 : (fun w : ℝ => (Q n h w) i - (Q n 0 w) i) (1 - tau) = 0 := by
      simpa using (hcl hmem).2
    exact sub_eq_zero.mp h0

/-- The Abel transform of `φ` written as a non-singular parametric integral. -/
lemma xiC_abel_subst {φ : ℝ → ℝ} {u : ℝ} (hu : u ≤ 1) :
    (∫ v in u..1, φ v / Real.sqrt (v - u)) =
      2 * Real.sqrt (1 - u) * ∫ t in (0 : ℝ)..1, φ (u + (1 - u) * t ^ 2) := by
  have h := Commons.Analysis.Abel.intervalIntegral_abel_subst (x := u) (b := 1) hu
    (E := ℝ) (fun _ σ => φ σ)
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- Linear decomposition of the difference of two Abel transforms. -/
lemma xiC_abel_linear {φ ψ : ℝ → ℝ} {a' s : ℝ} (ha's : a' < s) (hs1 : s < 1)
    (hφ : ContinuousOn φ (Set.Icc a' 1)) (hψ : ContinuousOn ψ (Set.Icc a' 1)) :
    (fun u : ℝ => ∫ v in u..1, φ v / Real.sqrt (v - u))
        - (fun u : ℝ => ∫ v in u..1, ψ v / Real.sqrt (v - u))
      =ᶠ[𝓝 s] fun u : ℝ => ∫ v in u..1, (φ v - ψ v) / Real.sqrt (v - u) := by
  filter_upwards [Ioo_mem_nhds ha's hs1] with u hu
  have hu1 : u ≤ 1 := le_of_lt hu.2
  have hpath : ContinuousOn (fun t : ℝ => u + (1 - u) * t ^ 2) (Set.uIcc (0 : ℝ) 1) := by
    fun_prop
  have hmem : Set.MapsTo (fun t : ℝ => u + (1 - u) * t ^ 2) (Set.uIcc (0 : ℝ) 1)
      (Set.Icc a' 1) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have ht20 : 0 ≤ t ^ 2 := sq_nonneg t
    have h1mu : 0 ≤ 1 - u := by linarith [hu.2]
    exact ⟨by nlinarith [hu.1, mul_nonneg h1mu ht20],
      by nlinarith [hu.2, ht2, ht20, mul_nonneg h1mu ht20]⟩
  have hI1 : IntervalIntegrable (fun t : ℝ => φ (u + (1 - u) * t ^ 2)) volume (0 : ℝ) 1 :=
    (hφ.comp' hpath hmem).intervalIntegrable
  have hI2 : IntervalIntegrable (fun t : ℝ => ψ (u + (1 - u) * t ^ 2)) volume (0 : ℝ) 1 :=
    (hψ.comp' hpath hmem).intervalIntegrable
  show (∫ v in u..1, φ v / Real.sqrt (v - u)) - (∫ v in u..1, ψ v / Real.sqrt (v - u))
      = ∫ v in u..1, (φ v - ψ v) / Real.sqrt (v - u)
  rw [xiC_abel_subst (φ := φ) hu1, xiC_abel_subst (φ := ψ) hu1,
    xiC_abel_subst (φ := fun v => φ v - ψ v) hu1]
  rw [← mul_sub, ← intervalIntegral.integral_sub hI1 hI2]

/-- Differentiability of the (scalar) Abel transform of a component of `Q n h` in the window. -/
lemma xiC_differentiableAt (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) {a' : ℝ} (ha' : 0 < a') (i : Fin 2) {s : ℝ}
    (hs : s ∈ Set.Ioo a' 1) :
    DifferentiableAt ℝ (fun u : ℝ => ∫ v in u..1, (Q n h v) i / Real.sqrt (v - u)) s := by
  have hQ := Work.OddVolterra.Smooth.Q_regularity n hn hh ha' hsupp hsmall (xiC_mem_hmid hsupp hsmall)
  have hcont : ContinuousOn (fun v : ℝ => (Q n h v) i) (Set.Icc a' 1) :=
    (continuous_apply i).comp_continuousOn hQ.1
  have hsm : ∀ b : ℝ, a' < b → b < 1 →
      ContDiffOn ℝ 2 (fun v : ℝ => (Q n h v) i) (Set.Icc a' b) := by
    intro b hb hb1
    have := ((ContinuousLinearMap.proj i).contDiff).comp_contDiffOn (hQ.2 b hb hb1)
    simpa [Function.comp_def] using this
  have hd := Work.OddVolterra.Abel.abel_transform_diff (E := ℝ) (a := a')
    (Q := fun v : ℝ => (Q n h v) i) (lt_trans hs.1 hs.2) hcont hsm s hs
  have hfun : (fun u : ℝ => ∫ v in u..1, (Real.sqrt (v - u))⁻¹ • ((Q n h v) i)) =
      fun u : ℝ => ∫ v in u..1, (Q n h v) i / Real.sqrt (v - u) := by
    funext u
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rwa [hfun] at hd

/-! ## The main estimate -/

/-- The components of `Q n h - Q n 0` are (up to sign) the differences of the inhomogeneities
`E₁`, `E₂`. -/
lemma xiC_Q_sub_zero (n : ℕ) (h : ℝ → ℝ) (v : ℝ) :
    (Q n h v) 0 - (Q n 0 v) 0 = -(E1 n h v - E1 n 0 v) := by
  change (-E1 n h v + iteratedDeriv (n + 1) (momentRHS n) v)
      - (-E1 n 0 v + iteratedDeriv (n + 1) (momentRHS n) v) = _
  ring

lemma xiC_Q_sub_one (n : ℕ) (h : ℝ → ℝ) (v : ℝ) :
    (Q n h v) 1 - (Q n 0 v) 1 = -(E2 n h v - E2 n 0 v) := by
  change (-E2 n h v) - (-E2 n 0 v) = _
  ring

/-- The main reduction: given the `δ`-bounds for the inhomogeneities `E₁`, `E₂`
(`E1_E2_diff_bounds`) and the bound for the derivative of the Abel transform
(`abel_deriv_bound`), the `Ξ`-data is continuous at `h = 0`. -/
theorem xiC_aux (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hE1E2 : ∃ C δ₀ : ℝ, 0 ≤ C ∧ 0 < δ₀ ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ δ₀ →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      (∀ v ∈ Set.Icc (a / 2) (1 - tau), |E1 n h v - E1 n 0 v| ≤ C * δ) ∧
      (∀ v ∈ Set.Icc (a / 2) (1 - tau), ∀ v' ∈ Set.Icc (a / 2) (1 - tau),
        |(E1 n h v - E1 n 0 v) - (E1 n h v' - E1 n 0 v')| ≤ C * δ * |v - v'|) ∧
      (∀ v ∈ Set.Icc (a / 2) (1 - tau), |E2 n h v - E2 n 0 v| ≤ C * δ) ∧
      (∀ v ∈ Set.Icc (a / 2) (1 - tau), ∀ v' ∈ Set.Icc (a / 2) (1 - tau),
        |(E2 n h v - E2 n 0 v) - (E2 n h v' - E2 n 0 v')| ≤ C * δ * |v - v'|))
    (hAb : ∀ {c d b₀ η : ℝ} (hcd : c < d) (hdb : d ≤ b₀) (hb₁ : b₀ ≤ 1) (hη : 0 ≤ η)
      {g : ℝ → ℝ} (hzero : ∀ v : ℝ, b₀ ≤ v → g v = 0)
      (hlip : ∀ u ∈ Set.Icc c b₀, ∀ v ∈ Set.Icc c b₀, |g u - g v| ≤ η * |u - v|),
      ∀ s ∈ Set.Icc d 1,
        |deriv (fun u : ℝ => ∫ v in u..(1 : ℝ), g v / Real.sqrt (v - u)) s|
          ≤ 10 * Real.sqrt (b₀ - c + 1) * η) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      (∀ s ∈ Set.Icc a 1, ‖Work.OddVolterra.Xi n h s - Work.OddVolterra.Xi n 0 s‖ < ε) := by
  intro ε hε
  obtain ⟨C, δ₀, hC0, hδ0pos, hE⟩ := hE1E2
  set η₀ : ℝ := 10 * Real.sqrt ((1 - tau) - a / 2 + 1) * C with hη₀def
  have hη₀nn : 0 ≤ η₀ := by
    rw [hη₀def]
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hC0
  set δ : ℝ := min δ₀ (min (1 / 100) (ε / (η₀ + 1))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min hδ0pos (lt_min (by norm_num) (by positivity))
  have hδle0 : δ ≤ δ₀ := by rw [hδdef]; exact min_le_left _ _
  have hδle100 : δ ≤ 1 / 100 := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδleε : δ ≤ ε / (η₀ + 1) := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hηδ : η₀ * δ < ε := by
    have h1 : η₀ * δ ≤ η₀ * (ε / (η₀ + 1)) := mul_le_mul_of_nonneg_left hδleε hη₀nn
    have h2 : η₀ * (ε / (η₀ + 1)) < ε := by
      rw [← mul_div_assoc, div_lt_iff₀ (by linarith : (0 : ℝ) < η₀ + 1)]
      nlinarith [hε, hη₀nn]
    linarith
  refine ⟨δ, hδpos, ?_⟩
  intro h hh hsupp hjet
  have hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100 := by
    intro t
    have h0 : |iteratedDeriv 0 h t| ≤ δ := hjet 0 (by omega) t
    rw [iteratedDeriv_zero] at h0
    exact le_trans h0 hδle100
  have hmid := xiC_mem_hmid hsupp hsmall
  have hsupp0 : Function.support (0 : ℝ → ℝ) ⊆ Set.Icc (1 - 2 * tau) (1 - tau) := by
    intro x hx
    rw [Function.mem_support] at hx
    exact absurd rfl hx
  have hsmall0 : ∀ t : ℝ, |(0 : ℝ → ℝ) t| ≤ 1 / 100 := by
    intro t
    rw [Pi.zero_apply, abs_zero]
    norm_num
  have hmid0 := xiC_mem_hmid_zero
  have hQh := Work.OddVolterra.Smooth.Q_regularity n hn hh (a := a / 2) (by linarith) hsupp hsmall hmid
  have hQh0 := Work.OddVolterra.Smooth.Q_regularity n hn contDiff_const (a := a / 2)
    (by linarith) hsupp0 hsmall0 hmid0
  have hQge : ∀ v : ℝ, 1 - tau ≤ v → Q n h v = Q n 0 v :=
    xiC_Q_eq_of_ge n hn hh hsupp hsmall (a' := a / 2) (by linarith)
      (by rw [Work.OddVolterra.Smooth.one_sub_tau_eq]; linarith)
  obtain ⟨hE1b, hE1l, hE2b, hE2l⟩ := hE h δ hh hδpos hδle0 hjet
  have hgb : ∀ i : Fin 2, ∀ v ∈ Set.Icc (a / 2) (1 - tau),
      |(Q n h v) i - (Q n 0 v) i| ≤ C * δ := by
    intro i
    fin_cases i
    · intro v hv
      change |(-E1 n h v + iteratedDeriv (n + 1) (momentRHS n) v)
        - (-E1 n 0 v + iteratedDeriv (n + 1) (momentRHS n) v)| ≤ C * δ
      rw [show (-E1 n h v + iteratedDeriv (n + 1) (momentRHS n) v)
          - (-E1 n 0 v + iteratedDeriv (n + 1) (momentRHS n) v)
          = -(E1 n h v - E1 n 0 v) from by ring, abs_neg]
      exact hE1b v hv
    · intro v hv
      change |(-E2 n h v) - (-E2 n 0 v)| ≤ C * δ
      rw [show (-E2 n h v) - (-E2 n 0 v) = -(E2 n h v - E2 n 0 v) from by ring, abs_neg]
      exact hE2b v hv
  have hgl : ∀ i : Fin 2, ∀ v ∈ Set.Icc (a / 2) (1 - tau),
      ∀ v' ∈ Set.Icc (a / 2) (1 - tau),
      |((Q n h v) i - (Q n 0 v) i) - ((Q n h v') i - (Q n 0 v') i)| ≤ C * δ * |v - v'| := by
    intro i
    fin_cases i
    · intro v hv v' hv'
      change |((-E1 n h v + iteratedDeriv (n + 1) (momentRHS n) v)
          - (-E1 n 0 v + iteratedDeriv (n + 1) (momentRHS n) v))
        - ((-E1 n h v' + iteratedDeriv (n + 1) (momentRHS n) v')
          - (-E1 n 0 v' + iteratedDeriv (n + 1) (momentRHS n) v'))| ≤ C * δ * |v - v'|
      rw [show ((-E1 n h v + iteratedDeriv (n + 1) (momentRHS n) v)
            - (-E1 n 0 v + iteratedDeriv (n + 1) (momentRHS n) v))
          - ((-E1 n h v' + iteratedDeriv (n + 1) (momentRHS n) v')
            - (-E1 n 0 v' + iteratedDeriv (n + 1) (momentRHS n) v'))
          = -((E1 n h v - E1 n 0 v) - (E1 n h v' - E1 n 0 v')) from by ring, abs_neg]
      exact hE1l v hv v' hv'
    · intro v hv v' hv'
      change |((-E2 n h v) - (-E2 n 0 v)) - ((-E2 n h v') - (-E2 n 0 v'))|
        ≤ C * δ * |v - v'|
      rw [show ((-E2 n h v) - (-E2 n 0 v)) - ((-E2 n h v') - (-E2 n 0 v'))
          = -((E2 n h v - E2 n 0 v) - (E2 n h v' - E2 n 0 v')) from by ring, abs_neg]
      exact hE2l v hv v' hv'
  have hgz : ∀ i : Fin 2, ∀ v : ℝ, 1 - tau ≤ v → (Q n h v) i - (Q n 0 v) i = 0 := by
    intro i v hv
    rw [congrFun (hQge v hv) i, sub_self]
  have hQtilde : ∀ i : Fin 2, ∀ s ∈ Set.Icc a 1,
      |(Qtilde n h s) i - (Qtilde n 0 s) i| ≤ η₀ * δ := by
    intro i s hs
    by_cases hsτ : s ≤ 1 - tau
    · have hs1 : s < 1 := lt_of_le_of_lt hsτ
        (by rw [Work.OddVolterra.Smooth.one_sub_tau_eq]; norm_num)
      have ha's : a / 2 < s := by linarith [hs.1]
      have hd1 : DifferentiableAt ℝ
          (fun u : ℝ => ∫ v in u..1, (Q n h v) i / Real.sqrt (v - u)) s :=
        xiC_differentiableAt n hn hh hsupp hsmall (a' := a / 2) (by linarith) i
          (Set.mem_Ioo.mpr ⟨ha's, hs1⟩)
      have hd2 : DifferentiableAt ℝ
          (fun u : ℝ => ∫ v in u..1, (Q n 0 v) i / Real.sqrt (v - u)) s :=
        xiC_differentiableAt n hn contDiff_const hsupp0 hsmall0 (a' := a / 2) (by linarith) i
          (Set.mem_Ioo.mpr ⟨ha's, hs1⟩)
      have hQh_s : (Qtilde n h s) i =
          deriv (fun u : ℝ => ∫ v in u..1, (Q n h v) i / Real.sqrt (v - u)) s := by
        fin_cases i <;> simp [Qtilde]
      have hQ0_s : (Qtilde n 0 s) i =
          deriv (fun u : ℝ => ∫ v in u..1, (Q n 0 v) i / Real.sqrt (v - u)) s := by
        fin_cases i <;> simp [Qtilde]
      rw [hQh_s, hQ0_s, ← deriv_sub hd1 hd2]
      have hev : (fun u : ℝ => ∫ v in u..1, (Q n h v) i / Real.sqrt (v - u))
            - (fun u : ℝ => ∫ v in u..1, (Q n 0 v) i / Real.sqrt (v - u))
          =ᶠ[𝓝 s] fun u : ℝ => ∫ v in u..1,
            ((Q n h v) i - (Q n 0 v) i) / Real.sqrt (v - u) :=
        xiC_abel_linear ha's hs1
          ((continuous_apply i).comp_continuousOn hQh.1)
          ((continuous_apply i).comp_continuousOn hQh0.1)
      rw [Filter.EventuallyEq.deriv_eq hev]
      have hcd : a / 2 < min a (1 - tau) := by
        refine lt_min (by linarith) ?_
        rw [Work.OddVolterra.Smooth.one_sub_tau_eq]; linarith
      have hdb : min a (1 - tau) ≤ 1 - tau := min_le_right _ _
      have hb1 : 1 - tau ≤ 1 := by rw [Work.OddVolterra.Smooth.one_sub_tau_eq]; norm_num
      have hη : 0 ≤ C * δ := mul_nonneg hC0 hδpos.le
      have hs' : s ∈ Set.Icc (min a (1 - tau)) 1 :=
        ⟨le_trans (min_le_left _ _) hs.1, hs.2⟩
      calc |deriv (fun u : ℝ => ∫ v in u..1,
              ((Q n h v) i - (Q n 0 v) i) / Real.sqrt (v - u)) s|
          ≤ 10 * Real.sqrt ((1 - tau) - a / 2 + 1) * (C * δ) :=
            hAb hcd hdb hb1 hη (hgz i) (hgl i) s hs'
        _ = η₀ * δ := by rw [hη₀def]; ring
    · have hgt : 1 - tau < s := lt_of_not_ge hsτ
      have hev : (fun u : ℝ => ∫ v in u..1, (Q n h v) i / Real.sqrt (v - u))
          =ᶠ[𝓝 s] fun u : ℝ => ∫ v in u..1, (Q n 0 v) i / Real.sqrt (v - u) := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with u hu
        refine intervalIntegral.integral_congr (fun v hv => ?_)
        have hvge : 1 - tau ≤ v := by
          have h1 : min u 1 ≤ v := hv.1
          have h2 : 1 - tau < min u 1 :=
            lt_min hu (by rw [Work.OddVolterra.Smooth.one_sub_tau_eq]; norm_num)
          linarith
        rw [congrFun (hQge v hvge) i]
      have hQh_s : (Qtilde n h s) i =
          deriv (fun u : ℝ => ∫ v in u..1, (Q n h v) i / Real.sqrt (v - u)) s := by
        fin_cases i <;> simp [Qtilde]
      have hQ0_s : (Qtilde n 0 s) i =
          deriv (fun u : ℝ => ∫ v in u..1, (Q n 0 v) i / Real.sqrt (v - u)) s := by
        fin_cases i <;> simp [Qtilde]
      rw [hQh_s, hQ0_s, Filter.EventuallyEq.deriv_eq hev, sub_self, abs_zero]
      exact mul_nonneg hη₀nn hδpos.le
  intro s hs
  have hnorm : ‖Xi n h s - Xi n 0 s‖ ≤ η₀ * δ := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hη₀nn hδpos.le)).mpr ?_
    intro i
    rw [Real.norm_eq_abs]
    fin_cases i
    · change |(profileX 1 : ℝ) - profileX 1| ≤ η₀ * δ
      rw [sub_self, abs_zero]
      exact mul_nonneg hη₀nn hδpos.le
    · change |(profileX 1 : ℝ) - profileX 1| ≤ η₀ * δ
      rw [sub_self, abs_zero]
      exact mul_nonneg hη₀nn hδpos.le
    · change |(Qtilde n h s) 0 - (Qtilde n 0 s) 0| ≤ η₀ * δ
      exact hQtilde 0 s hs
    · change |(Qtilde n h s) 1 - (Qtilde n 0 s) 1| ≤ η₀ * δ
      exact hQtilde 1 s hs
  exact lt_of_le_of_lt hnorm hηδ

/-- **`Ξ` is continuous at `h = 0` in the `C^{n+2}` topology.** -/
theorem xi_close_of_small (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      (∀ s ∈ Set.Icc a 1, ‖Work.OddVolterra.Xi n h s - Work.OddVolterra.Xi n 0 s‖ < ε) :=
  xiC_aux n hn a ha ha1
    (E1_E2_diff_bounds n hn (c := a / 2) (by linarith)
      (by rw [Work.OddVolterra.Smooth.one_sub_tau_eq]; linarith))
    (fun {c d b₀ η} hcd hdb hb₁ hη {g} hzero hlip =>
      abel_deriv_bound hcd hdb hb₁ hη hzero hlip)

end

end Work.OddVolterra.Existence
