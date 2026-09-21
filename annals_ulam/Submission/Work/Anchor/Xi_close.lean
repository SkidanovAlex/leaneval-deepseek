import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.xi_close_of_small
import Submission.Work.OddVolterra.Existence.iteratedDeriv_mul_abs_bound

/-!
# `Xi_close`: `Ξ` is Lipschitz at `h = 0` in the `C^{n+2}` topology

The requested lemma `Work.Anchor.Xi_close` states that there is a constant `C > 0` such that
for every `C^∞` perturbation `h` supported in the transition window and every `δ ≤ 1/100`
bounding the derivatives of `h` up to order `n + 2`, the `Ξ`-row of the odd transition-slope
system satisfies `‖Ξ n h s - Ξ n 0 s‖ ≤ C δ` for all `s ∈ [1/2, 19/20]`.

The first two components of `Ξ n h` do not depend on `h`; the last two are the *derivatives of
the Abel transforms* of the two components of `Q n h`, which differ from `Q n 0` only through
the inhomogeneities `E₁`, `E₂`.  The estimate is therefore

* `E₁`, `E₂` (and their `s`-Lipschitz constants) are `C δ`-close to the ball's,
* the derivative of the Abel transform of a Lipschitz function vanishing above `1 - τ` is
  controlled by its Lipschitz constant
  (`Work.OddVolterra.Existence.abel_deriv_bound`),
* `Q n h` and `Q n 0` agree on the window `[1 - τ, 1]`
  (`Work.OddVolterra.Existence.xiC_Q_eq_of_ge`).

The assembly is the one carried out in
`Submission/Work/OddVolterra/Existence/xi_close_of_small.lean` (`xiC_aux`), where however the
`E₁`/`E₂` bounds are supplied as an abstract hypothesis of the form
"`∃ C δ₀, ∀ δ ≤ δ₀, ‖h‖_{C^{n+2}} ≤ δ → ⋯ ≤ C δ`".  Since the requested statement needs the
*linear* form with the *visible* threshold `1/100`, the two comparisons needed below
(`xi_close_E1_E2_hundred`) are proved separately in this file, and the present module contains
the assembly with the linear conclusion.
-/

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Commons.Geometry.Ulam
open Work.OddVolterra.DiffBounds

noncomputable section

/-- **The assembly, with the linear conclusion.**  Suppose that, for a fixed perturbation `h`
(smooth, supported in the transition window, `|h| ≤ 1/100`), the two inhomogeneities `E₁`, `E₂`
differ from the ball's by at most `ϑ` in value and are `ϑ`-Lipschitz on the slope window
`[a/2, 1-τ]`.  Then the `Ξ`-row is `O(ϑ)` on `[a, 1]`.

This is the `xiC_aux` assembly with the `ε`-`δ` conclusion replaced by the linear one, and the
`E₁`/`E₂` estimate hypothesis replaced by a constant `ϑ` (so that it applies both to the
`C δ`-bounds below the threshold and to uniform bounds). -/
theorem xi_close_assembly (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ Cfin : ℝ, 0 < Cfin ∧ ∀ (h : ℝ → ℝ) (ϑ : ℝ), 0 ≤ ϑ →
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ t : ℝ, |h t| ≤ 1 / 100) →
      (∀ v ∈ Set.Icc (a / 2) (1 - tau), |E1 n h v - E1 n 0 v| ≤ ϑ) →
      (∀ v ∈ Set.Icc (a / 2) (1 - tau), ∀ v' ∈ Set.Icc (a / 2) (1 - tau),
        |(E1 n h v - E1 n 0 v) - (E1 n h v' - E1 n 0 v')| ≤ ϑ * |v - v'|) →
      (∀ v ∈ Set.Icc (a / 2) (1 - tau), |E2 n h v - E2 n 0 v| ≤ ϑ) →
      (∀ v ∈ Set.Icc (a / 2) (1 - tau), ∀ v' ∈ Set.Icc (a / 2) (1 - tau),
        |(E2 n h v - E2 n 0 v) - (E2 n h v' - E2 n 0 v')| ≤ ϑ * |v - v'|) →
      ∀ s ∈ Set.Icc a 1, ‖Xi n h s - Xi n 0 s‖ ≤ Cfin * ϑ := by
  set η₀ : ℝ := 10 * Real.sqrt ((1 - tau) - a / 2 + 1) with hη₀def
  have hη₀nn : 0 ≤ η₀ := by
    rw [hη₀def]
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  refine ⟨η₀ + 1, by linarith, ?_⟩
  intro h ϑ hϑ hh hsupp hsmall hE1b hE1l hE2b hE2l
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
  have hgb : ∀ i : Fin 2, ∀ v ∈ Set.Icc (a / 2) (1 - tau),
      |(Q n h v) i - (Q n 0 v) i| ≤ ϑ := by
    intro i
    fin_cases i
    · intro v hv
      change |(-E1 n h v + iteratedDeriv (n + 1) (momentRHS n) v)
        - (-E1 n 0 v + iteratedDeriv (n + 1) (momentRHS n) v)| ≤ ϑ
      rw [show (-E1 n h v + iteratedDeriv (n + 1) (momentRHS n) v)
          - (-E1 n 0 v + iteratedDeriv (n + 1) (momentRHS n) v)
          = -(E1 n h v - E1 n 0 v) from by ring, abs_neg]
      exact hE1b v hv
    · intro v hv
      change |(-E2 n h v) - (-E2 n 0 v)| ≤ ϑ
      rw [show (-E2 n h v) - (-E2 n 0 v) = -(E2 n h v - E2 n 0 v) from by ring, abs_neg]
      exact hE2b v hv
  have hgl : ∀ i : Fin 2, ∀ v ∈ Set.Icc (a / 2) (1 - tau),
      ∀ v' ∈ Set.Icc (a / 2) (1 - tau),
      |((Q n h v) i - (Q n 0 v) i) - ((Q n h v') i - (Q n 0 v') i)| ≤ ϑ * |v - v'| := by
    intro i
    fin_cases i
    · intro v hv v' hv'
      change |((-E1 n h v + iteratedDeriv (n + 1) (momentRHS n) v)
          - (-E1 n 0 v + iteratedDeriv (n + 1) (momentRHS n) v))
        - ((-E1 n h v' + iteratedDeriv (n + 1) (momentRHS n) v')
          - (-E1 n 0 v' + iteratedDeriv (n + 1) (momentRHS n) v'))| ≤ ϑ * |v - v'|
      rw [show ((-E1 n h v + iteratedDeriv (n + 1) (momentRHS n) v)
            - (-E1 n 0 v + iteratedDeriv (n + 1) (momentRHS n) v))
          - ((-E1 n h v' + iteratedDeriv (n + 1) (momentRHS n) v')
            - (-E1 n 0 v' + iteratedDeriv (n + 1) (momentRHS n) v'))
          = -((E1 n h v - E1 n 0 v) - (E1 n h v' - E1 n 0 v')) from by ring, abs_neg]
      exact hE1l v hv v' hv'
    · intro v hv v' hv'
      change |((-E2 n h v) - (-E2 n 0 v)) - ((-E2 n h v') - (-E2 n 0 v'))|
        ≤ ϑ * |v - v'|
      rw [show ((-E2 n h v) - (-E2 n 0 v)) - ((-E2 n h v') - (-E2 n 0 v'))
          = -((E2 n h v - E2 n 0 v) - (E2 n h v' - E2 n 0 v')) from by ring, abs_neg]
      exact hE2l v hv v' hv'
  have hgz : ∀ i : Fin 2, ∀ v : ℝ, 1 - tau ≤ v → (Q n h v) i - (Q n 0 v) i = 0 := by
    intro i v hv
    rw [congrFun (hQge v hv) i, sub_self]
  have hQtilde : ∀ i : Fin 2, ∀ s ∈ Set.Icc a 1,
      |(Qtilde n h s) i - (Qtilde n 0 s) i| ≤ η₀ * ϑ := by
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
      have hs' : s ∈ Set.Icc (min a (1 - tau)) 1 :=
        ⟨le_trans (min_le_left _ _) hs.1, hs.2⟩
      calc |deriv (fun u : ℝ => ∫ v in u..1,
              ((Q n h v) i - (Q n 0 v) i) / Real.sqrt (v - u)) s|
          ≤ 10 * Real.sqrt ((1 - tau) - a / 2 + 1) * ϑ :=
            abel_deriv_bound hcd hdb hb1 hϑ (hgz i) (hgl i) s hs'
        _ = η₀ * ϑ := by rw [hη₀def]
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
      exact mul_nonneg hη₀nn hϑ
  intro s hs
  have hnorm : ‖Xi n h s - Xi n 0 s‖ ≤ η₀ * ϑ := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hη₀nn hϑ)).mpr ?_
    intro i
    rw [Real.norm_eq_abs]
    fin_cases i
    · change |(profileX 1 : ℝ) - profileX 1| ≤ η₀ * ϑ
      rw [sub_self, abs_zero]
      exact mul_nonneg hη₀nn hϑ
    · change |(profileX 1 : ℝ) - profileX 1| ≤ η₀ * ϑ
      rw [sub_self, abs_zero]
      exact mul_nonneg hη₀nn hϑ
    · change |(Qtilde n h s) 0 - (Qtilde n 0 s) 0| ≤ η₀ * ϑ
      exact hQtilde 0 s hs
    · change |(Qtilde n h s) 1 - (Qtilde n 0 s) 1| ≤ η₀ * ϑ
      exact hQtilde 1 s hs
  calc ‖Xi n h s - Xi n 0 s‖ ≤ η₀ * ϑ := hnorm
    _ ≤ (η₀ + 1) * ϑ := by nlinarith [hϑ, hη₀nn]



/-- **Pointwise `C δ`-bound for the `E₂` slice difference at order `m`, with the threshold
`1/100` visible.**  This is `slice_pointwise_bound` with the existential threshold `δ₀ ≤ 1/100`
replaced by the number `1/100` itself (the proof is the same: the only use of the threshold in
the source is to derive `δ ≤ 1/100` for the parametric jet tool). -/
theorem xi_close_slice_pointwise (n m : ℕ) {c : ℝ} (hc : 0 < c)
    (hc1 : c ≤ 1 - Work.OddVolterra.tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ j : ℕ, j ≤ m + 1 → ∀ s : ℝ, |iteratedDeriv j h s| ≤ δ) →
      ∀ v ∈ Set.Icc c (1 - Work.OddVolterra.tau),
      ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
        |iteratedDeriv m (fun u : ℝ =>
              mPhiB n (u, h u, t) * (t + deriv h u)) v -
         iteratedDeriv m (fun u : ℝ =>
              mPhiB n (u, 0, t) * t) v| ≤ C * δ := by
  have hp_pos : (0 : ℝ) < Commons.Geometry.Ulam.profileX 1 :=
    Commons.Geometry.Ulam.profileX_pos 1 (by norm_num)
  have hp_nn : (0 : ℝ) ≤ Commons.Geometry.Ulam.profileX 1 := le_of_lt hp_pos
  have hb0 : (0 : ℝ) < 1 / 100 := by norm_num
  have hbox : (Set.Icc c (1 - Work.OddVolterra.tau) ×ˢ Set.Icc (-(1 / 100)) (1 / 100) ×ˢ
      Set.Icc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1)
      : Set (ℝ × ℝ × ℝ)) ⊆ mUpos :=
    m_box_subset_mUpos hc hc1 le_rfl rfl
  choose Cf hCf0 hCfb using fun k : ℕ =>
    Work.OddVolterra.Existence.exists_bound_comp_pair_sub_param k isOpen_mUpos hbox
      (contDiffOn_mPhiB n) hc1 hb0 hp_nn
  choose Mg hMg0 hMg using fun k : ℕ => m_ball_slice_bounds n hc hc1 k
  set D : ℝ := Finset.sum (Finset.range (m + 1)) (fun k => Cf k + Mg k) with hD
  have hDnn : 0 ≤ D := by
    rw [hD]
    exact Finset.sum_nonneg fun k _ => add_nonneg (hCf0 k) (hMg0 k)
  refine ⟨Commons.Geometry.Ulam.profileX 1 * Cf m + 2 ^ m * D, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg hp_nn (hCf0 m))
      (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m) hDnn)
  · intro h δ hh hδpos hδR hjet v hv t ht
    have htI : t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1))
        (Commons.Geometry.Ulam.profileX 1) := ht
    have htv : |t| ≤ Commons.Geometry.Ulam.profileX 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    have hδ0 : 0 ≤ δ := le_of_lt hδpos
    have hδ1 : δ ≤ 1 := by linarith
    have hv_small : |h v| ≤ 1 / 100 := by
      have h1 : |h v| ≤ δ := by
        simpa only [iteratedDeriv_zero] using hjet 0 (Nat.zero_le (m + 1)) v
      linarith
    have hvt_mem : (v, t) ∈ graphPos h :=
      mem_graphPos_of_box hc hc1 hv hv_small htv
    have hBh_at : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => mPhiB n (u, h u, t)) v := by
      have hpt : (v, h v, t) ∈ mUpos := mem_graphPos.mp hvt_mem
      have hm : ContDiffAt ℝ (⊤ : ℕ∞) (mPhiB n) (v, h v, t) :=
        (contDiffOn_mPhiB n).contDiffAt (isOpen_mUpos.mem_nhds hpt)
      have hcurve : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => (u, h u, t)) v :=
        contDiffAt_id.prodMk (hh.contDiffAt.prodMk contDiffAt_const)
      simpa [Function.comp_def] using hm.comp v hcurve
    have hdhC : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := by
      rw [← contDiffOn_univ]
      exact hh.contDiffOn.deriv_of_isOpen isOpen_univ Work.OddVolterra.Smooth.top_coe_add_one_le
    have hdh_at : ContDiffAt ℝ (⊤ : ℕ∞) (deriv h) v := hdhC.contDiffAt
    have hderivbound : ∀ i : ℕ, i ≤ m → |iteratedDeriv i (deriv h) v| ≤ δ := by
      intro i hi
      rw [← iteratedDeriv_succ' (f := h) (n := i)]
      exact hjet (i + 1) (Nat.succ_le_succ hi) v
    have hBbound : ∀ k : ℕ, k ≤ m → |iteratedDeriv k (fun u : ℝ => mPhiB n (u, h u, t)) v| ≤ D := by
      intro k hk
      have h1 : |iteratedDeriv k (fun u : ℝ => mPhiB n (u, h u, t)) v -
          iteratedDeriv k (fun u : ℝ => mPhiB n (u, 0, t)) v| ≤ Cf k * δ :=
        hCfb k h δ hδ0 hδ1 hδR hh
          (fun j hj u _ => hjet j (Nat.le_succ_of_le (le_trans hj hk)) u) v hv t htI
      have h2 : |iteratedDeriv k (fun u : ℝ => mPhiB n (u, 0, t)) v| ≤ Mg k :=
        hMg k v hv t htI
      have h3 : |iteratedDeriv k (fun u : ℝ => mPhiB n (u, h u, t)) v| ≤ Cf k * δ + Mg k := by
        calc |iteratedDeriv k (fun u : ℝ => mPhiB n (u, h u, t)) v|
            = |(iteratedDeriv k (fun u : ℝ => mPhiB n (u, h u, t)) v -
                iteratedDeriv k (fun u : ℝ => mPhiB n (u, 0, t)) v) +
                iteratedDeriv k (fun u : ℝ => mPhiB n (u, 0, t)) v| := by
              congr 1; ring
          _ ≤ _ := abs_add_le _ _
          _ ≤ Cf k * δ + Mg k := add_le_add h1 h2
      have h4 : Cf k * δ ≤ Cf k := by
        simpa using mul_le_of_le_one_right (hCf0 k) hδ1
      have h5 : Cf k + Mg k ≤ D := by
        rw [hD]
        exact Finset.single_le_sum (fun i _ => add_nonneg (hCf0 i) (hMg0 i))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
      linarith
    have hmm : ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_le_coe.mpr le_top
    have hmul1 : ContDiffAt ℝ (m : ℕ∞)
        (fun u : ℝ => t * mPhiB n (u, h u, t)) v :=
      (contDiffAt_const.mul hBh_at).of_le hmm
    have hmul2 : ContDiffAt ℝ (m : ℕ∞)
        (fun u : ℝ => deriv h u * mPhiB n (u, h u, t)) v :=
      (hdh_at.mul hBh_at).of_le hmm
    have hdiff : iteratedDeriv m (fun u : ℝ =>
            mPhiB n (u, h u, t) * (t + deriv h u)) v -
        iteratedDeriv m (fun u : ℝ => mPhiB n (u, 0, t) * t) v
        = t * (iteratedDeriv m (fun u : ℝ => mPhiB n (u, h u, t)) v -
            iteratedDeriv m (fun u : ℝ => mPhiB n (u, 0, t)) v)
          + iteratedDeriv m (fun u : ℝ => deriv h u * mPhiB n (u, h u, t)) v := by
      rw [show (fun u : ℝ => mPhiB n (u, h u, t) * (t + deriv h u)) =
            (fun u : ℝ => t * mPhiB n (u, h u, t)) +
              (fun u : ℝ => deriv h u * mPhiB n (u, h u, t)) from by
          funext u; simp only [Pi.add_apply]; ring]
      rw [show (fun u : ℝ => mPhiB n (u, 0, t) * t) =
            (fun u : ℝ => t * mPhiB n (u, 0, t)) from by funext u; ring]
      rw [iteratedDeriv_add (n := m) hmul1 hmul2]
      simp only [iteratedDeriv_const_mul_field]
      ring
    have hB1 : |iteratedDeriv m (fun u : ℝ => mPhiB n (u, h u, t)) v -
        iteratedDeriv m (fun u : ℝ => mPhiB n (u, 0, t)) v| ≤ Cf m * δ :=
      hCfb m h δ hδ0 hδ1 hδR hh
        (fun j hj u _ => hjet j (le_trans hj (Nat.le_succ m)) u) v hv t htI
    have hB2 : |iteratedDeriv m (fun u : ℝ => deriv h u * mPhiB n (u, h u, t)) v| ≤
        2 ^ m * δ * D :=
      Work.OddVolterra.Existence.iteratedDeriv_mul_abs_bound m (deriv h)
        (fun u : ℝ => mPhiB n (u, h u, t)) v δ D hdh_at hBh_at hδ0 hDnn hderivbound hBbound
    calc |iteratedDeriv m (fun u : ℝ =>
              mPhiB n (u, h u, t) * (t + deriv h u)) v -
         iteratedDeriv m (fun u : ℝ => mPhiB n (u, 0, t) * t) v|
        = |t * (iteratedDeriv m (fun u : ℝ => mPhiB n (u, h u, t)) v -
              iteratedDeriv m (fun u : ℝ => mPhiB n (u, 0, t)) v)
            + iteratedDeriv m (fun u : ℝ => deriv h u * mPhiB n (u, h u, t)) v| := by
          rw [hdiff]
      _ ≤ |t * (iteratedDeriv m (fun u : ℝ => mPhiB n (u, h u, t)) v -
              iteratedDeriv m (fun u : ℝ => mPhiB n (u, 0, t)) v)|
            + |iteratedDeriv m (fun u : ℝ => deriv h u * mPhiB n (u, h u, t)) v| :=
          abs_add_le _ _
      _ ≤ Commons.Geometry.Ulam.profileX 1 * (Cf m * δ) + 2 ^ m * δ * D := by
          refine add_le_add ?_ hB2
          rw [abs_mul]
          exact mul_le_mul htv hB1 (abs_nonneg _) hp_nn
      _ = (Commons.Geometry.Ulam.profileX 1 * Cf m + 2 ^ m * D) * δ := by ring

/-- **The `E₁`/`E₂` estimates with the visible threshold `1/100`.**

`E1_E2_diff_bounds` states the four estimates with an *existential* threshold `δ₀`, which hides
the fact (visible in its proof) that `δ₀ = 1/100` is available.  This version states the
threshold `1/100` explicitly, which is what `Work.Anchor.Xi_close` needs.  The two routes are

* `E₁ n h - E₁ n 0` is the `t`-integral of the difference of the order-`(n+1)` graph composites
  of `mPhiF n`; the parametric jet tool `exists_bound_comp_pair_sub_param` (whose threshold `R`
  is an *argument*, taken here to be `1/100`) bounds that difference by `A₁ δ`, and its
  order-`(n+2)` instance by `A₂ δ`.  Integrating gives the value bound, and the mean value
  theorem in `v` (with `hasDerivAt_iteratedDeriv_section`) the Lipschitz bound;
* `E₂ n h - E₂ n 0` is the `t`-integral of the difference of the order-`n` (resp. `n+1`) graph
  composites of `mPhiB n` against the linear factor `t + h'`; the threshold-free tool
  `xi_close_slice_pointwise` of this file bounds that difference pointwise by `C δ`. -/
theorem xi_close_E1_E2_hundred (n : ℕ) (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c)
    (hc1 : c ≤ 1 - tau) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      (∀ v ∈ Set.Icc c (1 - tau), |E1 n h v - E1 n 0 v| ≤ C * δ) ∧
      (∀ v ∈ Set.Icc c (1 - tau), ∀ v' ∈ Set.Icc c (1 - tau),
        |(E1 n h v - E1 n 0 v) - (E1 n h v' - E1 n 0 v')| ≤ C * δ * |v - v'|) ∧
      (∀ v ∈ Set.Icc c (1 - tau), |E2 n h v - E2 n 0 v| ≤ C * δ) ∧
      (∀ v ∈ Set.Icc c (1 - tau), ∀ v' ∈ Set.Icc c (1 - tau),
        |(E2 n h v - E2 n 0 v) - (E2 n h v' - E2 n 0 v')| ≤ C * δ * |v - v'|) := by
  have hp : (0 : ℝ) < profileX 1 := profileX_one_pos'
  have hpp : -(profileX 1) ≤ profileX 1 := by linarith
  have h2p : (0 : ℝ) ≤ 2 * profileX 1 := by linarith
  obtain ⟨A1, hA1nn, hA1⟩ := exists_bound_comp_pair_sub_param (i := n + 1) (Φ := mPhiF n)
    (c := c) (d := 1 - tau) (R := 1 / 100) (p := profileX 1) (U := mUpos) isOpen_mUpos
    (m_box_subset_mUpos (R := 1 / 100) (p := profileX 1) hc hc1 le_rfl rfl)
    (contDiffOn_mPhiF n) hc1 (by norm_num) hp.le
  obtain ⟨A2, hA2nn, hA2⟩ := exists_bound_comp_pair_sub_param (i := n + 2) (Φ := mPhiF n)
    (c := c) (d := 1 - tau) (R := 1 / 100) (p := profileX 1) (U := mUpos) isOpen_mUpos
    (m_box_subset_mUpos (R := 1 / 100) (p := profileX 1) hc hc1 le_rfl rfl)
    (contDiffOn_mPhiF n) hc1 (by norm_num) hp.le
  obtain ⟨Cq, hCqnn, hCq⟩ := xi_close_slice_pointwise n n hc hc1
  obtain ⟨Cr, hCrnn, hCr⟩ := xi_close_slice_pointwise n (n + 1) hc hc1
  set M : ℝ := max (max A1 A2) (max Cq Cr) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact le_trans hA1nn
      (le_trans (le_max_left A1 A2) (le_max_left (max A1 A2) (max Cq Cr)))
  refine ⟨M * (2 * profileX 1), mul_nonneg hMnn h2p, ?_⟩
  intro h δ hh hδpos hδR hjet
  have hδ0 : 0 ≤ δ := hδpos.le
  have hδ1 : δ ≤ 1 := by linarith
  have hsmall : ∀ v ∈ Set.Icc c (1 - tau), |h v| ≤ 1 / 100 := by
    intro v hv
    have h1 : |h v| ≤ δ := by
      simpa only [iteratedDeriv_zero] using hjet 0 (by omega) v
    linarith
  have hmemh : ∀ v ∈ Set.Icc c (1 - tau), ∀ t ∈ Set.uIcc (-(profileX 1)) (profileX 1),
      (v, t) ∈ graphPos h := by
    intro v hv t ht
    rw [Set.uIcc_of_le hpp] at ht
    exact mem_graphPos_of_box hc hc1 hv (hsmall v hv) (abs_le.mpr ⟨ht.1, ht.2⟩)
  have hmem0 : ∀ v ∈ Set.Icc c (1 - tau), ∀ t ∈ Set.uIcc (-(profileX 1)) (profileX 1),
      (v, t) ∈ graphPos (0 : ℝ → ℝ) := by
    intro v hv t ht
    rw [Set.uIcc_of_le hpp] at ht
    exact mem_graphPos_of_box hc hc1 hv (by norm_num) (abs_le.mpr ⟨ht.1, ht.2⟩)
  have hjet1 : ∀ j : ℕ, j ≤ n + 1 → ∀ u ∈ Set.Icc c (1 - tau),
      |iteratedDeriv j h u| ≤ δ := fun j hj u _ => hjet j (le_trans hj (by omega)) u
  have hjet2 : ∀ j : ℕ, j ≤ n + 2 → ∀ u ∈ Set.Icc c (1 - tau),
      |iteratedDeriv j h u| ≤ δ := fun j hj u _ => hjet j hj u
  have hIh : ∀ v ∈ Set.Icc c (1 - tau), IntervalIntegrable
      (fun t : ℝ => iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v)
      volume (-(profileX 1)) (profileX 1) := fun v hv =>
    intervalIntegrable_iteratedDeriv_section (V := graphPos h) (isOpen_graphPos hh)
      (contDiffOn_graphPhiF n hh) (n + 1) (hmemh v hv)
  have hI0 : ∀ v ∈ Set.Icc c (1 - tau), IntervalIntegrable
      (fun t : ℝ => iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v)
      volume (-(profileX 1)) (profileX 1) := fun v hv =>
    intervalIntegrable_iteratedDeriv_section (V := graphPos (0 : ℝ → ℝ))
      (isOpen_graphPos contDiff_const) (contDiffOn_graphPhiF n contDiff_const) (n + 1)
      (hmem0 v hv)
  have hIhE2 : ∀ v ∈ Set.Icc c (1 - tau), IntervalIntegrable
      (fun t : ℝ => iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v)
      volume (-(profileX 1)) (profileX 1) := fun v hv =>
    intervalIntegrable_iteratedDeriv_section (V := graphPos h) (isOpen_graphPos hh)
      (contDiffOn_graphPhiH n hh) n (hmemh v hv)
  have hI0E2 : ∀ v ∈ Set.Icc c (1 - tau), IntervalIntegrable
      (fun t : ℝ => iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v)
      volume (-(profileX 1)) (profileX 1) := fun v hv =>
    intervalIntegrable_iteratedDeriv_section (V := graphPos (0 : ℝ → ℝ))
      (isOpen_graphPos contDiff_const) (contDiffOn_graphPhiH n contDiff_const) n
      (hmem0 v hv)
  have hls0 : ∀ u t : ℝ, lineSlope (0 : ℝ → ℝ) u t = t := by
    intro u t
    simp [lineSlope]
  have hfoldh : ∀ t : ℝ, (fun u : ℝ => mPhiB n (u, h u, t) * (t + deriv h u))
      = fun u : ℝ => graphPhiH n h (u, t) := by
    intro t
    funext u
    rw [graphPhiH_apply]
    rfl
  have hfold0 : ∀ t : ℝ, (fun u : ℝ => mPhiB n (u, 0, t) * t)
      = fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t) := by
    intro t
    funext u
    rw [graphPhiH_apply]
    simp only [Pi.zero_apply, hls0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `E₁`, value bound
    intro v hv
    have hkey : E1 n h v - E1 n 0 v =
        ∫ t in (-(profileX 1))..(profileX 1),
          (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
            - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v) := by
      rw [mE1_eq n h v, mE1_eq n 0 v]
      simp only [Pi.zero_apply]
      exact (intervalIntegral.integral_sub (hIh v hv) (hI0 v hv)).symm
    have habs : IntervalIntegrable (fun t : ℝ =>
        |iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
          - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v|)
        volume (-(profileX 1)) (profileX 1) := ((hIh v hv).sub (hI0 v hv)).abs
    have hle : A1 ≤ M := by
      rw [hMdef]
      exact le_trans (le_max_left A1 A2) (le_max_left (max A1 A2) (max Cq Cr))
    calc |E1 n h v - E1 n 0 v|
        = |∫ t in (-(profileX 1))..(profileX 1),
            (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
              - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v)| := by rw [hkey]
      _ ≤ ∫ t in (-(profileX 1))..(profileX 1),
            |iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
              - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v| :=
          intervalIntegral.abs_integral_le_integral_abs hpp
      _ ≤ ∫ t in (-(profileX 1))..(profileX 1), A1 * δ :=
          intervalIntegral.integral_mono_on hpp habs intervalIntegrable_const
            (fun t ht => hA1 h δ hδ0 hδ1 hδR hh hjet1 v hv t ht)
      _ = A1 * δ * (2 * profileX 1) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ M * (2 * profileX 1) * δ := by
          calc A1 * δ * (2 * profileX 1) = (A1 * (2 * profileX 1)) * δ := by ring
            _ ≤ (M * (2 * profileX 1)) * δ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle h2p) hδ0
  · -- `E₁`, Lipschitz bound
    intro v hv v' hv'
    have hkeyv : E1 n h v - E1 n 0 v =
        ∫ t in (-(profileX 1))..(profileX 1),
          (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
            - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v) := by
      rw [mE1_eq n h v, mE1_eq n 0 v]
      simp only [Pi.zero_apply]
      exact (intervalIntegral.integral_sub (hIh v hv) (hI0 v hv)).symm
    have hkeyv' : E1 n h v' - E1 n 0 v' =
        ∫ t in (-(profileX 1))..(profileX 1),
          (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v'
            - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v') := by
      rw [mE1_eq n h v', mE1_eq n 0 v']
      simp only [Pi.zero_apply]
      exact (intervalIntegral.integral_sub (hIh v' hv') (hI0 v' hv')).symm
    have hsub : (E1 n h v - E1 n 0 v) - (E1 n h v' - E1 n 0 v') =
        ∫ t in (-(profileX 1))..(profileX 1),
          ((iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
              - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v)
            - (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v'
              - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v')) := by
      rw [hkeyv, hkeyv',
        ← intervalIntegral.integral_sub ((hIh v hv).sub (hI0 v hv))
          ((hIh v' hv').sub (hI0 v' hv'))]
    have hpair : IntervalIntegrable (fun t : ℝ =>
        (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
            - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v)
          - (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v'
            - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v'))
        volume (-(profileX 1)) (profileX 1) :=
      ((hIh v hv).sub (hI0 v hv)).sub ((hIh v' hv').sub (hI0 v' hv'))
    have hpt : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
        |(iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
            - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v)
          - (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v'
            - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v')|
        ≤ A2 * δ * |v - v'| := by
      intro t ht
      have htI : t ∈ Set.uIcc (-(profileX 1)) (profileX 1) := by
        rw [Set.uIcc_of_le hpp]; exact ht
      have hd1 : ∀ x ∈ Set.Icc c (1 - tau), HasDerivAt (fun s : ℝ =>
          iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) s)
          (iteratedDeriv ((n + 1) + 1) (fun u : ℝ => mPhiF n (u, h u, t)) x) x :=
        fun x hx => hasDerivAt_iteratedDeriv_section (V := graphPos h) (isOpen_graphPos hh)
          (contDiffOn_graphPhiF n hh) (n + 1) (hmemh x hx t htI)
      have hd0 : ∀ x ∈ Set.Icc c (1 - tau), HasDerivAt (fun s : ℝ =>
          iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) s)
          (iteratedDeriv ((n + 1) + 1) (fun u : ℝ => mPhiF n (u, 0, t)) x) x :=
        fun x hx => hasDerivAt_iteratedDeriv_section (V := graphPos (0 : ℝ → ℝ))
          (isOpen_graphPos contDiff_const) (contDiffOn_graphPhiF n contDiff_const) (n + 1)
          (hmem0 x hx t htI)
      have hdiff : ∀ x ∈ Set.Icc c (1 - tau), DifferentiableAt ℝ (fun s : ℝ =>
          (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) s
            - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) s)) x :=
        fun x hx => (hd1 x hx).differentiableAt.sub (hd0 x hx).differentiableAt
      have hbd : ∀ x ∈ Set.Icc c (1 - tau), ‖deriv (fun s : ℝ =>
          (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) s
            - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) s)) x‖ ≤ A2 * δ := by
        intro x hx
        have hdv : deriv (fun s : ℝ =>
            (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) s
              - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) s)) x
            = iteratedDeriv ((n + 1) + 1) (fun u : ℝ => mPhiF n (u, h u, t)) x
              - iteratedDeriv ((n + 1) + 1) (fun u : ℝ => mPhiF n (u, 0, t)) x :=
          ((hd1 x hx).sub (hd0 x hx)).deriv
        rw [hdv, Real.norm_eq_abs]
        exact hA2 h δ hδ0 hδ1 hδR hh hjet2 x hx t ht
      have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
        (s := Set.Icc c (1 - tau))
        (f := fun s : ℝ =>
          (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) s
            - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) s))
        (C := A2 * δ) hdiff hbd (convex_Icc c (1 - tau))
        hv' hv
      simpa only [Real.norm_eq_abs] using hmv
    calc |(E1 n h v - E1 n 0 v) - (E1 n h v' - E1 n 0 v')|
        = |∫ t in (-(profileX 1))..(profileX 1),
            ((iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
                - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v)
              - (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v'
                - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v'))| := by
          rw [hsub]
      _ ≤ ∫ t in (-(profileX 1))..(profileX 1),
            |(iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v
                - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v)
              - (iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, h u, t)) v'
                - iteratedDeriv (n + 1) (fun u : ℝ => mPhiF n (u, 0, t)) v')| :=
          intervalIntegral.abs_integral_le_integral_abs hpp
      _ ≤ ∫ t in (-(profileX 1))..(profileX 1), (A2 * δ * |v - v'|) :=
          intervalIntegral.integral_mono_on hpp hpair.abs intervalIntegrable_const hpt
      _ = (A2 * δ * |v - v'|) * (2 * profileX 1) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ M * (2 * profileX 1) * δ * |v - v'| := by
          have hle : A2 ≤ M := by
            rw [hMdef]
            exact le_trans (le_max_right A1 A2) (le_max_left (max A1 A2) (max Cq Cr))
          calc (A2 * δ * |v - v'|) * (2 * profileX 1)
              = (A2 * (2 * profileX 1)) * δ * |v - v'| := by ring
            _ ≤ (M * (2 * profileX 1)) * δ * |v - v'| :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle h2p) hδ0)
                  (abs_nonneg _)
  · -- `E₂`, value bound
    intro v hv
    have hkey : E2 n h v - E2 n 0 v =
        ∫ t in (-(profileX 1))..(profileX 1),
          (iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v
            - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v) := by
      rw [mE2_eq n h v, mE2_eq n 0 v]
      exact (intervalIntegral.integral_sub (hIhE2 v hv) (hI0E2 v hv)).symm
    have habs : IntervalIntegrable (fun t : ℝ =>
        |iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v
          - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v|)
        volume (-(profileX 1)) (profileX 1) := ((hIhE2 v hv).sub (hI0E2 v hv)).abs
    have hpt : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
        |iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v
          - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v| ≤ Cq * δ := by
      intro t ht
      have h1 := hCq h δ hh hδpos hδR
        (fun j hj s => hjet j (le_trans hj (by omega)) s) v hv t ht
      rw [hfoldh t, hfold0 t] at h1
      exact h1
    have hle : Cq ≤ M := by
      rw [hMdef]
      exact le_trans (le_max_left Cq Cr) (le_max_right (max A1 A2) (max Cq Cr))
    calc |E2 n h v - E2 n 0 v|
        = |∫ t in (-(profileX 1))..(profileX 1),
            (iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v
              - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v)| := by
          rw [hkey]
      _ ≤ ∫ t in (-(profileX 1))..(profileX 1),
            |iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v
              - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v| :=
          intervalIntegral.abs_integral_le_integral_abs hpp
      _ ≤ ∫ t in (-(profileX 1))..(profileX 1), (Cq * δ) :=
          intervalIntegral.integral_mono_on hpp habs intervalIntegrable_const hpt
      _ = Cq * δ * (2 * profileX 1) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ M * (2 * profileX 1) * δ := by
          calc Cq * δ * (2 * profileX 1) = (Cq * (2 * profileX 1)) * δ := by ring
            _ ≤ (M * (2 * profileX 1)) * δ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle h2p) hδ0
  · -- `E₂`, Lipschitz bound
    intro v hv v' hv'
    have hkeyv : E2 n h v - E2 n 0 v =
        ∫ t in (-(profileX 1))..(profileX 1),
          (iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v
            - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v) := by
      rw [mE2_eq n h v, mE2_eq n 0 v]
      exact (intervalIntegral.integral_sub (hIhE2 v hv) (hI0E2 v hv)).symm
    have hkeyv' : E2 n h v' - E2 n 0 v' =
        ∫ t in (-(profileX 1))..(profileX 1),
          (iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v'
            - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v') := by
      rw [mE2_eq n h v', mE2_eq n 0 v']
      exact (intervalIntegral.integral_sub (hIhE2 v' hv') (hI0E2 v' hv')).symm
    have hsub : (E2 n h v - E2 n 0 v) - (E2 n h v' - E2 n 0 v') =
        ∫ t in (-(profileX 1))..(profileX 1),
          ((iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v
              - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v)
            - (iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v'
              - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v')) := by
      rw [hkeyv, hkeyv',
        ← intervalIntegral.integral_sub ((hIhE2 v hv).sub (hI0E2 v hv))
          ((hIhE2 v' hv').sub (hI0E2 v' hv'))]
    have hpair : IntervalIntegrable (fun t : ℝ =>
        (iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v
            - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v)
          - (iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v'
            - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v'))
        volume (-(profileX 1)) (profileX 1) :=
      ((hIhE2 v hv).sub (hI0E2 v hv)).sub ((hIhE2 v' hv').sub (hI0E2 v' hv'))
    have hpt : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
        |(iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v
            - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v)
          - (iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v'
            - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v')|
        ≤ Cr * δ * |v - v'| := by
      intro t ht
      have htI : t ∈ Set.uIcc (-(profileX 1)) (profileX 1) := by
        rw [Set.uIcc_of_le hpp]; exact ht
      have hd1 : ∀ x ∈ Set.Icc c (1 - tau), HasDerivAt (fun s : ℝ =>
          iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) s)
          (iteratedDeriv (n + 1) (fun u : ℝ => graphPhiH n h (u, t)) x) x :=
        fun x hx => hasDerivAt_iteratedDeriv_section (V := graphPos h) (isOpen_graphPos hh)
          (contDiffOn_graphPhiH n hh) n (hmemh x hx t htI)
      have hd0 : ∀ x ∈ Set.Icc c (1 - tau), HasDerivAt (fun s : ℝ =>
          iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) s)
          (iteratedDeriv (n + 1) (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) x) x :=
        fun x hx => hasDerivAt_iteratedDeriv_section (V := graphPos (0 : ℝ → ℝ))
          (isOpen_graphPos contDiff_const) (contDiffOn_graphPhiH n contDiff_const) n
          (hmem0 x hx t htI)
      have hdiff : ∀ x ∈ Set.Icc c (1 - tau), DifferentiableAt ℝ (fun s : ℝ =>
          (iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) s
            - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) s)) x :=
        fun x hx => (hd1 x hx).differentiableAt.sub (hd0 x hx).differentiableAt
      have hbd : ∀ x ∈ Set.Icc c (1 - tau), ‖deriv (fun s : ℝ =>
          (iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) s
            - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) s)) x‖
          ≤ Cr * δ := by
        intro x hx
        have hdv : deriv (fun s : ℝ =>
            (iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) s
              - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) s)) x
            = iteratedDeriv (n + 1) (fun u : ℝ => graphPhiH n h (u, t)) x
              - iteratedDeriv (n + 1) (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) x :=
          ((hd1 x hx).sub (hd0 x hx)).deriv
        rw [hdv, Real.norm_eq_abs]
        have h1 := hCr h δ hh hδpos hδR (fun j hj s => hjet j hj s) x hx t ht
        rw [hfoldh t, hfold0 t] at h1
        exact h1
      have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
        (s := Set.Icc c (1 - tau))
        (f := fun s : ℝ =>
          (iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) s
            - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) s))
        (C := Cr * δ) hdiff hbd (convex_Icc c (1 - tau))
        hv' hv
      simpa only [Real.norm_eq_abs] using hmv
    calc |(E2 n h v - E2 n 0 v) - (E2 n h v' - E2 n 0 v')|
        = |∫ t in (-(profileX 1))..(profileX 1),
            ((iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v
                - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v)
              - (iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v'
                - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v'))| := by
          rw [hsub]
      _ ≤ ∫ t in (-(profileX 1))..(profileX 1),
            |(iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v
                - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v)
              - (iteratedDeriv n (fun u : ℝ => graphPhiH n h (u, t)) v'
                - iteratedDeriv n (fun u : ℝ => graphPhiH n (0 : ℝ → ℝ) (u, t)) v')| :=
          intervalIntegral.abs_integral_le_integral_abs hpp
      _ ≤ ∫ t in (-(profileX 1))..(profileX 1), (Cr * δ * |v - v'|) :=
          intervalIntegral.integral_mono_on hpp hpair.abs intervalIntegrable_const hpt
      _ = (Cr * δ * |v - v'|) * (2 * profileX 1) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ M * (2 * profileX 1) * δ * |v - v'| := by
          have hle : Cr ≤ M := by
            rw [hMdef]
            exact le_trans (le_max_right Cq Cr) (le_max_right (max A1 A2) (max Cq Cr))
          calc (Cr * δ * |v - v'|) * (2 * profileX 1)
              = (Cr * (2 * profileX 1)) * δ * |v - v'| := by ring
            _ ≤ (M * (2 * profileX 1)) * δ * |v - v'| :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle h2p) hδ0)
                  (abs_nonneg _)

end

end Work.OddVolterra.Existence

namespace Work.Anchor

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- The requested lemma: `Ξ` is Lipschitz at `h = 0` in the `C^{n+2}` topology, with a
constant valid for all perturbations whose derivatives up to order `n + 2` are bounded by
`δ ≤ 1/100`, on the slope interval `[1/2, 19/20]`. -/
theorem Xi_close (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
        (1 - Work.OddVolterra.tau) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20 : ℝ),
        ‖Work.OddVolterra.Xi n h s - Work.OddVolterra.Xi n 0 s‖ ≤ C * δ := by
  obtain ⟨C₀, hC₀nn, hE⟩ := Work.OddVolterra.Existence.xi_close_E1_E2_hundred n hn
    (c := (1 / 2 : ℝ) / 2) (by norm_num)
    (by rw [Work.OddVolterra.Smooth.one_sub_tau_eq]; norm_num)
  obtain ⟨K, hKpos, hK⟩ := Work.OddVolterra.Existence.xi_close_assembly n hn
    (a := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨K * (C₀ + 1), by positivity, ?_⟩
  intro h hh hsupp δ hδpos hδR hjet s hs
  have hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100 := by
    intro t
    have h1 : |iteratedDeriv 0 h t| ≤ δ := hjet 0 (by omega) t
    rw [iteratedDeriv_zero] at h1
    linarith
  obtain ⟨hE1b, hE1l, hE2b, hE2l⟩ := hE h δ hh hδpos hδR hjet
  have hmain := hK h (C₀ * δ) (mul_nonneg hC₀nn hδpos.le) hh hsupp hsmall
    hE1b hE1l hE2b hE2l s ⟨hs.1, by linarith [hs.2]⟩
  calc ‖Work.OddVolterra.Xi n h s - Work.OddVolterra.Xi n 0 s‖ ≤ K * (C₀ * δ) := hmain
    _ = K * C₀ * δ := by ring
    _ ≤ K * (C₀ + 1) * δ := by
        have h : 0 ≤ K * δ := mul_nonneg hKpos.le hδpos.le
        have he : K * (C₀ + 1) * δ = K * C₀ * δ + K * δ := by ring
        rw [he]; linarith

end Work.Anchor

