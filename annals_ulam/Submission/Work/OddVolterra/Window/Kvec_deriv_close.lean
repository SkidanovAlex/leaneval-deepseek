import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.JM_eq_J
import Submission.Work.Geometry.Ulam.ulam_faa_j
import Submission.Work.OddVolterra.Window.Zrad_jet_bounds
import Submission.Work.OddVolterra.Window.Theta_close_aux
import Submission.Work.OddVolterra.Window.krad_data
import Submission.Work.OddVolterra.Window.KvecDefs
import Submission.Work.OddVolterra.Window.JetCurve_box
import Submission.Work.OddVolterra.Window.KvecJet_data
import Submission.Work.OddVolterra.Window.KvecJet_smooth

/-!
# Bounds and closeness of the odd Abel kernel vector `Kvec` on the transition window

The target `Kvec_deriv_close` bounds the norm of

`Kvec n h a σ z = ![- (K₁(a,σ,-z₀) z₂ + K₁(a,σ,z₁) z₃), - (K₂(a,σ,-z₀) z₂ + K₂(a,σ,z₁) z₃)]`

and of its `a`-derivative on the window `σ ∈ [7/10,1]`, `a ∈ [9/20,σ]`, `|z i| ≤ 2`, `z 0, z 1 ≥ 1/5`,
uniformly over perturbations `h` supported in `[1-2τ,1-τ]` which are `δ`-small in `C^{n+2}`, and it
shows that the difference from the unperturbed kernel is `O(δ)`.

The route: off the diagonal (`a < σ`) and where `krad h σ t a > 0` the two kernels equal their
explicit smooth extensions `k1ext`, `k2ext` (`Kernel.Diag`).  Those extensions are the Faà-di-Bruno
polynomial of the radicand jet divided by the square root of the radicand; hence each component of
`Kvec` is the composition `F ∘ 𝐉` of a *fixed* smooth function `F` of the finite jet `KJIx n → ℝ`
(`KvecDefs`) with the jet curve `u ↦ KJet n h σ z u`.  The jet components are bounded, `O(δ)`-close
and have bounded `u`-derivatives (`KvecJet_data`), the two components are smooth on `KJopen`
(`KvecJet_smooth`), and the general jet-curve lemma `JetCurve_box` converts this into the four
estimates.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## Unfolding the kernels at the jet -/

/-- The first extracted jet block of the jet curve is the jet of `Zrad`. -/
lemma KJZ1_KJet_lt (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) {k : ℕ} (hk : k < n + 2) :
    KJZ1 n (KJet n h σ z u) k = kjet h σ (-(z 0)) u k := by
  rw [KJZ1_of_lt n _ hk]
  rfl

/-- The second extracted jet block of the jet curve is the jet of `Zrad`. -/
lemma KJZ2_KJet_lt (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) {k : ℕ} (hk : k < n + 2) :
    KJZ2 n (KJet n h σ z u) k = kjet h σ (z 1) u k := by
  rw [KJZ2_of_lt n _ hk]
  rfl

/-- The extracted derivative block of the jet curve. -/
lemma KJW_KJet_lt (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) {k : ℕ} (hk : k < n + 1) :
    KJW n (KJet n h σ z u) k = iteratedDeriv (k + 1) h u := by
  rw [KJW_of_lt n _ hk]
  rfl

/-- The `m`-th derivative of `lineSlope h · t` for `m ≥ 1` is the `(m+1)`-st derivative of `h`. -/
lemma iteratedDeriv_lineSlope (h : ℝ → ℝ) (u t : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    iteratedDeriv m (fun v : ℝ => lineSlope h v t) u = iteratedDeriv (m + 1) h u := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have h1 : iteratedDeriv (m' + 1) (fun v : ℝ => lineSlope h v t) u
      = iteratedDeriv (m' + 1) (deriv h) u :=
    iteratedDeriv_succ_add_const m' t (deriv h) u
  rw [h1, iteratedDeriv_succ' (n := m' + 1) (f := h)]

/-- `KJk1` applied to the first block of the jet curve is `k1ext` at `t = -z₀`. -/
lemma KJk1_KJet_eq (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) :
    KJk1 n u (KJZ1 n (KJet n h σ z u)) (krad h σ (-(z 0)) u)
      = k1ext n h σ (-(z 0)) u := by
  simp only [KJk1, k1ext]
  have hfun : (fun j : Fin (n + 2) => KJZ1 n (KJet n h σ z u) j.1)
      = fun j : Fin (n + 2) => kjet h σ (-(z 0)) u j.1 := by
    funext j; exact KJZ1_KJet_lt n h σ z u j.2
  rw [hfun]

/-- `KJk1` applied to the second block of the jet curve is `k1ext` at `t = z₁`. -/
lemma KJk1_KJet_eq2 (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) :
    KJk1 n u (KJZ2 n (KJet n h σ z u)) (krad h σ (z 1) u)
      = k1ext n h σ (z 1) u := by
  simp only [KJk1, k1ext]
  have hfun : (fun j : Fin (n + 2) => KJZ2 n (KJet n h σ z u) j.1)
      = fun j : Fin (n + 2) => kjet h σ (z 1) u j.1 := by
    funext j; exact KJZ2_KJet_lt n h σ z u j.2
  rw [hfun]

/-- `KJk2` applied to the first block of the jet curve is `k2ext` at `t = -z₀`. -/
lemma KJk2_KJet_eq (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) :
    KJk2 n u σ (-(z 0)) (KJZ1 n (KJet n h σ z u)) (krad h σ (-(z 0)) u)
        (KJW n (KJet n h σ z u))
      = k2ext n h σ (-(z 0)) u := by
  simp only [KJk2, k2ext]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hfun : (fun j : Fin (i + 1) => KJZ1 n (KJet n h σ z u) j.1)
      = fun j : Fin (i + 1) => kjet h σ (-(z 0)) u j.1 := by
    funext j
    exact KJZ1_KJet_lt n h σ z u (by have := j.2; omega)
  rw [hfun]
  have hlast : (if n - i = 0 then -(z 0) + KJW n (KJet n h σ z u) 0
        else KJW n (KJet n h σ z u) (n - i))
      = iteratedDeriv (n - i) (fun v : ℝ => lineSlope h v (-(z 0))) u := by
    by_cases h0 : n - i = 0
    · rw [if_pos h0, h0, iteratedDeriv_zero, KJW_KJet_lt n h σ z u (by omega : 0 < n + 1),
        iteratedDeriv_one]
      rfl
    · rw [if_neg h0, KJW_KJet_lt n h σ z u (by omega : n - i < n + 1)]
      exact (iteratedDeriv_lineSlope h u (-(z 0)) (n - i) (by omega)).symm
  rw [hlast]

/-- `KJk2` applied to the second block of the jet curve is `k2ext` at `t = z₁`. -/
lemma KJk2_KJet_eq2 (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) :
    KJk2 n u σ (z 1) (KJZ2 n (KJet n h σ z u)) (krad h σ (z 1) u)
        (KJW n (KJet n h σ z u))
      = k2ext n h σ (z 1) u := by
  simp only [KJk2, k2ext]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hfun : (fun j : Fin (i + 1) => KJZ2 n (KJet n h σ z u) j.1)
      = fun j : Fin (i + 1) => kjet h σ (z 1) u j.1 := by
    funext j
    exact KJZ2_KJet_lt n h σ z u (by have := j.2; omega)
  rw [hfun]
  have hlast : (if n - i = 0 then z 1 + KJW n (KJet n h σ z u) 0
        else KJW n (KJet n h σ z u) (n - i))
      = iteratedDeriv (n - i) (fun v : ℝ => lineSlope h v (z 1)) u := by
    by_cases h0 : n - i = 0
    · rw [if_pos h0, h0, iteratedDeriv_zero, KJW_KJet_lt n h σ z u (by omega : 0 < n + 1),
        iteratedDeriv_one]
      rfl
    · rw [if_neg h0, KJW_KJet_lt n h σ z u (by omega : n - i < n + 1)]
      exact (iteratedDeriv_lineSlope h u (z 1) (n - i) (by omega)).symm
  rw [hlast]

/-! ## The two rows of `Kvec` as functions of the jet -/

/-- **First row of the kernel vector.** -/
lemma Kvec_zero_eq_KF1 {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {σ : ℝ} {z : St}
    {u : ℝ} (hu : u < σ) (hk1 : 0 < krad h σ (-(z 0)) u) (hk2 : 0 < krad h σ (z 1) u) :
    Kvec n h u σ (z 0) (z 1) (z 2) (z 3) 0 = KF1 n (KJet n h σ z u) := by
  have hKvec : Kvec n h u σ (z 0) (z 1) (z 2) (z 3) 0
      = -(K1 n h u σ (-(z 0)) * (z 2) + K1 n h u σ (z 1) * (z 3)) := by simp [Kvec]
  rw [hKvec, K1_eq_k1ext hh n hu hk1, K1_eq_k1ext hh n hu hk2]
  simp only [KF1, KJet_aa, KJet_c2, KJet_c3, KJet_kd1, KJet_kd2]
  rw [← KJk1_KJet_eq n h σ z u, ← KJk1_KJet_eq2 n h σ z u]

/-- **Second row of the kernel vector.** -/
lemma Kvec_one_eq_KF2 {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hn : 1 ≤ n) {σ : ℝ}
    {z : St} {u : ℝ} (hu : u < σ) (hk1 : 0 < krad h σ (-(z 0)) u) (hk2 : 0 < krad h σ (z 1) u) :
    Kvec n h u σ (z 0) (z 1) (z 2) (z 3) 1 = KF2 n (KJet n h σ z u) := by
  have hKvec : Kvec n h u σ (z 0) (z 1) (z 2) (z 3) 1
      = -(K2 n h u σ (-(z 0)) * (z 2) + K2 n h u σ (z 1) * (z 3)) := by simp [Kvec]
  rw [hKvec, K2_eq_k2ext hh n hn hu hk1, K2_eq_k2ext hh n hn hu hk2]
  simp only [KF2, KJet_aa, KJet_sg, KJet_t1, KJet_t2, KJet_c2, KJet_c3, KJet_kd1, KJet_kd2]
  rw [← KJk2_KJet_eq n h σ z u, ← KJk2_KJet_eq2 n h σ z u]

theorem Kvec_deriv_close (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 ≤ δ → δ ≤ 1 / 100 →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ σ ∈ Set.Icc (7 / 10 : ℝ) 1, ∀ z : Work.OddVolterra.St,
        (1 / 5 : ℝ) ≤ z 0 → (1 / 5 : ℝ) ≤ z 1 → (∀ i : Fin 4, |z i| ≤ 2) →
        ∀ a ∈ Set.Icc (9 / 20 : ℝ) σ, a < σ →
          ‖Work.OddVolterra.Kvec n h a σ (z 0) (z 1) (z 2) (z 3)‖ ≤ C ∧
          ‖Work.OddVolterra.Kvec n h a σ (z 0) (z 1) (z 2) (z 3) -
            Work.OddVolterra.Kvec n 0 a σ (z 0) (z 1) (z 2) (z 3)‖ ≤ C * δ ∧
          ‖deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a‖ ≤ C ∧
          ‖deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a -
           deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3)) a‖ ≤ C * δ := by
  obtain ⟨C1, hC1n, hC1⟩ := JetCurve_box (E := KJIx n → ℝ) (fun v => KF1 n v) (isOpen_KJopen n)
    (convex_KJbox n (KJbz n)) (isCompact_KJbox n (KJbz n)) (KJbox_subset_KJopen n (KJbz n))
    (KvecJet_smooth n).1 (KJbz_nonneg n)
  obtain ⟨C2, hC2n, hC2⟩ := JetCurve_box (E := KJIx n → ℝ) (fun v => KF2 n v) (isOpen_KJopen n)
    (convex_KJbox n (KJbz n)) (isCompact_KJbox n (KJbz n)) (KJbox_subset_KJopen n (KJbz n))
    (KvecJet_smooth n).2 (KJbz_nonneg n)
  have hCnn : 0 ≤ (C1 + C2 + 1) * (KJbz n + 1) := by
    have h1 := hC1n; have h2 := hC2n; have h3 := KJbz_nonneg n; nlinarith
  refine ⟨(C1 + C2 + 1) * (KJbz n + 1), hCnn, ?_⟩
  intro h δ hh hδ0 hδ1 hsupp hjet σ hσ z hz0 hz1 hz a ha hat
  obtain ⟨hmem1, hcd1, hcd0, hder1, hder0, hclose, hclosed⟩ :=
    KvecJet_data (n := n) (hn := hn) (h := h) (hh := hh) (δ := δ) (σ := σ) (z := z)
      (hδ0 := hδ0) (hδ1 := hδ1) (hsupp := hsupp) (hjet := hjet) (hσ := hσ)
      (hz0 := hz0) (hz1 := hz1) (hz := hz) (a := a) (ha := ha)
  obtain ⟨hmem0, -, -, -, -, -, -⟩ :=
    KvecJet_data (n := n) (hn := hn) (h := (0 : ℝ → ℝ)) (hh := contDiff_const) (δ := 0)
      (σ := σ) (z := z) (hδ0 := le_rfl) (hδ1 := by norm_num) (hsupp := by simp)
      (hjet := by intro k hk s; simp) (hσ := hσ) (hz0 := hz0) (hz1 := hz1) (hz := hz)
      (a := a) (ha := ha)
  have hδ' : 0 ≤ KJbz n * δ := mul_nonneg (KJbz_nonneg n) hδ0
  have hJ1 := hC1 (fun u => KJet n h σ z u) (fun u => KJet n 0 σ z u) a (KJbz n * δ) hδ'
      hcd1 hcd0 hmem1 hmem0 hder1 hder0 hclose hclosed
  have hJ2 := hC2 (fun u => KJet n h σ z u) (fun u => KJet n 0 σ z u) a (KJbz n * δ) hδ'
      hcd1 hcd0 hmem1 hmem0 hder1 hder0 hclose hclosed
  obtain ⟨hA1, -, hE1, -, hG1, hH1⟩ := hJ1
  obtain ⟨hA2, -, hE2, -, hG2, hH2⟩ := hJ2
  -- constants
  have hC1_le : C1 ≤ (C1 + C2 + 1) * (KJbz n + 1) := by
    have h1 := hC1n; have h2 := hC2n; have h3 := KJbz_nonneg n; nlinarith
  have hC2_le : C2 ≤ (C1 + C2 + 1) * (KJbz n + 1) := by
    have h1 := hC1n; have h2 := hC2n; have h3 := KJbz_nonneg n; nlinarith
  have hC1d_le : C1 * (KJbz n * δ) ≤ (C1 + C2 + 1) * (KJbz n + 1) * δ := by
    have h1 := hC1n; have h2 := hC2n; have h3 := KJbz_nonneg n; nlinarith
  have hC2d_le : C2 * (KJbz n * δ) ≤ (C1 + C2 + 1) * (KJbz n + 1) * δ := by
    have h1 := hC1n; have h2 := hC2n; have h3 := KJbz_nonneg n; nlinarith
  have hCdnn : 0 ≤ (C1 + C2 + 1) * (KJbz n + 1) * δ := by
    have h1 := hC1n; have h2 := hC2n; have h3 := KJbz_nonneg n; nlinarith
  have hfin2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by intro i; fin_cases i <;> simp
  -- positivity of the four radicands at `a`
  have hkA : 0 < krad h σ (-(z 0)) a := by
    have h1 := hmem1.1 KJIx.kd1
    simp only [KJLo, KJet_kd1] at h1
    linarith
  have hkB : 0 < krad h σ (z 1) a := by
    have h1 := hmem1.1 KJIx.kd2
    simp only [KJLo, KJet_kd2] at h1
    linarith
  have hkA0 : 0 < krad 0 σ (-(z 0)) a := by
    have h1 := hmem0.1 KJIx.kd1
    simp only [KJLo, KJet_kd1] at h1
    linarith
  have hkB0 : 0 < krad 0 σ (z 1) a := by
    have h1 := hmem0.1 KJIx.kd2
    simp only [KJLo, KJet_kd2] at h1
    linarith
  -- the neighbourhood on which the kernels equal their jet formulas
  have hev : ∀ᶠ u in 𝓝 a, u < σ ∧ 0 < krad h σ (-(z 0)) u ∧ 0 < krad h σ (z 1) u ∧
      0 < krad 0 σ (-(z 0)) u ∧ 0 < krad 0 σ (z 1) u := by
    have h1 : ∀ᶠ u in 𝓝 a, u < σ := isOpen_Iio.mem_nhds hat
    have h2 : ∀ᶠ u in 𝓝 a, 0 < krad h σ (-(z 0)) u :=
      (continuous_krad hh σ (-(z 0))).continuousAt.eventually (isOpen_Ioi.mem_nhds hkA)
    have h3 : ∀ᶠ u in 𝓝 a, 0 < krad h σ (z 1) u :=
      (continuous_krad hh σ (z 1)).continuousAt.eventually (isOpen_Ioi.mem_nhds hkB)
    have h4 : ∀ᶠ u in 𝓝 a, 0 < krad 0 σ (-(z 0)) u :=
      (continuous_krad contDiff_const σ (-(z 0))).continuousAt.eventually (isOpen_Ioi.mem_nhds hkA0)
    have h5 : ∀ᶠ u in 𝓝 a, 0 < krad 0 σ (z 1) u :=
      (continuous_krad contDiff_const σ (z 1)).continuousAt.eventually (isOpen_Ioi.mem_nhds hkB0)
    filter_upwards [h1, h2, h3, h4, h5] with u h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  have hid1 : (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3) 0)
      =ᶠ[𝓝 a] (fun u : ℝ => KF1 n (KJet n h σ z u)) := by
    filter_upwards [hev] with u hu
    exact Kvec_zero_eq_KF1 hh hu.1 hu.2.1 hu.2.2.1
  have hid1' : (fun u : ℝ => Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3) 0)
      =ᶠ[𝓝 a] (fun u : ℝ => KF1 n (KJet n 0 σ z u)) := by
    filter_upwards [hev] with u hu
    exact Kvec_zero_eq_KF1 contDiff_const hu.1 hu.2.2.2.1 hu.2.2.2.2
  have hid2 : (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3) 1)
      =ᶠ[𝓝 a] (fun u : ℝ => KF2 n (KJet n h σ z u)) := by
    filter_upwards [hev] with u hu
    exact Kvec_one_eq_KF2 hh hn hu.1 hu.2.1 hu.2.2.1
  have hid2' : (fun u : ℝ => Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3) 1)
      =ᶠ[𝓝 a] (fun u : ℝ => KF2 n (KJet n 0 σ z u)) := by
    filter_upwards [hev] with u hu
    exact Kvec_one_eq_KF2 contDiff_const hn hu.1 hu.2.2.2.1 hu.2.2.2.2
  -- differentiability of the curves and the components
  have hJ1diff : DifferentiableAt ℝ (fun u : ℝ => KJet n h σ z u) a :=
    (hcd1.differentiable (by simp)).differentiableAt
  have hJ0diff : DifferentiableAt ℝ (fun u : ℝ => KJet n 0 σ z u) a :=
    (hcd0.differentiable (by simp)).differentiableAt
  have hmem1' : KJet n h σ z a ∈ KJopen n := KJbox_subset_KJopen n (KJbz n) hmem1
  have hmem0' : KJet n 0 σ z a ∈ KJopen n := KJbox_subset_KJopen n (KJbz n) hmem0
  have hF1diff : DifferentiableAt ℝ (fun v : KJIx n → ℝ => KF1 n v) (KJet n h σ z a) :=
    ((KvecJet_smooth n).1.differentiableOn (by simp)).differentiableAt
      ((isOpen_KJopen n).mem_nhds hmem1')
  have hF1diff0 : DifferentiableAt ℝ (fun v : KJIx n → ℝ => KF1 n v) (KJet n 0 σ z a) :=
    ((KvecJet_smooth n).1.differentiableOn (by simp)).differentiableAt
      ((isOpen_KJopen n).mem_nhds hmem0')
  have hF2diff : DifferentiableAt ℝ (fun v : KJIx n → ℝ => KF2 n v) (KJet n h σ z a) :=
    ((KvecJet_smooth n).2.differentiableOn (by simp)).differentiableAt
      ((isOpen_KJopen n).mem_nhds hmem1')
  have hF2diff0 : DifferentiableAt ℝ (fun v : KJIx n → ℝ => KF2 n v) (KJet n 0 σ z a) :=
    ((KvecJet_smooth n).2.differentiableOn (by simp)).differentiableAt
      ((isOpen_KJopen n).mem_nhds hmem0')
  have hcomp1 : DifferentiableAt ℝ (fun u : ℝ => KF1 n (KJet n h σ z u)) a :=
    hF1diff.comp a hJ1diff
  have hcomp2 : DifferentiableAt ℝ (fun u : ℝ => KF2 n (KJet n h σ z u)) a :=
    hF2diff.comp a hJ1diff
  have hcomp1' : DifferentiableAt ℝ (fun u : ℝ => KF1 n (KJet n 0 σ z u)) a :=
    hF1diff0.comp a hJ0diff
  have hcomp2' : DifferentiableAt ℝ (fun u : ℝ => KF2 n (KJet n 0 σ z u)) a :=
    hF2diff0.comp a hJ0diff
  have hDiffh : ∀ i : Fin 2, DifferentiableAt ℝ
      (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3) i) a := by
    intro i
    fin_cases i
    · exact hid1.differentiableAt_iff.mpr hcomp1
    · exact hid2.differentiableAt_iff.mpr hcomp2
  have hDiff0 : ∀ i : Fin 2, DifferentiableAt ℝ
      (fun u : ℝ => Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3) i) a := by
    intro i
    fin_cases i
    · exact hid1'.differentiableAt_iff.mpr hcomp1'
    · exact hid2'.differentiableAt_iff.mpr hcomp2'
  have hcoordh : ∀ i : Fin 2, (deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a) i
      = deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3) i) a := by
    intro i
    rw [deriv_pi (fun j => hDiffh j)]
  have hcoord0 : ∀ i : Fin 2, (deriv (fun u : ℝ => Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3)) a) i
      = deriv (fun u : ℝ => Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3) i) a := by
    intro i
    rw [deriv_pi (fun j => hDiff0 j)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pi_norm_le_iff_of_nonneg hCnn]
    intro i
    rcases hfin2 i with h | h
    · rw [h, Real.norm_eq_abs, Kvec_zero_eq_KF1 hh hat hkA hkB]
      exact le_trans hA1 hC1_le
    · rw [h, Real.norm_eq_abs, Kvec_one_eq_KF2 hh hn hat hkA hkB]
      exact le_trans hA2 hC2_le
  · rw [pi_norm_le_iff_of_nonneg hCdnn]
    intro i
    rcases hfin2 i with h | h
    · rw [h, Real.norm_eq_abs, Pi.sub_apply, Kvec_zero_eq_KF1 hh hat hkA hkB,
        Kvec_zero_eq_KF1 (h := (0 : ℝ → ℝ)) contDiff_const hat hkA0 hkB0]
      exact le_trans hG1 hC1d_le
    · rw [h, Real.norm_eq_abs, Pi.sub_apply, Kvec_one_eq_KF2 hh hn hat hkA hkB,
        Kvec_one_eq_KF2 (h := (0 : ℝ → ℝ)) contDiff_const hn hat hkA0 hkB0]
      exact le_trans hG2 hC2d_le
  · rw [pi_norm_le_iff_of_nonneg hCnn]
    intro i
    rw [hcoordh i]
    rcases hfin2 i with h | h
    · rw [h, Real.norm_eq_abs, hid1.deriv_eq]
      exact le_trans hE1 hC1_le
    · rw [h, Real.norm_eq_abs, hid2.deriv_eq]
      exact le_trans hE2 hC2_le
  · rw [pi_norm_le_iff_of_nonneg hCdnn]
    intro i
    rw [Pi.sub_apply, hcoordh i, hcoord0 i]
    rcases hfin2 i with h | h
    · rw [h, Real.norm_eq_abs, hid1.deriv_eq, hid1'.deriv_eq]
      exact le_trans hH1 hC1d_le
    · rw [h, Real.norm_eq_abs, hid2.deriv_eq, hid2'.deriv_eq]
      exact le_trans hH2 hC2d_le

end
end Work.OddVolterra.Window
