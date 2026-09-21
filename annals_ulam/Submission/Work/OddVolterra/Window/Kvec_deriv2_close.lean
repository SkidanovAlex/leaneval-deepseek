import Mathlib
import Submission.Work.OddVolterra.Window.Kvec_deriv_close
import Submission.Work.OddVolterra.Window.KvecJet_data
import Submission.Work.OddVolterra.Window.JetCurve_box
import Submission.Work.OddVolterra.Window.KvecJet_smooth
import Submission.Work.OddVolterra.Window.deriv_deriv_pi
import Submission.Work.OddVolterra.Window.KvecJet_data2

/-!
# The second `u`-derivative of the odd Abel kernel vector `Kvec` on the transition window

`Kvec_deriv_close` bounds `Kvec n h a σ z` and its first `a`-derivative on the transition window
and shows that the difference from the unperturbed kernel is `O(δ)`.  This file does the same for
the **second** `a`-derivative.

Off the diagonal (`a < σ`) and where the radicands are positive, each component of `Kvec` is a
composition `F ∘ j` of one of the two fixed smooth functions `KF1 n`, `KF2 n` of the finite jet
(`KvecDefs`) with the jet curve `j u = KJet n h σ z u`, so the second derivative is obtained by
applying `JetCurve_box` not to `KF_i` but to the "velocity" function

`KF_i' (x, y) = fderiv ℝ (KF_i) x y`  (`KF1'`, `KF2'`)

along the curve `u ↦ (j u, j' u)`, whose range lies in
`KJbox n (KJbz n) × closedBall 0 B`; here `B` is the constant of `KvecJet_data2`, which supplies
the bounds and the `O(δ)`-closeness of `j` and of its first two derivatives.  The remaining
ingredients are the chain rule (`KF1'_comp`, `KF2'_comp`: `KF_i' (j u, j' u) = (KF_i ∘ j)' u`),
the eventual equality of a component of `Kvec` with the corresponding composite
(`Kvec_zero_eq_KF1`, `Kvec_one_eq_KF2`), and the coordinatewise decomposition of the second
derivative of a `Fin 2`-valued curve (`deriv_deriv_pi`).
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- The first component of the kernel vector, differentiated once in the jet variable and
evaluated at the pair `(jet, derivative of the jet)`. -/
def KF1' (n : ℕ) (p : (KJIx n → ℝ) × (KJIx n → ℝ)) : ℝ :=
  fderiv ℝ (fun v : KJIx n → ℝ => KF1 n v) p.1 p.2

/-- The second component of the kernel vector, differentiated once in the jet variable. -/
def KF2' (n : ℕ) (p : (KJIx n → ℝ) × (KJIx n → ℝ)) : ℝ :=
  fderiv ℝ (fun v : KJIx n → ℝ => KF2 n v) p.1 p.2

lemma KF1'_smooth (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : (KJIx n → ℝ) × (KJIx n → ℝ) => KF1' n p)
      (KJopen n ×ˢ Set.univ) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (fun v : KJIx n → ℝ => KF1 n v)) (KJopen n) :=
    (KvecJet_smooth n).1.fderiv_of_isOpen (isOpen_KJopen n) (le_refl _)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : (KJIx n → ℝ) × (KJIx n → ℝ) =>
      fderiv ℝ (fun v : KJIx n → ℝ => KF1 n v) p.1) (KJopen n ×ˢ Set.univ) :=
    (h1.comp contDiffOn_fst (fun p hp => hp.1))
  exact ContDiffOn.clm_apply h2 (contDiffOn_id.snd)

lemma KF2'_smooth (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : (KJIx n → ℝ) × (KJIx n → ℝ) => KF2' n p)
      (KJopen n ×ˢ Set.univ) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (fun v : KJIx n → ℝ => KF2 n v)) (KJopen n) :=
    (KvecJet_smooth n).2.fderiv_of_isOpen (isOpen_KJopen n) (le_refl _)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : (KJIx n → ℝ) × (KJIx n → ℝ) =>
      fderiv ℝ (fun v : KJIx n → ℝ => KF2 n v) p.1) (KJopen n ×ˢ Set.univ) :=
    (h1.comp contDiffOn_fst (fun p hp => hp.1))
  exact ContDiffOn.clm_apply h2 (contDiffOn_id.snd)

lemma KF1'_comp {n : ℕ} {h : ℝ → ℝ} {σ : ℝ} {z : St} {u : ℝ}
    (hu : KJet n h σ z u ∈ KJopen n)
    (hd : DifferentiableAt ℝ (fun v : ℝ => KJet n h σ z v) u) :
    KF1' n (KJet n h σ z u, deriv (fun v : ℝ => KJet n h σ z v) u)
      = deriv (fun v : ℝ => KF1 n (KJet n h σ z v)) u := by
  have h1 : DifferentiableAt ℝ (fun v : KJIx n → ℝ => KF1 n v) (KJet n h σ z u) :=
    ((KvecJet_smooth n).1.differentiableOn (by simp)).differentiableAt
      ((isOpen_KJopen n).mem_nhds hu)
  have h2 := (h1.hasFDerivAt.comp_hasDerivAt u hd.hasDerivAt).deriv
  rw [KF1']
  exact h2.symm

lemma KF2'_comp {n : ℕ} {h : ℝ → ℝ} {σ : ℝ} {z : St} {u : ℝ}
    (hu : KJet n h σ z u ∈ KJopen n)
    (hd : DifferentiableAt ℝ (fun v : ℝ => KJet n h σ z v) u) :
    KF2' n (KJet n h σ z u, deriv (fun v : ℝ => KJet n h σ z v) u)
      = deriv (fun v : ℝ => KF2 n (KJet n h σ z v)) u := by
  have h1 : DifferentiableAt ℝ (fun v : KJIx n → ℝ => KF2 n v) (KJet n h σ z u) :=
    ((KvecJet_smooth n).2.differentiableOn (by simp)).differentiableAt
      ((isOpen_KJopen n).mem_nhds hu)
  have h2 := (h1.hasFDerivAt.comp_hasDerivAt u hd.hasDerivAt).deriv
  rw [KF2']
  exact h2.symm

lemma norm_prod_le {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    {x : E} {y : F} {c : ℝ} (hx : ‖x‖ ≤ c) (hy : ‖y‖ ≤ c) : ‖(x, y)‖ ≤ c := by
  rw [Prod.norm_def]; exact max_le hx hy


/-- **Second `u`-derivative of the two components of `Kvec` on the window**, with the
`O(δ)`-closeness to the unperturbed kernel. -/
theorem Kvec_deriv2_close (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 ≤ δ → δ ≤ 1 / 100 →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ σ ∈ Set.Icc (7 / 10 : ℝ) 1, ∀ z : Work.OddVolterra.St,
        (1 / 5 : ℝ) ≤ z 0 → (1 / 5 : ℝ) ≤ z 1 → (∀ i : Fin 4, |z i| ≤ 2) →
        ∀ a ∈ Set.Icc (9 / 20 : ℝ) σ, a < σ →
          ‖deriv (deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3))) a‖ ≤ C ∧
          ‖deriv (deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3))) a -
           deriv (deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3))) a‖ ≤ C * δ := by
  obtain ⟨B, hB0, hB⟩ := KvecJet_data2 n hn
  have hF1'sm : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : (KJIx n → ℝ) × (KJIx n → ℝ) => KF1' n p)
      (KJopen n ×ˢ Set.univ) := KF1'_smooth n
  have hF2'sm : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : (KJIx n → ℝ) × (KJIx n → ℝ) => KF2' n p)
      (KJopen n ×ˢ Set.univ) := KF2'_smooth n
  have hUopen : IsOpen (KJopen n ×ˢ (Set.univ : Set (KJIx n → ℝ))) :=
    (isOpen_KJopen n).prod isOpen_univ
  have hcvx : Convex ℝ (KJbox n (KJbz n) ×ˢ Metric.closedBall (0 : KJIx n → ℝ) B) :=
    (convex_KJbox n (KJbz n)).prod (convex_closedBall 0 B)
  have hcpt : IsCompact (KJbox n (KJbz n) ×ˢ Metric.closedBall (0 : KJIx n → ℝ) B) :=
    (isCompact_KJbox n (KJbz n)).prod (isCompact_closedBall 0 B)
  have hKcU : (KJbox n (KJbz n) ×ˢ Metric.closedBall (0 : KJIx n → ℝ) B)
      ⊆ (KJopen n ×ˢ (Set.univ : Set (KJIx n → ℝ))) := by
    intro p hp
    exact ⟨KJbox_subset_KJopen n (KJbz n) hp.1, trivial⟩
  obtain ⟨C1, hC1n, hC1⟩ := JetCurve_box (E := (KJIx n → ℝ) × (KJIx n → ℝ))
    (fun p : (KJIx n → ℝ) × (KJIx n → ℝ) => KF1' n p) hUopen hcvx hcpt hKcU hF1'sm hB0
  obtain ⟨C2, hC2n, hC2⟩ := JetCurve_box (E := (KJIx n → ℝ) × (KJIx n → ℝ))
    (fun p : (KJIx n → ℝ) × (KJIx n → ℝ) => KF2' n p) hUopen hcvx hcpt hKcU hF2'sm hB0
  refine ⟨(max C1 C2 + 1) * (B + 1), by positivity, ?_⟩
  intro h δ hh hδ0 hδ1 hsupp hjet σ hσ z hz0 hz1 hz a ha hat
  -- ## jet data
  obtain ⟨hmem1, hcd1, hcd0, -, -, -, -⟩ :=
    KvecJet_data (n := n) (hn := hn) (h := h) (hh := hh) (δ := δ) (σ := σ) (z := z)
      (hδ0 := hδ0) (hδ1 := hδ1) (hsupp := hsupp)
      (hjet := fun k hk s => hjet k (by omega) s) (hσ := hσ) (hz0 := hz0) (hz1 := hz1)
      (hz := hz) (ha := ha)
  obtain ⟨hmem0, -, -, -, -, -, -⟩ :=
    KvecJet_data (n := n) (hn := hn) (h := (0 : ℝ → ℝ)) (hh := contDiff_const) (δ := δ)
      (σ := σ) (z := z) (hδ0 := hδ0) (hδ1 := hδ1) (hsupp := by simp)
      (hjet := by intro k hk s; simpa using hδ0) (hσ := hσ) (hz0 := hz0) (hz1 := hz1)
      (hz := hz) (ha := ha)
  obtain ⟨hJd1, -, hJv, hJdv, hJdd1, hJdd⟩ :=
    hB (h := h) (δ := δ) (σ := σ) (z := z) (a := a) hh hδ0 hδ1 hsupp hjet hσ hz0 hz1 hz ha
  obtain ⟨hJ0d1, -, -, -, hJ0dd1, -⟩ :=
    hB (h := (0 : ℝ → ℝ)) (δ := δ) (σ := σ) (z := z) (a := a) contDiff_const hδ0 hδ1
      (by simp) (by intro k hk s; simpa using hδ0) hσ hz0 hz1 hz ha
  -- ## the two curves
  have hdJh : ContDiff ℝ (⊤ : ℕ∞) (deriv (fun v : ℝ => KJet n h σ z v)) := by
    simpa only [Function.iterate_one] using hcd1.iterate_deriv 1
  have hdJ0 : ContDiff ℝ (⊤ : ℕ∞) (deriv (fun v : ℝ => KJet n 0 σ z v)) := by
    simpa only [Function.iterate_one] using hcd0.iterate_deriv 1
  set g1 : ℝ → (KJIx n → ℝ) × (KJIx n → ℝ) :=
    fun u => (KJet n h σ z u, deriv (fun v : ℝ => KJet n h σ z v) u) with hg1
  set g0 : ℝ → (KJIx n → ℝ) × (KJIx n → ℝ) :=
    fun u => (KJet n 0 σ z u, deriv (fun v : ℝ => KJet n 0 σ z v) u) with hg0
  have hg1sm : ContDiff ℝ (⊤ : ℕ∞) g1 := by rw [hg1]; exact hcd1.prodMk hdJh
  have hg0sm : ContDiff ℝ (⊤ : ℕ∞) g0 := by rw [hg0]; exact hcd0.prodMk hdJ0
  have hderg1 : deriv g1 a = (deriv (fun v : ℝ => KJet n h σ z v) a,
      deriv (deriv (fun v : ℝ => KJet n h σ z v)) a) := by
    rw [hg1]
    exact (((hcd1.differentiable (by simp)).differentiableAt.hasDerivAt).prodMk
      ((hdJh.differentiable (by simp)).differentiableAt.hasDerivAt)).deriv
  have hderg0 : deriv g0 a = (deriv (fun v : ℝ => KJet n 0 σ z v) a,
      deriv (deriv (fun v : ℝ => KJet n 0 σ z v)) a) := by
    rw [hg0]
    exact (((hcd0.differentiable (by simp)).differentiableAt.hasDerivAt).prodMk
      ((hdJ0.differentiable (by simp)).differentiableAt.hasDerivAt)).deriv
  have hg1mem : g1 a ∈ KJbox n (KJbz n) ×ˢ Metric.closedBall (0 : KJIx n → ℝ) B := by
    rw [hg1]
    exact ⟨hmem1, by rw [Metric.mem_closedBall, dist_zero_right]; exact hJd1⟩
  have hg0mem : g0 a ∈ KJbox n (KJbz n) ×ˢ Metric.closedBall (0 : KJIx n → ℝ) B := by
    rw [hg0]
    exact ⟨hmem0, by rw [Metric.mem_closedBall, dist_zero_right]; exact hJ0d1⟩
  have hderg1b : ‖deriv g1 a‖ ≤ B := by
    rw [hderg1]; exact norm_prod_le hJd1 hJdd1
  have hderg0b : ‖deriv g0 a‖ ≤ B := by
    rw [hderg0]; exact norm_prod_le hJ0d1 hJ0dd1
  have hgclose : ‖g1 a - g0 a‖ ≤ B * δ := by
    have hsub : g1 a - g0 a = (KJet n h σ z a - KJet n 0 σ z a,
        deriv (fun v : ℝ => KJet n h σ z v) a - deriv (fun v : ℝ => KJet n 0 σ z v) a) := by
      rw [hg1, hg0]; rfl
    rw [hsub]; exact norm_prod_le hJv hJdv
  have hdergclose : ‖deriv g1 a - deriv g0 a‖ ≤ B * δ := by
    have hsub : deriv g1 a - deriv g0 a = (
        deriv (fun v : ℝ => KJet n h σ z v) a - deriv (fun v : ℝ => KJet n 0 σ z v) a,
        deriv (deriv (fun v : ℝ => KJet n h σ z v)) a -
          deriv (deriv (fun v : ℝ => KJet n 0 σ z v)) a) := by
      rw [hderg1, hderg0]; rfl
    rw [hsub]; exact norm_prod_le hJdv hJdd
  have hBδ0 : 0 ≤ B * δ := mul_nonneg hB0 hδ0
  obtain ⟨-, -, hE1, hE1', -, hH1⟩ := hC1 g1 g0 a (B * δ) hBδ0 hg1sm hg0sm hg1mem hg0mem
    hderg1b hderg0b hgclose hdergclose
  obtain ⟨-, -, hE2, hE2', -, hH2⟩ := hC2 g1 g0 a (B * δ) hBδ0 hg1sm hg0sm hg1mem hg0mem
    hderg1b hderg0b hgclose hdergclose
  -- ## the eventual identities between `Kvec` and the jet composites
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
  have hev : ∀ᶠ u in 𝓝 a, u < σ ∧ 0 < krad h σ (-(z 0)) u ∧ 0 < krad h σ (z 1) u ∧
      0 < krad 0 σ (-(z 0)) u ∧ 0 < krad 0 σ (z 1) u := by
    have h1 : ∀ᶠ u in 𝓝 a, u < σ := isOpen_Iio.mem_nhds hat
    have h2 : ∀ᶠ u in 𝓝 a, 0 < krad h σ (-(z 0)) u :=
      (continuous_krad hh σ (-(z 0))).continuousAt.eventually (isOpen_Ioi.mem_nhds hkA)
    have h3 : ∀ᶠ u in 𝓝 a, 0 < krad h σ (z 1) u :=
      (continuous_krad hh σ (z 1)).continuousAt.eventually (isOpen_Ioi.mem_nhds hkB)
    have h4 : ∀ᶠ u in 𝓝 a, 0 < krad 0 σ (-(z 0)) u :=
      (continuous_krad contDiff_const σ (-(z 0))).continuousAt.eventually
        (isOpen_Ioi.mem_nhds hkA0)
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
  -- ## the chain rule for the jet composites
  have hmem1o : KJet n h σ z a ∈ KJopen n := KJbox_subset_KJopen n (KJbz n) hmem1
  have hmem0o : KJet n 0 σ z a ∈ KJopen n := KJbox_subset_KJopen n (KJbz n) hmem0
  have hcross1 : (fun u : ℝ => KF1' n (g1 u))
      =ᶠ[𝓝 a] deriv (fun v : ℝ => KF1 n (KJet n h σ z v)) := by
    have hev1 : ∀ᶠ u in 𝓝 a, KJet n h σ z u ∈ KJopen n :=
      hcd1.continuous.continuousAt.eventually ((isOpen_KJopen n).mem_nhds hmem1o)
    filter_upwards [hev1] with u hu
    rw [hg1]
    exact KF1'_comp hu ((hcd1.differentiable (by simp)).differentiableAt)
  have hcross1' : (fun u : ℝ => KF1' n (g0 u))
      =ᶠ[𝓝 a] deriv (fun v : ℝ => KF1 n (KJet n 0 σ z v)) := by
    have hev1 : ∀ᶠ u in 𝓝 a, KJet n 0 σ z u ∈ KJopen n :=
      hcd0.continuous.continuousAt.eventually ((isOpen_KJopen n).mem_nhds hmem0o)
    filter_upwards [hev1] with u hu
    rw [hg0]
    exact KF1'_comp hu ((hcd0.differentiable (by simp)).differentiableAt)
  have hcross2 : (fun u : ℝ => KF2' n (g1 u))
      =ᶠ[𝓝 a] deriv (fun v : ℝ => KF2 n (KJet n h σ z v)) := by
    have hev1 : ∀ᶠ u in 𝓝 a, KJet n h σ z u ∈ KJopen n :=
      hcd1.continuous.continuousAt.eventually ((isOpen_KJopen n).mem_nhds hmem1o)
    filter_upwards [hev1] with u hu
    rw [hg1]
    exact KF2'_comp hu ((hcd1.differentiable (by simp)).differentiableAt)
  have hcross2' : (fun u : ℝ => KF2' n (g0 u))
      =ᶠ[𝓝 a] deriv (fun v : ℝ => KF2 n (KJet n 0 σ z v)) := by
    have hev1 : ∀ᶠ u in 𝓝 a, KJet n 0 σ z u ∈ KJopen n :=
      hcd0.continuous.continuousAt.eventually ((isOpen_KJopen n).mem_nhds hmem0o)
    filter_upwards [hev1] with u hu
    rw [hg0]
    exact KF2'_comp hu ((hcd0.differentiable (by simp)).differentiableAt)
  have hEq1 : deriv (fun u : ℝ => KF1' n (g1 u)) a
      = deriv (deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3) 0)) a :=
    hcross1.deriv_eq.trans (hid1.deriv).deriv_eq.symm
  have hEq1' : deriv (fun u : ℝ => KF1' n (g0 u)) a
      = deriv (deriv (fun u : ℝ => Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3) 0)) a :=
    hcross1'.deriv_eq.trans (hid1'.deriv).deriv_eq.symm
  have hEq2 : deriv (fun u : ℝ => KF2' n (g1 u)) a
      = deriv (deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3) 1)) a :=
    hcross2.deriv_eq.trans (hid2.deriv).deriv_eq.symm
  have hEq2' : deriv (fun u : ℝ => KF2' n (g0 u)) a
      = deriv (deriv (fun u : ℝ => Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3) 1)) a :=
    hcross2'.deriv_eq.trans (hid2'.deriv).deriv_eq.symm
  -- ## the two components are bounded by `C1` resp. `C2`
  have hkey0 : |deriv (deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3) 0)) a| ≤ C1 := by
    rw [← hEq1]; exact hE1
  have hkey0d : |deriv (deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3) 0)) a -
      deriv (deriv (fun u : ℝ => Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3) 0)) a| ≤ C1 * (B * δ) := by
    rw [← hEq1, ← hEq1']; exact hH1
  have hkey1 : |deriv (deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3) 1)) a| ≤ C2 := by
    rw [← hEq2]; exact hE2
  have hkey1d : |deriv (deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3) 1)) a -
      deriv (deriv (fun u : ℝ => Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3) 1)) a| ≤ C2 * (B * δ) := by
    rw [← hEq2, ← hEq2']; exact hH2
  -- ## the `C²` smoothness of the two `Kvec` curves
  have hK1at : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => KF1 n v) (KJet n h σ z a) :=
    (KvecJet_smooth n).1.contDiffAt ((isOpen_KJopen n).mem_nhds hmem1o)
  have hK1at0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => KF1 n v) (KJet n 0 σ z a) :=
    (KvecJet_smooth n).1.contDiffAt ((isOpen_KJopen n).mem_nhds hmem0o)
  have hK2at : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => KF2 n v) (KJet n h σ z a) :=
    (KvecJet_smooth n).2.contDiffAt ((isOpen_KJopen n).mem_nhds hmem1o)
  have hK2at0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => KF2 n v) (KJet n 0 σ z a) :=
    (KvecJet_smooth n).2.contDiffAt ((isOpen_KJopen n).mem_nhds hmem0o)
  have hc1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => KF1 n (KJet n h σ z u)) a := by
    have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
        ((fun v : KJIx n → ℝ => KF1 n v) ∘ (fun u : ℝ => KJet n h σ z u)) a :=
      ContDiffAt.comp a hK1at hcd1.contDiffAt
    exact hcomp
  have hc1_0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => KF1 n (KJet n 0 σ z u)) a := by
    have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
        ((fun v : KJIx n → ℝ => KF1 n v) ∘ (fun u : ℝ => KJet n 0 σ z u)) a :=
      ContDiffAt.comp a hK1at0 hcd0.contDiffAt
    exact hcomp
  have hc2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => KF2 n (KJet n h σ z u)) a := by
    have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
        ((fun v : KJIx n → ℝ => KF2 n v) ∘ (fun u : ℝ => KJet n h σ z u)) a :=
      ContDiffAt.comp a hK2at hcd1.contDiffAt
    exact hcomp
  have hc2_0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => KF2 n (KJet n 0 σ z u)) a := by
    have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
        ((fun v : KJIx n → ℝ => KF2 n v) ∘ (fun u : ℝ => KJet n 0 σ z u)) a :=
      ContDiffAt.comp a hK2at0 hcd0.contDiffAt
    exact hcomp
  have hΦh : ContDiffAt ℝ 2 (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) a := by
    rw [contDiffAt_pi]
    intro i
    fin_cases i
    · exact (Filter.EventuallyEq.congr_contDiffWithinAt_of_mem (s := Set.univ)
        (by simpa using hid1) (Set.mem_univ a)).mpr (hc1.of_le (WithTop.coe_le_coe.mpr le_top))
    · exact (Filter.EventuallyEq.congr_contDiffWithinAt_of_mem (s := Set.univ)
        (by simpa using hid2) (Set.mem_univ a)).mpr (hc2.of_le (WithTop.coe_le_coe.mpr le_top))
  have hΦ0 : ContDiffAt ℝ 2 (fun u : ℝ => Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3)) a := by
    rw [contDiffAt_pi]
    intro i
    fin_cases i
    · exact (Filter.EventuallyEq.congr_contDiffWithinAt_of_mem (s := Set.univ)
        (by simpa using hid1') (Set.mem_univ a)).mpr (hc1_0.of_le (WithTop.coe_le_coe.mpr le_top))
    · exact (Filter.EventuallyEq.congr_contDiffWithinAt_of_mem (s := Set.univ)
        (by simpa using hid2') (Set.mem_univ a)).mpr (hc2_0.of_le (WithTop.coe_le_coe.mpr le_top))
  have hddh : deriv (deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))) a
      = fun i : Fin 2 => deriv (deriv (fun u : ℝ =>
          Kvec n h u σ (z 0) (z 1) (z 2) (z 3) i)) a := deriv_deriv_pi hΦh
  have hdd0 : deriv (deriv (fun u : ℝ => Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3))) a
      = fun i : Fin 2 => deriv (deriv (fun u : ℝ =>
          Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3) i)) a := deriv_deriv_pi hΦ0
  -- ## the final constants
  have hM0 : 0 ≤ max C1 C2 := le_trans hC1n (le_max_left _ _)
  have hMC : max C1 C2 ≤ (max C1 C2 + 1) * (B + 1) := by nlinarith [hB0, hM0]
  have hMδ : max C1 C2 * (B * δ) ≤ (max C1 C2 + 1) * (B + 1) * δ := by
    nlinarith [hB0, hM0, hδ0]
  constructor
  · have hstep : ‖deriv (deriv (fun u : ℝ =>
        Kvec n h u σ (z 0) (z 1) (z 2) (z 3))) a‖ ≤ max C1 C2 := by
      rw [hddh, pi_norm_le_iff_of_nonneg hM0]
      intro i
      rw [Real.norm_eq_abs]
      fin_cases i
      · exact le_trans hkey0 (le_max_left C1 C2)
      · exact le_trans hkey1 (le_max_right C1 C2)
    exact le_trans hstep hMC
  · rw [hddh, hdd0]
    have hstep : ‖(fun i : Fin 2 => deriv (deriv (fun u : ℝ =>
            Kvec n h u σ (z 0) (z 1) (z 2) (z 3) i)) a) -
        (fun i : Fin 2 => deriv (deriv (fun u : ℝ =>
            Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3) i)) a)‖ ≤ max C1 C2 * (B * δ) := by
      rw [show (fun i : Fin 2 => deriv (deriv (fun u : ℝ =>
              Kvec n h u σ (z 0) (z 1) (z 2) (z 3) i)) a) -
          (fun i : Fin 2 => deriv (deriv (fun u : ℝ =>
              Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3) i)) a)
          = fun i : Fin 2 => (deriv (deriv (fun u : ℝ =>
                Kvec n h u σ (z 0) (z 1) (z 2) (z 3) i)) a -
              deriv (deriv (fun u : ℝ =>
                Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3) i)) a) from rfl]
      rw [pi_norm_le_iff_of_nonneg (mul_nonneg hM0 hBδ0)]
      intro i
      rw [Real.norm_eq_abs]
      fin_cases i
      · exact le_trans hkey0d (mul_le_mul_of_nonneg_right (le_max_left C1 C2) hBδ0)
      · exact le_trans hkey1d (mul_le_mul_of_nonneg_right (le_max_right C1 C2) hBδ0)
    exact le_trans hstep hMδ

end

end Work.OddVolterra.Window

