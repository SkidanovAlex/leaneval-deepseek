import Mathlib
import Submission.Work.Drive.contDiffOn_even_comp_sqrt
import Submission.Work.Drive.exists_even_smooth_cutoff

namespace Work.Drive

open Set Filter
open scoped ContDiff Topology

/-- If `χ : ℝ × ℝ → ℝ` is `C^∞` with `tsupport χ ⊆ U` and `f : ℝ × ℝ → E` is `C^∞` on the
open set `U`, then `p ↦ χ p • f p` is `C^∞` on all of `ℝ × ℝ`.

(Smoothness is clear at a point of `tsupport χ` since there `f` is smooth, and at every point
outside `tsupport χ` the product vanishes on a neighbourhood.) -/
theorem contDiff_smul_of_contDiffOn_of_tsupport_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ × ℝ → E} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U)
    {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hsupp : tsupport χ ⊆ U) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => χ p • f p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ tsupport χ
  · exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hsupp hp)))
  · have hmem : (tsupport χ)ᶜ ∈ 𝓝 p := (isClosed_closure).compl_mem_nhds hp
    have h0 : (fun q : ℝ × ℝ => χ q • f q) =ᶠ[𝓝 p] (fun _ => (0 : E)) := by
      filter_upwards [hmem] with q hq
      have hχq : χ q = 0 := by
        rw [← Function.notMem_support]
        intro hq'
        exact hq (subset_closure hq')
      rw [hχq, zero_smul]
    exact (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq h0

/-- **Localised Whitney factorisation through the square.**

A map `f : ℝ × ℝ → E` which is `C^∞` on the rectangle `(σ₀ - δ, σ₀ + δ) × (-2δ, 2δ)` and even
in the second variable there is, on `(σ₀ - δ, σ₀ + δ) × [0, δ²]`, the germ of a `C^∞` function of
`(σ, s²)`.

The proof localises: at a point `(σ₁, 0)` of the `σ`-axis we multiply `f` by the product of a
`C^∞` bump around `σ₁` (in the first coordinate) and an even `C^∞` bump around `0` (in the second
coordinate), with support so small that the product vanishes outside the rectangle where `f` is
smooth and even.  The resulting globally smooth, globally even function `F` has the same germ as `f`
at `(σ₁, 0)`, and the global factorisation `Work.Drive.contDiffOn_even_comp_sqrt` applied to `F`
gives the germ of the descent. -/
theorem contDiffOn_even_comp_sqrt_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → E} {σ₀ δ : ℝ} (hδ : 0 < δ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f
      (Set.Ioo (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Ioo (-(2 * δ)) (2 * δ)))
    (heven : ∀ σ s : ℝ, |s| < 2 * δ → f (σ, -s) = f (σ, s)) :
    ∃ g : ℝ × ℝ → E,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g
        (Set.Ioo (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc 0 (δ ^ 2)) ∧
      ∀ σ s : ℝ, σ ∈ Set.Ioo (σ₀ - δ) (σ₀ + δ) → 0 ≤ s → s < δ → g (σ, s ^ 2) = f (σ, s) := by
  have hUopen : IsOpen (Set.Ioo (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Ioo (-(2 * δ)) (2 * δ)) :=
    isOpen_Ioo.prod isOpen_Ioo
  refine ⟨fun p => f (p.1, Real.sqrt p.2), ?_, ?_⟩
  · intro p hp
    obtain ⟨σ₁, t₁⟩ := p
    rcases lt_or_eq_of_le (Set.mem_Icc.mp hp.2).1 with hpos | hzeq
    · -- `t₁ > 0`: `(σ, t) ↦ (σ, √t)` is smooth at `(σ₁, t₁)` and lands in the rectangle
      have ht2 : t₁ ≤ δ ^ 2 := (Set.mem_Icc.mp hp.2).2
      have hsqrt_le : Real.sqrt t₁ ≤ δ := by
        have h := Real.sqrt_le_sqrt ht2
        rwa [Real.sqrt_sq (le_of_lt hδ)] at h
      have hsqrt_pos : 0 < Real.sqrt t₁ := Real.sqrt_pos.mpr hpos
      have hmemU : (σ₁, Real.sqrt t₁) ∈
          Set.Ioo (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Ioo (-(2 * δ)) (2 * δ) :=
        ⟨hp.1, by linarith, by linarith⟩
      have hf_at : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (σ₁, Real.sqrt t₁) :=
        hf.contDiffAt (hUopen.mem_nhds hmemU)
      have hΦ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : ℝ × ℝ => (q.1, Real.sqrt q.2)) (σ₁, t₁) :=
        contDiffAt_fst.prodMk ((Real.contDiffAt_sqrt hpos.ne').comp _ contDiffAt_snd)
      exact (hf_at.comp (σ₁, t₁) hΦ).contDiffWithinAt
    · -- `t₁ = 0`
      have hσ : σ₁ ∈ Set.Ioo (σ₀ - δ) (σ₀ + δ) := hp.1
      have ht1 : t₁ = 0 := hzeq.symm
      subst ht1
      -- a ball around `(σ₁, 0)` inside the rectangle
      obtain ⟨ρ', hρ'pos, hρ'sub⟩ := Metric.isOpen_iff.1 hUopen (σ₁, 0)
        ⟨hσ, by constructor <;> linarith⟩
      have hρexists : ∃ ρ : ℝ, 0 < ρ ∧ ρ < ρ' ∧ ρ < 2 * δ := by
        refine ⟨min ρ' δ / 2, ?_, ?_, ?_⟩
        · have h : 0 < min ρ' δ := lt_min hρ'pos hδ
          linarith
        · have h : min ρ' δ ≤ ρ' := min_le_left _ _
          linarith
        · have h : min ρ' δ ≤ δ := min_le_right _ _
          linarith
      obtain ⟨ρ, hρpos, hρ_lt_ρ', hρ_lt_two⟩ := hρexists
      have hclsub : Metric.closedBall ((σ₁, 0) : ℝ × ℝ) ρ ⊆
          Set.Ioo (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Ioo (-(2 * δ)) (2 * δ) := by
        intro q hq
        refine hρ'sub ?_
        have h2 : dist q ((σ₁, 0) : ℝ × ℝ) ≤ ρ := by rwa [Metric.mem_closedBall] at hq
        rw [Metric.mem_ball]
        exact lt_of_le_of_lt h2 hρ_lt_ρ'
      -- the even smooth cutoff
      obtain ⟨χ, hχcd, _hχnn, _hχle, hχ1, hχsupp, hχeven⟩ :=
        exists_even_smooth_cutoff σ₁ (Ω := Metric.ball ((σ₁, 0) : ℝ × ℝ) ρ)
          Metric.isOpen_ball (Metric.mem_ball_self hρpos)
      have hcl : tsupport χ ⊆ Metric.closedBall ((σ₁, 0) : ℝ × ℝ) ρ := by
        have h : closure (Function.support χ) ⊆ Metric.closedBall ((σ₁, 0) : ℝ × ℝ) ρ := by
          rw [← closure_ball ((σ₁, 0) : ℝ × ℝ) hρpos.ne']
          exact closure_mono hχsupp
        exact h
      have hχtsupp : tsupport χ ⊆
          Set.Ioo (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Ioo (-(2 * δ)) (2 * δ) :=
        fun q hq => hclsub (hcl hq)
      -- the global smooth even extension
      have hFcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => χ q • f q) :=
        contDiff_smul_of_contDiffOn_of_tsupport_subset hUopen hf hχcd hχtsupp
      have hFeven : ∀ σ t : ℝ, (fun q : ℝ × ℝ => χ q • f q) (σ, -t)
          = (fun q : ℝ × ℝ => χ q • f q) (σ, t) := by
        intro σ t
        show χ (σ, -t) • f (σ, -t) = χ (σ, t) • f (σ, t)
        rw [hχeven (σ, t)]
        by_cases ht : |t| < 2 * δ
        · rw [heven σ t ht]
        · have hnot : χ (σ, t) = 0 := by
            by_contra hne
            have hmem : (σ, t) ∈ Function.support χ := by rwa [Function.mem_support]
            have hball : (σ, t) ∈ Metric.ball ((σ₁, 0) : ℝ × ℝ) ρ := hχsupp hmem
            have h2 : dist t (0 : ℝ) < ρ := by
              have h := hball
              rw [Metric.mem_ball, Prod.dist_eq] at h
              simpa using lt_of_le_of_lt (le_max_right _ _) h
            have h3 : |t| < ρ := by
              rw [Real.dist_eq, sub_zero] at h2
              exact h2
            have htg : 2 * δ ≤ |t| := le_of_not_gt ht
            linarith
          simp [hnot]
      obtain ⟨gF, hgFcd, hgFval⟩ :=
        contDiffOn_even_comp_sqrt (X := ℝ) (f := fun q : ℝ × ℝ => χ q • f q) hFcd hFeven
      have hχc : χ ((σ₁, 0) : ℝ × ℝ) = 1 := hχ1.self_of_nhds
      have hval0 : gF (σ₁, 0) = f (σ₁, 0) := by
        have h := hgFval σ₁ 0 (le_refl (0 : ℝ))
        simpa [Real.sqrt_zero, hχc] using h
      -- the congruence of the two descents near `(σ₁, 0)`
      refine ContDiffWithinAt.congr_of_eventuallyEq (f := gF) ?_ ?_ ?_
      · have hmem : ((σ₁, 0) : ℝ × ℝ) ∈ (Set.univ : Set ℝ) ×ˢ Set.Ici (0 : ℝ) := by simp
        exact (hgFcd (σ₁, 0) hmem).mono (fun q hq =>
          ⟨trivial, Set.mem_Ici.mpr (Set.mem_Icc.mp hq.2).1⟩)
      · have hcont : ContinuousAt (fun q : ℝ × ℝ => (q.1, Real.sqrt q.2))
            ((σ₁, 0) : ℝ × ℝ) :=
          continuousAt_fst.prodMk (Real.continuous_sqrt.continuousAt.comp continuousAt_snd)
        have hχ1' : ∀ᶠ q : ℝ × ℝ in
            𝓝 ((fun q : ℝ × ℝ => (q.1, Real.sqrt q.2)) ((σ₁, 0) : ℝ × ℝ)), χ q = 1 := by
          simpa using hχ1
        have hev : ∀ᶠ q in 𝓝[(Set.Ioo (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc 0 (δ ^ 2))]
            ((σ₁, 0) : ℝ × ℝ), χ (q.1, Real.sqrt q.2) = 1 :=
          (hcont.tendsto.eventually hχ1').filter_mono nhdsWithin_le_nhds
        filter_upwards [self_mem_nhdsWithin, hev] with q hqS hχq
        have hq2 : 0 ≤ q.2 := (Set.mem_Icc.mp hqS.2).1
        have hv := hgFval q.1 q.2 hq2
        show f (q.1, Real.sqrt q.2) = gF (q.1, q.2)
        rw [hv]
        show f (q.1, Real.sqrt q.2) = χ (q.1, Real.sqrt q.2) • f (q.1, Real.sqrt q.2)
        rw [hχq, one_smul]
      · show f ((σ₁, 0).1, Real.sqrt (σ₁, 0).2) = gF (σ₁, 0)
        simp only [Real.sqrt_zero]
        exact hval0.symm
  · intro σ s _hs hs0 _hsδ
    show f (σ, Real.sqrt (s ^ 2)) = f (σ, s)
    rw [Real.sqrt_sq hs0]

end Work.Drive
