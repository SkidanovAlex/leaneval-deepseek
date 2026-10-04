import Mathlib
import Submission.Work.Diff.GE.covRmFixedEvolDefs
import Submission.Work.Diff.GE.continuous_flow_quantities
import Submission.Work.Diff.GE.rmP_norm_bound
import Submission.Work.Diff.GE.continuousWithinAt_rmP_zero
import Submission.Work.Diff.GE.matrix_mulVec_inv_contDiffAt
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.reconDefs
import Submission.Work.Diff.EXT.eq_sum_frameVector_of_pairing
import Submission.Work.Diff.EXT.contMDiffAt_metric_pairing
import Submission.Work.Diff.GE.koszul_pairing_jointSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE

section Scalar

lemma deriv_eq_zero_of_even {θ : ℝ → ℝ} (h : ∀ τ, θ (-τ) = θ τ)
    (hθ : DifferentiableAt ℝ θ 0) : deriv θ 0 = 0 := by
  have hneg : DifferentiableAt ℝ (fun τ : ℝ ↦ -τ) 0 := by fun_prop
  have hneg' : deriv (fun τ : ℝ ↦ -τ) (0:ℝ) = -1 := by simp [deriv_neg, deriv_id]
  have key : deriv (fun τ : ℝ ↦ θ (-τ)) 0 = deriv θ 0 * deriv (fun τ : ℝ ↦ -τ) (0:ℝ) := by
    have h := deriv_comp (0 : ℝ) (by rw [neg_zero]; exact hθ) hneg
    simpa [Function.comp_def] using h
  rw [show (fun τ : ℝ ↦ θ (-τ)) = θ from funext h] at key
  rw [hneg'] at key
  linarith

lemma tendsto_deriv_comp_sqrt {θ : ℝ → ℝ} {L : ℝ}
    (hd : HasDerivAt (deriv θ) L 0) (h0 : deriv θ 0 = 0)
    (hθ : ∀ᶠ u in 𝓝[>] (0 : ℝ), DifferentiableAt ℝ θ u) :
    Filter.Tendsto (fun s : ℝ ↦ deriv (fun s' : ℝ ↦ θ (Real.sqrt s')) s)
      (𝓝[>] (0 : ℝ)) (𝓝 (L / 2)) := by
  have hslope : Filter.Tendsto (fun u : ℝ ↦ deriv θ u / u) (nhdsWithin 0 {0}ᶜ) (𝓝 L) := by
    have h := (hasDerivAt_iff_tendsto_slope).mp hd
    refine Filter.Tendsto.congr' ?_ h
    filter_upwards with u
    rw [slope_def_field, h0, sub_zero]
    ring
  have hsqrtT : Filter.Tendsto (fun s : ℝ ↦ Real.sqrt s) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h : Filter.Tendsto (fun s : ℝ ↦ Real.sqrt s) (𝓝[>] (0:ℝ)) (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    simpa using h
  have hsqrtGT : Filter.Tendsto (fun s : ℝ ↦ Real.sqrt s) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hsqrtT, by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact Real.sqrt_pos.mpr hs⟩
  have hsqrt0 : Filter.Tendsto (fun s : ℝ ↦ Real.sqrt s) (𝓝[>] (0:ℝ))
      (nhdsWithin 0 {0}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hsqrtT, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact fun hz => absurd hz (ne_of_gt (Real.sqrt_pos.mpr hs))
  have hlim : Filter.Tendsto (fun s : ℝ ↦ deriv θ (Real.sqrt s) / Real.sqrt s)
      (𝓝[>] (0:ℝ)) (𝓝 L) := hslope.comp hsqrt0
  have h2 : Filter.Tendsto (fun s : ℝ ↦ deriv θ (Real.sqrt s) / (2 * Real.sqrt s))
      (𝓝[>] (0:ℝ)) (𝓝 (L / 2)) := by
    have h3 := hlim.const_mul (1 / 2 : ℝ)
    have h4 : (1 / 2 : ℝ) * L = L / 2 := by ring
    rw [h4] at h3
    refine h3.congr' ?_
    filter_upwards with s
    ring
  have hdiff' : ∀ᶠ s in 𝓝[>] (0:ℝ), DifferentiableAt ℝ θ (Real.sqrt s) :=
    hsqrtGT.eventually hθ
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hdiff'] with s hs hdiff
  have hsne : s ≠ 0 := ne_of_gt hs
  have hchain : HasDerivAt (fun s' : ℝ ↦ θ (Real.sqrt s'))
      (deriv θ (Real.sqrt s) * (1 / (2 * Real.sqrt s))) s := by
    have h := (hdiff.hasDerivAt).comp s (Real.hasDerivAt_sqrt hsne)
    simpa only [Function.comp_def] using h
  rw [hchain.deriv]
  ring

/-- **One-sided derivative of an even reparametrised coefficient.** -/
theorem hasDerivWithinAt_sum_sqrt {n : ℕ} {c : Fin n → ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hc : ∀ k, ContDiffAt ℝ (⊤ : ℕ∞) (c k) 0)
    (hdiff : ∀ k, ∀ u ∈ Set.Ioo 0 (Real.sqrt T), DifferentiableAt ℝ (c k) u)
    (heven : ∀ k τ, c k (-τ) = c k τ) :
    (∀ k, HasDerivWithinAt (fun s : ℝ ↦ c k (Real.sqrt s)) (deriv (deriv (c k)) 0 / 2)
        (Set.Ico 0 T) 0) ∧
    (∀ k, Filter.Tendsto (fun s : ℝ ↦ deriv (fun s' : ℝ ↦ c k (Real.sqrt s')) s)
        (𝓝[>] (0 : ℝ)) (𝓝 (deriv (deriv (c k)) 0 / 2))) := by
  have hmain : ∀ k, (HasDerivWithinAt (fun s : ℝ ↦ c k (Real.sqrt s)) (deriv (deriv (c k)) 0 / 2)
        (Set.Ico 0 T) 0) ∧
      Filter.Tendsto (fun s : ℝ ↦ deriv (fun s' : ℝ ↦ c k (Real.sqrt s')) s)
        (𝓝[>] (0 : ℝ)) (𝓝 (deriv (deriv (c k)) 0 / 2)) := by
    intro k
    have hc2 : HasDerivAt (deriv (c k)) (deriv (deriv (c k)) 0) 0 :=
      (((hc k).derivWithin (m := (⊤ : ℕ∞)) (by simp)).differentiableAt
        (by norm_num)).hasDerivAt
    have h0 : deriv (c k) 0 = 0 :=
      deriv_eq_zero_of_even (heven k) ((hc k).differentiableAt (by simp))
    have hnear : ∀ᶠ u in 𝓝[>] (0 : ℝ), DifferentiableAt ℝ (c k) u := by
      have hpos : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Set.Ioo 0 (Real.sqrt T) := by
        rw [eventually_nhdsWithin_iff]
        filter_upwards [Iio_mem_nhds (show (0:ℝ) < Real.sqrt T by positivity)] with u hu hupos
        exact ⟨hupos, hu⟩
      filter_upwards [hpos] with u hu
      exact hdiff k u hu
    have hlim : Filter.Tendsto (fun s : ℝ ↦ deriv (fun s' : ℝ ↦ c k (Real.sqrt s')) s)
        (𝓝[>] (0 : ℝ)) (𝓝 (deriv (deriv (c k)) 0 / 2)) :=
      tendsto_deriv_comp_sqrt hc2 h0 hnear
    refine ⟨?_, hlim⟩
    have hd : DifferentiableOn ℝ (fun s : ℝ ↦ c k (Real.sqrt s)) (Set.Ioo 0 T) := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      have hsqrtmem : Real.sqrt t ∈ Set.Ioo 0 (Real.sqrt T) :=
        ⟨Real.sqrt_pos.mpr ht.1, Real.sqrt_lt_sqrt ht.1.le ht.2⟩
      have h1 : DifferentiableAt ℝ (fun s : ℝ ↦ Real.sqrt s) t :=
        (Real.hasDerivAt_sqrt ht0).differentiableAt
      have h2 : DifferentiableAt ℝ (c k) (Real.sqrt t) := hdiff k (Real.sqrt t) hsqrtmem
      exact (h2.comp t h1).differentiableWithinAt
    have hcont : ContinuousWithinAt (fun s : ℝ ↦ c k (Real.sqrt s)) (Set.Ioo 0 T) 0 := by
      show Filter.Tendsto (fun s : ℝ ↦ c k (Real.sqrt s)) (nhdsWithin 0 (Set.Ioo 0 T))
        (𝓝 ((fun s : ℝ ↦ c k (Real.sqrt s)) 0))
      have hsq : Filter.Tendsto (fun s : ℝ ↦ Real.sqrt s) (nhdsWithin 0 (Set.Ioo 0 T)) (𝓝 0) := by
        have h : Filter.Tendsto (fun s : ℝ ↦ Real.sqrt s) (nhdsWithin 0 (Set.Ioo 0 T))
            (𝓝 (Real.sqrt 0)) :=
          (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
        simpa using h
      have hck : ContinuousAt (fun u : ℝ ↦ c k u) 0 := (hc k).continuousAt
      have hcomp := hck.tendsto.comp hsq
      simpa only [Function.comp_def, Real.sqrt_zero] using hcomp
    have hIoo : Set.Ioo (0:ℝ) T ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT hT
    exact (hasDerivWithinAt_Ici_of_tendsto_deriv hd hcont hIoo hlim).mono Set.Ico_subset_Ici_self
  exact ⟨fun k => (hmain k).1, fun k => (hmain k).2⟩

/-- A limit along the right filter together with the correct value at `0` gives the limit along
`[0,T)`. -/
lemma tendsto_nhdsWithin_Ico_of_tendsto_gt {α : Type*} [TopologicalSpace α] {T : ℝ}
    (hT : 0 < T) {g : ℝ → α} {a : α}
    (h : Filter.Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 a)) (h0 : g 0 = a) :
    Filter.Tendsto g (nhdsWithin 0 (Set.Ico 0 T)) (𝓝 a) := by
  rw [Filter.tendsto_def] at h ⊢
  intro s hs
  have h' : g ⁻¹' s ∈ 𝓝[>] (0:ℝ) := h s hs
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at h' ⊢
  obtain ⟨U, hU, hUs⟩ := h'
  refine ⟨U, hU, fun x hx => ?_⟩
  rcases eq_or_lt_of_le hx.2.1 with hx0 | hxpos
  · have h0s : g 0 ∈ s := by rw [h0]; exact mem_of_mem_nhds hs
    rw [← hx0]
    exact h0s
  · exact hUs ⟨hx.1, hxpos⟩

/-- `0` is a point of unique differentiability of the half-open interval `[0,T)`. -/
lemma uniqueDiffWithinAt_Ico {T : ℝ} (hT : 0 < T) : UniqueDiffWithinAt ℝ (Set.Ico 0 T) 0 := by
  have hIoo : Set.Ioo (0:ℝ) T ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT hT
  have hIco : Set.Ico (0:ℝ) T ∈ 𝓝[>] (0:ℝ) :=
    Filter.mem_of_superset hIoo (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have hle : 𝓝[>] (0:ℝ) ≤ nhdsWithin (0:ℝ) (Set.Ico 0 T) := nhdsWithin_le_iff.mpr hIco
  exact UniqueDiffWithinAt.mono_nhds (𝕜 := ℝ) (s := Set.Ioi 0) (t := Set.Ico 0 T) (x := 0)
    (uniqueDiffWithinAt_Ioi 0) hle

end Scalar

/-- **A function represented by a sum of even reparametrised coefficients has a one-sided
derivative at `0` whose value is a sum of the coefficient derivatives.** -/
theorem exists_psi_of_expansion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {V : ℝ → E} {f : Fin n → E} {c : Fin n → ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hexp : ∀ s ∈ Set.Ico 0 T, V s = ∑ k, c k (Real.sqrt s) • f k)
    (hc : ∀ k, ContDiffAt ℝ (⊤ : ℕ∞) (c k) 0)
    (hdiff : ∀ k, ∀ u ∈ Set.Ioo 0 (Real.sqrt T), DifferentiableAt ℝ (c k) u)
    (heven : ∀ k τ, c k (-τ) = c k τ) :
    ∃ ψ : Fin n → ℝ → ℝ,
      (∀ k, ContinuousWithinAt (ψ k) (Set.Ico 0 T) 0) ∧
      (∀ s ∈ Set.Ico 0 T, derivWithin V (Set.Ico 0 T) s = ∑ k, ψ k s • f k) := by
  have huniq : UniqueDiffWithinAt ℝ (Set.Ico 0 T) 0 := uniqueDiffWithinAt_Ico hT
  have hmain := hasDerivWithinAt_sum_sqrt hT hc hdiff heven
  let ψ : Fin n → ℝ → ℝ := fun k => derivWithin (fun s' : ℝ ↦ c k (Real.sqrt s')) (Set.Ico 0 T)
  have hval : ∀ k, ψ k 0 = deriv (deriv (c k)) 0 / 2 := fun k => (hmain.1 k).derivWithin huniq
  have hsumfun : (fun s' : ℝ ↦ ∑ k : Fin n, c k (Real.sqrt s') • f k)
      = ∑ k : Fin n, (fun s' : ℝ ↦ c k (Real.sqrt s') • f k) := by
    funext y
    simp only [Finset.sum_apply]
  refine ⟨ψ, ?_, ?_⟩
  · intro k
    have hev : (ψ k) =ᶠ[𝓝[>] (0:ℝ)]
        (fun s : ℝ ↦ deriv (fun s' : ℝ ↦ c k (Real.sqrt s')) s) := by
      filter_upwards [Ioo_mem_nhdsGT hT] with s hs
      exact derivWithin_of_mem_nhds (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs)
        Set.Ioo_subset_Ico_self)
    have hlim : Filter.Tendsto (ψ k) (𝓝[>] (0:ℝ)) (𝓝 (deriv (deriv (c k)) 0 / 2)) :=
      (hmain.2 k).congr' hev.symm
    have h2 := tendsto_nhdsWithin_Ico_of_tendsto_gt hT hlim (hval k)
    show ContinuousWithinAt (ψ k) (Set.Ico 0 T) 0
    rw [ContinuousWithinAt, hval k]
    exact h2
  · intro s hs
    rcases eq_or_lt_of_le hs.1 with hs0 | hspos
    · subst hs0
      have hsum : HasDerivWithinAt (∑ k : Fin n, (fun s' : ℝ ↦ c k (Real.sqrt s') • f k))
          (∑ k : Fin n, ψ k 0 • f k) (Set.Ico 0 T) 0 := by
        have hA : ∀ k ∈ (Finset.univ : Finset (Fin n)),
            HasDerivWithinAt (fun s' : ℝ ↦ c k (Real.sqrt s') • f k) (ψ k 0 • f k)
              (Set.Ico 0 T) 0 := by
          intro k _
          have h1 : HasDerivWithinAt (fun s' : ℝ ↦ c k (Real.sqrt s')) (ψ k 0)
              (Set.Ico 0 T) 0 := by
            rw [hval k]
            exact hmain.1 k
          exact h1.smul_const (f k)
        have h := HasDerivWithinAt.sum (u := Finset.univ) (s := Set.Ico 0 T) (x := (0:ℝ))
          (A := fun k s' => c k (Real.sqrt s') • f k) (A' := fun k => ψ k 0 • f k) hA
        simpa using h
      have hcongr : derivWithin V (Set.Ico 0 T) 0
          = derivWithin (∑ k : Fin n, (fun s' : ℝ ↦ c k (Real.sqrt s') • f k))
              (Set.Ico 0 T) 0 := by
        refine derivWithin_congr (fun x hx => ?_)
          (show V 0 = (∑ k : Fin n, (fun s' : ℝ ↦ c k (Real.sqrt s') • f k)) 0 from ?_)
        · rw [Finset.sum_apply, ← hexp x hx]
        · rw [Finset.sum_apply, ← hexp 0 ⟨le_refl 0, hT⟩]
      rw [hcongr]
      exact hsum.derivWithin huniq
    · have hu : (0:ℝ) < s := hspos
      have hsT : s < T := hs.2
      have hmem_nhds : Set.Ico (0:ℝ) T ∈ 𝓝 s :=
        Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨hu, hsT⟩) Set.Ioo_subset_Ico_self
      have hsum : HasDerivWithinAt (∑ k : Fin n, (fun s' : ℝ ↦ c k (Real.sqrt s') • f k))
          (∑ k : Fin n, ψ k s • f k) (Set.Ico 0 T) s := by
        have hA : ∀ k ∈ (Finset.univ : Finset (Fin n)),
            HasDerivWithinAt (fun s' : ℝ ↦ c k (Real.sqrt s') • f k) (ψ k s • f k)
              (Set.Ico 0 T) s := by
          intro k _
          have hmem : Real.sqrt s ∈ Set.Ioo 0 (Real.sqrt T) :=
            ⟨Real.sqrt_pos.mpr hu, Real.sqrt_lt_sqrt hu.le hsT⟩
          have hderiv : HasDerivAt (fun s' : ℝ ↦ c k (Real.sqrt s'))
              (deriv (fun s' : ℝ ↦ c k (Real.sqrt s')) s) s := by
            have h1 : HasDerivAt (fun s' : ℝ ↦ Real.sqrt s')
                (1 / (2 * Real.sqrt s)) s := Real.hasDerivAt_sqrt (ne_of_gt hu)
            have h2 : HasDerivAt (c k) (deriv (c k) (Real.sqrt s)) (Real.sqrt s) :=
              (hdiff k (Real.sqrt s) hmem).hasDerivAt
            have h := h2.comp s h1
            have hcomp : deriv (fun s' : ℝ ↦ c k (Real.sqrt s')) s
                = deriv (c k) (Real.sqrt s) * (1 / (2 * Real.sqrt s)) := by
              have hdc := deriv_comp s h2.differentiableAt h1.differentiableAt
              rw [(Real.hasDerivAt_sqrt (ne_of_gt hu)).deriv] at hdc
              simpa [Function.comp_def] using hdc
            rw [hcomp]
            simpa [Function.comp_def] using h
          have hdw : HasDerivWithinAt (fun s' : ℝ ↦ c k (Real.sqrt s'))
              (derivWithin (fun s' : ℝ ↦ c k (Real.sqrt s')) (Set.Ico 0 T) s)
              (Set.Ico 0 T) s := by
            rw [derivWithin_of_mem_nhds hmem_nhds]
            exact hderiv.hasDerivWithinAt
          exact hdw.smul_const (f k)
        have h := HasDerivWithinAt.sum (u := Finset.univ) (s := Set.Ico 0 T) (x := s)
          (A := fun k s' => c k (Real.sqrt s') • f k) (A' := fun k => ψ k s • f k) hA
        simpa using h
      have hcongr : derivWithin V (Set.Ico 0 T) s
          = derivWithin (∑ k : Fin n, (fun s' : ℝ ↦ c k (Real.sqrt s') • f k))
              (Set.Ico 0 T) s := by
        refine derivWithin_congr (fun x hx => ?_)
          (show V s = (∑ k : Fin n, (fun s' : ℝ ↦ c k (Real.sqrt s') • f k)) s from ?_)
        · rw [Finset.sum_apply, ← hexp x hx]
        · rw [Finset.sum_apply, ← hexp s ⟨hs.1, hs.2⟩]
      rw [hcongr]
      refine hsum.derivWithin ?_
      exact UniqueDiffWithinAt.mono (uniqueDiffWithinAt_Ioo ⟨hu, hsT⟩) Set.Ioo_subset_Ico_self

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]

section Transfer

/-- **Transfer of continuity at the initial time.**  A quantity which is continuous at `0` along the
time-reparametrised family `τ ↦ G (τ²)` is continuous within `[0,T)` at `0` along the flow. -/
lemma continuousWithinAt_zero_of_continuousAt_sqFlow {α : Type*} [TopologicalSpace α]
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hT : 0 < T)
    {Q : Submission.Diff.SMet I M → α}
    (hQ : ContinuousAt (fun τ : ℝ ↦ Q (cfq_sqFlow G τ)) 0) :
    ContinuousWithinAt (fun s : ℝ ↦ Q (G s)) (Set.Ico 0 T) 0 := by
  refine cfq_continuousWithinAt_of_continuousAt_comp_sq hT hQ ?_
  intro s hs
  show Q (G s) = Q (cfq_sqFlow G (Real.sqrt s))
  have h : cfq_sqFlow G (Real.sqrt s) = G s := by
    show G ((Real.sqrt s) ^ 2) = G s
    rw [Real.sq_sqrt hs.1]
  rw [h]

end Transfer

section Flow

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]

/-- The time reparametrisation `t = τ²` turns `[0,T)` into the *full* open interval
`(-√T, √T)`.  This is `cfq_jointSmooth_sqFlow` with the optimal radius `ρ = √T` (the proof only
needs `τ² < T` for `|τ| < ρ`, which holds for `ρ = √T`). -/
lemma jointSmooth_sqFlow_sqrt {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hT : 0 < T)
    (h : Submission.Diff.JointSmooth G (Set.Ico 0 T)) :
    Submission.Diff.JointSmooth (cfq_sqFlow G) (Set.Ioo (-(Real.sqrt T)) (Real.sqrt T)) := by
  unfold Submission.Diff.JointSmooth
  have hsq : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M => (p.1) ^ 2) (Set.Ioo (-(Real.sqrt T)) (Real.sqrt T) ×ˢ (univ : Set M)) := by
    have h1 : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M => p.1)
        (Set.Ioo (-(Real.sqrt T)) (Real.sqrt T) ×ˢ (univ : Set M)) := contMDiffOn_fst
    simpa using h1.pow 2
  have hΛ : ContMDiffOn (𝓘(ℝ,ℝ).prod I) ((𝓘(ℝ,ℝ)).prod I) ∞
      (fun p : ℝ × M => (p.1 ^ 2, p.2))
      (Set.Ioo (-(Real.sqrt T)) (Real.sqrt T) ×ˢ (univ : Set M)) :=
    hsq.prodMk contMDiffOn_snd
  have hsub : (Set.Ioo (-(Real.sqrt T)) (Real.sqrt T) ×ˢ (univ : Set M))
      ⊆ (fun p : ℝ × M => (p.1 ^ 2, p.2)) ⁻¹' (Set.Ico 0 T ×ˢ (univ : Set M)) := by
    intro p hp
    obtain ⟨hp1, -⟩ := hp
    obtain ⟨hlo, hhi⟩ := hp1
    refine ⟨⟨?_, ?_⟩, trivial⟩
    · exact sq_nonneg p.1
    · show p.1 ^ 2 < T
      rw [← Real.sq_sqrt hT.le]
      exact sq_lt_sq' hlo hhi
  exact (ContMDiffOn.comp h hΛ hsub).congr (fun p _ => rfl)

end Flow

section JointField

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]

/-- A constant family of globally smooth tangent fields is jointly smooth. -/
lemma jointField_const' {X : Π y : M, TangentSpace I y}
    (hX : Work.Diff.GE.SmoothField (I := I) (M := M) X) :
    Work.Diff.EXT.JointField (I := I) (M := M) (fun _ : ℝ => X) (Set.univ : Set (ℝ × M)) :=
  hX.contMDiffOn.comp (t := univ)
    (contMDiffOn_snd (I := 𝓘(ℝ, ℝ)) (J := I) (M := ℝ) (N := M)) (fun y _ => trivial)

end JointField

section Koszul

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  [I.Boundaryless] [T2Space M]

/-- **The Koszul pairing of a jointly smooth family of metrics, along fixed smooth fields, is
smooth in the parameter.** -/
lemma koszul_pairing_contDiffAt {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    (A X Z : Π y : M, TangentSpace I y)
    (hA : Work.Diff.GE.SmoothField (I := I) (M := M) A)
    (hX : Work.Diff.GE.SmoothField (I := I) (M := M) X)
    (hZ : Work.Diff.GE.SmoothField (I := I) (M := M) Z) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun τ : ℝ ↦ (G τ).inner x
        (Submission.Diff.lcOf (G τ) A x (X x)) (Z x)) t₀ := by
  have hpair := koszul_pairing_jointSmooth (I := I) (M := M) (G := G)
    (V := J ×ˢ (univ : Set M)) (hJ.prod isOpen_univ)
    (by exact hG)
    (σ := fun _ : ℝ => A) (X := fun _ : ℝ => X) (Z := fun _ : ℝ => Z)
    ((jointField_const' (I := I) (M := M) hA).mono (Set.subset_univ _))
    ((jointField_const' (I := I) (M := M) hX).mono (Set.subset_univ _))
    ((jointField_const' (I := I) (M := M) hZ).mono (Set.subset_univ _))
  have hmem : J ×ˢ (univ : Set M) ∈ 𝓝 (t₀, x) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (hJ.mem_nhds ht₀) Filter.univ_mem
  have h1 : ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) (𝓘(ℝ,ℝ)) (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ (G p.1).inner p.2
        (Submission.Diff.lcOf (G p.1) A p.2 (X p.2)) (Z p.2)) (t₀, x) :=
    hpair.contMDiffAt hmem
  have h2 := h1.comp (t₀) (contMDiffAt_id.prodMk contMDiffAt_const)
  have h3 : ContMDiffAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℝ)) (⊤ : ℕ∞)
      (fun τ : ℝ ↦ (G τ).inner x
        (Submission.Diff.lcOf (G τ) A x (X x)) (Z x)) t₀ := by
    simpa only [Function.comp_def, Prod.mk.eta, id_eq] using h2
  exact h3.contDiffAt

end Koszul

section Coeff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  [I.Boundaryless] [T2Space M]

/-- The Gram matrix of the coordinate frame at `x` is smooth in the parameter. -/
lemma gramM_contDiffAt {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun τ : ℝ ↦ Work.Diff.EXT.gramM (I := I) (G τ) x x i j) t₀ := by
  have hfr : ∀ k : Fin (Module.finrank ℝ E),
      Work.Diff.EXT.SmoothFieldAt I M (Work.Diff.EXT.fr (I := I) x k) x := fun k =>
    Work.Diff.EXT.contMDiffAt_frameVector (I := I) x (Module.finBasis ℝ E k)
      (mem_chart_source H x)
  have hpair := Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) hJ hG ht₀
    (hfr i) (hfr j)
  have hcomp := hpair.comp (t₀) (contMDiffAt_id.prodMk contMDiffAt_const)
  have hcompF : ContMDiffAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℝ)) ∞
      (fun τ : ℝ ↦ (G τ).inner x (Work.Diff.EXT.fr (I := I) x i x)
        (Work.Diff.EXT.fr (I := I) x j x)) t₀ := by
    simpa only [Function.comp_def, Prod.mk.eta, id_eq] using hcomp
  have hcompL : ContMDiffAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℝ)) (⊤ : ℕ∞)
      (fun τ : ℝ ↦ (G τ).inner x (Work.Diff.EXT.fr (I := I) x i x)
        (Work.Diff.EXT.fr (I := I) x j x)) t₀ := hcompF
  have hcont : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun τ : ℝ ↦ (G τ).inner x (Work.Diff.EXT.fr (I := I) x i x)
        (Work.Diff.EXT.fr (I := I) x j x)) t₀ := hcompL.contDiffAt
  simpa only [Work.Diff.EXT.gramM, Matrix.of_apply] using hcont

/-- **The coefficients of the connection variation in the coordinate frame are smooth.** -/
lemma coeff_contDiffAt {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    (a v : TangentSpace I x) (k : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun τ : ℝ ↦ (Matrix.mulVec (Work.Diff.EXT.gramM (I := I) (G τ) x x)⁻¹
        (fun i ↦ (G τ).inner x
          (Submission.Diff.lcOf (G τ) (Submission.Diff.smoothExt x a) x v)
          (Work.Diff.GE.cFrame (I := I) x i x))) k) t₀ := by
  refine matrix_mulVec_inv_contDiffAt (Γ := fun τ ↦ Work.Diff.EXT.gramM (I := I) (G τ) x x)
    (p := fun τ i ↦ (G τ).inner x
      (Submission.Diff.lcOf (G τ) (Submission.Diff.smoothExt x a) x v)
      (Work.Diff.GE.cFrame (I := I) x i x)) ?_ ?_ ?_ k
  · intro i j
    exact gramM_contDiffAt (I := I) (M := M) hJ hG ht₀ x i j
  · exact Work.Diff.EXT.gramM_det_ne_zero (I := I) (G t₀) x
  · intro i
    have h := koszul_pairing_contDiffAt (I := I) (M := M) hJ hG ht₀ x
      (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x v)
      (Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x i x))
      (Work.Diff.GE.Gest.smoothExt_contMDiff x a)
      (Work.Diff.GE.Gest.smoothExt_contMDiff x v)
      (Work.Diff.GE.Gest.smoothExt_contMDiff x (Work.Diff.GE.cFrame (I := I) x i x))
    simpa only [Work.Diff.GE.smoothExt_apply] using h

end Coeff

section Crux

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  [I.Boundaryless] [T2Space M]

/-- The expansion of the connection variation in the coordinate frame, and the smoothness of its
coefficients. -/
lemma connVar_psi (hLC : Submission.Diff.LCSmooth I M) {G : ℝ → Submission.Diff.SMet I M}
    {T : ℝ} (hT : 0 < T) (hflow : Submission.Diff.IsRicciFlow G T) (x : M)
    (a v : TangentSpace I x) :
    ∃ ψ : Fin (Module.finrank ℝ E) → ℝ → ℝ,
      (∀ k, ContinuousWithinAt (ψ k) (Set.Ico 0 T) 0) ∧
      (∀ s ∈ Set.Ico 0 T,
        ((derivWithin (connVar G x a v) (Set.Ico 0 T) s : E) : TangentSpace I x)
          = ∑ k, ψ k s • Work.Diff.GE.cFrame (I := I) x k x) := by
  classical
  set ρ : ℝ := Real.sqrt T with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; exact Real.sqrt_pos.mpr hT
  have hJsm : Submission.Diff.JointSmooth (cfq_sqFlow G) (Set.Ioo (-ρ) ρ) := by
    rw [hρdef]
    exact jointSmooth_sqFlow_sqrt (I := I) (M := M) hT hflow.1
  -- the coefficient functions
  set c : Fin (Module.finrank ℝ E) → ℝ → ℝ := fun k τ ↦
    (Matrix.mulVec (Work.Diff.EXT.gramM (I := I) (cfq_sqFlow G τ) x x)⁻¹
      (fun i ↦ (cfq_sqFlow G τ).inner x
        (Submission.Diff.lcOf (cfq_sqFlow G τ) (Submission.Diff.smoothExt x a) x v)
        (Work.Diff.GE.cFrame (I := I) x i x))) k with hcdef
  have hc : ∀ k, ContDiffAt ℝ (⊤ : ℕ∞) (c k) 0 := by
    intro k
    have h0mem : (0:ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
    exact coeff_contDiffAt (I := I) (M := M) isOpen_Ioo hJsm h0mem x a v k
  have hdiff : ∀ k, ∀ u ∈ Set.Ioo 0 (Real.sqrt T), DifferentiableAt ℝ (c k) u := by
    intro k u hu
    have humem : u ∈ Set.Ioo (-ρ) ρ := by
      refine ⟨by linarith [hu.1], ?_⟩
      rw [hρdef]; exact hu.2
    exact (coeff_contDiffAt (I := I) (M := M) isOpen_Ioo hJsm humem x a v k).differentiableAt
      (by norm_num)
  have heven : ∀ k τ, c k (-τ) = c k τ := by
    intro k τ
    have hsq : cfq_sqFlow G (-τ) = cfq_sqFlow G τ := by
      show G ((-τ) ^ 2) = G (τ ^ 2)
      rw [neg_sq]
    simp only [hcdef, hsq]
  -- the expansion
  have hexp : ∀ s ∈ Set.Ico 0 T,
      connVar G x a v s = ∑ k, c k (Real.sqrt s) • Work.Diff.GE.cFrame (I := I) x k x := by
    intro s hs
    have hsρ : Real.sqrt s ∈ Set.Ioo (-ρ) ρ := by
      refine ⟨by linarith [Real.sqrt_nonneg s], ?_⟩
      rw [hρdef]
      exact Real.sqrt_lt_sqrt hs.1 hs.2
    have hfun : cfq_sqFlow G (Real.sqrt s) = G s := by
      show G ((Real.sqrt s) ^ 2) = G s
      rw [Real.sq_sqrt hs.1]
    have h := Work.Diff.EXT.eq_sum_frameVector_of_pairing (I := I)
      (g := cfq_sqFlow G (Real.sqrt s)) (x₀ := x) (p := x) (mem_chart_source H x)
      ((Submission.Diff.lcOf (cfq_sqFlow G (Real.sqrt s)) (Submission.Diff.smoothExt x a) x v
        : TangentSpace I x))
    have h' := h
    simp only [hfun, Work.Diff.EXT.gramM, Matrix.of_apply] at h'
    simp only [hcdef, hfun, Work.Diff.EXT.gramM, Matrix.of_apply, Work.Diff.EXT.fr,
      Work.Diff.GE.cFrame, Work.Diff.GE.cBasis, Submission.Geodesic.frameSection,
      Submission.Geodesic.frameVector, connVar]
    exact h'
  exact exists_psi_of_expansion (V := connVar G x a v)
    (f := fun k => (Work.Diff.GE.cFrame (I := I) x k x : TangentSpace I x))
    hT hexp hc hdiff heven

end Crux

section RmPSum

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

/-- `rmP4` is linear in the slot that is being updated, along a finite linear combination. -/
lemma rmP4_update_sum (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (p : Fin 4 → TangentSpace I x) (j : Fin 4) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (u : ι → TangentSpace I x) :
    rmP4 g x (Function.update p j (∑ i ∈ s, c i • u i))
      = ∑ i ∈ s, c i * rmP4 g x (Function.update p j (u i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h2 := rmP4_update_smul hLC g x p j (0 : ℝ) (0 : TangentSpace I x)
      simpa [Finset.sum_empty] using h2
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      rw [rmP4_update_add hLC g x p j (c i • u i) (∑ x_1 ∈ s, c x_1 • u x_1),
        rmP4_update_smul hLC g x p j (c i) (u i), ih]

end RmPSum

section ConnDeriv

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

/-- The frozen `rmP4` term is continuous at `0` within `[0,T)`. -/
lemma continuousWithinAt_rmP4_zero {G : ℝ → Submission.Diff.SMet I M} {T : ℝ}
    (hLC : Submission.Diff.LCSmooth I M) (hflow : Submission.Diff.IsRicciFlow G T)
    (x : M) (q : Fin 4 → TangentSpace I x) :
    ContinuousWithinAt (fun s : ℝ ↦ rmP4 (G s) x q) (Set.Ico 0 T) 0 := by
  have hz := continuousWithinAt_rmP_zero (I := I) (M := M) hLC hflow x
    (q 0) (q 1) (q 2) (q 3)
  simpa only [rmP4] using hz

/-- The `j`-th slot of `Rm` with the *time derivative* of the connection variation in it is
continuous at `0` within `[0,T)`. -/
lemma continuousWithinAt_rmP4_connVarDeriv {G : ℝ → Submission.Diff.SMet I M} {T : ℝ}
    (hT : 0 < T) (hflow : Submission.Diff.IsRicciFlow G T)
    (hLC : Submission.Diff.LCSmooth I M) (x : M) (v : TangentSpace I x)
    (j : Fin 4) (p : Fin 4 → TangentSpace I x) :
    ContinuousWithinAt (fun s : ℝ ↦ rmP4 (G s) x (Function.update p j
      (((derivWithin (connVar G x (p j) v) (Set.Ico 0 T) s : E) : TangentSpace I x))))
      (Set.Ico 0 T) 0 := by
  classical
  obtain ⟨ψ, hψ, hexp⟩ := connVar_psi hLC hT hflow x (p j) v
  have hsum : ContinuousWithinAt (fun s : ℝ ↦
      ∑ k, ψ k s * rmP4 (G s) x (Function.update p j (Work.Diff.GE.cFrame (I := I) x k x)))
      (Set.Ico 0 T) 0 := by
    show Filter.Tendsto (fun s : ℝ ↦
      ∑ k, ψ k s * rmP4 (G s) x (Function.update p j (Work.Diff.GE.cFrame (I := I) x k x)))
      (nhdsWithin 0 (Set.Ico 0 T))
      (𝓝 (∑ k, ψ k 0 * rmP4 (G 0) x (Function.update p j (Work.Diff.GE.cFrame (I := I) x k x))))
    refine tendsto_finset_sum Finset.univ (fun k _ => ?_)
    exact (hψ k).mul (continuousWithinAt_rmP4_zero hLC hflow x
      (Function.update p j (Work.Diff.GE.cFrame (I := I) x k x)))
  refine hsum.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have h1 : ((derivWithin (connVar G x (p j) v) (Set.Ico 0 T) s : E) : TangentSpace I x)
        = ∑ k, ψ k s • Work.Diff.GE.cFrame (I := I) x k x := hexp s hs
    have h2 := congrArg (Function.update p j) h1
    show rmP4 (G s) x (Function.update p j
        (((derivWithin (connVar G x (p j) v) (Set.Ico 0 T) s : E) : TangentSpace I x)))
      = ∑ k, ψ k s * rmP4 (G s) x (Function.update p j (Work.Diff.GE.cFrame (I := I) x k x))
    rw [h2]
    exact rmP4_update_sum hLC (G s) x p j Finset.univ (fun k => ψ k s)
      (fun k => Work.Diff.GE.cFrame (I := I) x k x)
  · have h1 : ((derivWithin (connVar G x (p j) v) (Set.Ico 0 T) 0 : E) : TangentSpace I x)
        = ∑ k, ψ k 0 • Work.Diff.GE.cFrame (I := I) x k x := hexp 0 ⟨le_refl 0, hT⟩
    have h2 := congrArg (Function.update p j) h1
    show rmP4 (G 0) x (Function.update p j
        (((derivWithin (connVar G x (p j) v) (Set.Ico 0 T) 0 : E) : TangentSpace I x)))
      = ∑ k, ψ k 0 * rmP4 (G 0) x (Function.update p j (Work.Diff.GE.cFrame (I := I) x k x))
    rw [h2]
    exact rmP4_update_sum hLC (G 0) x p j Finset.univ (fun k => ψ k 0)
      (fun k => Work.Diff.GE.cFrame (I := I) x k x)

end ConnDeriv

theorem covRm_fixed_evol_cont
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (F : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E) →
        Submission.Diff.Alg.Curv4 (Module.finrank ℝ E))
    (hFd : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFeq : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ, ∀ R,
      F (Submission.Diff.Alg.rot A R) = Submission.Diff.Alg.rot A (F R))
    (hCont : ∀ (G : ℝ → Submission.Diff.SMet I M) (J : Set ℝ), IsOpen J →
      Submission.Diff.JointSmooth G J →
      ∀ t ∈ J, ∀ x : M, ∀ v a b c d : TangentSpace I x,
      ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ ↦ Submission.Diff.covRm (G s) x v a b c d) t ∧
      ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ ↦ Work.Diff.GE.covLapRmAt (G s) x v a b c d) t ∧
      ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ ↦ Work.Diff.GE.lapCovRmAt (G s) x v a b c d) t ∧
      ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ ↦ Submission.Diff.rmNormSq (G s) x) t ∧
      ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ ↦ Submission.Diff.dRmNormSq (G s) x) t ∧
      (∀ A : Π y : M, TangentSpace I y, Work.Diff.GE.SmoothField (I := I) (M := M) A →
        ∃ d : ℝ → E,
          (∀ s ∈ J, HasDerivAt
            (fun σ : ℝ ↦ ((Submission.Diff.lcOf (G σ) A x v : TangentSpace I x) : E)) (d s) s) ∧
          ContinuousAt d t) ∧
      (∀ (F : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E) →
          Submission.Diff.Alg.Curv4 (Module.finrank ℝ E)),
        ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ, ∀ R,
          F (Submission.Diff.Alg.rot A R) = Submission.Diff.Alg.rot A (F R)) →
        ContDiffAt ℝ (⊤ : ℕ∞)
          (fun s : ℝ ↦ Work.Diff.GE.covReactionFormAt F (G s) x v a b c d) t)) :
    (∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
      ∀ x : M, ∀ v a b c d : TangentSpace I x,
      ContinuousWithinAt (fun s : ℝ ↦ Submission.Diff.covRm (G s) x v a b c d) (Set.Ico 0 T) 0) ∧
    (∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
      ∀ x : M, ∀ v a b c d : TangentSpace I x,
      ContinuousWithinAt (fun s : ℝ ↦ Work.Diff.GE.covRmTimeDerivWithin F G T s x v a b c d)
        (Set.Ico 0 T) 0) ∧
    (∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
      ∀ x : M, ∀ v a b c d : TangentSpace I x,
      ContinuousWithinAt (fun s : ℝ ↦ Work.Diff.GE.lapCovRmAt (G s) x v a b c d) (Set.Ico 0 T) 0 ∧
      ContinuousWithinAt (fun s : ℝ ↦ Submission.Diff.rmNormSq (G s) x) (Set.Ico 0 T) 0 ∧
      ContinuousWithinAt (fun s : ℝ ↦ Submission.Diff.dRmNormSq (G s) x) (Set.Ico 0 T) 0) := by
  have key : ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
      ((∀ x v a b c d, ContinuousWithinAt
          (fun s : ℝ ↦ Submission.Diff.covRm (G s) x v a b c d) (Set.Ico 0 T) 0) ∧
       (∀ x v a b c d, ContinuousWithinAt
          (fun s : ℝ ↦ Work.Diff.GE.covRmTimeDerivWithin F G T s x v a b c d) (Set.Ico 0 T) 0) ∧
       (∀ x v a b c d, ContinuousWithinAt
          (fun s : ℝ ↦ Work.Diff.GE.lapCovRmAt (G s) x v a b c d) (Set.Ico 0 T) 0 ∧
        ContinuousWithinAt (fun s : ℝ ↦ Submission.Diff.rmNormSq (G s) x) (Set.Ico 0 T) 0 ∧
        ContinuousWithinAt (fun s : ℝ ↦ Submission.Diff.dRmNormSq (G s) x) (Set.Ico 0 T) 0)) := by
    intro G T hflow
    by_cases hT : T ≤ 0
    · have hempty : Set.Ico (0 : ℝ) T = ∅ := Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)
      refine ⟨?_, ?_, ?_⟩ <;> intro x v a b c d <;>
        · rw [hempty]
          simp [ContinuousWithinAt, nhdsWithin_empty]
    · have hTpos : 0 < T := not_le.mp hT
      set ρ : ℝ := Real.sqrt T / 2 with hρdef
      have hρ : 0 < ρ := by positivity
      have hρT : ρ ^ 2 < T := by
        rw [hρdef, div_pow, Real.sq_sqrt hTpos.le]; nlinarith
      have hJsm : Submission.Diff.JointSmooth (cfq_sqFlow G) (Set.Ioo (-ρ) ρ) :=
        cfq_jointSmooth_sqFlow (I := I) (M := M) G hTpos hρ hρT hflow.1
      have h0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
      have hC := hCont (cfq_sqFlow G) (Set.Ioo (-ρ) ρ) isOpen_Ioo hJsm 0 h0
      refine ⟨?_, ?_, ?_⟩
      · intro x v a b c d
        exact continuousWithinAt_zero_of_continuousAt_sqFlow (G := G) (T := T) hTpos
          (Q := fun g => Submission.Diff.covRm g x v a b c d) ((hC x v a b c d).1.continuousAt)
      · intro x v a b c d
        have hA : ContinuousWithinAt
            (fun s : ℝ ↦ Work.Diff.GE.covLapRmAt (G s) x v a b c d) (Set.Ico 0 T) 0 :=
          continuousWithinAt_zero_of_continuousAt_sqFlow (G := G) (T := T) hTpos
            (Q := fun g => Work.Diff.GE.covLapRmAt g x v a b c d)
            ((hC x v a b c d).2.1.continuousAt)
        have hB : ContinuousWithinAt
            (fun s : ℝ ↦ Work.Diff.GE.covReactionFormAt F (G s) x v a b c d) (Set.Ico 0 T) 0 :=
          continuousWithinAt_zero_of_continuousAt_sqFlow (G := G) (T := T) hTpos
            (Q := fun g => Work.Diff.GE.covReactionFormAt F g x v a b c d)
            (((hC x v a b c d).2.2.2.2.2.2 F hFd hFeq).continuousAt)
        have hq0 := continuousWithinAt_rmP4_connVarDeriv (G := G) (T := T) hTpos hflow hLC x v
          (0 : Fin 4) ![a, b, c, d]
        have hq1 := continuousWithinAt_rmP4_connVarDeriv (G := G) (T := T) hTpos hflow hLC x v
          (1 : Fin 4) ![a, b, c, d]
        have hq2 := continuousWithinAt_rmP4_connVarDeriv (G := G) (T := T) hTpos hflow hLC x v
          (2 : Fin 4) ![a, b, c, d]
        have hq3 := continuousWithinAt_rmP4_connVarDeriv (G := G) (T := T) hTpos hflow hLC x v
          (3 : Fin 4) ![a, b, c, d]
        have hv0 : ∀ w : TangentSpace I x,
            Function.update ![a, b, c, d] (0 : Fin 4) w = ![w, b, c, d] := by
          intro w
          funext i
          fin_cases i <;> simp [Function.update_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons]
        have hv1 : ∀ w : TangentSpace I x,
            Function.update ![a, b, c, d] (1 : Fin 4) w = ![a, w, c, d] := by
          intro w
          funext i
          fin_cases i <;> simp [Function.update_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons]
        have hv2 : ∀ w : TangentSpace I x,
            Function.update ![a, b, c, d] (2 : Fin 4) w = ![a, b, w, d] := by
          intro w
          funext i
          fin_cases i <;> simp [Function.update_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons]
        have hv3 : ∀ w : TangentSpace I x,
            Function.update ![a, b, c, d] (3 : Fin 4) w = ![a, b, c, w] := by
          intro w
          funext i
          fin_cases i <;> simp [Function.update_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons]
        have hq0' : ContinuousWithinAt (fun s : ℝ ↦ Submission.Diff.rmP (G s) x
              (((derivWithin (connVar G x a v) (Set.Ico 0 T) s : E) : TangentSpace I x)) b c d)
            (Set.Ico 0 T) 0 := by
          simp only [rmP4, hv0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hq0
          exact hq0
        have hq1' : ContinuousWithinAt (fun s : ℝ ↦ Submission.Diff.rmP (G s) x a
              (((derivWithin (connVar G x b v) (Set.Ico 0 T) s : E) : TangentSpace I x)) c d)
            (Set.Ico 0 T) 0 := by
          simp only [rmP4, hv1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hq1
          exact hq1
        have hq2' : ContinuousWithinAt (fun s : ℝ ↦ Submission.Diff.rmP (G s) x a b
              (((derivWithin (connVar G x c v) (Set.Ico 0 T) s : E) : TangentSpace I x)) d)
            (Set.Ico 0 T) 0 := by
          simp only [rmP4, hv2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hq2
          exact hq2
        have hq3' : ContinuousWithinAt (fun s : ℝ ↦ Submission.Diff.rmP (G s) x a b c
              (((derivWithin (connVar G x d v) (Set.Ico 0 T) s : E) : TangentSpace I x)))
            (Set.Ico 0 T) 0 := by
          simp only [rmP4, hv3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hq3
          exact hq3
        have hmain : ContinuousWithinAt (fun s : ℝ ↦ Work.Diff.GE.covLapRmAt (G s) x v a b c d
            + Work.Diff.GE.covReactionFormAt F (G s) x v a b c d
            - Submission.Diff.rmP (G s) x
                (((derivWithin (connVar G x a v) (Set.Ico 0 T) s : E) : TangentSpace I x)) b c d
            - Submission.Diff.rmP (G s) x a
                (((derivWithin (connVar G x b v) (Set.Ico 0 T) s : E) : TangentSpace I x)) c d
            - Submission.Diff.rmP (G s) x a b
                (((derivWithin (connVar G x c v) (Set.Ico 0 T) s : E) : TangentSpace I x)) d
            - Submission.Diff.rmP (G s) x a b c
                (((derivWithin (connVar G x d v) (Set.Ico 0 T) s : E) : TangentSpace I x)))
            (Set.Ico 0 T) 0 :=
          ((((hA.add hB).sub hq0').sub hq1').sub hq2').sub hq3'
        exact hmain.congr_of_eventuallyEq (Filter.EventuallyEq.refl _ _) (by
          show Work.Diff.GE.covRmTimeDerivWithin F G T 0 x v a b c d = _
          rfl)
      · intro x v a b c d
        refine ⟨?_, ?_, ?_⟩
        · exact continuousWithinAt_zero_of_continuousAt_sqFlow (G := G) (T := T) hTpos
            (Q := fun g => Work.Diff.GE.lapCovRmAt g x v a b c d)
            ((hC x v a b c d).2.2.1.continuousAt)
        · exact continuousWithinAt_zero_of_continuousAt_sqFlow (G := G) (T := T) hTpos
            (Q := fun g => Submission.Diff.rmNormSq g x)
            ((hC x v a b c d).2.2.2.1.continuousAt)
        · exact continuousWithinAt_zero_of_continuousAt_sqFlow (G := G) (T := T) hTpos
            (Q := fun g => Submission.Diff.dRmNormSq g x)
            ((hC x v a b c d).2.2.2.2.1.continuousAt)
  exact ⟨fun G T hflow x v a b c d => (key G T hflow).1 x v a b c d,
    fun G T hflow x v a b c d => (key G T hflow).2.1 x v a b c d,
    fun G T hflow x v a b c d => (key G T hflow).2.2 x v a b c d⟩

end Work.Diff.GE
