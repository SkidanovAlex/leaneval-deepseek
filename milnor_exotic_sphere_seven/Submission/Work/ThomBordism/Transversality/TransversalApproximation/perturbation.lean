import Mathlib
import Submission.Work.ThomBordism.Transversality.Basic
import Submission.Work.ThomBordism.Transversality.BoxFamily.Smooth
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.setup
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.verticalFamily

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The perturbed map of the transversality homotopy theorem

This file proves `exists_perturbation` (see `verticalFamily.lean` for the plan): for a compact `T2`
manifold `M`, a `C^∞` map `F : M → X.E` into a `CoreTarget` and a `C^∞` function `χ : M → [0,1]`
such that `Φ` is a submersion at every point of `F '' tsupport χ`, there is `ε > 0` and a smooth
family `𝒢 : M → ℝ^k → X.E` on `M × {‖t‖ < ε}` with `𝒢 x 0 = F x` and
`Φ (𝒢 x t) = Φ (F x) + χ x • t`.

The construction is the composition of the finitely many vertical families covering
`F '' tsupport χ`, weighted by a smooth partition of unity subordinate to that cover.
-/

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter MeasureTheory

set_option autoImplicit false

namespace Work.ThomBordism.Transversality.TransversalApproximation

noncomputable section

open Work.ThomBordism.Transversality (CoreTarget)

variable {n k : ℕ}

/-- **Gluing of `ContMDiffOn` along an open cover.** -/
theorem contMDiffOn_iUnion_of_isOpen {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {f : M → M'} {n : WithTop ℕ∞} {ι : Type*} (O : ι → Set M) (hO : ∀ i, IsOpen (O i))
    (h : ∀ i, ContMDiffOn I I' n f (O i)) : ContMDiffOn I I' n f (⋃ i, O i) := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact ((h i).contMDiffAt ((hO i).mem_nhds hi)).contMDiffWithinAt

/-- **The intermediate maps of the perturbation**, defined by the recursion

`G 0 x t = F x`,   `G (i+1) x t = (V i).Ψ (G i x t) (ρ i x • χ x • t)`.

(The `if i < N` guard only truncates the sequence after `N` steps; it is resolved by
`dif_pos` in every application.) -/
noncomputable def Gseq {X : CoreTarget n k} {M : Type*} {N : ℕ}
    (V : Fin N → VerticalFamily X) (ρ : Fin N → M → ℝ) (χ : M → ℝ) (F : M → X.E) :
    ℕ → M → EuclideanSpace ℝ (Fin k) → X.E
  | 0 => fun x _ => F x
  | (i + 1) => fun x t =>
      if h : i < N then (V ⟨i, h⟩).Ψ (Gseq V ρ χ F i x t) (ρ ⟨i, h⟩ x • (χ x • t))
      else Gseq V ρ χ F i x t

theorem Gseq_zero {X : CoreTarget n k} {M : Type*} {N : ℕ}
    (V : Fin N → VerticalFamily X) (ρ : Fin N → M → ℝ) (χ : M → ℝ) (F : M → X.E) :
    Gseq V ρ χ F 0 = fun x (_ : EuclideanSpace ℝ (Fin k)) => F x := rfl

theorem Gseq_succ {X : CoreTarget n k} {M : Type*} {N : ℕ}
    (V : Fin N → VerticalFamily X) (ρ : Fin N → M → ℝ) (χ : M → ℝ) (F : M → X.E)
    {i : ℕ} (h : i < N) (x : M) (t : EuclideanSpace ℝ (Fin k)) :
    Gseq V ρ χ F (i + 1) x t =
      (V ⟨i, h⟩).Ψ (Gseq V ρ χ F i x t) (ρ ⟨i, h⟩ x • (χ x • t)) := by
  simp only [Gseq]
  rw [dif_pos h]

theorem Gseq_succ_of_not_lt {X : CoreTarget n k} {M : Type*} {N : ℕ}
    (V : Fin N → VerticalFamily X) (ρ : Fin N → M → ℝ) (χ : M → ℝ) (F : M → X.E)
    {i : ℕ} (h : ¬ i < N) (x : M) (t : EuclideanSpace ℝ (Fin k)) :
    Gseq V ρ χ F (i + 1) x t = Gseq V ρ χ F i x t := by
  simp only [Gseq]
  rw [dif_neg h]


/-- **The perturbed map.**  For `χ : M → [0,1]` smooth and `Φ` submersive at every point of
`F '' tsupport χ`, there is `ε > 0` and a smooth family `𝒢` on `M × {‖t‖ < ε}` with `𝒢 x 0 = F x`
and `Φ (𝒢 x t) = Φ (F x) + χ x • t`. -/
theorem exists_perturbation
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E' H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [CompactSpace M] [T2Space M]
    (X : CoreTarget n k) (F : M → X.E)
    (hF : ContMDiff I (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (χ : M → ℝ) (hχ : ContMDiff I (𝓘(ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hχsupp : ∀ x ∈ tsupport χ, IsSubmersionAt (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ (F x)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ 𝒢 : M → EuclideanSpace ℝ (Fin k) → X.E,
      ContMDiffOn (I.prod (𝓡 k)) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : M × EuclideanSpace ℝ (Fin k) => 𝒢 p.1 p.2)
        (Set.univ ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ε) ∧
      (∀ x, 𝒢 x 0 = F x) ∧
      (∀ x t, ‖t‖ < ε → X.Φ (𝒢 x t) = X.Φ (F x) + χ x • t) ∧
      (∀ x, (∀ᶠ y in 𝓝 x, χ y = 0) → ∀ t, 𝒢 x t = F x) := by
  classical
  -- ### Step 1: the cover and the partition of unity
  have hdata : ∃ (N : ℕ) (V : Fin N → VerticalFamily X) (W : Fin N → Set X.E)
      (δ : Fin N → ℝ) (ρ : Fin N → M → ℝ),
      (∀ i, IsOpen (W i)) ∧ (∀ i, 0 < δ i) ∧
      (∀ i, ContMDiff I (𝓘(ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ i)) ∧
      (∀ i, tsupport (ρ i) ⊆ F ⁻¹' (W i)) ∧
      (∀ i, ∀ y ∈ W i, ∀ t : EuclideanSpace ℝ (Fin k), ‖t‖ ≤ δ i → (y, t) ∈ (V i).valid) ∧
      (∀ x ∈ tsupport χ, ∑ i : Fin N, ρ i x = 1) := by
    have hcd : ∀ p : ↥(tsupport χ), ∃ V : VerticalFamily X, ∃ W : Set X.E, ∃ δ : ℝ,
        IsOpen W ∧ F p ∈ W ∧ 0 < δ ∧ ∀ y ∈ W, ∀ t : EuclideanSpace ℝ (Fin k), ‖t‖ ≤ δ → (y, t) ∈ V.valid :=
      fun p => exists_verticalFamily X (hχsupp p p.2)
    choose Vf Wf δf hWf hWfm hδf hbf using hcd
    have hcov : tsupport χ ⊆ ⋃ p : ↥(tsupport χ), F ⁻¹' (Wf p) := fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hx⟩, hWfm ⟨x, hx⟩⟩
    obtain ⟨s, hs⟩ := (isClosed_tsupport χ).isCompact.elim_finite_subcover
      (fun p : ↥(tsupport χ) => F ⁻¹' (Wf p)) (fun p => (hWf p).preimage hF.continuous) hcov
    let e : ↥s ≃ Fin (Fintype.card ↥s) := Fintype.equivFin ↥s
    have hcov' : tsupport χ ⊆ ⋃ i : Fin (Fintype.card ↥s), F ⁻¹' (Wf (e.symm i).1) := by
      intro x hx
      obtain ⟨p, hps, hpx⟩ := mem_iUnion₂.mp (hs hx)
      refine mem_iUnion.mpr ⟨e ⟨p, hps⟩, ?_⟩
      rw [e.symm_apply_apply]
      exact hpx
    obtain ⟨φ, hφsub⟩ := SmoothPartitionOfUnity.exists_isSubordinate I (isClosed_tsupport χ)
      (fun i : Fin (Fintype.card ↥s) => F ⁻¹' (Wf (e.symm i).1))
      (fun i => (hWf _).preimage hF.continuous) hcov'
    refine ⟨Fintype.card ↥s, fun i => Vf (e.symm i).1, fun i => Wf (e.symm i).1,
      fun i => δf (e.symm i).1, fun i x => φ i x, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun i => hWf _
    · exact fun i => hδf _
    · exact fun i => (φ i).contMDiff
    · intro i x hx
      exact hφsub i hx
    · intro i y hy t ht
      exact hbf (e.symm i).1 y hy t ht
    · intro x hx
      have h := φ.sum_eq_one hx
      rw [finsum_eq_sum_of_fintype] at h
      exact h
  obtain ⟨N, V, W, δ, ρ, hWopen, hδpos, hρsm, hsupp, hbox, hsum⟩ := hdata
  -- ### Step 2: the sequence of intermediate maps and its running sum
  let σ : ℕ → M → ℝ := fun i x => ∑ j : Fin N, if j.1 < i then ρ j x else 0
  have hσ_succ : ∀ (i : ℕ) (h : i < N) (x : M), σ (i + 1) x = σ i x + ρ ⟨i, h⟩ x := by
    intro i h x
    have hsplit : ∀ j : Fin N,
        (if j.1 < i + 1 then ρ j x else 0) =
          (if j.1 < i then ρ j x else 0) + (if j = ⟨i, h⟩ then ρ ⟨i, h⟩ x else 0) := by
      intro j
      by_cases hji : j.1 < i
      · have hne : j ≠ ⟨i, h⟩ := fun hc => absurd hji (by rw [hc]; exact lt_irrefl i)
        simp [hji, Nat.lt_succ_of_lt hji, hne]
      · rcases eq_or_lt_of_le (Nat.le_of_not_lt hji) with heq | hlt
        · have hje : j = ⟨i, h⟩ := by ext; exact heq.symm
          subst hje
          simp
        · have hne : j ≠ ⟨i, h⟩ := fun hc => absurd hlt (by rw [hc]; exact lt_irrefl i)
          have hni : ¬ (j.1 < i + 1) := by omega
          simp [hji, hni, hne]
    have hsingle : (∑ j : Fin N, if j = ⟨i, h⟩ then ρ ⟨i, h⟩ x else 0) = ρ ⟨i, h⟩ x := by
      rw [Finset.sum_eq_single ⟨i, h⟩]
      · simp
      · intro b _ hb; simp [hb]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    simp only [σ]
    rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib, hsingle]
  have hσN : ∀ x, σ N x = ∑ j : Fin N, ρ j x := by
    intro x
    simp only [σ]
    exact Finset.sum_congr rfl fun j _ => by simp [j.2]
  -- ### Step 3: the induction
  have key : ∀ i : ℕ, i ≤ N → ∃ ε : ℝ, 0 < ε ∧
      ContMDiffOn (I.prod (𝓡 k)) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : M × EuclideanSpace ℝ (Fin k) => Gseq V ρ χ F i p.1 p.2)
        (Set.univ ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ε) ∧
      (∀ x, Gseq V ρ χ F i x 0 = F x) ∧
      (∀ x t, ‖t‖ < ε → X.Φ (Gseq V ρ χ F i x t) = X.Φ (F x) + σ i x • (χ x • t)) ∧
      (∀ x, (∀ᶠ y in 𝓝 x, χ y = 0) → ∀ t, Gseq V ρ χ F i x t = F x) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨1, one_pos, ?_, ?_, ?_, ?_⟩
      · have h0 : Gseq V ρ χ F 0 = fun x (_ : EuclideanSpace ℝ (Fin k)) => F x := rfl
        rw [h0]
        exact (hF.comp contMDiff_fst).contMDiffOn
      · intro x; rfl
      · intro x t _
        have hz : σ 0 x = 0 := by
          simp only [σ]
          exact Finset.sum_eq_zero fun j _ => by simp
        simp only [Gseq_zero]
        rw [hz, zero_smul, add_zero]
      · intro x _ t
        rfl
    | succ i ih =>
      intro hi
      have hiN : i < N := Nat.lt_of_succ_le hi
      obtain ⟨ε, hε, hsmooth, hzero, hadd, hvanish⟩ := ih (Nat.le_of_succ_le hi)
      have hsuppi : tsupport (ρ ⟨i, hiN⟩) ⊆ F ⁻¹' (W ⟨i, hiN⟩) := hsupp ⟨i, hiN⟩
      have hboxi : ∀ y ∈ W ⟨i, hiN⟩, ∀ t : EuclideanSpace ℝ (Fin k), ‖t‖ ≤ δ ⟨i, hiN⟩ →
          (y, t) ∈ (V ⟨i, hiN⟩).valid := hbox ⟨i, hiN⟩
      have hwc : ContMDiff (I.prod (𝓡 k)) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : M × EuclideanSpace ℝ (Fin k) => ρ ⟨i, hiN⟩ q.1 • (χ q.1 • q.2)) :=
        ((hρsm ⟨i, hiN⟩).comp contMDiff_fst).smul ((hχ.comp contMDiff_fst).smul contMDiff_snd)
      have hargsm : ∀ p : M × EuclideanSpace ℝ (Fin k), ‖p.2‖ < ε →
          ContMDiffAt (I.prod (𝓡 k)) ((𝓡 n).prod (𝓡 k)) ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun q : M × EuclideanSpace ℝ (Fin k) =>
              (Gseq V ρ χ F i q.1 q.2, ρ ⟨i, hiN⟩ q.1 • (χ q.1 • q.2))) p := fun p hp =>
        ContMDiffAt.prodMk
          (hsmooth.contMDiffAt ((isOpen_univ.prod Metric.isOpen_ball).mem_nhds
            ⟨trivial, by simpa [Metric.mem_ball] using hp⟩))
          hwc.contMDiffAt
      have hcont : ∀ x ∈ tsupport (ρ ⟨i, hiN⟩), ContinuousAt
          (fun p : M × EuclideanSpace ℝ (Fin k) =>
            (Gseq V ρ χ F i p.1 p.2, ρ ⟨i, hiN⟩ p.1 • (χ p.1 • p.2))) (x, 0) :=
        fun x _ => (hargsm (x, 0) (by simpa using hε)).continuousAt
      have h0mem : ∀ x ∈ tsupport (ρ ⟨i, hiN⟩),
          (Gseq V ρ χ F i x 0, ρ ⟨i, hiN⟩ x • (χ x • 0)) ∈ (V ⟨i, hiN⟩).valid := by
        intro x hx
        have hxW : F x ∈ W ⟨i, hiN⟩ := hsuppi hx
        have hF0 : (F x, 0) ∈ (V ⟨i, hiN⟩).valid :=
          hboxi (F x) hxW 0 (by rw [norm_zero]; exact (hδpos ⟨i, hiN⟩).le)
        simp only [hzero x, smul_zero]
        exact hF0
      obtain ⟨δ', hδ'pos, hδ'mem⟩ := exists_uniform_ball_of_isCompact_of_continuousAt
        (y := fun x t => (Gseq V ρ χ F i x t, ρ ⟨i, hiN⟩ x • (χ x • t)))
        (isClosed_tsupport _).isCompact hcont (V ⟨i, hiN⟩).isOpen_valid h0mem
      refine ⟨min ε δ', lt_min hε hδ'pos, ?_, ?_, ?_, ?_⟩
      · intro p hp
        have hpε : ‖p.2‖ < ε :=
          lt_of_lt_of_le (by simpa [Metric.mem_ball] using hp.2) (min_le_left _ _)
        have hpδ : ‖p.2‖ < δ' :=
          lt_of_lt_of_le (by simpa [Metric.mem_ball] using hp.2) (min_le_right _ _)
        have hsm_i : ContMDiffAt (I.prod (𝓡 k)) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun q : M × EuclideanSpace ℝ (Fin k) => Gseq V ρ χ F i q.1 q.2) p :=
          hsmooth.contMDiffAt ((isOpen_univ.prod Metric.isOpen_ball).mem_nhds
            ⟨trivial, by simpa [Metric.mem_ball] using hpε⟩)
        by_cases hpt : p.1 ∈ tsupport (ρ ⟨i, hiN⟩)
        · have hmem : (Gseq V ρ χ F i p.1 p.2, ρ ⟨i, hiN⟩ p.1 • (χ p.1 • p.2)) ∈
              (V ⟨i, hiN⟩).valid := hδ'mem p.1 hpt p.2 hpδ
          have hargp := hargsm p hpε
          have hψ : ContMDiffAt ((𝓡 n).prod (𝓡 k)) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
              (fun w : X.E × EuclideanSpace ℝ (Fin k) => (V ⟨i, hiN⟩).Ψ w.1 w.2)
              (Gseq V ρ χ F i p.1 p.2, ρ ⟨i, hiN⟩ p.1 • (χ p.1 • p.2)) :=
            (V ⟨i, hiN⟩).contMDiffOn.contMDiffAt ((V ⟨i, hiN⟩).isOpen_valid.mem_nhds hmem)
          refine ((hψ.comp p hargp).congr_of_eventuallyEq ?_).contMDiffWithinAt.mono (subset_univ _)
          filter_upwards [hargp.continuousAt.preimage_mem_nhds
            ((V ⟨i, hiN⟩).isOpen_valid.mem_nhds hmem)] with q hq
          exact Gseq_succ V ρ χ F hiN q.1 q.2
        · refine (hsm_i.congr_of_eventuallyEq ?_).contMDiffWithinAt.mono (subset_univ _)
          filter_upwards [((isClosed_tsupport _).isOpen_compl.preimage continuous_fst).mem_nhds hpt]
            with q hq
          have hq0 : ρ ⟨i, hiN⟩ q.1 = 0 := by
            by_contra hc
            exact hq (subset_closure (mem_support.mpr hc))
          rw [Gseq_succ V ρ χ F hiN q.1 q.2, hq0]
          simp only [zero_smul, (V ⟨i, hiN⟩).zero_apply]
      · intro x
        simp only [Gseq_succ V ρ χ F hiN, hzero x, smul_zero, (V ⟨i, hiN⟩).zero_apply]
      · intro x t ht
        have htε : ‖t‖ < ε := lt_of_lt_of_le ht (min_le_left _ _)
        have htδ : ‖t‖ < δ' := lt_of_lt_of_le ht (min_le_right _ _)
        rw [Gseq_succ V ρ χ F hiN x t, hσ_succ i hiN x]
        by_cases hx : x ∈ tsupport (ρ ⟨i, hiN⟩)
        · rw [(V ⟨i, hiN⟩).Φ_apply _ _ (hδ'mem x hx t htδ), hadd x t htε, add_smul]
          abel
        · have hx0 : ρ ⟨i, hiN⟩ x = 0 := by
            by_contra hc
            exact hx (subset_closure (mem_support.mpr hc))
          rw [hx0, zero_smul, (V ⟨i, hiN⟩).zero_apply, hadd x t htε, add_zero]
      · intro x hx t
        rw [Gseq_succ V ρ χ F hiN x t, hx.self_of_nhds]
        rw [zero_smul, smul_zero, (V ⟨i, hiN⟩).zero_apply]
        exact hvanish x hx t
  -- ### Step 4: conclude
  obtain ⟨ε, hε, hsmooth, hzero, hadd, hvanish⟩ := key N le_rfl
  refine ⟨ε, hε, fun x t => Gseq V ρ χ F N x t, hsmooth, hzero, ?_, ?_⟩
  · intro x t ht
    rw [hadd x t ht]
    by_cases hx : χ x = 0
    · rw [hx]; simp
    · have hxS : x ∈ tsupport χ := subset_closure (mem_support.mpr hx)
      have hσ1 : σ N x = 1 := by rw [hσN]; exact hsum x hxS
      rw [hσ1, one_smul]
  · intro x hx t
    exact hvanish x hx t
end

end Work.ThomBordism.Transversality.TransversalApproximation
