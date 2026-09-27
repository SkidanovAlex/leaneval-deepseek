import Mathlib
import Submission.Work.Whitney.CutPush.flow_of_compactSupport
import Submission.Work.Drive.N2.jointFlowAssembly
import Submission.Work.Drive.N2.isIntegralCurve_mem_tsupport_or_eq
import Submission.Work.ODE.GlobalFlow
import Submission.Work.Whitney.CutPush.finite_localRetraction_sep
import Submission.Work.Whitney.CutPush.partition_of_unity_trail_arc
import Submission.Work.Isotopy.localRetraction_at
import Submission.Work.Whitney.CutPush.arc_unknotting
import Submission.Work.Drive.PushDisc.uniformInjOnNearArc
import Submission.Work.Drive.PushDisc.localInverseFamilyTwoSidedRepair

/-!
# Globalising a local isotopy along an arc

Given a smooth family `Ψ : ℝ → ℝ^m → ℝ^m` with `Ψ 0 = id` whose differential along the arc
`γ : ℝ → ℝ^m` is invertible at every time, the goal is a global `C^∞` diffeomorphism `A` of `ℝ^m`
which is the identity off a prescribed open set `U ⊇ γ '' Icc 0 1` and whose differential at `γ t`
is the differential of `Ψ 1` there.

The proof is the classical one: the family is a *local* isotopy near the arc; its material velocity
field, patched from local inverses of the family, is cut off (in space, along the trail, and in the
time parameter) and flowed; the flow is compared with the isotopy on the open set of points whose
orbit stays inside the patched region.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Set Topology Filter MeasureTheory

/-- The partial derivative of the uncurried family in its second variable. -/
lemma fderiv_uncurry_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ × E → E) {s : ℝ} {y : E} (hG : DifferentiableAt ℝ G (s, y)) (v : E) :
    fderiv ℝ G (s, y) (0, v) = fderiv ℝ (fun y' : E => G (s, y')) y v := by
  have h1 : HasFDerivAt (fun y' : E => (s, y')) (ContinuousLinearMap.inr ℝ ℝ E) y :=
    hasFDerivAt_prodMk_right s y
  have h2 : HasFDerivAt (fun y' : E => G (s, y'))
      ((fderiv ℝ G (s, y)) ∘L ContinuousLinearMap.inr ℝ ℝ E) y := by
    simpa only [Function.comp_def] using hG.hasFDerivAt.comp y h1
  rw [h2.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- The λ-derivative of the section of a jointly smooth `G : ℝ × E → E`. -/
lemma hasDerivAt_section {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ × E → E) {s : ℝ} (y : E) (hG : DifferentiableAt ℝ G (s, y)) :
    HasDerivAt (fun u : ℝ => G (u, y)) (fderiv ℝ G (s, y) (1, 0)) s := by
  have h1 : HasFDerivAt (fun u : ℝ => (u, y)) (ContinuousLinearMap.inl ℝ ℝ E) s :=
    hasFDerivAt_prodMk_left s y
  have h2 : HasFDerivAt (fun u : ℝ => G (u, y))
      ((fderiv ℝ G (s, y)) ∘L ContinuousLinearMap.inl ℝ ℝ E) s := by
    simpa only [Function.comp_def] using hG.hasFDerivAt.comp s h1
  have h3 : ((fderiv ℝ G (s, y)) ∘L ContinuousLinearMap.inl ℝ ℝ E) 1
      = fderiv ℝ G (s, y) (1, 0) := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, Prod.mk.eta]
  have h4 := h2.hasDerivAt
  rw [h3] at h4
  exact h4

/-- **A smooth bump equal to `1` near a compact set, supported in a prescribed open neighbourhood
of it, and compactly supported.** -/
lemma exists_contDiff_bump_compact {m : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K)
    (U : Set (EuclideanSpace ℝ (Fin m))) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : EuclideanSpace ℝ (Fin m) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ (∀ z, 0 ≤ χ z) ∧
      (∃ δ > 0, ∀ z, z ∈ Metric.thickening δ K → χ z = 1) ∧
      tsupport χ ⊆ U ∧ HasCompactSupport χ := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · refine ⟨fun _ => 0, contDiff_const, fun z => le_refl 0, ⟨1, one_pos, fun z hz => ?_⟩, ?_, ?_⟩
    · simp [Metric.thickening] at hz
    · intro z hz
      simp [tsupport] at hz
    · exact HasCompactSupport.zero
  obtain ⟨δ, hδpos, hδsub⟩ := hK.exists_cthickening_subset_open hU hKU
  set A : Set (EuclideanSpace ℝ (Fin m)) := Metric.thickening (δ/2) K with hA
  set B : Set (EuclideanSpace ℝ (Fin m)) := {z | (δ/4 : ℝ) < Metric.infDist z K} with hB
  have hAopen : IsOpen A := Metric.isOpen_thickening
  have hBopen : IsOpen B := by
    rw [hB]
    exact isOpen_lt continuous_const (Metric.continuous_infDist_pt K)
  have hcover : (Set.univ : Set (EuclideanSpace ℝ (Fin m))) ⊆ ⋃ i : Fin 2, ![A, B] i := by
    intro z _
    by_cases h : Metric.infDist z K ≤ δ/4
    · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
      simp only [Matrix.cons_val_zero]
      rw [hA, Metric.mem_thickening_iff]
      exact (Metric.infDist_lt_iff hKne).mp (by linarith)
    · refine Set.mem_iUnion.mpr ⟨1, ?_⟩
      have hBz : z ∈ B := by rw [hB]; exact lt_of_not_ge h
      simpa using hBz
  have hopen : ∀ i : Fin 2, IsOpen (![A, B] i) := by
    intro i
    fin_cases i <;> simp_all
  obtain ⟨ρ, hρsub⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (s := Set.univ) isClosed_univ
    (fun i : Fin 2 => ![A, B] i) hopen hcover
  have hA_of_supp : ∀ z ∈ tsupport (fun z => ρ 0 z), z ∈ A := by
    intro z hz
    have := hρsub 0 hz
    simpa using this
  refine ⟨fun z => ρ 0 z, (ρ 0).contMDiff.contDiff, fun z => ρ.nonneg 0 z, ?_, ?_, ?_⟩
  · refine ⟨δ/4, by linarith, fun z hz => ?_⟩
    have hz1 : ρ 1 z = 0 := by
      by_contra hne
      have hmem : z ∈ tsupport (fun z => ρ 1 z) := subset_tsupport _ hne
      have hBz : z ∈ B := by
        have := hρsub 1 hmem
        simpa using this
      have hBz' : δ/4 < Metric.infDist z K := hBz
      have hlt : Metric.infDist z K < δ/4 := by
        rw [Metric.mem_thickening_iff] at hz
        obtain ⟨y, hyK, hy⟩ := hz
        exact lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hyK) hy
      linarith
    have hsum : ∑ᶠ i : Fin 2, ρ i z = 1 := ρ.sum_eq_one (mem_univ z)
    rw [finsum_eq_sum_of_fintype, Fin.sum_univ_two] at hsum
    linarith
  · intro z hz
    have hAz : z ∈ A := hA_of_supp z hz
    rw [hA] at hAz
    exact hδsub ((Metric.thickening_subset_cthickening_of_le (by linarith) K) hAz)
  · refine IsCompact.of_isClosed_subset (s := Metric.cthickening (δ/2) K) ?_
      (isClosed_tsupport _) ?_
    · exact Metric.isCompact_of_isClosed_isBounded Metric.isClosed_cthickening
        hK.isBounded.cthickening
    · intro z hz
      have hAz : z ∈ A := hA_of_supp z hz
      rw [hA] at hAz
      exact (Metric.thickening_subset_cthickening_of_le (by linarith) K) hAz

/-- **A uniform radius for a family of curves staying in an open set.**  If the whole trail
`λ ↦ (λ, Ψ λ x₀)` lies in an open set `P`, then all nearby curves `λ ↦ (λ, Ψ λ y)` (with `y` close
to `x₀`) do as well, uniformly over `λ ∈ [0,1]`. -/
lemma exists_tube_radius {m : ℕ}
    (Ψ : ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hΨ : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin m) => Ψ p.1 p.2))
    (P : Set (ℝ × EuclideanSpace ℝ (Fin m))) (hP : IsOpen P)
    (x₀ : EuclideanSpace ℝ (Fin m))
    (h0 : ∀ lam, lam ∈ Set.Icc (0 : ℝ) 1 → (lam, Ψ lam x₀) ∈ P) :
    ∃ ε, 0 < ε ∧ ∀ lam, lam ∈ Set.Icc (0 : ℝ) 1 → ∀ y, ‖y - x₀‖ < ε →
      (lam, Ψ lam y) ∈ P := by
  have hG : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin m) => (p.1, Ψ p.1 p.2)) :=
    continuous_fst.prodMk hΨ
  have hW : IsOpen {p : ℝ × EuclideanSpace ℝ (Fin m) | (p.1, Ψ p.1 p.2) ∈ P} := hP.preimage hG
  have hsub : (Set.Icc (0 : ℝ) 1) ×ˢ ({x₀} : Set (EuclideanSpace ℝ (Fin m))) ⊆
      {p : ℝ × EuclideanSpace ℝ (Fin m) | (p.1, Ψ p.1 p.2) ∈ P} := by
    rintro ⟨lam, y⟩ ⟨hlam, hy⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact h0 lam hlam
  obtain ⟨u, v, hu, hv, huI, hvx, huv⟩ :=
    generalized_tube_lemma isCompact_Icc (isCompact_singleton (x := x₀)) hW hsub
  obtain ⟨ε, hεpos, hεsub⟩ := (Metric.isOpen_iff.mp hv) x₀ (hvx (mem_singleton x₀))
  refine ⟨ε, hεpos, fun lam hlam y hy => ?_⟩
  have hymem : y ∈ v := hεsub (Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hy))
  have hprod : (lam, y) ∈ u ×ˢ v := Set.mem_prod.mpr ⟨huI hlam, hymem⟩
  exact huv hprod

/-- **A smooth partition of unity on a neighbourhood of a compact set, subordinate to a finite open
cover.** -/
lemma exists_partitionOfUnity_compact {m : ℕ} {ι : Type} [Fintype ι]
    (T : Set (ℝ × EuclideanSpace ℝ (Fin m))) (hT : IsCompact T)
    (O : ι → Set ℝ) (hO : ∀ j, IsOpen (O j))
    (W : ι → Set (EuclideanSpace ℝ (Fin m))) (hW : ∀ j, IsOpen (W j))
    (hcover : T ⊆ ⋃ j, O j ×ˢ W j) :
    ∃ (ψ : ι → ℝ → EuclideanSpace ℝ (Fin m) → ℝ) (δ : ℝ), 0 < δ ∧
      (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (ψ j))) ∧
      (∀ j lam z, 0 ≤ ψ j lam z) ∧
      (∀ j, tsupport (fun p : ℝ × EuclideanSpace ℝ (Fin m) => ψ j p.1 p.2) ⊆ O j ×ˢ W j) ∧
      (∀ p ∈ Metric.thickening δ T, ∑ j, ψ j p.1 p.2 = 1) := by
  classical
  have hopen : IsOpen (⋃ j, O j ×ˢ W j) := isOpen_iUnion fun j => (hO j).prod (hW j)
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := hT.exists_cthickening_subset_open hopen hcover
  obtain ⟨ρ, hρsub⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin m))) (s := Metric.cthickening (δ₀/2) T)
    Metric.isClosed_cthickening (fun j => O j ×ˢ W j) (fun j => (hO j).prod (hW j))
    (fun p hp => hδ₀sub ((Metric.cthickening_mono (by linarith) T) hp))
  refine ⟨fun j lam z => ρ j (lam, z), δ₀/2, by linarith, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (ρ j).contMDiff.contDiff
  · intro j lam z; exact ρ.nonneg j (lam, z)
  · intro j
    simpa using hρsub j
  · intro p hp
    have h1 : ∑ᶠ j : ι, ρ j p = 1 :=
      ρ.sum_eq_one ((Metric.thickening_subset_cthickening_of_le (by linarith) T) hp)
    rwa [finsum_eq_sum_of_fintype] at h1


/-- **Globalisation of a local isotopy along an arc, given local inverse data.**

`Ψ` is a smooth one-parameter family of maps with `Ψ 0 = id` whose differential along the arc `γ`
(given by the boxes `Olam j ×ˢ Otgt j` with local inverses `par j` of `Ψ`) is invertible.  The
material velocity of the family is patched from the local inverses, cut off along the trail and off
`U`, and flowed; the flow agrees with the family on the open set of points whose orbit stays in the
patched region, which yields the prescribed differential at the arc points. -/
theorem exists_diffeo_of_localInverseData {m : ℕ}
    (γ : ℝ → EuclideanSpace ℝ (Fin m))
    (Ψ : ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (U : Set (EuclideanSpace ℝ (Fin m)))
    (hγsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hΨsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin m) => Ψ p.1 p.2))
    (hU : IsOpen U)
    (htrail : ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, Ψ lam (γ t) ∈ U)
    (hΨ0 : ∀ y, Ψ 0 y = y)
    (Ω : Set (EuclideanSpace ℝ (Fin m))) (hΩopen : IsOpen Ω)
    (hΩarc : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Ω)
    (hΩinj : ∀ lam ∈ Set.Icc (0 : ℝ) 1, Set.InjOn (Ψ lam) Ω)
    {ι : Type} [Fintype ι]
    (Olam : ι → Set ℝ) (Osrc : ι → Set (EuclideanSpace ℝ (Fin m)))
    (Otgt : ι → Set (EuclideanSpace ℝ (Fin m)))
    (par : ι → ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hOopen : ∀ j, IsOpen (Olam j)) (hSopen : ∀ j, IsOpen (Osrc j))
    (hTopen : ∀ j, IsOpen (Otgt j))
    (hSΩ : ∀ j, Osrc j ⊆ Ω)
    (hparsm : ∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (par j)) (Olam j ×ˢ Otgt j))
    (hparR : ∀ j, ∀ lam ∈ Olam j, ∀ z ∈ Otgt j,
      par j lam z ∈ Osrc j ∧ Ψ lam (par j lam z) = z)
    (hcover : ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∃ j, lam ∈ Olam j ∧ Ψ lam (γ t) ∈ Otgt j) :
    ∃ (A Ainv : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
      Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
      (∀ y, y ∉ U → A y = y) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, fderiv ℝ A (γ t) = fderiv ℝ (Ψ 1) (γ t)) := by
  classical
  -- ## the trail and its image
  let T : Set (ℝ × EuclideanSpace ℝ (Fin m)) :=
    {q | ∃ lam ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ Set.Icc (0 : ℝ) 1, q = (lam, Ψ lam (γ t))}
  have hTcomp : IsCompact T := by
    have hcont : Continuous (fun p : ℝ × ℝ => (p.1, Ψ p.1 (γ p.2))) :=
      continuous_fst.prodMk (hΨsm.continuous.comp
        (continuous_fst.prodMk (hγsm.continuous.comp continuous_snd)))
    have himg : T = (fun p : ℝ × ℝ => (p.1, Ψ p.1 (γ p.2))) ''
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
      ext q
      constructor
      · rintro ⟨lam, hlam, t, ht, rfl⟩
        exact ⟨(lam, t), ⟨hlam, ht⟩, rfl⟩
      · rintro ⟨⟨lam, t⟩, ⟨hlam, ht⟩, rfl⟩
        exact ⟨lam, hlam, t, ht, rfl⟩
    rw [himg]
    exact (isCompact_Icc.prod isCompact_Icc).image hcont
  let Timg : Set (EuclideanSpace ℝ (Fin m)) :=
    {z | ∃ lam ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ Set.Icc (0 : ℝ) 1, z = Ψ lam (γ t)}
  have hTimgcomp : IsCompact Timg := by
    have hcont : Continuous (fun p : ℝ × ℝ => Ψ p.1 (γ p.2)) :=
      hΨsm.continuous.comp (continuous_fst.prodMk (hγsm.continuous.comp continuous_snd))
    have himg : Timg = (fun p : ℝ × ℝ => Ψ p.1 (γ p.2)) ''
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
      ext z
      constructor
      · rintro ⟨lam, hlam, t, ht, rfl⟩
        exact ⟨(lam, t), ⟨hlam, ht⟩, rfl⟩
      · rintro ⟨⟨lam, t⟩, ⟨hlam, ht⟩, rfl⟩
        exact ⟨lam, hlam, t, ht, rfl⟩
    rw [himg]
    exact (isCompact_Icc.prod isCompact_Icc).image hcont
  have hTimgU : Timg ⊆ U := by
    rintro z ⟨lam, hlam, t, ht, rfl⟩
    exact htrail lam hlam t ht
  -- ## the partition of unity and the bumps
  have hTcov : T ⊆ ⋃ j, Olam j ×ˢ Otgt j := by
    rintro q ⟨lam, hlam, t, ht, rfl⟩
    obtain ⟨j, hj1, hj2⟩ := hcover lam hlam t ht
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_prod.mpr ⟨hj1, hj2⟩⟩
  obtain ⟨ψ, δ, hδpos, hψsm, hψnn, hψtsupp, hψsum⟩ :=
    exists_partitionOfUnity_compact T hTcomp Olam hOopen Otgt hTopen hTcov
  obtain ⟨χ, hχsm, hχnn, ⟨δχ, hδχpos, hχone⟩, hχsupp, hχcs⟩ :=
    exists_contDiff_bump_compact Timg hTimgcomp U hU hTimgU
  -- ## the material velocity field
  let vel : ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun lam y => fderiv ℝ (fun p : ℝ × EuclideanSpace ℝ (Fin m) => Ψ p.1 p.2) (lam, y) (1, 0)
  have hvelsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin m) => vel p.1 p.2) := by
    have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
          fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin m) => Ψ q.1 q.2) p) := by
      have h := (contDiffOn_infty_iff_fderiv_of_isOpen (𝕜 := ℝ)
        (f := fun q : ℝ × EuclideanSpace ℝ (Fin m) => Ψ q.1 q.2) (s := Set.univ) isOpen_univ).mp
        (hΨsm.contDiffOn (s := Set.univ))
      exact contDiffOn_univ.mp h.2
    exact hfd.clm_apply (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : ℝ × EuclideanSpace ℝ (Fin m) => ((1:ℝ), (0 : EuclideanSpace ℝ (Fin m)))))
  let X : ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun lam z => ∑ j, ψ j lam z • vel lam (par j lam z)
  have hXsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin m) => X p.1 p.2) := by
    have hfun : (fun p : ℝ × EuclideanSpace ℝ (Fin m) => X p.1 p.2)
        = fun p : ℝ × EuclideanSpace ℝ (Fin m) => ∑ j, ψ j p.1 p.2 • vel p.1 (par j p.1 p.2) := rfl
    rw [hfun]
    refine ContDiff.sum (fun j _ => ?_)
    refine Work.Whitney.CutPush.contDiff_smul_of_tsupport
      (f := fun p : ℝ × EuclideanSpace ℝ (Fin m) => ψ j p.1 p.2)
      (U := Olam j ×ˢ Otgt j) (hψsm j) ?_ ((hOopen j).prod (hTopen j)) (hψtsupp j)
    have hpair : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin m) => (p.1, par j p.1 p.2)) (Olam j ×ˢ Otgt j) :=
      ContDiffOn.prodMk contDiffOn_fst (hparsm j)
    exact hvelsm.contDiffOn.comp hpair (fun p _ => Set.mem_univ _)
  -- ## the cutoffs: in time (`arcBump`) and in space (`χ`)
  have harcBump_cs : HasCompactSupport Work.Whitney.CutPush.arcBump := by
    have hsub : tsupport Work.Whitney.CutPush.arcBump ⊆ Set.Icc (-2 : ℝ) 3 := by
      refine closure_minimal (fun t ht => ?_) isClosed_Icc
      rw [Set.mem_Icc]
      constructor
      · by_contra h
        exact ht (Work.Whitney.CutPush.arcBump_eq_zero_of_le (le_of_lt (not_le.mp h)))
      · by_contra h
        exact ht (Work.Whitney.CutPush.arcBump_eq_zero_of_ge (le_of_lt (not_le.mp h)))
    exact IsCompact.of_isClosed_subset (s := Set.Icc (-2 : ℝ) 3) isCompact_Icc
      (isClosed_tsupport _) hsub
  let V : ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun lam z => (Work.Whitney.CutPush.arcBump lam * χ z) • X lam z
  have hVsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin m) => V p.1 p.2) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin m) => Work.Whitney.CutPush.arcBump p.1 * χ p.2) :=
      (Work.Whitney.CutPush.arcBump_contDiff.comp contDiff_fst).mul (hχsm.comp contDiff_snd)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
          (Work.Whitney.CutPush.arcBump p.1 * χ p.2) • X p.1 p.2) := h1.smul hXsm
    simpa [V] using h2
  have hVcs : HasCompactSupport (fun p : ℝ × EuclideanSpace ℝ (Fin m) => V p.1 p.2) := by
    have hsupp : Function.support (fun p : ℝ × EuclideanSpace ℝ (Fin m) => V p.1 p.2) ⊆
        Function.support Work.Whitney.CutPush.arcBump ×ˢ Function.support χ := by
      intro p hp
      have h1 : Work.Whitney.CutPush.arcBump p.1 ≠ 0 := by
        intro h; exact hp (by simp [V, h])
      have h2 : χ p.2 ≠ 0 := by
        intro h; exact hp (by simp [V, h])
      exact ⟨h1, h2⟩
    refine IsCompact.of_isClosed_subset
      (s := tsupport Work.Whitney.CutPush.arcBump ×ˢ tsupport χ)
      (harcBump_cs.isCompact.prod hχcs.isCompact) (isClosed_tsupport _) ?_
    refine closure_minimal (fun x hx =>
      ⟨subset_tsupport _ (hsupp hx).1, subset_tsupport _ (hsupp hx).2⟩) ?_
    exact (isClosed_tsupport _).prod (isClosed_tsupport _)
  -- ## the material identity on the patched region
  have hmat : ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Ω,
      (lam, Ψ lam y) ∈ Metric.thickening δ T → Ψ lam y ∈ Metric.thickening δχ Timg →
      V lam (Ψ lam y) = vel lam y := by
    intro lam hlam y hyΩ hmem hmemχ
    have hsum1 : ∑ j, ψ j lam (Ψ lam y) = 1 := hψsum (lam, Ψ lam y) hmem
    have hXval : X lam (Ψ lam y) = vel lam y := by
      have hterm : ∀ j, ψ j lam (Ψ lam y) • vel lam (par j lam (Ψ lam y))
          = ψ j lam (Ψ lam y) • vel lam y := by
        intro j
        by_cases h : ψ j lam (Ψ lam y) = 0
        · rw [h, zero_smul, zero_smul]
        · have hmemψ : (lam, Ψ lam y) ∈
              tsupport (fun p : ℝ × EuclideanSpace ℝ (Fin m) => ψ j p.1 p.2) :=
            subset_tsupport _ (by simpa using h)
          obtain ⟨hlO, hlT⟩ := Set.mem_prod.mp (hψtsupp j hmemψ)
          obtain ⟨hy'src, hy'eq⟩ := hparR j lam hlO (Ψ lam y) hlT
          have : par j lam (Ψ lam y) = y :=
            hΩinj lam hlam (hSΩ j hy'src) hyΩ hy'eq
          rw [this]
      calc X lam (Ψ lam y) = ∑ j, ψ j lam (Ψ lam y) • vel lam (par j lam (Ψ lam y)) := rfl
        _ = ∑ j, ψ j lam (Ψ lam y) • vel lam y := Finset.sum_congr rfl (fun j _ => hterm j)
        _ = (∑ j, ψ j lam (Ψ lam y)) • vel lam y := (Finset.sum_smul).symm
        _ = vel lam y := by rw [hsum1, one_smul]
    have hχ1 : χ (Ψ lam y) = 1 := hχone _ hmemχ
    have ha1 : Work.Whitney.CutPush.arcBump lam = 1 :=
      Work.Whitney.CutPush.arcBump_eq_one ⟨by linarith [hlam.1], by linarith [hlam.2]⟩
    simp only [V, hχ1, ha1, mul_one, one_smul]
    exact hXval
  -- ## the product field and its flow
  let Xhat : ℝ × EuclideanSpace ℝ (Fin m) → ℝ × EuclideanSpace ℝ (Fin m) :=
    fun p => ((1:ℝ), V p.1 p.2)
  have hXhat_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Xhat := by
    have h := (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : ℝ × EuclideanSpace ℝ (Fin m) => (1:ℝ))).prodMk hVsm
    simpa [Xhat] using h
  have hVd_cs : HasCompactSupport (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
      fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin m) => V q.1 q.2) p) := hVcs.fderiv (𝕜 := ℝ)
  obtain ⟨Lv, hLv⟩ := Work.ODE.exists_nnnorm_le_of_hasCompactSupport
    (hVsm.continuous_fderiv (by norm_num)) hVd_cs
  have hV_lip : LipschitzWith Lv (fun p : ℝ × EuclideanSpace ℝ (Fin m) => V p.1 p.2) :=
    lipschitzWith_of_nnnorm_fderiv_le (hVsm.differentiable (by norm_num)) hLv
  obtain ⟨Mv, _hMv0, hMv⟩ := Work.ODE.exists_norm_le_of_hasCompactSupport
    (f := fun p : ℝ × EuclideanSpace ℝ (Fin m) => V p.1 p.2) hVsm.continuous hVcs
  have hXhat_lip : LipschitzWith (max 0 Lv) Xhat := by
    refine LipschitzWith.of_dist_le_mul (fun p q => ?_)
    have h1 : dist (Xhat p).1 (Xhat q).1 = 0 := by simp [Xhat]
    have h2 : dist (Xhat p).2 (Xhat q).2 ≤ (Lv : ℝ) * dist p q := by
      simpa [Xhat] using hV_lip.dist_le_mul p q
    have h2' : dist (Xhat p).2 (Xhat q).2 ≤ (Lv : ℝ) * max (dist p.1 q.1) (dist p.2 q.2) := by
      rw [show max (dist p.1 q.1) (dist p.2 q.2) = dist p q from Prod.dist_eq.symm]
      exact h2
    rw [Prod.dist_eq, Prod.dist_eq, h1, max_eq_right (by positivity)]
    exact le_trans h2' (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_right (0 : NNReal) Lv) (by positivity))
  have hXhat_bd : ∀ z, ‖Xhat z‖ ≤ max 1 Mv := by
    intro z
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · simpa [Xhat] using le_max_left (1 : ℝ) Mv
    · simpa [Xhat] using le_trans (hMv z) (le_max_right (1 : ℝ) Mv)
  have hXhat_db : ∀ z, ‖fderiv ℝ Xhat z‖ ≤ ((max 0 Lv : NNReal) : ℝ) :=
    fun z => norm_fderiv_le_of_lipschitz ℝ hXhat_lip
  obtain ⟨FL, δf, hδfpos, hFL0, hFLsem, hFLint, hFLsmooth⟩ :=
    Work.Whitney.CutPush.exists_flow_of_lipschitz Xhat hXhat_sm hXhat_lip hXhat_bd hXhat_db
  have hFLfst : ∀ s p, (FL s p).1 = p.1 + s := by
    intro s p
    have hY : LipschitzWith 0 (fun _ : ℝ => (1:ℝ)) := LipschitzWith.const 1
    have hcurve1 : IsIntegralCurve (fun u : ℝ => (FL u p).1) (fun _ z => (1:ℝ)) := by
      intro u
      have h2 := ((hFLint p u).hasFDerivAt.fst).hasDerivAt
      simpa [Xhat] using h2
    have hcurve2 : IsIntegralCurve (fun u : ℝ => p.1 + u) (fun _ z => (1:ℝ)) := by
      intro u
      simpa using (hasDerivAt_id u).const_add p.1
    have heq := Work.ODE.eq_of_isIntegralCurve (X := fun _ : ℝ => (1:ℝ)) (L := 0) hY
      hcurve1 hcurve2 (t := 0) (by simp [hFL0])
    have := congrFun heq s
    simpa using this
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδfpos
  have hstep : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FL ((1:ℝ) / ((n:ℝ) + 1))) :=
    hFLsmooth _ (by rw [abs_of_pos (by positivity)]; exact le_of_lt hn)
  have hstepneg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FL (-((1:ℝ) / ((n:ℝ) + 1)))) :=
    hFLsmooth _ (by rw [abs_neg, abs_of_pos (by positivity)]; exact le_of_lt hn)
  have hiter : ∀ (k : ℕ) (r : ℝ) p, FL ((k:ℝ) * r) p = (FL r)^[k] p := by
    intro k
    induction k with
    | zero => intro r p; simp [hFL0]
    | succ k ih =>
      intro r p
      have h1 : ((k:ℝ) + 1) * r = r + (k:ℝ) * r := by ring
      rw [Nat.cast_succ, h1, hFLsem, ih, Function.iterate_succ_apply']
  have hFL1_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FL 1) := by
    have hpow : (FL 1) = (FL ((1:ℝ)/((n:ℝ)+1)))^[n+1] := by
      funext p
      have h1 : ((n:ℝ) + 1) * ((1:ℝ)/((n:ℝ)+1)) = 1 := by field_simp
      have h2 : ((n:ℝ) + 1) = (((n+1 : ℕ)) : ℝ) := by push_cast; ring
      calc FL 1 p = FL ((((n+1 : ℕ)) : ℝ) * ((1:ℝ)/((n:ℝ)+1))) p := by rw [← h2, h1]
        _ = (FL ((1:ℝ)/((n:ℝ)+1)))^[n+1] p := hiter (n+1) _ p
    rw [hpow]
    exact Work.Whitney.contDiff_iterate (n+1) hstep
  have hFLneg1_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FL (-1)) := by
    have hpow : (FL (-1)) = (FL (-((1:ℝ)/((n:ℝ)+1))))^[n+1] := by
      funext p
      have h1 : ((n:ℝ) + 1) * (-((1:ℝ)/((n:ℝ)+1))) = -1 := by field_simp
      have h2 : ((n:ℝ) + 1) = (((n+1 : ℕ)) : ℝ) := by push_cast; ring
      calc FL (-1) p = FL ((((n+1 : ℕ)) : ℝ) * (-((1:ℝ)/((n:ℝ)+1)))) p := by rw [← h2, h1]
        _ = (FL (-((1:ℝ)/((n:ℝ)+1))))^[n+1] p := hiter (n+1) _ p
    rw [hpow]
    exact Work.Whitney.contDiff_iterate (n+1) hstepneg
  let A : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) := fun y => (FL 1 ((0:ℝ), y)).2
  let Ainv : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun y => (FL (-1) ((1:ℝ), y)).2
  have hA_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (FL 1 ((0:ℝ), y)).2)
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin m) => FL 1 ((0:ℝ), y)) :=
      hFL1_sm.comp (contDiff_const.prodMk contDiff_id)
    exact h1.snd
  have hAinv_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (FL (-1) ((1:ℝ), y)).2)
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin m) => FL (-1) ((1:ℝ), y)) :=
      hFLneg1_sm.comp (contDiff_const.prodMk contDiff_id)
    exact h1.snd
  have hleft : Function.LeftInverse Ainv A := by
    intro y
    show (FL (-1) ((1:ℝ), (FL 1 ((0:ℝ), y)).2)).2 = y
    have h1 : FL 1 ((0:ℝ), y) = (1, (FL 1 ((0:ℝ), y)).2) := by
      refine Prod.ext ?_ rfl
      rw [hFLfst]; norm_num
    rw [← h1]
    have h2 := hFLsem (-1) 1 ((0:ℝ), y)
    rw [show (-1:ℝ) + 1 = 0 by norm_num, hFL0] at h2
    exact (congrArg Prod.snd h2).symm
  have hright : Function.RightInverse Ainv A := by
    intro y
    show (FL 1 ((0:ℝ), (FL (-1) ((1:ℝ), y)).2)).2 = y
    have h1 : FL (-1) ((1:ℝ), y) = (0, (FL (-1) ((1:ℝ), y)).2) := by
      refine Prod.ext ?_ rfl
      rw [hFLfst]; norm_num
    rw [← h1]
    have h2 := hFLsem 1 (-1) ((1:ℝ), y)
    rw [show (1:ℝ) + -1 = 0 by norm_num, hFL0] at h2
    exact (congrArg Prod.snd h2).symm
  -- ## the diffeomorphism is the identity off `U`
  have hVzero : ∀ z, z ∉ U → ∀ lam, V lam z = 0 := by
    intro z hzU lam
    have hχz : χ z = 0 := by
      by_contra hne
      exact hzU (hχsupp (subset_tsupport _ hne))
    simp [V, hχz]
  have hAoff : ∀ y, y ∉ U → A y = y := by
    intro y hy
    have hcurve : IsIntegralCurve (fun s : ℝ => (s, y)) (fun _ z => Xhat z) := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ => (s, y)) (1, (0 : EuclideanSpace ℝ (Fin m))) s :=
        (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
      have h1' : HasDerivAt (fun s : ℝ => (s, y)) (Xhat (s, y)) s := by
        simpa [Xhat, hVzero y hy s] using h1
      exact h1'
    have hflow : IsIntegralCurve (fun s : ℝ => FL s ((0:ℝ), y)) (fun _ z => Xhat z) :=
      hFLint ((0:ℝ), y)
    have hagree : (fun s : ℝ => (s, y)) 0 = (fun s : ℝ => FL s ((0:ℝ), y)) 0 := by simp [hFL0]
    have heq := Work.ODE.eq_of_isIntegralCurve hXhat_lip hcurve hflow hagree
    have hval := congrFun heq 1
    show (FL (1:ℝ) ((0:ℝ), y)).2 = y
    have := congrArg Prod.snd hval
    simpa using this.symm
  -- ## comparison with the flow on the region whose orbit stays patched
  let P : Set (ℝ × EuclideanSpace ℝ (Fin m)) :=
    Metric.thickening δ T ∩ (Set.univ ×ˢ Metric.thickening δχ Timg)
  have hPopen : IsOpen P :=
    (Metric.isOpen_thickening).inter (isOpen_univ.prod Metric.isOpen_thickening)
  have hPtrail : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      (lam, Ψ lam (γ t)) ∈ P := by
    intro t ht lam hlam
    refine ⟨Metric.self_subset_thickening hδpos T ⟨lam, hlam, t, ht, rfl⟩, ?_⟩
    exact Set.mem_prod.mpr ⟨trivial, Metric.self_subset_thickening hδχpos Timg
      ⟨lam, hlam, t, ht, rfl⟩⟩
  have hMnbhd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ ε, 0 < ε ∧ ∀ y, ‖y - γ t‖ < ε →
      (y ∈ Ω ∧ ∀ lam, lam ∈ Set.Icc (0 : ℝ) 1 → (lam, Ψ lam y) ∈ P) := by
    intro t ht
    obtain ⟨ε₁, hε₁pos, hε₁⟩ := exists_tube_radius Ψ hΨsm.continuous P hPopen (γ t) (hPtrail t ht)
    obtain ⟨ε₂, hε₂pos, hε₂⟩ := (Metric.isOpen_iff.mp hΩopen) (γ t) (hΩarc t ht)
    refine ⟨min ε₁ ε₂, lt_min hε₁pos hε₂pos, fun y hy => ⟨?_, ?_⟩⟩
    · exact hε₂ (Metric.mem_ball.mpr
        (by rw [dist_eq_norm]; exact lt_of_lt_of_le hy (min_le_right _ _)))
    · intro lam hlam
      exact hε₁ lam hlam y (lt_of_lt_of_le hy (min_le_left _ _))
  have hAgree : ∀ y, y ∈ Ω → (∀ lam, lam ∈ Set.Icc (0 : ℝ) 1 → (lam, Ψ lam y) ∈ P) →
      A y = Ψ 1 y := by
    intro y hyΩ hytraj
    have hfderiv : ∀ u ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun u : ℝ => (u, Ψ u y)) (Xhat ((u, Ψ u y))) u := by
      intro u hu
      have h1 : HasDerivAt (fun u : ℝ => Ψ u y) (vel u y) u :=
        hasDerivAt_section (fun p : ℝ × EuclideanSpace ℝ (Fin m) => Ψ p.1 p.2) y
          (hΨsm.differentiable (by simp) (u, y))
      have h2 : HasDerivAt (fun u : ℝ => (u, Ψ u y)) ((1:ℝ), vel u y) u :=
        (hasDerivAt_id u).prodMk h1
      have h3 : ((1:ℝ), vel u y) = Xhat ((u, Ψ u y)) := by
        have h4 := hmat u hu y hyΩ (hytraj u hu).1 (Set.mem_prod.mp (hytraj u hu).2).2
        simp only [Xhat]
        rw [h4]
      rw [← h3]
      exact h2
    have hf : ∀ u ∈ Set.Ico (0 : ℝ) 1,
        HasDerivWithinAt (fun u : ℝ => (u, Ψ u y)) (Xhat ((u, Ψ u y))) (Set.Ici u) u :=
      fun u hu => (hfderiv u (Set.Ico_subset_Icc_self hu)).hasDerivWithinAt
    have hg : ∀ u ∈ Set.Ico (0 : ℝ) 1,
        HasDerivWithinAt (fun u : ℝ => FL u ((0:ℝ), y)) (Xhat (FL u ((0:ℝ), y))) (Set.Ici u) u :=
      fun u _ => (hFLint ((0:ℝ), y) u).hasDerivWithinAt
    have hcont_f : ContinuousOn (fun u : ℝ => (u, Ψ u y)) (Set.Icc (0 : ℝ) 1) := by
      refine Continuous.continuousOn ?_
      exact continuous_id.prodMk ((hΨsm.continuous.comp
        (continuous_id.prodMk continuous_const)))
    have hcont_g : ContinuousOn (fun u : ℝ => FL u ((0:ℝ), y)) (Set.Icc (0 : ℝ) 1) := by
      refine Continuous.continuousOn ?_
      rw [continuous_iff_continuousAt]
      intro u
      exact (hFLint ((0:ℝ), y) u).differentiableAt.continuousAt
    have heq := ODE_solution_unique (v := fun _ z => Xhat z) (K := max 0 Lv)
      (f := fun u : ℝ => (u, Ψ u y)) (g := fun u : ℝ => FL u ((0:ℝ), y))
      (a := 0) (b := 1) (fun _ => hXhat_lip) hcont_f hf hcont_g hg (by simp [hFL0, hΨ0])
    have h1 : ((1:ℝ), Ψ 1 y) = FL 1 ((0:ℝ), y) :=
      heq (by norm_num : (1:ℝ) ∈ Set.Icc (0 : ℝ) 1)
    show (FL (1:ℝ) ((0:ℝ), y)).2 = Ψ 1 y
    exact (congrArg Prod.snd h1).symm
  refine ⟨A, Ainv, hA_sm, hAinv_sm, hleft, hright, hAoff, ?_⟩
  intro t ht
  obtain ⟨ε, hεpos, hε⟩ := hMnbhd t ht
  have hnb : A =ᶠ[𝓝 (γ t)] (fun y => Ψ 1 y) := by
    filter_upwards [Metric.ball_mem_nhds (γ t) hεpos] with y hy
    exact hAgree y (hε y hy).1 (hε y hy).2
  exact hnb.fderiv_eq


theorem localIsotopyGlobalisation {m : ℕ}
    (γ : ℝ → EuclideanSpace ℝ (Fin m))
    (Ψ : ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (Y : ℝ → ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (U : Set (EuclideanSpace ℝ (Fin m)))
    (hγsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hΨsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × EuclideanSpace ℝ (Fin m) => Ψ p.1 p.2))
    (hYsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => Y p.1 p.2))
    (hU : IsOpen U) (hUsub : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ U)
    (hΨ0 : ∀ y, Ψ 0 y = y)
    (hYinv : ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Bijective (Y lam t))
    (hjet : ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      fderiv ℝ (Ψ lam) (γ t) = Y lam t)
    (htrail : ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, Ψ lam (γ t) ∈ U)
    (hsep : ∀ lam ∈ Set.Icc (0 : ℝ) 1, Set.InjOn (fun t : ℝ => Ψ lam (γ t)) (Set.Icc (0 : ℝ) 1))
    (hreg : ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      fderiv ℝ (fun s : ℝ => Ψ lam (γ s)) t 1 ≠ 0) :
    ∃ (A Ainv : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
      Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
      (∀ y, y ∉ U → A y = y) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, fderiv ℝ A (γ t) = Y 1 t) := by
  classical
  -- ## the differential of the family along the arc is invertible
  have hinv : ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Function.Bijective (fderiv ℝ (Ψ lam) (γ t)) := by
    intro lam hlam t ht
    rw [hjet lam hlam t ht]
    exact hYinv lam hlam t ht
  -- ## uniform injectivity near the arc
  obtain ⟨Ω, hΩopen, hΩarc, hΩinj⟩ :=
    uniformInjOnNearArc Ψ hΨsm γ hγsm hsep hinv
  -- ## local inverse data at every point of the parameter square
  have hpt : ∀ p : ↥(Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1),
      ∃ (O : Set ℝ) (Os : Set (EuclideanSpace ℝ (Fin m)))
        (Ot : Set (EuclideanSpace ℝ (Fin m)))
        (par : ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)),
        IsOpen O ∧ (p : ℝ × ℝ).1 ∈ O ∧ IsOpen Os ∧ γ (p : ℝ × ℝ).2 ∈ Os ∧ Os ⊆ Ω ∧
        IsOpen Ot ∧ Ψ (p : ℝ × ℝ).1 (γ (p : ℝ × ℝ).2) ∈ Ot ∧
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry par) (O ×ˢ Ot) ∧
        (∀ lam ∈ O, ∀ y ∈ Os, par lam (Ψ lam y) = y) ∧
        (∀ lam ∈ O, ∀ z ∈ Ot, par lam z ∈ Os ∧ Ψ lam (par lam z) = z) := by
    intro p
    have hp1 : (p : ℝ × ℝ).1 ∈ Set.Icc (0 : ℝ) 1 := p.2.1
    have hp2 : (p : ℝ × ℝ).2 ∈ Set.Icc (0 : ℝ) 1 := p.2.2
    have hbij : Function.Bijective (fun v : EuclideanSpace ℝ (Fin m) =>
        fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin m) => Ψ q.1 q.2)
          ((p : ℝ × ℝ).1, γ ((p : ℝ × ℝ).2)) (0, v)) := by
      have heq : (fun v : EuclideanSpace ℝ (Fin m) =>
          fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin m) => Ψ q.1 q.2)
            ((p : ℝ × ℝ).1, γ ((p : ℝ × ℝ).2)) (0, v))
          = fun v => fderiv ℝ (Ψ ((p : ℝ × ℝ).1)) (γ ((p : ℝ × ℝ).2)) v := by
        funext v
        exact fderiv_uncurry_snd (fun q : ℝ × EuclideanSpace ℝ (Fin m) => Ψ q.1 q.2)
          ((hΨsm.differentiable (by simp)) ((p : ℝ × ℝ).1, γ ((p : ℝ × ℝ).2))) v
      rw [heq]
      exact hinv _ hp1 _ hp2
    obtain ⟨O, Os, Ot, par, hO, hmO, hOs, hmOs, hsub, hOt, hmOt, hsm, hL, hR⟩ :=
      localInverseFamilyTwoSided_repair (fun q : ℝ × EuclideanSpace ℝ (Fin m) => Ψ q.1 q.2)
        Set.univ isOpen_univ ((p : ℝ × ℝ).1) (γ ((p : ℝ × ℝ).2)) (mem_univ _)
        (hΨsm.contDiffOn (s := Set.univ)) hbij Ω hΩopen (hΩarc _ hp2)
    exact ⟨O, Os, Ot, par, hO, hmO, hOs, hmOs, hsub, hOt, hmOt, hsm, hL, hR⟩
  choose O Os Ot par hO hmO hOs hmOs hsub hOt hmOt hsm hL hR using hpt
  -- ## finitely many boxes cover the trail
  set cover : ↥(Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) → Set (ℝ × ℝ) :=
    fun p => {q : ℝ × ℝ | q.1 ∈ O p ∧ Ψ q.1 (γ q.2) ∈ Ot p}
  have hcoveropen : ∀ p, IsOpen (cover p) := by
    intro p
    have h1 : IsOpen {q : ℝ × ℝ | q.1 ∈ O p} := (hO p).preimage continuous_fst
    have h2 : IsOpen {q : ℝ × ℝ | Ψ q.1 (γ q.2) ∈ Ot p} :=
      (hOt p).preimage (hΨsm.continuous.comp
        (continuous_fst.prodMk (hγsm.continuous.comp continuous_snd)))
    exact h1.inter h2
  have hcoversub : (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ⊆ ⋃ p, cover p := by
    rintro ⟨lam, t⟩ ⟨hlam, ht⟩
    let p₀ : ↥(Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := ⟨(lam, t), ⟨hlam, ht⟩⟩
    refine Set.mem_iUnion.mpr ⟨p₀, ?_⟩
    exact ⟨hmO p₀, hmOt p₀⟩
  obtain ⟨s, hs⟩ :=
    (isCompact_Icc.prod isCompact_Icc).elim_finite_subcover cover hcoveropen hcoversub
  -- ## the engine
  obtain ⟨A, Ainv, hA, hAinv, hl, hr, hoff, hjet'⟩ :=
    exists_diffeo_of_localInverseData γ Ψ U hγsm hΨsm hU htrail hΨ0 Ω hΩopen hΩarc hΩinj
      (fun j : ↥s => O j) (fun j : ↥s => Os j) (fun j : ↥s => Ot j) (fun j : ↥s => par j)
      (fun j => hO j) (fun j => hOs j) (fun j => hOt j) (fun j => hsub j)
      (fun j => hsm j) (fun j => hR j)
      (by
        intro lam hlam t ht
        have hmem : (lam, t) ∈ ⋃ p ∈ s, cover p := hs ⟨hlam, ht⟩
        rcases Set.mem_iUnion.mp hmem with ⟨p, hp⟩
        rcases Set.mem_iUnion.mp hp with ⟨hps, hpc⟩
        exact ⟨⟨p, hps⟩, hpc.1, hpc.2⟩)
  refine ⟨A, Ainv, hA, hAinv, hl, hr, hoff, ?_⟩
  intro t ht
  rw [hjet' t ht, hjet 1 (by norm_num) t ht]

end Work.Drive.PushDisc
