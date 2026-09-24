import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.Work.Drive.DipoleHelpers
import Submission.Work.PoleMoving.exists_twoPole_exhaustion
import Submission.Work.Drive.kishiNormalizedGreenBounded
import Submission.Work.Drive.greenSymmetryRegion
import Submission.Work.Drive.normalizedGreenExhaustion_locallyBounded
import Submission.Work.Drive.harmonicMontelEventually
import Submission.Work.Drive.hasLogPoleOn_of_isGreenOn_limit
import Submission.Work.Drive.harmonicOnX_extension_off_pair

open Filter Set
open scoped Topology Manifold

namespace Work.Drive



set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]


/-- Reindexing a locally uniform limit along a strictly monotone subsequence. -/
theorem tendstoLocallyUniformlyOn_comp_subseq {F : ℕ → X → ℝ} {f : X → ℝ} {s : Set X}
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (h : TendstoLocallyUniformlyOn F f atTop s) :
    TendstoLocallyUniformlyOn (fun k => F (σ k)) f atTop s := by
  intro u hu x hx
  obtain ⟨t, ht, ht'⟩ := h u hu x hx
  refine ⟨t, ht, ?_⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ht'
  exact Filter.eventually_atTop.mpr ⟨N, fun k hk => hN (σ k) (le_trans hk (hσ.id_le k))⟩

/-- The frontier of `Ω \ A` sits in `frontier Ω ∪ frontier A`. -/
theorem frontier_sdiff_subset_union_local {Ω A : Set X} :
    frontier (Ω \ A) ⊆ frontier Ω ∪ frontier A := by
  intro ξ hξ
  rw [frontier_eq_closure_inter_closure] at hξ
  obtain ⟨h1, h2⟩ := hξ
  rw [mem_closure_iff] at h1 h2
  by_cases hA : ξ ∈ closure A
  · right
    refine ⟨hA, fun hint => ?_⟩
    obtain ⟨y, hyA⟩ := h1 (interior A) isOpen_interior hint
    exact hyA.2.2 (interior_subset hyA.1)
  · left
    have hξAcl : ξ ∉ closure A := hA
    refine ⟨?_, ?_⟩
    · rw [mem_closure_iff]
      intro o ho hξo
      obtain ⟨y, hy, hyΩA⟩ := h1 o ho hξo
      exact ⟨y, hy, hyΩA.1⟩
    · intro hint
      have hcompl : (Ω \ A)ᶜ = Ωᶜ ∪ A := by
        ext y
        simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_union]
        tauto
      rw [hcompl] at h2
      have ho : IsOpen (interior Ω \ closure A) := isOpen_interior.sdiff isClosed_closure
      obtain ⟨y, hy, hy2⟩ := h2 (interior Ω \ closure A) ho ⟨hint, hξAcl⟩
      have hyA' : y ∉ A := fun h => hy.2 (subset_closure h)
      rcases hy2 with h | h
      · exact h (interior_subset hy.1)
      · exact hyA' h

/-- A compact set lies in some member of a covering exhaustion. -/
theorem exists_subset_iUnion_of_isCompact_asm {Ω : ℕ → Set X} (hΩo : ∀ n, IsOpen (Ω n))
    (hmono : ∀ n, Ω n ⊆ Ω (n + 1)) (hcov : (⋃ n, Ω n) = Set.univ) {K : Set X}
    (hK : IsCompact K) : ∃ N : ℕ, K ⊆ Ω N := by
  classical
  have hmono' : ∀ m n : ℕ, m ≤ n → Ω m ⊆ Ω n := by
    intro m n hmn
    induction hmn with
    | refl => exact subset_rfl
    | step h ih => exact ih.trans (hmono _)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover Ω hΩo (by rw [hcov]; exact subset_univ K)
  rcases t.eq_empty_or_nonempty with rfl | hne
  · refine ⟨0, fun x hx => ?_⟩
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.mp (ht hx)
    exact absurd hi (Finset.notMem_empty i)
  · exact ⟨t.max' hne, fun x hx => by
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
      exact hmono' i (t.max' hne) (Finset.le_max' t i hi) hxi⟩

/-- **Far-field bound for the pair functions of a pair exhaustion, from the one-sided
comparison at the poles.** -/
theorem pairFarField_of_oneSided_le {a b : X} (hab : a ≠ b) {Ω : ℕ → Set X} {gA gB : ℕ → X → ℝ}
    (hΩo : ∀ n, IsOpen (Ω n)) (hΩc : ∀ n, IsCompact (closure (Ω n)))
    (hnest : ∀ n, closure (Ω n) ⊆ Ω (n + 1)) (hcov : (⋃ n, Ω n) = Set.univ)
    (haΩ : ∀ n, a ∈ Ω n) (hbΩ : ∀ n, b ∈ Ω n)
    (hgA : ∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) a (gA n))
    (hgB : ∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) b (gB n))
    (hzA : ∀ n, ∀ x, x ∉ Ω n → gA n x = 0) (hzB : ∀ n, ∀ x, x ∉ Ω n → gB n x = 0)
    (hone : ∀ n, gB n a ≤ gA n b) :
    ∃ C : ℝ, ∀ n, ∀ x : X, x ∈ Ω n → x ∉ closure (Ω 0) →
      (gA n x - gA n b) - (gB n x - gB n a) ≤ C := by
  classical
  have hmono : ∀ n, Ω n ⊆ Ω (n + 1) := fun n => subset_closure.trans (hnest n)
  have hmono' : ∀ m n : ℕ, m ≤ n → Ω m ⊆ Ω n := by
    intro m n hmn
    induction hmn with
    | refl => exact subset_rfl
    | step h ih => exact ih.trans (hmono _)
  have hKA := fun K hK hKsub =>
    normalizedGreenExhaustion_locallyBounded (X := X) (a := a) (x₁ := b) hab.symm hΩo hΩc hmono
      hcov hgA hzA K hK hKsub
  have hKB := fun K hK hKsub =>
    normalizedGreenExhaustion_locallyBounded (X := X) (a := b) (x₁ := a) hab hΩo hΩc hmono
      hcov hgB hzB K hK hKsub
  have hFc : IsCompact (frontier (closure (Ω 0))) :=
    IsCompact.of_isClosed_subset (hΩc 0) isClosed_frontier
      (by simpa [closure_closure] using
        (frontier_subset_closure : frontier (closure (Ω 0)) ⊆ closure (closure (Ω 0))))
  have haF : a ∈ interior (closure (Ω 0)) :=
    mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset ((hΩo 0).mem_nhds (haΩ 0)) subset_closure)
  have hbF : b ∈ interior (closure (Ω 0)) :=
    mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset ((hΩo 0).mem_nhds (hbΩ 0)) subset_closure)
  have hFa : frontier (closure (Ω 0)) ⊆ Set.univ \ {a} := fun x hx =>
    ⟨mem_univ x, fun h => hx.2 (h ▸ haF)⟩
  have hFb : frontier (closure (Ω 0)) ⊆ Set.univ \ {b} := fun x hx =>
    ⟨mem_univ x, fun h => hx.2 (h ▸ hbF)⟩
  obtain ⟨CA, hCA⟩ := hKA _ hFc hFa
  obtain ⟨CB, hCB⟩ := hKB _ hFc hFb
  refine ⟨max (CA + CB) 0, ?_⟩
  intro n x hxΩ hxfar
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    exact absurd (subset_closure hxΩ) hxfar
  · have hclΩn : closure (Ω 0) ⊆ Ω n := (hnest 0).trans (hmono' 1 n hn)
    set U : Set X := Ω n \ closure (Ω 0) with hUdef
    have hUopen : IsOpen U := (hΩo n).sdiff isClosed_closure
    have hUcomp : IsCompact (closure U) :=
      IsCompact.of_isClosed_subset (hΩc n) isClosed_closure
        (by rw [hUdef]; exact closure_minimal (fun y hy => subset_closure hy.1) isClosed_closure)
    have hUne : U.Nonempty := ⟨x, hxΩ, hxfar⟩
    have hUneuniv : U ≠ Set.univ := by
      intro h
      have haU : a ∈ U := by rw [h]; exact mem_univ a
      exact haU.2 (subset_closure (haΩ 0))
    have hFrne : (frontier U).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hempty
      rcases (frontier_eq_empty_iff.mp hempty) with h | h
      · exact hUne.ne_empty h
      · exact hUneuniv h
    have hharm : Submission.HarmonicOnX (fun y => (gA n y - gA n b) - (gB n y - gB n a)) U := by
      have h1 : Submission.HarmonicOnX (fun y => gA n y - gA n b) U :=
        ((hgA n).2.1.mono (fun y hy => ⟨hy.1, fun h => hy.2 (h ▸ subset_closure (haΩ 0))⟩)).sub
          (Submission.harmonicOnX_const (gA n b))
      have h2 : Submission.HarmonicOnX (fun y => gB n y - gB n a) U :=
        ((hgB n).2.1.mono (fun y hy => ⟨hy.1, fun h => hy.2 (h ▸ subset_closure (hbΩ 0))⟩)).sub
          (Submission.harmonicOnX_const (gB n a))
      exact h1.sub h2
    refine Submission.SubharmonicOnX.le_of_frontier_limsup hUopen
      (hharm.subharmonic (fun y hy => (hharm y hy).continuousAt.continuousWithinAt)) hUcomp hFrne ?_
      x ⟨hxΩ, hxfar⟩
    intro ξ hξ ε hε
    have hξ' : ξ ∈ frontier (Ω n) ∪ frontier (closure (Ω 0)) :=
      frontier_sdiff_subset_union_local hξ
    rcases hξ' with hξfr | hξcl
    · have hξΩn : ξ ∉ Ω n := fun h => hξfr.2 ((hΩo n).interior_eq.symm ▸ h)
      have hlimA : ∀ᶠ y in 𝓝[Ω n] ξ, gA n y < ε / 4 := by
        obtain ⟨KA, hKAc, hKAΩ, hKAlt⟩ := (hgA n).2.2.1 (ε/4) (by linarith)
        have hξKA : ξ ∉ KA := fun h => hξΩn (hKAΩ h)
        have h1 : ∀ᶠ y in 𝓝[Ω n] ξ, y ∉ KA :=
          Filter.Eventually.filter_mono nhdsWithin_le_nhds
            (hKAc.isClosed.isOpen_compl.mem_nhds hξKA)
        filter_upwards [h1, self_mem_nhdsWithin] with y hy hyΩ
        exact hKAlt y hyΩ hy
      have hlimB : ∀ᶠ y in 𝓝[Ω n] ξ, gB n y < ε / 4 := by
        obtain ⟨KB, hKBc, hKBΩ, hKBlt⟩ := (hgB n).2.2.1 (ε/4) (by linarith)
        have hξKB : ξ ∉ KB := fun h => hξΩn (hKBΩ h)
        have h1 : ∀ᶠ y in 𝓝[Ω n] ξ, y ∉ KB :=
          Filter.Eventually.filter_mono nhdsWithin_le_nhds
            (hKBc.isClosed.isOpen_compl.mem_nhds hξKB)
        filter_upwards [h1, self_mem_nhdsWithin] with y hy hyΩ
        exact hKBlt y hyΩ hy
      filter_upwards [Filter.Eventually.filter_mono (nhdsWithin_mono ξ sdiff_subset) hlimA,
        Filter.Eventually.filter_mono (nhdsWithin_mono ξ sdiff_subset) hlimB,
        self_mem_nhdsWithin] with y hyA hyB hyU
      have hgb0 : 0 < gB n y := (hgB n).1 y hyU.1 (fun h => hyU.2 (h ▸ subset_closure (hbΩ 0)))
      have hnonneg : 0 ≤ gA n b - gB n a := by linarith [hone n]
      have hkey : (gA n y - gA n b) - (gB n y - gB n a)
          = (gA n y - gB n y) - (gA n b - gB n a) := by ring
      rw [hkey]
      linarith [hyA, hyB, hgb0, le_max_right (CA + CB) 0]
    · have h1 := hCA n ξ hξcl
      have h2 := hCB n ξ hξcl
      have hbound : (gA n ξ - gA n b) - (gB n ξ - gB n a) ≤ max (CA + CB) 0 := by
        have h1' := abs_le.mp h1
        have h2' := abs_le.mp h2
        have : (gA n ξ - gA n b) - (gB n ξ - gB n a) ≤ CA + CB := by linarith [h1'.2, h2'.1]
        exact le_trans this (le_max_left _ _)
      have hξne_a : ξ ≠ a := fun h => (hFa hξcl).2 (by simpa using h)
      have hξne_b : ξ ≠ b := fun h => (hFb hξcl).2 (by simpa using h)
      have hcont : ContinuousAt (fun y => (gA n y - gA n b) - (gB n y - gB n a)) ξ := by
        refine ContinuousAt.sub ?_ ?_
        · exact (((hgA n).2.1 ξ ⟨hclΩn (by simpa [closure_closure] using hξcl.1),
            by simpa using hξne_a⟩).continuousAt).sub continuousAt_const
        · exact (((hgB n).2.1 ξ ⟨hclΩn (by simpa [closure_closure] using hξcl.1),
            by simpa using hξne_b⟩).continuousAt).sub continuousAt_const
      refine hcont.continuousWithinAt.eventually (eventually_le_nhds ?_)
      linarith [hbound, hε]


/-- **The assembly.** -/
theorem exists_matched_of_oneSided_le {a b : X} (hab : a ≠ b) {Ω : ℕ → Set X} {gA gB : ℕ → X → ℝ}
    (hΩo : ∀ n, IsOpen (Ω n)) (hΩc : ∀ n, IsCompact (closure (Ω n)))
    (hnest : ∀ n, closure (Ω n) ⊆ Ω (n + 1)) (hcov : (⋃ n, Ω n) = Set.univ)
    (haΩ : ∀ n, a ∈ Ω n) (hbΩ : ∀ n, b ∈ Ω n)
    (hgA : ∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) a (gA n))
    (hgB : ∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) b (gB n))
    (hzA : ∀ n, ∀ x, x ∉ Ω n → gA n x = 0) (hzB : ∀ n, ∀ x, x ∉ Ω n → gB n x = 0)
    (hone : ∀ n, gB n a ≤ gA n b) :
    ∃ Ea Eb : X → ℝ,
      Submission.HarmonicOnX Ea (Set.univ \ {a}) ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {a}) a Ea ∧
      Submission.HarmonicOnX Eb (Set.univ \ {b}) ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {b}) b Eb ∧
      ∃ K : Set X, IsCompact K ∧ ∀ x : X, x ∉ K → Ea x - Eb x ≤ 1 := by
  classical
  have hLC : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  haveI := hLC
  have hmono : ∀ n, Ω n ⊆ Ω (n + 1) := fun n => subset_closure.trans (hnest n)
  have hmono' : ∀ m n : ℕ, m ≤ n → Ω m ⊆ Ω n := by
    intro m n hmn
    induction hmn with
    | refl => exact subset_rfl
    | step h ih => exact ih.trans (hmono _)
  have hKA : ∀ K : Set X, IsCompact K → K ⊆ Set.univ \ {a} → ∃ C, ∀ n, ∀ x ∈ K,
      |gA n x - gA n b| ≤ C := fun K hK hKsub =>
    normalizedGreenExhaustion_locallyBounded (X := X) (a := a) (x₁ := b) hab.symm hΩo hΩc hmono
      hcov hgA hzA K hK hKsub
  have hKB : ∀ K : Set X, IsCompact K → K ⊆ Set.univ \ {b} → ∃ C, ∀ n, ∀ x ∈ K,
      |gB n x - gB n a| ≤ C := fun K hK hKsub =>
    normalizedGreenExhaustion_locallyBounded (X := X) (a := b) (x₁ := a) hab hΩo hΩc hmono
      hcov hgB hzB K hK hKsub
  -- the pole controls
  obtain ⟨Ca, sa, hsa, hsub_a, hCa⟩ :=
    kishiLogPoleBound (X := X) (a := a) (x₁ := b) hab.symm (hΩo 0) hmono (haΩ 0) (hbΩ 0) hgA hKA
  obtain ⟨Cb, sb, hsb, hsub_b, hCb⟩ :=
    kishiLogPoleBound (X := X) (a := b) (x₁ := a) hab (hΩo 0) hmono (hbΩ 0) (haΩ 0) hgB hKB
  -- the far-field bound for the pair functions
  obtain ⟨Cff, hCff⟩ :=
    pairFarField_of_oneSided_le (X := X) hab hΩo hΩc hnest hcov haΩ hbΩ hgA hgB hzA hzB hone
  -- ## Montel on the `a`-family
  have hevA : ∀ K ⊆ (Set.univ \ {a} : Set X), IsCompact K → ∃ O, IsOpen O ∧ K ⊆ O ∧
      O ⊆ Set.univ \ {a} ∧ ∃ N, ∀ n ≥ N,
        Submission.HarmonicOnX (fun x => gA n x - gA n b) O := by
    intro K hKsub hK
    obtain ⟨N, hN⟩ := exists_subset_iUnion_of_isCompact_asm hΩo hmono hcov hK
    refine ⟨Ω N \ {a}, (hΩo N).sdiff isClosed_singleton, fun x hx => ⟨hN hx, (hKsub hx).2⟩,
      fun x hx => ⟨mem_univ x, hx.2⟩, N, fun n hn => ?_⟩
    exact ((hgA n).2.1.mono (fun y hy => ⟨hmono' N n hn hy.1, hy.2⟩)).sub
      (Submission.harmonicOnX_const (gA n b))
  have hbddA : ∀ K ⊆ (Set.univ \ {a} : Set X), IsCompact K → ∃ C, ∀ n, ∀ x ∈ K,
      |(fun x => gA n x - gA n b) x| ≤ C := fun K hKsub hK => hKA K hK hKsub
  obtain ⟨φ, Ea, hφ, hEaharm, hEaconv⟩ :=
    harmonicMontelEventually (X := X) (Y := Set.univ \ {a})
      (by
        have h : (Set.univ \ ({a} : Set X)) = ({a} : Set X)ᶜ := by
          ext x
          simp [Set.mem_sdiff]
        rw [h]
        exact isOpen_compl_singleton) hevA hbddA
  -- ## Montel on the `b`-family along the subsequence `φ`
  have hevB : ∀ K ⊆ (Set.univ \ {b} : Set X), IsCompact K → ∃ O, IsOpen O ∧ K ⊆ O ∧
      O ⊆ Set.univ \ {b} ∧ ∃ N, ∀ k ≥ N,
        Submission.HarmonicOnX (fun x => gB (φ k) x - gB (φ k) a) O := by
    intro K hKsub hK
    obtain ⟨M, hM⟩ := exists_subset_iUnion_of_isCompact_asm hΩo hmono hcov hK
    refine ⟨Ω M \ {b}, (hΩo M).sdiff isClosed_singleton, fun x hx => ⟨hM hx, (hKsub hx).2⟩,
      fun x hx => ⟨mem_univ x, hx.2⟩, M, fun k hk => ?_⟩
    have hkM : M ≤ φ k := le_trans hk (hφ.id_le k)
    exact ((hgB (φ k)).2.1.mono (fun y hy => ⟨hmono' M (φ k) hkM hy.1, hy.2⟩)).sub
      (Submission.harmonicOnX_const (gB (φ k) a))
  have hbddB : ∀ K ⊆ (Set.univ \ {b} : Set X), IsCompact K → ∃ C, ∀ k, ∀ x ∈ K,
      |(fun x => gB (φ k) x - gB (φ k) a) x| ≤ C := by
    intro K hKsub hK
    obtain ⟨C, hC⟩ := hKB K hK hKsub
    exact ⟨C, fun k x hx => hC (φ k) x hx⟩
  obtain ⟨σ, Eb, hσ, hEbharm, hEbconv⟩ :=
    harmonicMontelEventually (X := X) (Y := Set.univ \ {b})
      (by
        have h : (Set.univ \ ({b} : Set X)) = ({b} : Set X)ᶜ := by
          ext x
          simp [Set.mem_sdiff]
        rw [h]
        exact isOpen_compl_singleton) hevB hbddB
  -- ## the `a`-family along `φ ∘ σ` still converges to `Ea`
  have hEaconv' : TendstoLocallyUniformlyOn (fun k x => gA (φ (σ k)) x - gA (φ (σ k)) b)
      Ea atTop (Set.univ \ {a}) :=
    tendstoLocallyUniformlyOn_comp_subseq hσ hEaconv
  -- ## the pair functions along `φ ∘ σ` converge to `Ea - Eb`
  have hpsiconv : TendstoLocallyUniformlyOn
      (fun k x => (gA (φ (σ k)) x - gA (φ (σ k)) b) - (gB (φ (σ k)) x - gB (φ (σ k)) a))
      (Ea - Eb) atTop (Set.univ \ {a, b}) :=
    (hEaconv'.mono (fun x hx => ⟨hx.1, fun h => hx.2 (Or.inl h)⟩)).sub
      (hEbconv.mono (fun x hx => ⟨hx.1, fun h => hx.2 (Or.inr h)⟩))
  -- ## the poles
  have hEapole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {a}) a Ea :=
    hasLogPoleOn_of_isGreenOn_limit (X := X) (a := a) (x₁ := b) haΩ hΩo hmono hgA hEaconv hKA
  have hEbpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {b}) b Eb :=
    hasLogPoleOn_of_isGreenOn_limit (X := X) (a := b) (x₁ := a) hbΩ hΩo hmono hgB hEbconv hKB
  -- ## the far-field bound
  have hfar : ∀ x : X, x ∉ closure (Ω 0) → Ea x - Eb x ≤ max Cff 0 := by
    intro x hx
    have h1 : ∀ᶠ k in atTop, x ∈ Ω (φ (σ k)) := by
      obtain ⟨N, hN⟩ := exists_subset_iUnion_of_isCompact_asm hΩo hmono hcov (isCompact_singleton (x := x))
      refine Filter.eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
      refine hmono' N (φ (σ k)) ?_ (hN (show x ∈ ({x} : Set X) from rfl))
      exact le_trans hk (le_trans (hσ.id_le k) (hφ.id_le (σ k)))
    have h2 : ∀ᶠ k in atTop, (gA (φ (σ k)) x - gA (φ (σ k)) b)
        - (gB (φ (σ k)) x - gB (φ (σ k)) a) ≤ max Cff 0 := by
      filter_upwards [h1] with k hk
      exact le_trans (hCff (φ (σ k)) x hk hx) (le_max_left _ _)
    have hxa : x ≠ a := fun h => hx (by rw [h]; exact subset_closure (haΩ 0))
    have hxb : x ≠ b := fun h => hx (by rw [h]; exact subset_closure (hbΩ 0))
    exact le_of_tendsto (hpsiconv.tendsto_at ⟨mem_univ x, by simp [hxa, hxb]⟩) h2
  refine ⟨fun x => Ea x - (max Cff 0 - 1), Eb, ?_, ?_, hEbharm, hEbpole, closure (Ω 0), hΩc 0, ?_⟩
  · exact hEaharm.sub (Submission.harmonicOnX_const (max Cff 0 - 1))
  · exact hasLogPoleOn_sub_const' (max Cff 0 - 1) hEapole
  · intro x hx
    have h1 := hfar x hx
    linarith

/-- **The far-field matching of the two Evans potentials on a parabolic surface.**

On a connected, second countable, non-compact `ℂ`-charted surface `X` with `¬ HasWeakGreen X`
(parabolic in the potential-theoretic sense) and distinct points `a b`, there exist

* a harmonic `Ea` on `X ∖ {a}` with a *unit* logarithmic pole at `a`
  (`Work.SimplyConnected.ABS.HasLogPoleOn (univ ∖ {a}) a Ea`), and
* a harmonic `Eb` on `X ∖ {b}` with a unit logarithmic pole at `b`,

with *matched* behaviour at infinity: `Ea - Eb ≤ 1` off some compact set.

## Route

1. `Work.PoleMoving.exists_twoPole_exhaustion` gives a nested exhaustion `Ω n` carrying Green
   functions `gA n` (pole `a`) and `gB n` (pole `b`) on the *same* regions.
2. The classical **symmetry of the Green function of a region**, `gA n b = gB n a`
   (`Work.Drive.greenSymmetryRegion`), yields the one-sided comparison `gB n a ≤ gA n b`.
3. Kishi's local boundedness of the normalised Green functions
   (`Work.Drive.normalizedGreenExhaustion_locallyBounded`) makes the normalised families
   `gA n · - gA n b` and `gB n · - gB n a` locally uniformly bounded, and the *maximum principle*
   upgraded with that comparison bounds the pair functions `(gA n · - gA n b) - (gB n · - gB n a)`
   on the far region `Ω n ∖ closure (Ω 0)` (Lemma `pairFarField_of_oneSided_le`).
4. Montel for harmonic functions (`Work.Drive.harmonicMontelEventually`) produces limits `Ea` and
   `Eb`, the pole conditions pass to the limit
   (`Work.Drive.hasLogPoleOn_of_isGreenOn_limit`), and the far-field bound passes to the limit as
   well, giving `Ea - Eb ≤ C` off `closure (Ω 0)`; shifting by a constant finishes the proof.

Everything except step 2 is proved in this file, `sorry`-free. -/
theorem exists_matched_evans_of_not_hasWeakGreen {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) {a b : X} (hab : a ≠ b) (hO : ¬ Work.Drive.HasWeakGreen X) :
    ∃ Ea Eb : X → ℝ,
      Submission.HarmonicOnX Ea (Set.univ \ {a}) ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {a}) a Ea ∧
      Submission.HarmonicOnX Eb (Set.univ \ {b}) ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {b}) b Eb ∧
      ∃ K : Set X, IsCompact K ∧ ∀ x : X, x ∉ K → Ea x - Eb x ≤ 1 := by
  classical
  obtain ⟨Ω, gA, gB, hΩo, _hconn, hΩc, hnest, hcov, haΩ, hbΩ, hgA, hgB, hzA, hzB⟩ :=
    Work.PoleMoving.exists_twoPole_exhaustion (X := X) hX a b
  refine exists_matched_of_oneSided_le (X := X) hab hΩo hΩc hnest hcov haΩ hbΩ hgA hgB hzA hzB ?_
  intro n
  exact le_of_eq (Work.Drive.greenSymmetryRegion (X := X) (hΩo n) (hΩc n) hab
    (haΩ n) (hbΩ n) (hgA n) (hgB n)).symm

end Work.Drive
