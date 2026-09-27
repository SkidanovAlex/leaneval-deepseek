import Mathlib
import Submission.Work.EQ.H0_path_limit_window

namespace Work.EQ

open Filter _root_.Topology Set Metric

/-- Uniform backward-Puiseux cover of the window of a path of chains, carrying the
admissibility of the sign sequence: there is a single admissible `σ` covering the whole window on
the nonempty preconnected parameter set, with a parameter `t` satisfying
`t ^ (2 ^ (n₁ + m₁)) = ψ₁ (γ s) - u`.

This is `Work.EQ.H0_path_limit_window` with the additional clause `Work.EQ.Adm a c u R σ`, which
its internal argument already produces (the sign sequence is chosen out of the admissible family
built by `Work.EQ.window_coverage` in the covering step), together with the hypothesis
`I.Nonempty` which that proof needs in order to have a point at which to choose the admissible
sign sequence; the empty case is excluded. -/
theorem H0_path_limit_window_adm {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) {γ : ℝ → Work.EQ.ChainData} {S : ℝ} {n₁ m₁ : ℕ} {u : ℂ}
    (hu : u ≠ 0) {R : ℝ} (hR : 0 < R)
    (hc : AnalyticOnNhd ℂ
      (fun w : ℂ => Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n₁ * w)) (Metric.ball u R))
    (hchain : ∀ s : ℝ, S ≤ s → Work.EQ.IsChain a h (γ s))
    (hcont : ContinuousOn γ (Set.Ici S))
    (hfw : ∀ s : ℝ, S ≤ s → ∀ n : ℕ, n₁ ≤ n →
      (γ s).1 (n : ℤ) = Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n * (γ s).2.1))
    (hbw : ∀ s : ℝ, S ≤ s → ∀ n : ℕ, m₁ ≤ n →
      (γ s).1 (-(n : ℤ)) = Work.EQ.ugermC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n * (γ s).2.2))
    (I : Set ℝ) (hIS : ∀ s ∈ I, S ≤ s) (hI : IsPreconnected I) (hIne : I.Nonempty)
    (hne : ∀ s ∈ I, (γ s).2.1 ≠ u)
    (hcl : ∀ s ∈ I, ‖(γ s).2.1 - u‖ < (Work.EQ.rhoFin' a
        (fun w : ℂ => Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n₁ * w)) u R
        (n₁ + m₁)) ^ (2 ^ (n₁ + m₁))) :
    ∃ σ : Fin (n₁ + m₁) → Bool, Work.EQ.Adm a
        (fun w : ℂ => Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n₁ * w)) u R σ ∧
      ∀ s ∈ I, ∃ t : ℂ,
        t ^ (2 ^ (n₁ + m₁)) = (γ s).2.1 - u ∧ 0 < ‖t‖ ∧
        ‖t‖ < Work.EQ.rhoFin' a (fun w : ℂ => Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n₁ * w))
          u R (n₁ + m₁) ∧
        ∀ j : Fin (n₁ + m₁ + 1),
          (γ s).1 ((((j : ℕ) : ℤ) - (m₁ : ℤ))) =
            Work.EQ.branchPt a
              (fun w : ℂ => Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n₁ * w)) u R σ t j := by
  classical
  obtain ⟨s₀, hs₀⟩ := hIne
  set c : ℂ → ℂ × ℂ := fun w => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * w) with hcdef
  have hc' : AnalyticOnNhd ℂ c (Metric.ball u R) := by rw [hcdef]; exact hc
  set w : ℝ → ℂ := fun s => (γ s).2.1 - u with hwdef
  have hwcont : ContinuousOn w I := by
    have h1 : ContinuousOn (fun s : ℝ => (γ s).2.1) (Set.Ici S) :=
      (continuous_fst.comp continuous_snd : Continuous (fun p : ChainData => p.2.1)).comp_continuousOn hcont
    exact (h1.mono hIS).sub continuousOn_const
  have hwne : ∀ s ∈ I, w s ≠ 0 := fun s hs => by
    rw [hwdef]; exact sub_ne_zero.mpr (hne s hs)
  obtain ⟨t, htcont, htpow, htne⟩ :=
    _root_.Work.Topology.continuous_root hI hwcont hwne (k := 2 ^ (n₁ + m₁)) (by positivity)
  have htρ : ∀ s ∈ I, ‖t s‖ < rhoFin' a c u R (n₁ + m₁) := by
    intro s hs
    have hρpos : 0 < rhoFin' a c u R (n₁ + m₁) := rhoFin'_pos hR hc'
    have hcl' : ‖w s‖ < (rhoFin' a c u R (n₁ + m₁)) ^ (2 ^ (n₁ + m₁)) := by
      simpa only [hwdef, hcdef] using hcl s hs
    have h1 : ‖t s‖ ^ (2 ^ (n₁ + m₁)) = ‖w s‖ := by rw [← norm_pow, htpow s hs]
    rw [← h1] at hcl'
    exact lt_of_pow_lt_pow_left₀ (2 ^ (n₁ + m₁)) hρpos.le hcl'
  -- the finite family of closed sets
  haveI : Fintype {σ : Fin (n₁ + m₁) → Bool // Adm a c u R σ} := inferInstance
  have hAcov : ∀ s : ↥I, ∃ σ : {σ : Fin (n₁ + m₁) → Bool // Adm a c u R σ},
      s ∈ WindowSet a h γ u R n₁ m₁ t I σ.1 := by
    intro s
    have ht1 : t (s : ℝ) ^ (2 ^ (n₁ + m₁)) = (γ (s : ℝ)).2.1 - u := by
      simpa only [hwdef] using htpow (s : ℝ) s.2
    have ht0 : t (s : ℝ) ≠ 0 := htne (s : ℝ) s.2
    have ht2 : ‖t (s : ℝ)‖ < rhoFin' a
        (fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * w)) u R (n₁ + m₁) := by
      simpa only [hcdef] using htρ (s : ℝ) s.2
    obtain ⟨σ, hσadm, hσj⟩ :=
      window_coverage (a := a) (h := h) (γ := γ) (S := S) (n₁ := n₁) (m₁ := m₁) (u := u)
        (R := R) hR hc hchain hfw (s := (s : ℝ)) (hsS := hIS (s : ℝ) s.2) (t := t (s : ℝ))
        ht1 ht0 ht2
    exact ⟨⟨σ, hσadm⟩, hσj⟩
  have hAdisj : ∀ σ τ : {σ : Fin (n₁ + m₁) → Bool // Adm a c u R σ}, σ ≠ τ →
      Disjoint (WindowSet a h γ u R n₁ m₁ t I σ.1) (WindowSet a h γ u R n₁ m₁ t I τ.1) := by
    intro σ τ hστ
    rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    intro s hs
    simp only [Set.mem_inter_iff, WindowSet, mem_ofPred_eq] at hs
    have hne' : σ.1 ≠ τ.1 := fun hh => hστ (Subtype.ext hh)
    have heq : branchPt a c u R σ.1 (t (s : ℝ)) = branchPt a c u R τ.1 (t (s : ℝ)) := by
      funext j
      exact (hs.1 j).symm.trans (hs.2 j)
    exact branchPt_ne hR hc' σ.2 τ.2 hne' (t (s : ℝ))
      (norm_pos_iff.mpr (htne (s : ℝ) s.2)) (htρ (s : ℝ) s.2) heq
  have hAclosed : ∀ σ : {σ : Fin (n₁ + m₁) → Bool // Adm a c u R σ},
      IsClosed (WindowSet a h γ u R n₁ m₁ t I σ.1) := by
    intro σ
    have hwin : ∀ j : Fin (n₁ + m₁ + 1),
        Continuous (fun s : ↥I => (γ (s : ℝ)).1 ((((j : ℕ) : ℤ) - (m₁ : ℤ)))) := by
      intro j
      have h1 : ContinuousOn (fun s : ℝ => (γ s).1 ((((j : ℕ) : ℤ) - (m₁ : ℤ)))) (Set.Ici S) :=
        ((continuous_apply (((j : ℕ) : ℤ) - (m₁ : ℤ))).comp
          (continuous_fst : Continuous (Prod.fst : ChainData → ℤ → ℂ × ℂ))).comp_continuousOn hcont
      exact (h1.mono hIS).domRestrict
    have hbt : ∀ j : Fin (n₁ + m₁ + 1),
        Continuous (fun s : ↥I => branchPt a c u R σ.1 (t (s : ℝ)) j) := by
      intro j
      rw [continuous_iff_continuousAt]
      intro s
      have ht1 : ContinuousAt (fun s : ↥I => t (s : ℝ)) s := (htcont.domRestrict).continuousAt
      have hmem : t (s : ℝ) ∈ Metric.ball (0 : ℂ) (rhoFin' a c u R (n₁ + m₁)) \ {0} := by
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball, dist_zero_right]; exact htρ (s : ℝ) s.2
        · simp only [Set.mem_singleton_iff]; exact htne (s : ℝ) s.2
      have han := branchPt_analytic hR hc' σ.2 j
      have h2 : ContinuousAt (fun τ : ℂ => branchPt a c u R σ.1 τ j) (t (s : ℝ)) :=
        (han.1 _ hmem).continuousAt.prodMk (han.2 _ hmem).continuousAt
      exact h2.comp (f := fun s : ↥I => t (s : ℝ)) ht1
    rw [show WindowSet a h γ u R n₁ m₁ t I σ.1 =
        ⋂ j : Fin (n₁ + m₁ + 1), {s : ↥I |
          (γ (s : ℝ)).1 ((((j : ℕ) : ℤ) - (m₁ : ℤ))) =
            branchPt a c u R σ.1 (t (s : ℝ)) j} from by
      ext s; simp only [WindowSet, mem_ofPred_eq, Set.mem_iInter, hcdef]]
    exact isClosed_iInter (fun j => isClosed_eq (hwin j) (hbt j))
  -- one admissible sign sequence covers the whole parameter set
  obtain ⟨σ₀, hσ₀⟩ := hAcov ⟨s₀, hs₀⟩
  have hσ₀mem : (WindowSet a h γ u R n₁ m₁ t I σ₀.1).Nonempty := ⟨⟨s₀, hs₀⟩, hσ₀⟩
  have hopen : IsOpen (WindowSet a h γ u R n₁ m₁ t I σ₀.1) := by
    rw [← isClosed_compl_iff]
    have hcompl : (WindowSet a h γ u R n₁ m₁ t I σ₀.1)ᶜ =
        ⋃ τ : {σ : Fin (n₁ + m₁) → Bool // Adm a c u R σ},
          if τ = σ₀ then ∅ else WindowSet a h γ u R n₁ m₁ t I τ.1 := by
      ext s
      constructor
      · intro hs
        obtain ⟨σ, hσ⟩ := hAcov s
        have hσne : σ ≠ σ₀ := by rintro rfl; exact hs hσ
        exact Set.mem_iUnion.mpr ⟨σ, by rw [if_neg hσne]; exact hσ⟩
      · intro hs
        rw [Set.mem_iUnion] at hs
        obtain ⟨τ, hτ⟩ := hs
        by_cases hτeq : τ = σ₀
        · rw [if_pos hτeq] at hτ
          exact absurd hτ (Set.notMem_empty s)
        · rw [if_neg hτeq] at hτ
          intro hs
          have hd := hAdisj τ σ₀ hτeq
          rw [Set.disjoint_iff_inter_eq_empty] at hd
          have hmem : s ∈ WindowSet a h γ u R n₁ m₁ t I τ.1 ∩
              WindowSet a h γ u R n₁ m₁ t I σ₀.1 := ⟨hτ, hs⟩
          rw [hd] at hmem
          exact hmem
    rw [hcompl]
    refine isClosed_iUnion_of_finite (fun τ => ?_)
    by_cases hτeq : τ = σ₀
    · rw [if_pos hτeq]; exact isClosed_empty
    · rw [if_neg hτeq]; exact hAclosed τ
  haveI : PreconnectedSpace ↥I := Subtype.preconnectedSpace hI
  have huniv : WindowSet a h γ u R n₁ m₁ t I σ₀.1 = Set.univ :=
    IsClopen.eq_univ ⟨hAclosed σ₀, hopen⟩ hσ₀mem
  refine ⟨σ₀.1, σ₀.2, fun s hs => ⟨t s, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [hwdef] using htpow s hs
  · exact norm_pos_iff.mpr (htne s hs)
  · simpa only [hcdef] using htρ s hs
  · intro j
    have hmem : (⟨s, hs⟩ : ↥I) ∈ WindowSet a h γ u R n₁ m₁ t I σ₀.1 := by
      rw [huniv]; trivial
    simpa only [WindowSet, mem_ofPred_eq] using hmem j

end Work.EQ
