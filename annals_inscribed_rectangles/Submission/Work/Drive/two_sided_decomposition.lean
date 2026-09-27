import Mathlib
import Submission.Work.Drive.SeparationBase
import Submission.Work.Drive.accumulating_components_eq
import Submission.Work.Drive.isPathConnected_exterior

/-!
# The two-sided decomposition of the complement of a locally separating continuum

Let `K ⊆ ℝ × ℝ` be closed, connected and bounded, and suppose that at every point `p ∈ K` the set
`K` separates a neighbourhood `U` of `p` into exactly two open path connected pieces `U₁`, `U₂`
(each of which accumulates at every point of `K ∩ U`) — this is `Work.Drive.LocalSep`.
If `Kᶜ` is not path connected, then `Kᶜ` is the disjoint union of exactly two open path connected
sets, one bounded and one unbounded, and both have closure `Pᵢ ∪ K`.

This is the Jordan-curve-type separation statement used for the smooth Jordan curve of the
inscribed-rectangles theorem.
-/

namespace Work.Drive

open Set

theorem two_sided_decomposition {K : Set (ℝ × ℝ)} (hKclosed : IsClosed K)
    (hKconn : IsConnected K) (hKbdd : Bornology.IsBounded K)
    (hsep : ∀ p ∈ K, ∃ U U₁ U₂ : Set (ℝ × ℝ), LocalSep K U U₁ U₂ ∧ p ∈ U)
    (hnot : ¬ IsPathConnected (Kᶜ)) :
    ∃ P₁ P₂ : Set (ℝ × ℝ), P₁ ≠ P₂ ∧ IsPathConnected P₁ ∧ IsPathConnected P₂ ∧
      IsOpen P₁ ∧ IsOpen P₂ ∧ Kᶜ = P₁ ∪ P₂ ∧ Disjoint P₁ P₂ ∧
      ((Bornology.IsBounded P₁ ∧ ¬ Bornology.IsBounded P₂) ∨
        (Bornology.IsBounded P₂ ∧ ¬ Bornology.IsBounded P₁)) ∧
      closure P₁ = P₁ ∪ K ∧ closure P₂ = P₂ ∪ K := by
  have hGopen : IsOpen (Kᶜ) := hKclosed.isOpen_compl
  -- `K` is nonempty, since otherwise `Kᶜ = ℝ × ℝ` would be path connected
  have hKne : K.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hKe
    apply hnot
    rw [hKe, compl_empty]
    refine ⟨0, mem_univ _, fun y _ => ?_⟩
    exact JoinedIn.ofLine (f := fun s : ℝ => s • y) (by fun_prop) (by simp) (by simp) (by simp)
  obtain ⟨p, hpK⟩ := hKne
  obtain ⟨U, U₁, U₂, hU, hpU⟩ := hsep p hpK
  obtain ⟨y₁, hy₁⟩ := hU.pc₁.nonempty
  obtain ⟨y₂, hy₂⟩ := hU.pc₂.nonempty
  have hy₁Kc : y₁ ∈ Kᶜ := by
    have h : y₁ ∈ U \ K := by rw [← hU.union]; exact Or.inl hy₁
    exact h.2
  have hy₂Kc : y₂ ∈ Kᶜ := by
    have h : y₂ ∈ U \ K := by rw [← hU.union]; exact Or.inr hy₂
    exact h.2
  set P₁ : Set (ℝ × ℝ) := pathComponentIn (Kᶜ) y₁ with hP₁
  set P₂ : Set (ℝ × ℝ) := pathComponentIn (Kᶜ) y₂ with hP₂
  -- The key input: the two components of the local pieces at `p` are the only path components
  -- of `Kᶜ` whose closure meets `K`, and they meet `K` everywhere.
  have hstep := accumulating_components_eq hKclosed hsep hKconn.isPreconnected hpK hU hpU hy₁ hy₂
  have hacc₁ : K ⊆ closure P₁ := by
    intro q hq
    exact (hstep q hq P₁ ⟨y₁, hy₁Kc, hP₁⟩).mpr (Or.inl hP₁)
  have hacc₂ : K ⊆ closure P₂ := by
    intro q hq
    exact (hstep q hq P₂ ⟨y₂, hy₂Kc, hP₂⟩).mpr (Or.inr hP₂)
  -- `Kᶜ` is the union of the two components
  have hcover : Kᶜ = P₁ ∪ P₂ := by
    ext x
    constructor
    · intro hx
      by_contra hxc
      have hxC : x ∈ pathComponentIn (Kᶜ) x := mem_pathComponentIn_self hx
      have hne₁ : pathComponentIn (Kᶜ) x ≠ P₁ := fun h => hxc (Or.inl (h ▸ hxC))
      have hne₂ : pathComponentIn (Kᶜ) x ≠ P₂ := fun h => hxc (Or.inr (h ▸ hxC))
      have hcl : closure (pathComponentIn (Kᶜ) x) ∩ K = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro q ⟨hqcl, hqK⟩
        rcases (hstep q hqK (pathComponentIn (Kᶜ) x) ⟨x, hx, rfl⟩).mp hqcl with h | h
        · exact hne₁ h
        · exact hne₂ h
      -- the component is clopen in `ℝ × ℝ`, hence everything
      have hCclosed : IsClosed (pathComponentIn (Kᶜ) x) := by
        rw [← closure_subset_iff_isClosed]
        intro z hz
        have hzG : z ∈ Kᶜ := by
          rintro hzK
          exact (Set.eq_empty_iff_forall_notMem.mp hcl) z ⟨hz, hzK⟩
        by_contra hzC
        have hdisj : Disjoint (pathComponentIn (Kᶜ) x) (pathComponentIn (Kᶜ) z) := by
          refine Set.disjoint_left.mpr fun w hw₁ hw₂ => ?_
          have h3 : pathComponentIn (Kᶜ) x = pathComponentIn (Kᶜ) z :=
            (pathComponentIn_congr hw₁).symm.trans (pathComponentIn_congr hw₂)
          exact hzC (h3 ▸ mem_pathComponentIn_self hzG)
        obtain ⟨w, hw₁, hw₂⟩ := mem_closure_iff.mp hz (pathComponentIn (Kᶜ) z)
          (hGopen.pathComponentIn z) (mem_pathComponentIn_self hzG)
        exact (Set.disjoint_left.mp hdisj) hw₂ hw₁
      have hclopen : IsClopen (pathComponentIn (Kᶜ) x) :=
        ⟨hCclosed, hGopen.pathComponentIn x⟩
      rcases isClopen_iff.mp hclopen with h | h
      · exfalso
        rw [h] at hxC
        exact hxC
      · exfalso
        have h1 : p ∈ pathComponentIn (Kᶜ) x := by rw [h]; exact mem_univ p
        exact pathComponentIn_subset h1 hpK
    · rintro (hx | hx)
      · rw [hP₁] at hx; exact pathComponentIn_subset hx
      · rw [hP₂] at hx; exact pathComponentIn_subset hx
  have hPne : P₁ ≠ P₂ := by
    intro heq
    refine hnot ?_
    have hGK : Kᶜ = P₁ := by rw [hcover, heq, Set.union_self]
    rw [hGK, hP₁]
    exact isPathConnected_pathComponentIn hy₁Kc
  have hdisj : Disjoint P₁ P₂ := by
    refine Set.disjoint_left.mpr fun z hz₁ hz₂ => ?_
    rw [hP₁] at hz₁
    rw [hP₂] at hz₂
    exact hPne (by
      rw [hP₁, hP₂]
      exact (pathComponentIn_congr hz₁).symm.trans (pathComponentIn_congr hz₂))
  have hcl₁ : closure P₁ = P₁ ∪ K := by
    refine Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
    · by_cases hzK : z ∈ K
      · exact Or.inr hzK
      · refine Or.inl ?_
        have hzG : z ∈ Kᶜ := hzK
        rw [hcover] at hzG
        rcases hzG with h | h
        · exact h
        · exfalso
          have hopen : IsOpen P₂ := hP₂ ▸ hGopen.pathComponentIn y₂
          obtain ⟨w, hw₁, hw₂⟩ := mem_closure_iff.mp hz P₂ hopen h
          exact (Set.disjoint_left.mp hdisj) hw₂ hw₁
    · rcases hz with hz | hz
      · exact subset_closure hz
      · exact hacc₁ hz
  have hcl₂ : closure P₂ = P₂ ∪ K := by
    refine Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
    · by_cases hzK : z ∈ K
      · exact Or.inr hzK
      · refine Or.inl ?_
        have hzG : z ∈ Kᶜ := hzK
        rw [hcover] at hzG
        rcases hzG with h | h
        · exfalso
          have hopen : IsOpen P₁ := hP₁ ▸ hGopen.pathComponentIn y₁
          obtain ⟨w, hw₁, hw₂⟩ := mem_closure_iff.mp hz P₁ hopen h
          exact (Set.disjoint_left.mp hdisj) hw₁ hw₂
        · exact h
    · rcases hz with hz | hz
      · exact subset_closure hz
      · exact hacc₂ hz
  -- one of the two components is bounded, the other is not
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_ball (0 : ℝ × ℝ)).mp hKbdd
  set R : ℝ := max R₀ 1 with hRdef
  have hRnn : 0 ≤ R := le_trans zero_le_one (le_max_right _ _)
  have hKR : K ⊆ Metric.ball (0 : ℝ × ℝ) R := fun x hx =>
    Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp (hR₀ hx)) (le_max_left _ _))
  have hSsub : {x : ℝ × ℝ | R ≤ dist x 0} ⊆ Kᶜ := by
    intro x hx hxK
    have h1 : dist x 0 < R₀ := Metric.mem_ball.mp (hR₀ hxK)
    have h2 : R₀ ≤ dist x 0 := le_trans (le_max_left _ _) hx
    linarith
  have hSpc : IsPathConnected {x : ℝ × ℝ | R ≤ dist x 0} := isPathConnected_exterior R hRnn
  set c : ℝ × ℝ := (R + 1, 0) with hcdef
  have hcS : c ∈ {x : ℝ × ℝ | R ≤ dist x 0} := by
    rw [hcdef]
    simp only [mem_ofPred_eq, Prod.dist_eq, Real.dist_eq]
    norm_num
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hcKc : c ∈ Kᶜ := hSsub hcS
  have hSc : {x : ℝ × ℝ | R ≤ dist x 0} ⊆ pathComponentIn (Kᶜ) c :=
    hSpc.subset_pathComponentIn hcS hSsub
  have hQunb : ¬ Bornology.IsBounded (pathComponentIn (Kᶜ) c) := by
    intro hb
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball c).mp hb
    obtain ⟨n, hn⟩ := exists_nat_gt r
    have hmem : ((R + (n : ℝ) + 2 : ℝ), (0 : ℝ)) ∈ pathComponentIn (Kᶜ) c := by
      apply hSc
      simp only [mem_ofPred_eq, Prod.dist_eq, Real.dist_eq]
      norm_num
      exact le_trans (by linarith : R ≤ R + (n : ℝ) + 2) (le_max_left _ _)
    have hle : dist ((R + (n : ℝ) + 2 : ℝ), (0 : ℝ)) c < r := Metric.mem_ball.mp (hr hmem)
    have hdd : dist ((R + (n : ℝ) + 2 : ℝ), (0 : ℝ)) c = (n : ℝ) + 1 := by
      rw [hcdef]
      simp only [Prod.dist_eq, Real.dist_eq]
      norm_num
      rw [show R + ↑n + 2 - (R + 1) = ↑n + 1 from by ring,
        abs_of_nonneg (by positivity)]
    rw [hdd] at hle
    linarith
  -- any component other than the one through `c` is bounded
  have key : ∀ {P : Set (ℝ × ℝ)}, (P = P₁ ∨ P = P₂) → P ≠ pathComponentIn (Kᶜ) c →
      Bornology.IsBounded P := by
    intro P hP hne
    rw [Metric.isBounded_iff_subset_ball (0 : ℝ × ℝ)]
    refine ⟨R, fun x hx => ?_⟩
    by_contra hxout
    rw [Metric.mem_ball, not_lt] at hxout
    have hxQ : x ∈ pathComponentIn (Kᶜ) c := hSc hxout
    have hEq : P = pathComponentIn (Kᶜ) c := by
      rcases hP with rfl | rfl
      · exact (pathComponentIn_congr hx).symm.trans (pathComponentIn_congr hxQ)
      · exact (pathComponentIn_congr hx).symm.trans (pathComponentIn_congr hxQ)
    exact hne hEq
  refine ⟨P₁, P₂, hPne, ?_, ?_, ?_, ?_, hcover, hdisj, ?_, hcl₁, hcl₂⟩
  · rw [hP₁]; exact isPathConnected_pathComponentIn hy₁Kc
  · rw [hP₂]; exact isPathConnected_pathComponentIn hy₂Kc
  · rw [hP₁]; exact hGopen.pathComponentIn y₁
  · rw [hP₂]; exact hGopen.pathComponentIn y₂
  · have hcP : c ∈ P₁ ∪ P₂ := hcover ▸ hcKc
    rcases hcP with hcP | hcP
    · have hce : pathComponentIn (Kᶜ) c = P₁ := pathComponentIn_congr hcP
      right
      refine ⟨key (Or.inr rfl) (fun h => hPne ((h.trans hce).symm)), fun hb => ?_⟩
      rw [← hce] at hb
      exact hQunb hb
    · have hce : pathComponentIn (Kᶜ) c = P₂ := pathComponentIn_congr hcP
      left
      refine ⟨key (Or.inl rfl) (fun h => hPne (h.trans hce)), fun hb => ?_⟩
      rw [← hce] at hb
      exact hQunb hb

end Work.Drive
