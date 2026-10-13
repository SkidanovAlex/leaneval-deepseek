import Mathlib
import Submission.Work.WilG4cR.AlDgListSliceMem
import Submission.Work.WilG4c.FibreSmoothThin
import Submission.Work.WilG4c.FibreBadCoresR

namespace Work.WilG4c

/-- The cores cover with the format, the core count and the degree polynomial all chosen
*before* the order `r` (only the evaluation of the degree uses `r`).  This is the exact shape the
proved assembly `Work.WilG4c.FLemPOfFibreCores` consumes; it is `Work.WilG4c.FibreBadCoresR`
with the quantifiers over `r` moved inside, and it follows from the *same* proof (reorder the
quantifiers): there `AlDgListSlice_mem S hcd hder p n F0` supplies `(a, b)` before `r`, and the
core family has `M = 1` element, namely the complement of the fibre slice `C^r`-locus
`SliceLocus p n f r`.  In the `N = 0` branch use `K = 2`, `M = 1`, `b = MvPolynomial.C 1`. -/
theorem FibreBadCoresSharp (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (p N : ℕ) :
    ∀ F0 : ℕ, ∃ (K M : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + N + 1) →
        ∃ A : Fin M → Set (Fin (p + N) → ℝ),
          (∀ j, A j ∈ S.Ω (F0 + K) (MvPolynomial.eval ![D, r] b) (p + N)) ∧
          (∀ l : Fin p → ℝ,
            interior {z : Fin N → ℝ | Fin.append l z ∈ ⋃ j, A j} = ∅) ∧
          (∀ l : Fin p → ℝ,
            {z : Fin N → ℝ | ¬ ContDiffAt ℝ r (fun z : Fin N → ℝ => f l z) z} ⊆
              {z : Fin N → ℝ | Fin.append l z ∈ ⋃ j, A j}) := by
  intro F0
  by_cases hN : N = 0
  · -- Degenerate fibre dimension: the fibre is a single point, hence `C^∞`, so the fibre-bad
    -- locus is empty and the empty family of cores works.
    subst hN
    refine ⟨2, 1, MvPolynomial.C 1, ?_⟩
    intro D r f hf
    -- `∅ = univᶜ`, and `univ` is the empty intersection `⋂ i : Fin 0, ⋃` (format `1`, degree `0`).
    have hempty : (∅ : Set (Fin (p + 0) → ℝ)) ∈
        S.Ω (F0 + 2) (MvPolynomial.eval ![D, r] (MvPolynomial.C 1)) (p + 0) := by
      have huniv : (Set.univ : Set (Fin (p + 0) → ℝ)) ∈ S.Ω 1 0 (p + 0) := by
        have h := S.inter (F := 0) (n := p + 0) (k := 0)
          (D := fun i : Fin 0 => 0) (A := fun i : Fin 0 => Set.univ)
          (fun i => i.elim0)
        simpa using h
      have hempty' : (∅ : Set (Fin (p + 0) → ℝ)) ∈ S.Ω 2 0 (p + 0) := by
        simpa using S.compl huniv
      exact Work.WilG1.Omega.mono hempty' (by omega) (by simp)
    refine ⟨fun _ => ∅, ?_, ?_, ?_⟩
    · intro j
      simpa using hempty
    · intro l
      have hset : {z : Fin 0 → ℝ | Fin.append l z ∈ ⋃ j : Fin 1, (∅ : Set (Fin (p + 0) → ℝ))}
          = ∅ := by
        ext z
        simp
      rw [hset]
      exact interior_empty
    · intro l z hz
      exfalso
      apply hz
      have hfun : (fun z' : Fin 0 → ℝ => f l z') = fun _ => f l z :=
        funext fun z' => by rw [Subsingleton.elim z' z]
      rw [hfun]
      exact contDiffAt_const
  · -- The fibre has positive dimension: write `N = n + 1` and use the slice derivative graph.
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 1 :=
      ⟨N - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hN)).symm⟩
    obtain ⟨a, b, hAl⟩ := Work.WilG4cR.AlDgListSlice_mem S hcd hder p n F0
    obtain ⟨Kf, hKf⟩ := fibreGraphMem S p (n + 1)
    refine ⟨a + 2, 1, b, ?_⟩
    intro D r f hf
    -- A list of `r` directions; the fibre `C^r`-locus is the projection of the derivative graph.
    let L : List (Fin (n + 1)) := List.ofFn (fun _ : Fin r => (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)))
    have hLlen : L.length = r := List.length_ofFn
    have hgraph : Work.WilkG4c.AlDgListSlice p n f L ∈
        S.Ω a (MvPolynomial.eval ![D, L.length] b) (p + (n + 1) + 1) := hAl D f L hf
    have hproj := S.proj hgraph
    have hprojeq : WilkiesDesign.projLast (Work.WilkG4c.AlDgListSlice p n f L)
        = Work.WilkG4c.SliceLocus p n f L.length :=
      Set.ext (fun w => (Work.WilkG4c.sliceLocus_iff_exists_mem f L w).symm)
    rw [hprojeq, hLlen] at hproj
    have hcompl : (Work.WilkG4c.SliceLocus p n f r)ᶜ ∈
        S.Ω (a + 2) (MvPolynomial.eval ![D, r] b) (p + (n + 1)) :=
      S.compl hproj
    refine ⟨fun _ => (Work.WilkG4c.SliceLocus p n f r)ᶜ, ?_, ?_, ?_⟩
    · intro j
      exact Work.WilG1.Omega.mono hcompl (by omega) le_rfl
    · -- thinness of the fibres
      intro l
      have hthin : interior {z : Fin (n + 1) → ℝ | ¬ ContDiffAt ℝ r
          (fun z : Fin (n + 1) → ℝ => f l z) z} = ∅ :=
        interior_nonCk_empty S hcd (fun z : Fin (n + 1) → ℝ => f l z) (hKf F0 D f l hf)
      refine Set.eq_empty_of_subset_empty (le_trans (interior_mono ?_) (le_of_eq hthin))
      intro z hz
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion] at hz ⊢
      obtain ⟨j, hj⟩ := hz
      fin_cases j
      simp only [Set.mem_compl_iff] at hj
      intro hc
      exact hj (by simpa [Work.WilkG4c.SliceLocus, parPt_append_R, cubePt_append_R] using hc)
    · -- coverage
      intro l z hz
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      refine ⟨0, ?_⟩
      simp only [Set.mem_compl_iff]
      intro hc
      exact hz (by simpa [Work.WilkG4c.SliceLocus, parPt_append_R, cubePt_append_R] using hc)

end Work.WilG4c
