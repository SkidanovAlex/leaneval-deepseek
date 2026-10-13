import Mathlib
import Submission.Work.WilG4c.FibreBadCores
import Submission.Work.WilG4c.FibreSmoothThin
import Submission.Work.WilG4c.FibreCoreDefs
import Submission.Work.WilG1.Cell.smooth_k_cover
import Submission.Work.WilG1.Cell.thin_closure
import Submission.Work.WilG4cR.AlDgListSliceMem

namespace Work.WilG4c

/-! ## The fibre `C^k`-locus has thin closure

The `k = 1` case is `Work.WilG4c.interior_closure_nonC1_empty`; running the same argument with
`Work.WilG1.Cell.smooth_k_cover` at order `k` instead of `1` gives the general case, which is
what the sharp fibre-cores statement below consumes (the cover pieces of `smooth_k_cover` have
empty interior and are `Ω`-sets, so their closures are nowhere dense by `thin_closure`). -/
theorem interior_closure_nonCk_empty (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    {N F D k : ℕ} (g : (Fin N → ℝ) → ℝ) (hg : WilkiesDesign.graphOf g ∈ S.Ω F D (N + 1)) :
    interior (closure {z : Fin N → ℝ | ¬ ContDiffAt ℝ k g z}) = ∅ := by
  obtain ⟨m, a, b, A, hA, hint, hsub⟩ :=
    Work.WilG1.Cell.smooth_k_cover (S := S) hcd (k := k) g hg
  have hnw : ∀ i : Fin m, IsNowhereDense (A i) := fun i =>
    Work.WilG1.Cell.thin_closure (S := S) hcd (hA i) (hint i)
  have hnwU : IsNowhereDense (⋃ i : Fin m, A i) := IsNowhereDense.iUnion hnw
  exact Set.eq_empty_of_subset_empty
    (le_trans (interior_mono (closure_mono hsub)) (le_of_eq hnwU))

/-- The fibre non-`C^k` locus itself has empty interior (it is contained in the closure of the
same set). -/
theorem interior_nonCk_empty (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    {N F D k : ℕ} (g : (Fin N → ℝ) → ℝ) (hg : WilkiesDesign.graphOf g ∈ S.Ω F D (N + 1)) :
    interior {z : Fin N → ℝ | ¬ ContDiffAt ℝ k g z} = ∅ :=
  Set.eq_empty_of_subset_empty
    (le_trans (interior_mono (subset_closure :
      {z : Fin N → ℝ | ¬ ContDiffAt ℝ k g z} ⊆
        closure {z : Fin N → ℝ | ¬ ContDiffAt ℝ k g z}))
      (le_of_eq (interior_closure_nonCk_empty S hcd g hg)))

/-- Reading `parPt` at an appended point. -/
theorem parPt_append_R {p n : ℕ} (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) :
    Work.WilkG4c.parPt (Fin.append l z) = l := by
  funext i
  simp [Work.WilkG4c.parPt, Fin.append_left]

/-- Reading `cubePt` at an appended point. -/
theorem cubePt_append_R {p n : ℕ} (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) :
    Work.WilkG4c.cubePt (Fin.append l z) = z := by
  funext j
  simp [Work.WilkG4c.cubePt, Fin.append_right]

/-- The **sharp** version of `Work.WilG4c.FibreBadCores`, at arbitrary order `r`: the *fibre*
non-`C^r` locus of a family member is covered, uniformly in the parameter, by the fibres of
finitely many joint `Ω`-sets whose fibres have empty interior — with a format `K` that is
*independent of `r`* (only `M` and the degree polynomial `b` may depend on `r`).  Both inputs
`S.SharpCD` and `S.SharpDeriv` are available (they are hypotheses of the frozen
`Work.WilG4c.StepClean`).

For `r = 1` this is `Work.WilG4c.FibreBadCores` (proved, from `SharpCD` alone, via the four
first-order fibre cores `fibBad`, `fibBad (junkP ·)`, `disc (junkP ·)`, `disc`).  For `r ≥ 2`
the iterate-of-junk-partials construction does **not** give it: both the format and the degree of
the iterated junk partials grow with the order (`Work.WilG1.Cell.Junk.junkIt_mem`), whereas
`S.SharpDeriv` is *sharp* (format independent of the order, degree polynomial in it — see the
proof of `Work.WilG4c.StepBadLoc`, which gets `badLoc f m` with an `m`-independent format and a
degree polynomial in `(D, m)` out of `SharpDeriv`).  The statement is a *cover* by thin-fibred
joint sets and concerns only the locus, so it is strictly weaker than the registered
fibre-derivative-graph holes (`Work.WilG4c.AlDgListSlice_mem`,
`Work.WilG4c.SliceDerivGraphMem`); but it is exactly what the frozen §5.5 clean-up needs: it
upgrades a cell of a `SharpCD`-decomposition to a cell on whose fibre the proved
`Work.WilG4c.StepCellEngineFibre` applies. -/
theorem FibreBadCoresR (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (p N : ℕ) :
    ∀ F0 : ℕ, ∃ K : ℕ, ∀ r : ℕ, ∃ (M : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ),
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
    refine ⟨2, ?_⟩
    intro r
    refine ⟨1, MvPolynomial.C 1, ?_⟩
    intro D f hf
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
    refine ⟨a + 2, ?_⟩
    intro r
    refine ⟨1, b, ?_⟩
    intro D f hf
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
