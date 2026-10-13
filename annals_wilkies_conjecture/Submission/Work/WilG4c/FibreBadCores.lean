import Mathlib
import Submission.Work.WilG4c.FibreSmoothThin
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.FibreCoreDefs
import Submission.Work.WilG1.Cell.smooth_k_cover
import Submission.Work.WilG4c.SliceCoresMain.slice_cores
import Submission.Work.WilG4c.FibrewiseClosure.fibrewiseClosure_mem
import Submission.Work.WilG4c.UniformCores.junkP_mem_uniform
import Submission.Work.WilG4c.UniformCores.fibBad_mem_uniform
import Submission.Work.WilG4c.FibDiscMain.fibDisc_mem_uniform
import Submission.Work.WilG4c.CoreCover.smooth_core_cover
import Submission.Work.WilG4c.CoreThin.core_thin

set_option autoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG1.Cell
open Work.WilG4c.UniformCores Work.WilG4c.SliceCoresMain Work.WilG4c.FibrewiseClosure
open Work.WilG4c.FibDiscMain Work.WilG4c.CoreCover Work.WilG4c.CoreThin

/-- The fibre non-`C¹` locus of a family member `f : ℝ^p → ℝ^N → ℝ` (the set of `z` at which
the *fibre* function `z ↦ f l z` is not `C¹`) is covered, uniformly in the parameter `l`, by the
fibres of finitely many *joint* `Ω`-sets `A j ⊆ ℝ^{p+N}` whose fibres have empty interior in
`ℝ^N`.  The format/degree of the `A j` depend only on the family format `F0` (through `K`, `M`
and the polynomial `b`), never on `D` or on the family member itself; the sets `A j` of course
do.

Hint (from the reviewers): take pieces from *fibre directions only* and do **not** close them:
e.g. `⋃_i (fibBad g i ∪ fibBad (junkP g i) i' ∪ disc (junkP g i)) ∪ disc g` with `g = famFun f`,
where the `disc` must be the *fibre-wise* discontinuity (fix the parameter in the `∃z'`
quantifier).  Coverage of the fibre non-`C¹` locus is a per-fibre case split; each piece is
joint-`Ω` at a constant format and a degree polynomial in `D`, and each *fibre* is thin by
`fibreGraphMem` + `generic_continuity`/`smooth_k_cover` applied to the sliced function. -/
theorem FibreBadCores (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (p N : ℕ) :
    ∀ F0 : ℕ, ∃ (K M : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + N + 1) →
        ∃ A : Fin M → Set (Fin (p + N) → ℝ),
          (∀ j, A j ∈ S.Ω (F0 + K) (b.eval D) (p + N)) ∧
          (∀ l : Fin p → ℝ, interior {z : Fin N → ℝ | Fin.append l z ∈ ⋃ j, A j} = ∅) ∧
          (∀ l : Fin p → ℝ,
            {z : Fin N → ℝ | ¬ ContDiffAt ℝ 1 (fun z : Fin N → ℝ => f l z) z} ⊆
              {z : Fin N → ℝ | Fin.append l z ∈ ⋃ j, A j}) := by
  intro F0
  obtain ⟨Kf, hKf⟩ := fibreGraphMem S p N
  obtain ⟨Kc, cc, hfwc⟩ := fibrewiseClosure_mem S p N
  -- uniform `Ω`-bounds for the joint cores, one core index at a time
  have coreBound : ∀ a : CoreIx N, ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (D : ℕ) (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ),
        famGraph f ∈ S.Ω F0 D (p + N + 1) → jointCore f a ∈ S.Ω A (B.eval D) (p + N) := by
    intro a
    cases a with
    | fbad i =>
        obtain ⟨Aa, Ba, h⟩ := fibBad_mem_uniform S (p + N) F0 (Fin.natAdd p i)
        refine ⟨Aa, Ba, fun D f hf => ?_⟩
        simp only [jointCore]
        exact h D (famFun f) hf
    | fbadJ i i' =>
        obtain ⟨Aj, Bj, hj⟩ := junkP_mem_uniform S (p + N) F0 (Fin.natAdd p i)
        obtain ⟨Ab, Bb, hb⟩ := fibBad_mem_uniform S (p + N) Aj (Fin.natAdd p i')
        refine ⟨Ab, Bb.comp Bj, fun D f hf => ?_⟩
        simp only [jointCore]
        rw [Polynomial.eval_comp]
        exact hb (Bj.eval D) (junkP (famFun f) (Fin.natAdd p i)) (hj D (famFun f) hf)
    | discJ i =>
        obtain ⟨Aj, Bj, hj⟩ := junkP_mem_uniform S (p + N) F0 (Fin.natAdd p i)
        obtain ⟨Kd, bd, hd⟩ := fibDisc_mem_uniform S p N Aj
        refine ⟨Aj + Kd, bd.comp Bj, fun D f hf => ?_⟩
        simp only [jointCore]
        rw [Polynomial.eval_comp]
        exact hd (Bj.eval D) (junkP (famFun f) (Fin.natAdd p i)) (hj D (famFun f) hf)
    | disc0 =>
        obtain ⟨Kd, bd, hd⟩ := fibDisc_mem_uniform S p N F0
        refine ⟨F0 + Kd, bd, fun D f hf => ?_⟩
        simp only [jointCore]
        exact hd D (famFun f) hf
  choose A_core B_core hcoreBound using coreBound
  set Aall : ℕ := Finset.univ.sup A_core with hAall
  set ball : Polynomial ℕ := (∑ a : CoreIx N, B_core a) + Polynomial.C cc with hball
  refine ⟨Aall + Kc + F0, Fintype.card (CoreIx N), ball, ?_⟩
  intro D f hf
  let e : CoreIx N ≃ Fin (Fintype.card (CoreIx N)) := Fintype.equivFin _
  let Wfam : CoreIx N → Set (Fin (p + N) → ℝ) := fun a => fibrewiseClosure (jointCore f a)
  let A : Fin (Fintype.card (CoreIx N)) → Set (Fin (p + N) → ℝ) := fun j => Wfam (e.symm j)
  have hAe : ∀ a : CoreIx N, A (e a) = Wfam a := fun a => by simp [A]
  refine ⟨A, ?_, ?_, ?_⟩
  · -- `Ω`-membership
    intro j
    have h1 := hcoreBound (e.symm j) D f hf
    have h2 := (hfwc (A_core (e.symm j)) ((B_core (e.symm j)).eval D)
      (jointCore f (e.symm j)) h1).1
    refine Work.WilG1.Omega.mono h2 ?_ ?_
    · have hle : A_core (e.symm j) ≤ Aall := Finset.le_sup (Finset.mem_univ (e.symm j))
      omega
    · rw [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finsetSum]
      exact Nat.add_le_add_right
        (Finset.single_le_sum (f := fun a => (B_core a).eval D)
          (fun i _ => Nat.zero_le _) (Finset.mem_univ (e.symm j))) cc
  · -- thinness of the fibres
    intro l
    have hset : {z : Fin N → ℝ | Fin.append l z ∈ ⋃ j, A j}
        = ⋃ a : CoreIx N, closure (fibCore (fun z : Fin N → ℝ => f l z) a) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨j, hj⟩
        refine ⟨e.symm j, ?_⟩
        have h2 := (hfwc (A_core (e.symm j)) ((B_core (e.symm j)).eval D)
          (jointCore f (e.symm j)) (hcoreBound (e.symm j) D f hf)).2 l
        have h3 := (slice_cores p N f).2 (e.symm j) l
        rw [h3] at h2
        rw [← h2]
        exact hj
      · rintro ⟨a, ha⟩
        refine ⟨e a, ?_⟩
        have h2 := (hfwc (A_core a) ((B_core a).eval D)
          (jointCore f a) (hcoreBound a D f hf)).2 l
        have h3 := (slice_cores p N f).2 a l
        rw [h3] at h2
        rw [hAe a]
        change z ∈ fibreOf (fibrewiseClosure (jointCore f a)) l
        rw [h2]
        exact ha
    rw [hset]
    have hthin : ∀ a : CoreIx N,
        IsNowhereDense (closure (fibCore (fun z : Fin N → ℝ => f l z) a)) := by
      intro a
      have h := core_thin S hcd N (F0 + Kf) (D + Kf) (fun z : Fin N → ℝ => f l z)
        (hKf F0 D f l hf) a
      simpa [IsNowhereDense] using h
    have h2 : interior (closure (⋃ a : CoreIx N,
        closure (fibCore (fun z : Fin N → ℝ => f l z) a))) = ∅ := IsNowhereDense.iUnion hthin
    have hclosed : IsClosed (⋃ a : CoreIx N,
        closure (fibCore (fun z : Fin N → ℝ => f l z) a)) :=
      isClosed_iUnion_of_finite (fun a => isClosed_closure)
    rwa [hclosed.closure_eq] at h2
  · -- coverage
    intro l z hz
    have hsc := smooth_core_cover S N (F0 + Kf) (D + Kf) (fun z : Fin N → ℝ => f l z)
      (hKf F0 D f l hf)
    have hz' := hsc hz
    rw [Set.mem_iUnion] at hz'
    obtain ⟨a, ha⟩ := hz'
    simp only [Set.mem_ofPred_eq]
    rw [Set.mem_iUnion]
    refine ⟨e a, ?_⟩
    have h2 := (hfwc (A_core a) ((B_core a).eval D)
      (jointCore f a) (hcoreBound a D f hf)).2 l
    have h3 := (slice_cores p N f).2 a l
    rw [h3] at h2
    rw [hAe a]
    change z ∈ fibreOf (fibrewiseClosure (jointCore f a)) l
    rw [h2]
    exact ha

end Work.WilG4c
