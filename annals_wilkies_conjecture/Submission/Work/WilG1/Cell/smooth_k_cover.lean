/-
  WilG1 / Cell / smooth_k_cover.

  `smooth_k_cover`: the non-`C^k` locus of a definable function is covered by finitely many
  `Ω`-sets of empty interior.  The proof is the "junk partial" criterion:

  * for a word `w : List (Fin n)` let `junkIt f w` be the iterated one-variable ("junk")
    partial derivative of `f` along `w` (`JunkDefs`), with `junkP` the one-step operation;
  * `fibBad h i` is the set of parameters where the fibre of `h` in direction `i` is not
    differentiable, and `disc h` is the discontinuity locus of `h`;
  * `contDiffOn_of_avoids` (`C^k` on an open set on which all the iterated junk partials of
    words of length `≤ k` have existing fibre derivatives and are continuous) is proved by
    descending induction on the order, via the two classical facts
    `hasFDerivAt_of_fibrePartials` and `contDiffOn_jet_of_coord`;
  * thinness of `fibBad` is `partialBad_thin` (in an arbitrary direction, obtained from the
    last-direction version by a coordinate permutation), thinness of `disc` is
    `generic_continuity`, and `thin_closure` passes thinness to closures;
  * the finite family of closures is `Ω`-definable (`fibBad_mem`, `disc_mem`, `closure_mem`)
    and its union covers the non-`C^k` locus.
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Cell.JunkDefs
import Submission.Work.WilG1.Cell.partialBad_thin
import Submission.Work.WilG1.Cell.generic_continuity
import Submission.Work.WilG1.Cell.thin_closure
import Submission.Work.WilG1.Calc.closure_mem
import Submission.Work.WilG1.Plumb.Imports
import Submission.Work.WilG1.Plumb.junkPartial_mem
import Submission.Work.WilG1.Cell.Junk.hasFDerivAt_of_fibrePartials
import Submission.Work.WilG1.Cell.Junk.contDiffOn_jet_of_coord
import Submission.Work.WilG1.Cell.Junk.disc_mem
import Submission.Work.WilG1.Cell.Junk.fibBad_mem
import Submission.Work.WilG1.Cell.Junk.junkIt_mem
import Submission.Work.WilG1.Cell.Junk.fibBad_thin_of_last

set_option autoImplicit false
noncomputable section
open Classical
open scoped BigOperators Topology

namespace Work.WilG1.Cell

open WilkiesDesign Work.WilG1

/-! ## The bridge to `Plumb.junkPartial` -/

/-- The junk partial of `JunkDefs` is the `junkPartial` of `Plumb`. -/
theorem junkP_eq_junkPartial {N : ℕ} (g : (Fin (N + 1) → ℝ) → ℝ) (i : Fin (N + 1)) :
    junkP g i = Work.WilG1.junkPartial i g := by
  funext z
  simp only [junkP, Work.WilG1.junkPartial]
  congr 1
  funext x
  rw [Fin.insertNth_removeNth]
  rfl

/-! ## Polynomial bookkeeping -/

/-- A sum of evaluations is the evaluation of the sum. -/
theorem eval_sum_poly {ι : Type*} [Fintype ι] (b : ι → Polynomial ℕ) (D : ℕ) :
    (∑ i, b i).eval D = ∑ i, (b i).eval D := by
  classical
  have key : ∀ s : Finset ι, (∑ i ∈ s, b i).eval D = ∑ i ∈ s, (b i).eval D := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.eval_add, ih]
  simpa using key Finset.univ

/-- Every term of a sum of evaluations is bounded by the sum. -/
theorem eval_le_sum_eval {ι : Type*} [Fintype ι] (b : ι → Polynomial ℕ) (u : ι) (D : ℕ) :
    (b u).eval D ≤ (∑ i, b i).eval D := by
  rw [eval_sum_poly]
  exact Finset.single_le_sum (f := fun i => (b i).eval D) (fun i _ => Nat.zero_le _)
    (Finset.mem_univ u)

/-! ## The junk criterion -/

/-- If on an open set `V` every iterated junk partial of a word of length `≤ k` has existing
fibre derivatives and is continuous, then `f` is `C^k` on `V`. -/
theorem contDiffOn_of_avoids {S : WilkiesDesign.SOMin} {n F D k : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : WilkiesDesign.graphOf f ∈ S.Ω F D (n + 1))
    {V : Set (Fin n → ℝ)} (hV : IsOpen V)
    (h1 : ∀ (w : List (Fin n)), w.length ≤ k → ∀ i : Fin n, V ∩ fibBad (junkIt f w) i = ∅)
    (h2 : ∀ (w : List (Fin n)), w.length ≤ k → ContinuousOn (junkIt f w) V) :
    ContDiffOn ℝ k f V := by
  have key : ∀ m, ∀ w : List (Fin n), w.length + m ≤ k →
      ContDiffOn ℝ m (junkIt f w) V := by
    intro m
    induction m with
    | zero =>
      intro w hw
      exact (contDiffOn_zero (𝕜 := ℝ) (f := junkIt f w) (s := V)).mpr (h2 w (by omega))
    | succ m ih =>
      intro w hw
      -- the fibre derivatives of `junkIt f w` exist on `V`
      have hex : ∀ i : Fin n, ∀ z ∈ V, DifferentiableAt ℝ (fibreMap (junkIt f w) i z) (z i) := by
        intro i z hz
        have hznot : z ∉ fibBad (junkIt f w) i := by
          intro hzb
          have hmem : z ∈ V ∩ fibBad (junkIt f w) i := ⟨hz, hzb⟩
          rw [h1 w (by omega) i] at hmem
          exact hmem
        exact of_not_not hznot
      -- the junk partials are continuous at every point of `V`
      have hcont : ∀ z ∈ V, ∀ i : Fin n, ContinuousAt (junkP (junkIt f w) i) z := by
        intro z hz i
        have hc : ContinuousOn (junkIt f (w ++ [i])) V := h2 _ (by simp; omega)
        have := hc.continuousAt (hV.mem_nhds hz)
        simpa [junkIt_concat] using this
      have hdiff : DifferentiableOn ℝ (junkIt f w) V := fun z hz =>
        ((Junk.hasFDerivAt_of_fibrePartials (junkIt f w) hV hz (hex ·)
          (hcont z hz)).differentiableAt).differentiableWithinAt
      -- the derivative of `junkIt f w` is the jet of its junk partials
      have hjet : ContDiffOn ℝ m (fun y => fderivWithin ℝ (junkIt f w) V y) V := by
        have hcongr : ∀ y ∈ V, jet (fun i => junkP (junkIt f w) i y) =
            fderivWithin ℝ (junkIt f w) V y := by
          intro y hy
          rw [fderivWithin_of_isOpen hV hy]
          exact ((Junk.hasFDerivAt_of_fibrePartials (junkIt f w) hV hy (hex ·)
            (hcont y hy)).fderiv).symm
        rw [← contDiffOn_congr hcongr]
        exact Junk.contDiffOn_jet_of_coord _ (fun i => by
          have := ih (w ++ [i]) (by simp; omega)
          simpa [junkIt_concat] using this)
      have hres := contDiffOn_succ_of_fderivWithin (𝕜 := ℝ) (f := junkIt f w) (s := V)
        (n := (m : ℕ∞)) hdiff (by simp) (by simpa using hjet)
      simpa using hres
  simpa using key k [] (by simp)

/-! ## The finite family of bad sets -/

/-- The index type of the bad family: for every word of length `≤ k`, the fibre-bad sets in
each direction, and the discontinuity locus. -/
abbrev BadCore (n k : ℕ) : Type :=
  (Σ j : Fin (k + 1), (Fin j.val → Fin n) × Fin n) ⊕ (Σ j : Fin (k + 1), (Fin j.val → Fin n))

/-- The fibre-bad piece attached to a word and a direction. -/
def badInl {n k : ℕ} (f : (Fin n → ℝ) → ℝ)
    (u : Σ j : Fin (k + 1), (Fin j.val → Fin n) × Fin n) : Set (Fin n → ℝ) :=
  closure (fibBad (junkIt f (List.ofFn u.2.1)) u.2.2)

/-- The discontinuity piece attached to a word. -/
def badInr {n k : ℕ} (f : (Fin n → ℝ) → ℝ)
    (u : Σ j : Fin (k + 1), (Fin j.val → Fin n)) : Set (Fin n → ℝ) :=
  closure (disc (junkIt f (List.ofFn u.2)))

/-! ## The main theorem -/

theorem smooth_k_cover {S : WilkiesDesign.SOMin} (hcd : S.SharpCD) {n F D k : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : WilkiesDesign.graphOf f ∈ S.Ω F D (n + 1)) :
    ∃ (m : ℕ) (a : ℕ) (b : Polynomial ℕ) (A : Fin m → Set (Fin n → ℝ)),
      (∀ i, A i ∈ S.Ω a (b.eval D) n) ∧ (∀ i, interior (A i) = ∅) ∧
      {x : Fin n → ℝ | ¬ ContDiffAt ℝ k f x} ⊆ ⋃ i, A i := by
  -- the junk partials are definable, by iteration of `junkPartial_mem`
  have hstep : ∀ (m : ℕ) (F' : ℕ) (g : (Fin m → ℝ) → ℝ) (i : Fin m) (D' : ℕ),
      WilkiesDesign.graphOf g ∈ S.Ω F' D' (m + 1) →
        ∃ (a : ℕ) (b : Polynomial ℕ),
          WilkiesDesign.graphOf (junkP g i) ∈ S.Ω a (b.eval D') (m + 1) := by
    intro m F' g i D' hg
    rcases m with _ | m'
    · exact i.elim0
    · obtain ⟨a, b, hab⟩ := Work.WilG1.Plumb.junkPartial_mem (S := S) (n := m') (F := F')
        (D := D') i g hg
      refine ⟨a, b, ?_⟩
      rw [junkP_eq_junkPartial]
      exact hab
  obtain ⟨Ak, Bk, hBk⟩ := Junk.junkIt_mem (S := S) f k D hstep hf
  -- the finite enumeration of the bad pieces
  let e : BadCore n k ≃ Fin (Fintype.card (BadCore n k)) := Fintype.equivFin _
  let fam : Fin (Fintype.card (BadCore n k)) → Set (Fin n → ℝ) :=
    fun j => Sum.elim (badInl f) (badInr f) (e.symm j)
  -- each piece is `Ω`-definable
  have hex : ∀ u : BadCore n k,
      ∃ (a : ℕ) (b : Polynomial ℕ),
        Sum.elim (badInl f) (badInr f) u ∈ S.Ω a (b.eval D) n := by
    rintro (u | u)
    · obtain ⟨j, v, i⟩ := u
      have hlen : (List.ofFn v).length ≤ k := by
        rw [List.length_ofFn]
        exact Nat.lt_succ_iff.mp j.isLt
      have hgr := hBk (List.ofFn v) hlen
      obtain ⟨a, b, hab⟩ := Junk.fibBad_mem (S := S) (junkIt f (List.ofFn v)) hgr i
      refine ⟨a + 3 * n + 40, Polynomial.C 12 * (b.comp Bk) + Polynomial.C 60, ?_⟩
      have h1 : fibBad (junkIt f (List.ofFn v)) i ∈ S.Ω a ((b.comp Bk).eval D) n := by
        rw [Polynomial.eval_comp]
        exact hab
      exact Calc.closure_mem h1
    · obtain ⟨j, v⟩ := u
      have hlen : (List.ofFn v).length ≤ k := by
        rw [List.length_ofFn]
        exact Nat.lt_succ_iff.mp j.isLt
      have hgr := hBk (List.ofFn v) hlen
      obtain ⟨a, b, hab⟩ := Junk.disc_mem (S := S) (junkIt f (List.ofFn v)) hgr
      refine ⟨a + 3 * n + 40, Polynomial.C 12 * (b.comp Bk) + Polynomial.C 60, ?_⟩
      have h1 : disc (junkIt f (List.ofFn v)) ∈ S.Ω a ((b.comp Bk).eval D) n := by
        rw [Polynomial.eval_comp]
        exact hab
      exact Calc.closure_mem h1
  -- each piece is thin
  have hpiece_core : ∀ u : BadCore n k,
      IsNowhereDense (Sum.elim (badInl f) (badInr f) u) := by
    rintro (u | u)
    · obtain ⟨j, v, i⟩ := u
      have hlen : (List.ofFn v).length ≤ k := by
        rw [List.length_ofFn]
        exact Nat.lt_succ_iff.mp j.isLt
      have hgr := hBk (List.ofFn v) hlen
      obtain ⟨a, b, hab⟩ := Junk.fibBad_mem (S := S) (junkIt f (List.ofFn v)) hgr i
      have h1 : fibBad (junkIt f (List.ofFn v)) i ∈ S.Ω a ((b.comp Bk).eval D) n := by
        rw [Polynomial.eval_comp]
        exact hab
      have hthin : interior (fibBad (junkIt f (List.ofFn v)) i) = ∅ :=
        Junk.fibBad_thin_of_last (S := S) (fun p F' D' G hG => partialBad_thin (S := S) hcd G hG)
          (junkIt f (List.ofFn v)) hgr i
      exact IsNowhereDense.closure (thin_closure hcd h1 hthin)
    · obtain ⟨j, v⟩ := u
      have hlen : (List.ofFn v).length ≤ k := by
        rw [List.length_ofFn]
        exact Nat.lt_succ_iff.mp j.isLt
      have hgr := hBk (List.ofFn v) hlen
      obtain ⟨a, b, hab⟩ := Junk.disc_mem (S := S) (junkIt f (List.ofFn v)) hgr
      have h1 : disc (junkIt f (List.ofFn v)) ∈ S.Ω a ((b.comp Bk).eval D) n := by
        rw [Polynomial.eval_comp]
        exact hab
      have hthin : interior (disc (junkIt f (List.ofFn v))) = ∅ :=
        generic_continuity (S := S) hcd (junkIt f (List.ofFn v)) hgr
      exact IsNowhereDense.closure (thin_closure hcd h1 hthin)
  -- the chosen bounds
  let aF : BadCore n k → ℕ := fun u => Classical.choose (hex u)
  let bF : BadCore n k → Polynomial ℕ :=
    fun u => Classical.choose (Classical.choose_spec (hex u))
  have hmemF : ∀ u : BadCore n k,
      Sum.elim (badInl f) (badInr f) u ∈ S.Ω (aF u) ((bF u).eval D) n :=
    fun u => Classical.choose_spec (Classical.choose_spec (hex u))
  let aT : ℕ := Finset.univ.sup aF
  let bT : Polynomial ℕ := ∑ u : BadCore n k, bF u
  have hpiece : ∀ j : Fin (Fintype.card (BadCore n k)), IsNowhereDense (fam j) :=
    fun j => hpiece_core (e.symm j)
  have hclosed_j : ∀ j : Fin (Fintype.card (BadCore n k)), IsClosed (fam j) := by
    intro j
    rcases hu : e.symm j with u | u
    · have : fam j = badInl f u := by simp [fam, hu]
      rw [this]
      simp only [badInl]
      exact isClosed_closure
    · have : fam j = badInr f u := by simp [fam, hu]
      rw [this]
      simp only [badInr]
      exact isClosed_closure
  have hbad_closed : IsClosed (⋃ j, fam j) := isClosed_iUnion_of_finite fun j => hclosed_j j
  have hbad_nw : IsNowhereDense (⋃ j, fam j) := IsNowhereDense.iUnion hpiece
  have hbad_int : interior (⋃ j, fam j) = ∅ := hbad_closed.isNowhereDense_iff.mp hbad_nw
  -- the union is `Ω`-definable
  have hunion : (⋃ j, fam j) ∈ S.Ω aT (bT.eval D) n := by
    have h₁ : ∀ j : Fin (Fintype.card (BadCore n k)),
        fam j ∈ S.Ω aT ((bF (e.symm j)).eval D) n := by
      intro j
      exact Omega.mono (hmemF (e.symm j)) (Finset.le_sup (f := aF) (Finset.mem_univ _)) le_rfl
    have h₂ := S.union (fun j : Fin (Fintype.card (BadCore n k)) => (bF (e.symm j)).eval D)
      fam h₁
    have hsum : (∑ j : Fin (Fintype.card (BadCore n k)), (bF (e.symm j)).eval D)
        = bT.eval D := by
      change (∑ j : Fin (Fintype.card (BadCore n k)), (bF (e.symm j)).eval D)
        = (∑ u : BadCore n k, bF u).eval D
      rw [eval_sum_poly]
      exact (Fintype.sum_equiv e (fun u : BadCore n k => (bF u).eval D)
        (fun j : Fin (Fintype.card (BadCore n k)) => (bF (e.symm j)).eval D)
        (fun u => by simp)).symm
    rw [hsum] at h₂
    exact h₂
  -- the criterion applies off the bad set
  have hcrit : ContDiffOn ℝ k f (⋃ j, fam j)ᶜ := by
    refine contDiffOn_of_avoids f hf hbad_closed.isOpen_compl ?_ ?_
    · intro w hw i
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hz, hzb⟩
      have hz' : z ∈ ⋃ j, fam j := by
        refine Set.mem_iUnion.mpr
          ⟨e (Sum.inl ⟨⟨w.length, by omega⟩, (fun t => w.get t), i⟩), ?_⟩
        have h1 : e.symm (e (Sum.inl ⟨⟨w.length, by omega⟩, (fun t => w.get t), i⟩))
            = Sum.inl ⟨⟨w.length, by omega⟩, (fun t => w.get t), i⟩ :=
          Equiv.symm_apply_apply e _
        show z ∈ Sum.elim (badInl f) (badInr f) (e.symm _)
        rw [h1]
        simp only [Sum.elim_inl, badInl]
        exact subset_closure (by rw [List.ofFn_get]; exact hzb)
      exact hz hz'
    · intro w hw
      refine hbad_closed.isOpen_compl.continuousOn_iff.mpr fun y hy => ?_
      by_contra hcon
      have hy' : y ∈ ⋃ j, fam j := by
        refine Set.mem_iUnion.mpr
          ⟨e (Sum.inr ⟨⟨w.length, by omega⟩, (fun t => w.get t)⟩), ?_⟩
        have h1 : e.symm (e (Sum.inr ⟨⟨w.length, by omega⟩, (fun t => w.get t)⟩))
            = Sum.inr ⟨⟨w.length, by omega⟩, (fun t => w.get t)⟩ :=
          Equiv.symm_apply_apply e _
        show y ∈ Sum.elim (badInl f) (badInr f) (e.symm _)
        rw [h1]
        simp only [Sum.elim_inr, badInr]
        exact subset_closure (by rw [List.ofFn_get]; exact hcon)
      exact hy hy'
  refine ⟨1, aT, bT, fun _ => ⋃ j, fam j, ?_, ?_, ?_⟩
  · intro _
    exact hunion
  · intro _
    exact hbad_int
  · intro x hx
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    by_contra hxb
    exact hx (hcrit.contDiffAt (hbad_closed.isOpen_compl.mem_nhds hxb))

end Work.WilG1.Cell
