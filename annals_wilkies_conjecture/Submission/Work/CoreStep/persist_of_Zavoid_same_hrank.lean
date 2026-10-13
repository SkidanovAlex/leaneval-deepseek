/-
  Area E7 / `CoreLT_succ`, case B: **the level dichotomy for two sheets of ONE piece**.

  Read with `NOTES_S44_level_dichotomy_solved.md`.

  ## Mathematical content

  `Submission/Work/CoreStep/persist_of_Zavoid_cross2.lean` proves the level dichotomy for two
  sheets belonging to two strata `T ≠ T'` (with the extra hypothesis `hdisj`, which turned out to
  be **unused** and has been removed from its statement).  Its proof uses `hrank'` — the
  immersion condition `projRank T' z = N - T'.j` — only at the *second* sheet point, through
  `Work.WilE7.CoreStep.basePrLin_injective_on_ker_jac`.

  Hence the **same-piece** dichotomy is the special case `T' := T` of `cross2`: the only
  hypotheses the proof needs about the second sheet point are the ones the proof needs about the
  first (they are the same set!), and `havoid` in the same-piece form is *unconditional* in the
  base point, hence implies the `hlev`-conditioned form used by `cross2`.

  This closes the node `Work.CoreStep.persist_of_Zavoid_same` (which was left with a `sorry` and
  whose "crux" passes S40/S43 tried to attack with Remmert-style analytic geometry): the
  accessibility of the second branch is exactly what `hrank` (i.e. the immersion/rank condition
  on the stratum) provides, and no irreducibility or local Remmert theorem is needed.

  In the `CoreLT_succ` application the sheets come from **graph-like** strata (`S.j = m+1`, i.e.
  zero-dimensional fibres), for which `hrank` is *automatic*: the fibre block of the Jacobian is
  the square `(m+1) × (m+1)` matrix whose rank `S.j = m+1` is full, hence invertible
  (`Work.WilE7.DimAPI.projRank_eq_dim_of_sub_fibreGood`, node N1, gives `projRank S z = N - S.j`
  from `S.Good`, `S.j = m + 1` and finite fibres); and `S.j = m+1` itself follows from `hfin`
  (`Work.CoreStep.fibre_infinite_of_j_lt`).

  ## What is *not* claimed

  The dichotomy is **not** claimed here for a piece that is not immersive (a "fold" of the base
  projection): there the branch of a sheet need not be reachable from the other branch, and the
  S43 counterexamples (`branch_covers_of_levelPair{2}`) show that the naive statements are false.
  The `hrank` hypothesis is exactly the missing input, and the callers have it.
-/
import Mathlib
import Submission.Work.CoreStep.persist_of_Zavoid_same
import Submission.Work.CoreStep.persist_of_Zavoid_cross2

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.CoreStep

/-! ## §1. Continuity of the sheet pair point -/

/-- `absPt` is continuous (it is the reindexing `Fin (0+N) → Fin N`). -/
theorem continuous_absPt {N : ℕ} :
    Continuous fun z : Fin (0 + N) → ℝ => Work.WilE7.MainDesign.absPt z := by
  rw [continuous_pi_iff]
  intro i
  exact continuous_apply _

/-- `absPtUp` is continuous (it is the reindexing `Fin N → Fin (0+N)`). -/
theorem continuous_absPtUp {n m : ℕ} :
    Continuous fun u : Fin (n + (m + 1)) → ℝ => absPtUp (n := n) (m := m) u := by
  rw [continuous_pi_iff]
  intro i
  exact continuous_apply _

/-- The pair point of two piece points depends continuously on the pair. -/
theorem continuous_pairPtUp {n m : ℕ} :
    Continuous fun p : (Fin (pDim n m) → ℝ) × (Fin (pDim n m) → ℝ) =>
      pairPtUp (n := n) (m := m) p.1 p.2 := by
  rw [continuous_pi_iff]
  intro i
  simp only [pairPtUp, pairPt, absPtInv]
  have hG : Continuous fun q : (Fin (n + (m + 1)) → ℝ) × (Fin (n + (m + 1)) → ℝ) =>
      Fin.append q.1 q.2 := Fin.continuous_append (n + (m + 1)) (n + (m + 1))
  have hF : Continuous fun p : (Fin (pDim n m) → ℝ) × (Fin (pDim n m) → ℝ) =>
      (Work.WilE7.MainDesign.absPt p.1, Work.WilE7.MainDesign.absPt p.2) :=
    Continuous.prodMk (continuous_absPt.comp continuous_fst)
      (continuous_absPt.comp continuous_snd)
  exact ((continuous_apply (Fin.cast (Nat.zero_add (pPair n m)) i)).comp hG).comp hF

/-- `ContinuousOn` of a pair of continuous maps. -/
theorem continuousOn_prodMk {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] {C : Set α} {f : α → β} {g : α → γ}
    (hf : ContinuousOn f C) (hg : ContinuousOn g C) :
    ContinuousOn (fun x => (f x, g x)) C := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact Continuous.prodMk hf.domRestrict hg.domRestrict

/-- The sheet pair point is continuous on `C` as soon as the sheets are. -/
theorem continuousOn_sheetPairPt {n m k : ℕ} {C : Set (Fin n → ℝ)}
    (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j : Fin k, ContinuousOn (s j) C) (j j' : Fin k) :
    ContinuousOn (fun x : Fin n → ℝ => sheetPairPt s j j' x) C := by
  have happ : ∀ j : Fin k, ContinuousOn (fun x : Fin n → ℝ => Fin.append x (s j x)) C := by
    intro j
    exact (Fin.continuous_append n (m + 1)).comp_continuousOn
      (continuousOn_prodMk continuousOn_id (hcont j))
  have h1 : ContinuousOn
      (fun x : Fin n → ℝ => absPtUp (n := n) (m := m) (Fin.append x (s j x))) C :=
    continuous_absPtUp.comp_continuousOn (happ j)
  have h2 : ContinuousOn
      (fun x : Fin n → ℝ => absPtUp (n := n) (m := m) (Fin.append x (s j' x))) C :=
    continuous_absPtUp.comp_continuousOn (happ j')
  have h := (continuous_pairPtUp (n := n) (m := m)).comp_continuousOn
    (continuousOn_prodMk h1 h2)
  exact h

/-! ## §2. `projFirst` of an appended point -/

/-- `projFirst` of a `Fin.append` is the first block. -/
theorem projFirst_finAppend {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) :
    WilkiesDesign.E.projFirst n m (Fin.append x y) = x := by
  funext i
  simp only [WilkiesDesign.E.projFirst, Fin.append_left]

/-- The base projection of `absPtUp (Fin.append x y)` is `x`. -/
theorem projFirst_absPtInv_absPtUp_finAppend {n m : ℕ} (x : Fin n → ℝ)
    (y : Fin (m + 1) → ℝ) :
    WilkiesDesign.E.projFirst n (m + 1)
      (Work.WilE7.CoreStep.absPtInv (n := n) (m := m)
        (absPtUp (n := n) (m := m) (Fin.append x y))) = x := by
  rw [absPtInv_absPtUp]
  exact projFirst_finAppend x y

/-! ## §3. The level dichotomy for two sheets of one piece -/

/-- **The level dichotomy (same piece).**  For a `Good` absolute stratum `T` on which the base
projection is immersive (`hrank : projRank T z = N - T.j`), with finite fibres over `C`, sheets
`s` covering the fibres of `T` over `C`, and a list `Wl` of `Good` strata covering the
level-agreeing pair set `absLevelPairSet T T` and avoiding (in the sense of `havoid`) the pair
points of low-dimensional pieces and of the frontiers of the top-dimensional ones: two sheets that
agree in their last coordinate at a point of `C` agree on a neighbourhood of that point in `C`.

This is the special case `T' = T` of `Work.CoreStep.persist_of_Zavoid_cross2` (whose otherwise
unused disjointness hypothesis has been removed); `havoid` is unconditional in the base point, so
it implies the `hlev`-conditioned hypothesis of `cross2`. -/
theorem persist_of_Zavoid_same_hrank {n m k : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good)
    (hrank : ∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j)
    (hfin : ∀ x : Fin n → ℝ,
      (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x).Finite)
    (C : Set (Fin n → ℝ))
    (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j : Fin k, ContinuousOn (s j) C)
    (hinj : ∀ x : Fin n → ℝ, x ∈ C → Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C,
      Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x (s j x)) ∈ T.X.set)
    (hcov : ∀ z : Fin (n + (m + 1)) → ℝ, z ∈ Work.WilE7.MainDesign.absSet T →
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst n (m + 1) z) =
        WilkiesDesign.E.projSnd n (m + 1) z)
    (Wl : List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)))
    (hWlgood : ∀ W ∈ Wl, W.Good)
    (hWlsub : ∀ W ∈ Wl, W.X.set ⊆ (Work.WilE7.CoreStep.absLevelPairSet T T).set)
    (hWlcov : (Work.WilE7.CoreStep.absLevelPairSet T T).set = ⋃ W ∈ Wl, W.X.set)
    (havoid : ∀ (j j' : Fin k) (x₀ : Fin n → ℝ), x₀ ∈ C →
      (∀ W ∈ Wl, Work.WilE7.CoreStep.pPair n m - W.j < n + (m + 1) - T.j →
        Work.WilE7.CoreStep.pairPtUp
          (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))
          (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j' x₀)))
            ∉ W.X.set) ∧
      (∀ W ∈ Wl, Work.WilE7.CoreStep.pPair n m - W.j = n + (m + 1) - T.j →
        Work.WilE7.CoreStep.pairPtUp
          (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))
          (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j' x₀)))
            ∉ closure W.X.set \ W.X.set)) :
    ∀ (j j' : Fin k) (x₀ : Fin n → ℝ), x₀ ∈ C →
      (s j x₀) (Fin.last m) = (s j' x₀) (Fin.last m) →
      ∃ U ∈ nhds x₀, ∀ x ∈ C ∩ U, (s j x) (Fin.last m) = (s j' x) (Fin.last m) := by
  intro j j' x₀ hx₀ hlev
  exact persist_of_Zavoid_cross2 T T hT hT hrank hrank hfin hfin C s s hcont hcont
    hinj hinj hsub hsub hcov hcov Wl hWlgood hWlsub hWlcov
    (fun j j' x₀ hx₀ _ => ⟨(havoid j j' x₀ hx₀).1, (havoid j j' x₀ hx₀).2⟩)
    j j' x₀ hx₀ hlev

end Work.CoreStep
