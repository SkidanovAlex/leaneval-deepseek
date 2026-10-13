/-
  STATUS (see `Submission/Work/CoreStep/NOTES_persist_of_Zavoid_same_analysis.md`, and
  `Submission/Work/CoreStep/NOTES_S40_pair_piece_dim_and_levelImm.md` for the current pass).

  ## PASS S40 (read NOTES_S40_pair_piece_dim_and_levelImm.md)

  The target is now reduced to: `Work.CoreStep.persist_same_of_levelImm` (delegated: the
  target's conclusion under the extra hypothesis `himm`, i.e. `(π_n, λ)` immersive at every sheet
  point — this is `cross2`'s proof with `hrank` replaced by the level-agreement clause of the pair
  set), `Work.CoreStep.pair_piece_dim_le` (delegated: `pPair - W.j ≤ dim T` for a Good piece of the
  level pair set, which turns `havoid`'s `≥` into `dim W₀ = dim T`), and the single remaining case
  (CRUX): `himm` fails at a sheet point.  In the CRUX case a nonzero tangent direction `w ≠ 0` of
  `T` at that point has `basePrLin w = 0` and `levelOf w = 0`; the workspace has no branch/degree
  theory for this (everything built for this area is driven by `hrank`).  See §3 of that note.

  ---------------------------------------------------------------------------------------------

  UPDATE (this pass).  The reduction has been sharpened and the first two steps are now *proved*;
  three supporting lemmas were dispatched (see the ends of this comment).

  Notation: `N = n + (m+1)`, `D = N - T.j` (the dimension of `T`), `p₀` (resp. `q₀`) the sheet
  point of `s j` (resp. `s j'`) at `x₀`, `P₀ = pairPtUp p₀ q₀`.

  PROVED in this file:

  * `exists_pairPtUp_of_mem_absLevelPairSet'` (extraction): a point `z` of `absLevelPairSet T T`
    is `pairPtUp u v` for piece points `u`, `v` with a common base and equal last coordinates;
  * `level_agree_of_witness` (assembly): if for every `x ∈ C` near `x₀` the *level-agreeing* pair
    set contains a pair of piece points over `x` lying in the two uniqueness neighbourhoods
    `VU ∋ p₀`, `VU' ∋ q₀` of `persist_aux_sheet_unique`, then the two sheets agree in level on
    `C` near `x₀`.  (This is step (C3) above; it uses only the two proved auxiliaries.)
  * `exists_piece_of_pairPtUp` (extraction of the piece): combining the auxiliary with `hWlcov`
    and `havoid`'s first clause, the pair point `P₀` lies in some `W ∈ Wl` with
    `pPair n m - W.j ≥ D`, i.e. `dim W ≥ D`.  (This is step (C2)'s input.)

  THE CRUX, precisely.  Let `W₀` be that piece and `M` its local manifold through `P₀`
  (`dim M = pPair n m - W₀.j ≥ D`).  Then, with `M` shrunk to a small neighbourhood of `P₀`:
  for `u ∈ M` (a pair), write `u = (φ(a), ψ(b))` where `φ`, `ψ` are charts of the manifold
  `absSet T` at `p₀`, `q₀`; this identifies (a small piece of) `M` with a manifold germ
  `M̃ ⊆ Σ := {(a,b) : β(a,b) = 0, δ(a,b) = 0}` where
  `β(a,b) = π(φ a) - π(ψ b)` ("same base") and `δ(a,b) = λ(φ a) - λ(ψ b)` ("same level"), and
  `rank dβ(0) = dim (im dπ_{p₀} + im dπ_{q₀}) =: s` (with `Λ := dim M̃ = dim M`).
  The sheet-pair of `s j`, `s j'` over `x ∈ C` is the pair `(a(x), b(x)) ∈ Σ⁰ := {β = 0}`, and it
  tends to `(0,0)`; the conclusion is exactly `(a(x),b(x)) ∈ Σ` for `x ∈ C` near `x₀`.

  Two ingredients now available make this tractable:

  * `Work.WilE7.DimAPI.finrank_le_of_germ_subset_zero` (PROVED): a chart whose germ lies in
    `{f = 0}` has dimension at most `M - finrank (fderiv f 0).range` (chain rule + tangent space).
    Applied to `(β, δ)` this gives `Λ ≤ 2D - s`, so `s ≥ D` forces `Λ = D`.  Note `s ≥ D` holds as
    soon as one of the two sheet points is a *regular* point of `π` (rank `= D`); the case where
    both are critical is excluded by `persist_aux_sheet_unique`: over `x ∈ C` the fibre of
    `absSet T` in a neighbourhood of `p₀` is a *single* point, so a second branch through `p₀`
    would give two sheet values with the same limit at `x₀`, contradicting `hinj`.
  * `Work.WilE7.DimAPI.analytic_eq_zero_on_levelSet_germ` (dispatched): if `rank dβ = D` on a
    neighbourhood of `0` (constant rank — "the level set is a manifold") and a chart germ `γ` lies
    in `{β = 0} ∩ {δ = 0}`, then `{β = 0} ⊆ {δ = 0}` near `0`, i.e. the level agreement is *total*
    on the coincidence set.  A reviewer's counterexample shows the constant-rank hypothesis is
    indispensable.  This lemma, applied to `M̃ ⊆ Σ` with `Λ = D = rank dβ(0)`, is the crux:
    it yields `δ ≡ 0` on the germ `Σ⁰`, whence the sheet-pairs (which lie in `Σ⁰` and tend to
    `(0,0)`) lie in `Σ`.

  Also dispatched: `Work.WilE7.DimAPI.rank_eq_dim_of_injOn` (constant-rank + injective ⟹ full
  rank, the Rank Theorem step) and `Work.WilE7.DimAPI.chart_of_good_mem` (the local analytic
  chart of a `Good` absolute stratum, which supplies the `γ` above).

  REMAINING WORK (fourth pass — see `NOTES_persist_of_Zavoid_same_analysis.md` §6).
  **The target is now machine-reduced to ONE closure statement.**  The file proves (sorry-free):

  * `level_agree_of_pairPtUp_mem` — the *reverse extraction*: a pair point of two points that lies
    in `(absLevelPairSet T T).set` has equal last vertical coordinates;
  * `pairPtUp_apply`, `pairPtUp_inj` — the `0 + ·` bookkeeping and injectivity of `pairPtUp`;
  * `sheetPairPt s j j' x` — notation for the pair point of the two sheets at `x`;
  * **`persist_of_Zavoid_same_of_closure`** — the target follows from the *single* statement

      **(GAP′)**  `∀ x ∈ C, ∃ W ∈ Wl, pPair n m - W.j = n + (m+1) - T.j ∧
                  sheetPairPt s j j' x ∈ closure W.X.set`,

    because `havoid`'s second clause at the base point `x` forbids membership of `sheetPairPt s j j' x`
    in `closure W.X.set \ W.X.set`, so closure plus the clause forces the pair point *into* the
    piece, and the piece lies in the level-agreeing pair set; the reverse extraction then gives the
    level agreement at `x`.  This is the role of `havoid`'s **second** clause, and it is exactly the
    device that turns "the pair point approaches a top-dimensional piece" into "the pair point is in
    the level-agreeing set".

  So the whole remaining mathematical content is (GAP′).  Its mechanism (NOTES §6.3): with the
  charts `γ_p`, `γ_q` of `absSet T` at the two sheet points and `β, δ` as in §5.6, the pairs
  `PP(x)` are the points of `B := {β = 0}`, `dim B = D`, and `W₀`'s germ equals a `D`-dimensional
  component of `B`'s germ.  If `G := π∘γ_p` or `H := π∘γ_q` is an immersion at its centre then `B`
  is a graph over the second variable, hence irreducible, and `W₀`'s germ *is* `B`'s germ, so the
  `PP(x)` (which converge to `P₀ ∈ W₀.X.set`) lie in the closure of `W₀.X.set` — (GAP′) holds; this
  is a call to `Work.WilE7.DimAPI.analytic_eq_zero_on_levelSet_germ` once `β` has constant rank `D`
  near `0`, which in particular holds when `D = n` (`T.j = m+1`) with the base projection of rank
  `D` at the two sheet points (`Work.WilE7.CoreStep.piFamily`'s `hrank`).  If both `G` and `H` are
  *critical* at their centres, then the branches of the two inverses *merge* at the critical value
  and over `x ∈ C` the fibre of each chart is a singleton, so `C` lies at the merging locus, where
  the branches of `B` coalesce; the `PP(x)` then lie in the closure of every branch of `B` — and in
  particular of `W₀`'s — which again is (GAP′).  Formalising that second regime needs the local
  branch/degree (real Puiseux) theory of an analytic map germ, which the workspace does not have.

  THIRD PASS (read `NOTES_..._analysis.md` §5 for the full text).  Status of the tools and the
  sharpening of the single remaining gap.

  ALL TOOLS ARE NOW PROVED (sorry-free): `chart_of_good_mem`; `finrank_le_of_germ_subset_zero`;
  `submersion_reduction_of_rank`; `levelSet_subset_image_of_inj`;
  **`analytic_eq_zero_on_levelSet_germ`** (it was dispatched by the second pass and has since been
  completed — the `g`-step is `submersion_reduction_of_rank`); `rank_eq_dim_of_injOn`.  Two
  further provable structural lemmas were dispatched in this pass:
  `Work.WilE7.DimAPI.finrank_le_of_finite_fibres` (an analytic germ `(ℝ^K,0) → ℝ^P` with
  eventually finite fibres satisfies `K ≤ P`) and
  `Work.WilE7.DimAPI.germ_eq_of_subset_of_inj_fderiv` (two `K`-dimensional manifold germs at a
  point, one locally inside the other, coincide).

  THE PAPER'S MECHANISM.  `wilkies_paper/pfaff-wilkie.tex` (parametric cell step): after shrinking
  a cell, "**removing a smaller-dimensional part, we may assume that the projection `π_n|_X` is
  everywhere submersive**".  `havoid` is the formalisation of "the pair point lies in the
  top-dimensional part of the level-pair stratification", so the node is *exactly* that step.

  NEW (this pass), the key quantitative fact: **`dim W₀ = D` exactly.**  Pulling `W₀`'s germ back
  to the two branch charts gives a manifold germ `ρ : ℝ^Λ → ℝ^{2D}` (`Λ := pPair - W₀.j ≥ D` by
  `havoid`) with `im ρ ⊆ {β = 0}`; the projection `(a,b) ↦ b` along `ρ` has finite fibres (a fibre
  point `(a,b₀)` satisfies `π(γ_p a) = π(γ_q b₀)`, so `γ_p a` is in a `π`-fibre of `absSet T`,
  finite by `hfin`), hence `finrank_le_of_finite_fibres` gives `Λ ≤ D`, so `Λ = D`.  Consequently
  `finrank_le_of_germ_subset_zero` with `f = β` gives `s ≤ D`.

  THE SINGLE REMAINING GAP.  Show `δ(a(x),b(x)) = 0` for `x ∈ C` near `x₀` (in the chart
  coordinates of §5.6 of the NOTES).  The constant-rank hypothesis of
  `analytic_eq_zero_on_levelSet_germ` is *indispensable* — a reviewer's example
  (`β(x₁,x₂,x₃,x₄) = (x₃,x₄,x₁x₂)`, `δ = x₁`, `γ(t) = (0,t,0,0)`, where `L = M - s` and `{β = 0}`
  has two branches) shows that rank `D` *at* `0` is not enough.  In our setting the gap is
  therefore exactly: *the sheet-pair branch of `{β = 0}` is the same branch as `W₀`'s* — i.e. the
  submersivity of the two sheet branches over the base, or its substitute via the
  critical-value/branch analysis (`C` is forced into the critical-value sets of both branches,
  where a local-degree/parity argument is needed).  The CALLER (`πFamily`) supplies this input as
  `hrank` (`projRank T z = N - T.j`); with `hrank` added to the hypotheses the node is provable
  with today's tools.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.GermDefs
import Submission.Work.CoreStep.persist_aux_pairPtUp_mem
import Submission.Work.CoreStep.persist_aux_sheet_unique

namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.CoreStep

/-! ## §1. Bookkeeping: the two blocks of a point of the level-agreeing pair set -/

/-- **Elimination of a point of `absLevelPairSet`.**  A point `z` of the level-agreeing pair set is
the pair point of two piece points `u`, `v` over a common base point with equal last coordinates. -/
theorem exists_pairPtUp_of_mem_absLevelPairSet' {n m : ℕ}
    (T T' : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    {z : Fin (0 + Work.WilE7.CoreStep.pPair n m) → ℝ}
    (hz : z ∈ (Work.WilE7.CoreStep.absLevelPairSet T T').set) :
    ∃ u v : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ,
      u ∈ T.X.set ∧ v ∈ T'.X.set ∧ Work.WilE7.CoreStep.pairPtUp u v = z ∧
      (WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) =
        WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv v)) ∧
      ((WilkiesDesign.E.projSnd n (m + 1) (Work.WilE7.CoreStep.absPtInv u)) ⟨m, by omega⟩ =
        (WilkiesDesign.E.projSnd n (m + 1) (Work.WilE7.CoreStep.absPtInv v)) ⟨m, by omega⟩) := by
  have h := hz
  rw [Work.WilE7.CoreStep.absLevelPairSet, Work.WilE7.sp_reindex_set] at h
  rw [Work.WilE7.levelGlue_set] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  set z' : Fin ((n + (m + 1)) + (n + (m + 1))) → ℝ :=
    fun i => z ((Work.WilE7.finEquiv (Nat.zero_add (Work.WilE7.CoreStep.pPair n m))).symm i)
    with hz'
  have hz'z : ∀ i, z' (Fin.cast (Nat.zero_add (Work.WilE7.CoreStep.pPair n m)) i) = z i := by
    intro i
    show z ((Work.WilE7.finEquiv (Nat.zero_add (Work.WilE7.CoreStep.pPair n m))).symm
      (Fin.cast (Nat.zero_add (Work.WilE7.CoreStep.pPair n m)) i)) = z i
    congr 1
  have hsplit : Fin.append (WilkiesDesign.E.projFirst (n + (m + 1)) (n + (m + 1)) z')
      (WilkiesDesign.E.projSnd (n + (m + 1)) (n + (m + 1)) z') = z' :=
    SheetUnique.append_projFirst_projSnd z'
  refine ⟨Work.WilE7.CoreStep.absPtUp (n := n) (m := m)
      (WilkiesDesign.E.projFirst (n + (m + 1)) (n + (m + 1)) z'),
    Work.WilE7.CoreStep.absPtUp (n := n) (m := m)
      (WilkiesDesign.E.projSnd (n + (m + 1)) (n + (m + 1)) z'), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Work.WilE7.CoreStep.mem_absReindex] at h1
    exact h1
  · rw [Work.WilE7.CoreStep.mem_absReindex] at h2
    exact h2
  · -- the pair point reassembles `z`
    funext j
    show Fin.append
      (Work.WilE7.CoreStep.absPtInv (Work.WilE7.CoreStep.absPtUp (n := n) (m := m)
        (WilkiesDesign.E.projFirst (n + (m + 1)) (n + (m + 1)) z')))
      (Work.WilE7.CoreStep.absPtInv (Work.WilE7.CoreStep.absPtUp (n := n) (m := m)
        (WilkiesDesign.E.projSnd (n + (m + 1)) (n + (m + 1)) z')))
      (Fin.cast (Nat.zero_add (Work.WilE7.CoreStep.pPair n m)) j) = z j
    rw [Work.WilE7.CoreStep.absPtInv_absPtUp, Work.WilE7.CoreStep.absPtInv_absPtUp]
    rw [← hz'z j, hsplit]
  · rw [Work.WilE7.CoreStep.absPtInv_absPtUp, Work.WilE7.CoreStep.absPtInv_absPtUp, hz']
    exact h3
  · rw [Work.WilE7.CoreStep.absPtInv_absPtUp, Work.WilE7.CoreStep.absPtInv_absPtUp, hz']
    exact h4

/-! ## §2. The assembly step -/

/-- **Assembly.**  Suppose that for every `x ∈ C` near `x₀` the level-agreeing pair set contains a
pair of piece points over `x`, the first lying in an arbitrarily small neighbourhood `V` of
`(x₀, s j x₀)` and the second in one `V'` of `(x₀, s j' x₀)`.  Then, near `x₀`, the two sheets
`s j` and `s j'` agree in their last coordinate.

The point is that the local uniqueness `Work.CoreStep.persist_aux_sheet_unique` identifies such a
pair of piece points with the two sheet values at `x`, so the (already known) equality of the last
coordinates of the pair forces the sheets to agree. -/
theorem level_agree_of_witness {n m k : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ))
    (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j : Fin k, ContinuousOn (s j) C)
    (hinj : ∀ x : Fin n → ℝ, x ∈ C → Function.Injective fun j : Fin k => s j x)
    (hcov : ∀ z : Fin (n + (m + 1)) → ℝ, z ∈ Work.WilE7.MainDesign.absSet T →
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst n (m + 1) z) =
        WilkiesDesign.E.projSnd n (m + 1) z)
    (j j' : Fin k) (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ C)
    (VU : Set (Fin (n + (m + 1)) → ℝ)) (hVU : VU ∈ nhds (Fin.append x₀ (s j x₀)))
    (VU' : Set (Fin (n + (m + 1)) → ℝ)) (hVU' : VU' ∈ nhds (Fin.append x₀ (s j' x₀)))
    (huniq : ∀ x ∈ C, ∀ z ∈ Work.WilE7.MainDesign.absSet T,
      WilkiesDesign.E.projFirst n (m + 1) z = x → z ∈ VU → z = Fin.append x (s j x))
    (huniq' : ∀ x ∈ C, ∀ z ∈ Work.WilE7.MainDesign.absSet T,
      WilkiesDesign.E.projFirst n (m + 1) z = x → z ∈ VU' → z = Fin.append x (s j' x))
    (U : Set (Fin n → ℝ)) (hU : U ∈ nhds x₀)
    (hwit : ∀ x ∈ C ∩ U, ∃ u v : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ,
      u ∈ T.X.set ∧ v ∈ T.X.set ∧ Work.WilE7.MainDesign.absPt u ∈ VU ∧
        Work.WilE7.MainDesign.absPt v ∈ VU' ∧
        WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) = x ∧
        WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv v) = x ∧
        (WilkiesDesign.E.projSnd n (m + 1) (Work.WilE7.CoreStep.absPtInv u)) ⟨m, by omega⟩ =
          (WilkiesDesign.E.projSnd n (m + 1) (Work.WilE7.CoreStep.absPtInv v)) ⟨m, by omega⟩) :
    ∀ x ∈ C ∩ U, (s j x) (Fin.last m) = (s j' x) (Fin.last m) := by
  intro x hx
  obtain ⟨u, v, hu, hv, huV, hvV, hub, hvb, hlev⟩ := hwit x hx
  have huabs : Work.WilE7.MainDesign.absPt u ∈ Work.WilE7.MainDesign.absSet T :=
    ⟨u, hu, rfl⟩
  have hvabs : Work.WilE7.MainDesign.absPt v ∈ Work.WilE7.MainDesign.absSet T :=
    ⟨v, hv, rfl⟩
  have h1 : Work.WilE7.MainDesign.absPt u = Fin.append x (s j x) :=
    huniq x hx.1 _ huabs hub huV
  have h2 : Work.WilE7.MainDesign.absPt v = Fin.append x (s j' x) :=
    huniq' x hx.1 _ hvabs hvb hvV
  have key : (WilkiesDesign.E.projSnd n (m + 1) (Fin.append x (s j x))) ⟨m, by omega⟩ =
      (WilkiesDesign.E.projSnd n (m + 1) (Fin.append x (s j' x))) ⟨m, by omega⟩ := by
    rw [← h1, ← h2]
    exact hlev
  rw [show (WilkiesDesign.E.projSnd n (m + 1) (Fin.append x (s j x))) ⟨m, by omega⟩ =
      (s j x) (Fin.last m) from by
        rw [show (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m from Fin.ext rfl,
          WilkiesDesign.E.projSnd, Fin.append_right],
    show (WilkiesDesign.E.projSnd n (m + 1) (Fin.append x (s j' x))) ⟨m, by omega⟩ =
      (s j' x) (Fin.last m) from by
        rw [show (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m from Fin.ext rfl,
          WilkiesDesign.E.projSnd, Fin.append_right]] at key
  exact key

/-! ## §3. The pair point lies in a piece of dimension at least `dim T` -/

/-- **Extraction of the Good piece through the pair point.**  If the pair point of the two sheet
values at `x₀` lies in the level-agreeing pair set (which holds whenever the two sheets agree in
their last coordinate) and the list `Wl` covers that set, then — by the avoidance hypothesis
`havoid` — the piece of `Wl` containing the pair point has dimension at least `n + (m+1) - T.j`. -/
theorem exists_piece_of_pairPtUp {n m k : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ))
    (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hsub : ∀ j : Fin k, ∀ x ∈ C,
      Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x (s j x)) ∈ T.X.set)
    (j j' : Fin k) (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ C)
    (hlev : (s j x₀) (Fin.last m) = (s j' x₀) (Fin.last m))
    (Wl : List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)))
    (hWlcov : (Work.WilE7.CoreStep.absLevelPairSet T T).set = ⋃ W ∈ Wl, W.X.set)
    (havoid : ∀ W ∈ Wl, Work.WilE7.CoreStep.pPair n m - W.j < n + (m + 1) - T.j →
      Work.WilE7.CoreStep.pairPtUp
        (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))
        (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j' x₀)))
          ∉ W.X.set) :
    ∃ W ∈ Wl, Work.WilE7.CoreStep.pairPtUp
        (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))
        (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j' x₀)))
          ∈ W.X.set ∧ n + (m + 1) - T.j ≤ Work.WilE7.CoreStep.pPair n m - W.j := by
  have hmem := persist_aux_pairPtUp_mem T C s hsub j j' x₀ hx₀ hlev
  rw [hWlcov] at hmem
  obtain ⟨W, hWmem, hWX⟩ := Set.mem_iUnion₂.mp hmem
  refine ⟨W, hWmem, hWX, ?_⟩
  by_contra hlt
  push_neg at hlt
  exact havoid W hWmem hlt hWX

/-! ## §4. The reverse extraction, and the reduction of the target to one closure statement

Read `NOTES_persist_of_Zavoid_same_analysis.md` §6 for the analysis.  In short:

* `pairPtUp_inj` / `level_agree_of_pairPtUp_mem`: the *converse* of `mem_absLevelPairSet` — a pair
  point of two sheet points that lies in the level-agreeing pair set has equal last vertical
  coordinates.
* `persist_of_Zavoid_same_of_closure`: the target follows from the single statement that the sheet
  pair point at a base `x ∈ C` lies in the **closure** of a `dim T`-dimensional piece of `Wl`.
  Indeed `havoid`'s *second* clause then forces the pair point into the piece itself, and the piece
  is contained in the level-agreeing pair set.  (This is why `havoid`'s second clause is needed: it
  converts "closure" into "belongs".)
-/

/-- The coordinates of `pairPtUp` in terms of `pairPt` (the `0 + ·` bookkeeping). -/
theorem pairPtUp_apply {n m : ℕ} (u v : Fin (pDim n m) → ℝ) (i : Fin (pPair n m)) :
    pairPtUp u v (Fin.cast (Nat.zero_add (pPair n m)).symm i) = pairPt u v i := by
  simp [pairPtUp]

/-- **Injectivity of `pairPtUp`.** -/
theorem pairPtUp_inj {n m : ℕ} {u v u' v' : Fin (pDim n m) → ℝ}
    (h : pairPtUp u v = pairPtUp u' v') : u = u' ∧ v = v' := by
  have hfun : pairPt u v = pairPt u' v' := by
    funext i
    have hh := congrFun h (Fin.cast (Nat.zero_add (pPair n m)).symm i)
    rwa [pairPtUp_apply, pairPtUp_apply] at hh
  have h1 : absPtInv u = absPtInv u' := by
    have hh : WilkiesDesign.E.projFirst (n + (m + 1)) (n + (m + 1)) (pairPt u v) =
        WilkiesDesign.E.projFirst (n + (m + 1)) (n + (m + 1)) (pairPt u' v') := by
      rw [hfun]
    rwa [projFirst_pairPt, projFirst_pairPt] at hh
  have h2 : absPtInv v = absPtInv v' := by
    have hh : WilkiesDesign.E.projSnd (n + (m + 1)) (n + (m + 1)) (pairPt u v) =
        WilkiesDesign.E.projSnd (n + (m + 1)) (n + (m + 1)) (pairPt u' v') := by
      rw [hfun]
    rwa [projSnd_pairPt, projSnd_pairPt] at hh
  constructor
  · rw [← absPtUp_absPtInv u, h1, absPtUp_absPtInv u']
  · rw [← absPtUp_absPtInv v, h2, absPtUp_absPtInv v']

/-- **The reverse extraction.**  A pair point of two points that lies in the level-agreeing pair
set has equal last vertical coordinates. -/
theorem level_agree_of_pairPtUp_mem {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (u v : Fin (pDim n m) → ℝ)
    (hP : pairPtUp u v ∈ (absLevelPairSet T T).set) :
    (WilkiesDesign.E.projSnd n (m + 1) (absPtInv u)) (Fin.last m) =
      (WilkiesDesign.E.projSnd n (m + 1) (absPtInv v)) (Fin.last m) := by
  obtain ⟨u', v', -, -, hP', -, hlev'⟩ := exists_pairPtUp_of_mem_absLevelPairSet' T T hP
  obtain ⟨rfl, rfl⟩ := pairPtUp_inj hP'
  rw [show (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m from Fin.ext rfl] at hlev'
  exact hlev'

/-- The pair point of the two sheets `j`, `j'` at the base point `x₀`. -/
def sheetPairPt {n m k : ℕ} (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (j j' : Fin k) (x₀ : Fin n → ℝ) : Fin (0 + pPair n m) → ℝ :=
  pairPtUp (absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))
    (absPtUp (n := n) (m := m) (Fin.append x₀ (s j' x₀)))

/-- **The target reduced to one geometric statement.**  If for every base point `x ∈ C` the sheet
pair point at `x` lies in the closure of a `dim T`-dimensional piece of `Wl`, then the conclusion of
`persist_of_Zavoid_same` holds; `havoid`'s second clause upgrades closure to membership. -/
theorem persist_of_Zavoid_same_of_closure {n m k : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ))
    (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (Wl : List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)))
    (hWlsub : ∀ W ∈ Wl, W.X.set ⊆ (Work.WilE7.CoreStep.absLevelPairSet T T).set)
    (havoidb : ∀ (j j' : Fin k) (x₀ : Fin n → ℝ), x₀ ∈ C →
      ∀ W ∈ Wl, Work.WilE7.CoreStep.pPair n m - W.j = n + (m + 1) - T.j →
        sheetPairPt s j j' x₀ ∉ closure W.X.set \ W.X.set)
    (hclosure : ∀ (j j' : Fin k) (x₀ : Fin n → ℝ), x₀ ∈ C →
      ∃ W ∈ Wl, Work.WilE7.CoreStep.pPair n m - W.j = n + (m + 1) - T.j ∧
        sheetPairPt s j j' x₀ ∈ closure W.X.set) :
    ∀ (j j' : Fin k) (x₀ : Fin n → ℝ), x₀ ∈ C →
      (s j x₀) (Fin.last m) = (s j' x₀) (Fin.last m) →
      ∃ U ∈ nhds x₀, ∀ x ∈ C ∩ U, (s j x) (Fin.last m) = (s j' x) (Fin.last m) := by
  intro j j' x₀ hx₀ _
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  intro x hx
  obtain ⟨W, hW, hdim, hclos⟩ := hclosure j j' x hx.1
  have hnot := havoidb j j' x hx.1 W hW hdim
  have hmem : sheetPairPt s j j' x ∈ W.X.set := by
    by_contra hcon
    exact hnot ⟨hclos, hcon⟩
  have key := level_agree_of_pairPtUp_mem T
    (absPtUp (n := n) (m := m) (Fin.append x (s j x)))
    (absPtUp (n := n) (m := m) (Fin.append x (s j' x)))
    (hWlsub W hW hmem)
  rw [absPtInv_absPtUp, absPtInv_absPtUp] at key
  simpa only [WilkiesDesign.E.projSnd, Fin.append_right] using key

/- **RETIRED STATEMENT (pass S44).**  The theorem `persist_of_Zavoid_same` as stated here —
without the immersion hypothesis `hrank` on the stratum — is *not* what the case-B step of
`CoreLT_succ` needs, and the S43 "crux" (which tried to prove it via Remmert-style analytic
geometry) is superseded.  The correct statement, with the immersion hypothesis and proved from
`Work.CoreStep.persist_of_Zavoid_cross2` (specialised to `T' = T`), is

  `Work.CoreStep.persist_of_Zavoid_same_hrank`

in `Submission/Work/CoreStep/persist_of_Zavoid_same_hrank.lean`; in the application the sheets come
from graph-like strata, for which the immersion hypothesis is automatic.  All the *structural*
lemmas proved in the present file (`exists_pairPtUp_of_mem_absLevelPairSet'`,
`level_agree_of_witness`, `exists_piece_of_pairPtUp`, `level_agree_of_pairPtUp_mem`,
`persist_of_Zavoid_same_of_closure`) remain valid and are kept. -/

end Work.CoreStep
