/-
  `CoreLT_succ` — the remaining nodes, stated against the current workspace (2026-10-12/13).

  Deliverable of the c46 design agent (`cbc/wilkies_e7_coreltsucc.md`).  Type-checked on 18.221
  against `Submission/` as of 2026-10-13 00:00 UTC.

  Route = the reviewed design's Fix 2 (`sources/wilkiesE7main/wilkies_e7_main_design_REVIEW.md`):
  the vertical row is closed by the PAIR SET of a vertical piece `T` with each graph-like piece `S`
  (agreement of all `n+1` projTop coordinates), whose low strata / top-stratum frontiers go into Σ.
  No (BE), no index constancy, no `persist_of_Zavoid_same`.

  sorry'd declarations (and nothing else):
    G1 `attain_dichotomy_of_pairAvoid`            (geometry, Fix 2 `graphCell_compat_of_open`)
    G2 `isOpen_projTopSet_inter_cyl_of_pairAvoid` (geometry, `hAopen` for vertical pieces, any K)
    G3 `cell_compat_of_levelGraphs`               (topology, the band/graph clopen lemma)
    E0 `frontier_restrat`                         (bookkeeping: one-round frontier re-stratification)
    E1 `sigmaFamily_vpairs`                       (bookkeeping: Σ clauses for the vertical pairs)
    E2 `cellRefine_of_nodes`                      (bookkeeping: families + Σ/G split, NOTES_S52 §2.4)
    E3 `coreLT_succ_of_cellRefine`                (bookkeeping: inner call + glue + card)
  PROVED here from G1–G3: `gcase_vertical_cell`; PROVED here: `CoreLT_succ` from E2, E3.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreDefs
import Submission.Work.WilE7.CoreStep.AttainmentBasic
import Submission.Work.WilE7.CoreStep.GermDefs
import Submission.Work.WilE7.CoreStep.SigmaAux
import Submission.Work.WilE7.CoreStep.FibreEndDefs
import Submission.Work.WilE7.DecompDefs
import Submission.Work.WilE7.fiberProduct_semiPf

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.CoreLTSuccPlan

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt)

/-! ## 0. The hypotheses of `E7_prop_main_proved`, as named propositions -/

def HypFC : Prop := ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (n m : ℕ) (X : SemiPf (n + m)),
  X.fmt ≤ F →
  ∃ L : List (SemiPf (n + m)), L.length ≤ b.eval X.deg ∧
    (∀ Xh ∈ L, Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval X.deg ∧ ∀ x, (fiber Xh.set x).Finite) ∧
    projFirst n m '' X.set = ⋃ Xh ∈ L, projFirst n m '' Xh.set

def HypE2 : Prop := ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
  ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
    ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y

def HypE5 : Prop := ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)),
  X.fmt ≤ F →
  ∃ L : List (Stratum p q), L.length ≤ b.eval X.deg ∧
    (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
    X.set = (⋃ S ∈ L, S.X.set) ∧ L.Pairwise (fun S T => Disjoint S.X.set T.X.set)

def HypE6 : Prop := ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)),
  X.fmt ≤ F →
  ∃ Y Y' : SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
    Y'.deg ≤ b.eval X.deg ∧ Y.set = fiberClosure X.set ∧ Y'.set = fiberClosure X.set \ X.set

/-! ## 1. Vocabulary: the base-pair set of two different pieces and the base rank of a pair stratum -/

/-- `{(u,v) ∈ absSet R × absSet T : π_n u = π_n v}` (two *different* pieces; `absPairSet T` is the
case `R = T`). -/
def absPairSet2 {n m : ℕ} (R T : Stratum 0 (n + (m + 1))) : SemiPf (0 + pPair n m) :=
  Work.WilE7.SemiPf.reindex (Work.WilE7.finEquiv (Nat.zero_add (pPair n m))).symm
    (Work.WilE7.fiberProdZ (absReindex R) (absReindex T))

/-- The linear base projection `ℝ^{0 + pPair} → ℝ^n` (first `n` coordinates of the first factor). -/
def pairBaseLin (n m : ℕ) : (Fin (0 + pPair n m) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.funLeft ℝ ℝ (fun i : Fin n =>
    Fin.cast (Nat.zero_add (pPair n m)).symm (Fin.castAdd (n + (m + 1)) (Fin.castAdd (m + 1) i)))

/-- The base (`π_n`) rank of a pair stratum at a point. -/
def pairBaseRank {n m : ℕ} (W : Stratum 0 (pPair n m)) (w : Fin (0 + pPair n m) → ℝ) : ℕ :=
  Module.finrank ℝ ((LinearMap.ker (jac W w)).map (pairBaseLin n m))

/-- `himm`: `projTop` is injective on the tangent space (rank = `dim T`); every piece of
`piecesFrame` has it. -/
def HImm {n m : ℕ} (T : Stratum 0 (n + (m + 1))) : Prop :=
  ∀ z ∈ T.X.set, Module.finrank ℝ
    ((LinearMap.ker (jac T z)).map ((projTopLin n m).comp (absPtLin (n + (m + 1))))) =
      n + (m + 1) - T.j

/-! ## 2. G1 — the per-level attainment dichotomy from the pair set (Fix 2, `graphCell_compat_of_open`)

`S` carries continuous sheets `s j` over the preconnected cell `C` (graph-like, no rank needed);
`T` is any piece with `himm` (in the application: a vertical piece, `dim T = K+1`).  `Vl` is a
`Good` stratification of the level-pair set `{(u,v) ∈ S × T : projTop u = projTop v}`; over `C` its
low strata (`dim V < dim S`) and the frontiers of its top strata (`dim V = dim S`) are avoided —
exactly what `E1` puts into Σ, and a `G`-cell is Σ-free.

Proof sketch (TRUE).  `pr₁` is injective on `ker (jac V)` (a tangent `(σ,τ)` has
`σ ∈ ker jac S`, `τ ∈ ker jac T`, `dprojTop σ = dprojTop τ`; `σ = 0 ⇒ τ = 0` by `himm`), so
`dim V ≤ dim S`.  OPEN: a witness pair over `x₀` lies in a stratum which is not low, hence top; by
`DimAPI.openMap_of_equalDim` (L = pr₁) its `pr₁`-image contains `S ∩ U'`, which contains the sheet
points `s j x` for `x ∈ C` near `x₀`.  CLOSED: witnesses over `x_k → x₀` have a limit pair
`(s j x₀, t*)`, `t* ∈ closure T`; if `t* ∉ T` it lies in `closure V \ V` for a stratum `V`
containing infinitely many witness pairs: low `V` contradicts `hlow` at `x_k`, top `V` contradicts
`htop` at `x₀`.  Preconnected `C` ⇒ dichotomy.  (`havoid` is stated on base sets, not at sheet
points, because `t*` is not a sheet point.) -/
theorem attain_dichotomy_of_pairAvoid {n m k : ℕ}
    (S T : Stratum 0 (n + (m + 1))) (hS : S.Good) (hT : T.Good) (himm : HImm T)
    (C : Set (Fin n → ℝ)) (hCpc : IsPreconnected C)
    (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hsub : ∀ (j : Fin k) (x : Fin n → ℝ), x ∈ C →
      absPtUp (n := n) (m := m) (Fin.append x (s j x)) ∈ S.X.set)
    (Vl : List (Stratum 0 (pPair n m)))
    (hVgood : ∀ V ∈ Vl, V.Good)
    (hVsub : ∀ V ∈ Vl, V.X.set ⊆ (absLevelPairSet S T).set)
    (hVcov : (absLevelPairSet S T).set = ⋃ V ∈ Vl, V.X.set)
    (hlow : ∀ V ∈ Vl, pPair n m - V.j < n + (m + 1) - S.j →
      Disjoint (Work.CoreStep.pairSubBaseFst n m V) C)
    (htop : ∀ V ∈ Vl, pPair n m - V.j = n + (m + 1) - S.j →
      Disjoint (Work.CoreStep.pairFrontierBaseFst n m V) C)
    (j : Fin k) :
    (∀ x ∈ C, AttainAt T (fun y => (s j y) (Fin.last m)) x) ∨
      (∀ x ∈ C, ¬ AttainAt T (fun y => (s j y) (Fin.last m)) x) := by
  sorry

/-! ## 3. G2 — relative openness of the image of a vertical piece over a cell (`hAopen`, any `K`)

For `K = n` (span pieces, `T.j = m`) this is the PROVED `CoreStep.isOpen_projTopSet_inter_cyl`.
For `K < n` a vertical piece (dim `K+1`, `π_n`-rank `K`) has a `(K+1)`-dimensional, NON-open image
in `ℝ^{n+1}` (example: `n = 2, m = 1`, `T = {x₂ = 0, w = 0}`, `K = 1`); NOTES_S47 §8.1's
"the vertical row occurs exactly when `K = n`" is false, and every `T.j = m` lemma of the vertical
row (`attainment_open`, `isOpen_projTopSet_inter_cyl`, `AttainDichotomy`) covers only `K = n`.

`R` is a graph-like piece (`π_n`-rank = `dim R = dim T - 1`) with continuous sheets over `C`
(in the assembly: the active `π_n`-cut piece with `C ⊆ π_n(R)`); `Wl` stratifies the base-pair set
of `(R,T)`; over `C` its rank-deficient loci are avoided (E1, clause (4')).

Proof sketch (TRUE).  `x₀ ∈ C`, `t₀ ∈ T` over `x₀`, `r₀ = r j x₀`; the pair `(r₀,t₀)` lies in some
`W` of base rank `K` at that point.  Pick `e : Fin K ↪ Fin n` injective on `dπ_n(T_{t₀}T)`.
(i) `G = (e∘π_n, vert) : T → ℝ^{K+1}` has rank `K+1` at `t₀` (`himm` + `hvert`) — local diffeo
(`Dim.image_mem_nhds_of_surj_fderiv`); along a fibre `Γ_c = {e∘π_n = c}` the derivative of `π_n`
vanishes (`e` stays injective on `dπ_n(T_tT)` near `t₀`: rank `K` both sides), so `π_n(Γ_c)` is one
point `φ_T(c)`.  (ii) `e∘π_n` has rank `K` on `W` at `(r₀,t₀)`, so `e∘π_n(W ∩ U) ⊇` a ball, and the
unique `R`-point / `T`-point over `c` give `φ_T = φ_R` there.  (iii) `x ∈ C` near `x₀`:
`x = φ_R(e x) = φ_T(e x)`, so `G⁻¹(e x, v) ∈ T` lies over `x` with vertical value `v`, all `v` near
`v₀`.  No constant-rank theorem is needed (the kernel of `dπ_n|T` is 1-dimensional). -/
theorem isOpen_projTopSet_inter_cyl_of_pairAvoid {n m k : ℕ}
    (T R : Stratum 0 (n + (m + 1))) (hT : T.Good) (hR : R.Good) (himm : HImm T)
    (hvert : ∀ z ∈ T.X.set, projRank T z + 1 = n + (m + 1) - T.j)
    (hrankR : ∀ z ∈ R.X.set, projRank R z = n + (m + 1) - R.j)
    (hdimR : n + (m + 1) - R.j + 1 = n + (m + 1) - T.j)
    (C : Set (Fin n → ℝ)) (hk : 0 < k)
    (r : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hrcont : ∀ j, ContinuousOn (r j) C)
    (hrsub : ∀ (j : Fin k) (x : Fin n → ℝ), x ∈ C →
      absPtUp (n := n) (m := m) (Fin.append x (r j x)) ∈ R.X.set)
    (Wl : List (Stratum 0 (pPair n m)))
    (hWgood : ∀ W ∈ Wl, W.Good)
    (hWsub : ∀ W ∈ Wl, W.X.set ⊆ (absPairSet2 R T).set)
    (hWcov : (absPairSet2 R T).set = ⋃ W ∈ Wl, W.X.set)
    (hWlow : ∀ W ∈ Wl, ∀ w ∈ W.X.set, pairBaseRank W w < n + (m + 1) - R.j →
      Work.CoreStep.pairBase n m w ∉ C) :
    IsOpen {z : ↥(Work.WilE7.cyl C) | (z : Fin (n + 1) → ℝ) ∈ projTopSet T} := by
  sorry

/-! ## 4. G3 — the band/graph clopen lemma for an ARBITRARY decomposition of `cyl C`

`gcase_family` returns an existential `C'` (from `multiStrata_cells_sorted`), not `cfs C TT`, so
the PROVED `cells_compat_span_piece_of_dichotomy` (stated for `cfs`) cannot be applied to it.  This
lemma needs only the per-family compatibility of the cells with the level-graph unions (the
conclusion of the PROVED `gcase_compat_strong`), no sorting.

Proof (TRUE, elementary).  Cells are preconnected subsets of `cyl C`.  If `κ ⊆ ⋃ⱼ gr C (f t j)`,
`κ ∩ A` and `κ \ A` are finite unions of relatively closed graph traces (`hgraph`), so one is
empty.  Otherwise `κ` meets no level graph, so by `hbound` `κ ∩ closure A = κ ∩ A`, which is
relatively open (`hAopen`) and closed in `κ`. -/
theorem cell_compat_of_levelGraphs {p r : ℕ} {C : Set (Fin p → ℝ)}
    {C' : Finset (Set (Fin (p + 1) → ℝ))}
    (hC' : IsCylDecompOn (p + 1) (Work.WilE7.cyl C) C')
    (k : Fin r → ℕ) (f : (t : Fin r) → Fin (k t) → (Fin p → ℝ) → ℝ)
    (hf : ∀ t j, ContinuousOn (f t j) C)
    (hcompat : ∀ κ ∈ C', ∀ t : Fin r, κ ⊆ (⋃ j, Work.WilE7.gr C (f t j)) ∨
      Disjoint κ (⋃ j, Work.WilE7.gr C (f t j)))
    (A : Set (Fin (p + 1) → ℝ))
    (hAopen : IsOpen {z : ↥(Work.WilE7.cyl C) | (z : Fin (p + 1) → ℝ) ∈ A})
    (hgraph : ∀ t j, Work.WilE7.gr C (f t j) ⊆ A ∨ Disjoint (Work.WilE7.gr C (f t j)) A)
    (hbound : (closure A \ A) ∩ Work.WilE7.cyl C ⊆ ⋃ t, ⋃ j, Work.WilE7.gr C (f t j)) :
    ∀ κ ∈ C', κ ⊆ A ∨ Disjoint κ A := by
  sorry

/-! ## 5. The vertical row over a `G`-cell — PROVED from G1, G2, G3

Inputs as the assembly (E2) has them over a Σ-free base cell `C`: the active graph-like pieces
`S t` with their sheets, the `gcase_family` decomposition `C'` (compatibility in the
`gcase_compat_strong` form), a vertical piece `T`, the cut piece `S t₀` covering `C`, the pair
strata with their Σ-avoidance (E1), and `hbound` (from the PROVED `hbound_of_frontier_sheets_C`
applied to the E0 frontier strata). -/
def GCaseVertical : Prop :=
  ∀ (n m r : ℕ) (C : Set (Fin n → ℝ)), IsPreconnected C →
  ∀ (S : Fin r → Stratum 0 (n + (m + 1))), (∀ t, (S t).Good) →
  ∀ (k : Fin r → ℕ) (s : (t : Fin r) → Fin (k t) → (Fin n → ℝ) → (Fin (m + 1) → ℝ)),
    (∀ t j, ContinuousOn (s t j) C) →
    (∀ t j (x : Fin n → ℝ), x ∈ C →
      absPtUp (n := n) (m := m) (Fin.append x (s t j x)) ∈ (S t).X.set) →
  ∀ (C' : Finset (Set (Fin (n + 1) → ℝ))), IsCylDecompOn (n + 1) (Work.WilE7.cyl C) C' →
    (∀ κ ∈ C', ∀ t : Fin r,
      κ ⊆ (⋃ j, Work.WilE7.gr C (fun x => (s t j x) (Fin.last m))) ∨
      Disjoint κ (⋃ j, Work.WilE7.gr C (fun x => (s t j x) (Fin.last m)))) →
  ∀ (T : Stratum 0 (n + (m + 1))), T.Good → HImm T →
    (∀ z ∈ T.X.set, projRank T z + 1 = n + (m + 1) - T.j) →
  ∀ (t₀ : Fin r), 0 < k t₀ →
    (∀ z ∈ (S t₀).X.set, projRank (S t₀) z = n + (m + 1) - (S t₀).j) →
    n + (m + 1) - (S t₀).j + 1 = n + (m + 1) - T.j →
  ∀ (Wl : List (Stratum 0 (pPair n m))), (∀ W ∈ Wl, W.Good) →
    (∀ W ∈ Wl, W.X.set ⊆ (absPairSet2 (S t₀) T).set) →
    (absPairSet2 (S t₀) T).set = ⋃ W ∈ Wl, W.X.set →
    (∀ W ∈ Wl, ∀ w ∈ W.X.set, pairBaseRank W w < n + (m + 1) - (S t₀).j →
      Work.CoreStep.pairBase n m w ∉ C) →
  ∀ (Vl : Fin r → List (Stratum 0 (pPair n m))), (∀ t, ∀ V ∈ Vl t, V.Good) →
    (∀ t, ∀ V ∈ Vl t, V.X.set ⊆ (absLevelPairSet (S t) T).set) →
    (∀ t, (absLevelPairSet (S t) T).set = ⋃ V ∈ Vl t, V.X.set) →
    (∀ t, ∀ V ∈ Vl t, pPair n m - V.j < n + (m + 1) - (S t).j →
      Disjoint (Work.CoreStep.pairSubBaseFst n m V) C) →
    (∀ t, ∀ V ∈ Vl t, pPair n m - V.j = n + (m + 1) - (S t).j →
      Disjoint (Work.CoreStep.pairFrontierBaseFst n m V) C) →
    (closure (projTopSet T) \ projTopSet T) ∩ Work.WilE7.cyl C ⊆
      ⋃ t, ⋃ j, Work.WilE7.gr C (fun x => (s t j x) (Fin.last m)) →
  ∀ κ ∈ C', κ ⊆ projTopSet T ∨ Disjoint κ (projTopSet T)

theorem gcase_vertical_cell : GCaseVertical := by
  intro n m r C hCpc S hS k s hcont hsub C' hC' hcompat T hT himm hvert t₀ hk₀ hrankR hdimR
    Wl hWgood hWsub hWcov hWlow Vl hVgood hVsub hVcov hlow htop hbound
  -- G2: relative openness of the image of `T`
  have hAopen := isOpen_projTopSet_inter_cyl_of_pairAvoid T (S t₀) hT (hS t₀) himm hvert hrankR
    hdimR C hk₀ (s t₀) (hcont t₀) (hsub t₀) Wl hWgood hWsub hWcov hWlow
  -- G1: every level graph is inside or outside the image of `T`
  have hgraph : ∀ t j, Work.WilE7.gr C (fun x => (s t j x) (Fin.last m)) ⊆ projTopSet T ∨
      Disjoint (Work.WilE7.gr C (fun x => (s t j x) (Fin.last m))) (projTopSet T) := by
    intro t j
    rcases attain_dichotomy_of_pairAvoid (S t) T (hS t) hT himm C hCpc (s t) (hcont t) (hsub t)
        (Vl t) (hVgood t) (hVsub t) (hVcov t) (hlow t) (htop t) j with h | h
    · exact Or.inl (Work.WilE7.CoreStep.gr_subset_or_disjoint_of_attain T C _ h)
    · exact Or.inr (Work.WilE7.CoreStep.gr_disjoint_of_not_attain T C _ h)
  -- G3: the clopen argument on each cell
  have hf : ∀ t j, ContinuousOn (fun x => (s t j x) (Fin.last m)) C := fun t j =>
    (continuous_apply (Fin.last m)).comp_continuousOn (hcont t j)
  exact cell_compat_of_levelGraphs hC' k (fun t j x => (s t j x) (Fin.last m)) hf hcompat
    (projTopSet T) hAopen hgraph hbound

/-! ## 6. E0 — "Π closed under frontiers", one round (the re-stratification with its measure)

For a piece `T` of dimension `≤ K+1` (the vertical pieces), the frontier `closure T \ T` is covered
by (a) graph-like `Good` strata `S ⊆ closure T \ T` with `projRank S = dim S ≤ K` and (b) `SemiPf`
sets whose base image is `NullDimLT K` (Σ-admissible).

Measure.  `dim S < dim T` (`MainDesign.frontierDrop_abs`), so `dim S ≤ K`.  Infinite-`π_{n+1}`-fibre
frontier strata (the vertical segment of `cl {v = x·u}`) have `π_{n+1}`-rank `< dim S ≤ K`, hence
`π_n`-rank `< K`: they land in (b), so NO fibre cut and NO second round are needed: the frontiers of
the (a)-strata (dim `≤ K-1`) are absorbed by `sigmaFamily_len` clause (3) once the (a)-strata are put
in its `Pi` list (admissible: `dim ≤ K`).  (BV's iterated "closed under frontiers" with measure
`dim T₁ < dim X_α`, review Fix 2, is not needed beyond this round.)
Producers: `coreLT_succ.frontierFamily` + `coreLT_succ.gcase_strata` (full-rank locus) +
`coreLT_succ.rankSlice_sigmaLow_data` (rank `r < dim S ≤ K` loci) + `frontierDrop_abs`. -/
def FrontierRestrat : Prop :=
  ∀ F : ℕ, ∃ (A : ℕ) (B : Polynomial ℕ), ∀ (n m K D : ℕ) (T : Stratum 0 (n + (m + 1))),
    T.Good → T.X.fmt ≤ F → T.deg ≤ D → n + (m + 1) - T.j ≤ K + 1 →
    ∃ (Lg : List (Stratum 0 (n + (m + 1)))) (Ly : List (SemiPf (n + (m + 1)))),
      Lg.length ≤ B.eval D ∧ Ly.length ≤ B.eval D ∧
      (∀ S ∈ Lg, S.Good ∧ S.X.fmt ≤ A ∧ S.deg ≤ B.eval D ∧
        S.X.set ⊆ closure T.X.set \ T.X.set ∧ n + (m + 1) - S.j ≤ K ∧
        ∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j) ∧
      (∀ Y ∈ Ly, Y.fmt ≤ A ∧ Y.deg ≤ B.eval D ∧
        NullDimLT (projFirst n (m + 1) '' Y.set) K) ∧
      closure (absSet T) \ absSet T ⊆ (⋃ S ∈ Lg, absSet S) ∪ ⋃ Y ∈ Ly, Y.set

theorem frontier_restrat (hE5 : HypE5) (hE6 : HypE6) : FrontierRestrat := by
  sorry

/-! ## 7. E1 — the Σ clauses for the vertical pairs (review Fix 2: "extend Z_{αβ} to α ∈ Π_{k+1}")

`sigmaFamily_len` (PROVED) gives clauses (2)–(5) for pairs inside `Pi` (all of dim `≤ K`).  A
vertical piece (dim `K+1`) cannot be put in `Pi` (its frontier has base dim `K`).  For `S ∈ Pi`,
`T ∈ Pv` (vertical) we need, with Σ still `NullDimLT K`:
* (5') level pairs `absLevelPairSet S T`: low strata (`dim V < dim S`) and frontiers of top strata
  (`dim V = dim S`) — base dims `≤ dim S - 1 ≤ K - 1` (`stratum_nullDimLE`, `frontierDrop_abs`);
* (4') base pairs `absPairSet2 S T`: the loci of base rank `< dim S` — base dim `≤ K - 1`
  (`rankLocus_nullDimLE` after reindexing `pPair n m = n + ((m+1) + (n+(m+1)))`).
Same code as `sigmaFamily_len` clause (5) with the first factor in `Pi` and the second in `Pv`.

REVIEW FIX 1 (applied; the md5 of this file therefore differs from the reviewed file).  The
reviewed statement left `∃ m'' Sig A B` *inside* the `∀ D Pi Pv`, so the format bound `A` and the
degree bound `B` could depend on `D`; `E2` needs a format bound `F'` fixed *before* `D`.  The
bounds are now hoisted (`∃ Q A B` before `∀ D Pi Pv`) and the ambient dimension is fixed to
`m'' := pPair n m` (the dimension of the pair space, which is what the proof always chooses).
The same defect is present in the PROVED `Work.CoreStep.sigmaFamily_len`; the node
`Work.WilE7.Endgame.sigmaFamily_len_unif` supplies the hoisted version of that lemma. -/
def SigmaVPairs : Prop :=
  ∀ (n m K Fp : ℕ), ∃ (Q : MvPolynomial (Fin 3) ℕ) (A : ℕ) (B : Polynomial ℕ),
    ∀ (D : ℕ) (Pi Pv : List (Stratum 0 (n + (m + 1)))),
      (∀ T ∈ Pi ++ Pv, T.Good ∧ T.X.fmt ≤ Fp ∧ T.deg ≤ D) →
      (∀ S ∈ Pi, n + (m + 1) - S.j ≤ K) →
      (∀ S ∈ Pi, ∀ T ∈ Pv, (absLevelPairSet S T).fmt ≤ Fp ∧ (absPairSet2 S T).fmt ≤ Fp) →
      ∃ (Sig : List (SemiPf (n + pPair n m))),
        Sig.length ≤ MvPolynomial.eval ![D, Pi.length, Pv.length] Q ∧
        (∀ Z ∈ Sig, Z.fmt ≤ A ∧ Z.deg ≤ B.eval D ∧
          NullDimLT (projFirst n (pPair n m) '' Z.set) K) ∧
        (∀ S ∈ Pi, ∀ T ∈ Pv, ∃ Vl : List (Stratum 0 (pPair n m)),
          (∀ V ∈ Vl, V.Good ∧ V.X.set ⊆ (absLevelPairSet S T).set) ∧
          (absLevelPairSet S T).set = ⋃ V ∈ Vl, V.X.set ∧
          (∀ V ∈ Vl, pPair n m - V.j < n + (m + 1) - S.j →
            Work.CoreStep.pairSubBaseFst n m V ⊆
              ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) ∧
          (∀ V ∈ Vl, pPair n m - V.j = n + (m + 1) - S.j →
            Work.CoreStep.pairFrontierBaseFst n m V ⊆
              ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set)) ∧
        (∀ S ∈ Pi, ∀ T ∈ Pv, ∃ Wl : List (Stratum 0 (pPair n m)),
          (∀ W ∈ Wl, W.Good ∧ W.X.set ⊆ (absPairSet2 S T).set) ∧
          (absPairSet2 S T).set = ⋃ W ∈ Wl, W.X.set ∧
          (∀ W ∈ Wl, ∀ w ∈ W.X.set, pairBaseRank W w < n + (m + 1) - S.j →
            Work.CoreStep.pairBase n m w ∈
              ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set))

theorem sigmaFamily_vpairs (hE5 : HypE5) (hE6 : HypE6) : SigmaVPairs := by
  sorry

/-! ## 8. E2 / E3 — the assembly (no new mathematics)

`CellRefine n K`: for every instance of `CoreLT n (K+1)` there is an inner instance of `CoreLT n K`
(families `X'`, `Y'`; bounds; the outer `Y` transported into `Y'`) such that EVERY decomposition
`B` compatible with the inner instance can be refined base-cell by base-cell into a decomposition
compatible with the outer `X`: on a Σ-cell keep `B`'s cells over `b` (`compat_of_fibreProd`), on a
`G`-cell use `gcase_family` (graph-like pieces) + `gcase_vertical_cell` (vertical pieces). -/
def CellRefine (n K : ℕ) : Prop :=
  ∀ F : ℕ, ∃ (F' : ℕ) (P : Polynomial ℕ) (Nk Nl Ng : MvPolynomial (Fin 3) ℕ) (a : ℕ)
      (c : Polynomial ℕ),
    ∀ (D k l m m' : ℕ) (X : Fin k → SemiPf ((n + 1) + m)) (Y : Fin l → SemiPf (n + m')),
      (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) → (∀ i, (Y i).fmt ≤ F ∧ (Y i).deg ≤ D) →
      (∀ i, NullDimLT (basePr n m '' (X i).set) (K + 1)) →
      ∃ (k' l' m₁ m₂ : ℕ) (X' : Fin k' → SemiPf ((n + 1) + m₁)) (Y' : Fin l' → SemiPf (n + m₂)),
        k' ≤ MvPolynomial.eval ![D, k, l] Nk ∧ l' ≤ MvPolynomial.eval ![D, k, l] Nl ∧
        (∀ i, (X' i).fmt ≤ F' ∧ (X' i).deg ≤ P.eval D) ∧
        (∀ i, (Y' i).fmt ≤ F' ∧ (Y' i).deg ≤ P.eval D) ∧
        (∀ i, NullDimLT (basePr n m₁ '' (X' i).set) K) ∧
        (∀ j, ∃ j', projFirst n m' '' (Y j).set = projFirst n m₂ '' (Y' j').set) ∧
        ∀ B : Finset (Set (Fin (n + 1) → ℝ)), IsCylDecompOn (n + 1) (cubeC (n + 1)) B →
          (∀ i, ∀ κ ∈ B, κ ⊆ projFirst (n + 1) m₁ '' (X' i).set ∨
            Disjoint κ (projFirst (n + 1) m₁ '' (X' i).set)) →
          (∀ i, ∀ κ ∈ B, Fin.init '' κ ⊆ projFirst n m₂ '' (Y' i).set ∨
            Disjoint (Fin.init '' κ) (projFirst n m₂ '' (Y' i).set)) →
          ∀ b ∈ B.image (fun κ => Fin.init '' κ), ∃ B' : Finset (Set (Fin (n + 1) → ℝ)),
            ((∀ κ ∈ B', κ ∈ B) ∨
              ((∀ κ ∈ B', (∃ P : StarPiece (n + 1), P.set = κ ∧ P.X.fmt ≤ a ∧
                  P.X.deg ≤ c.eval D) ∧ SubPf (n + 1) κ) ∧
                B'.card ≤ MvPolynomial.eval ![D, k, l] Ng)) ∧
            IsCylDecompOn (n + 1) (cubeC (n + 1) ∩ {z | Fin.init z ∈ b}) B' ∧
            (∀ κ ∈ B', Fin.init '' κ = b) ∧
            (∀ i, ∀ κ ∈ B', κ ⊆ projFirst (n + 1) m '' (X i).set ∨
              Disjoint κ (projFirst (n + 1) m '' (X i).set))

/-- E2 (bookkeeping, 2–3.5K lines): pieces (`piecesFrame`), classification (`projRank_mem_two` +
`not_dimLE_of_projRank`), `π_n`-cut (`piFamily`), E0 frontier strata, `Pi`/`Pv`, Σ =
`sigmaFamily_len` ++ E1 ++ `sigmaLow`/`rankSlice_sigmaLow_data`, `±1` slices, `X'` = `Z_{T,S}`
(`fibreProd_sigma_lem`) ++ low pieces, `Y'` packed (`yFamily_pack_family`); per base cell: Σ-case
`compat_of_fibreProd` + `cylDecomp_fiber`; G-case: sheets (`sheets_over_cell_of_hrank_localFin`,
`hclosed_of_sigma`), `gcase_sheets` (levels, `hdich`), `gcase_family` (`rv = 0`),
`gcase_compat_strong`, `hbound_of_frontier_sheets_C` (E0 strata), `gcase_vertical_cell`. -/
theorem cellRefine_of_nodes (hFC : HypFC) (hE2 : HypE2) (hE5 : HypE5) (hE6 : HypE6)
    (h0 : FrontierRestrat) (h1 : SigmaVPairs) (hV : GCaseVertical) (n K : ℕ) :
    CellRefine n K := by
  sorry

/-- E3 (bookkeeping, 250–450 lines): inner call at `(F', P.eval D, k', l')`,
`DimAPI.cylDecomp_union_restricted` with `A = cubeC (n+1)` (base decomposition = the last clause
of `IsCylDecompOn` for `B`), `Y`-compatibility through `Fin.init '' κ' = b`, card
`≤ |B| · (|B| + Ng)` composed with the inner card polynomial, presentations from the inner call
(kept cells) or from `CellRefine` (new cells). -/
theorem coreLT_succ_of_cellRefine {n K : ℕ} (h : CoreLT n K) (hR : CellRefine n K) :
    CoreLT n (K + 1) := by
  sorry

/-! ## 9. `CoreLT_succ` (the skeleton's signature, plus the E7 hypotheses) — PROVED from the nodes -/

theorem CoreLT_succ (hFC : HypFC) (hE2 : HypE2) (hE5 : HypE5) (hE6 : HypE6) {n K : ℕ}
    (_hC : Work.WilE7.Core n) (h : CoreLT n K) : CoreLT n (K + 1) :=
  coreLT_succ_of_cellRefine h
    (cellRefine_of_nodes hFC hE2 hE5 hE6 (frontier_restrat hE5 hE6) (sigmaFamily_vpairs hE5 hE6)
      gcase_vertical_cell n K)

end Work.WilE7.CoreLTSuccPlan

#print axioms Work.WilE7.CoreLTSuccPlan.gcase_vertical_cell
#print axioms Work.WilE7.CoreLTSuccPlan.CoreLT_succ
