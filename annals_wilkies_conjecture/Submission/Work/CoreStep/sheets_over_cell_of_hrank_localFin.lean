import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.CoreStep.sheets_over_cell_of_hrank
import Submission.Work.CoreStep.branchDomain_open

set_option autoImplicit false
noncomputable section

open Classical Filter Topology

namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E

/-!
# Sheets over a cell from a stratum of full projection rank, with *local* finiteness

`Work.CoreStep.sheets_over_cell_of_hrank` proves the sheet decomposition of the absolute set
`absSet T` of a `Good` stratum `T` of full `π_n`-rank over a cell `C`, but it assumes that **every**
fibre of `absSet T` over `ℝⁿ` is finite.  The present file removes that global hypothesis,
retaining only the finiteness of the fibres *over the cell* `C`:

`hfin : ∀ x ∈ C, (fiber (absSet T) x).Finite`.

This is exactly the situation in the case-B step of the BV lexicographic induction: finiteness of
the fibres is known over the cell that is currently being processed, but nothing is known about
base points outside of it.

The two places where the global finiteness hypothesis entered the proof of
`sheets_over_cell_of_hrank` are

* the branch cofinality `Work.CoreStep.branchDomain_open` — whose proof never uses `hfin`: the
  blow-up/compactness argument only produces the second point `z★` over the *base point of `C`*;
* the covering-space argument `Work.WilE7.DimAPI.sheets_of_localGraph`, which *already* takes the
  local form of the finiteness hypothesis (and was applied there as `fun x _ => hfin x`).

So the local statement follows by re-running the same proof, with the cofinality supplied by the
copy `branchDomain_open_localFin` of `branchDomain_open` carrying the local hypothesis.
-/

/-! ## §1  Branch-domain cofinality with local finiteness

The statement is that of `Work.CoreStep.branchDomain_open` with `hfin` restricted to `C`; the proof
is the same (the compactness argument of `Work.CoreStep.fail_data` is insensitive to the
finiteness hypothesis). -/

theorem branchDomain_open_localFin {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good)
    (hrank : ∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j)
    (C : Set (Fin n → ℝ))
    (_hfin : ∀ x ∈ C, (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x).Finite)
    (hCsub : C ⊆ WilkiesDesign.E.projFirst n (m + 1) '' (Work.WilE7.MainDesign.absSet T))
    (hclosed : ∀ z ∈ closure (Work.WilE7.MainDesign.absSet T),
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C → z ∈ Work.WilE7.MainDesign.absSet T)
    (Wl : List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)))
    (hWlgood : ∀ W ∈ Wl, W.Good)
    (hWlsub : ∀ W ∈ Wl, W.X.set ⊆ (Work.WilE7.CoreStep.absPairSet T).set)
    (hWlcov : (Work.WilE7.CoreStep.absPairSet T).set = ⋃ W ∈ Wl, W.X.set)
    (havoid : ∀ (u v : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ) (x₀ : Fin n → ℝ),
      u ∈ T.X.set → v ∈ T.X.set →
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) = x₀ →
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv v) = x₀ → x₀ ∈ C →
      Work.WilE7.CoreStep.absPtInv u ≠ Work.WilE7.CoreStep.absPtInv v →
      ∀ W ∈ Wl, Work.WilE7.CoreStep.pairPtUp u v ∈ W.X.set →
        n + (m + 1) - T.j ≤ Work.WilE7.CoreStep.pPair n m - W.j) :
    ∀ u ∈ T.X.set, WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) ∈ C →
      ∀ V ∈ nhds (Work.WilE7.CoreStep.absPtInv u),
        ∃ U ∈ nhds (WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u)),
          C ∩ U ⊆ WilkiesDesign.E.projFirst n (m + 1) ''
            (Work.WilE7.MainDesign.absSet T ∩ V) := by
  intro u hu hpC V hV
  by_contra hcon
  -- the blow-up of the failing points produces a second point over the same base point
  obtain ⟨zstar, hzstarA, hzstarπ, hzstar_ne, hzstar_bad⟩ :=
    Work.CoreStep.fail_data T C hCsub hclosed u hpC V hV hcon
  obtain ⟨v, hv, hvz⟩ := hzstarA
  set u' : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ := Work.WilE7.CoreStep.absPtUp zstar
    with hu'def
  have hu'v : u' = v := by
    rw [hu'def, ← hvz]
    simpa [Work.CoreStep.absPtInv_eq_absPt] using Work.WilE7.CoreStep.absPtUp_absPtInv v
  have hu' : u' ∈ T.X.set := hu'v ▸ hv
  have hu'inv : Work.WilE7.CoreStep.absPtInv u' = zstar := by
    rw [hu'def]
    exact Work.WilE7.CoreStep.absPtInv_absPtUp zstar
  have hbase : WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u)
      = WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u') := by
    rw [hu'inv]
    exact hzstarπ.symm
  have hne : Work.WilE7.CoreStep.absPtInv u ≠ Work.WilE7.CoreStep.absPtInv u' := by
    rw [hu'inv]
    exact fun h => hzstar_ne h.symm
  -- the avoid condition for the pair `(u, u')`
  have havoid' : ∀ W ∈ Wl, Work.WilE7.CoreStep.pairPtUp u u' ∈ W.X.set →
      n + (m + 1) - T.j ≤ Work.WilE7.CoreStep.pPair n m - W.j := by
    intro W hWl hWmem
    exact havoid u u' (WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u))
      hu hu' rfl (by rw [hbase]) hpC hne W hWl hWmem
  -- the stratum of the pair set through the pair point
  have hpairmem : Work.WilE7.CoreStep.pairPtUp u u' ∈
      (Work.WilE7.CoreStep.absPairSet T).set :=
    Work.WilE7.CoreStep.mem_absPairSet T u u' hu hu' hbase
  have hpairmem' := hpairmem
  rw [hWlcov] at hpairmem'
  have hex : ∃ W ∈ Wl, Work.WilE7.CoreStep.pairPtUp u u' ∈ W.X.set := by
    simp only [Set.mem_iUnion, exists_prop] at hpairmem'
    exact hpairmem'
  obtain ⟨W, hWl, hWmem⟩ := hex
  have hWgood : W.Good := hWlgood W hWl
  have hWsub : W.X.set ⊆ (Work.WilE7.CoreStep.absPairSet T).set := hWlsub W hWl
  have hdim : Work.WilE7.CoreStep.pPair n m - W.j = n + (m + 1) - T.j :=
    Work.CoreStep.pair_dim_eq T hT hrank W hWgood hWsub u u' hu' hWmem (havoid' W hWl hWmem)
  -- the branch through `u` covers the branch through `u'`
  obtain ⟨O, hO, hOprop⟩ :=
    Work.CoreStep.branch_covers_of_good_pair T hT hrank W hWgood hWsub u u' hu hu' hbase
      hWmem hdim V hV
  -- and the bad points near `zstar` fall into that covering
  obtain ⟨z, hzO, hzA, -, hznot⟩ := hzstar_bad O hO
  obtain ⟨w, hwA, hwV, hwπ⟩ := hOprop z hzA hzO
  exact hznot ⟨w, ⟨hwA, hwV⟩, hwπ⟩

/-! ## §2  Boundedness of the absolute set

A private copy of the (non-exported) helper of `Work.CoreStep.sheets_over_cell_of_hrank`. -/

private theorem absSet_isBounded_loc {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) :
    Bornology.IsBounded (Work.WilE7.MainDesign.absSet S) :=
  (Work.CoreStep.cubeC_isCompact' N).isBounded.subset (Work.CoreStep.absSet_subset_cubeC S)

theorem sheets_over_cell_of_hrank_localFin {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : WilkiesDesign.E.Stratum.Good T)
    (hrank : ∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j)
    (C : Set (Fin n → ℝ))
    (hfin : ∀ x ∈ C, (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x).Finite)
    (hCell : WilkiesDesign.IsCell n C)
    (hCsub : C ⊆ WilkiesDesign.E.projFirst n (m + 1) '' (Work.WilE7.MainDesign.absSet T))
    (hclosed : ∀ z ∈ closure (Work.WilE7.MainDesign.absSet T),
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C → z ∈ Work.WilE7.MainDesign.absSet T)
    (Wl : List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)))
    (hWlgood : ∀ W ∈ Wl, W.Good)
    (hWlsub : ∀ W ∈ Wl, W.X.set ⊆ (Work.WilE7.CoreStep.absPairSet T).set)
    (hWlcov : (Work.WilE7.CoreStep.absPairSet T).set = ⋃ W ∈ Wl, W.X.set)
    (havoid : ∀ (u v : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ) (x₀ : Fin n → ℝ),
      u ∈ T.X.set → v ∈ T.X.set →
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) = x₀ →
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv v) = x₀ → x₀ ∈ C →
      Work.WilE7.CoreStep.absPtInv u ≠ Work.WilE7.CoreStep.absPtInv v →
      ∀ W ∈ Wl, Work.WilE7.CoreStep.pairPtUp u v ∈ W.X.set →
        n + (m + 1) - T.j ≤ Work.WilE7.CoreStep.pPair n m - W.j) :
    ∃ (k : ℕ) (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ)),
      (∀ j, ContinuousOn (s j) C) ∧
      (∀ x ∈ C, Function.Injective fun j : Fin k => s j x) ∧
      (∀ (j : Fin k) (x : Fin n → ℝ), x ∈ C →
        Fin.append x (s j x) ∈ Work.WilE7.MainDesign.absSet T) ∧
      (∀ x ∈ C, (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x).ncard = k) ∧
      (∀ z ∈ Work.WilE7.MainDesign.absSet T, WilkiesDesign.E.projFirst n (m + 1) z ∈ C →
        ∃ j : Fin k, s j (WilkiesDesign.E.projFirst n (m + 1) z) =
          WilkiesDesign.E.projSnd n (m + 1) z) := by
  -- The absolute set is bounded (it lives in the cube).
  have hbdd : Bornology.IsBounded (Work.WilE7.MainDesign.absSet T) := absSet_isBounded_loc T
  -- The local branch through every point of `absSet T`, from the implicit function theorem
  -- `localGraph_on_branch` (which uses `hT` and `hrank`).
  have hbranch : ∀ z ∈ Work.WilE7.MainDesign.absSet T,
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C →
      ∃ V ∈ nhds z, ∃ g : (Fin n → ℝ) → (Fin (m + 1) → ℝ),
        ContinuousOn g
          (WilkiesDesign.E.projFirst n (m + 1) '' (Work.WilE7.MainDesign.absSet T ∩ V)) ∧
        (∀ x ∈ WilkiesDesign.E.projFirst n (m + 1) ''
            (Work.WilE7.MainDesign.absSet T ∩ V),
          Fin.append x (g x) ∈ Work.WilE7.MainDesign.absSet T ∩ V) ∧
        (∀ w ∈ Work.WilE7.MainDesign.absSet T ∩ V,
          g (WilkiesDesign.E.projFirst n (m + 1) w) =
            WilkiesDesign.E.projSnd n (m + 1) w) := by
    intro z hz _
    obtain ⟨w, hw, hweq⟩ := hz
    subst hweq
    exact Work.WilE7.CoreStep.localGraph_on_branch T hT hrank w hw
  -- Branch cofinality: the branch through a point over `C` covers `C` near the base point.
  have hcof : ∀ z ∈ Work.WilE7.MainDesign.absSet T,
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C → ∀ V ∈ nhds z,
        ∃ U ∈ nhds (WilkiesDesign.E.projFirst n (m + 1) z),
          C ∩ U ⊆ WilkiesDesign.E.projFirst n (m + 1) ''
            (Work.WilE7.MainDesign.absSet T ∩ V) := by
    intro z hz hzC V hV
    obtain ⟨w, hw, hweq⟩ := hz
    subst hweq
    exact branchDomain_open_localFin T hT hrank C hfin hCsub hclosed Wl hWlgood hWlsub hWlcov
      havoid w hw hzC V hV
  -- The covering-space argument, in its already-local form.
  exact Work.WilE7.DimAPI.sheets_of_localGraph (p := n) (q := m + 1)
    (Work.WilE7.MainDesign.absSet T) C hCell hCsub hbdd hfin hclosed
    (fun z hz hzC =>
      Work.WilE7.CoreStep.hgraph_of_branch (Work.WilE7.MainDesign.absSet T) C z hz hzC
        (hbranch z hz hzC) (hcof z hz hzC))

end Work.CoreStep
