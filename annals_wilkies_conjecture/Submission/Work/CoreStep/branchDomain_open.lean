/-
  `Work.CoreStep.branchDomain_open`: **the branch domain of a `Good` absolute stratum through a
  point of `C` is a neighbourhood of the base point inside `C`.**

  This is the node named in `NOTES_S36_caseB_sheets_and_death.md` §6.  The mathematical content is
  the pair-stratum argument of Binyamini–Vorobiev: a pair `(u, u')` of distinct points of `T.X.set`
  over a base point `x₀ ∈ C` whose pair point `(π u, π u')` lies in a `Good` stratum `W` of the
  same-base pair set `absPairSet T` of dimension `≥ dim T` forces the two branch domains through
  `u` and `u'` to agree near `x₀`; hence every base point of `C` near `x₀` is realised by a point of
  `absSet T` arbitrarily near `absPtInv u`, which is the statement to be proved.

  ## Route

  * `Work.WilE7.DimAPI.openMap_of_equalDim` (already proved in this workspace) is exactly the
    "equal dimension" covering statement: a linear map `L` mapping `absSet W` into `absSet T`,
    injective on the tangent space of `W` at every one of its points, and with matching dimensions,
    covers `absSet T` locally by `L '' (absSet W ∩ U)`.  Here `L` is the projection onto the second
    half of the pair coordinates, so the covering statement says: every `z' ∈ absSet T` near
    `absPtInv u'` is a second-half projection of a pair point, whose **first** half is a point of
    `absSet T` with the same base point.  That is the branch-domain agreement.

  * The hypotheses of `openMap_of_equalDim` are discharged with the pair-set structure:
    `hmap` is immediate from `W.X.set ⊆ (absPairSet T).set`; `hinj` and the dimension identity
    `pPair n m - W.j = n + (m+1) - T.j` both come from the three tangent-space facts
    `jac_pair_facts` (the derivative of any function vanishing on `W.X.set` is killed by the
    tangent space `ker (jac W z)`, applied to the base-projection gap and to the two defining
    equation maps of `T`), together with `hrank`, which makes `π_n` injective on the tangent space
    of `T`.  The inequality `≤` is `havoid`, the inequality `≥` is the dimension count.

  * The remaining ingredient is the compactness/continuity input `fail_data`: if the covering fails
    at `u`, blowing up the failing base points produces a second point `zstar` of `absSet T` over
    `x₀` and a sequence of points of `absSet T` over `C` approaching it, whose base points are not
    covered by the branch of `u`.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreStep.GermDefs
import Submission.Work.CoreStep.branchDomainCover
import Submission.Work.CoreStep.fail_data

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E
namespace Work.CoreStep

open Work.WilE7 Work.WilE7.CoreStep

/-! ## The target theorem -/

theorem branchDomain_open {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good)
    (hrank : ∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j)
    (hfin : ∀ x : Fin n → ℝ,
      (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x).Finite)
    (C : Set (Fin n → ℝ))
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
    fail_data T C hCsub hclosed u hpC V hV hcon
  obtain ⟨v, hv, hvz⟩ := hzstarA
  set u' : Fin (pDim n m) → ℝ := absPtUp zstar with hu'def
  have hu'v : u' = v := by
    rw [hu'def, ← hvz]
    simpa [absPtInv_eq_absPt] using absPtUp_absPtInv v
  have hu' : u' ∈ T.X.set := hu'v ▸ hv
  have hu'inv : absPtInv u' = zstar := by
    rw [hu'def]
    exact Work.WilE7.CoreStep.absPtInv_absPtUp zstar
  have hbase : projFirst n (m + 1) (absPtInv u) = projFirst n (m + 1) (absPtInv u') := by
    rw [hu'inv]
    exact hzstarπ.symm
  have hne : absPtInv u ≠ absPtInv u' := by
    rw [hu'inv]
    exact fun h => hzstar_ne h.symm
  -- the avoid condition for the pair `(u, u')`
  have havoid' : ∀ W ∈ Wl, pairPtUp u u' ∈ W.X.set →
      n + (m + 1) - T.j ≤ pPair n m - W.j := by
    intro W hWl hWmem
    exact havoid u u' (projFirst n (m + 1) (absPtInv u)) hu hu' rfl (by rw [hbase])
      hpC hne W hWl hWmem
  -- the stratum of the pair set through the pair point
  have hpairmem : pairPtUp u u' ∈ (absPairSet T).set :=
    Work.WilE7.CoreStep.mem_absPairSet T u u' hu hu' hbase
  have hpairmem' := hpairmem
  rw [hWlcov] at hpairmem'
  have hex : ∃ W ∈ Wl, pairPtUp u u' ∈ W.X.set := by
    simp only [Set.mem_iUnion, exists_prop] at hpairmem'
    exact hpairmem'
  obtain ⟨W, hWl, hWmem⟩ := hex
  have hWgood : W.Good := hWlgood W hWl
  have hWsub : W.X.set ⊆ (absPairSet T).set := hWlsub W hWl
  have hdim : pPair n m - W.j = n + (m + 1) - T.j :=
    pair_dim_eq T hT hrank W hWgood hWsub u u' hu' hWmem (havoid' W hWl hWmem)
  -- the branch through `u` covers the branch through `u'`
  obtain ⟨O, hO, hOprop⟩ :=
    branch_covers_of_good_pair T hT hrank W hWgood hWsub u u' hu hu' hbase hWmem hdim V hV
  -- and the bad points near `zstar` fall into that covering
  obtain ⟨z, hzO, hzA, -, hznot⟩ := hzstar_bad O hO
  obtain ⟨w, hwA, hwV, hwπ⟩ := hOprop z hzA hzO
  exact hznot ⟨w, ⟨hwA, hwV⟩, hwπ⟩

end Work.CoreStep
