import Mathlib
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.DiskPairDefs
import Submission.Work.RatHurewicz.compression_of_relPiVanishing
import Submission.Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv
import Submission.Work.RatHurewicz.diskPair_zerothConnected
import Submission.Work.RatHurewicz.puncturedDisk_homotopyEquiv_cellSphere
import Submission.Work.RatHurewicz.fibre_puncturedDisk_homotopyEquiv
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.Stems.sphereConnectivity

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The disc pair `(D^{n+2}, D^{n+2} ∖ {0})` is `(n+1)`-connected

The compression form of the connectivity of the pair
`(cellDisk n, puncturedCellDisk n)` (`Work.RatHurewicz.CompressRel`, the form of tom Dieck
Proposition 6.7.5): every map of pairs `(Iᵈ, ∂Iᵈ) → (D^{n+2}, D^{n+2} ∖ {0})` with `d ≤ n+1` is
homotopic, relative to the boundary, into the complement of the centre.

It is obtained from `Work.RatHurewicz.compression_of_relPiVanishing` with
* the `0`-connectivity of the pair (`Work.RatHurewicz.diskPair_zerothConnected`), and
* the vanishing of `π_k` of the homotopy fibre of `puncturedCellDisk n ↪ cellDisk n` for `k ≤ n`:
  the fibre is homotopy equivalent to the punctured cell
  (`Work.RatHurewicz.fibre_puncturedDisk_homotopyEquiv`), which is homotopy equivalent to the
  sphere `S^{n+1} = cellSphere n` (`Work.RatHurewicz.puncturedDisk_homotopyEquiv_cellSphere`),
  whose homotopy groups vanish below degree `n+1` (`Work.Stems.sphereConnectivity`).
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- **The homotopy groups of the punctured model cell vanish in degrees `≤ n`.**  The punctured
cell is homotopy equivalent to the model sphere `S^{n+1} = cellSphere n` (radial retraction), and
`π_k(S^{n+1}) = 0` for `k ≤ n` (`Work.Stems.sphereConnectivity`, with `cellSphere n` definitionally
the sphere `Work.Stems.sphere (n+1)`). -/
theorem puncturedDisk_homotopyGroup_subsingleton (n : ℕ) :
    ∀ k ≤ n, ∀ x : ↥(puncturedCellDisk n),
      Subsingleton (HomotopyGroup (Fin k) ↥(puncturedCellDisk n) x) := by
  intro k hk x
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · -- `k = 0`: the punctured cell is path connected, being homotopy equivalent to a sphere
    subst h0
    have hrank : 1 < Module.rank ℝ (CellVec n) := by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      exact_mod_cast (by omega : 1 < n + 2)
    haveI : PathConnectedSpace (cellSphere n) :=
      (isPathConnected_iff_pathConnectedSpace).mp
        (isPathConnected_sphere hrank 0 (by norm_num : (0 : ℝ) ≤ 1))
    obtain ⟨e⟩ := puncturedDisk_homotopyEquiv_cellSphere n
    haveI : Subsingleton (ZerothHomotopy (cellSphere n)) :=
      (pathConnectedSpace_iff_zerothHomotopy.mp inferInstance).2
    haveI : Subsingleton (ZerothHomotopy ↥(puncturedCellDisk n)) :=
      subsingleton_zerothHomotopy_of_homotopyEquiv e inferInstance
    exact ⟨fun u v => (HomotopyGroup.pi0EquivZerothHomotopy (X := ↥(puncturedCellDisk n))
      (x := x)).injective (Subsingleton.elim _ _)⟩
  · -- `k ≥ 1`: transport along the homotopy equivalence with the sphere
    haveI : Nonempty (Fin k) := ⟨⟨0, hpos⟩⟩
    obtain ⟨e⟩ := puncturedDisk_homotopyEquiv_cellSphere n
    obtain ⟨me⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin k) e x
    haveI : Subsingleton (HomotopyGroup (Fin k) (cellSphere n) (e.toFun x)) :=
      Work.Stems.sphereConnectivity (n + 1) k (by omega) (e.toFun x)
    exact ⟨fun u v => me.injective (Subsingleton.elim _ _)⟩

/-- **The relative homotopy groups of the pair `(D^{n+2}, D^{n+2} ∖ {0})` vanish in the relevant
range**: `π_k` of the homotopy fibre of the inclusion of the punctured cell at `a` is trivial for
`k ≤ n`. -/
theorem relPiVanishing_puncturedCellDisk (n : ℕ) (a : ↥(puncturedCellDisk n)) :
    ∀ k ≤ n, Subsingleton (RelHomotopyGroup (setIncl (puncturedCellDisk n)) a k) := by
  intro k hk
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · -- `k = 0`: the fibre is homotopy equivalent to the punctured cell, which is path connected
    subst h0
    obtain ⟨e1⟩ := fibre_puncturedDisk_homotopyEquiv n a
    haveI hk0 : Subsingleton (HomotopyGroup (Fin 0) ↥(puncturedCellDisk n) a) :=
      puncturedDisk_homotopyGroup_subsingleton n 0 (Nat.zero_le n) a
    haveI hZ : Subsingleton (ZerothHomotopy ↥(puncturedCellDisk n)) :=
      (HomotopyGroup.pi0EquivZerothHomotopy (X := ↥(puncturedCellDisk n))
        (x := a)).surjective.subsingleton
    haveI hZ' : Subsingleton (ZerothHomotopy (cellFibre n a)) :=
      subsingleton_zerothHomotopy_of_homotopyEquiv e1 hZ
    exact ⟨fun u v => (HomotopyGroup.pi0EquivZerothHomotopy (X := cellFibre n a)
      (x := homotopyFibreBasepoint (setIncl (puncturedCellDisk n)) a)).injective
        (Subsingleton.elim _ _)⟩
  · haveI : Nonempty (Fin k) := ⟨⟨0, hpos⟩⟩
    obtain ⟨e1⟩ := fibre_puncturedDisk_homotopyEquiv n a
    obtain ⟨me⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin k) e1
      (homotopyFibreBasepoint (setIncl (puncturedCellDisk n)) a)
    haveI : Subsingleton (HomotopyGroup (Fin k) ↥(puncturedCellDisk n)
        (e1.toFun (homotopyFibreBasepoint (setIncl (puncturedCellDisk n)) a))) :=
      puncturedDisk_homotopyGroup_subsingleton n k hk _
    exact ⟨fun u v => me.injective (Subsingleton.elim _ _)⟩

/-- The disc pair `(D^{n+2}, D^{n+2} \ {0})` is `(n+1)`-connected in compression form: every map
of pairs `(I^d, ∂I^d) → (cellDisk n, {y | y ≠ 0})` with `d ≤ n+1` is homotopic, relative to `∂I^d`,
into the complement of the centre.  Route: the homotopy fibre of `{y | y ≠ 0} ⊆ cellDisk n` is
homotopy equivalent to `{y | y ≠ 0}` itself (convexity of the disc gives a straight-line section up
to homotopy), which is homotopy equivalent to the sphere `cellSphere n` (radial retraction), whose
homotopy groups vanish below degree `n+1` (`Work.Stems.sphereConnectivity`); hence
`RelHomotopyGroup (setIncl {y | y ≠ 0}) a k` is trivial for `k ≤ n`, and
`Work.RatHurewicz.compression_of_relPiVanishing` (with the 0-connectivity of the pair) gives the
compression at all levels `≤ n+1`. -/
theorem compressRel_cellDisk_compl_centre (n : ℕ) :
    ∀ d, d ≤ n + 1 → Work.RatHurewicz.CompressRel (Work.RatHurewicz.cellDisk n)
      {y : Work.RatHurewicz.cellDisk n | (y : EuclideanSpace ℝ (Fin (n + 2))) ≠ 0} d :=
  compression_of_relPiVanishing (A := puncturedCellDisk n) n
    (diskPair_zerothConnected n)
    (fun a k hk => relPiVanishing_puncturedCellDisk n a k hk)

end

end Work.RatHurewicz
