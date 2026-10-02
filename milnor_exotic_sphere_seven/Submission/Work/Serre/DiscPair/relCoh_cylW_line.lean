import Mathlib
import Submission.Work.Serre.C1Cyl
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.DiscPair.centreConePair
import Submission.Work.Serre.DiscPair.fibreConeLine
import Submission.Work.Thom.Cohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative cohomology of the mapping cylinder over a single point is a line

For a continuous map `q : X → B` with path connected fibres whose rational homology in degree `r`
(`r ≥ 1`) is that of `S^r` (a line `ℚ`), and for any point `w : B`, the relative cohomology

  `H^{r+1}(cyl q |_{q⁻¹(w)}, range (cylIncl q) |_{...}; ℚ)`

is a line `ℚ`.

The proof is the same cone-pair argument as `Work.Serre.DiscPair.fibreConeLine`, which does not use
the attached-cell structure of the base at all:

* `P := cylRetract q ⁻¹' {w}` is the cone on the fibre over `w`, hence contractible
  (`Work.Serre.DiscPair.cylRetractPreimageContractible`);
* the cone-pair isomorphism (`Work.Serre.DiscPair.conePairIso`) identifies the relative homology
  `H_{r+1}(P, A)` (`A = range (cylIncl q) ∩ P`, the base of the cone) with the reduced homology
  `H_r(A, {a})`, `a` the point of the base lying over a chosen `b` in the fibre;
* the base `A` is homeomorphic to the fibre `q ⁻¹' {w}` carrying `a` to `b`
  (`Work.Serre.DiscPair.baseHomeoFibreGen`), so `H_r(A, {a}) ≅ H_r(fibre, {b})`
  (`Work.Serre.CsrSharp.relChainsRHomeomorphCompat`);
* `H_r(fibre, {b}) ≅ H_r(fibre) ≅ ℚ` (`Work.Serre.DiscPair.nonempty_abs_iso_rel_singleton` and the
  hypothesis `hgen`).
* Finally the field universal coefficient theorem dualises relative homology to relative
  cohomology (`Work.Serre.DiscPair.nonempty_relCoh_iso_of_relH_line`).
-/

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

theorem relCoh_cylW_line {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (w : B) (r : ℕ) (hr : 1 ≤ r)
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre q b))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) r
      ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (Work.Thom.RelCoh ℚ (r + 1) ↥((Work.Serre.cylRetract q) ⁻¹' ({w} : Set B))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' ({w} : Set B)) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      ≅ ModuleCat.of ℚ ℚ) := by
  classical
  -- the cone on the fibre over `w`, and its base
  let P : Set (Work.Serre.cyl q) := (Work.Serre.cylRetract q) ⁻¹' ({w} : Set B)
  let A : Set ↥P := {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
  obtain ⟨b⟩ := (hpc w).nonempty
  let a : ↥P := ⟨Work.Serre.cylIncl q b.1, by
    show (Work.Serre.cylRetract q) (Work.Serre.cylIncl q b.1) = w
    exact (DFunLike.congr_fun (Work.Serre.cylRetract_cylIncl q) b.1).trans b.2⟩
  have ha : a ∈ A := ⟨b.1, rfl⟩
  haveI hcontr : ContractibleSpace ↥P := cylRetractPreimageContractible q w
  -- the cone pair computes the reduced homology of the base, shifted by one
  obtain ⟨iso₁⟩ := conePairIso (TopCat.of ↥P) A a ha (r + 1) (by omega)
  -- the base of the cone is the fibre
  obtain ⟨e, he⟩ := baseHomeoFibreGen q w b a ha rfl
  have he' : ∀ x : ↥A, x ∈ ({⟨a, ha⟩} : Set ↥A) ↔
      e x ∈ ({b} : Set (Work.StemsB.fibre q w)) := by
    intro x
    rw [Set.mem_singleton_iff, Set.mem_singleton_iff]
    exact ⟨fun hx => by rw [hx]; exact he, fun hx => e.injective (hx.trans he.symm)⟩
  obtain ⟨iso₂⟩ := Work.Serre.CsrSharp.relChainsRHomeomorphCompat ↥A (Work.StemsB.fibre q w)
    {⟨a, ha⟩} {b} e he' r
  -- the reduced homology of the fibre in degree `r` is `H_r(fibre) = ℚ`
  obtain ⟨iso₃⟩ := nonempty_abs_iso_rel_singleton (Work.StemsB.fibre q w) b r hr
  obtain ⟨iso₄⟩ := hgen w
  -- dualise to cohomology
  refine nonempty_relCoh_iso_of_relH_line A (r + 1) ?_
  exact ⟨iso₁ ≪≫ iso₂ ≪≫ iso₃.symm ≪≫ iso₄⟩

end

end Work.Serre.DiscPair
