import Mathlib
import ChallengeDeps
import Submission.Work.HomologyMV.Step
import Submission.Work.HomologyMV.Concrete
import Submission.Work.HomologyMV.kerModel_succ_iso_Sol
import Submission.Work.HomologyMV.wConcrete_surj
import Submission.Work.HomologyMV.wConcrete_ker

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `HomologyMV/`: the homology of `M̂`

This is the assembly of the Mayer–Vietoris computation of `H_*(M̂)` (blueprint §3).

The input is the data described in `Step.lean`, together with

* the surjectivity certificates `SurjCert w` and the kernel certificates `KernelCert w`
  (`Model.lean`), which for the concrete matrices of `rtdata` are provided by
  `Work.HomologyMV.wConcrete_surj` and `Work.HomologyMV.wConcrete_ker`;
* the identification `L.H (0,2) ≅ ℤ` of the degree-`0` slot with `ℤ` (from connectedness of `M̂`,
  or from `coker φ₀ ≅ ℤ` via `Work.HomologyMV.coker_toLin_iso_int_of_normalForm`).

The conclusion is the answer: `H_k(M̂) ≅ ℤ` for `k = 0, 4` and `H_k(M̂) = 0` otherwise, in the
exact shape of the target theorem.

## Main results

* `Work.HomologyMV.mv_homology` — `L.H (k,2) ≅ Sol k` for all `k`, from the abstract data;
* `Work.HomologyMV.intHomology_mv` — the same for `intHomology k X`, i.e. the shape of the
  target `Mhat_homology`, given the identification `L.H (k,2) ≅ intHomology k X`;
* `Work.HomologyMV.intHomology_of_concrete` — the same with the concrete matrices of `Data.lean`
  (`wConcrete`), so that the only inputs left are the long exact sequence, the identifications
  `eM`, `eN`, the commuting square and `H_0 ≅ ℤ`.
-/

namespace Work.HomologyMV

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

/-- **The Mayer–Vietoris computation of `H_*(M̂)`, abstract form.**

Given a Mayer–Vietoris long exact sequence whose first two slots in degree `k` are identified
with `ModelM k` and `ModelN k`, in such a way that the Mayer–Vietoris map becomes the model map
`w k`, and given the two certificate families for `w` and the degree-`0` identification
`H_0(M̂) ≅ ℤ`, the `X`-slot in degree `k` is `Sol k`, i.e. `ℤ` for `k = 0, 4` and `0` otherwise.

The mechanism: `step_iso` gives `H_k(M̂) ≅ ker (w (k-1))` for `k ≥ 1` (from the surjectivity of
`φ_k`), and the kernel certificates identify `ker (w (k-1))` with `kerModel (k-1)`, which is `ℤ`
exactly in degree `3`, i.e. `H_4(M̂) ≅ ℤ`. -/
theorem mv_homology (L : MVLES) (eM : ∀ k : ℤ, ModelM k ≅ L.H (k, 0))
    (eN : ∀ k : ℤ, ModelN k ≅ L.H (k, 1)) (w : ∀ k : ℤ, ModelM k ⟶ ModelN k)
    (hsq : ∀ k : ℤ, (eM k).hom ≫ L.d (k, 0) = w k ≫ (eN k).hom)
    (hsurj : SurjCert w) (hker : KernelCert w) (h0 : Nonempty (L.H (0, 2) ≅ Sol 0)) (k : ℕ) :
    Nonempty (L.H ((k : ℤ), 2) ≅ Sol k) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact h0
  · obtain ⟨e1⟩ := step_iso L eM eN w hsq (k : ℤ) (by omega) (hsurj (k : ℤ) (by omega))
    obtain ⟨e2⟩ := hker ((k : ℤ) - 1) (by omega)
    obtain ⟨e3⟩ := kerModel_succ_iso_Sol k hk
    exact ⟨e1 ≪≫ e2.toModuleIso ≪≫ e3⟩

/-- **The homology of `M̂` in the shape of the target theorem.**  If the `X`-slots of the
Mayer–Vietoris sequence are the singular homology of `X` (here `X = TopCat.of Mhat`), then in
every degree `k` the integral homology of `X` is `ℤ` for `k = 0, 4` and `0` otherwise. -/
theorem intHomology_mv {X : TopCat} (L : MVLES) (eM : ∀ k : ℤ, ModelM k ≅ L.H (k, 0))
    (eN : ∀ k : ℤ, ModelN k ≅ L.H (k, 1)) (w : ∀ k : ℤ, ModelM k ⟶ ModelN k)
    (hsq : ∀ k : ℤ, (eM k).hom ≫ L.d (k, 0) = w k ≫ (eN k).hom)
    (hsurj : SurjCert w) (hker : KernelCert w)
    (hX : ∀ k : ℕ, L.H ((k : ℤ), 2) ≅ LeanEval.Topology.intHomology k X)
    (h0 : Nonempty (L.H (0, 2) ≅ Sol 0)) (k : ℕ) :
    Nonempty (LeanEval.Topology.intHomology k X ≅
      (if k = 0 ∨ k = 4 then ModuleCat.of ℤ ℤ else ModuleCat.of ℤ PUnit)) := by
  obtain ⟨e⟩ := mv_homology L eM eN w hsq hsurj hker h0 k
  exact ⟨(hX k).symm ≪≫ e⟩

/-- **The theorem to instantiate.**  Same as `intHomology_mv`, with the concrete matrices of
`Data.lean` (`wConcrete`) and their certificates.  The remaining inputs are exactly the
Mayer–Vietoris long exact sequence of the cover `M̂ = A ∪ B`, the identifications of its first
two slots with the free models (from `H(M̄)`, `H(T³_v)`, `H(T²_v)`), the commuting square (from
the bridge witnesses of `CERT` and the homotopies of `SPACE`), and `H_0(M̂) ≅ ℤ`. -/
theorem intHomology_of_concrete {X : TopCat} (L : MVLES)
    (eM : ∀ k : ℤ, ModelM k ≅ L.H (k, 0)) (eN : ∀ k : ℤ, ModelN k ≅ L.H (k, 1))
    (hsq : ∀ k : ℤ, (eM k).hom ≫ L.d (k, 0) = wConcrete k ≫ (eN k).hom)
    (hX : ∀ k : ℕ, L.H ((k : ℤ), 2) ≅ LeanEval.Topology.intHomology k X)
    (h0 : Nonempty (L.H (0, 2) ≅ Sol 0)) (k : ℕ) :
    Nonempty (LeanEval.Topology.intHomology k X ≅
      (if k = 0 ∨ k = 4 then ModuleCat.of ℤ ℤ else ModuleCat.of ℤ PUnit)) :=
  intHomology_mv L eM eN wConcrete hsq wConcrete_surj wConcrete_ker hX h0 k

/-- Same as `intHomology_of_concrete`, with the degree-`0` input given in the natural form
`H_0(X) ≅ ℤ` (for instance from `ConnectedSpace X`); the identification `hX 0` turns it into the
`Sol 0` form. -/
theorem intHomology_of_concrete' {X : TopCat} (L : MVLES)
    (eM : ∀ k : ℤ, ModelM k ≅ L.H (k, 0)) (eN : ∀ k : ℤ, ModelN k ≅ L.H (k, 1))
    (hsq : ∀ k : ℤ, (eM k).hom ≫ L.d (k, 0) = wConcrete k ≫ (eN k).hom)
    (hX : ∀ k : ℕ, L.H ((k : ℤ), 2) ≅ LeanEval.Topology.intHomology k X)
    (h0 : Nonempty (LeanEval.Topology.intHomology 0 X ≅ ModuleCat.of ℤ ℤ)) (k : ℕ) :
    Nonempty (LeanEval.Topology.intHomology k X ≅
      (if k = 0 ∨ k = 4 then ModuleCat.of ℤ ℤ else ModuleCat.of ℤ PUnit)) :=
  intHomology_of_concrete L eM eN hsq hX
    (h0.map fun e => hX 0 ≪≫ e) k

end

end Work.HomologyMV
