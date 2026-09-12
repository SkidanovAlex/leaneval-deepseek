import Mathlib
import Submission.Work.Lattice.MixedRankSpectrum
import Submission.Work.Lattice.PresentationLattice
import Submission.Commons.LinearAlgebra.FreeModule.submodule_free_finite_of_torsionFree
import Submission.Commons.LinearAlgebra.ExteriorPower.wedge_linearCombination_det
import Submission.Commons.LinearAlgebra.FreeModule.relIndex_closure_natAbs_det
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent

/-!
# H3 — the rank-`r` intrinsic index identity (statement + first lemmas)

ROADMAP item (ii), open sub-lemma (H3) of the hull reduction in
`MixedRankSpectrum`: for two discrete subgroups `W ≤ M` of a full-rank lattice
`Λ ≤ ℝᵈ` (`E d`, `Submodule ℤ (E d)`) spanning the same `r`-dimensional real subspace
(`realSpan W = realSpan M`, so `subDim W = subDim M = r`),

    `latticeCovol W = latticeCovol M · (relIndex(W, M) : ℝ)`

— the rank-`r` analogue of the full-rank identity
`Submodularity.covol_eq_covol_lattice_mul_relIndex`; the index `[M : W]` is finite here
(`W ≤ M` full-rank in `realSpan M`).  This is the identity anchoring the per-hull fibre
counting (H2): `latticeCovol W ≤ C` ⟺ `relIndex(W,M) ≤ C / latticeCovol M`.

**Proof route (recorded)**, using the wedge (Plücker) coordinates in the AMBIENT `E d`
(no re-embedding into `realSpan M` needed):
1. `W` and `M` are free finite-rank `ℤ`-modules (L80
   `Commons.LinearAlgebra.FreeModule.submodule_free_finite_of_torsionFree` applied to the
   free finite torsion-free `↥Λ`), so they have `ℤ`-bases `b_W : Basis (Fin r) ℤ ↥W`,
   `b_M : Basis (Fin r) ℤ ↥M`;
2. transport a `ℤ`-basis to an ambient family: for `b : Basis ι ℤ ↥X`,
   `w i := (b i : E d)` gives `X = span ℤ (Set.range w)` and `realSpan X = span ℝ (Set.range
   w)` (proven below: `span_range_eq_self`, `realSpan_span_range`);
3. the wedge/covolume identification: `latticeCovol X = ‖ιMulti r w‖` when `w` is
   `ℝ`-independent (the family spans `realSpan X`, an `r`-dimensional space)
   (`GraysonData.latticeCovol_span`);
4. the change-of-basis relation: with the `ℤ`-matrix `A` expressing the `W`-basis in the
   `M`-basis (`wᵢ = Σⱼ Aᵢⱼ mⱼ`), `∧ᵢ wᵢ = det(A) · ∧ᵢ mᵢ`, so
   `‖ιMulti w‖ = |det A| · ‖ιMulti m‖`; and `relIndex(W,M) = |det A|` (Mathlib
   `AddSubgroup.relIndex_eq_natAbs_det`/`_eq_abs_det`).  Combining (2)–(4) yields (H3).

**Status**: steps 2 and 3 are PROVEN (`span_range_eq_self`, `realSpan_span_range`,
`realSpan_basis_image`, `linearIndependent_basis_image`,
`latticeCovol_eq_wedge_of_basis`).  Step 4a is PROVEN (`covol_span_mul_natAbs_det`:
the covolume ratio of two `ℤ`-spans with integer change-of-basis matrix `A` is
`|det A|`, via L82 `wedge_linearCombination_det`, `norm_smul`, `RingHom.map_det`,
`real_norm_int_cast`).  Step 4b — identifying `A.det.natAbs` with the index
`relIndex (span(range w)) (span(range m))` — is delegated to the fleet
(`Commons.LinearAlgebra.FreeModule.relIndex_closure_natAbs_det`, L83); then the
assembly (`exists_basis_family_of_le_lattice` families → covol_span_mul_natAbs_det +
L83 → `intrinsicIndexStatement`) completes H3.
-/


noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Submission.IntrinsicIndex

open Submission.GraysonData
open Submission.GraysonLattice

/-- **H3 top-level statement** (recorded): for discrete subgroups `W ≤ M` of the full-rank
lattice `Λ ≤ ℝᵈ` with the same real span, `latticeCovol W = latticeCovol M · relIndex`.
(The index is taken between the ambient `AddSubgroup`s `W.toAddSubgroup` and
`M.toAddSubgroup`.) -/
def intrinsicIndexStatement {d : ℕ} (Λ : Submodule ℤ (E d)) (W M : Submodule ℤ (E d)) : Prop :=
  W ≤ M ∧ W ≤ Λ ∧ M ≤ Λ ∧ realSpan W = realSpan M ∧
    latticeCovol W = latticeCovol M * (W.toAddSubgroup.relIndex M.toAddSubgroup : ℝ)

/-- **Step 2a**: a `ℤ`-basis of a submodule `X ≤ E d`, seen as an ambient family, spans
`X`: if `b : Basis ι ℤ ↥X` then `X = span ℤ (Set.range (fun i => (b i : E d)))`. -/
theorem span_range_eq_self {d : ℕ} {ι : Type*} [Fintype ι] (X : Submodule ℤ (E d))
    (b : Basis ι ℤ ↥X) : Submodule.span ℤ (Set.range (fun i : ι => (b i : E d))) = X := by
  classical
  apply le_antisymm
  · -- each basis vector lies in X
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact (b i : ↥X).2
  · -- every element of X is a ℤ-combination of the basis image
    intro x hx
    let x' : ↥X := ⟨x, hx⟩
    have hsum : (∑ i : ι, b.repr x' i • b i : ↥X) = x' := b.sum_repr x'
    have hxsum : (∑ i : ι, b.repr x' i • b i : E d) = x := by
      -- the subtype coercion is the ℤ-linear inclusion X.subtype, which commutes with sums
      have hlin : X.subtype (∑ i : ι, b.repr x' i • b i) =
          (∑ i : ι, b.repr x' i • (b i : E d)) := by
        simpa using (map_sum (X.subtype) (fun i : ι => b.repr x' i • b i) Finset.univ)
      rw [← hlin]
      exact congrArg (⇑X.subtype) hsum
    rw [← hxsum]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span (s := Set.range (fun i : ι => (b i : E d)))
      ⟨i, rfl⟩)

/-- **Step 2b**: the real span of the `ℤ`-span of a family is the `ℝ`-span of the family. -/
lemma realSpan_span_range {d : ℕ} {ι : Type*} (w : ι → E d) :
    realSpan (Submodule.span ℤ (Set.range w)) = Submodule.span ℝ (Set.range w) := by
  dsimp [realSpan]
  rw [Submodule.span_span_of_tower (R := ℤ) (S := ℝ) (M := E d) (s := Set.range w)]

/-- **Step 2c**: the real span of the image of a `ℤ`-basis of `X` is the `ℝ`-span of the
image family (i.e. `realSpan X = span ℝ (range (fun i => (b i : E d)))`). -/
lemma realSpan_basis_image {d : ℕ} {ι : Type*} [Fintype ι] (X : Submodule ℤ (E d))
    (b : Basis ι ℤ ↥X) :
    realSpan X = Submodule.span ℝ (Set.range (fun i : ι => (b i : E d))) := by
  calc
    realSpan X = realSpan (Submodule.span ℤ (Set.range (fun i : ι => (b i : E d)))) := by
          congr 1
          exact (span_range_eq_self X b).symm
    _ = Submodule.span ℝ (Set.range (fun i : ι => (b i : E d))) := by
          exact realSpan_span_range (fun i : ι => (b i : E d))

/-- **Step 3a**: the ambient image of a `ℤ`-basis of a rank-`r` subgroup is `ℝ`-linearly
independent (`r` vectors spanning the `r`-dimensional real span). -/
lemma linearIndependent_basis_image {d r : ℕ} (X : Submodule ℤ (E d))
    (hX : Module.finrank ℝ (realSpan X) = r) (b : Basis (Fin r) ℤ ↥X) :
    LinearIndependent ℝ (fun i : Fin r => (b i : E d)) := by
  classical
  rw [linearIndependent_iff_card_eq_finrank_span]
  have hspan : Submodule.span ℝ (Set.range (fun i : Fin r => (b i : E d))) = realSpan X := by
    exact (realSpan_basis_image X b).symm
  calc
    Fintype.card (Fin r)
        = Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : Fin r => (b i : E d)))) := by
          rw [hspan, Fintype.card_fin]
          exact hX.symm
    _ = Set.finrank ℝ (Set.range (fun i : Fin r => (b i : E d))) := by rfl

/-- **Step 3b**: the intrinsic covolume of a rank-`r` subgroup is the ambient wedge norm of
the image of any of its `ℤ`-bases: `latticeCovol X = ‖ιMulti r w‖` where
`w i := (b i : E d)`. -/
theorem latticeCovol_eq_wedge_of_basis {d r : ℕ} (X : Submodule ℤ (E d)) (hr : 0 < r)
    (hX : Module.finrank ℝ (realSpan X) = r) (b : Basis (Fin r) ℤ ↥X) :
    latticeCovol X = ‖exteriorPower.ιMulti ℝ r (fun i : Fin r => (b i : E d))‖ := by
  classical
  have hw : Submodule.span ℤ (Set.range (fun i : Fin r => (b i : E d))) = X :=
    span_range_eq_self X b
  have hLI : LinearIndependent ℝ (fun i : Fin r => (b i : E d)) :=
    linearIndependent_basis_image X hX b
  have hcov_eq : latticeCovol X =
      latticeCovol (Submodule.span ℤ (Set.range (fun i : Fin r => (b i : E d)))) := by
    exact congrArg (fun Y : Submodule ℤ (E d) => latticeCovol Y) hw.symm
  calc
    latticeCovol X
        = latticeCovol (Submodule.span ℤ (Set.range (fun i : Fin r => (b i : E d)))) := hcov_eq
    _ = ‖exteriorPower.ιMulti ℝ r (fun i : Fin r => (b i : E d))‖ :=
          latticeCovol_span (d := d) (r := r) hr (fun i : Fin r => (b i : E d)) hLI

/-- The real norm of the real cast of an integer equals its `natAbs`:
`‖(a : ℝ)‖ = (a.natAbs : ℝ)`. -/
lemma real_norm_int_cast (a : ℤ) : ‖(a : ℝ)‖ = (a.natAbs : ℝ) := by
  rw [Real.norm_eq_abs]
  rcases Int.natAbs_eq a with h | h
  · have hpos : 0 ≤ (a : ℝ) := by
      rw [h]
      exact_mod_cast Nat.zero_le a.natAbs
    rw [abs_of_nonneg hpos]
    simpa using congrArg (fun z : ℤ => (z : ℝ)) h
  · have hcast : (a : ℝ) = -(((a.natAbs : ℤ) : ℝ)) := by
      simpa using congrArg (fun z : ℤ => (z : ℝ)) h
    rw [hcast, abs_neg]
    rw [abs_of_nonneg]
    · simp
    · exact_mod_cast Nat.zero_le a.natAbs

/-- **Step 4a (covolume ratio = change-of-basis determinant, span form)**: if the
`ℝ`-independent family `w` is the image of the `ℝ`-independent family `m` under the
integer matrix `A` (`wᵢ = Σⱼ Aᵢⱼ • mⱼ` in `E d`), then the covolumes of the two `ℤ`-spans
satisfy `covol(span ℤ (range w)) = covol(span ℤ (range m)) · |det A|` (with `|det A|` the
`natAbs`).  The top wedges transform by `det A`
(`Commons.LinearAlgebra.ExteriorPower.wedge_linearCombination_det`), so the norms differ
by `|det A|`. -/
theorem covol_span_mul_natAbs_det {d r : ℕ} (hr : 0 < r) {w m : Fin r → E d}
    (hw : LinearIndependent ℝ w) (hm : LinearIndependent ℝ m)
    (A : Matrix (Fin r) (Fin r) ℤ) (hwA : ∀ i : Fin r, w i = ∑ j : Fin r, (A i j : ℝ) • m j) :
    latticeCovol (Submodule.span ℤ (Set.range w)) =
      latticeCovol (Submodule.span ℤ (Set.range m)) * (A.det.natAbs : ℝ) := by
  classical
  let AR : Matrix (Fin r) (Fin r) ℝ := fun i j => (A i j : ℝ)
  have hw0 : latticeCovol (Submodule.span ℤ (Set.range w)) = ‖exteriorPower.ιMulti ℝ r w‖ :=
    latticeCovol_span (d := d) (r := r) hr w hw
  have hm0 : latticeCovol (Submodule.span ℤ (Set.range m)) = ‖exteriorPower.ιMulti ℝ r m‖ :=
    latticeCovol_span (d := d) (r := r) hr m hm
  have hdet := Commons.LinearAlgebra.ExteriorPower.wedge_linearCombination_det
    (R := ℝ) (M := E d) (n := r) m AR
  -- hdet : ιMulti (fun i => ∑ j, AR i j • m j) = AR.det • ιMulti m
  have hAw : exteriorPower.ιMulti ℝ r (fun i : Fin r => ∑ j : Fin r, AR i j • m j) =
      exteriorPower.ιMulti ℝ r w := by
    congr 1
    funext i
    exact (hwA i).symm
  have hdetInt : AR.det = (A.det : ℝ) := by
    dsimp [AR]
    exact (RingHom.map_det (Int.castRingHom ℝ) A).symm
  calc
    latticeCovol (Submodule.span ℤ (Set.range w)) = ‖exteriorPower.ιMulti ℝ r w‖ := hw0
    _ = ‖exteriorPower.ιMulti ℝ r (fun i : Fin r => ∑ j : Fin r, AR i j • m j)‖ := by rw [hAw]
    _ = ‖AR.det • exteriorPower.ιMulti ℝ r m‖ := by rw [hdet]
    _ = ‖AR.det‖ * ‖exteriorPower.ιMulti ℝ r m‖ := by rw [norm_smul]
    _ = ‖exteriorPower.ιMulti ℝ r m‖ * ‖AR.det‖ := by ring
    _ = ‖exteriorPower.ιMulti ℝ r m‖ * (A.det.natAbs : ℝ) := by rw [hdetInt, real_norm_int_cast A.det]
    _ = latticeCovol (Submodule.span ℤ (Set.range m)) * (A.det.natAbs : ℝ) := by rw [hm0]

/-- The `ℤ`-rank of a full-rank lattice `Λ ≤ E d` is the ambient dimension `d`
(`ZLattice.rank` + `finrank ℝ (E d) = d`). -/
lemma finrank_zLattice {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    Module.finrank ℤ Λ = d := by
  have hr := ZLattice.rank ℝ Λ
  have hb := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  have hdim : Module.finrank ℝ (E d) = d := by
    rw [Module.finrank_eq_card_basis hb]
    simp
  rw [hr, hdim]

/-- **Strengthened presentation lemma**: every discrete subgroup `W` of a full-rank
lattice `Λ ≤ ℝᵈ` (`W ≠ ⊥`) is the `ℤ`-span of an `ℝ`-independent **and `ℤ`-independent**
member family (the PID-`ℤ`-basis of `W` coerced to the ambient space).  The
`LinearIndependent ℤ` certificate is what the H3 change-of-basis route needs for
`Commons.LinearAlgebra.FreeModule.relIndex_closure_natAbs_det`. -/
theorem exists_basis_int_of_le_lattice {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (W : Submodule ℤ (E d))
    (hWle : W ≤ Λ) (hW0 : W ≠ ⊥) :
    ∃ n : ℕ, 0 < n ∧ ∃ cW : Fin n → E d,
      LinearIndependent ℝ cW ∧ LinearIndependent ℤ cW ∧
      (∀ r : Fin n, cW r ∈ (Λ : Set (E d))) ∧
      W = Submodule.span ℤ (Set.range cW) := by
  classical
  let bE : Fin d → E d := latticeZBasisE (d := d) Λ hΛfin
  have hLI : LinearIndependent ℤ bE := by
    dsimp [bE]
    exact latticeZBasisE_linearIndependent_ℤ (d := d) Λ hΛfin
  have hle : W ≤ Submodule.span ℤ (Set.range bE) := by
    dsimp [bE]
    rw [span_latticeZBasisE (d := d) Λ hΛfin]
    exact hWle
  obtain ⟨n, bW⟩ := Submodule.basisOfPidOfLESpan (R := ℤ) (b := bE) hLI hle
  have hn0 : 0 < n := by
    by_contra hn
    have hnz : n = 0 := by omega
    subst n
    rw [Submodule.ne_bot_iff] at hW0
    obtain ⟨y, hyW, hy0⟩ := hW0
    let yW : W := ⟨y, hyW⟩
    have hspan : Submodule.span ℤ (Set.range (fun i : Fin 0 => bW i)) = ⊤ := bW.span_eq
    have hmem : yW ∈ Submodule.span ℤ (Set.range (fun i : Fin 0 => bW i)) := by
      rw [hspan]
      trivial
    have hybot : yW ∈ (⊥ : Submodule ℤ W) := by
      simpa using hmem
    have hyW0 : yW = 0 := (Submodule.mem_bot (R := ℤ)).mp hybot
    apply hy0
    exact congrArg (fun z : W => z.val) hyW0
  let cW : Fin n → E d := fun i => ((bW i : W) : E d)
  have hW_eq : W = Submodule.span ℤ (Set.range cW) := by
    apply le_antisymm
    · intro x hx
      let xW : W := ⟨x, hx⟩
      have hmem : xW ∈ Submodule.span ℤ (Set.range bW) := by
        rw [bW.span_eq]
        trivial
      rw [Submodule.mem_span_range_iff_exists_fun (α := Fin n) (R := ℤ) (v := bW)] at hmem
      rcases hmem with ⟨c, hc⟩
      have hcE : (∑ i : Fin n, c i • cW i) = x := by
        have hm := congrArg (fun z : W => (z : E d)) hc
        simpa [cW] using hm
      rw [← hcE]
      exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    · rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      exact (bW i : W).2
  have hzli : LinearIndependent ℤ cW := by
    have hliW : LinearIndependent ℤ (fun i : Fin n => (bW i : W)) := bW.linearIndependent
    exact hliW.map' (W.subtype.restrictScalars ℤ) (Submodule.ker_subtype W)
  refine ⟨n, hn0, cW, ?_, hzli, ?_, hW_eq⟩
  · -- ℝ-independence: membership in Λ + ℤ-independence (transfer lemma)
    exact linearIndependent_real_of_mem_lattice (d := d) Λ hΛfin cW (by
      intro r
      exact hWle ((bW r : W).2)) hzli
  · intro r
    exact hWle ((bW r : W).2)

/-- **Family-strengthened presentation lemma**: as `exists_basis_family_of_le_lattice`,
but with the family indexed by `Fin (subDim W)` and additionally `ℤ`-linearly
independent. -/
theorem exists_basis_family_int_of_le_lattice {d : ℕ} (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (W : Submodule ℤ (E d)) (hWle : W ≤ Λ) (hW0 : W ≠ ⊥) :
    ∃ cW : Fin (subDim W) → E d,
      LinearIndependent ℝ cW ∧ LinearIndependent ℤ cW ∧
      (∀ r : Fin (subDim W), cW r ∈ (Λ : Set (E d))) ∧
      W = Submodule.span ℤ (Set.range cW) := by
  classical
  rcases exists_basis_int_of_le_lattice (d := d) Λ hΛfin W hWle hW0 with
    ⟨n, hn0, cW0, hli, hzli, hmem, hW_eq⟩
  have hsub : subDim W = n := by
    rw [hW_eq]
    exact subDim_span_range_of_linearIndependent cW0 hli
  let e : Fin n ≃ Fin (subDim W) :=
    ((Fin.castOrderIso (n := subDim W) (m := n) hsub).toEquiv).symm
  let cW : Fin (subDim W) → E d := fun r => cW0 (e.symm r)
  refine ⟨cW, ?_, ?_, ?_, ?_⟩
  · have hli' : LinearIndependent ℝ (fun r : Fin (subDim W) => cW0 (e.symm r)) :=
      hli.comp e.symm e.symm.injective
    simpa [cW] using hli'
  · have hzli' : LinearIndependent ℤ (fun r : Fin (subDim W) => cW0 (e.symm r)) :=
      hzli.comp e.symm e.symm.injective
    simpa [cW] using hzli'
  · intro r
    simpa [cW] using hmem (e.symm r)
  · have hspan0 : Submodule.span ℤ (Set.range cW) = Submodule.span ℤ (Set.range cW0) := by
      dsimp [cW]
      exact span_int_range_comp_bijective (u := cW0) (e := e)
    calc
      W = Submodule.span ℤ (Set.range cW0) := hW_eq
      _ = Submodule.span ℤ (Set.range cW) := hspan0.symm

/-- **Span-level intrinsic index identity (H3)**: for `ℤ`-independent-`ℝ`-independent
families `w, m : Fin r → E d` with `w i ∈ span ℤ (range m)` for all `i`,
`latticeCovol(span(range w)) = latticeCovol(span(range m)) · relIndex`.  Composes
`covol_span_mul_natAbs_det` (covolume ratio = |det of the integer change matrix|) with
`relIndex_closure_natAbs_det` (index = |det|) through
`span_int_toAddSubgroup_eq_closure`. -/
theorem covol_eq_mul_relIndex_span {d r : ℕ} (hr : 0 < r) {w m : Fin r → E d}
    (hw : LinearIndependent ℝ w) (hm : LinearIndependent ℝ m) (hmℤ : LinearIndependent ℤ m)
    (hwmem : ∀ i : Fin r, w i ∈ Submodule.span ℤ (Set.range m)) :
    latticeCovol (Submodule.span ℤ (Set.range w)) =
      latticeCovol (Submodule.span ℤ (Set.range m)) *
        ((Submodule.span ℤ (Set.range w)).toAddSubgroup.relIndex
          (Submodule.span ℤ (Set.range m)).toAddSubgroup : ℝ) := by
  classical
  -- the integer change-of-basis matrix A: for each i choose integer coefficients of w i in m
  have hmem_i : ∀ i : Fin r, ∃ c : Fin r → ℤ, (∑ j : Fin r, c j • m j) = w i := by
    intro i
    exact (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (α := Fin r) (v := m) (x := w i)).mp
      (hwmem i)
  let A : Matrix (Fin r) (Fin r) ℤ := fun i j => Classical.choose (hmem_i i) j
  have hA0 : ∀ i : Fin r, w i = ∑ j : Fin r, A i j • m j := by
    intro i
    have h := Classical.choose_spec (hmem_i i)
    -- h : ∑ j, (Classical.choose (hmem_i i)) j • m j = w i
    exact h.symm
  have hA : ∀ i : Fin r, w i = ∑ j : Fin r, (A i j : ℝ) • m j := by
    intro i
    calc
      w i = ∑ j : Fin r, A i j • m j := hA0 i
      _ = ∑ j : Fin r, (A i j : ℝ) • m j := by
            apply Finset.sum_congr rfl
            intro j hj
            exact (Int.cast_smul_eq_zsmul ℝ (A i j) (m j)).symm
  have hcov := covol_span_mul_natAbs_det (d := d) (r := r) hr hw hm A hA
  have hidx := Commons.LinearAlgebra.FreeModule.relIndex_closure_natAbs_det (G := E d)
    (r := r) m hmℤ A w hA0
  -- identify the closures with the toAddSubgroups of the spans
  have hWcl : (Submodule.span ℤ (Set.range w)).toAddSubgroup =
      AddSubgroup.closure (Set.range w) :=
    Commons.LinearAlgebra.FreeModule.span_int_toAddSubgroup_eq_closure (s := Set.range w)
  have hMcl : (Submodule.span ℤ (Set.range m)).toAddSubgroup =
      AddSubgroup.closure (Set.range m) :=
    Commons.LinearAlgebra.FreeModule.span_int_toAddSubgroup_eq_closure (s := Set.range m)
  have hidx' : ((Submodule.span ℤ (Set.range w)).toAddSubgroup.relIndex
      (Submodule.span ℤ (Set.range m)).toAddSubgroup : ℝ) = (A.det.natAbs : ℝ) := by
    rw [hWcl, hMcl, hidx]
  calc
    latticeCovol (Submodule.span ℤ (Set.range w))
        = latticeCovol (Submodule.span ℤ (Set.range m)) * (A.det.natAbs : ℝ) := hcov
    _ = latticeCovol (Submodule.span ℤ (Set.range m)) *
        ((Submodule.span ℤ (Set.range w)).toAddSubgroup.relIndex
          (Submodule.span ℤ (Set.range m)).toAddSubgroup : ℝ) := by rw [hidx']

/-- **H3 (intrinsic index identity)**: for discrete subgroups `W ≤ M ≤ Λ` of a full-rank
lattice spanning the same real subspace (`realSpan W = realSpan M`), the covolume of `W`
is the covolume of `M` times the index `[M : W]`:
`latticeCovol W = latticeCovol M · (relIndex(W, M) : ℝ)`. -/
theorem intrinsicIndex {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (W M : Submodule ℤ (E d)) (hWM : W ≤ M) (hWΛ : W ≤ Λ) (hMΛ : M ≤ Λ)
    (hspan : realSpan W = realSpan M) (hW0 : W ≠ ⊥) :
    intrinsicIndexStatement Λ W M := by
  classical
  have hΛfin : Module.finrank ℤ Λ = d := finrank_zLattice Λ
  have hWΛ' : W ≤ Λ := hWΛ
  have hM0 : M ≠ ⊥ := by
    intro hMbot
    apply hW0
    have hWleBot : W ≤ (⊥ : Submodule ℤ (E d)) := by simpa [hMbot] using hWM
    exact le_bot_iff.mp hWleBot
  let r : ℕ := subDim M
  have hr : 0 < r := by
    dsimp [r]
    by_contra h
    have hz : subDim M = 0 := by omega
    have hMbot : M = ⊥ := (subDim_eq_zero_iff_bot M).mp hz
    exact hM0 hMbot
  -- the ℤ-basis families of M and W (ℤ- and ℝ-independent, spanning)
  rcases exists_basis_family_int_of_le_lattice (d := d) Λ hΛfin M hMΛ hM0 with
    ⟨m, hmℝ, hmℤ, _hmemM, hM_eq⟩
  rcases exists_basis_family_int_of_le_lattice (d := d) Λ hΛfin W hWΛ' hW0 with
    ⟨cW, hwℝ0, _hwℤ0, _hmemW, hW_eq⟩
  -- reindex the W family to Fin r (both ranks are r)
  have hsub : subDim W = r := by
    dsimp [r]
    unfold subDim
    rw [hspan]
  let e : Fin (subDim W) ≃ Fin r := (Fin.castOrderIso hsub).toEquiv
  let w : Fin r → E d := fun i => cW (e.symm i)
  have hw : LinearIndependent ℝ w := by
    dsimp [w]
    exact hwℝ0.comp e.symm e.symm.injective
  have hWspan : Submodule.span ℤ (Set.range w) = W := by
    have hsc := span_int_range_comp_bijective (u := cW) (e := e)
    rw [hsc]
    exact hW_eq.symm
  have hMspan : Submodule.span ℤ (Set.range m) = M := hM_eq.symm
  have hwmem : ∀ i : Fin r, w i ∈ Submodule.span ℤ (Set.range m) := by
    intro i
    have hwiW : w i ∈ W := by
      rw [← hWspan]
      exact Submodule.subset_span (s := Set.range w) ⟨i, rfl⟩
    have hwiM : w i ∈ M := hWM hwiW
    simpa [hMspan] using hwiM
  have hspanId := covol_eq_mul_relIndex_span (d := d) (r := r) hr hw hmℝ hmℤ hwmem
  -- rewrite the span-level identity to the submodule level
  have hWto : (Submodule.span ℤ (Set.range w)).toAddSubgroup = W.toAddSubgroup :=
    congrArg (fun X : Submodule ℤ (E d) => X.toAddSubgroup) hWspan
  have hMto : (Submodule.span ℤ (Set.range m)).toAddSubgroup = M.toAddSubgroup :=
    congrArg (fun X : Submodule ℤ (E d) => X.toAddSubgroup) hMspan
  have h1 : latticeCovol W = latticeCovol (Submodule.span ℤ (Set.range w)) := by
    exact (congrArg (fun X : Submodule ℤ (E d) => latticeCovol X) hWspan).symm
  have h2 : latticeCovol (Submodule.span ℤ (Set.range m)) = latticeCovol M := by
    exact congrArg (fun X : Submodule ℤ (E d) => latticeCovol X) hMspan
  have h3 : ((Submodule.span ℤ (Set.range w)).toAddSubgroup.relIndex
      (Submodule.span ℤ (Set.range m)).toAddSubgroup : ℝ) =
      (W.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
    rw [hWto, hMto]
  have hcov : latticeCovol W = latticeCovol M * (W.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
    calc
      latticeCovol W = latticeCovol (Submodule.span ℤ (Set.range w)) := h1
      _ = latticeCovol (Submodule.span ℤ (Set.range m)) *
            ((Submodule.span ℤ (Set.range w)).toAddSubgroup.relIndex
              (Submodule.span ℤ (Set.range m)).toAddSubgroup : ℝ) := hspanId
      _ = latticeCovol M * (W.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
            rw [h2, h3]
  exact ⟨hWM, hWΛ, hMΛ, hspan, hcov⟩

/-- **Covol-positivity**: a nonzero discrete subgroup of a full-rank lattice has positive
intrinsic covolume (`latticeCovol X > 0` for `X ≠ ⊥`, `X ≤ Λ`).  Via the wedge
identification `latticeCovol X = ‖ιMulti cX‖` (presentation family `cX`) and the
non-vanishing of the wedge of a `ℝ`-independent family (L43). -/
lemma latticeCovol_pos {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (X : Submodule ℤ (E d)) (hXΛ : X ≤ Λ) (hX0 : X ≠ ⊥) : 0 < latticeCovol X := by
  classical
  have hΛfin : Module.finrank ℤ Λ = d := finrank_zLattice Λ
  rcases exists_basis_family_of_le_lattice (d := d) Λ hΛfin X hXΛ hX0 with ⟨cX, hli, _hmemX, hX_eq⟩
  have hr : 0 < subDim X := by
    by_contra h
    have hz : subDim X = 0 := by omega
    exact hX0 ((subDim_eq_zero_iff_bot X).mp hz)
  have hcov : latticeCovol X = ‖exteriorPower.ιMulti ℝ (subDim X) cX‖ := by
    have hspan := latticeCovol_span (d := d) (r := subDim X) hr cX hli
    calc
      latticeCovol X = latticeCovol (Submodule.span ℤ (Set.range cX)) := by
            exact congrArg (fun Y : Submodule ℤ (E d) => latticeCovol Y) hX_eq
      _ = ‖exteriorPower.ιMulti ℝ (subDim X) cX‖ := hspan
  have hne : exteriorPower.ιMulti ℝ (subDim X) cX ≠ 0 :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent (K := ℝ)
      (k := subDim X) cX hli
  have hnorm : 0 < ‖exteriorPower.ιMulti ℝ (subDim X) cX‖ := norm_pos_iff.mpr hne
  rwa [hcov]

/-- **Covolume monotonicity of the hull**: for a nonzero `W ≤ Λ`, the hull has no larger
covolume: `latticeCovol (hull Λ W) ≤ latticeCovol W`.  Via the intrinsic index identity
(`intrinsicIndex` with `M := hull Λ W`), `covol W = covol(hull)·relIndex` with the index
`relIndex ≥ 1` (covol-positivity of both lattices). -/
theorem covol_hull_le_covol {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (W : Submodule ℤ (E d)) (hWΛ : W ≤ Λ) (hW0 : W ≠ ⊥) :
    latticeCovol (Submission.MixedRankSpectrum.hull Λ W) ≤ latticeCovol W := by
  classical
  let M : Submodule ℤ (E d) := Submission.MixedRankSpectrum.hull Λ W
  have hWM : W ≤ M := Submission.MixedRankSpectrum.W_le_hull Λ W hWΛ
  have hMΛ : M ≤ Λ := Submission.MixedRankSpectrum.hull_le_Λ Λ W
  have hspan : realSpan W = realSpan M := by
    dsimp [M]
    exact (Submission.MixedRankSpectrum.realSpan_hull_eq Λ W hWΛ).symm
  have hM0 : M ≠ ⊥ := by
    intro hMbot
    apply hW0
    have hWleBot : W ≤ (⊥ : Submodule ℤ (E d)) := by simpa [M, hMbot] using hWM
    exact le_bot_iff.mp hWleBot
  have hIdx := intrinsicIndex (d := d) Λ W M hWM hWΛ hMΛ hspan hW0
  -- hIdx : intrinsicIndexStatement Λ W M: gives the covol identity as the 5th conjunct
  have hcov : latticeCovol W = latticeCovol M *
      (W.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := hIdx.2.2.2.2
  have hposM : 0 < latticeCovol M := latticeCovol_pos Λ M hMΛ hM0
  have hposW : 0 < latticeCovol W := latticeCovol_pos Λ W hWΛ hW0
  have hdiv : (W.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) =
      latticeCovol W / latticeCovol M := by
    have hEq := congrArg (fun t : ℝ => t / latticeCovol M) hcov
    rw [hEq]
    field_simp [ne_of_gt hposM]
  have hri_pos : 0 < (W.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
    rw [hdiv]
    exact div_pos hposW hposM
  have hri_ne : W.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := by
    exact_mod_cast (ne_of_gt hri_pos)
  have hri1 : (1 : ℝ) ≤ (W.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hri_ne))
  calc
    latticeCovol M ≤ latticeCovol M *
        (W.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
          simpa using (mul_le_mul_of_nonneg_left hri1 (le_of_lt hposM))
    _ = latticeCovol W := hcov.symm

/-- A `ℤ`-independent family spanning `M` gives a `ℤ`-basis of the point group `↥M`. -/
noncomputable def basis_of_family {d r : ℕ} (M : Submodule ℤ (E d)) (m : Fin r → E d)
    (hmem : ∀ i : Fin r, m i ∈ (M : Set (E d))) (hli : LinearIndependent ℤ m)
    (hspan : M = Submodule.span ℤ (Set.range m)) : Basis (Fin r) ℤ ↥M := by
  classical
  let m' : Fin r → ↥M := fun i => ⟨m i, hmem i⟩
  have hli' : LinearIndependent ℤ m' := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hE : (∑ i : Fin r, c i • m i) = 0 := by
      have hc' := congrArg (fun z : ↥M => (z : E d)) hc
      simpa [m'] using hc'
    exact (Fintype.linearIndependent_iff.mp hli) c hE i
  have htop : ⊤ ≤ Submodule.span ℤ (Set.range m') := by
    intro x hx
    have hxE : (x : E d) ∈ M := x.2
    have hmemS : (x : E d) ∈ Submodule.span ℤ (Set.range m) := by simpa [hspan] using hxE
    rw [Submodule.mem_span_range_iff_exists_fun (R := ℤ) (α := Fin r) (v := m)] at hmemS
    rcases hmemS with ⟨c, hc⟩
    rw [Submodule.mem_span_range_iff_exists_fun (R := ℤ) (α := Fin r) (v := m')]
    refine ⟨c, ?_⟩
    apply Subtype.ext
    simpa [m'] using hc
  exact Basis.mk hli' htop

/-- **Per-hull finiteness (H2 core)**: for a discrete subgroup `M ≤ Λ` of a full-rank
lattice, only finitely many subgroups `W ≤ M` of the same rank (`subDim W = subDim M`)
have covolume ≤ `C`.  The `ℤ`-basis of `↥M` from the certified family makes `↥M` a free
finite-rank `ℤ`-module (so the bounded-index group core applies); `intrinsicIndex`
turns `latticeCovol W ≤ C` into the bounded-index condition
`relIndex(W,M) ≤ C / latticeCovol M`, and `subgroupOfLattice` injects into the finite
bounded-index type. -/
theorem finite_fibre_covol_le {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (M : Submodule ℤ (E d)) (hMΛ : M ≤ Λ) (hM0 : M ≠ ⊥) (C : ℝ) :
    Finite {W : Submodule ℤ (E d) // W ≤ M ∧ subDim W = subDim M ∧ latticeCovol W ≤ C} := by
  classical
  have hΛfin : Module.finrank ℤ Λ = d := finrank_zLattice Λ
  rcases exists_basis_family_int_of_le_lattice (d := d) Λ hΛfin M hMΛ hM0 with
    ⟨m, _hmℝ, hmℤ, _hmemΛ, hM_eq⟩
  have hmemM : ∀ i : Fin (subDim M), m i ∈ (M : Set (E d)) := by
    intro i
    rw [hM_eq]
    exact Submodule.subset_span (s := Set.range m) ⟨i, rfl⟩
  let bM : Basis (Fin (subDim M)) ℤ ↥M :=
    basis_of_family M m hmemM hmℤ hM_eq
  haveI : Module.Free ℤ ↥M := Module.Free.of_basis bM
  haveI : Module.Finite ℤ ↥M := Module.Finite.of_basis bM
  let A : Type := {W : Submodule ℤ (E d) // W ≤ M ∧ subDim W = subDim M ∧ latticeCovol W ≤ C}
  let T : Type := {H : AddSubgroup ↥M // H.index ≠ 0 ∧
    (H.index : ℝ) ≤ C / latticeCovol M}
  have hT : Finite T := Submission.SpectrumDiscreteness.finite_index_bounded_real
    (G := ↥M) (B := C / latticeCovol M)
  have hrpos : 0 < subDim M := by
    by_contra h
    have hz : subDim M = 0 := by omega
    exact hM0 ((subDim_eq_zero_iff_bot M).mp hz)
  have hposM : 0 < latticeCovol M := latticeCovol_pos Λ M hMΛ hM0
  let ψ : A → T := fun W => by
    classical
    have hWM : W.1 ≤ M := W.2.1
    have hWΛ : W.1 ≤ Λ := le_trans hWM hMΛ
    have hW0 : W.1 ≠ ⊥ := by
      intro hWbot
      have hz : subDim W.1 = 0 := (subDim_eq_zero_iff_bot W.1).mpr hWbot
      have hzM : subDim M = 0 := by rw [← W.2.2.1]; exact hz
      omega
    have hleV : realSpan W.1 ≤ realSpan M := by
      apply Submodule.span_mono
      intro x hx
      exact hWM hx
    have hfinV : Module.finrank ℝ (realSpan W.1) = Module.finrank ℝ (realSpan M) := by
      simpa [subDim] using W.2.2.1
    have hspan : realSpan W.1 = realSpan M := Submodule.eq_of_le_of_finrank_eq hleV hfinV
    have hIdx := intrinsicIndex (d := d) Λ W.1 M hWM hWΛ hMΛ hspan hW0
    have hcov : latticeCovol W.1 = latticeCovol M *
        (W.1.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := hIdx.2.2.2.2
    have hposW : 0 < latticeCovol W.1 := latticeCovol_pos Λ W.1 hWΛ hW0
    let H : AddSubgroup ↥M := Submission.FullRankSpectrum.subgroupOfLattice M W.1 hWM
    have hidx : H.index = W.1.toAddSubgroup.relIndex M.toAddSubgroup :=
      Submission.FullRankSpectrum.subgroupOfLattice_index M W.1 hWM
    have hleMx : latticeCovol M * (W.1.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) ≤ C := by
      rw [← hcov]
      exact W.2.2.2
    have hb : (W.1.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) ≤ C / latticeCovol M :=
      (le_div_iff₀ hposM).mpr (by simpa [mul_comm] using hleMx)
    have hdiv : (W.1.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) =
        latticeCovol W.1 / latticeCovol M := by
      have hEq := congrArg (fun t : ℝ => t / latticeCovol M) hcov
      rw [hEq]
      field_simp [ne_of_gt hposM]
    have hri_pos : 0 < (W.1.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
      rw [hdiv]
      exact div_pos hposW hposM
    have hne : H.index ≠ 0 := by
      rw [hidx]
      exact_mod_cast (ne_of_gt hri_pos)
    have hb' : (H.index : ℝ) ≤ C / latticeCovol M := by
      rw [hidx]
      exact hb
    exact ⟨H, hne, hb'⟩
  have hψinj : Function.Injective ψ := by
    intro U V h
    exact Subtype.ext (by
      have hH : Submission.FullRankSpectrum.subgroupOfLattice M U.1 U.2.1 =
          Submission.FullRankSpectrum.subgroupOfLattice M V.1 V.2.1 := by
        simpa [ψ] using congrArg (fun t : T => t.1) h
      have hpair : (⟨U.1, U.2.1⟩ : {X : Submodule ℤ (E d) // X ≤ M}) =
          (⟨V.1, V.2.1⟩ : {X : Submodule ℤ (E d) // X ≤ M}) :=
        Submission.FullRankSpectrum.subgroupOfLattice_injective M
          (by simpa [Submission.FullRankSpectrum.subgroupOfLattice] using hH)
      simpa using congrArg Subtype.val hpair)
  exact Finite.of_injective ψ hψinj

end Submission.IntrinsicIndex
