import Submission.Work.PTGeometric.AmbientPreData
import Submission.Work.PTGeometric.exists_cutoffs
import Submission.Work.PTGeometric.nonempty_ambCharts_of_family
import Submission.Work.PTGeometric.nonempty_ambCharts_of_family_verbatim

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: from continuous ambient data to the pre-data of the last mile

`Work.PTGeometric.AmbientPreData` asks for a **smooth** projection-valued `P`, a **smooth** `P`-valued
field `v`, a finite family of Grassmannian charts covering the source with `ℓ`-adapted frames, and
cut-offs covering the bad set.  This file shows that all of that is *produced* from the following much
weaker input, in which only **continuity** is required and no chart family appears:

* `P : M → End(ℝⁿ)` **continuous**, taking values in the orthogonal rank-`k` projections (`Gr n k`),
* `v : M → ℝⁿ` **continuous**, with `P x (v x) = v x`,
* the data are `C^∞` on an open neighbourhood `V` of the boundary (a collar `Sh` of `∂M` is already
  smooth and `∂M ⊆ interior Sh`) — this is what the null-homotopy provides near the collapse end,
* the collapse end `S ⊆ ∂M` with its identification with the pieces, `v ≠ 0` on `∂M ∖ S`,
* finitely many *prescribed* boundary charts `(ellE j, UE j)` at the boundary zeros `ptE j` of `v`,
  on which `v` is transverse to the zero section.

The proof is

1. **G2**: `smoothMap_into_tautTotal_eqOn` with the closed collar `Sh` gives globally `C^∞` `Pall, vall`
   with `Pall x ∈ Gr n k`, `Pall x (vall x) = vall x`, and `(Pall, vall) = (P, v)` on `Sh` (which contains `∂M`);
   consequently `avoid`, `S ∩ {vall = 0} = S ∩ {v = 0}` and the boundary transversality transfer by
   eventual equality;
2. the chart family: `nonempty_ambCharts_of_family` (a *hypothesis* of the theorem, so that this file
   does not depend on its proof) applied to `Pall` with the prescribed boundary charts;
3. the cut-offs: `exists_cutoffs` applied to `(C, vall)`, the hypothesis `hoff` being the boundary
   transversality just transferred;
4. the assembly of `AmbientPreData`.

## Main results

* `Work.PTGeometric.ContinuousAmbientData`
* `Work.PTGeometric.ambientPreData_of_continuous`
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism

variable {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-- **The continuous ambient data of the last mile.**  Everything the construction of
`AmbientPreData` needs, with *continuity* in place of smoothness and without any chart family: the
ambient projection-valued `P` and the `P`-valued field `v`, a collar `Sh` of the boundary on which the
data are already `C^∞`, the collapse end `S ⊆ ∂M` with its identification with the pieces, and finitely
many prescribed boundary charts witnessing the transversality of `v` at the boundary zeros. -/
structure ContinuousAmbientData (n k : ℕ) (ι : Type) [Fintype ι] (Fam : ι → Man8) where
  M : Type
  [topologicalSpace : TopologicalSpace M]
  [chartedSpace : ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [isManifold : IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M]
  [compactSpace : CompactSpace M]
  [t2Space : T2Space M]
  [nonempty : Nonempty M]
  /-- the ambient projection-valued map -/
  P : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)
  hP : Continuous P
  isProj : ∀ x, P x ∈ Gr n k
  /-- the ambient field -/
  v : M → EuclideanSpace ℝ (Fin n)
  hv : Continuous v
  mem : ∀ x, P x (v x) = v x
  /-- the collar of the boundary on which the data are already smooth -/
  Sh : Set M
  isClosed_Sh : IsClosed Sh
  bdry_subset_Sh : (𝓡∂ ((8 + k) + 1)).boundary M ⊆ interior Sh
  V : Set M
  isOpen_V : IsOpen V
  Sh_subset_V : Sh ⊆ V
  hPsmV : ContMDiffOn (𝓡∂ ((8 + k) + 1))
    (𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞ P V
  hvsmV : ContMDiffOn (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ v V
  /-- the collapse end -/
  S : Set M
  isClosed_S : IsClosed S
  S_subset_bdry : S ⊆ (𝓡∂ ((8 + k) + 1)).boundary M
  endHomeo : ↥(S ∩ {x : M | v x = 0}) ≃ₜ (Σ i : ι, (Fam i).pt)
  avoid : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary M, x ∉ S → v x ≠ 0
  /-- the finite **open cover** of the boundary zeros by the prescribed charts -/
  mE : ℕ
  ellE : Fin mE → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k)
  UE : Fin mE → Set M
  isOpen_UE : ∀ j, IsOpen (UE j)
  UE_subset_Sh : ∀ j, UE j ⊆ Sh
  ellE_inj : ∀ j y, y ∈ UE j → ∀ z : EuclideanSpace ℝ (Fin n), P y z = z → ellE j z = 0 → z = 0
  /-- the injectivity margin on the **closure** of each chart (so that the charts enter the chart
  family *verbatim*: the adapted frame is then globally smooth, cf.
  `Work.PTGeometric.nonempty_ambCharts_of_family_verbatim`) -/
  ellE_inj_cl : ∀ j, closure (UE j) ⊆
    {y : M | ∀ z : EuclideanSpace ℝ (Fin n), P y z = z → ellE j z = 0 → z = 0}
  /-- every boundary zero of `v` is covered by a prescribed chart -/
  bndZero_cov : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary M, v x = 0 → ∃ j, x ∈ UE j
  /-- `v` is transverse to the zero section at **every** boundary zero covered by a prescribed chart
  (not only at a base point) -/
  bndZero_trans : ∀ j, ∀ x ∈ UE j, ∀ (hx : x ∈ (𝓡∂ ((8 + k) + 1)).boundary M), v x = 0 →
    IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ (fun y => ellE j (v y)) x ∧
    IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
      (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary M) => ellE j (v y)) ⟨x, hx⟩

attribute [instance] ContinuousAmbientData.topologicalSpace ContinuousAmbientData.chartedSpace
  ContinuousAmbientData.isManifold ContinuousAmbientData.compactSpace ContinuousAmbientData.t2Space
  ContinuousAmbientData.nonempty

/-- **The last mile from continuous data**: continuous ambient data on a compact source (plus the
chart-building step of §13.5 of the README, taken here as a hypothesis so that this file is
independent of its proof) produce the pre-data of the ambient perturbation. -/
def ambientPreData_of_continuous {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (hk : k ≤ n) (D : ContinuousAmbientData n k ι Fam)
    (hmkC : ∀ (Pall : D.M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      ContMDiff (𝓡∂ ((8 + k) + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) Pall →
      (∀ x, Pall x ∈ Gr n k) →
      (∀ j, closure (D.UE j) ⊆
        {y : D.M | ∀ z : EuclideanSpace ℝ (Fin n), Pall y z = z → D.ellE j z = 0 → z = 0}) →
      ∃ (m' : ℕ) (C : AmbCharts n k D.M Pall m'), ∀ j : Fin D.mE, ∃ l : Fin m',
        C.ell l = D.ellE j ∧ C.U l = D.UE j) :
    AmbientPreData n k ι Fam := by
  classical
  -- ## 1. smoothing (G2), keeping the values on the collar `Sh`
  let hsm0 := smoothMap_into_tautTotal_eqOn n k hk D.M D.P D.v D.hP D.hv D.Sh D.isClosed_Sh D.V
      D.isOpen_V D.Sh_subset_V D.hPsmV D.hvsmV
      (fun x => ⟨D.P x, (D.isProj x).1, (D.isProj x).2.1, (D.isProj x).2.2, by simp⟩)
      (fun x _ => ⟨(D.isProj x).1, (D.isProj x).2.1, (D.isProj x).2.2⟩)
      (fun x _ => D.mem x)
  let Pall : D.M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Classical.choose hsm0
  let vall : D.M → EuclideanSpace ℝ (Fin n) :=
    Classical.choose (Classical.choose_spec hsm0)
  have hrest := Classical.choose_spec (Classical.choose_spec hsm0)
  have hPsmAll := hrest.1
  have hvsmAll := hrest.2.1
  have hsm := hrest.2.2.1
  have hprojSm := hrest.2.2.2.1
  have heqSh := hrest.2.2.2.2
  have heqv : ∀ x ∈ D.Sh, vall x = D.v x := fun x hx => (heqSh x hx).2
  have heqP : ∀ x ∈ D.Sh, Pall x = D.P x := fun x hx => (heqSh x hx).1
  have hmemAll : ∀ x, Pall x (vall x) = vall x := fun x => (hprojSm x).2.2.2
  have hprojAll : ∀ x, Pall x ∈ Gr n k := by
    intro x
    obtain ⟨h1, h2, h3, -⟩ := hprojSm x
    exact ⟨h1, h2, h3⟩
  -- ## 2. the prescribed charts are injective on the planes of `Pall`, even over their closures
  have hclAll : ∀ j, closure (D.UE j) ⊆
      {y : D.M | ∀ z : EuclideanSpace ℝ (Fin n), Pall y z = z → D.ellE j z = 0 → z = 0} := by
    intro j y hy z hz h0
    have hySh : y ∈ D.Sh := closure_minimal (D.UE_subset_Sh j) D.isClosed_Sh hy
    rw [heqP y hySh] at hz
    exact D.ellE_inj_cl j hy z hz h0
  -- ## 3. the chart family, containing the prescribed charts *verbatim*
  let mq : ℕ := Classical.choose (hmkC Pall hPsmAll hprojAll hclAll)
  let C : AmbCharts n k D.M Pall mq :=
    Classical.choose (Classical.choose_spec (hmkC Pall hPsmAll hprojAll hclAll))
  have hC := Classical.choose_spec (Classical.choose_spec (hmkC Pall hPsmAll hprojAll hclAll))
  -- ## 4. the boundary transversality for `(C, vall)`
  have hoff : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary D.M, AmbGood C vall x := by
    intro x hx
    by_cases hvxzero : vall x = 0
    · -- a boundary zero: covered by a prescribed chart
      have hvx : D.v x = 0 :=
        (heqv x (interior_subset (D.bdry_subset_Sh hx))).symm.trans hvxzero
      obtain ⟨j, hj⟩ := D.bndZero_cov x hx hvx
      obtain ⟨hsub, -⟩ := D.bndZero_trans j x hj hx hvx
      obtain ⟨l, hlell, hUeq⟩ := hC j
      refine Or.inr ⟨l, hUeq ▸ hj, ?_⟩
      have hev : (fun y => D.ellE j (D.v y)) =ᶠ[𝓝 x] (fun y => D.ellE j (vall y)) := by
        filter_upwards [isOpen_interior.mem_nhds (D.bdry_subset_Sh hx)] with y hy
        rw [heqv y (interior_subset hy)]
      rw [hlell]
      exact (IsSubmersionAt.congr_iff hev).mp hsub
    · exact Or.inl hvxzero
  -- ## 5. the cut-offs
  let χ : Fin mq → D.M → ℝ := Classical.choose (exists_cutoffs C vall hvsmAll hoff)
  have hχspec := Classical.choose_spec (exists_cutoffs C vall hvsmAll hoff)
  have hχsm : ∀ l, ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) (χ l) :=
    hχspec.1
  have hχrange : ∀ l x, 0 ≤ χ l x ∧ χ l x ≤ 1 := hχspec.2.1
  have hχU : ∀ l y, χ l y ≠ 0 → y ∈ C.U l := hχspec.2.2.1
  have hχint : ∀ l y, χ l y ≠ 0 → (𝓡∂ ((8 + k) + 1)).IsInteriorPoint y := hχspec.2.2.2.1
  have hχbd : ∃ V : Set D.M, IsOpen V ∧ (𝓡∂ ((8 + k) + 1)).boundary D.M ⊆ V ∧
      ∀ l y, y ∈ V → χ l y = 0 := hχspec.2.2.2.2.1
  have hχcov : ∀ x, (∀ l, χ l x = 0) → AmbGood C vall x := hχspec.2.2.2.2.2
  -- ## 6. assembly
  refine (⟨D.M, Pall, hPsmAll, hprojAll, vall, hvsmAll, hmemAll, mq, C, χ, hχsm, hχrange,
    hχU, hχint, hχbd, hχcov, D.S, D.isClosed_S, D.S_subset_bdry, ?_, ?_, ?_⟩ :
      AmbientPreData n k ι Fam)
  · -- the end identification: `vall = v` on `S ⊆ interior Sh`
    refine (Homeomorph.setCongr ?_).trans D.endHomeo
    ext x
    constructor
    · rintro ⟨hxS, hx0⟩
      exact ⟨hxS, by
        have h := heqv x (interior_subset (D.bdry_subset_Sh (D.S_subset_bdry hxS)))
        show D.v x = 0
        rw [← h]; exact hx0⟩
    · rintro ⟨hxS, hx0⟩
      exact ⟨hxS, by
        have h := heqv x (interior_subset (D.bdry_subset_Sh (D.S_subset_bdry hxS)))
        show vall x = 0
        rw [h]; exact hx0⟩
  · intro x hx hxS hx0
    have h := heqv x (interior_subset (D.bdry_subset_Sh hx))
    exact D.avoid x hx hxS (by rw [← h]; exact hx0)
  · -- the boundary transversality, transported along `vall = v` near the boundary
    intro x hx hx0
    have hvx : D.v x = 0 := by
      rw [← heqv x (interior_subset (D.bdry_subset_Sh hx))]
      exact hx0
    obtain ⟨j, hj⟩ := D.bndZero_cov x hx hvx
    obtain ⟨hsub, hbsub⟩ := D.bndZero_trans j x hj hx hvx
    obtain ⟨l, hlell, hUeq⟩ := hC j
    have hev : (fun y => D.ellE j (D.v y)) =ᶠ[𝓝 x] (fun y => D.ellE j (vall y)) := by
      filter_upwards [isOpen_interior.mem_nhds (D.bdry_subset_Sh hx)] with y hy
      rw [heqv y (interior_subset hy)]
    have hev3 : (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary D.M) => D.ellE j (D.v y))
        =ᶠ[𝓝 ⟨x, hx⟩] (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary D.M) => D.ellE j (vall y)) := by
      have hop : (Subtype.val ⁻¹' interior D.Sh) ∈
          𝓝 (⟨x, hx⟩ : ↥((𝓡∂ ((8 + k) + 1)).boundary D.M)) :=
        (continuous_subtype_val (p := fun z : D.M =>
          z ∈ (𝓡∂ ((8 + k) + 1)).boundary D.M)).continuousAt.preimage_mem_nhds
          (isOpen_interior.mem_nhds (D.bdry_subset_Sh hx))
      filter_upwards [hop] with y hy
      show D.ellE j (D.v ↑y) = D.ellE j (vall ↑y)
      rw [heqv (y : D.M) (interior_subset hy)]
    refine ⟨l, hUeq ▸ hj, ?_, ?_⟩
    · rw [hlell]
      exact (IsSubmersionAt.congr_iff hev).mp hsub
    · rw [hlell]
      exact (IsSubmersionAt.congr_iff hev3).mp hbsub

/-- **The ambient collapse end from continuous data.**  Composing the reduction above with the chain of
the last mile (`AmbientPreData ⟹ AmbientCollapseEnd`): a continuous realisation of the ambient data of
the collapse map on a positive multiple of the family (together with the chart-building step, taken as
a hypothesis) gives the ambient collapse-end data. -/
def ambientCollapseEnd_of_continuous {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (hk : k ≤ n) (D : ContinuousAmbientData n k ι Fam)
    (hmkC : ∀ (Pall : D.M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      ContMDiff (𝓡∂ ((8 + k) + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) Pall →
      (∀ x, Pall x ∈ Gr n k) →
      (∀ j, closure (D.UE j) ⊆
        {y : D.M | ∀ z : EuclideanSpace ℝ (Fin n), Pall y z = z → D.ellE j z = 0 → z = 0}) →
      ∃ (m' : ℕ) (C : AmbCharts n k D.M Pall m'), ∀ j : Fin D.mE, ∃ l : Fin m',
        C.ell l = D.ellE j ∧ C.U l = D.UE j) :
    AmbientCollapseEnd n k ι Fam :=
  (ambientPreData_of_continuous hk D hmkC).ambientCollapseEnd

/-- **The last mile from continuous data, with the chart step discharged.**  The only remaining input
of `ambientPreData_of_continuous` is supplied by `nonempty_ambCharts_of_family` (proved), so this
version has no hypothesis beyond the continuous ambient data themselves. -/
def ambientPreData_of_continuous' {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (hk : k ≤ n) (D : ContinuousAmbientData n k ι Fam) :
    AmbientPreData n k ι Fam :=
  ambientPreData_of_continuous hk D (fun Pall hPsmAll hprojAll hclAll =>
    nonempty_ambCharts_of_family_verbatim (n := n) (k := k) D.M hPsmAll hprojAll D.mE D.ellE
      D.UE D.isOpen_UE hclAll)

/-- **The whole last mile from continuous data, with the chart step discharged**: continuous ambient
data of the collapse map on the source produce the ambient collapse-end data of the last mile, hence
(via `Work.PTGeometric.exists_nullBordismFamily_of_ambientCollapseEnd`) a null-bordism of a multiple
of the family once the orientation datum of the situation is supplied. -/
def ambientCollapseEnd_of_continuous' {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (hk : k ≤ n) (D : ContinuousAmbientData n k ι Fam) :
    AmbientCollapseEnd n k ι Fam :=
  (ambientPreData_of_continuous' hk D).ambientCollapseEnd

/-- **The collapse end produced by the last mile from continuous data** (a chosen witness, so that the
statement of a geometric realisation can *name* it). -/
noncomputable def toAmbientCollapseEnd {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (hk : k ≤ n) (C : ContinuousAmbientData n k ι Fam) : AmbientCollapseEnd n k ι Fam :=
  (ambientPreData_of_continuous' hk C).ambientCollapseEnd

/-- **The underlying manifold of the produced collapse end is the source itself** (definitional): the
construction builds the region `{Φ ≤ 0}` from the continuous ambient data, so no `Classical.choice`
intervenes between `C.M` and the end's `M`. -/
@[simp] theorem toAmbientCollapseEnd_M {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (hk : k ≤ n) (C : ContinuousAmbientData n k ι Fam) :
    (toAmbientCollapseEnd hk C).M = C.M := rfl

/-- **The collapse end of the produced data is the collar of the source** (definitional). -/
@[simp] theorem toAmbientCollapseEnd_S {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (hk : k ≤ n) (C : ContinuousAmbientData n k ι Fam) :
    (toAmbientCollapseEnd hk C).S = C.S := rfl

end

end Work.PTGeometric
