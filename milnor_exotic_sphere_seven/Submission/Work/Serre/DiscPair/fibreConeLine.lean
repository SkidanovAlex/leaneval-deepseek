import Mathlib
import Submission.Work.Serre.DiscPair.centreConePair
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.DiscPair.cellStepPairKernel
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.StemsB.RelCochainDualR
import Submission.Work.Serre.CsrSharp.relChainsRHomeomorphCompat
import Submission.Work.Serre.ratCoh_ratH_iso_rat
import Submission.Work.Serre.C1CylExplicit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-- Helper: the base of the cone on the fibre of `q` over an arbitrary point `w` is homeomorphic
to the fibre `q ⁻¹' {w}`, carrying the canonical base point to `b`.  This is
`Work.Serre.DiscPair.baseHomeoFibre` with the attached-cell centre replaced by an arbitrary `w`. -/
theorem baseHomeoFibreGen {Γ : Type} [TopologicalSpace Γ] {X : Type} [TopologicalSpace X]
    (q : C(X, Γ)) (w : Γ)
    (b : Work.StemsB.fibre q w)
    (a : ↥((Work.Serre.cylRetract q) ⁻¹' {w}))
    (ha : a ∈ {x : ↥((Work.Serre.cylRetract q) ⁻¹' {w}) |
      (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)})
    (h : (a : Work.Serre.cyl q) = Work.Serre.cylIncl q b.1) :
    ∃ e : ↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {w}) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} ≃ₜ
        Work.StemsB.fibre q w,
      e ⟨a, ha⟩ = b := by
  obtain ⟨e₀, he₀⟩ := Work.Serre.cylHomeoExplicit q
  have key : ∀ (y : ↥((Work.Serre.cylRetract q) ⁻¹' {w}))
      (hy : (y : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)),
      q (e₀.symm ⟨y.1, hy⟩) = w := by
    intro y hy
    have h1 : (e₀ (e₀.symm ⟨y.1, hy⟩) : Work.Serre.cyl q) = (y : Work.Serre.cyl q) := by
      rw [Homeomorph.apply_symm_apply]
    have h2 : q (e₀.symm ⟨y.1, hy⟩) =
        Work.Serre.cylRetract q (Work.Serre.cylIncl q (e₀.symm ⟨y.1, hy⟩)) :=
      (DFunLike.congr_fun (Work.Serre.cylRetract_cylIncl q) (e₀.symm ⟨y.1, hy⟩)).symm
    rw [h2, ← he₀ (e₀.symm ⟨y.1, hy⟩), h1]
    exact Set.mem_singleton_iff.mp y.2
  let Ψ : ↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {w}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} →
      Work.StemsB.fibre q w :=
    fun y => ⟨e₀.symm ⟨y.1.1, y.2⟩, key y.1 y.2⟩
  let Φ : Work.StemsB.fibre q w →
      ↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {w}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} :=
    fun x => ⟨⟨Work.Serre.cylIncl q x.1, by
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact (DFunLike.congr_fun (Work.Serre.cylRetract_cylIncl q) x.1).trans x.2⟩, ⟨x.1, rfl⟩⟩
  have hleft : ∀ y, Φ (Ψ y) = y := by
    intro y
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    show (Work.Serre.cylIncl q (e₀.symm ⟨y.1.1, y.2⟩) : Work.Serre.cyl q) = y.1.1
    rw [← he₀ (e₀.symm ⟨y.1.1, y.2⟩), Homeomorph.apply_symm_apply]
  have hright : ∀ x, Ψ (Φ x) = x := by
    intro x
    refine Subtype.ext ?_
    show (e₀.symm (⟨(Work.Serre.cylIncl q x.1 : Work.Serre.cyl q), ⟨x.1, rfl⟩⟩ :
      ↥(Set.range (Work.Serre.cylIncl q))) : X) = x.1
    rw [show (⟨(Work.Serre.cylIncl q x.1 : Work.Serre.cyl q), ⟨x.1, rfl⟩⟩ :
          ↥(Set.range (Work.Serre.cylIncl q))) = e₀ x.1 from
        Subtype.ext (he₀ x.1).symm, Homeomorph.symm_apply_apply]
  have hcontΨ : Continuous Ψ :=
    Continuous.subtype_mk (((e₀.symm).continuous).comp
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)) _
  have hcontΦ : Continuous Φ :=
    Continuous.subtype_mk (Continuous.subtype_mk
      ((Work.Serre.cylIncl q).continuous.comp continuous_subtype_val) _) _
  let eu : ↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {w}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} ≃
      Work.StemsB.fibre q w :=
    { toFun := Ψ
      invFun := Φ
      left_inv := hleft
      right_inv := hright }
  refine ⟨Homeomorph.mk eu hcontΨ ?_, ?_⟩
  · show Continuous ⇑eu.symm
    exact hcontΦ
  · refine Subtype.ext ?_
    show (e₀.symm (⟨(a : Work.Serre.cyl q), ha⟩ : ↥(Set.range (Work.Serre.cylIncl q))) : X) = b.1
    rw [show (⟨(a : Work.Serre.cyl q), ha⟩ : ↥(Set.range (Work.Serre.cylIncl q))) = e₀ b.1 from
      Subtype.ext (by rw [he₀ b.1]; exact h), Homeomorph.symm_apply_apply]


/-- A module whose degree-`n` relative rational homology is a line has line relative rational
cohomology: this is the field universal coefficient theorem
`Work.StemsB.relComplexIsoDualR` + `Work.StemsB.fieldDualUCT` together with the linear algebra
`finrank`-duality `Subspace.dual_finrank_eq`. -/
theorem nonempty_relCoh_iso_of_relH_line {Y : Type} [TopologicalSpace Y] (Bset : Set Y) (n : ℕ)
    (h : Nonempty ((Work.StemsB.relChainsR ℚ (TopCat.of Y) Bset).homology n ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (Work.Thom.RelCoh ℚ n Y Bset ≅ ModuleCat.of ℚ ℚ) := by
  obtain ⟨eD⟩ := Work.StemsB.relComplexIsoDualR ℚ (TopCat.of Y) Bset
  obtain ⟨eU⟩ := Work.StemsB.fieldDualUCT ℚ (Work.StemsB.relChainsR ℚ (TopCat.of Y) Bset) n
  obtain ⟨eH⟩ := h
  have hfin : Module.finrank ℚ ↥(Work.Thom.RelCoh ℚ n Y Bset) = 1 := by
    rw [(HomologicalComplex.homologyMapIso eD n ≪≫ eU).toLinearEquiv.finrank_eq,
      Subspace.dual_finrank_eq, eH.toLinearEquiv.finrank_eq, CommSemiring.finrank_self]
  exact (Work.Serre.nonempty_iso_rat_iff_finrank _).mpr hfin

theorem fibreConeLine (r N D : ℕ) (hr : 1 ≤ r) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (w : Work.RatHurewicz.attachCells (D - 2) Γ ι f) :
    Nonempty (Work.Thom.RelCoh ℚ (r + 1)
        ↥((Work.Serre.cylRetract q) ⁻¹' {w})
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' {w}) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      ≅ ModuleCat.of ℚ ℚ) := by
  classical
  -- the cone on the fibre over `w`, and its base
  let P : Set (Work.Serre.cyl q) := (Work.Serre.cylRetract q) ⁻¹' {w}
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
