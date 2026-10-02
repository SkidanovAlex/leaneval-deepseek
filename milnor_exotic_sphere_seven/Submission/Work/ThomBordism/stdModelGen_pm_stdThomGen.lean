import Mathlib
import Submission.Work.ThomBordism.coorientationRef
import Submission.Work.ThomBordism.stdThomGen_span
import Submission.Work.ThomBordism.fibreRes_localDegreeClass_eq_nfGen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The determinate model generator is `±` the standard Thom generator

`Work.ThomBordism.stdModelGen k` is the image of the *explicit* model class
`Work.Thom.Mpun k PUnit` of `H^k(ℝ^k, ℝ^k∖0;ℤ)` under the canonical identification
`ℝ^k ≅ PUnit × ℝ^k`; `Work.ThomBordism.stdThomGen k hk` is the transport of the (opaque,
`Classical.choice`-chosen) Thom class of the trivial rank-`k` bundle over a point along the same
identification.  Both live in the standard pair `(ℝ^k, ℝ^k∖0)`, whose relative cohomology is `ℤ` in
degree `k`, so they differ by a *sign*; this file proves that.

Two generators of a `ℤ`-module isomorphic to `ℤ` differ by `±1`
(`Work.ThomBordism.exists_pm_smul_eq_of_span_eq_top`, an ingredient of the last-mile comparison).
Hence it suffices to prove that the *explicit* model generator generates:

* `Work.ThomBordism.Mpun_punit_span` — the punctured model class `Work.Thom.Mpun n PUnit` of the
  trivial rank-`n` bundle over a *point* generates `H^n(pt × ℝ^n, pt × (ℝ^n∖0);ℤ)`.  This is the
  `B = PUnit` case of the argument of `Work.Tubular.modelClassPunct_fibre_span_top`: the cupping map
  `x ↦ π^*(x) ⌣ Mpun n PUnit` is a bijection (`Work.Thom.Mpun_isModel`), `H⁰` of a point is `ℤ·1`
  (`Work.Cohomology.exists_smul_oneH`) and `1 ⌣ τ = τ` (`Work.Thom.mixedCup_oneH_zero`).
* `Work.ThomBordism.stdModelGen_span` — the pullback of `Mpun k PUnit` along the homeomorphism of
  pairs `ℝ^k ≅ PUnit × ℝ^k` generates (`Work.Tubular.span_singleton_map_eq_top`, the pullback along
  a homeomorphism of pairs being surjective).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.ThomBordism

open CategoryTheory

noncomputable section

/-! ## The punctured model class over a point generates -/

/-- **The punctured model class over a point generates.**  The `B = PUnit` case of
`Work.Tubular.modelClassPunct_fibre_span_top`: cupping with `Mpun n PUnit` is a bijection
(`Work.Thom.Mpun_isModel`), `H⁰(PUnit) = ℤ·1` and `1 ⌣ Mpun = Mpun`
(`Work.Thom.mixedCup_oneH_zero`). -/
theorem Mpun_punit_span (n : ℕ) :
    Submodule.span ℤ ({Work.Thom.Mpun n PUnit} : Set (Work.Thom.RelCoh ℤ n
      (PUnit × Work.Tubular.Euc n) (Work.Thom.Punct PUnit n))) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  rw [Submodule.mem_span_singleton]
  obtain ⟨x, hx⟩ := (Work.Thom.Mpun_isModel n PUnit 0).2
    ((Nat.zero_add n).symm ▸ y : Work.Thom.RelCoh ℤ (0 + n)
      (PUnit × Work.Tubular.Euc n) (Work.Thom.Punct PUnit n))
  obtain ⟨m, hm⟩ := Work.Cohomology.exists_smul_oneH (TopCat.of PUnit) x
  have hbase : (Work.Thom.mixedCupC ℤ (Work.Thom.Punct PUnit n) 0 n)
      ((Work.Thom.CohMap (Work.Thom.projFstA PUnit n) ℤ 0).hom
        (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of PUnit))))
      (Work.Thom.Mpun n PUnit)
      = (Nat.zero_add n).symm ▸ Work.Thom.Mpun n PUnit := by
    rw [Work.Thom.CohMap_oneH, Work.Thom.mixedCupC_eq_mixedCup, Work.Thom.mixedCup_oneH_zero]
  have hchain : (Work.Thom.mixedCupC ℤ (Work.Thom.Punct PUnit n) 0 n)
      ((Work.Thom.CohMap (Work.Thom.projFstA PUnit n) ℤ 0).hom
        (m • Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of PUnit))))
      (Work.Thom.Mpun n PUnit)
      = m • ((Nat.zero_add n).symm ▸ Work.Thom.Mpun n PUnit) := by
    rw [map_zsmul, map_zsmul, ← hbase]
    rfl
  have hfx : (Work.Thom.mixedCupC ℤ (Work.Thom.Punct PUnit n) 0 n)
      ((Work.Thom.CohMap (Work.Thom.projFstA PUnit n) ℤ 0).hom x)
      (Work.Thom.Mpun n PUnit)
      = m • ((Nat.zero_add n).symm ▸ Work.Thom.Mpun n PUnit) := by
    rw [hm]
    exact hchain
  have hy := hx.symm.trans hfx
  have h5 := congrArg (fun w => (Nat.zero_add n) ▸ w) hy
  rw [Work.Tubular.relCoh_cast_symm_cast, Work.Tubular.relCoh_cast_zsmul,
    Work.Tubular.relCoh_cast_symm_cast] at h5
  exact ⟨m, (int_smul_eq_zsmul (inferInstance : Module ℤ (Work.Thom.RelCoh ℤ n
    (PUnit × Work.Tubular.Euc n) (Work.Thom.Punct PUnit n))) m
      (Work.Thom.Mpun n PUnit)).trans h5.symm⟩

/-! ## The standard identification `ℝ^k ≅ PUnit × ℝ^k` -/

/-- The identification `ℝ^k ≅ PUnit × ℝ^k` underlying `Work.ThomBordism.stdModelGen`. -/
def ptAmbC (k : ℕ) : C(Work.Tubular.Euc k, PUnit × Work.Tubular.Euc k) :=
  ⟨fun v => (PUnit.unit, v), continuous_const.prodMk continuous_id⟩

/-- **The determinate model generator generates** `H^k(ℝ^k, ℝ^k∖0;ℤ)`.  It is the pullback of
`Mpun k PUnit` along the homeomorphism of pairs `v ↦ (PUnit.unit, v)`, whose inverse is the second
projection; the pullback along a homeomorphism of pairs is an isomorphism
(`Work.Thom.relCohMap_compA` + `Work.Thom.relCohMap_idA`), hence carries the generator
`Mpun k PUnit` (`Mpun_punit_span`) to a generator
(`Work.Tubular.span_singleton_map_eq_top`). -/
theorem stdModelGen_span (k : ℕ) (hk : 1 ≤ k) :
    Submodule.span ℤ ({stdModelGen k} : Set (Work.Thom.RelCoh ℤ k
      (Work.Tubular.Euc k) ({0}ᶜ : Set (Work.Tubular.Euc k)))) = ⊤ := by
  classical
  let P : Set (Work.Tubular.Euc k) := {0}ᶜ
  let Q : Set (PUnit × Work.Tubular.Euc k) := Work.Thom.Punct PUnit k
  let MAP : C(Work.Tubular.Euc k, PUnit × Work.Tubular.Euc k) := ptAmbC k
  let Ψ : C(PUnit × Work.Tubular.Euc k, Work.Tubular.Euc k) := ⟨Prod.snd, continuous_snd⟩
  -- `stdModelGen` is the pullback of `Mpun k PUnit` along `MAP`
  have hstd : stdModelGen k
      = (Work.Thom.relCohMap MAP P Q (fun v hv => hv) ℤ k).hom (Work.Thom.Mpun k PUnit) := rfl
  -- the two maps are inverse to one another
  have hΨMAP : ∀ v : Work.Tubular.Euc k, Ψ (MAP v) = v := fun v => rfl
  have hMAPΨ : ∀ p : PUnit × Work.Tubular.Euc k, MAP (Ψ p) = p :=
    fun p => Prod.ext (Subsingleton.elim _ _) rfl
  have hg : ∀ y ∈ Q, Ψ y ∈ P := fun y hy => hy
  have hgf : ∀ x ∈ P, (Ψ.comp MAP) x ∈ P := fun x hx => by
    rw [ContinuousMap.comp_apply, hΨMAP x]
    exact hx
  have hgf' : ∀ y ∈ Q, (MAP.comp Ψ) y ∈ Q := fun y hy => by
    rw [ContinuousMap.comp_apply, hMAPΨ y]
    exact hy
  have hcomp_id : Ψ.comp MAP = ContinuousMap.id (Work.Tubular.Euc k) :=
    ContinuousMap.ext hΨMAP
  have hcompA : Work.Thom.relCohMap Ψ Q P hg ℤ k
      ≫ Work.Thom.relCohMap MAP P Q (fun v hv => hv) ℤ k
      = 𝟙 (Work.Thom.RelCoh ℤ k (Work.Tubular.Euc k) P) := by
    rw [Work.Thom.relCohMap_compA (A := P) (B := Q) (C := P) MAP Ψ
      (fun v hv => hv) hg hgf ℤ k]
    exact (Work.Thom.relCohMap_congrA (A := P) (B := P) hcomp_id hgf
      (fun _ hx => hx) ℤ k).trans (Work.Thom.relCohMap_idA P ℤ k)
  -- hence the pullback along `MAP` is surjective
  have hsurj : Function.Surjective
      (Work.Thom.relCohMap MAP P Q (fun v hv => hv) ℤ k).hom := by
    have hlin : (Work.Thom.relCohMap MAP P Q (fun v hv => hv) ℤ k).hom.comp
        (Work.Thom.relCohMap Ψ Q P hg ℤ k).hom = LinearMap.id := by
      have h := congrArg ModuleCat.Hom.hom hcompA
      rwa [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact fun y => ⟨(Work.Thom.relCohMap Ψ Q P hg ℤ k).hom y, LinearMap.congr_fun hlin y⟩
  rw [hstd]
  exact Work.Tubular.span_singleton_map_eq_top
    (f := (Work.Thom.relCohMap MAP P Q (fun v hv => hv) ℤ k).hom)
    (x := Work.Thom.Mpun k PUnit) hsurj (Mpun_punit_span k)

/-! ## The comparison -/

theorem stdModelGen_pm_stdThomGen (k : ℕ) (hk : 1 ≤ k) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      Work.ThomBordism.stdModelGen k = ε • Work.ThomBordism.stdThomGen k hk := by
  -- the standard pair is `ℤ` in degree `k`
  obtain ⟨e⟩ := Work.Thom.relCohomology_euclidean_punctured k hk k
  rw [if_pos rfl] at e
  let E : Work.Thom.RelCoh ℤ k (Work.Tubular.Euc k)
      ({0}ᶜ : Set (Work.Tubular.Euc k)) ≃ₗ[ℤ] ℤ :=
    e.toLinearEquiv.trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ)
  rcases eq_pm_of_span_eq_top_of_iso E (stdModelGen_span k hk) (stdThomGen_span k hk) with h | h
  · exact ⟨1, Or.inl rfl, by rw [h, one_smul]⟩
  · exact ⟨-1, Or.inr rfl, by rw [h]; simp⟩

end

end Work.ThomBordism
