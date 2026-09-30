import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EMZ.BocksteinCore
import Submission.Work.Pi6.BOCK.coeffSESShortExact
import Submission.Work.Pi6.BOCK.ExpTensBasic
import Submission.Work.SSS.ExpTens
import Submission.Work.SSS.ExpTensLES
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

namespace Work.Pi6.K2Z

noncomputable section

/-- The submodule of `p`-multiples of a `ℤ`-module, as the range of multiplication by `p`. -/
abbrev pMultiples (p : ℕ) (M : ModuleCat ℤ) : Submodule ℤ ↥M :=
  LinearMap.range (((p : ℤ) • 𝟙 M)).hom

/-- Membership in the subgroup of `p`-multiples. -/
theorem mem_pMultiples {p : ℕ} {M : ModuleCat ℤ} {x : ↥M} :
    x ∈ (pMultiples p M).toAddSubgroup ↔ ∃ y : ↥M, (p : ℤ) • y = x := by
  show x ∈ LinearMap.range (((p : ℤ) • 𝟙 M)).hom ↔ ∃ y : ↥M, (p : ℤ) • y = x
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [← hy, Work.Pi6.EMZ.smul_id_hom_apply]⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [Work.Pi6.EMZ.smul_id_hom_apply, hy]⟩

/-- `·p` on a free `ℤ`-module is injective. -/
theorem injective_zsmul_of_free (M : ModuleCat ℤ) (hM : Module.Free ℤ ↥M) (c : ℤ) (hc : c ≠ 0) :
    Function.Injective (fun x : ↥M => c • x) := by
  haveI := hM
  intro x y hxy
  apply (Module.Free.chooseBasis ℤ ↥M).repr.injective
  apply Finsupp.ext
  intro i
  have h1 := congrArg (fun z => (Module.Free.chooseBasis ℤ ↥M).repr z i) hxy
  simp only [map_zsmul, Finsupp.smul_apply] at h1
  exact mul_left_cancel₀ hc (by simpa [zsmul_eq_mul] using h1)

/-- The unit comparison on homology, as a linear equivalence. -/
abbrev unitLinEquiv (X : Type) [TopologicalSpace X] (i : ℕ) :
    ↥((Work.SSS.expTens (Work.Pi6.EMZ.chZ X) Work.Pi6.EMZ.zZ).homology i) ≃ₗ[ℤ]
      ↥(Work.Pi6.HR ℤ X i) :=
  (Work.Pi6.EMZ.expTensUnitHomologyIso X i).toLinearEquiv

/-- **The mod-`p` Bockstein identification.**  For a prime `p`, a space `X` and `n ≥ 1`, if the
integral homology `H_{n-1}(X;ℤ)` is free then the mod-`p` homology in degree `n` is the quotient of
`H_n(X;ℤ)` by its subgroup of `p`-multiples. -/
theorem hrModP (p : ℕ) (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ) (hn : 1 ≤ n)
    (hprev : Module.Free ℤ (Work.Pi6.HR ℤ X (n - 1))) :
    Nonempty (Work.Pi6.HR (ZMod p) X n ≃+
      (↥(Work.Pi6.HR ℤ X n) ⧸ (pMultiples p (Work.Pi6.HR ℤ X n)).toAddSubgroup)) := by
  classical
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set S := Work.Pi6.EMZ.bockSES p X with hSdef
  have hS : S.ShortExact :=
    Work.Pi6.EMZ.bockSES_shortExact p hp X (Work.Pi6.BOCK.coeffSESShortExact p hp)
  have hij : (ComplexShape.down ℕ).Rel n (n - 1) := by
    rw [ComplexShape.down_Rel]; omega
  -- the map in the sequence is multiplication by `p`
  have hSmulF (i : ℕ) : (HomologicalComplex.homologyMap S.f i).hom
      = ((p : ℤ) • 𝟙 ((Work.SSS.expTens (Work.Pi6.EMZ.chZ X) Work.Pi6.EMZ.zZ).homology i)).hom := by
    apply LinearMap.ext
    intro y
    exact Work.Pi6.BOCK.homologyMap_expTensHom_mulP p (Work.Pi6.EMZ.chZ X) i y
  -- exactness facts
  have hker1 : LinearMap.range (hS.δ n (n - 1) hij).hom
      = LinearMap.ker (HomologicalComplex.homologyMap S.f (n - 1)).hom :=
    ShortComplex.Exact.moduleCat_range_eq_ker (hS.homology_exact₁ n (n - 1) hij)
  have hker2 : LinearMap.range (HomologicalComplex.homologyMap S.f n).hom
      = LinearMap.ker (HomologicalComplex.homologyMap S.g n).hom :=
    ShortComplex.Exact.moduleCat_range_eq_ker (hS.homology_exact₂ n)
  have hker3 : LinearMap.range (HomologicalComplex.homologyMap S.g n).hom
      = LinearMap.ker (hS.δ n (n - 1) hij).hom :=
    ShortComplex.Exact.moduleCat_range_eq_ker (hS.homology_exact₃ n (n - 1) hij)
  -- `·p` is injective on `H_{n-1}`
  haveI hfreeA : Module.Free ℤ
      ↥((Work.SSS.expTens (Work.Pi6.EMZ.chZ X) Work.Pi6.EMZ.zZ).homology (n - 1)) :=
    Module.Free.of_equiv (unitLinEquiv X (n - 1)).symm
  have hinjE : Function.Injective
      (fun y : ↥((Work.SSS.expTens (Work.Pi6.EMZ.chZ X) Work.Pi6.EMZ.zZ).homology (n - 1)) =>
        (p : ℤ) • y) :=
    injective_zsmul_of_free _ hfreeA p hpz
  have hinjf : Function.Injective (HomologicalComplex.homologyMap S.f (n - 1)).hom := by
    rw [hSmulF (n - 1)]
    exact hinjE
  -- the connecting map vanishes and the second map is surjective
  have hdelta : (hS.δ n (n - 1) hij) = 0 := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_zero, ← LinearMap.range_eq_bot, hker1, LinearMap.ker_eq_bot]
    exact hinjf
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap S.g n).hom := by
    rw [← LinearMap.range_eq_top, hker3, hdelta, ModuleCat.hom_zero]
    exact LinearMap.ker_zero
  -- the range of the first map is the subgroup of `p`-multiples
  have hrange : (LinearMap.range (HomologicalComplex.homologyMap S.f n).hom).toAddSubgroup
      = (pMultiples p ((Work.SSS.expTens (Work.Pi6.EMZ.chZ X) Work.Pi6.EMZ.zZ).homology n)).toAddSubgroup := by
    rw [hSmulF n]
  -- the quotient identification
  have hker2' : (HomologicalComplex.homologyMap S.g n).hom.toAddMonoidHom.ker
      = (LinearMap.range (HomologicalComplex.homologyMap S.f n).hom).toAddSubgroup := by
    ext x
    show (HomologicalComplex.homologyMap S.g n).hom x = 0 ↔
      x ∈ LinearMap.range (HomologicalComplex.homologyMap S.f n).hom
    rw [hker2]
    exact Iff.rfl
  have e1 : ((Work.SSS.expTens (Work.Pi6.EMZ.chZ X) Work.Pi6.EMZ.zZ).homology n ⧸
      (LinearMap.range (HomologicalComplex.homologyMap S.f n).hom).toAddSubgroup) ≃+
      (Work.SSS.expTens (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.Mp p)).homology n := by
    rw [← hker2']
    exact QuotientAddGroup.quotientKerEquivOfSurjective _ hsurj
  -- transport along the unit comparison
  have hmap : AddSubgroup.map (unitLinEquiv X n).toAddEquiv
      (LinearMap.range (HomologicalComplex.homologyMap S.f n).hom).toAddSubgroup
      = (pMultiples p (Work.Pi6.HR ℤ X n)).toAddSubgroup := by
    rw [hrange]
    ext x
    constructor
    · intro hx
      rw [AddSubgroup.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [mem_pMultiples] at hy ⊢
      obtain ⟨z, hz⟩ := hy
      refine mem_pMultiples.mpr ⟨unitLinEquiv X n z, ?_⟩
      rw [← hz]
      exact ((unitLinEquiv X n).toAddEquiv.toAddMonoidHom.map_zsmul (p : ℤ) z).symm
    · intro hx
      rw [mem_pMultiples] at hx
      obtain ⟨z, hz⟩ := hx
      rw [AddSubgroup.mem_map]
      refine ⟨(p : ℤ) • (unitLinEquiv X n).symm z, ?_, ?_⟩
      · exact mem_pMultiples.mpr ⟨(unitLinEquiv X n).symm z, rfl⟩
      · have h2 : (unitLinEquiv X n) ((p : ℤ) • (unitLinEquiv X n).symm z) = x := by
          calc (unitLinEquiv X n) ((p : ℤ) • (unitLinEquiv X n).symm z)
              = (p : ℤ) • (unitLinEquiv X n) ((unitLinEquiv X n).symm z) :=
                (unitLinEquiv X n).toAddEquiv.toAddMonoidHom.map_zsmul (p : ℤ)
                  ((unitLinEquiv X n).symm z)
            _ = (p : ℤ) • z := by rw [LinearEquiv.apply_symm_apply]
            _ = x := hz
        exact h2
  have e2 : ((Work.SSS.expTens (Work.Pi6.EMZ.chZ X) Work.Pi6.EMZ.zZ).homology n ⧸
      (LinearMap.range (HomologicalComplex.homologyMap S.f n).hom).toAddSubgroup) ≃+
      (↥(Work.Pi6.HR ℤ X n) ⧸ (pMultiples p (Work.Pi6.HR ℤ X n)).toAddSubgroup) :=
    QuotientAddGroup.congr _ _ (unitLinEquiv X n).toAddEquiv hmap
  exact ⟨(Work.Pi6.EMZ.expTensCoeffAddEquiv p hp X n).symm.trans (e1.symm.trans e2)⟩

end

end Work.Pi6.K2Z
