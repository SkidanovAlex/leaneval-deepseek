import Mathlib
import Submission.Work.ThomBordism.TubeLocalDegree
import Submission.Work.ThomBordism.localDegreeSpan
import Submission.Work.ThomBordism.gtdU_span_top
import Submission.Work.ThomBordism.localDegreeGenExists

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

namespace Work.ThomBordism

open CategoryTheory

noncomputable section

/-! ## The abstract step: two generators of a `ℤ`-module and a linear functional

The whole content of the target, apart from the geometry, is the following elementary statement about
a `ℤ`-module: if `U` and `g` both generate `M` as a `ℤ`-module and a linear functional `Ψ x` takes the
value `R x` at `U`, then it takes the value `R x` at `g` or at `-g`.  (Indeed `g = c • U` and
`U = d • g` for integers `c, d`, so `U = (d*c) • U`; either all the `R x` vanish, or `U` has infinite
order and `d*c = 1`, whence `c = ±1`.) -/

theorem ldClass_or_neg_of_spans {M : Type*} [AddCommGroup M] [Module ℤ M] {ι : Type*}
    (Ψ : ι → M →ₗ[ℤ] ℤ) (R : ι → ℤ) {U g : M}
    (hUspan : Submodule.span ℤ ({U} : Set M) = ⊤)
    (hgspan : Submodule.span ℤ ({g} : Set M) = ⊤)
    (hU : ∀ x, Ψ x U = R x) :
    (∀ x, Ψ x g = R x) ∨ (∀ x, Ψ x (-g) = R x) := by
  classical
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (show g ∈ Submodule.span ℤ ({U} : Set M) from by rw [hUspan]; exact Submodule.mem_top)
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp
    (show U ∈ Submodule.span ℤ ({g} : Set M) from by rw [hgspan]; exact Submodule.mem_top)
  have hcU : ∀ x, Ψ x g = c • R x := fun x => by rw [← hc, LinearMap.map_smul, hU x]
  by_cases hz : ∀ x, R x = 0
  · left
    intro x
    rw [hcU x, hz x, smul_zero]
  · push Not at hz
    obtain ⟨x₀, hx₀⟩ := hz
    have hg1 : Ψ x₀ U = d • Ψ x₀ g := by rw [← hd, LinearMap.map_smul]
    have hkey : R x₀ = (d * c) * R x₀ := by
      have h1 : R x₀ = (d * c) • R x₀ := by
        calc R x₀ = Ψ x₀ U := (hU x₀).symm
          _ = d • Ψ x₀ g := hg1
          _ = d • (c • R x₀) := by rw [hcU x₀]
          _ = (d * c) • R x₀ := by rw [← mul_zsmul (R x₀) d c]
      have h2 := h1
      rw [zsmul_eq_mul] at h2
      simpa using h2
    have hdc : d * c = 1 := by
      have h1' : (1 : ℤ) * R x₀ = (d * c) * R x₀ := by rw [one_mul]; exact hkey
      exact (mul_right_cancel₀ hx₀ h1').symm
    have hcpm : c = 1 ∨ c = -1 := by
      have hunit : IsUnit c := isUnit_iff_exists_inv.mpr ⟨d, by rw [mul_comm]; exact hdc⟩
      exact Int.isUnit_iff.mp hunit
    rcases hcpm with h1 | h1
    · left
      intro x
      rw [hcU x, h1, zsmul_eq_mul]
      simp
    · right
      intro x
      rw [map_neg, hcU x, h1, zsmul_eq_mul]
      norm_num

theorem gtdU_localDegreeExists {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
    (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
    (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    {ε : ℝ} (hε : 0 < ε) (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
    (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y.ofLp j| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))) :
    Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox (Work.ThomBordism.gtdU E ND G hgm) ∨
    Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox
      (-(Work.ThomBordism.gtdU E ND G hgm)) := by
  classical
  obtain ⟨U, hUspan, hUild⟩ := localDegreeGenExists hk E hε C q hU hR hbox g hg hg2
  have hGspan : Submodule.span ℤ ({Work.ThomBordism.gtdU E ND G hgm} : Set
      (Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E))) = ⊤ :=
    Work.ThomBordism.gtdU_span_top hk E ND G hbp hvec hgm
  let X := TopCat.of (Work.Tubular.NormalTotal E)
  let A := Work.Tubular.normalNonzero E
  have hUspan' : Submodule.span ℤ ({U} : Set (Work.Thom.RelCoh ℤ k X A)) = ⊤ := hUspan
  have hGspan' : Submodule.span ℤ ({Work.ThomBordism.gtdU E ND G hgm} : Set
      (Work.Thom.RelCoh ℤ k X A)) = ⊤ := hGspan
  -- the local-degree functional, as a family of linear maps.  (`LinearMap.comp` of the project's
  -- `mixedCup`/`relKronH` would force the elaborator to unfold the module structure of the huge
  -- type `RelCoh ℤ k X A` and is prohibitively slow; building the structure by hand is cheap.)
  let Φ : Work.Thom.Coh ℤ 8 X → (Work.Thom.RelCoh ℤ k X A →ₗ[ℤ] ℤ) := fun x =>
    { toFun := fun W => Work.Tubular.relKronH X A (8 + k)
        ((Work.Cohomology.mixedCup X A 8 k x) W)
        ((Nat.add_comm 8 k).symm ▸ (Work.Tubular.collapseRelK8 C g hg hR hbox))
      map_add' := by
        intro a b
        rw [map_add (Work.Cohomology.mixedCup X A 8 k x) a b,
            LinearMap.map_add (Work.Tubular.relKronH X A (8 + k)) _ _,
            LinearMap.add_apply]
      map_smul' := by
        intro n a
        rw [LinearMap.map_smul (Work.Cohomology.mixedCup X A 8 k x) n a,
            LinearMap.map_smul (Work.Tubular.relKronH X A (8 + k)) n _,
            LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul] }
  let RHS : Work.Thom.Coh ℤ 8 X → ℤ := fun x =>
    Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
      ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom x) V.c
  have hΦ : ∀ (x : Work.Thom.Coh ℤ 8 X) (W : Work.Thom.RelCoh ℤ k X A),
      Φ x W = Work.Tubular.relKronH X A (8 + k)
        ((Work.Cohomology.mixedCup X A 8 k x) W)
        ((Nat.add_comm 8 k).symm ▸ (Work.Tubular.collapseRelK8 C g hg hR hbox)) :=
    fun x W => rfl
  -- the degree bridge between the defining degree `k + 8` and the working degree `8 + k`
  have hbridge : ∀ (W : Work.Thom.RelCoh ℤ k X A) (x : Work.Thom.Coh ℤ 8 X),
      Work.Tubular.relKronH X A (k + 8)
        ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup X A 8 k x W))
        (Work.Tubular.collapseRelK8 C g hg hR hbox)
      = Φ x W := by
    intro W x
    rw [hΦ x W]
    exact (Work.Tubular.relKronH_bridgeA (Nat.add_comm 8 k)
      ((Work.Cohomology.mixedCup X A 8 k x W))
      (Work.Tubular.collapseRelK8 C g hg hR hbox)).symm
  have hU' : ∀ x, Φ x U = RHS x := by
    intro x
    rw [← hbridge U x]
    exact hUild x
  rcases ldClass_or_neg_of_spans Φ RHS hUspan' hGspan' hU' with h | h
  · left
    intro x
    rw [hbridge (Work.ThomBordism.gtdU E ND G hgm) x]
    exact h x
  · right
    intro x
    rw [hbridge (-(Work.ThomBordism.gtdU E ND G hgm)) x]
    exact h x

end

end Work.ThomBordism
