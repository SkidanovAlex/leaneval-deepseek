import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.TubeLocalDegree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Two `ℤ`-smul bookkeeping lemmas and the linear-algebra core of the uniformity

The deduction below is pure `ℤ`-linear algebra; only the *conventions* of the two `ℤ`-scalar
multiplications on an `AddCommGroup`-with-`Module ℤ` (the one coming from `ZSMul` and the one coming
from the `Module` structure, which the `Submodule` API uses) need to be related. -/

/-- The `ℤ`-smul coming from the `Module ℤ` structure agrees with the canonical (`ZSMul`) one. -/
lemma branchSign_int_smul_module_eq_zsmul {M : Type*} [AddCommGroup M] [Module ℤ M]
    (n : ℤ) (b : M) :
    (@HSMul.hSMul ℤ M M (@instHSMul ℤ M (DistribMulAction.toDistribSMul.toSMul))) n b
      = (@HSMul.hSMul ℤ M M (@instHSMul ℤ M (ZSMul.toSMul))) n b := by
  have h := Int.cast_smul_eq_zsmul (R := ℤ) n b
  rwa [Int.cast_id] at h

/-- `Submodule.mem_span_singleton` with the `ℤ`-smul written in the canonical `ZSMul` form. -/
lemma branchSign_exists_int_smul_eq_of_mem_span_singleton {M : Type*} [AddCommGroup M] [Module ℤ M]
    {U y : M} (hy : y ∈ Submodule.span ℤ ({U} : Set M)) :
    ∃ m : ℤ, (@HSMul.hSMul ℤ M M (@instHSMul ℤ M (ZSMul.toSMul))) m U = y := by
  obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp hy
  exact ⟨m, (branchSign_int_smul_module_eq_zsmul m U).symm.trans hm⟩

/-- **The uniformity of the branch sign, abstractly.**  Let `L : M →ₗ[ℤ] N` and let `U ∈ M` be a
generator of `M` (`span{U} = ⊤`).  If the fibre generator `gN` of `N` generates `N` and `N ≅ ℤ`
(so `gN ≠ 0` and `N` has no `ℤ`-torsion), then any `g ∈ M` with `L g = s • gN` and `L U = gN` is
`s • U`: indeed `g = m • U` for some `m`, so `m • gN = s • gN`, and cancelling the nonzero `gN`
(in the free rank-one module `N`) gives `m = s`. -/
lemma branchSign_core {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (L : M →ₗ[ℤ] N) (U g : M) (gN : N) (s : ℤ)
    (hspan : Submodule.span ℤ ({U} : Set M) = ⊤)
    (hiso : Nonempty (N ≃ₗ[ℤ] ℤ))
    (hspanN : Submodule.span ℤ ({gN} : Set N) = ⊤)
    (h1 : L g = s • gN) (h2 : L U = gN) :
    g = s • U := by
  have hmem : g ∈ Submodule.span ℤ ({U} : Set M) := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨m, hm⟩ := branchSign_exists_int_smul_eq_of_mem_span_singleton hmem
  obtain ⟨e⟩ := hiso
  have hnf : gN ≠ 0 := by
    intro h0
    have htopbot : (⊤ : Submodule ℤ N) = ⊥ := by
      rw [← hspanN, h0]; simp
    haveI : Subsingleton N := ⟨fun a b => by
      have ha : a ∈ (⊥ : Submodule ℤ N) := htopbot ▸ Submodule.mem_top
      have hb : b ∈ (⊥ : Submodule ℤ N) := htopbot ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at ha hb
      rw [ha, hb]⟩
    have h10 : (1 : ℤ) = 0 := by
      have h := Subsingleton.elim (e.symm 1) (e.symm 0)
      simpa using congrArg e h
    exact one_ne_zero h10
  have henf : e gN ≠ 0 := fun h => hnf (e.injective (by rw [h, map_zero]))
  have hkey : m • gN = s • gN := by
    calc m • gN = m • L U := by rw [h2]
      _ = L (m • U) := (map_zsmul L m U).symm
      _ = L g := by rw [hm]
      _ = s • gN := h1
  have hms : m = s := by
    have h := congrArg (fun z => e z) hkey
    rw [map_zsmul e m gN, map_zsmul e s gN] at h
    exact mul_right_cancel₀ henf (by simpa using h)
  rw [← hm, hms]


theorem branchSign_uniform_of_fibreGen (k : ℕ) (hk : 1 ≤ k)
    (hF1 : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
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
        (x : V.pt),
        nfRes E x k (Work.ThomBordism.gtdU E ND G hgm) = s • nfGen hk E ND x)
    (hF2 : ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
      (U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U →
      ∀ x : V.pt, nfRes E x k U = nfGen hk E ND x)
    (hspanG : ∀ {V : Work.ThomBordism.Man8}
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt),
      Submodule.span ℤ ({nfGen hk E ND x} : Set (Work.Thom.RelCoh ℤ k ↥(nfSet E x)
        (nfPunct E x))) = ⊤)
    (hiso : ∀ {V : Work.ThomBordism.Man8}
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt),
      Nonempty (Work.Thom.RelCoh ℤ k ↥(nfSet E x) (nfPunct E x) ≃ₗ[ℤ] ℤ)) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
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
        {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
        (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
        (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
        (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
        (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
        (hg2 : ∀ y, y ∈ C.openTube →
          g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
        (U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E)),
        Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U →
        Submodule.span ℤ ({U} : Set (Work.Thom.RelCoh ℤ k
          (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E))) = ⊤ →
        Work.ThomBordism.gtdU E ND G hgm = s • U := by
  obtain ⟨s, hspm, hs⟩ := hF1
  refine ⟨s, hspm, ?_⟩
  intro V hV E ND G hgm hbp hvec eps C q hU R hR hbox g hg hg2 U hld hspan
  obtain ⟨x⟩ := hV.toNonempty
  exact branchSign_core (nfRes E x k) U (Work.ThomBordism.gtdU E ND G hgm) (nfGen hk E ND x) s
    hspan (hiso (V := V) E ND x) (hspanG (V := V) E ND x)
    (hs E ND G hgm hbp hvec x) (hF2 E ND C q hU hR hbox g hg hg2 U hld x)

end Work.ThomBordism
