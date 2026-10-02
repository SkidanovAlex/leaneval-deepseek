import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.TubeLocalDegree
import Submission.Work.ThomBordism.gtdGaussCandidate
import Submission.Work.ThomBordism.gtdU_span_top
import Submission.Work.ThomBordism.fibreRes_gtdU_canonical
import Submission.Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero
import Submission.Work.ThomBordism.branchSign_uniform_of_fibreGen
import Submission.Work.ThomBordism.branchSign_uniform_gauss

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fibre restriction of a local-degree class is a *uniform* sign times the oriented generator

The datum is an embedding `E : V ↪ ℝ^{8+k}` of a closed oriented smooth `8`-manifold, a tube chart
`C` with its metric-free collapse `g`, and a class
`U ∈ H^k(ν, ν∖0)` implementing the local degree of `V.c` with respect to the collapse class
(`Work.ThomBordism.IsLocalDegreeClass`).  The conclusion is that on every fibre the restriction of
`U` is a *single* sign `t = ±1` — the same sign for all data and all points `x` — times the oriented
fibre generator `nfGen` (the reading of `stdThomGen` in the σ-corrected frame `Gauss.gframe`).

## The reduction

1. **Uniqueness** (`isLocalDegreeClass_eq_of_generating`, proved below): a local-degree class that
   generates `H^k(ν, ν∖0)` is *the* local-degree class, because the local-degree functional separates
   points (`Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero`: some `x` pairs nontrivially with
   `V.c`).
2. **The canonical Gauss candidate** (`Work.ThomBordism.gtdGaussCandidate`): from the tube data one
   gets a classifying map `G` of the normal bundle whose plane field is `padGaussFun` and whose
   vector field is the ambient normal vector; its class `gtdU E ND G hgm` generates
   (`Work.ThomBordism.gtdU_span_top`).
3. **The branch sign** (`Work.ThomBordism.branchSign_uniform_gauss`): a single `ε = ±1` with
   `IsLocalDegreeClass (ε • gtdU E ND G hgm)` for *every* datum.  By (1) this pins
   `U = ε • gtdU E ND G hgm`.
4. **The fibre reading** (`Work.ThomBordism.fibreRes_gtdU_canonical`): a single `s = ±1` with
   `nfRes E x k (gtdU E ND G hgm) = s • nfGen hk E ND x` for *every* datum and every `x`.
   Hence `nfRes E x k U = (ε * s) • nfGen hk E ND x`, with `t := ε * s` independent of the datum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

noncomputable section

/-- **Uniqueness of the local-degree class** (given a generating solution).

If `U₀` is a local-degree class generating `H^k(ν, ν∖0)` then *every* local-degree class equals
`U₀`: for `W = U - U₀` the local-degree functional vanishes, and since the functional separates
points (`Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero`) and `W` is a multiple of the
generator `U₀`, that multiple is `0`. -/
theorem isLocalDegreeClass_eq_of_generating {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    {k : ℕ} {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    {eps : ℝ} {C : Work.Tubular.TubeChart E eps} (q : Work.Tubular.NormalSphSub E eps)
    {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E eps (C.inv y)))
    {U₀ U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)}
    (hspan : Submodule.span ℤ ({U₀} : Set (Work.Thom.RelCoh ℤ k
      (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E))) = ⊤)
    (hU₀ : Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U₀)
    (hU : Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U) : U = U₀ := by
  classical
  obtain ⟨x₀, hx₀⟩ := exists_kronH_zeroSection_fund_ne_zero E
  let X := TopCat.of (Work.Tubular.NormalTotal E)
  let A := Work.Tubular.normalNonzero E
  let c := Work.Tubular.collapseRelK8 C g hg hR hbox
  let RHS : Work.Thom.Coh ℤ 8 X → ℤ := fun x =>
    Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
      ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom x) V.c
  let Φ : Work.Thom.Coh ℤ 8 X → (Work.Thom.RelCoh ℤ k X A →ₗ[ℤ] ℤ) := fun x =>
    { toFun := fun W => Work.Tubular.relKronH X A (8 + k)
        ((Work.Cohomology.mixedCup X A 8 k x) W)
        ((Nat.add_comm 8 k).symm ▸ c)
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
  have hbridge : ∀ (W : Work.Thom.RelCoh ℤ k X A) (x : Work.Thom.Coh ℤ 8 X),
      Work.Tubular.relKronH X A (k + 8)
        ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup X A 8 k x W)) c = Φ x W := by
    intro W x
    exact (Work.Tubular.relKronH_bridgeA (Nat.add_comm 8 k)
      ((Work.Cohomology.mixedCup X A 8 k x W)) c).symm
  have hU' : ∀ x, Φ x U = RHS x := fun x => (hbridge U x).symm.trans (hU x)
  have hU₀' : ∀ x, Φ x U₀ = RHS x := fun x => (hbridge U₀ x).symm.trans (hU₀ x)
  have hW : Φ x₀ (U - U₀) = 0 := by
    rw [map_sub, hU' x₀, hU₀' x₀, sub_self]
  obtain ⟨m, hm⟩ := branchSign_exists_int_smul_eq_of_mem_span_singleton (U := U₀) (y := U - U₀)
    (show U - U₀ ∈ Submodule.span ℤ ({U₀} : Set (Work.Thom.RelCoh ℤ k X A)) from by
      rw [hspan]; exact Submodule.mem_top)
  have hzero : Φ x₀ (m • U₀) = 0 := by rw [hm]; exact hW
  have hstep : Φ x₀ (m • U₀) = m * RHS x₀ := by
    have h' : Φ x₀ (m • U₀) = m • Φ x₀ U₀ :=
      AddMonoidHom.map_zsmul (Φ x₀).toAddMonoidHom m U₀
    rw [h', hU₀' x₀, zsmul_eq_mul, Int.cast_id]
  have hm0 : m = 0 := by
    rw [hstep] at hzero
    exact (mul_eq_zero.mp hzero).resolve_right hx₀
  have hlast : U - U₀ = 0 := by rw [← hm, hm0]; exact zero_smul ℤ U₀
  exact sub_eq_zero.mp hlast

theorem fibreRes_localDegreeClass_eq_nfGen_uniform (k : ℕ) (hk : 1 ≤ k) :
    ∃ t : ℤ, (t = 1 ∨ t = -1) ∧
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
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
      ∀ x : V.pt, nfRes E x k U = t • nfGen hk E ND x := by
  classical
  obtain ⟨s, hs, hF1⟩ := fibreRes_gtdU_canonical k hk
  obtain ⟨e₀, he₀, hbr⟩ := branchSign_uniform_gauss k hk
  refine ⟨e₀ * s, ?_, ?_⟩
  · rcases he₀ with h | h <;> rcases hs with h' | h' <;> rw [h, h'] <;> norm_num
  · intro V _ E ND eps C q hU R hR hbox g hg hg2 U hUild x
    obtain ⟨G, hbp, hvec, hgm, -⟩ :=
      gtdGaussCandidate E ND C.eps_pos C q hU hR hbox g hg hg2
    have hspanG : Submodule.span ℤ ({Work.ThomBordism.gtdU E ND G hgm} : Set
        (Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E))) = ⊤ :=
      Work.ThomBordism.gtdU_span_top (V := V) (k := k) hk E ND G hbp hvec hgm
    have hspanE : Submodule.span ℤ ({e₀ • Work.ThomBordism.gtdU E ND G hgm} : Set
        (Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E))) = ⊤ := by
      have hone : e₀ • Work.ThomBordism.gtdU E ND G hgm = Work.ThomBordism.gtdU E ND G hgm ∨
          e₀ • Work.ThomBordism.gtdU E ND G hgm = - Work.ThomBordism.gtdU E ND G hgm := by
        rcases he₀ with h | h
        · left; rw [h, one_smul]
        · right; rw [h]; simp
      exact Work.ThomBordism.span_zsmul_eq_top_of_eq_pm_one _ _ hone hspanG
    have hild : Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox
        (e₀ • Work.ThomBordism.gtdU E ND G hgm) := hbr E ND G hgm hbp hvec C q hU hR hbox g hg hg2
    have hUeq : U = e₀ • Work.ThomBordism.gtdU E ND G hgm :=
      isLocalDegreeClass_eq_of_generating (V := V) (k := k) (E := E) (C := C) q hR hbox g hg hg2
        hspanE hild hUild
    have h1 : nfRes E x k U = e₀ • nfRes E x k (Work.ThomBordism.gtdU E ND G hgm) := by
      rw [hUeq, map_zsmul]
    have h2 : nfRes E x k (Work.ThomBordism.gtdU E ND G hgm) = s • nfGen hk E ND x :=
      hF1 E ND G hgm hbp hvec x
    rw [h1, h2, smul_smul, mul_comm]

end

end Work.ThomBordism
