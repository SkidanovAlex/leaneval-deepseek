import Mathlib
import Submission.Work.Pi6.MSS.E1Aux
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The Serre cochain filtration is the annihilator of the Serre subcomplex

The Serre cochain filtration `coFilt 𝕜 f s n` is defined as the submodule of the `n`-cochains of
`X` vanishing on the singular simplices whose image in `Y` has essential dimension `< s`
(`Submission/Work/Pi6/MSS/Defs.lean`), while `compAnn 𝕜 A n` is the submodule of cochains vanishing
on the chains of a subcomplex `A` (`Submission/Work/Pi6/MSS/E1Aux.lean`).  This file proves that
they agree for `A = serreSubcomplex f s`, the preimage of the `s`-skeleton of `Y`:

* `Work.Pi6.MSS.mem_skeleton_iff_ess`: a simplex lies in the `s`-skeleton of `X` iff its essential
  dimension is `< s`;
* `Work.Pi6.MSS.mem_serreSubcomplex_iff_ess`: membership in `serreSubcomplex f s`, in terms of the
  essential dimension of the image;
* `Work.Pi6.MSS.mem_compAnn_iff`: a cochain lies in `compAnn 𝕜 A n` iff it vanishes on every
  generating simplex of `A` in degree `n`;
* `Work.Pi6.MSS.coFiltAnn`: `coFilt 𝕜 f s n = compAnn 𝕜 (serreSubcomplex f s) n`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

/-! ## The skeleton in terms of the essential dimension -/

/-- A simplex of `X` lies in the `s`-skeleton of `X` if and only if its essential dimension is
`< s`. -/
lemma mem_skeleton_iff_ess {X : SSet.{0}} {n : ℕ} (x : X _⦋n⦌) (s : ℕ) :
    x ∈ (X.skeleton s).obj (op ⦋n⦌) ↔ ess x < s := by
  have h1 : SSet.Subcomplex.ofSimplex x =
      SSet.Subcomplex.ofSimplex ((SSet.S.mk x).toN.simplex) := by
    rw [SSet.S.ofSimplex_eq_subcomplex_mk, ← SSet.S.subcomplex_toN (SSet.S.mk x)]
  rw [← SSet.Subcomplex.ofSimplex_le_iff x (X.skeleton s), h1,
    SSet.Subcomplex.ofSimplex_le_iff ((SSet.S.mk x).toN.simplex) (X.skeleton s),
    SSet.mem_skeleton_obj_iff_of_nonDegenerate X
      ⟨(SSet.S.mk x).toN.simplex, (SSet.S.mk x).toN.nonDegenerate⟩ s]
  simp only [ess]

/-- Membership in the Serre subcomplex `serreSubcomplex f s`, in terms of the essential dimension of
the image in `Y`. -/
lemma mem_serreSubcomplex_iff_ess {X Y : SSet.{0}} (f : X ⟶ Y) (s : ℕ) {n : ℕ}
    (τ : X _⦋n⦌) :
    τ ∈ (Work.StemsB.serreSubcomplex f s).obj (op ⦋n⦌) ↔
      ess (f.app (op ⦋n⦌) τ) < s := by
  rw [Work.StemsB.mem_serreSubcomplex, mem_skeleton_iff_ess]

/-! ## The annihilator of the chains of a subcomplex -/

/-- **The annihilator of the chains of a subcomplex**, described on generators: a cochain vanishes
on the chains of `A` iff it vanishes on every `n`-simplex of `A`. -/
lemma mem_compAnn_iff {𝕜 : Type} [CommRing 𝕜] {X : SSet.{0}} (A : X.Subcomplex) (n : ℕ)
    (c : Work.Cohomology.Cochain 𝕜 X n) :
    c ∈ compAnn 𝕜 A n ↔
      ∀ x : X _⦋n⦌, x ∈ A.obj (op ⦋n⦌) → Work.Cohomology.genEval 𝕜 X c x = 0 := by
  have key : ∀ σ : (A : SSet) _⦋n⦌,
      (Work.SSSR.sChainMap 𝕜 A.ι).f n
          (((A : SSet).ιChainComplex (R := ModuleCat.of 𝕜 𝕜) σ).hom 1)
        = (X.ιChainComplex (R := ModuleCat.of 𝕜 𝕜) (A.ι.app (op ⦋n⦌) σ)).hom 1 := by
    intro σ
    have hι := SSet.ι_chainComplexMap_f (A : SSet) X A.ι (ModuleCat.of 𝕜 𝕜) σ
    have h2 := congrArg (fun (g : ModuleCat.of 𝕜 𝕜
        ⟶ (X.chainComplex (ModuleCat.of 𝕜 𝕜)).X n) => g.hom 1) hι
    simpa only [Work.SSSR.sChainMap, ModuleCat.hom_comp, LinearMap.comp_apply] using h2
  have iota_app : ∀ σ : (A : SSet) _⦋n⦌, A.ι.app (op ⦋n⦌) σ = σ.1 := by
    intro σ
    rfl
  constructor
  · intro h x hx
    have hz := h (((A : SSet).ιChainComplex (R := ModuleCat.of 𝕜 𝕜) ⟨x, hx⟩).hom 1)
    rw [key ⟨x, hx⟩, iota_app ⟨x, hx⟩] at hz
    simpa only [Work.Cohomology.genEval] using hz
  · intro h z
    have hφ : (c.comp ((Work.SSSR.sChainMap 𝕜 A.ι).f n).hom) = 0 := by
      apply Work.Cohomology.genEval_ext (R := 𝕜) (X := (A : SSet))
      intro σ
      have hσ : Work.Cohomology.genEval 𝕜 (A : SSet)
            (c.comp ((Work.SSSR.sChainMap 𝕜 A.ι).f n).hom) σ
          = Work.Cohomology.genEval 𝕜 X c (A.ι.app (op ⦋n⦌) σ) := by
        rw [Work.Cohomology.genEval, Work.Cohomology.genEval, LinearMap.comp_apply,
          key σ]
      rw [hσ, iota_app σ, h σ.1 σ.2]
      simp [Work.Cohomology.genEval]
    have hz : (c.comp ((Work.SSSR.sChainMap 𝕜 A.ι).f n).hom) z = 0 := by
      rw [hφ, LinearMap.zero_apply]
    simpa only [LinearMap.comp_apply] using hz

/-! ## The main statement -/

/-- **The Serre cochain filtration is the annihilator of the chains on the Serre subcomplex.** -/
theorem coFiltAnn (𝕜 : Type) [CommRing 𝕜] {X Y : SSet.{0}} (f : X ⟶ Y) (s n : ℕ) :
    Work.Pi6.MSS.coFilt 𝕜 f s n =
      Work.Pi6.MSS.compAnn 𝕜 (Work.StemsB.serreSubcomplex f s) n := by
  refine le_antisymm ?_ ?_
  · intro c hc
    rw [mem_compAnn_iff]
    intro x hx
    exact hc x ((mem_serreSubcomplex_iff_ess f s x).mp hx)
  · intro c hc
    rw [mem_compAnn_iff] at hc
    intro τ hτ
    exact hc τ ((mem_serreSubcomplex_iff_ess f s τ).mpr hτ)

end

end Work.Pi6.MSS
