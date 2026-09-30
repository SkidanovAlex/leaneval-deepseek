import Mathlib
import Submission.Work.Pi6.MSS.e2ColAux
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.MSS.essMapLeCardImage
import Submission.Work.SSS.sSingP_fibreIncl_comp
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# `F^1 C^q` restricts to zero on the fibre

The first step of the Serre filtration of the singular cochains of `E` along a fibration `p : E → B`
consists of the cochains vanishing on the singular simplices of `E` lying over the vertices of `B`
(equivalently, over the constant simplices of `B`).  Every simplex of the fibre `p⁻¹(p e₀)` is such
a simplex, so the restriction of an `F^1`-cochain to the fibre vanishes:

`Work.Pi6.MSS.e2Col_coFilt_ker_res`.

The only geometric input is that a simplex which lies in the image of the constant simplicial map
at a vertex has essential dimension `0` (`Work.Pi6.MSS.ess_const_lt_one`), which is an instance of
`Work.Pi6.MSS.essMapLeCardImage` (the essential dimension of a pullback along `φ` is at most the
number of vertices in the image of `φ`).
-/

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

/-- A simplex lying in the image of the constant simplicial map at a vertex has essential dimension
`0`; in particular it is `< 1`.  (The simplex `(SSet.const y).app (op ⦋q⦌) x` is the degeneracy of
the `0`-simplex `y` along the constant morphism `⦋q⦌ ⟶ ⦋0⦌`, whose image has a single vertex.) -/
lemma ess_const_lt_one {X Y : SSet.{0}} (y : Y _⦋0⦌) (q : ℕ) (x : X _⦋q⦌) :
    ess ((SSet.const (X := X) y).app (op ⦋q⦌) x) < 1 := by
  have hmap : (SSet.const (X := X) y).app (op ⦋q⦌) x
      = Y.map (SimplexCategory.const ⦋q⦌ ⦋0⦌ 0).op y := rfl
  have hbound := essMapLeCardImage (X := Y) (SimplexCategory.const ⦋q⦌ ⦋0⦌ 0) y
  have himg : (Finset.univ.image (SimplexCategory.Hom.toOrderHom
      (SimplexCategory.const ⦋q⦌ ⦋0⦌ 0)) : Finset (Fin 1)) = {0} := by
    ext b
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨a, ha⟩
      rw [← ha]
      rfl
    · rintro rfl
      exact ⟨0, rfl⟩
  rw [himg, Finset.card_singleton] at hbound
  rw [hmap]
  omega

/-- **The Serre filtration step `F^1` is contained in the kernel of the restriction to the fibre.**
A cochain of `E` vanishing on the simplices over the vertices of `B` restricts to zero on the fibre
`p⁻¹(p e₀)`, because every simplex of the fibre projects to the constant simplex at `p e₀`. -/
theorem e2Col_coFilt_ker_res (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (q : ℕ)
    (c : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) q)
    (hc : c ∈ Work.Pi6.MSS.coFilt 𝕜 (Work.SSS.sSingP p) 1 q) :
    Work.Pi6.MSS.resCochain 𝕜 E B p e₀ q c = 0 := by
  -- the defining property of `F^1`: vanishing on the simplices with constant image in `B`
  have hc' : ∀ τ : (Work.SSS.sSing E) _⦋q⦌,
      ess ((Work.SSS.sSingP p).app (op ⦋q⦌) τ) < 1 →
      Work.Cohomology.genEval 𝕜 (Work.SSS.sSing E) c τ = 0 := hc
  -- `p ∘ (fibre inclusion) = const (p e₀)` on singular simplicial sets
  have hcomp := Work.SSS.sSingP_fibreIncl_comp p (p e₀)
  apply Work.Cohomology.genEval_ext
  intro σ
  have hkey : (Work.SSS.sSingP p).app (op ⦋q⦌)
        ((Work.SSS.sSingP (Work.StemsB.fibreIncl p (p e₀))).app (op ⦋q⦌) σ)
      = (SSet.const (TopCat.toSSetObj₀Equiv.symm (p e₀))).app (op ⦋q⦌) σ := by
    have h := congrArg
      (fun (g : Work.SSS.sSing (Work.StemsB.fibre p (p e₀)) ⟶ Work.SSS.sSing B) =>
        g.app (op ⦋q⦌) σ) hcomp
    rw [SSet.comp_app] at h
    exact h
  rw [genEval_resCochain, hc' _ (hkey ▸ ess_const_lt_one _ q σ)]
  simp [Work.Cohomology.genEval]

end

end Work.Pi6.MSS
