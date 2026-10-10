import Submission.Work.CY3Stab.Variety
import Submission.Work.CY3Stab.Prod.stronglyBirational_wProd_affine
import Submission.Work.CY3Stab.Prod.prodMap_isOver_pinned
import Submission.Work.CY3Stab.Prod.isDomain_cylTriplet_tensor
import Submission.Work.CY3Stab.ProdCoeff
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Main` — the stabilisation `Cr 5 → Cr n` and Theorem 1.2 (3) for `n ≥ 5`

This is the assembly module of the stabilisation chapter.  It contains

* `Work.CY3Stab.exists_cInv_ne_zero_add` — **the stabilisation step**: a non-vanishing invariant
  coefficient in `Cr 𝕜 5` yields one in `Cr 𝕜 (k + 5)`, by transporting the product map
  `φ × id_{𝔸ᵏ}` to affine space;
* `Work.CY3Stab.exists_cInv_ne_zero_of_prodStab` — the same in the shape of
  `Work.CY3.CY3Stabilisation.stabilise`, for `n ≥ 5` (with `k = n - 5`);
* `Work.CY3Stab.not_gen_of_CY3_infiniteField_of_prodStab` — **Theorem 1.2 (3) of the challenge for
  `n ≥ 5`**,
  from `Work.CY3.CY3Input` (the `thm:CY3` construction) and `Work.CY3.TotaroInput` (Totaro's
  `thm:BurtCY`/`cor-CYnSB`), together with the named residual `ProdStab 𝕜 (n - 5)`.

The route is the paper's: given `φ ∈ Cr 𝕜 5` with `cInv 𝕜 z₀ φ ≠ 0`, form `Ψ = φ × id_{𝔸ᵏ}` on the
cylinder `𝔸ᵏ × 𝔸⁵`, whose coefficient at the cylinder point is again nonzero
(`ProdStab.cInv_prodMap`), and transport `Ψ` back to a Cremona transformation of `𝔸^{k+5}` along
the isomorphism `𝔸ᵏ × 𝔸⁵ ≅ 𝔸^{k+5}` over `𝕜` (whose two halves are strong birationalities, hence
contribute nothing to the coefficient: `Work.CY3.cInv_transport_eq_of_eq_zero`).

The two interface facts used here are *proved* in this directory:
`Work.CY3Stab.varietyWProd` (the `Variety`-structure on the cylinder, with its canonical
`Over`-structure) and `Work.CY3Stab.Prod.stronglyBirational_wProd_affine` (the identification
`𝔸ᵏ × 𝔸⁵ ≅ 𝔸^{k+5}` as a strong birationality).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3Stab

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **The stabilisation step of `thm:bir-generation` (c)**: a non-vanishing invariant coefficient
in `Cr 𝕜 5` yields one in `Cr 𝕜 (k + 5)`.

The hypothesis `ProdStab 𝕜 k` is the *single* residual clause of the product analysis
(`Submission/Work/CY3Stab/Defs.lean`, `NOTES.md` §2): the `⟹` direction of the residue-field
comparison at the cylinder points.  Everything else — the `exDiv` analysis of `φ × id_{𝔸ᵏ}`, the
fact that `φ × id_{𝔸ᵏ}` is a map over `Spec 𝕜` at the canonical cylinder structure (proved in
`Work.CY3Stab.Prod.prodMap_isOver_pinned`) and the coefficient comparison
`cInv 𝕜 (prodPt z k) (φ × id) = cInv 𝕜 z φ` (`Work.CY3Stab.cInv_prodMap_eq`) — is proved here. -/
theorem exists_cInv_ne_zero_add (k : ℕ) (S : ProdStab 𝕜 k)
    (h : ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 5),
      cInv 𝕜 z₀ (φ : (Work.CY3.Affine 𝕜 5).BirationalMap (Work.CY3.Affine 𝕜 5)) ≠ 0) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 (k + 5)),
      cInv 𝕜 z₀ (φ : (Work.CY3.Affine 𝕜 (k + 5)).BirationalMap
        (Work.CY3.Affine 𝕜 (k + 5))) ≠ 0 := by
  classical
  obtain ⟨Z, hZ, z₀, φ₅, hφ⟩ := h
  letI : Z.Over (Spec (.of 𝕜)) := hZ
  -- the variety structure on the cylinder `𝔸ᵏ × 𝔸⁵` (with its canonical `Over`-structure)
  letI hVW : Variety 𝕜 (WProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k) :=
    varietyWProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k
  -- the `IsOver` instances of the given element of `Cr 𝕜 5` and of its inverse
  haveI hφ5over : (φ₅ : (Work.CY3.Affine 𝕜 5).BirationalMap (Work.CY3.Affine 𝕜 5)).IsOver
      (Spec (.of 𝕜)) := φ₅.2
  haveI hφ5s : ((φ₅ : (Work.CY3.Affine 𝕜 5).BirationalMap (Work.CY3.Affine 𝕜 5)).inv).IsOver
      (Spec (.of 𝕜)) := inferInstance
  -- the cylinder point over `z₀` is the generic point of its fibre: the domain-ness of the
  -- tensor of the cylinder triplet (proved in `Prod/isDomain_cylTriplet_tensor.lean`)
  haveI hDz : IsDomain (cylTriplet (𝕜 := 𝕜) Z z₀ k).tensor :=
    Work.CY3Stab.Prod.isDomain_cylTriplet_tensor 𝕜 k Z z₀
  haveI hDX : ∀ x : Work.CY3.Affine 𝕜 5,
      IsDomain (cylTriplet (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) x k).tensor :=
    fun x => Work.CY3Stab.Prod.isDomain_cylTriplet_tensor 𝕜 k (Work.CY3.Affine 𝕜 5) x
  -- the identification `𝔸ᵏ × 𝔸⁵ ≅ 𝔸^{k+5}` over `𝕜`, as a strong birationality
  have hBC : @Work.CY3.StronglyBirational 𝕜 _
      (WProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k) (Work.CY3.Affine 𝕜 (k + 5))
      (varietyWProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k)
      (inferInstance : Variety 𝕜 (Work.CY3.Affine 𝕜 (k + 5))) :=
    Work.CY3Stab.Prod.stronglyBirational_wProd_affine 𝕜 k
  obtain ⟨γ, hγover, hγ0⟩ := hBC
  haveI hγ : γ.IsOver (Spec (.of 𝕜)) := hγover
  haveI hγs : (γ.symm).IsOver (Spec (.of 𝕜)) := inferInstanceAs (γ.inv.IsOver (Spec (.of 𝕜)))
  -- the product map `Ψ = φ₅ × id` on the cylinder
  let Ψ : (WProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k).BirationalMap
      (WProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k) :=
    prodMap (𝕜 := 𝕜) k (φ₅ : (Work.CY3.Affine 𝕜 5).BirationalMap (Work.CY3.Affine 𝕜 5))
  -- `Ψ` is over the base field: the cylinder structure is the canonical one (`rfl`), so the
  -- *proved* `prodMap_isOver_pinned` applies
  haveI hΨover : Ψ.IsOver (Spec (.of 𝕜)) :=
    Work.CY3Stab.Prod.prodMap_isOver_pinned (𝕜 := 𝕜) k
      (φ₅ : (Work.CY3.Affine 𝕜 5).BirationalMap (Work.CY3.Affine 𝕜 5)) rfl rfl
  -- the transported Cremona transformation of `𝔸^{k+5}`
  refine ⟨WProd (𝕜 := 𝕜) Z k, inferInstance, prodPt (𝕜 := 𝕜) Z z₀ k,
    Work.CY3.transportCr (k + 5) (S := WProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k)
      (T := WProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k) γ.symm Ψ γ, ?_⟩
  rw [Work.CY3.transportCr_coe]
  have hε0 : cInv 𝕜 (prodPt (𝕜 := 𝕜) Z z₀ k) (γ.symm) = 0 := by
    rw [Work.LLink.cInv_eq_neg_symm, hγ0 (WProd (𝕜 := 𝕜) Z k) (prodPt Z z₀ k)]
    first | refl_ring1 | ring
  have hδ0 : cInv 𝕜 (prodPt (𝕜 := 𝕜) Z z₀ k) γ = 0 :=
    hγ0 (WProd (𝕜 := 𝕜) Z k) (prodPt Z z₀ k)
  rw [Work.CY3.cInv_transport_eq_of_eq_zero (k + 5) γ.symm Ψ γ
    (prodPt (𝕜 := 𝕜) Z z₀ k) hε0 hδ0]
  -- the coefficient comparison `cInv 𝕜 (prodPt z₀ k) (φ₅ × id) = cInv 𝕜 z₀ φ₅`, i.e. the residual
  intro hzero
  exact hφ (by
    rw [← S.cInv_prodMap (Work.CY3.Affine 𝕜 5)
      (φ₅ : (Work.CY3.Affine 𝕜 5).BirationalMap (Work.CY3.Affine 𝕜 5)) rfl Z z₀]
    exact hzero)

/-- **The stabilisation step of `thm:bir-generation` (c) in the shape of the CY3 chapter's named
input**: a non-vanishing invariant coefficient in `Cr 𝕜 5` yields one in `Cr 𝕜 n` for every
`n ≥ 5`. -/
theorem exists_cInv_ne_zero_of_prodStab {n : ℕ} (hn : 5 ≤ n) (S : ProdStab 𝕜 (n - 5))
    (h : ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 5),
      cInv 𝕜 z₀ (φ : (Work.CY3.Affine 𝕜 5).BirationalMap (Work.CY3.Affine 𝕜 5)) ≠ 0) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 n),
      cInv 𝕜 z₀ (φ : (Work.CY3.Affine 𝕜 n).BirationalMap (Work.CY3.Affine 𝕜 n)) ≠ 0 := by
  have h' := exists_cInv_ne_zero_add (𝕜 := 𝕜) (n - 5) S h
  rwa [Nat.sub_add_cancel hn] at h'

/-- **Theorem 1.2 (3) of the challenge for `n ≥ 5`**, from the `thm:CY3` construction and Totaro's
theorem, together with the named residual `ProdStab 𝕜 (n - 5)` of the product analysis. -/
theorem not_gen_of_CY3_infiniteField_of_prodStab {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜]
    [Infinite 𝕜] (I : Work.CY3.CY3Input 𝕜) (T : Work.CY3.TotaroInputAt 𝕜 I.data.Z I.data.Z')
    (S : ProdStab 𝕜 (n - 5)) : ¬ GenByPseudoRegularizable 𝕜 n :=
  Work.Motivic.not_gen_of_cInv_ne_zero 𝕜 n
    (exists_cInv_ne_zero_of_prodStab (𝕜 := 𝕜) hn S
      (Work.CY3.exists_cInv_ne_zero_infiniteField 𝕜 I T))

/-- **The named input `Work.CY3.CY3Stabilisation` of the CY3 chapter, produced from the residual
`ProdStab`**: the bridge consumed by `Work.CY3.not_gen_of_CY3_infiniteField` (and by the `n ≥ 5`
wiring of `Submission/Work/G2/LayerC.lean` and `Submission/Work/Totaro/Interface.lean`). -/
theorem cy3Stabilisation_of_prodStab (k : ℕ) (S : ProdStab 𝕜 k) :
    Work.CY3.CY3Stabilisation 𝕜 (k + 5) where
  stabilise := fun h => exists_cInv_ne_zero_add (𝕜 := 𝕜) k S h

/-- The same for `n ≥ 5`, in the exact shape of the CY3 chapter's named input. -/
theorem cy3Stabilisation_of_prodStab' {n : ℕ} (hn : 5 ≤ n) (S : ProdStab 𝕜 (n - 5)) :
    Work.CY3.CY3Stabilisation 𝕜 n := by
  have h := cy3Stabilisation_of_prodStab (𝕜 := 𝕜) (n - 5) S
  rwa [Nat.sub_add_cancel hn] at h

end

end Work.CY3Stab
