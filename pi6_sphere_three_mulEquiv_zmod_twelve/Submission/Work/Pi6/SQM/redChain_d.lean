import Mathlib
import Submission.Work.Pi6.SQM.SqOneDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `Pi6/SQM/redChain_d`

`redChain : C_*(Y;ℤ) → C_*(Y;𝔽₂)` (`Work.Pi6.SQM.RedDefs`) is the coefficientwise reduction of
integral chains.  This file proves that it is a **chain map**: it intertwines the integral and the
mod-2 boundaries,

`redChain X n (∂^{ℤ}_{n+1} c) = ∂^{𝔽₂}_{n+1} (redChain X (n+1) c)`.

Both sides are `ℤ`-linear in `c`, so it suffices to check the identity on the generators of the
integral chains, i.e. on a simplex `σ : X _⦋n+1⦌`.  There, the boundary formula
`SSet.ιChainComplex_d` and `redChain_genElt` reduce the claim to the elementary coefficient
identity `((-1 : ℤ)^i : 𝔽₂) = (-1 : 𝔽₂)^i`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genElt genEval chainC)

/-- **The boundary of a generator**, in any commutative ring `R`: the differential applied to the
chain carried by a simplex `σ : Y _⦋n+1⦌` is `∑ᵢ (-1)ⁱ dᵢσ`. -/
theorem redChain_d_d_genElt (Y : SSet) (R : Type) [CommRing R] (n : ℕ) (σ : Y _⦋n+1⦌) :
    ((Y.chainComplex (ModuleCat.of R R)).d (n+1) n) (genElt R Y σ)
      = ∑ i : Fin (n+2), (-1 : R)^((i:ℕ)) • genElt R Y (Y.δ i σ) := by
  have hh := congrArg (fun (g : ModuleCat.of R R ⟶ (Y.chainComplex (ModuleCat.of R R)).X n) =>
    (ConcreteCategory.hom g) (1 : R)) (SSet.ιChainComplex_d Y (ModuleCat.of R R) σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, LinearMap.smul_apply] at hh
  have key : (∑ x : Fin (n+2), (-(1:ℤ))^((x:ℕ)) •
        ((Y.ιChainComplex (R := ModuleCat.of R R) ((Y.δ x) σ)).hom (1:R)))
      = ∑ i : Fin (n+2), (-(1:ℤ))^((i:ℕ)) • genElt R Y (Y.δ i σ) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [genElt]
  have key2 : (∑ i : Fin (n+2), (-(1:ℤ))^((i:ℕ)) • genElt R Y (Y.δ i σ))
      = ∑ i : Fin (n+2), (-(1:R))^((i:ℕ)) • genElt R Y (Y.δ i σ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Int.cast_smul_eq_zsmul R ((-(1:ℤ))^((i:ℕ))) (genElt R Y (Y.δ i σ))]
    push_cast
    rfl
  exact hh.trans (key.trans key2)

/-- `redChain` commutes with the differential, on generators. -/
theorem redChain_d_genElt (X : SSet) (n : ℕ) (σ : X _⦋n+1⦌) :
    redChain X n (((X.chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n).hom (genElt ℤ X σ))
      = ((X.chainComplex (ModuleCat.of (ZMod 2) (ZMod 2))).d (n + 1) n).hom
          (redChain X (n + 1) (genElt ℤ X σ)) := by
  have h1 := redChain_d_d_genElt X ℤ n σ
  have h2 := redChain_d_d_genElt X (ZMod 2) n σ
  rw [h1, redChain_genElt, h2]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [LinearMap.map_smul, redChain_genElt]
  rw [← Int.cast_smul_eq_zsmul (ZMod 2) ((-(1:ℤ))^((i:ℕ))) (genElt (ZMod 2) X (X.δ i σ))]
  push_cast
  rfl

/-- **`redChain` is a chain map**: the coefficientwise reduction of integral chains commutes with
the differentials. -/
theorem redChain_d (X : SSet) (n : ℕ)
    (c : ↥((X.chainComplex (ModuleCat.of ℤ ℤ)).X (n + 1))) :
    Work.Pi6.SQM.redChain X n (((X.chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n).hom c)
      = ((X.chainComplex (ModuleCat.of (ZMod 2) (ZMod 2))).d (n + 1) n).hom
          (Work.Pi6.SQM.redChain X (n + 1) c) := by
  let f : (↥((chainC ℤ X).X (n+1))) →ₗ[ℤ] (↥((chainC F2 X).X n)) :=
    (redChain X n).comp (((X.chainComplex (ModuleCat.of ℤ ℤ)).d (n+1) n).hom)
  let g : (↥((chainC ℤ X).X (n+1))) →ₗ[ℤ] (↥((chainC F2 X).X n)) :=
    (LinearMap.restrictScalars ℤ (((X.chainComplex (ModuleCat.of F2 F2)).d (n+1) n).hom)).comp
      (redChain X (n+1))
  have hfg : f = g := chain_ext f g (fun σ => redChain_d_genElt X n σ)
  have hc := LinearMap.congr_fun hfg c
  simpa [f, g] using hc

end

end Work.Pi6.SQM
