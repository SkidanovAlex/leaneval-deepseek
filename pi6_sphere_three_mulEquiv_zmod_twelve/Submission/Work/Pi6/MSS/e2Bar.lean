import Mathlib
import Submission.Work.Pi6.MSS.e2FinalDefs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The pairing `E_2^{s,q} × E²_{s,q} → 𝕜` on representatives

For `x ∈ Z_2^s` and `v ∈ ker(d¹ : E¹_{s,q} → E¹_{s-1,q})` put

`e2L0 x v = evZ x (e2Hb v)`,

the evaluation of the `E¹`-functional of `x` on the class of `v`.  This is `Work.Pi6.MSS.e2L0`.

The two properties needed for the final assembly are

* `e2L0` vanishes on `pDen 2` (so that it descends to `E_2^{s,q}`), and
* `e2L0 x` vanishes on `im(d¹ : E¹_{s+1,q} → E¹_{s,q})` (so that the descent lands in
  `(im d¹)^⊥ ⊆ (ker d¹)^*`, the image of `(E²_{s,q})^*`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The `d¹`-cycles of the `E¹`-complex, as a submodule of `E¹_{s,q}`. -/
abbrev e2KerD (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s q : ℕ) :
    Submodule 𝕜 ↥((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X s) :=
  LinearMap.ker ((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d s (s - 1)).hom

/-- **The evaluation pairing on representatives**: `x ∈ Z_2^s` evaluated on the `d¹`-cycles of
`E¹_{s,q}`. -/
noncomputable def e2L0 (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s q : ℕ) :
    ↥(pZ 𝕜 (Wc 𝕜 p) 2 s (s + q)) →ₗ[𝕜]
      (↥(e2KerD 𝕜 p s q) →ₗ[𝕜] 𝕜) :=
  let hfirst : ↥(pZ 𝕜 (Wc 𝕜 p) 2 s (s + q)) →ₗ[𝕜]
      ↥(pZ 𝕜 (Wc 𝕜 p) 1 s (s + q)) :=
    LinearMap.codRestrict (pZ 𝕜 (Wc 𝕜 p) 1 s (s + q))
      (pZ 𝕜 (Wc 𝕜 p) 2 s (s + q)).subtype
      (fun x => pZ_two_le_one 𝕜 p s (s + q) x.2)
  let hsecond : ↥(pZ 𝕜 (Wc 𝕜 p) 1 s (s + q)) →ₗ[𝕜]
      ((↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) (s + q)) ⧸
        Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) (s + q)) →ₗ[𝕜] 𝕜) :=
    evZ 𝕜 p s (s + q) (hannSerre 𝕜 p)
  let g : ↥(e2KerD 𝕜 p s q) →ₗ[𝕜]
      (↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) (s + q)) ⧸
        Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) (s + q)) :=
    (e2Hb 𝕜 (Kg 𝕜 p s) (s + q)).hom.hom.comp (e2KerD 𝕜 p s q).subtype
  let hthird : ((↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) (s + q)) ⧸
        Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) (s + q)) →ₗ[𝕜] 𝕜) →ₗ[𝕜]
      (↥(e2KerD 𝕜 p s q) →ₗ[𝕜] 𝕜) :=
    { toFun := fun φ => φ.comp g
      map_add' := fun a b => by ext v; simp
      map_smul' := fun c a => by ext v; simp }
  hthird.comp (hsecond.comp hfirst)

/-- The image of `d¹ : E¹_{s+1,q} → E¹_{s,q}` as an element of the `d¹`-cycles. -/
noncomputable def e2dIm (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (s q : ℕ)
    (u : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X (s + 1)) : ↥(e2KerD 𝕜 p s q) :=
  ⟨(Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d (s + 1) s u, by
    show (ModuleCat.Hom.hom ((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d s (s - 1)))
      ((ModuleCat.Hom.hom ((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d (s + 1) s)) u) = 0
    by_cases h : (ComplexShape.down ℕ).Rel s (s - 1)
    · have h2 := congrArg ModuleCat.Hom.hom
        (HomologicalComplex.d_comp_d (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) (s + 1) s (s - 1))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero] at h2
      exact LinearMap.congr_fun h2 u
    · rw [HomologicalComplex.shape _ _ _ h]
      rfl⟩

/-- The projection of the `d¹`-cycles onto the `E²`-page `E²_{s,q} = H_s(E¹_{*,q})`, through the
identification `E²_{s,q} ≅ Z/B` of `e2Hb`. -/
noncomputable def e2mkQ (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (s q : ℕ) :
    ↥(e2KerD 𝕜 p s q) →ₗ[𝕜] (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).homology s :=
  (e2Hb 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s).inv.hom.comp
    (Work.StemsB.fdH 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s).mkQ

/-- The value rule of `e2mkQ`. -/
theorem e2mkQ_apply (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s q : ℕ) (v : ↥(e2KerD 𝕜 p s q)) :
    e2mkQ 𝕜 E B p s q v
      = (e2Hb 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s).inv.hom
          ((Work.StemsB.fdH 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) s).mkQ v) := rfl


end

end Work.Pi6.MSS


