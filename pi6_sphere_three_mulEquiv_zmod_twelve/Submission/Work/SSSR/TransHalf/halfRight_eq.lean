import Mathlib
import Submission.Work.SSSR.transportTransAux
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR.TransHalf

open scoped Topology unitInterval
open CategoryTheory
/-- **Cancellation of a transport computed through two ambient objects.**  Suppose that the two
"fibre" objects `X`, `Y` sit inside the ambient object `D` through the isomorphisms `A`, `A₁`, and
that the "middle" objects `M`, `N` sit inside a second ambient object `E` through the isomorphisms
`B₀`, `B₁`, while `M`, `N` are identified with `X`, `Y` through `P₀`, `P₁`.  If the two composite
ways `X → E → D` and `M → D` (resp. `Y → E → D` and `N → D`) of getting from a fibre to the ambient
object `D` agree, then the transport `A ≫ A₁⁻¹` computed through `D` agrees with the transport
computed through `E` and conjugated by `P₀`, `P₁`. -/
theorem halfRight_aux {C : Type*} [Category C] {X Y D M N E : C}
    (A : X ≅ D) (A₁ : Y ≅ D) (P₀ : M ≅ X) (P₁ : N ≅ Y)
    (B₀ : M ≅ E) (B₁ : N ≅ E) (Ψ : E ⟶ D)
    (h₀ : B₀.hom ≫ Ψ = P₀.hom ≫ A.hom) (h₁ : B₁.hom ≫ Ψ = P₁.hom ≫ A₁.hom) :
    Iso.trans A A₁.symm = Iso.trans P₀.symm (Iso.trans (Iso.trans B₀ B₁.symm) P₁) := by
  have hA : A.hom = P₀.inv ≫ B₀.hom ≫ Ψ := by
    have hh : P₀.inv ≫ B₀.hom ≫ Ψ = A.hom := by
      rw [h₀, Iso.inv_hom_id_assoc]
    exact hh.symm
  have hAinv : Ψ ≫ A₁.inv = B₁.inv ≫ P₁.hom := by
    have h := congrArg (fun f => B₁.inv ≫ f ≫ A₁.inv) h₁
    simp only [Category.assoc] at h
    rw [Iso.inv_hom_id_assoc] at h
    rw [Iso.hom_inv_id, Category.comp_id] at h
    exact h
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [hA]
  simp only [Category.assoc]
  rw [hAinv]

/-- The second half of the transport of the pullback of `p` along the concatenation `γ.trans δ`
agrees with the transport along `δ` conjugated by the homeomorphisms induced by the
reparametrisation `ψ : (e,t) ↦ (e, t/2+1/2)` of the pullback (on the fibre over `1` and the
identification of the fibre of the pullback over the junction point `1/2`). -/
theorem halfRight_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p) {b b' b'' : B}
    (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    Work.SSSR.halfRight p hp γ δ j =
      CategoryTheory.Iso.trans
        (CategoryTheory.Iso.symm (Work.SSSR.HZHomeoIso (Work.SSSR.psiTwelfthHomeo p γ δ) j))
        (CategoryTheory.Iso.trans (Work.SSSR.pathTrans (R := R) p hp δ j)
          (Work.SSSR.HZHomeoIso (Work.SSSR.psiOneHomeo p γ δ) j)) := by
  simp only [Work.SSSR.halfRight, Work.SSSR.pbTrans, Work.SSSR.pathTrans]
  have h0 : (Work.SSSR.inclIso p hp δ.toContinuousMap 0 j).hom ≫
        Work.SSSR.HZmap (R := R) (Work.SSSR.psiMap p γ δ) j
      = (Work.SSSR.HZHomeoIso (Work.SSSR.psiTwelfthHomeo p γ δ) j).hom ≫
        (Work.SSSR.inclIso p hp (γ.trans δ).toContinuousMap Work.SSSR.midI j).hom := by
    rw [Work.SSSR.HZHomeoIso_hom_HZmap]
    exact Work.SSSR.inclHZ_psiMap_mid p γ δ j
  have h1 : (Work.SSSR.inclIso p hp δ.toContinuousMap 1 j).hom ≫
        Work.SSSR.HZmap (R := R) (Work.SSSR.psiMap p γ δ) j
      = (Work.SSSR.HZHomeoIso (Work.SSSR.psiOneHomeo p γ δ) j).hom ≫
        (Work.SSSR.inclIso p hp (γ.trans δ).toContinuousMap 1 j).hom := by
    rw [Work.SSSR.HZHomeoIso_hom_HZmap]
    exact Work.SSSR.inclHZ_psiMap_one p γ δ j
  exact halfRight_aux _ _ _ _ _ _ _ h0 h1

end Work.SSSR.TransHalf
