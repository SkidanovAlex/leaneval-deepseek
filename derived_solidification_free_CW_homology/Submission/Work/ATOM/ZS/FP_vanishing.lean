import Mathlib
import Submission.Work.ATOM.ZS.Topo.Maps

namespace Work.ATOM.ZS

open CategoryTheory MonoidalCategory LightCondensed LightProfinite OnePoint Limits

/-! ## Toolbox: `zmap` of a constantly-`∞` map kills `P_proj`

A morphism `f : X ⟶ ℕ∪{∞}` whose value is constantly `∞` factors through the point
`∞ : pt ⟶ ℕ∪{∞}`, and `zmap ∞ = P_map` is killed by `P_proj` (it is the kernel inclusion of
`P = cokernel P_map`). -/

/-- `zmap` is functorial. -/
lemma zmap_comp {X Y Z : LightProfinite.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Work.ATOM.zmap (f ≫ g) = Work.ATOM.zmap f ≫ Work.ATOM.zmap g := by
  simp only [Work.ATOM.zmap, Functor.comp_map, Functor.map_comp]

/-- `zmap` applied to the inclusion of the point `∞` is `P_map`. -/
lemma zmap_ptAt_infty :
    Work.ATOM.zmap (Work.ATOM.ptAt (∞ : ↥LightProfinite.NatUnionInfty)) = LightCondensed.P_map := by
  rw [show Work.ATOM.ptAt (∞ : ↥LightProfinite.NatUnionInfty) =
      (LightCondensed.ι : Work.ATOM.pt ⟶ LightProfinite.NatUnionInfty) from by
    apply ConcreteCategory.hom_ext; intro x; rfl]
  rfl

/-- `P_map` is killed by the projection `P_proj` (it is the kernel inclusion of `P`). -/
lemma P_map_comp_P_proj : LightCondensed.P_map ≫ LightCondensed.P_proj = 0 := cokernel.condition _

/-- A morphism `ℤ[X] ⟶ ℤ[ℕ∪{∞}]` induced by a map `X ⟶ ℕ∪{∞}` which is constantly `∞` is killed
by `P_proj`: it factors through `ℤ[∞] ⟶ ℤ[ℕ∪{∞}]`, whose cokernel is `P`. -/
lemma zmap_const_infty_comp_P_proj {X : LightProfinite.{0}} (f : X ⟶ LightProfinite.NatUnionInfty)
    (hf : ∀ x, f x = ∞) : Work.ATOM.zmap f ≫ LightCondensed.P_proj = 0 := by
  have hfac : f = Work.ATOM.toPt X ≫ Work.ATOM.ptAt (∞ : ↥LightProfinite.NatUnionInfty) := by
    apply ConcreteCategory.hom_ext
    intro x
    simp only [ConcreteCategory.comp_apply]
    exact hf x
  rw [hfac, zmap_comp, zmap_ptAt_infty, Category.assoc, P_map_comp_P_proj, comp_zero]

/-- `φ_P` vanishes on the second `∞`-axis: `φ_P(q,∞) = ∞` for every `q`. -/
lemma phiP_infty_right (S : LightProfinite.{0}) [Infinite S] (q : ↥LightProfinite.NatUnionInfty) :
    Work.ATOM.phiP S (q, ∞) = ∞ := by
  rcases q with _ | k
  · exact Work.ATOM.phiP_infty_left S _
  · exact Work.ATOM.phiP_some_infty S k

/-- **The vanishing of `φ_P` on the two `∞`-axes.**  `φ_P(k,∞) = ∞` and `φ_P(∞,j) = ∞`
(`Work.ATOM.phiP_some_infty`, `Work.ATOM.phiP_infty_left`), so `zmap φ_P ≫ P_proj` kills the images
of both `zmap (whiskerRight ι ℕ∪{∞})` and `zmap (whiskerLeft ℕ∪{∞} ι)`; hence it descends along
`Work.ATOM.EApp` to `F_P : P ⊗ P ⟶ P`. -/
theorem FP_vanishing (S : LightProfinite.{0}) [Infinite S] :
    (Work.ATOM.zmap (MonoidalCategory.whiskerRight LightCondensed.ι
        (LightProfinite.NatUnionInfty)) ≫
        (Work.ATOM.zmap (Work.ATOM.phiP S) ≫ LightCondensed.P_proj) = 0) ∧
      (Work.ATOM.zmap (MonoidalCategory.whiskerLeft (LightProfinite.NatUnionInfty)
        LightCondensed.ι) ≫
        (Work.ATOM.zmap (Work.ATOM.phiP S) ≫ LightCondensed.P_proj) = 0) := by
  constructor
  · -- the first `∞`-axis: `whiskerRight ι ℕ∪{∞} ≫ φ_P` is the constant map at `∞`
    rw [← Category.assoc, ← zmap_comp]
    exact zmap_const_infty_comp_P_proj _ (fun p => by
      obtain ⟨u, q⟩ := p
      show Work.ATOM.phiP S
        ((MonoidalCategory.whiskerRight LightCondensed.ι LightProfinite.NatUnionInfty) (u, q)) = ∞
      rw [show (MonoidalCategory.whiskerRight LightCondensed.ι LightProfinite.NatUnionInfty) (u, q)
        = (∞, q) from rfl]
      exact Work.ATOM.phiP_infty_left S q)
  · -- the second `∞`-axis: `whiskerLeft ℕ∪{∞} ι ≫ φ_P` is the constant map at `∞`
    rw [← Category.assoc, ← zmap_comp]
    exact zmap_const_infty_comp_P_proj _ (fun p => by
      obtain ⟨q, u⟩ := p
      show Work.ATOM.phiP S
        ((MonoidalCategory.whiskerLeft LightProfinite.NatUnionInfty LightCondensed.ι) (q, u)) = ∞
      rw [show (MonoidalCategory.whiskerLeft LightProfinite.NatUnionInfty LightCondensed.ι) (q, u)
        = (q, ∞) from rfl]
      exact phiP_infty_right S q)

end Work.ATOM.ZS
