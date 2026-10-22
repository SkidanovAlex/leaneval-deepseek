import Mathlib
import Submission.Work.ANALYTIC.unprimedSetup
import Submission.Work.ANALYTIC.coordTimesDelta_mem_range
import Submission.Work.ANALYTIC.pt_kernel_cBounded
import Submission.Work.ANALYTIC.points_detect_zfree_NatUnionInfty

set_option backward.isDefEq.respectTransparency false

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

/-- The element `[const ∞]` of `ℤ[ℕ∪{∞}]` over the one-point space: the class of the constant
map `pt ⟶ ℕ∪{∞}` at `∞`, i.e. the image of the generator `zmap ι` under `homFreeEquiv`. -/
abbrev constInftyElem :
    ↥((Work.ATOM.zfree (LightProfinite.NatUnionInfty)).obj.obj (Opposite.op Work.ATOM.pt)) :=
  Work.ANALYTIC.freeHomEquiv Work.ATOM.pt (Work.ATOM.zfree (LightProfinite.NatUnionInfty))
    (Work.ATOM.zmap (LightCondensed.ι))

/-- `Work.ATOM.homFreeEquiv` and `Work.ANALYTIC.freeHomEquiv` are the same map, so the element
`[const ∞]` may be written in either notation. -/
theorem constInftyElem_atom :
    constInftyElem = Work.ATOM.homFreeEquiv Work.ATOM.pt
      (Work.ATOM.zfree (LightProfinite.NatUnionInfty)) (Work.ATOM.zmap (LightCondensed.ι)) := rfl

/-- The map `σ : (ℕ∪{∞}) ⟶ pt`. -/
abbrev sigmaMap : LightProfinite.NatUnionInfty ⟶ Work.ATOM.pt := Work.ATOM.toPt _

/-- `zmap` is functorial. -/
theorem zmap_comp {S T U : LightProfinite.{0}} (f : S ⟶ T) (g : T ⟶ U) :
    Work.ATOM.zmap f ≫ Work.ATOM.zmap g = Work.ATOM.zmap (f ≫ g) :=
  (CategoryTheory.Functor.map_comp (self := lightProfiniteToLightCondSet ⋙ free ℤ) f g).symm

/-- `ι ≫ σ = 𝟙` on the one-point space. -/
theorem iota_comp_sigma : LightCondensed.ι ≫ sigmaMap = 𝟙 Work.ATOM.pt := by
  apply ConcreteCategory.hom_ext
  intro x
  exact Subsingleton.elim _ _

/-- `zmap ι ≫ zmap σ = 𝟙`. -/
theorem zmap_iota_sigma : Work.ATOM.zmap (LightCondensed.ι) ≫ Work.ATOM.zmap sigmaMap =
    𝟙 (Work.ATOM.zfree Work.ATOM.pt) := by
  calc Work.ATOM.zmap (LightCondensed.ι) ≫ Work.ATOM.zmap sigmaMap
      = Work.ATOM.zmap (LightCondensed.ι ≫ sigmaMap) := zmap_comp _ _
    _ = Work.ATOM.zmap (𝟙 Work.ATOM.pt) := by rw [iota_comp_sigma]
    _ = 𝟙 (Work.ATOM.zfree Work.ATOM.pt) :=
        CategoryTheory.Functor.map_id (self := lightProfiniteToLightCondSet ⋙ free ℤ) _

/-- **Assembly.**  Given the two pointwise inputs (the kernel of `P_proj ≫ cBounded` at the point,
and the fact that sections of `ℤ[ℕ∪{∞}]` are detected by their restrictions to points), the map
`cBounded : P ⟶ ∏^bnd ℤ` is a monomorphism.

The proof: a map `φ : ℤ[T] ⟶ P` killed by `cBounded` lifts along the split quotient
`P_proj : ℤ[ℕ∪{∞}] ⟶ P` to `x = φ ≫ s`, because `s ≫ P_proj = 𝟙`.  Every restriction of `x` to a
point is a multiple `n·[const ∞]`, and the multiple is realised by the *same* element
`f = x ≫ zmap σ : ℤ[T] ⟶ ℤ[pt]` (whose restriction at `t` is `n·1`), so `x - f ≫ zmap ι` has all
point restrictions `0`, hence is `0`.  Therefore
`φ = x ≫ P_proj = f ≫ zmap ι ≫ P_proj = f ≫ P_map ≫ P_proj = 0`. -/
theorem mono_cBounded_of_inputs
    (hpt : ∀ x : ↥((Work.ATOM.zfree (LightProfinite.NatUnionInfty)).obj.obj
          (Opposite.op Work.ATOM.pt)),
      (cBounded.hom.app (Opposite.op Work.ATOM.pt))
        ((LightCondensed.P_proj.hom.app (Opposite.op Work.ATOM.pt)) x) = 0 →
      ∃ n : ℤ, x = n • constInftyElem)
    (hdet : ∀ (S : LightProfinite.{0})
      (x : ↥((Work.ATOM.zfree (LightProfinite.NatUnionInfty)).obj.obj (Opposite.op S))),
      (∀ s : ↥S, (Work.ATOM.zfree (LightProfinite.NatUnionInfty)).obj.map (Work.ATOM.ptAt s).op x
        = 0) → x = 0) :
    CategoryTheory.Mono cBounded := by
  -- A morphism `ℤ[T] ⟶ P` killed by `cBounded` is zero.
  have key : ∀ (T : LightProfinite.{0}) (φ : Work.ATOM.zfree T ⟶ LightCondensed.P),
      φ ≫ cBounded = 0 → φ = 0 := by
    intro T φ hφ
    obtain ⟨s, hs⟩ : ∃ s : LightCondensed.P ⟶ Work.ATOM.zfree (LightProfinite.NatUnionInfty),
        s ≫ LightCondensed.P_proj = 𝟙 LightCondensed.P :=
      ⟨LightCondensed.PSequence_split.s, LightCondensed.PSequence_split.s_g⟩
    have hx : (φ ≫ s) ≫ LightCondensed.P_proj = φ := by
      rw [Category.assoc, hs, Category.comp_id]
    -- The restriction of `x` to every point is a multiple of `[const ∞]`.
    have hrest : ∀ t : ↥T, ∃ n : ℤ,
        (Work.ATOM.zfree (LightProfinite.NatUnionInfty)).obj.map (Work.ATOM.ptAt t).op
            (Work.ANALYTIC.freeHomEquiv T (Work.ATOM.zfree (LightProfinite.NatUnionInfty))
              (φ ≫ s)) = n • constInftyElem := by
      intro t
      have hy0 : (cBounded.hom.app (Opposite.op Work.ATOM.pt))
          ((LightCondensed.P_proj.hom.app (Opposite.op Work.ATOM.pt))
            ((Work.ATOM.zfree (LightProfinite.NatUnionInfty)).obj.map (Work.ATOM.ptAt t).op
              (Work.ANALYTIC.freeHomEquiv T (Work.ATOM.zfree (LightProfinite.NatUnionInfty))
                (φ ≫ s)))) = 0 := by
        -- rewrite the restriction as a section over `pt`
        rw [← freeHomEquiv_naturality (Work.ATOM.ptAt t)
          (Work.ATOM.zfree (LightProfinite.NatUnionInfty)) (φ ≫ s)]
        -- and evaluate `P_proj ≫ cBounded` there
        rw [show (ConcreteCategory.hom (cBounded.hom.app (Opposite.op Work.ATOM.pt)))
              ((ConcreteCategory.hom (LightCondensed.P_proj.hom.app (Opposite.op Work.ATOM.pt)))
                ((Work.ANALYTIC.freeHomEquiv Work.ATOM.pt
                  (Work.ATOM.zfree (LightProfinite.NatUnionInfty)))
                  (Work.ATOM.zmap (Work.ATOM.ptAt t) ≫ φ ≫ s)))
            = (ConcreteCategory.hom
                ((LightCondensed.P_proj ≫ cBounded).hom.app (Opposite.op Work.ATOM.pt)))
                ((Work.ANALYTIC.freeHomEquiv Work.ATOM.pt
                  (Work.ATOM.zfree (LightProfinite.NatUnionInfty)))
                  (Work.ATOM.zmap (Work.ATOM.ptAt t) ≫ φ ≫ s)) from rfl]
        rw [← freeHomEquiv_naturality_target Work.ATOM.pt (LightCondensed.P_proj ≫ cBounded)
          (Work.ATOM.zmap (Work.ATOM.ptAt t) ≫ φ ≫ s)]
        have hW : (Work.ATOM.zmap (Work.ATOM.ptAt t) ≫ φ ≫ s) ≫
            (LightCondensed.P_proj ≫ cBounded) = 0 := by
          rw [show (Work.ATOM.zmap (Work.ATOM.ptAt t) ≫ φ ≫ s) ≫
                (LightCondensed.P_proj ≫ cBounded) = Work.ATOM.zmap (Work.ATOM.ptAt t) ≫
                  ((φ ≫ s) ≫ (LightCondensed.P_proj ≫ cBounded)) by
            simp only [Category.assoc]]
          rw [show (φ ≫ s) ≫ (LightCondensed.P_proj ≫ cBounded) =
                ((φ ≫ s) ≫ LightCondensed.P_proj) ≫ cBounded from
              (Category.assoc _ _ _).symm, hx, hφ, comp_zero]
        rw [hW]
        exact freeHomEquiv_zero Work.ATOM.pt boundedSeq
      exact hpt _ hy0
    -- The correction `f = x ≫ zmap σ`.
    obtain ⟨f, hf⟩ : ∃ f : Work.ATOM.zfree T ⟶ Work.ATOM.zfree Work.ATOM.pt,
        f = (φ ≫ s) ≫ Work.ATOM.zmap sigmaMap := ⟨_, rfl⟩
    -- `f` has the same restriction at every point as `x` does
    have hdiff : ∀ t : ↥T,
        (Work.ATOM.zfree (LightProfinite.NatUnionInfty)).obj.map (Work.ATOM.ptAt t).op
          (Work.ANALYTIC.freeHomEquiv T (Work.ATOM.zfree (LightProfinite.NatUnionInfty))
            ((φ ≫ s) - (f ≫ Work.ATOM.zmap (LightCondensed.ι)))) = 0 := by
      intro t
      obtain ⟨n, hn⟩ := hrest t
      -- the restriction of `x` at `t`, as a morphism
      have hcomp : (Work.ATOM.zmap (Work.ATOM.ptAt t) ≫ (φ ≫ s)) =
          n • Work.ATOM.zmap (LightCondensed.ι) := by
        apply (Work.ANALYTIC.freeHomEquiv Work.ATOM.pt
          (Work.ATOM.zfree (LightProfinite.NatUnionInfty))).injective
        rw [freeHomEquiv_naturality, hn, freeHomEquiv_zsmul]
      -- the restriction of the correction at `t`
      have hfrest : (Work.ATOM.zfree (LightProfinite.NatUnionInfty)).obj.map
          (Work.ATOM.ptAt t).op
          (Work.ANALYTIC.freeHomEquiv T (Work.ATOM.zfree (LightProfinite.NatUnionInfty))
            (f ≫ Work.ATOM.zmap (LightCondensed.ι))) = n • constInftyElem := by
        rw [← freeHomEquiv_naturality (Work.ATOM.ptAt t)
          (Work.ATOM.zfree (LightProfinite.NatUnionInfty)) (f ≫ Work.ATOM.zmap (LightCondensed.ι))]
        calc (Work.ANALYTIC.freeHomEquiv Work.ATOM.pt
              (Work.ATOM.zfree (LightProfinite.NatUnionInfty)))
              (Work.ATOM.zmap (Work.ATOM.ptAt t) ≫ (f ≫ Work.ATOM.zmap (LightCondensed.ι)))
            = (Work.ANALYTIC.freeHomEquiv Work.ATOM.pt
                (Work.ATOM.zfree (LightProfinite.NatUnionInfty)))
                ((Work.ATOM.zmap (Work.ATOM.ptAt t) ≫ (φ ≫ s)) ≫
                  (Work.ATOM.zmap sigmaMap ≫ Work.ATOM.zmap (LightCondensed.ι))) := by
                rw [hf]
                simp only [Category.assoc]
          _ = (Work.ANALYTIC.freeHomEquiv Work.ATOM.pt
                (Work.ATOM.zfree (LightProfinite.NatUnionInfty)))
                ((n • Work.ATOM.zmap (LightCondensed.ι)) ≫
                  (Work.ATOM.zmap sigmaMap ≫ Work.ATOM.zmap (LightCondensed.ι))) := by rw [hcomp]
          _ = n • ((Work.ANALYTIC.freeHomEquiv Work.ATOM.pt
                (Work.ATOM.zfree (LightProfinite.NatUnionInfty)))
                (Work.ATOM.zmap (LightCondensed.ι) ≫
                  (Work.ATOM.zmap sigmaMap ≫ Work.ATOM.zmap (LightCondensed.ι)))) := by
                rw [Linear.smul_comp, freeHomEquiv_zsmul]
          _ = n • ((Work.ANALYTIC.freeHomEquiv Work.ATOM.pt
                (Work.ATOM.zfree (LightProfinite.NatUnionInfty)))
                (Work.ATOM.zmap (LightCondensed.ι))) := by
                rw [← Category.assoc, zmap_iota_sigma, Category.id_comp]
          _ = n • constInftyElem := rfl
      -- combine
      have hsub : (Work.ANALYTIC.freeHomEquiv T (Work.ATOM.zfree (LightProfinite.NatUnionInfty)))
            ((φ ≫ s) - (f ≫ Work.ATOM.zmap (LightCondensed.ι)))
          = (Work.ANALYTIC.freeHomEquiv T (Work.ATOM.zfree (LightProfinite.NatUnionInfty))
              (φ ≫ s)) -
            (Work.ANALYTIC.freeHomEquiv T (Work.ATOM.zfree (LightProfinite.NatUnionInfty))
              (f ≫ Work.ATOM.zmap (LightCondensed.ι))) :=
        map_sub (freeHomEquivAddHom T (Work.ATOM.zfree (LightProfinite.NatUnionInfty))) _ _
      rw [hsub, map_sub, hn, hfrest, sub_self]
    -- hence the difference vanishes
    have hzero : (φ ≫ s) - (f ≫ Work.ATOM.zmap (LightCondensed.ι)) = 0 :=
      (Work.ANALYTIC.freeHomEquiv T (Work.ATOM.zfree (LightProfinite.NatUnionInfty))).injective
        (hdet T _ hdiff)
    have hxeq : (φ ≫ s) = f ≫ Work.ATOM.zmap (LightCondensed.ι) := sub_eq_zero.mp hzero
    calc φ = (φ ≫ s) ≫ LightCondensed.P_proj := hx.symm
      _ = (f ≫ Work.ATOM.zmap (LightCondensed.ι)) ≫ LightCondensed.P_proj := by rw [hxeq]
      _ = f ≫ (Work.ATOM.zmap (LightCondensed.ι) ≫ LightCondensed.P_proj) := Category.assoc _ _ _
      _ = f ≫ (LightCondensed.P_map ≫ LightCondensed.P_proj) := rfl
      _ = f ≫ 0 := by
            rw [show LightCondensed.P_map ≫ LightCondensed.P_proj = 0 from
              LightCondensed.PSequence.zero]
      _ = 0 := comp_zero
  -- conclude that `cBounded` is a monomorphism
  apply CategoryTheory.Sheaf.mono_of_injective
  intro S
  intro z z' hz
  obtain ⟨u, hzu⟩ : ∃ u : Work.ATOM.zfree S.unop ⟶ LightCondensed.P,
      z = freeHomEquiv S.unop LightCondensed.P u :=
    ⟨_, (Equiv.apply_symm_apply (freeHomEquiv S.unop LightCondensed.P) z).symm⟩
  obtain ⟨v, hzv⟩ : ∃ v : Work.ATOM.zfree S.unop ⟶ LightCondensed.P,
      z' = freeHomEquiv S.unop LightCondensed.P v :=
    ⟨_, (Equiv.apply_symm_apply (freeHomEquiv S.unop LightCondensed.P) z').symm⟩
  have huv : u = v := by
    have h2 : u ≫ cBounded = v ≫ cBounded := by
      apply (freeHomEquiv S.unop boundedSeq).injective
      rw [freeHomEquiv_naturality_target S.unop cBounded u,
        freeHomEquiv_naturality_target S.unop cBounded v]
      rw [hzu, hzv] at hz
      exact hz
    have h3 : (u - v) ≫ cBounded = 0 := by rw [Preadditive.sub_comp, h2, sub_self]
    exact sub_eq_zero.mp (key S.unop (u - v) h3)
  rw [hzu, hzv, huv]

end

/-- **`cBounded` is a monomorphism.**  The map `c : P ⟶ ∏^bnd ℤ`, `e_n ↦ δ_n`, is componentwise
injective; this makes the lift of a map `h : P ⊗ ℤ[S] ⟶ ∏^bnd ℤ` along `c` (when it exists, i.e.
when `h ≫ cokernel.π c = 0`) *unique*, hence canonical, which is what makes the `S`-point data
of the morphism `G` of `Work.ANALYTIC.exists_unprimedTower` natural in `S` and additive in `x`.

NOTE TO THE PROVER: two reviews disagreed about this statement.  A proposed counterexample on
`T = 𝟙 ⊔ 𝟙` with `z = [g₀₁] + [g₁₀] - [g₀₀] - [g₁₁] ∈ P(T)` (whose `cBounded(T)`-image is `0`)
appears to collapse to `z = 0` as well, because the sheaf condition gives
`M(T₁ ⊔ T₂) ≅ M(T₁) × M(T₂)` and both restrictions of `z` (along `ptAt s₁`, `ptAt s₂`) are
`[const 0] + [const 1] - [const 0] - [const 1] = 0` in `ℤ[ℕ∪∞](𝟙)`.  So the counterexample as
stated does not settle it; a *negative* outcome requires a genuine nonzero element of `P(S)` in
the kernel of `cBounded(S)` (a precise write-up, using `declare_false`, is a fully acceptable and
valuable outcome here).  Natural route for the positive answer: a morphism of sheaves of modules
is a mono iff all its components are injective; `cBounded(S)` is the quotient of the free map
`zmap g ↦ (m ↦ 1_{g⁻¹(m)})` by `ℤ·[const ∞]`, whose kernel is exactly `P_map`'s image
(`P_proj_cBounded`, `PSequence_exact`), so `ker cBounded(S) = 0`. -/
theorem mono_cBounded : CategoryTheory.Mono Work.ANALYTIC.cBounded := by
  apply mono_cBounded_of_inputs
  · intro x hx
    obtain ⟨n, hn⟩ := pt_kernel_cBounded x hx
    exact ⟨n, by rw [hn, constInftyElem_atom]⟩
  · exact points_detect_zfree_NatUnionInfty

end Work.ANALYTIC
