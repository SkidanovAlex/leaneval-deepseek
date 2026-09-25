import Mathlib
import Submission.Work.WingbergRoute.CupProduct

/-!
# `Work.WingbergRoute.cup_isLocallyConstant`

The cup-product formulas of `Submission/Work/WingbergRoute/CupProduct.lean` are
built from the inhomogeneous formulas

```
cup01Fun f a₀ b σ      = f a₀ (b σ)
cup11Fun f a b (σ,τ)   = f (a σ) (σ • b τ)
cup21Fun f α b (σ,τ,ρ) = f (α (σ,τ)) ((στ) • b ρ)
cup12Fun f a β (σ,τ,ρ) = f (a σ) (σ • β (τ,ρ))
cup10Fun f a b₀ σ      = f (a σ) (σ • b₀)
cup31Fun f β b (σ,τ,ρ,υ) = f (β (σ,τ,ρ)) ((στρ) • b υ)
cup22Fun f α β (σ,τ,ρ,υ) = f (α (σ,τ)) ((στ) • β (ρ,υ))
cup13Fun f a δ (σ,τ,ρ,υ) = f (a σ) (σ • δ (τ,ρ,υ))
```

This file proves that each of them is **locally constant** whenever the cochains fed into it are
(the coefficients being discrete `G`-modules and the pairing `f` being additive in each
variable).  Consequently each formula defines a genuine cochain in the sense of
`Work.ConCohomology.Cochain1/2/3`, which is what `Work.WingbergRoute.cup_leibniz` and
`Work.WingbergRoute.cup_wellDefined` need in order to speak about the cup product on cohomology.

The only two ingredients are

* `lc_pair`, that a pair of locally constant maps into two arbitrary types is locally constant, and
* `Work.ConCohomology.isLocallyConstant_smul_comp`, that `x ↦ s x • φ x` is locally constant for
  `φ` locally constant and `s` continuous.
-/

namespace Work.WingbergRoute

open Work.ConCohomology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The pointwise pairing of a tuple of two locally constant maps is locally constant. -/
private lemma lc_pair {X : Type*} [TopologicalSpace X] {Y Z : Type*} {f : X → Y} {g : X → Z}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
    IsLocallyConstant fun x => (f x, g x) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨U, hU, hxU, hUc⟩ := hf.exists_open x
  obtain ⟨V, hV, hxV, hVc⟩ := hg.exists_open x
  exact ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, fun y hy => by rw [hUc y hy.1, hVc y hy.2]⟩

/-- A pairing `f : A →+ B →+ C` applied to two locally constant functions is locally
constant. -/
private lemma lc_bilin {X : Type*} [TopologicalSpace X] {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B →+ C) {u : X → A} {v : X → B}
    (hu : IsLocallyConstant u) (hv : IsLocallyConstant v) :
    IsLocallyConstant fun x => f (u x) (v x) :=
  (lc_pair hu hv).comp fun q : A × B => f q.1 q.2

theorem cup_isLocallyConstant {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type*} [AddCommGroup A] [DistribMulAction G A] [Work.ConCohomology.IsDiscreteGModule G A]
    {B : Type*} [AddCommGroup B] [DistribMulAction G B] [Work.ConCohomology.IsDiscreteGModule G B]
    {C : Type*} [AddCommGroup C] [DistribMulAction G C] [Work.ConCohomology.IsDiscreteGModule G C]
    (f : A →+ B →+ C) :
    (∀ (a₀ : A) (b : Work.ConCohomology.Cochain1 G B),
        IsLocallyConstant (Work.WingbergRoute.cup01Fun f a₀ (b : G → B))) ∧
      (∀ (a : Work.ConCohomology.Cochain1 G A) (b : Work.ConCohomology.Cochain1 G B),
        IsLocallyConstant (Work.WingbergRoute.cup11Fun f (a : G → A) (b : G → B))) ∧
      (∀ (α : Work.ConCohomology.Cochain2 G A) (b : Work.ConCohomology.Cochain1 G B),
        IsLocallyConstant (Work.WingbergRoute.cup21Fun f (α : G × G → A) (b : G → B))) ∧
      (∀ (a : Work.ConCohomology.Cochain1 G A) (β : Work.ConCohomology.Cochain2 G B),
        IsLocallyConstant (Work.WingbergRoute.cup12Fun f (a : G → A) (β : G × G → B))) ∧
      (∀ (a : Work.ConCohomology.Cochain1 G A) (b₀ : B),
        IsLocallyConstant (Work.WingbergRoute.cup10Fun f (a : G → A) b₀)) ∧
      (∀ (β : Work.ConCohomology.Cochain3 G A) (b : Work.ConCohomology.Cochain1 G B),
        IsLocallyConstant (Work.WingbergRoute.cup31Fun f (β : G × G × G → A) (b : G → B))) ∧
      (∀ (α : Work.ConCohomology.Cochain2 G A) (β : Work.ConCohomology.Cochain2 G B),
        IsLocallyConstant (Work.WingbergRoute.cup22Fun f (α : G × G → A) (β : G × G → B))) ∧
      (∀ (a : Work.ConCohomology.Cochain1 G A) (δ : Work.ConCohomology.Cochain3 G B),
        IsLocallyConstant (Work.WingbergRoute.cup13Fun f (a : G → A) (δ : G × G × G → B))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a₀ b
    change IsLocallyConstant (fun σ : G => f a₀ (b σ))
    exact lc_bilin f (IsLocallyConstant.const a₀) b.isLocallyConstant
  · intro a b
    change IsLocallyConstant (fun p : G × G => f (a p.1) (p.1 • b p.2))
    exact lc_bilin f (a.isLocallyConstant.comp_continuous continuous_fst)
      (Work.ConCohomology.isLocallyConstant_smul_comp (φ := fun p : G × G => b p.2)
        (b.isLocallyConstant.comp_continuous continuous_snd) continuous_fst)
  · intro α b
    change IsLocallyConstant
      (fun p : G × G × G => f (α (p.1, p.2.1)) ((p.1 * p.2.1) • b p.2.2))
    exact lc_bilin f
      (α.isLocallyConstant.comp_continuous
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
      (Work.ConCohomology.isLocallyConstant_smul_comp (φ := fun p : G × G × G => b p.2.2)
        (b.isLocallyConstant.comp_continuous (continuous_snd.comp continuous_snd))
        (continuous_fst.mul (continuous_fst.comp continuous_snd)))
  · intro a β
    change IsLocallyConstant
      (fun p : G × G × G => f (a p.1) (p.1 • β (p.2.1, p.2.2)))
    exact lc_bilin f (a.isLocallyConstant.comp_continuous continuous_fst)
      (Work.ConCohomology.isLocallyConstant_smul_comp (φ := fun p : G × G × G => β (p.2.1, p.2.2))
        (β.isLocallyConstant.comp_continuous
          ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd)))
        continuous_fst)
  · intro a b₀
    change IsLocallyConstant (fun σ : G => f (a σ) (σ • b₀))
    exact lc_bilin f a.isLocallyConstant
      (Work.ConCohomology.IsDiscreteGModule.isLocallyConstant_smul (G := G) b₀)
  · intro β b
    change IsLocallyConstant
      (fun p : G × G × G × G =>
        f (β (p.1, p.2.1, p.2.2.1)) ((p.1 * p.2.1 * p.2.2.1) • b p.2.2.2))
    exact lc_bilin f
      (β.isLocallyConstant.comp_continuous
        (continuous_fst.prodMk
          ((continuous_fst.comp continuous_snd).prodMk
            ((continuous_fst.comp continuous_snd).comp continuous_snd))))
      (Work.ConCohomology.isLocallyConstant_smul_comp (φ := fun p : G × G × G × G => b p.2.2.2)
        (b.isLocallyConstant.comp_continuous
          (continuous_snd.comp (continuous_snd.comp continuous_snd)))
        ((continuous_fst.mul (continuous_fst.comp continuous_snd)).mul
          ((continuous_fst.comp continuous_snd).comp continuous_snd)))
  · intro α β
    change IsLocallyConstant
      (fun p : G × G × G × G =>
        f (α (p.1, p.2.1)) ((p.1 * p.2.1) • β (p.2.2.1, p.2.2.2)))
    exact lc_bilin f
      (α.isLocallyConstant.comp_continuous
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
      (Work.ConCohomology.isLocallyConstant_smul_comp
        (φ := fun p : G × G × G × G => β (p.2.2.1, p.2.2.2))
        (β.isLocallyConstant.comp_continuous
          (((continuous_fst.comp continuous_snd).comp continuous_snd).prodMk
            (continuous_snd.comp (continuous_snd.comp continuous_snd))))
        (continuous_fst.mul (continuous_fst.comp continuous_snd)))
  · intro a δ
    change IsLocallyConstant
      (fun p : G × G × G × G => f (a p.1) (p.1 • δ (p.2.1, p.2.2.1, p.2.2.2)))
    exact lc_bilin f (a.isLocallyConstant.comp_continuous continuous_fst)
      (Work.ConCohomology.isLocallyConstant_smul_comp
        (φ := fun p : G × G × G × G => δ (p.2.1, p.2.2.1, p.2.2.2))
        (δ.isLocallyConstant.comp_continuous
          ((continuous_fst.comp continuous_snd).prodMk
            (((continuous_fst.comp continuous_snd).comp continuous_snd).prodMk
              (continuous_snd.comp (continuous_snd.comp continuous_snd)))))
        continuous_fst)

end Work.WingbergRoute
