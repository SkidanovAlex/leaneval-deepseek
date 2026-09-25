import Mathlib
import Submission.Work.WingbergRoute.CupProduct

/-!
# `Work.WingbergRoute.cup_wellDefined` -- the cup product is well defined on cohomology

`Submission/Work/WingbergRoute/CupProduct.lean` defines the inhomogeneous cup product of
continuous cochains (`cup11Fun`, `cup21Fun`, ...) and `Submission/Work/WingbergRoute/cup_leibniz`
records the Leibniz rule `d(a ∪ b) = da ∪ b ± a ∪ db`.  This module draws the consequences that
make the cup product *descend* to cohomology, in exactly the five shapes consumed downstream:

1. `d⁰a₀ ∪ b` is a coboundary for every `1`-cocycle `b`  (`κ = f a₀ ∘ b`);
2. `a ∪ d⁰b₀ = -d¹κ` for every `1`-cocycle `a`  (`κ σ = f (a σ) (σ • b₀)`);
3. `z ∪ b` is a *cocycle* (`d³ = 0`) for a `2`-cocycle `z` and a `1`-cocycle `b`;
4. `d¹γ ∪ b` is a coboundary for every `1`-cochain `γ` and every `1`-cocycle `b`
   (`κ = cup11Fun f γ b`);
5. `z ∪ d⁰b₀` is a coboundary for every `2`-cocycle `z`  (`κ (σ,τ) = f (z σ τ) ((στ) • b₀)`).

Every identity is proved by an explicit pointwise computation: the `IsEquivariantBilin` hypothesis
of `f` converts the `G`-action on `C` into the action on the arguments of `f`, after which the
`1`-cocycle condition (`IsCocycle1`) and the `2`-cocycle condition (`IsCocycle2`) collapse the
expression to the required coboundary (respectively to zero).

The two elementary bilinear bookkeeping lemmas used in these computations are
`bilin_sub_add_sub` (`f X V - f Y V + f Z V - f W V = f (X - Y + Z - W) V`) and `bilin_sub_add`.

## Main declaration

* `Work.WingbergRoute.cup_wellDefined`
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

open scoped Classical

noncomputable section

namespace Work.WingbergRoute

open Work.ConCohomology Work.ShafarevichKoch

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A] [IsDiscreteGModule G A]
variable {B : Type*} [AddCommGroup B] [DistribMulAction G B] [IsDiscreteGModule G B]
variable {C : Type*} [AddCommGroup C] [DistribMulAction G C] [IsDiscreteGModule G C]

/-! ## Elementary lemmas -/

/-- The `1`-cocycle condition for an element of `Z¹(G,B)`, in the crossed-homomorphism form
`b (σ τ) = b σ + σ • b τ`. -/
private lemma z1_isCocycle1 (b : Z1 G B) : IsCocycle1 (b : G → B) := by
  have h : d1Fun (b : G → B) = 0 := by
    rw [← (d1Hom_eq_zero_iff (b : Cochain1 G B))]
    exact b.2
  exact (isCocycle1_iff_d1Fun _).mpr h

/-- The `2`-cocycle condition for an element of `Z²(G,A)`, in the factor-system form
`σ • z (τ,ρ) - z (σ τ, ρ) + z (σ, τρ) - z (σ,τ) = 0`. -/
private lemma z2_isCocycle2 (z : Z2 G A) : IsCocycle2 (z : G × G → A) := by
  have h : d2Fun (z : G × G → A) = 0 := by
    rw [← (d2Hom_eq_zero_iff (z : Cochain2 G A))]
    exact z.2
  exact (isCocycle2_iff_d2Fun _).mpr h

/-- Pointwise application of an additive pairing to two locally constant maps is locally constant. -/
private lemma isLocallyConstant_bilin (f : A →+ B →+ C) {X : Type*} [TopologicalSpace X]
    {φ : X → A} {ψ : X → B} (hφ : IsLocallyConstant φ) (hψ : IsLocallyConstant ψ) :
    IsLocallyConstant fun x => f (φ x) (ψ x) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨U, hU, hxU, hUc⟩ := hφ.exists_open x
  obtain ⟨V, hV, hxV, hVc⟩ := hψ.exists_open x
  exact ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, fun y hy => by rw [hUc y hy.1, hVc y hy.2]⟩

/-- Additivity of `f` in the first variable, in the shape `f (X - Y + Z - W) V`. -/
private lemma bilin_sub_add_sub (f : A →+ B →+ C) (X Y Z W : A) (V : B) :
    f X V - f Y V + f Z V - f W V = f (X - Y + Z - W) V := by
  simp only [map_sub, map_add, AddMonoidHom.sub_apply, AddMonoidHom.add_apply]

/-- Additivity of `f` in the first variable, in the shape `f (X - Y + Z) V`. -/
private lemma bilin_sub_add (f : A →+ B →+ C) (X Y Z : A) (V : B) :
    f X V - f Y V + f Z V = f (X - Y + Z) V := by
  simp only [map_sub, map_add, AddMonoidHom.sub_apply, AddMonoidHom.add_apply]

/-- Cancellation of the `U`-terms in a sum of the shape `P - Q + (U + Z) - U`. -/
private lemma bilin_cancel (P Q U Z : C) : (P - Q + (U + Z)) - U = P - Q + Z := by abel

/-- Cancellation of the `U`-terms in a sum of the shape `A - B + C - (U + V) + U`. -/
private lemma bilin_four_eq (A' B' C' U' V' : C) :
    A' - B' + C' - (U' + V') + U' = A' - B' + C' - V' := by abel

/-! ## The descent of the cup product to cohomology -/

theorem cup_wellDefined {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type*} [AddCommGroup A] [DistribMulAction G A] [Work.ConCohomology.IsDiscreteGModule G A]
    {B : Type*} [AddCommGroup B] [DistribMulAction G B] [Work.ConCohomology.IsDiscreteGModule G B]
    {C : Type*} [AddCommGroup C] [DistribMulAction G C] [Work.ConCohomology.IsDiscreteGModule G C]
    (f : A →+ B →+ C) (hf : Work.WingbergRoute.IsEquivariantBilin (G := G) f) :
    (∀ (a₀ : A) (b : Work.ConCohomology.Z1 G B), ∃ κ : Work.ConCohomology.Cochain1 G C,
        Work.WingbergRoute.cup11Fun f (Work.ConCohomology.d0Fun (M := A) a₀) (b : G → B)
          = Work.ConCohomology.d1Fun (M := C) (κ : G → C)) ∧
      (∀ (a : Work.ConCohomology.Z1 G A) (b₀ : B), ∃ κ : Work.ConCohomology.Cochain1 G C,
        Work.WingbergRoute.cup11Fun f (a : G → A) (Work.ConCohomology.d0Fun (M := B) b₀)
          = -Work.ConCohomology.d1Fun (M := C) (κ : G → C)) ∧
      (∀ (z : Work.ConCohomology.Z2 G A) (b : Work.ConCohomology.Z1 G B),
        Work.ShafarevichKoch.d3Fun (Work.WingbergRoute.cup21Fun f (z : G × G → A) (b : G → B))
          = 0) ∧
      (∀ (γ : Work.ConCohomology.Cochain1 G A) (b : Work.ConCohomology.Z1 G B),
        ∃ κ : Work.ConCohomology.Cochain2 G C,
        Work.WingbergRoute.cup21Fun f (Work.ConCohomology.d1Fun (M := A) (γ : G → A)) (b : G → B)
          = Work.ConCohomology.d2Fun (M := C) (κ : G × G → C)) ∧
      (∀ (z : Work.ConCohomology.Z2 G A) (b₀ : B), ∃ κ : Work.ConCohomology.Cochain2 G C,
        Work.WingbergRoute.cup21Fun f (z : G × G → A) (Work.ConCohomology.d0Fun (M := B) b₀)
          = Work.ConCohomology.d2Fun (M := C) (κ : G × G → C)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1) `d⁰a₀ ∪ b = d¹(f a₀ ∘ b)` for `b` a `1`-cocycle.
    intro a₀ b
    have hb : IsCocycle1 (b : G → B) := z1_isCocycle1 b
    refine ⟨⟨fun σ => f a₀ ((b : G → B) σ), ?_⟩, ?_⟩
    · exact (b.1.isLocallyConstant).comp (f a₀)
    · funext p
      obtain ⟨σ, τ⟩ := p
      have h1 : f (σ • a₀ - a₀) (σ • (b : G → B) τ)
          = f (σ • a₀) (σ • (b : G → B) τ) - f a₀ (σ • (b : G → B) τ) := by
        rw [map_sub]
        rfl
      have h2 : σ • (b : G → B) τ = (b : G → B) (σ * τ) - (b : G → B) σ := by
        rw [hb σ τ]
        abel
      simp only [Work.WingbergRoute.cup11Fun, Work.ConCohomology.d0Fun_apply,
        Work.ConCohomology.d1Fun_apply]
      rw [h1, hf σ a₀ ((b : G → B) τ), h2, map_sub]
      abel
  · -- (2) `a ∪ d⁰b₀ = -d¹κ` for `a` a `1`-cocycle, with `κ σ = f (a σ) (σ • b₀)`.
    intro a b₀
    have ha : IsCocycle1 (a : G → A) := by
      have h : d1Fun (a : G → A) = 0 := by
        rw [← (d1Hom_eq_zero_iff (a : Cochain1 G A))]
        exact a.2
      exact (isCocycle1_iff_d1Fun _).mpr h
    refine ⟨⟨fun σ => f ((a : G → A) σ) (σ • b₀), ?_⟩, ?_⟩
    · exact isLocallyConstant_bilin f a.1.isLocallyConstant
        (IsDiscreteGModule.isLocallyConstant_smul (G := G) b₀)
    · funext p
      obtain ⟨σ, τ⟩ := p
      have haeq : (a : G → A) (σ * τ) = (a : G → A) σ + σ • (a : G → A) τ := ha σ τ
      simp only [Work.WingbergRoute.cup11Fun, Work.ConCohomology.d0Fun_apply,
        Work.ConCohomology.d1Fun_apply, Pi.neg_apply, LocallyConstant.coe_mk]
      rw [smul_sub, ← mul_smul σ τ b₀, ← hf σ ((a : G → A) τ) (τ • b₀),
        ← mul_smul σ τ b₀, haeq]
      simp only [map_add, AddMonoidHom.add_apply, map_sub]
      abel
  · -- (3) `z ∪ b` is a cocycle for `z` a `2`-cocycle and `b` a `1`-cocycle.
    intro z b
    have hz : IsCocycle2 (z : G × G → A) := z2_isCocycle2 z
    have hb : IsCocycle1 (b : G → B) := z1_isCocycle1 b
    funext p
    obtain ⟨σ, τ, ρ, υ⟩ := p
    simp only [Work.WingbergRoute.cup21Fun, Work.ShafarevichKoch.d3Fun_apply, Pi.zero_apply]
    rw [← hf σ ((z : G × G → A) (τ, ρ)) ((τ * ρ) • (b : G → B) υ)]
    rw [← mul_smul σ (τ * ρ) ((b : G → B) υ)]
    rw [← mul_assoc σ τ ρ]
    rw [hb ρ υ]
    rw [smul_add]
    rw [← mul_smul (σ * τ) ρ ((b : G → B) υ)]
    rw [map_add]
    rw [bilin_four_eq]
    rw [bilin_sub_add_sub f (σ • (z : G × G → A) (τ, ρ)) ((z : G × G → A) (σ * τ, ρ))
      ((z : G × G → A) (σ, τ * ρ)) ((z : G × G → A) (σ, τ))
      (((σ * τ) * ρ) • (b : G → B) υ)]
    rw [hz σ τ ρ]
    simp
  · -- (4) `d¹γ ∪ b = d²(cup11Fun f γ b)` for `b` a `1`-cocycle.
    intro γ b
    have hb : IsCocycle1 (b : G → B) := z1_isCocycle1 b
    refine ⟨⟨fun p : G × G => f ((γ : G → A) p.1) (p.1 • (b : G → B) p.2), ?_⟩, ?_⟩
    · exact isLocallyConstant_bilin f ((γ.isLocallyConstant).comp_continuous continuous_fst)
        (isLocallyConstant_smul_comp (φ := fun p : G × G => (b : G → B) p.2)
          ((b.1.isLocallyConstant).comp_continuous continuous_snd) continuous_fst)
    · funext p
      obtain ⟨σ, τ, ρ⟩ := p
      simp only [Work.WingbergRoute.cup21Fun, Work.ConCohomology.d1Fun_apply,
        Work.ConCohomology.d2Fun_apply, LocallyConstant.coe_mk]
      conv_rhs => rw [← hf σ ((γ : G → A) τ) (τ • (b : G → B) ρ)]
      conv_rhs => rw [← mul_smul σ τ ((b : G → B) ρ)]
      conv_rhs => rw [hb τ ρ]
      conv_rhs => rw [smul_add]
      conv_rhs => rw [← mul_smul σ τ ((b : G → B) ρ)]
      conv_rhs => rw [map_add]
      rw [bilin_cancel]
      rw [bilin_sub_add f (σ • (γ : G → A) τ) ((γ : G → A) (σ * τ)) ((γ : G → A) σ)
        ((σ * τ) • (b : G → B) ρ)]
  · -- (5) `z ∪ d⁰b₀ = d²κ` for `z` a `2`-cocycle, with `κ (σ,τ) = f (z σ τ) ((στ) • b₀)`.
    intro z b₀
    have hz : IsCocycle2 (z : G × G → A) := z2_isCocycle2 z
    refine ⟨⟨fun p : G × G => f ((z : G × G → A) p) ((p.1 * p.2) • b₀), ?_⟩, ?_⟩
    · exact isLocallyConstant_bilin f z.1.isLocallyConstant
        (isLocallyConstant_smul_comp (IsLocallyConstant.const (X := G × G) b₀)
          (continuous_fst.mul continuous_snd))
    · funext p
      obtain ⟨σ, τ, ρ⟩ := p
      have hzrel : σ • (z : G × G → A) (τ, ρ) - (z : G × G → A) (σ * τ, ρ)
          + (z : G × G → A) (σ, τ * ρ) = (z : G × G → A) (σ, τ) := by
        have h := hz σ τ ρ
        rw [sub_eq_zero] at h
        exact h
      simp only [Work.WingbergRoute.cup21Fun, Work.ConCohomology.d0Fun_apply,
        Work.ConCohomology.d2Fun_apply, LocallyConstant.coe_mk]
      rw [smul_sub, ← mul_smul (σ * τ) ρ b₀]
      rw [← hf σ ((z : G × G → A) (τ, ρ)) ((τ * ρ) • b₀), ← mul_smul σ (τ * ρ) b₀,
        ← mul_assoc σ τ ρ]
      rw [map_sub]
      rw [bilin_sub_add f (σ • (z : G × G → A) (τ, ρ)) ((z : G × G → A) (σ * τ, ρ))
        ((z : G × G → A) (σ, τ * ρ)) (((σ * τ) * ρ) • b₀)]
      rw [hzrel]

end Work.WingbergRoute
