import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSEQP.EqpCechSetup

namespace Work.DSEQP

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option linter.style.haveILetI false

/-- The scalar action on a section of the Čech presheaf `cechPresheaf A X f` over the open `W`
is multiplication by the image of the scalar under `DSMap.phiU`. -/
lemma cechPresheaf_smul (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    (W : X.Opens) (a : A) (x : (DSMap.cechPresheaf A X f).obj (Opposite.op W)) :
    a • x = (DSMap.phiU A X f W) a * (show Γ(X, W) from x) := rfl

/-- The map of the Čech presheaf `cechPresheaf A X f` on the structure sheaf is the restriction
map of the structure sheaf. -/
lemma cechPresheaf_map_apply (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {V W : X.Opens} (h : V ≤ W) (x : (DSMap.cechPresheaf A X f).obj (Opposite.op W)) :
    ((DSMap.cechPresheaf A X f).map (homOfLE h).op).hom x
      = (X.presheaf.map (homOfLE h).op).hom x := rfl

/-- Componentwise localization of the structure sheaf at `X_g` over an affine open `W`.

`Work.DSEQP.Xg A X f g` is the open `f ⁻¹ᵁ D(g)` of `X`.  The statement says that the restriction
`Γ(X, W) → Γ(X, W ⊓ X_g)` is the localization of the `A`-module `Γ(X, W)` at `g`: every section of
`W ⊓ X_g` is, up to multiplication by a power of `g`, a restriction of a section of `W`, and a
section of `W` whose restriction vanishes is killed by a power of `g`.

Suggested route: `Work.DSEQP.Xg_eq_basicOpen` gives `Xg A X f g = X.basicOpen (DSMap.phi A X f g)`;
`Scheme.basicOpen_res` gives
`W ⊓ X.basicOpen (DSMap.phi A X f g) = X.basicOpen (DSMap.phiU A X f W g)`; then Mathlib's
`IsAffineOpen.isLocalization_basicOpen` (or `IsAffineOpen.isLocalization_of_eq_basicOpen`) says that
`Γ(X, X.basicOpen (phiU A X f W g))` is `Localization.Away (phiU A X f W g)` over `Γ(X, W)`.
Translate `IsLocalization.surj` and the kernel statement into the `g ^ k •` form, using that
`g ^ k • z = (phiU A X f W' g) ^ k * z` on `W' = W ⊓ X_g` and the naturality of `algebraMap`
(`DSMap.phiU_res`).  The analogue in the affine case `X = Spec R`, `X_g = D(g)` is
`Work.DSF1.Cech.specPresheaf_loc_affine` (see `Submission/Work/DSF1/Cech/specPresheaf_loc_affine.lean`),
whose proof can be copied almost verbatim. -/
theorem eqp_cech_affine_loc (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (W : X.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) (g : A) :
    (∀ z : (DSMap.cechPresheaf A X f).obj (Opposite.op (W ⊓ Work.DSEQP.Xg A X f g)),
      ∃ (k : ℕ) (t : (DSMap.cechPresheaf A X f).obj (Opposite.op W)),
        ((DSMap.cechPresheaf A X f).map
          (CategoryTheory.homOfLE (inf_le_left : W ⊓ Work.DSEQP.Xg A X f g ≤ W)).op).hom t = g ^ k • z) ∧
    (∀ t : (DSMap.cechPresheaf A X f).obj (Opposite.op W),
      ((DSMap.cechPresheaf A X f).map
        (CategoryTheory.homOfLE (inf_le_left : W ⊓ Work.DSEQP.Xg A X f g ≤ W)).op).hom t = 0 →
      ∃ k : ℕ, g ^ k • t = 0) := by
  -- The two halves are proved separately, both from the localization statement
  -- `IsLocalization.Away (phiU A X f W g) Γ(X, W ⊓ X_g)` over `Γ(X, W)`.
  have hle : W ⊓ Xg A X f g ≤ W := inf_le_left
  constructor
  · -- Every section over `W ⊓ X_g` is `g ^ k`-times a restriction from `W`.
    intro z
    have he : W ⊓ Xg A X f g = X.basicOpen (DSMap.phiU A X f W g) :=
      inf_Xg_eq_basicOpen_phiU f g W
    letI : Algebra Γ(X,W) ↑Γ(X, W ⊓ Xg A X f g) :=
      (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    have hloc : IsLocalization.Away (DSMap.phiU A X f W g) ↑Γ(X, W ⊓ Xg A X f g) :=
      hW.isLocalization_of_eq_basicOpen (DSMap.phiU A X f W g) (homOfLE hle) he
    haveI := hloc
    obtain ⟨⟨t, m⟩, hx⟩ := IsLocalization.surj (Submonoid.powers (DSMap.phiU A X f W g))
      (show Γ(X, W ⊓ Xg A X f g) from z)
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (m : Γ(X,W)) (DSMap.phiU A X f W g)).mp m.2
    refine ⟨n, t, ?_⟩
    have hx' : (X.presheaf.map (homOfLE hle).op).hom t
        = (show Γ(X, W ⊓ Xg A X f g) from z)
          * (X.presheaf.map (homOfLE hle).op).hom (m : Γ(X,W)) := hx.symm
    change (X.presheaf.map (homOfLE hle).op).hom t = g ^ n • z
    rw [hx', ← hn, map_pow, DSMap.phiU_res]
    rw [show g ^ n • (z : (DSMap.cechPresheaf A X f).obj (Opposite.op (W ⊓ Xg A X f g)))
        = (DSMap.phiU A X f (W ⊓ Xg A X f g)) (g ^ n)
            * (show Γ(X, W ⊓ Xg A X f g) from z) from rfl]
    rw [map_pow]
    ring
  · -- A section of `W` killed by the restriction to `W ⊓ X_g` is killed by a power of `g`.
    intro t ht
    have he : W ⊓ Xg A X f g = X.basicOpen (DSMap.phiU A X f W g) :=
      inf_Xg_eq_basicOpen_phiU f g W
    letI : Algebra Γ(X,W) ↑Γ(X, W ⊓ Xg A X f g) :=
      (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    have hloc : IsLocalization.Away (DSMap.phiU A X f W g) ↑Γ(X, W ⊓ Xg A X f g) :=
      hW.isLocalization_of_eq_basicOpen (DSMap.phiU A X f W g) (homOfLE hle) he
    haveI := hloc
    have h : (algebraMap Γ(X,W) ↑Γ(X, W ⊓ Xg A X f g)) (t : Γ(X,W))
        = (algebraMap Γ(X,W) ↑Γ(X, W ⊓ Xg A X f g)) (0 : Γ(X,W)) := by
      rw [map_zero]; exact ht
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq
      (M := Submonoid.powers (DSMap.phiU A X f W g)) h
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (c : Γ(X,W)) (DSMap.phiU A X f W g)).mp c.2
    have hc0 : (c : Γ(X,W)) * (show Γ(X,W) from t) = 0 := by rw [hc, mul_zero]
    refine ⟨n, ?_⟩
    have key : g ^ n • (t : (DSMap.cechPresheaf A X f).obj (Opposite.op W))
        = (DSMap.phiU A X f W g) ^ n * (show Γ(X,W) from t) := by
      rw [cechPresheaf_smul, map_pow]
    rw [key, hn]
    exact hc0

end Work.DSEQP
