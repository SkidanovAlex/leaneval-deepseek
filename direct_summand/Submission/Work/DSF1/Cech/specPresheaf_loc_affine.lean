import Mathlib
import Submission.Work.DSF1.Cech.CechDefs
import Submission.Work.DSF1.Cech.basicOpen_localization_facts
import Submission.Work.DSF1.Cech.coaug0_injective
import Submission.Work.DSF1.Cech.away_away_surj_ker

namespace Work.DSF1.Cech

universe u

open CategoryTheory AlgebraicGeometry Opposite Limits

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-!
# Localization of sections over an affine open of `Spec R`

Let `R` be a commutative ring, `X = Spec R`, `W ⊆ X` an affine open and `g : R`.
This file proves that the restriction of the structure sheaf
`Γ(X, W ⊓ D(g))` is obtained from `Γ(X, W)` by inverting (the image of) `g`:
every section on `W ⊓ D(g)` becomes, after multiplying by a power of `g`, the
restriction of a section on `W`, and a section on `W` killed by the restriction
is killed by a power of `g`.

The proof realizes `Γ(X, W ⊓ D(g))` as the localization `Γ(X,W)[1/f]` where
`f = algebraMap R Γ(X,W) g` is the image of `g`, using Mathlib's
`IsAffineOpen.isLocalization_of_eq_basicOpen`, and then translates the
localization statements into the `g`-power statements via the fact that
`𝒪(Spec R, -)` is an `R`-algebra with `algebraMap R Γ(X,W) g` restricting to
`algebraMap R Γ(X, W ⊓ D(g)) g`.
-/

/-- The image of `g` in the sections of a basic open, expressed through the
structure map `R → Γ(Spec R, ⊤)`. -/
lemma algebraMap_secRing_res_le_top (R : Type u) [CommRing R] (W : (spec R).Opens) (a : R) :
    algebraMap R ↑(secRing R W) a =
      resSection R (le_top : W ≤ ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) :=
  (resSection_le_top_GammaSpecIso_inv R W a).symm

/-- Restriction maps of the structure sheaf compose. -/
lemma resSection_comp_aux {R : Type u} [CommRing R] {U V W : (spec R).Opens}
    (h1 : V ≤ W) (h2 : W ≤ U) (x : ↑(secRing R U)) :
    resSection R h1 (resSection R h2 x) = resSection R (le_trans h1 h2) x := by
  simp only [resSection]
  have hop : (homOfLE (le_trans h1 h2) : V ⟶ U).op = (homOfLE h2).op ≫ (homOfLE h1).op :=
    Subsingleton.elim _ _
  rw [hop, Functor.map_comp]
  rfl

/-- `W ⊓ D(g)` is the basic open of the image of `g` in `Γ(Spec R, W)`. -/
lemma basicOpen_algebraMap_secRing {R : Type u} [CommRing R] (W : (spec R).Opens) (g : R) :
    W ⊓ PrimeSpectrum.basicOpen g = (spec R).basicOpen (algebraMap R ↑(secRing R W) g) := by
  rw [algebraMap_secRing_res_le_top R W g]
  rw [show resSection R (le_top : W ≤ ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom g) =
      ((spec R).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom g) from rfl]
  rw [Scheme.basicOpen_res, basicOpen_eq_of_affine]

/-- Naturality of `algebraMap R Γ(Spec R, -)`. -/
lemma algebraMap_secRing_naturality {R : Type u} [CommRing R] (W : (spec R).Opens) (g : R)
    {V : (spec R).Opens} (hVW : V ≤ W) :
    algebraMap R ↑(secRing R V) g = resSection R hVW (algebraMap R ↑(secRing R W) g) := by
  rw [algebraMap_secRing_res_le_top R V g, algebraMap_secRing_res_le_top R W g,
    resSection_comp_aux hVW (le_top : W ≤ ⊤)]

theorem specPresheaf_loc_affine (R : Type u) [CommRing R]
    {W : AlgebraicGeometry.Scheme.Opens (AlgebraicGeometry.Spec (CommRingCat.of R))}
    (hW : AlgebraicGeometry.IsAffineOpen W) (g : R) :
    (∀ z : (Work.DSF1.Cech.specPresheaf R).obj
        (Opposite.op (W ⊓ PrimeSpectrum.basicOpen g)),
      ∃ (k : ℕ) (t : (Work.DSF1.Cech.specPresheaf R).obj (Opposite.op W)),
        ((Work.DSF1.Cech.specPresheaf R).map
          (homOfLE (inf_le_left : W ⊓ PrimeSpectrum.basicOpen g ≤ W)).op).hom t = g ^ k • z) ∧
    (∀ t : (Work.DSF1.Cech.specPresheaf R).obj (Opposite.op W),
      ((Work.DSF1.Cech.specPresheaf R).map
        (homOfLE (inf_le_left : W ⊓ PrimeSpectrum.basicOpen g ≤ W)).op).hom t = 0 →
        ∃ k : ℕ, g ^ k • t = 0) := by
  constructor
  · intro z
    letI : Algebra ↑(secRing R W) ↑(secRing R (W ⊓ PrimeSpectrum.basicOpen g)) :=
      (resSection R (inf_le_left)).toAlgebra
    have hloc : IsLocalization.Away (algebraMap R ↑(secRing R W) g)
        ↑(secRing R (W ⊓ PrimeSpectrum.basicOpen g)) :=
      hW.isLocalization_of_eq_basicOpen (algebraMap R ↑(secRing R W) g) (homOfLE inf_le_left)
        (basicOpen_algebraMap_secRing W g)
    haveI := hloc
    obtain ⟨⟨t, m⟩, hx⟩ := IsLocalization.surj
      (Submonoid.powers (algebraMap R ↑(secRing R W) g))
      (show ↑(secRing R (W ⊓ PrimeSpectrum.basicOpen g)) from z)
    obtain ⟨n, hn⟩ := m.2
    refine ⟨n, t, ?_⟩
    rw [specPresheaf_map_apply, smul_eq_algebraMap_mul]
    dsimp only
    have hx' : resSection R (inf_le_left : W ⊓ PrimeSpectrum.basicOpen g ≤ W) t
        = (show ↑(secRing R (W ⊓ PrimeSpectrum.basicOpen g)) from z)
          * resSection R (inf_le_left : W ⊓ PrimeSpectrum.basicOpen g ≤ W) (↑m) := hx.symm
    rw [hx', ← hn, map_pow,
      ← algebraMap_secRing_naturality W g (inf_le_left : W ⊓ PrimeSpectrum.basicOpen g ≤ W),
      mul_comm, map_pow]
  · intro t ht
    letI : Algebra ↑(secRing R W) ↑(secRing R (W ⊓ PrimeSpectrum.basicOpen g)) :=
      (resSection R (inf_le_left)).toAlgebra
    have hloc : IsLocalization.Away (algebraMap R ↑(secRing R W) g)
        ↑(secRing R (W ⊓ PrimeSpectrum.basicOpen g)) :=
      hW.isLocalization_of_eq_basicOpen (algebraMap R ↑(secRing R W) g) (homOfLE inf_le_left)
        (basicOpen_algebraMap_secRing W g)
    haveI := hloc
    have h : algebraMap ↑(secRing R W) ↑(secRing R (W ⊓ PrimeSpectrum.basicOpen g))
        (show ↑(secRing R W) from t)
        = algebraMap ↑(secRing R W) ↑(secRing R (W ⊓ PrimeSpectrum.basicOpen g))
          (0 : ↑(secRing R W)) := by
      rw [map_zero]
      exact ht
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq
      (M := Submonoid.powers (algebraMap R ↑(secRing R W) g)) h
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (↑c) (algebraMap R ↑(secRing R W) g)).mp c.2
    have hc0 : (↑c : ↑(secRing R W)) * (show ↑(secRing R W) from t) = 0 := by rw [hc, mul_zero]
    refine ⟨n, ?_⟩
    rw [smul_eq_algebraMap_mul, map_pow, hn, hc0]

end Work.DSF1.Cech
