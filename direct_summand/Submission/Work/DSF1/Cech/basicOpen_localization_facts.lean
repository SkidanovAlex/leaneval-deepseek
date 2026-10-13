import Mathlib
import Submission.Work.DSF1.Cech.away_away_surj_ker

namespace Work.DSF1.Cech

universe u
open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false

/-!
# Localization facts for sections over basic opens of `Spec R`

This file proves `basicOpen_localization_facts`: for `g f : R`, the restriction map of
the structure sheaf of `Spec R` from the basic open `D(g)` to `D(g) ∩ D(f) = D(gf)`
exhibits the target as the localization of the source away from (the image of) `f`.

Concretely, writing `Γ(W) = secRing R W` for the ring of sections over the open `W` and
`resSection h : Γ(W') → Γ(W)` for the restriction along `h : W ≤ W'`:

* every element `z` of `Γ(D g ⊓ D f)` becomes, after multiplying by a power of the image of
  `f`, the restriction of an element of `Γ(D g)`;
* every element of `Γ(D g)` which is killed by the restriction to `Γ(D g ⊓ D f)` is killed by
  a power of the image of `f` in `Γ(D g)`.

The whole content is the abstract statement that `R[1/(g f)]` is the localization of
`R[1/g]` at the image of `f`, which is proved in
`Submission.Work.DSF1.Cech.away_away_surj_ker`.
-/

/-- The ring of sections of the structure sheaf of `Spec R` over the open `W`. -/
noncomputable abbrev secRing (R : Type u) [CommRing R]
    (W : TopologicalSpace.Opens (PrimeSpectrum.Top R)) : CommRingCat :=
  (Spec.structureSheaf R).obj.obj (op W)

/-- Restriction of sections of the structure sheaf of `Spec R` along `h : W ≤ W'`. -/
noncomputable abbrev resSection (R : Type u) [CommRing R]
    {W W' : TopologicalSpace.Opens (PrimeSpectrum.Top R)} (h : W ≤ W') :
    ↑(secRing R W') →+* ↑(secRing R W) :=
  (((Spec.structureSheaf R).1).map (homOfLE h).op).hom

/-- The restriction of the global section of `Spec R` corresponding to `a : R` is the image of
`a` under the structure map `R → Γ(Spec R, W)`. -/
lemma resSection_le_top_GammaSpecIso_inv (R : Type u) [CommRing R]
    (W : TopologicalSpace.Opens (PrimeSpectrum.Top R)) (a : R) :
    resSection R (le_top : W ≤ ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)
      = algebraMap R ↑(secRing R W) a := by
  have h := StructureSheaf.algebraMap_self_map R (op W) (op ⊤)
    (show (op ⊤ : (TopologicalSpace.Opens (PrimeSpectrum.Top R))ᵒᵖ) ⟶ op W
      from (homOfLE (le_top : W ≤ ⊤)).op)
  have h2 := congrArg (fun f : CommRingCat.of R ⟶ (Spec.structureSheaf R).obj.obj (op W) =>
    (CommRingCat.Hom.hom f) a) h
  simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [Scheme.ΓSpecIso_inv, CommRingCat.hom_ofHom]
  exact h2

theorem basicOpen_localization_facts (R : Type u) [CommRing R] (g f : R) :
    (∀ z : Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f),
        ∃ (k : ℕ) (t : Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen g)),
          z * ((((Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top).op).hom
              ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f)) ^ k) =
            (((Spec (CommRingCat.of R)).presheaf.map
              (homOfLE (inf_le_left :
                PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f ≤
                  PrimeSpectrum.basicOpen g)).op).hom t)) ∧
      (∀ t : Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen g),
        (((Spec (CommRingCat.of R)).presheaf.map
          (homOfLE (inf_le_left :
            PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f ≤
              PrimeSpectrum.basicOpen g)).op).hom t) = 0 →
          ∃ k : ℕ,
            t * ((((Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top).op).hom
              ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f)) ^ k) = 0) := by
  -- Rewrite everything in terms of the structure sheaf of `PrimeSpectrum R` and the
  -- sections/restriction abbreviations.
  change
    (∀ z : ↑(secRing R (PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f)),
        ∃ (k : ℕ) (t : ↑(secRing R (PrimeSpectrum.basicOpen g))),
          z * ((resSection R (le_top : PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f ≤ ⊤))
                ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f)) ^ k =
            (resSection R (inf_le_left :
              PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f ≤
                PrimeSpectrum.basicOpen g)) t) ∧
      (∀ t : ↑(secRing R (PrimeSpectrum.basicOpen g)),
        (resSection R (inf_le_left : PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f ≤
            PrimeSpectrum.basicOpen g)) t = 0 →
          ∃ k : ℕ,
            t * ((resSection R (le_top : PrimeSpectrum.basicOpen g ≤ ⊤))
                  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f)) ^ k = 0)
  let S : Type u := ↑(secRing R (PrimeSpectrum.basicOpen g))
  let T : Type u := ↑(secRing R (PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f))
  -- The localization structure: `S = R_g`, `T = R_{gf}`.
  have hlocV : IsLocalization.Away g S := by
    change IsLocalization.Away g (↑(secRing R (PrimeSpectrum.basicOpen g)))
    exact StructureSheaf.IsLocalization.to_basicOpen R g
  have hlocT : IsLocalization.Away (g * f) T := by
    change IsLocalization.Away (g * f)
      (↑(secRing R (PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f)))
    rw [show PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f
          = PrimeSpectrum.basicOpen (g * f) from (PrimeSpectrum.basicOpen_mul g f).symm]
    exact StructureSheaf.IsLocalization.to_basicOpen R (g * f)
  haveI := hlocV
  haveI := hlocT
  -- The restriction `Γ(D g) ⟶ Γ(D g ⊓ D f)` as the `S`-algebra structure of `T`.
  let φ : S →+* T := resSection R (inf_le_left :
    PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f ≤ PrimeSpectrum.basicOpen g)
  letI : Algebra S T := φ.toAlgebra
  -- Functoriality of the restriction maps.
  have hres_comp :
      resSection R (le_top : PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f ≤ ⊤) =
        (resSection R (inf_le_left : PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f ≤
            PrimeSpectrum.basicOpen g)).comp
          (resSection R (le_top : PrimeSpectrum.basicOpen g ≤ ⊤)) := by
    have hop : (homOfLE (le_top : PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f ≤ ⊤)).op =
        (homOfLE (le_top : PrimeSpectrum.basicOpen g ≤ ⊤)).op ≫
          (homOfLE (inf_le_left : PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f ≤
            PrimeSpectrum.basicOpen g)).op := Subsingleton.elim _ _
    have hmap := congrArg (((Spec.structureSheaf R).1).map) hop
    rw [Functor.map_comp] at hmap
    exact congrArg CommRingCat.Hom.hom hmap
  have hφ : ∀ x : ↑(secRing R ⊤),
      resSection R (le_top : PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f ≤ ⊤) x =
        φ (resSection R (le_top : PrimeSpectrum.basicOpen g ≤ ⊤) x) := by
    intro x
    exact RingHom.congr_fun hres_comp.symm x
  -- The restriction is an `R`-algebra map, so that `T` is an `S`-algebra compatible with `R`.
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [RingHom.algebraMap_toAlgebra]
    rw [← resSection_le_top_GammaSpecIso_inv R
          (PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f) r,
        ← resSection_le_top_GammaSpecIso_inv R (PrimeSpectrum.basicOpen g) r]
    exact hφ _)
  -- Apply the abstract `away`-of-`away` lemma.
  have key := away_away_surj_ker (R := R) (S := S) (T := T) g f
  refine ⟨?_, ?_⟩
  · intro z
    obtain ⟨k, t, ht⟩ := key.1 z
    refine ⟨k, t, ?_⟩
    rw [resSection_le_top_GammaSpecIso_inv R
          (PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f) f, ht,
      RingHom.algebraMap_toAlgebra]
  · intro t ht
    obtain ⟨k, hk⟩ := key.2 t (by rw [RingHom.algebraMap_toAlgebra]; exact ht)
    exact ⟨k, by rw [resSection_le_top_GammaSpecIso_inv R (PrimeSpectrum.basicOpen g) f, hk]⟩

end Work.DSF1.Cech
