import Mathlib
import Submission.Work.DSSEC.Basic
import Submission.Work.DSCHART.xiSec_self

namespace Work.DSSEC

attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry
universe u

/-!
# The fraction identity of the chart coordinates

We prove `Work.DSSEC.xiSecS_pair` by transferring the identity
`(x_k/x_b)·(x_b/x_a) = x_k/x_a`, which holds in the homogeneous localisation
`A[x]_{(x_a x_b)}`, to `Γ(X, U_a ∩ U_b)` along `i : X ⟶ ℙᴺ_A`.

The auxiliary vocabulary below names the pieces:

* `xiX l` — the coordinate `x_l`;
* `xiD l` — the chart `D₊(x_l)`;
* `xiDab a b` — `D₊(x_a x_b)`;
* `xiQ l k` — the fraction `x_k/x_l` in `A[x]_{(x_l)}`;
* `xiSecP l k` — its image in `Γ(ℙᴺ_A, D₊(x_l))` under `Proj.awayToSection`;
* `xiAlphab`, `xiAlphaa` — the inclusions `D₊(x_a x_b) ⊆ D₊(x_b)`, `⊆ D₊(x_a)`.

The proof has three steps:

1. `xiAway_mul` — the fraction identity in `A[x]_{(x_a x_b)}` (a `val`-injectivity and
   clearing-denominators computation in `Localization.Away (x_a x_b)`);
2. `xiSecP_pair` — the same identity in `Γ(ℙᴺ_A, D₊(x_a x_b))`, obtained by pushing (1)
   through the ring hom `Proj.awayToSection` and the `Proj.awayMap_awayToSection` identifications;
3. `xiSecS_eq_restrict` — the compatibility of `xiSecS` with the restriction of the chart
   coordinates to `D₊(x_a x_b)` and the pullback along `i` (`Scheme.Hom.map_appLE`).

The final theorem is then the image of (2) under the ring hom
`i.appLE D₊(x_a x_b) (U_a ∩ U_b)`.
-/

section Aux

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {N : ℕ}

/-- the coordinate `x_l = X_l ∈ A[x₀,…,x_N]`. -/
noncomputable abbrev xiX (l : Idx N) : MvPolynomial (Fin (N + 1)) A := MvPolynomial.X l.down

/-- the standard chart `D₊(x_l) ⊆ ℙᴺ_A`. -/
noncomputable abbrev xiD (l : Idx N) : (DSMap.PSpace A N).Opens :=
  Proj.basicOpen (DSMap.PGr A N) (xiX (A := A) l)

/-- the fraction `x_k / x_l ∈ A[x]_{(x_l)}`. -/
noncomputable abbrev xiQ (l k : Idx N) :
    HomogeneousLocalization.Away (DSMap.PGr A N) (xiX (A := A) l) :=
  HomogeneousLocalization.Away.mk (DSMap.PGr A N) (DSMap.Mix2.X_mem_PGr l.down) 1
    (xiX (A := A) k) (by rw [one_smul]; exact DSMap.Mix2.X_mem_PGr k.down)

/-- the section `x_k/x_l ∈ Γ(ℙᴺ_A, D₊(x_l))`. -/
noncomputable abbrev xiSecP (l k : Idx N) : Γ(DSMap.PSpace A N, xiD (A := A) l) :=
  (Proj.awayToSection (DSMap.PGr A N) (xiX (A := A) l)).hom (xiQ (A := A) l k)

/-- the open `D₊(x_a x_b)`. -/
noncomputable abbrev xiDab (a b : Idx N) : (DSMap.PSpace A N).Opens :=
  Proj.basicOpen (DSMap.PGr A N) (xiX (A := A) a * xiX (A := A) b)

/-- the inclusion `D₊(x_a x_b) ⊆ D₊(x_b)`. -/
noncomputable abbrev xiAlphab (a b : Idx N) :
    xiDab (A := A) (N := N) a b ≤ xiD (A := A) (N := N) b :=
  Proj.basicOpen_mono (DSMap.PGr A N) (xiX (A := A) b) (xiX (A := A) a * xiX (A := A) b)
    ⟨xiX (A := A) a, mul_comm _ _⟩

/-- the inclusion `D₊(x_a x_b) ⊆ D₊(x_a)`. -/
noncomputable abbrev xiAlphaa (a b : Idx N) :
    xiDab (A := A) (N := N) a b ≤ xiD (A := A) (N := N) a :=
  Proj.basicOpen_mono (DSMap.PGr A N) (xiX (A := A) a) (xiX (A := A) a * xiX (A := A) b)
    ⟨xiX (A := A) b, rfl⟩

/-- `xiSec i l k` is `i` applied to the section `x_k/x_l ∈ Γ(ℙᴺ_A, D₊(x_l))`. -/
theorem xiSec_eq_app (i : X ⟶ DSMap.PSpace A N) (l k : Idx N) :
    DSMap.Mix2.xiSec i l.down k.down = (i.app (xiD (A := A) l)).hom (xiSecP (A := A) l k) := by
  dsimp only [DSMap.Mix2.xiSec, xiSecP, xiQ, xiD, xiX]

/-- `xiSecS i S l hl k` is the image under `i.appLE` of the section `x_k/x_l` of the chart
`D₊(x_l)`. -/
theorem xiSecS_eq_appLE (i : X ⟶ DSMap.PSpace A N) (S : Finset (Idx N)) (l : Idx N)
    (hl : l ∈ S) (k : Idx N) :
    xiSecS i S l hl k =
      (i.appLE (xiD (A := A) l) (⨅ m ∈ S, DSMap.Mix2.chartCover i m)
        (iInf_chartCover_le_single i hl)).hom (xiSecP (A := A) l k) := by
  dsimp only [xiSecS]
  rw [xiSec_eq_app]
  dsimp only [Scheme.Hom.appLE]
  rfl

/-- The fraction identity in the homogeneous localisation `A[x]_{(x_a x_b)}`:
`(x_k/x_b)·(x_b/x_a) = x_k/x_a`.  Both sides are elements of `Away 𝒜 (x_a x_b)`; the identity
is checked by `val`-injectivity and clearing denominators in `Localization.Away (x_a x_b)`. -/
theorem xiAway_mul (a b k : Idx N) :
    HomogeneousLocalization.awayMap (DSMap.PGr A N) (DSMap.Mix2.X_mem_PGr a.down)
        (show xiX (A := A) a * xiX (A := A) b = xiX (A := A) b * xiX (A := A) a from
          mul_comm _ _) (xiQ (A := A) b k)
      * HomogeneousLocalization.awayMap (DSMap.PGr A N) (DSMap.Mix2.X_mem_PGr b.down)
          (show xiX (A := A) a * xiX (A := A) b = xiX (A := A) a * xiX (A := A) b from rfl)
          (xiQ (A := A) a b)
      = HomogeneousLocalization.awayMap (DSMap.PGr A N) (DSMap.Mix2.X_mem_PGr b.down)
          (show xiX (A := A) a * xiX (A := A) b = xiX (A := A) a * xiX (A := A) b from rfl)
          (xiQ (A := A) a k) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul]
  dsimp only [xiQ]
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

/-- The fraction identity on `Γ(ℙᴺ_A, D₊(x_a x_b))`: the restrictions of `x_k/x_b`, `x_b/x_a`
and `x_k/x_a` satisfy `(x_k/x_b)·(x_b/x_a) = x_k/x_a`. -/
theorem xiSecP_pair (a b k : Idx N) :
    ((DSMap.PSpace A N).presheaf.map (homOfLE (xiAlphab (A := A) a b)).op).hom
        (xiSecP (A := A) b k)
      * ((DSMap.PSpace A N).presheaf.map (homOfLE (xiAlphaa (A := A) a b)).op).hom
          (xiSecP (A := A) a b)
      = ((DSMap.PSpace A N).presheaf.map (homOfLE (xiAlphaa (A := A) a b)).op).hom
          (xiSecP (A := A) a k) := by
  have key := xiAway_mul (A := A) (N := N) a b k
  have h1 := congrArg
    (fun x => (Proj.awayToSection (DSMap.PGr A N) (xiX (A := A) a * xiX (A := A) b)).hom x) key
  simp only [map_mul] at h1
  have hb := congrArg (fun φ => CommRingCat.Hom.hom φ (xiQ (A := A) b k))
    (Proj.awayMap_awayToSection (DSMap.PGr A N) (f := xiX (A := A) b) (g := xiX (A := A) a)
      (DSMap.Mix2.X_mem_PGr a.down) (x := xiX (A := A) a * xiX (A := A) b) (hx := mul_comm _ _))
  have haab := congrArg (fun φ => CommRingCat.Hom.hom φ (xiQ (A := A) a b))
    (Proj.awayMap_awayToSection (DSMap.PGr A N) (f := xiX (A := A) a) (g := xiX (A := A) b)
      (DSMap.Mix2.X_mem_PGr b.down) (x := xiX (A := A) a * xiX (A := A) b) (hx := rfl))
  have haak := congrArg (fun φ => CommRingCat.Hom.hom φ (xiQ (A := A) a k))
    (Proj.awayMap_awayToSection (DSMap.PGr A N) (f := xiX (A := A) a) (g := xiX (A := A) b)
      (DSMap.Mix2.X_mem_PGr b.down) (x := xiX (A := A) a * xiX (A := A) b) (hx := rfl))
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at hb haab haak
  rw [hb, haab, haak] at h1
  simpa only [xiSecP] using h1

/-- Restricting the chart coordinates `x_k/x_l` to `D₊(x_a x_b)` and pulling back along `i`
gives `xiSecS`. -/
theorem xiSecS_eq_restrict (i : X ⟶ DSMap.PSpace A N) {a b : Idx N} (l : Idx N)
    (hl : l ∈ ({a, b} : Finset (Idx N)))
    (hU : (⨅ m ∈ ({a, b} : Finset (Idx N)), DSMap.Mix2.chartCover i m)
      ≤ i ⁻¹ᵁ xiDab (A := A) a b)
    (α : xiDab (A := A) (N := N) a b ≤ xiD (A := A) (N := N) l) (k : Idx N) :
    (i.appLE (xiDab (A := A) a b) (⨅ m ∈ ({a, b} : Finset (Idx N)), DSMap.Mix2.chartCover i m)
        hU).hom
        (((DSMap.PSpace A N).presheaf.map (homOfLE α).op).hom (xiSecP (A := A) l k))
      = xiSecS i {a, b} l hl k := by
  rw [xiSecS_eq_appLE i {a, b} l hl k]
  change (((DSMap.PSpace A N).presheaf.map (homOfLE α).op) ≫
      i.appLE (xiDab (A := A) a b) (⨅ m ∈ ({a, b} : Finset (Idx N)), DSMap.Mix2.chartCover i m)
        hU).hom (xiSecP (A := A) l k) = _
  rw [Scheme.Hom.map_appLE]

end Aux

/-- **The fraction identity of the chart coordinates**: on `U_a ∩ U_b` the sections `x_k/x_b`
and `x_b/x_a` multiply to `x_k/x_a`.  Pulling back along `i` from the identity in
`Γ(ℙᴺ, D₊(x_a x_b)) ≅ ↧(Away (PGr A N) (X_a·X_b))` proves it (uses `Proj.awayToSection`,
`Proj.awayMap_awayToSection`, `HomogeneousLocalization.val_injective`). -/
theorem xiSecS_pair {A : Type u} [CommRing A] {X : Scheme.{u}} {N : ℕ} (i : X ⟶ DSMap.PSpace A N)
    (a b k : Work.DSSEC.Idx N) :
    Work.DSSEC.xiSecS i {a, b} b (by simp) k * Work.DSSEC.xiSecS i {a, b} a (by simp) b =
      Work.DSSEC.xiSecS i {a, b} a (by simp) k := by
  have ha : a ∈ ({a, b} : Finset (Idx N)) := by simp
  have hb : b ∈ ({a, b} : Finset (Idx N)) := by simp
  have hU : (⨅ m ∈ ({a, b} : Finset (Idx N)), DSMap.Mix2.chartCover i m)
      ≤ i ⁻¹ᵁ xiDab (A := A) a b := by
    have h_eq : DSMap.Mix2.chartCover i a ⊓ DSMap.Mix2.chartCover i b
        = i ⁻¹ᵁ xiDab (A := A) a b := by
      simp only [DSMap.Mix2.chartCover, xiDab, xiX, Proj.basicOpen_mul, Scheme.Hom.preimage_inf]
    exact le_trans (le_inf (iInf_chartCover_le_single i ha) (iInf_chartCover_le_single i hb))
      (le_of_eq h_eq)
  have h2 := congrArg
    (fun x => (i.appLE (xiDab (A := A) a b) (⨅ m ∈ ({a, b} : Finset (Idx N)),
      DSMap.Mix2.chartCover i m) hU).hom x) (xiSecP_pair (A := A) (N := N) a b k)
  simp only [map_mul] at h2
  rw [xiSecS_eq_restrict i b hb hU (xiAlphab (A := A) a b) k,
    xiSecS_eq_restrict i a ha hU (xiAlphaa (A := A) a b) b,
    xiSecS_eq_restrict i a ha hU (xiAlphaa (A := A) a b) k] at h2
  exact h2

end Work.DSSEC
