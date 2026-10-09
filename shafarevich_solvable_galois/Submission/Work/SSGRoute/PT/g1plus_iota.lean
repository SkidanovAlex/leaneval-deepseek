import Mathlib
import Submission.Work.SSGRoute.E7cOmega.exists_orbitSupported_extLoc
import Submission.Work.SSGRoute.E7cOmega.eq_of_extLoc_eq_of_orbitSupported
import Submission.Work.SSGRoute.PT.pt_orbitIdele_H2_eq_zero
import Submission.Work.SSGRoute.PT.pt_pairing_ext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `G1⁺`'s orbit-placement map `ι_w` — the one construction the lead design listed as "not on disk"

For the assembly of `Work.SSGRoute.PT.canonical_localPairing_reciprocity_converse` (`G1⁺`) the
design (`_lead_design/ssg_pt_design_1002/DESIGN.md` §4) defines

> `pair M H a b` at a finite place `H = decomp k A` by choosing a finite Galois level `L ≤ Ω` where
> `a|_H`, `b|_H` factor, and setting `pair = χ_L (ι_{w'} (levelPair (βl a) [b]))`,

where `ι_{w'}` "places a class of `H²(D_{w'}, L_{w'}ˣ)` at the orbit of `w'` in `H²(Gal(L/k), 𝕀_L)`
and maps it to `C_L`".

**That map is a definition, not an obligation**: the orbit-placement *existence* is already proved
in the `E7cΩ` lane as

  `Work.SSGRoute.E7cOmega.exists_orbitSupported_extLoc :`
  `∀ (r : Place L) (a : H²(D_r, L_rˣ)), ∃ q : H²(Gal(L/k), 𝕀_L),`
  `  extLoc r q = a ∧ ∀ v ∉ orbit(r), extLoc v q = 0`

(via the surjectivity half of the idèle Shapiro theorem `ext_idele_shapiro`).  This file takes the
*choice* of such a `q` and pushes it to `C_L`:

* **`PT.iotaLift`** — the chosen orbit-supported idèle lift;
* **`PT.iota r z = extToClasses (iotaLift r z)`** — the map the design calls `ι_w`;
* **`PT.iotaLift_spec`** — its characterisation (`extLoc r _ = z`, vanishing off the orbit), by
  `Classical.choose_spec`;
* **`PT.iota_injective_of_ptorsion`** — `p • z = 0 → iota r z = 0 → z = 0`, i.e. **injectivity of
  `ι_w` on the `p`-torsion**, which is the property clause (4) (perfectness) of `G1⁺` uses.  It is a
  direct consequence of the *proved* single-orbit Hasse principle `PT.pt_orbitIdele_H2_eq_zero`
  (S2): the chosen lift is orbit-supported and dies in `C_L`, hence is `0`, hence so is `z`.
-/

namespace Work.SSGRoute.PT

open CategoryTheory

/-- **The chosen orbit-supported idèle lift** of a local `H²`-class: an element of
`H²(Gal(L/k), 𝕀_L)` whose localisation at `r` is `z` and which vanishes off the `Gal(L/k)`-orbit of
`r`.  (`Work.SSGRoute.E7cOmega.exists_orbitSupported_extLoc`.) -/
noncomputable def iotaLift {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (r : NK.GlobalCFT.Place L)
    (z : SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k) (K := L) r) 2) :
    SSGRoute.PTExt.extH (SSGRoute.PTExt.idelesK k L) 2 :=
  Classical.choose (Work.SSGRoute.E7cOmega.exists_orbitSupported_extLoc (k := k) (L := L) r z)

/-- **`ι_w`: the orbit-placement map** of the `G1⁺` construction — a class in `H²(D_r, L_rˣ)` is
placed at the orbit of `r` in `H²(Gal(L/k), 𝕀_L)` and pushed to `H²(Gal(L/k), C_L)`. -/
noncomputable def iota {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (r : NK.GlobalCFT.Place L)
    (z : SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k) (K := L) r) 2) :
    SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2 :=
  SSGRoute.PTExt.extToClasses (k := k) (iotaLift (k := k) (L := L) r z)

/-- **The characterisation of `ι_w`'s underlying lift**: its localisation at `r` is `z` and it
vanishes at every place outside the `Gal(L/k)`-orbit of `r`. -/
theorem iotaLift_spec {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (r : NK.GlobalCFT.Place L)
    (z : SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k) (K := L) r) 2) :
    SSGRoute.PTExt.extLoc (k := k) (K := L) r (iotaLift (k := k) (L := L) r z) = z ∧
      ∀ v : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • r ≠ v) →
        SSGRoute.PTExt.extLoc (k := k) (K := L) v (iotaLift (k := k) (L := L) r z) = 0 :=
  Classical.choose_spec (Work.SSGRoute.E7cOmega.exists_orbitSupported_extLoc (k := k) (L := L) r z)

/-- **The orbit-supported lift is unique.**  Any class with the two characteristic properties of
`iotaLift` *is* `iotaLift`: the difference vanishes off the orbit and has vanishing `r`-localisation,
so it is `0` by `Work.SSGRoute.E7cOmega.eq_of_extLoc_eq_of_orbitSupported`.  (The lemma is stated
with both classes carrying the vanishing-off-the-orbit property, which is exactly how `iotaLift`
is chosen.)  Consequently `ι_w` does not depend on the choice in
`Work.SSGRoute.E7cOmega.exists_orbitSupported_extLoc`. -/
theorem eq_iotaLift_of_spec {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (r : NK.GlobalCFT.Place L)
    (z : SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k) (K := L) r) 2)
    (q : SSGRoute.PTExt.extH (SSGRoute.PTExt.idelesK k L) 2)
    (hq : SSGRoute.PTExt.extLoc (k := k) (K := L) r q = z)
    (hq0 : ∀ v : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • r ≠ v) →
      SSGRoute.PTExt.extLoc (k := k) (K := L) v q = 0) :
    q = iotaLift (k := k) (L := L) r z :=
  Work.SSGRoute.E7cOmega.eq_of_extLoc_eq_of_orbitSupported (k := k) (L := L) r q
    (iotaLift (k := k) (L := L) r z) hq0 (iotaLift_spec (k := k) (L := L) r z).2
    (hq.trans (iotaLift_spec (k := k) (L := L) r z).1.symm)

/-- **`ι_w` is injective on the `p`-torsion.**  This is the property clause (4) (perfectness of the
canonical local pairing) of `G1⁺` consumes, and it is the single-orbit Hasse principle
`PT.pt_orbitIdele_H2_eq_zero` (S2, proved) applied to the orbit-supported chosen lift. -/
theorem iota_injective_of_ptorsion {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (p : ℕ) [Fact p.Prime]
    (r : NK.GlobalCFT.Place L)
    (z : SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k) (K := L) r) 2)
    (hz : p • z = 0) (hzero : iota (k := k) (L := L) r z = 0) :
    z = 0 := by
  obtain ⟨hspec, hvan⟩ := iotaLift_spec (k := k) (L := L) r z
  have hq0 : iotaLift (k := k) (L := L) r z = 0 :=
    pt_orbitIdele_H2_eq_zero k L r (iotaLift (k := k) (L := L) r z) hvan hzero
  rw [← hspec, hq0]
  exact SSGRoute.PTExt.extLoc_zero (k := k) (K := L) r

end Work.SSGRoute.PT
