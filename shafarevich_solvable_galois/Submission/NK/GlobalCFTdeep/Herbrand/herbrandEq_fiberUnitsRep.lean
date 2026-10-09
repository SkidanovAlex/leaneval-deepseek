import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.FiberUnitsLocal
import Submission.NK.GlobalCFTdeep.Herbrand.fiberUnitsRep_iso_coind
import Submission.NK.GlobalCFTdeep.Herbrand.RepIso
import Submission.NK.GlobalCFTdeep.Herbrand.CoindHerbrand
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitSubRep_ofFinite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Herbrand quotient of the unit part of a fibre

For a finite Galois extension `L / K` of number fields with cyclic Galois group, a finite place
`v` of `K`, a place `w` of `L` above it, the *unit part of the fibre of `v`*

  `∏_{w' | v} 𝒪_{w'}ˣ`

— the idèles supported on the places of `L` above `v` all of whose components are local units —
has Herbrand quotient `1` (Milne, *Class Field Theory*, III.2.5):

  `HerbrandEq (fiberUnitsRep v) 1`.

The proof combines Shapiro's lemma for the unit part of the fibre
(`NK.GlobalCFTdeep.fiberUnitsRep_iso_coind`, which identifies `∏_{w' | v} 𝒪_{w'}ˣ` with
`Coind_{D_w}^{G} 𝒪_wˣ`, reducing the problem to the decomposition group) with Herbrand's theorem
for the local units `h(D_w, 𝒪_wˣ) = 1` (`herbrandEq_localUnitSubRep_ofFinite`, proved from the
short exact sequence `0 ⟶ 𝒪_wˣ ⟶ L_wˣ ⟶ ℤ ⟶ 0` together with
`h(D_w, L_wˣ) = |D_w|` and `h(D_w, ℤ) = |D_w|`).
-/

namespace NK.GlobalCFTdeep.Herbrand

theorem herbrandEq_fiberUnitsRep {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (v : NK.GlobalCFT.Place K) (hv : v.IsFinite) (w : NK.GlobalCFT.Place L)
    (hw : NK.GlobalCFT.Place.LiesOver w v)
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w)] :
    NK.GlobalCFTdeep.HerbrandEq (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v) 1 := by
  classical
  -- reduce to a concrete place `Q` of `K` and a concrete place `q` of `L`
  obtain ⟨Q, rfl⟩ := NK.GlobalCFT.Place.isFinite_iff.mp hv
  have hwf : w.IsFinite := (NK.GlobalCFT.Place.isFinite_of_liesOver hw).mpr hv
  obtain ⟨q, rfl⟩ := NK.GlobalCFT.Place.isFinite_iff.mp hwf
  have hqQ : q.asIdeal.LiesOver Q.asIdeal := by
    rcases hw with ⟨w', v', h1, _⟩ | ⟨q', Q', h1, h2, h3⟩
    · exact absurd h1 (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w' q).symm
    · have h1' : q = q' := NK.GlobalCFT.Place.ofFinite_inj.mp h1
      have h2' : Q = Q' := NK.GlobalCFT.Place.ofFinite_inj.mp h2
      rw [← h1', ← h2'] at h3
      exact h3
  -- Herbrand's theorem for the local units
  have hloc : NK.GlobalCFTdeep.HerbrandEq
      (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) 1 :=
    herbrandEq_localUnitSubRep_ofFinite (K := K) (L := L) Q q
  -- Shapiro's lemma for the unit part of the fibre
  obtain ⟨e⟩ := NK.GlobalCFTdeep.fiberUnitsRep_iso_coind (K := K) (L := L)
    (NK.GlobalCFT.Place.ofFinite Q) q hw
  exact (NK.GlobalCFTdeep.herbrandEq_of_repIso e 1).mpr
    ((NK.GlobalCFTdeep.herbrandEq_coind_iff
      (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q))
      (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) 1).mpr hloc)

end NK.GlobalCFTdeep.Herbrand
