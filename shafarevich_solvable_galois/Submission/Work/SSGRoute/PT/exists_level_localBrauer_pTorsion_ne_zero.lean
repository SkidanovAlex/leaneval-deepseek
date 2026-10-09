import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.E7cOmega.exists_level_p_dvd_decomp
import Submission.Work.SSGRoute.local_pTorsion_card
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

Lead guidance. The design is in the workspace at _lead_design/ssg_pt_design_1002/DESIGN.md. Read the section for your statement FIRST (§2 C6 via the induced module from the normal closure of inertia; §3 CRUX-a 3-step; §4 G1+COUNT via the canonical class-formation pairing). It gives the proof route as numbered steps and the proved workspace names to reuse (local_duality_ext_in, detectsAt_of_coeff_surjection, grunwald_over_K_general, countingIdentity_of_reciprocity_and_converse, ...). Do not re-derive what is proved.
Memory: Lean only through the harness; no sleep loops around lake.
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute.PT

/-- Right-perfectness input: a nonzero `p`-torsion local Brauer class at some level, with
`p ∣ |D_{w'}|`.

For every place `w` of `K` that is finite there are a finite Galois level `L ⊇ K`, a place `w'` of
`L` over `w` with `p ∣ |D_{w'}|`, and `t ∈ H²(D_{w'}, L_{w'}ˣ)` (as `extH (localUnitsRep k L w') 2`)
with `p • t = 0` and `t ≠ 0`.

Route.  Take `M = 𝔽_p` (trivial) and `y := δ(π) ∈ Ext¹_{D_w}(𝔽_p, K_wˣ)`, the image of a uniformizer
`π` of `k_v` under the connecting map of `0 → ℤ → ℤ → 𝔽_p → 0`; its image under the valuation
(`ValuationSES`, `isUnramifiedExt_iff_comp_valHom`) is `δ(1) ≠ 0` in `Ext¹(𝔽_p, ℤ) = ℤ/p`, so
`y ≠ 0`.  Clause (i) of `Work.SSGRoute.local_duality_ext_in` gives a level and `h` with
`levelPair f ι y h ≠ 0`; it is `p`-torsion because `y` is.  Enlarge the level by an unramified
degree-`p` extension at `w'` (`E7cC.exists_level_unramified_p_dvd_inertiaDeg`) to get `p ∣ |D_{w'}|`;
local inflation of `H²` of units is injective (`Work.SSGRoute.localUnits_infl_injective`), so `t`
stays nonzero.

Implementation note.  This existential statement needs only two inputs, both axiom-clean on disk,
so no local duality is required:

* `Work.SSGRoute.E7cOmega.exists_level_p_dvd_decomp` produces, over an algebraically closed
  `Ω ⊇ K`, a finite Galois level `L ⊇ K` (an intermediate field) and a place `w'` of `L` lying over
  the given finite place `w`, with `p ∣ Nat.card (stabilizer (L ≃ₐ[k] L) w')`; the level is
  cyclotomic, `K(ζ_{|κ(v)|^p - 1})`.
* `Work.SSGRoute.local_pTorsion_card` identifies the `p`-torsion of the local Brauer group
  `H²(D_{w'}, L_{w'}ˣ) ≅ ℤ/|D_{w'}|` of order `|D_{w'}|`; it has exactly `p` elements when
  `p ∣ |D_{w'}|`, hence contains a nonzero `p`-torsion class. -/
theorem exists_level_localBrauer_pTorsion_ne_zero (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra k L) (_ : Algebra K L)
      (_ : IsScalarTower k K L) (_ : FiniteDimensional k L) (_ : IsGalois k L)
      (w' : NK.GlobalCFT.Place L),
      NK.GlobalCFT.Place.LiesOver w' (NK.GlobalCFT.Place.ofFinite q) ∧
      p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w') ∧
      ∃ t : SSGRoute.PTExt.extH (NK.HassePrinciple.localUnitsRep k L w') 2,
        p • t = 0 ∧ t ≠ 0 := by
  classical
  -- ## Step 1: a finite Galois level `L ⊇ K` and a place `w' ∣ w` with `p ∣ |D_{w'}|`.
  -- `exists_level_p_dvd_decomp` builds the cyclotomic level `K(ζ_{N^p - 1})`, whose decomposition
  -- group at any place over `w` has order `e · f` with `p ∣ f`.
  obtain ⟨L₀, hnfL₀, hfdL₀, hgalL₀, w', hlies, hpdvd⟩ :=
    Work.SSGRoute.E7cOmega.exists_level_p_dvd_decomp (Ω := AlgebraicClosure K) p k K ζ hζ
      (NK.GlobalCFT.Place.ofFinite q) ⟨q, rfl⟩
  refine ⟨↥L₀, inferInstance, hnfL₀, inferInstance, inferInstance, inferInstance,
    hfdL₀, hgalL₀, w', hlies, hpdvd, ?_⟩
  -- ## Step 2: `H²(D_{w'}, L_{w'}ˣ) ≅ ℤ/|D_{w'}|` has `p`-torsion of order `p`, hence is nonzero.
  have hp : p.Prime := Fact.out
  have hcard : Nat.card {x : SSGRoute.PTExt.extH
      (NK.HassePrinciple.localUnitsRep k ↥L₀ w') 2 // p • x = 0} = p :=
    Work.SSGRoute.local_pTorsion_card (k := k) (L := ↥L₀) p w' hpdvd
  haveI hfin : Finite {x : SSGRoute.PTExt.extH
      (NK.HassePrinciple.localUnitsRep k ↥L₀ w') 2 // p • x = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  haveI hnt : Nontrivial {x : SSGRoute.PTExt.extH
      (NK.HassePrinciple.localUnitsRep k ↥L₀ w') 2 // p • x = 0} :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; exact hp.one_lt)
  obtain ⟨t, ht⟩ := exists_ne (⟨0, by simp⟩ : {x : SSGRoute.PTExt.extH
      (NK.HassePrinciple.localUnitsRep k ↥L₀ w') 2 // p • x = 0})
  exact ⟨t.1, t.2, fun h0 => ht (Subtype.ext h0)⟩

end Work.SSGRoute.PT
