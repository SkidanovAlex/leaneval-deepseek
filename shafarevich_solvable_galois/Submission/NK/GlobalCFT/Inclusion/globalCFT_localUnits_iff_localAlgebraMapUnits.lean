import Mathlib
import Submission.NK.GlobalCFT.Inclusion
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_mem_integers_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local units and the local algebra map: the exact membership criterion

For `L / K` an extension of number fields and places `w` of `L` over `v` of `K`, an element
`z : K_vˣ` is a local unit (`z ∈ 𝒪_vˣ`, where at an archimedean place `𝒪_vˣ = K_vˣ`) if and only
if its image under the local algebra map `K_vˣ →* L_wˣ` is a local unit at `w`:

`Place.localAlgebraMapUnits w v h z ∈ Place.localUnits L w ↔ z ∈ Place.localUnits K v`.

At an archimedean place both sides are everything (and at a mixed place the hypothesis
`Place.LiesOver w v` is impossible), so the content is the nonarchimedean case `q | Q`: the
completion map `K_Q →+* L_q` *reflects* integrality as well as preserving it
(`Commons.NumberTheory.NumberField.Completion.adicCompletionMap_mem_integers_iff`, whose proof
uses that `v (map x) = (v x) ^ e` with ramification index `e ≥ 1`).  Note that this converse
direction is a genuinely local-field-theoretic statement: the valuation of `K_Q` is, up to a
positive multiple, the restriction of the valuation of `L_q`.

As a byproduct we record that `L / K` is automatically finite dimensional as soon as `K` and `L`
are number fields, which is what allows the local-field lemmas (stated for finite extensions) to
be applied here, where the ambient hypothesis only says `Algebra K L`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open NK.GlobalCFT
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Inclusion

/-- A number field `L` containing a number field `K` is finite dimensional over `K`: `L` is
finite over `ℚ` and the structure map `K → L` is injective, so the dimension over `K` is at most
the dimension over `ℚ`.  (Stated for `K` and `L` number fields with an arbitrary `Algebra K L`;
this is the finiteness hypothesis required by the local-field lemmas below, and it is recorded
here separately since it does not appear in the statement of the main theorem.) -/
theorem globalCFT_finiteDimensional_of_numberField {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] : FiniteDimensional K L := by
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun q => by simp
  exact Module.Finite.of_restrictScalars_finite ℚ K L

/-- If the place `ofFinite q` of `L` lies over the place `ofFinite Q` of `K`, then the prime `q`
lies over the prime `Q`. -/
private theorem liesOver_asIdeal {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] {q : HeightOneSpectrum (𝓞 L)} {Q : HeightOneSpectrum (𝓞 K)}
    (h : Place.LiesOver (Place.ofFinite q) (Place.ofFinite Q)) :
    q.asIdeal.LiesOver Q.asIdeal := by
  rcases h with ⟨w', v', hw, hv, _⟩ | ⟨q', Q', hw, hv, hQ⟩
  · exact absurd hw.symm (Place.ofInfinite_ne_ofFinite w' q)
  · obtain rfl := Place.ofFinite_inj.mp hw
    obtain rfl := Place.ofFinite_inj.mp hv
    exact hQ

/-- The local algebra map at nonarchimedean places is the map induced by the adic-completion map
`K_Q →+* L_q`, on unit groups. -/
private theorem localAlgebraMapUnits_ofFinite {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] {q : HeightOneSpectrum (𝓞 L)}
    {Q : HeightOneSpectrum (𝓞 K)} (h : Place.LiesOver (Place.ofFinite q) (Place.ofFinite Q))
    (hL : q.asIdeal.LiesOver Q.asIdeal) :
    Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q) h =
      Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q hL).toMonoidHom := by
  classical
  unfold Place.localAlgebraMapUnits
  simp only [dif_pos hL]

theorem globalCFT_localUnits_iff_localAlgebraMapUnits {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] {w : Place L} {v : Place K}
    (h : Place.LiesOver w v) (z : (Place.localField K v)ˣ) :
    Place.localAlgebraMapUnits w v h z ∈ Place.localUnits L w ↔
      z ∈ Place.localUnits K v := by
  haveI : FiniteDimensional K L := globalCFT_finiteDimensional_of_numberField
  classical
  rcases w with w | q
  · rcases v with v | Q
    · -- both places archimedean: the local units are everything on both sides
      simp [Place.localUnits_ofInfinite]
    · -- `w` archimedean and `v` nonarchimedean: no place of `L` lies over both
      exact absurd ((Place.isFinite_of_liesOver h).mpr (Place.isFinite_ofFinite Q))
        (Place.not_isFinite_ofInfinite w)
  · rcases v with v | Q
    · -- `w` nonarchimedean and `v` archimedean: no place of `L` lies over both
      exact absurd ((Place.isFinite_of_liesOver h).mp (Place.isFinite_ofFinite q))
        (Place.not_isFinite_ofInfinite v)
    · -- both places nonarchimedean: integrality is preserved and reflected
      have hL : q.asIdeal.LiesOver Q.asIdeal := liesOver_asIdeal h
      rw [Place.mem_localUnits_ofFinite, Place.mem_localUnits_ofFinite,
        localAlgebraMapUnits_ofFinite h hL]
      simp only [Units.coe_map, Units.coe_map_inv]
      exact and_congr
        (Commons.NumberTheory.NumberField.Completion.adicCompletionMap_mem_integers_iff
          Q q hL (z : Q.adicCompletion K))
        (Commons.NumberTheory.NumberField.Completion.adicCompletionMap_mem_integers_iff
          Q q hL ((z⁻¹ : (Q.adicCompletion K)ˣ) : Q.adicCompletion K))

end NK.GlobalCFT.Inclusion
