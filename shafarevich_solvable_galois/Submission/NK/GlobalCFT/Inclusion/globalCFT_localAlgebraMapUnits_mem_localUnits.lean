import Mathlib
import Submission.NK.GlobalCFT.Inclusion
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local algebra map preserves local units

For `L / K` an extension of number fields, `w` a place of `L` over a place `v` of `K`, the local
algebra map `Place.localAlgebraMapUnits w v h : K_vˣ →* L_wˣ` sends the group of local units
`𝒪_vˣ` into the group of local units `𝒪_wˣ`.

At an archimedean place the local units are all of `K_vˣ`, so the statement is vacuous there; the
content of the lemma is the nonarchimedean case, where `w = ofFinite q` over `v = ofFinite Q` and
the map is induced by the ring homomorphism `Q.adicCompletion K →+* q.adicCompletion L` of adic
completions.  Since this ring homomorphism sends the ring of integers `Q.adicCompletionIntegers K`
into `q.adicCompletionIntegers L`
(`Commons.RingTheory.Henselian.adicCompletionMap_mem_integers`), it sends units of the former into
units of the latter.
-/

namespace NK.GlobalCFT.Inclusion

open NK.GlobalCFT
open NumberField IsDedekindDomain

theorem globalCFT_localAlgebraMapUnits_mem_localUnits {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] {w : Place L} {v : Place K}
    (h : Place.LiesOver w v) {x : (Place.localField K v)ˣ} (hx : x ∈ Place.localUnits K v) :
    Place.localAlgebraMapUnits w v h x ∈ Place.localUnits L w := by
  classical
  -- split into the archimedean and nonarchimedean cases for `w` and `v`
  rcases w with w | q
  · -- `w` archimedean: the local units at `w` are everything
    rw [Place.localUnits_ofInfinite]
    exact Subgroup.mem_top _
  · rcases v with v | Q
    · -- `w` nonarchimedean, `v` archimedean: the local algebra map is trivial
      dsimp only [Place.localAlgebraMapUnits]
      rw [Place.localUnits_ofFinite]
      simp only [MonoidHom.one_apply, Submonoid.mem_units_iff]
      exact ⟨by simp, by simp⟩
    · -- `w` and `v` nonarchimedean
      dsimp only [Place.localAlgebraMapUnits]
      split_ifs with hL
      · -- the case in which `q` really lies over `Q`: the adic-completion map preserves units
        rw [Place.localUnits_ofFinite, Submonoid.mem_units_iff]
        have hxI : ((x : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) ∈
            (Q.adicCompletionIntegers K : Set (Q.adicCompletion K)) :=
          ((Submonoid.mem_units_iff (Q.adicCompletionIntegers K).toSubmonoid x).mp
            (by simpa [Place.localUnits_ofFinite] using hx)).1
        have hxI' : (((x⁻¹ : (Q.adicCompletion K)ˣ)) : Q.adicCompletion K) ∈
            (Q.adicCompletionIntegers K : Set (Q.adicCompletion K)) :=
          ((Submonoid.mem_units_iff (Q.adicCompletionIntegers K).toSubmonoid x).mp
            (by simpa [Place.localUnits_ofFinite] using hx)).2
        constructor
        · rw [Units.coe_map]
          exact Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hL hxI
        · rw [Units.coe_map_inv]
          exact Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hL hxI'
      · -- the (impossible) case in which `q` does not lie over `Q`: the map is trivial
        rw [Place.localUnits_ofFinite]
        simp only [MonoidHom.one_apply, Submonoid.mem_units_iff]
        exact ⟨by simp, by simp⟩

end NK.GlobalCFT.Inclusion
