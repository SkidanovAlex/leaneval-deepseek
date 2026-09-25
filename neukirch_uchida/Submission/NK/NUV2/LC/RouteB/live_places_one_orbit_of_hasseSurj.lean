import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.RouteB.hasseSurjDefs
import Submission.NK.NUV2.LC.RouteB.two_place_realisation
import Submission.NK.NUV2.LC.orbit_separation
import Submission.NK.NUV2.LC.RouteB.card_open_local
import Submission.NK.NUV2.LC.h2ProfiniteAddGroup
import Submission.NK.NUV2.LC.RouteB.kill_one_place
import Submission.NK.NUV2.LC.RouteB.res_surjective_open
-- (RouteB agent) stale import of the renamed former self `live_places_one_orbit.lean` removed;
-- every declaration used below is defined in this file.

namespace NK.NUV2.LC.RouteB

open scoped Pointwise

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## Elementary helpers -/

/-- **`rootFix ζ` is open.**  `ζ` is a primitive `p`-th root of unity, hence integral (a root of the
monic polynomial `X ^ p - 1`) over `K`; therefore `K⟮ζ⟯/K` is finite and its fixing subgroup
`rootFix ζ` is open in the Krull topology. -/
theorem isOpen_rootFix (p : ℕ) (hp : p.Prime) (ζ : K') (hζ : IsPrimitiveRoot ζ p) :
    IsOpen (rootFix (K := K) (K' := K') ζ : Set Gal(K'/K)) := by
  have hint : IsIntegral K ζ := (hζ.isIntegral hp.pos).tower_top
  haveI : FiniteDimensional K ↥(IntermediateField.adjoin K ({ζ} : Set K')) :=
    IntermediateField.adjoin.finiteDimensional hint
  exact IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin K ({ζ} : Set K'))

/-- `InOrbit` is monotone in the subgroup. -/
theorem InOrbit.mono {U U' : Subgroup Gal(K'/K)} (h : U ≤ U') {A A' : ValuationSubring K'}
    (hAB : InOrbit U A A') : InOrbit U' A A' := by
  obtain ⟨v, hv, hvA⟩ := hAB
  exact ⟨v, h hv, hvA⟩

/-- **Functoriality of the localisation under restriction.**  For `V ≤ U` and any two proofs of
`V ⊓ D_A ≤ U ⊓ D_A` (they are equal by proof irrelevance),
`loc_A (res x) = res (loc_A x)`. -/
theorem loc_res (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (A : NK.BrauerHasse.OverFinitePrime K K')
    (hD : V ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ U ⊓ NK.BrauerHasse.stabSubgroup A.1)
    (x : NK.BrauerHasse.H2Profinite p U) :
    NK.BrauerHasse.H2Profinite.loc p V
        (NK.LocalDecomposition.H2Profinite.res p h x) A =
      NK.LocalDecomposition.H2Profinite.res p hD
        (NK.BrauerHasse.H2Profinite.loc p U x A) := by
  have h1 : (NK.BrauerHasse.H2Profinite.loc p V
        (NK.LocalDecomposition.H2Profinite.res p h x) A : NK.BrauerHasse.H2Profinite p
          (V ⊓ NK.BrauerHasse.stabSubgroup A.1)) =
      NK.LocalDecomposition.H2Profinite.res p
        (inf_le_left : V ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ V)
        (NK.LocalDecomposition.H2Profinite.res p h x) :=
    NK.LocalDecomposition.loc_eq_res p V A (NK.LocalDecomposition.H2Profinite.res p h x)
  have h2 : NK.LocalDecomposition.H2Profinite.res p
        (inf_le_left : V ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ V)
        (NK.LocalDecomposition.H2Profinite.res p h x) =
      NK.LocalDecomposition.H2Profinite.res p
        ((inf_le_left : V ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ V).trans h) x :=
    NK.NUV2.LC.OddTwist.H2Profinite_res_comp p _ h x
  have h3 : NK.LocalDecomposition.H2Profinite.res p
        ((inf_le_left : V ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ V).trans h) x =
      NK.LocalDecomposition.H2Profinite.res p
        (hD.trans (inf_le_left : U ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ U)) x :=
    congrArg (fun hh => NK.LocalDecomposition.H2Profinite.res p hh x)
      (Subsingleton.elim _ _)
  have h4 : NK.LocalDecomposition.H2Profinite.res p
        (hD.trans (inf_le_left : U ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ U)) x =
      NK.LocalDecomposition.H2Profinite.res p hD
        (NK.LocalDecomposition.H2Profinite.res p
          (inf_le_left : U ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ U) x) :=
    (NK.NUV2.LC.OddTwist.H2Profinite_res_comp p hD
      (inf_le_left : U ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ U) x).symm
  have h5 : NK.LocalDecomposition.H2Profinite.res p hD
        (NK.LocalDecomposition.H2Profinite.res p
          (inf_le_left : U ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ U) x) =
      NK.LocalDecomposition.H2Profinite.res p hD
        (NK.BrauerHasse.H2Profinite.loc p U x A) :=
    congrArg (fun t => NK.LocalDecomposition.H2Profinite.res p hD t)
      (NK.LocalDecomposition.loc_eq_res p U A x).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-- **The level preimage.**  If `C ≤ U' ≤ C · Gal(K'/L)`, the level inclusion
`C/(C ⊓ Gal(K'/L)) →* U'/(U' ⊓ Gal(K'/L))` is bijective, so every class of `H²(C/(C ⊓ Gal(K'/L)))`
lifts to a class of `H²(U'/(U' ⊓ Gal(K'/L)))`. -/
theorem exists_level_preimage_of_le_sup (p : ℕ) {C U' : Subgroup Gal(K'/K)} (hCU : C ≤ U')
    (L : FiniteGaloisIntermediateField K K') (h : U' ≤ C ⊔ L.fixingSubgroup)
    (a : NK.BrauerHasse.LevelH2 p C L) :
    ∃ b : NK.BrauerHasse.LevelH2 p U' L,
      (NK.BrauerHasse.H2.map (NK.BrauerHasse.levelInclHom hCU L)).hom b = a :=
  NK.HassePrinciple.h2Map_surjective_of_bijective (NK.BrauerHasse.levelInclHom hCU L)
    ⟨NK.HassePrinciple.levelInclHom_injective hCU L,
      levelInclHom_surjective_of_le_sup_fixingSubgroup' hCU L h⟩ a

/-- **The one-place realisation at a closed subgroup.**  Let `V ≤ Gal(K'/K)` be closed,
`U₀ ≥ V` an open subgroup lying in `rootFix ζ`, and `B₁, B₂` two places of `K'` which are not
`U₀`-conjugate.  Then every non-zero class `z` of the *local* group `H²(V ⊓ D_{B₁}, Z/p)` is the
local component at `B₁` of a class of `H²(V, Z/p)` whose local component at `B₂` vanishes.

The construction: take a finite level `L` representing `z`, shrink `U₀` by the compactness lemma
`NK.NUV2.LC.RouteB.exists_open_le_inf_le_sup_aux` to an open `W ≥ V` with
`W ⊓ D_{B₁} ≤ (V ⊓ D_{B₁}) · Gal(K'/L)`; at the level `L` the inclusion of level groups is then
bijective, so `z` lifts to a class `c` of `H²(W ⊓ D_{B₁})`; the Hasse surjectivity `HasseSurj` at the
open level `W` realises the local pair `(c, 0)`, and restricting to `V` gives the class sought. -/
theorem exists_loc_ne_zero_and_loc_eq_zero_of_hasseSurj
    (p : ℕ) (ζ : K') (hH : HasseSurj p K K' ζ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : IsPrimitiveRoot ζ p)
    {V U₀ : Subgroup Gal(K'/K)} (hVcl : IsClosed (V : Set Gal(K'/K)))
    (hU₀open : IsOpen (U₀ : Set Gal(K'/K))) (hVU₀ : V ≤ U₀)
    (hU₀ζ : U₀ ≤ rootFix (K := K) (K' := K') ζ)
    (B₁ B₂ : NK.BrauerHasse.OverFinitePrime K K')
    (havoid : ¬ InOrbit (K := K) (K' := K') U₀ B₁.1 B₂.1)
    {z : NK.BrauerHasse.H2Profinite p (V ⊓ NK.BrauerHasse.stabSubgroup B₁.1)}
    (hz : z ≠ 0) :
    ∃ y : NK.BrauerHasse.H2Profinite p V,
      NK.BrauerHasse.H2Profinite.loc p V y B₁ ≠ 0 ∧
        NK.BrauerHasse.H2Profinite.loc p V y B₂ = 0 := by
  classical
  -- a finite level representing the local class `z`
  obtain ⟨L, a, hLa⟩ := NK.BrauerHasse.H2Profinite.ofLevel_surjective z
  -- the compactness step: an open `W` with `V ≤ W ≤ U₀` and `W ⊓ D_{B₁} ≤ (V ⊓ D_{B₁}) · Gal(K'/L)`
  obtain ⟨W, hVW, hWU₀, hWopen, hWinf⟩ :=
    exists_open_le_inf_le_sup_aux V U₀ (NK.BrauerHasse.stabSubgroup B₁.1) L.fixingSubgroup
      hVcl hVU₀ hU₀open (NK.LocalDecomposition.isClosed_stabSubgroup B₁.1)
      (IntermediateField.fixingSubgroup_isOpen (L : IntermediateField K K'))
  -- the lift of `z` to the local group of `W` at `B₁`
  have hCW : V ⊓ NK.BrauerHasse.stabSubgroup B₁.1 ≤
      W ⊓ NK.BrauerHasse.stabSubgroup B₁.1 := fun q hq => ⟨hVW hq.1, hq.2⟩
  obtain ⟨b, hb⟩ := exists_level_preimage_of_le_sup (p := p) hCW L hWinf a
  let c : NK.BrauerHasse.LocalH2 p W B₁.1 := NK.BrauerHasse.H2Profinite.ofLevel L b
  have hc : NK.LocalDecomposition.H2Profinite.res p hCW c = z := by
    rw [NK.LocalDecomposition.H2Profinite.res_ofLevel, hb, hLa]
  -- the Hasse surjectivity at the open level `W`, for the pair `(B₁, B₂)`
  let Bfam : Fin 2 → NK.BrauerHasse.OverFinitePrime K K' := Fin.cases B₁ (fun _ => B₂)
  have hpair : ∀ i j : Fin 2, i ≠ j →
      ¬ InOrbit (K := K) (K' := K') W (Bfam i).1 (Bfam j).1 := by
    have key : ∀ i j : Fin 2, i ≠ j → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by decide
    rintro i j hij
    rcases key i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fun h => havoid (h.mono hWU₀)
    · exact fun h => havoid (InOrbit.symm' (h.mono hWU₀))
  have hsurj := hH hp hp2 hζ W hWopen (hWU₀.trans hU₀ζ) (Fin 2) Bfam hpair
  let g : (i : Fin 2) → NK.BrauerHasse.LocalH2 p W (Bfam i).1 :=
    Fin.cases (motive := fun i => NK.BrauerHasse.LocalH2 p W (Bfam i).1) c (fun _ => 0)
  obtain ⟨x, hx⟩ := hsurj g
  have hx₀ : NK.BrauerHasse.H2Profinite.loc p W x B₁ = c := congrFun hx 0
  have hx₁ : NK.BrauerHasse.H2Profinite.loc p W x B₂ = 0 := congrFun hx 1
  refine ⟨NK.LocalDecomposition.H2Profinite.res p hVW x, ?_, ?_⟩
  · rw [loc_res p hVW B₁ hCW x, hx₀, hc]
    exact hz
  · rw [loc_res p hVW B₂
      (show V ⊓ NK.BrauerHasse.stabSubgroup B₂.1 ≤
          W ⊓ NK.BrauerHasse.stabSubgroup B₂.1 from fun q hq => ⟨hVW hq.1, hq.2⟩) x, hx₁]
    exact NK.NUV2.LC.OddTwist.H2Profinite_res_zero p _

theorem live_places_one_orbit_of_hasseSurj {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (hH : NK.NUV2.LC.RouteB.HasseSurj p K K' ζ)
    (V : Subgroup Gal(K'/K)) (hVcl : IsClosed (V : Set Gal(K'/K)))
    (hVζ : V ≤ NK.NUV2.LC.RouteB.rootFix (K := K) (K' := K') ζ)
    (hcard : Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V) = p)
    {A₁ A₂ : NK.BrauerHasse.OverFinitePrime K K'}
    (h₁ : NK.NUV2.LC.RouteB.IsLive (K := K) (K' := K') p V A₁.1)
    (h₂ : NK.NUV2.LC.RouteB.IsLive (K := K) (K' := K') p V A₂.1)
    (hsame : A₁.1.comap (algebraMap K K') = A₂.1.comap (algebraMap K K')) :
    NK.NUV2.LC.RouteB.InOrbit (K := K) (K' := K') V A₁.1 A₂.1 := by
  classical
  by_contra hnot
  -- (L5) orbit separation: an open subgroup `U₀ ≥ V` whose orbit of `A₁` still avoids `A₂`
  have horb : A₂.1 ∉ MulAction.orbit V A₁.1 := by
    intro hmem
    obtain ⟨v, hv⟩ := MulAction.mem_orbit_iff.mp hmem
    exact hnot ⟨(v : Gal(K'/K)), v.2, hv⟩
  obtain ⟨U₀, hU₀open, hVU₀, hU₀av⟩ :=
    NK.NUV2.LC.orbit_separation V hVcl A₁.1 A₂.1 horb
  -- shrink `U₀` into `rootFix ζ`
  set U₁ : Subgroup Gal(K'/K) := U₀ ⊓ rootFix (K := K) (K' := K') ζ with hU₁def
  have hU₁open : IsOpen (U₁ : Set Gal(K'/K)) := by
    rw [hU₁def, Subgroup.coe_inf]
    exact hU₀open.inter (isOpen_rootFix p hp ζ hζ)
  have hVU₁ : V ≤ U₁ := le_inf hVU₀ hVζ
  have hU₁ζ : U₁ ≤ rootFix (K := K) (K' := K') ζ := inf_le_right
  have hU₁av : ¬ InOrbit (K := K) (K' := K') U₁ A₁.1 A₂.1 := by
    rintro ⟨v, hv, hvA⟩
    exact hU₀av (MulAction.mem_orbit_iff.mpr ⟨⟨v, hv.1⟩, hvA⟩)
  have hA₂A₁ : ¬ InOrbit (K := K) (K' := K') U₁ A₂.1 A₁.1 :=
    fun h => hU₁av (InOrbit.symm' h)
  -- the two live local classes
  obtain ⟨z₁, hz₁⟩ := h₁
  obtain ⟨z₂, hz₂⟩ := h₂
  -- two classes of `H²(V, Z/p)` with independent local components
  obtain ⟨y₁, hy₁, hy₁'⟩ := exists_loc_ne_zero_and_loc_eq_zero_of_hasseSurj
    (K := K) (K' := K') p ζ hH hp hp2 hζ hVcl hU₁open hVU₁ hU₁ζ A₁ A₂ hU₁av hz₁
  obtain ⟨y₂, hy₂, hy₂'⟩ := exists_loc_ne_zero_and_loc_eq_zero_of_hasseSurj
    (K := K) (K' := K') p ζ hH hp hp2 hζ hVcl hU₁open hVU₁ hU₁ζ A₂ A₁ hA₂A₁ hz₂
  -- the cardinality squeeze: `H²(V, Z/p)` has only `p` elements
  exact squeeze_H2Profinite (K := K) (K' := K') p hp hcard A₁ A₂ y₁ y₂ hy₁ hy₂' hy₁' hy₂

end NK.NUV2.LC.RouteB
