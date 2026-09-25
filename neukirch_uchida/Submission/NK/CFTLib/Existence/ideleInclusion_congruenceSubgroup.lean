import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.GlobalCFT.Inclusion
import Submission.Commons.RingTheory.Henselian.valuation_completion_liesOver

/-!
# The idèle inclusion preserves the congruence subgroups

For a finite extension `L / K` of number fields, a map `u : Place L → Place K` sending each place
of `L` to a place of `K` below it and a monoid homomorphism `φ : 𝕀[K] →* 𝕀[L]` whose `w`-component
is the local embedding `K_{u w}ˣ →* L_wˣ`, the image of the congruence subgroup `U(m) ⊆ 𝕀[K]` of
modulus `m` is contained in `U(m) ⊆ 𝕀[L]`.

This is the ingredient that makes the idèlic Artin map of `K` the restriction of the one of `L`
compatible with moduli: the inclusion of idèles maps the modulus-`m` congruence subgroup of `K`
into the modulus-`m` congruence subgroup of `L`.

The two local inputs are:

* at a finite place `q | Q`, the congruence condition is preserved because `adicCompletionMap`
  satisfies `v_q (f x) = (v_Q x) ^ e` with `e` the ramification index
  (`Commons.RingTheory.Henselian.valuation_completion_liesOver`);
* at an infinite place, positivity is preserved because `completionMap` is compatible with the
  embeddings into `ℂ` (`NumberField.InfinitePlace.Completion.liesOver_extensionEmbedding`).

Since the place `u w` below `w` is an arbitrary element of `Place K`, the two local statements are
proved for an abstract place `v` together with an identification `v = ofFinite Q` (resp.
`v = ofInfinite v'`); this forces the local unit `x v` to be transported along that identification
(`castLocalFieldUnits`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Existence

open NK.GlobalCFT

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-! ### Transporting local units along an equality of places -/

/-- Transport a local unit at the place `v` to the place `v'` along an equality `v = v'`. -/
private def castLocalFieldUnits {v v' : Place K} (h : v = v')
    (y : (Place.localField K v)ˣ) : (Place.localField K v')ˣ := h ▸ y

/-- Transporting a component of an idèle along an equality of places is the same as evaluating
the idèle at the target place. -/
private theorem castLocalFieldUnits_eq {v v' : Place K} (h : v = v') (x : Idele K) :
    castLocalFieldUnits h (x v) = x v' := by
  cases h
  rfl

/-- The real number `ringEquivRealOfIsReal hv x`, seen inside `ℂ`, is `extensionEmbedding v x`:
this is the dictionary between positivity at an infinite place (as expressed by `PosAtReal`) and
positivity of the corresponding complex embedding. -/
private theorem ofReal_ringEquivRealOfIsReal {v : InfinitePlace K} (hv : v.IsReal)
    (x : v.Completion) :
    ((InfinitePlace.Completion.ringEquivRealOfIsReal hv x : ℝ) : ℂ)
      = InfinitePlace.Completion.extensionEmbedding v x := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]

/-! ### Unfolding the local unit embeddings

`Place.localAlgebraMapUnits` is a case distinction on the two places; its third argument (the
proof that the first place lies over the second) is irrelevant.  The next lemmas record the two
nontrivial cases of the definition. -/

private theorem localAlgebraMapUnits_congr (w : Place L) (v : Place K)
    (h h' : Place.LiesOver w v) :
    Place.localAlgebraMapUnits w v h = Place.localAlgebraMapUnits w v h' := rfl

private theorem localAlgebraMapUnits_ofInfinite (w : InfinitePlace L) (v : InfinitePlace K)
    [hwv : w.LiesOver v] (h : Place.LiesOver (Place.ofInfinite w) (Place.ofInfinite v)) :
    Place.localAlgebraMapUnits (Place.ofInfinite w) (Place.ofInfinite v) h =
      Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom := by
  rw [localAlgebraMapUnits_congr (Place.ofInfinite w) (Place.ofInfinite v) h
    (Place.liesOver_ofInfinite hwv)]
  unfold Place.localAlgebraMapUnits
  simp only [dif_pos hwv]

private theorem localAlgebraMapUnits_ofFinite (q : HeightOneSpectrum (𝓞 L))
    (Q : HeightOneSpectrum (𝓞 K)) [hqQ : q.asIdeal.LiesOver Q.asIdeal]
    (h : Place.LiesOver (Place.ofFinite q) (Place.ofFinite Q)) :
    Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q) h =
      Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q hqQ).toMonoidHom := by
  rw [localAlgebraMapUnits_congr (Place.ofFinite q) (Place.ofFinite Q) h
    (Place.liesOver_ofFinite hqQ)]
  unfold Place.localAlgebraMapUnits
  simp only [dif_pos hqQ]

/-! ### The two local inputs -/

/-- **The congruence condition at a finite place is preserved by the local embedding.**
If `y` is congruent to `1` modulo `m` at the prime `Q` of `𝓞 K` (i.e. `v_Q (y - 1) ≤ v_Q m`),
then its image under `adicCompletionMap` is congruent to `1` modulo `m` at any prime `q` of `𝓞 L`
lying over `Q`. -/
theorem congrAt_adicCompletionMap (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K))
    [hqQ : q.asIdeal.LiesOver Q.asIdeal] (m : ℕ) (y : (Q.adicCompletion K)ˣ)
    (hy : NK.CFTLib.Arl.CongrAt Q m y) :
    NK.CFTLib.Arl.CongrAt q m
      (Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q hqQ).toMonoidHom y) := by
  unfold NK.CFTLib.Arl.CongrAt at hy ⊢
  have hsub : ((Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q hqQ).toMonoidHom y :
        (q.adicCompletion L)ˣ) : q.adicCompletion L) - 1
      = Commons.RingTheory.Henselian.adicCompletionMap Q q hqQ ((y : Q.adicCompletion K) - 1) := by
    simp [Units.coe_map, map_sub]
  rw [hsub,
    Commons.RingTheory.Henselian.valuation_completion_liesOver Q q hqQ ((y : Q.adicCompletion K) - 1)]
  have h2 : ((m : ℕ) : q.adicCompletion L) =
      Commons.RingTheory.Henselian.adicCompletionMap Q q hqQ (((m : ℕ) : Q.adicCompletion K)) :=
    (map_natCast _ m).symm
  rw [h2,
    Commons.RingTheory.Henselian.valuation_completion_liesOver Q q hqQ (((m : ℕ) : Q.adicCompletion K))]
  exact pow_le_pow_left₀ zero_le hy _

/-- **Positivity at an infinite place is preserved by the local embedding.**
If `y` is positive at `v | w`, then its image under `completionMap` is positive at `w`. -/
theorem posAtReal_completionMap (w : InfinitePlace L) (v : InfinitePlace K) [hwv : w.LiesOver v]
    (y : v.Completionˣ) (hy : NK.CFTLib.Arl.PosAtReal v y) :
    NK.CFTLib.Arl.PosAtReal w
      (Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom y) := by
  intro hw
  have hv : v.IsReal := InfinitePlace.LiesOver.isReal_of_isReal_over w hw
  have hcoe : ((Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom y :
      w.Completionˣ) : w.Completion) = NumberField.LiesOver.completionMap (y : v.Completion) := rfl
  rw [hcoe]
  have hcomp : ∀ z : v.Completion,
      InfinitePlace.Completion.extensionEmbedding w (NumberField.LiesOver.completionMap z)
        = InfinitePlace.Completion.extensionEmbedding v z := by
    intro z
    have hlies := InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w hv
    have h := RingHom.congr_fun hlies.over z
    rwa [RingHom.comp_apply, RingHom.algebraMap_toAlgebra] at h
  have key : (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      (NumberField.LiesOver.completionMap (y : v.Completion))
      = (InfinitePlace.Completion.ringEquivRealOfIsReal hv) (y : v.Completion) := by
    apply Complex.ofReal_injective
    rw [ofReal_ringEquivRealOfIsReal hw, ofReal_ringEquivRealOfIsReal hv]
    exact hcomp _
  rw [key]
  exact hy hv

/-! ### The two local inputs, for an abstract place `v` below a place of `L` -/

/-- The finite congruence condition is preserved by the local embedding, stated for an abstract
place `v` of `K` together with an identification `v = ofFinite Q`. -/
theorem congrAt_localAlgebraMapUnits_ofFinite {q : HeightOneSpectrum (𝓞 L)} {v : Place K}
    {Q : HeightOneSpectrum (𝓞 K)} (hv : v = Place.ofFinite Q) [hqQ : q.asIdeal.LiesOver Q.asIdeal]
    (h : Place.LiesOver (Place.ofFinite q) v) (m : ℕ) (y : (Place.localField K v)ˣ)
    (hy : NK.CFTLib.Arl.CongrAt Q m (castLocalFieldUnits hv y)) :
    NK.CFTLib.Arl.CongrAt q m (Place.localAlgebraMapUnits (Place.ofFinite q) v h y) := by
  subst hv
  rw [localAlgebraMapUnits_ofFinite q Q h]
  exact congrAt_adicCompletionMap q Q m y hy

/-- Positivity is preserved by the local embedding, stated for an abstract place `v` of `K`
together with an identification `v = ofInfinite v'`. -/
theorem posAtReal_localAlgebraMapUnits_ofInfinite {w : InfinitePlace L} {v : Place K}
    {v' : InfinitePlace K} (hv : v = Place.ofInfinite v') [hwv : w.LiesOver v']
    (h : Place.LiesOver (Place.ofInfinite w) v) (y : (Place.localField K v)ˣ)
    (hy : NK.CFTLib.Arl.PosAtReal v' (castLocalFieldUnits hv y)) :
    NK.CFTLib.Arl.PosAtReal w (Place.localAlgebraMapUnits (Place.ofInfinite w) v h y) := by
  subst hv
  rw [localAlgebraMapUnits_ofInfinite w v' h]
  exact posAtReal_completionMap w v' y hy

/-! ### The main theorem -/

theorem ideleInclusion_congruenceSubgroup {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (u : NK.GlobalCFT.Place L → NK.GlobalCFT.Place K)
    (hu : ∀ w : NK.GlobalCFT.Place L, w.LiesOver (u w))
    (φ : NK.GlobalCFT.Idele K →* NK.GlobalCFT.Idele L)
    (hφ : ∀ (x : NK.GlobalCFT.Idele K) (w : NK.GlobalCFT.Place L),
      φ x w = NK.GlobalCFT.Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (m : ℕ) (x : NK.GlobalCFT.Idele K)
    (hx : x ∈ NK.CFTLib.Arl.congruenceSubgroup K m) :
    φ x ∈ NK.CFTLib.Arl.congruenceSubgroup L m := by
  obtain ⟨hfin, hpos⟩ := hx
  refine ⟨?_, ?_⟩
  · -- the finite places of `L` dividing `m`
    intro q hq
    -- the place of `K` below `q` is a finite place, i.e. it is `ofFinite Q` for a prime `Q`
    obtain ⟨Q, hQ⟩ := Place.isFinite_iff.mp
      ((Place.isFinite_of_liesOver (hu (Place.ofFinite q))).mp (Place.isFinite_ofFinite q))
    -- `q` lies over `Q`
    haveI hqQ : q.asIdeal.LiesOver Q.asIdeal := by
      rcases hu (Place.ofFinite q) with ⟨w', v', h1, _, _⟩ | ⟨q', Q', h1, h2, h3⟩
      · exact absurd h1.symm (Place.ofInfinite_ne_ofFinite w' q)
      · have hq' : q' = q := (Place.ofFinite_inj.mp h1).symm
        have hQ' : Q' = Q := Place.ofFinite_inj.mp (h2.symm.trans hQ)
        subst hq'
        subst hQ'
        exact h3
    -- `m` is contained in `Q` as well
    have hmQ : (m : 𝓞 K) ∈ Q.asIdeal := by
      rw [hqQ.over, Ideal.mem_under, map_natCast]
      exact hq
    -- the congruence condition at `Q`
    have hy : NK.CFTLib.Arl.CongrAt Q m
        (castLocalFieldUnits hQ (x (u (Place.ofFinite q)))) := by
      rw [castLocalFieldUnits_eq hQ x]
      exact hfin Q hmQ
    rw [hφ x (Place.ofFinite q)]
    exact congrAt_localAlgebraMapUnits_ofFinite hQ (hu (Place.ofFinite q)) m
      (x (u (Place.ofFinite q))) hy
  · -- the infinite places of `L`
    intro w
    -- the place of `K` below `w` is an infinite place `ofInfinite v`
    have hfinNeg : ¬ (u (Place.ofInfinite w)).IsFinite := by
      rw [← Place.isFinite_of_liesOver (hu (Place.ofInfinite w))]
      exact Place.not_isFinite_ofInfinite w
    obtain ⟨v, hv⟩ := Place.isInfinite_iff.mp (by
      by_contra h
      exact hfinNeg h)
    -- `w` lies over `v`
    haveI hwv : w.LiesOver v := by
      rcases hu (Place.ofInfinite w) with ⟨w', v', h1, h2, h3⟩ | ⟨q', _, h1, _, _⟩
      · have hw' : w' = w := (Place.ofInfinite_inj.mp h1).symm
        have hv' : v' = v := Place.ofInfinite_inj.mp (h2.symm.trans hv)
        subst hw'
        subst hv'
        exact h3
      · exact absurd h1 (Place.ofInfinite_ne_ofFinite w q')
    -- positivity at `v`
    have hy : NK.CFTLib.Arl.PosAtReal v
        (castLocalFieldUnits hv (x (u (Place.ofInfinite w)))) := by
      rw [castLocalFieldUnits_eq hv x]
      exact hpos v
    rw [hφ x (Place.ofInfinite w)]
    exact posAtReal_localAlgebraMapUnits_ofInfinite hv (hu (Place.ofInfinite w))
      (x (u (Place.ofInfinite w))) hy

end NK.CFTLib.Existence
