import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.Arl.posAtReal_localNormInfinite
import Submission.NK.CFTLib.Arl.val_norm_one_add_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm map carries the congruence subgroup into the congruence subgroup

Let `K ⊆ L` be a finite extension of number fields.  This file proves that the idèlic norm
`N_{L/K} : 𝕀 L →* 𝕀 K` maps the congruence subgroup `U_m(L)` of modulus `m` into the congruence
subgroup `U_m(K)` of the base field (`NK.CFTLib.Arl.normIdeleHom_mem_congruenceSubgroup`), and
deduces the requested lemma `NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup`: every idèle
`y` of `L` can be adjusted by a *principal* idèle `(d)`, `d : Lˣ`, so that `N_{L/K}(y · (d))`
lies in the congruence subgroup of `K`.

The two ingredients are

* the adjustment of idèles by principal idèles into `U_m(L)`
  (`NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust`), applied to `L`, and
* the compatibility of the norm with the congruence filtrations at each place: at a finite place
  this is `NK.CFTLib.Arl.val_norm_one_add_le` (a local statement, valid for a non-Galois
  extension), at an archimedean place it is `NK.CFTLib.Arl.posAtReal_localNormInfinite`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField RestrictedProduct WithZero NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Arl

open NK.GlobalCFT

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ## Two elementary lemmas -/

/-- A product of elements which are `≡ 1` modulo a value `c < 1` is `≡ 1` modulo `c`. -/
theorem val_prod_one_add_sub_one_le {F : Type*} [Field F]
    (v : Valuation F (WithZero (Multiplicative ℤ))) {ι : Type*}
    (s : Finset ι) (a : ι → F) {c : WithZero (Multiplicative ℤ)}
    (hc : c < 1) (ha : ∀ i ∈ s, v (a i) ≤ c) :
    v ((∏ i ∈ s, (1 + a i)) - 1) ≤ c := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.prod_insert hj]
    have ih' : v ((∏ i ∈ t, (1 + a i)) - 1) ≤ c :=
      ih fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hP : v (∏ i ∈ t, (1 + a i)) = 1 := by
      have h1 : v ((∏ i ∈ t, (1 + a i)) - 1) < 1 := lt_of_le_of_lt ih' hc
      have h2 : v ((1 : F) + ((∏ i ∈ t, (1 + a i)) - 1)) = v (1 : F) :=
        Valuation.map_add_eq_of_lt_left v (by rw [Valuation.map_one]; exact h1)
      rw [Valuation.map_one] at h2
      rwa [show (1 : F) + ((∏ i ∈ t, (1 + a i)) - 1) = ∏ i ∈ t, (1 + a i) from by ring] at h2
    have hkey : (1 + a j) * (∏ i ∈ t, (1 + a i)) - 1
        = ((∏ i ∈ t, (1 + a i)) - 1) + a j * (∏ i ∈ t, (1 + a i)) := by ring
    rw [hkey]
    refine Valuation.map_add_le v ih' ?_
    rw [Valuation.map_mul, hP, mul_one]
    exact ha j (Finset.mem_insert_self j t)

/-- `PosAtReal` is preserved by finite products of units. -/
theorem posAtReal_prod {K : Type*} [Field K] [NumberField K] {w : InfinitePlace K} {ι : Type*}
    (s : Finset ι) (f : ι → (w.Completion)ˣ) (h : ∀ i ∈ s, PosAtReal w (f i)) :
    PosAtReal w (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using posAtReal_one w
  | insert j t hj ih =>
    rw [Finset.prod_insert hj]
    exact posAtReal_mul (h j (Finset.mem_insert_self j t))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## The norm of the congruence subgroup -/

/-- **The idèlic norm maps the congruence subgroup of `L` into the congruence subgroup of `K`.**

At a finite place `𝔭 | (m)` the `𝔭`-component of `N_{L/K} x` is the product of the local norms
`∏_{𝔮 | 𝔭} N_{L_𝔮/K_𝔭} x_𝔮`, and each factor is `≡ 1 mod (m)` because `x_𝔮 ≡ 1 mod (m)` and the
norm is compatible with the congruence filtrations (`val_norm_one_add_le`); a product of elements
`≡ 1 mod (m)` is `≡ 1 mod (m)` (`val_prod_one_add_sub_one_le`).

At an archimedean place `v` the `v`-component of `N_{L/K} x` is the product of the local norms
`∏_{w | v} N_{L_w/K_v} x_w`, each of which is positive by `posAtReal_localNormInfinite` because
`x_w` is positive; a product of positive elements is positive (`posAtReal_prod`). -/
theorem normIdeleHom_mem_congruenceSubgroup (m : ℕ) (hm : 0 < m) {x : Idele L}
    (hx : x ∈ congruenceSubgroup L m) :
    Idele.normIdeleHom K L x ∈ congruenceSubgroup K m := by
  classical
  refine ⟨?_, ?_⟩
  · intro 𝔭 h𝔭
    rw [Idele.normIdeleHom_apply, Idele.normIdeleFun_ofFinite, Units.coe_prod,
      Finset.attach_eq_univ]
    -- the family of local norm deviations at the primes of `L` above `𝔭`
    set a : {q' : HeightOneSpectrum (𝓞 L) // q' ∈ Place.primesOverFinite (K := K) (L := L) 𝔭} →
        (𝔭.adicCompletion K) := fun q' =>
      ((Place.localNormFinite q'.1 𝔭
        ((Place.mem_primesOverFinite (K := K) (L := L) (Q := 𝔭) (q := q'.1)).mp q'.2)
        (x (Place.ofFinite q'.1)) : (𝔭.adicCompletion K)ˣ) : (𝔭.adicCompletion K)) - 1
      with hadef
    have hprod : (∏ q' : {q' : HeightOneSpectrum (𝓞 L) //
        q' ∈ Place.primesOverFinite (K := K) (L := L) 𝔭}, (1 + a q'))
        = ∏ q' : {q' : HeightOneSpectrum (𝓞 L) //
            q' ∈ Place.primesOverFinite (K := K) (L := L) 𝔭},
          ((Place.localNormFinite q'.1 𝔭
            ((Place.mem_primesOverFinite (K := K) (L := L) (Q := 𝔭) (q := q'.1)).mp q'.2)
            (x (Place.ofFinite q'.1)) : (𝔭.adicCompletion K)ˣ) : (𝔭.adicCompletion K)) := by
      refine Finset.prod_congr rfl fun q' _ => ?_
      rw [hadef]
      ring
    rw [← hprod]
    refine val_prod_one_add_sub_one_le
      (v := (Valued.v : Valuation (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ))))
      Finset.univ a (val_natCast_lt_one 𝔭 m h𝔭) ?_
    intro q' _
    -- the congruence condition at `q'`
    have hq' : q'.1.asIdeal.LiesOver 𝔭.asIdeal :=
      (Place.mem_primesOverFinite (K := K) (L := L) (Q := 𝔭) (q := q'.1)).mp q'.2
    have hmL : ((m : ℕ) : 𝓞 L) ∈ q'.1.asIdeal := by
      haveI : q'.1.asIdeal.LiesOver 𝔭.asIdeal := hq'
      have h4 : algebraMap (𝓞 K) (𝓞 L) ((m : ℕ) : 𝓞 K) ∈ q'.1.asIdeal :=
        (Ideal.mem_of_liesOver _ _ ((m : ℕ) : 𝓞 K)).mp h𝔭
      simpa using h4
    have hz := hx.1 q'.1 hmL
    rw [hadef]
    simp only [Place.localNormFinite, Units.coe_map]
    rw [show ((x (Place.ofFinite q'.1) : (q'.1.adicCompletion L)ˣ) : q'.1.adicCompletion L)
        = 1 + (((x (Place.ofFinite q'.1) : (q'.1.adicCompletion L)ˣ) :
            q'.1.adicCompletion L) - 1) from by ring]
    exact val_norm_one_add_le 𝔭 q'.1 hq' m hm _ hz
  · intro v
    -- name the family of local norms in the fibre of `v`
    let f : {w' : InfinitePlace L // w' ∈ Place.fiberInfinite (K := K) (L := L) v} →
        (v.Completion)ˣ := fun w' => by
      letI : w'.1.LiesOver v :=
        (Place.mem_fiberInfinite (K := K) (L := L) (v := v) (w := w'.1)).mp w'.2
      exact Place.localNormInfinite w'.1 v (x (Place.ofInfinite w'.1))
    have hgoal : (Idele.normIdeleHom K L x) (Place.ofInfinite v) = ∏ w', f w' := by
      rw [Idele.normIdeleHom_apply, Idele.normIdeleFun_ofInfinite, Finset.attach_eq_univ]
    rw [hgoal]
    refine posAtReal_prod Finset.univ f ?_
    intro w' _
    letI : w'.1.LiesOver v :=
      (Place.mem_fiberInfinite (K := K) (L := L) (v := v) (w := w'.1)).mp w'.2
    exact posAtReal_localNormInfinite v w'.1 (x (Place.ofInfinite w'.1)) (hx.2 w'.1)

/-! ## The requested lemma -/

theorem exists_norm_mul_mem_congruenceSubgroup (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (m : ℕ) (hm : 0 < m) :
    ∀ y : NK.GlobalCFT.Idele L, ∃ d : Lˣ,
      NK.GlobalCFT.Idele.normIdeleHom K L
        (y * NK.GlobalCFT.Idele.principalIdele L d) ∈ NK.CFTLib.Arl.congruenceSubgroup K m := by
  intro y
  obtain ⟨U, hU, hadj⟩ := exists_isCongruenceSubgroup_and_adjust L m hm
  obtain ⟨d, hd⟩ := hadj y
  refine ⟨d, ?_⟩
  have hd' : y * Idele.principalIdele L d ∈ congruenceSubgroup L m := by
    rw [hU.1] at hd
    exact hd
  exact normIdeleHom_mem_congruenceSubgroup m hm hd'

end NK.CFTLib.Arl
