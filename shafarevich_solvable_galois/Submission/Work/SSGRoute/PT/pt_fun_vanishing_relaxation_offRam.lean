import Mathlib
import Submission.Work.SSGRoute.PT.restrictedProduct_relaxation
import Submission.Work.SSGRoute.PT.pt_localPairingDual
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The functionals vanishing on the relaxation subgroup, `hU` required only off `Ram`

This is `Work.SSGRoute.PT.pt_fun_vanishing_relaxation` with the hypothesis relating `U'` to `U`

  `hU : ∀ i, ∀ y : Y i, y ∈ U' i ↔ ∀ x : X i, x ∈ U i → β i x y = 0`

weakened to the indices `i ∉ Ram`:

  `hU : ∀ i, i ∉ Ram → ∀ y : Y i, y ∈ U' i ↔ ∀ x : X i, x ∈ U i → β i x y = 0`.

The proof of the original statement uses `hU` at only two kinds of index:

* `i ∉ Ram`, where it rewrites `y ∈ U' i` into the vanishing of `β i · y` on `U i`, and
* `i ∈ T ⊆ Ram`, where only the *first* conjunct of `pt_localPairingDual` is consumed, i.e. the
  realisability of linear functionals by `β`, which is proved from `hβL`/`hβR` alone and never
  mentions `U'`.

At `i ∈ Ram ∖ T` the value of the constructed element is `0` and no hypothesis is needed.  So the
same argument goes through, with the `i ∈ T` invocation of `pt_localPairingDual` replaced by the
`hU`-free realisability lemma `linearFunctional_realized` isolated below.
-/

namespace Work.SSGRoute.PT

open scoped RestrictedProduct

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-- **Realisability of linear functionals without any hypothesis on `U'`.**  If `β : X →ₗ Y →ₗ 𝔽_p`
is non-degenerate in both variables on finite `𝔽_p`-modules, then `β.flip : Y →ₗ Xᵛ` is an
isomorphism, so every linear functional on `X` is realised by an element of `Y`.

This is precisely the first conjunct of `Work.SSGRoute.PT.pt_localPairingDual`; we isolate it here
because that conjunct — unlike the other two — does not mention the submodule `U'` at all, and hence
can be invoked at indices where the hypothesis `hU` relating `U` and `U'` is *not* available. -/
theorem linearFunctional_realized
    (p : ℕ) [Fact p.Prime]
    {X Y : Type*} [AddCommGroup X] [Module (ZMod p) X] [Finite X]
    [AddCommGroup Y] [Module (ZMod p) Y] [Finite Y]
    (β : X →ₗ[ZMod p] Y →ₗ[ZMod p] ZMod p)
    (hβL : ∀ x : X, (∀ y : Y, β x y = 0) → x = 0)
    (hβR : ∀ y : Y, (∀ x : X, β x y = 0) → y = 0) :
    ∀ φ : X →ₗ[ZMod p] ZMod p, ∃ y : Y, ∀ x : X, φ x = β x y := by
  classical
  haveI : Module.Finite (ZMod p) X := Module.Finite.of_finite
  haveI : Module.Finite (ZMod p) Y := Module.Finite.of_finite
  have hinjL : Function.Injective β := by
    intro x y hxy
    have hz : β (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h0 : ∀ z : Y, β (x - y) z = 0 := fun z => by rw [hz]; rfl
    have h1 : x - y = 0 := hβL (x - y) h0
    rwa [sub_eq_zero] at h1
  have hinjR : Function.Injective (LinearMap.flip β) := by
    intro x y hxy
    have hz : LinearMap.flip β (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h0 : ∀ z : X, β z (x - y) = 0 := by
      intro z
      have h1 := congrArg (fun (f : X →ₗ[ZMod p] ZMod p) => f z) hz
      simpa using h1
    have h1 : x - y = 0 := hβR (x - y) h0
    rwa [sub_eq_zero] at h1
  have hPQ : Module.finrank (ZMod p) X = Module.finrank (ZMod p) Y := by
    have h1 : Module.finrank (ZMod p) X ≤ Module.finrank (ZMod p) Y := by
      have h := LinearMap.finrank_le_finrank_of_injective (R := ZMod p)
        (M := X) (M' := Module.Dual (ZMod p) Y) hinjL
      rwa [Subspace.dual_finrank_eq] at h
    have h2 : Module.finrank (ZMod p) Y ≤ Module.finrank (ZMod p) X := by
      have h := LinearMap.finrank_le_finrank_of_injective (R := ZMod p)
        (M := Y) (M' := Module.Dual (ZMod p) X) hinjR
      rwa [Subspace.dual_finrank_eq] at h
    omega
  have hsurjR : Function.Surjective (LinearMap.flip β) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := ZMod p) (V := Y) (V₂ := Module.Dual (ZMod p) X)
      (by rw [Subspace.dual_finrank_eq, hPQ])).mp hinjR
  intro φ
  obtain ⟨y, hy⟩ := hsurjR φ
  refine ⟨y, fun x => ?_⟩
  have h := congrArg (fun (f : X →ₗ[ZMod p] ZMod p) => f x) hy
  simpa using h.symm

open scoped RestrictedProduct in
theorem pt_fun_vanishing_relaxation_offRam
    (p : ℕ) [Fact p.Prime]
    {ι : Type*} {X Y : ι → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module (ZMod p) (X i)] [∀ i, Finite (X i)]
    [∀ i, TopologicalSpace (X i)] [∀ i, DiscreteTopology (X i)]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module (ZMod p) (Y i)] [∀ i, Finite (Y i)]
    [∀ i, TopologicalSpace (Y i)] [∀ i, DiscreteTopology (Y i)]
    (U : ∀ i, Submodule (ZMod p) (X i)) (U' : ∀ i, Submodule (ZMod p) (Y i))
    (β : ∀ i, X i →ₗ[ZMod p] Y i →ₗ[ZMod p] ZMod p)
    (hβL : ∀ i, ∀ x : X i, (∀ y : Y i, β i x y = 0) → x = 0)
    (hβR : ∀ i, ∀ y : Y i, (∀ x : X i, β i x y = 0) → y = 0)
    (hβ0 : ∀ i, ∀ x ∈ U i, ∀ y ∈ U' i, β i x y = 0)
    (Ram : Set ι) (T : Finset ι) (hTRam : ∀ i ∈ T, i ∈ Ram)
    (hU : ∀ i, i ∉ Ram → ∀ y : Y i, y ∈ U' i ↔ ∀ x : X i, x ∈ U i → β i x y = 0)
    [DecidableEq ι]
    (L : (Πʳ i, [X i, U i]) →ₗ[ZMod p] ZMod p)
    (hL : ∀ w : Πʳ i, [X i, U i],
      (∀ i ∈ T, (w i : X i) = 0) → (∀ i, i ∉ Ram → (w i : X i) ∈ U i) → L w = 0) :
    ∃ b : Πʳ i, [Y i, U' i],
      (∀ i, i ∉ Ram → (b i : Y i) ∈ U' i) ∧
      (∀ i, i ∈ Ram → i ∉ T → (b i : Y i) = 0) ∧
      ∀ v : Πʳ i, [X i, U i], L v = restrictedPairing U U' β v b := by
  classical
  -- (1) `L` vanishes on the `single` elements contained in the relaxation subgroup
  have hWT : ∀ (i : ι) (x : X i), i ∈ Ram → i ∉ T →
      L (RestrictedProduct.single U i x) = 0 := by
    intro i x hRam hT
    apply hL
    · intro j hj
      by_cases hji : j = i
      · exfalso
        rw [hji] at hj
        exact hT hj
      · rw [RestrictedProduct.single_eq_of_ne U x hji]
    · intro j hjRam
      by_cases hji : j = i
      · exfalso
        rw [hji] at hjRam
        exact hjRam hRam
      · rw [RestrictedProduct.single_eq_of_ne U x hji]
        exact (U j).zero_mem
  have hWU : ∀ (i : ι) (u : X i), u ∈ U i → i ∉ Ram →
      L (RestrictedProduct.single U i u) = 0 := by
    intro i u hu hRam
    apply hL
    · intro j hj
      by_cases hji : j = i
      · exfalso
        rw [hji] at hj
        exact hRam (hTRam i hj)
      · rw [RestrictedProduct.single_eq_of_ne U u hji]
    · intro j hjRam
      by_cases hji : j = i
      · rw [hji, RestrictedProduct.single_eq_same]
        exact hu
      · rw [RestrictedProduct.single_eq_of_ne U u hji]
        exact (U j).zero_mem
  -- (2) the local values of `b`
  have hlocal : ∀ i, ∃ y : Y i,
      (i ∈ T → ∀ x : X i, L (RestrictedProduct.single U i x) = β i x y) ∧
      (i ∈ Ram → i ∉ T → y = 0) ∧
      (i ∉ Ram → y ∈ U' i ∧ ∀ x : X i, L (RestrictedProduct.single U i x) = β i x y) := by
    intro i
    by_cases hiT : i ∈ T
    · obtain ⟨y, hy⟩ := linearFunctional_realized (p := p) (β := β i) (hβL i) (hβR i)
        (L.comp (singleLin U i))
      exact ⟨y, fun _ => hy, fun _ h2 => absurd hiT h2, fun h1 => absurd (hTRam i hiT) h1⟩
    · by_cases hiR : i ∈ Ram
      · exact ⟨0, fun h => absurd h hiT, fun _ _ => rfl, fun h => absurd hiR h⟩
      · obtain ⟨y, hy⟩ := linearFunctional_realized (p := p) (β := β i) (hβL i) (hβR i)
          (L.comp (singleLin U i))
        refine ⟨y, fun h => absurd h hiT, fun h1 _ => absurd h1 hiR, fun _ => ⟨?_, hy⟩⟩
        rw [hU i hiR y]
        intro x hx
        rw [← hy x]
        exact hWU i x hx hiR
  choose b hbT hbRT hbR using hlocal
  have hbout : ∀ i, i ∉ T → (b i : Y i) ∈ U' i := by
    intro i hiT
    by_cases hiR : i ∈ Ram
    · rw [hbRT i hiR hiT]
      exact (U' i).zero_mem
    · exact (hbR i hiR).1
  have hbRam : ∀ i, i ∈ Ram → i ∉ T → (b i : Y i) = 0 := fun i h1 h2 => hbRT i h1 h2
  have hbPi : ∀ᶠ i in Filter.cofinite, (b i : Y i) ∈ U' i := by
    rw [Filter.eventually_cofinite]
    refine (T.finite_toSet).subset (fun i hi => ?_)
    by_contra hiT
    exact hi (hbout i hiT)
  have hbU' : ∀ i, i ∉ Ram → (b i : Y i) ∈ U' i := by
    intro i hiR
    by_cases hiT : i ∈ T
    · exact absurd (hTRam i hiT) hiR
    · exact hbout i hiT
  refine ⟨⟨b, hbPi⟩, hbU', hbRam, ?_⟩
  intro v
  have hvfin : ({i | (v i : X i) ∉ U i}).Finite := Filter.eventually_cofinite.mp v.2
  set E : Finset ι := hvfin.toFinset with hEdef
  set S : Finset ι := T ∪ E with hSdef
  -- the decomposition of `L (piSingle …)` into the single contributions
  have hsumL : ∀ S' : Finset ι, L (piSingle U S' (fun i => v i))
      = ∑ i ∈ S', L (RestrictedProduct.single U i (v i)) := by
    intro S'
    induction S' using Finset.induction_on with
    | empty =>
      have h0 : piSingle U (∅ : Finset ι) (fun i => v i) = 0 := by
        ext j
        rw [piSingle_apply_ite]
        simp
      rw [h0, map_zero, Finset.sum_empty]
    | insert a S' ha ih =>
      have hstep : piSingle U (insert a S') (fun i => v i)
          = RestrictedProduct.single U a (v a) + piSingle U S' (fun i => v i) := by
        ext j
        rw [RestrictedProduct.add_apply, piSingle_apply_ite, piSingle_apply_ite]
        by_cases hja : j = a
        · rw [hja]
          rw [if_pos (Finset.mem_insert_self a S'), RestrictedProduct.single_eq_same,
            if_neg (fun hcon => ha hcon), add_zero]
        · rw [RestrictedProduct.single_eq_of_ne U (v a) hja]
          by_cases hjS : j ∈ S'
          · rw [if_pos (Finset.mem_insert.mpr (Or.inr hjS)), if_pos hjS, zero_add]
          · rw [if_neg (fun hcon => (Finset.mem_insert.mp hcon).elim hja hjS), if_neg hjS,
              add_zero]
      rw [hstep, map_add, ih, Finset.sum_insert ha]
  -- the leftover term lies in the relaxation subgroup
  have hleft : L (v - piSingle U S (fun i => v i)) = 0 := by
    apply hL
    · intro j hj
      rw [sub_piSingle_apply U S (fun i => v i) v j,
        if_pos (by rw [hSdef]; exact Finset.mem_union_left _ hj), sub_self]
    · intro j hjRam
      rw [sub_piSingle_apply U S (fun i => v i) v j]
      by_cases hjS : j ∈ S
      · rw [if_pos hjS, sub_self]
        exact (U j).zero_mem
      · rw [if_neg hjS, sub_zero]
        by_contra hcon
        exact hjS (by rw [hSdef]; exact Finset.mem_union_right _ (hvfin.mem_toFinset.mpr hcon))
  have hLv : L v = L (piSingle U S (fun i => v i)) := by
    have h2 : piSingle U S (fun i => v i) + (v - piSingle U S (fun i => v i)) = v := by abel
    have h3 : L (piSingle U S (fun i => v i) + (v - piSingle U S (fun i => v i))) = L v := by
      rw [h2]
    rw [map_add, hleft, add_zero] at h3
    exact h3.symm
  -- the pairing side
  have hpair : restrictedPairing U U' β v ⟨b, hbPi⟩ = ∑ i ∈ S, β i (v i) (b i) := by
    refine restrictedPairing_eq_sum U U' β hβ0 v ⟨b, hbPi⟩ S (fun i hi => ⟨?_, ?_⟩)
    · by_contra hcon
      exact hi (by rw [hSdef]; exact Finset.mem_union_right _ (hvfin.mem_toFinset.mpr hcon))
    · by_contra hcon
      have hiT : i ∈ T := by
        by_contra hiT
        exact hcon (hbout i hiT)
      exact hi (by rw [hSdef]; exact Finset.mem_union_left _ hiT)
  have hterm : ∀ i ∈ S, L (RestrictedProduct.single U i (v i)) = β i (v i) (b i) := by
    intro i hiS
    by_cases hiT : i ∈ T
    · exact hbT i hiT (v i)
    · by_cases hiR : i ∈ Ram
      · rw [hbRT i hiR hiT, hWT i (v i) hiR hiT]
        simp
      · exact (hbR i hiR).2 (v i)
  rw [hpair, hLv, hsumL S]
  exact Finset.sum_congr rfl (fun i hi => hterm i hi)
end Work.SSGRoute.PT
