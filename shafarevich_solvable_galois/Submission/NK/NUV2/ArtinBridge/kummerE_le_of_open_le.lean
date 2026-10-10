import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
import Submission.NK.NUV2.ArtinBridge.exists_finset_forall_localUnits_imp_mem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Milne's subgroup `E` and an arbitrary subgroup `U` containing the `p`-th powers

Let `K` be a number field, `p` a natural number, `S ⊆ Place K` a finite set of places and
`U ≤ 𝕀 K` a subgroup of the idèle group with the two properties

* `U` contains every idèle which is a local unit outside a finite set `F₀` and is `1` on `F₀`
  (this is the shape of the membership criterion for an *open* subgroup `U`, see
  `exists_finset_forall_localUnits_imp_mem`), and
* `U` contains the `p`-th power of every idèle (`𝕀 K ^ p ≤ U`, i.e. `𝕀 K / U` has exponent
  dividing `p` — the shape of the quotients occurring in the Kummer case of the second
  inequality).

Then Milne's subgroup `E = ∏_{v ∈ S} K_v^{×p} · ∏_{v ∉ S} 𝒪_v^×` (the case `T = ∅` of
`kummerE`) is contained in `U`.

The argument is the intended one: an idèle `x ∈ E` is a `p`-th power at every `v ∈ S`, so
choosing a system of local `p`-th roots `a_v` of `x_v` on `S` (and `a_v = 1` outside `S`)
produces an idèle `a` with `a ^ p v = x v` on `S` and `a ^ p v = 1` outside `S`.  Then
`x · (a ^ p)⁻¹` is `1` on `S ⊇ F₀` and a local unit outside `S`, hence lies in `U` by the
membership criterion, and `x = (x · (a ^ p)⁻¹) · a ^ p ∈ U` because `a ^ p ∈ U` by hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.NUV2.ArtinBridge

open NK.GlobalCFT

/-- **Milne's `E` is contained in `U`** whenever `U` contains the `p`-th powers and the
"principal neighbourhood" of idèles which are `1` on `F₀` and local units outside `F₀`, for a
finite `F₀ ⊆ S`. -/
theorem kummerE_le_of_open_le {K : Type} [Field K] [NumberField K] {p : ℕ}
    (S F₀ : Finset (NK.GlobalCFT.Place K)) (U : Subgroup (NK.GlobalCFT.Idele K))
    (hF₀ : ∀ x : NK.GlobalCFT.Idele K,
      (∀ v : NK.GlobalCFT.Place K, v ∉ F₀ → x v ∈ NK.GlobalCFT.Place.localUnits K v) →
      (∀ v ∈ F₀, x v = 1) → x ∈ U)
    (hF₀S : F₀ ⊆ S)
    (hpow : ∀ x : NK.GlobalCFT.Idele K, x ^ p ∈ U) :
    NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p S ∅ ≤ U := by
  intro x hx
  rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.mem_kummerE] at hx
  obtain ⟨hxS, hxout⟩ := hx
  classical
  -- On `S` the idèle `x` is a `p`-th power, so we may choose a local `p`-th root there.
  have hroot : ∀ v : NK.GlobalCFT.Place K, v ∈ S →
      ∃ a : (NK.GlobalCFT.Place.localField K v)ˣ, a ^ p = x v := by
    intro v hv
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (hxS v hv)
    exact ⟨a, by rw [← powMonoidHom_apply]; exact ha⟩
  -- The chosen roots, set to `1` outside `S`.  Its values are local units outside `S`,
  -- so it assembles into an idèle.
  let f : (v : NK.GlobalCFT.Place K) → (NK.GlobalCFT.Place.localField K v)ˣ := fun v =>
    if hv : v ∈ S then Classical.choose (hroot v hv) else 1
  have hfS : ∀ v (hv : v ∈ S), f v ^ p = x v := by
    intro v hv
    have h : f v = Classical.choose (hroot v hv) := dif_pos hv
    rw [h]
    exact Classical.choose_spec (hroot v hv)
  have hfnotS : ∀ v, v ∉ S → f v = 1 := fun v hv => dif_neg hv
  have ha : ∀ᶠ v in Filter.cofinite, f v ∈ NK.GlobalCFT.Place.localUnits K v := by
    rw [Filter.eventually_cofinite]
    refine (S.finite_toSet).subset ?_
    intro v hv
    by_contra h
    exact hv (by rw [hfnotS v h]; exact Subgroup.one_mem _)
  let a : NK.GlobalCFT.Idele K := ⟨f, ha⟩
  -- `a ^ p` agrees with `x` on `S` and is `1` outside `S`.
  have hapowS : ∀ v (hv : v ∈ S), (a ^ p) v = x v := by
    intro v hv
    change (f v) ^ p = x v
    exact hfS v hv
  have hapownotS : ∀ v, v ∉ S → (a ^ p) v = 1 := by
    intro v hv
    change (f v) ^ p = 1
    rw [hfnotS v hv, one_pow]
  have h1 : a ^ p ∈ U := hpow a
  -- `x · (a ^ p)⁻¹` is `1` on `S` (in particular on `F₀`) and a local unit outside `S`.
  have h2 : x * (a ^ p)⁻¹ ∈ U := by
    refine hF₀ _ ?_ ?_
    · intro v _
      rw [NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply]
      by_cases hvS : v ∈ S
      · rw [hapowS v hvS, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [hapownotS v hvS, inv_one, mul_one]
        exact hxout v hvS (by simp)
    · intro v hvF
      rw [NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply,
        hapowS v (hF₀S hvF), mul_inv_cancel]
  have := U.mul_mem h2 h1
  simpa using this

end NK.NUV2.ArtinBridge
