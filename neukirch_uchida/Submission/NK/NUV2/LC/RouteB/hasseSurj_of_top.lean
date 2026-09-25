import Mathlib
import Submission.NK.NUV2.LC.RouteB.hasseSurjTopDefs
import Submission.NK.NUV2.LC.RouteB.hasseSurjOfTopAux

/-!
# `hasseSurj_of_top`: the reduction of the Hasse surjectivity to the `⊤`-case

`NK.NUV2.LC.RouteB.HasseSurj p K K' ζ` asks for the surjectivity of the localisation
`H²(U, Z/p) → ∏_i H²(U ⊓ D_{A_i}, Z/p)` for an **open** subgroup `U ≤ Gal(K'/K)` fixing a primitive
`p`-th root of unity `ζ` and pairwise non-`U`-conjugate places `A_i`.  With `F := K'^U` this is the
classical statement that every finite family of local Brauer classes of order dividing `p` over
pairwise distinct places of `F` is realised by a global class, which is exactly the `⊤`-case of the
statement over the number field `F` — the hypothesis `HasseSurjTop p`.

The reduction is the level bookkeeping between the two colimit descriptions of `H²(U, Z/p)`:

* the global transport `HT.Phi p (trData U hUcl hUopen hsc) : H²(U, Z/p) → H²(Gal(K'/F), Z/p)` is a
  **bijection** (`HT.Phi_surjective`, `HT.Phi_injective`);
* the local transport at a place `A` (`NK.NUV2.LC.RouteB.exists_localTransport`) is an
  **injection** intertwining the localisation maps with the global transport;
* the two predicates "the places are pairwise non-`U`-conjugate" and "the places of `K'` are
  pairwise non-conjugate over `F`" agree (`not_inOrbit_top_of_not_inOrbit`).

Everything is in `Submission/Work/NUV2/LC/RouteB/hasseSurjOfTopAux.lean`:

* the fixed field `K'^U` with its number-field and separable-closure structure, the topological
  group isomorphism `↥U ≃ₜ* Gal(K'/K'^U)` (`fixedFieldCME`) and the `HT.Tr` transport data
  (`trData`) for the pair `(U, ⊤)`;
* the local group isomorphism (`localGroupEquiv`) and, in the namespace `HTO`, the **level-aligned
  local transport** `LocPhi` (injective, `HTO.LocPhi_injective`, and compatible with `HT.Phi`,
  `HTO.LocPhi_loc`), packaged as `exists_localTransport`;
* the place bookkeeping (`comap_fixedField_ne_top`, `mem_fixedField_of_le_rootFix`,
  `not_inOrbit_top_of_not_inOrbit`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Pointwise

namespace NK.NUV2.LC.RouteB

theorem hasseSurj_of_top (p : ℕ) (h : HasseSurjTop p) {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K'] (ζ : K') : HasseSurj p K K' ζ := by
  intro hp hodd hζ U hUopen hUζ ι _ A hnot
  have hUcl : IsClosed (U : Set Gal(K'/K)) := Subgroup.isClosed_of_isOpen U hUopen
  haveI hfd : FiniteDimensional K ↥(fixedFieldOf U) := finiteDimensional_fixedField U hUopen
  haveI hnf : NumberField ↥(fixedFieldOf U) :=
    NumberField.of_module_finite K ↥(fixedFieldOf U)
  haveI hsc : IsSepClosure ↥(fixedFieldOf U) K' := isSepClosure_fixedField U
  -- the places of `K'` over finite primes of the fixed field
  let P : ι → NK.BrauerHasse.OverFinitePrime ↥(fixedFieldOf U) K' :=
    fun i => ⟨(A i).1, comap_fixedField_ne_top U (A i).1 (A i).2⟩
  have hnotF : ∀ i j : ι, i ≠ j →
      ¬ InOrbit (K := ↥(fixedFieldOf U)) (K' := K')
        (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) (A i).1 (A j).1 :=
    fun i j hij => not_inOrbit_top_of_not_inOrbit U hUcl (hnot i j hij)
  have hζmem : ζ ∈ fixedFieldOf U := mem_fixedField_of_le_rootFix U ζ hUζ
  have hζF : ∃ f : ↥(fixedFieldOf U), algebraMap ↥(fixedFieldOf U) K' f = ζ :=
    ⟨⟨ζ, hζmem⟩, rfl⟩
  have hsurj := h hp hodd (F := ↥(fixedFieldOf U)) (F' := K') ζ hζ hζF ι P hnotF
  -- the local transports
  have hLT : ∀ i : ι, ∃ Φ : NK.BrauerHasse.LocalH2 (K := K) (K' := K') p U (A i).1 →
      NK.BrauerHasse.LocalH2 (K := ↥(fixedFieldOf U)) (K' := K') p ⊤ (A i).1,
      Function.Injective Φ ∧
        ∀ x : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p U,
          Φ (NK.BrauerHasse.H2Profinite.loc p U x (A i)) =
            NK.BrauerHasse.H2Profinite.loc (K := ↥(fixedFieldOf U)) (K' := K') p ⊤
              (HT.Phi p (trData U hUcl hUopen hsc) x) (P i) :=
    fun i => exists_localTransport p U hUcl hUopen (A i).1 (A i).2
  intro y
  let Φ : (i : ι) → NK.BrauerHasse.LocalH2 (K := K) (K' := K') p U (A i).1 →
      NK.BrauerHasse.LocalH2 (K := ↥(fixedFieldOf U)) (K' := K') p ⊤ (A i).1 :=
    fun i => Classical.choose (hLT i)
  have hΦinj : ∀ i : ι, Function.Injective (Φ i) :=
    fun i => (Classical.choose_spec (hLT i)).1
  have hΦnat : ∀ (i : ι) (x : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p U),
      Φ i (NK.BrauerHasse.H2Profinite.loc p U x (A i)) =
        NK.BrauerHasse.H2Profinite.loc (K := ↥(fixedFieldOf U)) (K' := K') p ⊤
          (HT.Phi p (trData U hUcl hUopen hsc) x) (P i) :=
    fun i => (Classical.choose_spec (hLT i)).2
  obtain ⟨z, hz⟩ := hsurj (fun i => Φ i (y i))
  obtain ⟨x, hx⟩ := HT.Phi_surjective p (trData U hUcl hUopen hsc) z
  refine ⟨x, funext fun i => ?_⟩
  refine hΦinj i ?_
  rw [hΦnat i x, hx]
  exact congrFun hz i

end NK.NUV2.LC.RouteB
