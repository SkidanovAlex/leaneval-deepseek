import Mathlib
import Submission.Work.SSGRoute.HSTwoRow.finite_H1loc_decomp_loc
import Submission.Work.SSGRoute.PT.LocalPairingSpaces
import Submission.Work.SSGRoute.PT.finite_H1loc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A finite spanning set for the locally constant `1`-cocycles of a decomposition group

Let `k` be a number field, `Ω` an algebraic closure of `k`, `K/k` a finite Galois subextension,
`N` a finite `𝔽_p[Gal(K/k)]`-module and `A` a place of `Ω` over a finite prime of `k`.  Write
`G_k = Ω ≃ₐ[k] Ω` and `D_A = decomp k A` for the decomposition group of `A`.

The locally constant `1`-cocycles `a : G_k → N` of `D_A` (with `G_k` acting on `N` through
`res k K : G_k →* Gal(K/k)`) modulo coboundaries form the local cohomology group `H¹(D_A, N)`,
which is finite (`Work.SSGRoute.PT.finite_H1loc`).  This note extracts from that finiteness the
concrete spanning statement: there are finitely many *fixed* functions `φ i : G_k → N` such that
every locally constant cocycle of `D_A` is `∑ i, c i • φ i + z` with `c i ∈ 𝔽_p` and `z` a
coboundary.

Since `IsCoboundaryOn`, like `IsCocycleOn` and `IsLocConstOn`, only constrains the values on
`D_A`, the statement is exactly finite dimensionality of `H¹(D_A, N)`: choose `φ i` to be
cocycle representatives of a finite spanning family of the finite `𝔽_p`-vector space `H¹(D_A, N)`
and read off the coefficients through the cocycle condition, the off-`D_A` values playing no role.
-/

namespace Work.SSGRoute.PT

open Classical

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

theorem exists_finite_spanning_locCocycles (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N] [Finite N]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∃ (n : ℕ) (φ : Fin n → (Ω ≃ₐ[k] Ω) → N),
      ∀ a : (Ω ≃ₐ[k] Ω) → N,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
        ∃ (c : Fin n → ZMod p) (z : (Ω ≃ₐ[k] Ω) → N),
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) z ∧
            a = (∑ i, c i • φ i) + z := by
  classical
  -- the module of locally constant cocycles on `D_A`, realised as a submodule of `G_k → N`
  let Z : Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → N) :=
    Work.SSGRoute.lcCocycles p k Ω K N (SSGRoute.decomp k A)
  -- the coboundaries inside it; the quotient is `H1loc`
  let D : Submodule (ZMod p) ↥Z :=
    Submodule.comap Z.subtype (Work.SSGRoute.coboundaries p k Ω K N (SSGRoute.decomp k A))
  -- finiteness of the local `H¹` at the finite place `A`
  haveI hFinV : Finite (Work.SSGRoute.H1loc p k Ω K N (SSGRoute.decomp k A)) :=
    Work.SSGRoute.PT.finite_H1loc p k Ω K N A hA
  haveI hModFinV : Module.Finite (ZMod p)
      (Work.SSGRoute.H1loc p k Ω K N (SSGRoute.decomp k A)) :=
    Module.Finite.of_finite
  -- a finite family spanning the finite dimensional space `H¹(D_A, N)`
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ZMod p)
    (M := Work.SSGRoute.H1loc p k Ω K N (SSGRoute.decomp k A))
  -- lift the spanning family to locally constant cocycles
  have hsurj : Function.Surjective (Submodule.mkQ D) := Submodule.mkQ_surjective D
  let φ : Fin n → ↥Z := fun i => Classical.choose (hsurj (s i))
  have hφ : ∀ i, Submodule.mkQ D (φ i) = s i := fun i => Classical.choose_spec (hsurj (s i))
  refine ⟨n, fun i => (φ i : (Ω ≃ₐ[k] Ω) → N), ?_⟩
  intro a haCoc haLoc
  have haZ : a ∈ Z := ⟨haCoc, haLoc⟩
  -- the class of `a` is a linear combination of the `s i`
  have hmem : Submodule.mkQ D (⟨a, haZ⟩ : ↥Z) ∈ Submodule.span (ZMod p) (Set.range s) := by
    rw [hs]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p) (v := s)).mp hmem
  -- the corresponding linear combination of the lifts has the same class
  have hsum : Submodule.mkQ D (∑ i, c i • φ i) = Submodule.mkQ D (⟨a, haZ⟩ : ↥Z) := by
    have h1 : Submodule.mkQ D (∑ i, c i • φ i) = ∑ i, c i • s i := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, hφ i])
    rw [h1, hc]
  -- hence the difference is a coboundary
  have hker : (⟨a, haZ⟩ : ↥Z) - ∑ i, c i • φ i ∈ D := by
    have h0 : Submodule.mkQ D ((⟨a, haZ⟩ : ↥Z) - ∑ i, c i • φ i) = 0 := by
      rw [map_sub, hsum, sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  have hzB : a - ∑ i, c i • (φ i : (Ω ≃ₐ[k] Ω) → N) ∈
      Work.SSGRoute.coboundaries p k Ω K N (SSGRoute.decomp k A) := by
    have h := Submodule.mem_comap.mp hker
    simpa using h
  exact ⟨c, a - ∑ i, c i • (φ i : (Ω ≃ₐ[k] Ω) → N), hzB, by abel⟩

end Work.SSGRoute.PT
