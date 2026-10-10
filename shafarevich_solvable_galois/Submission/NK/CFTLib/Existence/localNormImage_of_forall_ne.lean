import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.CFTLib.hilbertReciprocity_cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.Existence

/-- **The local–global principle for norms of idèles, away from a single place.**

For a cyclic extension `L / K` of number fields and a principal idèle `(x)_v` of `K` which is a
local norm at every place `v ≠ v₀`, the principal idèle is an idèlic norm:

`(x)_v ∈ N_{L/K} 𝕀_L`.

Equivalently (`NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm`), `x` is a local norm at *every*
place of `K`.  The hypothesis gives all places but `v₀`; the missing one is supplied by **Hilbert
reciprocity in its one-place form** — "the set of places of local-norm failure is never a
singleton" (Milne, *Class Field Theory*, VII.8.1(a), equivalently VIII.2 Example 2.2(ii)), which is
the arithmetic heart of the deliverable `NK.CFTLib.hilbertReciprocity_cyclic`.

The content is carried by:
* `NK.CFTLib.hilbertReciprocity_onePlace_aux : NK.CFTLib.HilbertReciprocityOnePlace`
  (proved in `Submission/Work/CFTLib/hilbertReciprocity_cyclic.lean`, via the cycle-free copies of
  the Brauer-transfer chain in `Submission/Work/CFTLib/HRclean/`),
* the local dictionary `NK.CFTLib.IdeleHasse.localNormSubgroup` together with
  `NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff` (`Submission/Work/CFTLib/IdeleHasse/`),
* the componentwise local–global principle for idèlic norms
  `NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm`. -/
theorem localNormImage_of_forall_ne
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hcyc : IsCyclic (L ≃ₐ[K] L))
    {x : Kˣ} {v₀ : NK.GlobalCFT.Place K}
    (h : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ → ∃ y : NK.GlobalCFT.Idele L,
      NK.GlobalCFT.Idele.principalIdele K x v = NK.GlobalCFT.Idele.normIdeleFun K L y v) :
    NK.GlobalCFT.Idele.principalIdele K x ∈ NK.GlobalCFT.Idele.normImage K L := by
  classical
  -- the component of a principal idèle is the local image of `x`
  have hconv : ∀ (u : Kˣ) (v : NK.GlobalCFT.Place K),
      NK.GlobalCFT.Idele.principalIdele K u v = NK.CFTLib.localImageHom v u := by
    intro u v
    apply Units.ext
    rw [NK.GlobalCFT.Idele.principalIdele_apply, NK.CFTLib.localImageHom_apply]
    rfl
  -- ### the local condition at every place different from `v₀`
  have hloc : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
      NK.CFTLib.localImageHom v x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v := by
    intro v hv
    obtain ⟨y, hy⟩ := h v hv
    have hmem : NK.GlobalCFT.Idele.normIdeleFun K L y v ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v :=
      NK.CFTLib.IdeleHasse.normIdeleFun_mem_localNormSubgroup (K := K) (L := L) y v
    rw [← hy] at hmem
    rwa [hconv x v] at hmem
  -- ### Hilbert reciprocity in its one-place form supplies the missing place
  have h₀ : NK.CFTLib.localImageHom v₀ x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v₀ :=
    NK.CFTLib.hilbertReciprocity_onePlace_aux (K := K) (L := L) x v₀ hloc
  -- ### the local–global principle for idèlic norms
  rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm]
  intro v
  by_cases hv : v = v₀
  · subst hv
    obtain ⟨y, hy⟩ :=
      NK.CFTLib.exists_normIdeleFun_eq_of_mem_localNormSubgroup (K := K) (L := L) h₀
    exact ⟨y, (hconv x v).trans hy⟩
  · exact h v hv

end NK.CFTLib.Existence
