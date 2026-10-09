import Mathlib
import Submission.Work.SSGRoute.HSRow.TransgressionDefs
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.HSRow

/-- Monotonicity of the locally constant `2`-cocycles in the subgroup: a cocycle on `D` restricts
to a cocycle on any `I ≤ D` (`c` is not changed, only the range of the cocycle condition is
shrunk). -/
lemma lcCocycles2_mono
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    {I D : Subgroup (Ω ≃ₐ[k] Ω)} (hI : I ≤ D) :
    Work.SSGRoute.lcCocycles2 p k Ω K M D ≤ Work.SSGRoute.lcCocycles2 p k Ω K M I := by
  intro c hc
  obtain ⟨h1, h2⟩ := hc
  refine ⟨?_, ?_⟩
  · intro g hg h hh l hl
    exact h1 g (hI hg) h (hI hh) l (hI hl)
  · obtain ⟨U, hUo, hU⟩ := h2
    exact ⟨U, hUo, fun g hg h hh u hu v hv huI hvI =>
      hU g (hI hg) h (hI hh) u hu v hv (hI huI) (hI hvI)⟩

/-- Every locally constant `2`-cocycle on `D` admits a *primitive* of its restriction to `I ≤ D`:
since `H²_loc(I,M') = 0` for all finite `M'` (`hvan`, instantiated at `M`, which is finite), the
restriction `c|_I` is a locally constant `2`-coboundary on `I`.  (The restriction of `c` to `I × I`
is a `2`-cocycle on `I` because `I ≤ D`; `H2loc` is a quotient of `lcCocycles2` by the
`coboundaries2`, so `Subsingleton (H2loc I M)` says every element of `lcCocycles2 I M` lies in
`coboundaries2 I M`.) -/
theorem exists_primitive
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (D I : Subgroup (Ω ≃ₐ[k] Ω)) (hI : I ≤ D)
    (hvan : ∀ (M' : Type) [AddCommGroup M'] [Module (ZMod p) M']
        [DistribMulAction (K ≃ₐ[k] K) M'] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M'] [Finite M'],
        Subsingleton (Work.SSGRoute.H2loc p k Ω K M' I))
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (hc : c ∈ Work.SSGRoute.lcCocycles2 p k Ω K M D) :
    ∃ β : (Ω ≃ₐ[k] Ω) → M, SSGRoute.IsLocConstOn I β ∧
      ∀ n ∈ I, ∀ m ∈ I, SSGRoute.res k K n • β m - β (n * m) + β n = c n m := by
  have hmemI : c ∈ Work.SSGRoute.lcCocycles2 p k Ω K M I :=
    lcCocycles2_mono p k Ω K M hI hc
  have hsub : Subsingleton (Work.SSGRoute.H2loc p k Ω K M I) := hvan M
  have hzero : (Submodule.Quotient.mk (p := Submodule.comap
      (Work.SSGRoute.lcCocycles2 p k Ω K M I).subtype
      (Work.SSGRoute.coboundaries2 p k Ω K M I)) (⟨c, hmemI⟩) :
        Work.SSGRoute.H2loc p k Ω K M I) = 0 := @Subsingleton.elim _ hsub _ _
  have hcob : c ∈ Work.SSGRoute.coboundaries2 p k Ω K M I := by
    have h := Submodule.mem_comap.mp (Submodule.Quotient.mk_eq_zero _ |>.mp hzero)
    simpa using h
  obtain ⟨β, hβloc, hβeq⟩ := hcob
  exact ⟨β, hβloc, fun n hn m hm => (hβeq n hn m hm).symm⟩


end Work.SSGRoute.HSRow
