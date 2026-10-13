import Mathlib

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.DSEQ0.FFR

universe u

open CategoryTheory

/-- Auxiliary statement: if every finite `R`-module killed by `x` has projective
dimension `< D+1`, then so does every finite `R`-module killed by a power `x ^ K`.

The proof is by induction on `K`.  For the inductive step one uses the short exact
sequence `0 → xN → N → N/xN → 0`: the submodule `xN` is killed by `x ^ K` (hence has
small projective dimension by the induction hypothesis), while the quotient `N/xN` is
killed by `x` (hence by the hypothesis `hR'`); the bound for the middle term follows
from the long exact sequence for `Ext`. -/
private theorem pd_of_pow_isTorsionBy_aux
    (R : Type u) [CommRing R] (x : R) (D : ℕ) (T : ModuleCat.{u} R) [Module.Finite R T] (K : ℕ)
    (hT : Module.IsTorsionBy R T (x ^ K))
    (hR' : ∀ (N : ModuleCat.{u} R), Module.Finite R N → Module.IsTorsionBy R N x →
      CategoryTheory.HasProjectiveDimensionLT N (D + 1)) :
    CategoryTheory.HasProjectiveDimensionLT T (D + 1) := by
  have aux : ∀ (K : ℕ) (N : ModuleCat.{u} R), Module.Finite R N →
      Module.IsTorsionBy R N (x ^ K) →
      CategoryTheory.HasProjectiveDimensionLT N (D + 1) := by
    intro K
    induction K with
    | zero =>
      -- `x ^ 0 = 1`, so `N` is the zero module and `hR'` applies.
      intro N hN hT
      have h1 : ∀ t : ↥N, t = 0 := by
        intro t
        have := hT (x := t)
        simpa using this
      exact hR' N hN (fun t => by simp [h1 t])
    | succ K ih =>
      intro N hN hT
      haveI : Module.Finite R ↥N := hN
      -- `A` is the image `xN ⊆ N`, i.e. the range of multiplication by `x`.
      set A : Submodule R ↥N := LinearMap.range (LinearMap.lsmul R ↥N x)
      -- the short exact sequence `0 → A → N → N/A → 0`
      let S : ShortComplex (ModuleCat.{u} R) :=
        ShortComplex.mk (ModuleCat.ofHom A.subtype) (ModuleCat.ofHom A.mkQ) (by ext; simp)
      have hS : S.ShortExact :=
        ModuleCat.shortComplex_shortExact S
          (by
            show Function.Exact (⇑A.subtype) (⇑A.mkQ)
            rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype])
          A.injective_subtype
          A.mkQ_surjective
      -- `A` is finite (image of a finite module) and killed by `x ^ K`.
      have h1 : CategoryTheory.HasProjectiveDimensionLT S.X₁ (D + 1) :=
        ih S.X₁ (Module.Finite.range (LinearMap.lsmul R ↥N x)) (by
          intro y
          apply Subtype.ext
          obtain ⟨t, ht⟩ := LinearMap.mem_range.mp y.2
          show x ^ K • (y : ↥N) = 0
          rw [← ht]
          show x ^ K • (x • t) = 0
          have hkey : x ^ K • (x • t) = x ^ (K + 1) • t := by rw [pow_succ, smul_smul]
          rw [hkey]
          exact hT (x := t))
      -- `N / A` is finite (quotient of a finite module) and killed by `x`.
      have h3 : CategoryTheory.HasProjectiveDimensionLT S.X₃ (D + 1) :=
        hR' S.X₃ (Module.Finite.of_surjective A.mkQ A.mkQ_surjective) (by
          rw [Module.isTorsionBy_quotient_iff]
          intro m
          exact LinearMap.mem_range.mpr ⟨m, rfl⟩)
      exact hS.hasProjectiveDimensionLT_X₂ (D + 1) h1 h3
  exact aux K T inferInstance hT

theorem pd_of_pow_isTorsionBy (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : R) (hxm : x ∈ IsLocalRing.maximalIdeal R) (D : ℕ) (T : ModuleCat.{u} R) [Module.Finite R T] (K : ℕ) (hT : Module.IsTorsionBy R T (x ^ K)) (hR' : ∀ (N : ModuleCat.{u} R), Module.Finite R N → Module.IsTorsionBy R N x → CategoryTheory.HasProjectiveDimensionLT N (D + 1)) : CategoryTheory.HasProjectiveDimensionLT T (D + 1) :=
  pd_of_pow_isTorsionBy_aux R x D T K hT hR'

end Work.DSEQ0.FFR
