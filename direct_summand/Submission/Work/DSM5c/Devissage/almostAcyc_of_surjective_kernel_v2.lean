import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5c.Devissage.almostAcyc_span_pow

/-!
# DSM5c — dévissage through a surjection with kernel `(p) · ⊤` (mod-`p` variant)

This is the *mod-`p`* variant of `Work.DSM5c.Devissage.almostAcyc_of_surjective_kernel`: there the
hypothesis on `L` is honest almost acyclicity (`AlmostAcyc ϖ ⊥ L eL`), here it is almost acyclicity
*modulo* `(p)` (`AlmostAcyc ϖ (p) L eL`), and the conclusion is almost acyclicity of `K` modulo
`(p)`, which is exactly the shape in which the M5c comparison step produces its input.

The mathematical content is the same observation as in the honest variant: since `f` is termwise
surjective with kernel `(p) · ⊤`, the submodule `(p) · ⊤` is *saturated* for `f`, i.e. an element
whose image lies in `(p) · ⊤` already lies in `(p) · ⊤` (lemma
`mem_span_singleton_smul_top_of_map_mem` below).  With that in hand all three clauses of
`AlmostAcyc` transport along `f`, the coaugmentation being compatible by `he`.
-/

namespace Work.DSM5c.Devissage

open CategoryTheory

universe u

/-- **Saturation of `(p) · ⊤` along a surjection with kernel `(p) · ⊤`.**  If `g : M →ₗ[W] N` is
surjective and its kernel is exactly `(p) · ⊤ ⊆ M`, then the preimage of `(p) · ⊤ ⊆ N` is contained
in `(p) · ⊤`: an element of `M` mapping into `(p) · ⊤` already lies in `(p) · ⊤`. -/
lemma mem_span_singleton_smul_top_of_map_mem {p : ℕ} {W : Type u} [CommRing W]
    {M : Type u} [AddCommGroup M] [Module W M]
    {N : Type u} [AddCommGroup N] [Module W N]
    (g : M →ₗ[W] N) (hg : Function.Surjective g)
    (hker : ∀ x : M, g x = 0 ↔ x ∈ Ideal.span {(p : W)} • (⊤ : Submodule W M))
    (x : M) (hx : g x ∈ Ideal.span {(p : W)} • (⊤ : Submodule W N)) :
    x ∈ Ideal.span {(p : W)} • (⊤ : Submodule W M) := by
  obtain ⟨v, hv⟩ :=
    (Work.DSM5c.mem_span_singleton_smul_top (W := W) (p : W) (g x)).mp hx
  obtain ⟨v', hv'⟩ := hg v
  have hzero : g (x - (p : W) • v') = 0 := by
    rw [map_sub, map_smul, hv', hv, sub_self]
  have hmem : x - (p : W) • v' ∈ Ideal.span {(p : W)} • (⊤ : Submodule W M) :=
    (hker _).mp hzero
  have hx' : x = (x - (p : W) • v') + (p : W) • v' := by abel
  rw [hx']
  exact Submodule.add_mem _ hmem
    (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ((p : W))) Submodule.mem_top)

theorem almostAcyc_of_surjective_kernel_v2 {p : ℕ} [Fact p.Prime] {W : Type*} [CommRing W]
    (ϖ : ℕ → W) (K L : CochainComplex (ModuleCat W) ℕ) (f : K ⟶ L)
    (hsurj : ∀ q, Function.Surjective (f.f q).hom)
    (hker : ∀ (q : ℕ) (x : K.X q), (f.f q).hom x = 0 ↔ x ∈ Ideal.span {(p : W)} • (⊤ : Submodule W (K.X q)))
    (eK : ModuleCat.of W W ⟶ K.X 0) (eL : ModuleCat.of W W ⟶ L.X 0)
    (he : ∀ w : W, (f.f 0).hom (eK.hom w) = eL.hom w)
    (hL : DSMap.Mix2.AlmostAcyc ϖ (Ideal.span {(p : W)}) L eL) :
    DSMap.Mix2.AlmostAcyc ϖ (Ideal.span {(p : W)}) K eK := by
  -- the chain-map square, in `hom` form
  have hchain : ∀ {i j : ℕ} (x : K.X i),
      (f.f j).hom ((K.d i j).hom x) = (L.d i j).hom ((f.f i).hom x) := by
    intro i j x
    have h := HomologicalComplex.Hom.comm f i j
    have h2 := congrArg (fun (m : K.X i ⟶ L.X j) => m.hom x) h
    simpa only [ModuleCat.comp_apply] using h2.symm
  refine ⟨?_, ?_, ?_⟩
  · -- clause (1): `eK` is almost injective (mod `p`) on `H⁰`
    intro w hw k
    obtain ⟨v, hv⟩ :=
      (Work.DSM5c.mem_span_singleton_smul_top (W := W) (p : W) (eK.hom w)).mp hw
    have hLmem : eL.hom w ∈ Ideal.span {(p : W)} • (⊤ : Submodule W (L.X 0)) := by
      rw [← he w, ← hv, map_smul]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ((p : W))) Submodule.mem_top
    exact hL.1 w hLmem k
  · -- clause (2): `eK` is almost surjective (mod `p`) on `H⁰`
    intro z hz k
    have hzL : (L.d 0 1).hom ((f.f 0).hom z) ∈
        Ideal.span {(p : W)} • (⊤ : Submodule W (L.X 1)) := by
      rw [← hchain (i := 0) (j := 1) z]
      obtain ⟨v, hv⟩ :=
        (Work.DSM5c.mem_span_singleton_smul_top (W := W) (p : W) ((K.d 0 1).hom z)).mp hz
      rw [← hv, map_smul]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ((p : W))) Submodule.mem_top
    obtain ⟨w, hw⟩ := hL.2.1 ((f.f 0).hom z) hzL k
    refine ⟨w, ?_⟩
    exact mem_span_singleton_smul_top_of_map_mem (p := p) ((f.f 0).hom) (hsurj 0) (hker 0) _
      (by rw [map_sub, map_smul, he w]; exact hw)
  · -- clause (3): `Hᵠ` is almost zero (mod `p`) for `q ≥ 0`
    intro q z hz k
    have hzL : (L.d (q + 1) (q + 2)).hom ((f.f (q + 1)).hom z) ∈
        Ideal.span {(p : W)} • (⊤ : Submodule W (L.X (q + 2))) := by
      rw [← hchain (i := q + 1) (j := q + 2) z]
      obtain ⟨v, hv⟩ := (Work.DSM5c.mem_span_singleton_smul_top (W := W) (p : W)
        ((K.d (q + 1) (q + 2)).hom z)).mp hz
      rw [← hv, map_smul]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ((p : W))) Submodule.mem_top
    obtain ⟨yL, hyL⟩ := hL.2.2 q ((f.f (q + 1)).hom z) hzL k
    obtain ⟨y, hy⟩ := hsurj q yL
    refine ⟨y, ?_⟩
    exact mem_span_singleton_smul_top_of_map_mem (p := p) ((f.f (q + 1)).hom) (hsurj (q + 1))
      (hker (q + 1)) _
      (by rw [map_sub, map_smul, hchain (i := q) (j := q + 1) y, hy]; exact hyL)

end Work.DSM5c.Devissage
