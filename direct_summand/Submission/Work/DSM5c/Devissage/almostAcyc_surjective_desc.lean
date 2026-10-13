import Mathlib
import Submission.Work.DSM5c.Devissage.almostAcyc_of_surjective_kernel_v2

/-!
# DSM5c — dévissage along a termwise surjection, with `I • ⊤` saturated

Let `f : K ⟶ L` be a termwise surjective map of cochain complexes of `W`-modules, let `I ⊆ W` be an
ideal such that `I • ⊤` is *saturated* along `f` (an element of `K.X q` whose image lies in
`I • ⊤ ⊆ L.X q` already lies in `I • ⊤ ⊆ K.X q`), and let `eK : W → K.X 0`, `eL : W → L.X 0` be
coaugmentations compatible through `f`.  Then `ϖ`-almost acyclicity modulo `I` descends from `K` to
`L`: `AlmostAcyc ϖ I L eL` follows from `AlmostAcyc ϖ I K eK`.

The three clauses of `DSMap.Mix2.AlmostAcyc` are transported as follows.  Writing `hchain` for the
commutation of `f` with the differentials, and using that the image of `I • ⊤` under a linear map is
again contained in `I • ⊤`:

* a class in `H⁰(L)` coming from `W` is lifted to `K` along `hsurj 0`, the cocycle condition is
  pulled back along `hchain`, and `hsat` promotes the membership in `I • ⊤` to `K`;
* a `ϖ`-multiple of a `1`-cocycle of `L` is represented in the image of `eL` by lifting the cocycle
  to `K`, applying the corresponding clause of `hK`, and pushing forward along `f`;
* similarly in degree `≥ 1`, using surjectivity in degree `q` to push forward the primitive
  supplied by `hK`.
-/

namespace Work.DSM5c.Devissage

open CategoryTheory

/-- If `f : K ⟶ L` is a termwise-surjective chain map of complexes of `W`-modules whose kernel in
degree `q` is contained in `I • ⊤`, and the ideal `I • ⊤` is saturated along `f`, then
`AlmostAcyc ϖ I` descends from `K` to `L`. -/
theorem almostAcyc_surjective_desc {W : Type*} [CommRing W] (ϖ : ℕ → W) (I : Ideal W) (K L : CochainComplex (ModuleCat W) ℕ) (f : K ⟶ L) (hsurj : ∀ q, Function.Surjective (f.f q).hom) (hsat : ∀ (q : ℕ) (x : K.X q), (f.f q).hom x ∈ I • (⊤ : Submodule W (L.X q)) → x ∈ I • (⊤ : Submodule W (K.X q))) (eK : ModuleCat.of W W ⟶ K.X 0) (eL : ModuleCat.of W W ⟶ L.X 0) (he : ∀ w : W, (f.f 0).hom (eK.hom w) = eL.hom w) (hK : DSMap.Mix2.AlmostAcyc ϖ I K eK) : DSMap.Mix2.AlmostAcyc ϖ I L eL := by
  -- the chain-map square, in `hom` form
  have hchain : ∀ {i j : ℕ} (x : K.X i),
      (f.f j).hom ((K.d i j).hom x) = (L.d i j).hom ((f.f i).hom x) := by
    intro i j x
    have h := HomologicalComplex.Hom.comm f i j
    have h2 := congrArg (fun (m : K.X i ⟶ L.X j) => m.hom x) h
    simpa only [ModuleCat.comp_apply] using h2.symm
  -- the image of `I • ⊤` under `f` is contained in `I • ⊤`
  have hmap : ∀ (q : ℕ) {x : K.X q}, x ∈ I • (⊤ : Submodule W (K.X q)) →
      (f.f q).hom x ∈ I • (⊤ : Submodule W (L.X q)) := fun q _ hx =>
    Submodule.smul_top_le_comap_smul_top I (f.f q).hom hx
  refine ⟨?_, ?_, ?_⟩
  · -- clause (1): `eL` is almost injective on `H⁰`
    intro w hw k
    exact hK.1 w (hsat 0 (eK.hom w) (by rw [he w]; exact hw)) k
  · -- clause (2): `eL` is almost surjective on `H⁰`
    intro z hz k
    obtain ⟨x, rfl⟩ := hsurj 0 z
    have hx : (K.d 0 1).hom x ∈ I • (⊤ : Submodule W (K.X 1)) :=
      hsat 1 _ (by rw [hchain (i := 0) (j := 1) x]; exact hz)
    obtain ⟨w, hw⟩ := hK.2.1 x hx k
    refine ⟨w, ?_⟩
    have hmem := hmap 0 hw
    rwa [map_sub, map_smul, he w] at hmem
  · -- clause (3): `Hᵠ` is almost zero for `q ≥ 0`
    intro q z hz k
    obtain ⟨x, rfl⟩ := hsurj (q + 1) z
    have hx : (K.d (q + 1) (q + 2)).hom x ∈ I • (⊤ : Submodule W (K.X (q + 2))) :=
      hsat (q + 2) _ (by rw [hchain (i := q + 1) (j := q + 2) x]; exact hz)
    obtain ⟨y, hy⟩ := hK.2.2 q x hx k
    refine ⟨(f.f q).hom y, ?_⟩
    have hmem := hmap (q + 1) hy
    rwa [map_sub, map_smul, hchain (i := q) (j := q + 1) y] at hmem

end Work.DSM5c.Devissage
