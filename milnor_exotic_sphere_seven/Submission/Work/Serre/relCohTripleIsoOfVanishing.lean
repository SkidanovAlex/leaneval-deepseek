import Mathlib
import Submission.Work.Serre.TripleCohLES
import Submission.Work.Thom.Cohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Relative cohomology of a triple whose pair `(T,S)` is cohomologically trivial

The file proves `Work.Serre.relCohTripleIsoOfVanishing`: if `S ⊆ T ⊆ X` and the relative
cohomology `H^k(T,S;R)` vanishes for all `k ≤ n`, then `H^n(X,T;R) ≅ H^n(X,S;R)`.

The proof is the one described in the statement: the triple gives a short exact sequence of cochain
complexes `0 → C^*(X,T) → C^*(X,S) → C^*(T,S) → 0` (`Work.Serre.tripleShortCoh_shortExact`), whose
long exact sequence reads

`… → H^{n-1}(T,S) → H^n(X,T) → H^n(X,S) → H^n(T,S) → H^{n+1}(X,T) → …`

* surjectivity of the map in degree `n` from `H^n(T,S) = 0`: exactness at `H^n(X,S)` and the fact
  that the map `H^n(X,S) → H^n(T,S)` into a zero module is zero
  (`ShortComplex.exact_iff_epi` applied to `tripleCoh_exact₂`);
* injectivity in degree `n ≥ 1` from `H^{n-1}(T,S) = 0`: exactness at `H^n(X,T)` and the fact that
  the connecting map out of a zero module is zero
  (`ShortComplex.exact_iff_mono` applied to `tripleCoh_exact₁`).

For `n = 0` there is no preceding degree, and injectivity is proved directly.  Since the complex is
indexed by `ℕ`, `H^0` of a cochain complex has no incoming differential, so `homologyπ` in degree
`0` is an isomorphism `cycles 0 ≅ homology 0` (`CochainComplex.isoHomologyπ₀`) and the square
`CochainComplex.isoHomologyπ₀_inv_naturality` identifies `homologyMap φ 0` with `cyclesMap φ 0`,
which is a monomorphism because `φ.f 0` is (the degreewise inclusion of the smaller relative
cochains).  This is the content of the auxiliary lemma `mono_homologyMap_zero_of_mono` below.
-/

open CategoryTheory CategoryTheory.Limits

set_option linter.style.haveILetI false

namespace Work.Serre

noncomputable section

/-- **Injectivity of the degree-`0` map on homology of a cochain complex indexed by `ℕ`.**  For a
morphism `φ : K ⟶ L` of `ℕ`-indexed cochain complexes whose component `φ.f 0` is a monomorphism,
the induced map `H^0(K) → H^0(L)` is a monomorphism.

There is no incoming differential in degree `0`, so the canonical map `cycles 0 → H^0` is an
isomorphism (`CochainComplex.isoHomologyπ₀`); by
`CochainComplex.isoHomologyπ₀_inv_naturality`, `homologyMap φ 0` is conjugate to
`cyclesMap φ 0`, and `cyclesMap φ 0` is a monomorphism because it is the restriction of the
monomorphism `φ.f 0` to the cycles (`HomologicalComplex.cyclesMap_i`). -/
lemma mono_homologyMap_zero_of_mono {R : Type} [CommRing R] {K L : CochainComplex (ModuleCat R) ℕ}
    (φ : K ⟶ L) (h : Mono (φ.f 0)) : Mono (HomologicalComplex.homologyMap φ 0) := by
  have hc : Mono (HomologicalComplex.cyclesMap φ 0) := by
    have h1 : Mono (HomologicalComplex.cyclesMap φ 0 ≫ L.iCycles 0) := by
      rw [HomologicalComplex.cyclesMap_i]
      exact mono_comp _ _
    exact (mono_comp_iff_of_mono _ _).mp h1
  have h2 : Mono (HomologicalComplex.homologyMap φ 0 ≫ L.isoHomologyπ₀.inv) := by
    rw [CochainComplex.isoHomologyπ₀_inv_naturality φ]
    exact mono_comp _ _
  exact (mono_comp_iff_of_mono (HomologicalComplex.homologyMap φ 0) L.isoHomologyπ₀.inv).mp h2

/-- **Relative cohomology of a triple whose pair `(T,S)` is cohomologically trivial.**  For
subsets `S ⊆ T ⊆ X` of a topological space, coefficients in a commutative ring `R`, and `n : ℕ`: if
the relative cohomology `H^k(T,S;R)` vanishes for all `k ≤ n`, then the inclusion of relative
cochain complexes `C^*(X,T) ⊆ C^*(X,S)` (whose induced map on cohomology is
`HomologicalComplex.homologyMap (Work.Serre.tripleIncl R X S T hST) n`) is an isomorphism in
degree `n`.

Route: the triple `S ⊆ T ⊆ X` gives a short exact sequence of cochain complexes
`0 → C^*(X,T) → C^*(X,S) → C^*(T,S) → 0` (`Work.Serre.tripleShortCoh_shortExact`,
`Work.Serre.tripleCohδ`), whose long exact sequence gives surjectivity of the map from the vanishing
of `H^n(T,S;R)` (via `Work.Serre.tripleCoh_exact₂_range`) and injectivity from the vanishing of
`H^{n-1}(T,S;R)` (via `Work.Serre.tripleCoh_exact₁_range`).  For `n = 0` there is no preceding
degree, and injectivity in degree `0` must be proved directly: `H^0` of a cochain complex indexed by
`ℕ` is the kernel of its differential `d^0` (`Work.Cohomology.relComplex`, ℕ-indexed with
`ComplexShape.up`), and the map on these kernels induced by a componentwise injective cochain map is
injective (`HomologicalComplex.cyclesMap`, `HomologicalComplex.homologyπ_naturality`,
`ShortComplex.asIsoHomologyπ`). -/
theorem relCohTripleIsoOfVanishing (R : Type) [CommRing R] (X : TopCat) (S T : Set X)
    (hST : S ⊆ T) (n : ℕ)
    (h : ∀ k ≤ n, Subsingleton (Work.Thom.RelCoh R k (TopCat.of T) {x : ↥T | (x : X) ∈ S})) :
    Nonempty (Work.Thom.RelCoh R n X T ≅ Work.Thom.RelCoh R n X S) := by
  have hex := tripleShortCoh_shortExact R X S T hST
  -- Surjectivity in degree `n`: the restriction `H^n(X,S) → H^n(T,S)` lands in a vanishing group,
  -- hence is zero, and `range incl = ker restr`.
  have hepi : Epi (HomologicalComplex.homologyMap (tripleIncl R X S T hST) n) := by
    have he := hex.homology_exact₂ n
    haveI : Subsingleton ↑((tripleShortCoh R X S T hST).X₃.homology n) := h n le_rfl
    have hzero : HomologicalComplex.homologyMap (tripleShortCoh R X S T hST).g n = 0 :=
      IsZero.eq_zero_of_tgt (ModuleCat.isZero_of_subsingleton _) _
    exact (ShortComplex.exact_iff_epi _ hzero).mp he
  -- Injectivity in degree `n`.
  have hmono : Mono (HomologicalComplex.homologyMap (tripleIncl R X S T hST) n) := by
    rcases n with _ | m
    · -- degree `0`: no preceding degree, use the direct argument
      haveI : Mono (tripleIncl R X S T hST) := hex.mono_f
      exact mono_homologyMap_zero_of_mono _ inferInstance
    · -- degree `m + 1`: the connecting map `H^m(T,S) → H^{m+1}(X,T)` has vanishing source
      have hrel : (ComplexShape.up ℕ).Rel m (m + 1) := by simp [ComplexShape.up]
      have he := hex.homology_exact₁ m (m + 1) hrel
      haveI : Subsingleton ↑((tripleShortCoh R X S T hST).X₃.homology m) := h m (by omega)
      have hzero : hex.δ m (m + 1) hrel = 0 :=
        IsZero.eq_zero_of_src (ModuleCat.isZero_of_subsingleton _) _
      exact (ShortComplex.exact_iff_mono _ hzero).mp he
  haveI := hmono
  haveI := hepi
  haveI : IsIso (HomologicalComplex.homologyMap (tripleIncl R X S T hST) n) :=
    isIso_of_mono_of_epi _
  exact ⟨asIso (HomologicalComplex.homologyMap (tripleIncl R X S T hST) n)⟩

end

end Work.Serre
