import Mathlib
import Submission.Work.Pi6.SQM.SIG.cochainDiffPb
import Submission.Work.StemsB.serreStableExactTwo
import Submission.Work.StemsB.RelCochainDualR
import Submission.Work.StemsB.RelDualNatural
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Cohomology.DualComplexMap
import Submission.Work.StemsB.homotopyGroup_loopSpace
import Submission.Work.StemsB.pi_homeo_invariance
import Submission.Work.Cohomology.relChains_free
import Submission.Work.Pi6.SRANGE.BaseChange
import Submission.Work.Pi6.SRANGE.RelChainsBaseChange
import Submission.Work.Pi6.SRANGE.isIso_homologyMap_baseChangeMap
import Submission.Work.Pi6.SQ.evalOnePairRange
import Submission.Work.Pi6.SQ.X2.baseChangeSurjective
import Submission.Work.Pi6.SQ.fieldDualNat
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.SQ

noncomputable section

/-! ## The range of the suspension, via the Serre pair comparison

This file proves `Work.Pi6.SQ.sigmaRange`, clause (d) of `Work.Pi6.SQM.SigmaStar` for the concrete
suspension `Work.Pi6.SQM.SIG.sigma`.

The suspension is the composite `σ_n = δ⁻¹ q* ρ` of the isomorphism `ρ` (`SIG.rhoLM`, inverse to the
homology map of the inclusion of relative cochains), the pullback `q*` along the map of pairs
`(PK, ΩK) → (K, {k₀})` and the isomorphism `δ⁻¹` (`SIG.deltaInv`, inverse of the connecting map of
the pair `(PK, ΩK)`, which is an isomorphism since `PK` is contractible).  Hence the range of `σ`
is the range of `q*`.

`q*` is computed as follows.

* The relative UCT over the field `𝔽₂` (`Work.StemsB.relDualIso`, natural in the pair by
  `Work.StemsB.relDualIso_natural`) identifies `relComplex 𝔽₂ (X, A)` with the `𝔽₂`-dual of
  `relChainsR 𝔽₂ (X, A)`; it therefore conjugates `q*` into the map induced on the dual complexes
  by the *relative chain map* `Q : C_*(PK, ΩK; 𝔽₂) → C_*(K, {k₀}; 𝔽₂)`.
* The naturality of the field UCT (`Work.Pi6.SQ.fieldDualNat`) identifies the map induced by `Q` on
  the cohomology of the dual complexes with the transpose of the map induced by `Q` on homology.
* The `𝔽₂`-homology map induced by `Q` is the base change `ℤ → 𝔽₂` of the integral map induced by
  `Work.StemsB.relPairMap (evalOne K k₀) k₀` (`Work.Pi6.SRANGE.RelChainsBaseChange`): the
  isomorphisms in degrees `< 2b-1` follow from `Work.Pi6.SRANGE.isIso_homologyMap_baseChangeMap`,
  and the surjectivity in the boundary degree `2b-1` from
  `Work.Pi6.SQ.baseChangeSurjective_of_iso_below`.
* The integral input is `Work.Pi6.SQ.evalOnePairRange`: the Serre pair comparison for the
  path–loop fibration, giving an isomorphism in degrees `< b + (b-1) = 2b-1` and a surjection in
  degree `2b-1` (`b =` connectivity of `K` plus one, `b-1 =` connectivity of the fibre `ΩK` plus
  one).

Dualising (`Function.Injective` is dual to `Function.Surjective`), `q*` is bijective for
`q < 2b-1` (whence `σ_n` is bijective for `n + 2 < 2b`) and injective for `q = 2b-1` (whence `σ_n`
is injective for `n + 2 = 2b`). -/

/-! ### Small structural lemmas -/

private lemma bijective_of_isIso {M N : ModuleCat F2} (f : M ⟶ N) [IsIso f] :
    Function.Bijective f.hom :=
  ⟨(ModuleCat.mono_iff_injective f).mp inferInstance,
   (ModuleCat.epi_iff_surjective f).mp inferInstance⟩

private lemma injective_of_isIso {M N : ModuleCat F2} (f : M ⟶ N) [IsIso f] :
    Function.Injective f.hom := (bijective_of_isIso f).1

private lemma surjective_of_isIso {M N : ModuleCat F2} (f : M ⟶ N) [IsIso f] :
    Function.Surjective f.hom := (bijective_of_isIso f).2

/-- `ρ = SIG.rhoLM` is an isomorphism (it is inverse to the homology map of the inclusion of the
relative cochains). -/
private theorem bijective_rhoLM (K : Type) [TopologicalSpace K] (k₀ : K) (n : ℕ) :
    Function.Bijective (Work.Pi6.SQM.SIG.rhoLM K k₀ n).hom := by
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have h : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl F2 (TopCat.of K) ({k₀} : Set K)) (n + 2)))
          ((Work.Pi6.SQM.SIG.rhoLM K k₀ n).hom x)
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl F2 (TopCat.of K) ({k₀} : Set K)) (n + 2)))
          ((Work.Pi6.SQM.SIG.rhoLM K k₀ n).hom y) := by rw [hxy]
    rwa [Work.Pi6.SQM.SIG.relIncl_rhoLM, Work.Pi6.SQM.SIG.relIncl_rhoLM] at h
  · exact ⟨(ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl F2 (TopCat.of K) ({k₀} : Set K)) (n + 2))) z,
      Work.Pi6.SQM.SIG.rhoLM_relIncl K k₀ n z⟩

/-- `δ⁻¹ = SIG.deltaInv` is an isomorphism (it is the inverse of the composite of the connecting
map of the pair `(PK, ΩK)`, an isomorphism since `PK` is contractible, and the identification of the
fibre `fibreSet K k₀` with `ΩK = Path k₀ k₀`). -/
private theorem bijective_deltaInv (K : Type) [TopologicalSpace K] (k₀ : K) (n : ℕ) :
    Function.Bijective (Work.Pi6.SQM.SIG.deltaInv K k₀ n).hom := by
  haveI h : IsIso (Work.Pi6.SQM.SIG.deltaInv K k₀ n) := by
    rw [Work.Pi6.SQM.SIG.deltaInv]
    infer_instance
  exact bijective_of_isIso _

/-- Conjugation of a map by isomorphisms: the "middle" map of a commutative square is the
conjugate of the "outer" one.  Isomorphism/bijectivity/surjectivity/injectivity of `a` transfer
to `d` when the other two maps of the square `a ≫ b = c ≫ d` are isomorphisms. -/
private lemma bijective_of_sq {M₁ M₂ N₁ N₂ : ModuleCat F2} {a : M₁ ⟶ M₂} {b : M₂ ⟶ N₂}
    {c : M₁ ⟶ N₁} {d : N₁ ⟶ N₂} (hsq : a ≫ b = c ≫ d) [IsIso b] [IsIso c]
    (ha : Function.Bijective a.hom) : Function.Bijective d.hom := by
  have hd : d = CategoryTheory.inv c ≫ (a ≫ b) := by
    rw [hsq, ← Category.assoc, CategoryTheory.IsIso.inv_hom_id, Category.id_comp]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have h1 : (CategoryTheory.inv c ≫ (a ≫ b)).hom x
        = (CategoryTheory.inv c ≫ (a ≫ b)).hom y := by
      rw [← hd]; exact hxy
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h1
    simp only [LinearMap.comp_apply] at h1
    exact injective_of_isIso (CategoryTheory.inv c) (ha.1 (injective_of_isIso b h1))
  · intro y
    obtain ⟨w, hw⟩ := surjective_of_isIso b y
    obtain ⟨v, hv⟩ := ha.2 w
    obtain ⟨u, hu⟩ := surjective_of_isIso (CategoryTheory.inv c) v
    refine ⟨u, ?_⟩
    rw [hd, ModuleCat.hom_comp, ModuleCat.hom_comp]
    simp only [LinearMap.comp_apply]
    rw [hu, hv, hw]

private lemma injective_of_sq {M₁ M₂ N₁ N₂ : ModuleCat F2} {a : M₁ ⟶ M₂} {b : M₂ ⟶ N₂}
    {c : M₁ ⟶ N₁} {d : N₁ ⟶ N₂} (hsq : a ≫ b = c ≫ d) [IsIso b] [IsIso c]
    (ha : Function.Injective a.hom) : Function.Injective d.hom := by
  have hd : d = CategoryTheory.inv c ≫ (a ≫ b) := by
    rw [hsq, ← Category.assoc, CategoryTheory.IsIso.inv_hom_id, Category.id_comp]
  intro x y hxy
  have h1 : (CategoryTheory.inv c ≫ (a ≫ b)).hom x
      = (CategoryTheory.inv c ≫ (a ≫ b)).hom y := by
    rw [← hd]; exact hxy
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h1
  simp only [LinearMap.comp_apply] at h1
  exact injective_of_isIso (CategoryTheory.inv c) (ha (injective_of_isIso b h1))

private lemma surjective_of_sq {M₁ M₂ N₁ N₂ : ModuleCat F2} {a : M₁ ⟶ M₂} {b : M₂ ⟶ N₂}
    {c : M₁ ⟶ N₁} {d : N₁ ⟶ N₂} (hsq : a ≫ b = c ≫ d) [IsIso b] [IsIso c]
    (ha : Function.Surjective a.hom) : Function.Surjective d.hom := by
  have hd : d = CategoryTheory.inv c ≫ (a ≫ b) := by
    rw [hsq, ← Category.assoc, CategoryTheory.IsIso.inv_hom_id, Category.id_comp]
  intro y
  obtain ⟨w, hw⟩ := surjective_of_isIso b y
  obtain ⟨v, hv⟩ := ha w
  obtain ⟨u, hu⟩ := surjective_of_isIso (CategoryTheory.inv c) v
  refine ⟨u, ?_⟩
  rw [hd, ModuleCat.hom_comp, ModuleCat.hom_comp]
  simp only [LinearMap.comp_apply]
  rw [hu, hv, hw]

/-! ### The range of `q*` -/

private theorem qStar_range (K : Type) [TopologicalSpace K] (k₀ : K) (b : ℕ) (hb : 2 ≤ b)
    (hconn : ∀ i : ℕ, i < b → Subsingleton (HomotopyGroup (Fin i) K k₀)) :
    (∀ q : ℕ, q < b + (b - 1) → Function.Bijective (Work.Pi6.SQM.SIG.qStarLM K k₀ q).hom) ∧
    (Function.Injective (Work.Pi6.SQM.SIG.qStarLM K k₀ (b + (b - 1))).hom) := by
  classical
  -- the pair map `(PK, ΩK) → (K, {k₀})`
  let A : Set (Work.StemsB.PathSpace K k₀) := Work.Pi6.SQM.SIG.fibreSet K k₀
  let B : Set K := {k₀}
  let f : TopCat.of (Work.StemsB.PathSpace K k₀) ⟶ TopCat.of K :=
    TopCat.ofHom (Work.StemsB.evalOne K k₀)
  let g : TopCat.of A ⟶ TopCat.of B := Work.StemsB.fibreMap (Work.StemsB.evalOne K k₀) k₀
  have hw : Work.Cohomology.subtypeIncl (TopCat.of (Work.StemsB.PathSpace K k₀)) A ≫ f
      = g ≫ Work.Cohomology.subtypeIncl (TopCat.of K) B := by
    ext x
    exact x.2
  have hf : ∀ x ∈ A, f x ∈ B := fun x hx => hx
  -- (1) the integral Serre comparison for the path–loop fibration
  obtain ⟨hcmp, hsurj⟩ := evalOnePairRange K k₀ b hb hconn
  -- (2) base change `ℤ → 𝔽₂`
  obtain ⟨e, he⟩ := Work.Pi6.SRANGE.BaseChange F2
  obtain ⟨gB, hgB⟩ := Work.Pi6.SRANGE.RelChainsBaseChange F2 e he
  have hcompat := hgB (Work.StemsB.PathSpace K k₀) K (Work.StemsB.evalOne K k₀) k₀
  let CZ : ChainComplex (ModuleCat ℤ) ℕ :=
    Work.Cohomology.relChains (TopCat.of (Work.StemsB.PathSpace K k₀))
      ((Work.StemsB.evalOne K k₀) ⁻¹' ({k₀} : Set K))
  let DZ : ChainComplex (ModuleCat ℤ) ℕ := Work.Cohomology.relChains (TopCat.of K) ({k₀} : Set K)
  let ff : CZ ⟶ DZ := Work.StemsB.relPairMap (Work.StemsB.evalOne K k₀) k₀
  have hTF_C : ∀ i : ℕ, Module.IsTorsionFree ℤ ↥(CZ.X i) := by
    intro i
    haveI := Work.Cohomology.relChains_free (TopCat.of (Work.StemsB.PathSpace K k₀))
      ((Work.StemsB.evalOne K k₀) ⁻¹' ({k₀} : Set K)) i
    infer_instance
  have hTF_D : ∀ i : ℕ, Module.IsTorsionFree ℤ ↥(DZ.X i) := by
    intro i
    haveI := Work.Cohomology.relChains_free (TopCat.of K) ({k₀} : Set K) i
    infer_instance
  have hiso_bc : ∀ i : ℕ, i < b + (b - 1) →
      IsIso (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.baseChangeMap F2 ff) i) :=
    Work.Pi6.SRANGE.isIso_homologyMap_baseChangeMap F2 CZ DZ ff (b + (b - 1)) hTF_C hTF_D hcmp
  have hsurj_bc : Function.Surjective
      (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.baseChangeMap F2 ff) (b + (b - 1))).hom :=
    Work.Pi6.SQ.X2.baseChangeSurjective F2 ff (b + (b - 1)) hTF_C hTF_D hcmp hsurj
  have hcompatH : ∀ q : ℕ,
      HomologicalComplex.homologyMap (Work.Pi6.SRANGE.baseChangeMap F2 ff) q
          ≫ HomologicalComplex.homologyMap (gB (TopCat.of K) ({k₀} : Set K)).hom q
        = HomologicalComplex.homologyMap
            (gB (TopCat.of (Work.StemsB.PathSpace K k₀))
              ((Work.StemsB.evalOne K k₀) ⁻¹' ({k₀} : Set K))).hom q
          ≫ HomologicalComplex.homologyMap
              (Work.Pi6.SRANGE.relPairMapR F2 (Work.StemsB.evalOne K k₀) k₀) q := by
    intro q
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hcompat]
  have hQbij : ∀ q : ℕ, q < b + (b - 1) →
      Function.Bijective (HomologicalComplex.homologyMap
        (Work.Pi6.SRANGE.relPairMapR F2 (Work.StemsB.evalOne K k₀) k₀) q).hom :=
    fun q hq => by
      haveI := hiso_bc q hq
      exact bijective_of_sq (hcompatH q) (bijective_of_isIso _)
  have hQsurj : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Pi6.SRANGE.relPairMapR F2 (Work.StemsB.evalOne K k₀) k₀) (b + (b - 1))).hom :=
    surjective_of_sq (hcompatH _) hsurj_bc
  -- (3) the relative UCT over `𝔽₂`, natural in the pair
  -- the relative chain map over `𝔽₂`
  let Q : Work.StemsB.relChainsR F2 (TopCat.of (Work.StemsB.PathSpace K k₀)) A
      ⟶ Work.StemsB.relChainsR F2 (TopCat.of K) B :=
    Work.Serre.relChainsRMapOf (R := F2) (TopCat.of (Work.StemsB.PathSpace K k₀)) (TopCat.of K)
      A B f g hw
  have hnat := Work.StemsB.relDualIso_natural (R := F2)
    (X := TopCat.of (Work.StemsB.PathSpace K k₀)) (Y := TopCat.of K) A B f g hw hf
  have hnatq : ∀ q : ℕ,
      HomologicalComplex.homologyMap (Work.Cohomology.dualComplexMap F2
          (Work.StemsB.relChainsR F2 (TopCat.of (Work.StemsB.PathSpace K k₀)) A)
          (Work.StemsB.relChainsR F2 (TopCat.of K) B) Q) q
        ≫ HomologicalComplex.homologyMap
            (Work.StemsB.relDualIso F2 (TopCat.of (Work.StemsB.PathSpace K k₀)) A).hom q
      = HomologicalComplex.homologyMap
          (Work.StemsB.relDualIso F2 (TopCat.of K) B).hom q
        ≫ HomologicalComplex.homologyMap (Work.Pi6.SQM.SIG.pairMapK K k₀) q := by
    intro q
    have h := congrArg (fun φ => HomologicalComplex.homologyMap φ q) hnat
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
    exact h
  obtain ⟨Φ, hΦbij, hΦnat⟩ := fieldDualNat F2
  let CE : ChainComplex (ModuleCat F2) ℕ :=
    Work.StemsB.relChainsR F2 (TopCat.of (Work.StemsB.PathSpace K k₀)) A
  let CP : ChainComplex (ModuleCat F2) ℕ := Work.StemsB.relChainsR F2 (TopCat.of K) B
  have hdualBij : ∀ q : ℕ, Function.Bijective
      (HomologicalComplex.homologyMap Q q).hom →
      Function.Bijective (HomologicalComplex.homologyMap
        (Work.Cohomology.dualComplexMap F2 CE CP Q) q).hom := by
    intro q hQ
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have h1 := hΦnat CE CP Q q x
      have h2 := hΦnat CE CP Q q y
      have h3 : (LinearMap.dualMap (HomologicalComplex.homologyMap Q q).hom) (Φ CP q x)
          = (LinearMap.dualMap (HomologicalComplex.homologyMap Q q).hom) (Φ CP q y) := by
        rw [← h1, ← h2, hxy]
      have h4 : Φ CP q x = Φ CP q y :=
        (LinearMap.dualMap_injective_iff.mpr hQ.2) h3
      exact (hΦbij CP q).1 h4
    · intro y
      obtain ⟨w, hw'⟩ := (LinearMap.dualMap_surjective_iff.mpr hQ.1) (Φ CE q y)
      obtain ⟨x, hx⟩ := (hΦbij CP q).2 w
      refine ⟨x, ?_⟩
      have h1 := hΦnat CE CP Q q x
      rw [hx] at h1
      exact (hΦbij CE q).1 (by rw [h1, hw'])
  have hdualInj : ∀ q : ℕ, Function.Surjective
      (HomologicalComplex.homologyMap Q q).hom →
      Function.Injective (HomologicalComplex.homologyMap
        (Work.Cohomology.dualComplexMap F2 CE CP Q) q).hom := by
    intro q hQ
    intro x y hxy
    have h1 := hΦnat CE CP Q q x
    have h2 := hΦnat CE CP Q q y
    have h3 : (LinearMap.dualMap (HomologicalComplex.homologyMap Q q).hom) (Φ CP q x)
        = (LinearMap.dualMap (HomologicalComplex.homologyMap Q q).hom) (Φ CP q y) := by
      rw [← h1, ← h2, hxy]
    have h4 : Φ CP q x = Φ CP q y := (LinearMap.dualMap_injective_iff.mpr hQ) h3
    exact (hΦbij CP q).1 h4
  -- (4) assembly
  constructor
  · intro q hq
    have hbij := hdualBij q (hQbij q hq)
    have h := bijective_of_sq (hnatq q) hbij
    rw [Work.Pi6.SQM.SIG.qStarLM]
    exact h
  · have h := injective_of_sq (hnatq (b + (b - 1))) (hdualInj (b + (b - 1)) hQsurj)
    rw [Work.Pi6.SQM.SIG.qStarLM]
    exact h

/-- **Clause (d) of `Work.Pi6.SQM.SigmaStar`** for the concrete suspension `Work.Pi6.SQM.SIG.sigma`
(`σ_n := δ⁻¹ ∘ q* ∘ ρ` on the path fibration `evalOne : PK → K`, fibre `ΩK = Path k₀ k₀`):
for `K` `(b-1)`-connected (`2 ≤ b`), `σ_n` is bijective for `n + 2 < 2b` and injective for
`n + 2 = 2b` (`n ≥ 1`).  Route: `σ_n = δ⁻¹ q* ρ` with `ρ = SIG.rhoLM`, `δ = SIG.pairδ` isomorphisms
(`SIG.isIso_relIncl`, `SIG.isIso_pairδ`), so bijectivity/injectivity of `σ_n` is that of
`q* = SIG.qStarLM K k₀ (n+1)`; `q*` is the `𝔽₂`-dual (naturality of the relative UCT-with-field
duality) of the relative homology map `q_*` of the map of pairs `(PK, ΩK) → (K, {k₀})`; the latter
is an isomorphism in degrees `i < b + f` and an epimorphism in degree `b + f` for
`Work.StemsB.serrePairComparisonTwo` applied to `p = evalOne`, `b` = connectivity of `K`, `f = b-1`
(the fibre `ΩK` is `(b-2)`-connected by the loop-space shift `Work.StemsB.homotopyGroup_loopSpace`,
and `PK` is contractible), base-changed `ℤ → 𝔽₂`.  Dualising: iso for `i = n+1 < 2b-1` gives
bijectivity at `n+2 < 2b`, and epimorphism at `i = n+1 = 2b-1` gives injectivity at `n+2 = 2b`. -/
theorem sigmaRangeFinal :
    ∀ (K : Type) [TopologicalSpace K] (k₀ : K) (b : ℕ), 2 ≤ b →
      (∀ i : ℕ, i < b → Subsingleton (HomotopyGroup (Fin i) K k₀)) →
      ∀ n : ℕ, 1 ≤ n →
        (n + 2 < 2 * b → Function.Bijective (Work.Pi6.SQM.SIG.sigma K k₀ n)) ∧
        (n + 2 = 2 * b → Function.Injective (Work.Pi6.SQM.SIG.sigma K k₀ n)) := by
  intro K _ k₀ b hb hconn n hn
  obtain ⟨hqbij, hqinj⟩ := qStar_range K k₀ b hb hconn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hfun : ⇑(Work.Pi6.SQM.SIG.sigma K k₀ (m + 1))
      = ⇑(Work.Pi6.SQM.SIG.deltaInv K k₀ m).hom
        ∘ (⇑(Work.Pi6.SQM.SIG.qStarLM K k₀ (m + 2)).hom
          ∘ ⇑(Work.Pi6.SQM.SIG.rhoLM K k₀ m).hom) := by
    funext c
    rw [Work.Pi6.SQM.SIG.sigma_apply_def]
    rfl
  constructor
  · intro hlt
    have hq : m + 2 < b + (b - 1) := by omega
    rw [hfun]
    exact Function.Bijective.comp (bijective_deltaInv K k₀ m)
      (Function.Bijective.comp (hqbij (m + 2) hq) (bijective_rhoLM K k₀ m))
  · intro heq
    have hq : m + 2 = b + (b - 1) := by omega
    have hqinj' : Function.Injective (Work.Pi6.SQM.SIG.qStarLM K k₀ (m + 2)).hom := by
      rw [hq]
      exact hqinj
    rw [hfun]
    exact Function.Injective.comp (bijective_deltaInv K k₀ m).1
      (Function.Injective.comp hqinj' (bijective_rhoLM K k₀ m).1)

end

end Work.Pi6.SQ
