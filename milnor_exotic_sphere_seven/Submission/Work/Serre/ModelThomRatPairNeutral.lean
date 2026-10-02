import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Serre.Neu.Defs
import Submission.Work.Serre.Neu.Pairing
import Submission.Work.Serre.Neu.ShufSurj
import Submission.Work.Serre.relKronEquiv
import Submission.Work.Serre.relNormalizedRep_exists
import Submission.Work.ThomBordism.finrank_bdryLQ_add_bdryKQ

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.Serre.ModelThomRatPairNeutral` -- the neutral-island local model of the Thom class

-- IMPORTANT (island constraint): this module must NOT import `Submission.Work.Serre.ratShuffle`
-- nor any module that imports it (`Work.Serre.singSSet` is declared both in
-- `Submission.Work.Serre.E0Defs` and in `Submission.Work.Serre.ratShuffle`, so a module importing
-- both does not elaborate).  This statement is the *neutral-island port* of the already proved
-- `Work.Serre.modelThomRatPair` (`Submission/Work/Serre/modelThomRatPair.lean`, which lives on the
-- ratShuffle island and therefore cannot be imported together with the CW-model chain); it is the
-- "local model" input of the cellular step `Work.Serre.thomCylCellStepAlt`.  See
-- `Submission/Work/Serre/TICFR_SESSION_NOTES.md` (FINDING 2).

## How the port is done

The two "islands" differ *only* in the name of the singular simplicial set abbreviation:
`Work.Serre.singSSet X = TopCat.toSSet.obj (TopCat.of X)` is declared twice, once in
`Serre/E0Defs.lean` and once in `Serre/ratShuffle.lean`, so no module can import both.

The modules `Submission/Work/Serre/Neu/*.lean` are verbatim copies of the ratShuffle-island files
needed by the assembly, with two mechanical changes: (i) imports of ratShuffle-island modules are
redirected to the copies, and (ii) the abbreviation `singSSet` is renamed to `singSSetN` (the same
term, `TopCat.toSSet.obj (TopCat.of X)`), so that the copies can be imported next to
`Work.Serre.E0Defs` without a name clash.  No statement or proof is changed.  The ported files are

* `Neu/Defs.lean` (copy of `ratShuffle.lean`: the shuffle chain `shufRat` and the vocabulary),
* `Neu/Pairing.lean` (copy of `pairingIdentity.lean`: `pairingIdentityScalar`),
* `Neu/ShufSurj.lean` (copy of `shufRat_surjective.lean`), with its own copies of the auxiliary
  chain `ratHypotheses`, `relEZMap`, `relPA_ratGenerator`, `BaseChangeAux`, `Surj/*`.

**Caveat.**  Because the copies keep the original declaration names (`Work.Serre.shufRat`,
`Work.Serre.relBBA_rat`, ...), this module cannot be imported in the same file as any
ratShuffle-island module -- which is exactly the island constraint above (the consumer
`Work.Serre.thomCylCellStepAlt` is on the `E0Defs` side and may not import ratShuffle).

The statement is the "local model" of the Thom class for a rationally spherical pair: for
`(P,Q)` with rational relative cohomology concentrated in degree `r+1` through degree `N+1`, and
for any base `W`, the cup product with `tau := pi_2^*(beta)` (where `beta` generates
`H^{r+1}(P,Q;Q)`) is a bijection `H^m(W;Q) -> H^{m+r+1}(W x P, W x Q;Q)` in the range.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

theorem bijective_of_pairing {H H' V V' : Type*}
    [AddCommGroup H] [Module ℚ H] [AddCommGroup H'] [Module ℚ H']
    [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']
    (e₁ : V ≃ₗ[ℚ] (H →ₗ[ℚ] ℚ)) (e₂ : V' ≃ₗ[ℚ] (H' →ₗ[ℚ] ℚ))
    (T : H →ₗ[ℚ] H') (hT : Function.Surjective T)
    (Φ : V →ₗ[ℚ] V') (hpair : ∀ (v : V) (h : H), e₂ (Φ v) (T h) = e₁ v h) :
    Function.Bijective Φ := by
  classical
  set Ψ : V' →ₗ[ℚ] V :=
    e₁.symm.toLinearMap.comp ((LinearMap.dualMap T).comp e₂.toLinearMap) with hΨ
  have hΨ_apply : ∀ w : V', Ψ w = e₁.symm ((LinearMap.dualMap T) (e₂ w)) := by
    intro w
    rw [hΨ]
    rfl
  have hΨΦ : ∀ v : V, Ψ (Φ v) = v := by
    intro v
    rw [hΨ_apply]
    have h1 : (LinearMap.dualMap T) (e₂ (Φ v)) = e₁ v := by
      ext h
      rw [LinearMap.dualMap_apply, hpair v h]
    rw [h1, LinearEquiv.symm_apply_apply]
  have hΨ_inj : Function.Injective Ψ := by
    intro a b hab
    have h2 : (LinearMap.dualMap T) (e₂ a) = (LinearMap.dualMap T) (e₂ b) :=
      e₁.symm.injective (by rw [← hΨ_apply a, ← hΨ_apply b]; exact hab)
    have h3 : e₂ a = e₂ b := by
      ext h
      obtain ⟨h₀, rfl⟩ := hT h
      have h4 := congrArg (fun (f : H →ₗ[ℚ] ℚ) => f h₀) h2
      simpa only [LinearMap.dualMap_apply] using h4
    exact e₂.injective h3
  constructor
  · intro a b hab
    have h5 : Ψ (Φ a) = Ψ (Φ b) := by rw [hab]
    rwa [hΨΦ a, hΨΦ b] at h5
  · intro w
    refine ⟨Ψ w, ?_⟩
    have h6 : Ψ (w - Φ (Ψ w)) = 0 := by
      rw [map_sub, hΨΦ (Ψ w), sub_self]
    have h7 : w - Φ (Ψ w) = 0 := hΨ_inj (by rw [h6, map_zero])
    exact (sub_eq_zero.mp h7).symm

/-- **The abstract final linear-algebra step, with a scalar.**  As `bijective_of_pairing`, but the
pairing identity carries a non-zero scalar `t`: reduce to the unscaled statement by replacing `Φ`
by `t⁻¹ • Φ`. -/
theorem bijective_of_pairing_smul {H H' V V' : Type*}
    [AddCommGroup H] [Module ℚ H] [AddCommGroup H'] [Module ℚ H']
    [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']
    (e₁ : V ≃ₗ[ℚ] (H →ₗ[ℚ] ℚ)) (e₂ : V' ≃ₗ[ℚ] (H' →ₗ[ℚ] ℚ))
    (T : H →ₗ[ℚ] H') (hT : Function.Surjective T)
    (t : ℚ) (ht : t ≠ 0)
    (Φ : V →ₗ[ℚ] V') (hpair : ∀ (v : V) (h : H), e₂ (Φ v) (T h) = t • e₁ v h) :
    Function.Bijective Φ := by
  have h' : ∀ (v : V) (h : H), e₂ ((t⁻¹ • Φ) v) (T h) = e₁ v h := by
    intro v h
    rw [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, hpair v h, smul_smul,
      inv_mul_cancel₀ ht, one_smul]
  have hbij := bijective_of_pairing e₁ e₂ T hT (t⁻¹ • Φ) h'
  constructor
  · intro a b hab
    apply hbij.1
    simp only [LinearMap.smul_apply]
    rw [hab]
  · intro y
    obtain ⟨v, hv⟩ := hbij.2 (t⁻¹ • y)
    refine ⟨v, ?_⟩
    have hv' : t⁻¹ • Φ v = t⁻¹ • y := hv
    calc Φ v = t • (t⁻¹ • Φ v) := by rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
      _ = t • (t⁻¹ • y) := by rw [hv']
      _ = y := by rw [smul_smul, mul_inv_cancel₀ ht, one_smul]

theorem pairingIdentityScalar (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P]
    (Q : Set P) (m r : ℕ)
    (α : Work.Cohomology.Cochain ℚ (Work.Serre.singSSetN W) m)
    (hα : Work.Cohomology.cochainDiff ℚ (Work.Serre.singSSetN W) α = 0)
    (b : Work.Cohomology.relKern ℚ (TopCat.of P) Q (r + 1))
    (hb : Work.Cohomology.relDiffLM ℚ (TopCat.of P) Q (r + 1) b = 0)
    (hbdeg : ∀ x ∈ (Work.Serre.singSSetN P).degenerate (r + 1),
      Work.Cohomology.genEval ℚ (Work.Serre.singSSetN P) b.1 x = 0)
    (u : ↥((Work.Cohomology.singularChains ℚ (TopCat.of W)).cycles m))
    (v : ↥((Work.Serre.relPA_rat P Q).cycles (r + 1)))
    (vt : (Work.Cohomology.singularChains ℚ (TopCat.of P)).X (r + 1))
    (hvt : (Work.StemsB.rdRProj ℚ (TopCat.of P) Q (r + 1)) vt
            = (Work.Serre.relPA_rat P Q).iCycles (r + 1) v)
    (t' : ℚ)
    (hvt1 : Work.StemsB.rdRLM ℚ (TopCat.of P) (r + 1) b.1 vt = t')
    (c : ↥((Work.Serre.relBBA_rat W P Q).cycles (m + r + 1)))
    (hc : (Work.StemsB.rdRProj ℚ (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q} (m + r + 1))
            (Work.Serre.shufRat W P m (r + 1)
              (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) vt)
          = (Work.Serre.relBBA_rat W P Q).iCycles (m + r + 1) c) :
    (Classical.choose (Work.Serre.relKronEquiv (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q}
        (m + r + 1)))
      (Work.Thom.mixedCupC ℚ {x : W × P | x.2 ∈ Q} m (r + 1)
        ((Work.Thom.CohMap (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)) ℚ m).hom
          (Work.Cohomology.cohomologyClassOf ℚ (Work.Serre.singSSetN W) α hα))
        (Work.Thom.relCohMap (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))
          {x : W × P | x.2 ∈ Q} Q (fun _ hx => hx) ℚ (r + 1)
          (Work.Cohomology.relClassOf ℚ (TopCat.of P) Q b hb)))
      ((Work.Serre.relBBA_rat W P Q).homologyπ (m + r + 1) c)
      = t' * Work.Cohomology.kronH ℚ (Work.Serre.singSSetN W) m
          (Work.Cohomology.cohomologyClassOf ℚ (Work.Serre.singSSetN W) α hα)
          ((Work.Cohomology.singularChains ℚ (TopCat.of W)).homologyπ m u) := by
  -- the two pulled-back cochains
  have hα₁c := Work.Cohomology.cochainDiff_dualMap_chainComplexMap ℚ
    (TopCat.toSSet.map (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)))) α hα
  have hb₁c := @Work.Cohomology.relDiffLM_relMapLM ℚ _ (TopCat.of (W × P)) (TopCat.of P)
    {x : W × P | x.2 ∈ Q} Q (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))) (fun _ hx => hx) (r + 1) b hb
  -- their classes
  have hcl1 : (Work.Thom.CohMap (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)) ℚ m).hom
        (Work.Cohomology.cohomologyClassOf ℚ (singSSetN W) α hα)
      = Work.Cohomology.cohomologyClassOf ℚ (singSSetN (W × P)) ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℚ (TopCat.of (W × P)) (TopCat.of W) (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)))).f m)) α) hα₁c :=
    Work.Cohomology.singularCohomologyMap_classOf ℚ (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(W × P, W))) α hα
  have hcl2 : (Work.Thom.relCohMap (⟨Prod.snd, continuous_snd⟩ : C(W × P, P)) {x : W × P | x.2 ∈ Q} Q (fun _ hx => hx) ℚ (r + 1)).hom
        (Work.Cohomology.relClassOf ℚ (TopCat.of P) Q b hb)
      = Work.Cohomology.relClassOf ℚ (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q} (Work.Cohomology.relMapLM ℚ {x : W × P | x.2 ∈ Q} Q (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))) (fun _ hx => hx) (r + 1) b) hb₁c :=
    @Work.Cohomology.homologyMap_relComplexMap_relClassOf ℚ _ (TopCat.of (W × P)) (TopCat.of P)
      {x : W × P | x.2 ∈ Q} Q (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))) (fun _ hx => hx) (r + 1) b hb
  -- the mixed cup product
  obtain ⟨hmem, hd, hcup⟩ :=
    mixedCupC_apply (R := ℚ) (B := W × P) {x : W × P | x.2 ∈ Q} m (r + 1) ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℚ (TopCat.of (W × P)) (TopCat.of W) (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)))).f m)) α) (Work.Cohomology.relMapLM ℚ {x : W × P | x.2 ∈ Q} Q (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))) (fun _ hx => hx) (r + 1) b) hα₁c hb₁c
  have hfirst : Work.Thom.mixedCupC ℚ {x : W × P | x.2 ∈ Q} m (r + 1)
        ((Work.Thom.CohMap (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)) ℚ m).hom (Work.Cohomology.cohomologyClassOf ℚ (singSSetN W) α hα))
        ((Work.Thom.relCohMap (⟨Prod.snd, continuous_snd⟩ : C(W × P, P)) {x : W × P | x.2 ∈ Q} Q (fun _ hx => hx) ℚ (r + 1)).hom
          (Work.Cohomology.relClassOf ℚ (TopCat.of P) Q b hb))
      = Work.Cohomology.relClassOf ℚ (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q}
          ⟨Work.Cohomology.cup ℚ (singSSetN (W × P)) (n := m) (m := r + 1) ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℚ (TopCat.of (W × P)) (TopCat.of W) (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)))).f m)) α) (Work.Cohomology.relMapLM ℚ {x : W × P | x.2 ∈ Q} Q (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))) (fun _ hx => hx) (r + 1) b).1, hmem⟩ hd := by
    rw [hcl1, hcl2, hcup]
  -- the chain-level Kronecker rule
  have hchain : Work.StemsB.rdRLM ℚ (TopCat.of (W × P)) (m + r + 1)
        (↑⟨Work.Cohomology.cup ℚ (singSSetN (W × P)) (n := m) (m := r + 1) ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℚ (TopCat.of (W × P)) (TopCat.of W) (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)))).f m)) α) (Work.Cohomology.relMapLM ℚ {x : W × P | x.2 ∈ Q} Q (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))) (fun _ hx => hx) (r + 1) b).1, hmem⟩ : Work.Cohomology.relKern ℚ (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q} (m + r + 1))
        (Work.Serre.shufRat W P m (r + 1) (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) vt) = α (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) * t' := by
    show Work.Cohomology.cup ℚ (singSSetN (W × P)) (n := m) (m := r + 1) ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℚ (TopCat.of (W × P)) (TopCat.of W) (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)))).f m)) α) (Work.Cohomology.relMapLM ℚ {x : W × P | x.2 ∈ Q} Q (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))) (fun _ hx => hx) (r + 1) b).1 (Work.Serre.shufRat W P m (r + 1) (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) vt) = α (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) * t'
    rw [Work.Cohomology.relMapLM_coe]
    rw [Work.Serre.cup_dualChainMap_shufRat W P m (r + 1) α b.1 hbdeg
      (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) vt]
    have hbvt : (Work.StemsB.rdRLM ℚ (TopCat.of P) (r + 1) b.1) vt = t' := hvt1
    change α (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) *
        (Work.StemsB.rdRLM ℚ (TopCat.of P) (r + 1) b.1) vt
      = α (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) * t'
    rw [hbvt]
  have hkron : Work.Cohomology.kronH ℚ (singSSetN W) m
        (Work.Cohomology.cohomologyClassOf ℚ (singSSetN W) α hα)
        ((Work.Cohomology.singularChains ℚ (TopCat.of W)).homologyπ m u) = α (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) :=
    Work.Cohomology.kronH_apply ℚ (singSSetN W) α hα u
  rw [hfirst]
  rw [relKronEquiv_apply (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q} (m + r + 1)
    ⟨Work.Cohomology.cup ℚ (singSSetN (W × P)) (n := m) (m := r + 1) ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℚ (TopCat.of (W × P)) (TopCat.of W) (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)))).f m)) α) (Work.Cohomology.relMapLM ℚ {x : W × P | x.2 ∈ Q} Q (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))) (fun _ hx => hx) (r + 1) b).1, hmem⟩ hd c (Work.Serre.shufRat W P m (r + 1) (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) vt) hc]
  rw [hchain, hkron]
  exact mul_comm _ _

/-- **The local model of the Thom class for a rationally spherical pair, on the neutral island.**
For a pair `(P,Q)` whose rational relative cohomology is concentrated in degree `r+1` through
degree `N+1` (`H^n(P,Q;ℚ) = 0` for `0 < n ≤ N+1, n ≠ r+1`, `H^0(P,Q;ℚ) = 0`, and
`H^{r+1}(P,Q;ℚ) ≅ ℚ`) and for **any** base `W`, there is `τ ∈ H^{r+1}(W×P, W×Q;ℚ)` for which the
cup product `x ↦ π^*(x) ⌣ τ` is a bijection `H^m(W;ℚ) → H^{m+r+1}(W×P, W×Q;ℚ)` for every
`m` with `m + r + 1 ≤ N + 1`. -/
theorem ModelThomRatPairNeutral {P : Type} [TopologicalSpace P] (Q : Set P) (r N : ℕ)
    (hvan : ∀ n : ℕ, 0 < n → n ≤ N + 1 → n ≠ r + 1 →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ n P Q))
    (hzero : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ 0 P Q))
    (hgen : Nonempty (Work.Thom.RelCoh ℚ (r + 1) P Q ≅ ModuleCat.of ℚ ℚ))
    (W : Type) [TopologicalSpace W] :
    ∃ τ : Work.Thom.RelCoh ℚ (r + 1) (W × P) {x : W × P | x.2 ∈ Q},
      ∀ m : ℕ, m + r + 1 ≤ N + 1 →
        Function.Bijective (fun x : Work.Thom.Coh ℚ m W =>
          ((Work.Thom.mixedCupC ℚ {x : W × P | x.2 ∈ Q} m (r + 1)).flip τ)
            ((Work.Thom.CohMap (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)) ℚ m).hom x)) := by
  classical
  let AA : Set (W × P) := {x : W × P | x.2 ∈ Q}
  obtain ⟨v₀, vt₀, hvt₀, hgen₀, hT⟩ :=
    Work.Serre.shufRat_surjective W P Q r N hvan hzero hgen
  let iso := hgen.some
  let β : ↥(Work.Thom.RelCoh ℚ (r + 1) P Q) := iso.toLinearEquiv.symm 1
  have hβne : β ≠ 0 := by
    intro h
    have h1 : (1 : ℚ) = 0 := by
      have hh := congrArg (⇑iso.toLinearEquiv) h
      simpa [β] using hh
    exact one_ne_zero h1
  obtain ⟨b, hb, hbdeg, hbclass⟩ :=
    Work.Serre.relNormalizedRep_exists (TopCat.of P) Q (r + 1) β
  set t : ℚ := Work.StemsB.rdRLM ℚ (TopCat.of P) (r + 1) b.1 vt₀ with htdef
  set eP := Classical.choose (Work.Serre.relKronEquiv (TopCat.of P) Q (r + 1)) with heP
  have hev : eP β ((Work.Serre.relPA_rat P Q).homologyπ (r + 1) v₀) = t := by
    have hh := Classical.choose_spec (Work.Serre.relKronEquiv (TopCat.of P) Q (r + 1))
      b hb v₀ vt₀ hvt₀
    rw [hbclass] at hh
    rw [htdef]
    exact hh
  have ht0 : t ≠ 0 := by
    intro h0
    have h2 : eP β = 0 := by
      apply LinearMap.ext
      intro w
      obtain ⟨q, hq⟩ := hgen₀ w
      rw [hq, map_smul, hev, h0, smul_zero, LinearMap.zero_apply]
    have hβ0 : β = 0 := by
      have hh := congrArg (⇑eP.symm) h2
      simpa using hh
    exact hβne hβ0
  set τ : ↥(Work.Thom.RelCoh ℚ (r + 1) (W × P) AA) :=
    (Work.Thom.relCohMap (⟨Prod.snd, continuous_snd⟩ : C(W × P, P)) AA Q
      (fun _ hx => hx) ℚ (r + 1)).hom
      (Work.Cohomology.relClassOf ℚ (TopCat.of P) Q b hb) with hτ
  refine ⟨τ, fun m hm => ?_⟩
  obtain ⟨T, hTsurj, hTdesc⟩ := hT m hm
  set e₂ : ↥(Work.Thom.RelCoh ℚ (m + r + 1) (W × P) AA) ≃ₗ[ℚ]
      (↥((Work.Serre.relBBA_rat W P Q).homology (m + r + 1)) →ₗ[ℚ] ℚ) :=
    Classical.choose (Work.Serre.relKronEquiv (TopCat.of (W × P)) AA (m + r + 1)) with he₂
  set e₁ : ↥((Work.Cohomology.cochainC ℚ (Work.Serre.singSSetN W)).homology m) ≃ₗ[ℚ]
      (↥((Work.Cohomology.chainC ℚ (Work.Serre.singSSetN W)).homology m) →ₗ[ℚ] ℚ) :=
    LinearEquiv.ofBijective (Work.Cohomology.kronH ℚ (Work.Serre.singSSetN W) m)
      ((⟨Work.ThomBordism.kronHRatInjective (Work.Serre.singSSetN W) m,
         Work.ThomBordism.kronHRatSurjective (Work.Serre.singSSetN W) m⟩ :
          Function.Injective (Work.Cohomology.kronH ℚ (Work.Serre.singSSetN W) m) ∧
            Function.Surjective (Work.Cohomology.kronH ℚ (Work.Serre.singSSetN W) m)) :
        Function.Bijective (Work.Cohomology.kronH ℚ (Work.Serre.singSSetN W) m)) with he₁
  have hpair : ∀ (x : ↥((Work.Cohomology.cochainC ℚ (Work.Serre.singSSetN W)).homology m))
      (y : ↥((Work.Cohomology.chainC ℚ (Work.Serre.singSSetN W)).homology m)),
      e₂ (((Work.Thom.mixedCupC ℚ AA m (r + 1)).flip τ)
            ((Work.Thom.CohMap (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)) ℚ m).hom x))
          (T.hom y) = t • e₁ x y := by
    intro x y
    obtain ⟨α, hα, hαx⟩ :=
      Work.Cohomology.exists_cohomologyClassOf ℚ (Work.Serre.singSSetN W) m x
    obtain ⟨u, hu⟩ := (ModuleCat.epi_iff_surjective
      ((Work.Cohomology.singularChains ℚ (TopCat.of W)).homologyπ m)).mp inferInstance y
    obtain ⟨c₀, hc₀, hTc₀⟩ := hTdesc u
    have hTy : T.hom y = (Work.Serre.relBBA_rat W P Q).homologyπ (m + r + 1) c₀ := by
      rw [← hu, hTc₀]
    have hpairI := Work.Serre.pairingIdentityScalar W P Q m r α hα b hb hbdeg u v₀ vt₀ hvt₀
      t htdef.symm c₀ hc₀
    rw [he₂, he₁, LinearEquiv.ofBijective_apply]
    rw [hTy, hτ]
    simp only [← hαx, ← hu, smul_eq_mul]
    exact hpairI
  have hbij := Work.Serre.bijective_of_pairing_smul e₁ e₂ T.hom hTsurj t ht0
    (((Work.Thom.mixedCupC ℚ AA m (r + 1)).flip τ).comp
      (Work.Thom.CohMap (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)) ℚ m).hom) hpair
  change Function.Bijective (⇑(((Work.Thom.mixedCupC ℚ AA m (r + 1)).flip τ).comp
    (Work.Thom.CohMap (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)) ℚ m).hom))
  exact hbij


end

end Work.Serre
