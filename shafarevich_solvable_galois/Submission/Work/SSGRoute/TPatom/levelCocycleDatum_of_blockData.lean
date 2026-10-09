import Mathlib
import Submission.Work.SSGRoute.TPatom.detectionSingleBlock
import Submission.Work.SSGRoute.PTdualControl.C6_rankOneBrick
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-cocycle datum from the block-detecting Shapiro data

This file isolates the *wiring* half of the rank-one brick of node `C6`
(`Work.SSGRoute.PTdualControl.LevelCocycleDatum` for the coinduced permutation module
`coInd_N^Γ 𝔽_p`):

* the Shapiro `1`-cocycle of a character `y : ↥H →* Multiplicative 𝔽_p` of a level subgroup
  `H ≤ Gal(L/k)` is transported along the Mackey identification
  `θ : res_{galRes}(coInd_N^Γ 𝔽_p) ≅ coInd_H^{Gal(L/k)} 𝔽_p` into the coefficient module of the
  datum (here the transport is the *definition* `z γ = θ⁻¹ (ShapiroTerm y γ)`, and the cocycle
  identity is transported by linearity and equivariance of `θ⁻¹`);
* the value of `μ` on that cocycle is computed by the *proved* value formula
  `Work.SSGRoute.TPatom.shapiroValue_ne_zero_of_single_block` (single-block detection), applied to
  the transported functional `μ ∘ θ⁻¹`.

The arithmetic content — the existence of the level `L`, the place `q'`, the Frobenius element `d`,
the block system `X` and the character `y` with its single-block value conditions — is *not* here;
this file turns that arithmetic input into the datum. -/

namespace Work.SSGRoute.TPatom

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **The Shapiro `1`-cochain term of a character**, in the coinduced model
`Rep.coind H.subtype W`: the function `g ↦ y (c g γ)`.

This is the term of `Work.Sha2Lib.shapiroCocycle_mem`, factored out so that it can be named in
statements (e.g. in the inertia clause of the level-cocycle datum). -/
def shapiroTerm {Γ : Type} [Group Γ] {H : Subgroup Γ} (W : Rep.{0} SSGRoute.PTExt.Coeff ↥H)
    (htriv : ∀ (n : ↥H) (x : W.V), W.ρ n x = x)
    (c : Γ → Γ → ↥H)
    (hcoinv : ∀ (g γ : Γ) (n : ↥H), c ((n : Γ) * g) γ = c g γ)
    (y : ↥H →* Multiplicative W.V) (γ : Γ) : (Rep.coind H.subtype W).V :=
  ⟨fun g : Γ => Multiplicative.toAdd (y (c g γ)), by
    intro n g
    show Multiplicative.toAdd (y (c ((n : Γ) * g) γ))
      = W.ρ n (Multiplicative.toAdd (y (c g γ)))
    rw [hcoinv g γ n]
    exact (htriv n _).symm⟩

/-- **The Shapiro term is a `1`-cocycle** — `Work.Sha2Lib.shapiroCocycle_mem` restated for
`shapiroTerm`. -/
theorem shapiroTerm_mem_cocycles₁ {Γ : Type} [Group Γ] [Fintype Γ] {H : Subgroup Γ}
    (W : Rep.{0} SSGRoute.PTExt.Coeff ↥H)
    (htriv : ∀ (n : ↥H) (x : W.V), W.ρ n x = x)
    (c : Γ → Γ → ↥H)
    (hcmul : ∀ g γ γ' : Γ,
      ((c g (γ * γ') : ↥H) : Γ) = ((c g γ : ↥H) : Γ) * ((c (g * γ) γ' : ↥H) : Γ))
    (hcunit : ∀ g : Γ, ((c g 1 : ↥H) : Γ) = 1)
    (hcoinv : ∀ (g γ : Γ) (n : ↥H), c ((n : Γ) * g) γ = c g γ)
    (y : ↥H →* Multiplicative W.V) :
    (fun γ : Γ => shapiroTerm W htriv c hcoinv y γ) ∈
      groupCohomology.cocycles₁ (Rep.coind H.subtype W) := by
  simpa only [shapiroTerm] using
    Work.Sha2Lib.shapiroCocycle_mem W htriv c hcmul hcunit hcoinv y

/-- **A `D`-equivariant functional is trivial on the `D`-orbit of the `φ`-image**: for a linear
`G`-map `φ : A ⟶ B` and a `D`-equivariant functional `ν` on the restriction of `B`, the value of
`ν ∘ φ` at `v` equals its value at the `D`-translate of `v`.  This is the (only) equivariance
computation behind `transportedFunctional`. -/
lemma comp_apply_of_equivariant {G : Type} [Group G] {D : Subgroup G}
    {A B : Rep.{0} SSGRoute.PTExt.Coeff G} (φ : A ⟶ B)
    (ν : Rep.res D.subtype B ⟶ Work.SSGRoute.E7cOmega.divRep ↥D)
    (g : ↥D) (v : A.V) :
    ν.hom (φ.hom ((Rep.res D.subtype A).ρ g v)) = ν.hom (φ.hom v) := by
  show ν.hom (φ.hom (A.ρ (g : G) v)) = ν.hom (φ.hom v)
  calc ν.hom (φ.hom (A.ρ (g : G) v))
      = ν.hom (B.ρ (g : G) (φ.hom v)) := by
        rw [Rep.hom_comm_apply φ (g : G) v]
    _ = ν.hom ((Rep.res D.subtype B).ρ g (φ.hom v)) := rfl
    _ = (Work.SSGRoute.E7cOmega.divRep ↥D).ρ g (ν.hom (φ.hom v)) := by
        rw [Rep.hom_comm_apply ν g (φ.hom v)]
    _ = ν.hom (φ.hom v) := rfl

/-- A `D_w`-equivariant functional `μ` on `res_{D_w} M`, viewed as a functional on the restriction
of `M` to the level `L` along the ambient place compatibility `hgal`. -/
noncomputable def restrictedFunctional (p : ℕ) [Fact p.Prime] {k K L : Type} [Field k] [Field K]
    [NumberField k] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (w : NK.GlobalCFT.Place K) (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
        Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (D : Subgroup (L ≃ₐ[k] L))
    (hgal : ∀ σ : ↥D, SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L) ∈
      SSGRoute.PTExt.decompK (k := k) (K := K) w) :
    Rep.res D.subtype (Rep.res (SSGRoute.PTExt.galRes k K L) M) ⟶
      Work.SSGRoute.E7cOmega.divRep ↥D :=
  Rep.ofHom { toLinearMap := μ.hom.toLinearMap
              isIntertwining' := fun σ => LinearMap.ext (fun v => by
                show μ.hom ((Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M).ρ
                    (⟨SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L), hgal σ⟩ :
                      SSGRoute.PTExt.decompK (k := k) (K := K) w) v)
                  = (Work.SSGRoute.E7cOmega.divRep ↥D).ρ σ (μ.hom v)
                rw [Rep.hom_comm_apply μ
                  (⟨SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L), hgal σ⟩ :
                    SSGRoute.PTExt.decompK (k := k) (K := K) w) v]
                rfl) }

/-- The value of `restrictedFunctional` is that of `μ`. -/
@[simp]
lemma restrictedFunctional_apply (p : ℕ) [Fact p.Prime] {k K L : Type} [Field k] [Field K]
    [NumberField k] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (w : NK.GlobalCFT.Place K) (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
        Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (D : Subgroup (L ≃ₐ[k] L))
    (hgal : ∀ σ : ↥D, SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L) ∈
      SSGRoute.PTExt.decompK (k := k) (K := K) w)
    (v : (Rep.res (SSGRoute.PTExt.galRes k K L) M).V) :
    (restrictedFunctional p w M μ D hgal).hom v = μ.hom v := by
  simp only [restrictedFunctional, Rep.hom_ofHom, Representation.IntertwiningMap.coe_toLinearMap]
  rfl

/-- **The transported functional** `μ ∘ θ⁻¹`, a `D`-equivariant functional on the coinduced model.

`μ` is a `D_w`-equivariant functional on the coefficient module `M = coInd_N^Γ 𝔽_p` of the datum,
and `θ` is the Mackey identification of the restriction of `M` to the level `Gal(L/k)` with the
coinduced model `coInd_H^{Gal(L/k)} 𝔽_p`.  Precomposing with `θ⁻¹` gives the functional in the form
consumed by the value formula (`shapiroValue_ne_zero_of_single_block`).  The hypothesis `hgal` is
the compatibility of the place stabilizers (restriction of a stabilizer of `q'` stabilizes `w`),
which is what makes the `D`-equivariance of `μ ∘ θ⁻¹` provable. -/
noncomputable def transportedFunctional
    (p : ℕ) [Fact p.Prime] (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (w : NK.GlobalCFT.Place K)
    (N : Subgroup (K ≃ₐ[k] K)) (H : Subgroup (L ≃ₐ[k] L))
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
          (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))) ⟶
        Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (θ : Rep.res (SSGRoute.PTExt.galRes k K L)
            (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))) ≅
          Rep.coind H.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥H (ZMod p)))
    (D : Subgroup (L ≃ₐ[k] L))
    (hgal : ∀ σ : ↥D, SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L) ∈
      SSGRoute.PTExt.decompK (k := k) (K := K) w) :
    Rep.res D.subtype (Rep.coind H.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥H (ZMod p))) ⟶
      Work.SSGRoute.E7cOmega.divRep ↥D :=
  Rep.ofHom { toLinearMap := (restrictedFunctional p w
                  (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)))
                  μ D hgal).hom.toLinearMap.comp θ.inv.hom.toLinearMap
              isIntertwining' := fun σ => LinearMap.ext (fun v => by
                show (restrictedFunctional p w
                      (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)))
                      μ D hgal).hom
                    (θ.inv.hom ((Rep.res D.subtype (Rep.coind H.subtype
                      (Rep.trivial SSGRoute.PTExt.Coeff ↥H (ZMod p)))).ρ σ v))
                  = (Work.SSGRoute.E7cOmega.divRep ↥D).ρ σ
                    ((restrictedFunctional p w
                      (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)))
                      μ D hgal).hom (θ.inv.hom v))
                rw [comp_apply_of_equivariant θ.inv (restrictedFunctional p w
                  (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)))
                  μ D hgal) σ v]
                rfl) }

@[simp]
lemma transportedFunctional_apply (p : ℕ) [Fact p.Prime] (k K L : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (w : NK.GlobalCFT.Place K)
    (N : Subgroup (K ≃ₐ[k] K)) (H : Subgroup (L ≃ₐ[k] L))
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
          (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))) ⟶
        Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (θ : Rep.res (SSGRoute.PTExt.galRes k K L)
            (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))) ≅
          Rep.coind H.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥H (ZMod p)))
    (D : Subgroup (L ≃ₐ[k] L))
    (hgal : ∀ σ : ↥D, SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L) ∈
      SSGRoute.PTExt.decompK (k := k) (K := K) w)
    (v : (Rep.coind H.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥H (ZMod p))).V) :
    (transportedFunctional p k K L w N H μ θ D hgal).hom v = μ.hom (θ.inv.hom v) := by
  simp only [transportedFunctional, Rep.hom_ofHom, Representation.IntertwiningMap.coe_toLinearMap,
    LinearMap.coe_comp, Function.comp_apply, restrictedFunctional_apply]
  rfl

/-- **The level-cocycle datum from the block-detecting Shapiro data.**

This is the *wiring* half of the rank-one brick of node `C6`: given the level `L ⊇ K`, the place
`q' | q` with `p ∤ e`, the Mackey identification `θ`, the Shapiro factor `c`, the block system `X`
(partition of `Gal(L/k)` into the blocks `x d^j H`), the detecting block `x₀`, and the character
`y` of the level subgroup `H` whose values at the block elements `c x d^f` vanish for `x ≠ x₀` and
do not vanish at `x₀`, together with the `μ`-detection of the block `x₀` and the inertia clause,
the level-cocycle datum holds for `μ`.

The *arithmetic* content (existence of all this data) is the hypothesis of the caller; the point of
this file is that nothing else is needed. -/
theorem levelCocycleDatum_of_blockData
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
          (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))) ⟶
        Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    [Fintype (↥L ≃ₐ[k] ↥L)] [DecidableEq (↥L ≃ₐ[k] ↥L)]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
    (hcop : Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p)
    (H : Subgroup (↥L ≃ₐ[k] ↥L)) [H.Normal]
    (θ : Rep.res (SSGRoute.PTExt.galRes k K ↥L)
            (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))) ≅
          Rep.coind H.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥H (ZMod p)))
    (c : (↥L ≃ₐ[k] ↥L) → (↥L ≃ₐ[k] ↥L) → ↥H)
    (hcmul : ∀ g γ γ' : ↥L ≃ₐ[k] ↥L, ((c g (γ * γ') : ↥H) : ↥L ≃ₐ[k] ↥L) =
        ((c g γ : ↥H) : ↥L ≃ₐ[k] ↥L) * ((c (g * γ) γ' : ↥H) : ↥L ≃ₐ[k] ↥L))
    (hcunit : ∀ g : ↥L ≃ₐ[k] ↥L, ((c g 1 : ↥H) : ↥L ≃ₐ[k] ↥L) = 1)
    (hcoinv : ∀ (g γ : ↥L ≃ₐ[k] ↥L) (n : ↥H), c ((n : ↥L ≃ₐ[k] ↥L) * g) γ = c g γ)
    (hgal : ∀ σ : ↥(SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')),
        SSGRoute.PTExt.galRes k K ↥L (σ : ↥L ≃ₐ[k] ↥L) ∈
          SSGRoute.PTExt.decompK (k := k) (K := K) w)
    (d : ↥(SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')))
    (f : ℕ) (hf : 0 < f)
    (hdH : (((d : ↥L ≃ₐ[k] ↥L))) ^ f ∈ H)
    (X : Finset (↥L ≃ₐ[k] ↥L))
    (hpart : ∀ γ : ↥L ≃ₐ[k] ↥L, ∃! q : (↥L ≃ₐ[k] ↥L) × Fin f,
        q.1 ∈ X ∧ γ * (q.1 * ((d : ↥L ≃ₐ[k] ↥L)) ^ (q.2 : ℕ))⁻¹ ∈ H)
    (hblock : ∀ x ∈ X, ∀ δ : ↥(SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')),
        ∃ j : Fin f, (x * (δ : ↥L ≃ₐ[k] ↥L)) *
          (x * ((d : ↥L ≃ₐ[k] ↥L)) ^ (j : ℕ))⁻¹ ∈ H)
    (y : ↥H →* Multiplicative (ZMod p))
    (x₀ : ↥L ≃ₐ[k] ↥L) (hx₀ : x₀ ∈ X)
    (hinj : ∀ a : (Rep.trivial SSGRoute.PTExt.Coeff ↥H (ZMod p)).V, a ≠ 0 →
        (transportedFunctional p k K ↥L w N H μ θ
            (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
              (NK.GlobalCFT.Place.ofFinite q')) hgal).hom
          (Work.Sha2Lib.diracHom (Rep.trivial SSGRoute.PTExt.Coeff ↥H (ZMod p))
            (fun n _ a => rfl) x₀ a) ≠ 0)
    (hne : Multiplicative.toAdd (y (c x₀ (((d : ↥L ≃ₐ[k] ↥L)) ^ f))) ≠ 0)
    (hvan : ∀ x ∈ X, x ≠ x₀ →
        Multiplicative.toAdd (y (c x (((d : ↥L ≃ₐ[k] ↥L)) ^ f))) = 0)
    (hinertia : ∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
        θ.inv.hom (shapiroTerm (Rep.trivial SSGRoute.PTExt.Coeff ↥H (ZMod p))
          (fun _ _ => rfl) c hcoinv y γ) = 0) :
    Work.SSGRoute.PTdualControl.LevelCocycleDatum p k K Ω w q hwq
      (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))) μ := by
  classical
  let W : Rep.{0} SSGRoute.PTExt.Coeff ↥H :=
    Rep.trivial SSGRoute.PTExt.Coeff ↥H (ZMod p)
  have htriv : ∀ (n : ↥H) (x : W.V), W.ρ n x = x := fun n x => rfl
  let D : Subgroup (↥L ≃ₐ[k] ↥L) :=
    SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')
  have hval : (transportedFunctional p k K ↥L w N H μ θ D hgal).hom
      (shapiroTerm W htriv c hcoinv y (d : ↥L ≃ₐ[k] ↥L)) ≠ 0 := by
    refine shapiroValue_ne_zero_of_single_block (inferInstance : H.Normal) W htriv c hcmul
      hcunit hcoinv y
      D d f hf hdH X hpart hblock
      (transportedFunctional p k K ↥L w N H μ θ D hgal) x₀ hx₀ ?_ hne hvan
    intro a ha
    show (transportedFunctional p k K ↥L w N H μ θ D hgal).hom
      (Work.Sha2Lib.diracHom W (fun n _ a => rfl) x₀ a) ≠ 0
    exact hinj a ha
  have hzval : μ.hom (θ.inv.hom (shapiroTerm W htriv c hcoinv y
      (d : ↥L ≃ₐ[k] ↥L))) ≠ 0 := by
    rw [← transportedFunctional_apply p k K ↥L w N H μ θ D hgal
      (shapiroTerm W htriv c hcoinv y (d : ↥L ≃ₐ[k] ↥L))]
    exact hval
  have hzy : ∀ g g' : ↥L ≃ₐ[k] ↥L,
      shapiroTerm W htriv c hcoinv y (g * g') =
        (Rep.coind H.subtype W).ρ g (shapiroTerm W htriv c hcoinv y g') +
          shapiroTerm W htriv c hcoinv y g :=
    (groupCohomology.mem_cocycles₁_iff (A := Rep.coind H.subtype W)
      (fun γ : ↥L ≃ₐ[k] ↥L => shapiroTerm W htriv c hcoinv y γ)).mp
      (shapiroTerm_mem_cocycles₁ W htriv c hcmul hcunit hcoinv y)
  have hzmem : (fun γ : ↥L ≃ₐ[k] ↥L => θ.inv.hom (shapiroTerm W htriv c hcoinv y γ)) ∈
      groupCohomology.cocycles₁ (Rep.res (SSGRoute.PTExt.galRes k K ↥L)
        (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)))) := by
    rw [groupCohomology.mem_cocycles₁_iff]
    intro g g'
    rw [hzy g g', map_add]
    rw [Rep.hom_comm_apply θ.inv g (shapiroTerm W htriv c hcoinv y g')]
  exact ⟨L, inferInstance, inferInstance, inferInstance, q', hq', hcop,
    ⟨fun γ => θ.inv.hom (shapiroTerm W htriv c hcoinv y γ), hzmem⟩,
    fun γ hγ => hinertia γ hγ,
    (d : ↥L ≃ₐ[k] ↥L), d.2, hzval⟩

end Work.SSGRoute.TPatom
