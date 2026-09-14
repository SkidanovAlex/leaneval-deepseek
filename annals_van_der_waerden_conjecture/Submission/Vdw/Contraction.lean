import Mathlib
import Submission.Vdw.SplittingField
import Submission.Vdw.Embeddings
import Submission.Vdw.GaloisTower
import Submission.Commons.Data.Set.ncard_eq_natCard
import Submission.Commons.GroupTheory.GroupAction.ncard_smul_preimage

open Polynomial
open scoped NumberField Pointwise

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

/-!
# Contraction of primes through embeddings (backbone of the (c) fiber lemma)

For the inertia/orbit analysis of step (c) one needs the prime of
`K_p = ℚ[x]/(p)` under a prime `𝔓` of the splitting field `L = p.SplittingField`,
taken through an embedding `σ : K_p ↪ L`.  This module provides that
object, in the clean "pullback along the induced map of Dedekind domains"
form:

* `intRingMap σ` — the induced ring homomorphism `𝓞 K_p →+* 𝓞 L`
  (an embedding maps algebraic integers to algebraic integers,
  `IsIntegral.map`);
* `pullbackIdeal σ 𝔓 := Ideal.comap (intRingMap σ) 𝔓` — the contraction,
  with the explicit description `x ∈ pullbackIdeal σ 𝔓 ↔ σ x ∈ 𝔓`;
* `pullbackIdeal_isPrime` / `pullbackIdeal_liesOver` — the contraction is a
  prime ideal of `𝓞 K_p` lying over `p` whenever `𝔓` does.

Everything is stated for irreducible `p : ℚ[X]` (`[Fact (Irreducible p)]`),
with `K_p = AdjoinRoot p`.
-/

namespace Submission.Vdw

noncomputable section

open Polynomial

/-- An embedding `K_p ↪ L` of number fields maps `𝓞 K_p` into `𝓞 L`
(algebraic integers map to algebraic integers: `IsIntegral.map`). -/
noncomputable def intRingMap (p : ℚ[X]) [Fact (Irreducible p)]
    (σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField) :
    𝓞 (AdjoinRoot p) →+* 𝓞 p.SplittingField where
  toFun x := ⟨σ (x : AdjoinRoot p), IsIntegral.map σ x.2⟩
  map_one' := by
    apply Subtype.ext
    change σ ((1 : AdjoinRoot p)) = (1 : p.SplittingField)
    exact map_one σ
  map_mul' x y := by
    apply Subtype.ext
    change σ ((x : AdjoinRoot p) * (y : AdjoinRoot p)) =
      σ (x : AdjoinRoot p) * σ (y : AdjoinRoot p)
    exact map_mul σ (x : AdjoinRoot p) (y : AdjoinRoot p)
  map_zero' := by
    apply Subtype.ext
    change σ ((0 : AdjoinRoot p)) = (0 : p.SplittingField)
    exact map_zero σ
  map_add' x y := by
    apply Subtype.ext
    change σ ((x : AdjoinRoot p) + (y : AdjoinRoot p)) =
      σ (x : AdjoinRoot p) + σ (y : AdjoinRoot p)
    exact map_add σ (x : AdjoinRoot p) (y : AdjoinRoot p)

/-- The contraction of `𝔓` through `σ`: the prime of `𝓞 K_p` consisting of
the integral elements whose image under `σ` lies in `𝔓`. -/
noncomputable def pullbackIdeal (p : ℚ[X]) [Fact (Irreducible p)]
    (σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField) (𝔓 : Ideal (𝓞 p.SplittingField)) :
    Ideal (𝓞 (AdjoinRoot p)) :=
  Ideal.comap (intRingMap p σ) 𝔓

/-- Explicit membership: `x ∈ pullbackIdeal σ 𝔓` iff `σ x ∈ 𝔓`. -/
theorem mem_pullbackIdeal (p : ℚ[X]) [Fact (Irreducible p)]
    (σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField) (𝔓 : Ideal (𝓞 p.SplittingField))
    (x : 𝓞 (AdjoinRoot p)) :
    x ∈ pullbackIdeal p σ 𝔓 ↔ (intRingMap p σ x : 𝓞 p.SplittingField) ∈ 𝔓 := by
  rfl

end

/-- The pullback of a prime ideal is prime (comap of a prime under a ring
homomorphism). -/
theorem pullbackIdeal_isPrime (p : ℚ[X]) [Fact (Irreducible p)]
    (σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField) {𝔓 : Ideal (𝓞 p.SplittingField)}
    (h𝔓 : 𝔓.IsPrime) : (pullbackIdeal p σ 𝔓).IsPrime := by
  classical
  haveI : 𝔓.IsPrime := h𝔓
  exact Ideal.IsPrime.comap (intRingMap p σ)

/-- The induced map on integer rings is the identity on the integers:
`intRingMap σ` commutes with the maps from `ℤ` (an embedding fixes `ℚ`,
hence the integers). -/
theorem intRingMap_comp_algebraMap (p : ℚ[X]) [Fact (Irreducible p)]
    (σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField) :
    (intRingMap p σ).comp (algebraMap ℤ (𝓞 (AdjoinRoot p))) =
      algebraMap ℤ (𝓞 p.SplittingField) := by
  apply RingHom.ext
  intro z
  apply Subtype.ext
  change σ ((algebraMap ℤ (AdjoinRoot p)) z) = (algebraMap ℤ p.SplittingField) z
  calc
    σ ((algebraMap ℤ (AdjoinRoot p)) z) =
        σ ((algebraMap ℚ (AdjoinRoot p)) (z : ℚ)) := by
          simp
    _ = (algebraMap ℚ p.SplittingField) (z : ℚ) := σ.commutes (z : ℚ)
    _ = (algebraMap ℤ p.SplittingField) z := by
      simp

/-- **Contraction lies over `p`.**  If `𝔓` is a prime of `𝒪_L` over `p`,
then its pullback through any embedding is a prime of `𝒪 K_p` over `p`. -/
theorem pullbackIdeal_liesOver (p : ℚ[X]) [Fact (Irreducible p)]
    (σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField) (p0 : ℕ) (hp0 : Nat.Prime p0)
    {𝔓 : Ideal (𝓞 p.SplittingField)}
    (h𝔓 : 𝔓.LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ))) :
    (pullbackIdeal p σ 𝔓).LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ)) := by
  classical
  haveI : 𝔓.LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ)) := h𝔓
  constructor
  rw [Ideal.under_def, pullbackIdeal, Ideal.comap_comap]
  rw [intRingMap_comp_algebraMap p σ]
  rw [← Ideal.under_def]
  exact Ideal.over_def 𝔓 (Ideal.span ({(p0 : ℤ)} : Set ℤ))


/-- The ring of integers of `L` as an algebra over the ring of integers of
`K_p`, via the canonical embedding (an `Algebra` for use in tower
ramification statements over `𝓞 K_p → 𝓞 L`).  (Plain definition — its
parameters prevent global registration; use `letI`.) -/
noncomputable def intRingAlgebra (p : ℚ[X]) [Fact (Irreducible p)] :
    Algebra (𝓞 (AdjoinRoot p)) (𝓞 p.SplittingField) :=
  RingHom.toAlgebra (intRingMap p (kpolyAlgEmb p))


section TowerLemmas

/-- **Tower for `ramificationIdx` over `𝓞 K_p → 𝓞 L`.**  For `Q` a prime of
`𝓞 K_p` over `p0` and `𝔓` a prime of `𝒪 L` over `Q`:
`e(𝔓/ℚ) = e(Q/ℚ) · e(𝔓/Q)`.  (Assembled from the prime-based tower
`Ideal.ramificationIdx'_algebra_tower'` + the old/new translation
`Ideal.ramificationIdx'_eq_ramificationIdx`; the algebra/scalar-tower/
torsion-free instances are parameters, instantiated by `intRingAlgebra p`
at use.) -/
theorem ramificationIdx_tower_intRing (p : ℚ[X]) [Fact (Irreducible p)]
    [Algebra (𝓞 (AdjoinRoot p)) (𝓞 p.SplittingField)]
    [IsScalarTower ℤ (𝓞 (AdjoinRoot p)) (𝓞 p.SplittingField)]
    [Module.IsTorsionFree (𝓞 (AdjoinRoot p)) (𝓞 p.SplittingField)]
    (p0 : ℕ) (hp0 : Nat.Prime p0)
    (Q : Ideal (𝓞 (AdjoinRoot p))) [Q.IsPrime]
    [Q.LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ))]
    (𝔓 : Ideal (𝓞 p.SplittingField)) [𝔓.IsPrime]
    [𝔓.LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ))] [𝔓.LiesOver Q] :
    𝔓.ramificationIdx ℤ = Q.ramificationIdx ℤ * 𝔓.ramificationIdx (𝓞 (AdjoinRoot p)) := by
  classical
  let pZ : Ideal ℤ := Ideal.span ({(p0 : ℤ)} : Set ℤ)
  have hp0z : (p0 : ℤ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero hp0)
  have hpZ : pZ ≠ ⊥ := by
    dsimp [pZ]
    intro h
    exact hp0z (Ideal.span_singleton_eq_bot.mp h)
  have hQbot : Q ≠ ⊥ := by
    -- Q lies over the nonzero ideal pZ, so Q ≠ ⊥
    exact Ideal.ne_bot_of_liesOver_of_ne_bot hpZ Q
  have h := Ideal.ramificationIdx'_algebra_tower' (R := ℤ) (S := 𝓞 (AdjoinRoot p))
    (T := 𝓞 p.SplittingField) pZ Q 𝔓
  -- h : pZ.ramificationIdx' 𝔓 = pZ.ramificationIdx' Q * Q.ramificationIdx' 𝔓
  have h1 : pZ.ramificationIdx' 𝔓 = 𝔓.ramificationIdx ℤ := by
    exact Ideal.ramificationIdx'_eq_ramificationIdx (R := ℤ) (S := 𝓞 p.SplittingField)
      (p := pZ) (q := 𝔓) hpZ
  have h2 : pZ.ramificationIdx' Q = Q.ramificationIdx ℤ := by
    exact Ideal.ramificationIdx'_eq_ramificationIdx (R := ℤ) (S := 𝓞 (AdjoinRoot p))
      (p := pZ) (q := Q) hpZ
  have h3 : Q.ramificationIdx' 𝔓 = 𝔓.ramificationIdx (𝓞 (AdjoinRoot p)) := by
    exact Ideal.ramificationIdx'_eq_ramificationIdx (R := 𝓞 (AdjoinRoot p))
      (S := 𝓞 p.SplittingField) (p := Q) (q := 𝔓) hQbot
  calc
    𝔓.ramificationIdx ℤ = pZ.ramificationIdx' 𝔓 := h1.symm
    _ = pZ.ramificationIdx' Q * Q.ramificationIdx' 𝔓 := h
    _ = Q.ramificationIdx ℤ * 𝔓.ramificationIdx (𝓞 (AdjoinRoot p)) := by rw [h2, h3]

/-- **Tower for `inertiaDeg` over `𝓞 K_p → 𝓞 L`.**  For `Q` a prime of
`𝓞 K_p` over `p0` and `𝔓` a prime of `𝒪 L` over `Q`:
`f(𝔓/ℚ) = f(Q/ℚ) · f(𝔓/Q)`.  (Direct from `Ideal.inertiaDeg_tower` —
no flatness needed.) -/
theorem inertiaDeg_tower_intRing (p : ℚ[X]) [Fact (Irreducible p)]
    [Algebra (𝓞 (AdjoinRoot p)) (𝓞 p.SplittingField)]
    [IsScalarTower ℤ (𝓞 (AdjoinRoot p)) (𝓞 p.SplittingField)]
    (p0 : ℕ) (_hp0 : Nat.Prime p0)
    (Q : Ideal (𝓞 (AdjoinRoot p))) [Q.IsPrime]
    [Q.LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ))]
    (𝔓 : Ideal (𝓞 p.SplittingField)) [𝔓.IsPrime]
    [𝔓.LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ))] [𝔓.LiesOver Q] :
    𝔓.inertiaDeg ℤ = Q.inertiaDeg ℤ * 𝔓.inertiaDeg (𝓞 (AdjoinRoot p)) := by
  classical
  exact Ideal.inertiaDeg_tower (R := ℤ) (S := 𝓞 (AdjoinRoot p)) (T := 𝓞 p.SplittingField) Q 𝔓

end TowerLemmas

section PullbackGalois

/-- The ring endomorphism of `𝒪 L` induced by an automorphism `g` of `L`. -/
noncomputable def galIntMap (p : ℚ[X]) [Fact (Irreducible p)] (g : p.Gal) :
    𝓞 p.SplittingField →+* 𝓞 p.SplittingField where
  toFun y := ⟨g (y : p.SplittingField), IsIntegral.map (g.toAlgHom) y.2⟩
  map_one' := by
    apply Subtype.ext
    change g ((1 : p.SplittingField)) = (1 : p.SplittingField)
    exact map_one g.toAlgHom
  map_mul' x y := by
    apply Subtype.ext
    change g ((x : p.SplittingField) * (y : p.SplittingField)) =
      g (x : p.SplittingField) * g (y : p.SplittingField)
    exact map_mul g.toAlgHom (x : p.SplittingField) (y : p.SplittingField)
  map_zero' := by
    apply Subtype.ext
    change g ((0 : p.SplittingField)) = (0 : p.SplittingField)
    exact map_zero g.toAlgHom
  map_add' x y := by
    apply Subtype.ext
    change g ((x : p.SplittingField) + (y : p.SplittingField)) =
      g (x : p.SplittingField) + g (y : p.SplittingField)
    exact map_add g.toAlgHom (x : p.SplittingField) (y : p.SplittingField)

/-- `intRingMap` of the composed embedding `g ∘ ι` is the composition of the
induced maps: `intRingMap (g·ι) = galIntMap g ∘ intRingMap ι`. -/
theorem intRingMap_galSmulEmb (p : ℚ[X]) [Fact (Irreducible p)] (g : p.Gal) :
    intRingMap p (galSmulEmb p g (kpolyAlgEmb p)) =
      (galIntMap p g).comp (intRingMap p (kpolyAlgEmb p)) := by
  ext x
  rfl

/-- **Pullback through `g · ι`.**  For `σ = g·ι` and a prime `𝔓` of
`𝒪 L`, the contraction of `𝔓` through `σ` equals the contraction through
`ι` of the preimage ideal `g⁻¹(𝔓) = {y | g y ∈ 𝔓}`.  (This is the
`pullback (g·ι) 𝔓 = g⁻¹𝔓-over-ι(Q)` hinge of the fiber count: it reduces
counting embeddings with `pullbackIdeal σ 𝔓 = Q` to counting `g` with the
preimage ideal over `ι(Q)`.) -/
theorem pullbackIdeal_galSmulEmb (p : ℚ[X]) [Fact (Irreducible p)] (g : p.Gal)
    (𝔓 : Ideal (𝓞 p.SplittingField)) :
    pullbackIdeal p (galSmulEmb p g (kpolyAlgEmb p)) 𝔓 =
      pullbackIdeal p (kpolyAlgEmb p) (Ideal.comap (galIntMap p g) 𝔓) := by
  classical
  rw [pullbackIdeal, pullbackIdeal, Ideal.comap_comap]
  exact congrArg (fun h : 𝓞 (AdjoinRoot p) →+* 𝓞 p.SplittingField => Ideal.comap h 𝔓)
    (intRingMap_galSmulEmb p g)

end PullbackGalois


/-- **Contraction equals `Q` iff `𝔓'` lies over `Q`.**  In the extension of
Dedekind domains `𝓞 K_p → 𝒪 L` (the algebra `intRingAlgebra p`, whose
structure map is `intRingMap ι`), the contraction of a prime `𝔓'` of
`𝒪 L` through the canonical embedding `ι` is `Q` exactly when `𝔓'` lies
over `Q`, i.e. `𝔓'.under (𝓞 (AdjoinRoot p)) = Q`. -/
theorem pullbackIdeal_eq_iff_under (p : ℚ[X]) [Fact (Irreducible p)]
    [Algebra (𝓞 (AdjoinRoot p)) (𝓞 p.SplittingField)]
    (halg : (algebraMap (𝓞 (AdjoinRoot p)) (𝓞 p.SplittingField)) =
      intRingMap p (kpolyAlgEmb p))
    (𝔓' : Ideal (𝓞 p.SplittingField)) (Q : Ideal (𝓞 (AdjoinRoot p))) :
    pullbackIdeal p (kpolyAlgEmb p) 𝔓' = Q ↔
      𝔓'.under (𝓞 (AdjoinRoot p)) = Q := by
  classical
  rw [pullbackIdeal, ← halg, Ideal.under_def]


/-- The pullback condition depends only on the stabilizer coset of `g`:
if `g` and `g'` differ by an element of the stabilizer `embStabilizer p`
(`g⁻¹·g' ∈ H`) then `pullbackIdeal (g·ι) 𝔓 = pullbackIdeal (g'·ι) 𝔓`. -/
theorem pullbackIdeal_coset_invariant (p : ℚ[X]) [Fact (Irreducible p)]
    (g g' : p.Gal) (𝔓 : Ideal (𝓞 p.SplittingField))
    (hdiff : g⁻¹ * g' ∈ embStabilizer p) :
    pullbackIdeal p (galSmulEmb p g (kpolyAlgEmb p)) 𝔓 =
      pullbackIdeal p (galSmulEmb p g' (kpolyAlgEmb p)) 𝔓 := by
  classical
  have h : galSmulEmb p (g * (g⁻¹ * g')) (kpolyAlgEmb p) =
      galSmulEmb p g (kpolyAlgEmb p) := by
    rw [galSmulEmb_mul p g (g⁻¹ * g') (kpolyAlgEmb p)]
    rw [(mem_embStabilizer p (g⁻¹ * g')).mp hdiff]
  have hσ : galSmulEmb p g (kpolyAlgEmb p) = galSmulEmb p g' (kpolyAlgEmb p) := by
    calc
      galSmulEmb p g (kpolyAlgEmb p) =
          galSmulEmb p (g * (g⁻¹ * g')) (kpolyAlgEmb p) := h.symm
      _ = galSmulEmb p g' (kpolyAlgEmb p) := by
        congr 1
        rw [← mul_assoc, mul_inv_cancel, one_mul]
  rw [hσ]

section CosetCounting

/-- The orbit of the canonical embedding: `{σ | ∃ g, g·ι = σ}` equals all
embeddings (every embedding is `g·ι`, `Embeddings.exists_gal_of_embedding`). -/
theorem orbit_of_canonical_eq_univ (p : ℚ[X]) [Fact (Irreducible p)] :
    {σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField | ∃ g : p.Gal, galSmulEmb p g (kpolyAlgEmb p) = σ}
      = Set.univ := by
  ext σ
  constructor
  · intro h
    trivial
  · intro h
    exact exists_gal_of_embedding p σ

/-- For an embedding `σ = g₀·ι` in the orbit, the fiber `{g | g·ι = σ}` is
in bijection with the stabilizer `embStabilizer p`. -/
noncomputable def fiberEquivStabilizer (p : ℚ[X]) [Fact (Irreducible p)]
    (σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField)
    (hx : ∃ g : p.Gal, galSmulEmb p g (kpolyAlgEmb p) = σ) :
    {g : p.Gal // galSmulEmb p g (kpolyAlgEmb p) = σ} ≃ (embStabilizer p : Type _) := by
  classical
  let g₀ : p.Gal := Classical.choose hx
  have hg₀ : galSmulEmb p g₀ (kpolyAlgEmb p) = σ := Classical.choose_spec hx
  refine {
    toFun := fun g => ⟨g₀⁻¹ * g.1, ?_⟩
    invFun := fun h => ⟨g₀ * h.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · -- (g₀⁻¹·g)·ι = ι
    change galSmulEmb p (g₀⁻¹ * g.1) (kpolyAlgEmb p) = kpolyAlgEmb p
    rw [galSmulEmb_mul p g₀⁻¹ g.1 (kpolyAlgEmb p)]
    calc
      galSmulEmb p g₀⁻¹ (galSmulEmb p g.1 (kpolyAlgEmb p)) =
          galSmulEmb p g₀⁻¹ σ := by rw [g.2]
      _ = galSmulEmb p g₀⁻¹ (galSmulEmb p g₀ (kpolyAlgEmb p)) := by rw [hg₀]
      _ = galSmulEmb p (g₀⁻¹ * g₀) (kpolyAlgEmb p) := by rw [galSmulEmb_mul p g₀⁻¹ g₀ (kpolyAlgEmb p)]
      _ = kpolyAlgEmb p := by
        rw [inv_mul_cancel]
        exact galSmulEmb_one p (kpolyAlgEmb p)
  · -- (g₀·h)·ι = σ
    change galSmulEmb p (g₀ * h.1) (kpolyAlgEmb p) = σ
    rw [galSmulEmb_mul p g₀ h.1 (kpolyAlgEmb p)]
    calc
      galSmulEmb p g₀ (galSmulEmb p h.1 (kpolyAlgEmb p)) =
          galSmulEmb p g₀ (kpolyAlgEmb p) := by
            rw [(mem_embStabilizer p h.1).mp h.2]
      _ = σ := hg₀
  · intro g
    apply Subtype.ext
    simp
  · intro h
    apply Subtype.ext
    simp

/-- **The fiber-counting identity** ((c)): the number of `g ∈ Gal(L/ℚ)`
whose embedding `g·ι` contracts `𝔓` to `Q` equals `|embStabilizer p|`
times the number of embeddings contracting `𝔓` to `Q`.  Proof: `g ↦ g·ι`
has fibers bijective to the stabilizer (`fiberEquivStabilizer`) and every
embedding is in the image (`orbit_of_canonical_eq_univ`), so the preimage
of the embedding-set splits as `Σ` over that set of the fibers (the
sigma-chase of `Commons.GroupTheory.GroupAction.ncard_smul_preimage`,
instance-free). -/
theorem ncard_emb_fiber_mul (p : ℚ[X]) [Fact (Irreducible p)]
    (𝔓 : Ideal (𝓞 p.SplittingField)) (Q : Ideal (𝓞 (AdjoinRoot p))) :
    ({g : p.Gal | pullbackIdeal p (galSmulEmb p g (kpolyAlgEmb p)) 𝔓 = Q}).ncard =
      Nat.card (embStabilizer p) *
      ({σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField | pullbackIdeal p σ 𝔓 = Q}).ncard := by
  classical
  letI : Fintype (AdjoinRoot p →ₐ[ℚ] p.SplittingField) :=
    Fintype.ofEquiv (Fin p.natDegree) (embEquivFin p).symm
  let T : Type _ := {σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField //
    pullbackIdeal p σ 𝔓 = Q}
  let fiber : (AdjoinRoot p →ₐ[ℚ] p.SplittingField) → Type _ :=
    fun σ => {g : p.Gal // galSmulEmb p g (kpolyAlgEmb p) = σ}
  have h1 : {g : p.Gal // pullbackIdeal p (galSmulEmb p g (kpolyAlgEmb p)) 𝔓 = Q} ≃
      (Σ x : T, fiber x.1) := by
    refine {
      toFun := fun g => ⟨⟨galSmulEmb p g (kpolyAlgEmb p), g.2⟩, ⟨g, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by
        rw [p.2.2]
        exact p.1.2⟩
      left_inv := by
        intro g
        apply Subtype.ext
        rfl
      right_inv := by
        intro p
        cases p with
        | mk σ hg =>
          cases hg with
          | mk g hg_eq =>
            dsimp
            apply Sigma.ext
            · apply Subtype.ext
              exact hg_eq
            · apply (Subtype.heq_iff_coe_eq ?_).mpr
              · rfl
              · intro u
                simp [hg_eq] }
  calc
    ({g : p.Gal | pullbackIdeal p (galSmulEmb p g (kpolyAlgEmb p)) 𝔓 = Q}).ncard
        = Nat.card {g : p.Gal // pullbackIdeal p (galSmulEmb p g (kpolyAlgEmb p)) 𝔓 = Q} := by
          exact Commons.Data.Set.ncard_eq_natCard {g : p.Gal |
            pullbackIdeal p (galSmulEmb p g (kpolyAlgEmb p)) 𝔓 = Q}
    _ = Nat.card (Σ x : T, fiber x.1) := by exact Nat.card_congr h1
    _ = Nat.card T * Nat.card (embStabilizer p) := by
      calc
        Nat.card (Σ x : T, fiber x.1)
            = Nat.card (Σ _x : T, (embStabilizer p : Type _)) := by
              exact Nat.card_congr (Equiv.sigmaCongrRight (fun x : T =>
                fiberEquivStabilizer p x.1 (exists_gal_of_embedding p x.1)))
        _ = Nat.card (T × (embStabilizer p : Type _)) := by
              exact Nat.card_congr (Equiv.sigmaEquivProd T (embStabilizer p))
        _ = Nat.card T * Nat.card (embStabilizer p) := by
              exact Nat.card_prod T (embStabilizer p)
    _ = Nat.card (embStabilizer p) * Nat.card T := by rw [Nat.mul_comm]
    _ = Nat.card (embStabilizer p) *
          ({σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField | pullbackIdeal p σ 𝔓 = Q}).ncard := by
          congr 1
end CosetCounting
section OpenPrimeSide

/-! **Prime side of the fiber statement — PROVED (2026-09).**

For `𝔓` a prime of `𝒪_L` over `p` and `Q` a prime of `𝒪 K_p` over `p` with
`𝔓` *lying over* `Q` (hypothesis `h𝔓Q`), the number of embeddings
`σ : K_p ↪ L` whose contraction `pullbackIdeal σ 𝔓` equals `Q` is
`e_Q · f_Q` (`fiberCard` below).  The proof assembles:

1. the fiber identity `ncard_emb_fiber_mul` — `#{g | pullback (g·ι) 𝔓 = Q} =
   |embStabilizer| · #{σ | pullback σ 𝔓 = Q}` (proved above);
2. `pullbackIdeal_galSmulEmb` + `comap_galIntMap_eq_smul_inv`:
   `pullback (g·ι) 𝔓 = pullback ι (g⁻¹ • 𝔓)`, so counting over `g` is
   counting `{g | (g • 𝔓).under 𝒪K = Q}` (reindexing `g ↦ g⁻¹`);
3. the orbit count over the (transitive) action of `p.Gal` on the primes of
   `𝒪 L` over `p` (`ncard_smul_preimage` + `orbit_eq_univ`): the preimage of
   `{primes over Q}` has cardinality `|D(𝔓)| · #{primes of L over Q}` with
   `|D(𝔓)| = e(𝔓/p)·f(𝔓/p)` (`stabilizer_card_spl`);
4. the relative fundamental identity for the Galois extension
   `L/K_p` (`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`,
   instantiated via `GaloisTower.kpoly_isGalois`):
   `#{primes of L over Q} · e(𝔓/Q)·f(𝔓/Q) = |Gal(L/K_p)|`;
5. the tower decompositions `e(𝔓/p) = e(Q/p)·e(𝔓/Q)`,
   `f(𝔓/p) = f(Q/p)·f(𝔓/Q)` (`ramificationIdx_tower_intRing`,
   `inertiaDeg_tower_intRing`) and the cardinality identification
   `|embStabilizer| = |Gal(L/K_p)|` (`embStab_card_gal`, the automorphism
   bijection of `GaloisTower`); cancellation of `|embStabilizer| ≠ 0` yields
   `#{σ} = e_Q · f_Q`.

The supporting instance data (`IsScalarTower ℚ K_p L`,
`IsGalois K_p L`, the ring-of-integers Galois-group instances) is assembled
in `Submission/Vdw/GaloisTower.lean` (`kpoly_tower`, `kpoly_isGalois`).
-/

/-- `galIntMap p g` is the action of `g` on the integers of `L`. -/
theorem galIntMap_smul (p : ℚ[X]) [Fact (Irreducible p)]
    (g : p.Gal) (x : 𝓞 p.SplittingField) :
    galIntMap p g x = g • x := by
  rfl

/-- The contraction of `𝔓` through the automorphism `g` (i.e. `{y | g y ∈ 𝔓}`)
is the action of `g⁻¹` on the ideal `𝔓`. -/
theorem comap_galIntMap_eq_smul_inv (p : ℚ[X]) [Fact (Irreducible p)]
    (g : p.Gal) (𝔓 : Ideal (𝓞 p.SplittingField)) :
    Ideal.comap (galIntMap p g) 𝔓 = g⁻¹ • 𝔓 := by
  ext y
  simp only [Ideal.mem_comap, Ideal.mem_inv_pointwise_smul_iff, galIntMap_smul p g y]


theorem embStab_card_gal (p : ℚ[X]) [Fact (Irreducible p)] :
    letI : Algebra (AdjoinRoot p) p.SplittingField := kpolyAlgebra p
    letI : IsScalarTower ℚ (AdjoinRoot p) p.SplittingField := kpoly_tower p
    letI : IsGalois (AdjoinRoot p) p.SplittingField := kpoly_isGalois p
    Nat.card (embStabilizer p) = Nat.card Gal(p.SplittingField/(AdjoinRoot p)) := by
  letI : Algebra (AdjoinRoot p) p.SplittingField := kpolyAlgebra p
  letI : IsScalarTower ℚ (AdjoinRoot p) p.SplittingField := kpoly_tower p
  letI : IsGalois (AdjoinRoot p) p.SplittingField := kpoly_isGalois p
  let K := AdjoinRoot p
  let L := p.SplittingField
  -- promotion: an automorphism over ℚ fixing K pointwise is one over K
  let prom : (embStabilizer p) → L ≃ₐ[K] L := fun g => by
    let φ := g.1
    have hιk (x : K) : kpolyAlgEmb p x = kpolyEmb p x := by
      have hk : (kpolyAlgEmb p).toRingHom = kpolyEmb p := by
        dsimp [kpolyAlgEmb, kpolyEmb]
      exact (congrArg (fun f : K →+* L => f x) hk)
    have hfix : ∀ k : K, φ (algebraMap K L k) = algebraMap K L k := by
      intro k
      have hh : φ (kpolyAlgEmb p k) = kpolyAlgEmb p k := by
        have hh0 := congrArg (fun f : K →ₐ[ℚ] L => f k) g.2
        change ((g.1).toAlgHom.comp (kpolyAlgEmb p)) k = (kpolyAlgEmb p) k
        exact hh0
      change φ (kpolyEmb p k) = kpolyEmb p k
      rw [← hιk k]
      exact hh
    refine {
      toEquiv := (φ : L ≃ L)
      map_mul' := φ.map_mul'
      map_add' := φ.map_add'
      commutes' := hfix }
  -- restriction: an automorphism over K is one over ℚ fixing K pointwise
  let restr : (L ≃ₐ[K] L) → embStabilizer p := fun e => ⟨e.restrictScalars ℚ, by
      have hιk (x : K) : kpolyAlgEmb p x = kpolyEmb p x := by
        have hk : (kpolyAlgEmb p).toRingHom = kpolyEmb p := by
          dsimp [kpolyAlgEmb, kpolyEmb]
        exact (congrArg (fun f : K →+* L => f x) hk)
      apply AlgHom.ext
      intro k
      change (e.restrictScalars ℚ) (kpolyAlgEmb p k) = kpolyAlgEmb p k
      rw [hιk k]
      change (e.restrictScalars ℚ) (algebraMap K L k) = algebraMap K L k
      simpa using (e.commutes k)⟩
  apply Nat.card_congr
  refine {
    toFun := prom
    invFun := restr
    left_inv := ?_
    right_inv := ?_ }
  · intro g
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    rfl
  · intro e
    apply AlgEquiv.ext
    intro x
    rfl

theorem fiberCard (p : ℚ[X]) [Fact (Irreducible p)]
    (p0 : ℕ) (_hp0 : Nat.Prime p0)
    (𝔓 : Ideal (𝓞 p.SplittingField)) (h𝔓1 : 𝔓.IsPrime)
    (h𝔓2 : 𝔓.LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ)))
    (Q : Ideal (𝓞 (AdjoinRoot p))) (hQ1 : Q.IsPrime)
    (hQ2 : Q.LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ)))
    (h𝔓Q : pullbackIdeal p (kpolyAlgEmb p) 𝔓 = Q) :
    ({σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField |
      pullbackIdeal p σ 𝔓 = Q}).ncard = Q.ramificationIdx ℤ * Q.inertiaDeg ℤ := by
  classical
  let K : Type := AdjoinRoot p
  let L : Type := p.SplittingField
  let B : Type := 𝓞 (AdjoinRoot p)
  let C : Type := 𝓞 p.SplittingField
  let pZ : Ideal ℤ := Ideal.span ({(p0 : ℤ)} : Set ℤ)
  letI : Algebra K L := kpolyAlgebra p
  haveI : IsScalarTower ℚ K L := kpoly_tower p
  haveI : IsGalois K L := kpoly_isGalois p
  haveI : IsGalois ℚ L := spl_galois p
  haveI : 𝔓.IsPrime := h𝔓1
  haveI : Q.IsPrime := hQ1
  haveI : 𝔓.LiesOver pZ := h𝔓2
  haveI : Q.LiesOver pZ := hQ2
  -- algebraMap B C = intRingMap p (kpolyAlgEmb p)
  have halg : (algebraMap B C) = intRingMap p (kpolyAlgEmb p) := by rfl
  -- 𝔓 lies over Q through the canonical embedding
  have h𝔓under : 𝔓.under B = Q := (pullbackIdeal_eq_iff_under p halg 𝔓 Q).mp h𝔓Q
  haveI : 𝔓.LiesOver Q := ⟨h𝔓under.symm⟩
  -- relative fundamental identity at the prime Q of B
  have hrel0 :
      (Q.primesOver C).ncard *
        (Ideal.ramificationIdxIn Q C * Ideal.inertiaDegIn Q C) = Nat.card Gal(L/K) := by
    exact Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (A := B) (B := C) (G := Gal(L/K)) (p := Q)
  have hrel :
      (Q.primesOver C).ncard * (𝔓.ramificationIdx B * 𝔓.inertiaDeg B) =
        Nat.card Gal(L/K) := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := B) (B := C)
        (p := Q) (P := 𝔓) (G := Gal(L/K)),
      Ideal.inertiaDegIn_eq_inertiaDeg (A := B) (B := C)
        (p := Q) (P := 𝔓) (G := Gal(L/K))] at hrel0
    exact hrel0
  -- tower decompositions over ℤ ⊂ B ⊂ C
  have he_tower : 𝔓.ramificationIdx ℤ =
      Q.ramificationIdx ℤ * 𝔓.ramificationIdx B := by
    exact ramificationIdx_tower_intRing p p0 _hp0 Q 𝔓
  have hf_tower : 𝔓.inertiaDeg ℤ =
      Q.inertiaDeg ℤ * 𝔓.inertiaDeg B := by
    exact inertiaDeg_tower_intRing p p0 _hp0 Q 𝔓
  -- Galois-group instances for the counting (primes over p0)
  haveI : IsGaloisGroup p.Gal ℤ C :=
    Commons.NumberTheory.NumberField.ringOfIntegers_isGaloisGroup L
  haveI : IsGaloisGroup Gal(L/K) B C := inferInstance
  let X : Type _ := pZ.primesOver C
  haveI : Fintype X := (Algebra.QuasiFinite.finite_primesOver pZ).fintype
  let a : X := ⟨𝔓, ⟨h𝔓1, h𝔓2⟩⟩
  -- the count over the orbit: {g | g•a ∈ P} = |stab a| * |P|
  let P : Set X := {x : X | x.1.under B = Q}
  have hcnt : ({g : p.Gal | g • a ∈ P}).ncard =
      Nat.card (MulAction.stabilizer p.Gal a) * P.ncard := by
    have h := Commons.GroupTheory.GroupAction.ncard_smul_preimage p.Gal a P
    rw [MulAction.orbit_eq_univ p.Gal a] at h
    simpa using h
  -- the stabilizer of a in the primesOver action agrees with the ideal stabilizer
  have hstabset : MulAction.stabilizer p.Gal a = MulAction.stabilizer p.Gal 𝔓 := by
    ext g
    constructor
    · intro hg
      exact (congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hg))
    · intro hg
      apply MulAction.mem_stabilizer_iff.mpr
      apply Subtype.ext
      exact hg
  have hstab : Nat.card (MulAction.stabilizer p.Gal a) =
      Nat.card (MulAction.stabilizer p.Gal 𝔓) := by
    rw [hstabset]
  have hstabcard : Nat.card (MulAction.stabilizer p.Gal a) =
      𝔓.ramificationIdx ℤ * 𝔓.inertiaDeg ℤ := by
    rw [hstab]
    exact stabilizer_card_spl p p0 _hp0 𝔓
  -- |P| = (Q.primesOver C).ncard: P = {x : X | under B x = Q}
  haveI : Algebra.QuasiFinite B C := inferInstance
  haveI : Fintype (Q.primesOver C) :=
    (Algebra.QuasiFinite.finite_primesOver Q).fintype
  have hPcard : P.ncard = (Q.primesOver C).ncard := by
    rw [Commons.Data.Set.ncard_eq_natCard P]
    rw [Commons.Data.Set.ncard_eq_natCard (Q.primesOver C)]
    -- equivalence {x : X // x.1.under B = Q} ≃ {P0 : Ideal C // P0.IsPrime ∧ P0.LiesOver Q}
    let e : {x : X // x.1.under B = Q} ≃
        {P0 : Ideal C // P0.IsPrime ∧ P0.LiesOver Q} := {
      toFun := fun x => ⟨x.1.1, ⟨x.1.2.1, (by
          -- want x.1.LiesOver Q: over : Q = x.1.under B
          exact ⟨x.2.symm⟩)⟩⟩
      invFun := fun y => ⟨⟨y.1, ⟨y.2.1, by
          letI : y.1.LiesOver Q := y.2.2
          exact Ideal.LiesOver.trans (𝔓 := y.1) (P := Q) (p := pZ)⟩⟩, by
          exact y.2.2.over.symm⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro y
        apply Subtype.ext
        rfl }
    exact Nat.card_congr e
  -- count the g's: A1 := {g | pullback (g·ι) 𝔓 = Q}
  let A1 : Set p.Gal := {g | pullbackIdeal p (galSmulEmb p g (kpolyAlgEmb p)) 𝔓 = Q}
  have hA1₂ : A1 = {g : p.Gal | pullbackIdeal p (kpolyAlgEmb p) (g⁻¹ • 𝔓) = Q} := by
    ext g
    dsimp [A1]
    rw [pullbackIdeal_galSmulEmb p g 𝔓]
    rw [comap_galIntMap_eq_smul_inv p g 𝔓]
  have hA1₃ : A1.ncard = ({g : p.Gal | pullbackIdeal p (kpolyAlgEmb p) (g • 𝔓) = Q}).ncard := by
    rw [hA1₂]
    rw [Commons.Data.Set.ncard_eq_natCard {g : p.Gal | pullbackIdeal p (kpolyAlgEmb p) (g⁻¹ • 𝔓) = Q}]
    rw [Commons.Data.Set.ncard_eq_natCard {g : p.Gal | pullbackIdeal p (kpolyAlgEmb p) (g • 𝔓) = Q}]
    apply Nat.card_congr
    refine {
      toFun := fun g => ⟨g⁻¹, by
        change pullbackIdeal p (kpolyAlgEmb p) ((g⁻¹ : p.Gal) • 𝔓) = Q
        exact g.2⟩
      invFun := fun g => ⟨g⁻¹, by
        change pullbackIdeal p (kpolyAlgEmb p) ((g : p.Gal) • 𝔓) = Q
        exact g.2⟩
      left_inv := by
        intro g
        apply Subtype.ext
        rfl
      right_inv := by
        intro g
        apply Subtype.ext
        rfl }
  have hset4 : ({g : p.Gal | pullbackIdeal p (kpolyAlgEmb p) (g • 𝔓) = Q} : Set p.Gal) =
      {g : p.Gal | g • a ∈ P} := by
    ext g
    constructor
    · intro hg
      dsimp [P]
      change (g • 𝔓 : Ideal C).under B = Q
      exact (pullbackIdeal_eq_iff_under p halg (g • 𝔓) Q).mp hg
    · intro hg
      dsimp [P] at hg
      change (g • 𝔓 : Ideal C).under B = Q at hg
      exact (pullbackIdeal_eq_iff_under p halg (g • 𝔓) Q).mpr hg
  have hA1₄ : A1.ncard = ({g : p.Gal | g • a ∈ P}).ncard := by
    rw [hA1₃, hset4]

  -- the assembled counting identity: |A1| = e(𝔓/p0) f(𝔓/p0) * (Q.primesOver C).ncard
  have hA1cnt : A1.ncard =
      (𝔓.ramificationIdx ℤ * 𝔓.inertiaDeg ℤ) * (Q.primesOver C).ncard := by
    calc
      A1.ncard = ({g : p.Gal | g • a ∈ P}).ncard := hA1₄
      _ = Nat.card (MulAction.stabilizer p.Gal a) * P.ncard := hcnt
      _ = (𝔓.ramificationIdx ℤ * 𝔓.inertiaDeg ℤ) * (Q.primesOver C).ncard := by
        rw [hstabcard, hPcard]
  -- the orbit–stabilizer fiber identity (proved in the file): |A1| = |H| * T
  have hfib := ncard_emb_fiber_mul p 𝔓 Q
  -- |H| = |Gal(L/K)|
  have hHcard : Nat.card (embStabilizer p) = Nat.card Gal(L/K) := embStab_card_gal p
  -- put everything together
  let T : Set _ := {σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField | pullbackIdeal p σ 𝔓 = Q}
  have hfibA : A1.ncard = Nat.card (embStabilizer p) * T.ncard := by
    simpa [A1, T] using hfib
  have hmain : Nat.card (embStabilizer p) * T.ncard =
      (𝔓.ramificationIdx ℤ * 𝔓.inertiaDeg ℤ) * (Q.primesOver C).ncard := by
    rw [← hfibA]
    exact hA1cnt
  -- e(𝔓/p0) = e(Q/p0)·e(𝔓/Q), f likewise; then m·(e·f)_B = |Gal(L/K)|
  have hmain' : Nat.card (embStabilizer p) * T.ncard =
      (Q.ramificationIdx ℤ * Q.inertiaDeg ℤ) * Nat.card Gal(L/K) := by
    calc
      Nat.card (embStabilizer p) * T.ncard
          = (𝔓.ramificationIdx ℤ * 𝔓.inertiaDeg ℤ) * (Q.primesOver C).ncard := hmain
      _ = ((Q.ramificationIdx ℤ * 𝔓.ramificationIdx B) *
            (Q.inertiaDeg ℤ * 𝔓.inertiaDeg B)) * (Q.primesOver C).ncard := by
            rw [he_tower, hf_tower]
      _ = (Q.ramificationIdx ℤ * Q.inertiaDeg ℤ) *
            ((Q.primesOver C).ncard * (𝔓.ramificationIdx B * 𝔓.inertiaDeg B)) := by
            ring
      _ = (Q.ramificationIdx ℤ * Q.inertiaDeg ℤ) * Nat.card Gal(L/K) := by
            rw [hrel]
  -- |H|·T = e_Q·f_Q·|H|; cancel |H| (nonzero: the identity fixes ι)
  have hE : Nat.card (embStabilizer p) * T.ncard =
      (Q.ramificationIdx ℤ * Q.inertiaDeg ℤ) * Nat.card (embStabilizer p) := by
    rw [← hHcard] at hmain'
    exact hmain'
  have h1mem : (1 : p.Gal) ∈ embStabilizer p := by
    rfl
  have hH : Nat.card (embStabilizer p) ≠ 0 := by
    exact Nat.card_ne_zero.mpr ⟨⟨⟨1, h1mem⟩⟩, inferInstance⟩
  have hT : T.ncard = Q.ramificationIdx ℤ * Q.inertiaDeg ℤ := by
    rw [mul_comm (Q.ramificationIdx ℤ * Q.inertiaDeg ℤ) (Nat.card (embStabilizer p))] at hE
    exact mul_left_cancel₀ hH hE
  -- the target set is exactly T
  simpa [T] using hT

end OpenPrimeSide

end Submission.Vdw
