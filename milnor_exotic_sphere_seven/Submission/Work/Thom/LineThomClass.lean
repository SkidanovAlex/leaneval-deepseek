import Mathlib
import Submission.Work.Thom.LineKernel
import Submission.Work.Thom.LineThom
import Submission.Work.Thom.ThomClass
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Sph3Disc.pairDelta_mixedCup_general

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-!
# The Thom class of the trivial line bundle: the suspension isomorphism

For a topological space `B` and the trivial real line bundle `E = B × ℝ → B` this module proves

  **`Work.Thom.nonempty_thomClass_trivial_line`** : `ThomClass E 1` is inhabited,

i.e. the **Thom isomorphism** `H^k(B;ℤ) ≅ H^{k+1}(E,E∖0;ℤ)` for the trivial line bundle.  This is
the *suspension isomorphism*: the first non-contractible base for which the Thom class is
constructed (the trivial bundle over a contractible base is
`Submission/Work/Thom/thomClass_trivial_contractible.lean`).

The Thom class is `τ = δ u`, where

* `u ∈ H⁰(E∖0;ℤ)` is the **difference of the two ends** of the line bundle
  (`Work.Thom.lineDiffClass`: `1` on the negative half of each fibre, `0` on the positive half), and
* `δ : H⁰(E∖0;ℤ) → H¹(E,E∖0;ℤ)` is the connecting homomorphism of the pair `(E,E∖0)`
  (`Work.Thom.pairδC`).

On the two halves of `E∖0` the class `u` restricts to `0` and `1`, and the two projections
`σ_±^*` jointly detect `H^*(E∖0;ℤ)` (`Work.Thom.eq_zero_of_sigmaPlus_sigmaMinus_eq_zero`).  With
`s = (π|_{E∖0})^*`, `ρ = i_{E∖0}^*` and `π^* : H^*(B;ℤ) → H^*(E;ℤ)` the projection isomorphism, the
Thom map is, by the derivation rule of the connecting homomorphism
(`Work.Sph3Disc.pairDelta_mixedCup_general`),

  `x ↦ π^*(x) ⌣ τ = (-1)^k • δ(s x ⌣ u)`,

and `Φ : x ↦ δ(s x ⌣ u)` is bijective: *injective* because `s x ⌣ u ∈ ker δ = im ρ` forces
`σ₊^*(s x ⌣ u) = 0` and hence `s x ⌣ u = 0`; *surjective* because `ker δ = im ρ` is described by
the two projections.

## Main results

* `Work.Thom.lineTau` — the Thom class `τ = δ u`;
* `Work.Thom.linePhi`, `Work.Thom.linePhi_bijective` — the map `x ↦ δ(s x ⌣ u)`;
* `Work.Thom.thomMap_trivial_line_eq` — the Thom map is `(-1)^k` times `linePhi`;
* `Work.Thom.nonempty_thomClass_trivial_line` — the Thom class exists.
-/

open CategoryTheory AlgebraicTopology Limits Simplicial

open scoped Topology Simplicial

open Classical

open Work.TangentClasses

namespace Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι₀ : Type} [Inhabited ι₀]

/-! ## Notation for the trivial line bundle -/

/-- The total space of the trivial real line bundle over `B`. -/
abbrev TLTotal (B : Type) [TopologicalSpace B] (ι₀ : Type) [Inhabited ι₀] : Type :=
  (RealBundle.trivial B ℝ ι₀).TotalSpace

/-- The zero complement `E∖0` of the trivial real line bundle. -/
abbrev TLZero (B : Type) [TopologicalSpace B] (ι₀ : Type) [Inhabited ι₀] :
    Set (TLTotal B ι₀) :=
  zeroComplement (RealBundle.trivial B ℝ ι₀)

/-! ## The maps -/

/-- `s = (π|_{E∖0})^*`: the pullback of the projection of the trivial line bundle, restricted to
the zero complement. -/
abbrev lineS (k : ℕ) : Coh ℤ k B →ₗ[ℤ] Coh ℤ k ↥(TLZero B ι₀) :=
  (CohMap ((bundleProj (RealBundle.trivial B ℝ ι₀)).comp (subtypeMap (TLZero B ι₀))) ℤ k).hom

/-- `ρ = i_{E∖0}^*`: the restriction from `E` to `E∖0`. -/
abbrev lineRho (k : ℕ) : Coh ℤ k (TLTotal B ι₀) →ₗ[ℤ] Coh ℤ k ↥(TLZero B ι₀) :=
  (CohMap (subtypeMap (TLZero B ι₀)) ℤ k).hom

/-- `π^*`: the pullback along the projection of the trivial line bundle. -/
abbrev linePi (k : ℕ) : Coh ℤ k B →ₗ[ℤ] Coh ℤ k (TLTotal B ι₀) :=
  (CohMap (bundleProj (RealBundle.trivial B ℝ ι₀)) ℤ k).hom

/-- `σ₊^*`: the pullback along the positive constant section. -/
abbrev lineP (k : ℕ) : Coh ℤ k ↥(TLZero B ι₀) →ₗ[ℤ] Coh ℤ k (TLTotal B ι₀) :=
  (CohMap (sigmaPlus (B := B) (ι₀ := ι₀)) ℤ k).hom

/-- `σ₋^*`: the pullback along the negative constant section. -/
abbrev lineR (k : ℕ) : Coh ℤ k ↥(TLZero B ι₀) →ₗ[ℤ] Coh ℤ k (TLTotal B ι₀) :=
  (CohMap (sigmaMinus (B := B) (ι₀ := ι₀)) ℤ k).hom

/-- The difference-of-the-ends class of the trivial line bundle, as a class of `H⁰(E∖0;ℤ)`. -/
abbrev lineU : Coh ℤ 0 ↥(TLZero B ι₀) := lineDiffClass (B := B) (ι₀ := ι₀)

/-- Cupping with the difference of the ends, as a linear map. -/
def lineCupLM (k : ℕ) : Coh ℤ k ↥(TLZero B ι₀) →ₗ[ℤ] Coh ℤ k ↥(TLZero B ι₀) :=
  (LinearMap.applyₗ (lineU (B := B) (ι₀ := ι₀))).comp
    (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(TLZero B ι₀))) k 0)

/-- **`τ = δ u`**, the Thom class of the trivial line bundle: the image of the difference of the two
ends under the connecting homomorphism of the pair `(E,E∖0)`. -/
def lineTau : OpenThom (RealBundle.trivial B ℝ ι₀) 1 :=
  (pairδC (TLZero B ι₀) 0).hom (lineU (B := B) (ι₀ := ι₀))

/-- **The map `x ↦ δ(s x ⌣ u)`**: the Thom map up to the sign `(-1)^k`. -/
def linePhi (k : ℕ) : Coh ℤ k B →ₗ[ℤ] RelCoh ℤ (k + 1) (TLTotal B ι₀) (TLZero B ι₀) :=
  ((pairδC (TLZero B ι₀) k).hom).comp
    ((lineCupLM (B := B) (ι₀ := ι₀) k).comp (lineS (B := B) (ι₀ := ι₀) k))

/-! ## Basic identities -/

@[simp] theorem lineCupLM_apply (k : ℕ) (v : Coh ℤ k ↥(TLZero B ι₀)) :
    lineCupLM (B := B) (ι₀ := ι₀) k v
      = (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(TLZero B ι₀))) k 0)
          v (lineU (B := B) (ι₀ := ι₀)) := rfl

/-- The definition of `linePhi`. -/
theorem linePhi_apply (k : ℕ) (x : Coh ℤ k B) :
    linePhi (B := B) (ι₀ := ι₀) k x
      = (pairδC (TLZero B ι₀) k).hom
          (lineCupLM (B := B) (ι₀ := ι₀) k (lineS (B := B) (ι₀ := ι₀) k x)) := rfl

/-- `s = ρ ∘ π`. -/
theorem lineS_eq_lineRho_comp_linePi (k : ℕ) :
    lineS (B := B) (ι₀ := ι₀) k
      = (lineRho (B := B) (ι₀ := ι₀) k).comp (linePi (B := B) (ι₀ := ι₀) k) := by
  have h := CohMap_comp (subtypeMap (TLZero B ι₀)) (bundleProj (RealBundle.trivial B ℝ ι₀)) ℤ k
  have h2 := congrArg (fun f : Coh ℤ k B ⟶ Coh ℤ k ↥(TLZero B ι₀) => f.hom) h
  simpa only [ModuleCat.hom_comp, lineS, lineRho, linePi] using h2

/-- `s x = ρ (π x)`. -/
theorem lineS_apply_eq (k : ℕ) (x : Coh ℤ k B) :
    lineS (B := B) (ι₀ := ι₀) k x
      = lineRho (B := B) (ι₀ := ι₀) k (linePi (B := B) (ι₀ := ι₀) k x) := by
  have h := LinearMap.congr_fun (lineS_eq_lineRho_comp_linePi (B := B) (ι₀ := ι₀) k) x
  simpa only [LinearMap.comp_apply] using h

/-- The definition of `linePhi`, in the form `x ↦ δ(ρ(π x) ⌣ u)`. -/
theorem linePhi_apply_eq (k : ℕ) (x : Coh ℤ k B) :
    linePhi (B := B) (ι₀ := ι₀) k x
      = (pairδC (TLZero B ι₀) k).hom
          (lineCupLM (B := B) (ι₀ := ι₀) k
            (lineRho (B := B) (ι₀ := ι₀) k (linePi (B := B) (ι₀ := ι₀) k x))) := by
  rw [linePhi_apply, lineS_apply_eq]

/-- `σ₊ ∘ (π|_{E∖0}) = π`. -/
theorem lineSigmaPlus_comp_iota :
    ((bundleProj (RealBundle.trivial B ℝ ι₀)).comp (subtypeMap (TLZero B ι₀))).comp
        (sigmaPlus (B := B) (ι₀ := ι₀))
      = bundleProj (RealBundle.trivial B ℝ ι₀) := by
  apply ContinuousMap.ext
  intro p
  rfl

/-- `σ₋ ∘ (π|_{E∖0}) = π`. -/
theorem lineSigmaMinus_comp_iota :
    ((bundleProj (RealBundle.trivial B ℝ ι₀)).comp (subtypeMap (TLZero B ι₀))).comp
        (sigmaMinus (B := B) (ι₀ := ι₀))
      = bundleProj (RealBundle.trivial B ℝ ι₀) := by
  apply ContinuousMap.ext
  intro p
  rfl

/-- `σ₊^* ∘ s = π^*`. -/
theorem lineP_comp_lineS (k : ℕ) :
    (lineP (B := B) (ι₀ := ι₀) k).comp (lineS (B := B) (ι₀ := ι₀) k)
      = linePi (B := B) (ι₀ := ι₀) k := by
  have h := CohMap_comp (sigmaPlus (B := B) (ι₀ := ι₀))
    ((bundleProj (RealBundle.trivial B ℝ ι₀)).comp (subtypeMap (TLZero B ι₀))) ℤ k
  rw [lineSigmaPlus_comp_iota] at h
  have h2 := congrArg (fun f : Coh ℤ k B ⟶ Coh ℤ k (TLTotal B ι₀) => f.hom) h
  simpa only [ModuleCat.hom_comp, lineP, lineS, linePi] using h2.symm

/-- `σ₋^* ∘ s = π^*`. -/
theorem lineR_comp_lineS (k : ℕ) :
    (lineR (B := B) (ι₀ := ι₀) k).comp (lineS (B := B) (ι₀ := ι₀) k)
      = linePi (B := B) (ι₀ := ι₀) k := by
  have h := CohMap_comp (sigmaMinus (B := B) (ι₀ := ι₀))
    ((bundleProj (RealBundle.trivial B ℝ ι₀)).comp (subtypeMap (TLZero B ι₀))) ℤ k
  rw [lineSigmaMinus_comp_iota] at h
  have h2 := congrArg (fun f : Coh ℤ k B ⟶ Coh ℤ k (TLTotal B ι₀) => f.hom) h
  simpa only [ModuleCat.hom_comp, lineR, lineS, linePi] using h2.symm

/-- `σ₊^* ∘ ρ = id`. -/
theorem lineP_comp_lineRho (k : ℕ) :
    (lineP (B := B) (ι₀ := ι₀) k).comp (lineRho (B := B) (ι₀ := ι₀) k) = LinearMap.id := by
  have h := sigmaPlus_cohmMap_subtypeMap (B := B) (ι₀ := ι₀) k
  simpa only [lineP, lineRho] using h

/-- `σ₋^* ∘ ρ = id`. -/
theorem lineR_comp_lineRho (k : ℕ) :
    (lineR (B := B) (ι₀ := ι₀) k).comp (lineRho (B := B) (ι₀ := ι₀) k) = LinearMap.id := by
  have h := sigmaMinus_cohmMap_subtypeMap (B := B) (ι₀ := ι₀) k
  simpa only [lineR, lineRho] using h

/-- `ρ` is injective. -/
theorem lineRho_injective (k : ℕ) : Function.Injective (lineRho (B := B) (ι₀ := ι₀) k) := by
  intro x y hxy
  have h := LinearMap.congr_fun (lineP_comp_lineRho (B := B) (ι₀ := ι₀) k) x
  have h' := LinearMap.congr_fun (lineP_comp_lineRho (B := B) (ι₀ := ι₀) k) y
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h h'
  rw [hxy] at h
  exact h.symm.trans h'

/-- `π^*` is injective. -/
theorem linePi_injective (k : ℕ) : Function.Injective (linePi (B := B) (ι₀ := ι₀) k) :=
  (bijective_CohMap_bundleProj (RealBundle.trivial B ℝ ι₀) k).injective

/-- `π^*` is surjective. -/
theorem linePi_surjective (k : ℕ) : Function.Surjective (linePi (B := B) (ι₀ := ι₀) k) :=
  (bijective_CohMap_bundleProj (RealBundle.trivial B ℝ ι₀) k).surjective

/-! ## The values of the two projection pullbacks on `s x ⌣ u` -/

/-- `σ₊^*(s x ⌣ u) = 0`. -/
theorem lineP_lineCup_lineS (k : ℕ) (x : Coh ℤ k B) :
    lineP (B := B) (ι₀ := ι₀) k
        (lineCupLM (B := B) (ι₀ := ι₀) k (lineS (B := B) (ι₀ := ι₀) k x)) = 0 := by
  have hnat : lineP (B := B) (ι₀ := ι₀) k
      (lineCupLM (B := B) (ι₀ := ι₀) k (lineS (B := B) (ι₀ := ι₀) k x))
      = (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (TLTotal B ι₀))) k 0)
          ((CohMap (sigmaPlus (B := B) (ι₀ := ι₀)) ℤ k).hom (lineS (B := B) (ι₀ := ι₀) k x))
          ((CohMap (sigmaPlus (B := B) (ι₀ := ι₀)) ℤ 0).hom (lineU (B := B) (ι₀ := ι₀))) :=
    Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom (sigmaPlus (B := B) (ι₀ := ι₀))) k 0
      (lineS (B := B) (ι₀ := ι₀) k x) (lineU (B := B) (ι₀ := ι₀))
  have h1 : (CohMap (sigmaPlus (B := B) (ι₀ := ι₀)) ℤ k).hom
      (lineS (B := B) (ι₀ := ι₀) k x) = linePi (B := B) (ι₀ := ι₀) k x := by
    have h := LinearMap.congr_fun (lineP_comp_lineS (B := B) (ι₀ := ι₀) k) x
    simpa only [LinearMap.comp_apply, lineP] using h
  have h2 : (CohMap (sigmaPlus (B := B) (ι₀ := ι₀)) ℤ 0).hom (lineU (B := B) (ι₀ := ι₀)) = 0 :=
    sigmaPlus_lineDiffClass (B := B) (ι₀ := ι₀)
  rw [hnat, h1, h2, Work.Cohomology.cupH'_zero_right]

/-- `σ₋^*(s x ⌣ u) = π^* x`. -/
theorem lineR_lineCup_lineS (k : ℕ) (x : Coh ℤ k B) :
    lineR (B := B) (ι₀ := ι₀) k
        (lineCupLM (B := B) (ι₀ := ι₀) k (lineS (B := B) (ι₀ := ι₀) k x))
      = linePi (B := B) (ι₀ := ι₀) k x := by
  have hnat : lineR (B := B) (ι₀ := ι₀) k
      (lineCupLM (B := B) (ι₀ := ι₀) k (lineS (B := B) (ι₀ := ι₀) k x))
      = (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (TLTotal B ι₀))) k 0)
          ((CohMap (sigmaMinus (B := B) (ι₀ := ι₀)) ℤ k).hom (lineS (B := B) (ι₀ := ι₀) k x))
          ((CohMap (sigmaMinus (B := B) (ι₀ := ι₀)) ℤ 0).hom (lineU (B := B) (ι₀ := ι₀))) :=
    Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom (sigmaMinus (B := B) (ι₀ := ι₀))) k 0
      (lineS (B := B) (ι₀ := ι₀) k x) (lineU (B := B) (ι₀ := ι₀))
  have h1 : (CohMap (sigmaMinus (B := B) (ι₀ := ι₀)) ℤ k).hom
      (lineS (B := B) (ι₀ := ι₀) k x) = linePi (B := B) (ι₀ := ι₀) k x := by
    have h := LinearMap.congr_fun (lineR_comp_lineS (B := B) (ι₀ := ι₀) k) x
    simpa only [LinearMap.comp_apply, lineR] using h
  have h2 : (CohMap (sigmaMinus (B := B) (ι₀ := ι₀)) ℤ 0).hom (lineU (B := B) (ι₀ := ι₀))
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of (TLTotal B ι₀))) :=
    sigmaMinus_lineDiffClass (B := B) (ι₀ := ι₀)
  rw [hnat, h1, h2, Work.Cohomology.cupH'_one_right]

/-! ## The characterization of `im ρ` -/

/-- **Characterization of the image of `ρ`**: `v` is the restriction of a class of `E` if and only
if the two projections of `v` satisfy the relation defining the diagonal.  This is where the fact
that the two constant sections jointly detect `H^*(E∖0;ℤ)`
(`Work.Thom.eq_zero_of_sigmaPlus_sigmaMinus_eq_zero`) is used. -/
theorem lineRho_range_iff (k : ℕ) (v : Coh ℤ k ↥(TLZero B ι₀)) :
    v ∈ LinearMap.range (lineRho (B := B) (ι₀ := ι₀) k)
      ↔ lineR (B := B) (ι₀ := ι₀) k v
          = lineR (B := B) (ι₀ := ι₀) k
              (lineRho (B := B) (ι₀ := ι₀) k (lineP (B := B) (ι₀ := ι₀) k v)) := by
  constructor
  · rintro ⟨y, rfl⟩
    have h := LinearMap.congr_fun (lineP_comp_lineRho (B := B) (ι₀ := ι₀) k) y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
    rw [h]
  · intro hv
    refine ⟨lineP (B := B) (ι₀ := ι₀) k v, ?_⟩
    have hzero : lineR (B := B) (ι₀ := ι₀) k
        (v - lineRho (B := B) (ι₀ := ι₀) k (lineP (B := B) (ι₀ := ι₀) k v)) = 0 := by
      rw [map_sub, hv, sub_self]
    have hpzero : lineP (B := B) (ι₀ := ι₀) k
        (v - lineRho (B := B) (ι₀ := ι₀) k (lineP (B := B) (ι₀ := ι₀) k v)) = 0 := by
      rw [map_sub]
      have h := LinearMap.congr_fun (lineP_comp_lineRho (B := B) (ι₀ := ι₀) k)
        (lineP (B := B) (ι₀ := ι₀) k v)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
      rw [h, sub_self]
    have hbot := eq_zero_of_sigmaPlus_sigmaMinus_eq_zero (B := B) (ι₀ := ι₀) k
      (v - lineRho (B := B) (ι₀ := ι₀) k (lineP (B := B) (ι₀ := ι₀) k v)) hpzero hzero
    exact (sub_eq_zero.mp hbot).symm

/-! ## The kernel and the image of the connecting homomorphism -/

/-- `ρ` has image the kernel of the connecting homomorphism `δ`. -/
theorem lineRho_range_eq_ker_pairδC (k : ℕ) :
    LinearMap.range (lineRho (B := B) (ι₀ := ι₀) k)
      = LinearMap.ker (pairδC (TLZero B ι₀) k).hom := by
  have hex := pairExact₃ (TLZero B ι₀) k
  have h := ShortComplex.Exact.moduleCat_range_eq_ker hex
  simpa only [lineRho, restrCoh] using h

/-- **The connecting homomorphism `δ : H^k(E∖0;ℤ) → H^{k+1}(E,E∖0;ℤ)` is surjective.** -/
theorem linePairδC_surjective (k : ℕ) :
    Function.Surjective (pairδC (TLZero B ι₀) k).hom := by
  have hrel : (relToAbs ℤ (TLZero B ι₀) (k + 1)).hom = 0 := by
    apply LinearMap.ext
    intro y
    have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (relToAbs_comp_CohMap_subtype ℤ (TLZero B ι₀) (k + 1))) y
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
      LinearMap.zero_apply] at h
    have hinv := LinearMap.congr_fun
      (sigmaPlus_cohmMap_subtypeMap (B := B) (ι₀ := ι₀) (k + 1))
      ((relToAbs ℤ (TLZero B ι₀) (k + 1)).hom y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hinv
    simp only [h, map_zero] at hinv
    exact hinv.symm
  have hex := pairExact₁ (TLZero B ι₀) k
  have h := ShortComplex.Exact.moduleCat_range_eq_ker hex
  have htop : LinearMap.range (pairδC (TLZero B ι₀) k).hom = ⊤ := by
    rw [h, hrel, LinearMap.ker_zero]
  intro w
  have : w ∈ LinearMap.range (pairδC (TLZero B ι₀) k).hom := by
    rw [htop]
    exact Submodule.mem_top
  exact this

/-! ## The bijectivity of `Φ` -/

/-- **Injectivity** of `x ↦ δ(s x ⌣ u)`. -/
theorem linePhi_ker_eq_bot (k : ℕ) : LinearMap.ker (linePhi (B := B) (ι₀ := ι₀) k) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hx' : (pairδC (TLZero B ι₀) k).hom
      (lineCupLM (B := B) (ι₀ := ι₀) k (lineS (B := B) (ι₀ := ι₀) k x)) = 0 := by
    rw [← linePhi_apply]
    exact hx
  have hmem : lineCupLM (B := B) (ι₀ := ι₀) k (lineS (B := B) (ι₀ := ι₀) k x)
      ∈ LinearMap.range (lineRho (B := B) (ι₀ := ι₀) k) := by
    rw [lineRho_range_eq_ker_pairδC]
    exact hx'
  obtain ⟨y, hy⟩ := hmem
  have hy0 : y = 0 := by
    have h1 := LinearMap.congr_fun (lineP_comp_lineRho (B := B) (ι₀ := ι₀) k) y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
    have h2 : lineP (B := B) (ι₀ := ι₀) k (lineRho (B := B) (ι₀ := ι₀) k y) = 0 := by
      rw [hy, lineP_lineCup_lineS]
    rw [h1] at h2
    exact h2
  have hcup : lineCupLM (B := B) (ι₀ := ι₀) k (lineS (B := B) (ι₀ := ι₀) k x) = 0 := by
    rw [← hy, hy0, map_zero]
  have hpi : linePi (B := B) (ι₀ := ι₀) k x = 0 := by
    rw [← lineR_lineCup_lineS (B := B) (ι₀ := ι₀) k x, hcup, map_zero]
  exact linePi_injective (B := B) (ι₀ := ι₀) k (by rw [hpi, map_zero])

/-- **Surjectivity** of `x ↦ δ(s x ⌣ u)`. -/
theorem linePhi_surjective (k : ℕ) : Function.Surjective (linePhi (B := B) (ι₀ := ι₀) k) := by
  intro w
  obtain ⟨v, hv⟩ := linePairδC_surjective (B := B) (ι₀ := ι₀) k w
  obtain ⟨x, hx⟩ := linePi_surjective (B := B) (ι₀ := ι₀) k
    (lineR (B := B) (ι₀ := ι₀) k v
      - lineR (B := B) (ι₀ := ι₀) k
          (lineRho (B := B) (ι₀ := ι₀) k (lineP (B := B) (ι₀ := ι₀) k v)))
  refine ⟨x, ?_⟩
  have hp : lineP (B := B) (ι₀ := ι₀) k
      (v - lineCupLM (B := B) (ι₀ := ι₀) k (lineS (B := B) (ι₀ := ι₀) k x))
      = lineP (B := B) (ι₀ := ι₀) k v := by
    rw [map_sub, lineP_lineCup_lineS, sub_zero]
  have hr : lineR (B := B) (ι₀ := ι₀) k
      (v - lineCupLM (B := B) (ι₀ := ι₀) k (lineS (B := B) (ι₀ := ι₀) k x))
      = lineR (B := B) (ι₀ := ι₀) k v - linePi (B := B) (ι₀ := ι₀) k x := by
    rw [map_sub, lineR_lineCup_lineS]
  have hmem : v - lineCupLM (B := B) (ι₀ := ι₀) k (lineS (B := B) (ι₀ := ι₀) k x)
      ∈ LinearMap.range (lineRho (B := B) (ι₀ := ι₀) k) := by
    rw [lineRho_range_iff, hp, hr, hx]
    abel
  have hker : (pairδC (TLZero B ι₀) k).hom
      (v - lineCupLM (B := B) (ι₀ := ι₀) k (lineS (B := B) (ι₀ := ι₀) k x)) = 0 := by
    rw [← LinearMap.mem_ker, ← lineRho_range_eq_ker_pairδC]
    exact hmem
  rw [map_sub, sub_eq_zero] at hker
  rw [linePhi_apply, ← hker, hv]

/-- **The Thom isomorphism for the trivial line bundle, up to sign**: `x ↦ δ(s x ⌣ u)` is
bijective. -/
theorem linePhi_bijective (k : ℕ) : Function.Bijective (linePhi (B := B) (ι₀ := ι₀) k) :=
  ⟨(LinearMap.ker_eq_bot.mp (linePhi_ker_eq_bot (B := B) (ι₀ := ι₀) k)),
    linePhi_surjective (B := B) (ι₀ := ι₀) k⟩

/-! ## The Thom map -/

/-- `(-1)^k` is its own inverse in `ℤ`. -/
theorem negOnePow_mul_self (k : ℕ) : ((-1 : ℤ) ^ k) * ((-1 : ℤ) ^ k) = 1 := by
  rw [← pow_add, show k + k = 2 * k from (Nat.two_mul k).symm, pow_mul,
    show ((-1 : ℤ)) ^ 2 = 1 by norm_num, one_pow]

/-- **The Thom map of the trivial line bundle is `(-1)^k` times `Φ`.**  This is the derivation rule
for the connecting homomorphism applied to `π^*(x) ⌣ δ u`. -/
theorem thomMap_trivial_line_eq (k : ℕ) (x : Coh ℤ k B) :
    (thomMap (RealBundle.trivial B ℝ ι₀) 1 (lineTau (B := B) (ι₀ := ι₀)) k) x
      = ((-1 : ℤ) ^ k) • linePhi (B := B) (ι₀ := ι₀) k x := by
  rw [thomMap_apply, linePhi_apply]
  have hder := Work.Sph3Disc.pairDelta_mixedCup_general
    (TopCat.of (TLTotal B ι₀)) (TLZero B ι₀) k 0
    (linePi (B := B) (ι₀ := ι₀) k x) (lineU (B := B) (ι₀ := ι₀))
  have hM : (mixedCupC ℤ (TLZero B ι₀) k 1 (linePi (B := B) (ι₀ := ι₀) k x)
        (lineTau (B := B) (ι₀ := ι₀)))
      = ((-1 : ℤ) ^ k) • (pairδC (TLZero B ι₀) k).hom
          (lineCupLM (B := B) (ι₀ := ι₀) k
            (lineRho (B := B) (ι₀ := ι₀) k (linePi (B := B) (ι₀ := ι₀) k x))) := by
    have hder' : (pairδC (TLZero B ι₀) k).hom
          (lineCupLM (B := B) (ι₀ := ι₀) k
            (lineRho (B := B) (ι₀ := ι₀) k (linePi (B := B) (ι₀ := ι₀) k x)))
        = ((-1 : ℤ) ^ k) • (mixedCupC ℤ (TLZero B ι₀) k 1
            (linePi (B := B) (ι₀ := ι₀) k x) (lineTau (B := B) (ι₀ := ι₀))) := hder
    have hcs : ((-1 : ℤ) ^ k) • (((-1 : ℤ) ^ k) • (mixedCupC ℤ (TLZero B ι₀) k 1
        (linePi (B := B) (ι₀ := ι₀) k x) (lineTau (B := B) (ι₀ := ι₀))))
        = mixedCupC ℤ (TLZero B ι₀) k 1 (linePi (B := B) (ι₀ := ι₀) k x)
            (lineTau (B := B) (ι₀ := ι₀)) := by
      rw [smul_smul, negOnePow_mul_self k, one_smul]
    rw [← hcs]
    exact (congrArg (fun z => ((-1 : ℤ) ^ k) • z) hder').symm
  rw [hM, lineS_apply_eq]

/-- **The Thom map of the trivial line bundle is bijective in every degree** — the suspension
isomorphism `H^k(B;ℤ) ≅ H^{k+1}(E,E∖0;ℤ)`. -/
theorem bijective_thomMap_trivial_line (k : ℕ) :
    Function.Bijective (thomMap (RealBundle.trivial B ℝ ι₀) 1
      (lineTau (B := B) (ι₀ := ι₀)) k) := by
  have hb := linePhi_bijective (B := B) (ι₀ := ι₀) k
  have hc := negOnePow_mul_self k
  refine ⟨fun x y hxy => hb.injective ?_, fun w => ?_⟩
  · have h1 := thomMap_trivial_line_eq (B := B) (ι₀ := ι₀) k x
    have h2 := thomMap_trivial_line_eq (B := B) (ι₀ := ι₀) k y
    have h3 : ((-1 : ℤ) ^ k) • linePhi (B := B) (ι₀ := ι₀) k x
        = ((-1 : ℤ) ^ k) • linePhi (B := B) (ι₀ := ι₀) k y := by
      rw [← h1, hxy, h2]
    have h5 := congrArg (fun z => ((-1 : ℤ) ^ k) • z) h3
    have h6 : ((-1 : ℤ) ^ k) • (((-1 : ℤ) ^ k) • linePhi (B := B) (ι₀ := ι₀) k x)
        = linePhi (B := B) (ι₀ := ι₀) k x := by
      simp only [smul_smul, hc, one_smul]
    have h7 : ((-1 : ℤ) ^ k) • (((-1 : ℤ) ^ k) • linePhi (B := B) (ι₀ := ι₀) k y)
        = linePhi (B := B) (ι₀ := ι₀) k y := by
      simp only [smul_smul, hc, one_smul]
    exact h6.symm.trans (h5.trans h7)
  · obtain ⟨x, hx⟩ := hb.surjective (((-1 : ℤ) ^ k) • w)
    refine ⟨x, ?_⟩
    rw [thomMap_trivial_line_eq, hx, smul_smul, hc, one_smul]

/-- **The Thom class of the trivial line bundle exists**: for every topological space `B` the
trivial real line bundle `B × ℝ → B` is oriented in the strong sense of having a Thom class.  This
is the suspension isomorphism `H^k(B;ℤ) ≅ H^{k+1}(B × ℝ, B × ℝ^*;ℤ)`. -/
theorem nonempty_thomClass_trivial_line :
    Nonempty (ThomClass (RealBundle.trivial B ℝ ι₀) 1) :=
  ⟨⟨lineTau (B := B) (ι₀ := ι₀),
    fun k => bijective_thomMap_trivial_line (B := B) (ι₀ := ι₀) k⟩⟩

end

end Work.Thom
