import Mathlib
import Submission.Work.Drive.encFamQ0
import Submission.Work.Drive.contDiffAt_chartDiff3_family_fin
import Submission.Work.Drive.surjective_paramDeriv_encFamQ0

/-!
# The parameter space of the ends-clause family, as `𝔼¹⁸`

The corrected ends-clause family `Work.Drive.encFamQ0` (`Drive/encFamQ0.lean`) is parametrised by the
nested product

> `EncParQ0 = 𝔼⁴ × 𝔼⁴ × 𝔼⁴ × 𝔼⁴ × ℝ × ℝ`

(the class-perturbation parameter `p`, the three shear parameters `q₀, q₁, q₂` and the two level
twists `r₁, r₂`).  The parametric Sard `Work.Drive.localSard_family_in_open`, on the other hand, takes
its family on a *single* Euclidean space `𝔼ᵐ`.  This module supplies the missing bridge:

* `Work.Drive.encParEquiv : 𝔼¹⁸ ≃L[ℝ] EncParQ0`, the coordinate linear isometry
  (`EuclideanSpace.finAddEquivProd` nested six times, `𝔼¹ ≅ ℝ` for the two level parameters);
* **`Work.Drive.hrich_reparam_encParEquiv`** — the **richness transfer**: if a family
  `G : EncParQ0 → Fin 3 → 𝔼³ → M` has the pointwise parameter-surjectivity of the charted
  triple-difference map (the form in which `surjective_paramDeriv_encFamQ0` provides it for
  `encFamQ0`), then the *reparametrised* family `s ↦ G (encParEquiv s)` satisfies the richness
  hypothesis `hrich` of `localSard_family_in_open` (for `m = 18`).

The proof is the chain rule: `(chartDiff3 of the reparametrised family) = (chartDiff3 of G) ∘
encParEquiv`, so its derivative is the composite of the derivative of `G`'s charted map with the
surjective linear map `encParEquiv`; differentiability of `G`'s charted map at `encParEquiv s` is
obtained from the smoothness of the reparametrised charted map
(`Work.Drive.contDiffAt_chartDiff3_family_fin`) by composing with `encParEquiv.symm`.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology

noncomputable section

/-- `𝔼¹ ≅ ℝ` (the level parameters of the ends-clause family are scalars). -/
def euclOne : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 1 => ℝ)).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)

/-- **The parameter space of the corrected ends-clause family, as `𝔼¹⁸`.** -/
def encParEquiv : EuclideanSpace ℝ (Fin 18) ≃L[ℝ] EncParQ0 :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 4) (m := 14)).trans <|
    ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ _) <|
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 4) (m := 10)).trans <|
        ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ _) <|
          (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 4) (m := 6)).trans <|
            ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ _) <|
              (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 4) (m := 2)).trans <|
                ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ _) <|
                  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)).trans <|
                    ContinuousLinearEquiv.prodCongr euclOne euclOne

/-- **The richness transfer along the reparametrisation `encParEquiv`.**  Given a family `G` on the
nested product `EncParQ0` whose charted triple-difference map has surjective parameter derivative at
every zero (with the natural pointwise chart-residency hypothesis), the reparametrised family satisfies
the richness hypothesis of `Work.Drive.localSard_family_in_open` with `m = 18`. -/
theorem hrich_reparam_encParEquiv {ι : Type*} [Fintype ι] (M : ι → Type*)
    [∀ j, TopologicalSpace (M j)] [∀ j, T2Space (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin 4)) (M j)]
    [∀ j, IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (M j)]
    (G : ∀ j, EncParQ0 → Fin 3 → EuclideanSpace ℝ (Fin 3) → M j)
    (hG : ∀ j k, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 18) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 18) × EuclideanSpace ℝ (Fin 3) => G j (encParEquiv q.1) k q.2))
    (hsurj : ∀ j (p : M j) (t : EncParQ0) (y : EuclideanSpace ℝ (Fin 9)),
      (∀ k : Fin 3, G j t k (TParity.bPartC k y) ∈ (chr p).source) →
      TParity.chartDiff3 p (G j t) y = 0 →
      Function.Surjective
        (fderiv ℝ (fun t' : EncParQ0 => TParity.chartDiff3 p (G j t') y) t)) :
    ∀ j (p : M j) (K : Set (EuclideanSpace ℝ (Fin 9))) (s₀ : EuclideanSpace ℝ (Fin 18)) (δ : ℝ),
      IsCompact K → 0 < δ →
      (∀ (s : EuclideanSpace ℝ (Fin 18)) (y : EuclideanSpace ℝ (Fin 9)), ‖s - s₀‖ < δ → y ∈ K →
        ∀ k : Fin 3, G j (encParEquiv s) k (TParity.bPartC k y) ∈ (chr p).source) →
      ∀ (s : EuclideanSpace ℝ (Fin 18)) (y : EuclideanSpace ℝ (Fin 9)), ‖s - s₀‖ < δ → y ∈ K →
        TParity.chartDiff3 p (fun k x => G j (encParEquiv s) k x) y = 0 →
        Function.Surjective (fderiv ℝ (fun s' : EuclideanSpace ℝ (Fin 18) =>
          TParity.chartDiff3 p (fun k x => G j (encParEquiv s') k x) y) s) := by
  intro j p K s₀ δ hK hδ hres s y hs hyK hzero
  -- the pointwise residency at `s`, transported to `encParEquiv s`
  have hreg : ∀ k : Fin 3, G j (encParEquiv s) k (TParity.bPartC k y) ∈ (chr p).source :=
    hres s y hs hyK
  -- differentiability of the reparametrised charted map, from the joint smoothness
  have hC : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 18) × EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (fun k x => G j (encParEquiv q.1) k x) q.2) (s, y) :=
    contDiffAt_chartDiff3_family_fin 18
      (fun s' k x => G j (encParEquiv s') k x) (hG j) p s hreg
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
    rw [ne_eq, ← WithTop.coe_zero]
    intro h
    exact ENat.top_ne_zero (WithTop.coe_injective h)
  have hd1 : DifferentiableAt ℝ
      (fun s' : EuclideanSpace ℝ (Fin 18) =>
        TParity.chartDiff3 p (fun k x => G j (encParEquiv s') k x) y) s := by
    have hslice : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s' : EuclideanSpace ℝ (Fin 18) => (s', y)) s :=
      ContDiffAt.prodMk contDiffAt_id contDiffAt_const
    exact (hC.comp s hslice).differentiableAt hne
  -- the nested-product charted map, differentiable at `encParEquiv s`
  have hdF : DifferentiableAt ℝ
      (fun t' : EncParQ0 => TParity.chartDiff3 p (G j t') y) (encParEquiv s) := by
    have hd1' : HasFDerivAt ((fun s' : EuclideanSpace ℝ (Fin 18) =>
          TParity.chartDiff3 p (fun k x => G j (encParEquiv s') k x) y))
        (fderiv ℝ ((fun s' : EuclideanSpace ℝ (Fin 18) =>
          TParity.chartDiff3 p (fun k x => G j (encParEquiv s') k x) y))
          (encParEquiv.symm (encParEquiv s))) (encParEquiv.symm (encParEquiv s)) := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hd1.hasFDerivAt
    have h : HasFDerivAt ((fun s' : EuclideanSpace ℝ (Fin 18) =>
          TParity.chartDiff3 p (fun k x => G j (encParEquiv s') k x) y) ∘ ⇑encParEquiv.symm) _
        (encParEquiv s) :=
      hd1'.comp (encParEquiv s)
        (ContinuousLinearMap.hasFDerivAt (encParEquiv.symm : EncParQ0 →L[ℝ] EuclideanSpace ℝ (Fin 18)))
    have hfun : ((fun s' : EuclideanSpace ℝ (Fin 18) =>
          TParity.chartDiff3 p (fun k x => G j (encParEquiv s') k x) y) ∘ ⇑encParEquiv.symm)
        = fun t' : EncParQ0 => TParity.chartDiff3 p (G j t') y := by
      funext t'
      simp only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply]
    rw [hfun] at h
    exact h.differentiableAt
  -- the chain rule
  have hchain : fderiv ℝ (fun s' : EuclideanSpace ℝ (Fin 18) =>
        TParity.chartDiff3 p (fun k x => G j (encParEquiv s') k x) y) s
      = (fderiv ℝ (fun t' : EncParQ0 => TParity.chartDiff3 p (G j t') y) (encParEquiv s)).comp
          (encParEquiv : EuclideanSpace ℝ (Fin 18) →L[ℝ] EncParQ0) := by
    have h := (hdF.hasFDerivAt).comp s
      (ContinuousLinearMap.hasFDerivAt (encParEquiv : EuclideanSpace ℝ (Fin 18) →L[ℝ] EncParQ0))
    exact h.fderiv
  rw [hchain]
  have h0 : TParity.chartDiff3 p (G j (encParEquiv s)) y = 0 := hzero
  exact ((hsurj j p (encParEquiv s) y hreg h0).comp encParEquiv.surjective)

end

end Work.Drive
