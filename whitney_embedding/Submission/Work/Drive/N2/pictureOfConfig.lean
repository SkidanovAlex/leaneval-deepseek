import Mathlib
import Submission.Work.Drive.N2.roundConfigPictureGlobal

/-!
# The picture of a level set carried by a single labelled round configuration

`Work.Drive.N2.roundConfigPictureGlobal` produces the picture family of a *path* of labelled round
configurations.  The bands of the assembly need the special case of a *constant* path: a single
configuration `D` of `m` disjoint round circles drawn along the `m` components of a regular level set
`Λ = f ⁻¹' {b}`, extended to a globally smooth `A : M → ℝ³` which is injective on `Λ` and `ker df`-
immersive there.  That is exactly the picture `Work.Drive.N2.goodDrawingOn_band` consumes (its `A`,
`hAinj`, `hAimm`), so the bands are drawn by `goodDrawingOn_band` with `A` and the shared flow, with no
isotopy at all.

The construction is `roundConfigPictureGlobal` with `D s := D` (the smoothness rows of a constant path
are trivial).
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set

/-- **The picture of a level carried by one labelled round configuration.** -/
theorem exists_picture_of_config {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {b : ℝ} {n : ℕ} (γ : Fin n → ℝ → M)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = b → ¬ Work.Drive.Morse.IsCritical f x)
    (hγsm : ∀ i, ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (γ i))
    (hγval : ∀ (i : Fin n) (x : ℝ), f (γ i x) = b)
    (hγper : ∀ i x, γ i (x + 1) = γ i x)
    (hγinj : ∀ i, Set.InjOn (γ i) (Set.Ico 0 1))
    (hγlev : ∀ x : M, f x = b → ∃ (i : Fin n) (t : ℝ), x = γ i t)
    (hγdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i)) (Set.range (γ j)))
    (hγker : ∀ (i : Fin n) (x : ℝ) (v : TangentSpace (𝓡 2) (γ i x)),
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (γ i x) v = 0 →
        ∃ t : ℝ, mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ i) x t = v)
    (D : Work.Drive.N2.RoundConfig n) (hD : D.Disjoint) :
    ∃ A : M → EuclideanSpace ℝ (Fin 3),
      ContMDiff (𝓡 2) (𝓡 3) ∞ A ∧
      (∀ (i : Fin n) (x : ℝ), A (γ i x) = D.circle i x) ∧
      (∀ x y : M, (∃ (i : Fin n) (t : ℝ), x = γ i t) →
        (∃ (j : Fin n) (u : ℝ), y = γ j u) → A x = A y → x = y) ∧
      (∀ x : M, (∃ (i : Fin n) (t : ℝ), x = γ i t) →
        ∀ v : TangentSpace (𝓡 2) x, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
          mfderiv (𝓡 2) (𝓡 3) A x v = 0 → v = 0) := by
  obtain ⟨P, hPval, hPinj, hPimm, hPsm⟩ :=
    Work.Drive.N2.roundConfigPictureGlobal (f := f) (b := b) (D := fun _ : ℝ => D) γ
      hf hreg hγsm hγval hγper hγinj hγlev hγdisj hγker
      (fun _ => hD)
      (fun i => contDiff_const) (fun i => contDiff_const) (fun i => contDiff_const)
  exact ⟨P 0, hPsm.comp (contMDiff_const.prodMk contMDiff_id),
    fun i x => hPval 0 i x, fun x y hx hy => hPinj 0 x y hx hy,
    fun x hx v hv hv' => hPimm 0 x hx v hv hv'⟩

end Work.Drive.N2
