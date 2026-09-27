import Mathlib
import Submission.Work.Drive.PushDisc.milnorLens
import Submission.Work.Drive.PushDisc.injOn_nhds_of_compact_euclidean
import Submission.Work.Whitney.CutPush.collar_injectivity

/-!
# Injectivity in a neighbourhood of the lens

This file proves `Work.Drive.PushDisc.lensNhd`: a smooth map `Δ : ℝ × ℝ → Mdl k` which is injective
on the closed lens `lensK` and whose derivative is injective at every point of `lensK` is injective,
with injective derivative, on a closed thickening `Metric.cthickening ε lensK` of the lens.

The two inputs are the standard ones.

* Injectivity propagates from the compact set `lensK` by the topological brick
  `Work.Routing.injOn_nhds_of_compact_of_locallyInjOn`, the local injectivity coming from the
  inverse function theorem (`local_injOn_of_injective_fderiv_normed` below, the general-normed-space
  form of `Work.Embedding.local_injOn_of_injective_fderiv`).
* Injectivity of the derivative is an *open* condition: for `A : ℝ × ℝ →L[ℝ] F` it says that the
  images of the two vectors of the basis `Module.Basis.finTwoProd ℝ` are independent, and
  independence is open (`isOpen_setOfPred_linearIndependent`).
-/

namespace Work.Drive.PushDisc

open scoped ContDiff
open Set Metric

/-! ### Openness of injectivity for maps out of `ℝ × ℝ` -/

/-- For a linear map `A : ℝ × ℝ →ₗ[ℝ] F`, injectivity is the independence of the images of the
two vectors of the standard basis of `ℝ × ℝ`. -/
theorem injective_iff_linearIndependent_finTwo {F : Type*} [AddCommGroup F] [Module ℝ F]
    (A : (ℝ × ℝ) →ₗ[ℝ] F) :
    Function.Injective A ↔
      LinearIndependent ℝ (fun i : Fin 2 => A ((Module.Basis.finTwoProd ℝ) i)) := by
  have hsum : ∀ x, (∑ i : Fin 2, ((Module.Basis.finTwoProd ℝ).repr x) i •
      (Module.Basis.finTwoProd ℝ) i) = x := fun x => (Module.Basis.finTwoProd ℝ).sum_repr x
  constructor
  · intro h
    exact (Module.Basis.linearIndependent (Module.Basis.finTwoProd ℝ)).map' A
      (LinearMap.ker_eq_bot.mpr h)
  · intro hli
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hcoef : ∀ i : Fin 2, ((Module.Basis.finTwoProd ℝ).repr v) i = 0 := by
      refine (Fintype.linearIndependent_iff.mp hli)
        (fun i => ((Module.Basis.finTwoProd ℝ).repr v) i) ?_
      have haux : A (∑ i : Fin 2, ((Module.Basis.finTwoProd ℝ).repr v) i •
          (Module.Basis.finTwoProd ℝ) i) =
          ∑ i : Fin 2, ((Module.Basis.finTwoProd ℝ).repr v) i •
            A ((Module.Basis.finTwoProd ℝ) i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => map_smul A _ _
      rw [← haux, hsum v, hv]
    have hveq : v = ∑ i : Fin 2, ((Module.Basis.finTwoProd ℝ).repr v) i •
        (Module.Basis.finTwoProd ℝ) i := (hsum v).symm
    rw [hveq]
    simp [hcoef]

/-- **Injectivity of a continuous linear map out of `ℝ × ℝ` is an open condition.** -/
theorem isOpen_setOf_injective_finTwo {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    IsOpen {A : (ℝ × ℝ) →L[ℝ] F | Function.Injective A} := by
  have hcont : Continuous fun A : (ℝ × ℝ) →L[ℝ] F =>
      fun i : Fin 2 => A ((Module.Basis.finTwoProd ℝ) i) :=
    continuous_pi fun i =>
      (ContinuousLinearMap.apply ℝ F ((Module.Basis.finTwoProd ℝ) i)).continuous
  have hopen : IsOpen {g : Fin 2 → F | LinearIndependent ℝ g} :=
    isOpen_setOfPred_linearIndependent
  have hset : {A : (ℝ × ℝ) →L[ℝ] F | Function.Injective A} =
      (fun A : (ℝ × ℝ) →L[ℝ] F =>
        fun i : Fin 2 => A ((Module.Basis.finTwoProd ℝ) i)) ⁻¹'
        {g : Fin 2 → F | LinearIndependent ℝ g} := by
    ext A
    exact injective_iff_linearIndependent_finTwo (A : (ℝ × ℝ) →ₗ[ℝ] F)
  rw [hset]
  exact hopen.preimage hcont

/-! ### Local injectivity from an injective derivative -/

/-- **Local injectivity of a smooth map with injective derivative**, in general normed spaces: if
`ψ : E → F` is `C^∞` on an open set `V` containing `u₀` (both `E` and `F` finite dimensional) and
`fderiv ℝ ψ u₀` is injective, then `ψ` is injective on some open neighbourhood of `u₀`. -/
theorem local_injOn_of_injective_fderiv_normed {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {ψ : E → F} {V : Set E} (hV : IsOpen V) {u₀ : E} (hu₀ : u₀ ∈ V)
    (hψ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ V)
    (hinj : Function.Injective (fderiv ℝ ψ u₀)) :
    ∃ W : Set E, IsOpen W ∧ u₀ ∈ W ∧ Set.InjOn ψ W := by
  classical
  set A : E →L[ℝ] F := fderiv ℝ ψ u₀ with hA
  -- a continuous linear left inverse `G` of `A`
  have hker : LinearMap.ker A.toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  obtain ⟨g, hg⟩ := A.toLinearMap.exists_leftInverse_of_injective hker
  let G : F →L[ℝ] E := LinearMap.toContinuousLinearMap g
  have hGA : G ∘L A = ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro v
    have hv := LinearMap.congr_fun hg v
    simpa [G] using hv
  have hnz : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hψat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ u₀ := hψ.contDiffAt (hV.mem_nhds hu₀)
  have hΨcont : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => G (ψ u)) u₀ :=
    G.contDiff.contDiffAt.comp u₀ hψat
  have hΨderiv : HasFDerivAt (fun u => G (ψ u)) (G ∘L A) u₀ :=
    HasFDerivAt.comp u₀ (G.hasFDerivAt (x := ψ u₀)) (hψat.differentiableAt hnz |>.hasFDerivAt)
  have hΨderiv' : HasFDerivAt (fun u => G (ψ u))
      ((ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E)) u₀ := by
    have h := hΨderiv.congr_fderiv hGA
    simpa [ContinuousLinearEquiv.coe_refl] using h
  have hS : HasStrictFDerivAt (fun u => G (ψ u))
      ((ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E)) u₀ :=
    hΨcont.hasStrictFDerivAt' hΨderiv' hnz
  -- the inverse function theorem: `G ∘ ψ` has a local left inverse at `u₀`
  obtain ⟨S, hSmem, hSinj⟩ := Filter.eventually_iff_exists_mem.mp hS.eventually_left_inverse
  obtain ⟨W, hWsub, hWopen, hu₀W⟩ := _root_.mem_nhds_iff.mp hSmem
  refine ⟨W, hWopen, hu₀W, ?_⟩
  intro a ha b hb hab
  have h1 := hSinj a (hWsub ha)
  have h2 := hSinj b (hWsub hb)
  rw [← h1, ← h2, congrArg G hab]

/-! ### The main statement -/

theorem lensNhd {k : ℕ}
    (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (hΔ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ)
    (hinj : Set.InjOn Δ Work.Drive.PushDisc.lensK)
    (hdΔ : ∀ p ∈ Work.Drive.PushDisc.lensK, Function.Injective (fderiv ℝ Δ p)) :
    ∃ ε : ℝ, 0 < ε ∧ Set.InjOn Δ (Metric.cthickening ε Work.Drive.PushDisc.lensK) ∧
      (∀ p ∈ Metric.cthickening ε Work.Drive.PushDisc.lensK,
        Function.Injective (fderiv ℝ Δ p)) := by
  -- local injectivity at the points of the lens
  have hloc : ∀ x ∈ lensK, ∃ U : Set (ℝ × ℝ), IsOpen U ∧ x ∈ U ∧ Set.InjOn Δ U :=
    fun x hx => local_injOn_of_injective_fderiv_normed isOpen_univ (Set.mem_univ x)
      hΔ.contDiffOn (hdΔ x hx)
  obtain ⟨T, hTopen, hKT, hTinj⟩ :=
    Work.Routing.injOn_nhds_of_compact_of_locallyInjOn isCompact_lensK hloc
      (fun x _ => hΔ.continuous.continuousAt) hinj
  -- the derivative stays injective near the lens, injectivity being an open condition
  have hnz : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hSopen : IsOpen {p : ℝ × ℝ | Function.Injective (fderiv ℝ Δ p)} :=
    isOpen_setOf_injective_finTwo.preimage (hΔ.continuous_fderiv hnz)
  obtain ⟨δ, hδpos, hδsub⟩ := isCompact_lensK.exists_cthickening_subset_open
    (hTopen.inter hSopen) fun p hp => ⟨hKT hp, hdΔ p hp⟩
  exact ⟨δ, hδpos, hTinj.mono (hδsub.trans Set.inter_subset_left), fun p hp => (hδsub hp).2⟩

end Work.Drive.PushDisc
