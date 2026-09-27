import Mathlib
import Submission.Work.Projection.exists_good_direction
import Submission.Work.Projection.compact_embedding

/-!
# A smooth map which is injective and immersive on a compact set

For a compact set `K` in a second countable smooth `n`-manifold `M` we construct a smooth map
`φ : M → ℝ^{2n+1+m}` (for some `m`) which is injective on `K` and has injective `mfderiv` at every
point of `K`.

The construction is Whitney's partition-of-unity argument, restricted to `K`:

* `K` is closed (`IsCompact.isClosed`), and since `M` is second countable and locally compact it is
  `σ`-compact; Mathlib's `SmoothBumpCovering.exists_isSubordinate` therefore provides a smooth bump
  covering of `K`.  Its index type need not be finite, but by compactness of `K` and local
  finiteness of the supports only finitely many bumps meet `K`, and we pass to that finite
  subcovering.
* For a finite smooth bump covering `f` of `K` the "tangent map"
  `Φ p = ((f i p • extChartAt _ (f.c i) p)_i, (f i p)_i) : M → (ι → ℝ^n × ℝ)` is smooth
  (`piTangent`, `contMDiff_piTangent`), injective on `K` (`piTangent_injOn`) and has injective
  derivative on `K` (`piTangent_injective_mfderiv`).  These three lemmas are the restriction to a
  compact set of the (module-private) construction of
  `Mathlib/Geometry/Manifold/WhitneyEmbedding.lean`.
* Transporting along a linear isometry equivalence `ι → ℝ^n × ℝ ≃L[ℝ] ℝ^N` and padding by zeros
  with `Work.Projection.pad` finishes the proof.
-/

open scoped Manifold ContDiff
open Topology Function Set

namespace Work.Noncompact

section Bump

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- The "tangent map" of a smooth bump covering: at each point it records the chart coordinates
weighted by the bump functions, together with the values of the bump functions. -/
noncomputable def piTangent {ι : Type*} [Fintype ι] {s : Set M}
    (f : SmoothBumpCovering ι (𝓡 n) M s) :
    M → (ι → EuclideanSpace ℝ (Fin n) × ℝ) :=
  fun x i => (f i x • extChartAt (𝓡 n) (f.c i) x, f i x)

lemma piTangent_coe {ι : Type*} [Fintype ι] {s : Set M}
    (f : SmoothBumpCovering ι (𝓡 n) M s) :
    piTangent f = fun x i => (f i x • extChartAt (𝓡 n) (f.c i) x, f i x) := rfl

lemma piTangent_injOn {ι : Type*} [Fintype ι] {s : Set M}
    (f : SmoothBumpCovering ι (𝓡 n) M s) : InjOn (piTangent f) s := by
  intro x hx y _ h
  simp only [piTangent, funext_iff] at h
  obtain ⟨h₁, h₂⟩ := Prod.mk_inj.1 (h (f.ind x hx))
  rw [f.apply_ind x hx] at h₂
  rw [← h₂, f.apply_ind x hx, one_smul, one_smul] at h₁
  have := f.mem_extChartAt_source_of_eq_one h₂.symm
  exact (extChartAt (𝓡 n) (f.c _)).injOn (f.mem_extChartAt_ind_source x hx) this h₁

variable [IsManifold (𝓡 n) ∞ M] [T2Space M]

lemma contMDiff_piTangent {ι : Type*} [Fintype ι] {s : Set M}
    (f : SmoothBumpCovering ι (𝓡 n) M s) :
    ContMDiff (𝓡 n) (𝓘(ℝ, ι → EuclideanSpace ℝ (Fin n) × ℝ)) ∞ (piTangent f) := by
  rw [contMDiff_pi_space]
  intro i
  exact ((f i).contMDiff_smul contMDiffOn_extChartAt).prodMk_space (f i).contMDiff

/-- The `i`-th component of the tangent map, composed with the derivative, is the derivative of the
chart at the centre of the `i`-th bump function (the bump is eventually `1` at `x`). -/
lemma comp_piTangent_mfderiv {ι : Type*} [Fintype ι] {s : Set M}
    (f : SmoothBumpCovering ι (𝓡 n) M s) (x : M) (hx : x ∈ s) :
    ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ).comp
            (@ContinuousLinearMap.proj ℝ _ ι (fun _ => EuclideanSpace ℝ (Fin n) × ℝ) _ _
              (fun _ => inferInstance) (f.ind x hx))).comp
        (mfderiv (𝓡 n) (𝓘(ℝ, ι → EuclideanSpace ℝ (Fin n) × ℝ)) (piTangent f) x) =
      mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) (f.c (f.ind x hx))) x := by
  set L :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ).comp
      (@ContinuousLinearMap.proj ℝ _ ι (fun _ => EuclideanSpace ℝ (Fin n) × ℝ) _ _
        (fun _ => inferInstance) (f.ind x hx))
  have := L.hasMFDerivAt.comp x
    ((contMDiff_piTangent f).mdifferentiableAt (by simp)).hasMFDerivAt
  convert! hasMFDerivAt_unique this _
  refine (hasMFDerivAt_extChartAt (f.mem_chartAt_ind_source x hx)).congr_of_eventuallyEq ?_
  refine (f.eventuallyEq_one x hx).mono fun y hy => ?_
  simp only [L, piTangent_coe, ContinuousLinearMap.coe_comp, (· ∘ ·),
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply]
  rw [hy, Pi.one_apply, one_smul]

lemma piTangent_ker_mfderiv {ι : Type*} [Fintype ι] {s : Set M}
    (f : SmoothBumpCovering ι (𝓡 n) M s) (x : M) (hx : x ∈ s) :
    (mfderiv (𝓡 n) (𝓘(ℝ, ι → EuclideanSpace ℝ (Fin n) × ℝ)) (piTangent f) x).ker = ⊥ := by
  apply bot_unique
  rw [← (mdifferentiable_chart (f.c (f.ind x hx))).ker_mfderiv_eq_bot
      (f.mem_chartAt_ind_source x hx),
    ← comp_piTangent_mfderiv f x hx]
  exact LinearMap.ker_le_ker_comp _ _

lemma piTangent_injective_mfderiv {ι : Type*} [Fintype ι] {s : Set M}
    (f : SmoothBumpCovering ι (𝓡 n) M s) (x : M) (hx : x ∈ s) :
    Injective (mfderiv (𝓡 n) (𝓘(ℝ, ι → EuclideanSpace ℝ (Fin n) × ℝ)) (piTangent f) x) :=
  LinearMap.ker_eq_bot.1 (piTangent_ker_mfderiv f x hx)

end Bump

noncomputable section Main

open Work.Projection

/-- For every compact `K` in a second countable smooth `n`-manifold there is a smooth map into some
`ℝ^{2n+1+m}` that is injective on `K` and has injective derivative at every point of `K`. -/
theorem exists_local_map {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
    [SecondCountableTopology M] (K : Set M) (hK : IsCompact K) :
    ∃ (m : ℕ) (φ : M → EuclideanSpace ℝ (Fin (2 * n + 1 + m))),
      ContMDiff (𝓡 n) (𝓡 (2 * n + 1 + m)) ∞ φ ∧ Set.InjOn φ K ∧
      ∀ x ∈ K, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1 + m)) φ x) := by
  classical
  haveI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  haveI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  -- a smooth bump covering of the compact set `K`
  obtain ⟨ι, f, _⟩ := SmoothBumpCovering.exists_isSubordinate (𝓡 n) (s := K)
    (U := fun x : M => (chartAt (EuclideanSpace ℝ (Fin n)) x).source) hK.isClosed
    (fun x _ => (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds
      (mem_chart_source _ x))
  -- only finitely many bumps meet `K`
  let I : Set ι := {i | (support (f i) ∩ K).Nonempty}
  have hIfin : I.Finite := by
    simpa only [I] using f.locallyFinite.finite_nonempty_inter_compact hK
  haveI : Fintype I := hIfin.fintype
  -- the finite subcovering
  let g : SmoothBumpCovering I (𝓡 n) M K :=
    { c := fun j => f.c j.1
      toFun := fun j => f j.1
      c_mem' := fun j => f.c_mem' j.1
      locallyFinite' := locallyFinite_of_finite _
      eventuallyEq_one' := by
        intro x hx
        obtain ⟨i, hi⟩ := f.eventuallyEq_one' x hx
        refine ⟨⟨i, ?_⟩, hi⟩
        have hxs : x ∈ support (f i) := by
          rw [mem_support, hi.eq_of_nhds]
          norm_num
        exact ⟨x, hxs, hx⟩ }
  -- transport to a Euclidean space and pad by zeros
  let N : ℕ := Module.finrank ℝ (I → EuclideanSpace ℝ (Fin n) × ℝ)
  have hfr : Module.finrank ℝ (I → EuclideanSpace ℝ (Fin n) × ℝ) = N := rfl
  let eEF : (I → EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin N) :=
    ContinuousLinearEquiv.ofFinrankEq (by
      rw [hfr]
      exact (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := N)).symm)
  have hle : N ≤ 2 * n + 1 + N := by omega
  have hg : ContMDiff (𝓡 n) (𝓘(ℝ, I → EuclideanSpace ℝ (Fin n) × ℝ)) ∞ (piTangent g) :=
    contMDiff_piTangent g
  have hinner : ContMDiff (𝓡 n) (𝓡 N) ∞ (⇑eEF ∘ piTangent g) :=
    eEF.toDiffeomorph.contMDiff.comp hg
  refine ⟨N, ⇑(pad hle) ∘ (⇑eEF ∘ piTangent g), ?_, ?_, ?_⟩
  · exact contMDiff_comp_clm (pad hle) _ hinner
  · intro p hp q hq hpq
    exact piTangent_injOn g hp hq (eEF.injective (pad_injective hle hpq))
  · intro x hx
    rw [mfderiv_comp_clm (pad hle) (⇑eEF ∘ piTangent g) hinner x]
    rw [mfderiv_comp x eEF.differentiableAt.mdifferentiableAt
      (hg.mdifferentiableAt (by simp)), eEF.mfderiv_eq]
    exact (pad_injective hle).comp (eEF.injective.comp (piTangent_injective_mfderiv g x hx))

end Main

end Work.Noncompact
