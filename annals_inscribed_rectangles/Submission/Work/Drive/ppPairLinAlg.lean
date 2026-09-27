import Mathlib
import Submission.Work.Drive.ppRegCoord

/-!
# The linear algebra of the `s = 0` face of the pair map of the radial collapse

At the base `s = 0` of the radial collapse the pair map of the transport degenerates: by the bridge
hypothesis `E 0 u = D 0 (mk3 u 1)` (`E' 0 u = D 0 (mk3 u 1)` as well) the two plane blocks depend only
on the plane parameter `u`, so the two blocks' *plane* derivatives **coincide** and are the restriction
of `mfderiv D 0` to the level-`0` hyperplane of the block-`0` parameter:

> `S := (mfderiv D 0 x₀) ∘ ins2`,    `ins2 (a) = (a 0, a 1, 0)`  (`Work.Drive.ins2`).

The two sweep blocks contribute `- mfderiv D 1 (x 1)` and `- mfderiv D 2 (x 2)`.  This file proves the
sharp linear-algebra statement behind the face clause of `Work.Drive.PPRegAt` at `s = 0`:

> the map `(u, y, z) ↦ (S u - dV y, S u - dW z)` is **onto** exactly when
> `range S ⊓ range dV ⊓ range dW = ⊥` **and** `S`, `dV`, `dW` are injective.

(Over `ℝ⁴` the domain `ℝ² × ℝ³ × ℝ³` and the target `ℝ⁴ × ℝ⁴` both have dimension `8`, so surjectivity
is equivalent to injectivity of the difference map; the kernel is computed below.)

## Why this is the face condition

`Work.Drive.PPRegAt` at a meet with `ftS x = 0` asks for the surjectivity of the **face-restricted**
derivative (the direction `ftS` frozen), and that restricted derivative is exactly the map above.  So
the face clause at `s = 0` is equivalent to the *sharp* hole

> `S.range ⊓ dV.range ⊓ dW.range = ⊥` **and** `S`, `dV`, `dW` injective

— which, as `Submission/Work/Drive/PPREGAT_S0_STATUS.md` §2–§3 records, is *not* an extra hypothesis:
it is implied by `Meet3Hyp M D` through the flat-solution cancellation
(`Work.Drive.exists_flat_solution_of_tripleTransverse`), the preimage of any target being shiftable by
a multiple of the common direction supplied by `Meet3Hyp.face` at the top-face triple point
`(mk3 (ftU x) 1, ftY x, ftZ x)`.  This file is the *sharp kernel form* of that statement and an
independent cross-check of the cancellation argument; the bridge itself
(`Work.Drive.ppRegAt_zero_of_meet3Hyp`) is on disk and sorry-free and does **not** need it.

-/

namespace Work.Drive

open scoped Manifold ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The first block projection of `ℝ² × (ℝ³ × ℝ³)`. -/
def ppProjU : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) →L[ℝ]
    EuclideanSpace ℝ (Fin 2) :=
  ContinuousLinearMap.fst ℝ _ _

/-- The second block projection of `ℝ² × (ℝ³ × ℝ³)`. -/
def ppProjY : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) →L[ℝ]
    EuclideanSpace ℝ (Fin 3) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

/-- The third block projection of `ℝ² × (ℝ³ × ℝ³)`. -/
def ppProjZ : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) →L[ℝ]
    EuclideanSpace ℝ (Fin 3) :=
  (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

@[simp] lemma ppProjU_apply (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) ×
    EuclideanSpace ℝ (Fin 3)) : ppProjU p = p.1 := rfl
@[simp] lemma ppProjY_apply (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) ×
    EuclideanSpace ℝ (Fin 3)) : ppProjY p = p.2.1 := rfl
@[simp] lemma ppProjZ_apply (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) ×
    EuclideanSpace ℝ (Fin 3)) : ppProjZ p = p.2.2 := rfl

/-- **The degenerate pair-difference map at `s = 0`**: the two blocks share the plane derivative `S`. -/
def pairDiffCLM (S : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) (dV dW : EuclideanSpace ℝ (Fin 3) →L[ℝ] E) :
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) →L[ℝ] E × E :=
  ((S.comp ppProjU) - (dV.comp ppProjY)).prod ((S.comp ppProjU) - (dW.comp ppProjZ))

@[simp] lemma pairDiffCLM_apply (S : EuclideanSpace ℝ (Fin 2) →L[ℝ] E)
    (dV dW : EuclideanSpace ℝ (Fin 3) →L[ℝ] E)
    (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    pairDiffCLM S dV dW p = (S p.1 - dV p.2.1, S p.1 - dW p.2.2) := rfl

/-- **The kernel of the degenerate pair-difference map, sharply.**  It vanishes exactly when the three
derivatives are injective and their images meet only in `0`. -/
theorem pairDiffCLM_ker_eq_bot_iff (S : EuclideanSpace ℝ (Fin 2) →L[ℝ] E)
    (dV dW : EuclideanSpace ℝ (Fin 3) →L[ℝ] E) :
    LinearMap.ker (pairDiffCLM S dV dW).toLinearMap = ⊥ ↔
      (S.range ⊓ dV.range ⊓ dW.range = ⊥ ∧ Function.Injective S ∧
        Function.Injective dV ∧ Function.Injective dW) := by
  have hkerS : ∀ u : EuclideanSpace ℝ (Fin 2), S u = 0 →
      (u, 0, 0) ∈ LinearMap.ker (pairDiffCLM S dV dW).toLinearMap := by
    intro u hu
    rw [LinearMap.mem_ker]
    change pairDiffCLM S dV dW (u, 0, 0) = 0
    rw [pairDiffCLM_apply, hu]
    simp
  have hkerV : ∀ y : EuclideanSpace ℝ (Fin 3), dV y = 0 →
      (0, y, 0) ∈ LinearMap.ker (pairDiffCLM S dV dW).toLinearMap := by
    intro y hy
    rw [LinearMap.mem_ker]
    change pairDiffCLM S dV dW (0, y, 0) = 0
    rw [pairDiffCLM_apply, hy]
    simp
  have hkerW : ∀ z : EuclideanSpace ℝ (Fin 3), dW z = 0 →
      (0, 0, z) ∈ LinearMap.ker (pairDiffCLM S dV dW).toLinearMap := by
    intro z hz
    rw [LinearMap.mem_ker]
    change pairDiffCLM S dV dW (0, 0, z) = 0
    rw [pairDiffCLM_apply, hz]
    simp
  constructor
  · intro h
    have hS : Function.Injective S := by
      intro u u' huu
      have h0 : S (u - u') = 0 := by rw [map_sub, huu, sub_self]
      have h2 : (u - u', 0, 0) ∈ LinearMap.ker (pairDiffCLM S dV dW).toLinearMap := hkerS _ h0
      rw [h, Submodule.mem_bot] at h2
      exact sub_eq_zero.mp (congrArg Prod.fst h2)
    have hV : Function.Injective dV := by
      intro y y' hyy
      have h0 : dV (y - y') = 0 := by rw [map_sub, hyy, sub_self]
      have h2 : (0, y - y', 0) ∈ LinearMap.ker (pairDiffCLM S dV dW).toLinearMap := hkerV _ h0
      rw [h, Submodule.mem_bot] at h2
      exact sub_eq_zero.mp (congrArg (fun p => p.2.1) h2)
    have hW : Function.Injective dW := by
      intro z z' hzz
      have h0 : dW (z - z') = 0 := by rw [map_sub, hzz, sub_self]
      have h2 : (0, 0, z - z') ∈ LinearMap.ker (pairDiffCLM S dV dW).toLinearMap := hkerW _ h0
      rw [h, Submodule.mem_bot] at h2
      exact sub_eq_zero.mp (congrArg (fun p => p.2.2) h2)
    refine ⟨?_, hS, hV, hW⟩
    rw [Submodule.eq_bot_iff]
    rintro b ⟨⟨⟨u, hu⟩, ⟨y, hy⟩⟩, ⟨z, hz⟩⟩
    have hmem : (u, y, z) ∈ LinearMap.ker (pairDiffCLM S dV dW).toLinearMap := by
      rw [LinearMap.mem_ker]
      change pairDiffCLM S dV dW (u, y, z) = 0
      rw [pairDiffCLM_apply]
      refine Prod.ext ?_ ?_
      · show S u - dV y = 0
        exact sub_eq_zero.mpr (hu.trans hy.symm)
      · show S u - dW z = 0
        exact sub_eq_zero.mpr (hu.trans hz.symm)
    rw [h, Submodule.mem_bot] at hmem
    have hu0 : u = 0 := congrArg Prod.fst hmem
    exact hu.symm.trans (by rw [hu0, map_zero])
  · rintro ⟨hgen, hS, hV, hW⟩
    rw [Submodule.eq_bot_iff]
    rintro ⟨u, y, z⟩ hp
    rw [LinearMap.mem_ker] at hp
    change pairDiffCLM S dV dW (u, y, z) = 0 at hp
    rw [pairDiffCLM_apply, Prod.mk_eq_zero] at hp
    have h1 : S u = dV y := sub_eq_zero.mp hp.1
    have h2 : S u = dW z := sub_eq_zero.mp hp.2
    have hmem : S u ∈ S.range ⊓ dV.range ⊓ dW.range :=
      ⟨⟨⟨u, rfl⟩, ⟨y, h1.symm⟩⟩, ⟨z, h2.symm⟩⟩
    rw [hgen, Submodule.mem_bot] at hmem
    have hu : u = 0 := hS (by rw [hmem, map_zero])
    have hy : y = 0 := hV (by simp [← h1, hu])
    have hz : z = 0 := hW (by simp [← h2, hu])
    rw [hu, hy, hz]
    simp

/-- **Surjectivity of the degenerate pair-difference map**, over `ℝ⁴`: the domain and the target both
have dimension `8`, so the vanishing of the kernel is exactly what is needed. -/
theorem surjective_pairDiffCLM (hE : Module.finrank ℝ E = 4)
    (S : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) (dV dW : EuclideanSpace ℝ (Fin 3) →L[ℝ] E)
    (hS : Function.Injective S) (hV : Function.Injective dV) (hW : Function.Injective dW)
    (hgen : S.range ⊓ dV.range ⊓ dW.range = ⊥) :
    Function.Surjective (pairDiffCLM S dV dW) := by
  have hker := (pairDiffCLM_ker_eq_bot_iff S dV dW).mpr ⟨hgen, hS, hV, hW⟩
  have hinj : Function.Injective (pairDiffCLM S dV dW).toLinearMap := LinearMap.ker_eq_bot.mp hker
  have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) ×
      EuclideanSpace ℝ (Fin 3)) = 8 := by
    simp [Module.finrank_prod]
  have hcod : Module.finrank ℝ (E × E) = 8 := by
    simp [Module.finrank_prod, hE]
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) ×
      EuclideanSpace ℝ (Fin 3)) = Module.finrank ℝ (E × E) := by rw [hdom, hcod]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj

end

end Work.Drive
