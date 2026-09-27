import Mathlib
import Submission.Work.Drive.ppPairLinAlg

/-!
# The linear algebra of the `s = 1` face of the pair map of the radial collapse

At `s = 1` the two plane blocks of the pair map are the *distinct* chains `E 1`, `E' 1`, so — unlike
at `s = 0` (`Submission/Work/Drive/ppPairLinAlg.lean`, where both blocks share the derivative
`(mfderiv D 0) ∘ ins2`) — the face-restricted derivative is the `8 → 8` map

> `Ψ (a, y, z) = (A a − C y, B a − D z)`,  `A = ∂_u (E 1)`, `B = ∂_u (E' 1)`,
> `C = ∂_{y} V`, `D = ∂_{z} W`,

with the plane parameter `a` shared by the two blocks.  This is the linear-algebra input of the open
`ftS x = 1` half of `hend` (`Work.Drive.ppRegAt_one_of_goodDiam`; see
`Submission/Work/Drive/PPREGAT_S0_PROVED.md` §2 and `NOTES_LEAD_hblock_uniformity.md` §2/§4.3).

The kernel is computed sharply below:

> `ker Ψ = 0 ↔ {a | A a ∈ range C ∧ B a ∈ range D} = 0 ∧ ker C = 0 ∧ ker D = 0`,

and since the domain and the target both have dimension `8` (over `ℝ⁴`), that is exactly the
surjectivity.  The condition on the set `{a | A a ∈ range C ∧ B a ∈ range D}` is the shape the design
supplies: `range A ⊓ range C` is a line (a `2`- and a `3`-dimensional subspace of `ℝ⁴`), so
`{a | A a ∈ range C}` is a line `ℝ a₀` when `A` is injective, and the whole content is
**`B a₀ ∉ range D`** — the transversality of the *other* pair on that line.  This is the
"block-triangular" condition of the design note.
-/

namespace Work.Drive

open scoped Manifold ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The `s = 1` face pair-difference map**: the two plane blocks have *different* derivatives. -/
def pairDiffTwoCLM (A B : EuclideanSpace ℝ (Fin 2) →L[ℝ] E)
    (C D : EuclideanSpace ℝ (Fin 3) →L[ℝ] E) :
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) →L[ℝ] E × E :=
  ((A.comp ppProjU) - (C.comp ppProjY)).prod ((B.comp ppProjU) - (D.comp ppProjZ))

@[simp] lemma pairDiffTwoCLM_apply (A B : EuclideanSpace ℝ (Fin 2) →L[ℝ] E)
    (C D : EuclideanSpace ℝ (Fin 3) →L[ℝ] E)
    (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    pairDiffTwoCLM A B C D p = (A p.1 - C p.2.1, B p.1 - D p.2.2) := rfl

/-- **The kernel of the `s = 1` face pair-difference map, sharply.** -/
theorem pairDiffTwoCLM_ker_eq_bot_iff (A B : EuclideanSpace ℝ (Fin 2) →L[ℝ] E)
    (C D : EuclideanSpace ℝ (Fin 3) →L[ℝ] E) :
    LinearMap.ker (pairDiffTwoCLM A B C D).toLinearMap = ⊥ ↔
      ((∀ a : EuclideanSpace ℝ (Fin 2), A a ∈ C.range → B a ∈ D.range → a = 0) ∧
        Function.Injective C ∧ Function.Injective D) := by
  have hkerC : ∀ y : EuclideanSpace ℝ (Fin 3), C y = 0 →
      (0, y, 0) ∈ LinearMap.ker (pairDiffTwoCLM A B C D).toLinearMap := by
    intro y hy
    rw [LinearMap.mem_ker]
    change pairDiffTwoCLM A B C D (0, y, 0) = 0
    rw [pairDiffTwoCLM_apply, hy]
    simp
  have hkerD : ∀ z : EuclideanSpace ℝ (Fin 3), D z = 0 →
      (0, 0, z) ∈ LinearMap.ker (pairDiffTwoCLM A B C D).toLinearMap := by
    intro z hz
    rw [LinearMap.mem_ker]
    change pairDiffTwoCLM A B C D (0, 0, z) = 0
    rw [pairDiffTwoCLM_apply, hz]
    simp
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro a ha hb
      obtain ⟨y, hy⟩ := ha
      obtain ⟨z, hz⟩ := hb
      have hmem : (a, y, z) ∈ LinearMap.ker (pairDiffTwoCLM A B C D).toLinearMap := by
        rw [LinearMap.mem_ker]
        change pairDiffTwoCLM A B C D (a, y, z) = 0
        rw [pairDiffTwoCLM_apply]
        refine Prod.ext ?_ ?_
        · show A a - C y = 0
          rw [sub_eq_zero]; exact hy.symm
        · show B a - D z = 0
          rw [sub_eq_zero]; exact hz.symm
      rw [h, Submodule.mem_bot] at hmem
      exact congrArg Prod.fst hmem
    · intro y y' hyy
      have h0 : C (y - y') = 0 := by rw [map_sub, hyy, sub_self]
      have h2 : (0, y - y', 0) ∈ LinearMap.ker (pairDiffTwoCLM A B C D).toLinearMap := hkerC _ h0
      rw [h, Submodule.mem_bot] at h2
      exact sub_eq_zero.mp (congrArg (fun p => p.2.1) h2)
    · intro z z' hzz
      have h0 : D (z - z') = 0 := by rw [map_sub, hzz, sub_self]
      have h2 : (0, 0, z - z') ∈ LinearMap.ker (pairDiffTwoCLM A B C D).toLinearMap := hkerD _ h0
      rw [h, Submodule.mem_bot] at h2
      exact sub_eq_zero.mp (congrArg (fun p => p.2.2) h2)
  · rintro ⟨hset, hC, hD⟩
    rw [Submodule.eq_bot_iff]
    rintro ⟨a, y, z⟩ hp
    rw [LinearMap.mem_ker] at hp
    change pairDiffTwoCLM A B C D (a, y, z) = 0 at hp
    rw [pairDiffTwoCLM_apply, Prod.mk_eq_zero] at hp
    have h1 : A a = C y := sub_eq_zero.mp hp.1
    have h2 : B a = D z := sub_eq_zero.mp hp.2
    have ha : a = 0 := hset a ⟨y, h1.symm⟩ ⟨z, h2.symm⟩
    have hy : y = 0 := hC (by simp [← h1, ha])
    have hz : z = 0 := hD (by simp [← h2, ha])
    rw [ha, hy, hz]
    simp

/-- **Surjectivity of the `s = 1` face pair-difference map**, over `ℝ⁴` (domain and target both of
dimension `8`). -/
theorem surjective_pairDiffTwoCLM (hE : Module.finrank ℝ E = 4)
    (A B : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) (C D : EuclideanSpace ℝ (Fin 3) →L[ℝ] E)
    (hset : ∀ a : EuclideanSpace ℝ (Fin 2), A a ∈ C.range → B a ∈ D.range → a = 0)
    (hC : Function.Injective C) (hD : Function.Injective D) :
    Function.Surjective (pairDiffTwoCLM A B C D) := by
  have hker := (pairDiffTwoCLM_ker_eq_bot_iff A B C D).mpr ⟨hset, hC, hD⟩
  have hinj : Function.Injective (pairDiffTwoCLM A B C D).toLinearMap :=
    LinearMap.ker_eq_bot.mp hker
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
