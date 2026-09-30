import Mathlib
import Submission.Work.BW.sieg2KernelDefs
import Submission.Work.BW.sieg2_kerLatE_aux
import Submission.Work.BW.TV.mem_intLatE_iff_latL

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The integral kernel family of a `ℤ`-basis of the kernel lattice

`Work.BW.sieg2_kerLatE_family` turns a `ℤ`-basis `b` of the kernel lattice
`kerLatK a = (𝓞 F)^N ∩ ker (PhiE a)` into a family `v` of *integral kernel tuples*
`v i : (𝓞 F)^N` (rows killed by `a`) whose mixed coordinates `siegCoord (v i)` are literally the
vectors `kerLatEval a (b i)`:

* the existence of `v` is the surjectivity of the mixed-coordinate map
  `siegCoordE : (Fin N → 𝓞 F) → EuclideanSpace ℝ (Fin N × index F)` onto the integral lattice
  `intLatE F N` (`siegCoordE_surjective_intLatE`), applied to `kerLatEval a (b i) ∈ intLatE F N`;
* the kernel condition is transported from `PhiE a (kerLatEval a (b i)) = 0` through the
  coordinate bridges `psiAssemble_PhiE`, `psiAssemble_siegCoord` and `Phi_meK_sum`;
* `ℤ`-independence is transported from the basis `b` along the `ℤ`-linear map `TV.toEMap`
  (`linearIndependent_kerLatEval` and `LinearIndependent.of_comp`);
* the Gram determinant is unchanged because the mixed coordinate vectors are equal to the
  `kerLatEval a (b i)` themselves and `inner ℝ` agrees with `siegInner` on them
  (`inner_siegCoordE`).

All the bridges are proved in `Submission.Work.BW.sieg2_kerLatE_aux`.
-/

namespace Work.BW

theorem sieg2_kerLatE_family {F : Type*} [Field F] [NumberField F] {M N : ℕ} (hMN : M < N)
    (a : Fin M → Fin N → F) (hli : LinearIndependent F a)
    (b : Module.Basis (Fin (Module.finrank ℚ F * (N - M))) ℤ ↥(kerLatK (F := F) a)) :
    ∃ v : Fin (Module.finrank ℚ F * (N - M)) → (Fin N → NumberField.RingOfIntegers F),
      (∀ i n, ∑ m, a n m * (((v i m : NumberField.RingOfIntegers F)) : F) = 0) ∧
      LinearIndependent ℤ (fun i => Work.BW.siegCoord (v i)) ∧
      Work.BW.siegGramDet v =
        Real.sqrt (Matrix.det (Matrix.of (fun i j : Fin (Module.finrank ℚ F * (N - M)) =>
          inner ℝ (kerLatEval (F := F) a (b i)) (kerLatEval (F := F) a (b j))))) := by
  classical
  -- Every `b i` lies in the kernel lattice, hence its ambient vector lies in `intLatE F N` and is
  -- killed by `PhiE a`.
  have hmem : ∀ i, kerLatEval (F := F) a (b i) ∈ intLatE F N := by
    intro i
    have h1 : kerLatEval (F := F) a (b i) ∈ kerLatE (F := F) a := by
      simpa [kerLatEval] using (Submodule.mem_comap).mp (b i).2
    have h2 : kerLatEval (F := F) a (b i) ∈
        intLatE F N ⊓ ((PhiE a).ker).restrictScalars ℤ := h1
    exact h2.1
  have hker : ∀ i, PhiE a (kerLatEval (F := F) a (b i)) = 0 := by
    intro i
    have h1 : kerLatEval (F := F) a (b i) ∈ kerLatE (F := F) a := by
      simpa [kerLatEval] using (Submodule.mem_comap).mp (b i).2
    have h2 : kerLatEval (F := F) a (b i) ∈
        intLatE F N ⊓ ((PhiE a).ker).restrictScalars ℤ := h1
    exact LinearMap.mem_ker.mp h2.2
  -- Extract the integral tuples representing the basis vectors.
  choose v hv using fun i =>
    siegCoordE_surjective_intLatE (F := F) N (kerLatEval (F := F) a (b i)) (hmem i)
  refine ⟨v, ?_, ?_, ?_⟩
  · -- The rows of `a` kill each `v i`.
    intro i n
    have h1 : PhiE a (siegCoordE (v i)) = 0 := by rw [hv i]; exact hker i
    have h2 : Phi a (fun j => meK (((v i j : NumberField.RingOfIntegers F)) : F)) = 0 := by
      have h3 := psiAssemble_PhiE (F := F) a (siegCoordE (v i))
      rw [h1, psiAssemble_siegCoord] at h3
      simpa using h3.symm
    have h4 := congrFun h2 n
    rw [Phi_meK_sum a (v i)] at h4
    exact meK_eq_zero.mp h4
  · -- `ℤ`-independence is transported from the basis `b`.
    refine LinearIndependent.of_comp (TV.toEMap F N) ?_
    have hcomp : (TV.toEMap F N) ∘ (fun i => siegCoord (v i)) =
        fun i => kerLatEval (F := F) a (b i) := by
      funext i
      rw [Function.comp_apply, TV_toEMap_siegCoord, hv i]
    rw [hcomp]
    exact linearIndependent_kerLatEval (F := F) a b
  · -- The Gram determinant is the Gram determinant of the `kerLatEval a (b i)`.
    simp only [siegGramDet]
    congr 1
    congr 1
    ext i j
    simp only [Matrix.of_apply]
    rw [← hv i, ← hv j]
    exact (inner_siegCoordE (v i) (v j)).symm

end Work.BW
