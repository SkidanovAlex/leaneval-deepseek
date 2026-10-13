import Mathlib
import Submission.Work.DSG4a.FreePres
import Submission.Work.DSG4a.one_mem_splitIdeal_map_present
import Submission.Work.DSG4a.isUnimodular_tmul_presentMk_iff
import Submission.Work.DSG4a.Split

namespace Work.DSG4a

open TensorProduct

universe u

/-- **Unimodularity descends along a flat base change** for a finitely presented module.

If `M` is finitely presented (witnessed by the explicit free presentation `P`) and the base
change `1 ⊗ e` of `e : M` to a flat `A`-algebra `A'` is unimodular over `A'`, then the unit of
`A'` lies in the image of the splitting ideal of `e` under `algebraMap A A'`.

The proof reads the given unimodularity in the presentation `present P.D ≅ M`: an `A'`-valued
linear functional on `M` pulling `e` back to `1` becomes a functional on `A^m ⧸ im D'`
(equivalently, a solution vector `w` of the transposed system with `⟪w, e⟫ = 1`), and then
`one_mem_splitIdeal_map_present` applies, using flatness of `A'` to express `w` as a
combination of solutions over `A`. -/
theorem one_mem_map_splitIdeal_of_isUnimodular_tmul {A : Type u} [CommRing A] {A' : Type u}
    [CommRing A'] [Algebra A A'] {M : Type u} [AddCommGroup M] [Module A M]
    (P : Work.DSG4a.FreePres A M) (e : M) (hflat : Module.Flat A A')
    (h : Module.IsUnimodular A' (TensorProduct.mk A A' M (1 : A') e)) :
    (1 : A') ∈ (Work.DSG4a.splitIdeal A e).map (algebraMap A A') := by
  -- The chosen presentation identifies `e` with the class of the lifted vector.
  have he := FreePres.φ_presentMk_lift P e
  -- Unimodularity of `1 ⊗ e` over `A'` gives an `A`-linear functional `τ : M →ₗ[A] A'`
  -- with `τ e = 1`.
  have h' : Module.IsUnimodular A' ((1 : A') ⊗ₜ[A] e) := by
    simpa [TensorProduct.mk_apply] using h
  obtain ⟨τ, hτ⟩ := (isUnimodular_tmul_iff (A := A) (A' := A') e).mp h'
  -- Composing with the presentation gives a functional on `present P.D` with value `1` on
  -- the class of the lift of `e`.
  have hτ' : (τ ∘ₗ P.φ.toLinearMap) (Work.DSG4a.presentMk P.D (FreePres.lift P e)) = 1 := by
    rw [LinearMap.comp_apply]
    exact (congrArg τ he).trans hτ
  -- Hence the base change of that class is unimodular over `A'`.
  have huni : Module.IsUnimodular A' (Work.DSG4a.presentMk (fun i j => algebraMap A A' (P.D i j))
      (fun i => algebraMap A A' (FreePres.lift P e i))) := by
    refine (isUnimodular_tmul_presentMk_iff P.D (FreePres.lift P e)).mp ?_
    rw [TensorProduct.mk_apply]
    exact (isUnimodular_tmul_iff (A := A) (A' := A')
      (Work.DSG4a.presentMk P.D (FreePres.lift P e))).mpr ⟨τ ∘ₗ P.φ.toLinearMap, hτ'⟩
  -- Flat descent in coordinates.
  have hmain := one_mem_splitIdeal_map_present P.D (FreePres.lift P e) hflat huni
  -- The splitting ideal of `e` is that of the class of the lift, under the presentation.
  have hsplit : splitIdeal A e = splitIdeal A (Work.DSG4a.presentMk P.D (FreePres.lift P e)) := by
    conv_lhs => rw [← he]
    exact splitIdeal_linearEquiv P.φ _
  rwa [← hsplit] at hmain

end Work.DSG4a
