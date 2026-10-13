import Mathlib
import Submission.Work.DSF1.Sheaf.AcyclicToolkit

namespace Work.DSF1.Sheaf

open CategoryTheory CategoryTheory.Limits

universe u v w x

/-- If the homology of `F(K)` at `n+1` vanishes, then `F` of the projection `syzProj K n` is an
epimorphism: the vanishing of the homology of `F(K)` at `n+1` says precisely that the image of
`F.map (K.d n (n+1))` equals the kernel of `F.map (K.d (n+1) (n+2))`, i.e. that the corestriction
`F(K.X n) → ker (F.map (K.d (n+1) (n+2)))` is an epimorphism; since `F` preserves kernels, this
map is `F` applied to `syzProj K n` up to the canonical comparison isomorphism of kernels. -/
theorem epi_map_syzProj {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
    {D : Type w} [CategoryTheory.Category.{x} D] [CategoryTheory.Abelian D]
    (K : CochainComplex C ℕ) [∀ i : ℕ, HomologicalComplex.HasHomology K i]
    (F : CategoryTheory.Functor C D) [F.Additive] [CategoryTheory.Limits.PreservesFiniteLimits F]
    (n : ℕ)
    (h : CategoryTheory.Limits.IsZero
      (HomologicalComplex.homology ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) (n+1))) :
    CategoryTheory.Epi (F.map (Work.DSF1.Sheaf.syzProj K n)) := by
  -- The hypothesis says that the complex `F(K)` is exact at `n+1`.
  have hEx : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).ExactAt (n+1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) (n+1)).2 h
  -- hence its short complex `F(K).X n ⟶ F(K).X (n+1) ⟶ F(K).X (n+2)` is exact.
  have hS : (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc' n (n+1) (n+2)).Exact :=
    (HomologicalComplex.exactAt_iff'
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) n (n+1) (n+2)
      (ComplexShape.prev_eq' _ (ComplexShape.up_mk n (n+1) rfl))
      (ComplexShape.next_eq' _ (ComplexShape.up_mk (n+1) (n+2) rfl))).1 hEx
  -- so the corestriction of `F.map (K.d n (n+1))` to the kernel of `F.map (K.d (n+1) (n+2))`
  -- is an epimorphism.
  have hlift : Epi (Limits.kernel.lift (F.map (K.d (n+1) (n+2))) (F.map (K.d n (n+1)))
      (by rw [← F.map_comp, HomologicalComplex.d_comp_d, F.map_zero])) :=
    ShortComplex.Exact.epi_kernelLift hS
  -- `F` preserves kernels, so this map is `F (syzProj K n)` composed with the kernel comparison
  -- isomorphism.
  let g : F.obj (syz K (n+1)) ⟶ Limits.kernel (F.map (K.d (n+1) (n+2))) :=
    kernelComparison (K.d (n+1) (n+2)) F
  have hg : IsIso g := by
    change IsIso (kernelComparison (K.d (n+1) (n+2)) F)
    infer_instance
  have key : F.map (syzProj K n) ≫ g =
      Limits.kernel.lift (F.map (K.d (n+1) (n+2))) (F.map (K.d n (n+1)))
        (by rw [← F.map_comp, HomologicalComplex.d_comp_d, F.map_zero]) :=
    map_lift_kernelComparison (K.d (n+1) (n+2)) F
      (HomologicalComplex.d_comp_d K n (n+1) (n+2))
  have h2 : Epi (F.map (syzProj K n) ≫ g) := key ▸ hlift
  exact (epi_comp_iff_of_isIso (F.map (syzProj K n)) g).mp h2

end Work.DSF1.Sheaf
