import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.R_Rstar_expansion2
import Submission.Work.Diff.STE.B3.R_L_eq_zeta_sq
import Submission.Work.Diff.STE.B3.BNorm_J_sub_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-!
# The cross-chart transfer of the *periodised* component: `L_{lm} x_l = (ζ_l ∘ pt_m)² x_m`

The cross-chart expansion (`Work.Diff.STE.D.R_Rstar_expansion_pointwise`, and its
`[T2Space M]`-free form `Work.Diff.STE.B3.R_Rstar_expansion_pointwise_noT2`) writes the `m`-chart
component of the reconstruction `R*_l u` of a coefficient family `u` as

`R_m (R*_l u) a b z = ∑ c, ∑ d, coeffFun D l m a b c d z · u c d (tMapFun D l m z)`.

The present file instantiates this with the **periodised** component `u = Rper_l f` instead of the
localised component `u = R_l f`.  Since the localised component `R_l f c d` is supported in the open
centred cube (`B3Data.psi_supp`), the periodisation agrees with it at every point of the support of
the cut-off `χ l` (`Rper_eq_R_of_chi_ne`), and the prefactor of `coeffFun` — which contains
`ζ_l ∘ pt_m` and `χ_l ∘ coord_l ∘ pt_m` — vanishes whenever `χ_l` does.  Hence

`∑ c, ∑ d, coeffFun D l m a b c d z · Rper_l f c d (tMapFun D l m z)
    = (R_m (R*_l (R_l f)) a b z : ℂ)`,

and the pointwise reconstruction identity `R_l (R*_l f) = ζ_l² · f` in the form of
`Work.Diff.STE.B3.R_L_eq_zeta_sq` (`R_m (R*_l (R_l f)) = (ζ_l ∘ pt_m)² · R_m f`, valid for an
arbitrary pair of charts `l, m`) identifies the right-hand side with `(ζ_l ∘ pt_m)² · R_m f a b z`,
which is the statement of `coeffFun_transfer_Rper`.

No smoothness, no `[T2Space M]` and no `[I.Boundaryless]` is needed: the identity is purely
pointwise. -/

/-- **The periodisation agrees with the localised component on the support of the cut-off.**

`B3Data.Rper_eq_R` states this for points of the open centred cube and carries a spurious
`[I.Boundaryless]`; here the hypothesis is the natural one for the cross-chart transfer,
`χ l y ≠ 0`, which by `B3Data.hχsupp` forces `y` into the open cube. -/
lemma Rper_eq_R_of_chi_ne
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (f : Work.Diff.STE.Bil (I := I) (M := M)) (l : ι₀)
    (c d : Fin (Module.finrank ℝ E)) (y : Fin (Module.finrank ℝ E) → ℝ)
    (hy : D.χ l y ≠ 0) :
    D.Rper l f c d y = ((D.R l f c d y : ℝ) : ℂ) := by
  have hmem : y ∈ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    D.hχsupp l (Function.mem_support.mpr hy)
  exact Rper_eq_of_mem_cube (I := I) (M := M) D f l c d
    (fun k => (Set.mem_pi.mp hmem) k (Set.mem_univ k))

theorem coeffFun_transfer_Rper
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (f : Work.Diff.STE.Bil (I := I) (M := M)) (l m : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        ∑ c, ∑ d,
          Work.Diff.STE.D.coeffFun (I := I) (M := M) D l m a b c d z *
            D.Rper l f c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D l m z))
      = fun z : Fin (Module.finrank ℝ E) → ℝ =>
          (((D.ζ l (D.pt m z)) ^ 2 * D.R m f a b z : ℝ) : ℂ) := by
  funext z
  -- Step 1: the periodised sum is the complex lift of the sum against the localised component.
  have hstep : (∑ c, ∑ d,
        Work.Diff.STE.D.coeffFun (I := I) (M := M) D l m a b c d z *
          D.Rper l f c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D l m z))
      = ((∑ c, ∑ d, Work.Diff.STE.D.coeffFun (I := I) (M := M) D l m a b c d z
          * (fun c d y => D.R l f c d y) c d
              (Work.Diff.STE.D.tMapFun (I := I) (M := M) D l m z) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hχ : D.χ l (Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt m z)) = 0
    · -- the cut-off `χ l` vanishes at the transition point: the coefficient does too
      have hc : Work.Diff.STE.D.coeffFun (I := I) (M := M) D l m a b c d z = 0 := by
        simp only [Work.Diff.STE.D.coeffFun, hχ, mul_zero, zero_mul]
      simp only [hc, Complex.ofReal_zero, zero_mul]
    · -- the cut-off does not vanish: the periodisation is the component itself
      rw [Rper_eq_R_of_chi_ne (I := I) (M := M) D f l c d
        (Work.Diff.STE.D.tMapFun (I := I) (M := M) D l m z) hχ, Complex.ofReal_mul]
  -- Step 2: the cross-chart expansion turns the sum into the `m`-component of `R*_l (R_l f)`.
  calc (∑ c, ∑ d,
        Work.Diff.STE.D.coeffFun (I := I) (M := M) D l m a b c d z *
          D.Rper l f c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D l m z))
      = ((∑ c, ∑ d, Work.Diff.STE.D.coeffFun (I := I) (M := M) D l m a b c d z
          * (fun c d y => D.R l f c d y) c d
              (Work.Diff.STE.D.tMapFun (I := I) (M := M) D l m z) : ℝ) : ℂ) := hstep
    _ = ((D.R m (D.Rstar l (fun c d y => D.R l f c d y)) a b z : ℝ) : ℂ) := by
          rw [R_Rstar_expansion_pointwise_noT2 (I := I) (M := M) D l m a b
            (fun c d y => D.R l f c d y) z]
    _ = ((D.ζ l (D.pt m z) ^ 2 * D.R m f a b z : ℝ) : ℂ) := by
          rw [R_L_eq_zeta_sq (I := I) (M := M) D l m f a b z]

end Work.Diff.STE.B3
