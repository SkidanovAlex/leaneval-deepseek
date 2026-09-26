import Mathlib
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.LayerCont.LayerT2
import Submission.Work.Residues.ResidueTheoremK
import Submission.Work.CKFinal.S2op_integral_eq_zero
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Kernels.KernelFacts.KPlus_T2

namespace Work.CKFinal

open MeasureTheory UpperHalfPlane ModularGroup

/-- `S2op` is `ℂ`-homogeneous in the function variable: it is the group-algebra slash by
`S(T-I)²`, and `slash` commutes with scalar multiplication of the function
(`Work.Kernels.slash_smul_F`). -/
lemma S2op_smul (k : ℤ) (c : ℂ) (F : UpperHalfPlane → ℂ) :
    Work.Asymptotics.S2op k (c • F) = c • Work.Asymptotics.S2op k F := by
  simp only [Work.Asymptotics.S2op]
  rw [Work.Kernels.slash_smul_F]

/-- The pointwise annihilation of the contour kernel on the low piece: for every real `t`, the
integrand `σ ↦ K(σ,it)·e^{-πr²t}` of `layerLow` has vanishing `S(T-I)²`-defect.  This is
`Work.Residues.Kaxis_Kfun_slash_S_T2` together with `S2op_smul` (the Gaussian factor does not
depend on `σ`). -/
lemma S2op_Kaxis_gauss_pointwise (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) (τ : UpperHalfPlane) (t : ℝ) :
    Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        * Work.Asymptotics.gaussWeight r t) τ = 0 := by
  have h := Work.Residues.Kaxis_Kfun_slash_S_T2 ℓ d hd t
  have hF : Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t) = 0 := by
    simpa only [Work.Asymptotics.S2op] using h
  rw [show (fun σ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        * Work.Asymptotics.gaussWeight r t)
      = Work.Asymptotics.gaussWeight r t
        • (fun σ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t) from by
    funext σ; simp [smul_eq_mul, mul_comm]]
  rw [S2op_smul, hF, smul_zero]
  simp

/-- **`S(T-I)²` annihilates the low piece `layerLow` of the CKMRV layer** (the contour integral
over `(0,1]`), for every real `r`, whenever the three `S`-shifted contours `S•τ, S•(τ+1), S•(τ+2)`
are clean on `(0,1]`.

Route: `layerLow = sinSq r · ∫_{(0,1]} Kaxis (Kfun ℓ d) σ t · gaussWeight r t dt`; the three
integrands are integrable (`Work.LayerCont.Kaxis_gauss_integrableOn`, `p = 1`) and
`S2op` of the integrand vanishes pointwise in `t` (`Work.Residues.Kaxis_Kfun_slash_S_T2`), so
linearity of `S2op` under the Bochner integral (`Work.CKFinal.S2op_integral_eq_zero`) closes. -/
theorem S2op_layerLow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (r : ℝ)
    {τ : UpperHalfPlane}
    (hclean : ∀ (σ : UpperHalfPlane),
      σ ∈ ({ModularGroup.S • τ, ModularGroup.S • ((1 : ℝ) +ᵥ τ),
        ModularGroup.S • ((2 : ℝ) +ᵥ τ)} : Set UpperHalfPlane) →
      ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) 1 →
        Work.Kernels.jInvariantFun σ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane => Work.Asymptotics.layerLow ℓ d σ r) τ = 0 := by
  -- Integrability of the three shifted integrands on `(0,1]`, from cleanliness.
  have hInt : ∀ σ ∈ ({ModularGroup.S • τ, ModularGroup.S • ((1 : ℝ) +ᵥ τ),
      ModularGroup.S • ((2 : ℝ) +ᵥ τ)} : Set UpperHalfPlane),
      IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        * Work.Asymptotics.gaussWeight r t) (Set.Ioc (0 : ℝ) 1) :=
    fun σ hσ => Work.LayerCont.Kaxis_gauss_integrableOn ℓ d hd (p := 1) one_pos
      (fun t ht htI => hclean σ hσ t ht htI) r
  -- Linearity of `S2op` under the Bochner integral over `(0,1]`.
  have hS : Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane => ∫ t in Set.Ioc (0 : ℝ) 1,
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
          * Work.Asymptotics.gaussWeight r t) τ = 0 := by
    refine S2op_integral_eq_zero (s := Set.Ioc (0 : ℝ) 1)
      (f := fun (σ : UpperHalfPlane) (t : ℝ) => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        * Work.Asymptotics.gaussWeight r t) ?_ ?_ ?_ ?_
    · exact hInt (ModularGroup.S • τ) (by simp)
    · exact hInt (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) (by simp)
    · exact hInt (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) (by simp)
    · intro t
      exact S2op_Kaxis_gauss_pointwise ℓ d hd r τ t
  -- `layerLow` as the set integral over `(0,1]`.
  have hll : (fun σ : UpperHalfPlane => Work.Asymptotics.layerLow ℓ d σ r)
      = fun σ : UpperHalfPlane => Work.Asymptotics.sinSq r * ∫ t in Set.Ioc (0 : ℝ) 1,
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
            * Work.Asymptotics.gaussWeight r t := by
    funext σ
    rw [Work.Asymptotics.layerLow, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [Work.Asymptotics.gaussWeight]
  rw [hll]
  -- The `τ`-independent factor `sinSq r` pulls out of `S2op`.
  have hsplit : Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane => Work.Asymptotics.sinSq r * ∫ t in Set.Ioc (0 : ℝ) 1,
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
          * Work.Asymptotics.gaussWeight r t) τ
      = Work.Asymptotics.sinSq r * Work.Asymptotics.S2op ((d : ℤ) / 2)
        (fun σ : UpperHalfPlane => ∫ t in Set.Ioc (0 : ℝ) 1,
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
            * Work.Asymptotics.gaussWeight r t) τ := by
    rw [show (fun σ : UpperHalfPlane => Work.Asymptotics.sinSq r
        * ∫ t in Set.Ioc (0 : ℝ) 1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
          * Work.Asymptotics.gaussWeight r t)
        = Work.Asymptotics.sinSq r • (fun σ : UpperHalfPlane => ∫ t in Set.Ioc (0 : ℝ) 1,
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
            * Work.Asymptotics.gaussWeight r t) from by
      funext σ; simp]
    rw [S2op_smul]
    simp
  rw [hsplit, hS, mul_zero]

end Work.CKFinal
