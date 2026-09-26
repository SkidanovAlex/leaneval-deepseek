import Mathlib
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Residues.ResidueTheoremK
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.LayerCont.FarTail.CuspFar
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Kernels.KernelEquations
import Submission.Work.CKFinal.affine_exp_coeffs_zero
import Submission.Work.CKFinal.S2op_Aexp_expand

namespace Work.CKFinal

open Filter Topology

/-! ## Pointwise facts about `S2op` on the contour kernel -/

/-- The pointwise linearity of `S2op` in the function variable: on a difference it is the
difference of the `S2op`s. -/
private lemma S2op_sub_apply (k : ℤ) (F G : UpperHalfPlane → ℂ) (x : UpperHalfPlane) :
    Work.Asymptotics.S2op k (fun σ => F σ - G σ) x
      = Work.Asymptotics.S2op k F x - Work.Asymptotics.S2op k G x := by
  have hsub : Work.Asymptotics.S2op k (F - G)
      = Work.Asymptotics.S2op k F - Work.Asymptotics.S2op k G := by
    rw [sub_eq_add_neg, show (-G : UpperHalfPlane → ℂ) = (-1 : ℂ) • G by funext y; simp]
    rw [Work.Asymptotics.S2op, Work.Kernels.slash_add_F, Work.Kernels.slash_smul_F]
    rw [Work.Asymptotics.S2op, Work.Asymptotics.S2op]
    funext y
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul, one_mul]
    ring
  exact congr_fun hsub x

/-- The group-algebra generator `S(T-I)²` annihilates the contour kernel `K(·,it)`, in the
`S2op` notation used below. -/
private lemma S2op_Kaxis_eq_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (t : ℝ) :
    Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t) τ = 0 := by
  have h := congr_fun (Work.Residues.Kaxis_Kfun_slash_S_T2 ℓ d hd t) τ
  simpa only [Work.Asymptotics.S2op, Pi.zero_apply] using h

/-- **The limit of the cusp remainder forces `S(T-I)²` to kill the cusp coefficients.**  At any
point `τ`, if the `S(T-I)²`-defect of the cusp remainder `K^{(d)} - 𝒢` along the contour tends to `0`
as `t → ∞`, then every cusp coefficient function `Gcusp ℓ d i j` is annihilated by `S(T-I)²` at `τ`.

Route: `S2op` is linear, `S2op (Kaxis (Kfun ℓ d) · t) = 0` identically (`Kaxis_Kfun_slash_S_T2`),
and `S2op` of `Aexp G · t` is the `τ`-value of `Aexp` with `G i j` replaced by `S2op k (G i j)`, i.e.
`a + b t + e^{2πt}(c + d t)` with `a = S2op k (G 0 0) τ`, `b = i S2op k (G 0 1) τ`,
`c = S2op k (G 1 0) τ`, `d = i S2op k (G 1 1) τ`.  The hypothesis says this combination tends to
`0`; dividing by `e^{2πt}` gives `c + dt → 0`, hence `c = d = 0`, then `a + bt → 0`, hence
`a = b = 0`. -/
theorem S2op_Gcusp_of_tendsto (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane)
    (hlim : Filter.Tendsto (fun t : ℝ => Work.Asymptotics.S2op ((d : ℤ) / 2)
        (fun σ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t) τ)
      Filter.atTop (nhds 0)) :
    ∀ i j : Fin 2,
      Work.Asymptotics.S2op ((d : ℤ) / 2) (Work.Asymptotics.Gcusp ℓ d i j) τ = 0 := by
  -- The contour kernel is killed by `S(T-I)²`, so only the `Aexp` part survives the limit.
  have hpoint : ∀ t : ℝ, Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t) τ
      = - Work.Asymptotics.S2op ((d : ℤ) / 2)
          (fun σ : UpperHalfPlane => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t) τ := by
    intro t
    rw [S2op_sub_apply ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t)
      (fun σ : UpperHalfPlane => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t) τ,
      S2op_Kaxis_eq_zero ℓ d hd τ t]
    ring
  have hlim' : Filter.Tendsto (fun t : ℝ => Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane =>
        Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t) τ)
      Filter.atTop (nhds 0) := by
    have hneg : Filter.Tendsto (fun t : ℝ => - Work.Asymptotics.S2op ((d : ℤ) / 2)
        (fun σ : UpperHalfPlane =>
          Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t) τ)
        Filter.atTop (nhds 0) :=
      Filter.Tendsto.congr' (Filter.Eventually.of_forall fun t => hpoint t) hlim
    simpa using hneg.neg
  -- `S2op` of `Aexp G · t` is the affine-exponential combination of the four `S2op`s.
  have hexpand : Filter.Tendsto (fun t : ℝ =>
      Work.Asymptotics.S2op ((d : ℤ) / 2) (Work.Asymptotics.Gcusp ℓ d 0 0) τ
        + ((t : ℂ) * Complex.I) * Work.Asymptotics.S2op ((d : ℤ) / 2)
            (Work.Asymptotics.Gcusp ℓ d 0 1) τ
        + Complex.exp (2 * Real.pi * t) *
            (Work.Asymptotics.S2op ((d : ℤ) / 2) (Work.Asymptotics.Gcusp ℓ d 1 0) τ
              + ((t : ℂ) * Complex.I) * Work.Asymptotics.S2op ((d : ℤ) / 2)
                  (Work.Asymptotics.Gcusp ℓ d 1 1) τ))
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.congr' (Filter.Eventually.of_forall fun t =>
      S2op_Aexp_expand ((d : ℤ) / 2) (Work.Asymptotics.Gcusp ℓ d) τ t) hlim'
  -- The four coefficients of that affine-exponential combination all vanish.
  obtain ⟨h00, h01, h10, h11⟩ := affine_exp_coeffs_zero hexpand
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

end Work.CKFinal
