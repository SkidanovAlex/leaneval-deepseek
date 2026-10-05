import Mathlib

/-!
# General-domain (`X × ℝ`) version of the `sqrt_pow_contDiff` development

This is the analogue of `Submission.Work.RPB.B3.SqrtPowDefs` with the first coordinate
`ℝ` replaced by an arbitrary real normed space `X`.  `B3` handled `ψ : ℝ × ℝ → E` (one real
parameter); here `ψ : X × ℝ → E`.

`GG ψ n` is the level-`n` piecewise function
`z ↦ z.2 ^ n • ψ (z.1, √z.2)` on `z.2 ≥ 0` and `z ↦ z.2 ^ n • ψ (z.1, √(-z.2))` on `z.2 < 0`
(one and the same `ψ` on both branches, so the "matching" hypothesis of the `B3` version is
automatic).

The auxiliary objects are the building blocks of the induction on `n`:
* `pdX ψ z = (fderiv ℝ ψ z) ∘ inl` is the partial derivative in the `X`-direction, viewed as a
  continuous linear map `X →L[ℝ] E`;
* `pdU ψ z = (fderiv ℝ ψ z) (0,1)` is the partial derivative in the last variable;
* `ThetaG ψ n z = n • ψ z + ½ • (z.2 • pdU ψ z)`;
* `dG ψ n z` is the explicit value of the Fréchet derivative of `GG ψ (n+1)` at `z`.
-/

noncomputable section

namespace Work.RPB.B5.SqrtGen

open scoped ContDiff

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Level-`n` piecewise construction (both branches use the same `ψ`). -/
def GG (ψ : X × ℝ → E) (n : ℕ) : X × ℝ → E :=
  fun z => if 0 ≤ z.2 then z.2 ^ n • ψ (z.1, Real.sqrt z.2)
           else z.2 ^ n • ψ (z.1, Real.sqrt (-z.2))

/-- The partial derivative in the `X`-direction, as a continuous linear map `X →L[ℝ] E`. -/
def pdX (ψ : X × ℝ → E) : X × ℝ → (X →L[ℝ] E) :=
  fun z => (fderiv ℝ ψ z).comp (ContinuousLinearMap.inl ℝ X ℝ)

/-- The partial derivative in the last variable, as a function of the point. -/
def pdU (ψ : X × ℝ → E) : X × ℝ → E :=
  fun z => (fderiv ℝ ψ z) (0, 1)

/-- The operator `Θ_n ψ = n • ψ + ½ • (s • ∂₂ψ)`. -/
def ThetaG (ψ : X × ℝ → E) (n : ℕ) : X × ℝ → E :=
  fun z => n • ψ z + (1 / 2 : ℝ) • (z.2 • pdU ψ z)

/-- The explicit derivative of `GG ψ (n+1)`. -/
def dG (ψ : X × ℝ → E) (n : ℕ) : X × ℝ → ((X × ℝ) →L[ℝ] E) :=
  fun z => (z.2 • GG (pdX ψ) n z).comp (ContinuousLinearMap.fst ℝ X ℝ)
         + (ContinuousLinearMap.snd ℝ X ℝ).smulRight (GG (ThetaG ψ (n + 1)) n z)

/-- A continuous linear map out of `X × ℝ` expanded along the two factors. -/
lemma clm_apply_eq (A : (X × ℝ) →L[ℝ] E) (v : X × ℝ) :
    A v = (A.comp (ContinuousLinearMap.inl ℝ X ℝ)) v.1 + v.2 • A (0, 1) := by
  have hv : v = (ContinuousLinearMap.inl ℝ X ℝ) v.1 + v.2 • (0, 1) := by
    ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, ContinuousLinearMap.comp_apply]

/-- Unfolding of `pdX`. -/
lemma pdX_apply (ψ : X × ℝ → E) (z : X × ℝ) (v : X) :
    pdX ψ z v = (fderiv ℝ ψ z) (v, 0) := by
  simp only [pdX, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

/-- Unfolding of `pdU`. -/
lemma pdU_apply (ψ : X × ℝ → E) (z : X × ℝ) :
    pdU ψ z = (fderiv ℝ ψ z) (0, 1) := rfl

/-- Unfolding of `dG` on the positive half-plane. -/
lemma dG_eq_pos (ψ : X × ℝ → E) (n : ℕ) (z : X × ℝ) (hz : 0 < z.2) :
    dG ψ n z
      = ((z.2 ^ (n + 1)) • pdX ψ (z.1, Real.sqrt z.2)).comp
            (ContinuousLinearMap.fst ℝ X ℝ)
        + (ContinuousLinearMap.snd ℝ X ℝ).smulRight
            (z.2 ^ n • ((n + 1) • ψ (z.1, Real.sqrt z.2)
              + (1 / 2 : ℝ) • (Real.sqrt z.2 • pdU ψ (z.1, Real.sqrt z.2)))) := by
  simp only [dG, GG, ThetaG, hz.le, reduceIte]
  rw [pow_succ', smul_smul]

/-- Unfolding of `dG` on the negative half-plane. -/
lemma dG_eq_neg (ψ : X × ℝ → E) (n : ℕ) (z : X × ℝ) (hz : z.2 < 0) :
    dG ψ n z
      = ((z.2 ^ (n + 1)) • pdX ψ (z.1, Real.sqrt (-z.2))).comp
            (ContinuousLinearMap.fst ℝ X ℝ)
        + (ContinuousLinearMap.snd ℝ X ℝ).smulRight
            (z.2 ^ n • ((n + 1) • ψ (z.1, Real.sqrt (-z.2))
              + (1 / 2 : ℝ) • (Real.sqrt (-z.2) • pdU ψ (z.1, Real.sqrt (-z.2))))) := by
  have h : ¬ (0 ≤ z.2) := not_le.mpr hz
  simp only [dG, GG, ThetaG, h, reduceIte]
  rw [pow_succ', smul_smul]

/-- `GG` is homogeneous in the level: passing from level `n` to level `n+1` multiplies by `z.2`. -/
lemma GG_smul_succ (ψ : X × ℝ → E) (n : ℕ) :
    GG ψ (n + 1) = fun z => z.2 • GG ψ n z := by
  funext z
  by_cases h : 0 ≤ z.2 <;> simp only [GG, h, reduceIte] <;> rw [pow_succ', smul_smul]

/-- Pointwise form of `GG_smul_succ`. -/
lemma GG_smul_succ_apply (ψ : X × ℝ → E) (n : ℕ) (z : X × ℝ) :
    GG ψ (n + 1) z = z.2 • GG ψ n z := by
  rw [GG_smul_succ]

/-- `GG` is additive in the function. -/
lemma GG_add_fun (f g : X × ℝ → E) (n : ℕ) (z : X × ℝ) :
    GG (fun p => f p + g p) n z = GG f n z + GG g n z := by
  by_cases h : 0 ≤ z.2 <;> simp only [GG, h, reduceIte, smul_add]

/-- `Θ_{n+1} ψ = Θ_n ψ + ψ` as functions. -/
lemma ThetaG_succ_add (ψ : X × ℝ → E) (n : ℕ) :
    ThetaG ψ (n + 1) = fun p => ThetaG ψ n p + ψ p := by
  funext p; unfold ThetaG; rw [succ_nsmul]; abel

/-- The successor relation for the explicit derivatives: `dG (n+1) z` is obtained from `dG n z`
by the product rule for the factor `z.2`. -/
lemma dG_succ_eq (ψ : X × ℝ → E) (n : ℕ) (z : X × ℝ) :
    dG ψ (n + 1) z
      = (ContinuousLinearMap.snd ℝ X ℝ).smulRight (GG ψ (n + 1) z) + z.2 • dG ψ n z := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  simp only [dG]
  rw [GG_smul_succ ψ n, GG_smul_succ (pdX ψ) n, ThetaG_succ_add ψ (n + 1),
    GG_add_fun (ThetaG ψ (n + 1)) ψ (n + 1) z, GG_smul_succ (ThetaG ψ (n + 1)) n,
    GG_smul_succ ψ n]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, smul_add, smul_smul]
  rw [mul_comm ((ContinuousLinearMap.snd ℝ X ℝ) v) z.2]
  abel

end Work.RPB.B5.SqrtGen
