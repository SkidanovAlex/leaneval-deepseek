import Mathlib
import Submission.Work.Rigidity.AnnPlusWeightFourPDefs

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Rigidity

/-!
## Auxiliary slash computations at weight four

The proof of `Work.Rigidity.G2_vadd` is the weight-four instance of the group-theoretic
computation of CKMRV's proof (`univopt.tex`, Section 3.3): from `(T - I)² f = 0` one gets
`f ∣[4] T⁻¹ = 2 f - f ∣[4] T`, and from `f ∣[4] S = -f` together with the group relation
`T S T = -(S T⁻¹ S)` one gets

  `(f ∣[4] (T*S)) ∣[4] T = f ∣[4] (T*S) + 2 f`,

which is the `T`-action relation for `g₂` (since `∣[4] T` is translation by `1`).
-/

/-- `-1 ∈ SL(2,ℤ)` acts trivially on functions of even weight: `F ∣[k] (-1) = F`. -/
private lemma slash_neg_one_even {k : ℤ} (hk : Even k) (F : ℍ → ℂ) :
    F ∣[k] (-1 : SL(2, ℤ)) = F := by
  funext τ
  rw [ModularForm.SL_slash_apply]
  have h1 : ((-1 : SL(2, ℤ)) • τ : ℍ) = τ := by
    apply UpperHalfPlane.ext
    simp
  have h2 : UpperHalfPlane.denom (Work.Kernels.glOf (-1 : SL(2, ℤ))) (τ : ℂ) = -1 := by
    rw [show UpperHalfPlane.denom (Work.Kernels.glOf (-1 : SL(2, ℤ))) (τ : ℂ)
        = (Work.Kernels.glOf (-1 : SL(2, ℤ))) 1 0 * (τ : ℂ)
          + (Work.Kernels.glOf (-1 : SL(2, ℤ))) 1 1 from rfl]
    rw [Work.Kernels.glOf_apply, Work.Kernels.glOf_apply]
    simp
  rw [h1, h2]
  have h3 : ((-1 : ℂ)) ^ (-k) = 1 := by simpa using hk.neg_zpow (1 : ℂ)
  rw [h3, mul_one]

/-- `F ∣[k] (-γ) = F ∣[k] γ` for even weight `k`. -/
private lemma slash_neg_even {k : ℤ} (hk : Even k) (F : ℍ → ℂ) (γ : SL(2, ℤ)) :
    F ∣[k] (-γ) = F ∣[k] γ := by
  rw [show (-γ : SL(2, ℤ)) = (-1 : SL(2, ℤ)) * γ from by rw [neg_one_mul],
    SlashAction.slash_mul, slash_neg_one_even hk]

/-- The `(T - I)²` relation in slash form at weight four: `f ∣[4] T⁻¹ = 2 f - f ∣[4] T`. -/
private lemma slash_T_inv_four {f : ℍ → ℂ} (hT2 : Work.Kernels.T2op f = 0) :
    f ∣[(4 : ℤ)] ModularGroup.T⁻¹ = (2 : ℂ) • f - f ∣[(4 : ℤ)] ModularGroup.T := by
  have hT : f ∣[(4 : ℤ)] ModularGroup.T = fun τ : ℍ => f ((1 : ℝ) +ᵥ τ) := by
    funext τ; rw [Work.Kernels.slash_T_apply]
  have hTT : f ∣[(4 : ℤ)] (ModularGroup.T * ModularGroup.T) =
      fun τ : ℍ => f ((2 : ℝ) +ᵥ τ) := by
    rw [SlashAction.slash_mul, hT]
    funext τ
    rw [Work.Kernels.slash_T_apply]
    congr 1
    rw [Work.Kernels.vadd_one_add_one]
  have hzero : f ∣[(4 : ℤ)] (ModularGroup.T * ModularGroup.T)
      - (2 : ℂ) • (f ∣[(4 : ℤ)] ModularGroup.T) + f = 0 := by
    rw [hTT, hT]
    funext τ
    have h := congrFun hT2 τ
    simpa [Work.Kernels.T2op, Work.Kernels.vadd_one_add_one, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] using h
  have h1 : (f ∣[(4 : ℤ)] (ModularGroup.T * ModularGroup.T)
      - (2 : ℂ) • (f ∣[(4 : ℤ)] ModularGroup.T) + f) ∣[(4 : ℤ)] ModularGroup.T⁻¹ = 0 := by
    rw [hzero]; simp
  have h2 : ((f ∣[(4 : ℤ)] (ModularGroup.T * ModularGroup.T)) ∣[(4 : ℤ)] ModularGroup.T⁻¹
      - (2 : ℂ) • ((f ∣[(4 : ℤ)] ModularGroup.T) ∣[(4 : ℤ)] ModularGroup.T⁻¹)
      + f ∣[(4 : ℤ)] ModularGroup.T⁻¹) = 0 := by
    simpa only [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, SL_smul_slash]
      using h1
  have hTTri : ModularGroup.T * ModularGroup.T * ModularGroup.T⁻¹ = ModularGroup.T := by decide
  have hT1 : ModularGroup.T * ModularGroup.T⁻¹ = 1 := by decide
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul, hTTri, hT1,
    SlashAction.slash_one] at h2
  linear_combination h2

/-- **The `T`-action of `f ∣[4] (T*S)`**: under `(T - I)² f = 0` and `f ∣[4] S = -f` one has
`(f ∣[4] (T*S)) ∣[4] T = f ∣[4] (T*S) + 2 f`.  This is the group relation
`T S T = -(S T⁻¹ S)` together with `slash_T_inv_four`. -/
private lemma slash_TS_T_four {f : ℍ → ℂ} (hT2 : Work.Kernels.T2op f = 0)
    (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) :
    (f ∣[(4 : ℤ)] (ModularGroup.T * ModularGroup.S)) ∣[(4 : ℤ)] ModularGroup.T
      = f ∣[(4 : ℤ)] (ModularGroup.T * ModularGroup.S) + (2 : ℂ) • f := by
  have hgrp : ModularGroup.T * ModularGroup.S * ModularGroup.T
      = -(ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.S) := by decide
  have hTinv : f ∣[(4 : ℤ)] ModularGroup.T⁻¹ = (2 : ℂ) • f - f ∣[(4 : ℤ)] ModularGroup.T :=
    slash_T_inv_four hT2
  have key : (f ∣[(4 : ℤ)] (ModularGroup.T * ModularGroup.S)) ∣[(4 : ℤ)] ModularGroup.T
      = - ((f ∣[(4 : ℤ)] ModularGroup.T⁻¹) ∣[(4 : ℤ)] ModularGroup.S) := by
    rw [← SlashAction.slash_mul, hgrp, slash_neg_even (by norm_num), SlashAction.slash_mul,
      SlashAction.slash_mul, hS, SlashAction.neg_slash, SlashAction.neg_slash]
  rw [key, hTinv, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    SL_smul_slash, SlashAction.slash_mul, hS]
  ext τ
  simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The `T`-action relation for `g_2`.**  Let `f : ℍ → ℂ` satisfy `f ∣[4] S = -f` (written
`SlashAction.map (4 : ℤ) ModularGroup.S f = -f`, to avoid notation) and `(T - I)² f = 0` (in
the pointwise form `Work.Kernels.T2op f = 0`).  Then with `g_0 = f ∣[4] T - f`, `g_1 = f` and
`g_2 = f ∣[4] (T S) + f` (the definitions `G0`, `G1`, `G2` of
`Submission.Work.Rigidity.AnnPlusWeightFourPDefs`) one has the pointwise relation
`g_2 (τ + 1) = g_0 τ + 2 g_1 τ + g_2 τ`.

Sketch (everything is at weight `4`, `T • σ = 1 +ᵥ σ`, `S • σ = -1/σ`, and
`(F ∣[4] S) σ = (σ : ℂ)⁻⁴ F (S • σ)`; write `z = (σ : ℂ)`, so `((1 +ᵥ σ) : ℍ) : ℂ = z + 1`).
Put `h = f ∣[4] T`, so `h σ = f (σ + 1)` and `f ∣[4] (T*S) = h ∣[4] S`.  Then
`(f ∣[4] TST) τ = ((h ∣[4] S) ∣[4] T) τ = (h ∣[4] S) (τ+1) = (z+1)⁻⁴ f ((TS) • (τ+1))`.
Now `(TS) • (τ+1) = 1 - 1/(z+1) = S • ((S • τ) - 1)`, and the eigenrelation
`f (S • w) = -(w : ℂ)⁴ f w` at `w = (S • τ) - 1` gives
`f ((TS) • (τ+1)) = -(((1+τ)/τ))⁴ f ((S • τ) - 1)`, whence `(f ∣[4] TST) τ = -z⁻⁴ f ((S•τ)-1)`.
The second difference relation `f (w+2) - 2 f (w+1) + f w = 0` at `w = (S • τ) - 1` reads
`f ((S•τ)+1) - 2 f (S•τ) + f ((S•τ)-1) = 0`, so
`(f ∣[4] TST) τ = -z⁻⁴ (2 f (S•τ) - f ((S•τ)+1))`.  Finally `z⁻⁴ f (S•τ) = (f ∣[4] S) τ = -f τ`
and `z⁻⁴ f ((S•τ)+1) = (f ∣[4] (T*S)) τ`, giving `(f ∣[4] TST) τ = 2 f τ + (f ∣[4] (T*S)) τ`.
Adding `f (τ+1)` to both sides and rewriting `f (τ+1) = g_0 τ + g_1 τ` turns this into the
claimed relation. -/
theorem G2_vadd {f : UpperHalfPlane → ℂ}
    (hS : SlashAction.map (4 : ℤ) ModularGroup.S f = -f)
    (hT2 : Work.Kernels.T2op f = 0) (τ : UpperHalfPlane) :
    G2 f ((1 : ℝ) +ᵥ τ) = G0 f τ + 2 * G1 f τ + G2 f τ := by
  have hkey : (f ∣[(4 : ℤ)] (ModularGroup.T * ModularGroup.S)) ∣[(4 : ℤ)] ModularGroup.T
      = f ∣[(4 : ℤ)] (ModularGroup.T * ModularGroup.S) + (2 : ℂ) • f :=
    slash_TS_T_four hT2 hS
  -- evaluate the action of `∣[4] T` as translation by `1`
  have hpt : SlashAction.map (4 : ℤ) (ModularGroup.T * ModularGroup.S) f ((1 : ℝ) +ᵥ τ)
      = SlashAction.map (4 : ℤ) (ModularGroup.T * ModularGroup.S) f τ + 2 * f τ := by
    have h := congrFun hkey τ
    rw [Work.Kernels.slash_T_apply] at h
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
  simp only [G2, G0, G1, Pi.add_apply, Pi.sub_apply]
  rw [Work.Kernels.slash_T_apply, hpt]
  ring

end Work.Rigidity

end
