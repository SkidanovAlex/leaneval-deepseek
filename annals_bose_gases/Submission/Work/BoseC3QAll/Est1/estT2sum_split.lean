import Mathlib.Tactic.Module
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseC3QAll.Est1.estT2sum_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.estT2sum_split` — the split of `‖Y_kΦ‖²`

The first (purely algebraic) step of piece **B** (`Est1.estT2sum`): with
`Z = z/ℓ³`, `A_s = Atil F T E s k`, `b_p = F.bOp E.alpha p`,
`b_p† = F.bOpDag E.alpha p`, the shift
`Y_k = Z Σ_{s∈excited} γ_{sk}·(b_{s-k}† ∘ A_s)` satisfies

  `‖Y_kΦ‖² = Z²·(T2ComF F T E k Φ + T2OpF F T E k Φ)`.

Indeed, `F.bp` is bilinear and `b_q†` is the adjoint of `b_q`
(`Est1.bp_bOpDag_left`), so

  `bp (b_p† u) (b_q† v) = bp u (b_p (b_q† v)) = bp (b_q u) (b_p v) + [b_p,b_q†]·bp u v`

where the squeezed commutator `[b_p,b_q†]` is the scalar
`ccrK p q - α_pα_q ccrK(-q)(-p)` (`bOp_mul_bOpDag`, from the four elementary
commutators of `FockData`).  At `p = s-k`, `q = s'-k` this is `kCom F E s s' k`
(`kCom_eq''`, by `Q3KernelFSAll.hasKernel` and the evenness of `χ̂, χ̂²`).

## Contents

* `bOp_mul_bOpDag` — the general squeezed commutator.
* `kCom_eq''` — the scalar in the `kCom` normal form.
* `bp_bOpDag_bOpDag` — the termwise identity.
* `estT2sum_split` — the requested split.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

namespace Est1

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The general squeezed commutator -/

/-- `b_p b_q† = b_q† b_p + [b_p,b_q†]` with `[b_p,b_q†] = ccrK p q - α_pα_q ccrK(-q)(-p)`.

Expanding `b_p b_q† = (a_p + α_pa_{-p}†)(a_q† + α_qa_{-q})` and using the four
elementary commutators `[a_p,a_q†] = ccrK p q`, `[a_p,a_{-q}] = 0`,
`[a_{-p}†,a_q†] = 0`, `[a_{-p}†,a_{-q}] = -ccrK(-q)(-p)`. -/
theorem bOp_mul_bOpDag (F : FockData Mode) (E : Q3Env Mode) (p q : Mode) :
    F.bOp E.alpha p ∘ₗ F.bOpDag E.alpha q
      = F.bOpDag E.alpha q ∘ₗ F.bOp E.alpha p
        + (F.ccrK p q - E.alpha p * E.alpha q * F.ccrK (-q) (-p)) • (1 : F.H →ₗ[ℝ] F.H) := by
  have hA : ∀ f : F.H, F.a p (F.aDag q f) = F.aDag q (F.a p f) + (F.ccrK p q) • f := by
    intro f
    have h := congrArg (fun g : F.H →ₗ[ℝ] F.H => g f) (F.ccr p q)
    simpa using h
  have hB : ∀ f : F.H, F.a p (F.a (-q) f) = F.a (-q) (F.a p f) := by
    intro f
    have h := congrArg (fun g : F.H →ₗ[ℝ] F.H => g f) (F.ann_comm p (-q))
    simpa using h
  have hC : ∀ f : F.H, F.aDag (-p) (F.aDag q f) = F.aDag q (F.aDag (-p) f) := by
    intro f
    have h := congrArg (fun g : F.H →ₗ[ℝ] F.H => g f) (F.cre_comm (-p) q)
    simpa using h
  have hD : ∀ f : F.H, F.aDag (-p) (F.a (-q) f)
      = F.a (-q) (F.aDag (-p) f) - (F.ccrK (-q) (-p)) • f := by
    intro f
    have h := congrArg (fun g : F.H →ₗ[ℝ] F.H => g f) (F.ccr (-q) (-p))
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] at h
    rw [h]
    module
  ext f
  simp only [FockData.bOp, FockData.bOpDag, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_add, map_smul]
  rw [hA f, hB f, hC f, hD f]
  simp only [Module.End.one_apply]
  module

/-- The scalar of `bOp_mul_bOpDag` at `p = s-k`, `q = s'-k` is `Est1.kCom`:
`ccrK (k-s')(k-s) = ccrK (k-s)(k-s')` by `Q3KernelFSAll.hasKernel` and the evenness
of `χ̂` and `χ̂²`. -/
theorem kCom_eq'' {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3KernelFSAll K₀ F T E) (s s' k : Mode)
    (hs : E.fL s ≠ 0) (hs' : E.fL s' ≠ 0) (hk : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) :
    F.ccrK (s - k) (s' - k) - E.alpha (s - k) * E.alpha (s' - k) * F.ccrK (k - s') (k - s)
      = kCom F E s s' k := by
  have hsym : F.ccrK (k - s') (k - s) = F.ccrK (k - s) (k - s') := by
    rw [kerE hK s s' k hs hs' hk hW, kerD hK s s' k hs hs' hk hW]
  rw [hsym, kCom]

/-! ## 2. The termwise identity -/

/-- `F.bp u (b_q† v) = F.bp (b_q u) v` (adjointness of `b_q†` in the second slot). -/
theorem bp_right_bOpDag (F : FockData Mode) (E : Q3Env Mode) (q : Mode) (u v : F.H) :
    F.bp u (F.bOpDag E.alpha q v) = F.bp (F.bOp E.alpha q u) v := by
  rw [F.bp_symm u (F.bOpDag E.alpha q v), bp_bOpDag_left, F.bp_symm (F.bOp E.alpha q u) v]

/-- The termwise commutator identity: with `p = s-k`, `q = s'-k`,

  `bp (b_p† (A_sΦ)) (b_q† (A_{s'}Φ)) = bp (b_q (A_sΦ)) (b_p (A_{s'}Φ))
     + kCom F E s s' k · bp (A_sΦ) (A_{s'}Φ)`. -/
theorem bp_bOpDag_bOpDag {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3KernelFSAll K₀ F T E) (k s s' : Mode) (hs : E.fL s ≠ 0) (hs' : E.fL s' ≠ 0)
    (hk : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) (Φ : F.H) :
    F.bp (F.bOpDag E.alpha (s - k) (Atil F T E s k Φ))
        (F.bOpDag E.alpha (s' - k) (Atil F T E s' k Φ))
      = F.bp (F.bOp E.alpha (s' - k) (Atil F T E s k Φ))
          (F.bOp E.alpha (s - k) (Atil F T E s' k Φ))
        + kCom F E s s' k * F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ) := by
  have hcomm := LinearMap.congr_fun (bOp_mul_bOpDag F E (s - k) (s' - k))
    (Atil F T E s' k Φ)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply] at hcomm
  have e1 : -(s' - k) = k - s' := by abel
  have e2 : -(s - k) = k - s := by abel
  rw [e1, e2] at hcomm
  have hcoef := kCom_eq'' hK s s' k hs hs' hk hW
  rw [bp_bOpDag_left, hcomm, map_add, map_smul, smul_eq_mul, bp_right_bOpDag, ← hcoef]

/-- `bp (c • X) (d • Y) = c * d * bp X Y`. -/
theorem bp_smul_smul (F : FockData Mode) (c d : ℝ) (X Y : F.H) :
    F.bp (c • X) (d • Y) = c * d * F.bp X Y := by
  have h1 : F.bp (c • X) = c • F.bp X := map_smul (F.bp) c X
  have h2 : (F.bp X) (d • Y) = d • (F.bp X Y) := map_smul (F.bp X) d Y
  rw [h1, LinearMap.smul_apply, h2, smul_smul, smul_eq_mul]

/-! ## 3. The split -/

/-- `bp` of two finite sums (expansion of the bilinear form). -/
theorem bp_sum_sum' (F : FockData Mode) (S : Finset Mode) (u v : Mode → F.H) :
    F.bp (∑ s ∈ S, u s) (∑ s' ∈ S, v s') = ∑ s ∈ S, ∑ s' ∈ S, F.bp (u s) (v s') := by
  have h1 : F.bp (∑ s ∈ S, u s) = ∑ s ∈ S, F.bp (u s) := map_sum (F.bp) u S
  rw [h1, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun s _ => map_sum (F.bp (u s)) v S

/-- The value of the shift on a vector: `Y_kΦ = Z Σ_{s∈excited} γ_{sk}·(b_{s-k}† (A_{sk}Φ))`. -/
theorem shift_apply (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (k : Mode)
    (Φ : F.H) :
    (shift F T E k) Φ = (E.z / E.ell ^ 3) •
      ∑ s ∈ excited Mode, (gA E s k) •
        (F.bOpDag E.alpha (s - k) (Atil F T E s k Φ)) := by
  simp only [shift, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    map_sum, map_smul]

theorem estT2sum_split {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3KernelFSAll K₀ F T E) (k : Mode) (hk : k ∈ F.PHset E) (Φ : F.H) :
    F.bp (shift F T E k Φ) (shift F T E k Φ)
      = (E.z / E.ell ^ 3) ^ 2 * (T2ComF F T E k Φ + T2OpF F T E k Φ) := by
  classical
  have hexp : F.bp (∑ s ∈ excited Mode, (gA E s k) •
        (F.bOpDag E.alpha (s - k) (Atil F T E s k Φ)))
      (∑ s' ∈ excited Mode, (gA E s' k) •
        (F.bOpDag E.alpha (s' - k) (Atil F T E s' k Φ)))
      = T2OpF F T E k Φ + T2ComF F T E k Φ := by
    rw [bp_sum_sum', T2OpF, T2ComF, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s' _ => ?_
    by_cases hf : E.fL s = 0 ∨ E.fL s' = 0
    · obtain h | h := hf
      · simp [gA, h]
      · simp [gA, h]
    · have hs : E.fL s ≠ 0 := fun h => hf (Or.inl h)
      have hs' : E.fL s' ≠ 0 := fun h => hf (Or.inr h)
      by_cases hW : E.W1 k = 0
      · simp only [gA, T2OpF, T2ComF, hW, mul_zero, zero_mul, zero_smul, add_zero,
          map_zero, LinearMap.zero_apply]
      rw [bp_smul_smul]
      rw [bp_bOpDag_bOpDag hK k s s' hs hs' hk hW Φ]
      ring
  rw [shift_apply, bp_smul_smul, hexp]
  ring

end Est1

end Work.BoseC3QAll
