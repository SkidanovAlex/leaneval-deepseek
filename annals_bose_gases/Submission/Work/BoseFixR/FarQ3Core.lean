import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixR.FarBogPair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/FarQ3Core.lean` — the `ετ`-completion of the cubic word

FS §9's `eq:Rough1` at the honest family: the cubic word `T.Q3T Eρ` and the kinetic
reserve `½Σ_k ε τ_k⟨(n_k+n_{-k})f,f⟩` together dominate a negative multiple of `‖f‖²`.
This module contains the part of that argument that is *pure algebra plus the
per-mode completing square* — independent of the analytic row `HonW1sqRowAbs` and
of the arithmetic:

* `shiftZDag` — the "shift" operator `Z_k† = Σ_s f_L(s) a_{s-k}† ã_s` of FS's
  completing square `eq:RoughQ3_1`;
* `qw_Q3T_eq` — the identity

  `⟨f, Q3T E f⟩ = 2(z/ℓ³)Σ_{k∈P_H} Ŵ₁(k)⟨a_kf, Z_k† f⟩`,

  i.e. the cubic word is (twice) the sum of the shift blocks;
* `Q3T_block_ge` — the per-mode completing square (`Work.BoseB7A.completing_square`
  applied with `b = a_k`, `Y = (z/ℓ³)Ŵ₁(k)Z_k†`):

  `-(2/(ε‖k‖²))r_k²‖Z_k†f‖² ≤ (ε‖k‖²/2)‖a_kf‖² + 2r_k⟨a_kf, Z_k†f⟩`, `r_k = (z/ℓ³)Ŵ₁(k)`;
* `reserve_ge` — the reserve `½Σ_k ετ_k⟨(n_k+n_{-k})f,f⟩` dominates the kinetic
  blocks `Σ_{k∈P_H}(ε‖k‖²/2)‖a_kf‖²` (using `τ_k ≥ ‖k‖²/2` on `P_H`, which the
  caller supplies as `hτge`, and the evenness of `τ`).

The two analytic inputs (`HonW1sqRowAbs`, `HonTauGeHalfSq`) and the final
arithmetic are consumed in `FarQ3Wedge.lean`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseFixR

open Work.BoseB7 Work.BoseB7A

set_option autoImplicit false
set_option linter.unusedVariables false

variable {L : Type*} [AddCommGroup L] [Fintype L] [DecidableEq L]

/-! ## 1. The shift operator `Z_k†` -/

/-- **FS's shift `Z_k† = Σ_{s∈excited} f_L(s)·a_{s-k}†ã_s`** (the formal adjoint of
`Z_k = Σ_s f_L(s)ã_s†a_{s-k}`).  In the completing square `eq:RoughQ3_1` it is the
state the cubic word is linear in. -/
def shiftZDag (F : FockData L) (T : TildeData F) (E : Q3Env L) (k : L) :
    F.H →ₗ[ℝ] F.H :=
  ∑ s ∈ Work.BoseB7.excited L, (E.fL s) • (F.aDag (s - k) ∘ₗ T.ta s)

/-! ## 2. The quadratic form of a finite double sum with weights -/

/-- `qw` of a doubly-indexed weighted sum. -/
lemma qw_sum₂ (F : FockData L) (S S' : Finset L) (w : L → L → ℝ)
    (op : L → L → F.H →ₗ[ℝ] F.H) (f : F.H) :
    F.qw f (∑ s ∈ S, ∑ k ∈ S', w s k • op s k)
      = ∑ s ∈ S, ∑ k ∈ S', w s k * F.qw f (op s k) := by
  have h : (∑ s ∈ S, ∑ k ∈ S', w s k • op s k)
      = ∑ s ∈ S, (1 : ℝ) • (∑ k ∈ S', w s k • op s k) := by simp
  rw [h, qw_sum_finset_zp F S (fun _ => (1 : ℝ)) (fun s => ∑ k ∈ S', w s k • op s k) f]
  simp only [one_mul]
  exact Finset.sum_congr rfl fun s _ => qw_sum_finset_zp F S' (w s) (op s) f

/-! ## 3. The shift form of `Q3T` -/

/-- The two summands of `Q3T` have the same quadratic form. -/
lemma qw_qtermT_eq (F : FockData L) (T : TildeData F) (s k : L) (f : F.H) :
    F.qw f (T.qtermT s k) = F.bp (F.a k f) (F.aDag (s - k) (T.ta s f)) := by
  rw [FockData.qw]
  simp only [TildeData.qtermT, LinearMap.comp_apply]
  rw [T.taDag_adjoint s (F.a (s - k) (F.a k f)) f]
  rw [F.bp_symm (F.a (s - k) (F.a k f)) (T.ta s f)]
  rw [← F.aDag_adjoint (s - k) (T.ta s f) (F.a k f)]
  rw [F.bp_symm (F.aDag (s - k) (T.ta s f)) (F.a k f)]

lemma qw_qtermDagT_eq (F : FockData L) (T : TildeData F) (s k : L) (f : F.H) :
    F.qw f (T.qtermDagT s k) = F.bp (F.a k f) (F.aDag (s - k) (T.ta s f)) := by
  rw [FockData.qw]
  simp only [TildeData.qtermDagT, LinearMap.comp_apply]
  rw [F.aDag_adjoint k (F.aDag (s - k) (T.ta s f)) f]
  exact F.bp_symm (F.aDag (s - k) (T.ta s f)) (F.a k f)

/-- The shift pairing as a finite sum: `Σ_s f_L(s)⟨a_kf, a_{s-k}†ã_s f⟩ = ⟨a_kf, Z_k† f⟩`. -/
lemma bp_shift_eq_sum (F : FockData L) (T : TildeData F) (E : Q3Env L) (k : L) (f : F.H) :
    F.bp (F.a k f) ((shiftZDag F T E k) f)
      = ∑ s ∈ Work.BoseB7.excited L,
          E.fL s * F.bp (F.a k f) (F.aDag (s - k) (T.ta s f)) := by
  rw [shiftZDag, sum_smul_apply_zp]
  simp only [LinearMap.comp_apply]
  rw [F.bp_symm (F.a k f)
    (∑ s ∈ Work.BoseB7.excited L, E.fL s • (F.aDag (s - k) (T.ta s f)))]
  rw [bp_sum_zp]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [F.bp_symm (F.aDag (s - k) (T.ta s f)) (F.a k f)]

/-- **The shift identity for the cubic word** (FS's `eq:RoughQ3_1`'s first step):
the quadratic form of `Q3T` is twice the sum over `P_H` of the shift blocks. -/
theorem qw_Q3T_eq (F : FockData L) (T : TildeData F) (E : Q3Env L) (f : F.H) :
    F.qw f (T.Q3T E)
      = 2 * (E.z / E.ell ^ 3) *
          ∑ k ∈ F.PHset E, E.W1 k * F.bp (F.a k f) ((shiftZDag F T E k) f) := by
  -- step 1: unfold `Q3T` and rewrite each summand by the shift pairing
  have hstep : F.qw f (∑ s ∈ Work.BoseB7.excited L, ∑ k ∈ F.PHset E,
          (E.fL s * E.W1 k) • (T.qtermT s k + T.qtermDagT s k))
      = ∑ s ∈ Work.BoseB7.excited L, ∑ k ∈ F.PHset E,
          (E.fL s * E.W1 k) * (2 * F.bp (F.a k f) (F.aDag (s - k) (T.ta s f))) := by
    rw [qw_sum₂]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro k _
    rw [FockData.qw_add, qw_qtermT_eq, qw_qtermDagT_eq]
    ring
  -- step 2: reorganise the double sum and identify the `s`-sum with the shift state
  have hmain : (∑ s ∈ Work.BoseB7.excited L, ∑ k ∈ F.PHset E,
          (E.fL s * E.W1 k) * (2 * F.bp (F.a k f) (F.aDag (s - k) (T.ta s f))))
      = ∑ k ∈ F.PHset E, 2 * (E.W1 k * F.bp (F.a k f) ((shiftZDag F T E k) f)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    have h1 : ∀ s : L, (E.fL s * E.W1 k) * (2 * F.bp (F.a k f) (F.aDag (s - k) (T.ta s f)))
        = 2 * E.W1 k * (E.fL s * F.bp (F.a k f) (F.aDag (s - k) (T.ta s f))) := by
      intro s; ring
    rw [Finset.sum_congr rfl (fun s _ => h1 s), ← Finset.mul_sum, ← bp_shift_eq_sum]
    ring
  rw [TildeData.Q3T, FockData.qw_smul, hstep, hmain, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-! ## 4. The per-mode completing square -/

/-- **FS's completing square `eq:RoughQ3_1` per mode.**  With `r = (z/ℓ³)Ŵ₁(k)` and
the kinetic coefficient `ε‖k‖²/2`, the cubic block at the mode `k` is bounded below
by the (negative) square of the shift state. -/
theorem Q3T_block_ge (F : FockData L) (T : TildeData F) (E : Q3Env L) {ε : ℝ}
    (hε : 0 < ε) {k : L} (hk : 0 < ‖F.kmom k‖) (f : F.H) :
    -(2 / (ε * ‖F.kmom k‖ ^ 2)) * ((E.z / E.ell ^ 3) * E.W1 k) ^ 2
        * F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f)
      ≤ (ε * ‖F.kmom k‖ ^ 2 / 2) * F.bp (F.a k f) (F.a k f)
        + 2 * ((E.z / E.ell ^ 3) * E.W1 k) * F.bp (F.a k f) ((shiftZDag F T E k) f) := by
  have hc : 0 < ε * ‖F.kmom k‖ ^ 2 / 2 := by
    have : 0 < ‖F.kmom k‖ ^ 2 := pow_pos hk 2
    positivity
  have h := Work.BoseB7A.completing_square F (F.a k)
    (((E.z / E.ell ^ 3) * E.W1 k) • (shiftZDag F T E k)) (ε * ‖F.kmom k‖ ^ 2 / 2) hc f
  -- expand the `smul`'s
  have hexp : ∀ x y : F.H, F.bp (((E.z / E.ell ^ 3) * E.W1 k) • x) y
      = ((E.z / E.ell ^ 3) * E.W1 k) * F.bp x y := by
    intro x y; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hinner : ∀ (x : F.H) (r : ℝ) (y : F.H), (F.bp x) (r • y) = r * (F.bp x) y := by
    intro x r y
    rw [map_smul (F.bp x) r y, smul_eq_mul]
  have hexp2 : ∀ x y : F.H, F.bp (((E.z / E.ell ^ 3) * E.W1 k) • x)
        (((E.z / E.ell ^ 3) * E.W1 k) • y)
      = ((E.z / E.ell ^ 3) * E.W1 k) ^ 2 * F.bp x y := by
    intro x y
    rw [hexp x (((E.z / E.ell ^ 3) * E.W1 k) • y), hinner x _ y]
    ring
  simp only [LinearMap.smul_apply] at h
  rw [hexp2] at h
  rw [show F.bp (F.a k f)
        (((E.z / E.ell ^ 3) * E.W1 k) • (shiftZDag F T E k) f)
      = ((E.z / E.ell ^ 3) * E.W1 k) * F.bp (F.a k f) ((shiftZDag F T E k) f)
      from hinner (F.a k f) _ ((shiftZDag F T E k) f)] at h
  have hcpos : 0 < ε * ‖F.kmom k‖ ^ 2 / 2 := hc
  have hcinv : (ε * ‖F.kmom k‖ ^ 2 / 2)⁻¹ = 2 / (ε * ‖F.kmom k‖ ^ 2) := by
    field_simp
  rw [hcinv] at h
  linarith [h]

/-! ## 5. The reserve dominates the kinetic blocks -/

/-- The quadratic form of `n_k + n_{-k}` is the sum of the two kinetic blocks. -/
lemma qw_nOp_add (F : FockData L) (k : L) (f : F.H) :
    F.qw f (F.nOp k + F.nOp (-k))
      = F.bp (F.a k f) (F.a k f) + F.bp (F.a (-k) f) (F.a (-k) f) := by
  rw [FockData.qw_add]
  congr 1
  · rw [FockData.qw]; simp only [FockData.nOp, LinearMap.comp_apply, F.aDag_adjoint]
  · rw [FockData.qw]; simp only [FockData.nOp, LinearMap.comp_apply, F.aDag_adjoint]

/-- **The reserve covers the kinetic blocks.**  If `0 ≤ ε`, `0 ≤ τ`, `τ` is even and
`τ_k ≥ ‖k‖²/2` on `P_H`, then

  `Σ_{k∈P_H}(ε‖k‖²/2)‖a_kf‖² ≤ ½Σ_{k} ετ_k⟨(n_k+n_{-k})f,f⟩`. -/
theorem reserve_ge (F : FockData L) (E : Q3Env L) {ε : ℝ} (hε : 0 ≤ ε)
    (hτ0 : ∀ k : L, 0 ≤ E.tau k) (hτeven : ∀ k : L, E.tau (-k) = E.tau k)
    (hτge : ∀ k : L, F.PH E.KH E.aScat k → ‖F.kmom k‖ ^ 2 / 2 ≤ E.tau k) (f : F.H) :
    ∑ k ∈ F.PHset E, (ε * ‖F.kmom k‖ ^ 2 / 2) * F.bp (F.a k f) (F.a k f)
      ≤ (1 / 2) * ∑ k : L, ε * E.tau k * F.qw f (F.nOp k + F.nOp (-k)) := by
  -- the `n_k`-form is nonnegative
  have hnn : ∀ k : L, 0 ≤ F.bp (F.a k f) (F.a k f) := fun k => F.bp_nonneg (F.a k f)
  -- the reindexing `k ↦ -k`
  have hre : (∑ k : L, ε * E.tau k * F.bp (F.a (-k) f) (F.a (-k) f))
      = ∑ k : L, ε * E.tau k * F.bp (F.a k f) (F.a k f) := by
    refine Fintype.sum_equiv (Equiv.neg L) _ _
      (fun k => by simp [Equiv.neg_apply, hτeven])
  -- the reserve is a sum of nonnegative terms and covers `P_H`
  have hres : (1 / 2) * ∑ k : L, ε * E.tau k * F.qw f (F.nOp k + F.nOp (-k))
      = ∑ k : L, ε * E.tau k * F.bp (F.a k f) (F.a k f) := by
    have h1 : ∀ k : L, ε * E.tau k * F.qw f (F.nOp k + F.nOp (-k))
        = ε * E.tau k * F.bp (F.a k f) (F.a k f)
          + ε * E.tau k * F.bp (F.a (-k) f) (F.a (-k) f) := by
      intro k
      rw [qw_nOp_add]
      ring
    rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_add_distrib, hre]
    ring
  rw [hres]
  -- drop the terms outside `P_H` and the `k = 0` term (all nonnegative)
  have hsub : F.PHset E ⊆ (Finset.univ : Finset L) := Finset.subset_univ _
  have hnonneg : ∀ k ∈ (Finset.univ : Finset L), k ∉ F.PHset E →
      0 ≤ ε * E.tau k * F.bp (F.a k f) (F.a k f) := by
    intro k _ _
    exact mul_nonneg (mul_nonneg hε (hτ0 k)) (hnn k)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  refine le_trans ?_ hle
  -- the termwise bound on `P_H`
  refine Finset.sum_le_sum fun k hk => ?_
  have hPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
  have hkge := hτge k hPH
  have hknn : 0 ≤ F.bp (F.a k f) (F.a k f) := hnn k
  have h1 : ε * (‖F.kmom k‖ ^ 2 / 2) ≤ ε * E.tau k := mul_le_mul_of_nonneg_left hkge hε
  calc (ε * ‖F.kmom k‖ ^ 2 / 2) * F.bp (F.a k f) (F.a k f)
      = (ε * (‖F.kmom k‖ ^ 2 / 2)) * F.bp (F.a k f) (F.a k f) := by ring
    _ ≤ (ε * E.tau k) * F.bp (F.a k f) (F.a k f) :=
        mul_le_mul_of_nonneg_right h1 hknn
    _ = ε * E.tau k * F.bp (F.a k f) (F.a k f) := by ring

end Work.BoseFixR
