import Mathlib
import Submission.Work.BoseB7A.NWindow_bp_N_le
import Submission.Work.BoseB7A.NWindow_shift
import Submission.Work.BoseB7A.NWindow_ta_sum
import Submission.Work.BoseB7A.absorb_errA
import Submission.Work.BoseB7A.q3Denom_le_four
import Submission.Work.BoseB7A.smallness_ratios
import Submission.Work.BoseB7A.sum_W1alpha_le
import Submission.Work.BoseB7A.sum_W1alpha_sub_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7A.estQ3twoThreeA` — FS `eq:EstimateQ3Tilde2+3` (`Q₃⁽²⁾ + Q₃⁽³⁾`)

The estimate of FS §10 controlling the second and third pieces of the
Bogoliubov-split cubic word `Q₃⁽²⁾ + Q₃⁽³⁾` by the kinetic reserve
`(𝓁²/2)∫_{P_H^q}𝒟_k b_k†b_k` on the quarter region `P_H^q`:

```
−C·e23A·‖Φ‖²  ≤  ⟨Φ, (Q₃⁽²⁾ + Q₃⁽³⁾ + (𝓁²/2)·dNumOpR P_H^q) Φ⟩   (Φ ∈ NWindow 𝓜).
```

## The two words and the commutator

With `p = -k`, `q = s − k` (for `Q₃⁽²⁾`) and `p = k − s`, `q = k` (for
`Q₃⁽³⁾`), each of the four monomials is of the form

`ã_s† b_p† b_q`  resp.  `b_q† b_p ã_s`,

and moving `ã_s†` (`ã_s`) past `b_p†` (`b_p`) costs a **scalar** commutator
(`taDag_bOpDag_swap`, `bOp_ta_swap`):

`[ã_s†, b_p†] = [b_p, ã_s] = −α_p·ccrX(s,−p) • 1`.

Hence the *pair* `ã_s†b_p†b_q + b_q†b_pã_s` has the quadratic form

`2⟨ã_s(b_pΦ), b_qΦ⟩ + 2σ_{sp}⟨b_qΦ, Φ⟩`,   `σ_{sp} = −α_p·ccrX(s,−p)`,

the first term an off-diagonal pairing of `ã_s(b_pΦ)` with `b_qΦ` (both factors
carrying the low/high momentum split), the second the "constant" part.

## The two absorptions

* The pairing term is bounded by `ε‖ã_s(b_pΦ)‖² + ε⁻¹‖b_qΦ‖²` (`bp_cauchy`).
  Summed over `s` with `ε = (𝓜+1)^{-1/2}` the first half is
  `√(𝓜+1)Σ_q‖b_qΦ‖²` (`NWindow_ta_sum`, the window of `b_pΦ` being `𝓜+1`) and
  the second half costs the *number* `N_f ≤ K₀(K_ℓK_L)³` of modes in the
  support of `f_L` (`Q3Kernel.count_PL`, `k ↦ s−k` injective into `P_H^q`);
  both are absorbed by the reserve, whose weight is `𝒟_q ≥ 1/(64K_H²a²)` on
  `P_H^q` (`kernel_basic`).  This is `absorb_errA`'s first two conjuncts.
* The constant part is dominated by the *sum* `Σ_{k∈P_H}|Ŵ₁(k)α_k|`: by
  `|α_k| ≤ 2ρ|Ŵ₁(k)|/‖k‖²` on `P_H^q` and `sum_W1sq` this is at most
  `2ρK₀aℓ³` (`sum_W1alpha_le`), so the whole constant part is at most
  `C ρ a ℓ³ (K_ℓK_L)³ (|z|/ℓ³)𝓁η` — exactly `e23A` up to the factor `𝓁`
  (`absorb_errA`'s third conjunct).

Everything is asserted with one absolute constant `C` depending only on `K₀`.
-/

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace Work.BoseB7A

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. Elementary lemmas about the Fock form -/

/-- Two linear maps coincide as soon as their `bp`-matrix elements do: `bp` is a
positive definite symmetric form, so `X = Y` follows from
`∀ f g, ⟨X f, g⟩ = ⟨Y f, g⟩` (take `g = (X−Y) f`). -/
theorem linearMap_ext_bp (F : FockData Mode) {X Y : F.H →ₗ[ℝ] F.H}
    (h : ∀ f g : F.H, F.bp (X f) g = F.bp (Y f) g) : X = Y := by
  ext f
  have hz : F.bp (X f - Y f) (X f - Y f) = 0 := by
    have h1 := h f (X f)
    have h2 := h f (Y f)
    have e : F.bp (X f - Y f) (X f - Y f)
        = F.bp (X f) (X f) - F.bp (X f) (Y f) - F.bp (Y f) (X f) + F.bp (Y f) (Y f) := by
      simp only [map_sub, LinearMap.sub_apply]
      ring
    rw [e, h1, h2]
    ring
  have h3 : X f - Y f = 0 := F.bp_def (X f - Y f) hz
  simpa using sub_eq_zero.mp h3

/-- **Adjoint transfer**: an operator identity `X' = Y'` transfers to `X = Y`
as soon as `X'`, `Y'` are the `bp`-adjoints of `X`, `Y`. -/
theorem op_eq_of_adjoint_eq (F : FockData Mode) {X X' Y Y' : F.H →ₗ[ℝ] F.H}
    (hX : ∀ f g : F.H, F.bp (X f) g = F.bp f (X' g))
    (hY : ∀ f g : F.H, F.bp (Y f) g = F.bp f (Y' g)) (h : X' = Y') : X = Y := by
  refine linearMap_ext_bp F fun f g => ?_
  rw [hX f g, h, hY f g]

/-- `⟨c • v, g⟩ = c * ⟨v, g⟩`, in the form used below. -/
theorem bp_smul_left (F : FockData Mode) (c : ℝ) (v g : F.H) :
    F.bp (c • v) g = c * F.bp v g := by
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- The adjointness of the mode operators, in the four directions used below. -/
theorem bp_a (F : FockData Mode) (p : Mode) (X g : F.H) :
    F.bp (F.a p X) g = F.bp X (F.aDag p g) := by
  rw [F.bp_symm (F.a p X) g, ← F.aDag_adjoint p g X, F.bp_symm (F.aDag p g) X]

theorem bp_aDag (F : FockData Mode) (p : Mode) (X g : F.H) :
    F.bp (F.aDag p X) g = F.bp X (F.a p g) := F.aDag_adjoint p X g

theorem bp_ta (F : FockData Mode) (T : TildeData F) (s : Mode) (X g : F.H) :
    F.bp (T.ta s X) g = F.bp X (T.taDag s g) := by
  rw [F.bp_symm (T.ta s X) g, ← T.taDag_adjoint s g X, F.bp_symm (T.taDag s g) X]

theorem bp_taDag (F : FockData Mode) (T : TildeData F) (s : Mode) (X g : F.H) :
    F.bp (T.taDag s X) g = F.bp X (T.ta s g) := T.taDag_adjoint s X g

theorem bp_bOpDag (F : FockData Mode) {α : Mode → ℝ} (i : Mode) (X g : F.H) :
    F.bp (F.bOpDag α i X) g = F.bp X (F.bOp α i g) :=
  Work.BoseB7.bOpDag_adjoint F α i X g

/-! ## 2. The `ã`–`a` commutators (adjoints of the `TildeData` grading fields) -/

/-- `[a_p†, ã_s] = −ccrX s p`: the `TildeData.ta_aDag` field, rearranged. -/
theorem aDag_ta_comm (F : FockData Mode) (T : TildeData F) (s p : Mode) :
    F.aDag p ∘ₗ T.ta s
      = T.ta s ∘ₗ F.aDag p - (T.ccrX s p) • (1 : F.H →ₗ[ℝ] F.H) := by
  have h := T.ta_aDag s p
  rw [h]
  abel

/-- `[ã_s†, a_p†] = 0`, i.e. `ã_s†` commutes with every creation operator: the
adjoint of `TildeData.ta_a_comm`. -/
theorem taDag_aDag_comm (F : FockData Mode) (T : TildeData F) (s p : Mode) :
    T.taDag s ∘ₗ F.aDag p = F.aDag p ∘ₗ T.taDag s := by
  refine op_eq_of_adjoint_eq F (X := T.taDag s ∘ₗ F.aDag p) (X' := F.a p ∘ₗ T.ta s)
    (Y := F.aDag p ∘ₗ T.taDag s) (Y' := T.ta s ∘ₗ F.a p) ?_ ?_ (T.ta_a_comm s p).symm
  · intro f g
    simp only [LinearMap.comp_apply]
    rw [bp_taDag, bp_aDag]
  · intro f g
    simp only [LinearMap.comp_apply]
    rw [bp_aDag, bp_taDag]

/-- `[ã_s†, a_p] = −ccrX s p`: the adjoint of `TildeData.ta_aDag`
(`[ã_s, a_p†] = ccrX s p`). -/
theorem taDag_a_comm (F : FockData Mode) (T : TildeData F) (s p : Mode) :
    T.taDag s ∘ₗ F.a p
      = F.a p ∘ₗ T.taDag s - (T.ccrX s p) • (1 : F.H →ₗ[ℝ] F.H) := by
  refine op_eq_of_adjoint_eq F (X := T.taDag s ∘ₗ F.a p) (X' := F.aDag p ∘ₗ T.ta s)
    (Y := F.a p ∘ₗ T.taDag s - (T.ccrX s p) • (1 : F.H →ₗ[ℝ] F.H))
    (Y' := T.ta s ∘ₗ F.aDag p - (T.ccrX s p) • (1 : F.H →ₗ[ℝ] F.H)) ?_ ?_
    (aDag_ta_comm F T s p)
  · intro f g
    simp only [LinearMap.comp_apply]
    rw [bp_taDag, bp_a]
  · intro f g
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    rw [bp_a, bp_taDag]

/-! ## 3. The two swaps of `ã` past `b` -/

/-- `[b_p, ã_s] = −α_p ccrX(s,−p) • 1`: moving `ã_s` from the right of `b_p` to
its left.  The corresponding scalar is the squeezing parameter times the
`ã`–`a` commutator. -/
theorem bOp_ta_swap (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
    (s p : Mode) :
    F.bOp E.alpha p ∘ₗ T.ta s
      = T.ta s ∘ₗ F.bOp E.alpha p +
        (-(E.alpha p * T.ccrX s (-p))) • (1 : F.H →ₗ[ℝ] F.H) := by
  ext f
  have h1 : F.a p (T.ta s f) = T.ta s (F.a p f) := by
    have h := LinearMap.congr_fun (T.ta_a_comm s p) f
    simpa only [LinearMap.comp_apply] using h.symm
  have h2 : F.aDag (-p) (T.ta s f) = T.ta s (F.aDag (-p) f) - (T.ccrX s (-p)) • f := by
    have h := LinearMap.congr_fun (T.ta_aDag s (-p)) f
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] at h
    rw [eq_sub_iff_add_eq, ← h]
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, FockData.bOp, map_add, map_smul]
  rw [h1, h2]
  module

/-- `[ã_s†, b_p†] = −α_p ccrX(s,−p) • 1`: the `bp`-adjoint of `bOp_ta_swap`.
Necessary for the word `ã_s† b_p† b_q`: it moves `ã_s†` from the left of the word
to the right. -/
theorem taDag_bOpDag_swap (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
    (s p : Mode) :
    T.taDag s ∘ₗ F.bOpDag E.alpha p
      = F.bOpDag E.alpha p ∘ₗ T.taDag s +
        (-(E.alpha p * T.ccrX s (-p))) • (1 : F.H →ₗ[ℝ] F.H) := by
  refine op_eq_of_adjoint_eq F
    (X := T.taDag s ∘ₗ F.bOpDag E.alpha p)
    (X' := F.bOp E.alpha p ∘ₗ T.ta s)
    (Y := F.bOpDag E.alpha p ∘ₗ T.taDag s +
      (-(E.alpha p * T.ccrX s (-p))) • (1 : F.H →ₗ[ℝ] F.H))
    (Y' := T.ta s ∘ₗ F.bOp E.alpha p +
      (-(E.alpha p * T.ccrX s (-p))) • (1 : F.H →ₗ[ℝ] F.H)) ?_ ?_
    (bOp_ta_swap F T E s p)
  · intro f g
    simp only [LinearMap.comp_apply]
    rw [bp_taDag, bp_bOpDag]
  · intro f g
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_add, map_smul, smul_eq_mul]
    rw [bp_bOpDag, bp_taDag]

/-! ## 4. Linearity of the quadratic form, and the word identity -/

/-- Linearity of `qw` in the operator: `qw` is the quadratic form
`Φ ↦ ⟨A Φ, Φ⟩`, so it is linear in `A`. -/
theorem qw_finset_sum {ι : Type*} (F : FockData Mode) (Φ : F.H) (t : Finset ι)
    (c : ι → ℝ) (X : ι → F.H →ₗ[ℝ] F.H) :
    F.qw Φ (∑ i ∈ t, c i • X i) = ∑ i ∈ t, c i * F.qw Φ (X i) := by
  have h1 : (∑ i ∈ t, c i • X i) Φ = ∑ i ∈ t, c i • (X i Φ) := by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.smul_apply]
  calc F.qw Φ (∑ i ∈ t, c i • X i)
      = F.bp (∑ i ∈ t, c i • (X i Φ)) Φ := by rw [FockData.qw, h1]
    _ = (∑ i ∈ t, F.bp (c i • (X i Φ))) Φ := by rw [map_sum]
    _ = ∑ i ∈ t, (F.bp (c i • (X i Φ))) Φ := by rw [LinearMap.sum_apply]
    _ = ∑ i ∈ t, c i * F.bp (X i Φ) Φ :=
        Finset.sum_congr rfl fun i _ => bp_smul_left F (c i) (X i Φ) Φ
    _ = ∑ i ∈ t, c i * F.qw Φ (X i) :=
        Finset.sum_congr rfl fun i _ => by rw [FockData.qw]

/-- Linearity of `qw` in a scalar multiple. -/
theorem qw_smul' (F : FockData Mode) (Φ : F.H) (c : ℝ) (X : F.H →ₗ[ℝ] F.H) :
    F.qw Φ (c • X) = c * F.qw Φ X := by
  rw [FockData.qw, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    FockData.qw]

/-- `|a| * (|b| * X) = |a * b| * X`. -/
theorem abs_mul_abs_mul (a b X : ℝ) : |a| * (|b| * X) = |a * b| * X := by
  rw [abs_mul]; ring

/-- Linearity of `qw` in a scalar multiple of a sum. -/
theorem qw_smul_sum {ι : Type*} (F : FockData Mode) (Φ : F.H) (z : ℝ) (t : Finset ι)
    (c : ι → ℝ) (X : ι → F.H →ₗ[ℝ] F.H) :
    F.qw Φ (z • ∑ i ∈ t, c i • X i) = z * ∑ i ∈ t, c i * F.qw Φ (X i) := by
  have key : F.qw Φ (∑ i ∈ t, c i • X i) = ∑ i ∈ t, c i * F.qw Φ (X i) :=
    qw_finset_sum F Φ t c X
  simp only [FockData.qw] at key ⊢
  rw [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, key]

/-- Linearity of `qw` in a scalar multiple of a double sum. -/
theorem qw_double_sum (F : FockData Mode) (Φ : F.H) (z : ℝ) (t₁ t₂ : Finset Mode)
    (c : Mode → Mode → ℝ) (X : Mode → Mode → F.H →ₗ[ℝ] F.H) :
    F.qw Φ (z • ∑ s ∈ t₁, ∑ k ∈ t₂, c s k • X s k)
      = z * ∑ s ∈ t₁, ∑ k ∈ t₂, c s k * F.qw Φ (X s k) := by
  have h1 : (∑ s ∈ t₁, ∑ k ∈ t₂, c s k • X s k)
      = ∑ s ∈ t₁, (1 : ℝ) • (∑ k ∈ t₂, c s k • X s k) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [one_smul]
  rw [h1, qw_smul_sum F Φ z t₁ (fun _ => 1) (fun s => ∑ k ∈ t₂, c s k • X s k)]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [qw_finset_sum F Φ t₂ (fun k => c s k) (fun k => X s k)]
  ring

/-- **The single-term bound.**  For a word whose quadratic form is
`A·(2⟨u,v⟩ + 2σ⟨v,Φ⟩)` (the form produced by `qw_word_eq`), the elementary
inequalities `2⟨u,v⟩ ≤ ε‖u‖² + ε⁻¹‖v‖²` and `2|⟨v,Φ⟩| ≤ ‖v‖² + ‖Φ‖²` give

`-|A|(ε‖u‖² + ε⁻¹‖v‖² + |σ|(‖v‖² + ‖Φ‖²)) ≤ A(2⟨u,v⟩ + 2σ⟨v,Φ⟩)`. -/
theorem word_bound (F : FockData Mode) (Φ u v : F.H) (A σ ε : ℝ) (hε : 0 < ε) :
    -( |A| * (ε * F.bp u u + ε⁻¹ * F.bp v v + |σ| * (F.bp v v + F.bp Φ Φ)) )
      ≤ A * (2 * F.bp u v + 2 * σ * F.bp v Φ) := by
  have h1 : 2 * F.bp u v ≤ ε * F.bp u u + ε⁻¹ * F.bp v v := bp_cauchy F hε u v
  have h2 : -(2 * F.bp u v) ≤ ε * F.bp u u + ε⁻¹ * F.bp v v := by
    have h := bp_cauchy F hε (-u) v
    simpa using h
  have h3 : 2 * F.bp v Φ ≤ F.bp v v + F.bp Φ Φ := by
    have h := bp_cauchy F (by norm_num : (0 : ℝ) < 1) v Φ
    simpa using h
  have h4 : -(2 * F.bp v Φ) ≤ F.bp v v + F.bp Φ Φ := by
    have h := bp_cauchy F (by norm_num : (0 : ℝ) < 1) (-v) Φ
    simpa using h
  have h5 : |2 * F.bp u v| ≤ ε * F.bp u u + ε⁻¹ * F.bp v v := by
    rw [abs_le]
    exact ⟨by linarith, h1⟩
  have h6 : |2 * F.bp v Φ| ≤ F.bp v v + F.bp Φ Φ := by
    rw [abs_le]
    exact ⟨by linarith, h3⟩
  have h7 : -( |A| * (ε * F.bp u u + ε⁻¹ * F.bp v v)) ≤ A * (2 * F.bp u v) := by
    have h8 : |A * (2 * F.bp u v)| = |A| * |2 * F.bp u v| := abs_mul A _
    have h9 : |A| * |2 * F.bp u v| ≤ |A| * (ε * F.bp u u + ε⁻¹ * F.bp v v) :=
      mul_le_mul_of_nonneg_left h5 (abs_nonneg A)
    have h10 : -(A * (2 * F.bp u v)) ≤ |A * (2 * F.bp u v)| := neg_le_abs _
    linarith [h8]
  have h11 : -( |A| * (|σ| * (F.bp v v + F.bp Φ Φ)) ) ≤ A * (2 * σ * F.bp v Φ) := by
    have h8 : |2 * σ * F.bp v Φ| = |σ| * |2 * F.bp v Φ| := by
      rw [show (2 : ℝ) * σ * F.bp v Φ = σ * (2 * F.bp v Φ) from by ring, abs_mul]
    have h9 : |A| * |2 * σ * F.bp v Φ| ≤ |A| * (|σ| * (F.bp v v + F.bp Φ Φ)) := by
      rw [h8]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h6 (abs_nonneg σ))
        (abs_nonneg A)
    have h10 : -(A * (2 * σ * F.bp v Φ)) ≤ |A * (2 * σ * F.bp v Φ)| := neg_le_abs _
    have h12 : |A * (2 * σ * F.bp v Φ)| = |A| * |2 * σ * F.bp v Φ| := abs_mul A _
    linarith [h12]
  have e1 : -( |A| * (ε * F.bp u u + ε⁻¹ * F.bp v v + |σ| * (F.bp v v + F.bp Φ Φ)) )
      = -( |A| * (ε * F.bp u u + ε⁻¹ * F.bp v v))
        - (|A| * (|σ| * (F.bp v v + F.bp Φ Φ))) := by ring
  have e2 : A * (2 * F.bp u v + 2 * σ * F.bp v Φ)
      = A * (2 * F.bp u v) + A * (2 * σ * F.bp v Φ) := by ring
  rw [e1, e2]
  linarith [h7, h11]

/-- A sum over a reindexed finset is at most the sum over a larger finset,
provided the reindexing is injective and lands in the larger finset. -/
theorem sum_le_sum_of_inj {ι : Type*} [DecidableEq ι] {t u : Finset ι} {φ : ι → ι}
    (hφ : ∀ i j, φ i = φ j → i = j) (hsub : ∀ i ∈ t, φ i ∈ u) {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) : ∑ i ∈ t, f (φ i) ≤ ∑ j ∈ u, f j := by
  rw [← Finset.sum_image (fun x _ y _ h => hφ x y h)]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) (fun j _ _ => hf j)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact hsub i hi

/-- The constant of the estimate: a function of `K₀` only. -/
noncomputable def CtwoThree (K₀ : ℝ) : ℝ := 10 ^ 6 * (K₀ + 1) ^ 10 + 2

theorem CtwoThree_pos (K₀ : ℝ) : 0 < CtwoThree K₀ := by
  rw [CtwoThree]
  positivity

/-- **The word identity.**  For the pair of monomials
`ã_s†b_p†b_q + b_q†b_pã_s` (FS's `Q₃⁽²⁾`/`Q₃⁽³⁾` summands, with `b` the squeezed
modes and `ã` the θ-mode), the two scalar commutators
`[ã_s†,b_p†] = σ•1`, `[b_p,ã_s] = σ•1` convert the quadratic form into the
off-diagonal pairing plus the constant part:

`⟨Φ, (ã_s†b_p†b_q + b_q†b_pã_s) Φ⟩ = 2⟨ã_s(b_pΦ), b_qΦ⟩ + 2σ⟨b_qΦ,Φ⟩`. -/
theorem qw_word_eq (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
    (s p q : Mode) (σ : ℝ)
    (h1 : T.taDag s ∘ₗ F.bOpDag E.alpha p
      = F.bOpDag E.alpha p ∘ₗ T.taDag s + σ • (1 : F.H →ₗ[ℝ] F.H))
    (h2 : F.bOp E.alpha p ∘ₗ T.ta s
      = T.ta s ∘ₗ F.bOp E.alpha p + σ • (1 : F.H →ₗ[ℝ] F.H))
    (Φ : F.H) :
    F.qw Φ ((T.taDag s ∘ₗ (F.bOpDag E.alpha p ∘ₗ F.bOp E.alpha q)) +
        (F.bOpDag E.alpha q ∘ₗ (F.bOp E.alpha p ∘ₗ T.ta s)))
      = 2 * F.bp (T.ta s (F.bOp E.alpha p Φ)) (F.bOp E.alpha q Φ)
        + 2 * σ * F.bp (F.bOp E.alpha q Φ) Φ := by
  have e1 : ∀ v : F.H, T.taDag s (F.bOpDag E.alpha p v)
      = F.bOpDag E.alpha p (T.taDag s v) + σ • v := by
    intro v
    have h := LinearMap.congr_fun h1 v
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] using h
  have e2 : F.bOp E.alpha p (T.ta s Φ) = T.ta s (F.bOp E.alpha p Φ) + σ • Φ := by
    have h := LinearMap.congr_fun h2 Φ
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] using h
  simp only [FockData.qw, LinearMap.add_apply, LinearMap.comp_apply]
  rw [e1 (F.bOp E.alpha q Φ), e2]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  simp only [bp_bOpDag]
  rw [bp_taDag,
    F.bp_symm (F.bOp E.alpha q Φ) (T.ta s (F.bOp E.alpha p Φ)),
    F.bp_symm Φ (F.bOp E.alpha q Φ)]
  ring

/-! ## 4b. The summation helpers

The quadratic form of `Q₃⁽²⁾ + Q₃⁽³⁾` splits into four families of sums over the
`(s,k)` pairs; each is bounded here in isolation, with the coefficient function
and the pairing vector as parameters, so that the estimate below is a matter of
instantiating them. -/

/-- `kmom 0 = 0` (from `kmom (-i) = -kmom i`). -/
theorem kmom_zero (F : FockData Mode) : F.kmom 0 = 0 := by
  have h2 := F.kmom_neg 0
  rw [neg_zero] at h2
  have h : F.kmom 0 + F.kmom 0 = 0 := by
    nth_rewrite 1 [h2]
    abel
  have h3 : (2 : ℝ) • F.kmom 0 = 0 := by
    rw [two_smul]
    exact h
  exact (smul_eq_zero.mp h3).resolve_left (by norm_num)

/-- Pulling a constant out of a double sum. -/
theorem sum_const_mul_sum {ι κ : Type*} (t : Finset ι) (u : Finset κ) (c : ℝ)
    (f : ι → κ → ℝ) :
    ∑ i ∈ t, ∑ j ∈ u, c * f i j = c * ∑ i ∈ t, ∑ j ∈ u, f i j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

/-- **The `u`-part** of a word whose pairing vector is `ã_s(g k)` with `g`
independent of `s`: the window bound `Σ_s‖ã_sΨ‖² ≤ (𝓜+1)‖Ψ‖²` applied to each
`g k`. -/
theorem sum_u_le (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
    {M : ℝ} (hM : 0 ≤ M) {ε Wc : ℝ} (hε : 0 < ε) (hWc : 0 ≤ Wc)
    {c : Mode → Mode → ℝ} (hc : ∀ s k : Mode, k ∈ F.PHset E → |c s k| ≤ Wc)
    {g : Mode → F.H} (hg : ∀ k, T.NWindow (M + 1) (g k)) :
    (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
        |c s k| * (ε * F.bp (T.ta s (g k)) (T.ta s (g k))))
      ≤ Wc * (ε * (M + 1)) * (∑ k ∈ F.PHset E, F.bp (g k) (g k)) := by
  have hnonzero : ∀ s ∈ excited Mode, s ≠ 0 := fun s hs => by
    rw [Work.BoseB7.excited, Finset.mem_erase] at hs
    exact hs.1
  have h1 : (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
        |c s k| * (ε * F.bp (T.ta s (g k)) (T.ta s (g k))))
      ≤ ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
          Wc * (ε * F.bp (T.ta s (g k)) (T.ta s (g k))) := by
    refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun k hk => ?_
    exact mul_le_mul_of_nonneg_right (hc s k hk) (mul_nonneg hε.le (F.bp_nonneg _))
  have h2 : (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
        Wc * (ε * F.bp (T.ta s (g k)) (T.ta s (g k))))
      = (ε * Wc) * (∑ k ∈ F.PHset E, ∑ s ∈ excited Mode,
          F.bp (T.ta s (g k)) (T.ta s (g k))) := by
    rw [show (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
          Wc * (ε * F.bp (T.ta s (g k)) (T.ta s (g k))))
        = ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
            (ε * Wc) * F.bp (T.ta s (g k)) (T.ta s (g k)) from by
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring]
    rw [sum_const_mul_sum, Finset.sum_comm]
  have h3 : (∑ k ∈ F.PHset E, ∑ s ∈ excited Mode,
        F.bp (T.ta s (g k)) (T.ta s (g k)))
      ≤ ∑ k ∈ F.PHset E, (M + 1) * F.normSq (g k) :=
    Finset.sum_le_sum fun k _ =>
      NWindow_ta_sum F T (by linarith) (hg k) (excited Mode) hnonzero
  have h4 : (∑ k ∈ F.PHset E, (M + 1) * F.normSq (g k))
      = (M + 1) * (∑ k ∈ F.PHset E, F.normSq (g k)) :=
    (Finset.mul_sum (F.PHset E) (fun k => F.normSq (g k)) (M + 1)).symm
  calc (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
        |c s k| * (ε * F.bp (T.ta s (g k)) (T.ta s (g k))))
      ≤ ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
          Wc * (ε * F.bp (T.ta s (g k)) (T.ta s (g k))) := h1
    _ = (ε * Wc) * (∑ k ∈ F.PHset E, ∑ s ∈ excited Mode,
          F.bp (T.ta s (g k)) (T.ta s (g k))) := h2
    _ ≤ (ε * Wc) * (∑ k ∈ F.PHset E, (M + 1) * F.normSq (g k)) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg hε.le hWc)
    _ = (ε * Wc) * ((M + 1) * (∑ k ∈ F.PHset E, F.normSq (g k))) := by rw [h4]
    _ = Wc * (ε * (M + 1)) * (∑ k ∈ F.PHset E, F.normSq (g k)) := by ring

/-- **The `u`-part of `Q₃⁽³⁾`**, where the pairing vector `ã_s(b_{k−s}Φ)` depends
on both indices: after the reindexing `k ↦ k − s` (into `P_H^q`) the window bound
applies to the pairing against `b_pΦ`. -/
theorem sum_u3_le (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (Φ : F.H)
    {M : ℝ} (hM : 0 ≤ M) {ε Wc Tq : ℝ} (hε : 0 < ε) (hWc : 0 ≤ Wc)
    {Sf Sq : Finset Mode} (hSf : Sf ⊆ excited Mode)
    (hTq : Tq = ∑ q ∈ Sq, F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ))
    (hg : ∀ p, T.NWindow (M + 1) (F.bOp E.alpha p Φ))
    {c : Mode → Mode → ℝ} (hc : ∀ s k : Mode, k ∈ F.PHset E → |c s k| ≤ Wc)
    (hmem : ∀ s ∈ Sf, ∀ k ∈ F.PHset E, k - s ∈ Sq) :
    (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |c s k| *
        (ε * F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ))))
      ≤ Wc * (ε * (M + 1)) * Tq := by
  have hnonzero : ∀ s ∈ excited Mode, s ≠ 0 := fun s hs => by
    rw [Work.BoseB7.excited, Finset.mem_erase] at hs
    exact hs.1
  have h1 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |c s k| *
        (ε * F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ))))
      ≤ ∑ s ∈ Sf, ∑ k ∈ F.PHset E, Wc *
          (ε * F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ))) := by
    refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun k hk => ?_
    exact mul_le_mul_of_nonneg_right (hc s k hk) (mul_nonneg hε.le (F.bp_nonneg _))
  have h2 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, Wc *
        (ε * F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ))))
      = (ε * Wc) * (∑ s ∈ Sf, ∑ k ∈ F.PHset E,
          F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ))) := by
    rw [show (∑ s ∈ Sf, ∑ k ∈ F.PHset E, Wc *
          (ε * F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ))))
        = ∑ s ∈ Sf, ∑ k ∈ F.PHset E, (ε * Wc) *
            F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ)) from by
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring]
    exact sum_const_mul_sum Sf (F.PHset E) (ε * Wc) _
  have h3A : (∑ s ∈ Sf, ∑ k ∈ F.PHset E,
        F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ)))
      ≤ ∑ s ∈ Sf, ∑ p ∈ Sq,
          F.bp (T.ta s (F.bOp E.alpha p Φ)) (T.ta s (F.bOp E.alpha p Φ)) := by
    refine Finset.sum_le_sum fun s hs => ?_
    exact sum_le_sum_of_inj (t := F.PHset E) (u := Sq) (φ := fun k => k - s)
      (f := fun p => F.bp (T.ta s (F.bOp E.alpha p Φ)) (T.ta s (F.bOp E.alpha p Φ)))
      (fun i j hij => sub_left_inj.mp hij) (fun k hk => hmem s hs k hk)
      (fun p => F.bp_nonneg _)
  have h3B : (∑ s ∈ Sf, ∑ p ∈ Sq,
        F.bp (T.ta s (F.bOp E.alpha p Φ)) (T.ta s (F.bOp E.alpha p Φ)))
      ≤ ∑ s ∈ excited Mode, ∑ p ∈ Sq,
          F.bp (T.ta s (F.bOp E.alpha p Φ)) (T.ta s (F.bOp E.alpha p Φ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hSf ?_
    intro s _ _
    exact Finset.sum_nonneg fun p _ => F.bp_nonneg _
  have h3 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E,
        F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ)))
      ≤ ∑ p ∈ Sq, ∑ s ∈ excited Mode, F.bp (T.ta s (F.bOp E.alpha p Φ))
          (T.ta s (F.bOp E.alpha p Φ)) :=
    h3A.trans (h3B.trans (le_of_eq (Finset.sum_comm)))
  have h4 : (∑ p ∈ Sq, ∑ s ∈ excited Mode, F.bp (T.ta s (F.bOp E.alpha p Φ))
        (T.ta s (F.bOp E.alpha p Φ)))
      ≤ ∑ p ∈ Sq, (M + 1) * F.normSq (F.bOp E.alpha p Φ) :=
    Finset.sum_le_sum fun p _ =>
      NWindow_ta_sum F T (by linarith) (hg p) (excited Mode) hnonzero
  have h5 : (∑ p ∈ Sq, (M + 1) * F.normSq (F.bOp E.alpha p Φ)) = (M + 1) * Tq := by
    rw [hTq, Finset.mul_sum]
    rfl
  calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |c s k| *
        (ε * F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ))))
      ≤ ∑ s ∈ Sf, ∑ k ∈ F.PHset E, Wc *
          (ε * F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ))) := h1
    _ = (ε * Wc) * (∑ s ∈ Sf, ∑ k ∈ F.PHset E,
          F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ))) := h2
    _ ≤ (ε * Wc) * (∑ p ∈ Sq, ∑ s ∈ excited Mode, F.bp (T.ta s (F.bOp E.alpha p Φ))
            (T.ta s (F.bOp E.alpha p Φ))) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg hε.le hWc)
    _ ≤ (ε * Wc) * (∑ p ∈ Sq, (M + 1) * F.normSq (F.bOp E.alpha p Φ)) :=
        mul_le_mul_of_nonneg_left h4 (mul_nonneg hε.le hWc)
    _ = (ε * Wc) * ((M + 1) * Tq) := by rw [h5]
    _ = Wc * (ε * (M + 1)) * Tq := by ring

/-- **The `v`-part of `Q₃⁽²⁾`**: the norms `‖b_{s−k}Φ‖²` reindex into `P_H^q`
for each `s`, and the number of `s` in the support of `f_L` is `Nf`. -/
theorem sum_bsub_le (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (Φ : F.H)
    {Wc Nf Tq : ℝ} (hWc : 0 ≤ Wc)
    {Sf Sq : Finset Mode} (hNf : Nf = (Sf.card : ℝ))
    (hTq : Tq = ∑ q ∈ Sq, F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ))
    {c : Mode → Mode → ℝ} (hc : ∀ s k : Mode, k ∈ F.PHset E → |c s k| ≤ Wc)
    (hmem : ∀ s ∈ Sf, ∀ k ∈ F.PHset E, s - k ∈ Sq) :
    (∑ s ∈ Sf, ∑ k ∈ F.PHset E,
        |c s k| * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ))
      ≤ Wc * Nf * Tq := by
  have h1 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E,
        |c s k| * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ))
      ≤ ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
          Wc * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ) := by
    refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun k hk => ?_
    exact mul_le_mul_of_nonneg_right (hc s k hk) (F.bp_nonneg _)
  have h2 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E,
        Wc * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ))
      = Wc * (∑ s ∈ Sf, ∑ k ∈ F.PHset E,
          F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ)) :=
    sum_const_mul_sum Sf (F.PHset E) Wc _
  have h3 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E,
        F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ)) ≤ ∑ s ∈ Sf, Tq := by
    refine Finset.sum_le_sum fun s hs => ?_
    rw [hTq]
    exact sum_le_sum_of_inj (t := F.PHset E) (u := Sq) (φ := fun k => s - k)
      (f := fun p => F.bp (F.bOp E.alpha p Φ) (F.bOp E.alpha p Φ))
      (fun i j hij => sub_right_inj.mp hij) (fun k hk => hmem s hs k hk)
      (fun p => F.bp_nonneg _)
  have h4 : (∑ s ∈ Sf, Tq) = Nf * Tq := by
    rw [hNf, Finset.sum_const, nsmul_eq_mul]
  calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E,
        |c s k| * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ))
      ≤ ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
          Wc * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ) := h1
    _ = Wc * (∑ s ∈ Sf, ∑ k ∈ F.PHset E,
          F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ)) := h2
    _ ≤ Wc * (∑ s ∈ Sf, Tq) := mul_le_mul_of_nonneg_left h3 hWc
    _ = Wc * (Nf * Tq) := by rw [h4]
    _ = Wc * Nf * Tq := by ring

/-- **The `v`-part of `Q₃⁽³⁾`**: the norms `‖b_kΦ‖²` reindex into `P_H^q`
(`P_H ⊆ P_H^q`), and the number of `s` in the support of `f_L` is `Nf`. -/
theorem sum_b_le (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (Φ : F.H)
    {Wc Nf Tq : ℝ} (hWc : 0 ≤ Wc)
    {Sf Sq : Finset Mode} (hNf : Nf = (Sf.card : ℝ))
    (hTq : Tq = ∑ q ∈ Sq, F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ))
    {c : Mode → Mode → ℝ} (hc : ∀ s k : Mode, k ∈ F.PHset E → |c s k| ≤ Wc)
    (hmem : ∀ k ∈ F.PHset E, k ∈ Sq) :
    (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |c s k| * F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ))
      ≤ Wc * Nf * Tq := by
  have h1 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |c s k| * F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ))
      ≤ ∑ s ∈ Sf, ∑ k ∈ F.PHset E, Wc * F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ) := by
    refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun k hk => ?_
    exact mul_le_mul_of_nonneg_right (hc s k hk) (F.bp_nonneg _)
  have h2 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, Wc * F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ))
      = Wc * (∑ s ∈ Sf, ∑ k ∈ F.PHset E, F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ)) :=
    sum_const_mul_sum Sf (F.PHset E) Wc _
  have h3 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ))
      ≤ ∑ s ∈ Sf, Tq := by
    refine Finset.sum_le_sum fun s _ => ?_
    rw [hTq]
    exact sum_le_sum_of_inj (t := F.PHset E) (u := Sq) (φ := fun k => k)
      (fun i j hij => hij) (fun k hk => hmem k hk) (fun p => F.bp_nonneg _)
  have h4 : (∑ s ∈ Sf, Tq) = Nf * Tq := by
    rw [hNf, Finset.sum_const, nsmul_eq_mul]
  calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |c s k| * F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ))
      ≤ ∑ s ∈ Sf, ∑ k ∈ F.PHset E, Wc * F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ) := h1
    _ = Wc * (∑ s ∈ Sf, ∑ k ∈ F.PHset E, F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ)) := h2
    _ ≤ Wc * (∑ s ∈ Sf, Tq) := mul_le_mul_of_nonneg_left h3 hWc
    _ = Wc * (Nf * Tq) := by rw [h4]
    _ = Wc * Nf * Tq := by ring

/-! ## 5. The three splitting identities -/

/-- **`Q₃⁽²⁾` as a double sum of its per-`(s,k)` quadratic forms.**  The word
identity `qw_word_eq` at `p = -k`, `q = s − k` and `σ = −α_k ccrX(s,k)`
(`α` even). -/
theorem qw_Q3twoT_eq (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (Φ : F.H)
    (hαeven : ∀ k : Mode, E.alpha (-k) = E.alpha k) :
    F.qw Φ (T.Q3twoT E) =
      ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
        ((E.z / E.ell ^ 3) * (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k))) *
          (2 * F.bp (T.ta s (F.bOp E.alpha (-k) Φ)) (F.bOp E.alpha (s - k) Φ) +
           2 * (-(E.alpha k * T.ccrX s k)) * F.bp (F.bOp E.alpha (s - k) Φ) Φ) := by
  rw [TildeData.Q3twoT]
  rw [qw_double_sum F Φ]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [qw_word_eq F T E s (-k) (s - k) (-(E.alpha (-k) * T.ccrX s (-(-k))))
      (taDag_bOpDag_swap F T E s (-k)) (bOp_ta_swap F T E s (-k)) Φ]
  rw [neg_neg, hαeven k]
  ring

/-- **`Q₃⁽³⁾` as a double sum of its per-`(s,k)` quadratic forms.**  The word
identity `qw_word_eq` at `p = k − s`, `q = k` and `σ = −α_{s−k} ccrX(s, s−k)`. -/
theorem qw_Q3threeT_eq (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (Φ : F.H)
    (hαeven : ∀ k : Mode, E.alpha (-k) = E.alpha k) :
    F.qw Φ (T.Q3threeT E) =
      ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
        ((E.z / E.ell ^ 3) * (-(E.fL s * E.W1 k * E.alpha (s - k) * E.q3Denom s k))) *
          (2 * F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (F.bOp E.alpha k Φ) +
           2 * (-(E.alpha (s - k) * T.ccrX s (s - k))) * F.bp (F.bOp E.alpha k Φ) Φ) := by
  rw [TildeData.Q3threeT]
  rw [qw_double_sum F Φ]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [qw_word_eq F T E s (k - s) k (-(E.alpha (k - s) * T.ccrX s (-(k - s))))
      (taDag_bOpDag_swap F T E s (k - s)) (bOp_ta_swap F T E s (k - s)) Φ]
  rw [show -(k - s) = s - k from by abel, show k - s = -(s - k) from by abel, hαeven (s - k)]
  ring

/-- **The kinetic reserve** in terms of the `b`-norms: the diagonal Bogoliubov
quadratic `dNumOpR E (P_H^q) = Σ_{q∈P_H^q}𝒟_qb_q†b_q` has quadratic form
`Σ_q 𝒟_q‖b_qΦ‖²`. -/
theorem qw_dNumOpR_eq (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (Φ : F.H) :
    F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)) =
      ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
        E.D q * F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ) := by
  rw [FockData.dNumOpR, FockData.regionSum, qw_finset_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [FockData.qw, FockData.bNumOp, LinearMap.comp_apply, bp_bOpDag]

/-! ## 6. The estimate -/

/-! ### 6.1 The three numeric inputs

These are the lemmas `absorb_errA`, `sum_W1alpha_le`, `q3Denom_le_four` of this
directory; they are stated here in provisional form so that the operator
argument below can be developed and checked independently. -/

theorem CtwoThree_ge_two (K₀ : ℝ) : (2 : ℝ) ≤ CtwoThree K₀ := by
  rw [CtwoThree]
  have h : (0 : ℝ) ≤ (K₀ + 1) ^ 10 := Even.pow_nonneg (by norm_num) _
  linarith


/-- **The operator core of `estQ3twoThreeA`.**  Everything after the thresholds:
the two splitting identities, the `ε`-Young bounds on the four families of
`(s,k)`-sums, the kinetic reserve and the arithmetic.  The abbreviations
(`Wc`, `Sσ`, `ε`, `Sf`, `Sq`, `Nf`, `Tq`, the coefficients `B2 B3 c2 c3` and the
vectors `u2 v2 u3 v3`) are *parameters* with their defining equations, so that
the elaboration of this argument does not carry the unfolded terms. -/
private theorem twoThree_core (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
    (Φ : F.H)
    (Wc Sσ ε Nf Tq : ℝ) (Sf Sq : Finset Mode)
    (B2 B3 c2 c3 : Mode → Mode → ℝ) (u2 v2 u3 v3 : Mode → Mode → F.H)
    (hWcdef : Wc = 256 * (|E.z| / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille)
    (hSσdef : Sσ = 64 * K₀ ^ 2 * E.lille * eta E)
    (hεdef : ε = (Real.sqrt (E.bigM + 1))⁻¹)
    (hεmul : ε * (E.bigM + 1) = Real.sqrt (E.bigM + 1))
    (hεinv : ε⁻¹ = Real.sqrt (E.bigM + 1))
    (hSfdef : Sf = (excited Mode).filter (fun s => E.fL s ≠ 0))
    (hSqdef : Sq = (excited Mode).filter (F.PHq E.KH E.aScat))
    (hNfdef : Nf = (Sf.card : ℝ))
    (hTqdef : Tq = ∑ q ∈ Sq, F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ))
    (hB2def : ∀ s k : Mode, B2 s k = (E.z / E.ell ^ 3) *
      (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k)))
    (hB3def : ∀ s k : Mode, B3 s k = (E.z / E.ell ^ 3) *
      (-(E.fL s * E.W1 k * E.alpha (s - k) * E.q3Denom s k)))
    (hc2def : ∀ s k : Mode, c2 s k = -(E.alpha k * T.ccrX s k))
    (hc3def : ∀ s k : Mode, c3 s k = -(E.alpha (s - k) * T.ccrX s (s - k)))
    (hu2def : ∀ s k : Mode, u2 s k = T.ta s (F.bOp E.alpha (-k) Φ))
    (hv2def : ∀ s k : Mode, v2 s k = F.bOp E.alpha (s - k) Φ)
    (hu3def : ∀ s k : Mode, u3 s k = T.ta s (F.bOp E.alpha (k - s) Φ))
    (hv3def : ∀ s k : Mode, v3 s k = F.bOp E.alpha k Φ)
    (hαeven : ∀ k : Mode, E.alpha (-k) = E.alpha k)
    (hPHsub : ∀ i : Mode, F.PH E.KH E.aScat i → F.PHq E.KH E.aScat i)
    (hsubPHq : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → F.PHq E.KH E.aScat (s - k))
    (hHalf : ∀ q : Mode, F.PHq E.KH E.aScat q → 1 / 2 ≤ 1 - E.alpha q ^ 2)
    (hαle : ∀ q : Mode, F.PHq E.KH E.aScat q → |E.alpha q| ≤ 64 * K₀ * E.lille)
    (hDq : ∀ q : Mode, F.PHq E.KH E.aScat q → ‖F.kmom q‖ ^ 2 / 4 ≤ E.D q)
    (hDen4 : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.q3Denom s k ≤ 4)
    (hW1le : ∀ k : Mode, |E.W1 k| ≤ K₀ * E.aScat)
    (hfL0 : ∀ s : Mode, 0 ≤ E.fL s) (hfL1 : ∀ s : Mode, E.fL s ≤ 1)
    (hccr : ∀ s q : Mode, E.fL s ≠ 0 → F.PHq E.KH E.aScat q → |T.ccrX s q| ≤ K₀ * eta E)
    (hcount : (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) ≤ K₀ * (E.Kl * E.KL) ^ 3)
    (hW1sum : ∑ k ∈ F.PHset E, |E.W1 k * E.alpha k| ≤ 2 * E.rho * E.aScat * K₀ * E.ell ^ 3)
    (hW1sum_sub : ∀ s : Mode, E.fL s ≠ 0 →
      ∑ k ∈ F.PHset E, |E.W1 k * E.alpha (s - k)| ≤ 5 * E.rho * E.aScat * K₀ * E.ell ^ 3)
    (hbOpWin : ∀ k : Mode, T.NWindow (E.bigM + 1) (F.bOp E.alpha k Φ))
    (hell : 0 < E.ell) (ha : 0 < E.aScat) (hKl : 0 < E.Kl) (hKH : 0 < E.KH)
    (hKL : 0 < E.KL)
    (hmu : 0 < E.mu)
    (hlille_nn : 0 ≤ E.lille) (hη_nn : 0 ≤ eta E) (hK0 : 0 ≤ K₀) (hrho_nn : 0 ≤ E.rho)
    (hbigM : 0 ≤ E.bigM)
    (hzabs : |E.z| = Real.sqrt (E.rho * E.ell ^ 3))
    (hAbs1 : 4 * 256 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille *
              Real.sqrt (E.bigM + 1) * (1 + K₀ * (E.Kl * E.KL) ^ 3) *
              (128 * E.KH ^ 2 * E.aScat ^ 2) ≤ (1 / CtwoThree K₀) * E.lille ^ 2)
    (hAbs2 : 4 * 256 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille *
              (64 * K₀ ^ 2 * E.lille * eta E) * K₀ * (E.Kl * E.KL) ^ 3 *
              (128 * E.KH ^ 2 * E.aScat ^ 2) ≤ (1 / CtwoThree K₀) * E.lille ^ 2)
    (hAbs3 : 4 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ * (E.Kl * E.KL) ^ 3 *
              (8 * E.rho * K₀ * E.aScat * E.ell ^ 3) * (64 * K₀ ^ 2 * E.lille * eta E)
            ≤ (1 / CtwoThree K₀) * e23A E) :
    -(CtwoThree K₀ * e23A E) * F.normSq Φ ≤
      F.qw Φ (T.Q3twoT E + T.Q3threeT E + (E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat)) := by
  classical
  have hCpos : 0 < CtwoThree K₀ := CtwoThree_pos K₀
  have hC2 : (2 : ℝ) ≤ CtwoThree K₀ := CtwoThree_ge_two K₀
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  -- ===================== basic nonnegativity =====================
  have hSf_sub : Sf ⊆ excited Mode := by
    rw [hSfdef]; exact Finset.filter_subset _ _
  have hSq_sub : Sq ⊆ excited Mode := by
    rw [hSqdef]; exact Finset.filter_subset _ _
  have hNf_nn : 0 ≤ Nf := by rw [hNfdef]; positivity
  have hTq_nn : 0 ≤ Tq := by
    rw [hTqdef]; exact Finset.sum_nonneg fun q _ => F.bp_nonneg _
  have hsqrt_nn : 0 ≤ Real.sqrt (E.bigM + 1) := Real.sqrt_nonneg _
  have hnormsq_nn : 0 ≤ F.normSq Φ := F.bp_nonneg Φ
  have hWc_nn : 0 ≤ Wc := by
    rw [hWcdef]
    have h1 : (0 : ℝ) ≤ |E.z| / E.ell ^ 3 := by positivity
    have h2 : (0 : ℝ) ≤ K₀ ^ 2 := sq_nonneg K₀
    have h3 : (0 : ℝ) ≤ E.aScat := ha.le
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) h3) hlille_nn
  have hSσ_nn : 0 ≤ Sσ := by
    rw [hSσdef]
    have h2 : (0 : ℝ) ≤ K₀ ^ 2 := sq_nonneg K₀
    have h1 : (0 : ℝ) ≤ eta E := by
      rw [eta]
      exact Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hKl.le _) hlille_nn) _
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h2) hlille_nn) h1
  -- ===================== q3Denom positivity =====================
  have hDpos : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → 0 < E.q3Denom s k := by
    intro s k hfL hk
    have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
    have h1 := hHalf k (hPHsub k hkPH)
    have h2 := hHalf (s - k) (hsubPHq s k hfL hk)
    rw [Q3Env.q3Denom]
    have h3 : 0 < (1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2) := by nlinarith
    exact one_div_pos.mpr h3
  -- ===================== coefficient bounds =====================
  have hA2le : ∀ s k : Mode, k ∈ F.PHset E → |B2 s k| ≤ Wc := by
    intro s k hk
    by_cases hfL : E.fL s = 0
    · rw [hB2def]
      simp only [hfL, mul_zero, neg_zero, zero_mul, abs_zero]
      exact hWc_nn
    · have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
      have hkPHq : F.PHq E.KH E.aScat k := hPHsub k hkPH
      have hB : |E.fL s| * |E.W1 k| * |E.alpha k| * E.q3Denom s k ≤
          256 * K₀ ^ 2 * E.aScat * E.lille := by
        have hf1 : |E.fL s| ≤ 1 := by
          rw [abs_of_nonneg (hfL0 s)]; exact hfL1 s
        have hw : |E.W1 k| ≤ K₀ * E.aScat := hW1le k
        have hal : |E.alpha k| ≤ 64 * K₀ * E.lille := hαle k hkPHq
        have hd : E.q3Denom s k ≤ 4 := hDen4 s k hfL hk
        have hd0 : 0 ≤ E.q3Denom s k := (hDpos s k hfL hk).le
        have h01 : (0 : ℝ) ≤ |E.fL s| * |E.W1 k| := by positivity
        have h02 : (0 : ℝ) ≤ |E.alpha k| := abs_nonneg _
        have h03 : (0 : ℝ) ≤ K₀ * E.aScat := mul_nonneg hK0 ha.le
        have h04 : (0 : ℝ) ≤ K₀ ^ 2 * E.aScat * E.lille :=
          mul_nonneg (mul_nonneg (sq_nonneg K₀) ha.le) hlille_nn
        have hstep1 : |E.fL s| * |E.W1 k| ≤ 1 * (K₀ * E.aScat) :=
          mul_le_mul hf1 hw (abs_nonneg _) (by norm_num)
        have hstep2 : |E.fL s| * |E.W1 k| * |E.alpha k| ≤
            (1 * (K₀ * E.aScat)) * (64 * K₀ * E.lille) :=
          mul_le_mul hstep1 hal h02 (mul_nonneg (by norm_num) h03)
        calc |E.fL s| * |E.W1 k| * |E.alpha k| * E.q3Denom s k
            ≤ ((1 * (K₀ * E.aScat)) * (64 * K₀ * E.lille)) * 4 :=
              mul_le_mul hstep2 hd hd0 (by positivity)
          _ = 256 * K₀ ^ 2 * E.aScat * E.lille := by ring
      rw [hB2def]
      have habs : |E.z / E.ell ^ 3 * (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k))|
          = |E.z| / E.ell ^ 3 * (|E.fL s| * |E.W1 k| * |E.alpha k| * E.q3Denom s k) := by
        simp only [abs_mul, abs_neg, abs_div, abs_of_pos (pow_pos hell 3),
          abs_of_nonneg (hDpos s k hfL hk).le]
      rw [habs]
      have hz3 : 0 ≤ |E.z| / E.ell ^ 3 := by positivity
      calc |E.z| / E.ell ^ 3 * (|E.fL s| * |E.W1 k| * |E.alpha k| * E.q3Denom s k)
          ≤ |E.z| / E.ell ^ 3 * (256 * K₀ ^ 2 * E.aScat * E.lille) :=
            mul_le_mul_of_nonneg_left hB hz3
        _ = Wc := by rw [hWcdef]; ring
  have hA3le : ∀ s k : Mode, k ∈ F.PHset E → |B3 s k| ≤ Wc := by
    intro s k hk
    by_cases hfL : E.fL s = 0
    · rw [hB3def]
      simp only [hfL, mul_zero, neg_zero, zero_mul, abs_zero]
      exact hWc_nn
    · have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
      have hkPHq : F.PHq E.KH E.aScat k := hPHsub k hkPH
      have hskPHq : F.PHq E.KH E.aScat (s - k) := hsubPHq s k hfL hk
      have hB : |E.fL s| * |E.W1 k| * |E.alpha (s - k)| * E.q3Denom s k ≤
          256 * K₀ ^ 2 * E.aScat * E.lille := by
        have hf1 : |E.fL s| ≤ 1 := by
          rw [abs_of_nonneg (hfL0 s)]; exact hfL1 s
        have hw : |E.W1 k| ≤ K₀ * E.aScat := hW1le k
        have hal : |E.alpha (s - k)| ≤ 64 * K₀ * E.lille := hαle (s - k) hskPHq
        have hd : E.q3Denom s k ≤ 4 := hDen4 s k hfL hk
        have hd0 : 0 ≤ E.q3Denom s k := (hDpos s k hfL hk).le
        have h03 : (0 : ℝ) ≤ K₀ * E.aScat := mul_nonneg hK0 ha.le
        have hstep1 : |E.fL s| * |E.W1 k| ≤ 1 * (K₀ * E.aScat) :=
          mul_le_mul hf1 hw (abs_nonneg _) (by norm_num)
        have hstep2 : |E.fL s| * |E.W1 k| * |E.alpha (s - k)| ≤
            (1 * (K₀ * E.aScat)) * (64 * K₀ * E.lille) :=
          mul_le_mul hstep1 hal (abs_nonneg _) (mul_nonneg (by norm_num) h03)
        calc |E.fL s| * |E.W1 k| * |E.alpha (s - k)| * E.q3Denom s k
            ≤ ((1 * (K₀ * E.aScat)) * (64 * K₀ * E.lille)) * 4 :=
              mul_le_mul hstep2 hd hd0 (by positivity)
          _ = 256 * K₀ ^ 2 * E.aScat * E.lille := by ring
      rw [hB3def]
      have habs : |E.z / E.ell ^ 3 * (-(E.fL s * E.W1 k * E.alpha (s - k) * E.q3Denom s k))|
          = |E.z| / E.ell ^ 3 *
            (|E.fL s| * |E.W1 k| * |E.alpha (s - k)| * E.q3Denom s k) := by
        simp only [abs_mul, abs_neg, abs_div, abs_of_pos (pow_pos hell 3),
          abs_of_nonneg (hDpos s k hfL hk).le]
      rw [habs]
      have hz3 : 0 ≤ |E.z| / E.ell ^ 3 := by positivity
      calc |E.z| / E.ell ^ 3 * (|E.fL s| * |E.W1 k| * |E.alpha (s - k)| * E.q3Denom s k)
          ≤ |E.z| / E.ell ^ 3 * (256 * K₀ ^ 2 * E.aScat * E.lille) :=
            mul_le_mul_of_nonneg_left hB hz3
        _ = Wc := by rw [hWcdef]; ring
  have hc2le : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → |c2 s k| ≤ Sσ := by
    intro s k hfL hk
    have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
    have hkPHq : F.PHq E.KH E.aScat k := hPHsub k hkPH
    have hal : |E.alpha k| ≤ 64 * K₀ * E.lille := hαle k hkPHq
    have hcc : |T.ccrX s k| ≤ K₀ * eta E := hccr s k hfL hkPHq
    rw [hc2def]
    rw [abs_neg, abs_mul]
    have h1 : |E.alpha k| * |T.ccrX s k| ≤ (64 * K₀ * E.lille) * (K₀ * eta E) :=
      mul_le_mul hal hcc (abs_nonneg _) (by positivity)
    calc |E.alpha k| * |T.ccrX s k| ≤ (64 * K₀ * E.lille) * (K₀ * eta E) := h1
      _ = Sσ := by rw [hSσdef]; ring
  have hc3le : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → |c3 s k| ≤ Sσ := by
    intro s k hfL hk
    have hskPHq : F.PHq E.KH E.aScat (s - k) := hsubPHq s k hfL hk
    have hal : |E.alpha (s - k)| ≤ 64 * K₀ * E.lille := hαle (s - k) hskPHq
    have hcc : |T.ccrX s (s - k)| ≤ K₀ * eta E := hccr s (s - k) hfL hskPHq
    rw [hc3def]
    rw [abs_neg, abs_mul]
    have h1 : |E.alpha (s - k)| * |T.ccrX s (s - k)| ≤ (64 * K₀ * E.lille) * (K₀ * eta E) :=
      mul_le_mul hal hcc (abs_nonneg _) (by positivity)
    calc |E.alpha (s - k)| * |T.ccrX s (s - k)| ≤ (64 * K₀ * E.lille) * (K₀ * eta E) := h1
      _ = Sσ := by rw [hSσdef]; ring
  -- ===================== the two word identities =====================
  have hQ2 : F.qw Φ (T.Q3twoT E) = ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
      B2 s k * (2 * F.bp (u2 s k) (v2 s k) + 2 * c2 s k * F.bp (v2 s k) Φ) := by
    rw [qw_Q3twoT_eq F T E Φ hαeven]
    simp only [hB2def, hc2def, hu2def, hv2def]
    refine (Finset.sum_subset (by rw [hSfdef]; exact Finset.filter_subset _ _) ?_).symm
    intro s hs hns
    have hfL : E.fL s = 0 := by
      by_contra h
      exact hns (by rw [hSfdef]; exact Finset.mem_filter.mpr ⟨hs, h⟩)
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [hfL, mul_zero, neg_zero, zero_mul]
  have hQ3 : F.qw Φ (T.Q3threeT E) = ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
      B3 s k * (2 * F.bp (u3 s k) (v3 s k) + 2 * c3 s k * F.bp (v3 s k) Φ) := by
    rw [qw_Q3threeT_eq F T E Φ hαeven]
    simp only [hB3def, hc3def, hu3def, hv3def]
    refine (Finset.sum_subset (by rw [hSfdef]; exact Finset.filter_subset _ _) ?_).symm
    intro s hs hns
    have hfL : E.fL s = 0 := by
      by_contra h
      exact hns (by rw [hSfdef]; exact Finset.mem_filter.mpr ⟨hs, h⟩)
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [hfL, mul_zero, neg_zero, zero_mul]
  -- ===================== the per-word lower bounds =====================
  have hLB2 : -(∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| *
        (ε * F.bp (u2 s k) (u2 s k) + ε⁻¹ * F.bp (v2 s k) (v2 s k) +
          |c2 s k| * (F.bp (v2 s k) (v2 s k) + F.normSq Φ))) ≤ F.qw Φ (T.Q3twoT E) := by
    rw [hQ2, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    exact word_bound F Φ (u2 s k) (v2 s k) (B2 s k) (c2 s k) ε hεpos
  have hLB3 : -(∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| *
        (ε * F.bp (u3 s k) (u3 s k) + ε⁻¹ * F.bp (v3 s k) (v3 s k) +
          |c3 s k| * (F.bp (v3 s k) (v3 s k) + F.normSq Φ))) ≤ F.qw Φ (T.Q3threeT E) := by
    rw [hQ3, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    exact word_bound F Φ (u3 s k) (v3 s k) (B3 s k) (c3 s k) ε hεpos
  -- ===================== the region memberships =====================
  have hSq_mem : ∀ x : Mode, x ∈ Sq ↔ x ∈ excited Mode ∧ F.PHq E.KH E.aScat x := by
    intro x
    rw [hSqdef, Finset.mem_filter]
  have hSf_mem : ∀ s : Mode, s ∈ Sf ↔ s ∈ excited Mode ∧ E.fL s ≠ 0 := by
    intro s
    rw [hSfdef, Finset.mem_filter]
  have hmem_ph : ∀ k ∈ F.PHset E, k ∈ Sq := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    exact hSq_mem k |>.mpr ⟨hk'.1, hPHsub k hk'.2⟩
  have hmem_neg : ∀ k ∈ F.PHset E, -k ∈ Sq := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    refine hSq_mem (-k) |>.mpr ⟨?_, ?_⟩
    · rw [Work.BoseB7.excited, Finset.mem_erase]
      exact ⟨neg_ne_zero.mpr (Finset.mem_erase.mp hk'.1).1, Finset.mem_univ _⟩
    · have h2 : F.PHq E.KH E.aScat k := hPHsub k hk'.2
      simp only [FockData.PHq] at h2 ⊢
      rw [F.kmom_neg k, norm_neg]
      exact h2
  have hmem_sub : ∀ s ∈ Sf, ∀ k ∈ F.PHset E, s - k ∈ Sq := by
    intro s hs k hk
    have hs' := (hSf_mem s).mp hs
    have h1 := hsubPHq s k hs'.2 hk
    refine hSq_mem (s - k) |>.mpr ⟨?_, h1⟩
    rw [Work.BoseB7.excited, Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h0
    have h2 : F.kmom (s - k) = 0 := by rw [h0, kmom_zero]
    have h3 : 0 < ‖F.kmom (s - k)‖ := by
      have h4 : 0 < 1 / (4 * E.KH * E.aScat) := by positivity
      simp only [FockData.PHq] at h1
      linarith [h1]
    rw [h2, norm_zero] at h3
    exact absurd h3 (lt_irrefl 0)
  have hmem_ksub : ∀ s ∈ Sf, ∀ k ∈ F.PHset E, k - s ∈ Sq := by
    intro s hs k hk
    have hs' := (hSf_mem s).mp hs
    have h1 := hsubPHq s k hs'.2 hk
    have h2 : F.PHq E.KH E.aScat (k - s) := by
      simp only [FockData.PHq] at h1 ⊢
      have he : F.kmom (k - s) = -(F.kmom (s - k)) := by
        rw [show k - s = -(s - k) from by abel, F.kmom_neg]
      rw [he, norm_neg]
      exact h1
    refine hSq_mem (k - s) |>.mpr ⟨?_, h2⟩
    rw [Work.BoseB7.excited, Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h0
    have h3 : F.kmom (k - s) = 0 := by rw [h0, kmom_zero]
    have h4 : 0 < ‖F.kmom (k - s)‖ := by
      have h5 : 0 < 1 / (4 * E.KH * E.aScat) := by positivity
      simp only [FockData.PHq] at h2
      linarith [h2]
    rw [h3, norm_zero] at h4
    exact absurd h4 (lt_irrefl 0)
  -- ===================== the coefficient sum =====================
  have hcoefsum : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k|)
      ≤ Nf * (4 * (|E.z| / E.ell ^ 3) * (2 * E.rho * E.aScat * K₀ * E.ell ^ 3)) := by
    have h1 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k|)
        ≤ ∑ s ∈ Sf, ∑ k ∈ F.PHset E, 4 * (|E.z| / E.ell ^ 3) * |E.W1 k * E.alpha k| := by
      refine Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun k hk => ?_
      have hfL : E.fL s ≠ 0 := (hSf_mem s).mp hs |>.2
      have h3 : |B2 s k| ≤ 4 * (|E.z| / E.ell ^ 3) * |E.W1 k * E.alpha k| := by
        rw [hB2def]
        have habs : |E.z / E.ell ^ 3 * (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k))|
            = |E.z| / E.ell ^ 3 * (|E.fL s| * |E.W1 k| * |E.alpha k| * E.q3Denom s k) := by
          simp only [abs_mul, abs_neg, abs_div, abs_of_pos (pow_pos hell 3),
            abs_of_nonneg (hDpos s k hfL hk).le]
        rw [habs]
        have hf1 : |E.fL s| ≤ 1 := by
          rw [abs_of_nonneg (hfL0 s)]; exact hfL1 s
        have hd : E.q3Denom s k ≤ 4 := hDen4 s k hfL hk
        have hd0 : 0 ≤ E.q3Denom s k := (hDpos s k hfL hk).le
        have hz3 : 0 ≤ |E.z| / E.ell ^ 3 := by positivity
        calc |E.z| / E.ell ^ 3 * (|E.fL s| * |E.W1 k| * |E.alpha k| * E.q3Denom s k)
            ≤ |E.z| / E.ell ^ 3 * (1 * |E.W1 k * E.alpha k| * 4) := by
              refine mul_le_mul_of_nonneg_left ?_ hz3
              have h4 : |E.fL s| * (|E.W1 k| * |E.alpha k|) ≤ 1 * (|E.W1 k| * |E.alpha k|) :=
                mul_le_mul_of_nonneg_right hf1 (by positivity)
              nlinarith [h4, hd, hd0, abs_nonneg (E.W1 k * E.alpha k),
                abs_mul (E.W1 k) (E.alpha k)]
          _ = 4 * (|E.z| / E.ell ^ 3) * |E.W1 k * E.alpha k| := by ring
      exact h3
    have h2 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, 4 * (|E.z| / E.ell ^ 3) * |E.W1 k * E.alpha k|)
        = Nf * (4 * (|E.z| / E.ell ^ 3) * (∑ k ∈ F.PHset E, |E.W1 k * E.alpha k|)) := by
      rw [sum_const_mul_sum]
      rw [Finset.sum_const, nsmul_eq_mul, hNfdef]
      ring
    have h3 : (∑ k ∈ F.PHset E, |E.W1 k * E.alpha k|) ≤ 2 * E.rho * E.aScat * K₀ * E.ell ^ 3 :=
      hW1sum
    calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k|)
        ≤ ∑ s ∈ Sf, ∑ k ∈ F.PHset E, 4 * (|E.z| / E.ell ^ 3) * |E.W1 k * E.alpha k| := h1
      _ = Nf * (4 * (|E.z| / E.ell ^ 3) * (∑ k ∈ F.PHset E, |E.W1 k * E.alpha k|)) := h2
      _ ≤ Nf * (4 * (|E.z| / E.ell ^ 3) * (2 * E.rho * E.aScat * K₀ * E.ell ^ 3)) := by
          refine mul_le_mul_of_nonneg_left ?_ hNf_nn
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
  -- ===================== the eight sum bounds =====================
  have hu2 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε * F.bp (u2 s k) (u2 s k)))
      ≤ Wc * (ε * (E.bigM + 1)) * Tq := by
    have hR : (∑ k ∈ F.PHset E,
          F.bp (F.bOp E.alpha (-k) Φ) (F.bOp E.alpha (-k) Φ)) ≤ Tq := by
      rw [hTqdef]
      exact sum_le_sum_of_inj (t := F.PHset E) (u := Sq) (φ := fun k => -k)
        (f := fun p => F.bp (F.bOp E.alpha p Φ) (F.bOp E.alpha p Φ))
        (fun i j hij => neg_inj.mp hij) (fun k hk => hmem_neg k hk)
        (fun p => F.bp_nonneg _)
    have h := sum_u_le F T E (M := E.bigM) (by linarith) (ε := ε) (Wc := Wc) hεpos hWc_nn
      (c := B2) (fun s k hk => hA2le s k hk)
      (g := fun k => F.bOp E.alpha (-k) Φ) (fun k => hbOpWin (-k))
    calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε * F.bp (u2 s k) (u2 s k)))
        = ∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| *
            (ε * F.bp (T.ta s (F.bOp E.alpha (-k) Φ)) (T.ta s (F.bOp E.alpha (-k) Φ))) := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
          rw [hu2def]
      _ ≤ ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, |B2 s k| *
            (ε * F.bp (T.ta s (F.bOp E.alpha (-k) Φ)) (T.ta s (F.bOp E.alpha (-k) Φ))) :=
          Finset.sum_le_sum_of_subset_of_nonneg hSf_sub (fun s _ _ =>
            Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _)
              (mul_nonneg hεpos.le (F.bp_nonneg _)))
      _ ≤ Wc * (ε * (E.bigM + 1)) *
            (∑ k ∈ F.PHset E, F.bp (F.bOp E.alpha (-k) Φ) (F.bOp E.alpha (-k) Φ)) := h
      _ ≤ Wc * (ε * (E.bigM + 1)) * Tq :=
          mul_le_mul_of_nonneg_left hR (by positivity)
  have hu3 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (ε * F.bp (u3 s k) (u3 s k)))
      ≤ Wc * (ε * (E.bigM + 1)) * Tq := by
    have h := sum_u3_le F T E Φ (M := E.bigM) (by linarith) (ε := ε) (Wc := Wc) (Tq := Tq)
      hεpos hWc_nn (Sf := Sf) (Sq := Sq) hSf_sub hTqdef (fun p => hbOpWin p)
      (c := B3) (fun s k hk => hA3le s k hk) hmem_ksub
    simpa only [hu3def] using h
  have hv2 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε⁻¹ * F.bp (v2 s k) (v2 s k)))
      ≤ Wc * (ε⁻¹ * Nf) * Tq := by
    have h := sum_bsub_le F T E Φ (Wc := Wc) (Nf := Nf) (Tq := Tq) hWc_nn
      (Sf := Sf) (Sq := Sq) hNfdef hTqdef (c := B2)
      (fun s k hk => hA2le s k hk) hmem_sub
    calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε⁻¹ * F.bp (v2 s k) (v2 s k)))
        = ∑ s ∈ Sf, ∑ k ∈ F.PHset E, ε⁻¹ * (|B2 s k| * F.bp (v2 s k) (v2 s k)) := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring
      _ = ε⁻¹ * ∑ s ∈ Sf, ∑ k ∈ F.PHset E, (|B2 s k| * F.bp (v2 s k) (v2 s k)) :=
          sum_const_mul_sum Sf (F.PHset E) ε⁻¹ _
      _ = ε⁻¹ * ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
            (|B2 s k| * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ)) := by
          simp only [hv2def]
      _ ≤ ε⁻¹ * (Wc * Nf * Tq) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = Wc * (ε⁻¹ * Nf) * Tq := by ring
  have hv3 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (ε⁻¹ * F.bp (v3 s k) (v3 s k)))
      ≤ Wc * (ε⁻¹ * Nf) * Tq := by
    have h := sum_b_le F T E Φ (Wc := Wc) (Nf := Nf) (Tq := Tq) hWc_nn
      (Sf := Sf) (Sq := Sq) hNfdef hTqdef (c := B3)
      (fun s k hk => hA3le s k hk) hmem_ph
    calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (ε⁻¹ * F.bp (v3 s k) (v3 s k)))
        = ∑ s ∈ Sf, ∑ k ∈ F.PHset E, ε⁻¹ * (|B3 s k| * F.bp (v3 s k) (v3 s k)) := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring
      _ = ε⁻¹ * ∑ s ∈ Sf, ∑ k ∈ F.PHset E, (|B3 s k| * F.bp (v3 s k) (v3 s k)) :=
          sum_const_mul_sum Sf (F.PHset E) ε⁻¹ _
      _ = ε⁻¹ * ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
            (|B3 s k| * F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ)) := by
          simp only [hv3def]
      _ ≤ ε⁻¹ * (Wc * Nf * Tq) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = Wc * (ε⁻¹ * Nf) * Tq := by ring
  -- the σ-weighted norms
  have hσ2a : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.bp (v2 s k) (v2 s k)))
      ≤ Wc * Sσ * Nf * Tq := by
    have hc : ∀ s k : Mode, k ∈ F.PHset E → |B2 s k * c2 s k| ≤ Wc * Sσ := by
      intro s k hk
      rw [abs_mul]
      by_cases hfL : E.fL s = 0
      · rw [hB2def]
        simp only [hfL, mul_zero, neg_zero, zero_mul, abs_zero]
        exact mul_nonneg hWc_nn hSσ_nn
      · exact mul_le_mul (hA2le s k hk) (hc2le s k hfL hk) (abs_nonneg _) hWc_nn
    have h := sum_bsub_le F T E Φ (Wc := Wc * Sσ) (Nf := Nf) (Tq := Tq)
      (mul_nonneg hWc_nn hSσ_nn) (Sf := Sf) (Sq := Sq) hNfdef hTqdef
      (c := fun s k => B2 s k * c2 s k) hc hmem_sub
    calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.bp (v2 s k) (v2 s k)))
        = ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
            |B2 s k * c2 s k| * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ) := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
          rw [abs_mul_abs_mul, hv2def]
      _ ≤ (Wc * Sσ) * Nf * Tq := h
      _ = Wc * Sσ * Nf * Tq := by ring
  have hσ3a : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.bp (v3 s k) (v3 s k)))
      ≤ Wc * Sσ * Nf * Tq := by
    have hc : ∀ s k : Mode, k ∈ F.PHset E → |B3 s k * c3 s k| ≤ Wc * Sσ := by
      intro s k hk
      rw [abs_mul]
      by_cases hfL : E.fL s = 0
      · rw [hB3def]
        simp only [hfL, mul_zero, neg_zero, zero_mul, abs_zero]
        exact mul_nonneg hWc_nn hSσ_nn
      · exact mul_le_mul (hA3le s k hk) (hc3le s k hfL hk) (abs_nonneg _) hWc_nn
    have h := sum_b_le F T E Φ (Wc := Wc * Sσ) (Nf := Nf) (Tq := Tq)
      (mul_nonneg hWc_nn hSσ_nn) (Sf := Sf) (Sq := Sq) hNfdef hTqdef
      (c := fun s k => B3 s k * c3 s k) hc hmem_ph
    calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.bp (v3 s k) (v3 s k)))
        = ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
            |B3 s k * c3 s k| * F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ) := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
          rw [abs_mul_abs_mul, hv3def]
      _ ≤ (Wc * Sσ) * Nf * Tq := h
      _ = Wc * Sσ * Nf * Tq := by ring
  -- the constants
  have hσ2b : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.normSq Φ))
      ≤ (8 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ := by
    have h1 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.normSq Φ))
        = (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * |c2 s k|) * F.normSq Φ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by ring
    have h2 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * |c2 s k|)
        ≤ Sσ * (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k|) := by
      have h3 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * |c2 s k|)
          ≤ ∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * Sσ := by
        refine Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun k hk => ?_
        have hfL : E.fL s ≠ 0 := (hSf_mem s).mp hs |>.2
        exact mul_le_mul_of_nonneg_left (hc2le s k hfL hk) (abs_nonneg _)
      refine h3.trans ?_
      rw [show (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * Sσ)
          = Sσ * ∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| from by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => by ring]
    calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.normSq Φ))
        = (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * |c2 s k|) * F.normSq Φ := h1
      _ ≤ (Sσ * (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k|)) * F.normSq Φ :=
          mul_le_mul_of_nonneg_right h2 hnormsq_nn
      _ ≤ (Sσ * (Nf * (4 * (|E.z| / E.ell ^ 3) * (2 * E.rho * E.aScat * K₀ * E.ell ^ 3)))) *
            F.normSq Φ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoefsum hSσ_nn) hnormsq_nn
      _ = (8 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) *
            F.normSq Φ := by ring
  have hσ3b : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.normSq Φ))
      ≤ (20 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ := by
    have h1 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.normSq Φ))
        = (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * |c3 s k|) * F.normSq Φ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by ring
    have h2 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * |c3 s k|)
        ≤ Sσ * (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k|) := by
      have h3 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * |c3 s k|)
          ≤ ∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * Sσ := by
        refine Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun k hk => ?_
        have hfL : E.fL s ≠ 0 := (hSf_mem s).mp hs |>.2
        exact mul_le_mul_of_nonneg_left (hc3le s k hfL hk) (abs_nonneg _)
      refine h3.trans ?_
      rw [show (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * Sσ)
          = Sσ * ∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| from by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => by ring]
    have hcoefsum3 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k|)
        ≤ Nf * (4 * (|E.z| / E.ell ^ 3) * (5 * E.rho * E.aScat * K₀ * E.ell ^ 3)) := by
      have h3 : ∀ s ∈ Sf, (∑ k ∈ F.PHset E, |B3 s k|)
          ≤ 4 * (|E.z| / E.ell ^ 3) * (5 * E.rho * E.aScat * K₀ * E.ell ^ 3) := by
        intro s hs
        have hfL : E.fL s ≠ 0 := (hSf_mem s).mp hs |>.2
        have h4 : (∑ k ∈ F.PHset E, |B3 s k|)
            ≤ ∑ k ∈ F.PHset E, 4 * (|E.z| / E.ell ^ 3) * |E.W1 k * E.alpha (s - k)| := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [hB3def]
          have habs : |E.z / E.ell ^ 3 *
                (-(E.fL s * E.W1 k * E.alpha (s - k) * E.q3Denom s k))|
              = |E.z| / E.ell ^ 3 *
                (|E.fL s| * |E.W1 k| * |E.alpha (s - k)| * E.q3Denom s k) := by
            simp only [abs_mul, abs_neg, abs_div, abs_of_pos (pow_pos hell 3),
              abs_of_nonneg (hDpos s k hfL hk).le]
          rw [habs]
          have hf1 : |E.fL s| ≤ 1 := by
            rw [abs_of_nonneg (hfL0 s)]; exact hfL1 s
          have hd : E.q3Denom s k ≤ 4 := hDen4 s k hfL hk
          have hd0 : 0 ≤ E.q3Denom s k := (hDpos s k hfL hk).le
          have hz3 : 0 ≤ |E.z| / E.ell ^ 3 := by positivity
          calc |E.z| / E.ell ^ 3 * (|E.fL s| * |E.W1 k| * |E.alpha (s - k)| * E.q3Denom s k)
              ≤ |E.z| / E.ell ^ 3 * (1 * (|E.W1 k| * |E.alpha (s - k)|) * 4) := by
                refine mul_le_mul_of_nonneg_left ?_ hz3
                have h5 : |E.fL s| * (|E.W1 k| * |E.alpha (s - k)|) ≤
                    1 * (|E.W1 k| * |E.alpha (s - k)|) :=
                  mul_le_mul_of_nonneg_right hf1 (by positivity)
                have h6 : 0 ≤ 1 * (|E.W1 k| * |E.alpha (s - k)|) := by positivity
                have h7 : |E.fL s| * (|E.W1 k| * |E.alpha (s - k)|) * E.q3Denom s k
                    ≤ (1 * (|E.W1 k| * |E.alpha (s - k)|)) * 4 :=
                  mul_le_mul h5 hd hd0 h6
                nlinarith [h7]
            _ = 4 * (|E.z| / E.ell ^ 3) * |E.W1 k * E.alpha (s - k)| := by
                rw [abs_mul]; ring
        refine h4.trans ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hW1sum_sub s hfL) (by positivity)
      have h2 : (∑ s ∈ Sf, 4 * (|E.z| / E.ell ^ 3) * (5 * E.rho * E.aScat * K₀ * E.ell ^ 3))
          = Nf * (4 * (|E.z| / E.ell ^ 3) * (5 * E.rho * E.aScat * K₀ * E.ell ^ 3)) := by
        rw [Finset.sum_const, nsmul_eq_mul, hNfdef]
      calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k|)
          ≤ ∑ s ∈ Sf, 4 * (|E.z| / E.ell ^ 3) * (5 * E.rho * E.aScat * K₀ * E.ell ^ 3) :=
            Finset.sum_le_sum h3
        _ = Nf * (4 * (|E.z| / E.ell ^ 3) * (5 * E.rho * E.aScat * K₀ * E.ell ^ 3)) := h2
    calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.normSq Φ))
        = (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * |c3 s k|) * F.normSq Φ := h1
      _ ≤ (Sσ * (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k|)) * F.normSq Φ :=
          mul_le_mul_of_nonneg_right h2 hnormsq_nn
      _ ≤ (Sσ * (Nf * (4 * (|E.z| / E.ell ^ 3) * (5 * E.rho * E.aScat * K₀ * E.ell ^ 3)))) *
            F.normSq Φ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoefsum3 hSσ_nn) hnormsq_nn
      _ = (20 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) *
            F.normSq Φ := by ring
  -- ===================== the reserve =====================
  have hres : (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq
      ≤ F.qw Φ ((E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat)) := by
    have hDlb : ∀ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
        1 / (64 * E.KH ^ 2 * E.aScat ^ 2) ≤ E.D q := by
      intro q hq
      have hqPH : F.PHq E.KH E.aScat q := (Finset.mem_filter.mp hq).2
      have h1 : 1 / (4 * E.KH * E.aScat) ≤ ‖F.kmom q‖ := hqPH
      have h2 : ‖F.kmom q‖ ^ 2 / 4 ≤ E.D q := hDq q hqPH
      have h3 : 1 / (64 * E.KH ^ 2 * E.aScat ^ 2) ≤ ‖F.kmom q‖ ^ 2 / 4 := by
        have h4 : 1 / (64 * E.KH ^ 2 * E.aScat ^ 2)
            = (1 / (4 * E.KH * E.aScat)) ^ 2 * (4 : ℝ)⁻¹ := by
          field_simp
          ring
        rw [h4]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) h1 2) (by norm_num)
      exact h3.trans h2
    rw [qw_smul', qw_dNumOpR_eq F T E Φ, hTqdef, hSqdef]
    have hstep : (∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
          (1 / (64 * E.KH ^ 2 * E.aScat ^ 2)) * F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ))
        ≤ ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
          E.D q * F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ) := by
      refine Finset.sum_le_sum fun q hq => ?_
      exact mul_le_mul_of_nonneg_right (hDlb q hq) (F.bp_nonneg _)
    calc (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) *
          (∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
            F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ))
        = (E.lille ^ 2 / 2) * ((1 / (64 * E.KH ^ 2 * E.aScat ^ 2)) *
            (∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
              F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ))) := by ring
      _ = (E.lille ^ 2 / 2) * (∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
            (1 / (64 * E.KH ^ 2 * E.aScat ^ 2)) *
              F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ)) := by
          rw [Finset.mul_sum]
      _ ≤ (E.lille ^ 2 / 2) * (∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
            E.D q * F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
  -- ===================== the three numeric conditions =====================
  have he23nn : 0 ≤ e23A E := by
    rw [e23A]
    refine mul_nonneg (mul_nonneg (by positivity) (by positivity)) ?_
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_
    · exact Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hKl.le _) hlille_nn) _
    · positivity
    · exact Real.rpow_nonneg hKl.le _
    · exact Real.rpow_nonneg (mul_nonneg hmu.le (pow_nonneg ha.le 3)) _
  have hIcost : 2 * Wc * Real.sqrt (E.bigM + 1) * (1 + Nf) * Tq
      ≤ (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq := by
    have hNf_le : Nf ≤ K₀ * (E.Kl * E.KL) ^ 3 := by
      rw [hNfdef]
      have := hcount
      rwa [hSfdef]
    have hWcz : Wc = 256 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille := by
      rw [hWcdef, hzabs]
    have hpos : 0 < 128 * E.KH ^ 2 * E.aScat ^ 2 := by positivity
    have h1 : 4 * 256 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille *
          Real.sqrt (E.bigM + 1) * (1 + K₀ * (E.Kl * E.KL) ^ 3) *
          (128 * E.KH ^ 2 * E.aScat ^ 2)
        ≤ (1 / CtwoThree K₀) * E.lille ^ 2 := hAbs1
    have h2 : 2 * Wc * Real.sqrt (E.bigM + 1) * (1 + Nf)
        ≤ (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) := by
      rw [show (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2))
          = ((1 / CtwoThree K₀) * E.lille ^ 2) / (128 * E.KH ^ 2 * E.aScat ^ 2) from by ring]
      rw [le_div_iff₀ hpos]
      rw [hWcz]
      have hNf2 : 2 * (1 + Nf) ≤ 4 * (1 + K₀ * (E.Kl * E.KL) ^ 3) := by linarith
      have hA0 : 0 ≤ (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille *
          Real.sqrt (E.bigM + 1) * (128 * E.KH ^ 2 * E.aScat ^ 2) := by positivity
      nlinarith [h1, hNf2, hA0, hlille_nn, hNf_nn, hsqrt_nn, hWc_nn]
    calc 2 * Wc * Real.sqrt (E.bigM + 1) * (1 + Nf) * Tq
        = (2 * Wc * Real.sqrt (E.bigM + 1) * (1 + Nf)) * Tq := by ring
      _ ≤ ((1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2))) * Tq :=
          mul_le_mul_of_nonneg_right h2 hTq_nn
      _ = (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq := by ring
  have hScost : 2 * Wc * Sσ * Nf * Tq
      ≤ (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq := by
    have hNf_le : Nf ≤ K₀ * (E.Kl * E.KL) ^ 3 := by
      rw [hNfdef]
      have := hcount
      rwa [hSfdef]
    have hWcz : Wc = 256 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille := by
      rw [hWcdef, hzabs]
    have hSσz : Sσ = 64 * K₀ ^ 2 * E.lille * eta E := by rw [hSσdef]
    have hpos : 0 < 128 * E.KH ^ 2 * E.aScat ^ 2 := by positivity
    have h1 : 4 * 256 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille *
          (64 * K₀ ^ 2 * E.lille * eta E) * K₀ * (E.Kl * E.KL) ^ 3 *
          (128 * E.KH ^ 2 * E.aScat ^ 2)
        ≤ (1 / CtwoThree K₀) * E.lille ^ 2 := hAbs2
    have h2 : 2 * Wc * Sσ * Nf
        ≤ (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) := by
      rw [show (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2))
          = ((1 / CtwoThree K₀) * E.lille ^ 2) / (128 * E.KH ^ 2 * E.aScat ^ 2) from by ring]
      rw [le_div_iff₀ hpos]
      rw [hWcz, hSσz]
      have hNf2 : 2 * Nf ≤ 4 * (K₀ * (E.Kl * E.KL) ^ 3) := by linarith
      have hA0 : 0 ≤ (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille *
          (64 * K₀ ^ 2 * E.lille * eta E) * (128 * E.KH ^ 2 * E.aScat ^ 2) := by positivity
      nlinarith [h1, hNf2, hA0, hlille_nn, hNf_nn, hη_nn, hK0]
    calc 2 * Wc * Sσ * Nf * Tq = (2 * Wc * Sσ * Nf) * Tq := by ring
      _ ≤ ((1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2))) * Tq :=
          mul_le_mul_of_nonneg_right h2 hTq_nn
      _ = (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq := by ring
  have hEcost :
      (8 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ
        + (20 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ
      ≤ CtwoThree K₀ * e23A E * F.normSq Φ := by
    have h28 : (28 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ)
        ≤ CtwoThree K₀ * e23A E := by
      have hNf_le : Nf ≤ K₀ * (E.Kl * E.KL) ^ 3 := by
        rw [hNfdef]
        have := hcount
        rwa [hSfdef]
      have hstep1 : (28 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ)
          ≤ 32 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ * (E.Kl * E.KL) ^ 3 *
            (E.rho * E.aScat * K₀ * E.ell ^ 3) * (64 * K₀ ^ 2 * E.lille * eta E) := by
        rw [hzabs, hSσdef]
        have hfac : 0 ≤ (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * E.rho * E.aScat * K₀ *
            E.ell ^ 3 * (64 * K₀ ^ 2 * E.lille * eta E) := by positivity
        have hKL3 : 0 ≤ (E.Kl * E.KL) ^ 3 := by positivity
        nlinarith [hNf_le, hfac, hKL3, hK0, hlille_nn, hη_nn, hNf_nn, ha.le, hrho_nn,
          Real.sqrt_nonneg (E.rho * E.ell ^ 3), sq_nonneg K₀]
      have hstep2 : 32 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ * (E.Kl * E.KL) ^ 3 *
            (E.rho * E.aScat * K₀ * E.ell ^ 3) * (64 * K₀ ^ 2 * E.lille * eta E)
          = 4 * (Real.sqrt (E.rho * E.ell ^ 3) / E.ell ^ 3) * K₀ * (E.Kl * E.KL) ^ 3 *
            (8 * E.rho * K₀ * E.aScat * E.ell ^ 3) * (64 * K₀ ^ 2 * E.lille * eta E) := by ring
      have h3 : (1 / CtwoThree K₀) * e23A E ≤ CtwoThree K₀ * e23A E := by
        have h4 : (1 / CtwoThree K₀) ≤ CtwoThree K₀ := by
          rw [div_le_iff₀ hCpos]
          nlinarith [hC2]
        exact mul_le_mul_of_nonneg_right h4 he23nn
      exact hstep1.trans ((hstep2.symm ▸ hAbs3).trans h3)
    have hcomb : (8 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ
        + (20 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ
        = (28 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) *
            F.normSq Φ := by ring
    rw [hcomb]
    exact mul_le_mul_of_nonneg_right h28 hnormsq_nn
  -- ===================== the final assembly =====================
  have hsplit2 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| *
        (ε * F.bp (u2 s k) (u2 s k) + ε⁻¹ * F.bp (v2 s k) (v2 s k) +
          |c2 s k| * (F.bp (v2 s k) (v2 s k) + F.normSq Φ)))
      = (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε * F.bp (u2 s k) (u2 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε⁻¹ * F.bp (v2 s k) (v2 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.bp (v2 s k) (v2 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.normSq Φ)) := by
    rw [show (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| *
          (ε * F.bp (u2 s k) (u2 s k) + ε⁻¹ * F.bp (v2 s k) (v2 s k) +
            |c2 s k| * (F.bp (v2 s k) (v2 s k) + F.normSq Φ)))
        = ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
            ((|B2 s k| * (ε * F.bp (u2 s k) (u2 s k)) +
                |B2 s k| * (ε⁻¹ * F.bp (v2 s k) (v2 s k))) +
              (|B2 s k| * (|c2 s k| * F.bp (v2 s k) (v2 s k)) +
                |B2 s k| * (|c2 s k| * F.normSq Φ))) from by
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring]
    simp only [Finset.sum_add_distrib]
    abel
  have hsplit3 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| *
        (ε * F.bp (u3 s k) (u3 s k) + ε⁻¹ * F.bp (v3 s k) (v3 s k) +
          |c3 s k| * (F.bp (v3 s k) (v3 s k) + F.normSq Φ)))
      = (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (ε * F.bp (u3 s k) (u3 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (ε⁻¹ * F.bp (v3 s k) (v3 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.bp (v3 s k) (v3 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.normSq Φ)) := by
    rw [show (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| *
          (ε * F.bp (u3 s k) (u3 s k) + ε⁻¹ * F.bp (v3 s k) (v3 s k) +
            |c3 s k| * (F.bp (v3 s k) (v3 s k) + F.normSq Φ)))
        = ∑ s ∈ Sf, ∑ k ∈ F.PHset E,
            ((|B3 s k| * (ε * F.bp (u3 s k) (u3 s k)) +
                |B3 s k| * (ε⁻¹ * F.bp (v3 s k) (v3 s k))) +
              (|B3 s k| * (|c3 s k| * F.bp (v3 s k) (v3 s k)) +
                |B3 s k| * (|c3 s k| * F.normSq Φ))) from by
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring]
    simp only [Finset.sum_add_distrib]
    abel
  have htot8 : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε * F.bp (u2 s k) (u2 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (ε * F.bp (u3 s k) (u3 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (ε⁻¹ * F.bp (v2 s k) (v2 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (ε⁻¹ * F.bp (v3 s k) (v3 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.bp (v2 s k) (v2 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.bp (v3 s k) (v3 s k)))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B2 s k| * (|c2 s k| * F.normSq Φ))
        + (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |B3 s k| * (|c3 s k| * F.normSq Φ))
      ≤ 2 * (Wc * (ε * (E.bigM + 1))) * Tq + 2 * (Wc * (ε⁻¹ * Nf)) * Tq
        + 2 * (Wc * Sσ * Nf * Tq)
        + ((8 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ
          + (20 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) *
              F.normSq Φ) := by
    linarith [hu2, hu3, hv2, hv3, hσ2a, hσ3a, hσ2b, hσ3b]
  have hIcost2 : 2 * (Wc * (ε * (E.bigM + 1))) * Tq + 2 * (Wc * (ε⁻¹ * Nf)) * Tq
      ≤ (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq := by
    have heq : 2 * (Wc * (ε * (E.bigM + 1))) * Tq + 2 * (Wc * (ε⁻¹ * Nf)) * Tq
        = 2 * Wc * Real.sqrt (E.bigM + 1) * (1 + Nf) * Tq := by
      rw [hεmul, hεinv]
      ring
    rw [heq]
    exact hIcost
  have hScost2 : 2 * (Wc * Sσ * Nf * Tq)
      ≤ (1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq := by
    rw [show 2 * (Wc * Sσ * Nf * Tq) = 2 * Wc * Sσ * Nf * Tq from by ring]
    exact hScost
  have hcinv2 : 2 * (1 / CtwoThree K₀) ≤ 1 := by
    rw [show 2 * (1 / CtwoThree K₀) = 2 / CtwoThree K₀ from by ring, div_le_one hCpos]
    linarith [hC2]
  have hmain : -(CtwoThree K₀ * e23A E * F.normSq Φ)
      ≤ F.qw Φ (T.Q3twoT E + T.Q3threeT E +
          (E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat)) := by
    rw [FockData.qw_add, FockData.qw_add]
    have h2 := hLB2
    have h3 := hLB3
    rw [hsplit2] at h2
    rw [hsplit3] at h3
    have hreslb := hres
    have hnum : 2 * (Wc * (ε * (E.bigM + 1))) * Tq + 2 * (Wc * (ε⁻¹ * Nf)) * Tq
        + 2 * (Wc * Sσ * Nf * Tq)
        + ((8 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) * F.normSq Φ
          + (20 * (|E.z| / E.ell ^ 3) * Nf * E.rho * E.aScat * K₀ * E.ell ^ 3 * Sσ) *
              F.normSq Φ)
        ≤ 2 * ((1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq)
          + CtwoThree K₀ * e23A E * F.normSq Φ := by
      linarith [hIcost2, hScost2, hEcost]
    have hresnn' : 0 ≤ (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq :=
      mul_nonneg (by positivity) hTq_nn
    have h22 : 2 * ((1 / CtwoThree K₀) * ((E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq))
        ≤ (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq := by
      have h1 := mul_le_mul_of_nonneg_right hcinv2 hresnn'
      calc 2 * ((1 / CtwoThree K₀) * ((E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq))
          = (2 * (1 / CtwoThree K₀)) * ((E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq) := by ring
        _ ≤ 1 * ((E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq) := h1
        _ = (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq := by ring
    have heq : 2 * ((1 / CtwoThree K₀) * (E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq)
        = 2 * ((1 / CtwoThree K₀) * ((E.lille ^ 2 / (128 * E.KH ^ 2 * E.aScat ^ 2)) * Tq)) := by
      ring
    linarith [h2, h3, hreslb, htot8, hnum, hTq_nn, hnormsq_nn, h22, heq]

  rw [show -(CtwoThree K₀ * e23A E) * F.normSq Φ
        = -(CtwoThree K₀ * e23A E * F.normSq Φ) from by ring]
  exact hmain

theorem estQ3twoThreeA (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : Work.BoseB7A.EstQ3twoThreeA K₀ b₀ hb₀ := by
  classical
  have hCpos : 0 < CtwoThree K₀ := CtwoThree_pos K₀
  have hC2 : (2 : ℝ) ≤ CtwoThree K₀ := CtwoThree_ge_two K₀
  have hcinv_pos : 0 < 1 / CtwoThree K₀ := by positivity
  by_cases hK0 : 0 ≤ K₀
  · obtain ⟨tAbs, htAbs, hAbsE⟩ := absorb_errA K₀ b₀ hb₀ hK0 (1 / CtwoThree K₀) hcinv_pos
    obtain ⟨tW, htW, hWE⟩ := sum_W1alpha_le K₀ hK0
    obtain ⟨tDen, htDen, hDenE⟩ := q3Denom_le_four K₀ b₀ hb₀
    obtain ⟨tWs, htWs, hWsubE⟩ := sum_W1alpha_sub_le K₀ b₀ hb₀ hK0
    obtain ⟨tK, htK, hbas⟩ := kernel_basic K₀ b₀ hb₀
    obtain ⟨tP, htP, hPs⟩ := PH_subset_PHq_sub K₀ b₀ hb₀
    obtain ⟨tS, htS, hSm⟩ := smallness_ratios K₀ b₀ hb₀ (1 / CtwoThree K₀) hcinv_pos
    obtain ⟨tE, htE, hEt⟩ := eta_mul_le K₀ b₀ hb₀ (1 / CtwoThree K₀) hcinv_pos
    refine ⟨CtwoThree K₀,
      min tWs (min tW (min tAbs (min tDen (min tS (min tE (min tK tP)))))), le_of_lt hCpos, ?_, ?_⟩
    · exact lt_min htWs (lt_min htW (lt_min htAbs (lt_min htDen (lt_min htS (lt_min htE (lt_min htK htP))))))
    · intro Mode instA instF instD F T E hv htle hb hK Φ hΦ
      -- ===================== thresholds =====================
      have hTWs : hv.t ≤ tWs := le_trans htle (min_le_left _ _)
      have h00 : hv.t ≤ min tW (min tAbs (min tDen (min tS (min tE (min tK tP))))) :=
        le_trans htle (min_le_right _ _)
      have hTW : hv.t ≤ tW := le_trans h00 (min_le_left _ _)
      have h1 : hv.t ≤ min tAbs (min tDen (min tS (min tE (min tK tP)))) :=
        le_trans h00 (min_le_right _ _)
      have hTabs : hv.t ≤ tAbs := le_trans h1 (min_le_left _ _)
      have h2 : hv.t ≤ min tDen (min tS (min tE (min tK tP))) := le_trans h1 (min_le_right _ _)
      have hTden : hv.t ≤ tDen := le_trans h2 (min_le_left _ _)
      have h3 : hv.t ≤ min tS (min tE (min tK tP)) := le_trans h2 (min_le_right _ _)
      have hTs : hv.t ≤ tS := le_trans h3 (min_le_left _ _)
      have h4 : hv.t ≤ min tE (min tK tP) := le_trans h3 (min_le_right _ _)
      have hTe : hv.t ≤ tE := le_trans h4 (min_le_left _ _)
      have h5 : hv.t ≤ min tK tP := le_trans h4 (min_le_right _ _)
      have hTk : hv.t ≤ tK := le_trans h5 (min_le_left _ _)
      have hTp : hv.t ≤ tP := le_trans h5 (min_le_right _ _)
      -- ===================== scalars =====================
      have hell : 0 < E.ell := Work.BoseB7.ell_pos E hv
      have ha : 0 < E.aScat := hv.a_pos
      have hKH : 0 < E.KH := lt_of_lt_of_le one_pos hv.one_le_KH
      have hKl : 0 < E.Kl := lt_of_lt_of_le one_pos hv.one_le_Kl
      have hKL : 0 < E.KL := lt_of_lt_of_le one_pos hv.one_le_KL
      have hbigM1 : (1 : ℝ) ≤ E.bigM := hv.one_le_bigM
      have hbigM : (0 : ℝ) ≤ E.bigM := Work.BoseB7.bigM_nonneg E hv
      have hlille_nn : (0 : ℝ) ≤ E.lille := by
        rw [Work.BoseB7.lille_val E hv]
        exact Work.BoseBox.fsXp_nonneg hv.t_pos.le
      have hlille_pos : 0 < E.KH ^ 2 := by positivity
      have hmu : 0 < E.mu := Work.BoseB7.mu_pos E hv
      have hrho_nn : 0 ≤ E.rho := (Work.BoseB7.rho_pos E hv).le
      have hη_nn : 0 ≤ eta E := by
        rw [eta]
        exact Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hKl.le _) hlille_nn) _
      have hzsq : E.z ^ 2 = E.rho * E.ell ^ 3 := Work.BoseB7.zsq_eq E hv
      have hzabs : |E.z| = Real.sqrt (E.rho * E.ell ^ 3) := by
        rw [← hzsq, Real.sqrt_sq_eq_abs]
      have hMx : 0 < E.bigM + 1 := by linarith
      -- ===================== kernel facts =====================
      obtain ⟨hαeven, hAB, hHalf, hαle, hDq⟩ := hbas F T E hv hTk hb hK
      obtain ⟨hPHsub, hsubPHq⟩ := hPs F T E hv hTp hb hK
      have hDen4 : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.q3Denom s k ≤ 4 :=
        hDenE F T E hv hTden hb hK
      have hW1sum : ∑ k ∈ F.PHset E, |E.W1 k * E.alpha k| ≤
          2 * E.rho * E.aScat * K₀ * E.ell ^ 3 := hWE F T E hv hTW hK
      obtain ⟨hSm1, hSm2, hSm3, hSm4, hSm5, hSm6, hSm7, hSm8, hSm9⟩ := hSm E hv hTs hb
      obtain ⟨hηle, hη2le, hη3le, hη4le⟩ := hEt E hv hTe hb
      obtain ⟨hAbs1, hAbs2, hAbs3⟩ := hAbsE E hv hTabs hb
      -- ===================== the window =====================
      have hnonzero : ∀ s ∈ excited Mode, s ≠ 0 := fun s hs => by
        rw [Work.BoseB7.excited, Finset.mem_erase] at hs
        exact hs.1
      have hbOpWin : ∀ k : Mode, T.NWindow (E.bigM + 1) (F.bOp E.alpha k Φ) := fun k =>
        (NWindow_shift F T E hbigM hΦ 0 k).2.2.2.2.2.2.1
      have hWin : ∀ Ψ : F.H, T.NWindow (E.bigM + 1) Ψ →
          ∑ s ∈ excited Mode, F.bp (T.ta s Ψ) (T.ta s Ψ) ≤ (E.bigM + 1) * F.normSq Ψ :=
        fun Ψ hΨ => NWindow_ta_sum F T (by linarith : (0 : ℝ) ≤ E.bigM + 1) hΨ
          (excited Mode) hnonzero
      -- ===================== abbreviations =====================
      set ε : ℝ := (Real.sqrt (E.bigM + 1))⁻¹ with hεdef
      have hεpos : 0 < ε := by rw [hεdef]; positivity
      have hεmul : ε * (E.bigM + 1) = Real.sqrt (E.bigM + 1) := by
        rw [hεdef, inv_mul_eq_div, div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hMx))]
        have hsq := Real.sq_sqrt hMx.le
        rw [sq] at hsq
        exact hsq.symm
      have hεinv : ε⁻¹ = Real.sqrt (E.bigM + 1) := by rw [hεdef, inv_inv]
      set Wc : ℝ := 256 * (|E.z| / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille with hWcdef
      set Sσ : ℝ := 64 * K₀ ^ 2 * E.lille * eta E with hSσdef
      set Sf : Finset Mode := (excited Mode).filter (fun s => E.fL s ≠ 0) with hSfdef
      set Sq : Finset Mode := (excited Mode).filter (F.PHq E.KH E.aScat) with hSqdef
      set Nf : ℝ := (Sf.card : ℝ) with hNfdef
      set Tq : ℝ := ∑ q ∈ Sq, F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ) with hTqdef
      set B2 : Mode → Mode → ℝ :=
        fun s k => (E.z / E.ell ^ 3) * (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k))
        with hB2def
      set B3 : Mode → Mode → ℝ :=
        fun s k => (E.z / E.ell ^ 3) * (-(E.fL s * E.W1 k * E.alpha (s - k) * E.q3Denom s k))
        with hB3def
      set c2 : Mode → Mode → ℝ := fun s k => -(E.alpha k * T.ccrX s k) with hc2def
      set c3 : Mode → Mode → ℝ := fun s k => -(E.alpha (s - k) * T.ccrX s (s - k)) with hc3def
      set u2 : Mode → Mode → F.H := fun s k => T.ta s (F.bOp E.alpha (-k) Φ) with hu2def
      set v2 : Mode → Mode → F.H := fun s k => F.bOp E.alpha (s - k) Φ with hv2def
      have hv2val : ∀ s k, v2 s k = F.bOp E.alpha (s - k) Φ := by
        intro s k; rw [hv2def]
      set u3 : Mode → Mode → F.H := fun s k => T.ta s (F.bOp E.alpha (k - s) Φ) with hu3def
      set v3 : Mode → Mode → F.H := fun s k => F.bOp E.alpha k Φ with hv3def
      have hv3val : ∀ s k, v3 s k = F.bOp E.alpha k Φ := by
        intro s k; rw [hv3def]

      refine twoThree_core K₀ F T E Φ
        (256 * (|E.z| / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille)
        (64 * K₀ ^ 2 * E.lille * eta E)
        ((Real.sqrt (E.bigM + 1))⁻¹)
        (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ)
        (∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
          F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ))
        ((excited Mode).filter (fun s => E.fL s ≠ 0))
        ((excited Mode).filter (F.PHq E.KH E.aScat))
        (fun s k => (E.z / E.ell ^ 3) * (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k)))
        (fun s k => (E.z / E.ell ^ 3) * (-(E.fL s * E.W1 k * E.alpha (s - k) * E.q3Denom s k)))
        (fun s k => -(E.alpha k * T.ccrX s k))
        (fun s k => -(E.alpha (s - k) * T.ccrX s (s - k)))
        (fun s k => T.ta s (F.bOp E.alpha (-k) Φ))
        (fun s k => F.bOp E.alpha (s - k) Φ)
        (fun s k => T.ta s (F.bOp E.alpha (k - s) Φ))
        (fun s k => F.bOp E.alpha k Φ)
        rfl rfl rfl
        (by
          have hsq := Real.sq_sqrt hMx.le
          rw [sq] at hsq
          rw [inv_mul_eq_div, div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hMx))]
          exact hsq.symm)
        (by rw [inv_inv])
        rfl rfl rfl rfl
        (fun s k => rfl) (fun s k => rfl) (fun s k => rfl) (fun s k => rfl)
        (fun s k => rfl) (fun s k => rfl) (fun s k => rfl) (fun s k => rfl)
        hαeven hPHsub hsubPHq hHalf hαle hDq hDen4
        (fun k => hK.W1_le k) (fun s => hK.fL_nonneg s) (fun s => hK.fL_le_one s)
        (fun s q hfL hq => hK.ccrX_small s q hfL hq)
        hK.count_PL hW1sum
        (fun s hfL => hWsubE F T E hv hTWs hb hK s hfL)
        (fun k => hbOpWin k)
        hell ha hKl hKH hKL hmu hlille_nn hη_nn hK0 hrho_nn hbigM hzabs
        (hAbsE E hv hTabs hb).1 (hAbsE E hv hTabs hb).2.1 (hAbsE E hv hTabs hb).2.2
  · refine ⟨0, 1, le_refl 0, one_pos, ?_⟩
    intro Mode instA instF instD F T E hv htle hb hK Φ hΦ
    exfalso
    have h1 : |E.W1 0| ≤ K₀ * E.aScat := hK.W1_le 0
    have h2 : 0 < E.aScat := hv.a_pos
    have h3 : K₀ * E.aScat < 0 := mul_neg_of_neg_of_pos (not_le.mp hK0) h2
    linarith [abs_nonneg (E.W1 0)]

end Work.BoseB7A
