import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseC3QAll.NWindow_shift
import Submission.Work.BoseC3QAll.NWindow_ta_sum
import Submission.Work.BoseC3QAll.absorb_errA
import Submission.Work.BoseC3QAll.q3Denom_le_four
import Submission.Work.BoseC3QAll.smallness_ratios
import Submission.Work.BoseC3QAll.sum_W1alpha_le
import Submission.Work.BoseC3QAll.sum_W1alpha_sub_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseC3QAll.estQ3twoThreeA` — FS `eq:EstimateQ3Tilde2+3` (`Q₃⁽²⁾ + Q₃⁽³⁾`)

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
  support of `f_L` (`Q3KernelFSAll.count_PL`, `k ↦ s−k` injective into `P_H^q`);
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

namespace Work.BoseC3QAll

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

/-- `[a_p†, ã_s] = −ccrX s p`: the `Work.BoseB7A.TildeData.ta_aDag` field, rearranged. -/
theorem aDag_ta_comm (F : FockData Mode) (T : TildeData F) (s p : Mode) :
    F.aDag p ∘ₗ T.ta s
      = T.ta s ∘ₗ F.aDag p - (T.ccrX s p) • (1 : F.H →ₗ[ℝ] F.H) := by
  have h := T.ta_aDag s p
  rw [h]
  abel

/-- `[ã_s†, a_p†] = 0`, i.e. `ã_s†` commutes with every creation operator: the
adjoint of `Work.BoseB7A.TildeData.ta_a_comm`. -/
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

/-- `[ã_s†, a_p] = −ccrX s p`: the adjoint of `Work.BoseB7A.TildeData.ta_aDag`
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


end Work.BoseC3QAll
