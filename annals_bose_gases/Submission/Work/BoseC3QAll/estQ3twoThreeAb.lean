import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.estQ3twoThreeA
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
/-- **The `u`-part of `Q₃⁽³⁾`**, where the pairing vector `ã_s(b_{k−s}Φ)` depends
on both indices: after the reindexing `k ↦ k − s` (into `P_H^q`) the window bound
applies to the pairing against `b_pΦ`. -/
theorem sum_u3_le (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (Φ : F.H)
    {M : ℝ} (hM : 0 ≤ M) {ε Wc Tq : ℝ} (hε : 0 < ε) (hWc : 0 ≤ Wc)
    {Sf Sq : Finset Mode} (hSf : Sf ⊆ excited Mode)
    (hTq : Tq = ∑ q ∈ Sq, F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ))
    (hg : ∀ p, T.NWindow (M + 1) (F.bOp E.alpha p Φ))
    {c : Mode → Mode → ℝ} (hc : ∀ s k : Mode, k ∈ F.PHset E → |c s k| ≤ Wc)
    (hc0 : ∀ s k : Mode, k ∈ F.PHset E → E.W1 k = 0 → c s k = 0)
    (hmem : ∀ s ∈ Sf, ∀ k ∈ F.PHset E, E.W1 k ≠ 0 → k - s ∈ Sq) :
    (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |c s k| *
        (ε * F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ))))
      ≤ Wc * (ε * (M + 1)) * Tq := by
  have hnonzero : ∀ s ∈ excited Mode, s ≠ 0 := fun s hs => by
    rw [Work.BoseB7.excited, Finset.mem_erase] at hs
    exact hs.1
  -- the `k`-sums may be cut down to the guard set `{k | Ŵ₁ k ≠ 0}`: the
  -- summand carries the coefficient `c s k`, which vanishes off it
  have hGsub : (F.PHset E).filter (fun k => E.W1 k ≠ 0) ⊆ F.PHset E :=
    Finset.filter_subset _ _
  have hdrop : (∑ s ∈ Sf, ∑ k ∈ F.PHset E, |c s k| *
        (ε * F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ))))
      = ∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0), |c s k| *
        (ε * F.bp (T.ta s (F.bOp E.alpha (k - s) Φ))
          (T.ta s (F.bOp E.alpha (k - s) Φ))) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    refine (Finset.sum_subset hGsub fun k hk hknot => ?_).symm
    have hW : E.W1 k = 0 := by
      by_contra h
      exact hknot (Finset.mem_filter.mpr ⟨hk, h⟩)
    rw [hc0 s k hk hW]
    simp
  have h1 : (∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0), |c s k| *
        (ε * F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ))))
      ≤ ∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0), Wc *
          (ε * F.bp (T.ta s (F.bOp E.alpha (k - s) Φ))
            (T.ta s (F.bOp E.alpha (k - s) Φ))) := by
    refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun k hk => ?_
    exact mul_le_mul_of_nonneg_right (hc s k (hGsub hk)) (mul_nonneg hε.le (F.bp_nonneg _))
  have h2 : (∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0), Wc *
        (ε * F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ))))
      = (ε * Wc) * (∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
          F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ))) := by
    rw [show (∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0), Wc *
          (ε * F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ))))
        = ∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0), (ε * Wc) *
            F.bp (T.ta s (F.bOp E.alpha (k - s) Φ))
              (T.ta s (F.bOp E.alpha (k - s) Φ)) from by
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring]
    exact sum_const_mul_sum Sf ((F.PHset E).filter (fun k => E.W1 k ≠ 0)) (ε * Wc) _
  have h3A : (∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
        F.bp (T.ta s (F.bOp E.alpha (k - s) Φ)) (T.ta s (F.bOp E.alpha (k - s) Φ)))
      ≤ ∑ s ∈ Sf, ∑ p ∈ Sq,
          F.bp (T.ta s (F.bOp E.alpha p Φ)) (T.ta s (F.bOp E.alpha p Φ)) := by
    refine Finset.sum_le_sum fun s hs => ?_
    exact sum_le_sum_of_inj (t := (F.PHset E).filter (fun k => E.W1 k ≠ 0)) (u := Sq)
      (φ := fun k => k - s)
      (f := fun p => F.bp (T.ta s (F.bOp E.alpha p Φ)) (T.ta s (F.bOp E.alpha p Φ)))
      (fun i j hij => sub_left_inj.mp hij)
      (fun k hk => hmem s hs k (hGsub hk) (Finset.mem_filter.mp hk).2)
      (fun p => F.bp_nonneg _)
  have h3B : (∑ s ∈ Sf, ∑ p ∈ Sq,
        F.bp (T.ta s (F.bOp E.alpha p Φ)) (T.ta s (F.bOp E.alpha p Φ)))
      ≤ ∑ s ∈ excited Mode, ∑ p ∈ Sq,
          F.bp (T.ta s (F.bOp E.alpha p Φ)) (T.ta s (F.bOp E.alpha p Φ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hSf ?_
    intro s _ _
    exact Finset.sum_nonneg fun p _ => F.bp_nonneg _
  have h3 : (∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
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
      = ∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0), |c s k| *
          (ε * F.bp (T.ta s (F.bOp E.alpha (k - s) Φ))
            (T.ta s (F.bOp E.alpha (k - s) Φ))) := hdrop
    _ ≤ ∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0), Wc *
          (ε * F.bp (T.ta s (F.bOp E.alpha (k - s) Φ))
            (T.ta s (F.bOp E.alpha (k - s) Φ))) := h1
    _ = (ε * Wc) * (∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
          F.bp (T.ta s (F.bOp E.alpha (k - s) Φ))
            (T.ta s (F.bOp E.alpha (k - s) Φ))) := h2
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
    (hc0 : ∀ s k : Mode, k ∈ F.PHset E → E.W1 k = 0 → c s k = 0)
    (hmem : ∀ s ∈ Sf, ∀ k ∈ F.PHset E, E.W1 k ≠ 0 → s - k ∈ Sq) :
    (∑ s ∈ Sf, ∑ k ∈ F.PHset E,
        |c s k| * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ))
      ≤ Wc * Nf * Tq := by
  have hGsub : (F.PHset E).filter (fun k => E.W1 k ≠ 0) ⊆ F.PHset E :=
    Finset.filter_subset _ _
  have hdrop : (∑ s ∈ Sf, ∑ k ∈ F.PHset E,
        |c s k| * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ))
      = ∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
        |c s k| * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    refine (Finset.sum_subset hGsub fun k hk hknot => ?_).symm
    have hW : E.W1 k = 0 := by
      by_contra h
      exact hknot (Finset.mem_filter.mpr ⟨hk, h⟩)
    rw [hc0 s k hk hW]
    simp
  have h1 : (∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
        |c s k| * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ))
      ≤ ∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
          Wc * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ) := by
    refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun k hk => ?_
    exact mul_le_mul_of_nonneg_right (hc s k (hGsub hk)) (F.bp_nonneg _)
  have h2 : (∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
        Wc * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ))
      = Wc * (∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
          F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ)) :=
    sum_const_mul_sum Sf ((F.PHset E).filter (fun k => E.W1 k ≠ 0)) Wc _
  have h3 : (∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
        F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ)) ≤ ∑ s ∈ Sf, Tq := by
    refine Finset.sum_le_sum fun s hs => ?_
    rw [hTq]
    exact sum_le_sum_of_inj (t := (F.PHset E).filter (fun k => E.W1 k ≠ 0)) (u := Sq)
      (φ := fun k => s - k)
      (f := fun p => F.bp (F.bOp E.alpha p Φ) (F.bOp E.alpha p Φ))
      (fun i j hij => sub_right_inj.mp hij)
      (fun k hk => hmem s hs k (hGsub hk) (Finset.mem_filter.mp hk).2)
      (fun p => F.bp_nonneg _)
  have h4 : (∑ s ∈ Sf, Tq) = Nf * Tq := by
    rw [hNf, Finset.sum_const, nsmul_eq_mul]
  calc (∑ s ∈ Sf, ∑ k ∈ F.PHset E,
        |c s k| * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ))
      = ∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
          |c s k| * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ) := hdrop
    _ ≤ ∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
          Wc * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ) := h1
    _ = Wc * (∑ s ∈ Sf, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
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
  rw [Work.BoseB7A.TildeData.Q3twoT]
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
  rw [Work.BoseB7A.TildeData.Q3threeT]
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



end Work.BoseC3QAll
