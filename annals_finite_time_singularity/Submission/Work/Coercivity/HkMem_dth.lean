/-
# `H^k` membership passes from `f` to `D_θ f` and `D_z f`

`Work.Spaces.HkMem α k g` says that the `H^k`-integrand of `g`,
`Work.Spaces.HkIntegrand α k g`, has honest iterated integrals: every angular slice
`θ ↦ HkIntegrand α k g z θ` is integrable on `Iθ` (`z ∈ Iz`) and `z ↦ ∫_θ HkIntegrand α k g z θ`
is integrable on `Iz`.

The integrand is a sum of squares of weighted derivatives, grouped into two families:
the *pure* family `(D_z^i g · w/√sin(2θ)^η)²` (`0 ≤ i ≤ k`) and the *mixed* family
`(D_z^j D_θ^i g · W)²` (`1 ≤ i`, `i + j ≤ k`), where `W = Wt α = w · sin(2θ)^{-γ/2}`.

For `g = D_θ f` and `g = D_z f` every summand of `HkIntegrand α k g` is, up to a
dominating weight, a summand of `HkIntegrand α (k+1) f`:

* `D_θ`-family: `D_z^i (D_θ f) = D_z^i D_θ f` and `D_z^j D_θ^i (D_θ f) = D_z^j D_θ^{i+1} f`
  are *definitionally* mixed derivatives of `f` of total order `i + 1`, resp. `i + j + 1`;
* `D_z`-family: `D_z^i (D_z f) = D_z^{i+1} f` is a pure derivative of `f`, while
  `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f` uses the commutation of `D_z` and `D_θ`
  (`Work.Spaces.mixed_comm`, valid on the closed quadrant because `f` is `C^∞` on a
  neighbourhood of it);
* the pure `D_θ` summands carry the lighter weight `w/√sin(2θ)^η`; since `η < γ` and
  `sin(2θ) ∈ [0,1]` on `Iθ`, that weight is dominated by `W` (`Work.Spaces.H_le_Wt`).

The two index reindexings are `SumRowShift_eq` (`D_θ` case) and `SumShiftZ_le` (`D_z`
case).  Since the dominating integrand `HkIntegrand α (k+1) f` has honest integrals by
hypothesis, and the dominated integrands are a.e. strongly measurable
(`aesm_HkIntegrand_slice`, `aesm_uncurry_HkIntegrand`), the integrability transfers.

This is the membership half of the paper's statement that `ℋ^k` is closed under
`D_θ` and `D_z`; the corresponding statement for the admissible class `HkAdm` is
`Work.Coercivity.HkAdm_dth`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.H_le_Wt
import Submission.Work.Coercivity.SumShiftZ_le
import Submission.Work.Coercivity.SumRowShift_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Structural identities for the shifted families -/

/-- The pure family of the `H^k`-integrand of `D_θ f` is the family of mixed derivatives
`D_z^i D_θ f = mixed i 1 f` of `f`. -/
private lemma DzIter_Dth_eq (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Spaces.DzIter i (Spaces.Dth f) = Spaces.mixed i 1 f := by
  simp only [Spaces.mixed, Spaces.DthIter_succ, Spaces.DthIter_zero]

/-- The mixed family of the `H^k`-integrand of `D_θ f` is the mixed family of `f` with
the `D_θ`-order raised by one: `D_z^j D_θ^i D_θ f = mixed j (i+1) f`. -/
private lemma mixed_Dth_eq (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Spaces.mixed j i (Spaces.Dth f) = Spaces.mixed j (i + 1) f := by
  simp only [Spaces.mixed]
  have h : Spaces.Dth f = Spaces.DthIter 1 f := rfl
  rw [h, Spaces.DthIter_add_right]

/-- The pure family of the `H^k`-integrand of `D_z f` is the family of pure derivatives
`D_z^{i+1} f` of `f`. -/
private lemma DzIter_Dz_eq (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Spaces.DzIter i (Spaces.Dz f) = Spaces.DzIter (i + 1) f := by
  rw [Spaces.DzIter_add_right]
  rfl

/-- The mixed family of the `H^k`-integrand of `D_z f` is the mixed family of `f` with
the `D_z`-order raised by one: `D_z^j D_θ^i D_z f = D_z^{j+1} D_θ^i f` on the closed
quadrant, by commutation of `D_z` and `D_θ`. -/
private lemma mixed_Dz_eq (j i : ℕ) {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd f) {z θ : ℝ}
    (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ) :
    Spaces.mixed j i (Spaces.Dz f) z θ = Spaces.mixed (j + 1) i f z θ := by
  simpa using Spaces.mixed_comm f hsm j i 1 0 z θ hz hθ

/-- A sum over `i ≤ k` of `F (i+1)` is dominated by the sum over `a ≤ k+1` of `F a`
when `F ≥ 0` (the extra term being `F 0`). -/
private lemma SumSuccRange_le (k : ℕ) (F : ℕ → ℝ) (hF : ∀ a, 0 ≤ F a) :
    (∑ i ∈ Finset.range (k + 1), F (i + 1)) ≤ ∑ a ∈ Finset.range (k + 2), F a := by
  have h2 : (∑ a ∈ Finset.range (k + 2), F a)
      = (∑ i ∈ Finset.range (k + 1), F (i + 1)) + F 0 :=
    Finset.sum_range_succ' F (k + 1)
  linarith [hF 0]

/-! ## Pointwise domination of the shifted integrands -/

/-- **Pointwise domination, `D_θ` case.**  Every summand of the `H^k`-integrand of
`D_θ f` is dominated by a summand of the `H^{k+1}`-integrand of `f`: the pure summands
`D_z^i D_θ f` are mixed summands of `f` with weight `w/√sin^η ≤ W`, and the mixed
summands `D_z^j D_θ^{i+1} f` are themselves mixed summands of `f` at level `k+1`. -/
theorem HkIntegrand_Dth_le (α : ℝ) (hα : 0 < α) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ) :
    Spaces.HkIntegrand α k (Spaces.Dth f) z θ ≤ Spaces.HkIntegrand α (k + 1) f z θ := by
  set H : ℝ := Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2) with hH
  set W : ℝ := Spaces.Wt α z θ with hW
  have hLHS : Spaces.HkIntegrand α k (Spaces.Dth f) z θ
      = (∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i (Spaces.Dth f) z θ * H) ^ 2)
        + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i (Spaces.Dth f) z θ * W) ^ 2
              else 0)) := by
    simp only [Spaces.HkIntegrand, ← hH, ← hW]
  have hRHS : Spaces.HkIntegrand α (k + 1) f z θ
      = (∑ a ∈ Finset.range (k + 2), (Spaces.DzIter a f z θ * H) ^ 2)
        + (∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
            (if 1 ≤ a ∧ a + b ≤ k + 1 then (Spaces.mixed b a f z θ * W) ^ 2 else 0)) := by
    simp only [Spaces.HkIntegrand, ← hH, ← hW]
  have h1 : (∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i (Spaces.Dth f) z θ * H) ^ 2)
      ≤ ∑ i ∈ Finset.range (k + 1), (Spaces.mixed i 1 f z θ * W) ^ 2 := by
    calc (∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i (Spaces.Dth f) z θ * H) ^ 2)
        = ∑ i ∈ Finset.range (k + 1), (Spaces.mixed i 1 f z θ * H) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => by rw [DzIter_Dth_eq i f])
      _ ≤ ∑ i ∈ Finset.range (k + 1), (Spaces.mixed i 1 f z θ * W) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hw := Spaces.H_le_Wt α hα z θ hz hθ
          have h1 : (Spaces.mixed i 1 f z θ * H) ^ 2
              = (Spaces.mixed i 1 f z θ) ^ 2 * H ^ 2 := by ring
          have h2 : (Spaces.mixed i 1 f z θ * W) ^ 2
              = (Spaces.mixed i 1 f z θ) ^ 2 * W ^ 2 := by ring
          rw [h1, h2]
          exact mul_le_mul_of_nonneg_left hw (sq_nonneg _)
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i (Spaces.Dth f) z θ * W) ^ 2
                else 0))
      = (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j (i + 1) f z θ * W) ^ 2 else 0)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc, mixed_Dth_eq j i f]
    · rw [if_neg hc, if_neg hc]
  have hkey : (∑ i ∈ Finset.range (k + 1), (Spaces.mixed i 1 f z θ * W) ^ 2)
      + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j (i + 1) f z θ * W) ^ 2 else 0))
      = (∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
          (if 1 ≤ a ∧ a + b ≤ k + 1 then (Spaces.mixed b a f z θ * W) ^ 2 else 0)) := by
    simpa only using SumRowShift_eq k (fun a b => (Spaces.mixed b a f z θ * W) ^ 2)
  have hnn : 0 ≤ ∑ a ∈ Finset.range (k + 2), (Spaces.DzIter a f z θ * H) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  rw [hLHS, hRHS]
  linarith [h1, h2, hkey, hnn]

/-- **Pointwise domination, `D_z` case.**  Every summand of the `H^k`-integrand of
`D_z f` is dominated by a summand of the `H^{k+1}`-integrand of `f`: the pure summands
`D_z^i D_z f = D_z^{i+1} f` are pure summands of `f` at level `k+1`, and the mixed
summands `D_z^j D_θ^i D_z f = D_z^{j+1} D_θ^i f` are mixed summands of `f` at level
`k+1` (commutation of `D_z` and `D_θ`, which needs `SmoothNbhd f`). -/
theorem HkIntegrand_Dz_le (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd f)
    (z θ : ℝ) (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ) :
    Spaces.HkIntegrand α k (Spaces.Dz f) z θ ≤ Spaces.HkIntegrand α (k + 1) f z θ := by
  set H : ℝ := Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2) with hH
  set W : ℝ := Spaces.Wt α z θ with hW
  have hLHS : Spaces.HkIntegrand α k (Spaces.Dz f) z θ
      = (∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i (Spaces.Dz f) z θ * H) ^ 2)
        + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i (Spaces.Dz f) z θ * W) ^ 2
              else 0)) := by
    simp only [Spaces.HkIntegrand, ← hH, ← hW]
  have hRHS : Spaces.HkIntegrand α (k + 1) f z θ
      = (∑ a ∈ Finset.range (k + 2), (Spaces.DzIter a f z θ * H) ^ 2)
        + (∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
            (if 1 ≤ a ∧ a + b ≤ k + 1 then (Spaces.mixed b a f z θ * W) ^ 2 else 0)) := by
    simp only [Spaces.HkIntegrand, ← hH, ← hW]
  have h1 : (∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i (Spaces.Dz f) z θ * H) ^ 2)
      ≤ ∑ a ∈ Finset.range (k + 2), (Spaces.DzIter a f z θ * H) ^ 2 := by
    refine le_trans (le_of_eq ?_) (SumSuccRange_le k
      (fun a => (Spaces.DzIter a f z θ * H) ^ 2) (fun a => sq_nonneg _))
    exact Finset.sum_congr rfl (fun i _ => by rw [DzIter_Dz_eq i f])
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i (Spaces.Dz f) z θ * W) ^ 2
                else 0))
      = (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed (j + 1) i f z θ * W) ^ 2 else 0)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc, mixed_Dz_eq j i hsm hz hθ]
    · rw [if_neg hc, if_neg hc]
  have hkey : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed (j + 1) i f z θ * W) ^ 2 else 0))
      ≤ (∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
          (if 1 ≤ a ∧ a + b ≤ k + 1 then (Spaces.mixed b a f z θ * W) ^ 2 else 0)) := by
    simpa only using SumShiftZ_le k (fun a b => (Spaces.mixed b a f z θ * W) ^ 2)
      (fun a b => sq_nonneg _)
  rw [hLHS, hRHS]
  linarith [h1, h2, hkey]

/-! ## Integrability transfer -/

/-- If the `(k+1)`-integrand of `f` has honest iterated integrals, and the `k`-integrand
of the smooth `g` is pointwise dominated by it on the quadrant, then `g ∈ ℋ^k`.  This is
the assembly step of every membership transfer of this chapter: `SmoothNbhd g` supplies
the a.e. strong measurability of the integrand (`aesm_HkIntegrand_slice`,
`aesm_uncurry_HkIntegrand`) and the domination supplies the integrability. -/
theorem HkMem_of_HkIntegrand_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hsmg : Spaces.SmoothNbhd g) (h : Spaces.HkMem α (k + 1) f)
    (hle : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ,
      Spaces.HkIntegrand α k g z θ ≤ Spaces.HkIntegrand α (k + 1) f z θ) :
    Spaces.HkMem α k g := by
  have hmesθ : MeasurableSet Spaces.Iθ := measurableSet_Icc
  have hmesz : MeasurableSet Spaces.Iz := measurableSet_Ici
  have hslice := aesm_HkIntegrand_slice α k hsmg
  have hjoint := aesm_uncurry_HkIntegrand α k hsmg
  constructor
  · intro z hz
    refine Integrable.mono' (h.1 z hz) (hslice z hz) ?_
    filter_upwards [ae_restrict_mem hmesθ] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Spaces.HkIntegrand_nonneg α k g z θ)]
    exact hle z hz θ hθ
  · refine Integrable.mono' h.2 hjoint.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem hmesz] with z hz
    have hnn : 0 ≤ ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α k g z θ :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem hmesθ
        (fun θ _ => Spaces.HkIntegrand_nonneg α k g z θ))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem hmesθ (fun θ _ => Spaces.HkIntegrand_nonneg α k g z θ))
      (h.1 z hz)
      (ae_restrict_of_forall_mem hmesθ (fun θ hθ => hle z hz θ hθ))

/-! ## The target lemma -/

theorem HkMem_dth (α : ℝ) (hα : 0 < α) (k : ℕ) {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd f)
    (h : Spaces.HkMem α (k + 1) f) :
    Spaces.HkMem α k (Spaces.Dth f) ∧ Spaces.HkMem α k (Spaces.Dz f) :=
  ⟨HkMem_of_HkIntegrand_le α k hsm.Dth h (fun z hz θ hθ =>
      HkIntegrand_Dth_le α hα k f z θ hz hθ),
    HkMem_of_HkIntegrand_le α k hsm.Dz h (fun z hz θ hθ =>
      HkIntegrand_Dz_le α k hsm z θ hz hθ)⟩

end Work.Coercivity
