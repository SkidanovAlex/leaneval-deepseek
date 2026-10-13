/-
Copyright: work module for the Elgindi finite-time singularity project.

# `T2S` with the flat coefficient norm of order **2**

**Why this module exists.**  The frozen `T2S` (`T2S.lean`) carries `CoefThMem 1 f` and puts
`CoefTh 1 f` on the right.  Its `T2SupF` input needs, among others, the α-uniform pointwise
bound `|D_z² f| ≤ C(Xn α f + CoefTh 1 f)` on the open quadrant.  That bound is **not** obtainable
from `CoefThMem 1 f`: the θ-Lipschitz step
`|D_z²f(z,θ)| ≤ |D_z²f(z,θ₀)| + (π/2)·sup|∂_θ(D_z²f)|` needs `∂_θ(D_z²f) = D_z²(∂_θf)`, i.e. the
slot `(b,i) = (2,0)` of `CoefTh`, which only enters at `l ≥ 2`; and the radial-Hardy route is
documented FALSE in the `α < 1/10` regime (`NOTES_t2SupF.md`, `NOTES_t2SupF_b2_analysis.md`).
With `CoefThMem 2 f` the very same slot `(2,0)` *is* available and the route is short and
α-uniform (already proved ingredients: `SupDzAux.sup_dz_avg_le` and `supAbsO_le_coefTh`).

**What this module proves.**  `coefTh_mono` (monotonicity of `CoefTh` in the order), the
repaired bundle `T2SF2` (`CoefThMem 2`), the repaired input `T2SupF2` (with `CoefTh 2 f` on the
right), the reduction `T2SupF_of_T2SupF2` (the frozen `T2SupF` *follows* from `T2SupF2`, since
`CoefThMem 2 → CoefThMem 1` and `CoefTh 1 ≤ CoefTh 2`), and finally

`t2SupF2_of_cases : T2SupFB2C → T2SupF2`, i.e. the repaired input from its three cases (two of
which are proved here from `t2SupF.lean`, the third being the delegated `sup_dz2_coef2`).

**How the repaired `T2S` follows.**  The four remaining inputs of the assembly
(`T2SupG`, `T2Slice`, `T2Easy`, `T2Hard`, `T2Aesm`) are stated with the *weaker* bundle `T2SF`,
so they apply to `T2SF2`-data via `T2SF2.toT2SF`; re-running the bookkeeping of `T2S_of_pieces`
with `W := Xn α f + CoefTh 2 f` (the only change is the two places where `CoefTh 1 f` appears)
then gives the frozen statement with `CoefThMem 1 f` strengthened to `CoefThMem 2 f` and
`CoefTh 1 f` replaced by `CoefTh 2 f` on the right.  That duplication is deliberately *not* made
here, because the change of hypothesis is the lead's decision (it touches the frozen `T2S` and
`VocabO.T2Clause`).

Suggested repair for the lead: replace `CoefThMem 1 f` / `CoefTh 1 f` by `CoefThMem 2 f` /
`CoefTh 2 f` in `VocabO.T2Clause` and in the frozen `T2S` (the rows supply `CoefThMem 2 f` with
a little more work: `L₁₂(g)` for row 6, `V(Φ̃_g)` for row 16).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.TransportS.T2S_final
import Submission.Work.FTS.TransportS.t2SupF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- `CoefTh` is monotone in the order. -/
theorem coefTh_mono {l l' : ℕ} (hl : l ≤ l') (f : Fn) :
    Work.FTS.VocabO.CoefTh l f ≤ Work.FTS.VocabO.CoefTh l' f := by
  have hFr : Finset.range (l + 1) ⊆ Finset.range (l' + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have hF : ∀ b i : ℕ, (if b + i ≤ l then
        Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0)
      ≤ (if b + i ≤ l' then
        Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0) := by
    intro b i
    by_cases h : b + i ≤ l
    · rw [if_pos h, if_pos (le_trans h hl)]
    · rw [if_neg h]
      by_cases h2 : b + i ≤ l'
      · rw [if_pos h2]; exact supAbsO_nonneg _
      · rw [if_neg h2]
  have hnn : ∀ b : ℕ, 0 ≤ (∑ i ∈ Finset.range (l' + 1),
      (if b + i ≤ l' then
        Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0)) :=
    fun b => Finset.sum_nonneg fun i _ => by
      by_cases h : b + i ≤ l'
      · rw [if_pos h]; exact supAbsO_nonneg _
      · rw [if_neg h]
  have hnn' : ∀ b : ℕ, 0 ≤ (∑ i ∈ Finset.range (l + 1),
      (if b + i ≤ l' then
        Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0)) :=
    fun b => Finset.sum_nonneg fun i _ => by
      by_cases h : b + i ≤ l'
      · rw [if_pos h]; exact supAbsO_nonneg _
      · rw [if_neg h]
  unfold Work.FTS.VocabO.CoefTh
  have hFnn : ∀ b i : ℕ, 0 ≤ (if b + i ≤ l' then
      Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0) := by
    intro b i
    by_cases h : b + i ≤ l'
    · rw [if_pos h]; exact supAbsO_nonneg _
    · rw [if_neg h]
  calc (∑ b ∈ Finset.range (l + 1), ∑ i ∈ Finset.range (l + 1),
        (if b + i ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0))
      ≤ ∑ b ∈ Finset.range (l + 1), ∑ i ∈ Finset.range (l + 1),
        (if b + i ≤ l' then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0) :=
        Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun i _ => hF b i
    _ ≤ ∑ b ∈ Finset.range (l + 1), ∑ i ∈ Finset.range (l' + 1),
        (if b + i ≤ l' then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0) :=
        Finset.sum_le_sum fun b _ =>
          Finset.sum_le_sum_of_subset_of_nonneg hFr (fun i _ _ => hFnn b i)
    _ ≤ ∑ b ∈ Finset.range (l' + 1), ∑ i ∈ Finset.range (l' + 1),
        (if b + i ≤ l' then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg hFr (fun b _ _ =>
          Finset.sum_nonneg fun i _ => hFnn b i)

/-! ## The repaired bundle and input -/

/-- The repaired `f`-side bundle: `CoefThMem 2 f` in place of `CoefThMem 1 f`. -/
def T2SF2 (α : ℝ) (f : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen f ∧ Work.Spaces.HkMem α 4 f
    ∧ Work.FTS.VocabO.CoefThMem 2 f

theorem T2SF2.smoothOpen {α : ℝ} {f : Fn} (h : T2SF2 α f) :
    Work.FTS.EllipticEst.SmoothOpen f := h.1
theorem T2SF2.hk {α : ℝ} {f : Fn} (h : T2SF2 α f) : Work.Spaces.HkMem α 4 f := h.2.1
theorem T2SF2.coef2 {α : ℝ} {f : Fn} (h : T2SF2 α f) : Work.FTS.VocabO.CoefThMem 2 f := h.2.2

/-- `T2SF2` is a strengthening of `T2SF`. -/
theorem T2SF2.toT2SF {α : ℝ} {f : Fn} (h : T2SF2 α f) : T2SF α f :=
  ⟨h.1, h.2.1, coefThMem_mono (by norm_num : (1 : ℕ) ≤ 2) h.2.2⟩

/-- The repaired `T2SupF`: the pointwise order-≤2 bounds with `CoefTh 2 f` on the right. -/
def T2SupF2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 → T2SF2 α f →
    ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ|
        ≤ C * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 2 f)

/-- The `a ≥ 1` case of the *repaired* input, from the proved `t2SupF_aPos` and
`coefTh_mono`. -/
theorem t2SupF2_aPos :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 → T2SF2 α f →
      ∀ b a : ℕ, 1 ≤ a → a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b a f z θ|
          ≤ C * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 2 f) := by
  obtain ⟨C, hC, h⟩ := t2SupF_aPos
  refine ⟨C, hC, ?_⟩
  intro α f hα hα1 hf b a ha hab z θ hz hθ hθ1
  refine le_trans (h α f hα hα1 hf.toT2SF b a ha hab z θ hz hθ hθ1) ?_
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (coefTh_mono (by norm_num : (1 : ℕ) ≤ 2) f)) (le_of_lt hC)

/-- The `a = 0`, `b ≤ 1` case of the *repaired* input, from the proved `t2SupF_b_le_one` and
`coefTh_mono`. -/
theorem t2SupF2_b_le_one :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 → T2SF2 α f →
      ∀ b : ℕ, b ≤ 1 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.DzIter b f z θ|
          ≤ C * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 2 f) := by
  obtain ⟨C, hC, h⟩ := t2SupF_b_le_one
  refine ⟨C, hC, ?_⟩
  intro α f hα hα1 hf b hb z θ hz hθ hθ1
  refine le_trans (h α f hα hα1 hf.toT2SF b hb z θ hz hθ hθ1) ?_
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (coefTh_mono (by norm_num : (1 : ℕ) ≤ 2) f)) (le_of_lt hC)

/-- The `a = 0`, `b = 2` case of the *repaired* input — the delegated
`Work.FTS.TransportS.sup_dz2_coef2`. -/
def T2SupFB2C : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 → T2SF2 α f →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.DzIter 2 f z θ|
        ≤ C * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 2 f)

/-- **The repaired input `T2SupF2` from its three cases.**  The `a ≥ 1` and `a = 0, b ≤ 1`
cases are *proved* here (from the proved `t2SupF_aPos`/`t2SupF_b_le_one` of `t2SupF.lean`);
the single remaining case is the delegated `sup_dz2_coef2`. -/
theorem t2SupF2_of_cases (h2 : T2SupFB2C) : T2SupF2 := by
  obtain ⟨C1, _hC1, h1⟩ := t2SupF2_aPos
  obtain ⟨C0, _hC0, h0⟩ := t2SupF2_b_le_one
  obtain ⟨C2, _hC2, h2⟩ := h2
  refine ⟨2 * (C1 + C0 + C2) + 1, by positivity, ?_⟩
  intro α f hα hα1 hf b a hab z θ hz hθ hθ1
  have hWnn : 0 ≤ Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 2 f :=
    add_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) (coefTh_nonneg 2 f)
  have hCa : C1 ≤ 2 * (C1 + C0 + C2) + 1 := by linarith
  have hCb : C0 ≤ 2 * (C1 + C0 + C2) + 1 := by linarith
  have hCc : C2 ≤ 2 * (C1 + C0 + C2) + 1 := by linarith
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · subst ha0
    by_cases hb1 : b ≤ 1
    · exact le_trans
        (by simpa only [Work.Spaces.mixed_zero_right] using
          h0 α f hα hα1 hf b hb1 z θ hz hθ hθ1)
        (mul_le_mul_of_nonneg_right hCb hWnn)
    · have hb2 : b = 2 := by omega
      subst hb2
      exact le_trans
        (by simpa only [Work.Spaces.mixed_zero_right] using h2 α f hα hα1 hf z θ hz hθ hθ1)
        (mul_le_mul_of_nonneg_right hCc hWnn)
  · exact le_trans (h1 α f hα hα1 hf b a ha0 hab z θ hz hθ hθ1)
      (mul_le_mul_of_nonneg_right hCa hWnn)

end Work.FTS.TransportS
