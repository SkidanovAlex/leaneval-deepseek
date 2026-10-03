import Mathlib
import Submission.Work.KMTAreas.A7.fiberVarSamplingReduce
import Submission.Work.KMTAreas.iwEvenMultiplierGapUniform
import Submission.Work.KMTAreas.A7.fiberOpTex_eq_fiberOp_self_bdd
import Submission.Work.KMTAreas.A7.fiberOp_eq_finsetSynthesis
import Submission.Work.KMTAreas.A7.sublatticeShannonReproduction
import Submission.Work.KMTAreas.A7Hi.variationalNorm_tsum_le
import Submission.Work.KMTAreas.A7.cw_varphiNt_summable
namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-!
## The carrier-free slice decomposition of the fibre

For a finite set `A` of arithmetic frequencies, a profile `φ` and a sequence `f`, put

* `innerPiece φ f α z = ∑'_j fourier (-j) α * cw φ j * f (z - j)`  (the `α`-piece of the
  exact-height projection with profile `φ`), and
* `sliceInput A f y u = f u * (∑_{α ∈ A} fourier (y+u) α)`,
* `sliceSumm A φ f y z = ∑_{α ∈ A} fourier (y+z) α * innerPiece φ f α z`.

The point (KMT §8, the "tensor product structure") is that `sliceSumm A φ f y` **is a
convolution with the kernel `j ↦ cw φ j`** (so it is band limited to the support of `periodize φ`),
and that on the residue class `r` mod `q` (with `q • α = 0` for `α ∈ A`) the fibre
`fiberOp ρ l φ n₀ f` equals the slice `sliceSumm A φ f (n₀ - r)`; the slice whose index matches the
residue class `-c` is exactly the exact-height projection `Tex ρ l φ f` itself.
-/

/-- The `α`-piece of the exact-height projection with profile `φ`. -/
noncomputable def innerPiece (φ : ℝ → ℂ) (f : ℤ → ℂ) (α : Circ) (z : ℤ) : ℂ :=
  ∑' j : ℤ, fourier (T := 1) (-j) α * cw φ j * f (z - j)

/-- The input of the carrier-free slice: `f` modulated by the arithmetic character of the slice
index. -/
noncomputable def sliceInput (A : Finset Circ) (f : ℤ → ℂ) (y z : ℤ) : ℂ :=
  f z * (∑ α ∈ A, fourier (T := 1) (y + z) α)

/-- The carrier-free slice synthesis at the slice index `y`: the synthesis of the `α`-pieces with
the twist `fourier (y+z) α`.  It is band limited to the support of `periodize φ`. -/
noncomputable def sliceSumm (A : Finset Circ) (φ : ℝ → ℂ) (f : ℤ → ℂ) (y : ℤ) (z : ℤ) : ℂ :=
  ∑ α ∈ A, fourier (T := 1) (y + z) α * innerPiece φ f α z

/-- `fourier (T := 1) (q * y) α = 1` whenever `q • α = 0`. -/
lemma fourier_q_smul_eq_one {q : ℕ} {α : Circ} (h : q • α = 0) (y : ℤ) :
    fourier (T := 1) ((q : ℤ) * y) α = 1 := by
  have hq : ((q : ℤ)) • α = 0 := by simpa using h
  have hqc : α.toCircle ^ ((q : ℤ)) = 1 := by
    have h' := congrArg AddCircle.toCircle hq
    rw [AddCircle.toCircle_zsmul] at h'
    simpa using h'
  rw [fourier_apply, AddCircle.toCircle_zsmul, zpow_mul, hqc, one_zpow]
  simp

/-- The `α`-pieces are summable when `f` is bounded. -/
lemma summable_innerPiece {φ : ℝ → ℂ} (hφsum : Summable (fun j : ℤ => ‖cw φ j‖))
    {f : ℤ → ℂ} {B : ℝ} (hB : ∀ x : ℤ, ‖f x‖ ≤ B) (α : Circ) (z : ℤ) :
    Summable (fun j : ℤ => fourier (T := 1) (-j) α * cw φ j * f (z - j)) := by
  refine Summable.of_norm_bounded (hφsum.mul_right B) (fun j => ?_)
  have h1 : ‖fourier (T := 1) (-j) α‖ = 1 := by
    rw [fourier_apply]; exact Circle.norm_coe _
  calc ‖fourier (T := 1) (-j) α * cw φ j * f (z - j)‖
      = ‖cw φ j‖ * ‖f (z - j)‖ := by rw [mul_assoc, norm_mul, h1, one_mul, norm_mul]
    _ ≤ ‖cw φ j‖ * B := mul_le_mul_of_nonneg_left (hB (z - j)) (norm_nonneg _)

/-- The exact-height fibre is the synthesis of the `α`-pieces (`fiberOp_eq_finsetSynthesis`,
restated with `innerPiece`). -/
lemma fiberOp_eq_innerPiece (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ)
    (hφsum : Summable (fun j : ℤ => ‖cw φ j‖)) (f : ℤ → ℂ) (B : ℝ)
    (hB : ∀ x : ℤ, ‖f x‖ ≤ B) (n₀ : ℤ) (z : ℤ) :
    fiberOp ρ l φ n₀ f z
      = ∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) n₀ α * innerPiece φ f α z :=
  fiberOp_eq_finsetSynthesis ρ l φ hφsum f B hB n₀ z

/-- **The carrier-free slice form of the fibre.**  With `q • α = 0` for every `α ∈ A`, the fibre
at the residue `n₀` evaluated at a point of the residue class `r` is the carrier-free slice of
index `n₀ - r`. -/
lemma fiberOp_residue_eq_slice (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (q : ℕ)
    (hφsum : Summable (fun j : ℤ => ‖cw φ j‖)) (f : ℤ → ℂ) (B : ℝ)
    (hB : ∀ x : ℤ, ‖f x‖ ≤ B)
    (hq : ∀ α ∈ iwArithFreqsNew ρ l, q • α = 0) (n₀ r u : ℤ) :
    fiberOp ρ l φ n₀ f (q * u + r)
      = sliceSumm (iwArithFreqsNew ρ l) φ f (n₀ - r) (q * u + r) := by
  rw [fiberOp_eq_innerPiece ρ l φ hφsum f B hB n₀ (q * u + r), sliceSumm]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  have h1 : fourier (T := 1) (n₀ - r + (q * u + r)) α = fourier (T := 1) n₀ α := by
    have harg : n₀ - r + (q * u + r) = n₀ + (q : ℤ) * u := by ring
    rw [harg, fourier_add, fourier_q_smul_eq_one (hq α hα) u, mul_one]
  rw [h1]

/-- The carrier-free slice is a convolution with the kernel `j ↦ cw φ j`. -/
lemma sliceSumm_eq_conv (A : Finset Circ) (φ : ℝ → ℂ)
    (hφsum : Summable (fun j : ℤ => ‖cw φ j‖)) (f : ℤ → ℂ) (B : ℝ)
    (hB : ∀ x : ℤ, ‖f x‖ ≤ B) (y z : ℤ) :
    sliceSumm A φ f y z = ∑' j : ℤ, cw φ j * sliceInput A f y (z - j) := by
  have hsumm' : ∀ α ∈ A, Summable (fun j : ℤ =>
      fourier (T := 1) (y + (z - j)) α * cw φ j * f (z - j)) := by
    intro α _
    refine Summable.of_norm_bounded (hφsum.mul_right B) (fun j => ?_)
    have h1 : ‖fourier (T := 1) (y + (z - j)) α‖ = 1 := by
      rw [fourier_apply]; exact Circle.norm_coe _
    calc ‖fourier (T := 1) (y + (z - j)) α * cw φ j * f (z - j)‖
        = ‖cw φ j‖ * ‖f (z - j)‖ := by rw [mul_assoc, norm_mul, h1, one_mul, norm_mul]
      _ ≤ ‖cw φ j‖ * B := mul_le_mul_of_nonneg_left (hB (z - j)) (norm_nonneg _)
  have stepA : sliceSumm A φ f y z
      = ∑ α ∈ A, ∑' j : ℤ, fourier (T := 1) (y + (z - j)) α * cw φ j * f (z - j) := by
    rw [sliceSumm]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [innerPiece, ← tsum_mul_left]
    refine tsum_congr (fun j => ?_)
    have h1 : fourier (T := 1) (y + z) α * fourier (T := 1) (-j) α
        = fourier (T := 1) (y + (z - j)) α := by
      rw [← fourier_add]
      congr 1
      ring
    rw [← h1]
    ring
  rw [stepA, (Summable.tsum_finsetSum (s := A) hsumm').symm]
  refine tsum_congr (fun j => ?_)
  rw [sliceInput]
  rw [show (∑ x ∈ A, fourier (T := 1) (y + (z - j)) x * cw φ j * f (z - j))
        = (∑ x ∈ A, fourier (T := 1) (y + (z - j)) x) * (cw φ j * f (z - j)) by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun x _ => by ring)]
  ring

/-- `2 ^ (logN N) > N / 2` (the integer logarithm is a floor). -/
lemma two_pow_logN_gt (N : ℕ) :
    (N : ℝ) < (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) * 2 := by
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (max N 2)
  have hcast : (((max N 2 : ℕ)) : ℝ) < (2 : ℝ) ^ (Nat.log 2 (max N 2)) * 2 := by
    have h' : (((max N 2 : ℕ)) : ℝ) < (((2 : ℕ) ^ (Nat.log 2 (max N 2) + 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [pow_succ] using h'
  have hle : (N : ℝ) ≤ (((max N 2 : ℕ)) : ℝ) := by
    rw [Nat.cast_max]
    exact le_max_left _ _
  have hlog : ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) = ((Nat.log 2 (max N 2) : ℕ) : ℝ) := by
    rw [Work.Analysis.EndVar.logN]
    push_cast
    ring
  rw [hlog, Real.rpow_natCast]
  linarith

/-- The support of the modulated bump `φ_{N,t}` times `q` is at most `1/4`, as soon as the Farey
condition `8·2^{k₁}·q ≤ N` holds (`q ≥ 1`). -/
lemma varphiNt_support_mul_le (q : ℕ) (hq : 1 ≤ q) (k₁ N : ℕ) (t : ℝ)
    (hfarey : 8 * (2 : ℝ) ^ k₁ * (q : ℝ) ≤ (N : ℝ)) :
    ∀ ξ : ℝ, varphiNt N k₁ t ξ ≠ 0 → |ξ| * (q : ℝ) ≤ 1 / 4 := by
  intro ξ hξ
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℝ) < 8 * (2 : ℝ) ^ k₁ * (q : ℝ) := by positivity
    linarith
  have hlogpos : (0 : ℝ) < (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) := by positivity
  have hloglower : (N : ℝ) < (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) * 2 :=
    two_pow_logN_gt N
  have hfarey4 : 2 * (2 : ℝ) ^ k₁ * (q : ℝ) ≤ (N : ℝ) / 4 := by linarith
  by_cases hk : k₁ = 0
  · subst hk
    have hdef : varphiNt N 0 t ξ
        = Work.KMTContract.kmtEta (((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) * ξ)
          * ee ((N : ℝ) * t * ξ) := by
      rw [varphiNt, varphiN, if_pos rfl]
    have hne : Work.KMTContract.kmtEta
        (((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) * ξ) ≠ 0 := by
      intro h
      exact hξ (by rw [hdef, h, zero_mul])
    have hlt1 : ¬ (1 ≤ |((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) * ξ|) :=
      fun hc => hne (Work.KMTContract.kmtEta_zero hc)
    have hlt : (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) * |ξ| < 1 := by
      have := lt_of_not_ge hlt1
      rwa [abs_mul, abs_of_pos hlogpos] at this
    have habs : |ξ| < 1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) := by
      rw [lt_div_iff₀ hlogpos]
      rwa [mul_comm] at hlt
    have hstep : (1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) * (q : ℝ) ≤ 1 / 4 := by
      have h1 : 1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) ≤ 2 / (N : ℝ) := by
        rw [div_le_div_iff₀ hlogpos hNpos]
        nlinarith [hloglower]
      have h2 : (2 / (N : ℝ)) * (q : ℝ) ≤ 1 / 4 := by
        have h8 : 8 * (q : ℝ) ≤ (N : ℝ) := by simpa using hfarey
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hNpos (by norm_num : (0:ℝ) < 4)]
        linarith
      exact le_trans (mul_le_mul_of_nonneg_right h1 hqR.le) h2
    calc |ξ| * (q : ℝ) ≤ (1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) * (q : ℝ) :=
          mul_le_mul_of_nonneg_right (le_of_lt habs) hqR.le
      _ ≤ 1 / 4 := hstep
  · have hk1 : 1 ≤ k₁ := by omega
    have hsupp := varphiNt_support_le k₁ hk1 N t ξ hξ
    have hkey : (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) * (q : ℝ) ≤ 1 / 4 := by
      have h2 : (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) * (q : ℝ)
          ≤ (2 * (2 : ℝ) ^ k₁ / (N : ℝ)) * (q : ℝ) := by
        have h3 : (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
            < 2 * (2 : ℝ) ^ k₁ / (N : ℝ) := by
          rw [Real.rpow_sub (by norm_num : (0:ℝ) < 2), Real.rpow_natCast,
            div_lt_div_iff₀ hlogpos hNpos]
          have hmul : (2 : ℝ) ^ k₁ * (N : ℝ)
              < (2 : ℝ) ^ k₁ * ((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) * 2) :=
            mul_lt_mul_of_pos_left hloglower (by positivity)
          calc (2 : ℝ) ^ k₁ * (N : ℝ)
              < (2 : ℝ) ^ k₁ * ((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) * 2) := hmul
            _ = 2 * (2 : ℝ) ^ k₁ * (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) := by ring
        exact mul_le_mul_of_nonneg_right (le_of_lt h3) hqR.le
      have h3 : (2 * (2 : ℝ) ^ k₁ / (N : ℝ)) * (q : ℝ) ≤ 1 / 4 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hNpos (by norm_num : (0:ℝ) < 4)]
        nlinarith [hfarey]
      linarith
    exact le_trans (mul_le_mul_of_nonneg_right hsupp hqR.le) hkey

/-- The support of `φ_{N,t}` in the form needed for the band hypothesis: `|ξ| ≤ 1/(4q)`. -/
lemma varphiNt_support_le_quarter (q : ℕ) (hq : 1 ≤ q) (k₁ N : ℕ) (t : ℝ)
    (hfarey : 8 * (2 : ℝ) ^ k₁ * (q : ℝ) ≤ (N : ℝ)) :
    ∀ ξ : ℝ, varphiNt N k₁ t ξ ≠ 0 → |ξ| ≤ 1 / (4 * (q : ℝ)) := by
  intro ξ hξ
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h := varphiNt_support_mul_le q hq k₁ N t hfarey ξ hξ
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- **Step 1 of the assembly (bounded `f`).**  The fibre of the wide cut `mStarF U` applied to the
`S`-clipped exact-height projection is the `S`-clipped exact-height fibre
(`fiberOpTex_eq_fiberOp_self_bdd` plus the fact that the fibre of the zero sequence vanishes). -/
lemma fiberOp_mStarF_Sclip (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l₁ U : ℕ) (hU : 1 ≤ U)
    (hna : NonAliasing (-(2 * (U : ℤ))) (iwArithFreqsNew ρ l₁))
    (φ : ℝ → ℂ) (hφ : MeasureTheory.Integrable φ)
    (hφsum : Summable (fun j : ℤ => ‖cw φ j‖))
    (hφsupp : ∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1))
    (f : ℤ → ℂ) (B : ℝ) (hB : ∀ x : ℤ, ‖f x‖ ≤ B) (S : Prop) [Decidable S] (n₀ : ℤ) :
    fiberOp ρ l₁ (mStarF U) n₀ (if S then Tex ρ l₁ φ f else 0)
      = if S then fiberOp ρ l₁ φ n₀ f else 0 := by
  by_cases hS : S
  · rw [if_pos hS, if_pos hS]
    exact fiberOpTex_eq_fiberOp_self_bdd ρ hρ hρ1 l₁ U hU hna φ hφ hφsum hφsupp f B hB n₀
  · rw [if_neg hS, if_neg hS]
    funext y
    simp only [fiberOp, Pi.zero_apply, mul_zero, tsum_zero]

end

end Work.KMTAreas.A7


