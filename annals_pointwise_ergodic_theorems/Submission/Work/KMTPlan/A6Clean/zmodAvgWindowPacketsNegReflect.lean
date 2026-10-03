/-
# The `ZMod Q` presentation of the twisted bilinear multiplier via window packets

This module proves the **algebraic core** of the packet construction of
`Work.KMTPlan.A6Clean.PacketProfile`: the identity

  `zmodAvg (negReflect P) Q u v (x mod Q) = Btwist ρ P l₁ l₂ m₁ m₂ h k x`

for the canonical *packet profiles* of the two model inputs `h` and `k`, whose value at a residue
`θ : ZMod Q` is the Fourier synthesis of the **window pieces**

  `winPieceR m v α = winConvR m (winModR (-α) v)`

at the arithmetic frequencies `α ∈ iwArithFreqs ρ l`, with the character `e(-θ.val · α)` of `ZMod Q`.

Here `Q = arithQ ρ (max l₁ l₂)` is a common denominator of all arithmetic frequencies of height
`≤ 2^{l₁}`, `≤ 2^{l₂}` (so the characters are `Q`-periodic and may be evaluated at the
representative `θ.val`), and `negReflect P = -P(-X)` turns the *plus-sign* averaging operator
`zmodAvg P Q u v θ = Q⁻¹ ∑_{y<Q} u(θ+y) v(θ+P(y))` into the paper's *minus-sign* arithmetic
average `A_Ẑ(u,v) = Q⁻¹ ∑_y u(x-y) v(x-P(y))` (the bridge `Work.KMTPlan.A6.ZModAvgNegBridge`).

## The proof

Everything is a reindexing.  Writing `Q = arithQ ρ (max l₁ l₂)` and `x̂ = (x : ZMod Q)`,

  `zmodAvg (negReflect P) Q u v x̂ = Q⁻¹ ∑_{y : ZMod Q} u (x̂ - y) · v (x̂ - P(y))`,

and the profile value `u (x̂ - y)` is `∑_α e(-(x - y.val)α)·winPieceR m₁ h α x` — this is where the
periodicity of the characters enters: `-((x̂ - y).val) ≡ y.val - x (mod Q)` and the character is
invariant under adding multiples of `Q` (`fourier_neg_val_eq` below).  Summing back over the residues
`n₀ = y.val ∈ {0, …, Q-1}` (`Work.KMTPlan.A6.sum_range_cast_zmod`) and multiplying out gives

  `Q⁻¹ ∑_{n₀ < Q} (∑_{α∈A₁} e((n₀-x)α)·winPieceR m₁ h α x)·(∑_{β∈A₂} e((P(n₀)-x)β)·winPieceR m₂ k β x)`,

which is exactly `Btwist` by the fibre factorisation `Work.KMTAreas.A7.Btwist_eq_fiberSum` together
with the window-piece decomposition of a single fibre
`Work.KMTPlan.A6Clean.fiberOpSet_eq_windowPieceR` (and its twisted variant proved below).
-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.PacketProfile
import Submission.Work.KMTPlan.A6.ZModAvgNegBridge

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.KMTPlan.A6Clean

open MeasureTheory Polynomial Finset
open scoped BigOperators

noncomputable section

/-- **The character of `(ℚ/ℤ)_{≤l}` evaluated at a residue depends only on the residue.**  If
`n : ℤ` and `a : ZMod (arithQ ρ L)` are congruent, then `e(-(a.val)α) = e(-n α)` for every
height-`≤ l` frequency `α`, `l ≤ L`. -/
theorem fourier_neg_val_eq {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l L : ℕ} (hl : l ≤ L)
    {α : Work.Analysis.IonescuWainger.Circle}
    (hα : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l) (n : ℤ)
    (a : ZMod (Work.KMTAreas.A7.arithQ ρ L))
    (ha : ((n : ℤ) : ZMod (Work.KMTAreas.A7.arithQ ρ L)) = a) :
    fourier (T := 1) (-(a.val : ℤ)) α = fourier (T := 1) (-n) α := by
  haveI hNZ : NeZero (Work.KMTAreas.A7.arithQ ρ L) :=
    ⟨Nat.pos_iff_ne_zero.mp (Work.KMTAreas.A7.arithQ_pos ρ L)⟩
  have haval : (((a.val : ℤ)) : ZMod (Work.KMTAreas.A7.arithQ ρ L))
      = ((n : ℤ) : ZMod (Work.KMTAreas.A7.arithQ ρ L)) := by
    rw [ha]; simp
  have hdvd : (((Work.KMTAreas.A7.arithQ ρ L : ℕ)) : ℤ) ∣ n - (a.val : ℤ) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (a.val : ℤ) n (Work.KMTAreas.A7.arithQ ρ L)).mp haval
  obtain ⟨k, hk⟩ := hdvd
  have h : -(a.val : ℤ) = -n + k * (((Work.KMTAreas.A7.arithQ ρ L : ℕ)) : ℤ) := by
    have hk' := hk
    ring_nf at hk' ⊢
    linarith [hk']
  rw [h, fourier_add, Work.KMTPlan.A6Clean.fourier_mul_arithQ_eq_one hρ hρ1 hl hα k, mul_one]

/-- **The window-piece decomposition of the *twisted* arithmetic fibre**
`fiberOpPSet P A m n₀ v = fiberOpSet A m (P.eval n₀) v`: the twisted fibre is the ordinary fibre at
the shifted residue `P.eval n₀`, so `fiberOpSet_eq_windowPieceR` applies verbatim. -/
theorem fiberOpPSet_eq_windowPieceR (P : Polynomial ℤ)
    (A : Finset Work.Analysis.IonescuWainger.Circle) (m : ℝ → ℂ) (n₀ : ℤ) (v : ℤ → ℂ) (x : ℤ)
    (hsum : Summable (fun j : ℤ => Work.KMTAreas.A7.cw m j * v (x - j))) :
    Work.KMTAreas.A7.fiberOpPSet P A m n₀ v x
      = ∑ α ∈ A, fourier (T := 1) (P.eval n₀ - x) α * winPieceR m v α x :=
  fiberOpSet_eq_windowPieceR A m (P.eval n₀) v x hsum

/-- **The `ZMod Q` average of two packet profiles is the explicit residue sum.**  For arbitrary
"amplitudes" `p₁`, `p₂` of the two packet families, the `zmodAvg (negReflect P)`-average of the
profiles `θ ↦ ∑_{α ∈ (ℚ/ℤ)_{≤l₁}} e(-θ.val·α) p₁ α` and `θ ↦ ∑_{β ∈ (ℚ/ℤ)_{≤l₂}} e(-θ.val·β) p₂ β`
equals the double character sum over the residues `n₀ < Q`,

  `Q⁻¹ ∑_{n₀<Q} (∑_{α∈A₁} e((n₀-x)α) p₁ α)·(∑_{β∈A₂} e((P(n₀)-x)β) p₂ β)`,  `Q = arithQ ρ (max l₁ l₂)`.

This is the reindexed form of the fibre factorisation: the substitution `y ↦ -y` (which is what
`negReflect` accounts for) turns `P(-y)` into `P(n₀)`. -/
theorem zmodAvg_windowPackets_profile (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (P : Polynomial ℤ) (l₁ l₂ : ℕ)
    (p₁ p₂ : Work.Analysis.IonescuWainger.Circle → ℂ) (x : ℤ) :
    Work.KMTPlan.A6.zmodAvg (Work.KMTPlan.A6.negReflect P)
        (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
        (fun θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) =>
          ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
            fourier (T := 1) (-(θ.val : ℤ)) α * p₁ α)
        (fun θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) =>
          ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
            fourier (T := 1) (-(θ.val : ℤ)) β * p₂ β)
        ((x : ℤ) : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)))
      = ((Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℕ) : ℂ)⁻¹ *
          ∑ n₀ ∈ Finset.range (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
            (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
                fourier (T := 1) (n₀ - x) α * p₁ α)
              * (∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
                fourier (T := 1) (P.eval (n₀ : ℤ) - x) β * p₂ β) := by
  haveI hNZ : NeZero (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) :=
    ⟨Nat.pos_iff_ne_zero.mp (Work.KMTAreas.A7.arithQ_pos ρ (max l₁ l₂))⟩
  -- The character of a shifted residue, in terms of the representative `y.val`.
  have hU : ∀ y : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
      (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
          fourier (T := 1) (-(((((x : ℤ) : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)))
            - y).val : ℕ) : ℤ)) α * p₁ α)
        = ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
            fourier (T := 1) ((y.val : ℤ) - x) α * p₁ α := by
    intro y
    refine Finset.sum_congr rfl (fun α hα => ?_)
    have ha : (((x - (y.val : ℤ)) : ℤ) : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)))
        = ((x : ℤ) : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))) - y := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [fourier_neg_val_eq (L := max l₁ l₂) hρ hρ1 (le_max_left l₁ l₂) hα (x - (y.val : ℤ))
      (((x : ℤ) : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))) - y) ha]
    congr 1
    ring_nf
  -- The same for the twisted residue `P(y)`.
  have hV : ∀ y : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
      (∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
          fourier (T := 1) (-(((((x : ℤ) : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)))
            - Work.Analysis.Concentration.polyEvalZMod P
                (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) y).val : ℕ) : ℤ)) β * p₂ β)
        = ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
            fourier (T := 1) (P.eval (y.val : ℤ) - x) β * p₂ β := by
    intro y
    have hpoly : Work.Analysis.Concentration.polyEvalZMod P
          (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) y
        = ((P.eval (y.val : ℤ) : ℤ) : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))) := by
      have hy : y = (((y.val : ℕ) : ℤ) : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))) := by
        rw [← ZMod.natCast_zmod_val (n := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) y]
        simp
      conv_lhs => rw [hy]
      exact Work.KMTPlan.A6.polyEvalZMod_intCast P
        (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) (y.val : ℤ)
    refine Finset.sum_congr rfl (fun β hβ => ?_)
    have ha : (((x - P.eval (y.val : ℤ)) : ℤ) : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)))
        = ((x : ℤ) : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)))
            - Work.Analysis.Concentration.polyEvalZMod P
                (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) y := by
      rw [hpoly]
      push_cast
      ring
    rw [fourier_neg_val_eq (L := max l₁ l₂) hρ hρ1 (le_max_right l₁ l₂) hβ (x - P.eval (y.val : ℤ))
      (((x : ℤ) : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)))
        - Work.Analysis.Concentration.polyEvalZMod P
            (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) y) ha]
    congr 1
    ring_nf
  -- Reindex `y : ZMod Q` by the residues `n₀ = y.val < Q`.
  have hreindex : (∑ y : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
        (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
            fourier (T := 1) ((y.val : ℤ) - x) α * p₁ α)
          * (∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
            fourier (T := 1) (P.eval (y.val : ℤ) - x) β * p₂ β))
      = ∑ n₀ ∈ Finset.range (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
          (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
              fourier (T := 1) (n₀ - x) α * p₁ α)
            * (∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
              fourier (T := 1) (P.eval (n₀ : ℤ) - x) β * p₂ β) := by
    rw [← Work.KMTPlan.A6.sum_range_cast_zmod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
      (fun z : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) =>
        (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
            fourier (T := 1) ((z.val : ℤ) - x) α * p₁ α)
          * (∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
            fourier (T := 1) (P.eval (z.val : ℤ) - x) β * p₂ β))]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hy)]
  -- The bridge to the minus-sign average, then the two reindexings.
  rw [Work.KMTPlan.A6.ZModAvgNegBridge P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) _ _]
  simp only [Work.Analysis.Concentration.polyBilinearAverageZMod,
    Work.Analysis.Concentration.polyEvalZMod_X]
  congr 1
  calc (∑ y : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
        (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
            fourier (T := 1) (-(((((x : ℤ) : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)))
              - y).val : ℕ) : ℤ)) α * p₁ α)
          * (∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
            fourier (T := 1) (-(((((x : ℤ) : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)))
              - Work.Analysis.Concentration.polyEvalZMod P
                  (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) y).val : ℕ) : ℤ)) β * p₂ β))
      = ∑ y : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
        (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
            fourier (T := 1) ((y.val : ℤ) - x) α * p₁ α)
          * (∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
            fourier (T := 1) (P.eval (y.val : ℤ) - x) β * p₂ β) :=
        Finset.sum_congr rfl (fun y _ => by rw [hU y, hV y])
    _ = _ := hreindex

/-- **The arithmetic character is bounded by the number of frequencies.** -/
theorem norm_arithChar_le (ρ : ℝ) (l : ℕ) (y : ℤ) :
    ‖Work.KMTAreas.A7.arithChar ρ l y‖
      ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) := by
  rw [Work.KMTAreas.A7.arithChar]
  calc ‖∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l, (fourier (T := 1) y) α‖
      ≤ ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l, ‖(fourier (T := 1) y) α‖ :=
        norm_sum_le _ _
    _ = ∑ _α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun α _ => ?_)
        rw [Work.KMTAreas.A7.norm_fourier_applyR]
    _ = _ := by simp

theorem zmodAvgWindowPacketsNegReflect (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) (h k : ℤ → ℂ) (x : ℤ)
    (hsum₁ : Summable (fun j : ℤ => Work.KMTAreas.A7.cw m₁ j * h (x - j)))
    (hsum₂ : Summable (fun j : ℤ => Work.KMTAreas.A7.cw m₂ j * k (x - j))) :
    Work.KMTPlan.A6.zmodAvg (Work.KMTPlan.A6.negReflect P)
        (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
        (fun θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) =>
          ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
            fourier (T := 1) (-(θ.val : ℤ)) α
              * Work.KMTAreas.A7.winConvR m₁ (Work.KMTAreas.A7.winModR (-α) h) x)
        (fun θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) =>
          ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
            fourier (T := 1) (-(θ.val : ℤ)) β
              * Work.KMTAreas.A7.winConvR m₂ (Work.KMTAreas.A7.winModR (-β) k) x)
        ((x : ℤ) : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)))
      = Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ h k x := by
  -- The fibre families of `Btwist_eq_fiberSum` are summable, being bounded multiples of `hsum`.
  have h₁ : ∀ n₀ : ℤ, Summable (fun j : ℤ =>
      Work.KMTAreas.A7.arithChar ρ l₁ (n₀ - j) * Work.KMTAreas.A7.cw m₁ j * h (x - j)) := by
    intro n₀
    refine Summable.of_norm_bounded
      (hsum₁.norm.mul_left ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ))
      (fun j => ?_)
    have hb := norm_arithChar_le ρ l₁ (n₀ - j)
    have h2 : (0 : ℝ) ≤ ‖Work.KMTAreas.A7.cw m₁ j‖ * ‖h (x - j)‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc ‖Work.KMTAreas.A7.arithChar ρ l₁ (n₀ - j) * Work.KMTAreas.A7.cw m₁ j * h (x - j)‖
        = ‖Work.KMTAreas.A7.arithChar ρ l₁ (n₀ - j)‖
            * (‖Work.KMTAreas.A7.cw m₁ j‖ * ‖h (x - j)‖) := by
          rw [norm_mul, norm_mul]; ring
      _ ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
            * (‖Work.KMTAreas.A7.cw m₁ j‖ * ‖h (x - j)‖) :=
          mul_le_mul_of_nonneg_right hb h2
      _ = ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
            * ‖Work.KMTAreas.A7.cw m₁ j * h (x - j)‖ := by rw [norm_mul]
  have h₂ : ∀ n₀ : ℤ, Summable (fun j : ℤ =>
      Work.KMTAreas.A7.arithChar ρ l₂ (P.eval n₀ - j) * Work.KMTAreas.A7.cw m₂ j * k (x - j)) := by
    intro n₀
    refine Summable.of_norm_bounded
      (hsum₂.norm.mul_left ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ))
      (fun j => ?_)
    have hb := norm_arithChar_le ρ l₂ (P.eval n₀ - j)
    have h2 : (0 : ℝ) ≤ ‖Work.KMTAreas.A7.cw m₂ j‖ * ‖k (x - j)‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc ‖Work.KMTAreas.A7.arithChar ρ l₂ (P.eval n₀ - j) * Work.KMTAreas.A7.cw m₂ j * k (x - j)‖
        = ‖Work.KMTAreas.A7.arithChar ρ l₂ (P.eval n₀ - j)‖
            * (‖Work.KMTAreas.A7.cw m₂ j‖ * ‖k (x - j)‖) := by
          rw [norm_mul, norm_mul]; ring
      _ ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ)
            * (‖Work.KMTAreas.A7.cw m₂ j‖ * ‖k (x - j)‖) :=
          mul_le_mul_of_nonneg_right hb h2
      _ = ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ)
            * ‖Work.KMTAreas.A7.cw m₂ j * k (x - j)‖ := by rw [norm_mul]
  -- The explicit residue form of the left-hand side.
  rw [zmodAvg_windowPackets_profile ρ hρ hρ1 P l₁ l₂
      (fun α => Work.KMTAreas.A7.winConvR m₁ (Work.KMTAreas.A7.winModR (-α) h) x)
      (fun β => Work.KMTAreas.A7.winConvR m₂ (Work.KMTAreas.A7.winModR (-β) k) x) x]
  -- The fibre factorisation of `Btwist`.
  rw [Work.KMTAreas.A7.Btwist_eq_fiberSum ρ P l₁ l₂ m₁ m₂ h k x h₁ h₂]
  congr 1
  refine Finset.sum_congr rfl (fun n₀ _ => ?_)
  rw [fiberOpSet_eq_windowPieceR (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁) m₁ (n₀ : ℤ) h x
        hsum₁,
      fiberOpPSet_eq_windowPieceR P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) m₂ (n₀ : ℤ) k x
        hsum₂]
  simp only [winPieceR]

end

end Work.KMTPlan.A6Clean
