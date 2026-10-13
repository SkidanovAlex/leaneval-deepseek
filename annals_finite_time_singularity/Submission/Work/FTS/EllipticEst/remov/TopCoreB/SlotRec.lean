import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.CleanBase
import Submission.Work.FTS.EllipticEst.remov.Baux.PthSlotPointwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TopCoreB/SlotRec`: the pointwise `∂_θ`-slot recursions

Two purely pointwise inequalities comparing the *plain* angular derivatives `∂_θ^mf` (with
their natural weights `sin(2θ)^{2m-γ}` resp. `sin(2θ)^{2m-4-γ}`) to the *`D_θ`-slots*
`D_θ^tf` (with the weight `sin(2θ)^{-γ}` of the `ℋ^k`-norm).

* `slotRecStep` / `slotRecAll` — the *unshifted* recursion
  `(∂_θ^mf)²·σ^{2m-γ} ≤ C_m Σ_{t≤m} (D_θ^tf)²·σ^{-γ}`,
  used for the *source* functions (`F`, `z²∂_zzΨ`, `D_z(∂_θθΨ)`), whose natural weight in the
  `ℋ^k`-norm is the slot weight `σ^{-γ}`.
* `slotRecShiftAll` — the *shifted* recursion
  `(∂_θ^mf)²·σ^{2m-4-γ} ≤ C_m Σ_{i<m-1} (D_θ^i(∂_θθf))²·σ^{-γ}`,
  used for `Ψ` itself: its low slots are not controlled by the hypotheses, but its second
  derivative `B = ∂_θθΨ` is.

Both are proved by strong induction on `m` from the *reverse expansions*
`Work.FTS.EllipticEst.remov.reverse_expansion_2d` (resp. `..._top`) of
`remov/DthIter_expansion`, via the pointwise algebra `slotRecStep` (resp.
`Baux.PthSlotPointwise`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false
set_option linter.unusedSimpArgs false

theorem sin_two_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- Nonnegativity of the `D_θ`-slot integrand at an interior angle. -/
theorem slotTerm_nonneg (γ : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (g : ℝ) : 0 ≤ g ^ 2 * (Real.sin (2 * θ)) ^ (-γ) :=
  mul_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos (sin_two_pos_of_Ioo hθ) _))

/-- **The pointwise step of the unshifted slot recursion.**  From the reverse expansion at
order `m` (`hrev`) one gets

  `(∂_θ^mf)²·σ^{2m-γ} ≤ 2K²(m+1)·((D_θ^mf)²σ^{-γ} + Σ_{r<m}(∂_θ^rf)²σ^{2r-γ})`.

The factor `(m+1)` is Cauchy–Schwarz for the `m+1` terms of the reverse expansion. -/
theorem slotRecStep (γ : ℝ) (m : ℕ) (K : ℝ) (hK : 0 < K) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hrev : |Real.sin (2 * θ)| ^ m * |Work.Spaces.pthIter m f z θ|
      ≤ K * (|Work.Spaces.DthIter m f z θ|
        + ∑ r ∈ Finset.range m,
            |Real.sin (2 * θ)| ^ r * |Work.Spaces.pthIter r f z θ|)) :
    (Work.Spaces.pthIter m f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - γ)
      ≤ 2 * K ^ 2 * ((m : ℝ) + 1)
        * (((Work.Spaces.DthIter m f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
          + ∑ r ∈ Finset.range m,
              (Work.Spaces.pthIter r f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - γ)) := by
  set s : ℝ := Real.sin (2 * θ) with hsdef
  have hs : 0 < s := sin_two_pos_of_Ioo hθ
  have hsabs : ∀ r : ℕ, |s| ^ r = s ^ r := fun r => by rw [abs_of_pos hs]
  set S : ℝ := ∑ r ∈ Finset.range m, s ^ r * |Work.Spaces.pthIter r f z θ| with hSdef
  have hrev' : s ^ m * |Work.Spaces.pthIter m f z θ| ≤ K * (|Work.Spaces.DthIter m f z θ| + S) := by
    have h := hrev
    simp only [hsabs] at h
    rw [← hSdef] at h
    exact h
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  have hstep1 : (s ^ m) ^ 2 * (Work.Spaces.pthIter m f z θ) ^ 2
      ≤ K ^ 2 * (|Work.Spaces.DthIter m f z θ| + S) ^ 2 := by
    have h := pow_le_pow_left₀
      (by positivity : (0 : ℝ) ≤ s ^ m * |Work.Spaces.pthIter m f z θ|) hrev' 2
    simp only [mul_pow, sq_abs] at h
    exact h
  have hBS : (|Work.Spaces.DthIter m f z θ| + S) ^ 2
      ≤ 2 * ((Work.Spaces.DthIter m f z θ) ^ 2 + S ^ 2) := by
    nlinarith [sq_nonneg (|Work.Spaces.DthIter m f z θ| - S),
      sq_abs (Work.Spaces.DthIter m f z θ), abs_nonneg (Work.Spaces.DthIter m f z θ)]
  set Sig : ℝ := ∑ r ∈ Finset.range m,
    (s ^ r) ^ 2 * (Work.Spaces.pthIter r f z θ) ^ 2 with hSigdef
  have hSig_nn : 0 ≤ Sig := by
    rw [hSigdef]; exact Finset.sum_nonneg fun r _ => by positivity
  have hCS : S ^ 2 ≤ (m : ℝ) * Sig := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range m)
      (f := fun r => s ^ r * |Work.Spaces.pthIter r f z θ|)
    have h2 : (∑ r ∈ Finset.range m, (s ^ r * |Work.Spaces.pthIter r f z θ|) ^ 2) = Sig := by
      rw [hSigdef]
      exact Finset.sum_congr rfl fun r _ => by rw [mul_pow, sq_abs]
    rw [← hSdef, h2] at h
    simpa only [Finset.card_range] using h
  have hcore : (s ^ m) ^ 2 * (Work.Spaces.pthIter m f z θ) ^ 2
      ≤ 2 * K ^ 2 * ((m : ℝ) + 1)
        * ((Work.Spaces.DthIter m f z θ) ^ 2 + Sig) := by
    have h1 : K ^ 2 * (|Work.Spaces.DthIter m f z θ| + S) ^ 2
        ≤ K ^ 2 * (2 * ((Work.Spaces.DthIter m f z θ) ^ 2 + S ^ 2)) :=
      mul_le_mul_of_nonneg_left hBS hK2
    have h2 : K ^ 2 * (2 * ((Work.Spaces.DthIter m f z θ) ^ 2 + S ^ 2))
        ≤ 2 * K ^ 2 * ((Work.Spaces.DthIter m f z θ) ^ 2 + (m : ℝ) * Sig) := by
      nlinarith [hCS, hK2]
    have h3 : 2 * K ^ 2 * ((Work.Spaces.DthIter m f z θ) ^ 2 + (m : ℝ) * Sig)
        ≤ 2 * K ^ 2 * (((m : ℝ) + 1) * ((Work.Spaces.DthIter m f z θ) ^ 2 + Sig)) := by
      have hb : (Work.Spaces.DthIter m f z θ) ^ 2 + (m : ℝ) * Sig
          ≤ ((m : ℝ) + 1) * ((Work.Spaces.DthIter m f z θ) ^ 2 + Sig) := by
        nlinarith [hSig_nn, sq_nonneg (Work.Spaces.DthIter m f z θ)]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    calc (s ^ m) ^ 2 * (Work.Spaces.pthIter m f z θ) ^ 2
        ≤ K ^ 2 * (|Work.Spaces.DthIter m f z θ| + S) ^ 2 := hstep1
      _ ≤ K ^ 2 * (2 * ((Work.Spaces.DthIter m f z θ) ^ 2 + S ^ 2)) := h1
      _ ≤ 2 * K ^ 2 * ((Work.Spaces.DthIter m f z θ) ^ 2 + (m : ℝ) * Sig) := h2
      _ ≤ 2 * K ^ 2 * (((m : ℝ) + 1) * ((Work.Spaces.DthIter m f z θ) ^ 2 + Sig)) := h3
      _ = 2 * K ^ 2 * ((m : ℝ) + 1)
            * ((Work.Spaces.DthIter m f z θ) ^ 2 + Sig) := by ring
  have hpowL : s ^ (2 * (m : ℝ) - γ) = (s ^ m) ^ 2 * s ^ (-γ) := by
    have e1 : s ^ (2 * (m : ℝ)) = (s ^ m) ^ 2 := by
      have h1 : s ^ ((m : ℝ) * (2 : ℝ)) = (s ^ m) ^ (2 : ℝ) :=
        Real.rpow_natCast_mul (le_of_lt hs) m 2
      have h2 : (s ^ m) ^ (2 : ℝ) = (s ^ m) ^ (2 : ℕ) := Real.rpow_natCast _ 2
      rw [show 2 * (m : ℝ) = (m : ℝ) * 2 by ring, h1, h2]
    rw [show 2 * (m : ℝ) - γ = 2 * (m : ℝ) + (-γ) by ring, Real.rpow_add hs, e1]
  have hpowR : ∀ r : ℕ, s ^ (2 * (r : ℝ) - γ) = (s ^ r) ^ 2 * s ^ (-γ) := by
    intro r
    have e1 : s ^ (2 * (r : ℝ)) = (s ^ r) ^ 2 := by
      have h1 : s ^ ((r : ℝ) * (2 : ℝ)) = (s ^ r) ^ (2 : ℝ) :=
        Real.rpow_natCast_mul (le_of_lt hs) r 2
      have h2 : (s ^ r) ^ (2 : ℝ) = (s ^ r) ^ (2 : ℕ) := Real.rpow_natCast _ 2
      rw [show 2 * (r : ℝ) = (r : ℝ) * 2 by ring, h1, h2]
    rw [show 2 * (r : ℝ) - γ = 2 * (r : ℝ) + (-γ) by ring, Real.rpow_add hs, e1]
  have key := mul_le_mul_of_nonneg_right hcore (le_of_lt (Real.rpow_pos_of_pos hs (-γ)))
  have hexp : (2 * K ^ 2 * ((m : ℝ) + 1)
        * ((Work.Spaces.DthIter m f z θ) ^ 2 + Sig)) * s ^ (-γ)
      = 2 * K ^ 2 * ((m : ℝ) + 1)
          * ((Work.Spaces.DthIter m f z θ) ^ 2 * s ^ (-γ)
            + ∑ r ∈ Finset.range m,
                (Work.Spaces.pthIter r f z θ) ^ 2 * s ^ (2 * (r : ℝ) - γ)) := by
    rw [hSigdef]
    simp only [hpowR]
    rw [show (∑ r ∈ Finset.range m,
            (Work.Spaces.pthIter r f z θ) ^ 2 * ((s ^ r) ^ 2 * s ^ (-γ)))
          = (∑ r ∈ Finset.range m,
              (Work.Spaces.pthIter r f z θ) ^ 2 * (s ^ r) ^ 2) * s ^ (-γ) from by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun r _ => by ring]
    ring
  have hgoalL : Work.Spaces.pthIter m f z θ ^ 2 * s ^ (2 * (m : ℝ) - γ)
      = (s ^ m) ^ 2 * Work.Spaces.pthIter m f z θ ^ 2 * s ^ (-γ) := by
    rw [hpowL]; ring
  have hgoalR : 2 * K ^ 2 * ((m : ℝ) + 1)
        * (Work.Spaces.DthIter m f z θ ^ 2 * s ^ (-γ)
          + ∑ r ∈ Finset.range m,
              (Work.Spaces.pthIter r f z θ) ^ 2 * s ^ (2 * (r : ℝ) - γ))
      = (2 * K ^ 2 * ((m : ℝ) + 1) * (Work.Spaces.DthIter m f z θ ^ 2 + Sig)) * s ^ (-γ) :=
    hexp.symm
  rw [hgoalL, hgoalR]
  exact key

/-- **The unshifted slot recursion, for all orders up to `M` at once.**  There is `C > 0` with

  `(∂_θ^mf)²·σ^{2m-γ} ≤ C Σ_{t≤m} (D_θ^tf)²·σ^{-γ}`   for all `m ≤ M`,

on the open angular interval, for `f` smooth on the open quadrant. -/
theorem slotRecAll (γ : ℝ) (M : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ m : ℕ, m ≤ M → ∀ (f : ℝ → ℝ → ℝ) (z θ : ℝ),
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry f) (z, θ)) →
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pthIter m f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - γ)
        ≤ C * ∑ t ∈ Finset.range (m + 1),
            (Work.Spaces.DthIter t f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) := by
  induction M with
  | zero =>
      refine ⟨1, one_pos, fun m hm f z θ _ hθ => ?_⟩
      obtain rfl : m = 0 := Nat.le_zero.mp hm
      have hgoal : Work.Spaces.pthIter 0 f z θ ^ 2
            * Real.sin (2 * θ) ^ (2 * ((0 : ℕ) : ℝ) - γ)
          = ∑ t ∈ Finset.range 1,
              (Work.Spaces.DthIter t f z θ) ^ 2 * Real.sin (2 * θ) ^ (-γ) := by
        rw [Finset.sum_range_one, Work.Spaces.pthIter_zero, Work.Spaces.DthIter_zero,
          Nat.cast_zero, mul_zero, zero_sub]
      rw [hgoal, one_mul]
  | succ M ih =>
      obtain ⟨C₀, hC₀pos, hC₀⟩ := ih
      obtain ⟨K, hKpos, hK⟩ := revExp2d (M + 1)
      set Cnew : ℝ := 2 * K ^ 2 * ((M : ℝ) + 2) * (1 + ((M : ℝ) + 1) * C₀) with hCnewdef
      have hCnewpos : 0 < Cnew := by
        rw [hCnewdef]
        have h1 : (0 : ℝ) < 1 + ((M : ℝ) + 1) * C₀ := by
          have : (0 : ℝ) ≤ ((M : ℝ) + 1) * C₀ := by positivity
          linarith
        positivity
      refine ⟨max C₀ Cnew, lt_max_of_lt_left hC₀pos, fun m hm f z θ hf hθ => ?_⟩
      rcases Nat.lt_or_ge m (M + 1) with hlt | hge
      · refine le_trans (hC₀ m (by omega) f z θ hf hθ)
          (mul_le_mul_of_nonneg_right (le_max_left C₀ Cnew)
            (Finset.sum_nonneg fun t _ => slotTerm_nonneg γ hθ _))
      · obtain rfl : m = M + 1 := by omega
        have hstep := slotRecStep γ (M + 1) K hKpos f z θ hθ (hK f z θ hf)
        have hlow : ∀ r ∈ Finset.range (M + 1),
            (Work.Spaces.pthIter r f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - γ)
              ≤ C₀ * ∑ t ∈ Finset.range (M + 1 + 1),
                  (Work.Spaces.DthIter t f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) := by
          intro r hr
          have hrle : r ≤ M := by have := Finset.mem_range.mp hr; omega
          refine le_trans (hC₀ r (by omega) f z θ hf hθ) ?_
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.mpr (by omega))
              (fun t _ _ => slotTerm_nonneg γ hθ _)) hC₀pos.le
        have hsumle : (∑ r ∈ Finset.range (M + 1),
              (Work.Spaces.pthIter r f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - γ))
            ≤ ((M : ℝ) + 1) * (C₀ * ∑ t ∈ Finset.range (M + 1 + 1),
                  (Work.Spaces.DthIter t f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) := by
          calc (∑ r ∈ Finset.range (M + 1),
                (Work.Spaces.pthIter r f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - γ))
              ≤ ∑ _r ∈ Finset.range (M + 1),
                  C₀ * ∑ t ∈ Finset.range (M + 1 + 1),
                    (Work.Spaces.DthIter t f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) :=
                Finset.sum_le_sum hlow
            _ = ((M : ℝ) + 1) * (C₀ * ∑ t ∈ Finset.range (M + 1 + 1),
                  (Work.Spaces.DthIter t f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                push_cast
                ring
        have htop : (Work.Spaces.DthIter (M + 1) f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)
            ≤ ∑ t ∈ Finset.range (M + 1 + 1),
                (Work.Spaces.DthIter t f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) :=
          Finset.single_le_sum (fun t _ => slotTerm_nonneg γ hθ (Work.Spaces.DthIter t f z θ))
            (Finset.mem_range.mpr (Nat.lt_succ_self (M + 1)))
        have hinner : ((Work.Spaces.DthIter (M + 1) f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-γ)
            + ∑ r ∈ Finset.range (M + 1),
                (Work.Spaces.pthIter r f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - γ))
            ≤ (1 + ((M : ℝ) + 1) * C₀) * ∑ t ∈ Finset.range (M + 1 + 1),
                (Work.Spaces.DthIter t f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) := by
          have h := add_le_add htop hsumle
          have heq : (∑ t ∈ Finset.range (M + 1 + 1),
                  (Work.Spaces.DthIter t f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
                + ((M : ℝ) + 1) * (C₀ * ∑ t ∈ Finset.range (M + 1 + 1),
                    (Work.Spaces.DthIter t f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
              = (1 + ((M : ℝ) + 1) * C₀) * ∑ t ∈ Finset.range (M + 1 + 1),
                  (Work.Spaces.DthIter t f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) := by ring
          exact heq ▸ h
        have hsum0 : (0 : ℝ) ≤ ∑ t ∈ Finset.range (M + 1 + 1),
            (Work.Spaces.DthIter t f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) :=
          Finset.sum_nonneg fun t _ => slotTerm_nonneg γ hθ _
        have hfinal : (Work.Spaces.pthIter (M + 1) f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * ((M + 1 : ℕ) : ℝ) - γ)
            ≤ max C₀ Cnew * ∑ t ∈ Finset.range (M + 1 + 1),
                (Work.Spaces.DthIter t f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) := by
          set Ssum : ℝ := ∑ t ∈ Finset.range (M + 1 + 1),
              (Work.Spaces.DthIter t f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) with hSsum
          have hSnn : 0 ≤ Ssum := by
            rw [hSsum]; exact Finset.sum_nonneg fun t _ => slotTerm_nonneg γ hθ _
          have hle : 2 * K ^ 2 * (((M + 1 : ℕ) : ℝ) + 1) * (1 + ((M : ℝ) + 1) * C₀)
              ≤ Cnew := by
            rw [hCnewdef]
            exact le_of_eq (by push_cast; ring)
          have hre : 2 * K ^ 2 * (((M + 1 : ℕ) : ℝ) + 1)
                * ((1 + ((M : ℝ) + 1) * C₀) * Ssum)
              = (2 * K ^ 2 * (((M + 1 : ℕ) : ℝ) + 1) * (1 + ((M : ℝ) + 1) * C₀)) * Ssum := by
            ring
          have hmid : 2 * K ^ 2 * (((M + 1 : ℕ) : ℝ) + 1)
                * ((1 + ((M : ℝ) + 1) * C₀) * Ssum) ≤ Cnew * Ssum := by
            rw [hre]
            exact mul_le_mul_of_nonneg_right hle hSnn
          have hstart : (Work.Spaces.pthIter (M + 1) f z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * ((M + 1 : ℕ) : ℝ) - γ)
              ≤ 2 * K ^ 2 * (((M + 1 : ℕ) : ℝ) + 1)
                * ((1 + ((M : ℝ) + 1) * C₀) * Ssum) := by
            refine le_trans hstep (le_trans (mul_le_mul_of_nonneg_left hinner (by positivity)) ?_)
            exact le_rfl
          have hfin : Cnew * Ssum ≤ max C₀ Cnew * Ssum :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hSnn
          have := le_trans hstart (le_trans hmid hfin)
          rwa [hSsum] at this
        exact hfinal

end Work.FTS.EllipticEst.remov.TopCoreB

namespace Work.FTS.EllipticEst.remov.TopCoreB

/-- **The shifted slot recursion, for all orders up to `M` at once.**  There is `C > 0` with

  `(∂_θ^mf)²·σ^{2m-4-γ} ≤ C_m Σ_{i<m-1} (D_θ^i(∂_θθf))²·σ^{-γ}`   for all `2 ≤ m ≤ M`,

on the open angular interval, for `∂_θθf` smooth on the open quadrant.  This is the *pointwise*
form of `remov/Baux.PthSlotLe`; it is used for `Ψ` itself, whose second derivative is the slot
carrier of the hypotheses. -/
theorem slotRecShiftAll (γ : ℝ) (M : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ m : ℕ, m ≤ M → 2 ≤ m → ∀ (f : ℝ → ℝ → ℝ) (z θ : ℝ),
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry (Work.Spaces.pthIter 2 f)) (z, θ)) →
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pthIter m f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - 4 - γ)
        ≤ C * ∑ i ∈ Finset.range (m - 1),
            (Work.Spaces.DthIter i (Work.Spaces.pthIter 2 f) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-γ) := by
  induction M with
  | zero =>
      refine ⟨1, one_pos, fun m hm hm2 f z θ _ _ => ?_⟩
      have h : ¬ (m ≤ 0) := by omega
      exact absurd hm h
  | succ M ih =>
      obtain ⟨C₀, hC₀pos, hC₀⟩ := ih
      rcases Nat.lt_or_ge M 1 with hM0 | hM1
      · refine ⟨max C₀ 1, lt_max_of_lt_left hC₀pos, fun m hm hm2 f z θ _ _ => ?_⟩
        have h : ¬ (m ≤ M + 1) := by omega
        exact absurd hm h
      · obtain ⟨K, hKpos, hK⟩ := revExpTop (M + 1) (by omega)
        refine ⟨max C₀ (2 * K ^ 2 * ((M : ℝ) + 1) * (1 + (M : ℝ) * C₀) + 1), ?_, ?_⟩
        · exact lt_max_of_lt_left hC₀pos
        · intro m hm hm2 f z θ hf hθ
          rcases Nat.lt_or_ge m (M + 1) with hlt | hge
          · refine le_trans (hC₀ m (by omega) hm2 f z θ hf hθ)
              (mul_le_mul_of_nonneg_right (le_max_left C₀ _)
                (Finset.sum_nonneg fun i _ => slotTerm_nonneg γ hθ _))
          · obtain rfl : m = M + 1 := by omega
            have hstep := Work.FTS.EllipticEst.remov.Baux.PthSlotPointwise γ (M + 1) hm2 K hKpos
              f z θ hθ (hK f z θ hf hθ)
            have hcast : (((M + 1 : ℕ) : ℝ) - 1) = (M : ℝ) := by push_cast; ring
            set Ssum : ℝ := ∑ i ∈ Finset.range (M + 1 - 1),
                (Work.Spaces.DthIter i (Work.Spaces.pthIter 2 f) z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-γ) with hSsum
            have hSnn : 0 ≤ Ssum := by
              rw [hSsum]; exact Finset.sum_nonneg fun i _ => slotTerm_nonneg γ hθ _
            have hA : (Work.Spaces.DthIter (M + 1 - 2) (Work.Spaces.pthIter 2 f) z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-γ) ≤ Ssum := by
              rw [hSsum]
              exact Finset.single_le_sum
                (fun i _ => slotTerm_nonneg γ hθ (Work.Spaces.DthIter i
                  (Work.Spaces.pthIter 2 f) z θ))
                (Finset.mem_range.mpr (by omega))
            have hY : ∀ r ∈ Finset.range (M + 1 - 2),
                (Work.Spaces.pthIter (r + 2) f z θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * ((r + 2 : ℕ) : ℝ) - 4 - γ)
                  ≤ C₀ * Ssum := by
              intro r hr
              have hrlt : r < M - 1 := by
                have h := Finset.mem_range.mp hr; omega
              refine le_trans (hC₀ (r + 2) (by omega) (by omega) f z θ hf hθ) ?_
              refine mul_le_mul_of_nonneg_left ?_ hC₀pos.le
              rw [hSsum]
              exact Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.range_subset_range.mpr (by omega))
                (fun i _ _ => slotTerm_nonneg γ hθ (Work.Spaces.DthIter i
                  (Work.Spaces.pthIter 2 f) z θ))
            have hcard : ((M + 1 - 2 : ℕ) : ℝ) ≤ (M : ℝ) := by
              have h : M + 1 - 2 ≤ M := by omega
              exact_mod_cast h
            have hsumY : (∑ r ∈ Finset.range (M + 1 - 2),
                  (Work.Spaces.pthIter (r + 2) f z θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * ((r + 2 : ℕ) : ℝ) - 4 - γ))
                ≤ (M : ℝ) * (C₀ * Ssum) := by
              calc (∑ r ∈ Finset.range (M + 1 - 2),
                    (Work.Spaces.pthIter (r + 2) f z θ) ^ 2
                      * (Real.sin (2 * θ)) ^ (2 * ((r + 2 : ℕ) : ℝ) - 4 - γ))
                  ≤ ∑ _r ∈ Finset.range (M + 1 - 2), C₀ * Ssum := Finset.sum_le_sum hY
                _ = ((M + 1 - 2 : ℕ) : ℝ) * (C₀ * Ssum) := by
                    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                _ ≤ (M : ℝ) * (C₀ * Ssum) :=
                    mul_le_mul_of_nonneg_right hcard (mul_nonneg hC₀pos.le hSnn)
            have hinner : ((Work.Spaces.DthIter (M + 1 - 2) (Work.Spaces.pthIter 2 f) z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-γ)
                + ∑ r ∈ Finset.range (M + 1 - 2),
                    (Work.Spaces.pthIter (r + 2) f z θ) ^ 2
                      * (Real.sin (2 * θ)) ^ (2 * ((r + 2 : ℕ) : ℝ) - 4 - γ))
                ≤ (1 + (M : ℝ) * C₀) * Ssum := by
              have h := add_le_add hA hsumY
              have heq : Ssum + (M : ℝ) * (C₀ * Ssum) = (1 + (M : ℝ) * C₀) * Ssum := by ring
              exact heq ▸ h
            have hK2nn : (0 : ℝ) ≤ 2 * K ^ 2 * (((M + 1 : ℕ) : ℝ) - 1) := by
              rw [hcast]
              have hMnn : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 0 ≤ M)
              positivity
            have hstart : (Work.Spaces.pthIter (M + 1) f z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * ((M + 1 : ℕ) : ℝ) - 4 - γ)
                ≤ 2 * K ^ 2 * (((M + 1 : ℕ) : ℝ) - 1) * ((1 + (M : ℝ) * C₀) * Ssum) := by
              refine le_trans hstep ?_
              exact mul_le_mul_of_nonneg_left hinner hK2nn
            have hle : 2 * K ^ 2 * (((M + 1 : ℕ) : ℝ) - 1) * (1 + (M : ℝ) * C₀)
                ≤ max C₀ (2 * K ^ 2 * ((M : ℝ) + 1) * (1 + (M : ℝ) * C₀) + 1) := by
              rw [hcast]
              have hK2 : (0 : ℝ) ≤ 2 * K ^ 2 := by positivity
              have hC0nn : (0 : ℝ) ≤ 1 + (M : ℝ) * C₀ := by
                have hMnn : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 0 ≤ M)
                have := mul_nonneg hMnn hC₀pos.le
                linarith
              have h1 : 2 * K ^ 2 * (M : ℝ) * (1 + (M : ℝ) * C₀)
                  ≤ 2 * K ^ 2 * ((M : ℝ) + 1) * (1 + (M : ℝ) * C₀) := by
                have h2 : (M : ℝ) ≤ (M : ℝ) + 1 := by linarith
                exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hK2) hC0nn
              linarith [h1, le_max_right C₀ (2 * K ^ 2 * ((M : ℝ) + 1) * (1 + (M : ℝ) * C₀) + 1)]
            have hmid : 2 * K ^ 2 * (((M + 1 : ℕ) : ℝ) - 1) * ((1 + (M : ℝ) * C₀) * Ssum)
                ≤ (max C₀ (2 * K ^ 2 * ((M : ℝ) + 1) * (1 + (M : ℝ) * C₀) + 1)) * Ssum := by
              have hre : 2 * K ^ 2 * (((M + 1 : ℕ) : ℝ) - 1) * ((1 + (M : ℝ) * C₀) * Ssum)
                  = (2 * K ^ 2 * (((M + 1 : ℕ) : ℝ) - 1) * (1 + (M : ℝ) * C₀)) * Ssum := by ring
              rw [hre]
              exact mul_le_mul_of_nonneg_right hle hSnn
            have hfin := le_trans hstart hmid
            rw [hSsum] at hfin
            exact hfin

end Work.FTS.EllipticEst.remov.TopCoreB
