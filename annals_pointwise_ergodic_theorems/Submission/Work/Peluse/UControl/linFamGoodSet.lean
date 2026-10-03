import Mathlib
import Submission.Work.Peluse.UControl.peluseProp34Defs

/-!
# The good set of the linear-configuration average `linFamAvg`

`linFamAvg D l c N M H f b β` (`pelusePetChapterDefs.lean`) is the average, over the parameter box
`D.parBox l H`, of the nonnegative fibres

`linFib D l c N M f b β a = ‖((N:ℂ)*(M:ℂ))⁻¹ * ∑'_x f x * ∑_{y∈[M]} ∏_{i} C^{b i} f (x + dir(a)_i y + β_i(a))‖`

of the multilinear correlation along the *linear* configuration with the datum's directions.

This file proves the elementary "extraction of a good set" from that average
(`Work.Peluse.UControl.linFamGoodSet`): if the average is at least `γ` then the set `T` of the
parameters at which the fibre is at least `γ/2` carries at least the fraction `γ/12` of the box,
and of course satisfies the pointwise lower bound by construction.

The mathematics is the standard weighted-average argument, and it is *quantitative*:

* the fibres are nonnegative, so the average over the box is at least `γ` implies
  `γ·|box| ≤ ∑_{a∈box} linFib a`;
* the fibre is bounded by `3`: the `y`-sum contributes at most the factor `M`, the product of slots
  at most `1` (each slot is a translate of `f` or of its conjugate, and `‖f‖ ≤ 1` pointwise), and
  the `x`-sum is supported on `symIcc N`, of cardinality `2N+1`, so that
  `linFib a ≤ (2N+1)/N ≤ 3` for `N ≥ 1`;
* splitting the sum into the good part (`≥ γ/2` by definition) and its complement (`< γ/2`),
  `γ·|box| ≤ 3·|T| + (|box| - |T|)·(γ/2)`, whence `|T| ≥ γ·|box|/6 ≥ γ·|box|/12`.

Only the constant `3` matters, and any constant `< 6` would do: the fraction `γ/12` of the box is
the (loose) value needed by the consumer `LinFibBound` (`peluseProp34Defs.lean`).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-- The cardinality of the symmetric interval `[-N,N]`. -/
private lemma linFamGoodSet_card_symIcc (N : ℕ) : (symIcc N).card = 2 * N + 1 := by
  rw [symIcc]
  simp
  omega

/-- **The elementary arithmetic of the good set.**  From the average inequality
`γ·p ≤ 3·t + (p - t)·(γ/2)` with `γ, p, t ≥ 0` one gets `t ≥ γ·p/12`.

(Indeed, ignoring the nonnegative term `-t·γ/2` gives `γ·p ≤ 3t + p·γ/2`, i.e. `γ·p ≤ 6t`, and
`γ·p/12 ≤ γ·p/6 ≤ t`.) -/
private lemma linFamGoodSet_arith {γ p t : ℝ} (hγ : 0 ≤ γ) (hp : 0 ≤ p) (ht : 0 ≤ t)
    (h1 : γ * p ≤ 3 * t + (p - t) * (γ / 2)) : γ * p / 12 ≤ t := by
  have h2 : (p - t) * (γ / 2) ≤ p * (γ / 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h3 : γ * p ≤ 3 * t + p * (γ / 2) := le_trans h1 (by linarith)
  have h4 : γ * p / 2 ≤ 3 * t := by linarith
  have h5 : γ * p ≤ 6 * t := by linarith
  have h6 := mul_nonneg hγ hp
  linarith

theorem linFamGoodSet {l : ℕ} (D : Work.Peluse.UControl.IdxDatum) (c : ℤ) (hl : 2 ≤ l) :
    ∀ (N M H : ℕ) (f : ℤ → ℂ) (Cne : ℕ) (γ : ℝ)
      (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
      (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ),
      2 ≤ Fintype.card (D.I (l - 1)) → 1 ≤ N → 2 ≤ M → 1 ≤ Cne →
      0 < γ → γ ≤ 1 → (∀ x : ℤ, ‖f x‖ ≤ 1) → Work.Peluse.SupportIn f N →
      γ ≤ Work.Peluse.UControl.linFamAvg D l c N M H f b β →
      ∃ T : Finset (D.Idx l), T ⊆ D.parBox l H ∧
        (γ / 12) * (((D.parBox l H).card : ℕ) : ℝ) ≤ (T.card : ℝ) ∧
        ∀ a ∈ T, γ / 2 ≤ Work.Peluse.UControl.linFib D l c N M f b β a := by
  intro N M H f Cne γ b β hI hN hM hCne hγ0 hγ1 hf hs hγ
  classical
  -- ### Step 1: the fibre is bounded by `3`
  have hcard3 : ∀ a : D.Idx l, linFib D l c N M f b β a ≤ 3 := by
    intro a
    rw [linFib]
    have hcard : (symIcc N).card = 2 * N + 1 := linFamGoodSet_card_symIcc N
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    -- the `x`-sum is supported on `symIcc N`
    have hsupp : ∀ x : ℤ, x ∉ (symIcc N) →
        f x * ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin (Fintype.card (D.I (l - 1))),
          (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
            else f (x + (petDir D l c a i * (y : ℤ) + β a i))) = 0 := by
      intro x hx
      have hxN : N < x.natAbs := by
        rw [symIcc, Finset.mem_Icc] at hx
        omega
      rw [hs x hxN, zero_mul]
    rw [tsum_eq_sum hsupp]
    -- the elementary bound `‖NM)⁻¹‖ · ‖x-sum‖ ≤ (2N+1)/N`
    have hstep : ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑ x ∈ symIcc N, f x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin (Fintype.card (D.I (l - 1))),
            (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
              else f (x + (petDir D l c a i * (y : ℤ) + β a i)))‖
        ≤ ((N : ℝ) * (M : ℝ))⁻¹ * ((M : ℝ) * ((2 * N + 1 : ℕ) : ℝ)) := by
      rw [norm_mul]
      have hnorm : ‖((N : ℂ) * (M : ℂ))⁻¹‖ = ((N : ℝ) * (M : ℝ))⁻¹ := by
        rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
      rw [hnorm]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ‖∑ x ∈ symIcc N, f x *
            ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin (Fintype.card (D.I (l - 1))),
              (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
                else f (x + (petDir D l c a i * (y : ℤ) + β a i)))‖
          ≤ ∑ x ∈ symIcc N, (M : ℝ) := by
            refine le_trans (norm_sum_le _ _) ?_
            refine Finset.sum_le_sum (fun x _ => ?_)
            rw [norm_mul]
            refine le_trans (mul_le_mul_of_nonneg_right (hf x) (norm_nonneg _)) ?_
            rw [one_mul]
            refine le_trans (norm_sum_le _ _) ?_
            calc ∑ y ∈ Finset.Icc 1 M, ‖∏ i : Fin (Fintype.card (D.I (l - 1))),
                  (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
                    else f (x + (petDir D l c a i * (y : ℤ) + β a i)))‖
                ≤ ∑ _y ∈ Finset.Icc 1 M, (1 : ℝ) := by
                  refine Finset.sum_le_sum (fun y _ => ?_)
                  rw [norm_prod]
                  refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
                  by_cases hbi : b i
                  · simp [hbi, hf]
                  · simp [hbi, hf]
              _ = (M : ℝ) := by
                  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; norm_num
        _ = (M : ℝ) * ((2 * N + 1 : ℕ) : ℝ) := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring
    refine le_trans hstep ?_
    have hNM : ((N : ℝ) * (M : ℝ))⁻¹ * ((M : ℝ) * ((2 * N + 1 : ℕ) : ℝ))
        = ((2 * N + 1 : ℕ) : ℝ) / (N : ℝ) := by
      field_simp
    rw [hNM, div_le_iff₀ hN0]
    push_cast
    linarith
  -- ### Step 2: the average inequality `γ·|box| ≤ ∑ linFib`
  rw [linFamAvg_eq] at hγ
  set P : ℝ := (((D.parBox l H).card : ℕ) : ℝ) with hP
  set T : Finset (D.Idx l) :=
    (D.parBox l H).filter (fun a => γ / 2 ≤ linFib D l c N M f b β a) with hT
  have hTsub : T ⊆ D.parBox l H := by rw [hT]; exact Finset.filter_subset _ _
  have hne : (D.parBox l H).Nonempty := ⟨0, by rw [IdxDatum.mem_parBox]; intro j s; simp⟩
  have hPpos : 0 < P := by rw [hP]; exact_mod_cast (Finset.card_pos.mpr hne)
  have hPne : P ≠ 0 := ne_of_gt hPpos
  have hS : P * (P⁻¹ * ∑ a ∈ D.parBox l H, linFib D l c N M f b β a)
      = ∑ a ∈ D.parBox l H, linFib D l c N M f b β a := by
    rw [← mul_assoc, mul_inv_cancel₀ hPne, one_mul]
  have hmul : γ * P ≤ ∑ a ∈ D.parBox l H, linFib D l c N M f b β a := by
    have h := mul_le_mul_of_nonneg_left hγ hPpos.le
    rw [hS] at h
    linarith
  -- ### Step 3: splitting the box at the threshold `γ/2`
  have hsplit : ∑ a ∈ D.parBox l H, linFib D l c N M f b β a
      = ∑ a ∈ D.parBox l H \ T, linFib D l c N M f b β a
        + ∑ a ∈ T, linFib D l c N M f b β a :=
    (Finset.sum_sdiff hTsub).symm
  have hTsum : ∑ a ∈ T, linFib D l c N M f b β a ≤ 3 * (T.card : ℝ) := by
    calc ∑ a ∈ T, linFib D l c N M f b β a ≤ ∑ _a ∈ T, (3 : ℝ) :=
          Finset.sum_le_sum (fun a _ => hcard3 a)
      _ = 3 * (T.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hcomp : ∑ a ∈ D.parBox l H \ T, linFib D l c N M f b β a
      ≤ (P - (T.card : ℝ)) * (γ / 2) := by
    have hterm : ∀ a ∈ D.parBox l H \ T, linFib D l c N M f b β a ≤ γ / 2 := by
      intro a ha
      rw [Finset.mem_sdiff] at ha
      have hnot : ¬ (γ / 2 ≤ linFib D l c N M f b β a) := by
        intro hle
        exact ha.2 (by rw [hT]; exact Finset.mem_filter.mpr ⟨ha.1, hle⟩)
      exact le_of_lt (not_le.mp hnot)
    have hc : ((D.parBox l H \ T).card : ℝ) = (P - (T.card : ℝ)) := by
      rw [hP, Finset.card_sdiff, Finset.inter_eq_left.mpr hTsub,
        Nat.cast_sub (Finset.card_le_card hTsub)]
    calc ∑ a ∈ D.parBox l H \ T, linFib D l c N M f b β a
        ≤ ∑ _a ∈ D.parBox l H \ T, (γ / 2) := Finset.sum_le_sum hterm
      _ = ((D.parBox l H \ T).card : ℝ) * (γ / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (P - (T.card : ℝ)) * (γ / 2) := by rw [hc]
  -- ### Step 4: the conclusion
  have hmain : γ * P ≤ 3 * (T.card : ℝ) + (P - (T.card : ℝ)) * (γ / 2) := by
    rw [hsplit] at hmul
    linarith
  have harith : γ * P / 12 ≤ (T.card : ℝ) :=
    linFamGoodSet_arith hγ0.le hPpos.le (by positivity) hmain
  refine ⟨T, hTsub, ?_, ?_⟩
  · rw [hP] at harith
    linarith [harith]
  · intro a ha
    rw [hT] at ha
    exact (Finset.mem_filter.mp ha).2

end

end Work.Peluse.UControl
