import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.qDzLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowMulSupAux.mismatch
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.H2.T1Q.IbpCutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-!
# `mismatchSummandPt` — the mismatch summand with a *pointwise* coefficient price

This is the `Galerkin.Fn`-flavoured variant of `rowMulSupAux.mismatchSummand` in which the
coefficient slot `mixed i a A` is priced **pointwise** by `KA · (α + sin 2θ)·sin(2θ)^{α/5}`
(so neither `WlInfMem α 6 A` nor `WlInf α 6 A ≤ KA` is assumed, and the *same* constant `KA`
appears), with the summand being

`ρ · (D_z^iD_θ^aA) · (D_z^{b-i}f) · (D_z^bD_θ^af)`,  `ρ = leafGam α`,  `1 ≤ a`, `i ≤ b`, `a+b ≤ 6`.

The proof is the same AM–GM chain as in `mismatchSummand`: the exact weight identity
`σ^{-γ}(α+σ)σ^{α/5} = α σ^{-(1-α/10)} + σ^{α/10}` splits the `γ`-weight into the *critical*
weight `σ^{-(1-α/10)}` (whose `u`-slot is paid by the angular Hardy inequality `qDzLe`, with the
`α^{-2}` there cancelled by the `α²` of Young's inequality) plus the harmless `σ^{α/10}`-piece
(paid by the `η`-slots of `f`).
-/

/-- The product of the two restricted Lebesgue measures on `Iz × Iθ`. -/
private def zθμ : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-! ## Elementary weight identities -/

/-- `(σ^{-γ/2})² = σ^{-γ}` for `0 ≤ σ` (both sides being `0` at `σ = 0`). -/
private lemma rpow_neg_half_sq {s γ : ℝ} (hs : 0 ≤ s) : (s ^ (-(γ / 2))) ^ 2 = s ^ (-γ) := by
  rcases eq_or_ne γ 0 with hγ | hγ
  · subst hγ
    norm_num
  · rcases hs.lt_or_eq with h | h
    · rw [sq, ← Real.rpow_add h]
      congr 1
      ring
    · subst h
      rw [Real.zero_rpow (by simp [hγ]), Real.zero_rpow (by simpa using neg_ne_zero.mpr hγ)]
      ring

/-- `1 ≤ σ^{-q}` for `0 < σ ≤ 1` and `q ≥ 0`. -/
private lemma one_le_rpow_neg' {s q : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hq : 0 ≤ q) :
    (1 : ℝ) ≤ s ^ (-q) := by
  rw [Real.rpow_neg hs.le]
  have h1 : s ^ q ≤ 1 := Real.rpow_le_one hs.le hs1 hq
  have h2 : 0 < s ^ q := Real.rpow_pos_of_pos hs q
  exact (one_le_inv₀ h2).mpr h1

/-- `(g · Wt α z θ)² = w z² · sin(2θ)^{-γ} · g²`, on the quadrant (where `sin(2θ) ≥ 0`). -/
private lemma Wt_sq {α z θ g : ℝ} (hs : 0 ≤ Real.sin (2 * θ)) :
    (g * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * g ^ 2 := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow, rpow_neg_half_sq hs]
  ring

/-- `(g · (w₀/σ^{e/2}))² = w₀² · σ^{-e} · g²`. -/
private lemma zslot_sq {w₀ g σ e : ℝ} (hs : 0 ≤ σ) (he : e ≠ 0) :
    (g * (w₀ / σ ^ (e / 2))) ^ 2 = w₀ ^ 2 * σ ^ (-e) * g ^ 2 := by
  rw [Work.Spaces.sq_mul_div_rpow g w₀ σ e hs he]
  ring

/-- `2XY ≤ X² + Y²` for `X, Y ≥ 0`. -/
private lemma two_mul_le_add_sq (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    2 * X * Y ≤ X ^ 2 + Y ^ 2 := by
  nlinarith [sq_nonneg (X - Y)]

/-- Young's inequality with the `α²`-scaling: `α P |U||V| ≤ α²/2 (P U²) + 1/2 (P V²)`. -/
private lemma young_alpha {α P U V : ℝ} (hα : 0 ≤ α) (hP : 0 ≤ P) :
    α * P * |U| * |V| ≤ α ^ 2 / 2 * (P * U ^ 2) + 1 / 2 * (P * V ^ 2) := by
  have h := mul_le_mul_of_nonneg_left
    (two_mul_le_add_sq (α * |U|) |V| (mul_nonneg hα (abs_nonneg U)) (abs_nonneg V))
    (by linarith : (0 : ℝ) ≤ P / 2)
  have e1 : P / 2 * (2 * (α * |U|) * |V|) = α * P * |U| * |V| := by ring
  have e2 : P / 2 * ((α * |U|) ^ 2 + |V| ^ 2)
      = α ^ 2 / 2 * (P * U ^ 2) + 1 / 2 * (P * V ^ 2) := by
    rw [mul_pow, sq_abs, sq_abs]
    ring
  rw [e1, e2] at h
  exact h

/-- `P |U||V| ≤ (P U² + P V²)/2`. -/
private lemma young_one {P U V : ℝ} (hP : 0 ≤ P) :
    P * |U| * |V| ≤ 1 / 2 * (P * U ^ 2) + 1 / 2 * (P * V ^ 2) := by
  have h := mul_le_mul_of_nonneg_left
    (two_mul_le_add_sq |U| |V| (abs_nonneg U) (abs_nonneg V))
    (by linarith : (0 : ℝ) ≤ P / 2)
  have e1 : P / 2 * (2 * |U| * |V|) = P * |U| * |V| := by ring
  have e2 : P / 2 * (|U| ^ 2 + |V| ^ 2)
      = 1 / 2 * (P * U ^ 2) + 1 / 2 * (P * V ^ 2) := by
    rw [sq_abs, sq_abs]
    ring
  rw [e1, e2] at h
  exact h

/-- The `σ^{-(1-α/10)}` weight is dominated by the `γ`-weight. -/
private lemma rpow_one_sub_le_gam {α s : ℝ} (hα : 0 ≤ α) (hs : 0 < s) (hs1 : s ≤ 1) :
    s ^ (-(1 - α / 10)) ≤ s ^ (-(Work.Spaces.gam α)) := by
  refine Real.rpow_le_rpow_of_exponent_ge hs hs1 ?_
  rw [Work.Spaces.gam]
  linarith

/-- The `σ^{α/10}` weight is dominated by the `η`-weight. -/
private lemma rpow_beta_le_eta {α s : ℝ} (hα : 0 < α) (hs : 0 < s) (hs1 : s ≤ 1) :
    s ^ (α / 10) ≤ s ^ (-(Work.Spaces.eta)) := by
  have h2 : s ^ (α / 10) ≤ 1 := Real.rpow_le_one hs.le hs1 (by linarith)
  have h3 : (1 : ℝ) ≤ s ^ (-(Work.Spaces.eta)) :=
    one_le_rpow_neg' hs hs1 Work.Spaces.eta_nonneg
  linarith

/-- The `σ^{α/10}` weight is dominated by the `γ`-weight. -/
private lemma rpow_beta_le_gam {α s : ℝ} (hα : 0 < α) (hs : 0 < s) (hs1 : s ≤ 1) :
    s ^ (α / 10) ≤ s ^ (-(Work.Spaces.gam α)) := by
  have h2 : s ^ (α / 10) ≤ 1 := Real.rpow_le_one hs.le hs1 (by linarith)
  have h3 : (1 : ℝ) ≤ s ^ (-(Work.Spaces.gam α)) :=
    one_le_rpow_neg' hs hs1 (by rw [Work.Spaces.gam]; linarith)
  linarith

/-! ## Continuity on the open quadrant (for the a.e. strong measurability) -/

private lemma continuousOn_w_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
    funext p
    rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

private lemma continuousOn_rpow_sin_Q0 (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ q) Work.FTS.EllipticEst.Q0 := by
  have hbase : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  refine hbase.rpow_const (fun p hp => Or.inl ?_)
  obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

private lemma continuousOn_Wt (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p
    rfl
  rw [hfun]
  exact continuousOn_w_Q0.mul (continuousOn_rpow_sin_Q0 _)

private lemma continuousOn_leafGam (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
      = fun p : ℝ × ℝ =>
          (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) := by
    funext p
    rfl
  rw [hfun]
  exact (continuousOn_w_Q0.pow 2).mul (continuousOn_rpow_sin_Q0 _)

/-! ## The pointwise bound of the summand -/

private theorem mismatch_pt {α KA : ℝ} (hα : 0 < α) (hKA : 0 ≤ KA)
    {A f : ℝ → ℝ → ℝ} {i a b : ℕ}
    (hcoef : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed i a A z θ|
        ≤ KA * (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed i a A z θ
        * Work.Spaces.DzIter (b - i) f z θ * Work.Spaces.mixed b a f z θ|
      ≤ KA *
        (α ^ 2 / 2 * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
            * (Work.Spaces.DzIter (b - i) f z θ) ^ 2)
          + (Work.Spaces.mixed b a f z θ * Work.Spaces.Wt α z θ) ^ 2
          + 1 / 2 * (Work.Spaces.DzIter (b - i) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  set s : ℝ := Real.sin (2 * θ) with hsdef
  set W : ℝ := Work.Spaces.w z with hWdef
  set G : ℝ := Work.Spaces.DzIter (b - i) f z θ with hGdef
  set Y : ℝ := Work.Spaces.mixed b a f z θ with hYdef
  have hsp : 0 < s := by rw [hsdef]; exact hs
  have hs1' : s ≤ 1 := by rw [hsdef]; exact hs1
  have hWnn : 0 ≤ W := by rw [hWdef, Work.Spaces.w]; positivity
  have hlg : Work.FTS.TransportS.leafGam α z θ = W ^ 2 * s ^ (-(Work.Spaces.gam α)) := by
    rw [Work.FTS.TransportS.leafGam, ← hsdef, ← hWdef]
  -- the coefficient slot, pointwise
  have hcoef' : |Work.Spaces.mixed i a A z θ| ≤ (KA * (α + s)) * s ^ (α / 5) := by
    have h := hcoef z θ hz hθ.1 hθ.2
    rwa [← hsdef] at h
  -- the exact split `σ^{-γ}(α+σ)σ^{α/5} = α σ^{-(1-α/10)} + σ^{α/10}`
  have hsplit : s ^ (-(Work.Spaces.gam α)) * ((α + s) * s ^ (α / 5))
      = α * s ^ (-(1 - α / 10)) + s ^ (α / 10) := by
    have h1 : s ^ (-(Work.Spaces.gam α)) * s ^ (α / 5) = s ^ (-(1 - α / 10)) := by
      rw [← Real.rpow_add hsp]
      congr 1
      rw [Work.Spaces.gam]
      ring
    have h2a : s ^ (-(Work.Spaces.gam α)) * s = s ^ (-(Work.Spaces.gam α) + 1) :=
      (Real.rpow_add_one hsp.ne' _).symm
    have h2 : s ^ (-(Work.Spaces.gam α)) * s * s ^ (α / 5) = s ^ (α / 10) := by
      rw [h2a, ← Real.rpow_add hsp]
      congr 1
      rw [Work.Spaces.gam]
      ring
    calc s ^ (-(Work.Spaces.gam α)) * ((α + s) * s ^ (α / 5))
        = α * (s ^ (-(Work.Spaces.gam α)) * s ^ (α / 5))
          + s ^ (-(Work.Spaces.gam α)) * s * s ^ (α / 5) := by ring
      _ = α * s ^ (-(1 - α / 10)) + s ^ (α / 10) := by rw [h1, h2]
  -- the two AM–GM pieces
  have hAM1 : α * (W ^ 2 * s ^ (-(1 - α / 10))) * |G| * |Y|
      ≤ α ^ 2 / 2 * (W ^ 2 * s ^ (-(1 - α / 10)) * G ^ 2)
        + 1 / 2 * (W ^ 2 * s ^ (-(Work.Spaces.gam α)) * Y ^ 2) := by
    refine (young_alpha (α := α) (P := W ^ 2 * s ^ (-(1 - α / 10))) (U := G) (V := Y)
      hα.le (mul_nonneg (sq_nonneg W) (Real.rpow_nonneg hsp.le _))).trans ?_
    have hge := mul_le_mul_of_nonneg_left (rpow_one_sub_le_gam (α := α) hα.le hsp hs1')
      (sq_nonneg W)
    have hge2 := mul_le_mul_of_nonneg_right hge (sq_nonneg Y)
    linarith
  have hAM2 : (W ^ 2 * s ^ (α / 10)) * |G| * |Y|
      ≤ 1 / 2 * (W ^ 2 * s ^ (-(Work.Spaces.gam α)) * Y ^ 2)
        + 1 / 2 * (W ^ 2 * s ^ (-(Work.Spaces.eta)) * G ^ 2) := by
    refine (young_one (P := W ^ 2 * s ^ (α / 10)) (U := G) (V := Y)
      (mul_nonneg (sq_nonneg W) (Real.rpow_nonneg hsp.le _))).trans ?_
    have hb1 : W ^ 2 * s ^ (α / 10) ≤ W ^ 2 * s ^ (-(Work.Spaces.gam α)) :=
      mul_le_mul_of_nonneg_left (rpow_beta_le_gam (α := α) hα hsp hs1') (sq_nonneg W)
    have hb2 : W ^ 2 * s ^ (α / 10) ≤ W ^ 2 * s ^ (-(Work.Spaces.eta)) :=
      mul_le_mul_of_nonneg_left (rpow_beta_le_eta (α := α) hα hsp hs1') (sq_nonneg W)
    have h1' := mul_le_mul_of_nonneg_right hb1 (sq_nonneg Y)
    have h2' := mul_le_mul_of_nonneg_right hb2 (sq_nonneg G)
    linarith
  -- the absolute value unfolds
  have habs : |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed i a A z θ * G * Y|
      = W ^ 2 * s ^ (-(Work.Spaces.gam α)) * |Work.Spaces.mixed i a A z θ| * |G| * |Y| := by
    rw [hlg, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (mul_nonneg (sq_nonneg W) (Real.rpow_nonneg hsp.le _))]
  -- multiply the coefficient bound in
  have hstep : W ^ 2 * s ^ (-(Work.Spaces.gam α)) * |Work.Spaces.mixed i a A z θ| * |G| * |Y|
      ≤ W ^ 2 * s ^ (-(Work.Spaces.gam α)) * ((KA * (α + s)) * s ^ (α / 5))
          * |G| * |Y| :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcoef'
        (mul_nonneg (sq_nonneg W) (Real.rpow_nonneg hsp.le _)))
      (abs_nonneg G)) (abs_nonneg Y)
  have heq1 : W ^ 2 * s ^ (-(Work.Spaces.gam α)) * ((KA * (α + s)) * s ^ (α / 5))
        * |G| * |Y|
      = KA * (s ^ (-(Work.Spaces.gam α)) * ((α + s) * s ^ (α / 5))) * (W ^ 2 * |G| * |Y|) := by
    ring
  have heq2 : KA * (s ^ (-(Work.Spaces.gam α)) * ((α + s) * s ^ (α / 5)))
        * (W ^ 2 * |G| * |Y|)
      = KA * (α * (W ^ 2 * s ^ (-(1 - α / 10))) * |G| * |Y|
          + (W ^ 2 * s ^ (α / 10)) * |G| * |Y|) := by
    rw [hsplit]
    ring
  have hmain : W ^ 2 * s ^ (-(Work.Spaces.gam α)) * ((KA * (α + s)) * s ^ (α / 5))
        * |G| * |Y|
      ≤ KA * (α ^ 2 / 2 * (W ^ 2 * s ^ (-(1 - α / 10)) * G ^ 2)
          + (W ^ 2 * s ^ (-(Work.Spaces.gam α)) * Y ^ 2)
          + 1 / 2 * (W ^ 2 * s ^ (-(Work.Spaces.eta)) * G ^ 2)) := by
    rw [heq1, heq2]
    refine mul_le_mul_of_nonneg_left ?_ hKA
    linarith [hAM1, hAM2]
  have hbr : 0 ≤ α ^ 2 / 2 * (W ^ 2 * s ^ (-(1 - α / 10)) * G ^ 2)
        + (W ^ 2 * s ^ (-(Work.Spaces.gam α)) * Y ^ 2)
        + 1 / 2 * (W ^ 2 * s ^ (-(Work.Spaces.eta)) * G ^ 2) := by
    refine add_nonneg (add_nonneg (mul_nonneg (by positivity) ?_) ?_) ?_
    · exact mul_nonneg (mul_nonneg (sq_nonneg W) (Real.rpow_nonneg hsp.le _)) (sq_nonneg G)
    · exact mul_nonneg (mul_nonneg (sq_nonneg W) (Real.rpow_nonneg hsp.le _)) (sq_nonneg Y)
    · exact mul_nonneg (by norm_num)
        (mul_nonneg (mul_nonneg (sq_nonneg W) (Real.rpow_nonneg hsp.le _)) (sq_nonneg G))
  calc |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed i a A z θ * G * Y|
      = W ^ 2 * s ^ (-(Work.Spaces.gam α)) * |Work.Spaces.mixed i a A z θ| * |G| * |Y| := habs
    _ ≤ W ^ 2 * s ^ (-(Work.Spaces.gam α)) * ((KA * (α + s)) * s ^ (α / 5)) * |G| * |Y| := hstep
    _ ≤ KA * (α ^ 2 / 2 * (W ^ 2 * s ^ (-(1 - α / 10)) * G ^ 2)
          + (W ^ 2 * s ^ (-(Work.Spaces.gam α)) * Y ^ 2)
          + 1 / 2 * (W ^ 2 * s ^ (-(Work.Spaces.eta)) * G ^ 2)) := hmain
    _ = KA *
        (α ^ 2 / 2 * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
            * (Work.Spaces.DzIter (b - i) f z θ) ^ 2)
          + (Work.Spaces.mixed b a f z θ * Work.Spaces.Wt α z θ) ^ 2
          + 1 / 2 * (Work.Spaces.DzIter (b - i) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
        rw [Wt_sq (α := α) hs.le,
          zslot_sq (w₀ := Work.Spaces.w z) (g := Work.Spaces.DzIter (b - i) f z θ)
            (σ := Real.sin (2 * θ)) (e := Work.Spaces.eta) hs.le
            (by norm_num [Work.Spaces.eta]),
          ← hsdef, ← hWdef, ← hGdef, ← hYdef]

/-! ## The summand bound -/

theorem mismatchSummandPt : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (KA : ℝ) (i a b : ℕ),
      Work.FTS.EllipticEst.SmoothOpen A →
      Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 6 f →
      0 ≤ KA →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed i a A z θ|
            ≤ KA * (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) →
      1 ≤ a → i ≤ b → a + b ≤ 6 →
      MeasureTheory.Integrable (fun p : ℝ × ℝ =>
          Work.FTS.TransportS.leafGam α p.1 p.2 * Work.Spaces.mixed i a A p.1 p.2
            * Work.Spaces.DzIter (b - i) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2 * Work.Spaces.mixed i a A p.1 p.2
            * Work.Spaces.DzIter (b - i) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * KA * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨Cq, hCqpos, hq⟩ := Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.qDzLe
  refine ⟨Cq / 2 + 3 / 2, by positivity, ?_⟩
  intro α hα A f KA i a b hAso hfso hmf hKA0 hcoef ha hib hab
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hm5 : b - i ≤ 5 := by omega
  have hm6 : b - i ≤ 6 := by omega
  have hHk0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  -- the `ℋ⁶`-integrand is product-integrable, with value `HkSq α 6 f`
  obtain ⟨hHkint, hHkval⟩ :=
    Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen (α := α) (k := 6) hfso hmf
  -- the three pieces of the majorant
  set PA : ℝ × ℝ → ℝ := fun p => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(1 - α / 10))
      * (Work.Spaces.DzIter (b - i) f p.1 p.2) ^ 2 with hPAdef
  set PB : ℝ × ℝ → ℝ := fun p =>
      (Work.Spaces.mixed b a f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2 with hPBdef
  set PC : ℝ × ℝ → ℝ := fun p => (Work.Spaces.DzIter (b - i) f p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 with hPCdef
  set Φ : ℝ × ℝ → ℝ := fun p => KA * (α ^ 2 / 2 * PA p + PB p + 1 / 2 * PC p)
    with hPhidef
  set F : ℝ × ℝ → ℝ := fun p =>
      Work.FTS.TransportS.leafGam α p.1 p.2 * Work.Spaces.mixed i a A p.1 p.2
        * Work.Spaces.DzIter (b - i) f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2 with hFdef
  -- ## the `qDzLe` piece
  obtain ⟨hPAmem, hPAbd0⟩ := hq α hα f (b - i) hfso hmf hm5
  have hPAint : Integrable PA zθμ := by
    rw [zθμ, hPAdef]
    exact hPAmem
  have hPAbd : (∫ p, PA p ∂zθμ) ≤ Cq * α ^ (-(2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f) := by
    rw [zθμ, hPAdef]
    exact hPAbd0
  -- ## the mixed slot
  have hPBpt : ∀ p : ℝ × ℝ, PB p ≤ Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    intro p
    rw [hPBdef]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 6 f p.1 p.2 a b ha hab
  have hPBint : Integrable PB zθμ := by
    rw [hPBdef]
    refine hHkint.mono' ?_ ?_
    · exact Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed b a f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
        ((((hfso.mixed b a).continuousOn.mul (continuousOn_Wt α))).pow 2)
    · filter_upwards with p
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hPBpt p
  have hPBbd : (∫ p, PB p ∂zθμ) ≤ Work.Spaces.HkSq α 6 f := by
    rw [hPBdef]
    refine (MeasureTheory.integral_mono_ae hPBint hHkint
      (Filter.Eventually.of_forall fun p => hPBpt p)).trans (le_of_eq hHkval)
  -- ## the pure slot
  have hPCpt : ∀ p : ℝ × ℝ, PC p ≤ Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    intro p
    rw [hPCdef]
    exact Work.Spaces.sq_le_HkIntegrand_z α 6 f p.1 p.2 (b - i) hm6
  have hPCint : Integrable PC zθμ := by
    rw [hPCdef]
    refine hHkint.mono' ?_ ?_
    · have hsin : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
        intro p hp
        obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      exact Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ =>
        (Work.Spaces.DzIter (b - i) f p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (((hfso.DzIter (b - i)).continuousOn.mul (continuousOn_w_Q0.div
          (continuousOn_rpow_sin_Q0 _)
          (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsin p hp) _)))).pow 2)
    · filter_upwards with p
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hPCpt p
  have hPCbd : (∫ p, PC p ∂zθμ) ≤ Work.Spaces.HkSq α 6 f := by
    rw [hPCdef]
    refine (MeasureTheory.integral_mono_ae hPCint hHkint
      (Filter.Eventually.of_forall fun p => hPCpt p)).trans (le_of_eq hHkval)
  -- ## the majorant is integrable and its integral is bounded
  have hΦint : Integrable Φ zθμ := by
    rw [hPhidef]
    exact (((hPAint.const_mul (α ^ 2 / 2)).add hPBint).add
      (hPCint.const_mul (1 / 2))).const_mul KA
  have hΦval : (∫ p, Φ p ∂zθμ)
      = KA * ((α ^ 2 / 2 * (∫ p, PA p ∂zθμ) + (∫ p, PB p ∂zθμ))
        + 1 / 2 * (∫ p, PC p ∂zθμ)) := by
    rw [hPhidef, MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_add (f := fun p : ℝ × ℝ => α ^ 2 / 2 * PA p + PB p)
      (g := fun p : ℝ × ℝ => 1 / 2 * PC p) ((hPAint.const_mul _).add hPBint)
      (hPCint.const_mul _)]
    rw [MeasureTheory.integral_add (f := fun p : ℝ × ℝ => α ^ 2 / 2 * PA p)
      (g := fun p : ℝ × ℝ => PB p) (hPAint.const_mul _) hPBint]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hΦbnd : (∫ p, Φ p ∂zθμ) ≤ (Cq / 2 + 3 / 2) * KA * (1 + Work.Spaces.HkSq α 6 f) := by
    rw [hΦval]
    have hαsq : α ^ 2 * α ^ (-(2 : ℝ)) = 1 := by
      rw [← Real.rpow_natCast α 2, ← Real.rpow_add hα0,
        show ((2 : ℕ) : ℝ) + -(2 : ℝ) = 0 by norm_num, Real.rpow_zero]
    have h1 : α ^ 2 / 2 * (∫ p, PA p ∂zθμ) ≤ Cq / 2 * (1 + Work.Spaces.HkSq α 6 f) := by
      have h := mul_le_mul_of_nonneg_left hPAbd (by positivity : (0 : ℝ) ≤ α ^ 2 / 2)
      have h2 : α ^ 2 / 2 * (Cq * α ^ (-(2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f))
          = Cq / 2 * ((α ^ 2 * α ^ (-(2 : ℝ))) * (1 + Work.Spaces.HkSq α 6 f)) := by ring
      rw [h2, hαsq, one_mul] at h
      exact h
    have h2 : (∫ p, PB p ∂zθμ) ≤ Work.Spaces.HkSq α 6 f := hPBbd
    have h3 : 1 / 2 * (∫ p, PC p ∂zθμ) ≤ 1 / 2 * Work.Spaces.HkSq α 6 f :=
      mul_le_mul_of_nonneg_left hPCbd (by norm_num)
    have hsum : (α ^ 2 / 2 * (∫ p, PA p ∂zθμ) + (∫ p, PB p ∂zθμ))
          + 1 / 2 * (∫ p, PC p ∂zθμ)
        ≤ (Cq / 2 + 3 / 2) * (1 + Work.Spaces.HkSq α 6 f) := by
      nlinarith [h1, h2, h3, hHk0, hCqpos]
    calc KA * ((α ^ 2 / 2 * (∫ p, PA p ∂zθμ) + (∫ p, PB p ∂zθμ))
          + 1 / 2 * (∫ p, PC p ∂zθμ))
        ≤ KA * ((Cq / 2 + 3 / 2) * (1 + Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul_of_nonneg_left hsum hKA0
      _ = (Cq / 2 + 3 / 2) * KA * (1 + Work.Spaces.HkSq α 6 f) := by ring
  -- ## the pointwise domination on the open quadrant
  have hFaesm : AEStronglyMeasurable F zθμ := by
    rw [zθμ, hFdef]
    refine Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.leafGam α p.1 p.2 * Work.Spaces.mixed i a A p.1 p.2
        * Work.Spaces.DzIter (b - i) f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2) ?_
    exact ((((continuousOn_leafGam α).mul ((hAso.mixed i a).continuousOn)).mul
      ((hfso.DzIter (b - i)).continuousOn)).mul ((hfso.mixed b a).continuousOn))
  have hpt : ∀ p : ℝ × ℝ, 0 < p.1 → 0 < p.2 → p.2 < Real.pi / 2 → ‖F p‖ ≤ Φ p := by
    intro p hz hθ hθ2
    have h := mismatch_pt (α := α) (KA := KA) hα0 hKA0 (A := A) (f := f) (i := i) (a := a)
      (b := b) hcoef hz ⟨hθ, hθ2⟩
    simp only [hFdef, hPhidef, hPAdef, hPBdef, hPCdef]
    rw [Real.norm_eq_abs]
    exact h
  have hdomF : ∀ᵐ p ∂zθμ, ‖F p‖ ≤ Φ p := by
    rw [zθμ]
    exact Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ hθ2 => hpt (z, θ) hz hθ hθ2)
  have hFint : Integrable F zθμ := hΦint.mono' hFaesm hdomF
  have hFabs : |∫ p, F p ∂zθμ| ≤ ∫ p, Φ p ∂zθμ :=
    (abs_integral_le_integral_abs).trans
      (MeasureTheory.integral_mono_ae hFint.abs hΦint hdomF)
  refine ⟨hFint, ?_⟩
  exact hFabs.trans hΦbnd

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
