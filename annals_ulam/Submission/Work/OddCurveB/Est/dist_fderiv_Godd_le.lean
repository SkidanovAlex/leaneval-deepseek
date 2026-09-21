import Mathlib
import Submission.Work.OddCurveB.Existence.Box
import Submission.Work.OddCurveB.Est.differentiableAt_Godd

/-!
# The `fderiv` of the perturbed odd Volterra map is close to the base linearization

`Godd n h s z` depends on the perturbation `h` only through the two numbers `(h s, h'(s))`
(`Work.OddCurveB.Existence.Godd_eq_GoddDiag`), and the diagonal system is the explicit
function `GoddDiag n s (h s) (h' s) z` of its arguments.  Because the diagonal Abel kernels
are "power times square root" functions of the polynomial radicand `Drad s hs hp t`, the map

`Φ : ((ℝ × ℝ × ℝ) × St) → (St →L[ℝ] St)`,
`Φ ((s, hs, hp), z) = fderiv ℝ (fun w => GoddDiag n s hs hp w) z`

is **continuous** (`continuous_fderiv_GoddDiag`): `GoddDiag` is `C¹` in all of its variables,
which reduces to the `C¹`-regularity of `x ↦ x ^ k √x` (`contDiff_pow_mul_sqrt`) via the
identity `x ^ k * √x = x ^ (k + 1/2)` and Mathlib's `Real.contDiff_rpow_const_of_le`.

Uniform continuity of `Φ` on a compact box then gives the estimate: for every tolerance `τ`
there is `ε > 0` such that any bump `h` with `|h| ≤ ε`, `|h'| ≤ ε` has

`‖fderiv (Godd n h s) z - fderiv (Godd n 0 s) (baseState s)‖ ≤ Cg ‖z - baseState s‖ + τ`

for all `s ∈ [a,b]` and all `z` in the unit ball around `baseState s` — the hypothesis
`hclD` of the long-interval Volterra engine `Work.VolterraLong.volterra_long_exists`
(see `Work.VolterraLong.Corollaries.Odd.odd_volterra_long_exists`).
-/

namespace Work.OddCurveB.Est

open Work.OddVolterra
open Work.OddCurveB.Existence

noncomputable section

/-! ## `x ↦ x ^ k √x` and its `C¹`-regularity

The key point is that `x ↦ x ^ k √x` is *globally* `C¹` for `k ≥ 1`, including at `0` and on
the negative half-line, where `Real.sqrt` is `0` and the function is locally constant.  This is
immediate from the rpow identity `x ^ k √x = x ^ (k + 1/2)`: for `x < 0` the extra factor
`cos ((k + 1/2) π) = 0` kills the rpow. -/

lemma pow_mul_sqrt_eq_rpow (k : ℕ) (u : ℝ) : u ^ k * Real.sqrt u = u ^ ((k : ℝ) + 1 / 2) := by
  rcases lt_trichotomy u 0 with hlt | rfl | hlt
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt hlt), mul_zero, Real.rpow_def_of_neg hlt]
    have hcos : Real.cos (((k : ℝ) + 1 / 2) * Real.pi) = 0 := by
      have h1 : ((k : ℝ) + 1 / 2) * Real.pi = Real.pi / 2 + ((k : ℤ) : ℝ) * Real.pi := by
        push_cast; ring
      rw [h1, Real.cos_add_int_mul_pi]; simp
    rw [hcos, mul_zero]
  · rw [Real.sqrt_zero, mul_zero]
    exact (Real.zero_rpow (by positivity : ((k : ℝ) + 1 / 2) ≠ 0)).symm
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hlt]

lemma contDiff_pow_mul_sqrt {k : ℕ} (hk : 1 ≤ k) :
    ContDiff ℝ 1 (fun u : ℝ => u ^ k * Real.sqrt u) := by
  rw [show (fun u : ℝ => u ^ k * Real.sqrt u) = fun u : ℝ => u ^ ((k : ℝ) + 1 / 2)
      from funext (pow_mul_sqrt_eq_rpow k)]
  refine Real.contDiff_rpow_const_of_le (p := (k : ℝ) + 1 / 2) (n := 1) ?_
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  linarith

/-! ## The diagonal Abel kernels are `C¹` in all of their variables -/

lemma contDiff_Kdiag1 (n : ℕ) (hn : 1 ≤ n) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ × ℝ × ℝ => Kdiag1 n p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have h : (fun p : ℝ × ℝ × ℝ × ℝ => Kdiag1 n p.1 p.2.1 p.2.2.1 p.2.2.2)
      = fun p : ℝ × ℝ × ℝ × ℝ =>
          ((Nat.doubleFactorial (2 * n + 1) : ℝ) * (-1) ^ (n + 1) / Real.sqrt 2) *
            (Drad p.1 p.2.1 p.2.2.1 p.2.2.2 ^ n *
              Real.sqrt (Drad p.1 p.2.1 p.2.2.1 p.2.2.2)) := by
    funext p
    exact Kdiag1_eq n p.1 p.2.1 p.2.2.1 p.2.2.2
  rw [h]
  have hD : ContDiff ℝ 1 (fun p : ℝ × ℝ × ℝ × ℝ => Drad p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    unfold Drad; fun_prop
  have hcomp : ContDiff ℝ 1 (fun p : ℝ × ℝ × ℝ × ℝ =>
      Drad p.1 p.2.1 p.2.2.1 p.2.2.2 ^ n * Real.sqrt (Drad p.1 p.2.1 p.2.2.1 p.2.2.2)) := by
    simpa [Function.comp_def] using (contDiff_pow_mul_sqrt hn).comp hD
  exact contDiff_const.mul hcomp

lemma contDiff_Kdiag2 (n : ℕ) (hn : 2 ≤ n) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ × ℝ × ℝ => Kdiag2 n p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have h : (fun p : ℝ × ℝ × ℝ × ℝ => Kdiag2 n p.1 p.2.1 p.2.2.1 p.2.2.2)
      = fun p : ℝ × ℝ × ℝ × ℝ =>
          ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-1) ^ n / Real.sqrt 2) *
            (Drad p.1 p.2.1 p.2.2.1 p.2.2.2 ^ (n - 1) *
              Real.sqrt (Drad p.1 p.2.1 p.2.2.1 p.2.2.2)) * (p.2.2.2 + p.2.2.1) := by
    funext p
    exact Kdiag2_eq n (by omega) p.1 p.2.1 p.2.2.1 p.2.2.2
  rw [h]
  have hD : ContDiff ℝ 1 (fun p : ℝ × ℝ × ℝ × ℝ => Drad p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    unfold Drad; fun_prop
  have hcomp : ContDiff ℝ 1 (fun p : ℝ × ℝ × ℝ × ℝ =>
      Drad p.1 p.2.1 p.2.2.1 p.2.2.2 ^ (n - 1) *
        Real.sqrt (Drad p.1 p.2.1 p.2.2.1 p.2.2.2)) := by
    simpa [Function.comp_def] using (contDiff_pow_mul_sqrt (k := n - 1) (by omega)).comp hD
  have hlin : ContDiff ℝ 1 (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.2 + p.2.2.1) := by fun_prop
  exact (contDiff_const.mul hcomp).mul hlin

/-! ## `GoddDiag` is `C¹` in all of its variables -/

lemma contDiff_GoddDiag_all (n : ℕ) (hn : 2 ≤ n) :
    ContDiff ℝ 1 (fun q : ((ℝ × ℝ × ℝ) × St) × St =>
      GoddDiag n q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.2) := by
  have hfun : (fun q : ((ℝ × ℝ × ℝ) × St) × St => GoddDiag n q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.2)
      = fun q : ((ℝ × ℝ × ℝ) × St) × St =>
        ![q.2 0, q.2 1,
          -(Work.OddCurveB.Existence.abelMass *
            (-(Kdiag1 n q.1.1.1 q.1.1.2.1 q.1.1.2.2 (-(q.2 0)) * q.2 2 +
                Kdiag1 n q.1.1.1 q.1.1.2.1 q.1.1.2.2 (q.2 1) * q.2 3))),
          -(Work.OddCurveB.Existence.abelMass *
            (-(Kdiag2 n q.1.1.1 q.1.1.2.1 q.1.1.2.2 (-(q.2 0)) * q.2 2 +
                Kdiag2 n q.1.1.1 q.1.1.2.1 q.1.1.2.2 (q.2 1) * q.2 3)))] := rfl
  rw [hfun, contDiff_pi]
  intro i
  fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.reduceFinMk]
  · fun_prop
  · fun_prop
  · have hA : ContDiff ℝ 1 (fun q : ((ℝ × ℝ × ℝ) × St) × St =>
        Kdiag1 n q.1.1.1 q.1.1.2.1 q.1.1.2.2 (-(q.2 0))) := by
      have hφ : ContDiff ℝ 1 (fun q : ((ℝ × ℝ × ℝ) × St) × St =>
          ((q.1.1.1, q.1.1.2.1, q.1.1.2.2, -(q.2 0)) : ℝ × ℝ × ℝ × ℝ)) := by fun_prop
      simpa [Function.comp_def] using (contDiff_Kdiag1 n (by omega)).comp hφ
    have hB : ContDiff ℝ 1 (fun q : ((ℝ × ℝ × ℝ) × St) × St =>
        Kdiag1 n q.1.1.1 q.1.1.2.1 q.1.1.2.2 (q.2 1)) := by
      have hφ : ContDiff ℝ 1 (fun q : ((ℝ × ℝ × ℝ) × St) × St =>
          ((q.1.1.1, q.1.1.2.1, q.1.1.2.2, q.2 1) : ℝ × ℝ × ℝ × ℝ)) := by fun_prop
      simpa [Function.comp_def] using (contDiff_Kdiag1 n (by omega)).comp hφ
    have h2 : ContDiff ℝ 1 (fun q : ((ℝ × ℝ × ℝ) × St) × St => q.2 2) := by fun_prop
    have h3 : ContDiff ℝ 1 (fun q : ((ℝ × ℝ × ℝ) × St) × St => q.2 3) := by fun_prop
    have h := (((hA.mul h2).add (hB.mul h3)).neg).const_smul
      (Work.OddCurveB.Existence.abelMass)
    simpa [smul_eq_mul] using h.neg
  · have hA : ContDiff ℝ 1 (fun q : ((ℝ × ℝ × ℝ) × St) × St =>
        Kdiag2 n q.1.1.1 q.1.1.2.1 q.1.1.2.2 (-(q.2 0))) := by
      have hφ : ContDiff ℝ 1 (fun q : ((ℝ × ℝ × ℝ) × St) × St =>
          ((q.1.1.1, q.1.1.2.1, q.1.1.2.2, -(q.2 0)) : ℝ × ℝ × ℝ × ℝ)) := by fun_prop
      simpa [Function.comp_def] using (contDiff_Kdiag2 n hn).comp hφ
    have hB : ContDiff ℝ 1 (fun q : ((ℝ × ℝ × ℝ) × St) × St =>
        Kdiag2 n q.1.1.1 q.1.1.2.1 q.1.1.2.2 (q.2 1)) := by
      have hφ : ContDiff ℝ 1 (fun q : ((ℝ × ℝ × ℝ) × St) × St =>
          ((q.1.1.1, q.1.1.2.1, q.1.1.2.2, q.2 1) : ℝ × ℝ × ℝ × ℝ)) := by fun_prop
      simpa [Function.comp_def] using (contDiff_Kdiag2 n hn).comp hφ
    have h2 : ContDiff ℝ 1 (fun q : ((ℝ × ℝ × ℝ) × St) × St => q.2 2) := by fun_prop
    have h3 : ContDiff ℝ 1 (fun q : ((ℝ × ℝ × ℝ) × St) × St => q.2 3) := by fun_prop
    have h := (((hA.mul h2).add (hB.mul h3)).neg).const_smul
      (Work.OddCurveB.Existence.abelMass)
    simpa [smul_eq_mul] using h.neg

/-! ## Continuity of `((s,hs,hp),z) ↦ fderiv (GoddDiag n s hs hp ·) z` -/

theorem continuous_fderiv_GoddDiag (n : ℕ) (hn : 2 ≤ n) :
    Continuous (fun e : (ℝ × ℝ × ℝ) × St =>
      fderiv ℝ (fun w : St => GoddDiag n e.1.1 e.1.2.1 e.1.2.2 w) e.2) := by
  have h := Continuous.fderiv (𝕜 := ℝ) (n := (1 : WithTop ℕ∞))
    (f := fun e : (ℝ × ℝ × ℝ) × St => fun w : St => GoddDiag n e.1.1 e.1.2.1 e.1.2.2 w)
    (g := fun e : (ℝ × ℝ × ℝ) × St => e.2)
    (contDiff_GoddDiag_all n hn) continuous_snd le_rfl
  exact h

/-! ## The profile is smooth, so the base state is continuous -/

lemma contDiff_profileX_est : ContDiff ℝ (⊤ : ℕ∞) Commons.Geometry.Ulam.profileX := by
  show ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => 1 / Real.sqrt (1 + s ^ 2))
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Real.sqrt (1 + s ^ 2)) :=
    ((contDiff_const.add (contDiff_id.pow 2)) : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => 1 + s ^ 2)).sqrt
      (fun s => by positivity)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (Real.sqrt (1 + s ^ 2))⁻¹) :=
    h1.inv (fun s => by positivity)
  simpa [one_div] using h2

lemma continuous_baseState : Continuous Work.OddVolterra.baseState := by
  have hfun : Work.OddVolterra.baseState =
      fun s : ℝ => ![Commons.Geometry.Ulam.profileX s, Commons.Geometry.Ulam.profileX s,
        deriv Commons.Geometry.Ulam.profileX s, deriv Commons.Geometry.Ulam.profileX s] := rfl
  rw [hfun]
  refine continuous_pi (fun i => ?_)
  have hc : Continuous Commons.Geometry.Ulam.profileX :=
    contDiff_profileX_est.continuous
  have hd : Continuous (deriv Commons.Geometry.Ulam.profileX) :=
    contDiff_profileX_est.continuous_deriv (by simp)
  fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.reduceFinMk]
  · exact hc
  · exact hc
  · exact hd
  · exact hd

/-! ## The estimate -/

theorem dist_fderiv_Godd_le (n : ℕ) (hn : 2 ≤ n) {a b : ℝ} (hab : a ≤ b) (Cg : ℝ) (hCg : 0 ≤ Cg)
    (hbase_lip : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState s) 1,
      ‖fderiv ℝ (fun w => Work.OddVolterra.Godd n 0 s w) z -
       fderiv ℝ (fun w => Work.OddVolterra.Godd n 0 s w) (Work.OddVolterra.baseState s)‖
        ≤ Cg * ‖z - Work.OddVolterra.baseState s‖) :
    ∀ τ > 0, ∃ ε > 0, ∀ h : ℝ → ℝ,
      (∀ s : ℝ, |h s| ≤ ε) → (∀ s : ℝ, |deriv h s| ≤ ε) →
      ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState s) 1,
        ‖fderiv ℝ (fun w => Work.OddVolterra.Godd n h s w) z -
         fderiv ℝ (fun w => Work.OddVolterra.Godd n 0 s w) (Work.OddVolterra.baseState s)‖
          ≤ Cg * ‖z - Work.OddVolterra.baseState s‖ + τ := by
  intro τ hτ
  -- the base state stays in a fixed ball of finite radius
  obtain ⟨s₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab)
    (continuous_baseState.norm).continuousOn
  set R : ℝ := ‖baseState s₀‖ + 1 with hR
  -- the compact box on which the linearization is uniformly continuous
  have hKc : IsCompact ((Set.Icc a b ×ˢ (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1))
      ×ˢ Metric.closedBall (0 : St) R) :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod (isCompact_closedBall 0 R)
  obtain ⟨γ, hγ, hunif⟩ := Metric.uniformContinuousOn_iff_le.mp
    (hKc.uniformContinuousOn_of_continuous (continuous_fderiv_GoddDiag n hn).continuousOn) τ hτ
  refine ⟨min γ 1, lt_min hγ one_pos, ?_⟩
  intro h hh hh' s hs z hz
  have hhs1 : |h s| ≤ 1 := le_trans (hh s) (min_le_right _ _)
  have hhp1 : |deriv h s| ≤ 1 := le_trans (hh' s) (min_le_right _ _)
  have hhsγ : |h s| ≤ γ := le_trans (hh s) (min_le_left _ _)
  have hhpγ : |deriv h s| ≤ γ := le_trans (hh' s) (min_le_left _ _)
  have hzR : z ∈ Metric.closedBall (0 : St) R := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hsplit : ‖z‖ ≤ ‖z - baseState s‖ + ‖baseState s‖ := by
      calc ‖z‖ = ‖(z - baseState s) + baseState s‖ := by ring_nf
        _ ≤ ‖z - baseState s‖ + ‖baseState s‖ := norm_add_le _ _
    have hzs : ‖z - baseState s‖ ≤ 1 := by
      have h' := hz; rw [Metric.mem_closedBall, dist_eq_norm] at h'; exact h'
    have hbs : ‖baseState s‖ ≤ ‖baseState s₀‖ := hmax hs
    rw [hR]; linarith
  have hmem : (((s, h s, deriv h s) : ℝ × ℝ × ℝ), z) ∈
      (Set.Icc a b ×ˢ (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)) ×ˢ
        Metric.closedBall (0 : St) R :=
    ⟨⟨hs, ⟨(abs_le.mp hhs1).1, (abs_le.mp hhs1).2⟩,
      ⟨(abs_le.mp hhp1).1, (abs_le.mp hhp1).2⟩⟩, hzR⟩
  have hmem0 : (((s, 0, 0) : ℝ × ℝ × ℝ), z) ∈
      (Set.Icc a b ×ˢ (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)) ×ˢ
        Metric.closedBall (0 : St) R :=
    ⟨⟨hs, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩, hzR⟩
  have hdist : dist (((s, h s, deriv h s) : ℝ × ℝ × ℝ), z)
      (((s, 0, 0) : ℝ × ℝ × ℝ), z) ≤ γ := by
    rw [dist_pt]
    exact max_le hhsγ hhpγ
  have hclose := hunif _ hmem _ hmem0 hdist
  rw [dist_eq_norm] at hclose
  have hclose' : ‖fderiv ℝ (fun w : St => Godd n h s w) z -
      fderiv ℝ (fun w : St => Godd n 0 s w) z‖ ≤ τ := by
    rw [show (fun w : St => Godd n h s w)
          = (fun w : St => GoddDiag n s (h s) (deriv h s) w) from
        funext fun w => Godd_eq_GoddDiag n h s w,
      show (fun w : St => Godd n 0 s w) = (fun w : St => GoddDiag n s 0 0 w) from
        funext fun w => Godd_zero_eq n s w]
    exact hclose
  calc ‖fderiv ℝ (fun w : St => Godd n h s w) z -
        fderiv ℝ (fun w : St => Godd n 0 s w) (baseState s)‖
      ≤ ‖fderiv ℝ (fun w : St => Godd n h s w) z - fderiv ℝ (fun w : St => Godd n 0 s w) z‖ +
        ‖fderiv ℝ (fun w : St => Godd n 0 s w) z -
          fderiv ℝ (fun w : St => Godd n 0 s w) (baseState s)‖ := by
        have hsplit : fderiv ℝ (fun w : St => Godd n h s w) z -
              fderiv ℝ (fun w : St => Godd n 0 s w) (baseState s)
            = (fderiv ℝ (fun w : St => Godd n h s w) z - fderiv ℝ (fun w : St => Godd n 0 s w) z)
              + (fderiv ℝ (fun w : St => Godd n 0 s w) z -
                  fderiv ℝ (fun w : St => Godd n 0 s w) (baseState s)) := by abel
        rw [hsplit]
        exact norm_add_le _ _
    _ ≤ τ + Cg * ‖z - baseState s‖ := add_le_add hclose' (hbase_lip s hs z hz)
    _ = Cg * ‖z - baseState s‖ + τ := by ring

end

end Work.OddCurveB.Est
