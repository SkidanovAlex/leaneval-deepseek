import Mathlib
import Submission.Work.BourgainPlan.Maximal.major_arc_bound_pre
import Submission.Work.BourgainPlan.Maximal.polyProfile_decay_sharp
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.rpow_decay_le_exp_decay

/-!
# Decay of the Weyl kernel on a major arc away from its centre

For an integer polynomial `P` of degree `d = P.natDegree ≥ 2` with leading coefficient
`c = P.leadingCoeff > 0`, the Weyl kernel `W_N(θ) = N⁻¹ Σ_{n<N} e(θ P(n))` (`polyWeylKernel P N θ`)
decays polynomially in `N` as soon as `θ` lies on a major arc `|cθ − (a/q + l)| ≤ N^{−(d−1/4)}`
(`1 ≤ q ≤ N^{1/4}`, `(a,q) = 1`, `l ∈ [-1,c]`) but at distance `≳ N^{−(d−χ)}` from its centre
`(a/q + l)/c`, for any `χ > 0`.

Two ingredients give the bound — and both are *exponentially* strong in `n` at `N = 2^n`, which is
why the theorem only needs `(n+1)^{−α}` for an arbitrary `α > 0`:

* the major-arc approximation `major_arc_bound_pre`:
  `‖W_N(θ) − W_{qc}(a+lq)·Φ_N(θ − (a/q+l)/c)‖ ≤ C N^{−c₀}`;
* the van der Corput decay of the profile `polyProfile_decay_sharp`:
  `‖Φ_N(β)‖ ≤ C (|β| N^d)^{−1/d}`, applied at the offset `β = θ − (a/q+l)/c`, whose modulus is
  `> (1/4) 2^{−n(d−χ)}`; hence `|β| N^d ≥ (1/4) 2^{nχ}`.

Both terms are therefore `≤ K · 2^{−γn}` for a suitable `γ = min(c₀, χ/(2d)) > 0`, and an
exponential bound of this shape eventually beats `(n+1)^{−α}`.
-/

namespace Work.BourgainPlan.Maximal

open Filter
open scoped Topology

set_option autoImplicit false

/-! ## Elementary arithmetic -/

/-- `polyDil P n = (2^n)^d` as a real power of `2`: `polyDil P n = 2^{n·d}`. -/
private lemma polyDil_eq_rpow (P : Polynomial ℤ) (n : ℕ) :
    polyDil P n = (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ)) := by
  rw [polyDil, Commons.Analysis.ExponentialSums.powDil_eq_nat]
  rw [show (((2 ^ n : ℕ)) : ℝ) = (2 : ℝ) ^ (n : ℝ) by
        push_cast; rw [Real.rpow_natCast]]
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (n : ℝ)) P.natDegree]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- `(2^n)^{-b} = 2^{-bn}`. -/
private lemma natPowTwo_rpow_neg (n : ℕ) (b : ℝ) :
    (((2 ^ n : ℕ)) : ℝ) ^ (-b) = (2 : ℝ) ^ (-(b * (n : ℝ))) := by
  rw [show (((2 ^ n : ℕ)) : ℝ) = (2 : ℝ) ^ (n : ℝ) by
        push_cast; rw [Real.rpow_natCast]]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring_nf

/-! ## The arc condition in terms of `|β| · polyDil P n` -/

/-- The distance bound `|β| > (1/4)·2^{−n(d−χ)}` propagates to
`|β| · polyDil P n ≥ (1/4)·2^{nχ}`, because `polyDil P n = 2^{nd}`. -/
private lemma arc_beta_mul_polyDil_lower (P : Polynomial ℤ) {χ β : ℝ} {n : ℕ}
    (hβ : (1 / 4 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ))) < |β|) :
    (1 / 4 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * χ) ≤ |β| * polyDil P n := by
  have hp : polyDil P n = (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ)) := polyDil_eq_rpow P n
  have hprod : (1 / 4 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ)))
        * (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ)) = (1 / 4) * (2 : ℝ) ^ ((n : ℝ) * χ) := by
    rw [mul_assoc (1 / 4), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  calc (1 / 4 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * χ)
      = (1 / 4 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ)))
          * (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ)) := hprod.symm
    _ ≤ |β| * (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ)) :=
        mul_le_mul_of_nonneg_right hβ.le (by positivity)
    _ = |β| * polyDil P n := by rw [hp]

/-- On the arc, `4 ≤ nχ` gives `1 ≤ |β| · polyDil P n`: indeed `(1/4)·2^{nχ} ≥ 1`. -/
private lemma one_le_abs_mul_polyDil (P : Polynomial ℤ) {χ β : ℝ} {n : ℕ}
    (hβ : (1 / 4 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ))) < |β|)
    (hn : 4 ≤ χ * (n : ℝ)) :
    1 ≤ |β| * polyDil P n := by
  refine le_trans ?_ (arc_beta_mul_polyDil_lower P hβ)
  have h1 : (2 : ℝ) ^ (4 : ℝ) ≤ (2 : ℝ) ^ (χ * (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hn
  have h2 : (χ * (n : ℝ)) = ((n : ℝ) * χ) := by ring
  rw [h2] at h1
  have h3 : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num
  rw [h3] at h1
  linarith

/-- The `rpow` decay of the arc quantity: `((1/4)·2^{nχ})^{−1/d} ≤ 2^{−γn}` whenever
`γ ≤ χ/(2d)` and `4 ≤ nχ`. -/
private lemma arc_pow_le_exp_decay (d : ℕ) (hd : 1 ≤ d) {χ γ : ℝ}
    (hγ : γ ≤ χ / (2 * (d : ℝ))) {n : ℕ} (hn : 4 ≤ χ * (n : ℝ)) :
    ((1 / 4 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * χ)) ^ (-(1 / (d : ℝ)))
      ≤ (2 : ℝ) ^ (-(γ * (n : ℝ))) := by
  have hd1 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h14 : (1 / 4 : ℝ) = (2 : ℝ) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hpow : (1 / 4 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * χ) = (2 : ℝ) ^ ((n : ℝ) * χ - 2) := by
    rw [h14, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; ring_nf
  rw [hpow]
  rw [← Real.rpow_mul (x := 2) (by norm_num : (0 : ℝ) ≤ 2) ((n : ℝ) * χ - 2) (-(1 / (d : ℝ)))]
  have hstep : ((n : ℝ) * χ - 2) * (-(1 / (d : ℝ))) ≤ ((n : ℝ) * χ / 2) * (-(1 / (d : ℝ))) := by
    apply mul_le_mul_of_nonpos_right
    · linarith
    · have : (0 : ℝ) < 1 / (d : ℝ) := by positivity
      linarith
  refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hstep) ?_
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2d : (0 : ℝ) < 2 * (d : ℝ) := by linarith
  have h1 : γ * (2 * (d : ℝ)) ≤ χ := (le_div_iff₀ h2d).mp hγ
  have h2 : (γ * (2 * (d : ℝ))) * (n : ℝ) ≤ χ * (n : ℝ) :=
    mul_le_mul_of_nonneg_right h1 hn0
  have hgoal : γ * (n : ℝ) ≤ (n : ℝ) * χ / (2 * (d : ℝ)) := by
    rw [le_div_iff₀ h2d]; linarith [h2]
  have h4 : ((n : ℝ) * χ / 2) * (-(1 / (d : ℝ))) = -((n : ℝ) * χ / (2 * (d : ℝ))) := by ring
  rw [h4, neg_le_neg_iff]
  exact hgoal

/-! ## The model term on the arc -/

/-- The single arc term `polyModelTermPre` decays like `2^{−γn}` on the arc, as soon as the
distance from the centre exceeds `(1/4)·2^{−n(d−χ)}`. -/
private lemma modelTermPre_decay (P : Polynomial ℤ) {χ γ Cp : ℝ}
    (hCp : 0 < Cp) (hd : 1 ≤ P.natDegree)
    (hprof : ∀ β : ℝ, β ≠ 0 → ∀ k : ℕ, 1 ≤ |β| * polyDil P k →
        ‖polyProfile P (2 ^ k) β‖ ≤ Cp * (|β| * polyDil P k) ^ (-(1 / (P.natDegree : ℝ))))
    {n : ℕ} (hn : 4 ≤ χ * (n : ℝ)) {q a : ℕ} {l : ℤ} {θ : ℝ}
    (hγχ : γ ≤ χ / (2 * (P.natDegree : ℝ)))
    (hbig : (1 / 4 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ)))
        < |θ - (((a : ℝ) / (q : ℝ) + (l : ℝ)) / (P.leadingCoeff : ℝ))|) :
    ‖polyModelTermPre P (2 ^ n) q a l θ‖ ≤ Cp * (2 : ℝ) ^ (-(γ * (n : ℝ))) := by
  set β : ℝ := θ - (((a : ℝ) / (q : ℝ) + (l : ℝ)) / (P.leadingCoeff : ℝ)) with hβdef
  have hpos : 0 < (1 / 4 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ))) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
  have hβne : β ≠ 0 := abs_pos.mp (lt_trans hpos hbig)
  have h1 : 1 ≤ |β| * polyDil P n := one_le_abs_mul_polyDil P hbig hn
  have hlow := arc_beta_mul_polyDil_lower P hbig
  have hterm : ‖polyModelTermPre P (2 ^ n) q a l θ‖ ≤ ‖polyProfile P (2 ^ n) β‖ := by
    rw [hβdef, polyModelTermPre, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_polyWeight_le_one P _ _)
  calc ‖polyModelTermPre P (2 ^ n) q a l θ‖
      ≤ ‖polyProfile P (2 ^ n) β‖ := hterm
    _ ≤ Cp * (|β| * polyDil P n) ^ (-(1 / (P.natDegree : ℝ))) := hprof β hβne n h1
    _ ≤ Cp * ((1 / 4 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * χ)) ^ (-(1 / (P.natDegree : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hCp.le
        exact Real.rpow_le_rpow_of_nonpos
          (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)) hlow
          (neg_nonpos.mpr (by positivity))
    _ ≤ Cp * (2 : ℝ) ^ (-(γ * (n : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hCp.le
        exact arc_pow_le_exp_decay P.natDegree hd hγχ hn

/-! ## The main theorem -/

theorem onArc_kernel_decay (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree)
    {χ : ℝ} (hχ0 : 0 < χ) {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (q : ℕ) (a : ℕ) (l : ℤ) (θ : ℝ),
      1 ≤ q → (q : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (1 / 4)) → a < q → Nat.gcd a q = 1 →
      l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff →
      |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ) - (l : ℝ)|
          ≤ ((2 ^ n : ℕ) : ℝ) ^ (-((P.natDegree : ℝ) - (1 : ℝ) / 4)) →
      (1 / 4 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ)))
          < |θ - (((a : ℝ) / (q : ℝ) + (l : ℝ)) / (P.leadingCoeff : ℝ))| →
      ‖Work.BourgainPlan.Maximal.polyWeylKernel P (2 ^ n) θ‖ ≤ C * ((n : ℝ) + 1) ^ (-α) := by
  obtain ⟨c₀, Cm, hc₀, hCm, happrox⟩ := major_arc_bound_pre P hc hd
  obtain ⟨Cp, hCp, hprof⟩ := polyProfile_decay_sharp P hd
  have hdR : (0 : ℝ) < (P.natDegree : ℝ) := by
    have : 0 < P.natDegree := by omega
    exact_mod_cast this
  have hdnat : 1 ≤ P.natDegree := by omega
  set γ : ℝ := min c₀ (χ / (2 * (P.natDegree : ℝ))) with hγdef
  have hγpos : 0 < γ := lt_min hc₀ (div_pos hχ0 (mul_pos (by norm_num) hdR))
  have hγc₀ : γ ≤ c₀ := min_le_left _ _
  have hγχ : γ ≤ χ / (2 * (P.natDegree : ℝ)) := min_le_right _ _
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → 4 ≤ χ * (n : ℝ) := by
    have htend : Tendsto (fun n : ℕ => χ * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hχ0
    exact eventually_atTop.1 (htend.eventually_ge_atTop 4)
  obtain ⟨Ncross, hcross⟩ :=
    rpow_decay_le_exp_decay α γ hα hγpos (Cm + Cp) (by linarith)
  refine ⟨1, by norm_num, max Ncross N₁, ?_⟩
  intro n hn q a l θ hq1 hqN haq hgcd _hl harc hbig
  have hnN : Ncross ≤ n := le_trans (le_max_left _ _) hn
  have hn₁ : N₁ ≤ n := le_trans (le_max_right _ _) hn
  have hnχ : 4 ≤ χ * (n : ℝ) := hN₁ n hn₁
  have hq14 : (q : ℝ) ≤ (((2 ^ n : ℕ)) : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [show (((2 ^ n : ℕ)) : ℝ) = (2 : ℝ) ^ (n : ℝ) by
          push_cast; rw [Real.rpow_natCast]]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact hqN
  have hdiff : ‖polyWeylKernel P (2 ^ n) θ - polyModelTermPre P (2 ^ n) q a l θ‖
      ≤ Cm * (2 : ℝ) ^ (-(γ * (n : ℝ))) := by
    have h := happrox (2 ^ n) q a l θ hq1 hq14 haq hgcd harc
    calc ‖polyWeylKernel P (2 ^ n) θ - polyModelTermPre P (2 ^ n) q a l θ‖
        ≤ Cm * (((2 ^ n : ℕ)) : ℝ) ^ (-c₀) := h
      _ = Cm * (2 : ℝ) ^ (-(c₀ * (n : ℝ))) := by rw [natPowTwo_rpow_neg]
      _ ≤ Cm * (2 : ℝ) ^ (-(γ * (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hCm.le
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith [hγc₀, hn0]
  have hmod : ‖polyModelTermPre P (2 ^ n) q a l θ‖ ≤ Cp * (2 : ℝ) ^ (-(γ * (n : ℝ))) :=
    modelTermPre_decay (P := P) (hCp := hCp) (hd := hdnat) (hprof := hprof)
      (hn := hnχ) (hγχ := hγχ) (hbig := hbig)
  have hsplit : ‖polyWeylKernel P (2 ^ n) θ‖
      ≤ ‖polyWeylKernel P (2 ^ n) θ - polyModelTermPre P (2 ^ n) q a l θ‖
        + ‖polyModelTermPre P (2 ^ n) q a l θ‖ := by
    calc ‖polyWeylKernel P (2 ^ n) θ‖
        = ‖(polyWeylKernel P (2 ^ n) θ - polyModelTermPre P (2 ^ n) q a l θ)
            + polyModelTermPre P (2 ^ n) q a l θ‖ := by ring_nf
      _ ≤ ‖polyWeylKernel P (2 ^ n) θ - polyModelTermPre P (2 ^ n) q a l θ‖
            + ‖polyModelTermPre P (2 ^ n) q a l θ‖ := norm_add_le _ _
  calc ‖polyWeylKernel P (2 ^ n) θ‖
      ≤ ‖polyWeylKernel P (2 ^ n) θ - polyModelTermPre P (2 ^ n) q a l θ‖
        + ‖polyModelTermPre P (2 ^ n) q a l θ‖ := hsplit
    _ ≤ Cm * (2 : ℝ) ^ (-(γ * (n : ℝ))) + Cp * (2 : ℝ) ^ (-(γ * (n : ℝ))) :=
        add_le_add hdiff hmod
    _ = (Cm + Cp) * (2 : ℝ) ^ (-(γ * (n : ℝ))) := by ring
    _ ≤ ((n : ℝ) + 1) ^ (-α) := hcross n hnN
    _ = 1 * ((n : ℝ) + 1) ^ (-α) := by ring

end Work.BourgainPlan.Maximal
