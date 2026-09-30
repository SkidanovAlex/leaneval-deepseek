import Mathlib
import Submission.Vinogradov.Extension
import Submission.Commons.Analysis.Integral.lp_ell2_minkowski_real
import Submission.Commons.Analysis.Inequalities.holder_prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open MeasureTheory Complex
open scoped Real BigOperators Interval

namespace Submission.Vinogradov
open Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# Ball inflation (BDG §6, the `k = n` companion of Theorem `nt4`)

Bourgain–Demeter–Guth, *Proof of the main conjecture in Vinogradov's mean value
theorem for degrees higher than three*, Ann. of Math. 184 (2016), §6 ends with
the inequality

    (1/|𝓑|) Σ_{Δ∈𝓑} [Π_{i=1}^{M_n} (Σ_{J_i⊂I_i, |J_i|=ρ} ‖E_{J_i} g‖²_{Lᵖ_♯(w_Δ)})^{1/2}]^{p/M_n}
      ≲ [Π_{i=1}^{M_n} (Σ_{J_i⊂I_i, |J_i|=ρ} ‖E_{J_i} g‖²_{Lᵖ_♯(w_B)})^{1/2}]^{p/M_n},

which "will work as a substitute for Theorem nt4 when `k = n`": it is the
ball-inflation step used in the iteration scheme of §8, and it is *not* a
decoupling inequality (the intervals `J_i` are the same on both sides; only the
ball on the left is smaller).  Its proof is the paper's displayed Minkowski
inequality

    Σ_i (Σ_k ‖f_k‖²_{Lᵖ(w_i)})^{p/2} ≤ (Σ_k ‖f_k‖²_{Lᵖ(Σ_i w_i)})^{p/2}

(valid for `p ≥ 2`) together with the finitely-overlapping-cover bound
`Σ_Δ w_Δ ≲ w_B`.

`ball_inflation_kn` below is the *single-factor* inequality in the
unnormalised weighted `Lᵖ` language of this development
(`wLpPow k c R p f = ∫ ‖f‖ᵖ w_{B(c,R)}`), and `ball_inflation_kn_multi` is the
`M_n`-fold version, phrased exactly in the shape of the display above (with the
paper's `Lᵖ_♯(w)` normalisation replaced by unnormalised `wLpPow`, which only
changes the *normalisation* of the two sides, see the remark below).

## Remark on the normalisation

The two sides of the display above are normalised differently in the paper
(`Lᵖ_♯(w_Δ)` averages over `|Δ|`, `Lᵖ_♯(w_B)` over `|B|`, while the sum on the
left is divided by the *cardinality* `|𝓑|`).  With the paper's normalisation
this is only consistent when a factor `(|B|/|Δ|)^{p/2−1}` — a power of the
scale ratio — is ignored, which is exactly the kind of factor that the `δ^{-ε}`
bookkeeping of §8 can absorb, but which is not `1` for `p > 2`.  The
statements formalised here therefore use the *unnormalised* powers `wLpPow`
throughout: on that scale the inequality is exactly true with no hidden
normalisation factor, and the `♯`-normalised form is recovered by multiplying
the two sides by the appropriate (scale-dependent) powers of `|B|`, `|Δ|`.
-/

lemma integrable_count_fin (m : ℕ) (f : Fin m → ℝ) :
    Integrable f (Measure.count : Measure (Fin m)) := by
  rw [integrable_count_iff]
  exact (hasSum_fintype fun i => ‖f i‖).summable

lemma mixed_norm_minkowski_fin {κ : Type*} [Fintype κ] {m : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (b : κ → Fin m → ℝ) (hb : ∀ J i, 0 ≤ b J i) :
    (∑ i : Fin m, (∑ J : κ, (b J i) ^ 2) ^ (p / 2)) ^ (1 / p)
      ≤ (∑ J : κ, (∑ i : Fin m, (b J i) ^ p) ^ (2 / p)) ^ ((1:ℝ) / 2) := by
  have h := Commons.Analysis.Integral.lp_ell2_minkowski_real (μ := (Measure.count : Measure (Fin m)))
      hp (F := fun J i => b J i) (fun J i => hb J i)
      (fun J => integrable_count_fin m _) (integrable_count_fin m _)
  simpa [MeasureTheory.integral_count] using h

/-- If `w_{c'}` is pointwise dominated by a multiple of `w_B`, integrability with
respect to `w_B` transfers to integrability with respect to `w_{c'}`. -/
lemma integrable_mul_ballWeight_of_le (n : ℕ) (c : E n) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    {C : ℝ} {c' : E n}
    (hle : ∀ x : E n, ballWeight n c' r x ≤ C * ballWeight n c R x)
    {p : ℝ} {f : E n → ℂ}
    (hint : Integrable (fun x : E n => ‖f x‖ ^ p * ballWeight n c R x) volume) :
    Integrable (fun x : E n => ‖f x‖ ^ p * ballWeight n c' r x) volume := by
  have hA : AEMeasurable (fun x : E n => ‖f x‖ ^ p) volume := by
    have hprod : AEMeasurable (fun x : E n => ‖f x‖ ^ p * ballWeight n c R x) volume :=
      hint.aemeasurable
    have hw : AEMeasurable (fun x : E n => ballWeight n c R x) volume :=
      (ballWeight_continuous n c hR).aemeasurable
    have hdiv := hprod.div hw
    refine hdiv.congr ?_
    filter_upwards with x
    have hne : ballWeight n c R x ≠ 0 := ne_of_gt (ballWeight_pos n c hR x)
    simp only [Pi.div_apply]
    exact mul_div_cancel_right₀ _ hne
  refine Integrable.mono' (hint.const_mul C) (hA.mul (ballWeight_continuous n c' hr).aemeasurable).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) p) (le_of_lt (ballWeight_pos n c' hr x)))]
  calc ‖f x‖ ^ p * ballWeight n c' r x
      ≤ ‖f x‖ ^ p * (C * ballWeight n c R x) :=
        mul_le_mul_of_nonneg_left (hle x) (Real.rpow_nonneg (norm_nonneg _) p)
    _ = C * (‖f x‖ ^ p * ballWeight n c R x) := by ring


/-- The weighted `Lᵖ` power is nonnegative. -/
lemma wLpPow_nonneg (n : ℕ) (c : E n) {R : ℝ} (hR : 0 < R) (p : ℝ) (f : E n → ℂ) :
    0 ≤ wLpPow n c R p f := by
  unfold wLpPow
  exact integral_nonneg (fun x => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) p)
    (le_of_lt (ballWeight_pos n c hR x)))


/-- **Ball inflation, single family** (the `k = n` case of BDG §6, Thm `nt4`'s
companion inequality).  If the balls `Δᵢ = B(c'ᵢ, r)` form a separated cover of
the comparison ball `B(c,R)` (`r ≤ R`, centres in `B(c,R)`, `r`-separated), then
for every `p ≥ 2` the `ℓ²`-decoupling sum over the cover is dominated by the
single comparison sum:

  `(1/m) Σᵢ (Σ_J ‖E_J g‖²_{Lᵖ(w_{Δᵢ})})^{p/2} ≤ C (Σ_J ‖E_J g‖²_{Lᵖ(w_B)})^{p/2}`,

with a constant `C` independent of `p`, `g`, the interval family and the scale.
This is the paper's displayed Minkowski inequality combined with
`Σᵢ w_{Δᵢ} ≤ C w_B`. -/

theorem ball_inflation_kn (n : ℕ) (hn : 1 ≤ n) (c : E n) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ R) (m : ℕ) (c' : Fin m → E n)
    (hcen : ∀ i, ‖c' i - c‖ ≤ R) (hsep : ∀ i j, i ≠ j → r ≤ ‖c' i - c' j‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℝ) (hp : 2 ≤ p) {κ : Type*} [Fintype κ] (a b : κ → ℝ) (g : ℝ → ℂ),
      (∀ J : κ, Integrable (fun x : E n => ‖extOp n g (a J) (b J) x‖ ^ p * ballWeight n c R x) volume) →
      (1 / (m : ℝ)) * (∑ i : Fin m, (∑ J : κ, (wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2))
        ≤ C * (∑ J : κ, (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2) := by
  obtain ⟨C, hC0, hcover⟩ := ballWeight_sum_cover_le_uniform n hn c hR hr hrR c' hcen hsep
  refine ⟨C, hC0, ?_⟩
  intro p hp κ _ a b g hint
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  -- (1) pointwise domination of each small weight by the comparison weight
  have hwi : ∀ i : Fin m, ∀ x : E n, ballWeight n (c' i) r x ≤ C * ballWeight n c R x := by
    intro i x
    have h1 : ballWeight n (c' i) r x ≤ ∑ j : Fin m, ballWeight n (c' j) r x :=
      Finset.single_le_sum (fun j _ => le_of_lt (ballWeight_pos n (c' j) hr x)) (Finset.mem_univ i)
    exact le_trans h1 (hcover x)
  -- (2) integrability in each small weight
  have hint2 : ∀ (J : κ) (i : Fin m),
      Integrable (fun x : E n => ‖extOp n g (a J) (b J) x‖ ^ p * ballWeight n (c' i) r x) volume :=
    fun J i => integrable_mul_ballWeight_of_le n c hR hr (hwi i) (hint J)
  -- (3) the cover-sum bound, for each interval
  have hsum : ∀ J : κ, ∑ i : Fin m, wLpPow n (c' i) r p (extOp n g (a J) (b J))
      ≤ C * wLpPow n c R p (extOp n g (a J) (b J)) :=
    fun J => wLpPow_sum_le_of_cover n c hR hr c' hC0 hcover (le_of_lt hp0) _
      (fun i => hint2 J i) (hint J)
  -- (4) nonnegativity
  have wnn : ∀ (J : κ) (i : Fin m), 0 ≤ wLpPow n (c' i) r p (extOp n g (a J) (b J)) :=
    fun J i => wLpPow_nonneg n (c' i) hr p _
  have wnnB : ∀ J : κ, 0 ≤ wLpPow n c R p (extOp n g (a J) (b J)) :=
    fun J => wLpPow_nonneg n c hR p _
  -- (5) the mixed-norm Minkowski step
  set B : κ → Fin m → ℝ := fun J i => (wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (1 / p) with hBdef
  have hBnn : ∀ J i, 0 ≤ B J i := fun J i => Real.rpow_nonneg (wnn J i) _
  have hmink := mixed_norm_minkowski_fin (κ := κ) hp B hBnn
  have hsq : ∀ (J : κ) (i : Fin m), (B J i) ^ 2
      = (wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p) := by
    intro J i
    rw [hBdef]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (wnn J i)]
    congr 1
    ring
  have hpw : ∀ (J : κ) (i : Fin m), (B J i) ^ p = wLpPow n (c' i) r p (extOp n g (a J) (b J)) := by
    intro J i
    show ((wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (1 / p)) ^ p = _
    rw [← Real.rpow_mul (wnn J i) (1 / p) p, div_mul_cancel₀ 1 (ne_of_gt hp0), Real.rpow_one]
  have hstep1 : (∑ i : Fin m, (∑ J : κ, (wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2)) ^ (1 / p)
      ≤ (∑ J : κ, (∑ i : Fin m, wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)) ^ ((1:ℝ) / 2) := by
    simpa only [hsq, hpw] using hmink
  -- (6) the cover-sum substitution
  have hinner : ∀ J : κ, (∑ i : Fin m, wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)
      ≤ C ^ (2 / p) * (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p) := by
    intro J
    have h0 : 0 ≤ ∑ i : Fin m, wLpPow n (c' i) r p (extOp n g (a J) (b J)) :=
      Finset.sum_nonneg (fun i _ => wnn J i)
    calc (∑ i : Fin m, wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)
        ≤ (C * wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p) :=
          Real.rpow_le_rpow h0 (hsum J) (by positivity)
      _ = C ^ (2 / p) * (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p) :=
          Real.mul_rpow (le_of_lt hC0) (wnnB J)
  have hstep2 : (∑ J : κ, (∑ i : Fin m, wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)) ^ ((1:ℝ) / 2)
      ≤ C ^ (1 / p) * (∑ J : κ, (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ ((1:ℝ) / 2) := by
    have hsumle : (∑ J : κ, (∑ i : Fin m, wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p))
        ≤ ∑ J : κ, C ^ (2 / p) * (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p) :=
      Finset.sum_le_sum (fun J _ => hinner J)
    have h0 : 0 ≤ ∑ J : κ, (∑ i : Fin m, wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p) :=
      Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => wnn J i)) _)
    calc (∑ J : κ, (∑ i : Fin m, wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)) ^ ((1:ℝ) / 2)
        ≤ (∑ J : κ, C ^ (2 / p) * (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ ((1:ℝ) / 2) :=
          Real.rpow_le_rpow h0 hsumle (by norm_num)
      _ = (C ^ (2 / p) * ∑ J : κ, (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ ((1:ℝ) / 2) := by
          rw [Finset.mul_sum]
      _ = (C ^ (2 / p)) ^ ((1:ℝ) / 2) * (∑ J : κ, (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ ((1:ℝ) / 2) :=
          Real.mul_rpow (Real.rpow_nonneg (le_of_lt hC0) _) (Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (wnnB J) _))
      _ = C ^ (1 / p) * (∑ J : κ, (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ ((1:ℝ) / 2) := by
          congr 1
          rw [← Real.rpow_mul (le_of_lt hC0)]
          congr 1
          field_simp
  -- (7) assemble, raising to the p-th power
  have hA0 : 0 ≤ ∑ i : Fin m, (∑ J : κ, (wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2) :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (wnn J i) _)) _)
  have hB0 : 0 ≤ (∑ J : κ, (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2) :=
    Real.rpow_nonneg (Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (wnnB J) _)) _
  have h1 : (∑ i : Fin m, (∑ J : κ, (wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2)) ^ (1 / p)
      ≤ C ^ (1 / p) * (∑ J : κ, (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ ((1:ℝ) / 2) :=
    le_trans hstep1 hstep2
  have hZ0 : 0 ≤ C ^ (1 / p) * (∑ J : κ, (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ ((1:ℝ) / 2) :=
    mul_nonneg (Real.rpow_nonneg (le_of_lt hC0) _)
      (Real.rpow_nonneg (Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (wnnB J) _)) _)
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hA0 _) h1 (le_of_lt hp0)
  have h3 : ((∑ i : Fin m, (∑ J : κ, (wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2)) ^ (1 / p)) ^ p
      = ∑ i : Fin m, (∑ J : κ, (wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2) := by
    rw [← Real.rpow_mul hA0 (1 / p) p, div_mul_cancel₀ 1 (ne_of_gt hp0), Real.rpow_one]
  have h4 : (C ^ (1 / p) * (∑ J : κ, (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ ((1:ℝ) / 2)) ^ p
      = C * (∑ J : κ, (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2) := by
    rw [Real.mul_rpow (Real.rpow_nonneg (le_of_lt hC0) _)
      (Real.rpow_nonneg (Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (wnnB J) _)) _)]
    rw [← Real.rpow_mul (le_of_lt hC0), ← Real.rpow_mul (Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (wnnB J) _))]
    rw [div_mul_cancel₀ 1 (ne_of_gt hp0), show ((1:ℝ) / 2) * p = p / 2 by ring, Real.rpow_one]
  have hmain : (∑ i : Fin m, (∑ J : κ, (wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2))
      ≤ C * (∑ J : κ, (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2) := by
    rw [← h3, ← h4]
    exact h2
  -- (8) the cover average
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [Fin.sum_univ_zero, mul_zero]
    exact mul_nonneg (le_of_lt hC0) hB0
  · have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    calc (1 / (m : ℝ)) * (∑ i : Fin m, (∑ J : κ, (wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2))
        = (∑ i : Fin m, (∑ J : κ, (wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2)) / (m : ℝ) := by
          rw [one_div, ← div_eq_inv_mul]
      _ ≤ ∑ i : Fin m, (∑ J : κ, (wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2) :=
          div_le_self hA0 hm1
      _ ≤ C * (∑ J : κ, (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2) := hmain


/-- **Ball inflation, `M_n` families** — the display at the end of BDG §6
(with `M := M_n`, the family `I_j` the `j`-th block of intervals, and the two
sides in the unnormalised weighted `Lᵖ` language of this development):

  `(1/m) Σ_i ∏_j (Σ_{J ∈ I_j} ‖E_J g‖²_{Lᵖ(w_{Δᵢ})})^{p/(2M)}
     ≤ C ∏_j (Σ_{J ∈ I_j} ‖E_J g‖²_{Lᵖ(w_B)})^{p/(2M)}`

with the *same* constant `C` as in `ball_inflation_kn`.  It is the
`M_n`-fold generalisation of the single-family inequality, obtained from it by
Hölder's inequality with the `M` equal exponents `M` (the commons lemma
`holder_prod`). -/
theorem ball_inflation_kn_multi (n : ℕ) (hn : 1 ≤ n) (c : E n) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ R) (m : ℕ) (c' : Fin m → E n)
    (hcen : ∀ i, ‖c' i - c‖ ≤ R) (hsep : ∀ i j, i ≠ j → r ≤ ‖c' i - c' j‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℝ) (hp : 2 ≤ p) (M : ℕ) (hM : 1 ≤ M) {κ : Type*} [Fintype κ]
      (ℓ : κ → Fin M) (a b : κ → ℝ) (g : ℝ → ℂ),
      (∀ J : κ, Integrable (fun x : E n => ‖extOp n g (a J) (b J) x‖ ^ p * ballWeight n c R x) volume) →
      (1 / (m : ℝ)) * (∑ i : Fin m, ∏ j : Fin M,
        (∑ J ∈ Finset.univ.filter (fun J => ℓ J = j), (wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / (2 * M)))
        ≤ C * ∏ j : Fin M,
        (∑ J ∈ Finset.univ.filter (fun J => ℓ J = j), (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / (2 * M)) := by
  obtain ⟨C, hC0, hsingle⟩ := ball_inflation_kn n hn c hR hr hrR m c' hcen hsep
  refine ⟨C, hC0, ?_⟩
  intro p hp M hM κ _ ℓ a b g hint
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  -- the fiber identity: sums over the subtype are the filtered sums
  have hfib : ∀ (c'' : E n) (R' : ℝ) (j : Fin M),
      (∑ J : {J : κ // ℓ J = j}, (wLpPow n c'' R' p (extOp n g (a J.1) (b J.1))) ^ (2 / p))
      = ∑ J ∈ Finset.univ.filter (fun J => ℓ J = j), (wLpPow n c'' R' p (extOp n g (a J) (b J))) ^ (2 / p) := by
    intro c'' R' j
    exact (Finset.sum_subtype (Finset.univ.filter (fun J : κ => ℓ J = j)) (fun x => by simp)
      (fun J => (wLpPow n c'' R' p (extOp n g (a J) (b J))) ^ (2 / p))).symm
  set X : Fin M → Fin m → ℝ := fun j i =>
    (∑ J ∈ Finset.univ.filter (fun J => ℓ J = j), (wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / (2 * M)) with hX
  have hAnn : ∀ (j : Fin M) (i : Fin m), 0 ≤ ∑ J ∈ Finset.univ.filter (fun J => ℓ J = j),
      (wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p) := by
    intro j i
    exact Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (wLpPow_nonneg n (c' i) hr p _) _)
  have hBnn : ∀ j : Fin M, 0 ≤ ∑ J ∈ Finset.univ.filter (fun J => ℓ J = j),
      (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p) := by
    intro j
    exact Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (wLpPow_nonneg n c hR p _) _)
  have hXnn : ∀ j i, 0 ≤ X j i := fun j i => Real.rpow_nonneg (hAnn j i) _
  have hXM : ∀ (j : Fin M) (i : Fin m), (X j i) ^ M
      = (∑ J ∈ Finset.univ.filter (fun J => ℓ J = j), (wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2) := by
    intro j i
    show ((∑ J ∈ Finset.univ.filter (fun J => ℓ J = j), (wLpPow n (c' i) r p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / (2 * M))) ^ M = _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hAnn j i)]
    congr 1
    field_simp
  -- Holder with M factors
  have hholder := Commons.Analysis.Inequalities.holder_prod hM (Finset.univ : Finset (Fin m)) X hXnn
  -- step B, on each fiber
  have hstepB : ∀ j : Fin M,
      (1 / (m : ℝ)) * (∑ i : Fin m, (X j i) ^ M)
        ≤ C * (∑ J ∈ Finset.univ.filter (fun J => ℓ J = j), (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2) := by
    intro j
    have h := hsingle p hp (κ := {J : κ // ℓ J = j}) (a := fun J => a J.1) (b := fun J => b J.1) g
      (fun J => hint J.1)
    simpa only [hXM, hfib] using h

  -- Holder over the cover with M factors
  have hAnn' : ∀ j : Fin M, 0 ≤ ∑ i : Fin m, (X j i) ^ M :=
    fun j => Finset.sum_nonneg (fun i _ => pow_nonneg (hXnn j i) M)
  have h1 : (1 / (m : ℝ)) * (∑ i : Fin m, ∏ j : Fin M, X j i)
      ≤ (1 / (m : ℝ)) * ∏ j : Fin M, (∑ i : Fin m, (X j i) ^ M) ^ (1 / ((M:ℕ):ℝ)) :=
    mul_le_mul_of_nonneg_left (by simpa using hholder) (by positivity)
  have h2 : (∏ j : Fin M, ((1 / (m : ℝ)) * (∑ i : Fin m, (X j i) ^ M)) ^ (1 / ((M:ℕ):ℝ)))
      = (1 / (m : ℝ)) * ∏ j : Fin M, (∑ i : Fin m, (X j i) ^ M) ^ (1 / ((M:ℕ):ℝ)) := by
    rw [Finset.prod_congr rfl (fun j _ => Real.mul_rpow (by positivity) (hAnn' j))]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 1 / (m : ℝ)),
      div_mul_cancel₀ 1 (ne_of_gt hM0), Real.rpow_one]
  have h3 : (∏ j : Fin M, ((1 / (m : ℝ)) * (∑ i : Fin m, (X j i) ^ M)) ^ (1 / ((M:ℕ):ℝ)))
      ≤ ∏ j : Fin M, (C * (∑ J ∈ Finset.univ.filter (fun J => ℓ J = j),
          (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2)) ^ (1 / ((M:ℕ):ℝ)) :=
    Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg (mul_nonneg (by positivity) (hAnn' j)) _)
      (fun j _ => Real.rpow_le_rpow (mul_nonneg (by positivity) (hAnn' j)) (hstepB j) (by positivity))
  have h4 : (∏ j : Fin M, (C * (∑ J ∈ Finset.univ.filter (fun J => ℓ J = j),
          (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2)) ^ (1 / ((M:ℕ):ℝ)))
      = C * ∏ j : Fin M, (∑ J ∈ Finset.univ.filter (fun J => ℓ J = j),
          (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / (2 * M)) := by
    rw [Finset.prod_congr rfl (fun j _ => Real.mul_rpow (le_of_lt hC0) (Real.rpow_nonneg (hBnn j) _))]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hC0), div_mul_cancel₀ 1 (ne_of_gt hM0),
        Real.rpow_one]
    · refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [← Real.rpow_mul (hBnn j)]
      congr 1
      ring
  simpa only [hX] using calc
    (1 / (m : ℝ)) * (∑ i : Fin m, ∏ j : Fin M, X j i)
        ≤ (1 / (m : ℝ)) * ∏ j : Fin M, (∑ i : Fin m, (X j i) ^ M) ^ (1 / ((M:ℕ):ℝ)) := h1
    _ = ∏ j : Fin M, ((1 / (m : ℝ)) * (∑ i : Fin m, (X j i) ^ M)) ^ (1 / ((M:ℕ):ℝ)) := h2.symm
    _ ≤ ∏ j : Fin M, (C * (∑ J ∈ Finset.univ.filter (fun J => ℓ J = j),
          (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / 2)) ^ (1 / ((M:ℕ):ℝ)) := h3
    _ = C * ∏ j : Fin M, (∑ J ∈ Finset.univ.filter (fun J => ℓ J = j),
          (wLpPow n c R p (extOp n g (a J) (b J))) ^ (2 / p)) ^ (p / (2 * M)) := h4


end Submission.Vinogradov
