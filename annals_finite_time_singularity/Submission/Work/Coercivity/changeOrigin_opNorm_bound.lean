import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Operator-norm bound for `FormalMultilinearSeries.changeOrigin`

If `p : FormalMultilinearSeries ℝ E ℝ` satisfies `‖p n‖ ≤ M / s ^ n` and `a : E` has
`‖a‖ ≤ ρ` with `4 ρ < s`, then the `k`-th coefficient of the series re-expanded at `a`
satisfies

  `‖p.changeOrigin a k‖ ≤ 2 ^ (k+1) * M / s ^ k`,

provided `‖a‖` lies in the radius of convergence of `p`.

The proof bounds `‖p.changeOrigin a k‖` by the sum
`∑' l, #{σ : Finset (Fin (k+l)) // σ.card = l} * (‖p (k+l)‖ * ‖a‖ ^ l)`
(via `FormalMultilinearSeries.nnnorm_changeOrigin_le`), and then estimates the cardinality
crudely by `2 ^ (k+l)` to reduce the whole thing to a geometric series in `2ρ/s ≤ 1/2`.
-/

open scoped BigOperators

namespace Work.Coercivity

/-- `∑' l, (2 * x) ^ l ≤ 2` whenever `0 ≤ x ≤ 1/4`. -/
lemma tsum_two_mul_pow_le_quarter {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) :
    ∑' l : ℕ, (2 * x) ^ l ≤ 2 := by
  have hnorm : ‖(2 * x : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  rw [tsum_geometric_of_norm_lt_one hnorm]
  have h : (1 / 2 : ℝ) ≤ 1 - 2 * x := by linarith
  calc (1 - 2 * x)⁻¹ = 1 / (1 - 2 * x) := (one_div _).symm
    _ ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) h
    _ = 2 := by norm_num

/-- `∑' l, 2 ^ (k+l) * x ^ l ≤ 2 ^ (k+1)` whenever `0 ≤ x ≤ 1/4`. -/
lemma tsum_two_pow_mul_le_quarter (k : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) :
    ∑' l : ℕ, (2 : ℝ) ^ (k + l) * x ^ l ≤ 2 ^ (k + 1) := by
  have hnorm : ‖(2 * x : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hsummable : Summable (fun l : ℕ => (2 * x) ^ l) :=
    summable_geometric_of_norm_lt_one hnorm
  have h1 : (2 : ℝ) ^ k * ∑' l : ℕ, (2 * x) ^ l
      = ∑' l : ℕ, (2 : ℝ) ^ (k + l) * x ^ l := by
    rw [← Summable.tsum_mul_left (a := (2 : ℝ) ^ k) hsummable]
    apply tsum_congr
    intro l
    rw [mul_pow, pow_add]
    ring
  rw [← h1]
  calc (2 : ℝ) ^ k * ∑' l : ℕ, (2 * x) ^ l ≤ (2 : ℝ) ^ k * 2 :=
        mul_le_mul_of_nonneg_left (tsum_two_mul_pow_le_quarter hx0 hx) (by positivity)
    _ = 2 ^ (k + 1) := by ring

/-- Bound for the `changeOrigin` series as an `NNReal`-valued `tsum` over the index type
`Σ l, {σ : Finset (Fin (k+l)) // σ.card = l}` produced by
`FormalMultilinearSeries.nnnorm_changeOrigin_le`. -/
lemma changeOrigin_tsum_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : FormalMultilinearSeries ℝ E ℝ) {a : E} {M s ρ : ℝ} (k : ℕ)
    (hM : 0 < M) (hs : 0 < s) (hρ : 0 ≤ ρ) (h4 : 4 * ρ < s)
    (hp : ∀ n, ‖p n‖ ≤ M / s ^ n) (ha : ‖a‖ ≤ ρ)
    (ha_rad : (‖a‖₊ : ENNReal) < p.radius) :
    ((∑' t : Σ l : ℕ, {σ : Finset (Fin (k + l)) // σ.card = l},
        ‖p (k + t.fst)‖₊ * ‖a‖₊ ^ t.fst : NNReal) : ℝ) ≤ (2 : ℝ) ^ (k + 1) * M / s ^ k := by
  have hsumNN : Summable (fun t : Σ l : ℕ, {σ : Finset (Fin (k + l)) // σ.card = l} =>
      ‖p (k + t.fst)‖₊ * ‖a‖₊ ^ t.fst) := p.changeOriginSeries_summable_aux₂ ha_rad k
  have hsumR : Summable (fun t : Σ l : ℕ, {σ : Finset (Fin (k + l)) // σ.card = l} =>
      ((‖p (k + t.fst)‖₊ * ‖a‖₊ ^ t.fst : NNReal) : ℝ)) := NNReal.summable_coe.mpr hsumNN
  have hρs : ρ / s ≤ 1 / 4 := by rw [div_le_iff₀ hs]; linarith
  have hx0 : 0 ≤ (2 * ρ) / s := div_nonneg (by linarith) (le_of_lt hs)
  have hxle : (2 * ρ) / s ≤ 1 / 2 := by rw [div_le_iff₀ hs]; linarith
  have hfun_pt : ∀ l : ℕ,
      (2 : ℝ) ^ (k + l) * (M / s ^ (k + l) * ρ ^ l)
        = ((2 : ℝ) ^ k * M / s ^ k) * ((2 * ρ) / s) ^ l := by
    intro l
    have hsne : s ≠ 0 := ne_of_gt hs
    have hs1 : s ^ (k + l) ≠ 0 := pow_ne_zero _ hsne
    have hs2 : s ^ k ≠ 0 := pow_ne_zero _ hsne
    have hs3 : s ^ l ≠ 0 := pow_ne_zero _ hsne
    rw [div_pow, mul_pow, pow_add (2 : ℝ) k l, pow_add s k l]
    field_simp
  have hnorm2 : ‖((2 * ρ) / s : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    linarith
  have hgeo : ∑' l : ℕ, ((2 * ρ) / s) ^ l = (1 - (2 * ρ) / s)⁻¹ :=
    tsum_geometric_of_norm_lt_one hnorm2
  have hfin : (1 - (2 * ρ) / s)⁻¹ ≤ (2 : ℝ) := by
    have h : (1 / 2 : ℝ) ≤ 1 - 2 * ρ / s := by linarith
    calc (1 - 2 * ρ / s)⁻¹ = 1 / (1 - 2 * ρ / s) := (one_div _).symm
      _ ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) h
      _ = 2 := by norm_num
  have hg : Summable (fun l : ℕ => (2 : ℝ) ^ (k + l) * (M / s ^ (k + l) * ρ ^ l)) := by
    rw [show (fun l : ℕ => (2 : ℝ) ^ (k + l) * (M / s ^ (k + l) * ρ ^ l))
          = fun l : ℕ => ((2 : ℝ) ^ k * M / s ^ k) * ((2 * ρ) / s) ^ l from
        funext hfun_pt]
    exact (summable_geometric_of_norm_lt_one hnorm2).mul_left _
  have hbound_each : ∀ l : ℕ, (Fintype.card {σ : Finset (Fin (k + l)) // σ.card = l} : ℝ)
        * ((‖p (k + l)‖₊ : ℝ) * (‖a‖₊ : ℝ) ^ l)
      ≤ (2 : ℝ) ^ (k + l) * (M / s ^ (k + l) * ρ ^ l) := by
    intro l
    have hcard : (Fintype.card {σ : Finset (Fin (k + l)) // σ.card = l} : ℝ)
        ≤ (2 : ℝ) ^ (k + l) := by
      have := Fintype.card_finset_len (α := Fin (k + l)) l
      rw [this, Fintype.card_fin]
      exact_mod_cast Nat.choose_le_two_pow (k + l) l
    have hp' : (‖p (k + l)‖₊ : ℝ) ≤ M / s ^ (k + l) := by
      rw [coe_nnnorm]; exact hp (k + l)
    have ha' : (‖a‖₊ : ℝ) ^ l ≤ ρ ^ l := by
      apply pow_le_pow_left₀ (by positivity)
      rw [coe_nnnorm]; exact ha
    have hMs' : (0 : ℝ) ≤ M / s ^ (k + l) :=
      div_nonneg (le_of_lt hM) (pow_nonneg (le_of_lt hs) _)
    have hρl : (0 : ℝ) ≤ ρ ^ l := pow_nonneg hρ l
    calc (Fintype.card {σ : Finset (Fin (k + l)) // σ.card = l} : ℝ)
          * ((‖p (k + l)‖₊ : ℝ) * (‖a‖₊ : ℝ) ^ l)
        ≤ (2 : ℝ) ^ (k + l) * ((M / s ^ (k + l)) * ρ ^ l) :=
          mul_le_mul hcard (mul_le_mul hp' ha' (by positivity) hMs') (by positivity)
            (by positivity)
      _ = (2 : ℝ) ^ (k + l) * (M / s ^ (k + l) * ρ ^ l) := by ring
  have hgard : (fun l : ℕ => (Fintype.card {σ : Finset (Fin (k + l)) // σ.card = l} : ℝ)
        * ((‖p (k + l)‖₊ : ℝ) * (‖a‖₊ : ℝ) ^ l))
      = fun l : ℕ => ∑' σ : {σ : Finset (Fin (k + l)) // σ.card = l},
              ((‖p (k + l)‖₊ * ‖a‖₊ ^ l : NNReal) : ℝ) := by
    funext l
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NNReal.coe_mul,
      NNReal.coe_pow]
  have hf : Summable (fun l : ℕ => (Fintype.card {σ : Finset (Fin (k + l)) // σ.card = l} : ℝ)
        * ((‖p (k + l)‖₊ : ℝ) * (‖a‖₊ : ℝ) ^ l)) := by
    rw [hgard]; exact hsumR.sigma
  have hstep1 : ((∑' t : Σ l : ℕ, {σ : Finset (Fin (k + l)) // σ.card = l},
        ‖p (k + t.fst)‖₊ * ‖a‖₊ ^ t.fst : NNReal) : ℝ)
      = ∑' l : ℕ, (Fintype.card {σ : Finset (Fin (k + l)) // σ.card = l} : ℝ)
          * ((‖p (k + l)‖₊ : ℝ) * (‖a‖₊ : ℝ) ^ l) := by
    rw [NNReal.coe_tsum, hsumR.tsum_sigma, hgard]
  rw [hstep1]
  calc ∑' l : ℕ, (Fintype.card {σ : Finset (Fin (k + l)) // σ.card = l} : ℝ)
          * ((‖p (k + l)‖₊ : ℝ) * (‖a‖₊ : ℝ) ^ l)
      ≤ ∑' l : ℕ, (2 : ℝ) ^ (k + l) * (M / s ^ (k + l) * ρ ^ l) :=
        Summable.tsum_le_tsum hbound_each hf hg
    _ = ∑' l : ℕ, ((2 : ℝ) ^ k * M / s ^ k) * ((2 * ρ) / s) ^ l := by
        apply tsum_congr; intro l; exact hfun_pt l
    _ = ((2 : ℝ) ^ k * M / s ^ k) * ∑' l : ℕ, ((2 * ρ) / s) ^ l :=
        Summable.tsum_mul_left _ (summable_geometric_of_norm_lt_one hnorm2)
    _ = ((2 : ℝ) ^ k * M / s ^ k) * (1 - (2 * ρ) / s)⁻¹ := by rw [hgeo]
    _ ≤ ((2 : ℝ) ^ k * M / s ^ k) * 2 := mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = (2 : ℝ) ^ (k + 1) * M / s ^ k := by rw [pow_succ]; ring

theorem changeOrigin_opNorm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : FormalMultilinearSeries ℝ E ℝ) {a : E} {M s ρ : ℝ} (k : ℕ)
    (hM : 0 < M) (hs : 0 < s) (hρ : 0 ≤ ρ) (h4 : 4 * ρ < s)
    (hp : ∀ n, ‖p n‖ ≤ M / s ^ n) (ha : ‖a‖ ≤ ρ)
    (ha_rad : (‖a‖₊ : ENNReal) < p.radius) :
    ‖p.changeOrigin a k‖ ≤ (2:ℝ) ^ (k+1) * M / s ^ k := by
  have hle := p.nnnorm_changeOrigin_le k ha_rad
  have hcoe : ‖p.changeOrigin a k‖ = ((‖p.changeOrigin a k‖₊ : NNReal) : ℝ) :=
    (coe_nnnorm _).symm
  rw [hcoe]
  exact le_trans (by exact_mod_cast hle)
    (changeOrigin_tsum_bound p k hM hs hρ h4 hp ha ha_rad)

end Work.Coercivity
