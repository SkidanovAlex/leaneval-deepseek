import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.est_gamma

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW analytic_core split, fix round 21:05) -- node `est_gamma_log`.
Definitions in `Submission.Work.BW.DefsAC`; the elementary facts about the modified height and the
sibling `est_gamma` come from `Submission.Work.BW.est_gamma`.

===== FIXES_2105.md (excerpt) =====
* **`est_gamma_log`.** Both bounds for all `i : Fin n`. The proof is identical to `est_gamma`'s;
  for `i = k` the row is `0`.
  * Consumers: `est21_l` (H325's child), and through it `est21` and `est22`.

BW's `a(t')` (§17) runs over **all** `n` operators `b_k ∂/∂z_i`, since `ellM_eq_sum_derVec` sums
over `i : Fin n`.  It therefore needs `|γ_i(λ) log α_i| ≤ e^{h+1}D` for every `i : Fin n`.  The
proved `est_gamma` gives this only for `i = ι m`.
-/

namespace Work.BW

/-- BW §13/§17 in the general form needed by §17: for any index `i0` of the coefficient vector
(distinct from the distinguished index `k`), any `X` with `‖X‖ ≤ d·h'(α_{i0})` satisfies
`‖γ_{i0} · X‖ ≤ e^{hL} 2^v D ≤ e^{h+1} D`.  Same proof as `est_gamma_aux`, the two columns `i0`
and `k` being distinct. -/
private lemma est_gamma_aux_gen {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (i0 : Fin n) (hi0 : i0 ≠ k) (lm : Fin r → ℕ)
    (hlm : ∀ j, lm j ≤ pDj r (dK K) σ j) (X : ℂ)
    (hX : ‖X‖ ≤ (dK K : ℝ) * BakerWustholz.modifiedHeight φ (α i0)) :
    ‖gam b k L i0 lm * X‖ ≤ Real.exp ((acH K b v : ℝ) + 1) * pD r (dK K) σ := by
  obtain ⟨hst, hr, hBH, hι, hp0, hp9, hp12, h10⟩ := H
  obtain ⟨hLI, hbspan, hα'ne, hKum, hσpos, hα'hmod, hrow, hkapp⟩ := hBH
  obtain ⟨hιne, hιind⟩ := hι
  obtain ⟨hn2, hαne, hlogind, hgcd, hbk, hmhle, hXbw, hexp1c, hlogc⟩ := hst
  have hd : 0 < (dK K : ℝ) := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    exact_mod_cast this
  have hd1 : 1 ≤ dK K := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Nat.cast_pos.mp hd))
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr)
  have hmh_ge : ∀ t : Fin n, (1 : ℝ) / (dK K : ℝ) ≤ BakerWustholz.modifiedHeight φ (α t) :=
    fun t => modifiedHeight_ge_inv_dK φ (α t)
  have hmh_nonneg : ∀ t : Fin n, 0 ≤ BakerWustholz.modifiedHeight φ (α t) := by
    intro t
    exact le_trans (div_nonneg one_pos.le hd.le) (hmh_ge t)
  have hb : ∀ i : Fin n, |((b i : ℤ) : ℝ)| ≤ Real.exp (hL b (dK K)) := by
    intro i
    have habs : |((b i : ℤ) : ℝ)| = ((b i).natAbs : ℝ) := by
      rw [← Int.cast_abs]; congr 1; exact (Int.natCast_natAbs (b i)).symm
    rw [habs]
    have hM : ((b i).natAbs : ℝ) ≤ ((Finset.univ.sup fun i => (b i).natAbs : ℕ) : ℝ) := by
      exact_mod_cast Finset.le_sup (f := fun i => (b i).natAbs) (Finset.mem_univ i)
    have hMe : ((Finset.univ.sup fun i => (b i).natAbs : ℕ) : ℝ) ≤ Real.exp (hL b (dK K)) := by
      by_cases h : (Finset.univ.sup fun i => (b i).natAbs) = 0
      · simp only [h, Nat.cast_zero]; exact (Real.exp_pos _).le
      · have h1 : 1 ≤ (Finset.univ.sup fun i => (b i).natAbs : ℕ) :=
          Nat.one_le_iff_ne_zero.mpr h
        have hpos : 0 < ((Finset.univ.sup fun i => (b i).natAbs : ℕ) : ℝ) := by
          exact_mod_cast h1
        calc ((Finset.univ.sup fun i => (b i).natAbs : ℕ) : ℝ)
            = Real.exp (Real.log ((Finset.univ.sup fun i => (b i).natAbs : ℕ) : ℝ)) :=
              (Real.exp_log hpos).symm
          _ ≤ Real.exp (hL b (dK K)) := Real.exp_le_exp.mpr (le_max_left _ _)
    linarith
  have hrow' : ∀ i : Fin r,
      ∑ t : Fin n, |((L i t : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α t) ≤
        (2 : ℝ) ^ v * σ i := hrow
  -- §11 applied to the two distinct columns `i0` and `k` of the row `i`
  have htwo : ∀ i : Fin r,
      |((L i i0 : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α i0)
        + |((L i k : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α k) ≤ (2 : ℝ) ^ v * σ i := by
    intro i
    have hpair : |((L i i0 : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α i0)
        + |((L i k : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α k)
        ≤ ∑ t : Fin n, |((L i t : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α t) := by
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg (s := ({i0, k} : Finset (Fin n)))
        (f := fun t => |((L i t : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α t))
        (Finset.subset_univ _) (fun x _ _ => mul_nonneg (abs_nonneg _) (hmh_nonneg x))
      rwa [Finset.sum_insert (by simp [hi0]), Finset.sum_singleton] at hsub
    exact le_trans hpair (hrow' i)
  -- `D ≥ 0`
  have hDnn : 0 ≤ pD r (dK K) σ := by
    simp only [pD]
    have hlog : 0 ≤ Real.log (2 * ↑r * ↑(dK K)) := by
      apply Real.log_nonneg
      have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
      have h2 : (1 : ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd1
      nlinarith
    have hp : 0 ≤ ∏ j : Fin r, σ j := Finset.prod_nonneg (fun j _ => (hσpos j).le)
    have h1 : (0 : ℝ) ≤ 2 * (r : ℝ) ^ r := by positivity
    have h2 : (0 : ℝ) ≤ (32 * (dK K : ℝ)) ^ (r + 1) := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hlog) hp
  -- `λ_i ≤ D_i` summed with the weights `d σ_i` gives at most `D`
  have hsum : (dK K : ℝ) * ∑ i : Fin r, σ i * (lm i : ℝ) ≤ pD r (dK K) σ := by
    have hpoint : ∀ i : Fin r, (dK K : ℝ) * σ i * (lm i : ℝ) ≤ pD r (dK K) σ / r := by
      intro i
      have hσi : 0 < σ i := hσpos i
      have hdσ : 0 < (dK K : ℝ) * σ i := mul_pos hd hσi
      have hfloor : (pDj r (dK K) σ i : ℝ) ≤ pD r (dK K) σ / ((r : ℝ) * dK K * σ i) := by
        rw [pDj]
        exact Nat.floor_le (by positivity)
      have hlm' : (lm i : ℝ) ≤ (pDj r (dK K) σ i : ℝ) := by exact_mod_cast hlm i
      calc (dK K : ℝ) * σ i * (lm i : ℝ)
          ≤ (dK K : ℝ) * σ i * (pDj r (dK K) σ i : ℝ) :=
            mul_le_mul_of_nonneg_left hlm' (le_of_lt hdσ)
        _ ≤ (dK K : ℝ) * σ i * (pD r (dK K) σ / ((r : ℝ) * dK K * σ i)) :=
            mul_le_mul_of_nonneg_left hfloor (le_of_lt hdσ)
        _ = pD r (dK K) σ / r := by
            field_simp
    calc (dK K : ℝ) * ∑ i : Fin r, σ i * (lm i : ℝ)
        = ∑ i : Fin r, (dK K : ℝ) * σ i * (lm i : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ ∑ _i : Fin r, pD r (dK K) σ / r := Finset.sum_le_sum (fun i _ => hpoint i)
      _ = pD r (dK K) σ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  -- `e^{h'(L)} 2^v ≤ e^{h+1}`
  have hexp : Real.exp (hL b (dK K)) * (2 : ℝ) ^ v ≤ Real.exp ((acH K b v : ℝ) + 1) := by
    have h2 : (2 : ℝ) ^ v = Real.exp ((v : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [h2, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hx0 : 0 ≤ hL b (dK K) + (v : ℝ) * Real.log 2 := by
      have h1 : 0 < hL b (dK K) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
      have h2 : 0 ≤ (v : ℝ) * Real.log 2 := by positivity
      linarith
    have hfl := (Nat.floor_lt (a := hL b (dK K) + (v : ℝ) * Real.log 2) hx0
        (n := acH K b v + 1)).mp (Nat.lt_succ_self _)
    simp only [Nat.cast_add, Nat.cast_one] at hfl
    exact le_of_lt hfl
  -- per-summand bound
  have hterm : ∀ i : Fin r,
      |((derVec b k L i0 i : ℤ) : ℝ)| * (lm i : ℝ) * ‖X‖
        ≤ Real.exp (hL b (dK K)) * (dK K : ℝ) * (2 : ℝ) ^ v * σ i * (lm i : ℝ) := by
    intro i
    have hscale : (|((L i i0 : ℤ) : ℝ)| + |((L i k : ℤ) : ℝ)|) * ‖X‖
        ≤ (dK K : ℝ) * ((2 : ℝ) ^ v * σ i) := by
      have hmhjk : BakerWustholz.modifiedHeight φ (α i0)
          ≤ BakerWustholz.modifiedHeight φ (α k) := hmhle i0
      have step : (|((L i i0 : ℤ) : ℝ)| + |((L i k : ℤ) : ℝ)|) * ‖X‖
          ≤ (|((L i i0 : ℤ) : ℝ)| + |((L i k : ℤ) : ℝ)|)
              * ((dK K : ℝ) * BakerWustholz.modifiedHeight φ (α i0)) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
      have step2 : (|((L i i0 : ℤ) : ℝ)| + |((L i k : ℤ) : ℝ)|)
            * ((dK K : ℝ) * BakerWustholz.modifiedHeight φ (α i0))
          ≤ (dK K : ℝ) * ((2 : ℝ) ^ v * σ i) := by
        have hk : |((L i k : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α i0)
            ≤ |((L i k : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α k) :=
          mul_le_mul_of_nonneg_left hmhjk (abs_nonneg _)
        calc (|((L i i0 : ℤ) : ℝ)| + |((L i k : ℤ) : ℝ)|)
              * ((dK K : ℝ) * BakerWustholz.modifiedHeight φ (α i0))
            = (dK K : ℝ) * (|((L i i0 : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α i0)
                + |((L i k : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α i0)) := by ring
          _ ≤ (dK K : ℝ) * (|((L i i0 : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α i0)
                + |((L i k : ℤ) : ℝ)| * BakerWustholz.modifiedHeight φ (α k)) := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hd); linarith
          _ ≤ (dK K : ℝ) * ((2 : ℝ) ^ v * σ i) :=
              mul_le_mul_of_nonneg_left (htwo i) (le_of_lt hd)
      exact step.trans step2
    have h1 : |((derVec b k L i0 i : ℤ) : ℝ)|
        ≤ Real.exp (hL b (dK K)) * (|((L i i0 : ℤ) : ℝ)| + |((L i k : ℤ) : ℝ)|) := by
      have hcast : ((derVec b k L i0 i : ℤ) : ℝ)
          = (b k : ℝ) * (L i i0 : ℝ) - (b i0 : ℝ) * (L i k : ℝ) := by
        simp only [derVec, Int.cast_sub, Int.cast_mul]
      rw [hcast]
      calc |(b k : ℝ) * (L i i0 : ℝ) - (b i0 : ℝ) * (L i k : ℝ)|
          ≤ |(b k : ℝ) * (L i i0 : ℝ)| + |(b i0 : ℝ) * (L i k : ℝ)| := abs_sub _ _
        _ = |(b k : ℝ)| * |(L i i0 : ℝ)| + |(b i0 : ℝ)| * |(L i k : ℝ)| := by
            rw [abs_mul, abs_mul]
        _ ≤ Real.exp (hL b (dK K)) * |(L i i0 : ℝ)|
              + Real.exp (hL b (dK K)) * |(L i k : ℝ)| := by
            gcongr
            · exact hb k
            · exact hb i0
        _ = Real.exp (hL b (dK K)) * (|(L i i0 : ℝ)| + |(L i k : ℝ)|) := by ring
    calc |((derVec b k L i0 i : ℤ) : ℝ)| * (lm i : ℝ) * ‖X‖
        ≤ (Real.exp (hL b (dK K)) * (|((L i i0 : ℤ) : ℝ)| + |((L i k : ℤ) : ℝ)|))
            * (lm i : ℝ) * ‖X‖ := by gcongr
      _ = Real.exp (hL b (dK K)) * (lm i : ℝ)
            * ((|((L i i0 : ℤ) : ℝ)| + |((L i k : ℤ) : ℝ)|) * ‖X‖) := by ring
      _ ≤ Real.exp (hL b (dK K)) * (lm i : ℝ) * ((dK K : ℝ) * ((2 : ℝ) ^ v * σ i)) := by
          gcongr
      _ = Real.exp (hL b (dK K)) * (dK K : ℝ) * (2 : ℝ) ^ v * σ i * (lm i : ℝ) := by ring
  have hfinal : (∑ i : Fin r,
        Real.exp (hL b (dK K)) * (dK K : ℝ) * (2 : ℝ) ^ v * σ i * (lm i : ℝ))
      = Real.exp (hL b (dK K)) * (2 : ℝ) ^ v
          * ((dK K : ℝ) * ∑ i : Fin r, σ i * (lm i : ℝ)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [norm_mul]
  have hgnorm : ‖gam b k L i0 lm‖
      ≤ ∑ i : Fin r, |((derVec b k L i0 i : ℤ) : ℝ)| * (lm i : ℝ) := by
    rw [gam]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [norm_mul, Complex.norm_intCast, Complex.norm_natCast]
  calc ‖gam b k L i0 lm‖ * ‖X‖
      ≤ (∑ i : Fin r, |((derVec b k L i0 i : ℤ) : ℝ)| * (lm i : ℝ)) * ‖X‖ :=
        mul_le_mul_of_nonneg_right hgnorm (norm_nonneg _)
    _ = ∑ i : Fin r, |((derVec b k L i0 i : ℤ) : ℝ)| * (lm i : ℝ) * ‖X‖ := by
        rw [Finset.sum_mul]
    _ ≤ ∑ i : Fin r,
          Real.exp (hL b (dK K)) * (dK K : ℝ) * (2 : ℝ) ^ v * σ i * (lm i : ℝ) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = Real.exp (hL b (dK K)) * (2 : ℝ) ^ v
          * ((dK K : ℝ) * ∑ i : Fin r, σ i * (lm i : ℝ)) := hfinal
    _ ≤ Real.exp (hL b (dK K)) * (2 : ℝ) ^ v * pD r (dK K) σ :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ Real.exp ((acH K b v : ℝ) + 1) * pD r (dK K) σ :=
        mul_le_mul_of_nonneg_right hexp hDnn


/-- BW §17 (p. 48–49): for EVERY index `i : Fin n` (not only the chosen `ι m`), `|γ_i(λ)| ≤ e^{h+1}D` and `|γ_i(λ) log α_i| ≤ e^{h+1}D` for `λ_j ≤ D_j`, where `γ_i(λ) = Σ_j (b_k L_{ji} − b_i L_{jk}) λ_j`. Proof as `est_gamma`: `|b| ≤ e^{h'(L)}`, `|log α_i| ≤ d h'(α_i) ≤ d h'(α_k)` (`Standing`), the two terms `|L_{ji}| h'(α_i) + |L_{jk}| h'(α_k)` sit in one BH sum `≤ 2^v σ_j` (for `i = k` the row is `0`), `Σ_j dσ_jλ_j ≤ D`, `e^{h'(L)}2^v ≤ e^{h+1}`. Needed by `est21_l` for BW's `a(t')`, which runs over all `n` operators `b_k ∂/∂z_i` (`ellM_eq_sum_derVec` sums over `Fin n`). -/
theorem est_gamma_log {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (i : Fin n) (lm : Fin r → ℕ)
    (hlm : ∀ j, lm j ≤ pDj r (dK K) σ j) :
    ‖gam b k L i lm‖ ≤ Real.exp ((acH K b v : ℝ) + 1) * acD K σ ∧
      ‖gam b k L i lm * Complex.log (φ (α i))‖ ≤ Real.exp ((acH K b v : ℝ) + 1) * acD K σ := by
  by_cases hik : i = k
  · -- the degenerate index: the row of `derVec` is identically zero
    obtain ⟨hst, hr, hBH, hι, hp0, hp9, hp12, h10⟩ := H
    obtain ⟨hLI, hbspan, hα'ne, hKum, hσpos, hα'hmod, hrow, hkapp⟩ := hBH
    have hd : 0 < (dK K : ℝ) := by
      have : 0 < Module.finrank ℚ K := Module.finrank_pos
      exact_mod_cast this
    have hd1 : 1 ≤ dK K := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Nat.cast_pos.mp hd))
    have hr1 : 1 ≤ r := le_trans (by norm_num) hr
    have hDnn : 0 ≤ pD r (dK K) σ := by
      simp only [pD]
      have hlog : 0 ≤ Real.log (2 * ↑r * ↑(dK K)) := by
        apply Real.log_nonneg
        have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
        have h2 : (1 : ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd1
        nlinarith
      have hp : 0 ≤ ∏ j : Fin r, σ j := Finset.prod_nonneg (fun j _ => (hσpos j).le)
      have h1 : (0 : ℝ) ≤ 2 * (r : ℝ) ^ r := by positivity
      have h2 : (0 : ℝ) ≤ (32 * (dK K : ℝ)) ^ (r + 1) := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hlog) hp
    have hgam0 : gam b k L i lm = 0 := by
      rw [gam]
      refine Finset.sum_eq_zero (fun i' _ => ?_)
      rw [hik]
      simp [derVec]
    have hRnn : 0 ≤ Real.exp ((acH K b v : ℝ) + 1) * acD K σ :=
      mul_nonneg (Real.exp_pos _).le hDnn
    exact ⟨by rw [hgam0, norm_zero]; exact hRnn,
      by rw [hgam0, zero_mul, norm_zero]; exact hRnn⟩
  · constructor
    · have hX1 : ‖(1 : ℂ)‖ ≤ (dK K : ℝ) * BakerWustholz.modifiedHeight φ (α i) := by
        rw [norm_one]
        have hd : 0 < (dK K : ℝ) := by
          have : 0 < Module.finrank ℚ K := Module.finrank_pos
          exact_mod_cast this
        have h := mul_le_mul_of_nonneg_left (modifiedHeight_ge_inv_dK φ (α i)) (le_of_lt hd)
        rwa [mul_one_div, div_self (ne_of_gt hd)] at h
      simpa using est_gamma_aux_gen H i hik lm hlm (1 : ℂ) hX1
    · exact est_gamma_aux_gen H i hik lm hlm (Complex.log (φ (α i)))
        (norm_log_le_dK_mul_modifiedHeight φ (α i))

end Work.BW
