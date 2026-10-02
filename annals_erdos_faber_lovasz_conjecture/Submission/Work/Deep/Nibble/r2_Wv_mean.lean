import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.r2_setup
import Submission.Work.Deep.Nibble.r2_own_b
import Submission.Work.Deep.Nibble.r2_comb_count

/-!
# The mean of the residual degree `Wv` in the second round of the nibble

`Wv 𝓖 ω v` (defined in `r2_setup.lean`) is the residual degree of an uncovered vertex `v`
after one round of the wasteful nibble on the hypergraph `𝓖`, where each edge is kept
independently with probability `p = θ/D`.  This file computes its expectation up to a
relative error `ε'/2`, under the round's standing hypotheses.

The argument is: by linearity of expectation and the independence of the coordinates, for
each `e ∋ v` the probability that all blockers `Bset 𝓖 v e` are unkept is
`(1-p)^{|Bset 𝓖 v e|}`, and by `r2_comb_count` we have
`|Bset 𝓖 v e| = ∑_{w ∈ e∖{v}} (hd 𝓖 w - 1) = (r-1)(D-1)(1 + O(ε))`.
Hence `E[Wv] = ∑_{e ∋ v}(1-p)^{|Bset 𝓖 v e|}`, which is `(D ± εD)·(1-p)^{(r-1)(D-1)}(1 ± O(εθr))`,
while `Dlev r θ D = D(1-θ/D)^{(r-1)(D-1)}`; the hypothesis `ε' ≥ 100(ε + εrθ)` pays for both
errors.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Elementary helper lemmas -/

/-- The `Finset` version of an edge has the cardinality of the edge. -/
lemma r2_Wv_card_eFin (𝓖 : Set (Set V)) (e : 𝓖) : (eFin 𝓖 e).card = (e : Set V).ncard := by
  classical
  have hf : ((e : Set V)).Finite := Set.toFinite _
  have hset : hf.toFinset = eFin 𝓖 e := by ext w; simp
  rw [Set.ncard_eq_toFinset_card ((e : Set V)) hf, hset]

/-- An edge of an `r`-uniform hypergraph has `r` vertices. -/
lemma r2_Wv_eFin_card_eq (𝓖 : Set (Set V)) {r : ℕ} (huni : HUnif 𝓖 r) (e : 𝓖) :
    (eFin 𝓖 e).card = r := by
  rw [r2_Wv_card_eFin]; exact huni (e : Set V) e.2

/-- **The number of blockers of `e` at `v` is `(r-1)(D-1)(1+O(ε))`.**

For `v ∈ e`, the blockers `Bset 𝓖 v e` number `∑_{w ∈ e∖{v}} (hd 𝓖 w - 1)`, and each of the
`r-1` summands is within `ε·D` of `D - 1`. -/
lemma r2_Wv_bset_card_dev (𝓖 : Set (Set V)) {r : ℕ} (hr : 2 ≤ r) (hlin : HLin 𝓖) (huni : HUnif 𝓖 r)
    {v : V} {e : 𝓖} (hve : v ∈ (e : Set V)) {ε : ℝ} (hε : 0 ≤ ε) {D : ℕ}
    (hdeg : ∀ w : V, |((hd 𝓖 w : ℝ)) - (D:ℝ)| ≤ ε * (D:ℝ)) :
    |(((Bset 𝓖 v e).card : ℝ)) - ((((r - 1) * (D - 1) : ℕ) : ℝ))|
      ≤ ((r:ℝ) - 1) * ε * (D:ℝ) := by
  classical
  have hr1 : 1 ≤ r := by omega
  have hD1 : 1 ≤ D := by
    by_contra h
    have hD0 : D = 0 := by omega
    have hv1 : 1 ≤ hd 𝓖 v := by
      rw [hd_eq_card_thruF 𝓖 v]
      exact Finset.card_pos.mpr ⟨e, (mem_thruF (𝓖 := 𝓖)).mpr hve⟩
    have h1 : (1:ℝ) ≤ (hd 𝓖 v : ℝ) := by exact_mod_cast hv1
    have h2 := hdeg v
    rw [hD0] at h2
    simp at h2
    linarith
  have hcomb := (r2_comb_count 𝓖 hr1 hlin huni).2.1 v e hve
  have hS : ((eFin 𝓖 e).erase v).card = r - 1 := by
    rw [Finset.card_erase_of_mem ((eFin_mem_iff (𝓖 := 𝓖)).mpr hve), r2_Wv_eFin_card_eq 𝓖 huni e]
  have hge1 : ∀ w ∈ (eFin 𝓖 e).erase v, 1 ≤ hd 𝓖 w := by
    intro w hw
    rw [Finset.mem_erase] at hw
    rw [hd_eq_card_thruF 𝓖 w]
    exact Finset.card_pos.mpr ⟨e, (mem_thruF (𝓖 := 𝓖)).mpr ((eFin_mem_iff (𝓖 := 𝓖)).mp hw.2)⟩
  have hcast : ((Bset 𝓖 v e).card : ℝ)
      = ∑ w ∈ (eFin 𝓖 e).erase v, ((hd 𝓖 w : ℝ) - 1) := by
    rw [hcomb, Nat.cast_sum]
    exact Finset.sum_congr rfl fun w hw => by
      rw [Nat.cast_sub (hge1 w hw), Nat.cast_one]
  have hx0 : ((((r - 1) * (D - 1) : ℕ)) : ℝ)
      = ∑ w ∈ (eFin 𝓖 e).erase v, ((D : ℝ) - 1) := by
    rw [Finset.sum_const, hS, nsmul_eq_mul, Nat.cast_mul, Nat.cast_sub hr1, Nat.cast_sub hD1]
    ring
  calc |((Bset 𝓖 v e).card : ℝ) - ((((r - 1) * (D - 1) : ℕ)) : ℝ)|
      = |(∑ w ∈ (eFin 𝓖 e).erase v, ((hd 𝓖 w : ℝ) - 1))
          - (∑ w ∈ (eFin 𝓖 e).erase v, ((D : ℝ) - 1))| := by rw [hcast, hx0]
    _ = |∑ w ∈ (eFin 𝓖 e).erase v, (((hd 𝓖 w : ℝ) - 1) - ((D : ℝ) - 1))| := by
        rw [← Finset.sum_sub_distrib]
    _ = |∑ w ∈ (eFin 𝓖 e).erase v, ((hd 𝓖 w : ℝ) - (D : ℝ))| := by
        congr 1
        exact Finset.sum_congr rfl fun w _ => by ring
    _ ≤ ∑ w ∈ (eFin 𝓖 e).erase v, |((hd 𝓖 w : ℝ) - (D : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w ∈ (eFin 𝓖 e).erase v, ε * (D : ℝ) :=
        Finset.sum_le_sum fun w _ => hdeg w
    _ = (((eFin 𝓖 e).erase v).card : ℝ) * (ε * (D : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((r : ℝ) - 1) * ε * (D : ℝ) := by
        rw [hS, Nat.cast_sub hr1]
        ring

/-- Bernoulli's inequality for a natural exponent: `(1-p)^n ≥ 1 - np` for `0 ≤ p ≤ 1`. -/
lemma r2_Wv_one_sub_mul_le_pow {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    1 - (n:ℝ) * p ≤ (1 - p)^n := by
  have h := one_add_mul_le_pow (a := -p) (by linarith) n
  have e1 : (1 + (n:ℝ) * (-p)) = (1 - (n:ℝ) * p) := by ring
  have e2 : (1 + -p : ℝ) = (1 - p) := by ring
  rw [e1, e2] at h
  exact h

/-- **The multiplicative comparison of `(1-p)^b` with `(1-p)^x` when `|b - x| ≤ t`.**

For `q = 1-p ∈ [0,1]` and natural exponents, `q^x (1 - tp) ≤ q^b ≤ q^x/(1-tp)`.  This is the
form in which the degree irregularity of the nibble is absorbed. -/
lemma r2_Wv_pow_close {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {b x : ℕ} {t : ℝ}
    (hb : |(b:ℝ) - (x:ℝ)| ≤ t) (htp : t * p ≤ 1/2) :
    (1-p)^x * (1 - t*p) ≤ (1-p)^b ∧ (1-p)^b ≤ (1-p)^x / (1 - t*p) := by
  have ht0 : 0 ≤ t := le_trans (abs_nonneg _) hb
  have htp0 : 0 ≤ t * p := mul_nonneg ht0 hp0
  have hq0 : 0 ≤ 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  have h1tp : 0 < 1 - t*p := by linarith
  have h1tp1 : 1 - t*p ≤ 1 := by linarith
  obtain ⟨hbl, hbu⟩ := abs_le.mp hb
  rcases le_total x b with hle | hle
  · set m : ℕ := b - x with hm
    have hbm : b = x + m := by omega
    have hmc : (m:ℝ) = (b:ℝ) - (x:ℝ) := by rw [hbm]; push_cast; ring
    have hmt : (m:ℝ) ≤ t := by rw [hmc]; linarith
    have hmp : (m:ℝ) * p ≤ t * p := mul_le_mul_of_nonneg_right hmt hp0
    have hbern : 1 - (m:ℝ)*p ≤ (1-p)^m := r2_Wv_one_sub_mul_le_pow hp0 hp1 m
    have hqm : 1 - t*p ≤ (1-p)^m := by linarith
    have hqx : 0 ≤ (1-p)^x := pow_nonneg hq0 x
    have hqm1 : (1-p)^m ≤ 1 := pow_le_one₀ hq0 hq1
    constructor
    · calc (1-p)^x * (1 - t*p) ≤ (1-p)^x * (1-p)^m := mul_le_mul_of_nonneg_left hqm hqx
        _ = (1-p)^b := by rw [hbm, pow_add]
    · calc (1-p)^b = (1-p)^x * (1-p)^m := by rw [hbm, pow_add]
        _ ≤ (1-p)^x / (1 - t*p) := by
            rw [le_div_iff₀ h1tp]
            have h1' : (1-p)^m * (1 - t*p) ≤ 1 := by
              nlinarith [hqm1, h1tp1, pow_nonneg hq0 m]
            calc (1-p)^x * (1-p)^m * (1 - t*p) = (1-p)^x * ((1-p)^m * (1-t*p)) := by ring
              _ ≤ (1-p)^x * 1 := mul_le_mul_of_nonneg_left h1' hqx
              _ = (1-p)^x := by ring
  · set m : ℕ := x - b with hm
    have hxm : x = b + m := by omega
    have hmc : (m:ℝ) = (x:ℝ) - (b:ℝ) := by rw [hxm]; push_cast; ring
    have hmt : (m:ℝ) ≤ t := by rw [hmc]; linarith
    have hmp : (m:ℝ) * p ≤ t * p := mul_le_mul_of_nonneg_right hmt hp0
    have hbern : 1 - (m:ℝ)*p ≤ (1-p)^m := r2_Wv_one_sub_mul_le_pow hp0 hp1 m
    have hqm : 1 - t*p ≤ (1-p)^m := by linarith
    have hqx : 0 ≤ (1-p)^x := pow_nonneg hq0 x
    have hqb_le : (1-p)^x ≤ (1-p)^b := pow_le_pow_of_le_one hq0 hq1 hle
    constructor
    · calc (1-p)^x * (1 - t*p) ≤ (1-p)^x * 1 := mul_le_mul_of_nonneg_left h1tp1 hqx
        _ = (1-p)^x := by ring
        _ ≤ (1-p)^b := hqb_le
    · rw [le_div_iff₀ h1tp, hxm, pow_add]
      exact mul_le_mul_of_nonneg_left hqm (pow_nonneg hq0 b)

/-- **The expectation of the residual degree, before the numerical bounds.**

`Wv 𝓖 ω v` is the number of edges `e ∋ v` all of whose blockers are unkept, so by linearity
of expectation and independence `E[Wv] = ∑_{e ∋ v} (1-p)^{|Bset 𝓖 v e|}`. -/
lemma r2_Wv_exp_eq (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V) :
    (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => ((Wv 𝓖 ω v : ℕ) : ℝ))
      = ∑ e ∈ thruF 𝓖 v, (1 - p) ^ ((Bset 𝓖 v e).card) := by
  classical
  have hpt : ∀ ω : 𝓖 → Bool, ((Wv 𝓖 ω v : ℕ) : ℝ)
      = ∑ e ∈ thruF 𝓖 v, (if ∀ f ∈ Bset 𝓖 v e, ω f = false then (1:ℝ) else 0) := by
    intro ω
    rw [Wv, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : ∀ f ∈ Bset 𝓖 v e, ω f = false <;> simp [h]
  rw [show (fun ω : 𝓖 → Bool => ((Wv 𝓖 ω v : ℕ) : ℝ))
      = (fun ω => ∑ e ∈ thruF 𝓖 v, (if ∀ f ∈ Bset 𝓖 v e, ω f = false then (1:ℝ) else 0))
      from funext hpt]
  rw [FinProb.exp_sum_finset]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [FinProb.exp_indicator, edgeMeasure_prob_unkept]

/-! ## The main estimate -/

theorem r2_Wv_mean {V : Type*} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V)) {r : ℕ} (hr : 2 ≤ r)
    {θ δ ε' ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100) (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1 / 2)
    (hε'2 : 100 * (ε + ε * (r : ℝ) * θ) ≤ ε')
    {D : ℕ} (hD : 2 ≤ D) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1)
    (hθD : θ / (D : ℝ) ≤ 1 / 2)
    (hlin : Work.Deep.Nibble.HLin 𝓖) (huni : Work.Deep.Nibble.HUnif 𝓖 r)
    (hdeg : ∀ v : V, |((Work.Deep.Nibble.hd 𝓖 v : ℝ)) - (D : ℝ)| ≤ ε * (D : ℝ)) :
    ∀ v : V, |(Work.Deep.Nibble.edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp
        (fun ω => ((Work.Deep.Nibble.Wv 𝓖 ω v : ℕ) : ℝ))
        - Work.Deep.Nibble.Dlev r θ D| ≤ ε' * Work.Deep.Nibble.Dlev r θ D / 2 := by
  intro v
  classical
  have hD1 : 1 ≤ D := by omega
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD1
  have hD2 : (2:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
  have hrn : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg r
  have hε0 : 0 ≤ ε := by
    have h := hdeg v
    have h2 : 0 ≤ ε * (D:ℝ) := le_trans (abs_nonneg _) h
    have h2' : 0 ≤ (D:ℝ) * ε := by linarith
    exact nonneg_of_mul_nonneg_right h2' hDpos
  have hθnn : 0 ≤ θ := le_of_lt hθ0
  have hE1 : ε + ε * (r:ℝ) * θ ≤ ε'/100 := by linarith
  have hE2 : 0 ≤ ε * (r:ℝ) * θ := mul_nonneg (mul_nonneg hε0 hrn) hθnn
  have hε_le : ε ≤ ε'/100 := by linarith
  have hrθ_le : ε * (r:ℝ) * θ ≤ ε'/100 := by linarith
  set q : ℝ := 1 - θ/(D:ℝ) with hq
  have hq0 : 0 ≤ q := by rw [hq]; linarith
  have hq1 : q ≤ 1 := by rw [hq]; linarith
  set t : ℝ := ((r:ℝ) - 1) * ε * (D:ℝ) with ht
  set u : ℝ := t * (θ/(D:ℝ)) with hu
  have hu_eq : u = ((r:ℝ) - 1) * ε * θ := by
    rw [hu, ht]
    field_simp
  have hu_nn : 0 ≤ u := by
    rw [hu_eq]
    exact mul_nonneg (mul_nonneg (by linarith) hε0) hθnn
  have hu_le : u ≤ ε'/100 := by
    rw [hu_eq]
    have h3 : ((r:ℝ) - 1) * ε * θ ≤ (r:ℝ) * ε * θ := by
      have h4 : (0:ℝ) ≤ ε * θ := mul_nonneg hε0 hθnn
      nlinarith [hr1]
    have h5 : (r:ℝ) * ε * θ = ε * (r:ℝ) * θ := by ring
    linarith
  have hu_small : u ≤ 1/200 := by linarith
  have hu_half : u ≤ 1/2 := by linarith
  have h1u : (0:ℝ) < 1 - u := by linarith
  have h1u' : (0:ℝ) ≤ 1 - u := le_of_lt h1u
  have h1ε : (0:ℝ) ≤ 1 - ε := by linarith
  set E : ℝ := (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp
        (fun ω => ((Wv 𝓖 ω v : ℕ) : ℝ)) with hEdef
  have hE : E = ∑ e ∈ thruF 𝓖 v, q ^ ((Bset 𝓖 v e).card) := by
    rw [hEdef, r2_Wv_exp_eq 𝓖 hp0 hp1 v, ← hq]
  have hper : ∀ e ∈ thruF 𝓖 v, q ^ ((r-1)*(D-1)) * (1-u) ≤ q ^ ((Bset 𝓖 v e).card)
      ∧ q ^ ((Bset 𝓖 v e).card) ≤ q ^ ((r-1)*(D-1))/(1-u) := by
    intro e he
    have hve : v ∈ (e : Set V) := (mem_thruF (𝓖 := 𝓖)).mp he
    have hb := r2_Wv_bset_card_dev 𝓖 hr hlin huni hve hε0 hdeg
    have hb' : |((Bset 𝓖 v e).card : ℝ) - (((r-1)*(D-1) : ℕ) : ℝ)| ≤ t := by
      rw [ht]; exact hb
    have h2 := r2_Wv_pow_close hp0 hp1 hb' hu_half
    rwa [← hq, ← hu] at h2
  have hlow : ((thruF 𝓖 v).card : ℝ) * (q^((r-1)*(D-1)) * (1-u)) ≤ E := by
    rw [hE]
    calc ((thruF 𝓖 v).card : ℝ) * (q^((r-1)*(D-1)) * (1-u))
        = ∑ _e ∈ thruF 𝓖 v, (q^((r-1)*(D-1)) * (1-u)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ e ∈ thruF 𝓖 v, q ^ ((Bset 𝓖 v e).card) :=
          Finset.sum_le_sum fun e he => (hper e he).1
  have hup : E ≤ ((thruF 𝓖 v).card : ℝ) * (q^((r-1)*(D-1))/(1-u)) := by
    rw [hE]
    calc ∑ e ∈ thruF 𝓖 v, q ^ ((Bset 𝓖 v e).card)
        ≤ ∑ _e ∈ thruF 𝓖 v, (q^((r-1)*(D-1))/(1-u)) :=
          Finset.sum_le_sum fun e he => (hper e he).2
      _ = ((thruF 𝓖 v).card : ℝ) * (q^((r-1)*(D-1))/(1-u)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((thruF 𝓖 v).card : ℝ) = (hd 𝓖 v : ℝ) := by
    rw [hd_eq_card_thruF 𝓖 v]
  have hdlo : (D:ℝ) - ε*(D:ℝ) ≤ (hd 𝓖 v : ℝ) := by
    have h := hdeg v; rw [abs_le] at h; linarith [h.1]
  have hdhi : (hd 𝓖 v : ℝ) ≤ (D:ℝ) + ε*(D:ℝ) := by
    have h := hdeg v; rw [abs_le] at h; linarith [h.2]
  have hqn : 0 ≤ q^((r-1)*(D-1)) := pow_nonneg hq0 _
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Dlev r θ D := ⟨Dlev r θ D, rfl⟩
  have hLval : L = (D:ℝ) * q ^ ((r-1)*(D-1)) := by rw [hL, Dlev, ← hq]
  have hLnn : 0 ≤ L := by rw [hLval]; positivity
  have hA : (1-ε)*(1-u)*L ≤ E := by
    calc (1-ε)*(1-u)*L
        = ((D:ℝ) - ε*(D:ℝ)) * (q^((r-1)*(D-1)) * (1-u)) := by rw [hLval]; ring
      _ ≤ (hd 𝓖 v : ℝ) * (q^((r-1)*(D-1)) * (1-u)) :=
          mul_le_mul_of_nonneg_right hdlo (mul_nonneg hqn h1u')
      _ = ((thruF 𝓖 v).card : ℝ) * (q^((r-1)*(D-1)) * (1-u)) := by rw [hcard]
      _ ≤ E := hlow
  have hB : E ≤ (1+ε)*L/(1-u) := by
    have hdiv : 0 ≤ q^((r-1)*(D-1))/(1-u) := div_nonneg hqn h1u'
    calc E ≤ ((thruF 𝓖 v).card : ℝ) * (q^((r-1)*(D-1))/(1-u)) := hup
      _ = (hd 𝓖 v : ℝ) * (q^((r-1)*(D-1))/(1-u)) := by rw [hcard]
      _ ≤ ((D:ℝ) + ε*(D:ℝ)) * (q^((r-1)*(D-1))/(1-u)) :=
          mul_le_mul_of_nonneg_right hdhi hdiv
      _ = (1+ε)*L/(1-u) := by rw [hLval, ← mul_div_assoc]; ring
  have hsum_le : ε + u ≤ ε'/50 := by linarith
  have h2' : ε + u ≤ ε'/2 := by linarith
  have h3 : ε + u ≤ (ε'/2) * (1-u) := by
    have hh : (ε + u)/(1-u) ≤ ε'/2 := by
      rw [div_le_iff₀ h1u]
      nlinarith [hsum_le, hu_small, hε'0]
    rwa [div_le_iff₀ h1u] at hh
  have hB' : E * (1-u) ≤ (1+ε) * L := by
    have h := hB
    rw [le_div_iff₀ h1u] at h
    linarith [h]
  have hlow' : -(ε' * L / 2) ≤ E - L := by
    have step1 : (1-ε)*(1-u)*L - L ≤ E - L := by linarith [hA]
    have step2 : -(ε+u) * L ≤ (1-ε)*(1-u)*L - L := by
      have h5 : (1-ε)*(1-u)*L - L = (-(ε+u) + ε*u) * L := by ring
      have h6 : 0 ≤ (ε*u) * L := mul_nonneg (mul_nonneg hε0 hu_nn) hLnn
      linarith
    have step3 : -(ε'/2) * L ≤ -(ε + u) * L := by
      have h7 : 0 ≤ (ε'/2 - (ε+u)) * L := mul_nonneg (by linarith [h2']) hLnn
      linarith
    linarith
  have hup' : E - L ≤ ε' * L / 2 := by
    have hfac : (E - L) * (1-u) ≤ (ε' * L / 2) * (1-u) := by
      have e1 : (E - L) * (1-u) = E * (1-u) - L * (1-u) := by ring
      have e2 : E * (1-u) - L * (1-u) ≤ (1+ε) * L - L * (1-u) := by linarith [hB']
      have e3 : (1+ε) * L - L * (1-u) = (ε+u)*L := by ring
      have e4 : (ε+u)*L ≤ ((ε'/2)*(1-u))*L := mul_le_mul_of_nonneg_right h3 hLnn
      have e5 : ((ε'/2)*(1-u))*L = (ε' * L / 2) * (1-u) := by ring
      linarith [e1, e2, e3, e4, e5]
    exact le_of_mul_le_mul_right hfac h1u
  rw [← hL, abs_le]
  exact ⟨hlow', hup'⟩

end Work.Deep.Nibble
