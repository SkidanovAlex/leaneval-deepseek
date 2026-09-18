import Mathlib
import Submission.Commons.NumberTheory.DuffinSchaeffer.coprime_symmetric_window_card
import Submission.Commons.NumberTheory.DuffinSchaeffer.reduced_pair_coprime_fiber
import Submission.Commons.NumberTheory.DuffinSchaeffer.residue_fiber_formula
import Submission.Commons.NumberTheory.Totient.coprime_interval_count_le
import Submission.Commons.NumberTheory.Nat.prod_dvd_iff_all_dvd
import Submission.Commons.NumberTheory.Nat.prime_dvd_finset_prod
import Submission.Commons.Data.Nat.exists_canonical_congruence_solution
import Submission.Commons.NumberTheory.Totient.totient_mul_gcd
import Submission.Commons.NumberTheory.Totient.totient_eq_prod_primeFactors
import Submission.Commons.Data.Nat.factorization_prod_prime_pow_apply

open scoped BigOperators

namespace Commons.NumberTheory.DuffinSchaeffer

set_option linter.unusedVariables false

/-- The reduced residues modulo `n`, `0 ≤ m < n` with `(m,n)=1`. -/
private def redMod (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun m : ℕ => m.gcd n = 1)

private lemma card_redMod (n : ℕ) : (redMod n).card = n.totient := by
  classical
  calc
    (redMod n).card = ((Finset.range n).filter (fun m : ℕ => n.Coprime m)).card := by
      congr 1
      refine Finset.filter_congr ?_
      intro m hm
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
    _ = n.totient := by
      exact (Nat.totient_eq_card_coprime n).symm

/-! ## Basic context arithmetic -/

private lemma fw_gcd_pos_of_q (q r : ℕ) (hq : 0 < q) : 0 < q.gcd r :=
  Nat.gcd_pos_of_pos_left r hq

private lemma fw_gcd_pos_of_r (q r : ℕ) (hr : 0 < r) : 0 < q.gcd r :=
  Nat.gcd_pos_of_pos_right q hr

private lemma fw_gQ_eq (q r : ℕ) : (q.gcd r) * (q / q.gcd r) = q := by
  rw [mul_comm]
  exact Nat.div_mul_cancel (Nat.gcd_dvd_left q r)

private lemma fw_gRr_eq (q r : ℕ) : (q.gcd r) * (r / q.gcd r) = r := by
  rw [mul_comm]
  exact Nat.div_mul_cancel (Nat.gcd_dvd_right q r)

private lemma fw_Q_pos (q r : ℕ) (hq : 0 < q) : 0 < q / q.gcd r := by
  have h : 0 < (q.gcd r) * (q / q.gcd r) := by
    rw [fw_gQ_eq q r]
    exact hq
  exact pos_of_mul_pos_right h (Nat.zero_le (q.gcd r))

private lemma fw_Rr_pos (q r : ℕ) (hr : 0 < r) : 0 < r / q.gcd r := by
  have h : 0 < (q.gcd r) * (r / q.gcd r) := by
    rw [fw_gRr_eq q r]
    exact hr
  exact pos_of_mul_pos_right h (Nat.zero_le (q.gcd r))

private lemma fw_L_eq_qRr (q r : ℕ) : q * r / q.gcd r = q * (r / q.gcd r) := by
  rw [Nat.mul_div_assoc q (Nat.gcd_dvd_right q r)]

private lemma fw_L_eq_rQ (q r : ℕ) : q * r / q.gcd r = r * (q / q.gcd r) := by
  rw [mul_comm, Nat.mul_div_assoc r (Nat.gcd_dvd_left q r)]

private lemma fw_L_eq_gQRr (q r : ℕ) :
    q * r / q.gcd r = q.gcd r * (q / q.gcd r) * (r / q.gcd r) := by
  calc
    q * r / q.gcd r = q * (r / q.gcd r) := fw_L_eq_qRr q r
    _ = (q.gcd r * (q / q.gcd r)) * (r / q.gcd r) := by rw [fw_gQ_eq q r]

private lemma fw_L_pos (q r : ℕ) (hq : 0 < q) (hr : 0 < r) : 0 < q * r / q.gcd r := by
  have hle : q.gcd r ≤ q * r := by
    exact le_trans (Nat.le_of_dvd hq (Nat.gcd_dvd_left q r)) (Nat.le_mul_of_pos_right q hr)
  exact Nat.div_pos hle (fw_gcd_pos_of_q q r hq)

private lemma fw_mRr_lt_L (q r m : ℕ) (hq : 0 < q) (hr : 0 < r) (hm : m < q) :
    m * (r / q.gcd r) < q * r / q.gcd r := by
  have hR0 : 0 < r / q.gcd r := fw_Rr_pos q r hr
  calc
    m * (r / q.gcd r) < q * (r / q.gcd r) := Nat.mul_lt_mul_of_pos_right hm hR0
    _ = q * r / q.gcd r := (fw_L_eq_qRr q r).symm

private lemma fw_nQ_lt_L (q r n : ℕ) (hq : 0 < q) (hr : 0 < r) (hn : n < r) :
    n * (q / q.gcd r) < q * r / q.gcd r := by
  have hQ0 : 0 < q / q.gcd r := fw_Q_pos q r hq
  calc
    n * (q / q.gcd r) < r * (q / q.gcd r) := Nat.mul_lt_mul_of_pos_right hn hQ0
    _ = q * r / q.gcd r := (fw_L_eq_rQ q r).symm

/-- `q/gcd(q,r)` and `r/gcd(q,r)` are coprime. -/
private lemma fw_coprime_Q_Rr (q r : ℕ) (hq : 0 < q) :
    Nat.Coprime (q / q.gcd r) (r / q.gcd r) := by
  rw [Nat.Coprime]
  have hg : 0 < q.gcd r := fw_gcd_pos_of_q q r hq
  let g : ℕ := q.gcd r
  let Q : ℕ := q / g
  let Rr : ℕ := r / g
  have hgdq : g * (Q.gcd Rr) ∣ q := by
    calc
      g * (Q.gcd Rr) ∣ g * Q := Nat.mul_dvd_mul_left g (Nat.gcd_dvd_left Q Rr)
      _ = q := by rw [mul_comm]; exact Nat.div_mul_cancel (Nat.gcd_dvd_left q r)
  have hgdr : g * (Q.gcd Rr) ∣ r := by
    calc
      g * (Q.gcd Rr) ∣ g * Rr := Nat.mul_dvd_mul_left g (Nat.gcd_dvd_right Q Rr)
      _ = r := by rw [mul_comm]; exact Nat.div_mul_cancel (Nat.gcd_dvd_right q r)
  have hgdg : g * (Q.gcd Rr) ∣ g := Nat.dvd_gcd hgdq hgdr
  rcases hgdg with ⟨c, hc⟩
  have hd1c : c * (Q.gcd Rr) = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hg
    calc
      g * (c * (Q.gcd Rr)) = (g * (Q.gcd Rr)) * c := by ring
      _ = g := hc.symm
      _ = g * 1 := by rw [mul_one]
  exact Nat.dvd_one.mp ⟨c, by rw [mul_comm]; exact hd1c.symm⟩

/-! ## Window partition: counting pairs by value residue -/


/-- `Σ` over the fibres of a function: `#{a : f a ∈ s} = Σ_{t∈s} #{a : f a = t}` -/
private lemma card_filter_mem_fibers {α : Type*} [DecidableEq α] (t0 : Finset α)
    (s : Finset ℕ) (f : α → ℕ) :
    (t0.filter (fun a => f a ∈ s)).card = ∑ t ∈ s, (t0.filter (fun a => f a = t)).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
      calc
        (t0.filter (fun a => f a ∈ insert x s)).card
            = (t0.filter (fun a => f a = x ∨ f a ∈ s)).card := by
                congr 1
                ext a
                simp [Finset.mem_insert]
        _ = ((t0.filter (fun a => f a = x)) ∪ (t0.filter (fun a => f a ∈ s))).card := by
                congr 1
                ext a
                simp only [Finset.mem_filter, Finset.mem_union]
                tauto
        _ = (t0.filter (fun a => f a = x)).card +
            (t0.filter (fun a => f a ∈ s)).card := by
                have hdisj : Disjoint (t0.filter (fun a => f a = x))
                    (t0.filter (fun a => f a ∈ s)) := by
                  rw [Finset.disjoint_left]
                  intro a ha hb
                  have hxval : f a = x := (Finset.mem_filter.mp ha).2
                  have hxmem : f a ∈ s := (Finset.mem_filter.mp hb).2
                  rw [hxval] at hxmem
                  exact hx hxmem
                exact Finset.card_union_of_disjoint hdisj
        _ = (t0.filter (fun a => f a = x)).card + ∑ t ∈ s, (t0.filter (fun a => f a = t)).card := by
                rw [ih]
        _ = ∑ t ∈ insert x s, (t0.filter (fun a => f a = t)).card := by
                rw [Finset.sum_insert hx]

/-! ## Window membership via the residue value -/

private lemma fw_mod_eq_self (a L : ℕ) (h : a < L) : a % L = a := Nat.mod_eq_of_lt h

/-- `(b + L - a) % L = (L - ((a + L - b) % L)) % L` for `a,b < L` -/
private lemma fw_bwd_of_fwd (a b L : ℕ) (ha : a < L) (hb : b < L) :
    ((b + L - a) % L) = (L - ((a + L - b) % L)) % L := by
  by_cases hab : a = b
  · subst b
    simp
  · have hne : a ≠ b := hab
    rcases lt_or_gt_of_ne hne with hablt | habgt
    · have hf0 : (a + L - b) % L = a + L - b := Nat.mod_eq_of_lt (by omega)
      rw [hf0]
      have hL : L - (a + L - b) = b - a := by omega
      rw [hL]
      calc
        (b + L - a) % L = (L + (b - a)) % L := by congr 1; omega
        _ = (b - a) % L := by
          rw [Nat.add_mod, Nat.mod_self]
          simp
    · have hf1 : (a + L - b) % L = a - b := by
        calc
          (a + L - b) % L = (L + (a - b)) % L := by congr 1; omega
          _ = (a - b) % L := by
            rw [Nat.add_mod, Nat.mod_self]
            simp
          _ = a - b := Nat.mod_eq_of_lt (by omega)
      rw [hf1]
      have hL : L - (a - b) = b + L - a := by omega
      rw [hL]

/-- backward residue ≤ W iff `v = 0` or `v ≥ L - W`, for `v < L`, `2W+1 ≤ L` -/
private lemma fw_bwd_le_iff (v W L : ℕ) (hL : 0 < L) (hv : v < L) (hW : 2 * W + 1 ≤ L) :
    ((L - v) % L ≤ W) ↔ v = 0 ∨ L - W ≤ v := by
  by_cases hv0 : v = 0
  · simp [hv0]
  · have hvpos : 0 < v := Nat.pos_of_ne_zero hv0
    have hmod : (L - v) % L = L - v := Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    constructor
    · intro hle
      right
      omega
    · intro h
      rcases h with hv0' | hge
      · contradiction
      · omega

/-- window equivalence: `(v ≤ W ∨ (L-v)%L ≤ W)` iff `v` lies in `[0,W] ∪ [L-W, L-1]`,
for `2W+1 ≤ L` and `v < L`. -/
private lemma fw_in_window_iff (v W L : ℕ) (hL : 0 < L) (hv : v < L) (hW : 2 * W + 1 ≤ L) :
    (v ≤ W ∨ (L - v) % L ≤ W) ↔ v ∈ Finset.Icc 0 W ∨ v ∈ Finset.Icc (L - W) (L - 1) := by
  classical
  rw [fw_bwd_le_iff v W L hL hv hW]
  constructor
  · intro h
    rcases h with hlo | hz | hhi
    · left
      exact Finset.mem_Icc.mpr ⟨by omega, hlo⟩
    · left
      subst v
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · right
      exact Finset.mem_Icc.mpr ⟨hhi, by omega⟩
  · intro h
    rcases h with hlo | hhi
    · left
      exact (Finset.mem_Icc.mp hlo).2
    · rw [Finset.mem_Icc] at hhi
      right
      omega

/-! ## Expansion of the multiplicative window product (P3 building block) -/

/-- coefficient `(p-2)/(p-1)` -/
private noncomputable def fwCp (p : ℕ) : ℝ := (((p - 2 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ))

/-- coefficient `1/(p-1)` -/
private noncomputable def fwDp (p : ℕ) : ℝ := ((1 : ℝ) / ((p - 1 : ℕ) : ℝ))

private lemma fw_cp_add_dp (p : ℕ) (hp : 2 ≤ p) : fwCp p + fwDp p = 1 := by
  have hden : (p - 1 : ℕ) ≠ 0 := by omega
  have hnum : (((p - 2 : ℕ) : ℝ) + 1) = ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : (p - 2 : ℕ) + 1 = p - 1)
  dsimp [fwCp, fwDp]
  rw [← add_div]
  rw [hnum]
  exact div_self (by exact_mod_cast hden)

/-- product of indicators over a finite set of primes = indicator that the product divides `s` -/
private lemma prod_indicator_dvd_of_primes (U : Finset ℕ) (s : ℕ)
    (hU : ∀ p ∈ U, p.Prime) :
    (∏ p ∈ U, (if p ∣ s then (1 : ℝ) else 0)) =
      (if (∏ p ∈ U, p) ∣ s then (1 : ℝ) else 0) := by
  classical
  by_cases hd : (∏ p ∈ U, p) ∣ s
  · have hall : ∀ p ∈ U, p ∣ s := by
      intro p hp
      exact dvd_trans (Finset.dvd_prod_of_mem (fun p : ℕ => p) hp) hd
    rw [if_pos hd]
    apply Finset.prod_eq_one
    intro p hp
    rw [if_pos (hall p hp)]
  · have hsome : ∃ p ∈ U, ¬ p ∣ s := by
      by_contra hn
      push_neg at hn
      by_cases hs : s = 0
      · subst s
        exact hd (by simp)
      · have hS : U ⊆ s.primeFactors := by
          intro p hp
          exact Nat.mem_primeFactors.mpr ⟨hU p hp, hn p hp, hs⟩
        have hdvd : (∏ p ∈ U, p) ∣ s :=
          (Commons.NumberTheory.Nat.prod_dvd_iff_all_dvd hS).mpr (fun p hp => hn p hp)
        exact hd hdvd
    rcases hsome with ⟨p0, hp0U, hp0⟩
    simp [hd]
    apply Finset.prod_eq_zero hp0U
    exact if_neg hp0

/-- Expansion: `∏_{p | R, p ∤ s} (p-2)/(p-1) = Σ_{U ⊆ primeFactors R}
`∏_{p∈U} 1/(p-1) · ∏_{p∉U} (p-2)/(p-1) · [∏_{p∈U} p | s]`. -/
private lemma fw_prod_expand (R s : ℕ) :
    (∏ p ∈ R.primeFactors.filter (fun p : ℕ => ¬ p ∣ s), fwCp p) =
      ∑ U ∈ R.primeFactors.powerset,
        (∏ p ∈ U, fwDp p) * (∏ p ∈ R.primeFactors \ U, fwCp p) *
          (if (∏ p ∈ U, p) ∣ s then (1 : ℝ) else 0) := by
  classical
  have hfilter : (∏ p ∈ R.primeFactors.filter (fun p : ℕ => ¬ p ∣ s), fwCp p) =
      ∏ p ∈ R.primeFactors, (fwCp p + fwDp p * (if p ∣ s then (1 : ℝ) else 0)) := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpc : fwCp p + fwDp p = 1 := fw_cp_add_dp p hpp.two_le
    by_cases hps : p ∣ s
    · simp [hps, hpc]
    · simp [hps]
  calc
    (∏ p ∈ R.primeFactors.filter (fun p : ℕ => ¬ p ∣ s), fwCp p)
        = ∏ p ∈ R.primeFactors, (fwCp p + fwDp p * (if p ∣ s then (1 : ℝ) else 0)) := hfilter
    _ = ∑ U ∈ R.primeFactors.powerset,
        (∏ p ∈ U, (fwDp p * (if p ∣ s then (1 : ℝ) else 0))) *
          (∏ p ∈ R.primeFactors \ U, fwCp p) := by
          have hswap : (∏ p ∈ R.primeFactors, (fwCp p + fwDp p * (if p ∣ s then (1 : ℝ) else 0))) =
              ∏ p ∈ R.primeFactors, ((fwDp p * (if p ∣ s then (1 : ℝ) else 0)) + fwCp p) := by
            refine Finset.prod_congr rfl ?_
            intro p hp
            rw [add_comm]
          rw [hswap]
          exact Finset.prod_add (fun p : ℕ => fwDp p * (if p ∣ s then (1 : ℝ) else 0))
            (fun p : ℕ => fwCp p) R.primeFactors
    _ = ∑ U ∈ R.primeFactors.powerset,
        (∏ p ∈ U, fwDp p) * (∏ p ∈ R.primeFactors \ U, fwCp p) *
          (if (∏ p ∈ U, p) ∣ s then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro U hU
          have hUp : ∀ p ∈ U, p.Prime := fun p hp =>
            Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hU hp)
          have hsplit : (∏ p ∈ U, (fwDp p * (if p ∣ s then (1 : ℝ) else 0))) =
              (∏ p ∈ U, fwDp p) * (if (∏ p ∈ U, p) ∣ s then (1 : ℝ) else 0) := by
            rw [Finset.prod_mul_distrib]
            congr 1
            exact prod_indicator_dvd_of_primes U s hUp
          rw [hsplit]
          ring

/-! ## Window partition (value fibres) -/

/-- the value residue of the pair `(m,n)` -/
private def fwVal2 (q r m n : ℕ) : ℕ :=
  let g : ℕ := q.gcd r
  let L : ℕ := q * r / g
  ((m * (r / g)) % L + L - (n * (q / g)) % L) % L

/-- the pair set of reduced residues -/
private def fwPQ (q r : ℕ) : Finset (ℕ × ℕ) :=
  Finset.product ((Finset.range q).filter (fun m : ℕ => m.gcd q = 1))
                 ((Finset.range r).filter (fun n : ℕ => n.gcd r = 1))

/-- P for the pair set -/
private noncomputable def fwP (q r W : ℕ) : ℕ × ℕ → Prop :=
  let L : ℕ := q * r / (q.gcd r)
  fun mn => (((mn.1 * (r / q.gcd r)) % L) + L - ((mn.2 * (q / q.gcd r)) % L)) % L ≤ W ∨
            (((mn.2 * (q / q.gcd r)) % L) + L - ((mn.1 * (r / q.gcd r)) % L)) % L ≤ W

private noncomputable instance fwP_dec (q r W : ℕ) : DecidablePred (fwP q r W) :=
  fun _ => Classical.propDecidable _

/-- P iff the value lies in `[0,W] ∪ [L-W, L-1]`, for `2W+1 ≤ L`. -/
private lemma fwP_val_mem (q r W : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hW : 2 * W + 1 ≤ q * r / (q.gcd r)) (mn : ℕ × ℕ) (hmn : mn ∈ fwPQ q r) :
    let L : ℕ := q * r / (q.gcd r)
    let v : ℕ := ((mn.1 * (r / q.gcd r)) % L + L - (mn.2 * (q / q.gcd r)) % L) % L
    fwP q r W mn ↔ v ∈ Finset.Icc 0 W ∨ v ∈ Finset.Icc (L - W) (L - 1) := by
  classical
  intro L v
  have hL0 : 0 < L := by
    dsimp [L]
    exact fw_L_pos q r hq hr
  have ha : (mn.1 * (r / q.gcd r)) % L < L := Nat.mod_lt _ hL0
  have hb : (mn.2 * (q / q.gcd r)) % L < L := Nat.mod_lt _ hL0
  have hv : v < L := by
    dsimp [v]
    exact Nat.mod_lt _ hL0
  change (((mn.1 * (r / q.gcd r)) % L + L - (mn.2 * (q / q.gcd r)) % L) % L ≤ W ∨
          ((mn.2 * (q / q.gcd r)) % L + L - (mn.1 * (r / q.gcd r)) % L) % L ≤ W) ↔
         v ∈ Finset.Icc 0 W ∨ v ∈ Finset.Icc (L - W) (L - 1)
  have hbwd : ((mn.2 * (q / q.gcd r)) % L + L - (mn.1 * (r / q.gcd r)) % L) % L =
      (L - v) % L := by
    dsimp [v]
    exact fw_bwd_of_fwd ((mn.1 * (r / q.gcd r)) % L) ((mn.2 * (q / q.gcd r)) % L) L ha hb
  have hfwd : ((mn.1 * (r / q.gcd r)) % L + L - (mn.2 * (q / q.gcd r)) % L) % L = v := by
    rfl
  rw [hfwd, hbwd]
  exact fw_in_window_iff v W L hL0 hv hW

private lemma fw_card_filter_P (q r W : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hW : 2 * W + 1 ≤ q * r / (q.gcd r)) :
    let L : ℕ := q * r / (q.gcd r)
    let f : ℕ × ℕ → ℕ := fun mn => ((mn.1 * (r / q.gcd r)) % L + L - (mn.2 * (q / q.gcd r)) % L) % L
    ((fwPQ q r).filter (fwP q r W)).card =
      ∑ t ∈ Finset.Icc 0 W, ((fwPQ q r).filter (fun mn : ℕ × ℕ => f mn = t)).card +
      ∑ t ∈ Finset.Icc (L - W) (L - 1), ((fwPQ q r).filter (fun mn : ℕ × ℕ => f mn = t)).card := by
  classical
  intro L f
  let S : Finset ℕ := (Finset.Icc 0 W) ∪ (Finset.Icc (L - W) (L - 1))
  have hP : (fwPQ q r).filter (fwP q r W) =
      (fwPQ q r).filter (fun mn : ℕ × ℕ => f mn ∈ S) := by
    apply Finset.filter_congr
    intro mn hmn
    have hiff := fwP_val_mem q r W hq hr hW mn hmn
    -- hiff is about v-expression; f is the same expression
    simpa [S, f] using hiff
  have hfib : ((fwPQ q r).filter (fun mn : ℕ × ℕ => f mn ∈ S)).card =
      ∑ t ∈ S, ((fwPQ q r).filter (fun mn : ℕ × ℕ => f mn = t)).card := by
    exact card_filter_mem_fibers (fwPQ q r) S f
  have hdisj : Disjoint (Finset.Icc 0 W) (Finset.Icc (L - W) (L - 1)) := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    have ht1' := (Finset.mem_Icc.mp ht1)
    have ht2' := (Finset.mem_Icc.mp ht2)
    have hW' : W + 1 ≤ L - W := by
      dsimp [L]
      omega
    omega
  calc
    ((fwPQ q r).filter (fwP q r W)).card
        = ((fwPQ q r).filter (fun mn : ℕ × ℕ => f mn ∈ S)).card := by rw [hP]
    _ = ∑ t ∈ S, ((fwPQ q r).filter (fun mn : ℕ × ℕ => f mn = t)).card := hfib
    _ = ∑ t ∈ Finset.Icc 0 W, ((fwPQ q r).filter (fun mn : ℕ × ℕ => f mn = t)).card +
        ∑ t ∈ Finset.Icc (L - W) (L - 1), ((fwPQ q r).filter (fun mn : ℕ × ℕ => f mn = t)).card := by
          dsimp [S]
          rw [Finset.sum_union hdisj]

/-! ## General-case assembly: definitions and arithmetic -/

/-- `A := Q·Rr`, the product of the coprime quotients (equals `q·r/g²`). -/
private def fwA (q r : ℕ) : ℕ := (q / (q.gcd r)) * (r / (q.gcd r))

/-- the primes of `g = (q,r)` not dividing `A`. -/
private def fwPr (q r : ℕ) : Finset ℕ :=
  (q.gcd r).primeFactors.filter (fun p : ℕ => ¬ p ∣ fwA q r)

private lemma fwA_eq_mul_div_gcd_sq (q r : ℕ) :
    q * r / ((q.gcd r) * (q.gcd r)) = fwA q r := by
  dsimp [fwA]
  exact (Nat.div_mul_div_comm (Nat.gcd_dvd_left q r) (Nat.gcd_dvd_right q r)).symm

private lemma fwA_pos (q r : ℕ) (hq : 0 < q) (hr : 0 < r) : 0 < fwA q r := by
  exact Nat.mul_pos (fw_Q_pos q r hq) (fw_Rr_pos q r hr)

private lemma fwA_eq_one_iff (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    fwA q r = 1 ↔ q / (q.gcd r) = 1 ∧ r / (q.gcd r) = 1 := by
  constructor
  · intro h
    have hQ : 0 < q / (q.gcd r) := fw_Q_pos q r hq
    have hR : 0 < r / (q.gcd r) := fw_Rr_pos q r hr
    have hprod : (q / (q.gcd r)) * (r / (q.gcd r)) = 1 := by simpa [fwA] using h
    have hQ1 : q / (q.gcd r) = 1 := by
      exact Nat.eq_one_of_mul_eq_one_left (by rw [mul_comm, hprod])
    have hR1 : r / (q.gcd r) = 1 := Nat.eq_one_of_mul_eq_one_left hprod
    exact ⟨hQ1, hR1⟩
  · intro h
    rcases h with ⟨hQ, hR⟩
    dsimp [fwA]
    rw [hQ, hR]

private lemma fw_L_eq_g_mul_A (q r : ℕ) :
    q * r / (q.gcd r) = (q.gcd r) * fwA q r := by
  dsimp [fwA]
  calc
    q * r / (q.gcd r) = ((q.gcd r) * (q / (q.gcd r))) * (r / (q.gcd r)) := fw_L_eq_gQRr q r
    _ = (q.gcd r) * ((q / (q.gcd r)) * (r / (q.gcd r))) := by rw [mul_assoc]

private lemma fw_A_dvd_L (q r : ℕ) : fwA q r ∣ q * r / (q.gcd r) := by
  rw [fw_L_eq_g_mul_A q r, mul_comm]
  exact dvd_mul_right (fwA q r) (q.gcd r)

private lemma fw_g_dvd_L (q r : ℕ) : (q.gcd r) ∣ q * r / (q.gcd r) := by
  rw [fw_L_eq_g_mul_A q r]
  exact dvd_mul_right (q.gcd r) (fwA q r)

/-- a prime of `fwPr` divides `g` (so is a prime). -/
private lemma fwPr_mem_iff (q r p : ℕ) :
    p ∈ fwPr q r ↔ p ∈ (q.gcd r).primeFactors ∧ ¬ p ∣ fwA q r := by
  simp [fwPr]

/-- an element of `fwPr` is prime, divides `g` and does not divide `A`. -/
private lemma fwPr_prime_dvd_g (q r p : ℕ) (hp : p ∈ fwPr q r) :
    p.Prime ∧ p ∣ (q.gcd r) ∧ ¬ p ∣ fwA q r := by
  have h := (fwPr_mem_iff q r p).mp hp
  exact ⟨(Nat.mem_primeFactors.mp h.1).1, (Nat.mem_primeFactors.mp h.1).2.1, h.2⟩

/-- an element of `fwPr` divides `L`. -/
private lemma fwPr_dvd_L (q r p : ℕ) (hp : p ∈ fwPr q r) : p ∣ q * r / (q.gcd r) := by
  exact dvd_trans (fwPr_prime_dvd_g q r p hp).2.1 (fw_g_dvd_L q r)

/-- `A` and the product over `fwPr` are coprime. -/
private lemma fwA_coprime_prod_fwPr (q r : ℕ) :
    Nat.Coprime (fwA q r) (∏ p ∈ fwPr q r, p) := by
  classical
  by_contra hg
  rcases Nat.exists_prime_and_dvd (n := (fwA q r).gcd (∏ p ∈ fwPr q r, p)) hg with ⟨p, hpP, hpd⟩
  have hpdA : p ∣ fwA q r := dvd_trans hpd (Nat.gcd_dvd_left _ _)
  have hpdP : p ∣ ∏ x ∈ fwPr q r, x := dvd_trans hpd (Nat.gcd_dvd_right _ _)
  rcases Commons.NumberTheory.Nat.prime_dvd_finset_prod (s := fwPr q r) hpP (fun x : ℕ => x) hpdP with
    ⟨x, hx, hpx⟩
  have hxP : x.Prime := (fwPr_prime_dvd_g q r x hx).1
  have hpxeq : p = x := by
    rcases hxP.eq_one_or_self_of_dvd p hpx with h1 | hEq
    · exact False.elim (hpP.ne_one h1)
    · exact hEq
  have hxndA : ¬ x ∣ fwA q r := (fwPr_prime_dvd_g q r x hx).2.2
  exact hxndA (by simpa [hpxeq] using hpdA)

/-! ## The `h`-weight and its subset expansion -/

/-- `gprod_S(s) = ∏_{p ∈ S, p∤s} (p−2)/(p−1)` (the fibre weight product). -/
private noncomputable def fwGprod (S : Finset ℕ) (s : ℕ) : ℝ :=
  ∏ p ∈ S.filter (fun p : ℕ => ¬ p ∣ s), fwCp p

/-- the indicator of coprimality with `A`. -/
private noncomputable def fwCopr (q r t : ℕ) : ℝ :=
  if t.gcd (fwA q r) = 1 then (1 : ℝ) else 0

/-- `h(t) = [gcd(t,A)=1]·gprod(t)`, the fibre weight (before multiplying by `φ(g)`). -/
private noncomputable def fwH (q r t : ℕ) : ℝ := fwCopr q r t * fwGprod (fwPr q r) t

/-- subset expansion of `gprod` over an arbitrary prime set -/
private lemma fw_prod_expand_set (S : Finset ℕ) (s : ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S.filter (fun p : ℕ => ¬ p ∣ s), fwCp p) =
      ∑ U ∈ S.powerset,
        (∏ p ∈ U, fwDp p) * (∏ p ∈ S \ U, fwCp p) *
          (if (∏ p ∈ U, p) ∣ s then (1 : ℝ) else 0) := by
  classical
  have hfilter : (∏ p ∈ S.filter (fun p : ℕ => ¬ p ∣ s), fwCp p) =
      ∏ p ∈ S, (fwCp p + fwDp p * (if p ∣ s then (1 : ℝ) else 0)) := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hpc : fwCp p + fwDp p = 1 := fw_cp_add_dp p (hS p hp).two_le
    by_cases hps : p ∣ s
    · simp [hps, hpc]
    · simp [hps]
  calc
    (∏ p ∈ S.filter (fun p : ℕ => ¬ p ∣ s), fwCp p)
        = ∏ p ∈ S, (fwCp p + fwDp p * (if p ∣ s then (1 : ℝ) else 0)) := hfilter
    _ = ∑ U ∈ S.powerset,
        (∏ p ∈ U, (fwDp p * (if p ∣ s then (1 : ℝ) else 0))) *
          (∏ p ∈ S \ U, fwCp p) := by
          have hswap : (∏ p ∈ S, (fwCp p + fwDp p * (if p ∣ s then (1 : ℝ) else 0))) =
              ∏ p ∈ S, ((fwDp p * (if p ∣ s then (1 : ℝ) else 0)) + fwCp p) := by
            refine Finset.prod_congr rfl ?_
            intro p hp
            rw [add_comm]
          rw [hswap]
          exact Finset.prod_add (fun p : ℕ => fwDp p * (if p ∣ s then (1 : ℝ) else 0))
            (fun p : ℕ => fwCp p) S
    _ = ∑ U ∈ S.powerset,
        (∏ p ∈ U, fwDp p) * (∏ p ∈ S \ U, fwCp p) *
          (if (∏ p ∈ U, p) ∣ s then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro U hU
          have hUp : ∀ p ∈ U, p.Prime := fun p hp => hS p (Finset.mem_powerset.mp hU hp)
          have hsplit : (∏ p ∈ U, (fwDp p * (if p ∣ s then (1 : ℝ) else 0))) =
              (∏ p ∈ U, fwDp p) * (if (∏ p ∈ U, p) ∣ s then (1 : ℝ) else 0) := by
            rw [Finset.prod_mul_distrib]
            congr 1
            exact prod_indicator_dvd_of_primes U s hUp
          rw [hsplit]
          ring

/-- `gprod` equals the `U`-weighted sum over subsets. -/
private lemma fw_gprod_expand (S : Finset ℕ) (s : ℕ) (hS : ∀ p ∈ S, p.Prime) :
    fwGprod S s =
      ∑ U ∈ S.powerset,
        (∏ p ∈ U, fwDp p) * (∏ p ∈ S \ U, fwCp p) *
          (if (∏ p ∈ U, p) ∣ s then (1 : ℝ) else 0) := by
  dsimp [fwGprod]
  exact fw_prod_expand_set S s hS

/-- `Σ_U γ_U = 1` over a prime set. -/
private lemma fw_sum_gamma_eq_one (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ U ∈ S.powerset, (∏ p ∈ U, fwDp p) * (∏ p ∈ S \ U, fwCp p)) = 1 := by
  classical
  calc
    (∑ U ∈ S.powerset, (∏ p ∈ U, fwDp p) * (∏ p ∈ S \ U, fwCp p))
        = ∏ p ∈ S, (fwDp p + fwCp p) := by
          exact (Finset.prod_add (fun p : ℕ => fwDp p) (fun p : ℕ => fwCp p) S).symm
    _ = 1 := by
          refine Finset.prod_eq_one ?_
          intro p hp
          simpa [add_comm] using (fw_cp_add_dp p (hS p hp).two_le)

/-- `Σ_U γ_U / ∏_{p∈U}p = ∏_{p∈S} (p−1)/p` over a prime set. -/
private lemma fw_sum_gamma_div_dprod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ U ∈ S.powerset,
        (∏ p ∈ U, fwDp p) * (∏ p ∈ S \ U, fwCp p) * ((∏ p ∈ U, (p : ℝ))⁻¹)) =
      ∏ p ∈ S, (((p : ℝ) - 1) / (p : ℝ)) := by
  classical
  have hprod_inv : ∀ U ∈ S.powerset,
      (∏ p ∈ U, (fwDp p)) * ((∏ p ∈ U, (p : ℝ))⁻¹) =
        ∏ p ∈ U, (fwDp p * ((p : ℝ)⁻¹)) := by
    intro U hU
    calc
      (∏ p ∈ U, fwDp p) * ((∏ p ∈ U, (p : ℝ))⁻¹)
          = (∏ p ∈ U, fwDp p) * (∏ p ∈ U, ((p : ℝ)⁻¹)) := by
              rw [Finset.prod_inv_distrib]
      _ = ∏ p ∈ U, (fwDp p * ((p : ℝ)⁻¹)) := by
              rw [Finset.prod_mul_distrib]
  calc
    (∑ U ∈ S.powerset,
        (∏ p ∈ U, fwDp p) * (∏ p ∈ S \ U, fwCp p) * ((∏ p ∈ U, (p : ℝ))⁻¹))
        = ∑ U ∈ S.powerset,
            (∏ p ∈ U, (fwDp p * ((p : ℝ)⁻¹))) * (∏ p ∈ S \ U, fwCp p) := by
            refine Finset.sum_congr rfl ?_
            intro U hU
            calc
              (∏ p ∈ U, fwDp p) * (∏ p ∈ S \ U, fwCp p) * ((∏ p ∈ U, (p : ℝ))⁻¹)
                  = (∏ p ∈ U, fwDp p) * ((∏ p ∈ U, (p : ℝ))⁻¹) *
                      (∏ p ∈ S \ U, fwCp p) := by ring
              _ = (∏ p ∈ U, (fwDp p * ((p : ℝ)⁻¹))) * (∏ p ∈ S \ U, fwCp p) := by
                      rw [hprod_inv U hU]
    _ = ∏ p ∈ S, (fwDp p * ((p : ℝ)⁻¹) + fwCp p) := by
            exact (Finset.prod_add (fun p : ℕ => fwDp p * ((p : ℝ)⁻¹))
              (fun p : ℕ => fwCp p) S).symm
    _ = ∏ p ∈ S, (((p : ℝ) - 1) / (p : ℝ)) := by
            refine Finset.prod_congr rfl ?_
            intro p hp
            have hpp : p.Prime := hS p hp
            have hp2 : 2 ≤ p := hpp.two_le
            have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
            have hc2 : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
              rw [Nat.cast_sub (by omega : (2 : ℕ) ≤ p)]
              norm_num
            have hc1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
              rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ p)]
              norm_num
            have hdenR : (p : ℝ) - 1 ≠ 0 := by
              rw [← hc1]
              exact_mod_cast (by omega : (p - 1 : ℕ) ≠ 0)
            dsimp [fwCp, fwDp]
            rw [hc2, hc1]
            field_simp [hp0, hdenR]
            ring

/-! ## Divisibility reflection and divisor-count bounds -/

/-- `b ∣ a−s ↔ b ∣ s` when `b ∣ a` and `s ≤ a`. -/
private lemma fw_dvd_sub_iff (a b s : ℕ) (hba : b ∣ a) (hs : s ≤ a) : b ∣ a - s ↔ b ∣ s := by
  constructor
  · intro h
    have hdvd : b ∣ a - (a - s) := Nat.dvd_sub hba h
    have hsub : a - (a - s) = s := Nat.sub_sub_self hs
    rwa [hsub] at hdvd
  · intro hs'
    exact Nat.dvd_sub hba hs'

/-- `gcd(a−s,A) = gcd(s,A)` when `A ∣ a` and `s ≤ a`. -/
private lemma fw_gcd_sub_eq_gcd (a A s : ℕ) (hAd : A ∣ a) (hs : s ≤ a) :
    (a - s).gcd A = s.gcd A := by
  classical
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · have hg : (a - s).gcd A ∣ a - s := Nat.gcd_dvd_left _ _
      have hgA : (a - s).gcd A ∣ A := Nat.gcd_dvd_right _ _
      have hga : (a - s).gcd A ∣ a := dvd_trans hgA hAd
      exact (fw_dvd_sub_iff a ((a - s).gcd A) s hga hs).mp hg
    · exact Nat.gcd_dvd_right _ _
  · apply Nat.dvd_gcd
    · have hg : s.gcd A ∣ s := Nat.gcd_dvd_left _ _
      have hgA : s.gcd A ∣ A := Nat.gcd_dvd_right _ _
      have hga : s.gcd A ∣ a := dvd_trans hgA hAd
      exact (fw_dvd_sub_iff a (s.gcd A) s hga hs).mpr hg
    · exact Nat.gcd_dvd_right _ _

/-- `gcd(L−s,A) = gcd(s,A)` for `s ≤ L`. -/
private lemma fw_gcd_L_sub_A (q r s : ℕ) (hs : s ≤ q * r / (q.gcd r)) :
    ((q * r / (q.gcd r)) - s).gcd (fwA q r) = s.gcd (fwA q r) :=
  fw_gcd_sub_eq_gcd (q * r / (q.gcd r)) (fwA q r) s (fw_A_dvd_L q r) hs

/-- divisor-count of `n ≥ 1` is at least `2^ω(n)`. -/
private lemma fw_card_divisors_ge (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℕ) ^ n.primeFactors.card ≤ n.divisors.card := by
  classical
  have hn0 : n ≠ 0 := by omega
  rw [Nat.card_divisors hn0]
  calc
    (∏ p ∈ n.primeFactors, (n.factorization p + 1))
        ≥ (∏ p ∈ n.primeFactors, (2 : ℕ)) := by
            refine Finset.prod_le_prod₀ ?_ ?_
            · intro p hp
              exact Nat.zero_le _
            · intro p hp
              have hpP : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
              have hpd : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
              have hfac_ne : n.factorization p ≠ 0 := by
                intro hz
                have hz' := (Nat.factorization_eq_zero_iff n p).mp hz
                tauto
              omega
    _ = (2 : ℕ) ^ n.primeFactors.card := by
            simp [Finset.card_powerset]

/-- real version of the divisor-count bound. -/
private lemma fw_card_divisors_ge_real (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) ^ n.primeFactors.card ≤ (n.divisors.card : ℝ) := by
  exact_mod_cast (fw_card_divisors_ge n hn)

/-- `n ≥ 1` has at least one divisor, so `τ n ≥ 1`. -/
private lemma fw_tau_ge_one (n : ℕ) (hn : 1 ≤ n) : 1 ≤ n.divisors.card := by
  classical
  have hmem : 1 ∈ n.divisors := by
    rw [Nat.mem_divisors]
    exact ⟨one_dvd n, by omega⟩
  exact Finset.card_pos.mpr ⟨1, hmem⟩

/-- `3 ≤ 3^ω(g)` when `2 ≤ g`. -/
private lemma fw_three_le_three_pow (g : ℕ) (hg : 2 ≤ g) :
    (3 : ℝ) ≤ (3 : ℝ) ^ g.primeFactors.card := by
  classical
  have hg1 : g ≠ 1 := by omega
  rcases Nat.exists_prime_and_dvd hg1 with ⟨p, hpP, hpd⟩
  have hmem : p ∈ g.primeFactors := Nat.mem_primeFactors.mpr ⟨hpP, hpd, by omega⟩
  have hω0 : 0 < g.primeFactors.card := Finset.card_pos.mpr ⟨p, hmem⟩
  have hω1 : 1 ≤ g.primeFactors.card := by omega
  have hbase : 3 ≤ (3 : ℝ) ^ 1 := by norm_num
  exact le_trans hbase (pow_le_pow_right₀ (by norm_num : 1 ≤ (3 : ℝ)) hω1)

/-- the error bound in the general case: `φ(g)(1 + 2^{ω(A)+1}) ≤ φ(g)·τ(A)·3^{ω(g)}`
(with `A` replaced by `q·r/g²` in the divisor count). -/
private lemma fw_err_le (q r : ℕ) (hg : 2 ≤ q.gcd r) (hA : 1 ≤ fwA q r) :
    ((q.gcd r).totient : ℝ) * ((2 : ℝ) ^ ((fwA q r).primeFactors.card + 1) + 1) ≤
    ((q.gcd r).totient : ℝ) *
      (((q * r / ((q.gcd r) * (q.gcd r))).divisors.card : ℕ) : ℝ) *
      (3 : ℝ) ^ (q.gcd r).primeFactors.card := by
  have hτ : ((q * r / ((q.gcd r) * (q.gcd r))).divisors.card : ℕ) = (fwA q r).divisors.card := by
    rw [fwA_eq_mul_div_gcd_sq q r]
  rw [hτ]
  have hφ0 : 0 ≤ ((q.gcd r).totient : ℝ) := by exact_mod_cast Nat.zero_le _
  have h2 : (2 : ℝ) ^ ((fwA q r).primeFactors.card + 1) ≤
      (2 : ℝ) * ((fwA q r).divisors.card : ℝ) := by
    have hAω : (2 : ℝ) ^ (fwA q r).primeFactors.card ≤ ((fwA q r).divisors.card : ℝ) :=
      fw_card_divisors_ge_real (fwA q r) hA
    have hpow : (2 : ℝ) ^ ((fwA q r).primeFactors.card + 1) =
        (2 : ℝ) * (2 : ℝ) ^ (fwA q r).primeFactors.card := by
      rw [pow_succ']
    rw [hpow]
    nlinarith
  have h1 : (1 : ℝ) ≤ ((fwA q r).divisors.card : ℝ) := by
    exact_mod_cast (fw_tau_ge_one (fwA q r) hA)
  have h3 : (3 : ℝ) ≤ (3 : ℝ) ^ (q.gcd r).primeFactors.card :=
    fw_three_le_three_pow (q.gcd r) hg
  have hτ0 : 0 ≤ ((fwA q r).divisors.card : ℝ) := by exact_mod_cast Nat.zero_le _
  have hsum : (2 : ℝ) ^ ((fwA q r).primeFactors.card + 1) + 1 ≤
      (3 : ℝ) * ((fwA q r).divisors.card : ℝ) := by
    nlinarith
  calc
    ((q.gcd r).totient : ℝ) * ((2 : ℝ) ^ ((fwA q r).primeFactors.card + 1) + 1)
        ≤ ((q.gcd r).totient : ℝ) * ((3 : ℝ) * ((fwA q r).divisors.card : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hsum hφ0
    _ = ((q.gcd r).totient : ℝ) * ((fwA q r).divisors.card : ℝ) * (3 : ℝ) := by ring
    _ ≤ ((q.gcd r).totient : ℝ) * ((fwA q r).divisors.card : ℝ) *
          (3 : ℝ) ^ (q.gcd r).primeFactors.card := by
            exact mul_le_mul_of_nonneg_left h3 (mul_nonneg hφ0 (by exact_mod_cast Nat.zero_le _))

/-! ## The fibre identity and coefficient identity (main analytic facts) -/

/-- the value residue of a pair. -/
private noncomputable def fwVal (q r : ℕ) (mn : ℕ × ℕ) : ℕ :=
  (((mn.1 * (r / (q.gcd r))) % (q * r / (q.gcd r))) + (q * r / (q.gcd r)) -
    ((mn.2 * (q / (q.gcd r))) % (q * r / (q.gcd r)))) % (q * r / (q.gcd r))

/-- the fibre cardinality at value `t`. -/
private noncomputable def fwFib (q r t : ℕ) : ℕ :=
  ((fwPQ q r).filter (fun mn : ℕ × ℕ => fwVal q r mn = t)).card

/-- the count of `j ∈ [1,x]` coprime to `A`. -/
private noncomputable def fwCcnt (A x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun j : ℕ => j.gcd A = 1)).card

/-- `d_U = ∏_{p∈U} p`. -/
private noncomputable def fwDprod (U : Finset ℕ) : ℕ := ∏ p ∈ U, p

/-- the weight `γ_U`. -/
private noncomputable def fwGamma (q r : ℕ) (U : Finset ℕ) : ℝ :=
  (∏ p ∈ U, fwDp p) * (∏ p ∈ (fwPr q r) \ U, fwCp p)

/-- `pf(q·r) = pf(g) ∪ pf(A)`. -/
private lemma fw_pf_gA (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    (q * r).primeFactors = (q.gcd r).primeFactors ∪ (fwA q r).primeFactors := by
  classical
  have hqreq : q * r = ((q.gcd r) * (q.gcd r)) * fwA q r := by
    dsimp [fwA]
    calc
      q * r = (q.gcd r) * (q / q.gcd r) * ((q.gcd r) * (r / q.gcd r)) := by
        rw [fw_gQ_eq q r, fw_gRr_eq q r]
      _ = ((q.gcd r) * (q.gcd r)) * ((q / q.gcd r) * (r / q.gcd r)) := by ring
  have hgg : (q.gcd r) * (q.gcd r) ≠ 0 := by positivity
  have hA : (fwA q r) ≠ 0 := ne_of_gt (fwA_pos q r hq hr)
  have hg0 : q.gcd r ≠ 0 := by positivity
  calc
    (q * r).primeFactors = (((q.gcd r) * (q.gcd r)) * fwA q r).primeFactors := by rw [hqreq]
    _ = ((q.gcd r) * (q.gcd r)).primeFactors ∪ (fwA q r).primeFactors :=
        Nat.primeFactors_mul hgg hA
    _ = (q.gcd r).primeFactors ∪ (fwA q r).primeFactors := by
        rw [Nat.primeFactors_mul hg0 hg0]
        simp


/-- `fwPr = pf(g) ∖ pf(A)` (membership version). -/
private lemma fw_pf_fwPr (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    fwPr q r = (q.gcd r).primeFactors \ (fwA q r).primeFactors := by
  classical
  have hA : (fwA q r) ≠ 0 := ne_of_gt (fwA_pos q r hq hr)
  ext p
  constructor
  · intro hp
    have hpfw := (fwPr_mem_iff q r p).mp hp
    rw [Finset.mem_sdiff]
    constructor
    · exact hpfw.1
    · intro hpA
      exact hpfw.2 (Nat.mem_primeFactors.mp hpA).2.1
  · intro hp
    rw [Finset.mem_sdiff] at hp
    have hpg := hp.1
    have hpP : p.Prime := (Nat.mem_primeFactors.mp hpg).1
    rw [fwPr_mem_iff]
    constructor
    · exact hpg
    · intro hpd
      exact hp.2 (Nat.mem_primeFactors.mpr ⟨hpP, hpd, hA⟩)

/-- `pf(q·r) = pf(A) ∪ fwPr`, disjoint. -/
private lemma fw_pf_split (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    (q * r).primeFactors = (fwA q r).primeFactors ∪ fwPr q r := by
  classical
  have hgA := fw_pf_gA q r hq hr
  have hfw := fw_pf_fwPr q r hq hr
  calc
    (q * r).primeFactors = (q.gcd r).primeFactors ∪ (fwA q r).primeFactors := hgA
    _ = (q.gcd r).primeFactors \ (fwA q r).primeFactors ∪ (fwA q r).primeFactors := by
            rw [Finset.sdiff_union_self_eq_union]
    _ = (fwA q r).primeFactors ∪ ((q.gcd r).primeFactors \ (fwA q r).primeFactors) := by
            rw [Finset.union_comm]
    _ = (fwA q r).primeFactors ∪ fwPr q r := by rw [← hfw]

/-- disjointness of `pf(A)` and `fwPr`. -/
private lemma fw_pf_A_disjoint_fwPr (q r : ℕ) :
    Disjoint (fwA q r).primeFactors (fwPr q r) := by
  classical
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb hab
  have haA : a ∣ fwA q r := (Nat.mem_primeFactors.mp ha).2.1
  have hbfw := (fwPr_mem_iff q r b).mp hb
  have hbnd : ¬ b ∣ fwA q r := hbfw.2
  have hbA : b ∣ fwA q r := by rwa [hab] at haA
  exact hbnd hbA


/-- Euler product `φ(n)/n = ∏_{p|n}(1 − 1/p)` over the reals, `n ≠ 0`. -/
private lemma fw_phi_ratio_prod (n : ℕ) (hn : n ≠ 0) :
    ((Nat.totient n : ℝ) / (n : ℝ)) = ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hq : (Nat.totient n : ℚ) / (n : ℚ) = ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) := by
    rw [Nat.totient_eq_mul_prod_factors]
    field_simp [hnQ]
  calc
    (Nat.totient n : ℝ) / (n : ℝ) = (((Nat.totient n : ℚ) / (n : ℚ) : ℚ) : ℝ) := by
      norm_num [Rat.cast_div]
    _ = ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
      have hc := congrArg (fun q : ℚ => (q : ℝ)) hq
      simpa [Rat.cast_div] using hc
    _ = ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
      refine Finset.prod_congr rfl ?_
      intro p hp
      rw [one_div]

/-- arithmetic step: `φ(q)φ(r)/L = φ(qr)·φ(g)/(qr)`. -/
private lemma fw_coeff_arith (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    (q.totient : ℝ) * (r.totient : ℝ) / ((q * r / (q.gcd r) : ℕ) : ℝ) =
      ((q * r).totient : ℝ) * ((q.gcd r).totient : ℝ) / ((q * r : ℕ) : ℝ) := by
  classical
  have hg0 : (q.gcd r : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (fw_gcd_pos_of_q q r hq))
  have hL0 : ((q * r / (q.gcd r) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (fw_L_pos q r hq hr))
  have hqr0 : ((q * r : ℕ) : ℝ) ≠ 0 := by positivity
  have htm : (q.totient : ℝ) * (r.totient : ℝ) * (q.gcd r : ℝ) =
      ((q * r).totient : ℝ) * ((q.gcd r).totient : ℝ) := by
    have h' : (q * r).totient * (q.gcd r).totient =
        q.totient * r.totient * (q.gcd r) :=
      Commons.NumberTheory.Totient.totient_mul_gcd q r
    apply_fun (fun n : ℕ => (n : ℝ)) at h'
    simpa [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using h'.symm
  have hcross : (q.totient : ℝ) * (r.totient : ℝ) * ((q * r : ℕ) : ℝ) =
      ((q * r).totient : ℝ) * ((q.gcd r).totient : ℝ) * ((q * r / (q.gcd r) : ℕ) : ℝ) := by
    have hLg : ((q * r : ℕ) : ℝ) = (q.gcd r : ℝ) * ((q * r / (q.gcd r) : ℕ) : ℝ) := by
      have hd : q.gcd r ∣ q * r := dvd_trans (Nat.gcd_dvd_left q r) (dvd_mul_right q r)
      have hn : (q.gcd r) * (q * r / (q.gcd r)) = q * r := Nat.mul_div_cancel' hd
      have hc : (q.gcd r : ℝ) * ((q * r / (q.gcd r) : ℕ) : ℝ) = ((q * r : ℕ) : ℝ) := by
        exact_mod_cast hn
      exact hc.symm
    calc
      (q.totient : ℝ) * (r.totient : ℝ) * ((q * r : ℕ) : ℝ)
          = (q.totient : ℝ) * (r.totient : ℝ) *
              ((q.gcd r : ℝ) * ((q * r / (q.gcd r) : ℕ) : ℝ)) := by
              rw [hLg]
          _ = ((q.totient : ℝ) * (r.totient : ℝ) * (q.gcd r : ℝ)) *
                ((q * r / (q.gcd r) : ℕ) : ℝ) := by ring
          _ = (((q * r).totient : ℝ) * ((q.gcd r).totient : ℝ)) *
                ((q * r / (q.gcd r) : ℕ) : ℝ) := by rw [htm]
          _ = ((q * r).totient : ℝ) * ((q.gcd r).totient : ℝ) *
                ((q * r / (q.gcd r) : ℕ) : ℝ) := by ring
  field_simp [hL0, hqr0]
  rw [hcross]
  ring

/-- the product over `p | qr` splits into the product over `p | A` and over `fwPr`. -/
private lemma fw_euler_split (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    (∏ p ∈ (q * r).primeFactors, (1 - (1 : ℝ) / (p : ℝ))) =
      (∏ p ∈ (fwA q r).primeFactors, (1 - (1 : ℝ) / (p : ℝ))) *
        (∏ p ∈ fwPr q r, (1 - (1 : ℝ) / (p : ℝ))) := by
  classical
  rw [fw_pf_split q r hq hr]
  rw [Finset.prod_union (fw_pf_A_disjoint_fwPr q r)]

/-- per-prime: `(p−1)/p = 1 − 1/p`. -/
private lemma fw_pm1_div_p_eq (p : ℕ) (hp0 : (p : ℝ) ≠ 0) :
    ((p : ℝ) - 1) / (p : ℝ) = 1 - (1 : ℝ) / (p : ℝ) := by
  field_simp [hp0]


private lemma fw_sub_mod_imp (x y t L : ℕ) (hL : 0 < L) (hx : x < L) (hy : y < L) (ht : t < L) :
    ((x + L - y) % L = t) → (x % L = (y + t) % L) := by
  intro h
  by_cases hxy : y ≤ x
  · have hsub : x + L - y = L + (x - y) := by omega
    rw [hsub] at h
    rw [Nat.add_mod, Nat.mod_self] at h
    simp at h
    have hxyL : x - y < L := by omega
    rw [Nat.mod_eq_of_lt hxyL] at h
    have hxmod : x % L = x := Nat.mod_eq_of_lt hx
    have hytL : (y + t) < L := by rw [← h]; omega
    have hyt : (y + t) % L = y + t := Nat.mod_eq_of_lt hytL
    rw [hxmod, hyt]
    omega
  · have hxy' : x < y := lt_of_not_ge hxy
    have hsub : x + L - y < L := by omega
    rw [Nat.mod_eq_of_lt hsub] at h
    have hye : y + t = x + L := by omega
    have hxmod : x % L = x := Nat.mod_eq_of_lt hx
    rw [hxmod]
    apply Eq.symm
    calc
      (y + t) % L = (x + L) % L := by rw [hye]
      _ = x % L := by simp [Nat.add_mod]
      _ = x := hxmod


/-- `a ≡ b [MOD q]` with `b ≤ a` implies `q | a − b`. -/
private lemma fw_modEq_dvd_sub {a b q : ℕ} (h : a ≡ b [MOD q]) (hb : b ≤ a) : q ∣ a - b := by
  have hsub := Nat.ModEq.sub (c := b) (d := b) hb (le_rfl : b ≤ b) h (Nat.ModEq.refl b)
  have hz : b - b = 0 := Nat.sub_self b
  rw [hz] at hsub
  exact Nat.modEq_zero_iff_dvd.mp hsub

/-- `a ≡ b [MOD q]` with `a ≤ b` implies `q | b − a`. -/
private lemma fw_modEq_dvd_sub' {a b q : ℕ} (h : a ≡ b [MOD q]) (ha : a ≤ b) : q ∣ b - a := by
  apply fw_modEq_dvd_sub (a := b) (b := a) (q := q) ?_ ha
  exact h.symm

/-- `(c·x) % (c·m) = c·(x % m)` — reduction of a scaled modulus. -/
private lemma fw_mul_mod_left (m c x : ℕ) : (c * x) % (c * m) = c * (x % m) := by
  by_cases hm : m = 0
  · subst m; simp
  · by_cases hc : c = 0
    · subst c; simp
    · have hposc : 0 < c := Nat.pos_of_ne_zero hc
      have hposm : 0 < m := Nat.pos_of_ne_zero hm
      have hdiv : x = m * (x / m) + x % m := (Nat.div_add_mod x m).symm
      have hxeq : c * x = (x / m) * (c * m) + c * (x % m) := by
        calc
          c * x = c * (m * (x / m) + x % m) := congrArg (fun z : ℕ => c * z) hdiv
          _ = (x / m) * (c * m) + c * (x % m) := by ring
      have hcr : c * (x % m) < c * m := Nat.mul_lt_mul_of_pos_left (Nat.mod_lt x hposm) hposc
      calc
        (c * x) % (c * m) = ((x / m) * (c * m) + c * (x % m)) % (c * m) := by rw [hxeq]
        _ = (c * (x % m)) % (c * m) := by
              have hdvd : (c * m) ∣ (x / m) * (c * m) := ⟨x / m, by ring⟩
              have hz : ((x / m) * (c * m)) % (c * m) = 0 := Nat.mod_eq_zero_of_dvd hdvd
              rw [Nat.add_mod, hz]
              simp
        _ = c * (x % m) := by rw [Nat.mod_eq_of_lt hcr]

/-- multiplying a congruence by `c` enlarges the modulus by `c`. -/
private lemma fw_mul_lift_modEq (m c x y : ℕ) (h : x ≡ y [MOD m]) :
    c * x ≡ c * y [MOD c * m] := by
  have hx : (c * x) % (c * m) = c * (x % m) := fw_mul_mod_left m c x
  have hy : (c * y) % (c * m) = c * (y % m) := fw_mul_mod_left m c y
  change (c * x) % (c * m) = (c * y) % (c * m)
  rw [hx, hy]
  exact congrArg (fun z : ℕ => c * z) h


/-- Branch 2 of the fibre parametrization (`t ≤ a0·R`): with
`s = (a0·R − t)/Q` and `b(y) = (s + R·y) % (g·R)`, we have
`(b(y)·Q + t) ≡ a(y)·R (mod gQR)` where `a(y) = a0 + Q·y`. -/
private lemma fw_branch2 (g Q R a0 t y : ℕ) (hQ : 0 < Q) (hR : 0 < R)
    (htle : t ≤ a0 * R) (hdiv : Q ∣ a0 * R - t) (hy : y < g) (ha0 : a0 < Q) :
    let L : ℕ := g * Q * R
    let s : ℕ := (a0 * R - t) / Q
    let bv : ℕ := (s + R * y) % (g * R)
    (bv * Q + t) % L = (a0 + Q * y) * R := by
  classical
  intro L s bv
  have hg : 1 ≤ g := by omega
  have hL : 0 < L := by
    dsimp [L]
    positivity
  have hs : s * Q = a0 * R - t := by
    dsimp [s]
    exact Nat.div_mul_cancel hdiv
  have ha0lt : a0 + Q * y < Q * g := by
    have hy1 : y + 1 ≤ g := by omega
    calc
      a0 + Q * y < Q + Q * y := Nat.add_lt_add_right ha0 (Q * y)
      _ = Q * (y + 1) := by ring
      _ ≤ Q * g := Nat.mul_le_mul_left Q hy1
  have haRlt : (a0 + Q * y) * R < L := by
    dsimp [L]
    rw [show g * Q * R = Q * g * R by ring]
    exact Nat.mul_lt_mul_of_pos_right ha0lt hR
  have hx : s + R * y ≡ bv [MOD g * R] := by
    dsimp [bv]
    exact ((Nat.mod_modEq (s + R * y) (g * R)).symm)
  have hlift : Q * (s + R * y) ≡ Q * bv [MOD g * Q * R] := by
    have h1 := fw_mul_lift_modEq (g * R) Q (s + R * y) bv hx
    -- h1 : Q·(s+Ry) ≡ Q·by [MOD Q·(g·R)]; convert modulus to g·Q·R
    simpa [mul_assoc, mul_comm, mul_left_comm] using h1
  -- a(y)·R = (a0 + Q·y)·R
  have heq : Q * (s + R * y) + t = (a0 + Q * y) * R := by
    calc
      Q * (s + R * y) + t = (Q * s + Q * (R * y)) + t := by ring
      _ = (s * Q + Q * (R * y)) + t := by ring
      _ = ((a0 * R - t) + Q * (R * y)) + t := by rw [hs]
      _ = a0 * R + Q * (R * y) := by
            have hswap : ((a0 * R - t) + Q * (R * y)) + t = ((a0 * R - t) + t) + Q * (R * y) := by ring
            rw [hswap, Nat.sub_add_cancel htle]
      _ = (a0 + Q * y) * R := by ring
  have hmain : Q * bv + t ≡ (a0 + Q * y) * R [MOD L] := by
    -- chain: Q·by + t ≡ Q·(s+Ry) + t = heq
    have hc1 : Q * bv + t ≡ Q * (s + R * y) + t [MOD L] := by
      apply Nat.ModEq.add
      · -- Q·by ≡ Q·(s+Ry) mod L: from hlift (Q·(s+Ry) ≡ Q·by): symm
        exact hlift.symm
      · exact Nat.ModEq.refl t
    rw [heq] at hc1
    dsimp [L] at hc1 ⊢
    exact hc1
  -- convert the congruence to a `%`-equality and reduce the right-hand side
  change (bv * Q + t) % L = (a0 + Q * y) * R
  have hEq0 : (Q * bv + t) % L = ((a0 + Q * y) * R) % L := hmain
  have hEq1 : (Q * bv + t) % L = (a0 + Q * y) * R := by
    rw [Nat.mod_eq_of_lt haRlt] at hEq0
    exact hEq0
  simpa [mul_comm, mul_left_comm, mul_assoc] using hEq1


/-- adding a full multiple of the modulus leaves the residue unchanged. -/
private lemma fw_add_modEq_self (L X : ℕ) : (L + X) ≡ X [MOD L] := by
  change (L + X) % L = X % L
  rw [Nat.add_mod, Nat.mod_self]
  simp

/-- Branch 1 of the fibre parametrization (`a0·R ≤ t`): with `u = (t − a0·R)/Q`,
`w = g·R − u` and `b(y) = (R·y + w) % (g·R)`, we have
`(b(y)·Q + t) ≡ a(y)·R (mod gQR)` where `a(y) = a0 + Q·y`. -/
private lemma fw_branch1 (g Q R a0 t y : ℕ) (hQ : 0 < Q) (hR : 0 < R)
    (ht : t < g * Q * R) (htle : a0 * R ≤ t) (hdiv : Q ∣ t - a0 * R) (hy : y < g) (ha0 : a0 < Q) :
    let L : ℕ := g * Q * R
    let u : ℕ := (t - a0 * R) / Q
    let w : ℕ := g * R - u
    let bv : ℕ := (R * y + w) % (g * R)
    (bv * Q + t) % L = (a0 + Q * y) * R := by
  classical
  intro L u w bv
  have hu : u * Q = t - a0 * R := by
    dsimp [u]
    exact Nat.div_mul_cancel hdiv
  have huQ : Q * u = t - a0 * R := by rw [mul_comm]; exact hu
  have hwle : u ≤ g * R := by
    have hsub : t - a0 * R < g * Q * R := by omega
    dsimp [u]
    have hconv : (t - a0 * R) / Q < g * R := by
      have hEq : g * Q * R = (g * R) * Q := by ring
      have h' : t - a0 * R < (g * R) * Q := by rwa [hEq] at hsub
      exact (Nat.div_lt_iff_lt_mul hQ).mpr h'
    exact le_of_lt hconv
  have hQw : Q * w = g * Q * R - (t - a0 * R) := by
    dsimp [w]
    calc
      Q * (g * R - u) = Q * (g * R) - Q * u := Nat.mul_sub_left_distrib Q (g * R) u
      _ = g * Q * R - Q * u := by ring
      _ = g * Q * R - (t - a0 * R) := by rw [huQ]
  have hQwT : Q * w + t = g * Q * R + a0 * R := by
    have hYt : (t - a0 * R) ≤ t := Nat.sub_le t (a0 * R)
    have hYX : (t - a0 * R) ≤ g * Q * R := by omega
    have hXsub : (g * Q * R - (t - a0 * R)) + t = g * Q * R + (t - (t - a0 * R)) := by omega
    have hsubsub : t - (t - a0 * R) = a0 * R := Nat.sub_sub_self htle
    calc
      Q * w + t = (g * Q * R - (t - a0 * R)) + t := by rw [hQw]
      _ = g * Q * R + (t - (t - a0 * R)) := hXsub
      _ = g * Q * R + a0 * R := by rw [hsubsub]
  have ha0lt : a0 + Q * y < Q * g := by
    have hy1 : y + 1 ≤ g := by omega
    calc
      a0 + Q * y < Q + Q * y := Nat.add_lt_add_right ha0 (Q * y)
      _ = Q * (y + 1) := by ring
      _ ≤ Q * g := Nat.mul_le_mul_left Q hy1
  have haRlt : (a0 + Q * y) * R < L := by
    dsimp [L]
    rw [show g * Q * R = Q * g * R by ring]
    exact Nat.mul_lt_mul_of_pos_right ha0lt hR
  have hbv : R * y + w ≡ bv [MOD g * R] := by
    dsimp [bv]
    exact ((Nat.mod_modEq (R * y + w) (g * R)).symm)
  have hlift : Q * (R * y + w) ≡ Q * bv [MOD g * Q * R] := by
    have h1 := fw_mul_lift_modEq (g * R) Q (R * y + w) bv hbv
    simpa [mul_assoc, mul_comm, mul_left_comm] using h1
  have hsum : Q * (R * y + w) + t = (g * Q * R) + (a0 + Q * y) * R := by
    calc
      Q * (R * y + w) + t = (Q * (R * y) + Q * w) + t := by ring
      _ = Q * (R * y) + (Q * w + t) := by ring
      _ = Q * (R * y) + (g * Q * R + a0 * R) := by rw [hQwT]
      _ = g * Q * R + (a0 + Q * y) * R := by ring
  have h2 : Q * (R * y + w) + t ≡ (a0 + Q * y) * R [MOD L] := by
    have he : Q * (R * y + w) + t ≡ (g * Q * R) + (a0 + Q * y) * R [MOD L] := by
      rw [hsum]
    have hladd : (g * Q * R) + (a0 + Q * y) * R ≡ (a0 + Q * y) * R [MOD L] := by
      dsimp [L]
      exact fw_add_modEq_self (g * Q * R) ((a0 + Q * y) * R)
    exact he.trans hladd
  have hmain : Q * bv + t ≡ (a0 + Q * y) * R [MOD L] := by
    have hc1 : Q * bv + t ≡ Q * (R * y + w) + t [MOD L] := by
      apply Nat.ModEq.add
      · exact hlift.symm
      · exact Nat.ModEq.refl t
    exact hc1.trans h2
  change (bv * Q + t) % L = (a0 + Q * y) * R
  have hEq0 : (Q * bv + t) % L = ((a0 + Q * y) * R) % L := hmain
  have hEq1 : (Q * bv + t) % L = (a0 + Q * y) * R := by
    rw [Nat.mod_eq_of_lt haRlt] at hEq0
    exact hEq0
  simpa [mul_comm, mul_left_comm, mul_assoc] using hEq1


/-- a residue `x < L` equal to `t` modulo `L` is actually `t`. -/
private lemma fw_mod_eq_of_modEq_lt {x t L : ℕ} (h : x ≡ t [MOD L]) (hx : x < L) (ht : t < L) :
    x = t := Nat.ModEq.eq_of_lt_of_lt h hx ht


/-- from `a0·R ≡ t [MOD Q]` and `a0·R ≤ t`: `Q | t − a0·R`. -/
private lemma fw_a0_dvd_sub {Q a0 R t : ℕ} (hc : a0 * R ≡ t [MOD Q]) (hle : a0 * R ≤ t) :
    Q ∣ t - a0 * R := by
  have hs : t ≡ a0 * R [MOD Q] := hc.symm
  have hsub := Nat.ModEq.sub (c := a0 * R) (d := a0 * R) hle (le_rfl : a0 * R ≤ a0 * R) hs
    (Nat.ModEq.refl (a0 * R))
  have hz : a0 * R - a0 * R = 0 := Nat.sub_self (a0 * R)
  rw [hz] at hsub
  exact Nat.modEq_zero_iff_dvd.mp hsub

/-- from `a0·R ≡ t [MOD Q]` and `t ≤ a0·R`: `Q | a0·R − t`. -/
private lemma fw_a0_dvd_sub' {Q a0 R t : ℕ} (hc : a0 * R ≡ t [MOD Q]) (hle : t ≤ a0 * R) :
    Q ∣ a0 * R - t := by
  have hsub := Nat.ModEq.sub (c := t) (d := t) hle (le_rfl : t ≤ t) hc (Nat.ModEq.refl t)
  have hz : t - t = 0 := Nat.sub_self t
  rw [hz] at hsub
  exact Nat.modEq_zero_iff_dvd.mp hsub


/-- `gcd(x + Q·y, Q) = gcd(x, Q)` — the `Q`-part is translation invariant. -/
private lemma fw_gcd_add_mul (x Q y : ℕ) : (x + Q * y).gcd Q = x.gcd Q := by
  have hmod : (x + Q * y) % Q = x % Q := by
    rw [Nat.add_mod, Nat.mul_mod]
    simp
  calc
    (x + Q * y).gcd Q = Q.gcd (x + Q * y) := Nat.gcd_comm (x + Q * y) Q
    _ = ((x + Q * y) % Q).gcd Q := Nat.gcd_rec Q (x + Q * y)
    _ = (x % Q).gcd Q := by rw [hmod]
    _ = Q.gcd x := (Nat.gcd_rec Q x).symm
    _ = x.gcd Q := Nat.gcd_comm Q x

/-- if `t ⊥ Q` and `a0·R ≡ t [MOD Q]` then `a0 ⊥ Q`. -/
private lemma fw_coprime_of_modEq_mul {Q a0 R t : ℕ} (htQ : Nat.Coprime t Q)
    (hc : a0 * R ≡ t [MOD Q]) : Nat.Coprime a0 Q := by
  rw [Nat.Coprime]
  by_contra hne
  rcases Nat.exists_prime_and_dvd (n := a0.gcd Q) hne with ⟨p, hpP, hpd⟩
  have hpa : p ∣ a0 := dvd_trans hpd (Nat.gcd_dvd_left _ _)
  have hpq : p ∣ Q := dvd_trans hpd (Nat.gcd_dvd_right _ _)
  have hm : (a0 * R) % p = t % p := by
    have hred1 : (a0 * R) % Q % p = (a0 * R) % p := Nat.mod_mod_of_dvd (a0 * R) hpq
    have hred2 : t % Q % p = t % p := Nat.mod_mod_of_dvd t hpq
    have hc' : (a0 * R) % Q % p = t % Q % p := congrArg (fun z : ℕ => z % p) hc
    rwa [hred1, hred2] at hc'
  have hpaR : p ∣ a0 * R := dvd_trans hpa (dvd_mul_right a0 R)
  have hz : (a0 * R) % p = 0 := Nat.mod_eq_zero_of_dvd hpaR
  have htmp : t % p = 0 := by
    rw [hz] at hm
    exact hm.symm
  have hpt : p ∣ t := (Nat.dvd_iff_mod_eq_zero).mpr htmp
  have hg : t.gcd Q = 1 := htQ
  have hpdvdg : p ∣ t.gcd Q := Nat.dvd_gcd hpt hpq
  exact hpP.not_dvd_one (by simpa [hg] using hpdvdg)


/-- `gcd(x, g)` depends only on `x % g`. -/
private lemma fw_gcd_mod_eq_gcd (x g : ℕ) : x.gcd g = (x % g).gcd g := by
  calc
    x.gcd g = g.gcd x := Nat.gcd_comm x g
    _ = (x % g).gcd g := Nat.gcd_rec g x

/-- `gcd(x, g)` depends only on `x % (g·R)` (since `g | g·R`). -/
private lemma fw_gcd_mod_mul (x g R : ℕ) : x.gcd g = (x % (g * R)).gcd g := by
  have hr : (x % (g * R)) % g = x % g := Nat.mod_mod_of_dvd x (dvd_mul_right g R)
  calc
    x.gcd g = (x % g).gcd g := fw_gcd_mod_eq_gcd x g
    _ = ((x % (g * R)) % g).gcd g := by rw [← hr]
    _ = (x % (g * R)).gcd g := (fw_gcd_mod_eq_gcd (x % (g * R)) g).symm


/-- canonical representative of the `t`-class modulo `Q` along the unit `R`. -/
private lemma fw_exists_a0 (Q R t : ℕ) (hQ : 1 ≤ Q) (hcopR : Nat.Coprime R Q) :
    ∃ a0 : ℕ, a0 < Q ∧ a0 * R ≡ t [MOD Q] := by
  have h := Commons.Data.Nat.exists_canonical_congruence_solution Q R t hQ hcopR
  rcases h with ⟨a0, h1, h2, hcong⟩
  refine ⟨a0 % Q, Nat.mod_lt a0 (by omega), ?_⟩
  have hm : a0 % Q ≡ a0 [MOD Q] := Nat.mod_modEq a0 Q
  exact hm.mul_right R |>.trans hcong

/-- multiplication by `Q` is injective on `{b < g·R}` modulo `g·Q·R`. -/
private lemma fw_Q_mul_injective (Q R g b b' : ℕ) (hQ : 0 < Q) (hb : b < g * R)
    (hb' : b' < g * R) : (Q * b) % (g * Q * R) = (Q * b') % (g * Q * R) → b = b' := by
  intro h
  have h1 : Q * b < g * Q * R := by
    calc
      Q * b < Q * (g * R) := Nat.mul_lt_mul_of_pos_left hb hQ
      _ = g * Q * R := by ring
  have h2 : Q * b' < g * Q * R := by
    calc
      Q * b' < Q * (g * R) := Nat.mul_lt_mul_of_pos_left hb' hQ
      _ = g * Q * R := by ring
  have hb1 : (Q * b) % (g * Q * R) = Q * b := Nat.mod_eq_of_lt h1
  have hb2 : (Q * b') % (g * Q * R) = Q * b' := Nat.mod_eq_of_lt h2
  have heq : Q * b = Q * b' := by rwa [hb1, hb2] at h
  exact Nat.mul_left_cancel hQ heq


/-- reverse: `x ≡ y+t (mod L)` implies the wrapped value `t`. -/
private lemma fw_sub_mod_rev (x y t L : ℕ) (hL : 0 < L) (hx : x < L) (hy : y < L) (ht : t < L) :
    (x % L = (y + t) % L) → ((x + L - y) % L = t) := by
  intro h
  have hxmod : x % L = x := Nat.mod_eq_of_lt hx
  by_cases hxy : y ≤ x
  · have hytL : y + t < L := by
      by_contra hnot
      have hge : L ≤ y + t := by omega
      have h1 : y + t - L < L := by omega
      have hd : (y + t) = L + (y + t - L) := by omega
      have hytm : (y + t) % L = y + t - L := by
        rw [hd]
        rw [Nat.add_mod, Nat.mod_self]
        simp
        exact Nat.mod_eq_of_lt h1
      rw [hxmod, hytm] at h
      omega
    have hyt : (y + t) % L = y + t := Nat.mod_eq_of_lt hytL
    rw [hxmod, hyt] at h
    have hsub : x + L - y = L + t := by omega
    rw [hsub]
    have hLt : (L + t) % L = t % L := by
      rw [Nat.add_mod, Nat.mod_self]
      simp
    rw [hLt]
    exact Nat.mod_eq_of_lt ht
  · have hxy' : x < y := lt_of_not_ge hxy
    have hge : L ≤ y + t := by
      by_contra hnot
      have hlt : y + t < L := by omega
      have hyt : (y + t) % L = y + t := Nat.mod_eq_of_lt hlt
      rw [hxmod, hyt] at h
      omega
    have h1 : y + t - L < L := by omega
    have hd : (y + t) = L + (y + t - L) := by omega
    have hytm : (y + t) % L = y + t - L := by
      rw [hd]
      rw [Nat.add_mod, Nat.mod_self]
      simp
      exact Nat.mod_eq_of_lt h1
    rw [hxmod, hytm] at h
    have hsub : x + L - y = t := by omega
    rw [hsub]
    exact Nat.mod_eq_of_lt ht

/-- `(x+L−y) mod L = t` iff `x ≡ y+t (mod L)` for `x,y,t < L`. -/
private lemma fw_sub_mod_iff (x y t L : ℕ) (hL : 0 < L) (hx : x < L) (hy : y < L) (ht : t < L) :
    ((x + L - y) % L = t) ↔ (x % L = (y + t) % L) := by
  constructor
  · exact fw_sub_mod_imp x y t L hL hx hy ht
  · exact fw_sub_mod_rev x y t L hL hx hy ht

/-- the window value `((aR)%L + L − (bQ)%L)%L` equals `t` iff `aR ≡ bQ + t (mod L)`. -/
private lemma fw_val_eq_congr_iff (a b Rr Q L t : ℕ) (hL : 0 < L) (h1 : a * Rr < L)
    (h2 : b * Q < L) (ht : t < L) :
    (((a * Rr) % L + L - (b * Q) % L) % L = t) ↔ ((a * Rr) % L = ((b * Q + t) % L)) := by
  let x : ℕ := (a * Rr) % L
  let y : ℕ := (b * Q) % L
  have hyt : (((b * Q) % L + t) % L) = ((b * Q + t) % L) := by
    have htm : t % L = t := Nat.mod_eq_of_lt ht
    calc
      ((b * Q) % L + t) % L = ((b * Q) % L + t % L) % L := by rw [htm]
      _ = (b * Q + t) % L := by exact (Nat.add_mod (b * Q) t L).symm
  constructor
  · intro hv
    have h := fw_sub_mod_imp x y t L hL
      (by dsimp [x]; exact Nat.mod_lt (a * Rr) hL)
      (by dsimp [y]; exact Nat.mod_lt (b * Q) hL) ht hv
    simpa [x, y, Nat.mod_mod, hyt] using h
  · intro hc
    have h := fw_sub_mod_rev x y t L hL
      (by dsimp [x]; exact Nat.mod_lt (a * Rr) hL)
      (by dsimp [y]; exact Nat.mod_lt (b * Q) hL) ht
    -- need x % L = (y + t) % L from hc: (a·Rr)%L = (b·Q+t)%L
    have h' : x % L = (y + t) % L := by
      dsimp [x, y]
      rw [hyt]
      simpa [Nat.mod_mod] using hc
    -- h' : x%L = (y+t)%L: apply reverse then rewrite x,y back? The goal is ((a·Rr)%L + L − (b·Q)%L)%L = t:
    have h2' := h h'
    -- h2' : (x + L − y) % L = t
    simpa [x, y] using h2'


/-! ## Fibre identity: exact count via the residue formula -/

/-- `residue_fiber_formula` applied to our parameters, fully unfolded. -/
private lemma fw_residue (q r t : ℕ) (hq : 0 < q) (hr : 0 < r) :
    ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
          ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
        (fun ab : ℕ × ℕ =>
          ((ab.1 * (r / (q.gcd r))) % (q * r / (q.gcd r)) =
            ((ab.2 * (q / (q.gcd r)) + t) % (q * r / (q.gcd r)))))).card) : ℕ) =
    (if t.gcd ((q / (q.gcd r)) * (r / (q.gcd r))) = 1 then
      (∏ p ∈ ((q / (q.gcd r)) * (r / (q.gcd r))).primeFactors,
        (p ^ ((q.gcd r).factorization p)).totient) *
      (∏ p ∈ (∏ p ∈ ((q.gcd r).primeFactors).filter (fun p : ℕ => ¬ p ∣ (q / (q.gcd r)) * (r / (q.gcd r))),
              p ^ ((q.gcd r).factorization p)).primeFactors,
        if p ∣ t % (q * r / (q.gcd r)) then
          (p ^ ((∏ p ∈ ((q.gcd r).primeFactors).filter (fun p : ℕ => ¬ p ∣ (q / (q.gcd r)) * (r / (q.gcd r))),
              p ^ ((q.gcd r).factorization p)).factorization p)).totient
        else p ^ ((∏ p ∈ ((q.gcd r).primeFactors).filter (fun p : ℕ => ¬ p ∣ (q / (q.gcd r)) * (r / (q.gcd r))),
              p ^ ((q.gcd r).factorization p)).factorization p - 1) * (p - 2))
    else 0) := by
  simpa using (Commons.NumberTheory.DuffinSchaeffer.residue_fiber_formula q r t hq hr)

/-- `fwFib q r t` counts the reduced pairs satisfying the residue congruence. -/
private lemma fw_fib_eq_rf (q r t : ℕ) (hq : 0 < q) (hr : 0 < r) (ht : t < q * r / (q.gcd r)) :
    fwFib q r t = ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
          ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
        (fun ab : ℕ × ℕ =>
          ((ab.1 * (r / (q.gcd r))) % (q * r / (q.gcd r)) =
            ((ab.2 * (q / (q.gcd r)) + t) % (q * r / (q.gcd r)))))).card) : ℕ) := by
  classical
  unfold fwFib
  dsimp [fwPQ]
  congr 1
  apply Finset.filter_congr
  intro mn hmn
  have hL : 0 < q * r / (q.gcd r) := fw_L_pos q r hq hr
  have hmem := Finset.mem_product.mp hmn
  have hmq : mn.1 < q := (Finset.mem_range.mp (Finset.mem_filter.mp hmem.1).1)
  have hnr : mn.2 < r := (Finset.mem_range.mp (Finset.mem_filter.mp hmem.2).1)
  have h1 : mn.1 * (r / (q.gcd r)) < q * r / (q.gcd r) := fw_mRr_lt_L q r mn.1 hq hr hmq
  have h2 : mn.2 * (q / (q.gcd r)) < q * r / (q.gcd r) := fw_nQ_lt_L q r mn.2 hq hr hnr
  change ((fwVal q r mn) = t) ↔
      ((mn.1 * (r / (q.gcd r))) % (q * r / (q.gcd r)) =
        ((mn.2 * (q / (q.gcd r)) + t) % (q * r / (q.gcd r))))
  exact fw_val_eq_congr_iff mn.1 mn.2 (r / (q.gcd r)) (q / (q.gcd r)) (q * r / (q.gcd r)) t hL h1 h2 ht

/-- `K = ∏_{p∈fwPr} p^{v_p(g)}`: the "equal-exponent" part of `g`. -/
private noncomputable def fwK (q r : ℕ) : ℕ :=
  ∏ p ∈ fwPr q r, p ^ ((q.gcd r).factorization p)

/-- the prime factors of `fwK` are exactly `fwPr`. -/
private lemma fw_pfK_eq_F (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    (fwK q r).primeFactors = fwPr q r := by
  classical
  change ((∏ p ∈ (Nat.primeFactors (q.gcd r)).filter (fun p => ¬ p ∣ (q / (q.gcd r)) * (r / (q.gcd r))),
        p ^ ((q.gcd r).factorization p)).primeFactors) =
      (Nat.primeFactors (q.gcd r)).filter (fun p => ¬ p ∣ (q / (q.gcd r)) * (r / (q.gcd r)))
  exact Commons.NumberTheory.DuffinSchaeffer.rf_pfK_eq_F q r hq.ne' hr.ne'

/-- at `p ∈ fwPr`, the `fwK`-factorization equals the `g`-factorization. -/
private lemma fw_K_fact (q r p : ℕ) (hq : 0 < q) (hr : 0 < r) (hpF : p ∈ fwPr q r) :
    (fwK q r).factorization p = (q.gcd r).factorization p := by
  classical
  have hprim : ∀ x ∈ fwPr q r, x.Prime := by
    intro x hx
    exact (fwPr_prime_dvd_g q r x hx).1
  have hf := Commons.Data.Nat.factorization_prod_prime_pow_apply (fwPr q r)
    (fun x => (q.gcd r).factorization x) hprim p
  dsimp [fwK]
  rw [if_pos hpF] at hf
  exact hf

/-- `g.factorization p ≥ 1` for `p ∈ pf(g)`. -/
private lemma fw_g_fact_pos (q r p : ℕ) (hq : 0 < q) (hp : p ∈ (q.gcd r).primeFactors) :
    0 < (q.gcd r).factorization p := by
  have hpd : p ∣ q.gcd r := (Nat.mem_primeFactors.mp hp).2.1
  have hg : q.gcd r ≠ 0 := (fw_gcd_pos_of_q q r hq).ne'
  exact Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hg hpd

/-- the product over `K.primeFactors` in the residue formula equals a product over `fwPr`. -/
private lemma fw_S_form (q r x : ℕ) (hq : 0 < q) (hr : 0 < r) :
    (∏ p ∈ (fwK q r).primeFactors,
        if p ∣ x then (p ^ ((fwK q r).factorization p)).totient
        else p ^ ((fwK q r).factorization p - 1) * (p - 2)) =
    (∏ p ∈ fwPr q r,
        if p ∣ x then (p ^ ((q.gcd r).factorization p)).totient
        else p ^ ((q.gcd r).factorization p - 1) * (p - 2)) := by
  classical
  rw [fw_pfK_eq_F q r hq hr]
  refine Finset.prod_congr rfl ?_
  intro p hp
  have hf := fw_K_fact q r p hq hr hp
  by_cases hpx : p ∣ x
  · simp [hpx, hf]
  · simp [hpx, hf]

/-- the fibre count at value `t` (`t < L`): exact product formula in the coprime case. -/
private lemma fw_fib_residue_form (q r t : ℕ) (hq : 0 < q) (hr : 0 < r)
    (ht : t < q * r / (q.gcd r)) :
    fwFib q r t = (if t.gcd (fwA q r) = 1 then
      (∏ p ∈ (fwA q r).primeFactors, (p ^ ((q.gcd r).factorization p)).totient) *
        (∏ p ∈ fwPr q r,
          if p ∣ t then (p ^ ((q.gcd r).factorization p)).totient
          else p ^ ((q.gcd r).factorization p - 1) * (p - 2))
      else 0) := by
  classical
  have h1 := fw_fib_eq_rf q r t hq hr ht
  have h2 := fw_residue q r t hq hr
  -- replace the K-product in h2 by fwK and S over fwPr
  have hKdef : (∏ p ∈ ((q.gcd r).primeFactors).filter (fun p : ℕ => ¬ p ∣ (q / (q.gcd r)) * (r / (q.gcd r))),
        p ^ ((q.gcd r).factorization p)) = fwK q r := by
    rfl
  have htmod : t % (q * r / (q.gcd r)) = t := Nat.mod_eq_of_lt ht
  have hS := fw_S_form q r (t % (q * r / (q.gcd r))) hq hr
  have hA : (q / (q.gcd r)) * (r / (q.gcd r)) = fwA q r := rfl
  rw [h1]
  rw [h2]
  rw [hKdef]
  rw [hS]
  rw [htmod]
  rw [hA]

/-! ## The fibre count in real form -/

/-- primes of `g` dividing `A`. -/
private noncomputable def fwG1 (q r : ℕ) : Finset ℕ :=
  (q.gcd r).primeFactors.filter (fun p : ℕ => p ∣ fwA q r)

/-- `T`: primes of `fwPr` not dividing `t`. -/
private noncomputable def fwTw (q r t : ℕ) : Finset ℕ :=
  (fwPr q r).filter (fun p : ℕ => ¬ p ∣ t)

/-- `B`: primes of `fwPr` dividing `t`. -/
private noncomputable def fwB (q r t : ℕ) : Finset ℕ :=
  (fwPr q r).filter (fun p : ℕ => p ∣ t)

/-- product over `S` splits as product over `T` times product over `S ∖ T`. -/
private lemma fw_prod_sdiff_split {S T : Finset ℕ} (hT : T ⊆ S) (f : ℕ → ℝ) :
    (∏ p ∈ S, f p) = (∏ p ∈ S \ T, f p) * (∏ p ∈ T, f p) := by
  exact (Finset.prod_sdiff hT).symm

/-- product over `S` equals product over `T` when `f = 1` outside `T`. -/
private lemma fw_prod_eq_prod_subset {S T : Finset ℕ} (hT : T ⊆ S) (f : ℕ → ℝ)
    (h1 : ∀ p ∈ S, p ∉ T → f p = 1) : (∏ p ∈ S, f p) = ∏ p ∈ T, f p := by
  classical
  rw [fw_prod_sdiff_split hT]
  have hrest : (∏ p ∈ S \ T, f p) = 1 := by
    rw [Finset.prod_eq_one]
    intro p hp
    exact h1 p (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hp).2
  rw [hrest, one_mul]

/-- product of an `if` over a finite set splits over the two filter parts. -/
private lemma fw_prod_ite_split (S : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (f g : ℕ → ℝ) :
    (∏ x ∈ S, if p x then f x else g x) = (∏ x ∈ S with p x, f x) * (∏ x ∈ S with ¬ p x, g x) := by
  classical
  exact Finset.prod_ite (s := S) (p := p) (f := f) (g := g)

/-- `fwG1 ⊆ pf(A)`. -/
private lemma fwG1_sub_pfA (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    fwG1 q r ⊆ (fwA q r).primeFactors := by
  classical
  intro p hp
  have hmem := Finset.mem_filter.mp hp
  have hpP : p.Prime := (Nat.mem_primeFactors.mp hmem.1).1
  exact Nat.mem_primeFactors.mpr ⟨hpP, hmem.2, (fwA_pos q r hq hr).ne'⟩

/-- `pf(g) = fwG1 ∪ fwPr`. -/
private lemma fwG_eq_G1_union_F (q r : ℕ) :
    (q.gcd r).primeFactors = fwG1 q r ∪ fwPr q r := by
  classical
  ext p
  constructor
  · intro hp
    by_cases hpdA : p ∣ fwA q r
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hp, hpdA⟩))
    · exact Finset.mem_union.mpr (Or.inr ((fwPr_mem_iff q r p).mpr ⟨hp, hpdA⟩))
  · intro hp
    rcases Finset.mem_union.mp hp with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact (fwPr_mem_iff q r p).mp h |>.1

/-- `fwG1` and `fwPr` are disjoint. -/
private lemma fwG1_disj_F (q r : ℕ) : Disjoint (fwG1 q r) (fwPr q r) := by
  classical
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb hab
  have haA : a ∣ fwA q r := (Finset.mem_filter.mp ha).2
  have hb' := (fwPr_mem_iff q r b).mp hb
  have hbA : b ∣ fwA q r := by rwa [hab] at haA
  exact hb'.2 hbA

/-- `fwB` and `fwTw` are disjoint. -/
private lemma fwB_disj_T (q r t : ℕ) : Disjoint (fwB q r t) (fwTw q r t) := by
  classical
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb hab
  have hpa : a ∣ t := (Finset.mem_filter.mp ha).2
  have hnb : ¬ b ∣ t := (Finset.mem_filter.mp hb).2
  exact hnb (by simpa [hab] using hpa)

/-- `fwG1` and `fwB` are disjoint. -/
private lemma fwG1_disj_B (q r t : ℕ) : Disjoint (fwG1 q r) (fwB q r t) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpG1 hpB
  have hpF : p ∈ fwPr q r := (Finset.mem_filter.mp hpB).1
  have hpF' : p ∉ fwPr q r := (Finset.disjoint_left.mp (fwG1_disj_F q r)) hpG1
  exact hpF' hpF

/-- `pf(g) ∖ T = fwG1 ∪ fwB`. -/
private lemma fwG_sdiff_T_eq (q r t : ℕ) :
    (q.gcd r).primeFactors \ fwTw q r t = fwG1 q r ∪ fwB q r t := by
  classical
  ext p
  constructor
  · intro hp
    rcases Finset.mem_sdiff.mp hp with ⟨hpG, hpT⟩
    by_cases hpA : p ∣ fwA q r
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hpG, hpA⟩))
    · have hpF : p ∈ fwPr q r := (fwPr_mem_iff q r p).mpr ⟨hpG, hpA⟩
      have hpnotpt : ¬ (¬ p ∣ t) := by
        intro hnot
        exact hpT (Finset.mem_filter.mpr ⟨hpF, hnot⟩)
      have hpt : p ∣ t := by
        by_contra hnpt
        exact hpnotpt hnpt
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hpF, hpt⟩))
  · intro hp
    rcases Finset.mem_union.mp hp with hg1 | hb
    · rw [Finset.mem_sdiff]
      constructor
      · exact (Finset.mem_filter.mp hg1).1
      · intro hpT
        have hpF' : p ∉ fwPr q r := (Finset.disjoint_left.mp (fwG1_disj_F q r)) hg1
        exact hpF' (Finset.mem_filter.mp hpT).1
    · rw [Finset.mem_sdiff]
      constructor
      · exact (fwPr_mem_iff q r p).mp (Finset.mem_filter.mp hb).1 |>.1
      · intro hpT
        have hpt : p ∣ t := (Finset.mem_filter.mp hb).2
        exact (Finset.mem_filter.mp hpT).2 hpt

/-- `fwPr = fwB ∪ fwTw`. -/
private lemma fwF_eq_B_union_T (q r t : ℕ) : fwPr q r = fwB q r t ∪ fwTw q r t := by
  classical
  ext p
  constructor
  · intro hp
    by_cases hpt : p ∣ t
    · rw [Finset.mem_union]
      exact Or.inl (by simpa [fwB, Finset.mem_filter] using ⟨hp, hpt⟩)
    · rw [Finset.mem_union]
      exact Or.inr (by simpa [fwTw, Finset.mem_filter] using ⟨hp, hpt⟩)
  · intro hp
    rw [Finset.mem_union] at hp
    rcases hp with h | h
    · have h' : p ∈ (fwPr q r).filter (fun p : ℕ => p ∣ t) := by simpa [fwB] using h
      exact (Finset.mem_filter.mp h').1
    · have h' : p ∈ (fwPr q r).filter (fun p : ℕ => ¬ p ∣ t) := by simpa [fwTw] using h
      exact (Finset.mem_filter.mp h').1

/-- `φ(g) = ∏_{p|g} φ(p^{v_p(g)})` over the reals. -/
private lemma fw_phi_g_prod (q r : ℕ) (hq : 0 < q) :
    ((q.gcd r).totient : ℝ) =
      ∏ p ∈ (q.gcd r).primeFactors, (((p ^ ((q.gcd r).factorization p)).totient : ℕ) : ℝ) := by
  classical
  have hg : q.gcd r ≠ 0 := (fw_gcd_pos_of_q q r hq).ne'
  have h1 := Commons.NumberTheory.Totient.totient_eq_prod_primeFactors (q.gcd r) hg
  have hcast : ((q.gcd r).totient : ℝ) = ∏ p ∈ (q.gcd r).primeFactors,
      (((p ^ ((q.gcd r).factorization p - 1) * (p - 1) : ℕ) : ℝ)) := by
    exact_mod_cast h1
  rw [hcast]
  refine Finset.prod_congr rfl ?_
  intro p hp
  have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpos : 0 < (q.gcd r).factorization p := fw_g_fact_pos q r p hq hp
  rw [← Nat.totient_prime_pow hpP hpos]

/-- per-prime: `φ(p^c)·(p−2)/(p−1) = p^{c−1}(p−2)` (as reals). -/
private lemma fw_tot_pow_mul_cp (p c : ℕ) (hp : p.Prime) (hc : 0 < c) :
    (((p ^ c).totient : ℕ) : ℝ) * fwCp p = (((p ^ (c - 1) * (p - 2) : ℕ) : ℝ)) := by
  rw [Nat.totient_prime_pow hp hc]
  dsimp [fwCp]
  have hpm : (p - 1 : ℕ) ≠ 0 := by
    have hp2 : 2 ≤ p := hp.two_le
    omega
  have h1 : (((p ^ (c - 1) * (p - 1) : ℕ) : ℝ)) = ((p ^ (c - 1) : ℕ) : ℝ) * (((p - 1 : ℕ) : ℝ)) := by
    rw [Nat.cast_mul]
  rw [h1]
  have hden : ((p - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpm
  field_simp [hden]
  rw [Nat.cast_mul]

/-- for `p | A` with `p ∤ g`, the `φ`-factor is `1`. -/
private lemma fw_ph_one_off_G1 (q r : ℕ) (hq : 0 < q) :
    ∀ p ∈ (fwA q r).primeFactors, p ∉ fwG1 q r →
      (((p ^ ((q.gcd r).factorization p)).totient : ℕ) : ℝ) = 1 := by
  classical
  intro p hpA hpnotG1
  have hpP : p.Prime := Nat.prime_of_mem_primeFactors hpA
  have hpA' : p ∣ fwA q r := (Nat.mem_primeFactors.mp hpA).2.1
  have hpnotg : ¬ p ∣ q.gcd r := by
    intro hpg
    have hmem : p ∈ (q.gcd r).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpP, hpg, (fw_gcd_pos_of_q q r hq).ne'⟩
    exact hpnotG1 (Finset.mem_filter.mpr ⟨hmem, hpA'⟩)
  have hc0 : (q.gcd r).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpnotg
  rw [hc0]
  norm_num

/-- main real identity for the fibre count. -/
private lemma fw_res_real (q r t : ℕ) (hq : 0 < q) (hr : 0 < r) :
    (∏ p ∈ (fwA q r).primeFactors, (((p ^ ((q.gcd r).factorization p)).totient : ℕ) : ℝ)) *
      (∏ p ∈ fwPr q r,
        if p ∣ t then ((((p ^ ((q.gcd r).factorization p)).totient : ℕ) : ℝ))
        else ((((p ^ ((q.gcd r).factorization p - 1) * (p - 2) : ℕ) : ℝ)))) =
    ((q.gcd r).totient : ℝ) *
      (∏ p ∈ (fwPr q r).filter (fun p : ℕ => ¬ p ∣ t), fwCp p) := by
  classical
  let ph : ℕ → ℝ := fun p => (((p ^ ((q.gcd r).factorization p)).totient : ℕ) : ℝ)
  let pw : ℕ → ℝ := fun p => (((p ^ ((q.gcd r).factorization p - 1) * (p - 2) : ℕ) : ℝ))
  let G : Finset ℕ := (q.gcd r).primeFactors
  let F : Finset ℕ := fwPr q r
  let Tw : Finset ℕ := fwTw q r t
  let B : Finset ℕ := fwB q r t
  have hG1A : fwG1 q r ⊆ (fwA q r).primeFactors := fwG1_sub_pfA q r hq hr
  have hTsubG : Tw ⊆ G := by
    intro p hp
    have hpF : p ∈ fwPr q r := (Finset.mem_filter.mp hp).1
    exact (fwPr_mem_iff q r p).mp hpF |>.1
  have hGunion : G = fwG1 q r ∪ F := fwG_eq_G1_union_F q r
  have hdisj1 : Disjoint (fwG1 q r) F := fwG1_disj_F q r
  have hpp : ∀ p ∈ Tw, ph p * fwCp p = pw p := by
    intro p hpT
    have hpF : p ∈ fwPr q r := (Finset.mem_filter.mp hpT).1
    have hpP : p.Prime := (fwPr_prime_dvd_g q r p hpF).1
    have hcpos : 0 < (q.gcd r).factorization p := by
      have hpg : p ∣ q.gcd r := (fwPr_prime_dvd_g q r p hpF).2.1
      have hg : q.gcd r ≠ 0 := (fw_gcd_pos_of_q q r hq).ne'
      exact Nat.Prime.factorization_pos_of_dvd hpP hg hpg
    exact fw_tot_pow_mul_cp p ((q.gcd r).factorization p) hpP hcpos
  have hprodA : (∏ p ∈ (fwA q r).primeFactors, ph p) = ∏ p ∈ fwG1 q r, ph p := by
    exact fw_prod_eq_prod_subset hG1A ph
      (by intro p hp hpnot; simpa [ph] using fw_ph_one_off_G1 q r hq p hp hpnot)
  have hF_filter_t : (fwPr q r).filter (fun p : ℕ => p ∣ t) = fwB q r t := rfl
  have hF_filter_nt : (fwPr q r).filter (fun p : ℕ => ¬ p ∣ t) = fwTw q r t := rfl
  have hprodF : (∏ p ∈ F, if p ∣ t then ph p else pw p) =
      (∏ p ∈ B, ph p) * (∏ p ∈ Tw, pw p) := by
    calc
      (∏ p ∈ F, if p ∣ t then ph p else pw p)
          = (∏ p ∈ F with p ∣ t, ph p) * (∏ p ∈ F with ¬ p ∣ t, pw p) :=
              fw_prod_ite_split F (fun p : ℕ => p ∣ t) ph pw
      _ = (∏ p ∈ B, ph p) * (∏ p ∈ Tw, pw p) := by
              have hset1 : F.filter (fun p : ℕ => p ∣ t) = B := by
                simpa [F, B] using (hF_filter_t)
              have hset2 : F.filter (fun p : ℕ => ¬ p ∣ t) = Tw := by
                simpa [F, Tw] using (hF_filter_nt)
              rw [hset1, hset2]
  have hL : (∏ p ∈ (fwA q r).primeFactors, ph p) * (∏ p ∈ F, if p ∣ t then ph p else pw p) =
      (∏ p ∈ fwG1 q r, ph p) * (∏ p ∈ B, ph p) * (∏ p ∈ Tw, pw p) := by
    rw [hprodA, hprodF]
    ring
  have hprodG : (∏ p ∈ G, ph p) = (∏ p ∈ fwG1 q r, ph p) * (∏ p ∈ F, ph p) := by
    rw [hGunion]
    rw [Finset.prod_union hdisj1]
  have hFsplit : F = B ∪ Tw := by
    simpa [F, B, Tw] using (fwF_eq_B_union_T q r t)
  have hprodG1F : (∏ p ∈ fwG1 q r, ph p) * (∏ p ∈ F, ph p) =
      (∏ p ∈ fwG1 q r, ph p) * (∏ p ∈ B, ph p) * (∏ p ∈ Tw, ph p) := by
    calc
      (∏ p ∈ fwG1 q r, ph p) * (∏ p ∈ F, ph p)
          = (∏ p ∈ fwG1 q r, ph p) * (∏ p ∈ B ∪ Tw, ph p) := by rw [hFsplit]
      _ = (∏ p ∈ fwG1 q r, ph p) * ((∏ p ∈ B, ph p) * (∏ p ∈ Tw, ph p)) := by
              rw [Finset.prod_union (fwB_disj_T q r t)]
      _ = (∏ p ∈ fwG1 q r, ph p) * (∏ p ∈ B, ph p) * (∏ p ∈ Tw, ph p) := by ring
  have hprodT : (∏ p ∈ Tw, (ph p * fwCp p)) = (∏ p ∈ Tw, ph p) * (∏ p ∈ Tw, fwCp p) := by
    rw [Finset.prod_mul_distrib]
  have hprodGs : (∏ p ∈ G \ Tw, ph p) = (∏ p ∈ fwG1 q r, ph p) * (∏ p ∈ B, ph p) := by
    dsimp [G, Tw, B]
    rw [fwG_sdiff_T_eq q r t]
    rw [Finset.prod_union (fwG1_disj_B q r t)]
  have hR : ((q.gcd r).totient : ℝ) * (∏ p ∈ Tw, fwCp p) =
      (∏ p ∈ fwG1 q r, ph p) * (∏ p ∈ B, ph p) * (∏ p ∈ Tw, ph p * fwCp p) := by
    calc
      ((q.gcd r).totient : ℝ) * (∏ p ∈ Tw, fwCp p)
          = (∏ p ∈ G, ph p) * (∏ p ∈ Tw, fwCp p) := by
              rw [fw_phi_g_prod q r hq]
      _ = ((∏ p ∈ G \ Tw, ph p) * (∏ p ∈ Tw, ph p)) * (∏ p ∈ Tw, fwCp p) := by
              rw [fw_prod_sdiff_split hTsubG]
      _ = (∏ p ∈ G \ Tw, ph p) * ((∏ p ∈ Tw, ph p) * (∏ p ∈ Tw, fwCp p)) := by ring
      _ = (∏ p ∈ G \ Tw, ph p) * (∏ p ∈ Tw, (ph p * fwCp p)) := by rw [← hprodT]
      _ = ((∏ p ∈ fwG1 q r, ph p) * (∏ p ∈ B, ph p)) * (∏ p ∈ Tw, (ph p * fwCp p)) := by
              rw [hprodGs]
      _ = (∏ p ∈ fwG1 q r, ph p) * (∏ p ∈ B, ph p) * (∏ p ∈ Tw, ph p * fwCp p) := by ring
  have hTpp : (∏ p ∈ Tw, ph p * fwCp p) = ∏ p ∈ Tw, pw p := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    exact hpp p hp
  calc
    (∏ p ∈ (fwA q r).primeFactors, ph p) *
        (∏ p ∈ fwPr q r, if p ∣ t then ph p else pw p)
        = (∏ p ∈ fwG1 q r, ph p) * (∏ p ∈ B, ph p) * (∏ p ∈ Tw, pw p) := by
            simpa [F] using hL
    _ = (∏ p ∈ fwG1 q r, ph p) * (∏ p ∈ B, ph p) * (∏ p ∈ Tw, ph p * fwCp p) := by
            rw [← hTpp]
    _ = ((q.gcd r).totient : ℝ) * (∏ p ∈ Tw, fwCp p) := by
            rw [hR]
    _ = ((q.gcd r).totient : ℝ) *
          (∏ p ∈ (fwPr q r).filter (fun p : ℕ => ¬ p ∣ t), fwCp p) := by
            simp [Tw, fwTw]

/-- Exact fibre count in `fwH` form: the number of reduced pairs with value
`t < L` equals `φ(g)·fwH(q,r,t)`. -/
private lemma fw_fibre_eq (q r t : ℕ) (hq : 0 < q) (hr : 0 < r) (ht : t < q * r / (q.gcd r)) :
    ((fwFib q r t) : ℝ) = ((q.gcd r).totient : ℝ) * fwH q r t := by
  classical
  have hnat := fw_fib_residue_form q r t hq hr ht
  by_cases hc : t.gcd (fwA q r) = 1
  · have hfwH : fwH q r t =
        ∏ p ∈ (fwPr q r).filter (fun p : ℕ => ¬ p ∣ t), fwCp p := by
      dsimp [fwH, fwCopr, fwGprod]
      rw [if_pos hc]
      simp
    calc
      ((fwFib q r t : ℕ) : ℝ)
          = (∏ p ∈ (fwA q r).primeFactors, (((p ^ ((q.gcd r).factorization p)).totient : ℕ) : ℝ)) *
              (∏ p ∈ fwPr q r,
                if p ∣ t then ((((p ^ ((q.gcd r).factorization p)).totient : ℕ) : ℝ))
                else ((((p ^ ((q.gcd r).factorization p - 1) * (p - 2) : ℕ) : ℝ)))) := by
              have hpos := congrArg (fun n : ℕ => (n : ℝ)) hnat
              rw [if_pos hc] at hpos
              simpa [Nat.cast_mul, Nat.cast_prod, Nat.cast_ite] using hpos
      _ = ((q.gcd r).totient : ℝ) *
            (∏ p ∈ (fwPr q r).filter (fun p : ℕ => ¬ p ∣ t), fwCp p) :=
              fw_res_real q r t hq hr
      _ = ((q.gcd r).totient : ℝ) * fwH q r t := by rw [hfwH]
  · have hfwH0 : fwH q r t = 0 := by
      dsimp [fwH, fwCopr]
      rw [if_neg hc]
      simp
    calc
      ((fwFib q r t : ℕ) : ℝ) = 0 := by
          have hnat0 := congrArg (fun n : ℕ => (n : ℝ)) hnat
          rw [if_neg hc] at hnat0
          simpa using hnat0
      _ = ((q.gcd r).totient : ℝ) * fwH q r t := by rw [hfwH0]; simp

/-- Coefficient identity: `φ(q)φ(r)/L = φ(g)·(φ(A)/A)·∏_{p∈fwPr}(p−1)/p`. -/
private lemma fw_coeff_eq (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    (q.totient : ℝ) * (r.totient : ℝ) / ((q * r / (q.gcd r) : ℕ) : ℝ) =
      ((q.gcd r).totient : ℝ) * ((fwA q r).totient : ℝ) / (fwA q r : ℝ) *
        (∏ p ∈ fwPr q r, (((p : ℝ) - 1) / (p : ℝ))) := by
  classical
  have hqrN : q * r ≠ 0 := by positivity
  have hAN : fwA q r ≠ 0 := ne_of_gt (fwA_pos q r hq hr)
  calc
    (q.totient : ℝ) * (r.totient : ℝ) / ((q * r / (q.gcd r) : ℕ) : ℝ)
        = ((q * r).totient : ℝ) * ((q.gcd r).totient : ℝ) / ((q * r : ℕ) : ℝ) :=
            fw_coeff_arith q r hq hr
    _ = ((q.gcd r).totient : ℝ) * (((q * r).totient : ℝ) / ((q * r : ℕ) : ℝ)) := by ring
    _ = ((q.gcd r).totient : ℝ) *
          (∏ p ∈ (q * r).primeFactors, (1 - (1 : ℝ) / (p : ℝ))) := by
            rw [fw_phi_ratio_prod (q * r) hqrN]
    _ = ((q.gcd r).totient : ℝ) *
          ((∏ p ∈ (fwA q r).primeFactors, (1 - (1 : ℝ) / (p : ℝ))) *
            (∏ p ∈ fwPr q r, (1 - (1 : ℝ) / (p : ℝ)))) := by
            rw [fw_euler_split q r hq hr]
    _ = ((q.gcd r).totient : ℝ) *
          ((((fwA q r).totient : ℝ) / (fwA q r : ℝ)) *
            (∏ p ∈ fwPr q r, (1 - (1 : ℝ) / (p : ℝ)))) := by
            rw [fw_phi_ratio_prod (fwA q r) hAN]
    _ = ((q.gcd r).totient : ℝ) *
          ((((fwA q r).totient : ℝ) / (fwA q r : ℝ)) *
            (∏ p ∈ fwPr q r, (((p : ℝ) - 1) / (p : ℝ)))) := by
            have hprod : (∏ p ∈ fwPr q r, (1 - (1 : ℝ) / (p : ℝ))) =
                (∏ p ∈ fwPr q r, (((p : ℝ) - 1) / (p : ℝ))) := by
                refine Finset.prod_congr rfl ?_
                intro p hp
                have hpIn : p ∈ (q.gcd r).primeFactors := (fwPr_mem_iff q r p).mp hp |>.1
                have hpp : p.Prime := (Nat.mem_primeFactors.mp hpIn).1
                exact (fw_pm1_div_p_eq p (by exact_mod_cast hpp.ne_zero)).symm
            rw [hprod]
    _ = ((q.gcd r).totient : ℝ) * ((fwA q r).totient : ℝ) / (fwA q r : ℝ) *
          (∏ p ∈ fwPr q r, (((p : ℝ) - 1) / (p : ℝ))) := by
            have hAr : (fwA q r : ℝ) ≠ 0 := by exact_mod_cast hAN
            field_simp [hAr]

/-- `gprod(S,0) = 1`. -/
private lemma fwGprod_zero (S : Finset ℕ) : fwGprod S 0 = 1 := by
  classical
  dsimp [fwGprod]
  have hnot : (fun p : ℕ => ¬ p ∣ 0) = (fun _ : ℕ => False) := by
    funext p
    apply propext
    constructor
    · intro h
      exact h (dvd_zero p)
    · intro hf
      exact False.elim hf
  have hf : (S.filter (fun p : ℕ => ¬ p ∣ 0)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro p hp
    exact fun h => h (dvd_zero p)
  rw [hf]
  simp

/-- reflection of `gprod`: `p ∣ (L−s) ⟺ p ∣ s` for `p ∈ S ⊆ fwPr`. -/
private lemma fwGprod_L_sub (q r : ℕ) (S : Finset ℕ) (s : ℕ) (hs : s ≤ q * r / (q.gcd r))
    (hS : ∀ p ∈ S, p ∈ fwPr q r) :
    fwGprod S ((q * r / (q.gcd r)) - s) = fwGprod S s := by
  classical
  dsimp [fwGprod]
  have heq : (S.filter (fun p : ℕ => ¬ p ∣ (q * r / (q.gcd r)) - s)) =
      S.filter (fun p : ℕ => ¬ p ∣ s) := by
    apply Finset.filter_congr
    intro p hp
    have hpdL : p ∣ q * r / (q.gcd r) := fwPr_dvd_L q r p (hS p hp)
    exact not_congr (fw_dvd_sub_iff (q * r / (q.gcd r)) p s hpdL hs)
  rw [heq]

/-- reflection of the coprimality indicator across `L`. -/
private lemma fwCopr_L_sub (q r s : ℕ) (hs : s ≤ q * r / (q.gcd r)) :
    fwCopr q r ((q * r / (q.gcd r)) - s) = fwCopr q r s := by
  classical
  dsimp [fwCopr]
  have hg : ((q * r / (q.gcd r)) - s).gcd (fwA q r) = s.gcd (fwA q r) :=
    fw_gcd_L_sub_A q r s hs
  by_cases h1 : s.gcd (fwA q r) = 1
  · have h1' : ((q * r / (q.gcd r)) - s).gcd (fwA q r) = 1 := by
      rw [hg, h1]
    rw [if_pos h1, if_pos h1']
  · have hn1 : ¬ ((q * r / (q.gcd r)) - s).gcd (fwA q r) = 1 := by
      intro h
      apply h1
      rwa [← hg]
    rw [if_neg h1, if_neg hn1]

/-- reflection of `fwH` across `L`. -/
private lemma fwH_L_sub (q r s : ℕ) (hs : s ≤ q * r / (q.gcd r)) :
    fwH q r ((q * r / (q.gcd r)) - s) = fwH q r s := by
  classical
  dsimp [fwH]
  rw [fwCopr_L_sub q r s hs]
  exact congrArg (fun x : ℝ => fwCopr q r s * x) (fwGprod_L_sub q r (fwPr q r) s hs (by intro p hp; exact hp))

/-! ## Window reduction to a single initial segment -/

/-- the window-weight sum `Σ_{s∈[1,W]} h(s)`. -/
private noncomputable def fwSumLow (q r W : ℕ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 W, fwH q r s

/-- `h(0) = [A=1]`. -/
private lemma fwH_zero (q r : ℕ) : fwH q r 0 = (if fwA q r = 1 then (1 : ℝ) else 0) := by
  classical
  dsimp [fwH, fwCopr]
  have hgA : Nat.gcd 0 (fwA q r) = fwA q r := by simp
  have hprod : fwGprod (fwPr q r) 0 = 1 := fwGprod_zero (fwPr q r)
  rw [hprod, mul_one]
  by_cases h1 : fwA q r = 1
  · have hgcd : Nat.gcd 0 (fwA q r) = 1 := by rw [hgA, h1]
    rw [if_pos hgcd, if_pos h1]
  · have hgcd : ¬ Nat.gcd 0 (fwA q r) = 1 := by
      intro hz
      apply h1
      rw [hgA] at hz
      exact hz
    rw [if_neg hgcd, if_neg h1]

/-- `Icc 0 W = insert 0 (Icc 1 W)`. -/
private lemma fw_Icc0_eq_insert (W : ℕ) :
    Finset.Icc 0 W = insert 0 (Finset.Icc 1 W) := by
  classical
  ext t
  constructor
  · intro h
    have htW : t ≤ W := (Finset.mem_Icc.mp h).2
    by_cases ht0 : t = 0
    · rw [ht0]
      simp
    · rw [Finset.mem_insert, Finset.mem_Icc]
      right
      exact ⟨by omega, htW⟩
  · intro h
    rw [Finset.mem_insert, Finset.mem_Icc] at h
    rw [Finset.mem_Icc]
    rcases h with h0 | hw
    · omega
    · exact ⟨by omega, hw.2⟩

/-- `Σ_{t∈Icc0W} F t = F 0 + Σ_{t∈Icc1W} F t`. -/
private lemma fw_sum_Icc0 (W : ℕ) (F : ℕ → ℝ) :
    (∑ t ∈ Finset.Icc 0 W, F t) = F 0 + ∑ t ∈ Finset.Icc 1 W, F t := by
  rw [fw_Icc0_eq_insert W]
  rw [Finset.sum_insert]
  simp

/-- The upper window `[L−W, L−1]` is in bijection with `[1,W]` under `t ↦ L−t`. -/
private lemma fw_up_image (q r W : ℕ) (hW : 2 * W + 1 ≤ q * r / (q.gcd r)) :
    ((Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1)).image
        (fun t : ℕ => (q * r / (q.gcd r)) - t)) = Finset.Icc 1 W := by
  classical
  let L : ℕ := q * r / (q.gcd r)
  have hW' : 2 * W + 1 ≤ L := by simpa [L] using hW
  have hL1 : 1 ≤ L := by omega
  change ((Finset.Icc (L - W) (L - 1)).image (fun t : ℕ => L - t)) = Finset.Icc 1 W
  ext s
  constructor
  · intro h
    rw [Finset.mem_image] at h
    rcases h with ⟨t, ht, hs⟩
    have htlo : L - W ≤ t := (Finset.mem_Icc.mp ht).1
    have hthi : t ≤ L - 1 := (Finset.mem_Icc.mp ht).2
    have h1 : 1 ≤ L - t := by omega
    have h2 : L - t ≤ W := by omega
    rw [Finset.mem_Icc]
    rw [← hs]
    exact ⟨h1, h2⟩
  · intro h
    have hmem := Finset.mem_Icc.mp h
    rw [Finset.mem_image]
    refine ⟨L - s, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨by omega, by omega⟩
    · omega

/-- sum over the upper window of `h` equals the sum over `[1,W]`. -/
private lemma fw_sum_up_h_eq (q r W : ℕ) (hW : 2 * W + 1 ≤ q * r / (q.gcd r)) :
    (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1), fwH q r t) =
      ∑ s ∈ Finset.Icc 1 W, fwH q r s := by
  classical
  let L : ℕ := q * r / (q.gcd r)
  have hW' : 2 * W + 1 ≤ L := by simpa [L] using hW
  have hL1 : 1 ≤ L := by omega
  have hrefl : ∀ t : ℕ, t ≤ L → fwH q r t = fwH q r (L - t) := by
    intro t htle
    have hh := fwH_L_sub q r t htle
    exact hh.symm
  change (∑ t ∈ Finset.Icc (L - W) (L - 1), fwH q r t) = ∑ s ∈ Finset.Icc 1 W, fwH q r s
  refine Finset.sum_bij (fun t ht => L - t) ?_ ?_ ?_ ?_
  · intro t ht
    have ht' := Finset.mem_Icc.mp ht
    rw [Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  · intro t1 ht1 t2 ht2 hEq
    have h1 : t1 ≤ L := by
      have h := Finset.mem_Icc.mp ht1
      omega
    have h2 : t2 ≤ L := by
      have h := Finset.mem_Icc.mp ht2
      omega
    omega
  · intro s hs
    have hs' := Finset.mem_Icc.mp hs
    refine ⟨L - s, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨by omega, by omega⟩
    · omega
  · intro t ht
    have htle : t ≤ L := by
      have h := Finset.mem_Icc.mp ht
      omega
    exact hrefl t htle

/-- The window count equals `φ(g)(h(0) + 2·Σ_{[1,W]} h)`. -/
private lemma fw_card_eq_low (q r W : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hW : 2 * W + 1 ≤ q * r / (q.gcd r)) :
    (((fwPQ q r).filter (fwP q r W)).card : ℝ) =
      ((q.gcd r).totient : ℝ) * (fwH q r 0 + 2 * fwSumLow q r W) := by
  classical
  have hLpos : 0 < q * r / (q.gcd r) := fw_L_pos q r hq hr
  have hfib : ∀ t : ℕ, t < q * r / (q.gcd r) →
      ((fwFib q r t : ℕ) : ℝ) = ((q.gcd r).totient : ℝ) * fwH q r t := by
    intro t ht
    have hf := fw_fibre_eq q r t hq hr ht
    simpa [fwFib, fwVal] using hf
  -- bounds for t in the windows
  have htL0 : ∀ t ∈ Finset.Icc 0 W, t < q * r / (q.gcd r) := by
    intro t ht
    have htW : t ≤ W := (Finset.mem_Icc.mp ht).2
    have hW' : W < q * r / (q.gcd r) := by omega
    omega
  have htL1 : ∀ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1),
      t < q * r / (q.gcd r) := by
    intro t ht
    have hthi : t ≤ (q * r / (q.gcd r)) - 1 := (Finset.mem_Icc.mp ht).2
    omega
  have hsum0 : (∑ t ∈ Finset.Icc 0 W, ((fwFib q r t : ℕ) : ℝ)) =
      ((q.gcd r).totient : ℝ) * (∑ t ∈ Finset.Icc 0 W, fwH q r t) := by
    calc
      (∑ t ∈ Finset.Icc 0 W, ((fwFib q r t : ℕ) : ℝ))
          = ∑ t ∈ Finset.Icc 0 W, ((q.gcd r).totient : ℝ) * fwH q r t := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              exact hfib t (htL0 t ht)
      _ = ((q.gcd r).totient : ℝ) * (∑ t ∈ Finset.Icc 0 W, fwH q r t) := by
              rw [Finset.mul_sum]
  have hsum1 : (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1),
      ((fwFib q r t : ℕ) : ℝ)) =
      ((q.gcd r).totient : ℝ) * (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W)
        ((q * r / (q.gcd r)) - 1), fwH q r t) := by
    calc
      (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1),
          ((fwFib q r t : ℕ) : ℝ))
          = ∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1),
              ((q.gcd r).totient : ℝ) * fwH q r t := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              exact hfib t (htL1 t ht)
      _ = ((q.gcd r).totient : ℝ) * (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W)
          ((q * r / (q.gcd r)) - 1), fwH q r t) := by
              rw [Finset.mul_sum]
  have hcardN := fw_card_filter_P q r W hq hr hW
  change ((fwPQ q r).filter (fwP q r W)).card =
      (∑ t ∈ Finset.Icc 0 W, (fwFib q r t : ℕ)) +
      (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1),
        (fwFib q r t : ℕ)) at hcardN
  have hup : (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1), fwH q r t) =
      fwSumLow q r W := by
    exact fw_sum_up_h_eq q r W hW
  calc
    (((fwPQ q r).filter (fwP q r W)).card : ℝ)
        = (∑ t ∈ Finset.Icc 0 W, ((fwFib q r t : ℕ) : ℝ)) +
          (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1),
            ((fwFib q r t : ℕ) : ℝ)) := by
            exact_mod_cast hcardN
    _ = ((q.gcd r).totient : ℝ) * (∑ t ∈ Finset.Icc 0 W, fwH q r t) +
        ((q.gcd r).totient : ℝ) * (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W)
          ((q * r / (q.gcd r)) - 1), fwH q r t) := by
            rw [hsum0, hsum1]
    _ = ((q.gcd r).totient : ℝ) * ((∑ t ∈ Finset.Icc 0 W, fwH q r t) +
        (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1), fwH q r t)) := by
            ring
    _ = ((q.gcd r).totient : ℝ) * (fwH q r 0 + 2 * fwSumLow q r W) := by
            rw [fw_sum_Icc0 W (fun t : ℕ => fwH q r t)]
            rw [hup]
            rw [fwSumLow]
            ring

/-! ## Bounding the fibre-weight sum -/

/-- elements of `fwPr` are prime. -/
private lemma fwPr_prime (q r p : ℕ) (hp : p ∈ fwPr q r) : p.Prime :=
  (fwPr_prime_dvd_g q r p hp).1

/-- `∏_{p∈U} p` divides `∏_{p∈S} p` for `U ⊆ S`. -/
private lemma fw_dprod_dvd_prod {S U : Finset ℕ} (hU : U ⊆ S) :
    fwDprod U ∣ fwDprod S := by
  classical
  refine ⟨∏ p ∈ S \ U, p, ?_⟩
  dsimp [fwDprod]
  rw [mul_comm]
  exact (Finset.prod_sdiff (f := fun p : ℕ => p) hU).symm

/-- `A ⊥ d_U` for `U ⊆ fwPr`. -/
private lemma fw_coprime_A_dprod (q r : ℕ) (U : Finset ℕ) (hU : U ⊆ fwPr q r) :
    Nat.Coprime (fwDprod U) (fwA q r) := by
  classical
  by_contra hg
  rcases Nat.exists_prime_and_dvd (n := (fwDprod U).gcd (fwA q r)) hg with ⟨p, hpP, hpd⟩
  have hpdU : p ∣ fwDprod U := dvd_trans hpd (Nat.gcd_dvd_left _ _)
  have hpdA : p ∣ fwA q r := dvd_trans hpd (Nat.gcd_dvd_right _ _)
  rcases Commons.NumberTheory.Nat.prime_dvd_finset_prod (s := U) hpP (fun x : ℕ => x) hpdU with
    ⟨x, hx, hpx⟩
  have hxU : x ∈ fwPr q r := hU hx
  have hxP : x.Prime := (fwPr_prime_dvd_g q r x hxU).1
  have hpxeq : p = x := by
    rcases hxP.eq_one_or_self_of_dvd p hpx with h1 | hEq
    · exact False.elim (hpP.ne_one h1)
    · exact hEq
  have hxndA : ¬ x ∣ fwA q r := (fwPr_prime_dvd_g q r x hxU).2.2
  exact hxndA (by simpa [hpxeq] using hpdA)

/-- `gcd(d·j, A) = gcd(j, A)` when `d ⊥ A`. -/
private lemma fw_gcd_mul_of_coprime (d j A : ℕ) (hdA : Nat.Coprime d A) :
    (d * j).gcd A = j.gcd A := by
  classical
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · have hgA : (d * j).gcd A ∣ A := Nat.gcd_dvd_right _ _
      have hgj : (d * j).gcd A ∣ d * j := Nat.gcd_dvd_left _ _
      have hcop : ((d * j).gcd A).Coprime d := hdA.symm.coprime_dvd_left hgA
      exact hcop.dvd_of_dvd_mul_left hgj
    · exact Nat.gcd_dvd_right _ _
  · apply Nat.dvd_gcd
    · exact dvd_trans (Nat.gcd_dvd_left j A) ⟨d, mul_comm d j⟩
    · exact Nat.gcd_dvd_right _ _

/-- reindex: multiples of `d` in `[1,x]` coprime to `A` count `j ∈ [1, x/d]`
coprime to `A` (when `d ⊥ A`). -/
private lemma fw_coprime_multiples_card (A d x : ℕ) (hd : 0 < d) (hAd : Nat.Coprime d A) :
    ((Finset.Icc 1 x).filter (fun s : ℕ => d ∣ s ∧ s.gcd A = 1)).card =
      fwCcnt A (x / d) := by
  classical
  let S : Finset ℕ := (Finset.Icc 1 x).filter (fun s : ℕ => d ∣ s ∧ s.gcd A = 1)
  let T : Finset ℕ := (Finset.Icc 1 (x / d)).filter (fun j : ℕ => j.gcd A = 1)
  change S.card = T.card
  refine (Finset.card_bij (fun j hj => d * j) ?_ ?_ ?_).symm
  · intro j hj
    have hjm := Finset.mem_filter.mp hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hjm.1).1
    have hjx : j ≤ x / d := (Finset.mem_Icc.mp hjm.1).2
    have hjA : j.gcd A = 1 := hjm.2
    rw [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · constructor
      · exact Nat.succ_le_of_lt (Nat.mul_pos hd (by omega))
      · have hjx' : j * d ≤ x := (Nat.le_div_iff_mul_le hd).mp hjx
        rwa [mul_comm] at hjx'
    · constructor
      · exact dvd_mul_right d j
      · rw [fw_gcd_mul_of_coprime d j A hAd, hjA]
  · intro j1 hj1 j2 hj2 hEq
    exact Nat.mul_left_cancel hd hEq
  · intro s hs
    have hsm := Finset.mem_filter.mp hs
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hsm.1).1
    have hsx : s ≤ x := (Finset.mem_Icc.mp hsm.1).2
    have hds : d ∣ s := hsm.2.1
    have hsA : s.gcd A = 1 := hsm.2.2
    rcases hds with ⟨j, hj⟩
    have hj0 : j ≠ 0 := by
      intro hz
      subst j
      simp at hj
      omega
    refine ⟨j, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · constructor
        · exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
        · have hjx' : d * j ≤ x := by rw [hj.symm]; exact hsx
          exact (Nat.le_div_iff_mul_le hd).mpr (by rwa [mul_comm] at hjx')
      · have hjj : j ∣ s := by rw [hj]; exact ⟨d, mul_comm d j⟩
        have hgA : j.gcd A ∣ A := Nat.gcd_dvd_right _ _
        have hgS : j.gcd A ∣ s := dvd_trans (Nat.gcd_dvd_left j A) hjj
        have hg1 : j.gcd A ∣ 1 := by
          rw [← hsA]
          exact Nat.dvd_gcd hgS hgA
        exact Nat.dvd_antisymm hg1 (one_dvd _)
    · rw [← hj]

private lemma fw_copr_multiples_sum (q r d W : ℕ) (hd : 0 < d) (hAd : Nat.Coprime d (fwA q r)) :
    (∑ s ∈ Finset.Icc 1 W, fwCopr q r s * (if d ∣ s then (1 : ℝ) else 0)) =
      (fwCcnt (fwA q r) (W / d) : ℝ) := by
  classical
  have hsplit : ∀ s ∈ Finset.Icc 1 W,
      fwCopr q r s * (if d ∣ s then (1 : ℝ) else 0) =
        (if s.gcd (fwA q r) = 1 ∧ d ∣ s then (1 : ℝ) else 0) := by
    intro s hs
    by_cases h1 : s.gcd (fwA q r) = 1 <;> by_cases h2 : d ∣ s <;> simp [fwCopr, h1, h2]
  calc
    (∑ s ∈ Finset.Icc 1 W, fwCopr q r s * (if d ∣ s then (1 : ℝ) else 0))
        = ∑ s ∈ Finset.Icc 1 W, (if s.gcd (fwA q r) = 1 ∧ d ∣ s then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            exact hsplit s hs
    _ = (((Finset.Icc 1 W).filter (fun s : ℕ => s.gcd (fwA q r) = 1 ∧ d ∣ s)).card : ℝ) := by
            rw [Finset.sum_boole]
    _ = (((Finset.Icc 1 W).filter (fun s : ℕ => d ∣ s ∧ s.gcd (fwA q r) = 1)).card : ℝ) := by
            congr 1
            apply congrArg Finset.card
            ext s
            simp [and_comm, and_left_comm, and_assoc]
    _ = ((fwCcnt (fwA q r) (W / d)) : ℝ) := by
            congr 1
            exact fw_coprime_multiples_card (fwA q r) d W hd hAd

/-- crude bound on the coprime count in `[1,x]` with a `2^ω(A)` error term. -/
private lemma fw_copr_Icc_le (q r x : ℕ) (hA : 1 ≤ fwA q r) :
    (fwCcnt (fwA q r) x : ℝ) ≤ (x : ℝ) * ((fwA q r).totient : ℝ) / (fwA q r : ℝ) +
      (2 : ℝ) ^ (fwA q r).primeFactors.card := by
  classical
  by_cases hA2 : 2 ≤ fwA q r
  · have hb := Commons.NumberTheory.Totient.coprime_interval_count_le (fwA q r) x hA2
    have hω : (2 : ℝ) ^ ((fwA q r).primeFactors.card - 1) ≤
        (2 : ℝ) ^ (fwA q r).primeFactors.card := by
      exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (Nat.sub_le _ _)
    dsimp [fwCcnt]
    linarith
  · have hA1 : fwA q r = 1 := by omega
    have hcnt : (fwCcnt (fwA q r) x : ℝ) ≤ (x : ℝ) := by
      dsimp [fwCcnt]
      calc
        (((Finset.Icc 1 x).filter (fun j : ℕ => j.gcd (fwA q r) = 1)).card : ℝ)
            ≤ ((Finset.Icc 1 x).card : ℝ) := by
                exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _))
        _ = (x : ℝ) := by
                rw [Nat.card_Icc]
                simp [hA1]
    have hR : (x : ℝ) * ((fwA q r).totient : ℝ) / (fwA q r : ℝ) +
        (2 : ℝ) ^ (fwA q r).primeFactors.card = (x : ℝ) + 1 := by
        rw [hA1]
        norm_num
    linarith

/-- expansion of the weight-sum over the subset weights and coprime counts. -/
private lemma fw_sumH_expand (q r W : ℕ) :
    fwSumLow q r W =
      ∑ U ∈ (fwPr q r).powerset, fwGamma q r U * (fwCcnt (fwA q r) (W / fwDprod U) : ℝ) := by
  classical
  calc
    fwSumLow q r W
        = ∑ s ∈ Finset.Icc 1 W, fwCopr q r s * fwGprod (fwPr q r) s := by
            simp [fwSumLow, fwH]
    _ = ∑ s ∈ Finset.Icc 1 W, fwCopr q r s *
          (∑ U ∈ (fwPr q r).powerset,
            fwGamma q r U * (if fwDprod U ∣ s then (1 : ℝ) else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            congr 1
            have hg := fw_gprod_expand (fwPr q r) s (fun p hp => fwPr_prime q r p hp)
            rw [hg]
            refine Finset.sum_congr rfl ?_
            intro U hU
            by_cases hdiv : fwDprod U ∣ s
            · have hif : (∏ p ∈ U, p) ∣ s := by simpa [fwDprod] using hdiv
              simp [hif, fwGamma, fwDprod]
            · have hif : ¬ (∏ p ∈ U, p) ∣ s := by simpa [fwDprod] using hdiv
              simp [hif, fwGamma, fwDprod]
    _ = ∑ s ∈ Finset.Icc 1 W, ∑ U ∈ (fwPr q r).powerset,
          fwCopr q r s * (fwGamma q r U * (if fwDprod U ∣ s then (1 : ℝ) else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            exact (Finset.mul_sum (s := (fwPr q r).powerset)
              (f := fun U : Finset ℕ => fwGamma q r U * (if fwDprod U ∣ s then (1 : ℝ) else 0))
              (a := fwCopr q r s))
    _ = ∑ U ∈ (fwPr q r).powerset, ∑ s ∈ Finset.Icc 1 W,
          fwCopr q r s * (fwGamma q r U * (if fwDprod U ∣ s then (1 : ℝ) else 0)) := by
            exact Finset.sum_comm (s := Finset.Icc 1 W) (t := (fwPr q r).powerset)
              (f := fun s U => fwCopr q r s * (fwGamma q r U * (if fwDprod U ∣ s then (1 : ℝ) else 0)))
    _ = ∑ U ∈ (fwPr q r).powerset, fwGamma q r U *
          (∑ s ∈ Finset.Icc 1 W, fwCopr q r s * (if fwDprod U ∣ s then (1 : ℝ) else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro U hU
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro s hs
            ring
    _ = ∑ U ∈ (fwPr q r).powerset, fwGamma q r U * (fwCcnt (fwA q r) (W / fwDprod U) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro U hU
            have hUsub : U ⊆ fwPr q r := Finset.mem_powerset.mp hU
            have hd0 : 0 < fwDprod U := by
              dsimp [fwDprod]
              exact Finset.prod_pos (fun p hp => (fwPr_prime q r p (hUsub hp)).pos)
            have hAd : Nat.Coprime (fwDprod U) (fwA q r) := fw_coprime_A_dprod q r U hUsub
            congr 1
            exact fw_copr_multiples_sum q r (fwDprod U) W hd0 hAd

/-- `φ(A)/A ≥ 0`. -/
private lemma fw_ratio_nonneg (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    0 ≤ ((fwA q r).totient : ℝ) / (fwA q r : ℝ) := by
  positivity

/-- `γ_U ≥ 0`. -/
private lemma fwGamma_nonneg (q r : ℕ) (U : Finset ℕ) (hU : U ⊆ fwPr q r) : 0 ≤ fwGamma q r U := by
  classical
  dsimp [fwGamma]
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro p hp
    have hpp : p.Prime := fwPr_prime q r p (hU hp)
    have hp2 : 2 ≤ p := hpp.two_le
    dsimp [fwDp]
    exact div_nonneg (by norm_num) (by positivity)
  · apply Finset.prod_nonneg
    intro p hp
    have hpS : p ∈ (fwPr q r) := (Finset.mem_sdiff.mp hp).1
    have hpp : p.Prime := fwPr_prime q r p hpS
    have hp2 : 2 ≤ p := hpp.two_le
    dsimp [fwCp]
    exact div_nonneg (by positivity) (by positivity)

/-- `(x/d : ℕ) ≤ x/d` in reals. -/
private lemma fw_nat_div_le_real (x d : ℕ) : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / (d : ℝ) := by
  exact Nat.cast_div_le (α := ℝ)

/-- per-`U` bound in the weight-sum. -/
private lemma fw_term_le (q r W : ℕ) (U : Finset ℕ) (hq : 0 < q) (hr : 0 < r) (hU : U ⊆ fwPr q r) :
    fwGamma q r U * (((W / fwDprod U : ℕ) : ℝ) * (((fwA q r).totient : ℝ) / (fwA q r : ℝ))) ≤
      fwGamma q r U * (((W : ℝ) * ((∏ p ∈ U, (p : ℝ))⁻¹)) *
        (((fwA q r).totient : ℝ) / (fwA q r : ℝ))) := by
  classical
  have hγ0 : 0 ≤ fwGamma q r U := fwGamma_nonneg q r U hU
  have hφ0 : 0 ≤ ((fwA q r).totient : ℝ) / (fwA q r : ℝ) := fw_ratio_nonneg q r hq hr
  have hx1 : ((W / fwDprod U : ℕ) : ℝ) ≤ (W : ℝ) / (fwDprod U : ℝ) := fw_nat_div_le_real W (fwDprod U)
  have hprod : (W : ℝ) / (fwDprod U : ℝ) = (W : ℝ) * ((∏ p ∈ U, (p : ℝ))⁻¹) := by
    calc
      (W : ℝ) / (fwDprod U : ℝ) = (W : ℝ) * ((fwDprod U : ℝ)⁻¹) := by rw [div_eq_mul_inv]
      _ = (W : ℝ) * ((∏ p ∈ U, (p : ℝ))⁻¹) := by
            congr 1
            dsimp [fwDprod]
            rw [Nat.cast_prod (s := U) (f := fun p : ℕ => p)]
  have hx : ((W / fwDprod U : ℕ) : ℝ) ≤ (W : ℝ) * ((∏ p ∈ U, (p : ℝ))⁻¹) := by
    exact le_trans hx1 (le_of_eq hprod)
  have hm := mul_le_mul_of_nonneg_left hx hγ0
  calc
    fwGamma q r U * (((W / fwDprod U : ℕ) : ℝ) * (((fwA q r).totient : ℝ) / (fwA q r : ℝ)))
        = (fwGamma q r U * ((W / fwDprod U : ℕ) : ℝ)) *
            (((fwA q r).totient : ℝ) / (fwA q r : ℝ)) := by ring
    _ ≤ (fwGamma q r U * ((W : ℝ) * ((∏ p ∈ U, (p : ℝ))⁻¹))) *
            (((fwA q r).totient : ℝ) / (fwA q r : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hm hφ0
    _ = fwGamma q r U * (((W : ℝ) * ((∏ p ∈ U, (p : ℝ))⁻¹)) *
            (((fwA q r).totient : ℝ) / (fwA q r : ℝ))) := by ring

/-- the weight-sum is at most the main term plus `2^ω(A)`. -/
private lemma fw_sumH_bound (q r W : ℕ) (hq : 0 < q) (hr : 0 < r) :
    fwSumLow q r W ≤ (W : ℝ) * ((fwA q r).totient : ℝ) / (fwA q r : ℝ) *
        (∏ p ∈ fwPr q r, (((p : ℝ) - 1) / (p : ℝ))) +
      (2 : ℝ) ^ (fwA q r).primeFactors.card := by
  classical
  let ratio : ℝ := ((fwA q r).totient : ℝ) / (fwA q r : ℝ)
  have hA : 1 ≤ fwA q r := by
    have hpos : 0 < fwA q r := fwA_pos q r hq hr
    omega
  have hγ0 : ∀ U ∈ (fwPr q r).powerset, 0 ≤ fwGamma q r U := by
    intro U hU
    exact fwGamma_nonneg q r U (Finset.mem_powerset.mp hU)
  have hbU : ∀ U ∈ (fwPr q r).powerset,
      fwGamma q r U * (fwCcnt (fwA q r) (W / fwDprod U) : ℝ) ≤
        fwGamma q r U * (((W / fwDprod U : ℕ) : ℝ) * ratio) +
          fwGamma q r U * (2 : ℝ) ^ (fwA q r).primeFactors.card := by
    intro U hU
    have hb := fw_copr_Icc_le q r (W / fwDprod U) hA
    have hm := mul_le_mul_of_nonneg_left hb (hγ0 U hU)
    calc
      fwGamma q r U * (fwCcnt (fwA q r) (W / fwDprod U) : ℝ)
          ≤ fwGamma q r U * (((W / fwDprod U : ℕ) : ℝ) * ratio +
              (2 : ℝ) ^ (fwA q r).primeFactors.card) := by
              simpa [ratio, div_eq_mul_inv, mul_assoc] using hm
      _ = fwGamma q r U * (((W / fwDprod U : ℕ) : ℝ) * ratio) +
          fwGamma q r U * (2 : ℝ) ^ (fwA q r).primeFactors.card := by ring
  have hter : ∀ U ∈ (fwPr q r).powerset,
      fwGamma q r U * (((W / fwDprod U : ℕ) : ℝ) * ratio) ≤
        fwGamma q r U * (((W : ℝ) * ((∏ p ∈ U, (p : ℝ))⁻¹)) * ratio) := by
    intro U hU
    simpa [ratio] using (fw_term_le q r W U hq hr (Finset.mem_powerset.mp hU))
  have hpull : (∑ U ∈ (fwPr q r).powerset,
      fwGamma q r U * (((W : ℝ) * ((∏ p ∈ U, (p : ℝ))⁻¹)) * ratio)) =
      (W : ℝ) * ratio * (∑ U ∈ (fwPr q r).powerset,
        fwGamma q r U * ((∏ p ∈ U, (p : ℝ))⁻¹)) := by
    calc
      (∑ U ∈ (fwPr q r).powerset,
          fwGamma q r U * (((W : ℝ) * ((∏ p ∈ U, (p : ℝ))⁻¹)) * ratio))
          = ∑ U ∈ (fwPr q r).powerset,
              (fwGamma q r U * (W : ℝ) * ((∏ p ∈ U, (p : ℝ))⁻¹)) * ratio := by
              refine Finset.sum_congr rfl ?_
              intro U hU
              ring
      _ = (∑ U ∈ (fwPr q r).powerset,
            fwGamma q r U * (W : ℝ) * ((∏ p ∈ U, (p : ℝ))⁻¹)) * ratio := by
            rw [← Finset.sum_mul]
      _ = ((W : ℝ) * (∑ U ∈ (fwPr q r).powerset,
            fwGamma q r U * ((∏ p ∈ U, (p : ℝ))⁻¹))) * ratio := by
            congr 1
            have hW : (∑ U ∈ (fwPr q r).powerset,
                fwGamma q r U * (W : ℝ) * ((∏ p ∈ U, (p : ℝ))⁻¹)) =
                (W : ℝ) * (∑ U ∈ (fwPr q r).powerset,
                  fwGamma q r U * ((∏ p ∈ U, (p : ℝ))⁻¹)) := by
              calc
                (∑ U ∈ (fwPr q r).powerset,
                    fwGamma q r U * (W : ℝ) * ((∏ p ∈ U, (p : ℝ))⁻¹))
                    = ∑ U ∈ (fwPr q r).powerset,
                        (W : ℝ) * (fwGamma q r U * ((∏ p ∈ U, (p : ℝ))⁻¹)) := by
                        refine Finset.sum_congr rfl ?_
                        intro U hU
                        ring
                _ = (W : ℝ) * (∑ U ∈ (fwPr q r).powerset,
                        fwGamma q r U * ((∏ p ∈ U, (p : ℝ))⁻¹)) := by
                        rw [← Finset.mul_sum]
            exact hW
      _ = (W : ℝ) * ratio * (∑ U ∈ (fwPr q r).powerset,
            fwGamma q r U * ((∏ p ∈ U, (p : ℝ))⁻¹)) := by ring
  calc
    fwSumLow q r W
        = ∑ U ∈ (fwPr q r).powerset,
            fwGamma q r U * (fwCcnt (fwA q r) (W / fwDprod U) : ℝ) := fw_sumH_expand q r W
    _ ≤ ∑ U ∈ (fwPr q r).powerset,
            (fwGamma q r U * (((W / fwDprod U : ℕ) : ℝ) * ratio) +
              fwGamma q r U * (2 : ℝ) ^ (fwA q r).primeFactors.card) := by
            exact Finset.sum_le_sum (fun U hU => hbU U hU)
    _ = ∑ U ∈ (fwPr q r).powerset,
            (fwGamma q r U * (((W / fwDprod U : ℕ) : ℝ) * ratio)) +
          (2 : ℝ) ^ (fwA q r).primeFactors.card := by
            rw [Finset.sum_add_distrib]
            have hsum1 : (∑ U ∈ (fwPr q r).powerset, fwGamma q r U * (2 : ℝ) ^ (fwA q r).primeFactors.card) =
                (2 : ℝ) ^ (fwA q r).primeFactors.card := by
              calc
                (∑ U ∈ (fwPr q r).powerset, fwGamma q r U * (2 : ℝ) ^ (fwA q r).primeFactors.card)
                    = (∑ U ∈ (fwPr q r).powerset, fwGamma q r U) *
                        (2 : ℝ) ^ (fwA q r).primeFactors.card := by
                        rw [← Finset.sum_mul]
                _ = (2 : ℝ) ^ (fwA q r).primeFactors.card := by
                        have hg : (∑ U ∈ (fwPr q r).powerset, fwGamma q r U) = 1 := by
                          simpa [fwGamma] using (fw_sum_gamma_eq_one (fwPr q r) (fun p hp => fwPr_prime q r p hp))
                        rw [hg]
                        ring
            rw [hsum1]
    _ ≤ ∑ U ∈ (fwPr q r).powerset,
            (fwGamma q r U * (((W : ℝ) * ((∏ p ∈ U, (p : ℝ))⁻¹)) * ratio)) +
          (2 : ℝ) ^ (fwA q r).primeFactors.card := by
            have hS : (∑ U ∈ (fwPr q r).powerset,
                fwGamma q r U * (((W / fwDprod U : ℕ) : ℝ) * ratio)) ≤
                (∑ U ∈ (fwPr q r).powerset,
                  fwGamma q r U * (((W : ℝ) * ((∏ p ∈ U, (p : ℝ))⁻¹)) * ratio)) :=
              Finset.sum_le_sum (fun U hU => hter U hU)
            linarith
    _ = (W : ℝ) * ratio * (∑ U ∈ (fwPr q r).powerset,
            fwGamma q r U * ((∏ p ∈ U, (p : ℝ))⁻¹)) +
          (2 : ℝ) ^ (fwA q r).primeFactors.card := by
            rw [hpull]
    _ = (W : ℝ) * ((fwA q r).totient : ℝ) / (fwA q r : ℝ) *
            (∏ p ∈ fwPr q r, (((p : ℝ) - 1) / (p : ℝ))) +
          (2 : ℝ) ^ (fwA q r).primeFactors.card := by
            dsimp [ratio]
            have hgd : (∑ U ∈ (fwPr q r).powerset,
                fwGamma q r U * ((∏ p ∈ U, (p : ℝ))⁻¹)) =
                ∏ p ∈ fwPr q r, (((p : ℝ) - 1) / (p : ℝ)) := by
              simpa [fwGamma] using (fw_sum_gamma_div_dprod (fwPr q r) (fun p hp => fwPr_prime q r p hp))
            rw [hgd]
            ring

/-- The general-case bound (g ≥ 2, disjoint window). -/
private lemma fw_general_bound (q r W : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hW : 2 * W + 1 ≤ q * r / (q.gcd r)) (hg : 2 ≤ q.gcd r) :
    (((fwPQ q r).filter (fwP q r W)).card : ℝ) ≤
      2 * (W : ℝ) * ((q.gcd r).totient : ℝ) * ((fwA q r).totient : ℝ) / (fwA q r : ℝ) *
        (∏ p ∈ fwPr q r, (((p : ℝ) - 1) / (p : ℝ))) +
      ((q.gcd r).totient : ℝ) * ((2 : ℝ) ^ ((fwA q r).primeFactors.card + 1) + 1) := by
  classical
  let B : ℝ := (W : ℝ) * ((fwA q r).totient : ℝ) / (fwA q r : ℝ) *
        (∏ p ∈ fwPr q r, (((p : ℝ) - 1) / (p : ℝ)))
  let Pw : ℝ := (2 : ℝ) ^ (fwA q r).primeFactors.card
  have hφ0 : 0 ≤ ((q.gcd r).totient : ℝ) := by exact_mod_cast Nat.zero_le _
  have h0 : fwH q r 0 ≤ 1 := by
    rw [fwH_zero q r]
    by_cases hA1 : fwA q r = 1 <;> simp [hA1]
  have hbnd := fw_sumH_bound q r W hq hr
  calc
    (((fwPQ q r).filter (fwP q r W)).card : ℝ)
        = ((q.gcd r).totient : ℝ) * (fwH q r 0 + 2 * fwSumLow q r W) :=
            fw_card_eq_low q r W hq hr hW
    _ ≤ ((q.gcd r).totient : ℝ) * (1 + 2 * fwSumLow q r W) := by
            have hadd : fwH q r 0 + 2 * fwSumLow q r W ≤ 1 + 2 * fwSumLow q r W := by
              linarith
            exact mul_le_mul_of_nonneg_left hadd hφ0
    _ ≤ ((q.gcd r).totient : ℝ) * (1 + 2 * (B + Pw)) := by
            have hs : fwSumLow q r W ≤ B + Pw := by
              simpa [B, Pw] using hbnd
            have hm2 : 2 * fwSumLow q r W ≤ 2 * (B + Pw) := by
              nlinarith
            have hadd : 1 + 2 * fwSumLow q r W ≤ 1 + 2 * (B + Pw) := by linarith
            exact mul_le_mul_of_nonneg_left hadd hφ0
    _ = ((q.gcd r).totient : ℝ) * (1 + 2 * B + 2 * Pw) := by ring
    _ = ((q.gcd r).totient : ℝ) * (1 + 2 * Pw) + ((q.gcd r).totient : ℝ) * 2 * B := by ring
    _ = ((q.gcd r).totient : ℝ) * ((2 : ℝ) ^ ((fwA q r).primeFactors.card + 1) + 1) +
        2 * (W : ℝ) * ((q.gcd r).totient : ℝ) * ((fwA q r).totient : ℝ) / (fwA q r : ℝ) *
          (∏ p ∈ fwPr q r, (((p : ℝ) - 1) / (p : ℝ))) := by
            have hpow : 2 * Pw = (2 : ℝ) ^ ((fwA q r).primeFactors.card + 1) := by
              dsimp [Pw]
              rw [pow_succ']
            rw [hpow]
            dsimp [B]
            ring
    _ = 2 * (W : ℝ) * ((q.gcd r).totient : ℝ) * ((fwA q r).totient : ℝ) / (fwA q r : ℝ) *
        (∏ p ∈ fwPr q r, (((p : ℝ) - 1) / (p : ℝ))) +
      ((q.gcd r).totient : ℝ) * ((2 : ℝ) ^ ((fwA q r).primeFactors.card + 1) + 1) := by ring

/-- main-term equality from the coefficient identity. -/
private lemma fw_main_term_eq (q r W : ℕ) (hq : 0 < q) (hr : 0 < r) :
    2 * (W : ℝ) * ((q.gcd r).totient : ℝ) * ((fwA q r).totient : ℝ) / (fwA q r : ℝ) *
        (∏ p ∈ fwPr q r, (((p : ℝ) - 1) / (p : ℝ))) =
      2 * (W : ℝ) * ((q.totient * r.totient : ℕ) : ℝ) / ((q * r / (q.gcd r) : ℕ) : ℝ) := by
  classical
  have hc := fw_coeff_eq q r hq hr
  calc
    2 * (W : ℝ) * ((q.gcd r).totient : ℝ) * ((fwA q r).totient : ℝ) / (fwA q r : ℝ) *
        (∏ p ∈ fwPr q r, (((p : ℝ) - 1) / (p : ℝ)))
        = 2 * (W : ℝ) * (((q.gcd r).totient : ℝ) * ((fwA q r).totient : ℝ) /
            (fwA q r : ℝ) * (∏ p ∈ fwPr q r, (((p : ℝ) - 1) / (p : ℝ)))) := by ring
    _ = 2 * (W : ℝ) * ((q.totient : ℝ) * (r.totient : ℝ) / ((q * r / (q.gcd r) : ℕ) : ℝ)) := by
            rw [← hc]
    _ = 2 * (W : ℝ) * ((q.totient * r.totient : ℕ) : ℝ) / ((q * r / (q.gcd r) : ℕ) : ℝ) := by
            rw [Nat.cast_mul]
            ring

/-- the general case, in the final form. -/
private lemma fw_general_goal (q r W : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hW : 2 * W + 1 ≤ q * r / (q.gcd r)) (hg : 2 ≤ q.gcd r) :
    (((fwPQ q r).filter (fwP q r W)).card : ℝ) ≤
      (2 * (W : ℝ) * ((q.totient * r.totient : ℕ) : ℝ) / ((q * r / (q.gcd r) : ℕ) : ℝ)) +
      (((q.gcd r).totient : ℕ) : ℝ) * (((q * r / ((q.gcd r) * (q.gcd r))).divisors.card : ℕ) : ℝ) *
        (3 : ℝ) ^ (q.gcd r).primeFactors.card := by
  classical
  have hA : 1 ≤ fwA q r := by
    have hpos : 0 < fwA q r := fwA_pos q r hq hr
    omega
  have hb := fw_general_bound q r W hq hr hW hg
  have hmain := fw_main_term_eq q r W hq hr
  have herr := fw_err_le q r hg hA
  calc
    (((fwPQ q r).filter (fwP q r W)).card : ℝ)
        ≤ 2 * (W : ℝ) * ((q.gcd r).totient : ℝ) * ((fwA q r).totient : ℝ) / (fwA q r : ℝ) *
            (∏ p ∈ fwPr q r, (((p : ℝ) - 1) / (p : ℝ))) +
          ((q.gcd r).totient : ℝ) * ((2 : ℝ) ^ ((fwA q r).primeFactors.card + 1) + 1) := hb
    _ = 2 * (W : ℝ) * ((q.totient * r.totient : ℕ) : ℝ) / ((q * r / (q.gcd r) : ℕ) : ℝ) +
          ((q.gcd r).totient : ℝ) * ((2 : ℝ) ^ ((fwA q r).primeFactors.card + 1) + 1) := by
            rw [hmain]
    _ ≤ 2 * (W : ℝ) * ((q.totient * r.totient : ℕ) : ℝ) / ((q * r / (q.gcd r) : ℕ) : ℝ) +
          (((q.gcd r).totient : ℕ) : ℝ) * (((q * r / ((q.gcd r) * (q.gcd r))).divisors.card : ℕ) : ℝ) *
            (3 : ℝ) ^ (q.gcd r).primeFactors.card := by
            exact add_le_add_right herr (2 * (W : ℝ) * ((q.totient * r.totient : ℕ) : ℝ) /
              ((q * r / (q.gcd r) : ℕ) : ℝ))

/-- trivial case `q = 0`: card is `0` and the right-hand side vanishes. -/
private lemma fw_triv_left (q r W : ℕ) (hq : q = 0) :
    (((fwPQ q r).filter (fwP q r W)).card : ℝ) ≤
      (2 * (W : ℝ) * ((q.totient * r.totient : ℕ) : ℝ) / ((q * r / (q.gcd r) : ℕ) : ℝ)) +
      (((q.gcd r).totient : ℕ) : ℝ) * (((q * r / ((q.gcd r) * (q.gcd r))).divisors.card : ℕ) : ℝ) *
        (3 : ℝ) ^ (q.gcd r).primeFactors.card := by
  classical
  subst q
  have hcard : (((fwPQ 0 r).filter (fwP 0 r W)).card : ℝ) = 0 := by
    dsimp [fwPQ]
    simp
  have hmain : (2 * (W : ℝ) * ((Nat.totient 0 * r.totient : ℕ) : ℝ) /
      ((0 * r / (Nat.gcd 0 r) : ℕ) : ℝ)) = 0 := by
    have hnum : ((Nat.totient 0 * r.totient : ℕ) : ℝ) = 0 := by
      simp [Nat.totient_zero]
    rw [hnum]
    ring
  have herr : (((Nat.gcd 0 r).totient : ℕ) : ℝ) *
      (((0 * r / ((Nat.gcd 0 r) * (Nat.gcd 0 r))).divisors.card : ℕ) : ℝ) *
        (3 : ℝ) ^ (Nat.gcd 0 r).primeFactors.card = 0 := by
    have hτ : ((0 * r / ((Nat.gcd 0 r) * (Nat.gcd 0 r))).divisors.card : ℕ) = 0 := by
      simp [Nat.divisors_zero]
    rw [hτ]
    ring
  rw [hcard, hmain, herr]
  norm_num

/-- trivial case `r = 0`: card is `0` and the right-hand side vanishes. -/
private lemma fw_triv_right (q r W : ℕ) (hr : r = 0) :
    (((fwPQ q r).filter (fwP q r W)).card : ℝ) ≤
      (2 * (W : ℝ) * ((q.totient * r.totient : ℕ) : ℝ) / ((q * r / (q.gcd r) : ℕ) : ℝ)) +
      (((q.gcd r).totient : ℕ) : ℝ) * (((q * r / ((q.gcd r) * (q.gcd r))).divisors.card : ℕ) : ℝ) *
        (3 : ℝ) ^ (q.gcd r).primeFactors.card := by
  classical
  subst r
  have hcard : (((fwPQ q 0).filter (fwP q 0 W)).card : ℝ) = 0 := by
    dsimp [fwPQ]
    simp
  have hmain : (2 * (W : ℝ) * ((q.totient * Nat.totient 0 : ℕ) : ℝ) /
      ((q * 0 / (q.gcd 0) : ℕ) : ℝ)) = 0 := by
    have hnum : ((q.totient * Nat.totient 0 : ℕ) : ℝ) = 0 := by
      simp [Nat.totient_zero]
    rw [hnum]
    ring
  have herr : (((q.gcd 0).totient : ℕ) : ℝ) *
      (((q * 0 / ((q.gcd 0) * (q.gcd 0))).divisors.card : ℕ) : ℝ) *
        (3 : ℝ) ^ (q.gcd 0).primeFactors.card = 0 := by
    have hτ : ((q * 0 / ((q.gcd 0) * (q.gcd 0))).divisors.card : ℕ) = 0 := by
      simp [Nat.divisors_zero]
    rw [hτ]
    ring
  rw [hcard, hmain, herr]
  norm_num

/-- case `2W ≥ L`: every pair satisfies the window condition, so `card ≤ φ(q)φ(r)`.
We prove directly the full inequality. -/
private lemma fw_largeW_goal (q r W : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hW : q * r / (q.gcd r) ≤ 2 * W) :
    (((fwPQ q r).filter (fwP q r W)).card : ℝ) ≤
      (2 * (W : ℝ) * ((q.totient * r.totient : ℕ) : ℝ) / ((q * r / (q.gcd r) : ℕ) : ℝ)) +
      (((q.gcd r).totient : ℕ) : ℝ) * (((q * r / ((q.gcd r) * (q.gcd r))).divisors.card : ℕ) : ℝ) *
        (3 : ℝ) ^ (q.gcd r).primeFactors.card := by
  classical
  have hLpos : 0 < q * r / (q.gcd r) := fw_L_pos q r hq hr
  have hcard : (((fwPQ q r).filter (fwP q r W)).card : ℝ) ≤
      ((q.totient * r.totient : ℕ) : ℝ) := by
    have hle : (fwPQ q r).filter (fwP q r W) ⊆ fwPQ q r := Finset.filter_subset _ _
    have hcard' : ((fwPQ q r).filter (fwP q r W)).card ≤ (fwPQ q r).card :=
      Finset.card_le_card hle
    have hpq : (fwPQ q r).card = q.totient * r.totient := by
      dsimp [fwPQ]
      rw [Finset.card_product]
      congr 1
      · change (redMod q).card = q.totient
        exact card_redMod q
      · change (redMod r).card = r.totient
        exact card_redMod r
    have hle2 : ((fwPQ q r).filter (fwP q r W)).card ≤ q.totient * r.totient := by
      simpa [hpq] using hcard'
    exact_mod_cast hle2
  -- main-term ≥ φ(q)φ(r) because 2W ≥ L
  have hL1 : 1 ≤ (q * r / (q.gcd r) : ℕ) := hLpos
  have hratio : (1 : ℝ) ≤ (2 * (W : ℝ)) / ((q * r / (q.gcd r) : ℕ) : ℝ) := by
    have hc : ((q * r / (q.gcd r) : ℕ) : ℝ) ≤ (2 * (W : ℝ)) := by
      exact_mod_cast hW
    have hL0 : 0 < ((q * r / (q.gcd r) : ℕ) : ℝ) := by exact_mod_cast hLpos
    rw [le_div_iff₀ hL0]
    simpa using hc
  have hmul : ((q.totient * r.totient : ℕ) : ℝ) ≤
      (2 * (W : ℝ)) * ((q.totient * r.totient : ℕ) : ℝ) / ((q * r / (q.gcd r) : ℕ) : ℝ) := by
    have hφ0 : 0 ≤ ((q.totient * r.totient : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
    have hm : ((q.totient * r.totient : ℕ) : ℝ) * 1 ≤
        ((q.totient * r.totient : ℕ) : ℝ) * ((2 * (W : ℝ)) / ((q * r / (q.gcd r) : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio hφ0
    -- need ((φφ) · (2W/L)) = (2W · φφ)/L
    calc
      ((q.totient * r.totient : ℕ) : ℝ)
          = ((q.totient * r.totient : ℕ) : ℝ) * 1 := by ring
      _ ≤ ((q.totient * r.totient : ℕ) : ℝ) * ((2 * (W : ℝ)) / ((q * r / (q.gcd r) : ℕ) : ℝ)) := hm
      _ = (2 * (W : ℝ)) * ((q.totient * r.totient : ℕ) : ℝ) / ((q * r / (q.gcd r) : ℕ) : ℝ) := by
            ring
  have herr0 : 0 ≤ (((q.gcd r).totient : ℕ) : ℝ) *
      (((q * r / ((q.gcd r) * (q.gcd r))).divisors.card : ℕ) : ℝ) *
        (3 : ℝ) ^ (q.gcd r).primeFactors.card := by positivity
  linarith

/-! ## Coprime case: `q ⊥ r` -/

/-- under `gcd q r = 1`, `L = q·r`. -/
private lemma fw_coprime_L (q r : ℕ) (hg : q.gcd r = 1) : q * r / (q.gcd r) = q * r := by
  rw [hg]
  exact Nat.div_one (q * r)

/-- under `gcd q r = 1`, `Q = q`. -/
private lemma fw_coprime_Q (q r : ℕ) (hg : q.gcd r = 1) : q / q.gcd r = q := by
  rw [hg]
  exact Nat.div_one q

/-- under `gcd q r = 1`, `R = r`. -/
private lemma fw_coprime_R (q r : ℕ) (hg : q.gcd r = 1) : r / q.gcd r = r := by
  rw [hg]
  exact Nat.div_one r

/-- under `gcd q r = 1`, `A = q·r`. -/
private lemma fw_coprime_A (q r : ℕ) (hg : q.gcd r = 1) : fwA q r = q * r := by
  dsimp [fwA]
  rw [fw_coprime_Q q r hg, fw_coprime_R q r hg]

/-- the value residue of a reduced pair is congruent to `a·r ≡ b·q + t (mod q·r)`. -/
private lemma fw_coprime_val_congr (q r t a b : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hg : q.gcd r = 1) (ha : a < q) (hb : b < r) (ht : t < q * r) :
    fwVal q r (a, b) = t → (a * r) % (q * r) = ((b * q + t) % (q * r)) := by
  classical
  intro hv
  let L : ℕ := q * r
  have hL0 : 0 < L := by
    dsimp [L]
    exact mul_pos hq hr
  have hx : a * r < L := by
    dsimp [L]
    exact Nat.mul_lt_mul_of_pos_right ha hr
  have hy : b * q < L := by
    dsimp [L]
    calc
      b * q < r * q := Nat.mul_lt_mul_of_pos_right hb hq
      _ = q * r := by rw [mul_comm]
  have hval : fwVal q r (a, b) =
      ((a * r) % L + L - (b * q) % L) % L := by
    dsimp [fwVal]
    rw [fw_coprime_Q q r hg, fw_coprime_R q r hg, fw_coprime_L q r hg]
  -- since a·r, b·q < L the inner % reduce to themselves
  have hx' : (a * r) % L = a * r := Nat.mod_eq_of_lt hx
  have hy' : (b * q) % L = b * q := Nat.mod_eq_of_lt hy
  rw [hval, hx', hy'] at hv
  have himp := fw_sub_mod_imp (a * r) (b * q) t L hL0 hx hy ht
  have hcon : (a * r) % L = ((b * q + t) % L) := himp hv
  dsimp [L] at hcon
  simpa using hcon

/-- the fibre at `t` contains at most one pair, and only if `t ⊥ q·r`. -/
private lemma fw_fib_coprime_le (q r t : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hg : q.gcd r = 1) (ht : t < q * r) :
    ((fwFib q r t) : ℝ) ≤ (if t.gcd (q * r) = 1 then (1 : ℝ) else 0) := by
  classical
  let S : Finset (ℕ × ℕ) :=
    ((Finset.product (Finset.range q) (Finset.range r)).filter
      (fun mn : ℕ × ℕ => mn.1.gcd q = 1 ∧ mn.2.gcd r = 1 ∧
        (mn.1 * r) % (q * r) = ((mn.2 * q + t) % (q * r))))
  have hsubset : (fwPQ q r).filter (fun mn : ℕ × ℕ => fwVal q r mn = t) ⊆ S := by
    intro mn hmn
    rcases mn with ⟨a, b⟩
    have hmem' := Finset.mem_filter.mp hmn
    have hpq : (a, b) ∈ fwPQ q r := hmem'.1
    have hv : fwVal q r (a, b) = t := hmem'.2
    have hpq' : a ∈ (Finset.range q).filter (fun m : ℕ => m.gcd q = 1) ∧
                b ∈ (Finset.range r).filter (fun n : ℕ => n.gcd r = 1) := by
      simpa [fwPQ] using (Finset.mem_product.mp hpq)
    have ha' : a ∈ Finset.range q ∧ a.gcd q = 1 := Finset.mem_filter.mp hpq'.1
    have hb' : b ∈ Finset.range r ∧ b.gcd r = 1 := Finset.mem_filter.mp hpq'.2
    have ha : a < q := Finset.mem_range.mp ha'.1
    have ha1 : a.gcd q = 1 := ha'.2
    have hb : b < r := Finset.mem_range.mp hb'.1
    have hb1 : b.gcd r = 1 := hb'.2
    have hcong := fw_coprime_val_congr q r t a b hq hr hg ha hb ht hv
    dsimp [S]
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨Finset.mem_range.mpr ha, Finset.mem_range.mpr hb⟩, ⟨ha1, hb1, hcong⟩⟩
  have hcardS : S.card = if t.gcd (q * r) = 1 then 1 else 0 := by
    have hcop : Nat.Coprime q r := by
      rwa [Nat.coprime_iff_gcd_eq_one]
    have hc := Commons.NumberTheory.DuffinSchaeffer.reduced_pair_coprime_fiber q r t hq hr hcop
    dsimp [S]
    simpa using hc
  calc
    ((fwFib q r t) : ℝ)
        = (((fwPQ q r).filter (fun mn : ℕ × ℕ => fwVal q r mn = t)).card : ℝ) := by
            dsimp [fwFib]
    _ ≤ (S.card : ℝ) := by
            exact_mod_cast (Finset.card_le_card hsubset)
    _ = (if t.gcd (q * r) = 1 then (1 : ℝ) else 0) := by
            rw [hcardS]
            by_cases h1 : t.gcd (q * r) = 1 <;> simp [h1]

/-- the coprime indicator `[gcd(t, q·r) = 1]` (as a real). -/
private noncomputable def fwCind (q r t : ℕ) : ℝ :=
  if t.gcd (q * r) = 1 then (1 : ℝ) else 0

/-- `fwCind(q,r,0) = [q·r = 1]`. -/
private lemma fwCind_zero (q r : ℕ) : fwCind q r 0 = (if q * r = 1 then (1 : ℝ) else 0) := by
  classical
  dsimp [fwCind]
  by_cases h1 : q * r = 1
  · have hg : Nat.gcd 0 (q * r) = 1 := by rw [h1]; simp
    rw [if_pos h1, if_pos hg]
  · have hg : ¬ Nat.gcd 0 (q * r) = 1 := by
      intro hz
      apply h1
      have hg : Nat.gcd 0 (q * r) = q * r := by simp
      rwa [hg] at hz
    rw [if_neg h1, if_neg hg]

/-- reflection: `gcd(q·r − s, q·r) = gcd(s, q·r)`. -/
private lemma fwCind_reflect (q r s : ℕ) (hs : s ≤ q * r) :
    fwCind q r ((q * r) - s) = fwCind q r s := by
  classical
  dsimp [fwCind]
  have hg : Nat.gcd ((q * r) - s) (q * r) = s.gcd (q * r) := by
    -- gcd(a − s, a) = gcd(s, a) when a := q·r: use fw_gcd_sub_eq_gcd with A := q·r: but A | a: needs A | a with a = A: trivially a | a
    exact fw_gcd_sub_eq_gcd (q * r) (q * r) s (dvd_refl (q * r)) hs
  by_cases h1 : s.gcd (q * r) = 1
  · have h2 : Nat.gcd ((q * r) - s) (q * r) = 1 := by rw [hg, h1]
    rw [if_pos h2, if_pos h1]
  · have h2 : ¬ Nat.gcd ((q * r) - s) (q * r) = 1 := by
      intro hz
      apply h1
      rwa [hg] at hz
    rw [if_neg h2, if_neg h1]

/-- generic reindex of the upper window `[N−W, N−1]` to `[1,W]`. -/
private lemma fw_sum_up_reflect (N W : ℕ) (F : ℕ → ℝ) (hN : 1 ≤ N)
    (hW : 2 * W + 1 ≤ N) (hrefl : ∀ s : ℕ, s ≤ N → F (N - s) = F s) :
    (∑ t ∈ Finset.Icc (N - W) (N - 1), F t) = ∑ s ∈ Finset.Icc 1 W, F s := by
  classical
  calc
    (∑ t ∈ Finset.Icc (N - W) (N - 1), F t)
        = ∑ t ∈ Finset.Icc (N - W) (N - 1), F (N - t) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            have htle : t ≤ N := by
              have ht' := Finset.mem_Icc.mp ht
              omega
            exact (hrefl t htle).symm
    _ = ∑ s ∈ Finset.Icc 1 W, F s := by
            refine Finset.sum_bij (fun t ht => N - t) ?_ ?_ ?_ ?_
            · intro t ht
              have ht' := Finset.mem_Icc.mp ht
              rw [Finset.mem_Icc]
              exact ⟨by omega, by omega⟩
            · intro t1 ht1 t2 ht2 hEq
              have h1 : t1 ≤ N := by
                have h := Finset.mem_Icc.mp ht1
                omega
              have h2 : t2 ≤ N := by
                have h := Finset.mem_Icc.mp ht2
                omega
              omega
            · intro s hs
              have hs' := Finset.mem_Icc.mp hs
              refine ⟨N - s, ?_, ?_⟩
              · rw [Finset.mem_Icc]
                exact ⟨by omega, by omega⟩
              · omega
            · intro t ht
              rfl


/-- bound of the window count by the coprime indicators. -/
private lemma fw_card_coprime_le (q r W : ℕ) (hq : 0 < q) (hr : 0 < r) (hg : q.gcd r = 1)
    (hW : 2 * W + 1 ≤ q * r / (q.gcd r)) :
    (((fwPQ q r).filter (fwP q r W)).card : ℝ) ≤
      (∑ t ∈ Finset.Icc 0 W, fwCind q r t) +
      (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1), fwCind q r t) := by
  classical
  have hW' : 2 * W + 1 ≤ q * r := by
    rw [fw_coprime_L q r hg] at hW
    exact hW
  have htL0 : ∀ t ∈ Finset.Icc 0 W, t < q * r := by
    intro t ht
    have htW : t ≤ W := (Finset.mem_Icc.mp ht).2
    omega
  have htL1 : ∀ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1),
      t < q * r := by
    intro t ht
    have hthi : t ≤ (q * r / (q.gcd r)) - 1 := (Finset.mem_Icc.mp ht).2
    rw [fw_coprime_L q r hg] at hthi
    omega
  have hfib0 : ∀ t ∈ Finset.Icc 0 W, ((fwFib q r t : ℕ) : ℝ) ≤ fwCind q r t := by
    intro t ht
    exact fw_fib_coprime_le q r t hq hr hg (htL0 t ht)
  have hfib1 : ∀ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1),
      ((fwFib q r t : ℕ) : ℝ) ≤ fwCind q r t := by
    intro t ht
    exact fw_fib_coprime_le q r t hq hr hg (htL1 t ht)
  have hcast : (((fwPQ q r).filter (fwP q r W)).card : ℝ) =
      (∑ t ∈ Finset.Icc 0 W, ((fwFib q r t : ℕ) : ℝ)) +
      (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1),
        ((fwFib q r t : ℕ) : ℝ)) := by
    have hcardN := fw_card_filter_P q r W hq hr hW
    change ((fwPQ q r).filter (fwP q r W)).card =
        (∑ t ∈ Finset.Icc 0 W, (fwFib q r t : ℕ)) +
        (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1),
          (fwFib q r t : ℕ)) at hcardN
    exact_mod_cast hcardN
  calc
    (((fwPQ q r).filter (fwP q r W)).card : ℝ)
        = (∑ t ∈ Finset.Icc 0 W, ((fwFib q r t : ℕ) : ℝ)) +
          (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1),
            ((fwFib q r t : ℕ) : ℝ)) := hcast
    _ ≤ (∑ t ∈ Finset.Icc 0 W, fwCind q r t) +
          (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1),
            fwCind q r t) := by
            exact add_le_add (Finset.sum_le_sum (fun t ht => hfib0 t ht))
              (Finset.sum_le_sum (fun t ht => hfib1 t ht))

/-- the two indicator windows equal `[q·r=1] + 2·Σ_{[1,W]}`. -/
private lemma fw_ind_sum_eq (q r W : ℕ) (hq : 0 < q) (hr : 0 < r) (hg : q.gcd r = 1)
    (hW : 2 * W + 1 ≤ q * r) :
    (∑ t ∈ Finset.Icc 0 W, fwCind q r t) +
      (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1), fwCind q r t)
      = (if q * r = 1 then (1 : ℝ) else 0) + 2 * (∑ s ∈ Finset.Icc 1 W, fwCind q r s) := by
  classical
  have hIcc : Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1) =
      Finset.Icc ((q * r) - W) ((q * r) - 1) := by
    rw [fw_coprime_L q r hg]
  have hN : 1 ≤ q * r := by
    have hm := mul_pos hq hr
    omega
  have hup := fw_sum_up_reflect (q * r) W (fwCind q r) hN hW (fwCind_reflect q r)
  calc
    (∑ t ∈ Finset.Icc 0 W, fwCind q r t) +
      (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1), fwCind q r t)
        = (fwCind q r 0 + ∑ s ∈ Finset.Icc 1 W, fwCind q r s) +
          (∑ t ∈ Finset.Icc ((q * r) - W) ((q * r) - 1), fwCind q r t) := by
            rw [fw_sum_Icc0 W (fun t : ℕ => fwCind q r t), hIcc]
    _ = (fwCind q r 0 + ∑ s ∈ Finset.Icc 1 W, fwCind q r s) +
          (∑ s ∈ Finset.Icc 1 W, fwCind q r s) := by
            rw [hup]
    _ = (if q * r = 1 then (1 : ℝ) else 0) + 2 * (∑ s ∈ Finset.Icc 1 W, fwCind q r s) := by
            rw [fwCind_zero q r]
            ring

/-- `Σ_{[1,W]} [gcd(s,q·r)=1] ≤ W·φ(qr)/(qr) + 2^{ω(qr)−1}` for `2 ≤ q·r`. -/
private lemma fw_coprime_count_bound (q r W : ℕ) (hqr : 2 ≤ q * r) :
    (∑ s ∈ Finset.Icc 1 W, fwCind q r s) ≤ (W : ℝ) * ((Nat.totient (q * r) : ℝ) / (q * r : ℝ)) +
      (2 : ℝ) ^ ((q * r).primeFactors.card - 1) := by
  classical
  have hb := Commons.NumberTheory.Totient.coprime_interval_count_le (q * r) W hqr
  calc
    (∑ s ∈ Finset.Icc 1 W, fwCind q r s)
        = (((Finset.Icc 1 W).filter (fun s : ℕ => s.gcd (q * r) = 1)).card : ℝ) := by
            dsimp [fwCind]
            rw [Finset.sum_boole]
    _ ≤ (W : ℝ) * ((Nat.totient (q * r) : ℝ) / (q * r : ℝ)) +
          (2 : ℝ) ^ ((q * r).primeFactors.card - 1) := by
            simpa [div_eq_mul_inv, mul_assoc] using hb


/-- The coprime case (`gcd q r = 1`), in the final form. -/
private lemma fw_coprime_goal (q r W : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hW : 2 * W + 1 ≤ q * r / (q.gcd r)) (hg : q.gcd r = 1) :
    (((fwPQ q r).filter (fwP q r W)).card : ℝ) ≤
      (2 * (W : ℝ) * ((q.totient * r.totient : ℕ) : ℝ) / ((q * r / (q.gcd r) : ℕ) : ℝ)) +
      (((q.gcd r).totient : ℕ) : ℝ) * (((q * r / ((q.gcd r) * (q.gcd r))).divisors.card : ℕ) : ℝ) *
        (3 : ℝ) ^ (q.gcd r).primeFactors.card := by
  classical
  by_cases hqr1 : q * r = 1
  · -- q = r = 1, W = 0; card ≤ 1 and RHS = 1
    have hq1 : q = 1 := by
      have h' : r * q = 1 := by rwa [mul_comm]
      exact Nat.eq_one_of_mul_eq_one_left h'
    have hr1 : r = 1 := by
      exact Nat.eq_one_of_mul_eq_one_left hqr1
    have hW0 : W = 0 := by
      rw [hq1, hr1] at hW
      norm_num at hW
      omega
    have hle : (((fwPQ q r).filter (fwP q r W)).card : ℝ) ≤ 1 := by
      rw [hq1, hr1]
      have hsub : (fwPQ 1 1).filter (fwP 1 1 W) ⊆ (fwPQ 1 1) := Finset.filter_subset _ _
      have hle' : ((fwPQ 1 1).filter (fwP 1 1 W)).card ≤ (fwPQ 1 1).card := Finset.card_le_card hsub
      have hf1 : (Finset.range 1).filter (fun m : ℕ => m.gcd 1 = 1) = {0} := by
        ext m
        constructor
        · intro hm
          have hmem := Finset.mem_filter.mp hm
          have hm0 : m = 0 := by
            have hmr : m < 1 := Finset.mem_range.mp hmem.1
            omega
          rw [hm0]
          simp
        · intro hm
          simp [hm]
      have hpq : (fwPQ 1 1).card = 1 := by
        dsimp [fwPQ]
        rw [Finset.card_product]
        simp
      have hle2 : ((fwPQ 1 1).filter (fwP 1 1 W)).card ≤ 1 := by
        rw [hpq] at hle'
        exact hle'
      exact_mod_cast hle2
    have hR : (2 * (W : ℝ) * ((q.totient * r.totient : ℕ) : ℝ) /
          ((q * r / (q.gcd r) : ℕ) : ℝ)) +
        (((q.gcd r).totient : ℕ) : ℝ) * (((q * r / ((q.gcd r) * (q.gcd r))).divisors.card : ℕ) : ℝ) *
          (3 : ℝ) ^ (q.gcd r).primeFactors.card = 1 := by
        rw [hW0, hq1, hr1]
        norm_num
    linarith
  · have hpos : 0 < q * r := mul_pos hq hr
    have hqr2 : 2 ≤ q * r := by omega
    have hW' : 2 * W + 1 ≤ q * r := by
      rw [fw_coprime_L q r hg] at hW
      exact hW
    have hN : 1 ≤ q * r := by omega
    have hcop : Nat.Coprime q r := by rwa [Nat.coprime_iff_gcd_eq_one]
    have hφ : (q * r).totient = q.totient * r.totient := Nat.totient_mul hcop
    have hg1 : (q.gcd r).totient = 1 := by
      rw [hg]
      simp
    have hdiv : q * r / ((q.gcd r) * (q.gcd r)) = q * r := by
      rw [hg]
      norm_num
    have hw3 : (3 : ℝ) ^ (q.gcd r).primeFactors.card = 1 := by
      rw [hg]
      simp
    have hmain : (2 * (W : ℝ) * ((q.totient * r.totient : ℕ) : ℝ) /
          ((q * r / (q.gcd r) : ℕ) : ℝ)) =
        2 * (W : ℝ) * ((Nat.totient (q * r) : ℝ) / (q * r : ℝ)) := by
        have hq0r : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
        have hr0r : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
        rw [← hφ, fw_coprime_L q r hg]
        field_simp [hq0r, hr0r]
        rw [Nat.cast_mul]
        ring_nf
    have herr : ((((q.gcd r).totient : ℕ) : ℝ) *
          (((q * r / ((q.gcd r) * (q.gcd r))).divisors.card : ℕ) : ℝ) *
            (3 : ℝ) ^ (q.gcd r).primeFactors.card) = (((q * r).divisors.card : ℕ) : ℝ) := by
        rw [hg1, hdiv, hw3]
        norm_num
    have h2 : (((fwPQ q r).filter (fwP q r W)).card : ℝ) ≤
        2 * (∑ s ∈ Finset.Icc 1 W, fwCind q r s) := by
        have hb := fw_card_coprime_le q r W hq hr hg hW
        have hs := fw_ind_sum_eq q r W hq hr hg hW'
        have hz : (if q * r = 1 then (1 : ℝ) else 0) = 0 := by
          rw [if_neg hqr1]
        calc
          (((fwPQ q r).filter (fwP q r W)).card : ℝ)
              ≤ (∑ t ∈ Finset.Icc 0 W, fwCind q r t) +
                (∑ t ∈ Finset.Icc ((q * r / (q.gcd r)) - W) ((q * r / (q.gcd r)) - 1), fwCind q r t) := hb
          _ = (if q * r = 1 then (1 : ℝ) else 0) +
                2 * (∑ s ∈ Finset.Icc 1 W, fwCind q r s) := hs
          _ = 2 * (∑ s ∈ Finset.Icc 1 W, fwCind q r s) := by rw [hz]; ring
    have hcnt := fw_coprime_count_bound q r W hqr2
    have h4 : 2 * (∑ s ∈ Finset.Icc 1 W, fwCind q r s) ≤
        2 * (W : ℝ) * ((Nat.totient (q * r) : ℝ) / (q * r : ℝ)) +
          (2 : ℝ) ^ (q * r).primeFactors.card := by
        -- 2·C ≤ 2·(Wφ/qr + 2^{k−1}) = 2Wφ/qr + 2^{k}
        have hk : (q * r).primeFactors.card - 1 + 1 = (q * r).primeFactors.card := by
          have hne : (q * r) ≠ 1 := by omega
          rcases Nat.exists_prime_and_dvd hne with ⟨p, hpP, hpd⟩
          have hω1 : 1 ≤ (q * r).primeFactors.card := by
            have hm : p ∈ (q * r).primeFactors := Nat.mem_primeFactors.mpr ⟨hpP, hpd, by omega⟩
            exact Finset.card_pos.mpr ⟨p, hm⟩
          omega
        have hmul := mul_le_mul_of_nonneg_left hcnt (by norm_num : 0 ≤ (2 : ℝ))
        -- hmul: 2·C ≤ 2·(Wφ/qr + 2^{k−1})
        have hpow : (2 : ℝ) * (2 : ℝ) ^ ((q * r).primeFactors.card - 1) =
            (2 : ℝ) ^ (q * r).primeFactors.card := by
          calc
            (2 : ℝ) * 2 ^ ((q * r).primeFactors.card - 1)
                = 2 ^ ((q * r).primeFactors.card - 1) * (2 : ℝ) := by rw [mul_comm]
            _ = 2 ^ (((q * r).primeFactors.card - 1) + 1) := by rw [← pow_succ]
            _ = 2 ^ (q * r).primeFactors.card := by rw [hk]
        nlinarith
    have hτ : (2 : ℝ) ^ (q * r).primeFactors.card ≤ (((q * r).divisors.card : ℕ) : ℝ) := by
      exact fw_card_divisors_ge_real (q * r) hN
    calc
      (((fwPQ q r).filter (fwP q r W)).card : ℝ)
          ≤ 2 * (W : ℝ) * ((Nat.totient (q * r) : ℝ) / (q * r : ℝ)) +
              (2 : ℝ) ^ (q * r).primeFactors.card := le_trans h2 h4
      _ ≤ 2 * (W : ℝ) * ((Nat.totient (q * r) : ℝ) / (q * r : ℝ)) +
              (((q * r).divisors.card : ℕ) : ℝ) := by
              exact add_le_add_right hτ (2 * (W : ℝ) * ((Nat.totient (q * r) : ℝ) / (q * r : ℝ)))
      _ = (2 * (W : ℝ) * ((q.totient * r.totient : ℕ) : ℝ) /
            ((q * r / (q.gcd r) : ℕ) : ℝ)) +
            ((((q.gcd r).totient : ℕ) : ℝ) *
              (((q * r / ((q.gcd r) * (q.gcd r))).divisors.card : ℕ) : ℝ) *
                (3 : ℝ) ^ (q.gcd r).primeFactors.card) := by
              rw [hmain, herr]

theorem fibre_window_count_le_global (q r W : ℕ) :
    let g : ℕ := q.gcd r
    let L : ℕ := q * r / g
    let Rr : ℕ := r / g
    let Q : ℕ := q / g
    let P : ℕ × ℕ → Prop :=
      fun mn => (((mn.1 * Rr) % L) + L - ((mn.2 * Q) % L)) % L ≤ W ∨
                (((mn.2 * Q) % L) + L - ((mn.1 * Rr) % L)) % L ≤ W
    let PQ : Finset (ℕ × ℕ) :=
      Finset.product ((Finset.range q).filter (fun m : ℕ => m.gcd q = 1))
                     ((Finset.range r).filter (fun n : ℕ => n.gcd r = 1))
    (((PQ.filter P).card : ℝ) ≤
      (2 * (W : ℝ) * ((q.totient * r.totient : ℕ) : ℝ) / (L : ℝ)) +
        ((g.totient : ℕ) : ℝ) * (((q * r / (g * g)).divisors.card : ℕ) : ℝ) * (3 : ℝ) ^ g.primeFactors.card) := by
  classical
  intro g L Rr Q P PQ
  have hLe : L = q * r / (q.gcd r) := rfl
  have hge : g = q.gcd r := rfl
  have hset : PQ.filter P = (fwPQ q r).filter (fwP q r W) := by
    apply Finset.ext
    intro x
    rcases x with ⟨x1, x2⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, g, L, Rr, Q]
    simp only [P, PQ, fwP, fwPQ]
    simp only [Rr, Q, L, g]
  rw [hset]
  rw [hLe, hge]
  by_cases hq : q = 0
  · exact fw_triv_left q r W hq
  · by_cases hr : r = 0
    · exact fw_triv_right q r W hr
    · have hq0 : 0 < q := Nat.pos_of_ne_zero hq
      have hr0 : 0 < r := Nat.pos_of_ne_zero hr
      by_cases hW : 2 * W + 1 ≤ q * r / (q.gcd r)
      · by_cases hg : q.gcd r = 1
        · exact fw_coprime_goal q r W hq0 hr0 hW hg
        · have hg2 : 2 ≤ q.gcd r := by
            have hgpos : 1 ≤ q.gcd r := Nat.succ_le_of_lt (fw_gcd_pos_of_q q r hq0)
            omega
          exact fw_general_goal q r W hq0 hr0 hW hg2
      · have hbig : q * r / (q.gcd r) ≤ 2 * W := by omega
        exact fw_largeW_goal q r W hq0 hr0 hbig

end Commons.NumberTheory.DuffinSchaeffer
