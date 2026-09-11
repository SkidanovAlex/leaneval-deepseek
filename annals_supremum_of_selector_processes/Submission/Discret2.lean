import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ChallengeDeps
import Submission.Multi
import Submission.MultiMass
import Submission.Discret1

/-!
# TASK (child): prove ALL lemmas in this file (no unfinished proofs may remain).  Statements are fixed; you
# may add helper lemmas.  This is the real/measure core of the paper's discretization step.

## SETTING: finite cells C; masses mu : C -> R>=0 (sum <= 1; positive on G's support); N draws
# from the atomic law (mass mu c at c); G a TRIMMED cover multiset: (N:real)*(mu c:real) <=
# (G c:real) whenever 0 < G c  (so N mu/G <= 1) and mu c > 0 on G's support.
# gT c := log(N·mu c / G c) if G c > 0 else 0   (<= 0 on support);
# tT := Σ G c·gT c (<= 0); costG := Π (e·N·mu c)^(G c)/(G c)!  (paper eq.multi-w-cost).
# X_i iid with law P{C} = mu C (atomic).  Wanted: P(Σ_i gT(X_i) ≤ tT) ≤ costG  (paper eq.final-H).

## PROOF ROUTES per lemma:
# gT_nonpos: 0 < G c & N·mu c <= G c (reals, mu c >= 0) -> argument in (0,1]: log <= 0.
#   Need N·mu c / G c <= 1: from hle divide by G c > 0.  log <= 0: Real.log_le_zero (arg <= 1, 0 < arg
#   — arg > 0 needs mu c > 0 or (N > 0): you have N : Nat possibly 0: state handles via hle & 0<Gc:
#   prove arg > 0 from mu c >= 0? if mu c = 0 arg = 0: log 0 = 0 (log at 0 is 0 by convention but
#   log_le_zero needs 0 < arg: then use hμpos if given; adjust: for gT_nonpos add hypothesis
#   0 < (mu c : real) OR prove directly when mu c = 0: N·0/Gc = 0 <= Gc <= 1-trivially: log(0)=0
#   <= 0: do by_cases on mu c = 0 and use Real.log_nonpos? (Real.log (0)=0).  Keep the lemma's
#   statement but be careful; you may split by_cases (mu c = 0) inside.)
# sum_gT_le: per c: if G c = 0 term = 0; else Wc >= Gc and gT <= 0: Wc·gT <= Gc·gT.
# mass_exp_sum_eq: LHS = Σ_{m size N} mass μ m · Π_c exp(-gT c)^(m c)
#   (exp(-Σ mc gT c) = Π exp(-gT c)^(m c)); equals (Σ_c μc·exp(-gT c))^N by Multi.mass_sum_eq_pow
#   applied to weights w c := (μ c : ℝ)·exp(-gT c) (≥ 0): mass N w m = mass N μ m · Π exp(-gT)^(m c):
#   show mass N (fun c => w c) m = mass N μ m * ∏ exp(-gT c)^(m c) by unfolding mass and per-x
#   algebra ((a·b)^k = a^k·b^k; cancel factorial denominators).  mass_sum_eq_pow is
#   Submission.Multi.mass_sum_eq_pow (imported via MultiMass) with X := C.
# sum_mu_exp_neg_gT_le: per c: if G c = 0: exp(-gT c) = exp 0 = 1: term = μc.
#   if G c > 0: exp(-gT c) = exp(-log(Nμc/Gc)) = Gc/(N μc) (exp_log, μc > 0): term = μc·Gc/(Nμc)
#   = Gc/N.  So LHS = (Σ_{Gc>0} Gc/N) + (Σ_{Gc=0} μc) = (Σ_{Gc>0}Gc)/N + (Σ_{Gc=0} μc)
#   = |G|/N − (Σ_{Gc>0}? no: Σ_{Gc=0} μc ≤ Σ_all μc ≤ 1; Σ_{Gc>0}Gc = sizeM G: LHS ≤ |G|/N + 1.
#   Implement: LHS = |G|/N + Σ_{Gc=0} μc ≤ |G|/N + 1 (via split the sum at the condition 0 < G c:
#   rw [← Finset.sum_filter_add_sum_filter_not ...]; per-part rewriting; |G| = sizeM G = Σ_c G c).
# exp_tT: tT = Σ Gc·gT c: exp(tT) = Π_c exp(Gc·gT c): for Gc=0 term exp(0·?) = 1 = ((Nμc/Gc)^0 = 1);
#   for Gc>0: exp(Gc·log(Nμc/Gc)) = (Nμc/Gc)^Gc (Real.exp_nat_mul? exp (n·log x) = x^n for 0<x:
#   prove helper exp_nat_log (x) (n) (hx : 0 < x) : Real.exp ((n : ℝ) · Real.log x) = x ^ n using
#   Real.rpow_def_of_pos / exp_log / rpow_natCast or induction on n: exp(log x * n): use
#   `Real.exp_nat_mul`? search: #check Real.exp_nat_mul, Real.exp_log, Real.log_pow.  For Gc=0 the
#   RHS factor is 0^0 = 1 (pow 0 = 1) ✓ (no positivity needed).
# pow_one_add_le_exp: (1 + |G|/N)^N ≤ exp(|G|): from log(1 + u) ≤ u: N·log(1+|G|/N) ≤ |G|:
#   exp of both sides: exp(N·log(1+u)) = (1+u)^N (same exp_nat_log with x = 1+u > 0); handle N=0
#   trivially (1^0 = 1 ≤ e^{|G|}? need exp |G| ≥ 1: fine) and u ≥ 0: log_one_add_le:
#   #check Real.log_one_add_le (x) (hx : -1 < x): gives log (1+x) ≤ x.
# prob_sum_gT_le_tT:
#   a) Let A := {ω | Σ_i gT (X_i ω) ≤ tT}: A = ⋃_{m ∈ (msizeExact C N).filter (fun m => Σ_c
#      (m c:ℝ)·gT c ≤ tT)} {ω | countVec (fun i => X i ω) = m} (finite disjoint union; use
#      measure_biUnion or induction + measure_union for disjointness; toReal afterwards or keep
#      ENNReal and bound by toReal(costG) ≤ ... careful direction: we want (P A).toReal ≤ costG:
#      use ENNReal bound then toReal_le? (P A) ≤ ENNReal-of-something: define real RHS bound, cast
#      to ENNReal... simpler: do the whole bound in ℝ≥0∞ then toReal: since P A ≤ Σ_m mass-ENNReal·
#      [m ∈ A-cond] — bound ≤ ENNReal.ofReal (costG)? toReal of a ≤ in ENNReal gives ≤ of toReals
#      only when both finite; costG real finite; use: toReal_mono with the ENNReal inequality.
#      cleanest: prove P A ≤ (costG : ℝ≥0∞) [coe of the real cost if ≥ 0] then take toReal.
#      Alternatively prove with real measures: ∫-free; use the identity (P A).toReal =
#      Σ_{m cond} massReal m as REALS and proceed with the real chain: requires real measure
#      additivity over the finite disjoint union: do this: P A = Σ_m∈T P{countVec = m} (ENNReal
#      additivity, Finset.measure-biUnion-style); apply toReal to both sides: toReal_sum? measures
#      are finite (prob): `ENNReal.toReal_sum`... use: ((Σ over T of P{countVec=m}).toReal) =
#      Σ over T of (P{countVec=m}).toReal [ENNReal.toReal_sum needs each < ∞ — probability OK];
#      and (P{countVec=m}).toReal = mass N (toReal μ) m via Discret1.prob_countVec + toReal of the
#      ENNReal formula: prove helper in this file:
#        mass_eq_of_prob_countVec : (P {countVec = m}).toReal =
#          Multi.mass N (fun c => (μ c : ℝ)) m   [given prob_countVec; toReal_mul/toReal_prod/
#          toReal_pow/toReal_inv, all finite/nonzero: (Nat.factorial k : ℝ≥0∞) ≠ 0 and ≠ ∞; μ c ≤ 1
#          as probability (finite); if needed assume hμle1 : ∀ c, μ c ≤ 1 to make (μ c)^(m c) finite
#          (it is finite since μ c : ℝ≥0 coerces to finite ENNReal; toReal_pow for coe: (↑a)^k has
#          toReal (a^k) fine).]
#   b) real bound: Σ_{m cond} mass m ≤ e^{tT}·Σ_{all m} mass m·e^{−Σ mc·gT c}
#      [for m in cond: 1 ≤ e^{tT − Σ}: exp_nonneg & monotone: e^{tT-Σ} ≥ 1 since tT−Σ ≥ 0]
#      = e^{tT}·(Σ μc·e^{−gT c})^N (mass_exp_sum_eq)
#      ≤ e^{tT}·(1 + |G|/N)^N (sum_mu_exp_neg_gT_le, N pow monotone)
#      ≤ e^{tT}·e^{|G|} (pow_one_add_le_exp)
#      = Π(Nμc/Gc)^{Gc}·e^{Gc}·? (exp_tT)  ≤ costG (e^{Gc}·(Nμc/Gc)^{Gc} = (eNμc/Gc)^{Gc} ≤
#      (eNμc)^{Gc}/Gc! because Gc! ≤ Gc^{Gc}: per-coordinate; prod over c; also for Gc=0 terms 1).
#      NOTE exp(tT)·exp(|G|): tT ≤ 0 so exp(tT) ≤ 1 but we don't need that.
#   You will need helper exp/prod identities; add freely.  Keep the imports as-is.  Namespace
#   Submission.Discret2.  Final theorem name/signature fixed.  No sorries at the end.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
open Classical
open MeasureTheory ProbabilityTheory Measure
open scoped BigOperators ENNReal NNReal

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Discret2

variable {C : Type*} [Fintype C] [DecidableEq C] [MeasurableSpace C] [MeasurableSingletonClass C]


/-- the total mass of the common law of `X_i` is 1 -/
lemma sum_mu_ennreal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (hNpos : 0 < N) (X : Fin N → Ω → C) (μ : C → ℝ≥0)
    (hmeas : ∀ i : Fin N, Measurable (X i))
    (hlaw : ∀ i : Fin N, ∀ c : C, P {ω | X i ω = c} = (μ c : ℝ≥0∞)) :
    (∑ c : C, (μ c : ℝ≥0∞)) = 1 := by
  classical
  let i0 : Fin N := ⟨0, hNpos⟩
  let A : C → Set Ω := fun c => {ω | X i0 ω = c}
  have hunion : (⋃ c ∈ (Finset.univ : Finset C), A c) = Set.univ := by
    ext ω
    constructor
    · intro hω; trivial
    · intro hω
      exact Set.mem_biUnion (Finset.mem_univ (X i0 ω)) (by simp [A])
  have hdisj : ((Finset.univ : Finset C) : Set C).PairwiseDisjoint A := by
    intro c hc c' hc' hne
    change Disjoint (A c) (A c')
    rw [Set.disjoint_left]
    intro ω hω hω'
    apply hne
    exact hω.symm.trans hω'
  have hmeasA : ∀ c ∈ (Finset.univ : Finset C), MeasurableSet (A c) := by
    intro c hc
    dsimp [A]
    have heq : {ω | X i0 ω = c} = X i0 ⁻¹' ({c} : Set C) := by
      ext ω
      simp
    rw [heq]
    exact MeasurableSet.preimage (measurableSet_singleton c) (hmeas i0)
  calc
    (∑ c : C, (μ c : ℝ≥0∞)) = ∑ c ∈ (Finset.univ : Finset C), P (A c) := by
        refine Finset.sum_congr rfl ?_
        intro c hc
        dsimp [A]
        exact (hlaw i0 c).symm
    _ = P (⋃ c ∈ (Finset.univ : Finset C), A c) := by
        exact (measure_biUnion_finset hdisj hmeasA).symm
    _ = P Set.univ := by
        rw [hunion]
    _ = 1 := by
        rw [MeasureTheory.IsProbabilityMeasure.measure_univ]

/-- the total mass is ≤ 1 (real) -/
lemma sum_mu_real_le_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (hNpos : 0 < N) (X : Fin N → Ω → C) (μ : C → ℝ≥0)
    (hmeas : ∀ i : Fin N, Measurable (X i))
    (hlaw : ∀ i : Fin N, ∀ c : C, P {ω | X i ω = c} = (μ c : ℝ≥0∞)) :
    (∑ c : C, (μ c : ℝ)) ≤ 1 := by
  have hENN := sum_mu_ennreal (Ω := Ω) P hNpos X μ hmeas hlaw
  have hsum_toReal : (∑ c : C, (μ c : ℝ≥0∞)).toReal = ∑ c : C, (μ c : ℝ) := by
    rw [ENNReal.toReal_sum]
    · simp
    · intro c hc
      exact ENNReal.coe_ne_top
  calc
    (∑ c : C, (μ c : ℝ)) = (∑ c : C, (μ c : ℝ≥0∞)).toReal := by rw [hsum_toReal]
    _ = (1 : ℝ≥0∞).toReal := by rw [hENN]
    _ = 1 := by simp
    _ ≤ 1 := le_rfl

/-- reindexing a tuple-sum over the values: ∑ᵢ f(t i) = ∑_c (count c)·f c -/
lemma sum_coord {N : ℕ} (t : Fin N → C) (f : C → ℝ) :
    (∑ i : Fin N, f (t i)) = ∑ c : C, (Discret1.countVec (N := N) t c : ℝ) * f c := by
  classical
  calc
    (∑ i : Fin N, f (t i)) = ∑ c : C, ∑ i ∈ (Finset.univ : Finset (Fin N)) with t i = c, f c := by
        rw [Finset.sum_fiberwise']
    _ = ∑ c : C, ((Finset.univ.filter (fun i : Fin N => t i = c)).card : ℝ) * f c := by
        refine Finset.sum_congr rfl ?_
        intro c hc
        rw [Finset.sum_const]
        simp
    _ = ∑ c : C, (Discret1.countVec (N := N) t c : ℝ) * f c := by
        rfl

/-- the real mass of a count-vector event equals the multinomial real mass -/
lemma mass_eq_prob_toReal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (X : Fin N → Ω → C) (μ : C → ℝ≥0) (m : C → ℕ)
    (hX : iIndepFun X P) (hmeas : ∀ i : Fin N, Measurable (X i))
    (hlaw : ∀ i : Fin N, ∀ c : C, P {ω | X i ω = c} = (μ c : ℝ≥0∞))
    (hm : (∑ c : C, m c) = N) :
    (P {ω | ∀ c : C, Discret1.countVec (fun i : Fin N => X i ω) c = m c}).toReal
      = Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m := by
  classical
  have h := Discret1.prob_countVec (Ω := Ω) P X μ m hX hmeas hlaw hm
  calc
    (P {ω | ∀ c : C, Discret1.countVec (fun i : Fin N => X i ω) c = m c}).toReal
        = ((Nat.factorial N : ℝ≥0∞) *
            ∏ c : C, (μ c : ℝ≥0∞) ^ m c * (Nat.factorial (m c) : ℝ≥0∞)⁻¹).toReal := by
            rw [h]
    _ = (Nat.factorial N : ℝ) *
          ∏ c : C, ((μ c : ℝ) ^ m c * (Nat.factorial (m c) : ℝ)⁻¹) := by
            simp [ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_pow,
              ENNReal.toReal_inv, ENNReal.toReal_natCast]
    _ = Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m := by
            rfl

/-- log of N·μ(c)/G(c), 0 when G c = 0 -/
noncomputable def gT (N : ℕ) (μ : C → ℝ≥0) (G : C → ℕ) (c : C) : ℝ :=
  if h : G c = 0 then 0 else Real.log ((N : ℝ) * (μ c : ℝ) / (G c : ℝ))

/-- t̃_G = Σ_c G c · gT c -/
noncomputable def tT (N : ℕ) (μ : C → ℝ≥0) (G : C → ℕ) : ℝ :=
  ∑ c : C, (G c : ℝ) * gT N μ G c

/-- (eNμ)-cost of the multiset G -/
noncomputable def costG (N : ℕ) (μ : C → ℝ≥0) (G : C → ℕ) : ℝ :=
  ∏ c : C, ((Real.exp 1) * (N : ℝ) * (μ c : ℝ)) ^ G c / Nat.factorial (G c)

/-- per-coordinate log is nonpositive under the trimmed condition -/
lemma gT_nonpos (N : ℕ) (μ : C → ℝ≥0) (G : C → ℕ) {c : C}
    (hG : 0 < G c) (hle : (N : ℝ) * (μ c : ℝ) ≤ (G c : ℝ)) : gT N μ G c ≤ 0 := by
  unfold gT
  rw [dif_neg (ne_of_gt hG)]
  refine Real.log_nonpos ?_ ?_
  · positivity
  · rw [div_le_iff₀ (by exact_mod_cast hG)]
    simpa using hle

/-- coverage: G ⊆ W implies Σ_c W c·gT c ≤ t̃ -/
lemma sum_gT_le (N : ℕ) (μ : C → ℝ≥0) (G W : C → ℕ)
    (hGW : ∀ c : C, G c ≤ W c)
    (htrim : ∀ c : C, 0 < G c → (N : ℝ) * (μ c : ℝ) ≤ (G c : ℝ)) :
    (∑ c : C, (W c : ℝ) * gT N μ G c) ≤ tT N μ G := by
  unfold tT
  exact Finset.sum_le_sum (by
    intro c hc
    by_cases hG0 : G c = 0
    · have hg0 : gT N μ G c = 0 := by simp [gT, hG0]
      simp [hg0]
    · have hG : 0 < G c := Nat.pos_of_ne_zero hG0
      have hg : gT N μ G c ≤ 0 := gT_nonpos N μ G hG (htrim c hG)
      have hsub : (W c : ℝ) - (G c : ℝ) ≥ 0 := by
        have : (G c : ℝ) ≤ (W c : ℝ) := by exact_mod_cast hGW c
        linarith
      have hmul : ((W c : ℝ) - (G c : ℝ)) * gT N μ G c ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos hsub hg
      nlinarith)

/-- mass of a product weight splits -/
lemma mass_mul_prod {N : ℕ} (a : C → ℝ) (b : C → ℝ) (m : C → ℕ) :
    Multi.mass (X := C) N (fun c : C => a c * b c) m =
      Multi.mass (X := C) N a m * ∏ c : C, b c ^ m c := by
  classical
  unfold Multi.mass
  have hprod : (∏ x : C, (a x * b x) ^ m x / Nat.factorial (m x)) =
      (∏ x : C, a x ^ m x / Nat.factorial (m x)) * (∏ x : C, b x ^ m x) := by
    calc
      (∏ x : C, (a x * b x) ^ m x / Nat.factorial (m x))
          = ∏ x : C, (a x ^ m x * b x ^ m x / Nat.factorial (m x)) := by
              refine Finset.prod_congr rfl ?_
              intro x hx
              rw [mul_pow]
      _ = ∏ x : C, ((a x ^ m x / Nat.factorial (m x)) * b x ^ m x) := by
              refine Finset.prod_congr rfl ?_
              intro x hx
              ring
      _ = (∏ x : C, a x ^ m x / Nat.factorial (m x)) * (∏ x : C, b x ^ m x) := by
              rw [← Finset.prod_mul_distrib]
  calc
    (Nat.factorial N : ℝ) * (∏ x : C, (a x * b x) ^ m x / Nat.factorial (m x))
        = (Nat.factorial N : ℝ) * ((∏ x : C, a x ^ m x / Nat.factorial (m x)) * (∏ x : C, b x ^ m x)) := by rw [hprod]
    _ = ((Nat.factorial N : ℝ) * (∏ x : C, a x ^ m x / Nat.factorial (m x))) * (∏ x : C, b x ^ m x) := by ring

/-- exp(-sum f) = product of exp(-f) -/
lemma exp_neg_sum (f : C → ℝ) :
    Real.exp (-(∑ c : C, f c)) = ∏ c : C, Real.exp (- f c) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]

/-- exp(-n·f) = exp(-f)^n -/
lemma exp_neg_mul_nat (f : ℝ) (n : ℕ) :
    Real.exp (-((n : ℝ) * f)) = (Real.exp (-f)) ^ n := by
  calc
    Real.exp (-((n : ℝ) * f)) = Real.exp ((n : ℝ) * (-f)) := by congr 1; ring
    _ = (Real.exp (-f)) ^ n := by rw [Real.exp_nat_mul]

/-- mass-weighted exp bound: Σ_m mass·exp(−Σ m gT) = (Σ μc exp(−gT))^N -/
lemma mass_exp_sum_eq (N : ℕ) (μ : C → ℝ≥0) (G : C → ℕ) :
    (∑ m ∈ Multi.msizeExact (X := C) N,
        Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m *
          Real.exp (-(∑ c : C, (m c : ℝ) * gT N μ G c)))
      = (∑ c : C, (μ c : ℝ) * Real.exp (- gT N μ G c)) ^ N := by
  classical
  let w : C → ℝ := fun c => (μ c : ℝ) * Real.exp (-gT N μ G c)
  have hper : ∀ m : C → ℕ,
      Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m *
        Real.exp (-(∑ c : C, (m c : ℝ) * gT N μ G c)) = Multi.mass (X := C) N w m := by
    intro m
    calc
      Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m * Real.exp (-(∑ c : C, (m c : ℝ) * gT N μ G c))
          = Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m * ∏ c : C, (Real.exp (- gT N μ G c)) ^ m c := by
              congr 1
              calc
                Real.exp (-(∑ c : C, (m c : ℝ) * gT N μ G c))
                    = ∏ c : C, Real.exp (-((m c : ℝ) * gT N μ G c)) := by
                        rw [exp_neg_sum]
                _ = ∏ c : C, (Real.exp (- gT N μ G c)) ^ m c := by
                        refine Finset.prod_congr rfl ?_
                        intro c hc
                        exact exp_neg_mul_nat (gT N μ G c) (m c)
      _ = Multi.mass (X := C) N w m := by
              rw [mass_mul_prod (a := fun c : C => (μ c : ℝ))
                (b := fun c : C => Real.exp (- gT N μ G c)) (m := m)]
  calc
    (∑ m ∈ Multi.msizeExact (X := C) N,
        Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m *
          Real.exp (-(∑ c : C, (m c : ℝ) * gT N μ G c)))
        = ∑ m ∈ Multi.msizeExact (X := C) N, Multi.mass (X := C) N w m := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            exact hper m
    _ = (∑ c : C, w c) ^ N := by
            exact Multi.mass_sum_eq_pow (M := N) (μ := w)
    _ = (∑ c : C, (μ c : ℝ) * Real.exp (- gT N μ G c)) ^ N := by
            simp [w]

/-- exp(-gT) = G/(Nμ) on the support, giving the (1+|G|/N) bound -/
lemma sum_mu_exp_neg_gT_le (N : ℕ) (μ : C → ℝ≥0) (G : C → ℕ)
    (hμpos : ∀ c : C, 0 < G c → 0 < (μ c : ℝ))
    (hsumle : (∑ c : C, (μ c : ℝ)) ≤ 1) :
    (∑ c : C, (μ c : ℝ) * Real.exp (- gT N μ G c)) ≤ 1 + (Multi.sizeM G : ℝ) / (N : ℝ) := by
  by_cases hN0 : N = 0
  · subst hN0
    have hg0 : ∀ c : C, gT 0 μ G c = 0 := by
      intro c
      unfold gT
      by_cases hG0 : G c = 0
      · simp [hG0]
      · rw [dif_neg hG0]
        have hz : (0 : ℝ) * (μ c : ℝ) / (G c : ℝ) = 0 := by simp
        simpa using congrArg Real.log hz
    calc
      (∑ c : C, (μ c : ℝ) * Real.exp (- gT 0 μ G c))
          = ∑ c : C, (μ c : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro c hc
              rw [hg0 c]
              simp
      _ ≤ 1 := hsumle
    have hx : (Multi.sizeM G : ℝ) / (↑(0 : ℕ) : ℝ) = 0 := by simp
    simpa [hx]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hNpos)
    have hterm : ∀ c : C, (μ c : ℝ) * Real.exp (- gT N μ G c) ≤ (G c : ℝ) / (N : ℝ) + (μ c : ℝ) := by
      intro c
      by_cases hG0 : G c = 0
      · have hg0 : gT N μ G c = 0 := by simp [gT, hG0]
        have hle0 : (μ c : ℝ) ≤ (G c : ℝ) / (N : ℝ) + (μ c : ℝ) := by
          have : (G c : ℝ) / (N : ℝ) = 0 := by simp [hG0]
          rw [this]
          simp
        calc
          (μ c : ℝ) * Real.exp (- gT N μ G c) = (μ c : ℝ) := by simp [hg0]
          _ ≤ (G c : ℝ) / (N : ℝ) + (μ c : ℝ) := hle0
      · have hG : 0 < G c := Nat.pos_of_ne_zero hG0
        have hμ : 0 < (μ c : ℝ) := hμpos c hG
        have hμne : (μ c : ℝ) ≠ 0 := ne_of_gt hμ
        have harg : 0 < (N : ℝ) * (μ c : ℝ) / (G c : ℝ) := by positivity
        rw [show gT N μ G c = Real.log ((N : ℝ) * (μ c : ℝ) / (G c : ℝ)) by
              unfold gT; rw [dif_neg hG0]]
        rw [Real.exp_neg, Real.exp_log harg]
        field_simp [hμne, hNne]
        nlinarith
    calc
      (∑ c : C, (μ c : ℝ) * Real.exp (- gT N μ G c))
          ≤ ∑ c : C, ((G c : ℝ) / (N : ℝ) + (μ c : ℝ)) := by
              exact Finset.sum_le_sum (by intro c hc; exact hterm c)
      _ = (∑ c : C, (G c : ℝ) / (N : ℝ)) + (∑ c : C, (μ c : ℝ)) := by
              rw [Finset.sum_add_distrib]
      _ = ((∑ c : C, (G c : ℝ)) / (N : ℝ)) + (∑ c : C, (μ c : ℝ)) := by
              rw [Finset.sum_div]
      _ ≤ 1 + (Multi.sizeM G : ℝ) / (N : ℝ) := by
              have hGsum : (∑ c : C, (G c : ℝ)) = (Multi.sizeM G : ℝ) := by
                dsimp [Multi.sizeM]
                rw [← Nat.cast_sum]
              rw [hGsum]
              linarith

/-- e^{t̃} = ∏ (Nμ/G)^G -/
lemma exp_tT (N : ℕ) (hNpos : 0 < N) (μ : C → ℝ≥0) (G : C → ℕ)
    (hμpos : ∀ c : C, 0 < G c → 0 < (μ c : ℝ)) :
    Real.exp (tT N μ G) = ∏ c : C, ((N : ℝ) * (μ c : ℝ) / (G c : ℝ)) ^ G c := by
  have hper : ∀ c : C, Real.exp ((G c : ℝ) * gT N μ G c) = ((N : ℝ) * (μ c : ℝ) / (G c : ℝ)) ^ G c := by
    intro c
    by_cases hG0 : G c = 0
    · have hg0 : gT N μ G c = 0 := by simp [gT, hG0]
      have hc0 : (G c : ℝ) = 0 := by exact_mod_cast hG0
      simp [hg0, hc0, hG0]
    · have hG : 0 < G c := Nat.pos_of_ne_zero hG0
      have hμ : 0 < (μ c : ℝ) := hμpos c hG
      have hN : 0 < (N : ℝ) := by exact_mod_cast hNpos
      have harg : 0 < (N : ℝ) * (μ c : ℝ) / (G c : ℝ) := by positivity
      unfold gT
      rw [dif_neg hG0]
      calc
        Real.exp ((G c : ℝ) * Real.log ((N : ℝ) * (μ c : ℝ) / (G c : ℝ)))
            = (Real.exp (Real.log ((N : ℝ) * (μ c : ℝ) / (G c : ℝ)))) ^ G c := by
                rw [Real.exp_nat_mul]
        _ = ((N : ℝ) * (μ c : ℝ) / (G c : ℝ)) ^ G c := by rw [Real.exp_log harg]
  calc
    Real.exp (tT N μ G) = Real.exp (∑ c : C, (G c : ℝ) * gT N μ G c) := by rfl
    _ = ∏ c : C, Real.exp ((G c : ℝ) * gT N μ G c) := by rw [Real.exp_sum]
    _ = ∏ c : C, ((N : ℝ) * (μ c : ℝ) / (G c : ℝ)) ^ G c := by
        refine Finset.prod_congr rfl ?_
        intro c hc
        exact hper c

/-- (1 + |G|/N)^N ≤ e^{|G|} -/
lemma pow_one_add_le_exp (N : ℕ) (G : C → ℕ) :
    (1 + (Multi.sizeM G : ℝ) / (N : ℝ)) ^ N ≤ Real.exp (Multi.sizeM G : ℝ) := by
  by_cases hN0 : N = 0
  · subst hN0
    simp only [pow_zero]
    exact Real.one_le_exp (by exact_mod_cast (Nat.zero_le (Multi.sizeM G)))
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hNpos)
    let u : ℝ := (Multi.sizeM G : ℝ) / (N : ℝ)
    have hu0 : 0 ≤ u := by
      dsimp [u]
      exact div_nonneg (by exact_mod_cast (Nat.zero_le (Multi.sizeM G))) (by positivity)
    have hpos : 0 < 1 + u := by linarith
    have hlog : Real.log (1 + u) ≤ u := by
      rw [Real.log_le_iff_le_exp hpos]
      simpa [add_comm] using Real.add_one_le_exp u
    have hmul : (N : ℝ) * Real.log (1 + u) ≤ (Multi.sizeM G : ℝ) := by
      calc
        (N : ℝ) * Real.log (1 + u) ≤ (N : ℝ) * u := by
            exact mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg N)
        _ = (Multi.sizeM G : ℝ) := by
            dsimp [u]
            rw [mul_div_cancel₀ _ hNne]
    calc
      (1 + (Multi.sizeM G : ℝ) / (N : ℝ)) ^ N
          = Real.exp ((N : ℝ) * Real.log (1 + (Multi.sizeM G : ℝ) / (N : ℝ))) := by
              have hpos' : 0 < 1 + (Multi.sizeM G : ℝ) / (N : ℝ) := by
                dsimp [u] at hpos
                simpa [u] using hpos
              calc
                (1 + (Multi.sizeM G : ℝ) / (N : ℝ)) ^ N
                    = (Real.exp (Real.log (1 + (Multi.sizeM G : ℝ) / (N : ℝ)))) ^ N := by
                        rw [Real.exp_log hpos']
                _ = Real.exp ((N : ℝ) * Real.log (1 + (Multi.sizeM G : ℝ) / (N : ℝ))) := by
                        rw [Real.exp_nat_mul]
      _ ≤ Real.exp (Multi.sizeM G : ℝ) := by
              dsimp [u] at hmul
              exact Real.exp_le_exp.mpr hmul

/-- the trimmed-condition mass sum is bounded by e^{t̃}·full weighted sum -/
lemma sum_mass_cond_le (N : ℕ) (μ : C → ℝ≥0) (G : C → ℕ) :
    (∑ m ∈ (Multi.msizeExact (X := C) N).filter
        (fun m : C → ℕ => (∑ c : C, (m c : ℝ) * gT N μ G c) ≤ tT N μ G),
        Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m)
      ≤ Real.exp (tT N μ G) *
          (∑ m ∈ Multi.msizeExact (X := C) N,
            Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m *
              Real.exp (-(∑ c : C, (m c : ℝ) * gT N μ G c))) := by
  classical
  let E : Finset (C → ℕ) := Multi.msizeExact (X := C) N
  let B : Finset (C → ℕ) :=
    E.filter (fun m : C → ℕ => (∑ c : C, (m c : ℝ) * gT N μ G c) ≤ tT N μ G)
  have hμnonneg : ∀ x : C, 0 ≤ (μ x : ℝ) := by intro x; positivity
  have hmass_nonneg : ∀ m : C → ℕ, 0 ≤ Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m := by
    intro m
    exact Multi.mass_nonneg N hμnonneg m
  have hper : ∀ m ∈ B, Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m ≤
      Real.exp (tT N μ G) * (Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m *
        Real.exp (-(∑ c : C, (m c : ℝ) * gT N μ G c))) := by
    intro m hmB
    have hcond : (∑ c : C, (m c : ℝ) * gT N μ G c) ≤ tT N μ G := (Finset.mem_filter.mp hmB).2
    let S : ℝ := ∑ c : C, (m c : ℝ) * gT N μ G c
    have hD : 0 ≤ tT N μ G - S := by dsimp [S]; linarith
    have hOne : 1 ≤ Real.exp (tT N μ G - S) := Real.one_le_exp hD
    have hm : 0 ≤ Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m := hmass_nonneg m
    have hle : Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m ≤
        Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m * Real.exp (tT N μ G - S) := by
          exact le_mul_of_one_le_right hm hOne
    have heqD : Real.exp (tT N μ G - S) =
        Real.exp (tT N μ G) * Real.exp (-S) := by
          rw [sub_eq_add_neg, ← Real.exp_add]
    calc
      Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m
          ≤ Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m * Real.exp (tT N μ G - S) := hle
      _ = Real.exp (tT N μ G) * (Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m *
            Real.exp (-S)) := by
              rw [heqD]
              ring
      _ = Real.exp (tT N μ G) * (Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m *
            Real.exp (-(∑ c : C, (m c : ℝ) * gT N μ G c))) := by
              dsimp [S]
  have hsubset : B ⊆ E := by
    intro m hm
    exact (Finset.mem_filter.mp hm).1
  have hnonneg_out : ∀ m ∈ E, m ∉ B →
      0 ≤ Real.exp (tT N μ G) * (Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m *
        Real.exp (-(∑ c : C, (m c : ℝ) * gT N μ G c))) := by
    intro m hmE hmnotB
    exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (hmass_nonneg m) (Real.exp_nonneg _))
  calc
    (∑ m ∈ B, Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m)
        ≤ ∑ m ∈ B, Real.exp (tT N μ G) * (Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m *
            Real.exp (-(∑ c : C, (m c : ℝ) * gT N μ G c))) := by
            exact Finset.sum_le_sum (by intro m hmB; exact hper m hmB)
    _ ≤ ∑ m ∈ E, Real.exp (tT N μ G) * (Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m *
            Real.exp (-(∑ c : C, (m c : ℝ) * gT N μ G c))) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg_out
    _ = Real.exp (tT N μ G) *
          (∑ m ∈ E, Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m *
            Real.exp (-(∑ c : C, (m c : ℝ) * gT N μ G c))) := by
            dsimp [E, B]
            rw [← Finset.mul_sum]


/-- coordinate factor: (x/n)^n·e^n ≤ (e·x)^n/n! -/
lemma coord_factor_le (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (x / (n : ℝ)) ^ n * (Real.exp 1) ^ n ≤ ((Real.exp 1) * x) ^ n / Nat.factorial n := by
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hfac_le : (Nat.factorial n : ℝ) ≤ (n : ℝ) ^ n := by
      exact_mod_cast (Nat.factorial_le_pow n)
    have hfacpos : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast (Nat.factorial_pos n)
    have hpowpos : 0 < (n : ℝ) ^ n := by positivity
    have hA : 0 ≤ ((Real.exp 1) * x) ^ n := by positivity
    have hdiv : 1 / (n : ℝ) ^ n ≤ 1 / (Nat.factorial n : ℝ) := by
      exact one_div_le_one_div_of_le hfacpos hfac_le
    calc
      (x / (n : ℝ)) ^ n * (Real.exp 1) ^ n
          = (x ^ n / (n : ℝ) ^ n) * (Real.exp 1) ^ n := by rw [div_pow]
      _ = ((Real.exp 1) * x) ^ n / (n : ℝ) ^ n := by
              rw [mul_pow]
              ring
      _ ≤ ((Real.exp 1) * x) ^ n / Nat.factorial n := by
              calc
                ((Real.exp 1) * x) ^ n / (n : ℝ) ^ n
                    = ((Real.exp 1) * x) ^ n * (1 / (n : ℝ) ^ n) := by ring
                _ ≤ ((Real.exp 1) * x) ^ n * (1 / (Nat.factorial n : ℝ)) := by
                        exact mul_le_mul_of_nonneg_left hdiv hA
                _ = ((Real.exp 1) * x) ^ n / Nat.factorial n := by ring

/-- e^{t̃}·e^{|G|} ≤ costG -/
lemma exp_tT_mul_exp_size_le_costG (N : ℕ) (hNpos : 0 < N) (μ : C → ℝ≥0) (G : C → ℕ)
    (hμpos : ∀ c : C, 0 < G c → 0 < (μ c : ℝ)) :
    Real.exp (tT N μ G) * Real.exp (Multi.sizeM G : ℝ) ≤ costG N μ G := by
  have hsize : (Multi.sizeM G : ℝ) = ∑ c : C, (G c : ℝ) := by
    dsimp [Multi.sizeM]
    rw [← Nat.cast_sum]
  have hx : ∀ c : C, 0 ≤ (N : ℝ) * (μ c : ℝ) := by
    intro c
    positivity
  have hepow : ∀ c : C, Real.exp (G c : ℝ) = (Real.exp 1) ^ G c := by
    intro c
    have h' := Real.exp_nat_mul (1 : ℝ) (G c)
    rw [← h']
    simp
  calc
    Real.exp (tT N μ G) * Real.exp (Multi.sizeM G : ℝ)
        = (∏ c : C, ((N : ℝ) * (μ c : ℝ) / (G c : ℝ)) ^ G c) *
            (∏ c : C, Real.exp (G c : ℝ)) := by
              rw [exp_tT N hNpos μ G hμpos]
              congr 1
              calc
                Real.exp (Multi.sizeM G : ℝ) = Real.exp (∑ c : C, (G c : ℝ)) := by rw [hsize]
                _ = ∏ c : C, Real.exp (G c : ℝ) := by rw [Real.exp_sum]
    _ = ∏ c : C, (((N : ℝ) * (μ c : ℝ) / (G c : ℝ)) ^ G c * Real.exp (G c : ℝ)) := by
              rw [← Finset.prod_mul_distrib]
    _ ≤ ∏ c : C, ((Real.exp 1) * (N : ℝ) * (μ c : ℝ)) ^ G c / Nat.factorial (G c) := by
              refine Finset.prod_le_prod ?_ ?_
              · intro c hc
                have hb : 0 ≤ (N : ℝ) * (μ c : ℝ) / (G c : ℝ) := by
                  exact div_nonneg (hx c) (by exact_mod_cast (Nat.zero_le (G c)))
                exact mul_nonneg (pow_nonneg hb (G c)) (Real.exp_nonneg (G c : ℝ))
              · intro c hc
                have hterm := coord_factor_le (G c) ((N : ℝ) * (μ c : ℝ)) (hx c)
                rw [hepow c, mul_assoc]
                exact hterm
    _ = costG N μ G := by
              rfl

/-- the full weighted mass sum is bounded by e^{|G|} -/
lemma weighted_mass_sum_le_exp (N : ℕ) (hNpos : 0 < N) (μ : C → ℝ≥0) (G : C → ℕ)
    (hμpos : ∀ c : C, 0 < G c → 0 < (μ c : ℝ))
    (hsumle : (∑ c : C, (μ c : ℝ)) ≤ 1) :
    (∑ m ∈ Multi.msizeExact (X := C) N,
        Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m *
          Real.exp (-(∑ c : C, (m c : ℝ) * gT N μ G c)))
      ≤ Real.exp (Multi.sizeM G : ℝ) := by
  have hsum_nonneg : 0 ≤ ∑ c : C, (μ c : ℝ) * Real.exp (- gT N μ G c) := by
    exact Finset.sum_nonneg (by intro c hc; positivity)
  calc
    (∑ m ∈ Multi.msizeExact (X := C) N,
        Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m *
          Real.exp (-(∑ c : C, (m c : ℝ) * gT N μ G c)))
        = (∑ c : C, (μ c : ℝ) * Real.exp (- gT N μ G c)) ^ N := by
            exact mass_exp_sum_eq N μ G
    _ ≤ (1 + (Multi.sizeM G : ℝ) / (N : ℝ)) ^ N := by
            exact pow_le_pow_left₀ hsum_nonneg
              (sum_mu_exp_neg_gT_le N μ G hμpos hsumle) N
    _ ≤ Real.exp (Multi.sizeM G : ℝ) := by
            exact pow_one_add_le_exp N G

/-- the event {Σ gT(Xᵢ) ≤ t̃} is covered by the count-vector events of the trimmed set -/
lemma event_le_union_countVec {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (X : Fin N → Ω → C) (μ : C → ℝ≥0) (G : C → ℕ) :
    P {ω | (∑ i : Fin N, gT N μ G (X i ω)) ≤ tT N μ G} ≤
      ∑ m ∈ (Multi.msizeExact (X := C) N).filter
          (fun m : C → ℕ => (∑ c : C, (m c : ℝ) * gT N μ G c) ≤ tT N μ G),
        P {ω | ∀ c : C, Discret1.countVec (fun i : Fin N => X i ω) c = m c} := by
  classical
  let E : Finset (C → ℕ) := Multi.msizeExact (X := C) N
  let B : Finset (C → ℕ) := E.filter (fun m : C → ℕ =>
      (∑ c : C, (m c : ℝ) * gT N μ G c) ≤ tT N μ G)
  let A : Set Ω := {ω | (∑ i : Fin N, gT N μ G (X i ω)) ≤ tT N μ G}
  let S : (C → ℕ) → Set Ω := fun m =>
    {ω | ∀ c : C, Discret1.countVec (fun i : Fin N => X i ω) c = m c}
  have hcover : A ⊆ ⋃ m ∈ B, S m := by
    intro ω hω
    let m0 : C → ℕ := fun c => Discret1.countVec (fun i : Fin N => X i ω) c
    have hsize : (∑ c : C, m0 c) = N := by
      dsimp [m0]
      exact Discret1.sum_countVec (N := N) (fun i : Fin N => X i ω)
    have hm0E : m0 ∈ E := by
      dsimp [E]
      exact Multi.mem_msizeExact hsize
    have hcond : (∑ c : C, (m0 c : ℝ) * gT N μ G c) ≤ tT N μ G := by
      have hsum : (∑ c : C, (m0 c : ℝ) * gT N μ G c) = ∑ i : Fin N, gT N μ G (X i ω) := by
        calc
          (∑ c : C, (m0 c : ℝ) * gT N μ G c)
              = ∑ c : C, (Discret1.countVec (N := N) (fun i : Fin N => X i ω) c : ℝ) * gT N μ G c := by
                  dsimp [m0]
          _ = ∑ i : Fin N, gT N μ G (X i ω) := by
                  exact (sum_coord (t := fun i : Fin N => X i ω)
                    (f := fun c : C => gT N μ G c)).symm
      rw [hsum]
      exact hω
    have hm0B : m0 ∈ B := by
      dsimp [B]
      rw [Finset.mem_filter]
      exact ⟨hm0E, hcond⟩
    have hmem : ω ∈ S m0 := by
      simp [S, m0]
    exact Set.mem_biUnion hm0B hmem
  have hPmono : P A ≤ P (⋃ m ∈ B, S m) := by
    exact measure_mono hcover
  have hPsub : P (⋃ m ∈ B, S m) ≤ ∑ m ∈ B, P (S m) := by
    exact measure_biUnion_finset_le B S
  calc
    P {ω | (∑ i : Fin N, gT N μ G (X i ω)) ≤ tT N μ G}
        = P A := rfl
    _ ≤ P (⋃ m ∈ B, S m) := hPmono
    _ ≤ ∑ m ∈ B, P (S m) := hPsub
    _ = ∑ m ∈ (Multi.msizeExact (X := C) N).filter
          (fun m : C → ℕ => (∑ c : C, (m c : ℝ) * gT N μ G c) ≤ tT N μ G),
        P {ω | ∀ c : C, Discret1.countVec (fun i : Fin N => X i ω) c = m c} := by
            dsimp [B, E, S]

/-- toReal of the count-vector-probability sum equals the real mass sum -/
lemma sum_S_mass_real {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (X : Fin N → Ω → C) (μ : C → ℝ≥0) (G : C → ℕ)
    (hX : iIndepFun X P) (hmeas : ∀ i : Fin N, Measurable (X i))
    (hlaw : ∀ i : Fin N, ∀ c : C, P {ω | X i ω = c} = (μ c : ℝ≥0∞)) :
    ((∑ m ∈ (Multi.msizeExact (X := C) N).filter
        (fun m : C → ℕ => (∑ c : C, (m c : ℝ) * gT N μ G c) ≤ tT N μ G),
        P {ω | ∀ c : C, Discret1.countVec (fun i : Fin N => X i ω) c = m c})).toReal
      = ∑ m ∈ (Multi.msizeExact (X := C) N).filter
        (fun m : C → ℕ => (∑ c : C, (m c : ℝ) * gT N μ G c) ≤ tT N μ G),
          Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m := by
  classical
  let B : Finset (C → ℕ) := (Multi.msizeExact (X := C) N).filter (fun m : C → ℕ =>
      (∑ c : C, (m c : ℝ) * gT N μ G c) ≤ tT N μ G)
  have hne_top : ∀ s : Set Ω, P s ≠ ∞ := by
    intro s
    have hle : P s ≤ P Set.univ := measure_mono (by intro ω hω; trivial)
    have h1 : P Set.univ = 1 := MeasureTheory.IsProbabilityMeasure.measure_univ
    rw [h1] at hle
    exact ne_of_lt (lt_of_le_of_lt hle (by norm_num : (1 : ℝ≥0∞) < ∞))
  have hfinite : ∀ m ∈ B, P {ω | ∀ c : C, Discret1.countVec (fun i : Fin N => X i ω) c = m c} ≠ ∞ := by
    intro m hmB
    exact hne_top _
  calc
    ((∑ m ∈ B, P {ω | ∀ c : C, Discret1.countVec (fun i : Fin N => X i ω) c = m c})).toReal
        = ∑ m ∈ B, (P {ω | ∀ c : C, Discret1.countVec (fun i : Fin N => X i ω) c = m c}).toReal := by
            rw [ENNReal.toReal_sum]
            exact hfinite
    _ = ∑ m ∈ B, Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m := by
            refine Finset.sum_congr rfl ?_
            intro m hmB
            have hmE : m ∈ Multi.msizeExact (X := C) N := (Finset.mem_filter.mp hmB).1
            have hsizeM : Multi.sizeM m = N := (Multi.mem_msizeExact_iff (X := C) (M := N)).mp hmE
            have hm : (∑ c : C, m c) = N := by
              simpa [Multi.sizeM] using hsizeM
            exact mass_eq_prob_toReal (Ω := Ω) P X μ m hX hmeas hlaw hm
    _ = ∑ m ∈ (Multi.msizeExact (X := C) N).filter
        (fun m : C → ℕ => (∑ c : C, (m c : ℝ) * gT N μ G c) ≤ tT N μ G),
          Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m := by
            rfl

/-- the real mass sum over the trimmed set is at most costG -/
lemma sum_B_mass_le_cost (N : ℕ) (hNpos : 0 < N) (μ : C → ℝ≥0) (G : C → ℕ)
    (hμpos : ∀ c : C, 0 < G c → 0 < (μ c : ℝ))
    (hsumle : (∑ c : C, (μ c : ℝ)) ≤ 1) :
    (∑ m ∈ (Multi.msizeExact (X := C) N).filter
        (fun m : C → ℕ => (∑ c : C, (m c : ℝ) * gT N μ G c) ≤ tT N μ G),
        Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m)
      ≤ costG N μ G := by
  calc
    (∑ m ∈ (Multi.msizeExact (X := C) N).filter
        (fun m : C → ℕ => (∑ c : C, (m c : ℝ) * gT N μ G c) ≤ tT N μ G),
        Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m)
        ≤ Real.exp (tT N μ G) *
            (∑ m ∈ Multi.msizeExact (X := C) N,
              Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m *
                Real.exp (-(∑ c : C, (m c : ℝ) * gT N μ G c))) := by
            exact sum_mass_cond_le N μ G
    _ ≤ Real.exp (tT N μ G) * Real.exp (Multi.sizeM G : ℝ) := by
            exact mul_le_mul_of_nonneg_left (weighted_mass_sum_le_exp N hNpos μ G hμpos hsumle)
              (Real.exp_nonneg (tT N μ G))
    _ ≤ costG N μ G := by
            exact exp_tT_mul_exp_size_le_costG N hNpos μ G hμpos
/-- the final per-G probability bound: P(Σ_i gT(X_i) ≤ t̃) ≤ costG -/
lemma prob_sum_gT_le_tT {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (hNpos : 0 < N) (X : Fin N → Ω → C) (μ : C → ℝ≥0)
    (G : C → ℕ)
    (hX : iIndepFun X P) (hmeas : ∀ i : Fin N, Measurable (X i))
    (hlaw : ∀ i : Fin N, ∀ c : C, P {ω | X i ω = c} = (μ c : ℝ≥0∞))
    (hμpos : ∀ c : C, 0 < G c → 0 < (μ c : ℝ))
    (htrim : ∀ c : C, 0 < G c → (N : ℝ) * (μ c : ℝ) ≤ (G c : ℝ)) :
    (P {ω | (∑ i : Fin N, gT N μ G (X i ω)) ≤ tT N μ G}).toReal ≤ costG N μ G := by
  classical
  let B : Finset (C → ℕ) := (Multi.msizeExact (X := C) N).filter (fun m : C → ℕ =>
      (∑ c : C, (m c : ℝ) * gT N μ G c) ≤ tT N μ G)
  have hsumle : (∑ c : C, (μ c : ℝ)) ≤ 1 := by
    exact sum_mu_real_le_one (Ω := Ω) P hNpos X μ hmeas hlaw
  have hL4 := event_le_union_countVec (Ω := Ω) P X μ G
  have hne_top : ∀ s : Set Ω, P s ≠ ∞ := by
    intro s
    have hle : P s ≤ P Set.univ := measure_mono (by intro ω hω; trivial)
    rw [MeasureTheory.IsProbabilityMeasure.measure_univ] at hle
    exact ne_of_lt (lt_of_le_of_lt hle (by norm_num : (1 : ℝ≥0∞) < ∞))
  have hPm1 : ∀ m ∈ B, P {ω | ∀ c : C, Discret1.countVec (fun i : Fin N => X i ω) c = m c} ≤ 1 := by
    intro m hmB
    have hle : P {ω | ∀ c : C, Discret1.countVec (fun i : Fin N => X i ω) c = m c} ≤ P Set.univ :=
      measure_mono (by intro ω hω; trivial)
    simpa [MeasureTheory.IsProbabilityMeasure.measure_univ] using hle
  have hfinSum : (∑ m ∈ B, P {ω | ∀ c : C, Discret1.countVec (fun i : Fin N => X i ω) c = m c}) ≠ ∞ := by
    have hlecard : (∑ m ∈ B, P {ω | ∀ c : C, Discret1.countVec (fun i : Fin N => X i ω) c = m c})
        ≤ (B.card : ℝ≥0∞) := by
      calc
        (∑ m ∈ B, P {ω | ∀ c : C, Discret1.countVec (fun i : Fin N => X i ω) c = m c})
            ≤ ∑ m ∈ B, (1 : ℝ≥0∞) := by
                exact Finset.sum_le_sum (by intro m hmB; exact hPm1 m hmB)
        _ = (B.card : ℝ≥0∞) := by
                rw [Finset.sum_const]
                simp
    exact ne_of_lt (lt_of_le_of_lt hlecard (lt_top_iff_ne_top.mpr (ENNReal.natCast_ne_top B.card)))
  have hSR := sum_S_mass_real (Ω := Ω) P X μ G hX hmeas hlaw
  have hBound := sum_B_mass_le_cost N hNpos μ G hμpos hsumle
  calc
    (P {ω | (∑ i : Fin N, gT N μ G (X i ω)) ≤ tT N μ G}).toReal
        ≤ (∑ m ∈ B, P {ω | ∀ c : C, Discret1.countVec (fun i : Fin N => X i ω) c = m c}).toReal := by
            exact ENNReal.toReal_mono hfinSum (by simpa [B] using hL4)
    _ = ∑ m ∈ B, Multi.mass (X := C) N (fun c : C => (μ c : ℝ)) m := by
            simpa [B] using hSR
    _ ≤ costG N μ G := by
            simpa [B] using hBound

end Discret2
end Submission
