import Mathlib
import Submission.PolyaCore
import Submission.XTransfer
import Submission.DirSet
import Submission.FeketeLim
import Submission.SS2
import Submission.SS3asm
import Submission.SS1

/-!
# The Fekete–Chebyshev block (tool layer for E1's Dubinin content)

`Submission.E1Content.hedgehogBound_of_short_spikes` (the single deep
`sorry` of the E1 reduction) says: a hedgehog `star S` whose `s` spikes are
all shorter than `4^(1/s)` is polynomially controllable on a fattening
(`HedgehogBound S`).  The classical route is Fekete's equality between the
*Chebyshev constant* and the *transfinite diameter* (= logarithmic
capacity), plus Dubinin's bound `τ(∪[0,a_j]) ≤ 4^(−1/s)·max|a_j|`.

This module lays down the formal language for that route:

    MonicDeg n       := { p | p.Monic ∧ p.natDegree = n }
    chebyshevNumber K n := sInf { c ≥ 0 | ∃ p ∈ MonicDeg n,
                                     ∀ X ∈ K, ‖p.eval X‖ ≤ c }
    vdm x n          := ∏_{j<i<n} ‖x_i − x_j‖           (Vandermonde)
    feketeNumber K n := sSup { vdm x n | x₀,…,x_{n−1} ∈ K }
    PolyDecayOn K    := ∃ C θ ≥ 0, θ < 1, ∀ j ≥ 1,
                           ∃ p ∈ MonicDeg j, ∀ X ∈ K, ‖p.eval X‖ ≤ C·θ^j

PROVED below:
* `polyDecay_fatStar_iff_hedgehogBound`: `PolyDecayOn` on *some* fattening
  `FatStar S ε` is exactly `HedgehogBound S` (the engine interface),
* `polyDecay_mono`: polynomial decay is monotone in the set (a smaller set
  is easier: `K ⊆ K'` and decay on `K'` gives decay on `K`; the reverse
  direction -- decay on a compact set implies decay on a small fattening --
  is *capacity continuity* (Bernstein–Walsh / Green-function estimates),
  DEEP and NOT attempted here),
* `polyDecay_imp_chebyshev`: each witnessing `p_j` bounds the Chebyshev
  number (`chebyshevNumber K j ≤ C·θ^j`).

STATEMENTS (DEEP; `sorry`, do not import until proved):
* `chebyshev_submultiplicative` (`t_{m+n} ≤ t_m·t_n`; elementary -- prove
  in a fresh single-lemma file via `csInf_le`/`le_csInf`, see the docstring
  below),
* `fekete_chebyshev_equality` (limsup of Chebyshev root numbers = limsup of
  Fekete root numbers = logarithmic capacity; Fekete's theorem),
* `hedgehog_decay_of_short_spikes` (the Dubinin content: spikes < 4^(1/s)
  ⟹ `PolyDecayOn (FatStar S ε)` for some `ε > 0`; = the E1 crux).

Corrected record (this module previously proposed a `fattening_continuity`
lemma "PolyDecayOn (star S) ⟹ ∃ε, PolyDecayOn (FatStar S ε)").  That
direction is NOT elementary: the witnesses of decay on the star may blow up
in its ε-neighbourhood, and lifting decay requires capacity continuity of
the fattening (Green-function/Bernstein–Walsh estimates), which is part of
the deep theory; the easy direction is `polyDecay_mono` below.  The
short-spike theorem therefore must be proved directly on the fattening
(Dubinin), and `polyDecay_fatStar_iff_hedgehogBound` then converts it to
`HedgehogBound`.
-/

noncomputable section

open scoped Real Polynomial Topology BigOperators

namespace Submission.Dubinin

open Polynomial
open Submission.PolyaCore
open Submission.DirSet

/-- Monic complex polynomials of degree exactly `n`. -/
def MonicDeg (n : ℕ) : Set ℂ[X] := {p : ℂ[X] | p.Monic ∧ p.natDegree = n}

/-- The sup-norm of a polynomial on `K`. -/
def supNorm (K : Set ℂ) (p : ℂ[X]) : ℝ :=
  sSup {d : ℝ | ∃ X ∈ K, d = ‖p.eval X‖}

/-- **Chebyshev number.**  `chebyshevNumber K n` is the infimum, over monic
polynomials of degree `n`, of their sup-norm on `K`. -/
def chebyshevNumber (K : Set ℂ) (n : ℕ) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ ∃ p ∈ MonicDeg n, ∀ X ∈ K, ‖p.eval X‖ ≤ c}

/-- The Vandermonde product of `n` points (pairs `j < i < n`, each pair
counted once). -/
def vdm (x : ℕ → ℂ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, ‖x j - x i‖

/-- **Fekete number.**  `feketeNumber K n` is the supremum of the Vandermonde
products over `n`-point configurations in `K`. -/
def feketeNumber (K : Set ℂ) (n : ℕ) : ℝ :=
  sSup {d : ℝ | ∃ x : ℕ → ℂ, (∀ i : ℕ, i < n → x i ∈ K) ∧ d = vdm x n}

/-- Polynomial decay on `K`: monic `p_j` of every degree `j ≥ 1` with
`‖p_j‖ ≤ C·θ^j` on `K`, for some `θ < 1` (this is `HedgehogBound` when
`K = FatStar S ε`). -/
def PolyDecayOn (K : Set ℂ) : Prop :=
  ∃ C θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
    ∀ j : ℕ, 1 ≤ j → ∃ p ∈ MonicDeg j, ∀ X ∈ K, ‖p.eval X‖ ≤ C * θ ^ j

/-- `PolyDecayOn` on *some* fattening `FatStar S ε` is exactly
`HedgehogBound S` (the interface of
`E1Content.hedgehogBound_of_short_spikes`); `PolyDecayOn` and
`HedgehogBound` coincide up to the `0 < C` and `j = 0` clauses. -/
lemma polyDecay_fatStar_iff_hedgehogBound (S : Finset ℂ) :
    (∃ ε : ℝ, 0 < ε ∧ PolyDecayOn (FatStar S ε)) ↔ HedgehogBound S := by
  classical
  constructor
  · rintro ⟨ε, hε, hdec⟩
    rcases hdec with ⟨C, θ, hθ0, hθ1, hp⟩
    refine ⟨ε, hε, max C 1, ?_, θ, hθ0, hθ1, ?_⟩
    · exact lt_of_lt_of_le zero_lt_one (le_max_right C 1)
    · intro j
      by_cases hj : 1 ≤ j
      · rcases hp j hj with ⟨p, hpm, hb⟩
        refine ⟨p, hpm.1, hpm.2, ?_⟩
        intro X hX
        exact le_trans (hb X hX)
          (mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg hθ0 j))
      · have hj0 : j = 0 := by omega
        subst j
        refine ⟨1, ?_, ?_, ?_⟩
        · simp
        · simp
        · intro X hX
          have hb0 : ‖(1 : ℂ[X]).eval X‖ = 1 := by simp
          rw [hb0]
          have hpow : θ ^ 0 = 1 := by simp
          rw [hpow]
          simpa using (le_max_right C 1)
  · rintro ⟨ε', hε', C, hC, θ, hθ0, hθ1, hpol⟩
    refine ⟨ε', hε', C, θ, hθ0, hθ1, ?_⟩
    intro j hj
    rcases hpol j with ⟨p, hpm, hdeg, hb⟩
    refine ⟨p, ⟨hpm, hdeg⟩, ?_⟩
    exact hb

/-- Polynomial decay is monotone in the set: a smaller set is easier to
control.  (This is the EASY direction of fattening: decay on `K' ⊇ K`
restricts to `K`; decay on `K` does NOT in general lift to a fattening --
that would be capacity continuity.) -/
lemma polyDecay_mono {K K' : Set ℂ} (h : K ⊆ K') (hdec : PolyDecayOn K') :
    PolyDecayOn K := by
  rcases hdec with ⟨C, θ, hθ0, hθ1, hp⟩
  refine ⟨C, θ, hθ0, hθ1, ?_⟩
  intro j hj
  rcases hp j hj with ⟨p, hpm, hb⟩
  refine ⟨p, hpm, ?_⟩
  intro X hX
  exact hb X (h hX)

/-- `chebyshevNumber K n ≤ c` whenever a monic degree-`n` polynomial is
bounded by `c ≥ 0` on `K` (membership in the defining set, `csInf_le'`). -/
lemma chebyshevNumber_le_of_bounds {K : Set ℂ} {n : ℕ} {p : ℂ[X]}
    (hp : p ∈ MonicDeg n) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ X ∈ K, ‖p.eval X‖ ≤ c) :
    chebyshevNumber K n ≤ c := by
  unfold chebyshevNumber
  exact csInf_le (by
    -- BddBelow: 0 is a lower bound of the defining set
    refine ⟨0, ?_⟩
    intro b hb
    exact hb.1) ⟨hc, ⟨p, ⟨hp, hb⟩⟩⟩

/-- `PolyDecayOn K` implies that the Chebyshev numbers of `K` decay
geometrically (each `p_j` witnesses the bound, `chebyshevNumber K j ≤
C·θ^j`).  Needs `K` nonempty so the witnessed bound forces `C·θ^j ≥ 0`. -/
lemma polyDecay_imp_chebyshev {K : Set ℂ} (hKne : K.Nonempty) (hdec : PolyDecayOn K) :
    ∃ C θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      ∀ j : ℕ, 1 ≤ j → chebyshevNumber K j ≤ C * θ ^ j := by
  rcases hdec with ⟨C, θ, hθ0, hθ1, hp⟩
  refine ⟨C, θ, hθ0, hθ1, ?_⟩
  intro j hj
  rcases hp j hj with ⟨p, hpm, hb⟩
  have hc0 : 0 ≤ C * θ ^ j := by
    rcases hKne with ⟨X, hX⟩
    exact le_trans (norm_nonneg (p.eval X)) (hb X hX)
  exact chebyshevNumber_le_of_bounds hpm hc0 hb

/-- The defining set of `chebyshevNumber K n`: admissible bounds `c ≥ 0` for
monic polynomials of degree `n` on `K`; `chebyshevNumber K n` is its
infimum. -/
def chebyshevSet (K : Set ℂ) (n : ℕ) : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ ∃ p ∈ MonicDeg n, ∀ X ∈ K, ‖p.eval X‖ ≤ c}

/-- Every element of `chebyshevSet K n` is nonnegative. -/
lemma chebyshevSet_nonneg (K : Set ℂ) (n : ℕ) :
    ∀ c ∈ chebyshevSet K n, 0 ≤ c := by
  intro c hc
  exact hc.1

/-- `chebyshevSet K n` is bounded below (by `0`). -/
lemma chebyshevSet_bddBelow (K : Set ℂ) (n : ℕ) : BddBelow (chebyshevSet K n) := by
  exact ⟨0, chebyshevSet_nonneg K n⟩

/-- For bounded `K`, `chebyshevSet K n` is nonempty: `X ^ n` is monic of
degree `n` and bounded on `K`. -/
lemma chebyshevSet_nonempty (K : Set ℂ) (hK : Bornology.IsBounded K) (n : ℕ) :
    (chebyshevSet K n).Nonempty := by
  rcases hK.exists_norm_le with ⟨R, hR⟩
  refine ⟨(max R 0) ^ n, pow_nonneg (le_max_right R 0) n, Polynomial.X ^ n, ?_, ?_⟩
  · exact ⟨monic_X_pow n, natDegree_X_pow n⟩
  · intro X hX
    have hle : ‖X‖ ≤ max R 0 := le_trans (hR X hX) (le_max_left R 0)
    calc ‖(Polynomial.X ^ n).eval X‖ = ‖X ^ n‖ := by simp
      _ = ‖X‖ ^ n := by rw [norm_pow]
      _ ≤ (max R 0) ^ n := pow_le_pow_left₀ (norm_nonneg X) hle n

/-- The product of an admissible bound of degree `m` and one of degree `n`
is an admissible bound for degree `m + n` (products of monic polynomials are
monic of the sum of the degrees, and norms are submultiplicative). -/
lemma chebyshevSet_mul_mem {K : Set ℂ} {m n : ℕ} {a b : ℝ}
    (ha : a ∈ chebyshevSet K m) (hb : b ∈ chebyshevSet K n) :
    a * b ∈ chebyshevSet K (m + n) := by
  rcases ha with ⟨ha0, p, hpm, hpa⟩
  rcases hb with ⟨hb0, q, hqn, hqb⟩
  refine ⟨mul_nonneg ha0 hb0, p * q, ?_, ?_⟩
  · refine ⟨hpm.1.mul hqn.1, ?_⟩
    rw [natDegree_mul hpm.1.ne_zero hqn.1.ne_zero, hpm.2, hqn.2]
  · intro X hX
    calc ‖(p * q).eval X‖ = ‖(p.eval X) * (q.eval X)‖ := by rw [eval_mul]
      _ ≤ ‖p.eval X‖ * ‖q.eval X‖ := norm_mul_le _ _
      _ ≤ a * b := mul_le_mul (hpa X hX) (hqb X hX) (norm_nonneg _) ha0

/-- Real-infimum analogue of "multiplication by a nonnegative constant
commutes with an infimum over the left factor": if `c ≤ b * a` for every
`a ∈ A` and `0 ≤ b`, then `c ≤ b * sInf A`. -/
lemma le_sInf_mul_of_forall_le_mul {A : Set ℝ} {b c : ℝ} (hAne : A.Nonempty)
    (hAbdd : BddBelow A) (hb : 0 ≤ b) (h : ∀ a ∈ A, c ≤ b * a) : c ≤ b * sInf A := by
  by_cases hb0 : b = 0
  · rcases hAne with ⟨a, ha⟩
    have hc0 : c ≤ 0 := by
      calc c ≤ b * a := h a ha
      _ = 0 := by simp [hb0]
    simpa [hb0] using hc0
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hle : c / b ≤ sInf A := by
      apply (le_csInf_iff hAbdd hAne).2
      intro a ha
      exact (div_le_iff₀ hbpos).2 (by
        calc c ≤ b * a := h a ha
        _ = a * b := by ring)
    calc c = b * (c / b) := by rw [mul_div_cancel₀ c hb0]
      _ ≤ b * sInf A := mul_le_mul_of_nonneg_left hle hbpos.le

/-- Infima multiply in the right order: if `c` lies below every product
`a·b` (all elements of `A`, `B` nonnegative), then `c` lies below the
product of the infima. -/
lemma csInf_le_csInf_mul {A B : Set ℝ} (hAne : A.Nonempty) (hAbdd : BddBelow A)
    (hApos : ∀ a ∈ A, 0 ≤ a) (hBne : B.Nonempty) (hBbdd : BddBelow B)
    (hBpos : ∀ b ∈ B, 0 ≤ b) {c : ℝ} (h : ∀ a ∈ A, ∀ b ∈ B, c ≤ a * b) :
    c ≤ sInf A * sInf B := by
  have hA0 : 0 ≤ sInf A := le_csInf hAne (by intro a ha; exact hApos a ha)
  have h2 : ∀ b ∈ B, c ≤ sInf A * b := by
    intro b hb
    have hstep : c ≤ b * sInf A :=
      le_sInf_mul_of_forall_le_mul hAne hAbdd (hBpos b hb) (fun a ha => by
        calc c ≤ a * b := h a ha b hb
        _ = b * a := by ring)
    rwa [mul_comm b] at hstep
  exact le_sInf_mul_of_forall_le_mul hBne hBbdd hA0 h2

/-- **Submultiplicativity of the Chebyshev numbers** (elementary core of
Fekete's theorem): `t_{m+n} ≤ t_m·t_n`.  Needs `K` nonempty and bounded so
the defining sets are nonempty and `csInf` reasoning applies. -/
lemma chebyshev_submultiplicative {K : Set ℂ} (hKne : K.Nonempty)
    (hKb : Bornology.IsBounded K) (m n : ℕ) :
    chebyshevNumber K (m + n) ≤ chebyshevNumber K m * chebyshevNumber K n := by
  change sInf (chebyshevSet K (m + n)) ≤ sInf (chebyshevSet K m) * sInf (chebyshevSet K n)
  apply csInf_le_csInf_mul (A := chebyshevSet K m) (B := chebyshevSet K n)
  · exact chebyshevSet_nonempty K hKb m
  · exact chebyshevSet_bddBelow K m
  · intro c hc
    exact hc.1
  · exact chebyshevSet_nonempty K hKb n
  · exact chebyshevSet_bddBelow K n
  · intro c hc
    exact hc.1
  · intro a ha b hb
    exact csInf_le (chebyshevSet_bddBelow K (m + n)) (chebyshevSet_mul_mem ha hb)

/-- If `sInf S < a` then some member of the (nonempty, bounded-below) set
`S` is strictly below `a` (the infimum is approached by members). -/
lemma member_lt_of_sInf_lt {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddBelow S) {a : ℝ}
    (h : sInf S < a) : ∃ b ∈ S, b < a := by
  exact (csInf_lt_iff hbdd hne).1 h

/-- **Inf-approachability.**  A strict bound on the Chebyshev number is
witnessed by an actual monic polynomial. -/
lemma chebyshevNumber_lt_exists_bound {K : Set ℂ} (hK : Bornology.IsBounded K)
    {n : ℕ} {c : ℝ} (hc : chebyshevNumber K n < c) :
    ∃ p ∈ MonicDeg n, ∀ X ∈ K, ‖p.eval X‖ ≤ c := by
  have hne : (chebyshevSet K n).Nonempty := chebyshevSet_nonempty K hK n
  have hbdd : BddBelow (chebyshevSet K n) := chebyshevSet_bddBelow K n
  have hc' : sInf (chebyshevSet K n) < c := by
    simpa [chebyshevNumber, chebyshevSet] using hc
  rcases member_lt_of_sInf_lt hne hbdd hc' with ⟨s, hs, hslt⟩
  rcases hs with ⟨hs0, p, hpm, hpb⟩
  refine ⟨p, hpm, ?_⟩
  intro X hX
  exact le_trans (hpb X hX) (le_of_lt hslt)

/-- **Decay of the Chebyshev numbers gives polynomial decay** (the converse
of `polyDecay_imp_chebyshev`): from `chebyshevNumber K j ≤ C·θ^j` for all
`j ≥ 1` (with `0 ≤ C`, `0 ≤ θ < 1`) extract actual monic witnesses on `K`.
Pick `θ' := (θ + 1)/2` (so `θ < θ' < 1`) and `C' := C + 1`; then
`C·θ^j ≤ C·θ'^j < (C+1)·θ'^j`, so `chebyshevNumber K j < (C+1)·θ'^j` and
`chebyshevNumber_lt_exists_bound` yields the witness. -/
lemma chebyshev_decay_imp_polyDecay {K : Set ℂ} (hKne : K.Nonempty)
    (hK : Bornology.IsBounded K) {C θ : ℝ} (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (h : ∀ j : ℕ, 1 ≤ j → chebyshevNumber K j ≤ C * θ ^ j) :
    PolyDecayOn K := by
  let θ' : ℝ := (θ + 1) / 2
  have hθ'0 : 0 ≤ θ' := by
    dsimp [θ']
    nlinarith
  have hθθ' : θ < θ' := by
    dsimp [θ']
    linarith
  have hθθ'' : θ ≤ θ' := le_of_lt hθθ'
  have hθ'pos : 0 < θ' := lt_of_le_of_lt hθ0 hθθ'
  have hθ'1 : θ' < 1 := by
    dsimp [θ']
    linarith
  refine ⟨C + 1, θ', hθ'0, hθ'1, ?_⟩
  intro j hj
  have hcb : chebyshevNumber K j < (C + 1) * θ' ^ j := by
    have hp1 : C * θ ^ j ≤ C * θ' ^ j := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hθ0 hθθ'' j) hC
    have hp2 : C * θ' ^ j < (C + 1) * θ' ^ j := by
      rw [add_mul, one_mul]
      exact lt_add_of_pos_right (C * θ' ^ j) (pow_pos hθ'pos j)
    exact lt_of_le_of_lt (h j hj) (lt_of_le_of_lt hp1 hp2)
  rcases chebyshevNumber_lt_exists_bound (K := K) (n := j) hK hcb with ⟨p, hpm, hb⟩
  exact ⟨p, hpm, hb⟩

/-- **Fekete's equality (PROVED via `Submission.FeketeLim`).**  The
Chebyshev root numbers and the Fekete root numbers have the same limsup
(the common value is the logarithmic capacity).  Fekete's theorem. -/
theorem fekete_chebyshev_equality (K : Set ℂ) (hKne : K.Nonempty)
    (hKb : Bornology.IsBounded K) :
    Filter.limsup (fun n : ℕ => (chebyshevNumber K (n + 1)) ^ (1 / ((n + 1 : ℝ)))) Filter.atTop
      = Filter.limsup (fun n : ℕ => (feketeNumber K (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))) Filter.atTop := by
  simpa [feketeNumber, vdm, chebyshevNumber, MonicDeg,
    Submission.FeketeLim.feketeNumber, Submission.FeketeLim.feketeSet,
    Submission.FeketeLim.vdm, Submission.FeketeLim.chebyshevNumber,
    Submission.FeketeLim.MonicDeg] using
      (Submission.FeketeLim.fekete_chebyshev_equality K hKne hKb)

lemma feketeNumber_eq_SS1 (K : Set ℂ) (n : ℕ) :
    feketeNumber K n = Submission.SS1.feketeNumber K n := by
  simp [feketeNumber, Submission.SS1.feketeNumber, vdm, Submission.SS1.vdm,
    Submission.SS1.feketeSet]

/-- **SS1 (DEEP -- Dubinin's inequality in Fekete form).**  A hedgehog
`star S` whose `s := |dirSet S|` spikes are all strictly shorter than
`4^(1/s)` has Fekete numbers decaying geometrically in the exponent
`n(n−1)/2`: for some `0 ≤ ρ < 1`, `C ≥ 0`, every `n ≥ 1` satisfies
`feketeNumber (star S) n ≤ C · ρ^(n(n−1)/2)`.  (Sharp form:
`limsup feketeNumber(star S) n^(2/(n(n−1))) ≤ 4^(−1/s)·max ‖w‖ < 1`.)
This is the genuinely deep potential-theoretic content: the classical
proof bounds the Fekete (max-Vandermonde) configurations on the hedgehog
by distributing the `n` points among the `s` spikes and applying the
single-segment Chebyshev/Fekete bound per spike together with a
symmetrization/angular argument (Dubinin 1985), or via Eremenko's
conformal representation + the verified Konyagin–Lev circle inequality. -/
theorem fekete_decay_of_short_spikes (S : Finset ℂ) (hs : 0 < (dirSet S).card)
    (hshort : ∀ w ∈ spikeEndpoints S,
      ‖w‖ < (4 : ℝ) ^ (1 / ((dirSet S).card : ℝ))) :
    ∃ ρ C : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ 0 ≤ C ∧
      ∀ n : ℕ, 1 ≤ n →
        feketeNumber (Submission.XTransfer.star S) n ≤ C * ρ ^ (n * (n - 1) / 2) := by
  classical
  rcases (Submission.SS1.fekete_decay_of_short_spikes S hs hshort) with ⟨ρ, C, hρ0, hρ1, hC0, hmain⟩
  refine ⟨ρ, C, hρ0, hρ1, hC0, ?_⟩
  intro n hn
  have hb := hmain n hn
  simpa [feketeNumber_eq_SS1] using hb

/-- **SS2 (PROVED via `Submission.SS2`).**  Geometric decay of the Fekete
numbers of `star S` (rate `ρ < 1`) gives polynomial decay on `star S`
(`PolyDecayOn`). -/
theorem polyDecay_star_of_fekete_decay (S : Finset ℂ) (hSne : S.Nonempty)
    (hm : ∃ ρ C : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ 0 ≤ C ∧
      ∀ n : ℕ, 1 ≤ n →
        feketeNumber (Submission.XTransfer.star S) n ≤ C * ρ ^ (n * (n - 1) / 2)) :
    PolyDecayOn (Submission.XTransfer.star S) := by
  classical
  rcases (Submission.SS2.polyDecay_star_of_fekete_decay S hSne hm) with ⟨C, θ, hθ0, hθ1, hp⟩
  refine ⟨C, θ, hθ0, hθ1, ?_⟩
  intro j hj
  rcases hp j hj with ⟨p, hpm, hdeg, hb⟩
  refine ⟨p, ⟨hpm, hdeg⟩, hb⟩

/-- **SS3 (PROVED via `Submission.SS3asm`).**  Polynomial decay on the
hedgehog `star S` lifts to decay on some fattening `FatStar S ε`
(`∃ ε > 0, PolyDecayOn (FatStar S ε)`): the witnesses on the star grow on
the ε-neighbourhood of each spike by the uniform segment-growth lemma
(`Submission.SS3core.segment_growth`), and for small ε the enlarged base
stays below the decay rate.  Needs `S.Nonempty` (the star is nonempty)
and all spike endpoints nonzero (each conjugate is nonzero in the
application). -/
theorem polyDecay_fat_of_star (S : Finset ℂ) (hSne : S.Nonempty)
    (hw0 : ∀ w ∈ spikeEndpoints S, w ≠ 0)
    (hdec : PolyDecayOn (Submission.XTransfer.star S)) :
    ∃ ε : ℝ, 0 < ε ∧ PolyDecayOn (FatStar S ε) := by
  classical
  rcases hdec with ⟨C, θ, hθ0, hθ1, hp⟩
  let C0 : ℝ := max C 0
  have hC0 : 0 ≤ C0 := le_max_right C 0
  -- rebuild the rate with the nonnegative constant C0
  have hdec0 : Submission.SS3asm.PolyDecayRate (Submission.XTransfer.star S) C0 θ := by
    intro j hj
    rcases hp j hj with ⟨p, hmem, hb⟩
    have hpm : p.Monic := hmem.1
    have hdeg : p.natDegree = j := hmem.2
    refine ⟨p, hpm, hdeg, ?_⟩
    intro X hX
    exact le_trans (hb X hX)
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (pow_nonneg hθ0 j))
  rcases (Submission.SS3asm.polyDecay_fat_of_star_decay (S := S) hSne hw0 hC0 hθ0 hθ1 hdec0)
    with ⟨ε, hε, C', θ', hθ'0, hθ'1, hrate⟩
  refine ⟨ε, hε, C', θ', hθ'0, hθ'1, ?_⟩
  intro j hj
  rcases hrate j hj with ⟨p, hpm, hdeg, hb⟩
  refine ⟨p, ⟨hpm, hdeg⟩, hb⟩

/-- **Dubinin content (ASSEMBLY; the E1 crux in `PolyDecayOn` form).**  A
hedgehog whose `s` spikes are all strictly shorter than `4^(1/s)` is
polynomially controllable on a fattening.  = SS1 + SS2 + SS3.  Via
`polyDecay_fatStar_iff_hedgehogBound` this is
`E1Content.hedgehogBound_of_short_spikes`. -/
theorem hedgehog_decay_of_short_spikes (S : Finset ℂ) (hSne : S.Nonempty)
    (hw0 : ∀ w ∈ spikeEndpoints S, w ≠ 0)
    (hs : 0 < (dirSet S).card)
    (hshort : ∀ w ∈ spikeEndpoints S,
      ‖w‖ < (4 : ℝ) ^ (1 / ((dirSet S).card : ℝ))) :
    ∃ ε : ℝ, 0 < ε ∧ PolyDecayOn (FatStar S ε) := by
  have hdec := fekete_decay_of_short_spikes S hs hshort
  have hpoly := polyDecay_star_of_fekete_decay S hSne hdec
  exact polyDecay_fat_of_star S hSne hw0 hpoly
end Submission.Dubinin

end
