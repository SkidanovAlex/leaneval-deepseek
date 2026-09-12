import Mathlib
import Submission.FeketeSeq
import Submission.EngineUpper
import Submission.EngineLower

/-!
# Isolated task: the Cesàro/limsup Fekete equality (two-sided sandwich)

Self-contained definitions (mirror of Submission/Dubinin.lean where the
result will later live).  Prove ONLY the declarations below; leave nothing unfinished.  You may import the proved modules Submission.Fekete,
Submission.FeketeRev, Submission.FeketeSeq for the finitary comparisons
(DL1: `Submission.FeketeSeq.fekete_succ_le` : m_{n+1} ≤ (n+1)·t_n·m_n;
DL2: `Submission.FeketeSeq.cheb_le_fekete_succ_div` : t_n ≤ m_{n+1}/m_n),
and Submission.Dubinin is NOT importable (it still has unfinished
proofs) -- copy
`chebyshev_submultiplicative` (t_{m+n} ≤ t_m·t_n) locally if you need it
(it is short; its statement needs `K.Nonempty` and bounded `K`).

MAIN THEOREM (`fekete_chebyshev_equality`): for `K : Set ℂ` nonempty and
bounded,

    limsup_n (chebyshevNumber K (n+1))^(1/(n+1))
      = limsup_n (feketeNumber K (n+1))^(2/((n+1)·n))

(the two limsups over `n : ℕ` at `Filter.atTop`; the common value is the
logarithmic capacity).  Decompose as `le_antisymm` of:

  UPPER (`chebyshev_root_le_fekete_root`):
      limsup t-root ≤ limsup m-root.
      Skeleton: DL1 says log m_{n+1} − log m_n ≤ log(n+1) + log t_n (for
      the eventually positive case; handle zeros separately).  Summing
      n = 1..N: log m_{N+1} ≤ log m_1 + Σ log(k+1) + Σ log t_k.  Divide by
      N(N+1)/2 and take limsups: (Σ log t_k)/(N(N+1)/2) ≤ max_{k≤N}
      (log t_k)/k (each k-term contributes k·(log t_k/k), and
      Σ_{k≤N} k ≤ N(N+1)/2), so the limsup of the left is ≤ the limsup of
      (1/k)·log t_k; the Σ log(k+1) term is o(N²) and vanishes.  This
      yields limsup (2/(N(N+1)))·log m_{N+1} ≤ limsup (1/k)·log t_k, i.e.
      the m-root limsup ≤ the t-root limsup.

  LOWER (`fekete_root_le_chebyshev_root`):
      limsup m-root ≤ limsup t-root.
      Skeleton: DL2 says log t_n ≤ log m_{n+1} − log m_n.  Summing:
      Σ_{n=1}^N log t_n ≤ log m_{N+1} − log m_1.  Since (for each fixed
      k ≤ N) (1/k)·log t_k ≤ (Σ_{n≤N} log t_n)·(1/k) only when log t_n ≥ 0
      -- instead use: liminf of the Cesàro average ≥ liminf of the
      sequence, or handle signs by splitting into the positive and
      negative parts / using the limsup of averages argument; then
      (1/k)·log t_k ≤ (2/(N(N+1)))·Σ log t_n·(stuff) via the same weighted
      argument inverted.  Concretely: it is enough to show, for every
      subsequential limit `a` of (1/k)·log t_k along `k_j → ∞`, that
      `a ≤ limsup (2/(N(N+1)))·log m_{N+1}`; along `k_j`, take `N = k_j`
      and use `(1/k_j)·log t_{k_j} ≤ (2/(k_j(k_j+1)))·Σ_{n≤k_j} log t_n +
      o(1)` -- valid since log t is eventually nonnegative (t_n ≥ 1 for
      all n when K has ≥ 2 points: the constant polynomial argument gives
      t_n ≥ ...; alternatively split Σ log t_n = Σ (log t_n)⁺ − Σ
      (log t_n)⁻ and bound only the positive part above by log m via DL2,
      the negative part being harmless for an upper bound of the limsup).

  Sign convention: work with `log (t_n)` etc.; convert back to powers
  `t_n^(1/n) = exp((1/n)·log t_n)` (Real.rpow / exp_log), using
  continuity and strict monotonicity of `exp` to pass limsups through.

SUGGESTED LOCAL HELPERS (add freely, with proofs): t-submultiplicativity
(t_{m+n} ≤ t_m t_n) copied from Dubinin; m-decreasing of the rooted
sequence `d_n := m_n^(2/(n(n−1)))` or the log-version
`(2/(n(n−1)))·log m_n ≤ (2/((n−1)(n−2)))·log m_{n−1}` (from DL1 or DL2:
DL2 gives log t_{n−1} ≤ log m_n − log m_{n−1} ≥ ... use `t_{n−1} ≥ 1`
so `log m_n − log m_{n−1} ≥ 0`?? not directly; derive instead
`(log m_{n+1} − log m_n)/n → 0`-type asymptotics from DL1+DL2 together
with submultiplicativity of t); Cesàro-weighted lemmas
(`Finset.sum_le_sum`, `geom`-free, `(Σ_{k≤N} k·a_k)/(Σ_{k≤N} k) ≤ max
a_k`); `log`/`exp`/`Real.rpow` identities (`Real.log_pow`,
`Real.exp_log`, `Real.rpow_def_of_pos`, continuity of `exp` and
`Real.log` on positives); `Filter.limsup_le_limsup`,
`Tendsto`/`limsup` interaction (`Filter.limsup_le`),
`Filter.limsup_le_limsup_of_le` if available, or prove directly with the
`limsup`-as-inf-of-sup characterization.

NOTES on ℝ: conditionally complete lattice lemmas as usual; `limsup` is
`Filter.limsup : (ℕ → ℝ) → Filter ℕ → ℝ` (total); use
`Filter.limsup_le_iff`, `Filter.le_limsup`, etc.  If the full equality
proves too heavy in one go, FIRST prove the two one-sided lemmas
(`chebyshev_root_le_fekete_root`, `fekete_root_le_chebyshev_root`) with
clean statements (state them before the main theorem), then assemble.
Do NOT change the main theorem's statement.
-/

noncomputable section

open scoped Real Polynomial Topology BigOperators

namespace Submission.FeketeLim

/-- Monic complex polynomials of degree exactly `n`. -/
def MonicDeg (n : ℕ) : Set ℂ[X] := {p : ℂ[X] | p.Monic ∧ p.natDegree = n}

/-- The Vandermonde product of `n` points. -/
def vdm (x : ℕ → ℂ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, ‖x j - x i‖

/-- The set of Vandermonde products over `n`-point configurations in `K`. -/
def feketeSet (K : Set ℂ) (n : ℕ) : Set ℝ :=
  {d : ℝ | ∃ x : ℕ → ℂ, (∀ i : ℕ, i < n → x i ∈ K) ∧ d = vdm x n}

/-- **Fekete number.** -/
def feketeNumber (K : Set ℂ) (n : ℕ) : ℝ := sSup (feketeSet K n)

/-- **Chebyshev number.** -/
def chebyshevNumber (K : Set ℂ) (n : ℕ) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ ∃ p ∈ MonicDeg n, ∀ X ∈ K, ‖p.eval X‖ ≤ c}


/-- A positive radius bounding the set. -/
lemma bounded_radius {K : Set ℂ} (hKb : Bornology.IsBounded K) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ‖z‖ ≤ R := hKb.exists_pos_norm_le

/-- Local copy: Vandermonde products are nonnegative. -/
lemma vdm_nonneg (x : ℕ → ℂ) (n : ℕ) : 0 ≤ vdm x n := by
  change 0 ≤ Submission.Fekete.vdm x n
  exact Submission.Fekete.vdm_nonneg x n

/-- Local copy: a norm-bounded configuration has a bounded Vandermonde
product. -/
lemma vdm_le_of_norm_le {x : ℕ → ℂ} {n : ℕ} {R : ℝ}
    (hx : ∀ k : ℕ, k < n → ‖x k‖ ≤ R) :
    vdm x n ≤ (max 1 (2 * R)) ^ (n * n) := by
  change Submission.FeketeRev.vdm x n ≤ (max 1 (2 * R)) ^ (n * n)
  exact Submission.FeketeRev.vdm_le_of_norm_le (x := x) (n := n) (R := R) hx

/-- Local copy: a monic bounded polynomial bounds the Chebyshev number. -/
lemma chebyshevNumber_le_of_bounds {K : Set ℂ} {n : ℕ} {p : ℂ[X]}
    (hp : p ∈ MonicDeg n) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ X ∈ K, ‖p.eval X‖ ≤ c) : chebyshevNumber K n ≤ c := by
  change Submission.Fekete.chebyshevNumber K n ≤ c
  exact Submission.Fekete.chebyshevNumber_le_of_bounds (E := K) (n := n) (p := p) hp hc hb

/-- Local copy: the Chebyshev number is bounded by the Fekete ratio. -/
lemma chebyshevNumber_le_fekete_ratio {K : Set ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hE : Bornology.IsBounded K) {x : ℕ → ℂ}
    (hx : ∀ i : ℕ, i < n → x i ∈ K) (hv : 0 < vdm x n) :
    chebyshevNumber K n ≤ feketeNumber K (n + 1) / vdm x n := by
  change Submission.Fekete.chebyshevNumber K n ≤
    Submission.Fekete.feketeNumber K (n + 1) / Submission.Fekete.vdm x n
  exact Submission.Fekete.chebyshevNumber_le_fekete_ratio (E := K) (n := n) hn hE hx hv

/-- Local copy: reverse finitary Fekete comparison (no compactness needed). -/
lemma vdm_le_of_monic_bound {K : Set ℂ} {N : ℕ} (hN : 1 ≤ N) {p : ℂ[X]}
    (hpmonic : p.Monic) (hpdeg : p.natDegree = N) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ X ∈ K, ‖p.eval X‖ ≤ M) {x : ℕ → ℂ}
    (hx : ∀ i : ℕ, i < N + 1 → x i ∈ K) :
    vdm x (N + 1) ≤ (N + 1 : ℝ) * M * feketeNumber K N := by
  have hv := Submission.FeketeRev.vdm_le_of_monic_bound (E := K) (N := N) hN hpmonic hpdeg
    (M := M) hM hb (x := x) hx
  change Submission.FeketeRev.vdm x (N + 1) ≤ (N + 1 : ℝ) * M * Submission.FeketeRev.feketeNumber K N at hv
  exact hv

/-- `chebyshevNumber K n` is nonnegative for bounded `K` and `1 ≤ n`. -/
lemma chebyshevNumber_nonneg {K : Set ℂ} (hKb : Bornology.IsBounded K) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ chebyshevNumber K n := by
  unfold chebyshevNumber
  let S : Set ℝ := {c : ℝ | 0 ≤ c ∧ ∃ p : ℂ[X], p ∈ MonicDeg n ∧ ∀ X ∈ K, ‖p.eval X‖ ≤ c}
  have hS_bdd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro c hc
    exact hc.1
  have hS_ne : S.Nonempty := by
    let p : ℂ[X] := (Polynomial.X : ℂ[X]) ^ n
    rcases hKb.exists_pos_norm_le with ⟨R, hRpos, hR⟩
    refine ⟨R ^ n, ⟨pow_nonneg (le_of_lt hRpos) n, p, ?_, ?_⟩⟩
    · dsimp [p, MonicDeg]
      constructor
      · exact Polynomial.monic_X.pow n
      · rw [Polynomial.natDegree_X_pow]
    · intro z hz
      have hzR : ‖z‖ ≤ R := hR z hz
      calc
        ‖p.eval z‖ = ‖z ^ n‖ := by simp [p]
        _ = ‖z‖ ^ n := by rw [norm_pow]
        _ ≤ R ^ n := by gcongr
  exact le_csInf hS_ne (fun c hc => hc.1)

/-- `feketeNumber K n` is nonnegative for nonempty bounded `K`. -/
lemma feketeNumber_nonneg {K : Set ℂ} (hKne : K.Nonempty) (hKb : Bornology.IsBounded K) (n : ℕ) :
    0 ≤ feketeNumber K n := by
  rcases hKne with ⟨e, he⟩
  have hmem : vdm (fun _ : ℕ => e) n ∈ feketeSet K n := by
    refine ⟨fun _ : ℕ => e, ?_, rfl⟩
    intro i hi
    exact he
  have hbdd : BddAbove (feketeSet K n) := by
    rcases hKb.exists_pos_norm_le with ⟨R, hRpos, hR⟩
    refine ⟨(max 1 (2 * R)) ^ (n * n), ?_⟩
    intro d hd
    rcases hd with ⟨x, hx, rfl⟩
    exact vdm_le_of_norm_le (x := x) (n := n) (R := R) (fun k hk => hR (x k) (hx k hk))
  exact le_trans (vdm_nonneg (fun _ : ℕ => e) n) (le_csSup hbdd hmem)

/-- The single-point Fekete number is `1`. -/
lemma feketeNumber_one {K : Set ℂ} (hKne : K.Nonempty) : feketeNumber K 1 = 1 := by
  have hmem : (1 : ℝ) ∈ {d : ℝ | ∃ x : ℕ → ℂ, (∀ i : ℕ, i < 1 → x i ∈ K) ∧ d = vdm x 1} := by
    rcases hKne with ⟨e, he⟩
    refine ⟨fun _ => e, ?_, ?_⟩
    · intro i hi
      exact he
    · unfold vdm
      simp
  have hall : ∀ d ∈ {d : ℝ | ∃ x : ℕ → ℂ, (∀ i : ℕ, i < 1 → x i ∈ K) ∧ d = vdm x 1}, d ≤ 1 := by
    intro d hd
    rcases hd with ⟨x, hx, rfl⟩
    unfold vdm
    simp
  unfold feketeNumber feketeSet
  refine le_antisymm ?_ ?_
  · exact csSup_le ⟨1, hmem⟩ hall
  · exact le_csSup ⟨1, hall⟩ hmem

/-- `chebyshevNumber K n ≤ R^n` when `R` bounds `K`. -/
lemma chebyshevNumber_le_pow {K : Set ℂ} {n : ℕ} {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) : chebyshevNumber K n ≤ R ^ n := by
  let p : ℂ[X] := (Polynomial.X : ℂ[X]) ^ n
  have hp : p ∈ MonicDeg n := by
    dsimp [p, MonicDeg]
    constructor
    · exact Polynomial.monic_X.pow n
    · rw [Polynomial.natDegree_X_pow]
  have hb : ∀ X ∈ K, ‖p.eval X‖ ≤ R ^ n := by
    intro X hX
    calc
      ‖p.eval X‖ = ‖X ^ n‖ := by simp [p]
      _ = ‖X‖ ^ n := by rw [norm_pow]
      _ ≤ R ^ n := pow_le_pow_left₀ (norm_nonneg X) (hR X hX) n
  exact chebyshevNumber_le_of_bounds hp (pow_nonneg hR0 n) hb

/-- `feketeNumber K n ≤ (max 1 (2R))^(n*n)` when `R` bounds `K`. -/
lemma feketeNumber_le_sq {K : Set ℂ} (hKne : K.Nonempty) {n : ℕ} {R : ℝ}
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) :
    feketeNumber K n ≤ (max 1 (2 * R)) ^ (n * n) := by
  unfold feketeNumber
  refine csSup_le ?_ ?_
  · rcases hKne with ⟨w, hw⟩
    refine ⟨vdm (fun _ => w) n, ?_⟩
    refine ⟨fun _ => w, ?_, rfl⟩
    intro i hi
    exact hw
  · intro d hd
    rcases hd with ⟨x, hx, rfl⟩
    exact vdm_le_of_norm_le (x := x) (n := n) (R := R) (fun k hk => hR (x k) (hx k hk))

/-- Local copy: epsilon-based `A ≤ B` argument. -/
lemma le_of_forall_pos_le_smul {A B C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε : ℝ, 0 < ε → A ≤ B + C * ε) : A ≤ B :=
  Submission.FeketeSeq.le_of_forall_pos_le_smul (A := A) (B := B) (C := C) hC h

/-- Near-optimal Chebyshev polynomial: for every `ε > 0` there is a monic
degree-`n` polynomial bounded by `chebyshevNumber K n + ε` on `K`. -/
lemma exists_monic_chebyshev_add {K : Set ℂ} (hKb : Bornology.IsBounded K) {n : ℕ} (hn : 1 ≤ n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X], p.Monic ∧ p.natDegree = n ∧
      ∀ X ∈ K, ‖p.eval X‖ ≤ chebyshevNumber K n + ε := by
  let S : Set ℝ := {c : ℝ | 0 ≤ c ∧ ∃ p : ℂ[X],
    p ∈ MonicDeg n ∧ ∀ X ∈ K, ‖p.eval X‖ ≤ c}
  have hS_bdd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro c hc
    exact hc.1
  have hS_ne : S.Nonempty := by
    let p : ℂ[X] := (Polynomial.X : ℂ[X]) ^ n
    rcases hKb.exists_pos_norm_le with ⟨R, hRpos, hR⟩
    refine ⟨R ^ n, ⟨pow_nonneg (le_of_lt hRpos) n, p, ?_, ?_⟩⟩
    · dsimp [p, MonicDeg]
      constructor
      · exact Polynomial.monic_X.pow n
      · rw [Polynomial.natDegree_X_pow]
    · intro z hz
      calc
        ‖p.eval z‖ = ‖z ^ n‖ := by simp [p]
        _ = ‖z‖ ^ n := by rw [norm_pow]
        _ ≤ R ^ n := pow_le_pow_left₀ (norm_nonneg z) (hR z hz) n
  have hlt : sInf S < chebyshevNumber K n + ε := by
    change sInf {c : ℝ | 0 ≤ c ∧ ∃ p : ℂ[X], p ∈ MonicDeg n ∧ ∀ X ∈ K, ‖p.eval X‖ ≤ c}
      < chebyshevNumber K n + ε
    unfold chebyshevNumber
    linarith
  rcases Submission.FeketeSeq.member_lt_of_sInf_lt hS_ne hS_bdd hlt with ⟨c, hcS, hclt⟩
  rcases hcS with ⟨hc0, p, hpMem, hpb⟩
  rcases hpMem with ⟨hpmonic, hpdeg⟩
  refine ⟨p, hpmonic, hpdeg, ?_⟩
  intro X hX
  exact le_trans (hpb X hX) (le_of_lt hclt)

/-- A near-optimal configuration for the `(n+1)`-point Fekete number: for
every `δ > 0` there is an `(n+1)`-configuration in `K` whose Vandermonde
product exceeds `feketeNumber K (n+1) − δ`. -/
lemma exists_fekete_approx {K : Set ℂ} (hKne : K.Nonempty) (hKb : Bornology.IsBounded K)
    {n : ℕ} (δ : ℝ) (hδ : 0 < δ) :
    ∃ x : ℕ → ℂ, (∀ i : ℕ, i < n + 1 → x i ∈ K) ∧
      feketeNumber K (n + 1) - δ < vdm x (n + 1) := by
  have hS_ne : (feketeSet K (n + 1)).Nonempty := by
    rcases hKne with ⟨e, he⟩
    refine ⟨vdm (fun _ => e) (n + 1), ?_⟩
    refine ⟨fun _ => e, ?_, rfl⟩
    intro i hi
    exact he
  have hS_bdd : BddAbove (feketeSet K (n + 1)) := by
    rcases hKb.exists_pos_norm_le with ⟨R, hRpos, hR⟩
    refine ⟨(max 1 (2 * R)) ^ ((n + 1) * (n + 1)), ?_⟩
    intro d hd
    rcases hd with ⟨x, hx, rfl⟩
    exact vdm_le_of_norm_le (x := x) (n := n + 1) (R := R) (fun k hk => hR (x k) (hx k hk))
  have hlt' : feketeNumber K (n + 1) - δ < sSup (feketeSet K (n + 1)) := by
    simpa [feketeNumber] using (show feketeNumber K (n + 1) - δ < feketeNumber K (n + 1) by linarith)
  rcases (lt_csSup_iff hS_bdd hS_ne).1 hlt' with ⟨d, hdmem, hdlt⟩
  rcases hdmem with ⟨x, hx, rfl⟩
  exact ⟨x, hx, hdlt⟩

/-- **DL1 without compactness**: `m_{n+1} ≤ (n+1)·t_n·m_n` for bounded
nonempty `K`. -/
lemma fekete_succ_le_of_bounded {K : Set ℂ} (hKne : K.Nonempty) (hKb : Bornology.IsBounded K)
    {n : ℕ} (hn : 1 ≤ n) :
    feketeNumber K (n + 1) ≤ (n + 1 : ℝ) * chebyshevNumber K n * feketeNumber K n := by
  let tn : ℝ := chebyshevNumber K n
  let mN : ℝ := feketeNumber K n
  let mN1 : ℝ := feketeNumber K (n + 1)
  change mN1 ≤ ((n + 1 : ℝ) * tn) * mN
  have hmn0 : 0 ≤ mN := by
    dsimp [mN]
    exact feketeNumber_nonneg hKne hKb n
  have htn0 : 0 ≤ tn := by
    dsimp [tn]
    exact chebyshevNumber_nonneg hKb hn
  have hinner : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → mN1 ≤ ((n + 1 : ℝ) * (tn + ε)) * mN + δ := by
    intro ε hε δ hδ
    rcases exists_monic_chebyshev_add (K := K) hKb (n := n) hn ε hε with ⟨p, hpmonic, hpdeg, hpb⟩
    rcases exists_fekete_approx (K := K) hKne hKb (n := n) δ hδ with ⟨x, hx, hvdmgt⟩
    have hv : vdm x (n + 1) ≤ (n + 1 : ℝ) * (tn + ε) * mN := by
      have hmain := vdm_le_of_monic_bound (K := K) (N := n) hn hpmonic hpdeg
        (M := tn + ε) (hM := by linarith) (hb := hpb) (x := x) (hx := hx)
      dsimp [mN] at hmain ⊢
      simpa [mul_assoc] using hmain
    have hlt2 : mN1 - δ < ((n + 1 : ℝ) * (tn + ε)) * mN := by
      dsimp [mN1]
      exact lt_of_lt_of_le hvdmgt hv
    linarith
  have hForall : ∀ ε : ℝ, 0 < ε → mN1 ≤ ((n + 1 : ℝ) * (tn + ε)) * mN := by
    intro ε hε
    exact le_of_forall_pos_le_add (fun δ hδ => hinner ε hε δ hδ)
  apply le_of_forall_pos_le_smul (A := mN1) (B := ((n + 1 : ℝ) * tn) * mN) (C := (n + 1 : ℝ) * mN)
  · exact mul_nonneg (by positivity) hmn0
  · intro ε hε
    have hh := hForall ε hε
    nlinarith

/-- **DL2 without compactness** (multiplicative form): `t_n·m_n ≤ m_{n+1}`
when `0 < m_n`. -/
lemma cheb_mul_le_fekete_succ_of_bounded {K : Set ℂ} (hKne : K.Nonempty)
    (hKb : Bornology.IsBounded K) {n : ℕ} (hn : 1 ≤ n)
    (hm : 0 < feketeNumber K n) :
    chebyshevNumber K n * feketeNumber K n ≤ feketeNumber K (n + 1) := by
  let tn : ℝ := chebyshevNumber K n
  let mN : ℝ := feketeNumber K n
  let mN1 : ℝ := feketeNumber K (n + 1)
  change tn * mN ≤ mN1
  have htn0 : 0 ≤ tn := by
    dsimp [tn]
    exact chebyshevNumber_nonneg hKb hn
  have hmn : 0 < mN := by simpa [mN] using hm
  have hinner : ∀ δ : ℝ, 0 < δ → δ < mN → tn * (mN - δ) ≤ mN1 := by
    intro δ hδ hδm
    have hsucc : (n - 1) + 1 = n := by omega
    rcases exists_fekete_approx (K := K) hKne hKb (n := n - 1) δ hδ with ⟨x, hx, hvdmgt⟩
    have hx' : ∀ i : ℕ, i < n → x i ∈ K := by
      intro i hi
      exact hx i (by omega)
    have hvdmgt' : feketeNumber K n - δ < vdm x n := by
      simpa [mN, hsucc] using hvdmgt
    have hvdmpos : 0 < vdm x n := by
      have : 0 < mN - δ := by linarith
      exact lt_trans this hvdmgt'
    have hratio := chebyshevNumber_le_fekete_ratio (K := K) (n := n) hn hKb hx' hvdmpos
    have hle : tn ≤ mN1 / vdm x n := by
      dsimp [tn, mN1] at hratio ⊢
      exact hratio
    have h1m : tn * vdm x n ≤ mN1 := (le_div_iff₀ hvdmpos).1 hle
    have h2 : tn * (mN - δ) ≤ tn * vdm x n := by
      exact mul_le_mul_of_nonneg_left (le_of_lt hvdmgt') htn0
    calc
      tn * (mN - δ) ≤ tn * vdm x n := h2
      _ ≤ mN1 := h1m
  have hgoal : tn * mN ≤ mN1 := by
    apply le_of_forall_pos_le_smul (A := tn * mN) (B := mN1) (C := tn)
    · exact htn0
    · intro ε hε
      let δ : ℝ := min (mN / 2) ε
      have hδ0 : 0 < δ := by
        dsimp [δ]
        exact lt_min (by linarith) hε
      have hδm : δ < mN := by
        dsimp [δ]
        have h1 : min (mN / 2) ε ≤ mN / 2 := min_le_left _ _
        exact lt_of_le_of_lt h1 (by linarith)
      have hh := hinner δ hδ0 hδm
      have hδe : δ ≤ ε := by
        dsimp [δ]
        exact min_le_right _ _
      nlinarith
  simpa [mul_comm, mul_left_comm, mul_assoc] using hgoal

/-- **Submultiplicativity of the Chebyshev numbers** (no compactness needed):
`t_{a+b} ≤ t_a·t_b`. -/
lemma chebyshev_mul_le_of_bounded {K : Set ℂ} (hKne : K.Nonempty) (hKb : Bornology.IsBounded K)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    chebyshevNumber K (a + b) ≤ chebyshevNumber K a * chebyshevNumber K b := by
  let ta : ℝ := chebyshevNumber K a
  let tb : ℝ := chebyshevNumber K b
  change chebyshevNumber K (a + b) ≤ ta * tb
  have hta0 : 0 ≤ ta := by dsimp [ta]; exact chebyshevNumber_nonneg hKb ha
  have htb0 : 0 ≤ tb := by dsimp [tb]; exact chebyshevNumber_nonneg hKb hb
  have hinner : ∀ ε : ℝ, 0 < ε → chebyshevNumber K (a + b) ≤ (ta + ε) * (tb + ε) := by
    intro ε hε
    rcases exists_monic_chebyshev_add (K := K) hKb (n := a) ha ε hε with ⟨pa, hpa_m, hpa_d, hpa_b⟩
    rcases exists_monic_chebyshev_add (K := K) hKb (n := b) hb ε hε with ⟨pb, hpb_m, hpb_d, hpb_b⟩
    have hp_m : (pa * pb).Monic := hpa_m.mul hpb_m
    have hp_d : (pa * pb).natDegree = a + b := by
      rw [Polynomial.natDegree_mul hpa_m.ne_zero hpb_m.ne_zero, hpa_d, hpb_d]
    have hpbnd : ∀ X ∈ K, ‖(pa * pb).eval X‖ ≤ (ta + ε) * (tb + ε) := by
      intro X hX
      calc
        ‖(pa * pb).eval X‖ = ‖(pa.eval X) * (pb.eval X)‖ := by simp
        _ ≤ ‖pa.eval X‖ * ‖pb.eval X‖ := norm_mul_le _ _
        _ ≤ (ta + ε) * (tb + ε) := by
          exact mul_le_mul (hpa_b X hX) (hpb_b X hX) (norm_nonneg (pb.eval X))
            (le_trans (norm_nonneg (pa.eval X)) (hpa_b X hX))
    have hM : 0 ≤ (ta + ε) * (tb + ε) := mul_nonneg (by linarith) (by linarith)
    have hmain := chebyshevNumber_le_of_bounds (p := pa * pb) ⟨hp_m, hp_d⟩ hM hpbnd
    dsimp [ta, tb]
    exact hmain
  have hgoal : chebyshevNumber K (a + b) ≤ ta * tb := by
    apply le_of_forall_pos_le_smul (A := chebyshevNumber K (a + b)) (B := ta * tb) (C := ta + tb + 1)
    · nlinarith
    · intro ε hε
      let m : ℝ := min ε 1
      have hh := hinner m (lt_min hε (by norm_num))
      have hε1 : m ≤ ε := by dsimp [m]; exact min_le_left _ _
      have h1ε : m ≤ (1 : ℝ) := by dsimp [m]; exact min_le_right _ _
      have hm0 : 0 ≤ m := by
        dsimp [m]
        exact le_of_lt (lt_min hε (by norm_num))
      have hsq : m * m ≤ m := by nlinarith
      nlinarith [hh, hε1, hta0, htb0, hsq]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hgoal

/-- Local copy: positive Vandermonde products for distinct points. -/
lemma vdm_pos {x : ℕ → ℂ} {n : ℕ} (hdist : ∀ a, a < n → ∀ b, b < a → x b ≠ x a) :
    0 < vdm x n := by
  change 0 < Submission.FeketeRev.vdm x n
  exact Submission.FeketeRev.vdm_pos (x := x) (n := n) hdist

/-- Local copy: `vdm = 0` when two configuration points coincide. -/
lemma vdm_eq_zero_of_lt {x : ℕ → ℂ} {n a b : ℕ} (hb : b < a) (ha : a < n) (hx : x b = x a) :
    vdm x n = 0 := by
  change Submission.FeketeRev.vdm x n = 0
  exact Submission.FeketeRev.vdm_eq_zero_of_lt (x := x) (n := n) (a := a) (b := b) hb ha hx

/-- Local copy: the family of Vandermonde products over a bounded set is
bounded above. -/
lemma feketeSet_bddAbove_of_bounded {K : Set ℂ} (hKb : Bornology.IsBounded K) (n : ℕ) :
    BddAbove (feketeSet K n) := by
  change BddAbove (Submission.FeketeRev.feketeSet K n)
  exact Submission.FeketeRev.feketeSet_bddAbove (E := K) (n := n) hKb

/-- Local copy: Lagrange interpolation identity for the leading coefficient. -/
lemma lagrange_sum_one {N : ℕ} {p : ℂ[X]} (hpmonic : p.Monic) (hpdeg : p.natDegree = N)
    {x : ℕ → ℂ} (hvs : Set.InjOn x (↑(Finset.range (N + 1)))) :
    (1 : ℂ) = ∑ i ∈ Finset.range (N + 1),
      p.eval (x i) / ∏ j ∈ (Finset.range (N + 1)).erase i, (x i - x j) :=
  Submission.FeketeRev.lagrange_sum_one (N := N) (p := p) hpmonic hpdeg (x := x) hvs

/-- For an infinite `K` the Fekete numbers are all strictly positive. -/
lemma feketeNumber_pos_of_infinite {K : Set ℂ} (hKb : Bornology.IsBounded K)
    (hKinf : K.Infinite) {n : ℕ} (hn : 1 ≤ n) : 0 < feketeNumber K n := by
  let φ : ℕ ↪ K := hKinf.natEmbedding
  let x : ℕ → ℂ := fun i => (φ i : K)
  have hxinK : ∀ i : ℕ, x i ∈ K := by
    intro i
    exact (φ i).2
  have hinj : ∀ a, a < n → ∀ b, b < a → x b ≠ x a := by
    intro a ha b hb h
    have hφ : (φ b : K) = (φ a : K) := by
      apply Subtype.ext
      exact h
    have : b = a := φ.injective hφ
    omega
  by_cases hn0 : n = 1
  · subst n
    simpa using (show 0 < feketeNumber K 1 by
      rw [feketeNumber_one (K := K)]
      · norm_num
      · exact hKinf.nonempty)
  · have hn2 : 2 ≤ n := by omega
    have hvdm : 0 < vdm x n := vdm_pos (x := x) (n := n) hinj
    have hmem : vdm x n ∈ feketeSet K n := by
      exact ⟨x, fun i hi => hxinK i, rfl⟩
    have hbdd : BddAbove (feketeSet K n) := feketeSet_bddAbove_of_bounded hKb n
    have hle : vdm x n ≤ feketeNumber K n := le_csSup hbdd hmem
    exact lt_of_lt_of_le hvdm hle

/-- For an infinite `K` the Chebyshev numbers are all strictly positive. -/
lemma chebyshevNumber_pos_of_infinite {K : Set ℂ} (hKb : Bornology.IsBounded K)
    (hKinf : K.Infinite) {n : ℕ} (hn : 1 ≤ n) : 0 < chebyshevNumber K n := by
  let φ : ℕ ↪ K := hKinf.natEmbedding
  let x : ℕ → ℂ := fun i => (φ i : K)
  have hxinK : ∀ i : ℕ, x i ∈ K := by
    intro i
    exact (φ i).2
  have hinj : ∀ a, a < n + 1 → ∀ b, b < a → x b ≠ x a := by
    intro a ha b hb h
    have hφ : (φ b : K) = (φ a : K) := by
      apply Subtype.ext
      exact h
    have : b = a := φ.injective hφ
    omega
  have hInjOn : Set.InjOn x (↑(Finset.range (n + 1))) := by
    intro a ha b hb h
    have ha' : a < n + 1 := by simpa using (Finset.mem_coe.mp ha)
    have hb' : b < n + 1 := by simpa using (Finset.mem_coe.mp hb)
    by_cases hab : a = b
    · exact hab
    · by_cases hab' : a < b
      · have : x a ≠ x b := hinj b hb' a hab'
        exact False.elim (this h)
      · have hba : b < a := lt_of_le_of_ne (le_of_not_gt hab') (Ne.symm hab)
        have : x b ≠ x a := hinj a ha' b hba
        exact False.elim (this h.symm)
  let sep : ℕ → ℝ := fun i => ∏ j ∈ (Finset.range (n + 1)).erase i, ‖x i - x j‖
  have hsep_pos : ∀ i, i ∈ Finset.range (n + 1) → 0 < sep i := by
    intro i hi
    dsimp [sep]
    refine Finset.prod_pos ?_
    intro j hj
    rcases Finset.mem_erase.mp hj with ⟨hji, hjn⟩
    have hi' : i < n + 1 := by simpa using hi
    have hj' : j < n + 1 := by simpa using hjn
    have hnei : j ≠ i := (Finset.mem_erase.mp hj).1
    have hne : x i ≠ x j := by
      by_cases hij : j < i
      · exact (hinj i hi' j hij).symm
      · have hle_i : i ≤ j := le_of_not_gt hij
        rcases lt_or_eq_of_le hle_i with hlt2 | heq
        · exact hinj j hj' i hlt2
        · exact False.elim (hnei heq.symm)
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  let sumInv : ℝ := ∑ i ∈ Finset.range (n + 1), (1 : ℝ) / sep i
  have hSum_pos : 0 < sumInv := by
    dsimp [sumInv]
    exact Finset.sum_pos (fun i hi => one_div_pos.mpr (hsep_pos i hi)) (by simp)
  let δ : ℝ := (sumInv)⁻¹
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact inv_pos.mpr hSum_pos
  let S : Set ℝ := {c : ℝ | 0 ≤ c ∧ ∃ p : ℂ[X], p ∈ MonicDeg n ∧ ∀ X ∈ K, ‖p.eval X‖ ≤ c}
  have hS_ne : S.Nonempty := by
    let p : ℂ[X] := (Polynomial.X : ℂ[X]) ^ n
    rcases hKb.exists_pos_norm_le with ⟨R, hRpos, hR⟩
    refine ⟨R ^ n, ⟨pow_nonneg (le_of_lt hRpos) n, p, ?_, ?_⟩⟩
    · dsimp [p, MonicDeg]
      constructor
      · exact Polynomial.monic_X.pow n
      · rw [Polynomial.natDegree_X_pow]
    · intro z hz
      calc
        ‖p.eval z‖ = ‖z ^ n‖ := by simp [p]
        _ = ‖z‖ ^ n := by rw [norm_pow]
        _ ≤ R ^ n := pow_le_pow_left₀ (norm_nonneg z) (hR z hz) n
  have hδ_mem_le : ∀ c ∈ S, δ ≤ c := by
    intro c hcS
    rcases hcS with ⟨hc0, p, hpMem, hpb⟩
    rcases hpMem with ⟨hpmonic, hpdeg⟩
    have h1 : (1 : ℝ) ≤ ∑ i ∈ Finset.range (n + 1), ‖p.eval (x i)‖ / sep i := by
      have hlc := lagrange_sum_one (N := n) (p := p) hpmonic hpdeg (x := x) hInjOn
      have hnorm := congrArg (fun z : ℂ => ‖z‖) hlc
      calc
        (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
        _ = ‖(∑ i ∈ Finset.range (n + 1),
            p.eval (x i) / ∏ j ∈ (Finset.range (n + 1)).erase i, (x i - x j))‖ := hnorm
        _ ≤ ∑ i ∈ Finset.range (n + 1),
            ‖p.eval (x i) / ∏ j ∈ (Finset.range (n + 1)).erase i, (x i - x j)‖ := norm_sum_le _ _
        _ = ∑ i ∈ Finset.range (n + 1), ‖p.eval (x i)‖ / sep i := by
          dsimp [sep]
          apply Finset.sum_congr rfl
          intro i hi
          rw [norm_div]
          congr 1
          rw [← norm_prod]
    have hle : (∑ i ∈ Finset.range (n + 1), ‖p.eval (x i)‖ / sep i) ≤ c * sumInv := by
      dsimp [sumInv]
      calc
        (∑ i ∈ Finset.range (n + 1), ‖p.eval (x i)‖ / sep i)
            ≤ ∑ i ∈ Finset.range (n + 1), c / sep i := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact div_le_div_of_nonneg_right (hpb (x i) (hxinK i)) (le_of_lt (hsep_pos i hi))
        _ = c * (∑ i ∈ Finset.range (n + 1), (1 : ℝ) / sep i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
    have h1c : (1 : ℝ) ≤ c * sumInv := le_trans h1 hle
    have hc' : (sumInv)⁻¹ ≤ c := by
      rw [← one_div]
      rw [div_le_iff₀ hSum_pos]
      simpa [mul_comm] using h1c
    dsimp [δ]
    exact hc'
  have hle_inf : δ ≤ chebyshevNumber K n := by
    change δ ≤ sInf S
    exact le_csInf hS_ne hδ_mem_le
  exact lt_of_lt_of_le hδpos hle_inf

open Polynomial in
/-- For finite `K` with `s` points the Chebyshev numbers of degree `≥ s`
vanish. -/
lemma chebyshevNumber_eq_zero_of_finite {K : Set ℂ} (hKf : K.Finite)
    {n : ℕ} (hn : (hKf.toFinset).card ≤ n) : chebyshevNumber K n = 0 := by
  let s : Finset ℂ := hKf.toFinset
  have hmemK : ∀ z ∈ K, z ∈ s := by
    intro z hz
    simpa [s] using (hKf.mem_toFinset).2 hz
  let p : ℂ[X] := (∏ a ∈ s, (X - C a)) * X ^ (n - s.card)
  have hprod_monic : (∏ a ∈ s, (X - C a)).Monic :=
    monic_prod_of_monic s (fun a => X - C a) (fun a ha => monic_X_sub_C a)
  have hp_monic : p.Monic := by
    dsimp [p]
    exact hprod_monic.mul (monic_X.pow (n - s.card))
  have hp_deg : p.natDegree = n := by
    dsimp [p]
    rw [Polynomial.natDegree_mul hprod_monic.ne_zero (monic_X.pow (n - s.card)).ne_zero]
    rw [Polynomial.natDegree_prod]
    · have hsum : (∑ i ∈ s, (X - C i).natDegree) = s.card := by
        calc
          (∑ i ∈ s, (X - C i).natDegree) = ∑ _i ∈ s, (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact Polynomial.natDegree_X_sub_C i
          _ = s.card := by simp
      rw [hsum, Polynomial.natDegree_X_pow]
      have hn' : s.card ≤ n := by simpa [s] using hn
      omega
    · intro a ha
      exact (monic_X_sub_C a).ne_zero
  have hp_van : ∀ z ∈ K, p.eval z = 0 := by
    intro z hz
    have hzmem : z ∈ s := hmemK z hz
    dsimp [p]
    rw [Polynomial.eval_mul]
    have hzero : (∏ a ∈ s, (X - C a)).eval z = 0 := by
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero hzmem (by simp)
    simp [hzero]
  let S : Set ℝ := {c : ℝ | 0 ≤ c ∧ ∃ p : ℂ[X], p ∈ MonicDeg n ∧ ∀ X ∈ K, ‖p.eval X‖ ≤ c}
  have hzero_mem : 0 ∈ S := by
    refine ⟨le_rfl, p, ⟨hp_monic, hp_deg⟩, ?_⟩
    intro X hX
    rw [hp_van X hX, norm_zero]
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro c hc
    exact hc.1
  unfold chebyshevNumber
  change sInf S = 0
  exact le_antisymm (csInf_le hbdd hzero_mem) (le_csInf ⟨0, hzero_mem⟩ (fun c hc => hc.1))

/-- For finite `K` with `s` points the Fekete numbers of degree `> s` vanish. -/
lemma feketeNumber_eq_zero_of_finite {K : Set ℂ} (hKne : K.Nonempty) (hKf : K.Finite)
    {n : ℕ} (hn : (hKf.toFinset).card < n) : feketeNumber K n = 0 := by
  let s : Finset ℂ := hKf.toFinset
  have hmemK : ∀ z ∈ K, z ∈ s := by
    intro z hz
    simpa [s] using (hKf.mem_toFinset).2 hz
  have hall : ∀ d ∈ feketeSet K n, d = 0 := by
    intro d hd
    rcases hd with ⟨x, hx, rfl⟩
    by_contra hne0
    have hdist : ∀ a, a < n → ∀ b, b < a → x b ≠ x a := by
      intro a ha b hb h
      exact False.elim (hne0 (vdm_eq_zero_of_lt (x := x) (n := n) (a := a) (b := b) hb ha h))
    have hInjR : Set.InjOn x (↑(Finset.range n)) := by
      intro a ha b hb h
      have ha' : a < n := by simpa using (Finset.mem_coe.mp ha)
      have hb' : b < n := by simpa using (Finset.mem_coe.mp hb)
      by_cases hab : a < b
      · exact False.elim ((hdist b hb' a hab) h)
      · by_cases hba : b < a
        · exact False.elim ((hdist a ha' b hba) h.symm)
        · exact le_antisymm (le_of_not_gt hba) (le_of_not_gt hab)
    let vals : Finset ℂ := (Finset.range n).image x
    have hvals_sub : vals ⊆ s := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨k, hk, rfl⟩
      exact hmemK (x k) (hx k (Finset.mem_range.mp hk))
    have hcard_eq : vals.card = n := by
      dsimp [vals]
      rw [Finset.card_image_of_injOn hInjR, Finset.card_range]
    have hcard_le : vals.card ≤ (hKf.toFinset).card := by
      simpa [s] using (Finset.card_le_card hvals_sub)
    have : n ≤ (hKf.toFinset).card := by omega
    omega
  have hnonempty : (feketeSet K n).Nonempty := by
    rcases hKne with ⟨e, he⟩
    refine ⟨vdm (fun _ => e) n, ?_⟩
    refine ⟨fun _ => e, ?_, rfl⟩
    intro i hi
    exact he
  have hle0 : feketeNumber K n ≤ 0 := by
    unfold feketeNumber
    exact csSup_le hnonempty (fun d hd => by rw [hall d hd])
  have hge0 : 0 ≤ feketeNumber K n := feketeNumber_nonneg hKne hKf.isBounded n
  exact le_antisymm hle0 hge0

/-- Real-power identity: `(x^m)^e = x^(m*e)` for a natural exponent `m`. -/
lemma rpow_nat_mul (x : ℝ) (hx : 0 ≤ x) (m : ℕ) (e : ℝ) :
    (x ^ m) ^ e = x ^ ((m : ℝ) * e) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx]

/-- The Chebyshev root numbers are bounded by the radius of `K`. -/
lemma chebRoot_bounded {K : Set ℂ} (hKb : Bornology.IsBounded K) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ z ∈ K, ‖z‖ ≤ R) (n : ℕ) :
    (chebyshevNumber K (n + 1)) ^ (1 / ((n + 1 : ℝ))) ≤ R := by
  have htle : chebyshevNumber K (n + 1) ≤ R ^ (n + 1) :=
    chebyshevNumber_le_pow hR0 hR
  have ht0 : 0 ≤ chebyshevNumber K (n + 1) := by
    exact chebyshevNumber_nonneg hKb (by omega)
  calc
    (chebyshevNumber K (n + 1)) ^ (1 / ((n + 1 : ℝ)))
        ≤ (R ^ (n + 1)) ^ (1 / ((n + 1 : ℝ))) := by
          exact Real.rpow_le_rpow ht0 htle (by positivity)
    _ = R := by
          have h1 : (R ^ (n + 1) : ℝ) = R ^ ((n + 1 : ℕ) : ℝ) := (Real.rpow_natCast R (n + 1)).symm
          rw [h1]
          rw [← Real.rpow_mul hR0]
          have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
          have hExp : ((n + 1 : ℕ) : ℝ) * (1 / ((n + 1 : ℝ))) = 1 := by
            rw [hcast]
            field_simp
          rw [hExp, Real.rpow_one]

/-- The Fekete root numbers are bounded above (by `(max 1 (2R))^4`). -/
lemma feketeRoot_bounded {K : Set ℂ} (hKne : K.Nonempty) (hKb : Bornology.IsBounded K) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ z ∈ K, ‖z‖ ≤ R) (n : ℕ) :
    (feketeNumber K (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ))) ≤ (max 1 (2 * R)) ^ 4 := by
  let C : ℝ := max 1 (2 * R)
  have hC1 : 1 ≤ C := by dsimp [C]; exact le_max_left 1 (2 * R)
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  by_cases hn0 : n = 0
  · subst n
    have hm1 : feketeNumber K 1 = 1 := feketeNumber_one hKne
    have : (1 : ℝ) ≤ C ^ 4 := by
      have : 1 ≤ C ^ 4 := one_le_pow₀ hC1
      simpa using this
    rw [hm1]
    simp
    exact this
  · have hn1 : 1 ≤ n := by omega
    have hle : feketeNumber K (n + 1) ≤ C ^ ((n + 1) * (n + 1)) := by
      dsimp [C]
      exact feketeNumber_le_sq (K := K) hKne (n := n + 1) (R := R) hR
    have hm0 : 0 ≤ feketeNumber K (n + 1) := feketeNumber_nonneg hKne hKb (n + 1)
    have hb0 : 0 ≤ C ^ ((n + 1) * (n + 1)) := pow_nonneg hC0 _
    have he0 : 0 ≤ 2 / (((n + 1 : ℝ)) * (n : ℝ)) := by
      have h1 : 0 < ((n + 1 : ℝ)) := by positivity
      have h2 : 0 < (n : ℝ) := by positivity
      positivity
    have hstep : (feketeNumber K (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))
        ≤ (C ^ ((n + 1) * (n + 1))) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ))) := by
      exact Real.rpow_le_rpow hm0 hle he0
    have hpow : (C ^ ((n + 1) * (n + 1))) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))
        = C ^ ((2 * (n + 1 : ℝ)) / (n : ℝ)) := by
      have hcast : ((((n + 1) * (n + 1) : ℕ) : ℝ)) = ((n + 1 : ℝ) * (n + 1 : ℝ)) := by
        norm_num
      calc
        (C ^ ((n + 1) * (n + 1))) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))
            = C ^ ((((n + 1) * (n + 1) : ℕ) : ℝ) * (2 / (((n + 1 : ℝ)) * (n : ℝ)))) := by
              exact rpow_nat_mul C hC0 ((n + 1) * (n + 1)) (2 / (((n + 1 : ℝ)) * (n : ℝ)))
        _ = C ^ ((2 * (n + 1 : ℝ)) / (n : ℝ)) := by
              congr 1
              rw [hcast]
              field_simp
    have hexp : (2 * (n + 1 : ℝ)) / (n : ℝ) ≤ 4 := by
      have hnpos : 0 < (n : ℝ) := by positivity
      have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      rw [div_le_iff₀ hnpos]
      nlinarith
    have hCpow : C ^ ((2 * (n + 1 : ℝ)) / (n : ℝ)) ≤ C ^ 4 := by
      have h4 : C ^ (4 : ℝ) = C ^ 4 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num]
        exact Real.rpow_natCast C 4
      rw [← h4]
      exact Real.rpow_le_rpow_of_exponent_le hC1 hexp
    calc
      (feketeNumber K (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))
          ≤ (C ^ ((n + 1) * (n + 1))) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ))) := hstep
      _ = C ^ ((2 * (n + 1 : ℝ)) / (n : ℝ)) := hpow
      _ ≤ C ^ 4 := by
            simpa [C] using hCpow
      _ = (max 1 (2 * R)) ^ 4 := rfl

/-- **Upper sandwich half**: limsup of the Chebyshev root numbers is at
most the limsup of the Fekete root numbers. -/
theorem chebyshev_root_le_fekete_root (K : Set ℂ) (hKne : K.Nonempty)
    (hKb : Bornology.IsBounded K) :
    Filter.limsup (fun n : ℕ => (chebyshevNumber K (n + 1)) ^ (1 / ((n + 1 : ℝ)))) Filter.atTop
      ≤ Filter.limsup (fun n : ℕ => (feketeNumber K (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))) Filter.atTop := by
  by_cases hKf : K.Finite
  · -- finite `K`: both root sequences are eventually zero
    have hA0 : ∀ᶠ n : ℕ in Filter.atTop,
        (chebyshevNumber K (n + 1)) ^ (1 / ((n + 1 : ℝ))) = 0 := by
      rw [Filter.eventually_atTop]
      refine ⟨(hKf.toFinset).card + 1, ?_⟩
      intro n hn
      have ht0 : chebyshevNumber K (n + 1) = 0 :=
        chebyshevNumber_eq_zero_of_finite hKf (by omega)
      rw [ht0, Real.zero_rpow]
      exact one_div_ne_zero (by positivity : (n + 1 : ℝ) ≠ 0)
    have hB0 : ∀ᶠ n : ℕ in Filter.atTop,
        (feketeNumber K (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ))) = 0 := by
      rw [Filter.eventually_atTop]
      refine ⟨(hKf.toFinset).card + 1, ?_⟩
      intro n hn
      have hcard : 1 ≤ (hKf.toFinset).card := by
        rcases hKne with ⟨e, he⟩
        exact Finset.card_pos.mpr ⟨e, (hKf.mem_toFinset).2 he⟩
      have hn1 : 1 ≤ n := by omega
      have hmn : feketeNumber K (n + 1) = 0 :=
        feketeNumber_eq_zero_of_finite hKne hKf (by omega)
      rw [hmn]
      apply Real.zero_rpow
      have hpos : 0 < (2 : ℝ) / (((n + 1 : ℝ)) * (n : ℝ)) := by
        positivity
      exact ne_of_gt hpos
    have hlimA : Filter.limsup (fun n : ℕ => (chebyshevNumber K (n + 1)) ^ (1 / ((n + 1 : ℝ)))) Filter.atTop = 0 := by
      rw [Filter.limsup_congr hA0]
      rw [Filter.limsup_const]
    have hlimB : Filter.limsup (fun n : ℕ => (feketeNumber K (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))) Filter.atTop = 0 := by
      rw [Filter.limsup_congr hB0]
      rw [Filter.limsup_const]
    rw [hlimA, hlimB]
  · -- infinite `K`: use Engine U
    rcases bounded_radius hKb with ⟨R, hRpos, hR⟩
    have ht0 : ∀ j : ℕ, 1 ≤ j → 0 < (fun j : ℕ => chebyshevNumber K j) j := by
      intro j hj
      exact chebyshevNumber_pos_of_infinite hKb hKf (n := j) hj
    have hm0 : ∀ j : ℕ, 1 ≤ j → 0 < (fun j : ℕ => feketeNumber K j) j := by
      intro j hj
      exact feketeNumber_pos_of_infinite hKb hKf (n := j) hj
    have hm1 : (fun j : ℕ => feketeNumber K j) 1 = 1 := by
      exact feketeNumber_one hKne
    have hsub : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        (fun j : ℕ => chebyshevNumber K j) (a + b)
          ≤ (fun j : ℕ => chebyshevNumber K j) a * (fun j : ℕ => chebyshevNumber K j) b := by
      intro a b ha hb
      exact chebyshev_mul_le_of_bounded hKne hKb ha hb
    have hDL2 : ∀ j : ℕ, 1 ≤ j →
        (fun j : ℕ => chebyshevNumber K j) j * (fun j : ℕ => feketeNumber K j) j
          ≤ (fun j : ℕ => feketeNumber K j) (j + 1) := by
      intro j hj
      exact cheb_mul_le_fekete_succ_of_bounded hKne hKb (n := j) hj
        (feketeNumber_pos_of_infinite hKb hKf (n := j) hj)
    have hbdA : ∀ n : ℕ, (chebyshevNumber K (n + 1)) ^ (1 / ((n + 1 : ℝ))) ≤ R := by
      intro n
      exact chebRoot_bounded hKb (le_of_lt hRpos) hR n
    have hbdB : ∀ n : ℕ, (feketeNumber K (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))
        ≤ (max 1 (2 * R)) ^ 4 := by
      intro n
      exact feketeRoot_bounded hKne hKb (le_of_lt hRpos) hR n
    exact Submission.EngineUpper.cheb_root_le_fekete_root_of_positive ht0 hm0 hm1 hsub hDL2 hRpos hbdA
      (by positivity) hbdB

/-- **Lower sandwich half**: limsup of the Fekete root numbers is at most
the limsup of the Chebyshev root numbers. -/
theorem fekete_root_le_chebyshev_root (K : Set ℂ) (hKne : K.Nonempty)
    (hKb : Bornology.IsBounded K) :
    Filter.limsup (fun n : ℕ => (feketeNumber K (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))) Filter.atTop
      ≤ Filter.limsup (fun n : ℕ => (chebyshevNumber K (n + 1)) ^ (1 / ((n + 1 : ℝ)))) Filter.atTop := by
  by_cases hKf : K.Finite
  · -- finite `K`: both root sequences are eventually zero
    have hA0 : ∀ᶠ n : ℕ in Filter.atTop,
        (chebyshevNumber K (n + 1)) ^ (1 / ((n + 1 : ℝ))) = 0 := by
      rw [Filter.eventually_atTop]
      refine ⟨(hKf.toFinset).card + 1, ?_⟩
      intro n hn
      have ht0 : chebyshevNumber K (n + 1) = 0 :=
        chebyshevNumber_eq_zero_of_finite hKf (by omega)
      rw [ht0, Real.zero_rpow]
      exact one_div_ne_zero (by positivity : (n + 1 : ℝ) ≠ 0)
    have hB0 : ∀ᶠ n : ℕ in Filter.atTop,
        (feketeNumber K (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ))) = 0 := by
      rw [Filter.eventually_atTop]
      refine ⟨(hKf.toFinset).card + 1, ?_⟩
      intro n hn
      have hcard : 1 ≤ (hKf.toFinset).card := by
        rcases hKne with ⟨e, he⟩
        exact Finset.card_pos.mpr ⟨e, (hKf.mem_toFinset).2 he⟩
      have hn1 : 1 ≤ n := by omega
      have hmn : feketeNumber K (n + 1) = 0 :=
        feketeNumber_eq_zero_of_finite hKne hKf (by omega)
      rw [hmn]
      apply Real.zero_rpow
      have hpos : 0 < (2 : ℝ) / (((n + 1 : ℝ)) * (n : ℝ)) := by
        positivity
      exact ne_of_gt hpos
    have hlimA : Filter.limsup (fun n : ℕ => (chebyshevNumber K (n + 1)) ^ (1 / ((n + 1 : ℝ)))) Filter.atTop = 0 := by
      rw [Filter.limsup_congr hA0]
      rw [Filter.limsup_const]
    have hlimB : Filter.limsup (fun n : ℕ => (feketeNumber K (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))) Filter.atTop = 0 := by
      rw [Filter.limsup_congr hB0]
      rw [Filter.limsup_const]
    rw [hlimB, hlimA]
  · -- infinite `K`: use Engine L
    rcases bounded_radius hKb with ⟨R, hRpos, hR⟩
    have ht0 : ∀ j : ℕ, 1 ≤ j → 0 < (fun j : ℕ => chebyshevNumber K j) j := by
      intro j hj
      exact chebyshevNumber_pos_of_infinite hKb hKf (n := j) hj
    have hm0 : ∀ j : ℕ, 1 ≤ j → 0 < (fun j : ℕ => feketeNumber K j) j := by
      intro j hj
      exact feketeNumber_pos_of_infinite hKb hKf (n := j) hj
    have hm1 : (fun j : ℕ => feketeNumber K j) 1 = 1 := by
      exact feketeNumber_one hKne
    have hDL1 : ∀ j : ℕ, 1 ≤ j →
        (fun j : ℕ => feketeNumber K j) (j + 1)
          ≤ (j + 1 : ℝ) * (fun j : ℕ => chebyshevNumber K j) j * (fun j : ℕ => feketeNumber K j) j := by
      intro j hj
      exact fekete_succ_le_of_bounded hKne hKb (n := j) hj
    have hbdA : ∀ n : ℕ, (chebyshevNumber K (n + 1)) ^ (1 / ((n + 1 : ℝ))) ≤ R := by
      intro n
      exact chebRoot_bounded hKb (le_of_lt hRpos) hR n
    have hbdB : ∀ n : ℕ, (feketeNumber K (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))
        ≤ (max 1 (2 * R)) ^ 4 := by
      intro n
      exact feketeRoot_bounded hKne hKb (le_of_lt hRpos) hR n
    exact Submission.EngineLower.fekete_root_le_cheb_root_of_positive ht0 hm0 hm1 hDL1 hRpos hbdA
      (by positivity) hbdB

/-- **Fekete's equality.**  limsup of the Chebyshev root numbers equals the
limsup of the Fekete root numbers (the logarithmic capacity). -/
theorem fekete_chebyshev_equality (K : Set ℂ) (hKne : K.Nonempty)
    (hKb : Bornology.IsBounded K) :
    Filter.limsup (fun n : ℕ => (chebyshevNumber K (n + 1)) ^ (1 / ((n + 1 : ℝ)))) Filter.atTop
      = Filter.limsup (fun n : ℕ => (feketeNumber K (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))) Filter.atTop := by
  exact le_antisymm (chebyshev_root_le_fekete_root K hKne hKb)
    (fekete_root_le_chebyshev_root K hKne hKb)

end Submission.FeketeLim

end
