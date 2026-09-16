import Submission.ZagierHoffmanProof.StepL198
import Submission.ZagierHoffmanProof.StepB5

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial RatFunc
open scoped BigOperators WithZero Topology
open WithZero

/-!
# Step L199: non-vanishing of every MZV with all entries `≤ q`

The block decomposition `ζ_A(𝔰) = Σ_d S_d(𝔰)` reduces the valuation of `ζ_A(𝔰)` to those of
the level-`d` power sums, which carry the full "chain" structure

  `S_d(𝔰) = Σ_{d = d₁ > d₂ > ⋯ > d_r ≥ 0} P_{d₁}(𝔰₀)·P_{d₂}(𝔰₁)···P_{d_r}(𝔰_{r-1})`.

The key input is the exact valuation of the depth-one power sums: by the PURE PRODUCT formula
`P_d(a)·P_d(b) = P_d(a+b)` for `a + b ≤ q` (paper Remark 2.2(2), committed as `P_pure`) one has
`P_d(n) = P_d(1)^n` for every `n ≤ q`, hence (StepL195)

  `v (P_d(n)) = exp (−n · Sexp d)`,   `Sexp d = q + q² + … + q^d`   (`d ≥ 1`),

which is strictly decreasing in `d`.  Consequently the summands of a block have DISTINCT
valuations and the largest is attained at the unique chain `(d, r-2, …, 0)`:

  `v (S_d(𝔰)) = exp (−(𝔰₀·Sexp d + Σ_{j≥1} 𝔰_j·Sexp (r-1-j)))`   (`d ≥ r-1`),

and dually the dominating LEVEL is the smallest admissible one, `d = r-1`:

  `v (ζ_A(𝔰)) = exp (−Σ_j 𝔰_j·Sexp (r-1-j))  ≠ 0`.

Hence every MZV whose entries are all `≤ q` — in particular every element of the spanning set
`𝒯 w` of Theorem A — is nonzero: the reachable part of Thakur's non-vanishing theorem.
Theorems B/D in general remain ABP-gated.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## 1. The exponent `Se n d = n · Sexp d` of `v (P_d(n))` for `n ≤ q` -/

/-- `Se n d = n · Sexp d`: the exponent of the valuation of `P_d(n)` for `1 ≤ n ≤ q`. -/
noncomputable def Se (n : ℕ+) (d : ℕ) : ℤ := (n : ℤ) * Sexp F d

/-- All entries of the tuple are `≤ q`. -/
def EntriesOK {r : ℕ} (𝔰 : Fin r → ℕ+) : Prop := ∀ j, (𝔰 j : ℕ) ≤ Nat.card F

lemma Se_zero (n : ℕ+) : Se F n 0 = 0 := by simp [Se, Sexp]

lemma Se_one (d : ℕ) : Se F oneExp d = Sexp F d := by simp [Se, oneExp]

/-- `n · Sexp d = Wtwo d` at `n = q`: the formulas of StepL195 and StepL198 agree. -/
lemma Se_qExp (d : ℕ) : Se F (qExp F) d = Wtwo F d := by
  rw [Se]
  induction d with
  | zero => simp [Sexp, Wtwo]
  | succ d ih =>
      rw [Sexp_succ, Wtwo_succ, mul_add, ih]
      have hq : ((qExp F : ℕ+) : ℤ) = (Nat.card F : ℤ) := rfl
      rw [hq]
      ring

lemma Se_lt_succ (n : ℕ+) (d : ℕ) : Se F n d < Se F n (d + 1) := by
  have hn : (0 : ℤ) < (n : ℤ) := by
    have h := n.pos
    exact_mod_cast h
  have hs : Sexp F d < Sexp F (d + 1) := by
    rw [Sexp_succ]
    have hq : (0 : ℤ) < (Nat.card F : ℤ) := by
      have h := card_ge_two F
      exact_mod_cast (by omega : 0 < Nat.card F)
    have := pow_pos hq (d + 1)
    linarith
  have := mul_lt_mul_of_pos_left hs hn
  simpa [Se] using this

lemma Se_strictMono (n : ℕ+) : StrictMono (Se F n) :=
  strictMono_nat_of_lt_succ fun d => Se_lt_succ F n d

/-- ★ For `n ≤ q` the depth-one power sum is the `n`-th power of `P_d(1)` (pure case of the
Thakur-Chen product, iteration of `P_pure`). -/
lemma P_eq_pow_nat (d : ℕ) (hd : 1 ≤ d) :
    ∀ m : ℕ, ∀ (hm : 1 ≤ m), ∀ (hmq : m ≤ Nat.card F),
      P F d ⟨m, hm⟩ = (P F d oneExp) ^ m := by
  intro m
  induction m with
  | zero => intro h1; exact absurd h1 (by omega)
  | succ m ih =>
      intro hm hmq
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        rw [pow_one]
        congr 1
      · have ih' := ih h0 (by omega)
        have hpure := P_pure F d hd ⟨m, h0⟩ oneExp (by
          show m + 1 ≤ Nat.card F
          omega)
        have hp : P F d ⟨m + 1, hm⟩ = P F d ⟨m, h0⟩ * P F d oneExp := hpure.symm
        rw [hp, ih', pow_succ]

/-- ★ For `n ≤ q`, `P_d(n) = P_d(1)^n`. -/
lemma P_eq_pow_of_le_card (d : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ Nat.card F) :
    P F d n = (P F d oneExp) ^ (n : ℕ) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    rw [P_zero_eq_one F n, P_zero_eq_one F oneExp, one_pow]
  · exact P_eq_pow_nat F d hd (n : ℕ) n.pos hn

/-- ★★ `v (P_d(n)) = exp (−n · Sexp d)` for every `n ≤ q`. -/
lemma val_P_se (n : ℕ+) (hn : (n : ℕ) ≤ Nat.card F) (d : ℕ) :
    Valued.v (P F d n) = WithZero.exp (-(Se F n d)) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    rw [P_zero_eq_one F n, map_one, Se_zero F, neg_zero, WithZero.exp_zero]
  · rw [P_eq_pow_of_le_card F d n hn, map_pow, val_P_oneExp' F d hd, Se]
    rw [show (-((n : ℤ) * Sexp F d)) = (n : ℕ) • (-(Sexp F d)) by
      simp [nsmul_eq_mul]]
    rw [← WithZero.exp_nsmul]

/-- `0 < WithZero.exp (-x)` (with the type of `x` fixed to `ℤ`, to help elaboration). -/
lemma exp_neg_pos (x : ℤ) : (0 : ℤᵐ⁰) < WithZero.exp (-x) := WithZero.exp_pos

/-- `EntriesOK` is inherited by the tail of the tuple. -/
lemma EntriesOK.tail {r : ℕ} {𝔰 : Fin r → ℕ+} (h : EntriesOK F 𝔰) :
    EntriesOK F (expTail 𝔰) := by
  intro j
  exact h ⟨(j : ℕ) + 1, by have := j.2; omega⟩

/-! ## 2. The block exponent `bloExp` -/

/-- The exponent of the block `S_d(𝔰)`:
`bloExp r 𝔰 d = Se(𝔰₀,d) + bloExp (r-1) (tail 𝔰) (r-2)`, i.e. explicitly
`Se(𝔰₀,d) + Σ_{j≥1} Se(𝔰_j, r-1-j)`. -/
noncomputable def bloExp : (r : ℕ) → (Fin r → ℕ+) → ℕ → ℤ
  | 0, _, _ => 0
  | 1, 𝔰, d => Se F (𝔰 0) d
  | (r + 2), 𝔰, d => Se F (𝔰 0) d + bloExp (r + 1) (expTail 𝔰) r

lemma bloExp_one (𝔰 : Fin 1 → ℕ+) (d : ℕ) : bloExp F 1 𝔰 d = Se F (𝔰 0) d := by
  rw [bloExp]

lemma bloExp_succ (r : ℕ) (𝔰 : Fin (r + 2) → ℕ+) (d : ℕ) :
    bloExp F (r + 2) 𝔰 d = Se F (𝔰 0) d + bloExp F (r + 1) (expTail 𝔰) r := by
  rw [bloExp]

/-- ★ `bloExp r 𝔰` is strictly increasing in the index. -/
lemma bloExp_lt (r : ℕ) (hr : 0 < r) (𝔰 : Fin r → ℕ+) (h𝔰 : EntriesOK F 𝔰) :
    StrictMono (fun d => bloExp F r 𝔰 d) := by
  refine strictMono_nat_of_lt_succ fun d => ?_
  match r with
  | 0 => exact absurd hr (by omega)
  | 1 =>
      rw [bloExp_one F 𝔰 d, bloExp_one F 𝔰 (d + 1)]
      exact Se_lt_succ F (𝔰 0) d
  | (k + 2) =>
      rw [bloExp_succ F k 𝔰 d, bloExp_succ F k 𝔰 (d + 1)]
      have h := Se_lt_succ F (𝔰 0) d
      linarith

/-! ## 3. Blocks below the diagonal are empty -/

/-- The degree-`d` block of a depth-`r` tuple is empty for `d < r - 1`. -/
lemma S_eq_zero_of_lt {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) {d : ℕ} (hd : d < r - 1) :
    S F r hr 𝔰 d = 0 := by
  classical
  let A := {a : monicStrictAntiNatDegree F r // a ∈ blockSet F r hr d}
  have hempty : ∀ a : A, False := by
    intro a
    have hdeg : (a.1.val ⟨0, hr⟩).natDegree = d := a.2
    have key : ∀ k : ℕ, ∀ (hk : k < r), (a.1.val ⟨k, hk⟩).natDegree + k ≤ d := by
      intro k
      induction k with
      | zero =>
          intro hk
          have h0 : (a.1.val ⟨0, hk⟩) = a.1.val ⟨0, hr⟩ := rfl
          rw [h0, hdeg]
          omega
      | succ k ih =>
          intro hk
          have hk' : k < r := by omega
          have ihk := ih hk'
          have hlt : (a.1.val ⟨k + 1, hk⟩).natDegree < (a.1.val ⟨k, hk'⟩).natDegree := by
            have hlt' := a.1.2.1 (show (⟨k, hk'⟩ : Fin r) < ⟨k + 1, hk⟩ by simp)
            simpa using hlt'
          omega
    have hlast := key (r - 1) (by omega)
    omega
  haveI hfin : Finite A := by
    dsimp [A]
    exact finite_block F hr d
  letI : Fintype A := Fintype.ofFinite (α := A)
  change (∑' a : A, zetaTerm F 𝔰 a.1) = 0
  rw [tsum_fintype]
  exact Finset.sum_eq_zero fun a _ => (hempty a).elim

/-! ## 4. The valuation of the blocks `S_d(𝔰)` -/

/-- ★★ `v (S_d(𝔰)) = exp (−bloExp r 𝔰 d)` for every `d ≥ r - 1`, for tuples with entries in
`{1, q}` (induction on the depth, using the level recursion `S_d(𝔰) = P_d(𝔰₀)·S_<d(tail)`
and the fact that the tail's dominating level is its own diagonal `r - 2`). -/
theorem val_S_bloExp : ∀ (r : ℕ) (hr : 0 < r) (𝔰 : Fin r → ℕ+) (h𝔰 : EntriesOK F 𝔰) (d : ℕ),
    r - 1 ≤ d → Valued.v (S F r hr 𝔰 d) = WithZero.exp (-(bloExp F r 𝔰 d)) := by
  intro r
  induction r with
  | zero => intro hr; exact absurd hr (by omega)
  | succ r ih =>
      intro hr 𝔰 h𝔰 d hd
      rcases Nat.eq_zero_or_pos r with hr0 | hr0
      · subst hr0
        rw [S_one_eq_P F d (by norm_num) 𝔰, bloExp_one F 𝔰 d]
        exact val_P_se F (𝔰 0) (h𝔰 0) d
      · obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
        have hT : 0 < k + 1 := by omega
        have htail : EntriesOK F (expTail 𝔰) := EntriesOK.tail F h𝔰
        have hrec : S F (k + 2) hr 𝔰 d
            = P F d (𝔰 0) * S_lt F (k + 1) hT (expTail 𝔰) d :=
          S_d_recursion F (k + 2) (by omega) (by omega) (by omega) 𝔰 d
        rw [hrec, S_lt_eq_sum_levels F (k + 1) hT (expTail 𝔰) d]
        have hIHk : Valued.v (S F (k + 1) hT (expTail 𝔰) k)
            = WithZero.exp (-(bloExp F (k + 1) (expTail 𝔰) k)) :=
          ih hT (expTail 𝔰) htail k (by omega)
        have hdom : Valued.v (∑ i ∈ Finset.range d, S F (k + 1) hT (expTail 𝔰) i)
            = WithZero.exp (-(bloExp F (k + 1) (expTail 𝔰) k)) := by
          refine (Valuation.map_sum_eq_of_lt (v := Valued.v) (j := k)
            (Finset.mem_range.mpr (by omega)) ?_).trans hIHk
          intro i hi
          rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
          obtain ⟨hir, hik⟩ := hi
          have hid : i < d := Finset.mem_range.mp hir
          rcases lt_trichotomy i k with h | h | h
          · have hzero : S F (k + 1) hT (expTail 𝔰) i = 0 :=
              S_eq_zero_of_lt F (by omega : 0 < k + 1) (expTail 𝔰) (by omega : i < k + 1 - 1)
            rw [hzero, map_zero, hIHk]
            exact exp_neg_pos (bloExp F (k + 1) (expTail 𝔰) k)
          · exact absurd h hik
          · rw [ih hT (expTail 𝔰) htail i (by omega), hIHk, WithZero.exp_lt_exp]
            have hmono := (bloExp_lt F (k + 1) (by omega) (expTail 𝔰) htail).lt_iff_lt.mpr h
            linarith
        rw [map_mul, hdom, val_P_se F (𝔰 0) (h𝔰 0) d, bloExp_succ F k 𝔰 d,
          ← WithZero.exp_add]
        congr 1
        ring

/-! ## 5. A summable family dominated by a single term -/

/-- ★★ If `f` is summable and `f n₀` strictly dominates (in valuation) all other terms, then
`v (∑' f) = v (f n₀)` (in particular the sum is nonzero).  Proof: rescale by `f n₀` and move
the dominating index to `0` with `Equiv.swap`, reducing to `val_tsum_eq_one_of`. -/
theorem val_tsum_eq_of_dominates (f : ℕ → RatFunc.CompletionAtInfty F) (n₀ : ℕ) (β : ℤᵐ⁰)
    (hβ : β ≠ 0) (hf : Valued.v (f n₀) = β) (hsumm : Summable f)
    (hlt : ∀ n : ℕ, n ≠ n₀ → Valued.v (f n) < β) :
    Valued.v (∑' n, f n) = β := by
  classical
  set c : RatFunc.CompletionAtInfty F := f n₀ with hc
  have hcβ : Valued.v c = β := by rw [hc]; exact hf
  have hcne : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hcβ
    exact hβ hcβ.symm
  have hβpos : (0 : ℤᵐ⁰) < β := by
    have h1 : Valued.v (f (n₀ + 1)) < β := hlt (n₀ + 1) (by omega)
    have h2 : (0 : ℤᵐ⁰) ≤ Valued.v (f (n₀ + 1)) := zero_le
    exact lt_of_le_of_lt h2 h1
  set e : ℕ ≃ ℕ := Equiv.swap 0 n₀ with he
  set g : ℕ → RatFunc.CompletionAtInfty F := fun n => f (e n) * c⁻¹ with hg
  have hsumm' : Summable (fun n => f (e n)) := (Equiv.summable_iff e).mpr hsumm
  have hgs : Summable g := by rw [hg]; exact hsumm'.mul_right _
  have hg0 : g 0 = 1 := by
    have he0 : e 0 = n₀ := by rw [he]; exact Equiv.swap_apply_left 0 n₀
    rw [hg]
    simp only []
    rw [he0, ← hc, mul_inv_cancel₀ hcne]
  have hglt : ∀ n : ℕ, 1 ≤ n → Valued.v (g n) < (1 : ℤᵐ⁰) := by
    intro n hn
    have hene : e n ≠ n₀ := by
      by_cases h : n = n₀
      · rw [he, h, Equiv.swap_apply_right]
        omega
      · rw [he, Equiv.swap_apply_of_ne_of_ne (by omega : n ≠ 0) h]
        exact h
    have hfn : Valued.v (f (e n)) < β := hlt (e n) hene
    rw [hg]
    simp only []
    rw [map_mul, map_inv₀, hcβ]
    calc Valued.v (f (e n)) * β⁻¹ < β * β⁻¹ :=
          mul_lt_mul_of_pos_right hfn (inv_pos.mpr hβpos)
      _ = 1 := mul_inv_cancel₀ hβ
  have hone := val_tsum_eq_one_of F g hg0 hgs hglt
  have hsumg : ∑' n, g n = (∑' n, f n) * c⁻¹ := by
    rw [hg]
    rw [hsumm'.tsum_mul_right c⁻¹, Equiv.tsum_eq e f]
  have hmul : (∑' n, g n) * c = ∑' n, f n := by
    rw [hsumg, mul_assoc, inv_mul_cancel₀ hcne, mul_one]
  rw [← hmul, map_mul, hone, one_mul]
  exact hcβ

/-! ## 6. Non-vanishing of the `{1, q}`-entry MZVs -/

/-- ★★★ `v (ζ_A(𝔰)) = exp (−Σ_j Se(𝔰_j, r−1−j))` for MZVs with all entries in `{1, q}`. -/
theorem val_zeta_entries {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) (h𝔰 : EntriesOK F 𝔰) :
    Valued.v (ζ_A F 𝔰) = WithZero.exp (-(bloExp F r 𝔰 (r - 1))) := by
  classical
  have hsumm := summable_S F hr 𝔰
  rw [zeta_eq_tsum_block F hr 𝔰]
  refine val_tsum_eq_of_dominates F _ (r - 1) _ WithZero.exp_ne_zero ?_ hsumm ?_
  · exact val_S_bloExp F r hr 𝔰 h𝔰 (r - 1) (by omega)
  · intro d hd
    rcases lt_trichotomy d (r - 1) with h | h | h
    · have hzero : S F r hr 𝔰 d = 0 := S_eq_zero_of_lt F hr 𝔰 h
      rw [hzero, map_zero]
      exact exp_neg_pos (bloExp F r 𝔰 (r - 1))
    · exact absurd h hd
    · rw [val_S_bloExp F r hr 𝔰 h𝔰 d (by omega), WithZero.exp_lt_exp]
      have hmono := (bloExp_lt F r hr 𝔰 h𝔰).lt_iff_lt.mpr h
      linarith

/-- ★★★ Every MZV with all entries in `{1, q}` is nonzero. -/
theorem zeta_entries_ne_zero {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) (h𝔰 : EntriesOK F 𝔰) :
    ζ_A F 𝔰 ≠ 0 := by
  intro h0
  have h := val_zeta_entries F hr 𝔰 h𝔰
  rw [h0, map_zero] at h
  exact WithZero.exp_ne_zero h.symm



end ZagierHoffmanPositiveChar
