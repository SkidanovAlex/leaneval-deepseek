import Mathlib
import Submission.Work.TMC14Core.Defs
import Submission.Work.TMC7Core.Scale.lyapAvg_lipschitz
import Submission.Work.TMC14Core.Rat
import Submission.Work.TMC14Core.uniform_small_scale
/-!
# TMC14Core: `Work.TMC14Core.transferEstimate` (ROUTE_LEAD 14f, transfer part)

The `q`-step transfer matrix of a *rational* approximant `p/q` of an irrational frequency
`α`, at a complex energy close to a window `[c,d]` on which the Lyapunov exponent of `α`
vanishes, is bounded by `exp (ε q)` uniformly in the phase `θ`.

Assembly (ROUTE_LEAD §4 C14 item 14f), all inputs proved below or in the shared library:

* `uniform_small_scale` (proved in the chapter): part (2) of `P_LEBasics` is uniform in a
  complex neighbourhood of the compact window `[c,d]`, with rate `ε/8`;
* `iterC_alpha_perturb_lip` (proved here, §2): at fixed complex energy `‖z‖ ≤ R` the
  log-Frobenius norm of the `k`-step transfer matrix is Lipschitz in the frequency with an
  explicit constant, so the frequency perturbation `α → p/q` costs at most `C·|p/q - α|`;
* `block_prod_bound` (proved here, §1): a product of `⌊q/k⌋` blocks of length `k` and one
  remainder block is bounded by `E₀ · B^{q/k}`;
* the two constants `δ` and `Q` are chosen so that `e^{qε} = e^{qε/2}·e^{qε/2}` absorbs the
  block bound and the remainder.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace Work.TMC14Core

/-! ## 1. Elementary cocycle API in the `TMC14Core` vocabulary -/

/-- `A_{m+n}(x) = A_m(x + nα) · A_n(x)`. -/
theorem iterC_add (α lam : ℝ) (E : ℂ) (m n : ℕ) (x : ℝ) :
    iterC α lam E (m + n) x = iterC α lam E m (x + (n : ℝ) * α) * iterC α lam E n x := by
  induction m with
  | zero => simp [iterC_zero]
  | succ m ih =>
    have hy : x + ((m + n : ℕ) : ℝ) * α = x + (n : ℝ) * α + (m : ℝ) * α := by
      push_cast; ring
    rw [Nat.succ_add, iterC_succ, ih, iterC_succ, hy, mul_assoc]

/-- Iterates of the transfer cocycle have Frobenius norm at least `1`. -/
theorem one_le_frob_iterC (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    1 ≤ frob (iterC α lam E n x) := by
  have h1 : Real.sqrt 2 ≤ frob (iterC α lam E n x) :=
    Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one (iterC_det α lam E n x)
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  linarith

/-- Uniform growth bound for the transfer cocycle at complex energy `z` with `‖z‖ ≤ R`. -/
theorem frob_iterC_le_pow (α lam : ℝ) (z : ℂ) (R : ℝ) (hz : ‖z‖ ≤ R) (n : ℕ) (x : ℝ) :
    frob (iterC α lam z n x) ≤ Real.sqrt 2 * (Real.sqrt ((R + 2 * |lam|) ^ 2 + 2)) ^ n := by
  set M : ℝ := Real.sqrt ((R + 2 * |lam|) ^ 2 + 2) with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef, ← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (R + 2 * |lam|)]
  have hM0 : 0 ≤ M := le_trans zero_le_one hM1
  have htmC : ∀ y : ℝ, frob (tmC lam z y) ≤ M := by
    intro y
    rw [hMdef]
    refine le_trans (Work.TMC7Core.Scale.frob_tmC_le lam z y) (Real.sqrt_le_sqrt ?_)
    have h1 : ‖z‖ + 2 * |lam| ≤ R + 2 * |lam| := by linarith [abs_nonneg lam]
    have h2 : (0 : ℝ) ≤ ‖z‖ + 2 * |lam| := by positivity
    nlinarith [h2, h1]
  induction n with
  | zero =>
    rw [iterC_zero]
    have h : frob (1 : Matrix (Fin 2) (Fin 2) ℂ) = Real.sqrt 2 := Work.TMC7Core.frob_one
    rw [h, pow_zero, mul_one]
  | succ n ih =>
    rw [iterC_succ]
    calc frob (tmC lam z (x + (n : ℝ) * α) * iterC α lam z n x)
        ≤ frob (tmC lam z (x + (n : ℝ) * α)) * frob (iterC α lam z n x) :=
          Work.TMC7Core.Cocycle.frob_mul_le _ _
      _ ≤ M * (Real.sqrt 2 * M ^ n) :=
          mul_le_mul (htmC _) ih (Work.TMC7Core.frob_nonneg _) hM0
      _ = Real.sqrt 2 * M ^ (n + 1) := by rw [pow_succ]; ring

/-- **Block decomposition.**  If every `k`-step block is bounded by `B` and every shorter
block by `E₀`, then the `q`-step product is bounded by `E₀ · B^{q/k}` (`k ≥ 1`). -/
theorem block_prod_bound (β lam : ℝ) (z : ℂ) (k q : ℕ) (hk : 1 ≤ k) (B E₀ : ℝ)
    (hB0 : 0 ≤ B) (hBk : ∀ y : ℝ, frob (iterC β lam z k y) ≤ B)
    (hrem : ∀ j : ℕ, j < k → ∀ y : ℝ, frob (iterC β lam z j y) ≤ E₀) :
    ∀ x : ℝ, frob (iterC β lam z q x) ≤ E₀ * B ^ (q / k) := by
  have key : ∀ m s : ℕ, s < k → ∀ x : ℝ,
      frob (iterC β lam z (k * m + s) x) ≤ E₀ * B ^ m := by
    intro m
    induction m with
    | zero => intro s hs x; simpa using hrem s hs x
    | succ m ih =>
      intro s hs x
      have hshape : k * (m + 1) + s = k + (k * m + s) := by ring
      have hy : ((k * m + s : ℕ) : ℝ) = (k : ℝ) * (m : ℝ) + (s : ℝ) := by push_cast; ring
      rw [hshape, iterC_add]
      calc frob (iterC β lam z k (x + ((k * m + s : ℕ) : ℝ) * β)
              * iterC β lam z (k * m + s) x)
          ≤ frob (iterC β lam z k (x + ((k * m + s : ℕ) : ℝ) * β))
              * frob (iterC β lam z (k * m + s) x) :=
            Work.TMC7Core.Cocycle.frob_mul_le _ _
        _ ≤ B * (E₀ * B ^ m) :=
            mul_le_mul (hBk _) (ih s hs x) (Work.TMC7Core.frob_nonneg _) hB0
        _ = E₀ * B ^ (m + 1) := by rw [pow_succ]; ring
  intro x
  have h := key (q / k) (q % k) (Nat.mod_lt q (lt_of_lt_of_le Nat.zero_lt_one hk)) x
  rwa [Nat.div_add_mod] at h

/-! ## 2. Perturbation of the frequency: the single analytic input

At a fixed complex energy `z` with `‖z‖ ≤ R` the log-Frobenius norm of the `k`-step
transfer matrix is Lipschitz in the frequency.  Both `k`-step matrices are written as
ordered products (`Work.TMC7Core.matProd`), and the difference of the two products is
estimated by the product-stability lemma `Work.TMC7Core.Scale.frob_matProd_sub_le`; the
movement of every phase is at most `k |β - α|`, and each transfer matrix is
`max 1 (4π|λ|)`-Lipschitz in its phase.  Finally `|log a - log b| ≤ |a - b|` for `a,b ≥ 1`
and `|‖A‖ - ‖B‖| ≤ ‖A - B‖` convert this to the logarithm of the Frobenius norm. -/

/-- The local iterates are ordered products of transfer matrices. -/
theorem iterC_eq_matProd (α lam : ℝ) (z : ℂ) (n : ℕ) (x : ℝ) :
    iterC α lam z n x = Work.TMC7Core.matProd (fun j => tmC lam z (x + (j : ℝ) * α)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterC_succ, ih, Work.TMC7Core.matProd_succ]

/-- **Frequency perturbation of the `k`-step transfer matrix.**  For `‖z‖ ≤ R` the
log-Frobenius norm of `A_k` is Lipschitz in the frequency, uniformly in the phase. -/
theorem iterC_alpha_perturb_lip (lam R : ℝ) (k : ℕ) (_hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α β : ℝ) (z : ℂ) (x : ℝ), ‖z‖ ≤ R →
      |Real.log (frob (iterC β lam z k x)) - Real.log (frob (iterC α lam z k x))|
        ≤ C * |β - α| := by
  set M : ℝ := Real.sqrt ((R + 2 * |lam|) ^ 2 + 2) with hMdef
  set L : ℝ := max 1 (4 * Real.pi * |lam|) with hLdef
  have hM2 : Real.sqrt 2 ≤ M := by
    rw [hMdef]; apply Real.sqrt_le_sqrt; nlinarith [sq_nonneg (R + 2 * |lam|)]
  have hM0 : 0 ≤ M := le_trans (Real.sqrt_nonneg 2) hM2
  have hL0 : 0 ≤ L := by rw [hLdef]; exact le_trans zero_le_one (le_max_left _ _)
  have hmax0 : (0 : ℝ) ≤ max 1 (4 * Real.pi * |lam|) := le_trans zero_le_one (le_max_left _ _)
  refine ⟨(k : ℝ) ^ 2 * M ^ k * L,
    mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hM0 k)) hL0, ?_⟩
  intro α β z x hz
  have hMtm : ∀ y : ℝ, frob (tmC lam z y) ≤ M := by
    intro y
    rw [hMdef]
    refine le_trans (Work.TMC7Core.Scale.frob_tmC_le lam z y) (Real.sqrt_le_sqrt ?_)
    have h1 : ‖z‖ + 2 * |lam| ≤ R + 2 * |lam| := by linarith [abs_nonneg lam]
    have h2 : (0 : ℝ) ≤ ‖z‖ + 2 * |lam| := by positivity
    nlinarith [h2, h1]
  set A : ℕ → Matrix (Fin 2) (Fin 2) ℂ :=
    fun j => tmC lam z (x + min (j : ℝ) (k : ℝ) * β) with hAdef
  set B : ℕ → Matrix (Fin 2) (Fin 2) ℂ :=
    fun j => tmC lam z (x + min (j : ℝ) (k : ℝ) * α) with hBdef
  have hA : ∀ j, frob (A j) ≤ M := by intro j; rw [hAdef]; exact hMtm _
  have hB : ∀ j, frob (B j) ≤ M := by intro j; rw [hBdef]; exact hMtm _
  have hD0 : 0 ≤ L * (k : ℝ) * |β - α| :=
    mul_nonneg (mul_nonneg hL0 (Nat.cast_nonneg k)) (abs_nonneg _)
  have hAB : ∀ j, frob (A j - B j) ≤ L * (k : ℝ) * |β - α| := by
    intro j
    rw [hAdef, hBdef]
    have h1 := Work.TMC7Core.Scale.frob_tmC_sub_le lam z z
      (x + min (j : ℝ) (k : ℝ) * β) (x + min (j : ℝ) (k : ℝ) * α)
    rw [sub_self, norm_zero, zero_add] at h1
    refine le_trans h1 ?_
    have harg : |(x + min (j : ℝ) (k : ℝ) * β) - (x + min (j : ℝ) (k : ℝ) * α)|
        = min (j : ℝ) (k : ℝ) * |β - α| := by
      rw [show (x + min (j : ℝ) (k : ℝ) * β) - (x + min (j : ℝ) (k : ℝ) * α)
            = min (j : ℝ) (k : ℝ) * (β - α) by ring, abs_mul,
          abs_of_nonneg (le_min (Nat.cast_nonneg j) (Nat.cast_nonneg k))]
    rw [harg, hLdef]
    have hmk : min (j : ℝ) (k : ℝ) ≤ (k : ℝ) := min_le_right _ _
    have h3 : min (j : ℝ) (k : ℝ) * |β - α| ≤ (k : ℝ) * |β - α| :=
      mul_le_mul_of_nonneg_right hmk (abs_nonneg _)
    calc max 1 (4 * Real.pi * |lam|) * (min (j : ℝ) (k : ℝ) * |β - α|)
        ≤ max 1 (4 * Real.pi * |lam|) * ((k : ℝ) * |β - α|) :=
          mul_le_mul_of_nonneg_left h3 hmax0
      _ = max 1 (4 * Real.pi * |lam|) * (k : ℝ) * |β - α| := by ring
  have hmain : frob (Work.TMC7Core.matProd A k - Work.TMC7Core.matProd B k)
      ≤ (k : ℝ) * M ^ k * (L * (k : ℝ) * |β - α|) :=
    Work.TMC7Core.Scale.frob_matProd_sub_le A B M (L * (k : ℝ) * |β - α|)
      hM2 hD0 hA hB hAB k
  have hEA : iterC β lam z k x = Work.TMC7Core.matProd A k := by
    rw [iterC_eq_matProd]
    exact (Work.TMC7Core.Scale.matProd_congr (A := A)
      (B := fun j => tmC lam z (x + (j : ℝ) * β)) (n := k) (fun j hj => by
        have hq : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast (le_of_lt hj)
        simp only [hAdef, min_eq_left hq])).symm
  have hEB : iterC α lam z k x = Work.TMC7Core.matProd B k := by
    rw [iterC_eq_matProd]
    exact (Work.TMC7Core.Scale.matProd_congr (A := B)
      (B := fun j => tmC lam z (x + (j : ℝ) * α)) (n := k) (fun j hj => by
        have hq : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast (le_of_lt hj)
        simp only [hBdef, min_eq_left hq])).symm
  have hstep : frob (iterC β lam z k x - iterC α lam z k x)
      ≤ (k : ℝ) ^ 2 * M ^ k * L * |β - α| := by
    rw [hEA, hEB]
    calc frob (Work.TMC7Core.matProd A k - Work.TMC7Core.matProd B k)
        ≤ (k : ℝ) * M ^ k * (L * (k : ℝ) * |β - α|) := hmain
      _ = (k : ℝ) ^ 2 * M ^ k * L * |β - α| := by ring
  have h1 : 1 ≤ frob (iterC β lam z k x) := one_le_frob_iterC β lam z k x
  have h2 : 1 ≤ frob (iterC α lam z k x) := one_le_frob_iterC α lam z k x
  calc |Real.log (frob (iterC β lam z k x)) - Real.log (frob (iterC α lam z k x))|
      ≤ |frob (iterC β lam z k x) - frob (iterC α lam z k x)| :=
        Work.TMC7Core.Scale.abs_log_sub_log_le _ _ h1 h2
    _ ≤ frob (iterC β lam z k x - iterC α lam z k x) :=
        Work.TMC7Core.Scale.abs_frob_sub_le _ _
    _ ≤ (k : ℝ) ^ 2 * M ^ k * L * |β - α| := hstep

/-! ## 3. The main theorem -/

theorem transferEstimate (hLE : Work.TMC14Core.P_LEBasics) :
    ∀ (α lam c d : ℝ), Irrational α → 0 < lam → lam ≤ 1 → c < d →
      (∀ E ∈ Set.Icc c d, lyap α lam (E:ℂ) = 0) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ Q : ℕ, ∃ r : ℝ, 0 < r ∧
        ∀ (p : ℤ) (q : ℕ), Q ≤ q → |α - (p:ℝ)/(q:ℝ)| < δ/(q:ℝ) →
          ∀ z : ℂ, (∃ E ∈ Set.Icc c d, ‖z - E‖ < r) → ∀ θ : ℝ,
            frob (iterC ((p:ℝ)/(q:ℝ)) lam z q θ) ≤ Real.exp (ε * (q:ℝ)) := by
  intro α lam c d hIrr hlam0 hlam1 hcd hzero ε hε
  -- ## Step 1: uniform bound near the window at the irrational frequency
  obtain ⟨ρ, hρpos, n₀, hn₀⟩ :=
    uniform_small_scale hLE α lam c d hIrr hcd hzero (ε / 8) (by linarith)
  -- ## Step 2: block length
  set k : ℕ := max n₀ 1 with hkdef
  have hk1 : 1 ≤ k := le_max_right _ _
  have hkn : n₀ ≤ k := le_max_left _ _
  -- ## Step 3: radius and energy bound
  set r : ℝ := min ρ 1 with hrdef
  have hrpos : 0 < r := lt_min hρpos one_pos
  have hrρ : r ≤ ρ := min_le_left _ _
  have hr1 : r ≤ 1 := min_le_right _ _
  set R : ℝ := max |c| |d| + 1 with hRdef
  set M : ℝ := Real.sqrt ((R + 2 * |lam|) ^ 2 + 2) with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef, ← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (R + 2 * |lam|)]
  have hM0 : 0 ≤ M := le_trans zero_le_one hM1
  -- ## Step 4: perturbation constant
  obtain ⟨C, hC0, hCbd⟩ := iterC_alpha_perturb_lip lam R k hk1
  -- ## Step 5: the two constants δ, Q
  set δ : ℝ := (3 * (k : ℝ) * ε / 8) / (C + 1) with hδdef
  have hCp : (0 : ℝ) < C + 1 := by linarith
  have hδpos : 0 < δ := by
    rw [hδdef]; exact div_pos (by positivity) hCp
  have hδbd : C * δ < 3 * (k : ℝ) * ε / 8 := by
    have h3 : (0 : ℝ) < 3 * (k : ℝ) * ε / 8 := by
      have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
      positivity
    rw [hδdef, mul_div_assoc']
    rw [div_lt_iff₀ hCp]
    nlinarith [h3, hC0]
  obtain ⟨Q₀, hQ₀⟩ := exists_nat_ge (2 * (Real.log (Real.sqrt 2 * M ^ k) + 1) / ε)
  set Q : ℕ := max k Q₀ with hQdef
  refine ⟨δ, hδpos, Q, r, hrpos, ?_⟩
  intro p q hQq hαp z hz θ
  set β : ℝ := (p : ℝ) / (q : ℝ) with hβdef
  have hqk : k ≤ q := le_trans (le_max_left k Q₀) hQq
  have hq1 : 1 ≤ q := le_trans hk1 hqk
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hqQ₀ : Q₀ ≤ q := le_trans (le_max_right k Q₀) hQq
  have hqQ₀' : (Q₀ : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqQ₀
  -- the energy `z` sits in the window's neighbourhood, and `‖z‖ ≤ R`
  have hzρ : ∃ E ∈ Set.Icc c d, ‖z - E‖ < ρ := by
    obtain ⟨E, hE, hElt⟩ := hz; exact ⟨E, hE, lt_of_lt_of_le hElt hrρ⟩
  have hzR : ‖z‖ ≤ R := by
    obtain ⟨E, hE, hElt⟩ := hz
    have hsplit : ‖z‖ ≤ ‖z - E‖ + ‖(E : ℂ)‖ := by
      have h := norm_add_le (z - E) (E : ℂ)
      simpa using h
    have hEnorm : ‖(E : ℂ)‖ = |E| := RCLike.norm_ofReal E
    have hEmax : |E| ≤ max |c| |d| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le c, le_max_left |c| |d|, hE.1]
      · linarith [le_abs_self d, le_max_right |c| |d|, hE.2]
    have : ‖z - E‖ < 1 := lt_of_lt_of_le hElt hr1
    rw [hEnorm] at hsplit
    rw [hRdef]; linarith
  -- ## Step 6: every block of length `k` has norm at most `exp (k ε / 2)`
  have hblock : ∀ y : ℝ, frob (iterC β lam z k y) ≤ Real.exp ((k : ℝ) * ε / 2) := by
    intro y
    have hαbd : Real.log (frob (iterC α lam z k y)) ≤ (k : ℝ) * (ε / 8) := hn₀ z hzρ k hkn y
    have hdiff : |Real.log (frob (iterC β lam z k y)) - Real.log (frob (iterC α lam z k y))|
        ≤ C * |β - α| := hCbd α β z y hzR
    have hβα : |β - α| ≤ δ := by
      have hlt : |β - α| < δ / (q : ℝ) := by
        simpa [abs_sub_comm] using hαp
      have hq1' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      have h2 : δ / (q : ℝ) ≤ δ := by
        rw [div_le_iff₀ hqpos]; nlinarith [hδpos, hq1']
      linarith
    have hlog : Real.log (frob (iterC β lam z k y)) ≤ (k : ℝ) * ε / 2 := by
      have h1 : Real.log (frob (iterC β lam z k y)) - Real.log (frob (iterC α lam z k y))
          ≤ C * |β - α| := le_of_abs_le hdiff
      have h2 : C * |β - α| ≤ C * δ := mul_le_mul_of_nonneg_left hβα hC0
      have h3 : C * δ ≤ 3 * (k : ℝ) * ε / 8 := le_of_lt hδbd
      have h4 : (k : ℝ) * (ε / 8) + 3 * (k : ℝ) * ε / 8 = (k : ℝ) * ε / 2 := by ring
      linarith
    have hpos : 0 < frob (iterC β lam z k y) :=
      lt_of_lt_of_le one_pos (one_le_frob_iterC β lam z k y)
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.mpr hlog
  -- ## Step 7: the remainder block
  have hrem : ∀ j : ℕ, j < k → ∀ y : ℝ, frob (iterC β lam z j y) ≤ Real.sqrt 2 * M ^ k := by
    intro j hj y
    have h1 : frob (iterC β lam z j y) ≤ Real.sqrt 2 * M ^ j := frob_iterC_le_pow β lam z R hzR j y
    have h2 : M ^ j ≤ M ^ k := pow_le_pow_right₀ hM1 (le_of_lt hj)
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 2))
  -- ## Step 8: assemble
  have hmain := block_prod_bound β lam z k q hk1 (Real.exp ((k : ℝ) * ε / 2)) (Real.sqrt 2 * M ^ k)
    (Real.exp_nonneg _) hblock hrem θ
  have hexp1 : (Real.exp ((k : ℝ) * ε / 2)) ^ (q / k) ≤ Real.exp ((q : ℝ) * ε / 2) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h : ((q / k : ℕ) : ℝ) * (k : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (Nat.div_mul_le_self q k)
    nlinarith [h, hε]
  have hconst : Real.sqrt 2 * M ^ k ≤ Real.exp ((q : ℝ) * ε / 2) := by
    have hL : Real.log (Real.sqrt 2 * M ^ k) ≤ (q : ℝ) * ε / 2 := by
      have h1 : 2 * (Real.log (Real.sqrt 2 * M ^ k) + 1) ≤ (Q₀ : ℝ) * ε := by
        rw [div_le_iff₀ hε] at hQ₀; linarith
      have h2 : (Q₀ : ℝ) * ε / 2 ≤ (q : ℝ) * ε / 2 := by nlinarith [hε]
      linarith
    have hpos : 0 < Real.sqrt 2 * M ^ k := by positivity
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.mpr hL
  calc frob (iterC β lam z q θ)
      ≤ Real.sqrt 2 * M ^ k * (Real.exp ((k : ℝ) * ε / 2)) ^ (q / k) := hmain
    _ ≤ Real.exp ((q : ℝ) * ε / 2) * Real.exp ((q : ℝ) * ε / 2) :=
        mul_le_mul hconst hexp1 (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (ε * (q : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring

end Work.TMC14Core
