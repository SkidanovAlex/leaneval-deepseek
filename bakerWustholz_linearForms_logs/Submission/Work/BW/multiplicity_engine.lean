import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.DefsMult
import Submission.Work.BW.zeroest_defs
import Submission.Work.BW.ellW_B_mem_span
import Submission.Work.BW.exists_det_submatrix_ne_zero
import Submission.Work.BW.cardMod_true_of_linearIndependent
import Submission.Work.BW.cardMod_true_rank_one
import Submission.Work.BW.int_mem_span_of_mem_span_rat
import Submission.Work.BW.cast_mem_span_rat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The exclusion table and the transfer for `multiplicity_prop` (BW §10)

This file contains the *engine* of `Work.BW.multiplicity_prop`: given the output of
`zero_estimate_stepwise` (a connected subgroup `G' = G_a^ε × ker 𝒵` of codimension `k`, a step
`m` and Philippon's inequality), together with the exclusion conditions (E0)–(E3), it produces
the theorem's conclusion — or a contradiction.

The engine is stated in the dimension `N` in which the zero estimate is applied, with the
conclusion measured against the ambient dimension `r ≥ N` (the `(N+1)!` of the zero estimate is
compared with the `(r+1)!` of `constA`/`constB` through `Nat.descFactorial_le`). For the
non-degenerate application `N = r` and `δ = 𝒟`; for the partially degenerate application
`N = N' < r` and `δ = 𝒟 ∘ liftIdx σ`.
-/

namespace Work.BW

open scoped BigOperators

/-! ## Small sequence/monotonicity helpers -/

/-- A sequence that does not increase at every step is nonincreasing on `{0,…,r}`. -/
lemma anti_of_step {r : ℕ} {f : ℕ → ℕ} (hf : ∀ m, m < r → f (m + 1) ≤ f m) :
    ∀ ⦃i j : ℕ⦄, i ≤ j → j ≤ r → f j ≤ f i := by
  intro i j hij
  induction hij with
  | refl => intro _; exact le_rfl
  | step h ih => intro hj; exact le_trans (hf _ (by omega)) (ih (by omega))

/-- `Sq (k-1) + 1 ≤ Sq m + 1` for `m + 1 ≤ k ≤ r`. -/
lemma sq_le_succ {r : ℕ} {Sq : ℕ → ℕ} (hSa : ∀ m, m < r → Sq (m + 1) ≤ Sq m)
    {m k : ℕ} (hm : m + 1 ≤ k) (hk : k ≤ r) : Sq (k - 1) + 1 ≤ Sq m + 1 := by
  exact Nat.succ_le_succ (anti_of_step hSa (by omega) (by omega))

/-- `C(Tq (k-1) + k-1, k-1) ≤ C(Tq m + k-1, k-1)` for `m + 1 ≤ k ≤ r`. -/
lemma choose_mono_top {r : ℕ} {Tq : ℕ → ℕ} (hTa : ∀ m, m < r → Tq (m + 1) ≤ Tq m)
    {m k : ℕ} (hm : m + 1 ≤ k) (hk : k ≤ r) :
    (Tq (k - 1) + (k - 1)).choose (k - 1) ≤ (Tq m + (k - 1)).choose (k - 1) := by
  have h3 : Tq (k - 1) ≤ Tq m := anti_of_step hTa (by omega) (by omega)
  exact Nat.choose_le_choose (k - 1) (Nat.add_le_add_right h3 (k - 1))

/-- Pascal comparison: `C(N₂, k-1) ≤ C(N₁, k)` when `N₂ + 1 ≤ N₁` and `1 ≤ k`. -/
lemma choose_le_choose_of_lt (N₁ N₂ k : ℕ) (h : N₂ + 1 ≤ N₁) (hk : 1 ≤ k) :
    N₂.choose (k - 1) ≤ N₁.choose k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h1 : N₂.choose k' ≤ (N₁ - 1).choose k' := Nat.choose_le_choose k' (by omega)
  have h2 : (N₁ - 1).choose k' ≤ N₁.choose (k' + 1) := by
    cases N₁ with
    | zero => omega
    | succ n =>
        simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
        rw [Nat.choose_succ_succ]
        omega
  exact le_trans h1 h2

/-- `n! = (n-k)! * n.descFactorial k` for `k ≤ n`. -/
lemma factorial_eq_factorial_mul_descFactorial {n k : ℕ} (hk : k ≤ n) :
    n.factorial = (n - k).factorial * n.descFactorial k :=
  (Nat.factorial_mul_descFactorial hk).symm

/-- `∏ i, f i = (∏ i ∈ J, f i) * (∏ i ∈ Jᶜ, f i)`. -/
lemma prod_split {N : ℕ} (f : Fin N → ℝ) (J : Finset (Fin N)) :
    ∏ i : Fin N, f i = (∏ i ∈ J, f i) * (∏ i ∈ Jᶜ, f i) := by
  classical
  have h := Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin N))
    (fun i => i ∈ J) f
  have h1 : (Finset.univ.filter fun i : Fin N => i ∈ J) = J := by ext i; simp
  have h2 : (Finset.univ.filter fun i : Fin N => ¬ (i ∈ J)) = Jᶜ := by ext i; simp
  rw [h1, h2] at h
  exact h.symm

/-- `cardMod` is at least `1`. -/
lemma one_le_cardMod {N ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) (θ : Fin N → ℂ) (S : ℕ) :
    1 ≤ cardMod ε M θ S := by
  have hmem : ((if ε then (0 : ℂ) else (S : ℂ)),
      fun j : Fin ρ => ∏ i, θ i ^ ((S : ℤ) * M j i)) ∈
      (Finset.range (S + 1)).image
        (fun s : ℕ => ((if ε then (0 : ℂ) else (s : ℂ)),
          fun j : Fin ρ => ∏ i, θ i ^ ((s : ℤ) * M j i))) :=
    Finset.mem_image.mpr ⟨S, Finset.mem_range.mpr (Nat.lt_succ_self S), rfl⟩
  have hne : ((Finset.range (S + 1)).image
        (fun s : ℕ => ((if ε then (0 : ℂ) else (s : ℂ)),
          fun j : Fin ρ => ∏ i, θ i ^ ((s : ℤ) * M j i)))).card ≠ 0 :=
    Finset.card_ne_zero_of_mem hmem
  simpa only [cardMod] using Nat.one_le_iff_ne_zero.mpr hne

/-- `a ≤ b → 0 ≤ c → a * c ≤ b * c` for `ℝ` (which has no `MulLeftMono`). -/
lemma mul_le_mul_of_nonneg_rightℝ {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  nlinarith [h, hc]

/-- `a ≤ b → 0 ≤ c → c * a ≤ c * b` for `ℝ`. -/
lemma mul_le_mul_of_nonneg_leftℝ {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  nlinarith [h, hc]

/-- `a ≤ b → c ≤ d → 0 ≤ a → 0 ≤ c → a * c ≤ b * d` for `ℝ`. -/
lemma mul_le_mulℝ {a b c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ a) (h4 : 0 ≤ c) :
    a * c ≤ b * d := by
  nlinarith [h1, h2, h3, h4]

/-- A single term of a sum is at most the sum. -/
lemma sq_le_sum {N m : ℕ} (Sq : ℕ → ℕ) (hm : m ≤ N) :
    Sq m ≤ ∑ k ∈ Finset.range (N + 1), Sq k :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))

/-- Some `ρ`-element set of columns carries a non-zero minor. -/
lemma exists_minorJ_ne_zero {ρ N : ℕ} (M : Fin ρ → Fin N → ℤ)
    (hM : LinearIndependent ℚ (fun j i => (M j i : ℚ))) :
    ∃ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 := by
  obtain ⟨J, hJ, hdet⟩ :=
    exists_det_submatrix_ne_zero (K := ℚ) (A := fun j i => (M j i : ℚ)) hM
  refine ⟨J, hJ, fun h0 => hdet ?_⟩
  have hcast : ((minorJ M J hJ : ℤ) : ℚ) =
      (Matrix.submatrix (fun j i => (M j i : ℚ)) id (J.orderEmbOfFin hJ)).det := by
    have h1 : ((minorJ M J hJ : ℤ) : ℚ) =
        (Matrix.map (fun a b : Fin ρ => M a (J.orderEmbOfFin hJ b)) (fun z : ℤ => (z : ℚ))).det :=
      Int.cast_det _
    rw [h1]
    rfl
  rw [← hcast]
  simp [h0]

/-- A non-zero integer has absolute value at least one. -/
lemma one_le_abs_int {n : ℤ} (h : n ≠ 0) : (1 : ℤ) ≤ |n| := by
  rcases lt_or_gt_of_ne h.symm with hgt | hlt
  · rw [abs_of_pos hgt]; omega
  · rw [abs_of_neg hlt]; omega

/-! ## The hypothesis package -/

/-- The data consumed by the exclusion table: the degree bounds `δ` in the dimension `N` in which
the zero estimate is applied, the budgets `𝒮`, the step sequences `Sq`/`Tq`, the exclusion
conditions (E0)–(E3), and the logarithmic-form data `B`, `ℓ`. -/
structure ZEData (N r : ℕ) where
  hNr : N ≤ r
  hr : 2 ≤ r
  δ : Fin (N + 1) → ℝ
  hδnn : ∀ i, 0 ≤ δ i
  hδ0 : 1 ≤ δ 0
  hδ1 : ∀ i, 1 ≤ ⌊δ i⌋₊
  𝒮 : ℝ
  hSpos : 0 < 𝒮
  Sq : ℕ → ℕ
  Tq : ℕ → ℕ
  hSa : ∀ m, m < N → Sq (m + 1) ≤ Sq m
  hTa : ∀ m, m < N → Tq (m + 1) ≤ Tq m
  hSsum : ((∑ m ∈ Finset.range (N + 1), Sq m : ℕ) : ℝ) ≤ 𝒮
  hE0 : ∀ j : Fin N, ((r : ℝ) + 1) * δ j.succ < (Tq 0 : ℝ) + 1
  hE1 : ∀ m, m < r → ∀ e : Fin (N + 1) → ℕ, (∀ i, e i ≤ 1) → ∑ i, e i = m + 1 →
      ((r + 1).descFactorial (m + 1) : ℝ) * ∏ i, δ i ^ e i <
        ((Sq m : ℝ) + 1) * ((Tq m + m + 1).choose (m + 1) : ℝ)
  hE2 : N = r → ((N + 1).factorial : ℝ) * ∏ i, ((⌊δ i⌋₊ : ℕ) : ℝ) <
      ((Sq N : ℝ) + 1) * ((Tq N + N).choose N : ℝ)
  hE3 : N = r → ((N + 1).factorial : ℝ) * ∏ i : Fin N, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) <
      ((Sq (N - 1) : ℝ) + 1) * ((Tq (N - 1) + (N - 1)).choose (N - 1) : ℝ)
  B : Fin N → ℤ
  hB : B ≠ 0
  ℓ : Fin N → ℂ
  hℓ : LinearIndependent ℚ ℓ
  hΛ : ‖∑ i, (B i : ℂ) * ℓ i‖ < Real.pi / 𝒮
/-! ## Cancellation of the zero estimate's inequality -/

/-- **Case `ε = true`.** If the zero estimate's inequality is read at `L = j` and step `m ≥ i`,
then it dominates

`(Sq i + 1) · C(Tq i + j, j) · |Δ_J| ≤ (N+1).descFactorial ρ · ∏_{i∈J} Dd_{i+1}`,

for every `J` with non-vanishing minor. (`i = j = ρ-1` is the transfer, `i = ρ-1, j = ρ` the
transversal exclusion.) -/
lemma ze_cancel_true {N r : ℕ} (D : ZEData N r) (ρ i j : ℕ) (M : Fin ρ → Fin N → ℤ) (m L : ℕ)
    (hL : L = j) (hmi : m ≤ i) (hiN : i ≤ N) (hρN : ρ ≤ N)
    (hcard : D.Sq m + 1 ≤ cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq m))
    (hineq : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
      (((D.Tq m + L).choose L : ℕ) : ℝ) *
          (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) *
        ((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
        ((⌊D.δ 0⌋₊ : ℕ) : ℝ) * ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) ≤
        ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ))
    (J : Finset (Fin N)) (hJ : J.card = ρ) (hΔ : minorJ M J hJ ≠ 0) :
    (((D.Sq i : ℝ) + 1) * ((D.Tq i + j).choose j : ℝ)) * |(minorJ M J hJ : ℝ)| ≤
      ((N + 1).descFactorial ρ : ℝ) * ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by
  classical
  have hCr : ((D.Tq i + j).choose j : ℝ) ≤ ((D.Tq m + L).choose L : ℝ) := by
    have h1 : D.Tq i ≤ D.Tq m := anti_of_step D.hTa hmi hiN
    have h2 : (D.Tq i + j).choose j ≤ (D.Tq m + L).choose L := by
      rw [hL]
      exact Nat.choose_le_choose j (Nat.add_le_add_right h1 j)
    exact_mod_cast h2
  have hS : (D.Sq i : ℝ) + 1 ≤ (D.Sq m : ℝ) + 1 := by
    have h1 : D.Sq i ≤ D.Sq m := anti_of_step D.hSa hmi hiN
    exact_mod_cast Nat.succ_le_succ h1
  have hze := hineq J hJ hΔ
  try simp only [mul_one, one_mul] at hze
  have hPCpos : (0 : ℝ) < ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by
    apply Finset.prod_pos
    intro i _
    have h : 1 ≤ ⌊D.δ i.succ⌋₊ := D.hδ1 i.succ
    exact_mod_cast (by omega : (0 : ℕ) < ⌊D.δ i.succ⌋₊)
  have hprod : ∏ i : Fin (N + 1), ((⌊D.δ i⌋₊ : ℕ) : ℝ) =
      ((⌊D.δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) *
        (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) := by
    rw [Fin.prod_univ_succ, prod_split (fun i : Fin N => ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) J]
    ring
  have hfact : ((N + 1).factorial : ℝ) =
      ((N + 1 - ρ).factorial : ℝ) * ((N + 1).descFactorial ρ : ℝ) := by
    have h := factorial_eq_factorial_mul_descFactorial (n := N + 1) (k := ρ) (by omega)
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
  have hstep : (((D.Sq i : ℝ) + 1) * ((D.Tq i + j).choose j : ℝ)) *
      (((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
        (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))
      ≤ ((N + 1 - ρ).factorial : ℝ) * ((N + 1).descFactorial ρ : ℝ) *
        (((⌊D.δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) *
          (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by
    calc (((D.Sq i : ℝ) + 1) * ((D.Tq i + j).choose j : ℝ)) *
          (((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
            (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))
        ≤ (((D.Sq m : ℝ) + 1) * ((D.Tq m + L).choose L : ℝ)) *
            (((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
              (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by
          apply mul_le_mul_of_nonneg_rightℝ (mul_le_mulℝ hS hCr (by positivity) (by positivity))
          positivity
      _ ≤ (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) *
            ((((D.Tq m + L).choose L : ℝ) * ((N + 1 - ρ).factorial : ℝ) *
              |(minorJ M J hJ : ℝ)| * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
              (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))) := by
          have h1 : (D.Sq m : ℝ) + 1 ≤
              (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) := by
            exact_mod_cast hcard
          calc (((D.Sq m : ℝ) + 1) * ((D.Tq m + L).choose L : ℝ)) *
                (((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
                  (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))
              = ((D.Sq m : ℝ) + 1) * (((D.Tq m + L).choose L : ℝ) *
                  ((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
                  (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by ring
            _ ≤ (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) *
                  ((((D.Tq m + L).choose L : ℝ) * ((N + 1 - ρ).factorial : ℝ) *
                    |(minorJ M J hJ : ℝ)| * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
                    (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))) :=
                mul_le_mul_of_nonneg_rightℝ h1 (by positivity)
      _ ≤ ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ) := by
          calc _ = (((D.Tq m + L).choose L : ℕ) : ℝ) *
                (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) *
                ((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
                ((⌊D.δ 0⌋₊ : ℕ) : ℝ) * ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by ring
            _ ≤ ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ) := hze
      _ = ((N + 1 - ρ).factorial : ℝ) * ((N + 1).descFactorial ρ : ℝ) *
            (((⌊D.δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) *
              (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by
          rw [hfact, hprod] <;> try ring
  have hdivpos : (0 : ℝ) < ((N + 1 - ρ).factorial : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
      (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) := by
    refine mul_pos (mul_pos ?_ ?_) hPCpos
    · exact_mod_cast Nat.factorial_pos _
    · exact_mod_cast (by have h := D.hδ1 0; omega : (0 : ℕ) < ⌊D.δ 0⌋₊)
  refine le_of_mul_le_mul_right ?_ hdivpos
  calc ((((D.Sq i : ℝ) + 1) * ((D.Tq i + j).choose j : ℝ)) * |(minorJ M J hJ : ℝ)|) *
        (((N + 1 - ρ).factorial : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
          (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))
      = (((D.Sq i : ℝ) + 1) * ((D.Tq i + j).choose j : ℝ)) *
        (((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
          (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by ring
    _ ≤ ((N + 1 - ρ).factorial : ℝ) * ((N + 1).descFactorial ρ : ℝ) *
        (((⌊D.δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) *
          (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := hstep
    _ = (((N + 1).descFactorial ρ : ℝ) * (∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) *
        (((N + 1 - ρ).factorial : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
          (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by ring

/-- **Case `ε = false`.** Same cancellation; the factor `Dd₀` survives on the right. -/
lemma ze_cancel_false {N r : ℕ} (D : ZEData N r) (ρ i j : ℕ) (M : Fin ρ → Fin N → ℤ) (m L : ℕ)
    (hL : L = j) (hmi : m ≤ i) (hiN : i ≤ N) (hρN : ρ ≤ N)
    (hcard : D.Sq m + 1 ≤ cardMod false M (fun i => Complex.exp (D.ℓ i)) (D.Sq m))
    (hineq : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
      (((D.Tq m + L).choose L : ℕ) : ℝ) *
          (cardMod false M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) *
        ((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
        1 * ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) ≤
        ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ))
    (J : Finset (Fin N)) (hJ : J.card = ρ) (hΔ : minorJ M J hJ ≠ 0) :
    (((D.Sq i : ℝ) + 1) * ((D.Tq i + j).choose j : ℝ)) * |(minorJ M J hJ : ℝ)| ≤
      ((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
        ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by
  classical
  have hCr : ((D.Tq i + j).choose j : ℝ) ≤ ((D.Tq m + L).choose L : ℝ) := by
    have h1 : D.Tq i ≤ D.Tq m := anti_of_step D.hTa hmi hiN
    have h2 : (D.Tq i + j).choose j ≤ (D.Tq m + L).choose L := by
      rw [hL]
      exact Nat.choose_le_choose j (Nat.add_le_add_right h1 j)
    exact_mod_cast h2
  have hS : (D.Sq i : ℝ) + 1 ≤ (D.Sq m : ℝ) + 1 := by
    have h1 : D.Sq i ≤ D.Sq m := anti_of_step D.hSa hmi hiN
    exact_mod_cast Nat.succ_le_succ h1
  have hze := hineq J hJ hΔ
  try simp only [mul_one, one_mul] at hze
  have hPCpos : (0 : ℝ) < ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by
    apply Finset.prod_pos
    intro i _
    have h : 1 ≤ ⌊D.δ i.succ⌋₊ := D.hδ1 i.succ
    exact_mod_cast (by omega : (0 : ℕ) < ⌊D.δ i.succ⌋₊)
  have hprod : ∏ i : Fin (N + 1), ((⌊D.δ i⌋₊ : ℕ) : ℝ) =
      ((⌊D.δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) *
        (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) := by
    rw [Fin.prod_univ_succ, prod_split (fun i : Fin N => ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) J]
    ring
  have hfact : ((N + 1).factorial : ℝ) =
      ((N + 1 - (ρ + 1)).factorial : ℝ) * ((N + 1).descFactorial (ρ + 1) : ℝ) := by
    have h := factorial_eq_factorial_mul_descFactorial (n := N + 1) (k := ρ + 1) (by omega)
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
  have hstep : (((D.Sq i : ℝ) + 1) * ((D.Tq i + j).choose j : ℝ)) *
      (((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
        (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))
      ≤ ((N + 1 - (ρ + 1)).factorial : ℝ) * ((N + 1).descFactorial (ρ + 1) : ℝ) *
        (((⌊D.δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) *
          (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by
    calc (((D.Sq i : ℝ) + 1) * ((D.Tq i + j).choose j : ℝ)) *
          (((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
            (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))
        ≤ (((D.Sq m : ℝ) + 1) * ((D.Tq m + L).choose L : ℝ)) *
            (((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
              (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by
          apply mul_le_mul_of_nonneg_rightℝ (mul_le_mulℝ hS hCr (by positivity) (by positivity))
          positivity
      _ ≤ (cardMod false M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) *
            ((((D.Tq m + L).choose L : ℝ) * ((N + 1 - (ρ + 1)).factorial : ℝ) *
              |(minorJ M J hJ : ℝ)| *
              (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))) := by
          have h1 : (D.Sq m : ℝ) + 1 ≤
              (cardMod false M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) := by
            exact_mod_cast hcard
          calc (((D.Sq m : ℝ) + 1) * ((D.Tq m + L).choose L : ℝ)) *
                (((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
                  (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))
              = ((D.Sq m : ℝ) + 1) * (((D.Tq m + L).choose L : ℝ) *
                  ((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
                  (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by ring
            _ ≤ (cardMod false M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) *
                  ((((D.Tq m + L).choose L : ℝ) * ((N + 1 - (ρ + 1)).factorial : ℝ) *
                    |(minorJ M J hJ : ℝ)| *
                    (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))) :=
                mul_le_mul_of_nonneg_rightℝ h1 (by positivity)
      _ ≤ ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ) := by
          calc _ = (((D.Tq m + L).choose L : ℕ) : ℝ) *
                (cardMod false M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) *
                ((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
                ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by ring
            _ ≤ ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ) := hze
      _ = ((N + 1 - (ρ + 1)).factorial : ℝ) * ((N + 1).descFactorial (ρ + 1) : ℝ) *
            (((⌊D.δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) *
              (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by
          rw [hfact, hprod] <;> try ring
  have hdivpos : (0 : ℝ) < ((N + 1 - (ρ + 1)).factorial : ℝ) *
      (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) :=
    mul_pos (by exact_mod_cast Nat.factorial_pos _) hPCpos
  refine le_of_mul_le_mul_right ?_ hdivpos
  calc ((((D.Sq i : ℝ) + 1) * ((D.Tq i + j).choose j : ℝ)) * |(minorJ M J hJ : ℝ)|) *
        (((N + 1 - (ρ + 1)).factorial : ℝ) * (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))
      = (((D.Sq i : ℝ) + 1) * ((D.Tq i + j).choose j : ℝ)) *
        (((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
          (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by ring
    _ ≤ ((N + 1 - (ρ + 1)).factorial : ℝ) * ((N + 1).descFactorial (ρ + 1) : ℝ) *
        (((⌊D.δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) *
          (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := hstep
    _ = (((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
          (∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) *
        (((N + 1 - (ρ + 1)).factorial : ℝ) *
          (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by ring

/-! ## The maximising minor and the transfer -/

/-- A non-zero integral minor has absolute value at least one. -/
lemma one_le_abs_minorJ {ρ N : ℕ} {M : Fin ρ → Fin N → ℤ} {J : Finset (Fin N)}
    {hJ : J.card = ρ} (hΔ : minorJ M J hJ ≠ 0) : (1 : ℝ) ≤ |(minorJ M J hJ : ℝ)| := by
  have h : (1 : ℤ) ≤ |minorJ M J hJ| := one_le_abs_int hΔ
  have h2 : ((1 : ℤ) : ℝ) ≤ ((|minorJ M J hJ| : ℤ) : ℝ) := by exact_mod_cast h
  have h3 : ((1 : ℤ) : ℝ) ≤ |((minorJ M J hJ : ℤ) : ℝ)| := by rwa [Int.cast_abs] at h2
  simpa using h3

/-- `constA r ρ ≥ 0`. -/
lemma constA_nonneg (r ρ : ℕ) : 0 ≤ constA r ρ := by
  have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 - (ρ : ℤ)) := zpow_nonneg (by norm_num) _
  have h2 : (0 : ℝ) ≤ (ρ.factorial : ℝ) ^ 2 := by positivity
  have h3 : (0 : ℝ) ≤ (r : ℝ) ^ ρ := by positivity
  have h4 : (0 : ℝ) ≤ ((r + 1).descFactorial ρ : ℝ) := by positivity
  rw [constA]
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4

/-- `constB r ρ ≥ 0`. -/
lemma constB_nonneg (r ρ : ℕ) : 0 ≤ constB r ρ := by
  have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 - (ρ : ℤ)) := zpow_nonneg (by norm_num) _
  have h2 : (0 : ℝ) ≤ (ρ.factorial : ℝ) ^ 2 := by positivity
  have h3 : (0 : ℝ) ≤ (r : ℝ) ^ ρ := by positivity
  have h4 : (0 : ℝ) ≤ ((r + 1).descFactorial (ρ + 1) : ℝ) := by positivity
  rw [constB]
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4

/-- The maximising `ρ`-set of columns and a Minkowski-reduced basis with the sharp bound.

`hmin` is the interface to `Work.BW.prim_basis_from_minors` (which needs the lattice machinery
`Work.BW.minkowski_basis`); it is passed as a hypothesis so that the exclusion table and the
transfer can be verified independently of that development. -/
lemma exists_maximiser {N r : ℕ} (D : ZEData N r) (ρ : ℕ) (M : Fin ρ → Fin N → ℤ)
    (hρ1 : 1 ≤ ρ) (hρN : ρ ≤ N) (hM : PrimSys M) (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (hmin : ∀ (J₀ : Finset (Fin N)) (hJ₀ : J₀.card = ρ),
      (∀ (I : Finset (Fin N)) (hI : I.card = ρ),
        |(minorJ M I hI : ℝ)| * ∏ i ∈ I, a i ≤ |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i) →
      ∃ M' : Fin ρ → Fin N → ℤ, PrimSys M' ∧
        Submodule.span ℤ (Set.range M') = Submodule.span ℤ (Set.range M) ∧
        (∏ j, ∑ i, a i * |(M' j i : ℝ)|) ≤
          (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * (N : ℝ) ^ ρ *
            |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i)
    (hred : ∀ (I : Finset (Fin N)) (hI : I.card = ρ), minorJ M I hI ≠ 0 →
      (((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ)) *
          |(minorJ M I hI : ℝ)| ≤
        ((N + 1).descFactorial ρ : ℝ) * ∏ i ∈ I, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) :
    ∃ (M' : Fin ρ → Fin N → ℤ) (J₀ : Finset (Fin N)) (hJ₀ : J₀.card = ρ),
      PrimSys M' ∧ Submodule.span ℤ (Set.range M') = Submodule.span ℤ (Set.range M) ∧
      minorJ M J₀ hJ₀ ≠ 0 ∧
      (∏ j, ∑ i, a i * |(M' j i : ℝ)|) ≤
        (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * (N : ℝ) ^ ρ *
          |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i ∧
      (((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ)) *
          |(minorJ M J₀ hJ₀ : ℝ)| ≤
        ((N + 1).descFactorial ρ : ℝ) * ∏ i ∈ J₀, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by
  classical
  have hne : ((Finset.univ : Finset (Fin N)).powersetCard ρ).Nonempty := by
    refine ⟨Finset.map ⟨fun i : Fin ρ => (⟨i.1, by have := i.2; omega⟩ : Fin N),
      fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩
      (Finset.univ : Finset (Fin ρ)), ?_⟩
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by simp⟩
  obtain ⟨J₀, hJ₀mem, hJ₀max⟩ := Finset.exists_max_image
    ((Finset.univ : Finset (Fin N)).powersetCard ρ)
    (fun I => if h : I.card = ρ then |(minorJ M I h : ℝ)| * ∏ i ∈ I, a i else 0) hne
  have hJ₀ : J₀.card = ρ := (Finset.mem_powersetCard.mp hJ₀mem).2
  obtain ⟨J₁, hJ₁, hΔ₁⟩ := exists_minorJ_ne_zero M hM.1
  have hmem₁ : J₁ ∈ (Finset.univ : Finset (Fin N)).powersetCard ρ :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ J₁, hJ₁⟩
  have hmax₁ := hJ₀max J₁ hmem₁
  have hpos₁ : 0 < |(minorJ M J₁ hJ₁ : ℝ)| * ∏ i ∈ J₁, a i :=
    mul_pos (abs_pos.mpr (fun h => hΔ₁ (by exact_mod_cast h)))
      (Finset.prod_pos fun i _ => ha i)
  have hpos₀ : 0 < |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i := by
    have h := hmax₁
    rw [dif_pos hJ₁, dif_pos hJ₀] at h
    exact lt_of_lt_of_le hpos₁ h
  have hΔ₀ : minorJ M J₀ hJ₀ ≠ 0 := by
    intro h0
    rw [h0] at hpos₀
    simp at hpos₀
  have hmax : ∀ (I : Finset (Fin N)) (hI : I.card = ρ),
      |(minorJ M I hI : ℝ)| * ∏ i ∈ I, a i ≤ |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i := by
    intro I hI
    have hmem : I ∈ (Finset.univ : Finset (Fin N)).powersetCard ρ :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ I, hI⟩
    have h := hJ₀max I hmem
    rw [dif_pos hI, dif_pos hJ₀] at h
    exact h
  obtain ⟨M', hM'prim, hM'span, hM'bound⟩ := hmin J₀ hJ₀ hmax
  exact ⟨M', J₀, hJ₀, hM'prim, hM'span, hΔ₀, hM'bound, hred J₀ hJ₀ hΔ₀⟩

/-- Transfer to the `G_a × H'` alternative (case A) of `multiplicity_prop`. -/
lemma ze_good_true {N r : ℕ} (D : ZEData N r) (ρ : ℕ) (M : Fin ρ → Fin N → ℤ)
    (hρ1 : 1 ≤ ρ) (hρN : ρ ≤ N) (hM : PrimSys M) (hρr : ρ < r)
    (hBM : (fun i => (D.B i : ℚ)) ∈ Submodule.span ℚ (Set.range fun j i => (M j i : ℚ)))
    (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (hmin : ∀ (J₀ : Finset (Fin N)) (hJ₀ : J₀.card = ρ),
      (∀ (I : Finset (Fin N)) (hI : I.card = ρ),
        |(minorJ M I hI : ℝ)| * ∏ i ∈ I, a i ≤ |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i) →
      ∃ M' : Fin ρ → Fin N → ℤ, PrimSys M' ∧
        Submodule.span ℤ (Set.range M') = Submodule.span ℤ (Set.range M) ∧
        (∏ j, ∑ i, a i * |(M' j i : ℝ)|) ≤
          (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * (N : ℝ) ^ ρ *
            |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i)
    (hred : ∀ (I : Finset (Fin N)) (hI : I.card = ρ), minorJ M I hI ≠ 0 →
      (((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ)) *
        |(minorJ M I hI : ℝ)| ≤
      ((N + 1).descFactorial ρ : ℝ) * ∏ i ∈ I, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) :
    ∃ M' : Fin ρ → Fin N → ℤ, PrimSys M' ∧
      (fun i => (D.B i : ℚ)) ∈ Submodule.span ℚ (Set.range fun j i => (M' j i : ℚ)) ∧
      ∃ J : Finset (Fin N), J.card = ρ ∧
        (∏ j, ∑ i, a i * |(M' j i : ℝ)|) * ((D.Sq (ρ - 1) : ℝ) + 1) *
            ((D.Tq (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ) ≤
          constA r ρ * ∏ i ∈ J, (a i * D.δ i.succ) := by
  obtain ⟨M', J₀, hJ₀, hM'prim, hM'span, hΔ₀, hM'bound, hred₀⟩ :=
    exists_maximiser D ρ M hρ1 hρN hM a ha hmin hred
  have hBspan : (fun i => (D.B i : ℚ)) ∈
      Submodule.span ℚ (Set.range fun j i => (M' j i : ℚ)) := by
    have h1 : D.B ∈ Submodule.span ℤ (Set.range M) := int_mem_span_of_mem_span_rat hM hBM
    have h2 : D.B ∈ Submodule.span ℤ (Set.range M') := by rw [hM'span]; exact h1
    exact cast_mem_span_rat M' h2
  refine ⟨M', hM'prim, hBspan, J₀, hJ₀, ?_⟩
  set Pb : ℝ := ∏ j, ∑ i, a i * |(M' j i : ℝ)| with hPb
  set A : ℝ := ((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ)
    with hA
  set Dlt : ℝ := |(minorJ M J₀ hJ₀ : ℝ)| with hDltv
  set Pa : ℝ := ∏ i ∈ J₀, a i with hPa
  set Pd : ℝ := ∏ i ∈ J₀, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) with hPd
  set C2N : ℝ := (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * (N : ℝ) ^ ρ with hC2N
  set C2R : ℝ := (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * (r : ℝ) ^ ρ with hC2R
  set dN : ℝ := ((N + 1).descFactorial ρ : ℝ) with hdN
  set dR : ℝ := ((r + 1).descFactorial ρ : ℝ) with hdR
  have hPann : 0 ≤ Pa := by rw [hPa]; exact Finset.prod_nonneg fun i _ => (ha i).le
  have hPdnn : 0 ≤ Pd := by rw [hPd]; exact Finset.prod_nonneg fun i _ => by positivity
  have hC2Nnn : 0 ≤ C2N := by rw [hC2N]; positivity
  have hDltnn : 0 ≤ Dlt := by rw [hDltv]; positivity
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  have h_iii : C2N * dN ≤ C2R * dR := by
    have hNrr : N ≤ r := D.hNr
    have hpp : (N : ℝ) ^ ρ ≤ (r : ℝ) ^ ρ :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hNrr) ρ
    have hdesc : dN ≤ dR := by
      rw [hdN, hdR]
      exact_mod_cast Nat.descFactorial_le ρ (by omega : N + 1 ≤ r + 1)
    have hdNnn : 0 ≤ dN := by rw [hdN]; positivity
    have h1 : (N : ℝ) ^ ρ * dN ≤ (r : ℝ) ^ ρ * dR :=
      le_trans (mul_le_mul_of_nonneg_rightℝ hpp hdNnn)
        (mul_le_mul_of_nonneg_leftℝ hdesc (by positivity))
    calc C2N * dN = (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 *
          ((N : ℝ) ^ ρ * dN) := by rw [hC2N]; ring
      _ ≤ (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * ((r : ℝ) ^ ρ * dR) :=
          mul_le_mul_of_nonneg_leftℝ h1 (by positivity)
      _ = C2R * dR := by rw [hC2R]; ring
  have h_main : Pb * A ≤ (C2R * dR) * (Pa * Pd) := by
    have h_i : Pb ≤ C2N * Dlt * Pa := by rw [hPb, hC2N, hDltv, hPa]; exact hM'bound
    have h_ii : A * Dlt ≤ dN * Pd := by rw [hA, hDltv, hdN, hPd]; exact hred₀
    calc Pb * A ≤ (C2N * Dlt * Pa) * A := mul_le_mul_of_nonneg_rightℝ h_i hAnn
      _ = (C2N * Pa) * (A * Dlt) := by ring
      _ ≤ (C2N * Pa) * (dN * Pd) := mul_le_mul_of_nonneg_leftℝ h_ii (mul_nonneg hC2Nnn hPann)
      _ = (C2N * dN) * (Pa * Pd) := by ring
      _ ≤ (C2R * dR) * (Pa * Pd) := mul_le_mul_of_nonneg_rightℝ h_iii (mul_nonneg hPann hPdnn)
  have h_prod : Pa * Pd ≤ ∏ i ∈ J₀, (a i * D.δ i.succ) := by
    rw [hPa, hPd, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ ?_ ?_
    · intro i _
      exact mul_nonneg (ha i).le (by exact_mod_cast Nat.zero_le _)
    · intro i _
      exact mul_le_mul_of_nonneg_leftℝ (Nat.floor_le (D.hδnn i.succ)) (ha i).le
  calc (∏ j, ∑ i, a i * |(M' j i : ℝ)|) * ((D.Sq (ρ - 1) : ℝ) + 1) *
        ((D.Tq (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ) = Pb * A := by rw [hPb, hA]; ring
    _ ≤ (C2R * dR) * (Pa * Pd) := h_main
    _ = constA r ρ * (Pa * Pd) := by rw [hC2R, hdR, constA]
    _ ≤ constA r ρ * ∏ i ∈ J₀, (a i * D.δ i.succ) :=
        mul_le_mul_of_nonneg_leftℝ h_prod (constA_nonneg r ρ)

/-- Transfer to the `0 × H'` alternative (case B) of `multiplicity_prop`. -/
lemma ze_good_false {N r : ℕ} (D : ZEData N r) (ρ : ℕ) (M : Fin ρ → Fin N → ℤ)
    (hρ1 : 1 ≤ ρ) (hρN : ρ ≤ N) (hM : PrimSys M) (hρr : ρ < r)
    (hBM : (fun i => (D.B i : ℚ)) ∈ Submodule.span ℚ (Set.range fun j i => (M j i : ℚ)))
    (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (hmin : ∀ (J₀ : Finset (Fin N)) (hJ₀ : J₀.card = ρ),
      (∀ (I : Finset (Fin N)) (hI : I.card = ρ),
        |(minorJ M I hI : ℝ)| * ∏ i ∈ I, a i ≤ |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i) →
      ∃ M' : Fin ρ → Fin N → ℤ, PrimSys M' ∧
        Submodule.span ℤ (Set.range M') = Submodule.span ℤ (Set.range M) ∧
        (∏ j, ∑ i, a i * |(M' j i : ℝ)|) ≤
          (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * (N : ℝ) ^ ρ *
            |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i)
    (hred : ∀ (I : Finset (Fin N)) (hI : I.card = ρ), minorJ M I hI ≠ 0 →
      (((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + ρ).choose ρ : ℝ)) * |(minorJ M I hI : ℝ)| ≤
      ((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
        ∏ i ∈ I, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) :
    ∃ M' : Fin ρ → Fin N → ℤ, PrimSys M' ∧
      (fun i => (D.B i : ℚ)) ∈ Submodule.span ℚ (Set.range fun j i => (M' j i : ℚ)) ∧
      ∃ J : Finset (Fin N), J.card = ρ ∧
        (∏ j, ∑ i, a i * |(M' j i : ℝ)|) * ((D.Sq ρ : ℝ) + 1) *
            ((D.Tq ρ + ρ).choose ρ : ℝ) ≤
          constB r ρ * D.δ 0 * ∏ i ∈ J, (a i * D.δ i.succ) := by
  classical
  have hNr' : N ≤ r := D.hNr
  have hNr' : N ≤ r := D.hNr
  have hne : ((Finset.univ : Finset (Fin N)).powersetCard ρ).Nonempty := by
    refine ⟨Finset.map ⟨fun i : Fin ρ => (⟨i.1, by have := i.2; omega⟩ : Fin N),
      fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩
      (Finset.univ : Finset (Fin ρ)), ?_⟩
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by simp⟩
  obtain ⟨J₀, hJ₀mem, hJ₀max⟩ := Finset.exists_max_image
    ((Finset.univ : Finset (Fin N)).powersetCard ρ)
    (fun I => if h : I.card = ρ then |(minorJ M I h : ℝ)| * ∏ i ∈ I, a i else 0) hne
  have hJ₀ : J₀.card = ρ := (Finset.mem_powersetCard.mp hJ₀mem).2
  obtain ⟨J₁, hJ₁, hΔ₁⟩ := exists_minorJ_ne_zero M hM.1
  have hmem₁ : J₁ ∈ (Finset.univ : Finset (Fin N)).powersetCard ρ :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ J₁, hJ₁⟩
  have hmax₁ := hJ₀max J₁ hmem₁
  have hpos₁ : 0 < |(minorJ M J₁ hJ₁ : ℝ)| * ∏ i ∈ J₁, a i :=
    mul_pos (abs_pos.mpr (fun h => hΔ₁ (by exact_mod_cast h)))
      (Finset.prod_pos fun i _ => ha i)
  have hpos₀ : 0 < |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i := by
    have h := hmax₁
    rw [dif_pos hJ₁, dif_pos hJ₀] at h
    exact lt_of_lt_of_le hpos₁ h
  have hΔ₀ : minorJ M J₀ hJ₀ ≠ 0 := by
    intro h0
    rw [h0] at hpos₀
    simp at hpos₀
  have hmax : ∀ (I : Finset (Fin N)) (hI : I.card = ρ),
      |(minorJ M I hI : ℝ)| * ∏ i ∈ I, a i ≤ |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i := by
    intro I hI
    have hmem : I ∈ (Finset.univ : Finset (Fin N)).powersetCard ρ :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ I, hI⟩
    have h := hJ₀max I hmem
    rw [dif_pos hI, dif_pos hJ₀] at h
    exact h
  obtain ⟨M', hM'prim, hM'span, hM'bound⟩ := hmin J₀ hJ₀ hmax
  have hBspan : (fun i => (D.B i : ℚ)) ∈
      Submodule.span ℚ (Set.range fun j i => (M' j i : ℚ)) := by
    have h1 : D.B ∈ Submodule.span ℤ (Set.range M) := int_mem_span_of_mem_span_rat hM hBM
    have h2 : D.B ∈ Submodule.span ℤ (Set.range M') := by rw [hM'span]; exact h1
    exact cast_mem_span_rat M' h2
  refine ⟨M', hM'prim, hBspan, J₀, hJ₀, ?_⟩
  have hred₀ := hred J₀ hJ₀ hΔ₀
  set Pb : ℝ := ∏ j, ∑ i, a i * |(M' j i : ℝ)| with hPb
  set A : ℝ := ((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + ρ).choose ρ : ℝ) with hA
  set Dlt : ℝ := |(minorJ M J₀ hJ₀ : ℝ)| with hDltv
  set Pa : ℝ := ∏ i ∈ J₀, a i with hPa
  set Pd : ℝ := ∏ i ∈ J₀, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) with hPd
  set C2N : ℝ := (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * (N : ℝ) ^ ρ with hC2N
  set C2R : ℝ := (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * (r : ℝ) ^ ρ with hC2R
  set dN : ℝ := ((N + 1).descFactorial (ρ + 1) : ℝ) with hdN
  set dR : ℝ := ((r + 1).descFactorial (ρ + 1) : ℝ) with hdR
  have hPann : 0 ≤ Pa := by rw [hPa]; exact Finset.prod_nonneg fun i _ => (ha i).le
  have hPdnn : 0 ≤ Pd := by rw [hPd]; exact Finset.prod_nonneg fun i _ => by positivity
  have hC2Nnn : 0 ≤ C2N := by rw [hC2N]; positivity
  set D0 : ℝ := ((⌊D.δ 0⌋₊ : ℕ) : ℝ) with hD0
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  have hD0le : D0 ≤ D.δ 0 := by rw [hD0]; exact Nat.floor_le (D.hδnn 0)
  have h_iii : C2N * dN ≤ C2R * dR := by
    have hNrr : N ≤ r := D.hNr
    have hpp : (N : ℝ) ^ ρ ≤ (r : ℝ) ^ ρ :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hNrr) ρ
    have hdesc : dN ≤ dR := by
      rw [hdN, hdR]
      exact_mod_cast Nat.descFactorial_le (ρ + 1) (by omega : N + 1 ≤ r + 1)
    have hdNnn : 0 ≤ dN := by rw [hdN]; positivity
    have h1 : (N : ℝ) ^ ρ * dN ≤ (r : ℝ) ^ ρ * dR :=
      le_trans (mul_le_mul_of_nonneg_rightℝ hpp hdNnn)
        (mul_le_mul_of_nonneg_leftℝ hdesc (by positivity))
    calc C2N * dN = (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 *
          ((N : ℝ) ^ ρ * dN) := by rw [hC2N]; ring
      _ ≤ (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * ((r : ℝ) ^ ρ * dR) :=
          mul_le_mul_of_nonneg_leftℝ h1 (by positivity)
      _ = C2R * dR := by rw [hC2R]; ring
  have h_main : Pb * A ≤ (C2R * dR * D.δ 0) * (Pa * Pd) := by
    have h_i : Pb ≤ C2N * Dlt * Pa := by rw [hPb, hC2N, hDltv, hPa]; exact hM'bound
    have h_ii : A * Dlt ≤ dN * D0 * Pd := by rw [hA, hDltv, hdN, hD0, hPd]; exact hred₀
    calc Pb * A ≤ (C2N * Dlt * Pa) * A := mul_le_mul_of_nonneg_rightℝ h_i hAnn
      _ = (C2N * Pa) * (A * Dlt) := by ring
      _ ≤ (C2N * Pa) * (dN * D0 * Pd) := mul_le_mul_of_nonneg_leftℝ h_ii (mul_nonneg hC2Nnn hPann)
      _ = (C2N * dN) * D0 * (Pa * Pd) := by ring
      _ ≤ (C2R * dR) * D.δ 0 * (Pa * Pd) :=
          mul_le_mul_of_nonneg_rightℝ
            (le_trans (mul_le_mul_of_nonneg_rightℝ h_iii (by rw [hD0]; positivity))
              (mul_le_mul_of_nonneg_leftℝ hD0le (by positivity))) (by positivity)
      _ = (C2R * dR * D.δ 0) * (Pa * Pd) := by ring
  have h_prod : Pa * Pd ≤ ∏ i ∈ J₀, (a i * D.δ i.succ) := by
    rw [hPa, hPd, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ ?_ ?_
    · intro i _
      exact mul_nonneg (ha i).le (by exact_mod_cast Nat.zero_le _)
    · intro i _
      exact mul_le_mul_of_nonneg_leftℝ (Nat.floor_le (D.hδnn i.succ)) (ha i).le
  calc (∏ j, ∑ i, a i * |(M' j i : ℝ)|) * ((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + ρ).choose ρ : ℝ)
      = Pb * A := by rw [hPb, hA]; ring
    _ ≤ (C2R * dR * D.δ 0) * (Pa * Pd) := h_main
    _ = constB r ρ * D.δ 0 * (Pa * Pd) := by rw [hC2R, hdR, constB]
    _ ≤ constB r ρ * D.δ 0 * ∏ i ∈ J₀, (a i * D.δ i.succ) :=
        mul_le_mul_of_nonneg_leftℝ h_prod (mul_nonneg (constB_nonneg r ρ) (by linarith [D.hδ0]))

/-! ## The indicator vectors used in the exclusion table -/

/-- The indicator of the columns `J` among the torus coordinates (zero at the `G_a` coordinate). -/
def indT {N : ℕ} (J : Finset (Fin N)) : Fin (N + 1) → ℕ :=
  Fin.cases 0 fun j => if j ∈ J then 1 else 0

/-- The indicator of `J` together with the `G_a` coordinate. -/
def indT0 {N : ℕ} (J : Finset (Fin N)) : Fin (N + 1) → ℕ :=
  Fin.cases 1 fun j => if j ∈ J then 1 else 0

lemma indT_le_one {N : ℕ} (J : Finset (Fin N)) (i : Fin (N + 1)) : indT J i ≤ 1 := by
  induction i using Fin.cases with
  | zero => simp [indT]
  | succ j => simp only [indT, Fin.cases_succ]; split <;> omega

lemma indT0_le_one {N : ℕ} (J : Finset (Fin N)) (i : Fin (N + 1)) : indT0 J i ≤ 1 := by
  induction i using Fin.cases with
  | zero => simp [indT0]
  | succ j => simp only [indT0, Fin.cases_succ]; split <;> omega

lemma sum_indT {N : ℕ} (J : Finset (Fin N)) : ∑ i, indT J i = J.card := by
  rw [Fin.sum_univ_succ]
  simp only [indT, Fin.cases_zero, Fin.cases_succ, zero_add]
  have h1 : (∑ j : Fin N, (if j ∈ J then (1 : ℕ) else 0)) = J.card := by
    rw [← Finset.card_filter]
    congr 1
    ext j
    simp
  rw [h1]

lemma sum_indT0 {N : ℕ} (J : Finset (Fin N)) : ∑ i, indT0 J i = J.card + 1 := by
  rw [Fin.sum_univ_succ]
  simp only [indT0, Fin.cases_zero, Fin.cases_succ]
  have h1 : (∑ j : Fin N, (if j ∈ J then (1 : ℕ) else 0)) = J.card := by
    rw [← Finset.card_filter]
    congr 1
    ext j
    simp
  rw [h1]
  omega

lemma prod_delta_indT {N : ℕ} (δ : Fin (N + 1) → ℝ) (J : Finset (Fin N)) :
    ∏ i, δ i ^ indT J i = ∏ i ∈ J, δ i.succ := by
  have hpow : ∀ j : Fin N, δ j.succ ^ indT J j.succ = (if j ∈ J then δ j.succ else 1) := by
    intro j
    by_cases h : j ∈ J
    · simp only [indT, Fin.cases_succ, if_pos h, pow_one]
    · simp only [indT, Fin.cases_succ, if_neg h, pow_zero]
  rw [Fin.prod_univ_succ]
  rw [show indT J 0 = 0 from rfl]
  simp only [pow_zero, one_mul]
  rw [show (∏ j : Fin N, δ j.succ ^ indT J j.succ) =
      (∏ j : Fin N, if j ∈ J then δ j.succ else 1) from
    Finset.prod_congr rfl fun j _ => hpow j]
  exact Finset.prod_ite_mem_eq J (fun j : Fin N => δ j.succ)

lemma prod_delta_indT0 {N : ℕ} (δ : Fin (N + 1) → ℝ) (J : Finset (Fin N)) :
    ∏ i, δ i ^ indT0 J i = δ 0 * ∏ i ∈ J, δ i.succ := by
  have hpow : ∀ j : Fin N, δ j.succ ^ indT0 J j.succ = (if j ∈ J then δ j.succ else 1) := by
    intro j
    by_cases h : j ∈ J
    · simp only [indT0, Fin.cases_succ, if_pos h, pow_one]
    · simp only [indT0, Fin.cases_succ, if_neg h, pow_zero]
  rw [Fin.prod_univ_succ]
  rw [show indT0 J 0 = 1 from rfl]
  simp only [pow_one]
  rw [show (∏ j : Fin N, δ j.succ ^ indT0 J j.succ) =
      (∏ j : Fin N, if j ∈ J then δ j.succ else 1) from
    Finset.prod_congr rfl fun j _ => hpow j]
  rw [Finset.prod_ite_mem_eq J (fun j : Fin N => δ j.succ)]

/-! ## The exclusion table -/

/-- **Transversal exclusion, `ε = true`**: if the zero estimate returns `ℓ = ρ = k` with `ρ ≥ 2`,
its inequality contradicts (E1) at `m = ρ-1` with `e` the indicator of `J`. -/
lemma ze_bad_true {N r : ℕ} (D : ZEData N r) (ρ : ℕ) (M : Fin ρ → Fin N → ℤ) (m L : ℕ)
    (hρN : ρ ≤ N) (hM : PrimSys M) (hm : m + 1 ≤ ρ) (hρ2 : 2 ≤ ρ) (hL : L = ρ)
    (hcard : D.Sq m + 1 ≤ cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq m))
    (hineq : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
      (((D.Tq m + L).choose L : ℕ) : ℝ) *
          (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) *
        ((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
        ((⌊D.δ 0⌋₊ : ℕ) : ℝ) * ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) ≤
        ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ)) : False := by
  classical
  have hNr' : N ≤ r := D.hNr
  have hρ1 : 1 ≤ ρ := by omega
  obtain ⟨J, hJ, hΔ⟩ := exists_minorJ_ne_zero M hM.1
  have hred := ze_cancel_true D ρ (ρ - 1) ρ M m L hL (by omega) (by omega) hρN hcard hineq J hJ hΔ
  have hΔ1 := one_le_abs_minorJ hΔ
  have hA : (0 : ℝ) ≤ ((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + ρ).choose ρ : ℝ) := by
    positivity
  have hle : ((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + ρ).choose ρ : ℝ) ≤
      ((N + 1).descFactorial ρ : ℝ) * ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by
    calc ((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + ρ).choose ρ : ℝ)
        = (((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + ρ).choose ρ : ℝ)) * 1 := by ring
      _ ≤ (((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + ρ).choose ρ : ℝ)) *
            |(minorJ M J hJ : ℝ)| := mul_le_mul_of_nonneg_leftℝ hΔ1 hA
      _ ≤ ((N + 1).descFactorial ρ : ℝ) *
            ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := hred
  have hdesc : ((N + 1).descFactorial ρ : ℝ) ≤ ((r + 1).descFactorial ρ : ℝ) :=
    by exact_mod_cast Nat.descFactorial_le ρ (by omega : N + 1 ≤ r + 1)
  have hprodle : ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) ≤ ∏ i ∈ J, D.δ i.succ :=
    Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => Nat.floor_le (D.hδnn i.succ))
  have hE1 : ((r + 1).descFactorial ρ : ℝ) * ∏ i ∈ J, D.δ i.succ <
      ((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + ρ).choose ρ : ℝ) := by
    have h := D.hE1 (ρ - 1) (by omega) (indT J) (indT_le_one J) (by rw [sum_indT]; omega)
    have hT : (D.Tq (ρ - 1) + (ρ - 1) + 1) = (D.Tq (ρ - 1) + ρ) := by omega
    have hρ1' : ρ - 1 + 1 = ρ := by omega
    rw [prod_delta_indT, hT, hρ1'] at h
    exact h
  have hlt : ((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + ρ).choose ρ : ℝ) <
      ((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + ρ).choose ρ : ℝ) :=
    calc _ ≤ ((N + 1).descFactorial ρ : ℝ) *
          ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := hle
      _ ≤ ((r + 1).descFactorial ρ : ℝ) * ∏ i ∈ J, D.δ i.succ :=
          le_trans (mul_le_mul_of_nonneg_rightℝ hdesc
              (Finset.prod_nonneg fun i _ => by positivity))
            (mul_le_mul_of_nonneg_leftℝ hprodle (by positivity))
      _ < _ := hE1
  exact absurd hlt (lt_irrefl _)

/-- **Transversal exclusion, `ε = true`, `ρ = 1`**: here the classes may collide, so only
`cardMod ≥ 1` is available; (E0) gives the contradiction. -/
lemma ze_bad_true_one {N r : ℕ} (D : ZEData N r) (M : Fin 1 → Fin N → ℤ) (m L : ℕ)
    (hM : PrimSys M) (hm : m + 1 ≤ 1) (hL : L = 1)
    (hineq : ∀ (J : Finset (Fin N)) (hJ : J.card = 1), minorJ M J hJ ≠ 0 →
      (((D.Tq m + L).choose L : ℕ) : ℝ) *
          (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) *
        ((N + 1 - 1).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
        ((⌊D.δ 0⌋₊ : ℕ) : ℝ) * ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) ≤
        ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ)) : False := by
  classical
  have hNr' : N ≤ r := D.hNr
  obtain ⟨J, hJ, hΔ⟩ := exists_minorJ_ne_zero M hM.1
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hJ
  have hm0 : m = 0 := by omega
  subst hm0
  have hze := hineq {j} rfl hΔ
  rw [hL] at hze
  rw [show N + 1 - 1 = N from by omega] at hze
  simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] at hze
  have hΔ1 := one_le_abs_minorJ hΔ
  have hcard1 : (1 : ℝ) ≤ (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq 0) : ℝ) := by
    have h := one_le_cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq 0)
    exact_mod_cast h
  have hNpos : (0 : ℝ) < ((N).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos N
  have hD0pos : (0 : ℝ) < ((⌊D.δ 0⌋₊ : ℕ) : ℝ) := by
    have h : 1 ≤ ⌊D.δ 0⌋₊ := D.hδ1 0
    exact_mod_cast (by omega : (0 : ℕ) < ⌊D.δ 0⌋₊)
  have hPCpos : (0 : ℝ) < ∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by
    apply Finset.prod_pos
    intro i _
    have h : 1 ≤ ⌊D.δ i.succ⌋₊ := D.hδ1 i.succ
    exact_mod_cast (by omega : (0 : ℕ) < ⌊D.δ i.succ⌋₊)
  have hprod : ∏ i : Fin (N + 1), ((⌊D.δ i⌋₊ : ℕ) : ℝ) =
      ((⌊D.δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ ({j} : Finset (Fin N)), ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) *
        (∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) := by
    rw [Fin.prod_univ_succ, prod_split (fun i : Fin N => ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) {j}]
    ring
  have hfact : ((N + 1).factorial : ℝ) = ((N).factorial : ℝ) * ((N : ℝ) + 1) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hprod1 : (∏ i ∈ ({j} : Finset (Fin N)), ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) =
      ((⌊D.δ j.succ⌋₊ : ℕ) : ℝ) :=
      Finset.prod_singleton (fun i : Fin N => ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) j
  rw [hprod, hprod1, hfact] at hze
  -- hze : (Tq 0 + 1) * cardMod * N! * |Δ| * Dd0 * PC ≤ (N! * (N+1)) * (Dd0 * Dd_{j+1} * PC)
  have hdiv : (0 : ℝ) < (N.factorial : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
      (∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) := by
    refine mul_pos (mul_pos (by exact_mod_cast Nat.factorial_pos N) ?_) hPCpos
    exact_mod_cast (by have h := D.hδ1 0; omega : (0 : ℕ) < ⌊D.δ 0⌋₊)
  have hmul : (D.Tq 0 : ℝ) + 1 ≤ ((D.Tq 0 : ℝ) + 1) *
      (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq 0) : ℝ) *
        |(minorJ M {j} rfl : ℝ)| := by
    have hCM1 : (1 : ℝ) ≤ (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq 0) : ℝ) := by
      exact_mod_cast hcard1
    have hmul1 : (D.Tq 0 : ℝ) + 1 ≤ ((D.Tq 0 : ℝ) + 1) *
        (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq 0) : ℝ) := by
      have h := mul_le_mul_of_nonneg_leftℝ hCM1
        (show (0 : ℝ) ≤ (D.Tq 0 : ℝ) + 1 by positivity)
      simpa using h
    have hmul2 : ((D.Tq 0 : ℝ) + 1) *
          (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq 0) : ℝ) ≤
        ((D.Tq 0 : ℝ) + 1) *
          (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq 0) : ℝ) *
            |(minorJ M {j} rfl : ℝ)| := by
      have h := mul_le_mul_of_nonneg_leftℝ hΔ1
        (show (0 : ℝ) ≤ ((D.Tq 0 : ℝ) + 1) *
          (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq 0) : ℝ) by positivity)
      simpa [mul_assoc] using h
    exact le_trans hmul1 hmul2
  have hbig : ((D.Tq 0 : ℝ) + 1) * ((N.factorial : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
        (∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) ≤
      (((D.Tq 0 : ℝ) + 1) * (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq 0) : ℝ) *
        |(minorJ M {j} rfl : ℝ)|) * ((N.factorial : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
        (∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) :=
    mul_le_mul_of_nonneg_rightℝ hmul (le_of_lt hdiv)
  have h1 : (D.Tq 0 : ℝ) + 1 ≤ ((N : ℝ) + 1) * ((⌊D.δ j.succ⌋₊ : ℕ) : ℝ) := by
    refine le_of_mul_le_mul_right ?_ hdiv
    refine le_trans hbig ?_
    calc ((D.Tq 0 : ℝ) + 1) * (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq 0) : ℝ) *
          |(minorJ M {j} rfl : ℝ)| * ((N.factorial : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
          (∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))
        = ((D.Tq 0 : ℝ) + 1) * (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq 0) : ℝ) *
            (N.factorial : ℝ) * |(minorJ M {j} rfl : ℝ)| * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
            (∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) := by ring
      _ ≤ (N.factorial : ℝ) * ((N : ℝ) + 1) *
            (((⌊D.δ 0⌋₊ : ℕ) : ℝ) * ((⌊D.δ j.succ⌋₊ : ℕ) : ℝ) *
              (∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by
          simpa only [mul_assoc] using hze
      _ = (((N : ℝ) + 1) * ((⌊D.δ j.succ⌋₊ : ℕ) : ℝ)) *
            ((N.factorial : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
              (∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by ring
  have h2 : ((N : ℝ) + 1) * ((⌊D.δ j.succ⌋₊ : ℕ) : ℝ) ≤
      ((r : ℝ) + 1) * ((⌊D.δ j.succ⌋₊ : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_rightℝ (by exact_mod_cast (by omega : N + 1 ≤ r + 1)) (by positivity)
  have h3 : ((r : ℝ) + 1) * ((⌊D.δ j.succ⌋₊ : ℕ) : ℝ) ≤ ((r : ℝ) + 1) * D.δ j.succ :=
    mul_le_mul_of_nonneg_leftℝ (Nat.floor_le (D.hδnn j.succ)) (by positivity)
  linarith [h1, h2, h3, D.hE0 j]

/-- **`G_a × 1` exclusion (`ε = true`, `ρ = r`, no collisions)**: contradicts (E3). -/
lemma ze_rho_eq_r_true {N r : ℕ} (D : ZEData N r) (ρ : ℕ) (M : Fin ρ → Fin N → ℤ) (m L : ℕ)
    (hρN : ρ ≤ N) (hρr : ρ = r) (hM : PrimSys M) (hm : m + 1 ≤ ρ) (hL : L = ρ - 1)
    (hcard : D.Sq m + 1 ≤ cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq m))
    (hineq : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
      (((D.Tq m + L).choose L : ℕ) : ℝ) *
          (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) *
        ((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
        ((⌊D.δ 0⌋₊ : ℕ) : ℝ) * ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) ≤
        ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ)) : False := by
  classical
  have hNr' : N ≤ r := D.hNr
  have hρ1 : 1 ≤ ρ := by omega
  have hNr : N = r := by omega
  obtain ⟨J, hJ, hΔ⟩ := exists_minorJ_ne_zero M hM.1
  have hJu : J = Finset.univ := Finset.eq_univ_of_card J (by rw [hJ]; simp only [Fintype.card_fin]; omega)
  have hred := ze_cancel_true D ρ (ρ - 1) (ρ - 1) M m L hL (by omega) (by omega) hρN hcard hineq J hJ hΔ
  have hΔ1 := one_le_abs_minorJ hΔ
  have hA : (0 : ℝ) ≤ ((D.Sq (ρ - 1) : ℝ) + 1) *
      ((D.Tq (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ) := by positivity
  have hds : ((N + 1).descFactorial ρ : ℝ) = ((N + 1).factorial : ℝ) := by
    have h := factorial_eq_factorial_mul_descFactorial (n := N + 1) (k := ρ) (by omega)
    have h1 : N + 1 - ρ = 1 := by omega
    rw [h1] at h
    have h3 : ((N + 1).factorial : ℝ) = 1 * ((N + 1).descFactorial ρ : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
    simpa using h3.symm
  have hPJ : ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) =
      ∏ i : Fin N, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by simp [hJu]
  have hle : ((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ) ≤
      ((N + 1).factorial : ℝ) * ∏ i : Fin N, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by
    calc ((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ)
        = (((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ)) * 1 :=
          by ring
      _ ≤ (((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ)) *
            |(minorJ M J hJ : ℝ)| := mul_le_mul_of_nonneg_leftℝ hΔ1 hA
      _ ≤ ((N + 1).descFactorial ρ : ℝ) * ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := hred
      _ = ((N + 1).factorial : ℝ) * ∏ i : Fin N, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by
          rw [hds, hPJ]
  have hE3 := D.hE3 hNr
  rw [show N - 1 = ρ - 1 from by omega] at hE3
  have hlt : ((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ) <
      ((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ) := by
    calc _ ≤ ((N + 1).factorial : ℝ) * ∏ i : Fin N, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := hle
      _ < _ := hE3
  exact absurd hlt (lt_irrefl _)

/-- **Transversal exclusion, `ε = false`, `ρ < r`**: contradicts (E1) at `m = ρ` with `e` the
indicator of `J` together with the `G_a` coordinate. -/
lemma ze_bad_false {N r : ℕ} (D : ZEData N r) (ρ : ℕ) (M : Fin ρ → Fin N → ℤ) (m L : ℕ)
    (hρN : ρ ≤ N) (hM : PrimSys M) (hm : m + 1 ≤ ρ + 1) (hρr : ρ < r) (hL : L = ρ + 1)
    (hcard : D.Sq m + 1 ≤ cardMod false M (fun i => Complex.exp (D.ℓ i)) (D.Sq m))
    (hineq : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
      (((D.Tq m + L).choose L : ℕ) : ℝ) *
          (cardMod false M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) *
        ((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
        1 * ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) ≤
        ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ)) : False := by
  classical
  have hNr' : N ≤ r := D.hNr
  obtain ⟨J, hJ, hΔ⟩ := exists_minorJ_ne_zero M hM.1
  have hred := ze_cancel_false D ρ ρ (ρ + 1) M m L hL (by omega) (by omega) hρN hcard hineq J hJ hΔ
  have hΔ1 := one_le_abs_minorJ hΔ
  have hA : (0 : ℝ) ≤ ((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + (ρ + 1)).choose (ρ + 1) : ℝ) := by
    positivity
  have hle : ((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + (ρ + 1)).choose (ρ + 1) : ℝ) ≤
      ((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
        ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by
    calc ((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + (ρ + 1)).choose (ρ + 1) : ℝ)
        = (((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + (ρ + 1)).choose (ρ + 1) : ℝ)) * 1 := by ring
      _ ≤ (((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + (ρ + 1)).choose (ρ + 1) : ℝ)) *
            |(minorJ M J hJ : ℝ)| := mul_le_mul_of_nonneg_leftℝ hΔ1 hA
      _ ≤ ((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
            ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := hred
  have hdesc : ((N + 1).descFactorial (ρ + 1) : ℝ) ≤ ((r + 1).descFactorial (ρ + 1) : ℝ) :=
    by exact_mod_cast Nat.descFactorial_le (ρ + 1) (by omega : N + 1 ≤ r + 1)
  have hD0le : ((⌊D.δ 0⌋₊ : ℕ) : ℝ) ≤ D.δ 0 := Nat.floor_le (D.hδnn 0)
  have hprodle : ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) ≤ ∏ i ∈ J, D.δ i.succ :=
    Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => Nat.floor_le (D.hδnn i.succ))
  have hE1 : ((r + 1).descFactorial (ρ + 1) : ℝ) * D.δ 0 * ∏ i ∈ J, D.δ i.succ <
      ((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + ρ + 1).choose (ρ + 1) : ℝ) := by
    have h := D.hE1 ρ hρr (indT0 J) (indT0_le_one J) (by rw [sum_indT0]; omega)
    simpa only [prod_delta_indT0, mul_assoc] using h
  have hlt : ((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + ρ + 1).choose (ρ + 1) : ℝ) <
      ((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + ρ + 1).choose (ρ + 1) : ℝ) := by
    have hCnn : (0 : ℝ) ≤ ((⌊D.δ 0⌋₊ : ℕ) : ℝ) := by positivity
    have hPN : (0 : ℝ) ≤ ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) :=
      Finset.prod_nonneg fun i _ => by positivity
    have hA'nn : (0 : ℝ) ≤ ((r + 1).descFactorial (ρ + 1) : ℝ) := by positivity
    have hD0pos : (0 : ℝ) < D.δ 0 := by linarith [D.hδ0]
    have hstep1 : ((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) ≤
        ((r + 1).descFactorial (ρ + 1) : ℝ) * D.δ 0 :=
      le_trans (mul_le_mul_of_nonneg_rightℝ hdesc hCnn)
        (mul_le_mul_of_nonneg_leftℝ hD0le hA'nn)
    calc ((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + ρ + 1).choose (ρ + 1) : ℝ)
        ≤ ((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
            ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := hle
      _ ≤ (((r + 1).descFactorial (ρ + 1) : ℝ) * D.δ 0) *
            ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_rightℝ hstep1 hPN
      _ ≤ (((r + 1).descFactorial (ρ + 1) : ℝ) * D.δ 0) * ∏ i ∈ J, D.δ i.succ :=
          mul_le_mul_of_nonneg_leftℝ hprodle (mul_nonneg hA'nn hD0pos.le)
      _ < _ := hE1
  exact absurd hlt (lt_irrefl _)

/-- **`0 × 1` exclusion (`ε = false`, `ρ = r`)**: contradicts (E2). -/
lemma ze_rho_eq_r_false {N r : ℕ} (D : ZEData N r) (ρ : ℕ) (M : Fin ρ → Fin N → ℤ) (m L : ℕ)
    (hρN : ρ ≤ N) (hρr : ρ = r) (hNr : N = r) (hm : m + 1 ≤ ρ + 1) (hM : PrimSys M)
    (hL : L = ρ ∨ L = ρ + 1)
    (hcard : D.Sq m + 1 ≤ cardMod false M (fun i => Complex.exp (D.ℓ i)) (D.Sq m))
    (hineq : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
      (((D.Tq m + L).choose L : ℕ) : ℝ) *
          (cardMod false M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) *
        ((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
        1 * ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) ≤
        ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ)) : False := by
  classical
  have hNr' : N ≤ r := D.hNr
  obtain ⟨J, hJ, hΔ⟩ := exists_minorJ_ne_zero M hM.1
  have hJu : J = Finset.univ := Finset.eq_univ_of_card J (by rw [hJ]; simp only [Fintype.card_fin]; omega)
  have hmN : m ≤ N := by omega
  have hred := ze_cancel_false D ρ ρ L M m L (by rfl) (by omega) (by omega) hρN hcard hineq J hJ hΔ
  -- hred : (Sq ρ + 1) * C(Tq ρ + L, L) * |Δ| ≤ descFactorial(ρ+1) * Dd0 * ∏_J Dd
  have hΔ1 := one_le_abs_minorJ hΔ
  have hA : (0 : ℝ) ≤ ((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + L).choose L : ℝ) := by positivity
  have hPJ : ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) =
      ∏ i : Fin N, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by simp [hJu]
  have hprod : ((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
      ∏ i : Fin N, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) =
      ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ) := by
    have h := factorial_eq_factorial_mul_descFactorial (n := N + 1) (k := ρ + 1) (by omega)
    have hfac : ((N + 1).factorial : ℝ) =
        ((N + 1 - (ρ + 1)).factorial : ℝ) * ((N + 1).descFactorial (ρ + 1) : ℝ) :=
      by exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
    have h1 : N + 1 - (ρ + 1) = 0 := by omega
    rw [h1] at hfac
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul] at hfac
    rw [hfac, Fin.prod_univ_succ]
    ring
  have hle : ((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + L).choose L : ℝ) ≤
      ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ) := by
    calc ((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + L).choose L : ℝ)
        = (((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + L).choose L : ℝ)) * 1 := by ring
      _ ≤ (((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + L).choose L : ℝ)) *
            |(minorJ M J hJ : ℝ)| := mul_le_mul_of_nonneg_leftℝ hΔ1 hA
      _ ≤ ((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
            ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := hred
      _ = ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ) := by rw [hPJ, hprod]
  have hE2 := D.hE2 hNr
  have hρN' : ρ = N := by omega
  have hcmp : ((D.Tq N + N).choose N : ℝ) ≤ ((D.Tq ρ + L).choose L : ℝ) := by
    rcases hL with hL | hL
    · rw [hL, hρN']
    · rw [hL, hρN']
      exact_mod_cast (choose_le_choose_of_lt (D.Tq N + N + 1) (D.Tq N + N) (N + 1)
        (by omega) (by omega))
  have hle' : ((D.Sq N : ℝ) + 1) * ((D.Tq ρ + L).choose L : ℝ) ≤
      ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ) := by
    simpa only [hρN'] using hle
  have hlt : ((D.Sq N : ℝ) + 1) * ((D.Tq N + N).choose N : ℝ) <
      ((D.Sq N : ℝ) + 1) * ((D.Tq N + N).choose N : ℝ) :=
    calc ((D.Sq N : ℝ) + 1) * ((D.Tq N + N).choose N : ℝ)
        ≤ ((D.Sq N : ℝ) + 1) * ((D.Tq ρ + L).choose L : ℝ) :=
          mul_le_mul_of_nonneg_leftℝ hcmp (by positivity)
      _ ≤ ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ) := hle'
      _ < ((D.Sq N : ℝ) + 1) * ((D.Tq N + N).choose N : ℝ) := hE2
  exact absurd hlt (lt_irrefl _)

/-! ## The engine -/

/-- **The engine of `multiplicity_prop`**: given the output of the zero estimate (a subgroup of
codimension `k = (if ε then 0 else 1) + ρ`, a step `m` and Philippon's inequality), the dichotomy
`L = ellW ∈ {k-1, k}` and the identification `L = k-1 → B ∈ ℚ𝒵`, together with the exclusion
conditions (E0)–(E3), the conclusion of `multiplicity_prop` follows. `hmin` is the interface to
`prim_basis_from_minors` (the Minkowski reduction of the maximising minor). -/
theorem ze_engine {N r : ℕ} (D : ZEData N r) (ε : Bool) (ρ : ℕ) (M : Fin ρ → Fin N → ℤ)
    (m L : ℕ) (hρN : ρ ≤ N) (hM : PrimSys M) (hε : ¬(ε = true ∧ ρ = 0))
    (hm : m + 1 ≤ (if ε then 0 else 1) + ρ)
    (hLdich : L = (if ε then 0 else 1) + ρ - 1 ∨ L = (if ε then 0 else 1) + ρ)
    (hLpos : ε = false → 1 ≤ L)
    (hGoodB : L = (if ε then 0 else 1) + ρ - 1 →
      (fun i => (D.B i : ℚ)) ∈ Submodule.span ℚ (Set.range fun j i => (M j i : ℚ)))
    (hmin : ∀ (a : Fin N → ℝ), (∀ i, 0 < a i) →
      ∀ (J₀ : Finset (Fin N)) (hJ₀ : J₀.card = ρ),
        (∀ (I : Finset (Fin N)) (hI : I.card = ρ),
          |(minorJ M I hI : ℝ)| * ∏ i ∈ I, a i ≤ |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i) →
        ∃ M' : Fin ρ → Fin N → ℤ, PrimSys M' ∧
          Submodule.span ℤ (Set.range M') = Submodule.span ℤ (Set.range M) ∧
          (∏ j, ∑ i, a i * |(M' j i : ℝ)|) ≤
            (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * (N : ℝ) ^ ρ *
              |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i)
    (hineq : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
      (((D.Tq m + L).choose L : ℕ) : ℝ) *
          (cardMod ε M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) *
        ((N + 1 - ((if ε then 0 else 1) + ρ)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
        (if ε then ((⌊D.δ 0⌋₊ : ℕ) : ℝ) else 1) *
          ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) ≤
        ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ)) :
    ∃ ρ' : ℕ, 1 ≤ ρ' ∧ ρ' < r ∧ ∀ a : Fin N → ℝ, (∀ i, 0 < a i) →
      ∃ M' : Fin ρ' → Fin N → ℤ, PrimSys M' ∧
        (fun i => (D.B i : ℚ)) ∈ Submodule.span ℚ (Set.range fun j i => (M' j i : ℚ)) ∧
        ∃ J : Finset (Fin N), J.card = ρ' ∧
          ((∏ j, ∑ i, a i * |(M' j i : ℝ)|) * ((D.Sq (ρ' - 1) : ℝ) + 1) *
                ((D.Tq (ρ' - 1) + (ρ' - 1)).choose (ρ' - 1) : ℝ) ≤
              constA r ρ' * ∏ i ∈ J, (a i * D.δ i.succ) ∨
            (∏ j, ∑ i, a i * |(M' j i : ℝ)|) * ((D.Sq ρ' : ℝ) + 1) *
                ((D.Tq ρ' + ρ').choose ρ' : ℝ) ≤
              constB r ρ' * D.δ 0 * ∏ i ∈ J, (a i * D.δ i.succ)) := by
  classical
  have hNr' : N ≤ r := D.hNr
  have h2r : 2 ≤ r := D.hr
  cases ε with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel_left] at hLdich hLpos hGoodB hineq
    have hmρ : m ≤ ρ := by
      have hm1 : m + 1 ≤ 1 + ρ := by simpa using hm
      omega
    have hineq' : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
        (((D.Tq m + L).choose L : ℕ) : ℝ) *
            (cardMod false M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) *
          ((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
          1 * ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) ≤
          ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ) := by
      intro J hJ hΔ
      have h := hineq J hJ hΔ
      have hk : N + 1 - (1 + ρ) = N + 1 - (ρ + 1) := by rw [Nat.add_comm 1 ρ]
      rw [hk] at h
      simpa only [mul_one] using h
    have hcardF : D.Sq m + 1 ≤ cardMod false M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) := by
      rw [cardMod_false]
    by_cases hgood : L = ρ
    · have hBM := hGoodB (by omega)
      have hρ1 : 1 ≤ ρ := by have h := hLpos trivial; omega
      by_cases hρr : ρ < r
      · have hred : ∀ (I : Finset (Fin N)) (hI : I.card = ρ), minorJ M I hI ≠ 0 →
            (((D.Sq ρ : ℝ) + 1) * ((D.Tq ρ + ρ).choose ρ : ℝ)) * |(minorJ M I hI : ℝ)| ≤
              ((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
                ∏ i ∈ I, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) :=
          fun I hI hΔI =>
            ze_cancel_false D ρ ρ ρ M m L hgood hmρ hρN hρN hcardF hineq' I hI hΔI
        exact ⟨ρ, hρ1, hρr, fun a ha => by
          obtain ⟨M', hP, hBs, J, hJc, hb⟩ :=
            ze_good_false D ρ M hρ1 hρN hM hρr hBM a ha (hmin a ha) hred
          exact ⟨M', hP, hBs, J, hJc, Or.inr hb⟩⟩
      · exact absurd (ze_rho_eq_r_false D ρ M m L hρN (by omega : ρ = r) (by omega : N = r)
          (by omega : m + 1 ≤ ρ + 1) hM (Or.inl hgood) hcardF hineq') (by simp)
    · have hLbad : L = ρ + 1 := by
        rcases hLdich with h | h
        · exact absurd h hgood
        · exact h.trans (Nat.add_comm 1 ρ)
      by_cases hρr : ρ < r
      · exact (ze_bad_false D ρ M m L hρN hM (by omega : m + 1 ≤ ρ + 1) hρr hLbad hcardF
          hineq').elim
      · exact (ze_rho_eq_r_false D ρ M m L hρN (by omega : ρ = r) (by omega : N = r)
          (by omega : m + 1 ≤ ρ + 1) hM (Or.inr hLbad) hcardF hineq').elim
  | true =>
    simp only [↓reduceIte, zero_add] at hLdich hGoodB hineq hm
    have hmρ : m ≤ ρ := by omega
    have hineq' : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
        (((D.Tq m + L).choose L : ℕ) : ℝ) *
            (cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) : ℝ) *
          ((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
          ((⌊D.δ 0⌋₊ : ℕ) : ℝ) * ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) ≤
          ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ) := by
      intro J hJ hΔ
      simpa using hineq J hJ hΔ
    have hρ1 : 1 ≤ ρ := by by_contra h; exact hε ⟨rfl, by omega⟩
    by_cases hρ2 : 2 ≤ ρ
    · have hcardT : D.Sq m + 1 ≤ cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) := by
        rw [cardMod_true_of_linearIndependent hρ2 M hM.1 (fun i => D.ℓ i) D.hℓ]
      by_cases hgood : L = ρ - 1
      · by_cases hρr : ρ < r
        · have hred : ∀ (I : Finset (Fin N)) (hI : I.card = ρ), minorJ M I hI ≠ 0 →
              (((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ)) *
                |(minorJ M I hI : ℝ)| ≤
                ((N + 1).descFactorial ρ : ℝ) * ∏ i ∈ I, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) :=
            fun I hI hΔI =>
              ze_cancel_true D ρ (ρ - 1) (ρ - 1) M m L hgood
                (by omega : m ≤ ρ - 1) (by omega : ρ - 1 ≤ N) hρN hcardT hineq' I hI hΔI
          have hBM := hGoodB hgood
          exact ⟨ρ, hρ1, hρr, fun a ha => by
            obtain ⟨M', hP, hBs, J, hJc, hb⟩ :=
              ze_good_true D ρ M hρ1 hρN hM hρr hBM a ha (hmin a ha) hred
            exact ⟨M', hP, hBs, J, hJc, Or.inl hb⟩⟩
        · exact absurd (ze_rho_eq_r_true D ρ M m L hρN (by omega : ρ = r) hM
            (by omega : m + 1 ≤ ρ) hgood hcardT hineq') (by simp)
      · have hLbad : L = ρ := by
          rcases hLdich with h | h
          · exact absurd h hgood
          · exact h
        exact (ze_bad_true D ρ M m L hρN hM (by omega : m + 1 ≤ ρ) hρ2 hLbad hcardT hineq').elim
    · have hρe : ρ = 1 := by omega
      subst hρe
      by_cases hgood : L = 1 - 1
      · have hBM := hGoodB hgood
        have hcardT1 : D.Sq m + 1 ≤ cardMod true M (fun i => Complex.exp (D.ℓ i)) (D.Sq m) := by
          refine le_of_eq ?_
          exact (cardMod_true_rank_one M hM D.B D.hB hBM (fun i => D.ℓ i) D.hℓ D.𝒮 D.hSpos
            (le_trans (by exact_mod_cast sq_le_sum D.Sq (by omega : m ≤ N)) D.hSsum) D.hΛ).symm
        have hρr : (1 : ℕ) < r := by omega
        have hred : ∀ (I : Finset (Fin N)) (hI : I.card = 1), minorJ M I hI ≠ 0 →
            (((D.Sq (1 - 1) : ℝ) + 1) * ((D.Tq (1 - 1) + (1 - 1)).choose (1 - 1) : ℝ)) *
              |(minorJ M I hI : ℝ)| ≤
              ((N + 1).descFactorial 1 : ℝ) * ∏ i ∈ I, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) :=
          fun I hI hΔI =>
            ze_cancel_true D 1 (1 - 1) (1 - 1) M m L hgood
              (by omega : m ≤ 1 - 1) (by omega : 1 - 1 ≤ N) hρN hcardT1 hineq' I hI hΔI
        exact ⟨1, le_refl 1, hρr, fun a ha => by
          obtain ⟨M', hP, hBs, J, hJc, hb⟩ :=
            ze_good_true D 1 M (le_refl 1) hρN hM hρr hBM a ha (hmin a ha) hred
          exact ⟨M', hP, hBs, J, hJc, Or.inl hb⟩⟩
      · have hLbad : L = 1 := by
          rcases hLdich with h | h
          · exact absurd h hgood
          · exact h
        exact (ze_bad_true_one D M m L hM (by omega : m + 1 ≤ 1) hLbad hineq').elim

end Work.BW