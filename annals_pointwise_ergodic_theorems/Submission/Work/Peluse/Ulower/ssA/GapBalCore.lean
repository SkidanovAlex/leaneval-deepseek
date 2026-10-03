import Mathlib
import Submission.Work.Peluse.Ulower.gap_localise
import Submission.Work.Peluse.Ulower.ss_u2_level
import Submission.Work.Peluse.Ulower.ss_u2_level_A
import Submission.Work.Peluse.Ulower.ssA.DegreeLowering

/-!
# `Work.Peluse.Ulower.gap_bal_core` --- the balanced chapter in the "many shift tuples" form

This file proves the bridge used by the localisation of the gap regime
(`Work.Peluse.Ulower.gap_local_block`, `NOTES_gap_extraction_SESSION3.md`).

## Mathematical content

The hypothesis `ManyShiftsHypDensity P s Ns N D f_0 f_1 delta gamma` is the "many shift tuples" form
of the `U^s`-information on the dual function `F_2 = dualFn N P f_0 f_1`: a `gamma`-fraction of the
shift tuples `sh : Fin (s-2) -> Z x Z` (entries in `arithIcc P.leadingCoeff D`) satisfies
`delta <= boxNormPow 2 (arithIcc P.leadingCoeff D) (symIcc (dSup P Ns N)) (iterDelta (s-2) sh F_2)`.
It is the conclusion of the peel `Work.Peluse.Ulower.gap_peel_many`.

The first ingredient is the **converse direction**, `ssManyShiftsLeUNormPow`: the peel identity
`boxNormPow_eq_peel_two` expresses the level-`s` box norm as the average of the level-two box norms
of the iterated differences, each of which is a *non-negative real*
(`BoxNorm.boxSumPow_eq_boxNormPow`); hence a `gamma`-fraction of tuples contributing at least
`delta` gives `gamma * delta <= uNormPow s (arithIcc P.leadingCoeff D) (symIcc (dSup P Ns N)) F_2`.
(The `iterDelta`/`iterDelta'` discrepancy is harmless: the two iterated differences differ pointwise
by a conjugation, and the level-two box norm is invariant under pointwise conjugation.)

The second ingredient is the standard balanced chapter, in the two forms in which it is consumed at
the *unbalanced* scale relation `N^d <= A * Ns`, `Ns <= A * N^d` (constants depending on `A`):

* `ssDegreeLoweringA` --- Peluse's Lemma 3.9 (the degree lowering `U^s => U^2`);
* `ss_u2_level_A` --- Peluse's Section 9 (`U^2 => progression average`).

Both are genuine chapters of the paper's proof, stated for the unbalanced instance; they are
delegated.  The final arithmetic: with `alpha := delta * gamma * (D/Ns)` the three estimates give
`progAvgSum N' q f_1 >= alpha^K * Ns / C`, `N' >= alpha^K * N / C` and `q <= C * alpha^{-K}`, which
is exactly the target's conclusion.

## Main results

* `ssBoxNormPowStarFn`, `ssIterDeltaEqIterDeltaOr`, `ssManyShiftsLeUNormPow`;
* `ssDegreeLoweringA`, `ss_u2_level_A` (delegated chapters);
* `ssGapBalCore`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-! ## Pointwise conjugation and the level-two box norm -/

/-- Pointwise conjugation of a function. -/
def ssStarFn (G : ℤ → ℂ) : ℤ → ℂ := fun x => star (G x)

lemma ssStarIterateStar (n : ℕ) (z : ℂ) :
    (star^[n]) (star z) = star ((star^[n]) z) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']

/-- The conjugate of a box sum is the box sum of the conjugate function. -/
lemma ssBoxSumPowStarFn (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (G : ℤ → ℂ) :
    Work.Peluse.boxSumPow t Q S (ssStarFn G) = star (Work.Peluse.boxSumPow t Q S G) := by
  simp only [Work.Peluse.boxSumPow, Work.Peluse.prodCubeSum_eq]
  have hA : star ((((S.card : ℂ))⁻¹ * ∏ i : Fin t, (((Q i).card : ℂ))⁻¹) *
      ∏ i : Fin t, (((Q i).card : ℂ))⁻¹)
      = ((((S.card : ℂ))⁻¹ * ∏ i : Fin t, (((Q i).card : ℂ))⁻¹) *
      ∏ i : Fin t, (((Q i).card : ℂ))⁻¹) := by
    simp
  have hE : star (∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ∑' x : ℤ, ∏ ω : Fin t → Bool,
            (star^[Work.Peluse.weight ω]) (G (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)))
      = ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ∑' x : ℤ, ∏ ω : Fin t → Bool,
            (star^[Work.Peluse.weight ω]) (ssStarFn G (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)) := by
    rw [star_sum]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [star_sum]
    refine Finset.sum_congr rfl (fun h' _ => ?_)
    rw [tsum_star]
    refine tsum_congr (fun x => ?_)
    rw [star_prod]
    refine Finset.prod_congr rfl (fun ω _ => ?_)
    rw [ssStarFn, ← ssStarIterateStar]
  rw [star_mul, hA, hE, mul_comm]

/-- The box-norm power is invariant under pointwise conjugation. -/
lemma ssBoxNormPowStarFn (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (G : ℤ → ℂ) :
    Work.Peluse.boxNormPow t Q S (ssStarFn G) = Work.Peluse.boxNormPow t Q S G := by
  rw [Work.Peluse.boxNormPow, Work.Peluse.boxNormPow, ssBoxSumPowStarFn, norm_star]

/-! ## `iterDelta` versus `iterDelta'` -/

/-- `iterDelta` and `iterDelta'` differ at most by a pointwise conjugation. -/
lemma ssIterDeltaEqIterDeltaOr : ∀ (k : ℕ) (sh : Fin k → ℤ × ℤ) (F : ℤ → ℂ),
    iterDelta k sh F = iterDelta' k sh F ∨ iterDelta k sh F = ssStarFn (iterDelta' k sh F) := by
  intro k
  induction k with
  | zero => intro sh F; left; rfl
  | succ k ih =>
      intro sh F
      rcases ih (fun i => sh i.succ) F with hcase | hcase
      · right
        rw [iterDelta_succ, hcase]
        funext x
        simp only [iterDelta', ssStarFn, star_mul, star_star, mul_comm]
      · left
        rw [iterDelta_succ, hcase]
        funext x
        simp only [iterDelta', ssStarFn, star_star]

/-! ## The peel-forward estimate -/

/-- **The "many shift tuples" hypothesis implies the `U^s`-lower bound `gamma * delta`.** -/
theorem ssManyShiftsLeUNormPow {P : Polynomial ℤ} {s Ns N D : ℕ} {f₀ f₁ : ℤ → ℂ} {δ γ : ℝ}
    (hs : 2 ≤ s) (hD : 1 ≤ D) (hN : 1 ≤ N) (hNNs : N ≤ Ns)
    (h0 : SupportIn f₀ Ns) (h1 : SupportIn f₁ Ns) (hδ : 0 < δ)
    (h : ManyShiftsHypDensity P s Ns N D f₀ f₁ δ γ) :
    γ * δ ≤ uNormPow s (arithIcc P.leadingCoeff D) (symIcc (dSup P Ns N)) (dualFn N P f₀ f₁) := by
  obtain ⟨H, hHmem, hHcard, hHlev⟩ := h
  set Q : Finset ℤ := arithIcc P.leadingCoeff D with hQ
  set S : Finset ℤ := symIcc (dSup P Ns N) with hS
  set F : ℤ → ℂ := dualFn N P f₀ f₁ with hF
  have hQne : Q.Nonempty := by
    rw [hQ, arithIcc]
    exact Finset.image_nonempty.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hD⟩⟩
  have hFfin : FinSuppZ F := by
    rw [hF]
    exact FinSuppZ.of_supportIn (Work.Peluse.Tools.dualFn_supportIn (by omega) P f₀ f₁ h0 h1 hNNs)
  have hQpos : (0 : ℝ) < (Q.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hQne
  have hpeel := boxNormPow_eq_peel_two (t := s) hs Q S F hFfin hQne
  have hconv : ∀ sh ∈ H, Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S (iterDelta' (s - 2) sh F)
      = Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S (iterDelta (s - 2) sh F) := by
    intro sh _
    rcases ssIterDeltaEqIterDeltaOr (s - 2) sh F with h' | h'
    · rw [h']
    · rw [h', ssBoxNormPowStarFn]
  have hHsub : H ⊆ Fintype.piFinset (fun _ : Fin (s - 2) => Q.product Q) := by
    intro sh hsh
    refine Fintype.mem_piFinset.mpr (fun i => ?_)
    exact Finset.mem_product.mpr ⟨(hHmem sh hsh i).1, (hHmem sh hsh i).2⟩
  have hsum : γ * (Q.card : ℝ) ^ (2 * (s - 2)) * δ ≤
      ∑ H' ∈ Fintype.piFinset (fun _ : Fin (s - 2) => Q.product Q),
        Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S (iterDelta' (s - 2) H' F) := by
    have h1' : (∑ H' ∈ H, Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S
          (iterDelta' (s - 2) H' F))
        ≤ ∑ H' ∈ Fintype.piFinset (fun _ : Fin (s - 2) => Q.product Q),
          Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S (iterDelta' (s - 2) H' F) :=
      Finset.sum_le_sum_of_subset_of_nonneg hHsub (fun x _ _ => norm_nonneg _)
    have h2' : (∑ H' ∈ H, Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S
          (iterDelta' (s - 2) H' F))
        = ∑ H' ∈ H, Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S
          (iterDelta (s - 2) H' F) :=
      Finset.sum_congr rfl (fun sh hsh => hconv sh hsh)
    have h3' : (∑ _H' ∈ H, δ) ≤ ∑ H' ∈ H, Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S
          (iterDelta (s - 2) H' F) :=
      Finset.sum_le_sum (fun sh hsh => hHlev sh hsh)
    have h4' : (∑ _H' ∈ H, δ) = (H.card : ℝ) * δ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h5' : γ * (Q.card : ℝ) ^ (2 * (s - 2)) * δ ≤ (H.card : ℝ) * δ :=
      mul_le_mul_of_nonneg_right hHcard (le_of_lt hδ)
    calc γ * (Q.card : ℝ) ^ (2 * (s - 2)) * δ
        ≤ (H.card : ℝ) * δ := h5'
      _ = ∑ _H' ∈ H, δ := h4'.symm
      _ ≤ ∑ H' ∈ H, Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S
            (iterDelta (s - 2) H' F) := h3'
      _ = ∑ H' ∈ H, Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S
            (iterDelta' (s - 2) H' F) := h2'.symm
      _ ≤ ∑ H' ∈ Fintype.piFinset (fun _ : Fin (s - 2) => Q.product Q),
            Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S (iterDelta' (s - 2) H' F) := h1'
  have hkey : uNormPow s Q S F = ((Q.card : ℝ))⁻¹ ^ (2 * (s - 2)) *
      ∑ H' ∈ Fintype.piFinset (fun _ : Fin (s - 2) => Q.product Q),
        Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S (iterDelta' (s - 2) H' F) := hpeel
  rw [hkey]
  have hstep : ((Q.card : ℝ))⁻¹ ^ (2 * (s - 2)) * (γ * (Q.card : ℝ) ^ (2 * (s - 2)) * δ)
      = γ * δ := by
    have hpow : ((Q.card : ℝ))⁻¹ ^ (2 * (s - 2)) * ((Q.card : ℝ) ^ (2 * (s - 2)) * (γ * δ))
        = γ * δ := by
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (ne_of_gt hQpos), one_pow, one_mul]
    calc ((Q.card : ℝ))⁻¹ ^ (2 * (s - 2)) * (γ * (Q.card : ℝ) ^ (2 * (s - 2)) * δ)
        = ((Q.card : ℝ))⁻¹ ^ (2 * (s - 2)) * ((Q.card : ℝ) ^ (2 * (s - 2)) * (γ * δ)) := by
          ring
      _ = γ * δ := hpow
  calc γ * δ = ((Q.card : ℝ))⁻¹ ^ (2 * (s - 2)) * (γ * (Q.card : ℝ) ^ (2 * (s - 2)) * δ) :=
        hstep.symm
    _ ≤ ((Q.card : ℝ))⁻¹ ^ (2 * (s - 2)) *
        ∑ H' ∈ Fintype.piFinset (fun _ : Fin (s - 2) => Q.product Q),
          Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S (iterDelta' (s - 2) H' F) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)


private lemma gap_asm_fac {a r : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hr0 : 0 ≤ r)
    (K₂ K₃ : ℕ) :
    (a * r) ^ (2 * K₂ * K₃ + 2 * K₃) ≤ (a * r) ^ (2 * K₂ * K₃) * r ^ (2 * K₃) := by
  rw [mul_pow, mul_pow]
  have h1 : a ^ (2 * K₂ * K₃ + 2 * K₃) ≤ a ^ (2 * K₂ * K₃) :=
    pow_le_pow_of_le_one ha0 ha1 (by omega)
  have h2 : r ^ (2 * K₂ * K₃ + 2 * K₃) = r ^ (2 * K₂ * K₃) * r ^ (2 * K₃) := by
    rw [← pow_add]
  rw [h2]
  have h3 : a ^ (2 * K₂ * K₃) * (r ^ (2 * K₂ * K₃) * r ^ (2 * K₃))
      = a ^ (2 * K₂ * K₃) * r ^ (2 * K₂ * K₃) * r ^ (2 * K₃) := by ring
  rw [← h3]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

private lemma gap_asm_norm {A B X N' C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : A * B * X ≤ C * B⁻¹ * A⁻¹ * N') : A ^ 2 * B ^ 2 * X / C ≤ N' := by
  have hkey : (C * B⁻¹ * A⁻¹ * N') * (A * B) = C * N' := by
    field_simp
  have hmul := mul_le_mul_of_nonneg_right h (le_of_lt (mul_pos hA hB))
  rw [hkey] at hmul
  have h2 : (A * B * X) * (A * B) = A ^ 2 * B ^ 2 * X := by ring
  rw [h2] at hmul
  rw [div_le_iff₀ hC]
  simpa [mul_comm] using hmul


private lemma gap_conv1 {x : ℝ} (K₂ K₃ : ℕ) : ((x ^ K₂)⁻¹) ^ K₃ = ((x ^ (K₂ * K₃)))⁻¹ := by
  rw [inv_pow, ← pow_mul]

private lemma gap_conv2 {x : ℝ} (K₂ K₃ : ℕ) : ((x ^ K₂)) ^ K₃ = x ^ (K₂ * K₃) := by
  rw [← pow_mul]

private lemma gap_conv3 {r : ℝ} (K₃ : ℕ) : r⁻¹ ^ K₃ = (r ^ K₃)⁻¹ := inv_pow r K₃

private lemma gap_exp1 {x : ℝ} (K₂ K₃ : ℕ) : ((x ^ (K₂ * K₃)) ^ 2) = x ^ (2 * K₂ * K₃) := by
  have h : (K₂ * K₃) * 2 = 2 * K₂ * K₃ := by ring
  rw [← pow_mul, h]

private lemma gap_exp2 {r : ℝ} (K₃ : ℕ) : (r ^ K₃) ^ 2 = r ^ (2 * K₃) := by
  have h : K₃ * 2 = 2 * K₃ := by ring
  rw [← pow_mul, h]

private lemma gap_inv_pow_mul {a : ℝ} (n m : ℕ) : ((a ^ n)⁻¹) ^ m = (a⁻¹) ^ (n * m) := by
  calc ((a ^ n)⁻¹) ^ m = ((a ^ n) ^ m)⁻¹ := inv_pow (a ^ n) m
    _ = (a ^ (n * m))⁻¹ := by rw [← pow_mul]
    _ = (a⁻¹) ^ (n * m) := (inv_pow a (n * m)).symm

private lemma gap_inv_mul (a b : ℝ) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  rw [mul_inv]

private lemma gap_mul_pow (a b : ℝ) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n :=
  mul_pow a b n

/-! ## The `s = 2` case at the balanced scale (checked against the proved `ss_u2_level`) -/

/-- Sanity check: the `s = 2` case of `ssGapBalCore` at the balanced scale, from the *proved*
`ss_u2_level`. -/
theorem ssGapBalCoreTwo {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (h1 : Work.Peluse.PeluseU2Inverse) (h2 : Work.Peluse.PeluseMajorArc P) :
    ∃ C K : ℕ, 1 ≤ C ∧ 1 ≤ K ∧
      ∀ (Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (δ γ : ℝ),
        2 ≤ P.natDegree → 1 ≤ N → 1 ≤ Ns → 1 ≤ D →
        Work.Peluse.Scaled Ns N P.natDegree → N ≤ Ns → (D : ℝ) ≤ (Ns : ℝ) →
        Work.Peluse.SupportIn f₀ Ns → Work.Peluse.SupportIn f₁ Ns →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
        0 < δ → δ ≤ 1 → 0 < γ → γ ≤ 1 →
        Work.Peluse.Ulower.ManyShiftsHypDensity P 2 Ns N D f₀ f₁ δ γ →
        ∃ q N' : ℕ, 1 ≤ q ∧ 1 ≤ N' ∧ N' ≤ N ∧
          (q : ℝ) ≤ (C : ℝ) * (δ⁻¹) ^ K * (γ⁻¹) ^ K * ((Ns : ℝ) / (D : ℝ)) ^ K ∧
          (δ ^ K * γ ^ K * ((D : ℝ) / (Ns : ℝ)) ^ K) * (N : ℝ) / (C : ℝ) ≤ (N' : ℝ) ∧
          (δ ^ K * γ ^ K * ((D : ℝ) / (Ns : ℝ)) ^ K) * (Ns : ℝ) / (C : ℝ) ≤
            Work.Peluse.progAvgSum N' (q : ℤ) f₁ := by
  obtain ⟨C₃, K₃, hC₃, hK₃, hSSL⟩ := ss_u2_level (P := P) hd h1 h2
  refine ⟨C₃, 2 * K₃, hC₃, by omega, ?_⟩
  intro Ns N D f₀ f₁ δ γ hd' hN hNs hD hScaled hNNs hDNs h0 h1' hb0 hb1 hδ0 hδ1 hγ0 hγ1 hmany
  have hγδ0 : 0 < γ * δ := mul_pos hγ0 hδ0
  have hγδ1 : γ * δ ≤ 1 := by nlinarith
  have hη : γ * δ ≤ Work.Peluse.uNormPow 2 (Work.Peluse.arithIcc P.leadingCoeff D)
        (Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)) (Work.Peluse.dualFn N P f₀ f₁) :=
    ssManyShiftsLeUNormPow (s := 2) (by norm_num) hD hN hNNs h0 h1' hδ0 hmany
  obtain ⟨q, N', hq1, hq, hN'1, hN'le, hN'low, hprog⟩ :=
    hSSL Ns N D f₀ f₁ (γ * δ) hd' hN hNs hScaled hNNs hD hDNs h0 h1' hb0 hb1 hγδ0 hγδ1 hη
  have hC₃pos : (0 : ℝ) < (C₃ : ℝ) := by exact_mod_cast hC₃
  refine ⟨q, N', hq1, hN'1, hN'le, ?_, ?_, ?_⟩
  · -- q-bound
    refine le_trans hq ?_
    simp only [one_pow, mul_one]
    have hδinv : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ1
    have hγinv : (1 : ℝ) ≤ γ⁻¹ := (one_le_inv₀ hγ0).mpr hγ1
    have hratio : (1 : ℝ) ≤ (Ns : ℝ) / (D : ℝ) := by
      rw [one_le_div (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD) : (0:ℝ) < (D:ℝ))]
      exact_mod_cast hDNs
    have hp1 : (γ * δ)⁻¹ ^ K₃ ≤ (δ⁻¹) ^ (2 * K₃) * (γ⁻¹) ^ (2 * K₃) := by
      rw [mul_inv, mul_pow]
      have e1 : (δ⁻¹) ^ K₃ ≤ (δ⁻¹) ^ (2 * K₃) := pow_le_pow_right₀ hδinv (by omega)
      have e2 : (γ⁻¹) ^ K₃ ≤ (γ⁻¹) ^ (2 * K₃) := pow_le_pow_right₀ hγinv (by omega)
      have hd0 : (0 : ℝ) ≤ δ⁻¹ := le_of_lt (inv_pos.mpr hδ0)
      have hg0 : (0 : ℝ) ≤ γ⁻¹ := le_of_lt (inv_pos.mpr hγ0)
      calc (γ⁻¹) ^ K₃ * (δ⁻¹) ^ K₃ ≤ (γ⁻¹) ^ (2 * K₃) * (δ⁻¹) ^ (2 * K₃) :=
            mul_le_mul e2 e1 (pow_nonneg hd0 _) (pow_nonneg hg0 _)
        _ = (δ⁻¹) ^ (2 * K₃) * (γ⁻¹) ^ (2 * K₃) := by ring
    have hp2 : (1 : ℝ) ≤ ((Ns : ℝ) / (D : ℝ)) ^ (2 * K₃) := one_le_pow₀ hratio
    have hns0 : (0 : ℝ) ≤ (Ns : ℝ) / (D : ℝ) := by positivity
    calc (C₃ : ℝ) * ((Ns : ℝ) / (D : ℝ)) ^ K₃ * ((γ * δ)⁻¹) ^ K₃
        = (C₃ : ℝ) * ((γ * δ)⁻¹) ^ K₃ * ((Ns : ℝ) / (D : ℝ)) ^ K₃ := by ring
      _ ≤ (C₃ : ℝ) * ((δ⁻¹) ^ (2 * K₃) * (γ⁻¹) ^ (2 * K₃)) *
            ((Ns : ℝ) / (D : ℝ)) ^ K₃ := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hns0 _)
          exact mul_le_mul_of_nonneg_left hp1 (by positivity)
      _ ≤ (C₃ : ℝ) * ((δ⁻¹) ^ (2 * K₃) * (γ⁻¹) ^ (2 * K₃)) *
            ((Ns : ℝ) / (D : ℝ)) ^ (2 * K₃) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_pow_right₀ hratio (by omega)
      _ = (C₃ : ℝ) * (δ⁻¹) ^ (2 * K₃) * (γ⁻¹) ^ (2 * K₃) *
            ((Ns : ℝ) / (D : ℝ)) ^ (2 * K₃) := by ring
  · -- N'-clause
    have hlow : (γ * δ) ^ (2 * K₃) * ((D : ℝ) / (Ns : ℝ)) ^ (2 * K₃) * (N : ℝ) / (C₃ : ℝ)
        ≤ (N' : ℝ) := by
      have hrew : (γ * δ) ^ K₃ * ((D : ℝ) / (Ns : ℝ)) ^ K₃ * (N : ℝ) ≤
          (C₃ : ℝ) * ((Ns : ℝ) / (D : ℝ)) ^ K₃ * ((γ * δ)⁻¹) ^ K₃ * (N' : ℝ) := by
        simpa using hN'low
      have hr0 : (0 : ℝ) < (D : ℝ) / (Ns : ℝ) :=
        div_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD) : (0:ℝ) < (D:ℝ)) (by exact_mod_cast hNs : (0:ℝ) < (Ns:ℝ))
      have hinv : (((Ns : ℝ) / (D : ℝ)) ^ K₃) = (((D : ℝ) / (Ns : ℝ)) ^ K₃)⁻¹ := by
        have hthis : (D : ℝ) / (Ns : ℝ) = ((Ns : ℝ) / (D : ℝ))⁻¹ := (inv_div (Ns:ℝ) (D:ℝ)).symm
        rw [hthis, inv_pow, inv_inv]
      have hinv2 : ((γ * δ)⁻¹) ^ K₃ = (((γ * δ) ^ K₃))⁻¹ := inv_pow (γ * δ) K₃
      rw [hinv, hinv2] at hrew
      have h := gap_asm_norm (A := (γ * δ) ^ K₃) (B := ((D : ℝ) / (Ns : ℝ)) ^ K₃) (X := (N : ℝ))
        (N' := (N' : ℝ)) (C := (C₃ : ℝ)) (pow_pos hγδ0 _) (pow_pos hr0 _) hC₃pos hrew
      rw [← pow_mul, ← pow_mul] at h
      have e1 : K₃ * 2 = 2 * K₃ := by ring
      rw [e1] at h
      exact h
    convert hlow using 2 <;> ring_nf
  · -- progAvgSum-clause
    have hlow : (γ * δ) ^ (2 * K₃) * ((D : ℝ) / (Ns : ℝ)) ^ (2 * K₃) * (Ns : ℝ) / (C₃ : ℝ)
        ≤ Work.Peluse.progAvgSum N' (q : ℤ) f₁ := by
      have hrew : (γ * δ) ^ K₃ * ((D : ℝ) / (Ns : ℝ)) ^ K₃ * (Ns : ℝ) ≤
          (C₃ : ℝ) * ((Ns : ℝ) / (D : ℝ)) ^ K₃ * ((γ * δ)⁻¹) ^ K₃ *
            Work.Peluse.progAvgSum N' (q : ℤ) f₁ := by
        simpa using hprog
      have hr0 : (0 : ℝ) < (D : ℝ) / (Ns : ℝ) :=
        div_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD) : (0:ℝ) < (D:ℝ)) (by exact_mod_cast hNs : (0:ℝ) < (Ns:ℝ))
      have hinv : (((Ns : ℝ) / (D : ℝ)) ^ K₃) = (((D : ℝ) / (Ns : ℝ)) ^ K₃)⁻¹ := by
        have hthis : (D : ℝ) / (Ns : ℝ) = ((Ns : ℝ) / (D : ℝ))⁻¹ := (inv_div (Ns:ℝ) (D:ℝ)).symm
        rw [hthis, inv_pow, inv_inv]
      have hinv2 : ((γ * δ)⁻¹) ^ K₃ = (((γ * δ) ^ K₃))⁻¹ := inv_pow (γ * δ) K₃
      rw [hinv, hinv2] at hrew
      have h := gap_asm_norm (A := (γ * δ) ^ K₃) (B := ((D : ℝ) / (Ns : ℝ)) ^ K₃) (X := (Ns : ℝ))
        (N' := Work.Peluse.progAvgSum N' (q : ℤ) f₁) (C := (C₃ : ℝ)) (pow_pos hγδ0 _)
        (pow_pos hr0 _) hC₃pos hrew
      rw [← pow_mul, ← pow_mul] at h
      have e1 : K₃ * 2 = 2 * K₃ := by ring
      rw [e1] at h
      exact h
    convert hlow using 2 <;> ring_nf


/-! ## The two chapters of the balanced assembly (imported)

  * `Work.Peluse.Ulower.degree_lowering_A` --- Peluse Lemma 3.9 (the degree lowering `U^s => U^2`) 
    in `Submission/Work/Peluse/Ulower/ssDegreeLoweringA.lean`;
  * `Work.Peluse.Ulower.ss_u2_level_A` --- Peluse Section 9 (`U^2 => progression average`) 
    in `Submission/Work/Peluse/Ulower/ss_u2_level_A.lean`.
-/
/-! ## The assembly -/

theorem ssGapBalCore {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (h1 : Work.Peluse.PeluseU2Inverse) (h2 : Work.Peluse.PeluseMajorArc P) :
    ∀ (s : ℕ) (hs : 2 ≤ s) (A : ℕ), 1 ≤ A → ∃ C K : ℕ, 1 ≤ C ∧ 1 ≤ K ∧
      ∀ (Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (δ γ : ℝ),
        2 ≤ P.natDegree → 1 ≤ N → 1 ≤ Ns → 1 ≤ D →
        (N : ℝ) ≤ (Ns : ℝ) →
        (N : ℝ) ^ P.natDegree ≤ (A : ℝ) * (Ns : ℝ) →
        (Ns : ℝ) ≤ (A : ℝ) * (N : ℝ) ^ P.natDegree →
        (D : ℝ) ≤ (Ns : ℝ) →
        Work.Peluse.SupportIn f₀ Ns → Work.Peluse.SupportIn f₁ Ns →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
        0 < δ → δ ≤ 1 → 0 < γ → γ ≤ 1 →
        Work.Peluse.Ulower.ManyShiftsHypDensity P s Ns N D f₀ f₁ δ γ →
        ∃ q N' : ℕ, 1 ≤ q ∧ 1 ≤ N' ∧ N' ≤ N ∧
          (q : ℝ) ≤ (C : ℝ) * (δ⁻¹) ^ K * (γ⁻¹) ^ K * ((Ns : ℝ) / (D : ℝ)) ^ K ∧
          (δ ^ K * γ ^ K * ((D : ℝ) / (Ns : ℝ)) ^ K) * (N : ℝ) / (C : ℝ) ≤ (N' : ℝ) ∧
          (δ ^ K * γ ^ K * ((D : ℝ) / (Ns : ℝ)) ^ K) * (Ns : ℝ) / (C : ℝ) ≤
            Work.Peluse.progAvgSum N' (q : ℤ) f₁ := by
  intro s hs A hA
  obtain ⟨K₂, hK₂, hDL⟩ := ssDegreeLoweringA (P := P) hd h1 h2 A hA s hs
  obtain ⟨C₃, K₃, hC₃, hK₃, hSSL⟩ := ss_u2_level_A (P := P) hd h1 h2 A hA
  refine ⟨C₃, 2 * (K₂ * K₃ + K₃), hC₃, by omega, ?_⟩
  intro Ns N D f₀ f₁ δ γ hd' hN hNs hD hNNs hsc1 hsc2 hDNs h0 h1' hb0 hb1 hδ0 hδ1 hγ0 hγ1 hmany
  have hγδ0 : 0 < γ * δ := mul_pos hγ0 hδ0
  have hγδ1 : γ * δ ≤ 1 := by nlinarith
  have hNNs' : N ≤ Ns := by exact_mod_cast hNNs
  have hη : γ * δ ≤ Work.Peluse.uNormPow s (Work.Peluse.arithIcc P.leadingCoeff D)
        (Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)) (Work.Peluse.dualFn N P f₀ f₁) :=
    ssManyShiftsLeUNormPow hs hD hN hNNs' h0 h1' hδ0 hmany
  have hdl := hDL Ns N D f₀ f₁ (γ * δ) hd' hN hNs hD hNNs hsc1 hsc2 hDNs h0 h1' hb0 hb1 hγδ0 hγδ1 hη
  set r : ℝ := (D : ℝ) / (Ns : ℝ) with hrdef
  have hNsR : (0 : ℝ) < (Ns : ℝ) := by exact_mod_cast hNs
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hr0 : 0 < r := by rw [hrdef]; exact div_pos hDR hNsR
  have hr1 : r ≤ 1 := by rw [hrdef, div_le_one hNsR]; exact hDNs
  have hα0 : 0 < (γ * δ) * r := mul_pos hγδ0 hr0
  have hα1 : (γ * δ) * r ≤ 1 := by nlinarith [hγδ1, hr1, hγδ0, hr0]
  have hαdef : (γ * δ) * r = (γ * δ) * ((D : ℝ) / (Ns : ℝ)) := by rw [hrdef]
  have hdl' : ((γ * δ) * r) ^ K₂ ≤ Work.Peluse.uNormPow 2 (Work.Peluse.arithIcc P.leadingCoeff D)
        (Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)) (Work.Peluse.dualFn N P f₀ f₁) := by
    rw [hαdef]
    exact hdl
  have hδ₂pos : 0 < ((γ * δ) * r) ^ K₂ := pow_pos hα0 _
  have hδ₂1 : ((γ * δ) * r) ^ K₂ ≤ 1 := pow_le_one₀ (le_of_lt hα0) hα1
  obtain ⟨q, N', hq1, hq, hN'1, hN'le, hN'low, hprog⟩ :=
    hSSL Ns N D f₀ f₁ (((γ * δ) * r) ^ K₂) hd' hN hNs hD hNNs hsc1 hsc2 hDNs h0 h1' hb0 hb1
      hδ₂pos hδ₂1 hdl'
  have hratio : (Ns : ℝ) / (D : ℝ) = r⁻¹ := by rw [hrdef, inv_div]
  -- normalised forms
  have hq' : (q : ℝ) ≤ (C₃ : ℝ) * r⁻¹ ^ K₃ * ((((γ * δ) * r) ^ K₂)⁻¹) ^ K₃ := by
    have : ((Ns : ℝ) / (D : ℝ)) ^ K₃ = r⁻¹ ^ K₃ := by rw [hratio]
    simpa [this] using hq
  have hN'low' : (((γ * δ) * r) ^ K₂) ^ K₃ * r ^ K₃ * (N : ℝ)
      ≤ (C₃ : ℝ) * r⁻¹ ^ K₃ * ((((γ * δ) * r) ^ K₂)⁻¹) ^ K₃ * (N' : ℝ) := by
    have : ((Ns : ℝ) / (D : ℝ)) ^ K₃ = r⁻¹ ^ K₃ := by rw [hratio]
    simpa [this] using hN'low
  have hprog' : (((γ * δ) * r) ^ K₂) ^ K₃ * r ^ K₃ * (Ns : ℝ)
      ≤ (C₃ : ℝ) * r⁻¹ ^ K₃ * ((((γ * δ) * r) ^ K₂)⁻¹) ^ K₃ *
          Work.Peluse.progAvgSum N' (q : ℤ) f₁ := by
    have : ((Ns : ℝ) / (D : ℝ)) ^ K₃ = r⁻¹ ^ K₃ := by rw [hratio]
    simpa [this] using hprog
  -- reduce the reciprocal factors to the standard form
  have eA : ((((γ * δ) * r) ^ K₂)⁻¹) ^ K₃
      = (δ⁻¹) ^ (K₂ * K₃) * (γ⁻¹) ^ (K₂ * K₃) * (r⁻¹) ^ (K₂ * K₃) := by
    rw [gap_inv_pow_mul (a := (γ * δ) * r) K₂ K₃, gap_inv_mul (γ * δ) r,
      gap_mul_pow (γ * δ)⁻¹ r⁻¹ (K₂ * K₃), gap_inv_mul γ δ,
      gap_mul_pow γ⁻¹ δ⁻¹ (K₂ * K₃)]
    ring
  have hfin : ∀ {X Y : ℝ}, ((γ * δ) * r) ^ (K₂ * K₃) * r ^ K₃ * X
      ≤ (C₃ : ℝ) * (r ^ K₃)⁻¹ * ((((γ * δ) * r) ^ (K₂ * K₃))⁻¹) * Y →
      ((γ * δ) * r) ^ (2 * K₂ * K₃) * r ^ (2 * K₃) * X / (C₃ : ℝ) ≤ Y := by
    intro X Y hX
    have hAm : 0 < ((γ * δ) * r) ^ (K₂ * K₃) := pow_pos hα0 _
    have hBm : 0 < r ^ K₃ := pow_pos hr0 _
    have hCm : 0 < (C₃ : ℝ) := by exact_mod_cast hC₃
    have h := gap_asm_norm hAm hBm hCm hX
    rw [gap_exp1, gap_exp2] at h
    exact h
  have hN'fin : ((γ * δ) * r) ^ (2 * K₂ * K₃) * r ^ (2 * K₃) * (N : ℝ) / (C₃ : ℝ) ≤ (N' : ℝ) := by
    apply hfin
    rw [gap_conv1, gap_conv2, gap_conv3] at hN'low'
    exact hN'low'
  have hprogfin : ((γ * δ) * r) ^ (2 * K₂ * K₃) * r ^ (2 * K₃) * (Ns : ℝ) / (C₃ : ℝ)
      ≤ Work.Peluse.progAvgSum N' (q : ℤ) f₁ := by
    apply hfin
    rw [gap_conv1, gap_conv2, gap_conv3] at hprog'
    exact hprog'
  -- the exponent comparisons
  have hδinv1 : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ1
  have hγinv1 : (1 : ℝ) ≤ γ⁻¹ := (one_le_inv₀ hγ0).mpr hγ1
  have hrinv1 : (1 : ℝ) ≤ r⁻¹ := by
    apply one_le_inv₀ hr0 |>.mpr
    exact hr1
  have hKle1 : K₂ * K₃ ≤ 2 * (K₂ * K₃ + K₃) := by omega
  have hKle2 : K₂ * K₃ + K₃ ≤ 2 * (K₂ * K₃ + K₃) := by omega
  refine ⟨q, N', hq1, hN'1, hN'le, ?_, ?_, ?_⟩
  · -- the `q`-bound
    refine le_trans hq' ?_
    rw [eA]
    have e1 : (δ⁻¹) ^ (K₂ * K₃) ≤ (δ⁻¹) ^ (2 * (K₂ * K₃ + K₃)) :=
      pow_le_pow_right₀ hδinv1 hKle1
    have e2 : (γ⁻¹) ^ (K₂ * K₃) ≤ (γ⁻¹) ^ (2 * (K₂ * K₃ + K₃)) :=
      pow_le_pow_right₀ hγinv1 hKle1
    have e3 : (r⁻¹) ^ (K₂ * K₃ + K₃) ≤ (r⁻¹) ^ (2 * (K₂ * K₃ + K₃)) :=
      pow_le_pow_right₀ hrinv1 hKle2
    have e4 : r⁻¹ ^ K₃ * (r⁻¹) ^ (K₂ * K₃) = (r⁻¹) ^ (K₂ * K₃ + K₃) := by
      rw [← pow_add]; ring_nf
    have hC3nn : (0 : ℝ) ≤ (C₃ : ℝ) := by positivity
    calc (C₃ : ℝ) * r⁻¹ ^ K₃ *
          ((δ⁻¹) ^ (K₂ * K₃) * (γ⁻¹) ^ (K₂ * K₃) * (r⁻¹) ^ (K₂ * K₃))
        = (C₃ : ℝ) * ((r⁻¹) ^ (K₂ * K₃ + K₃) * ((δ⁻¹) ^ (K₂ * K₃) * (γ⁻¹) ^ (K₂ * K₃))) := by
          rw [← e4]; ring
      _ ≤ (C₃ : ℝ) * ((r⁻¹) ^ (2 * (K₂ * K₃ + K₃)) *
            ((δ⁻¹) ^ (2 * (K₂ * K₃ + K₃)) * (γ⁻¹) ^ (2 * (K₂ * K₃ + K₃)))) := by
          refine mul_le_mul_of_nonneg_left ?_ hC3nn
          exact mul_le_mul e3 (mul_le_mul e1 e2 (by positivity) (by positivity))
            (by positivity) (by positivity)
      _ = (C₃ : ℝ) * (δ⁻¹) ^ (2 * (K₂ * K₃ + K₃)) * (γ⁻¹) ^ (2 * (K₂ * K₃ + K₃)) *
            (r⁻¹) ^ (2 * (K₂ * K₃ + K₃)) := by ring
      _ = (C₃ : ℝ) * (δ⁻¹) ^ (2 * (K₂ * K₃ + K₃)) * (γ⁻¹) ^ (2 * (K₂ * K₃ + K₃)) *
            ((Ns : ℝ) / (D : ℝ)) ^ (2 * (K₂ * K₃ + K₃)) := by rw [hratio]
  · -- the `N'`-clause
    have hfac := gap_asm_fac (le_of_lt hγδ0) hγδ1 (le_of_lt hr0) K₂ K₃
    have hKK : 2 * (K₂ * K₃ + K₃) = 2 * K₂ * K₃ + 2 * K₃ := by ring
    rw [hKK]
    calc (δ ^ (2 * K₂ * K₃ + 2 * K₃) * γ ^ (2 * K₂ * K₃ + 2 * K₃) *
            ((D : ℝ) / (Ns : ℝ)) ^ (2 * K₂ * K₃ + 2 * K₃)) * (N : ℝ) / (C₃ : ℝ)
        = ((γ * δ) * r) ^ (2 * K₂ * K₃ + 2 * K₃) * (N : ℝ) / (C₃ : ℝ) := by
          rw [hrdef, mul_pow, mul_pow]; ring
      _ ≤ ((γ * δ) * r) ^ (2 * K₂ * K₃) * r ^ (2 * K₃) * (N : ℝ) / (C₃ : ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hfac (by positivity)
      _ ≤ (N' : ℝ) := hN'fin
  · -- the progression-average clause
    have hfac := gap_asm_fac (le_of_lt hγδ0) hγδ1 (le_of_lt hr0) K₂ K₃
    have hKK : 2 * (K₂ * K₃ + K₃) = 2 * K₂ * K₃ + 2 * K₃ := by ring
    rw [hKK]
    calc (δ ^ (2 * K₂ * K₃ + 2 * K₃) * γ ^ (2 * K₂ * K₃ + 2 * K₃) *
            ((D : ℝ) / (Ns : ℝ)) ^ (2 * K₂ * K₃ + 2 * K₃)) * (Ns : ℝ) / (C₃ : ℝ)
        = ((γ * δ) * r) ^ (2 * K₂ * K₃ + 2 * K₃) * (Ns : ℝ) / (C₃ : ℝ) := by
          rw [hrdef, mul_pow, mul_pow]; ring
      _ ≤ ((γ * δ) * r) ^ (2 * K₂ * K₃) * r ^ (2 * K₃) * (Ns : ℝ) / (C₃ : ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hfac (by positivity)
      _ ≤ Work.Peluse.progAvgSum N' (q : ℤ) f₁ := hprogfin

end

end Work.Peluse.Ulower
