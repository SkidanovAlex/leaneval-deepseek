import Mathlib
import Submission.Work.Peluse.BoxNorm.boxNormPow_shift
import Submission.Work.Peluse.Peel.boxSumPow_peel
import Submission.Work.Peluse.Peel.boxNormPow_one_tsum

/-!
# The diagonal lower bound for Peluse's box norm

For a function `f ≥ 0` (real) supported in `symIcc N`, the `2^m`-th power of Peluse's box norm
dominates the normalised `L²` mass of `f` raised to the `2^{m-1}`, up to the loss `H^{-m}` where
`H` bounds the cardinalities of the shift sets `Q i`:

`(H^m)⁻¹ · ((∑_{x ∈ symIcc N} ‖f x‖²)/|symIcc N|)^{2^{m-1}} ≤ ‖f‖_{□^m_Q(symIcc N)}^{2^m}`.

The proof has three ingredients.

* **Peeling the box norm.**  The identity `boxSumPow_peel` expresses the level-`(t+1)` box sum of a
  function as the average over `h, h' ∈ Q 0` of the level-`t` box sum of the difference
  `Δ'_{h,h'} f`.  Keeping only the diagonal pairs `h = h'` — legitimate because every term is a
  nonnegative real (`boxSumPow_eq_boxNormPow`) — and using the translation invariance
  (`boxNormPow_shift`) gives the *diagonal* inequality
  `|Q 0|⁻¹ · boxNormPow t (Q∘succ) S (h²) ≤ boxNormPow (t+1) Q S h`
  (`diag_peel_succ`, valid for `t ≥ 1`; the case `t = 0` is the same statement at level `1` and is
  proved from the sum-of-squares form of the level-one box norm, `level_one_ge_base`).
* **Iterating the diagonal.**  Applying it `m-1` times gives
  `(∏_{i<m} |Q i|⁻¹) · (∑_{x} h(x)^{2^m})/|S| ≤ boxNormPow m Q S h` (`main_ge`).
* **Power mean and cardinality bookkeeping.**  `(avg h²)^{2^{m-1}} ≤ avg h^{2^m}` (`powMeanZ`),
  and `H^{-m} ≤ ∏_{i<m} |Q i|⁻¹` (`cardBound`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.Peel

noncomputable section

open Work.Peluse

/-! ## Elementary toolbox -/

/-- The conjugation fixes real numbers. -/
lemma diag_star_ofReal (r : ℝ) : star ((r : ℂ)) = (r : ℂ) := Complex.conj_ofReal r

/-- The product of a real number and the conjugate of a real number. -/
lemma diag_ofReal_mul_star_ofReal (r s : ℝ) :
    ((r : ℝ) : ℂ) * star ((s : ℝ) : ℂ) = (((r * s : ℝ)) : ℂ) := by
  rw [diag_star_ofReal, ← Complex.ofReal_mul]

/-- The "diagonal square" of a real number. -/
lemma diag_ofReal_mul_star_self (r : ℝ) :
    ((r : ℝ) : ℂ) * star ((r : ℝ) : ℂ) = (((r ^ 2 : ℝ)) : ℂ) := by
  rw [diag_ofReal_mul_star_ofReal]; ring_nf

/-- Membership in the symmetric interval: `x ∈ symIcc n ↔ |x| ≤ n`. -/
lemma diag_mem_symIcc (n : ℕ) (x : ℤ) : x ∈ Work.Peluse.symIcc n ↔ |x| ≤ (n : ℤ) := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  exact abs_le.symm

/-! ## `FinSuppZ` bookkeeping -/

lemma diag_supportIn_shift {f : ℤ → ℂ} {N : ℕ} (h : Work.Peluse.SupportIn f N) (p : ℤ) :
    Work.Peluse.SupportIn (fun x => f (x + p)) (N + p.natAbs) := by
  intro x hx
  apply h
  have htri : x.natAbs ≤ (x + p).natAbs + p.natAbs := by
    have h' := Int.natAbs_add_le (x + p) (-p)
    simpa [Int.natAbs_neg, add_assoc] using h'
  omega

lemma diag_supportIn_star {f : ℤ → ℂ} {N : ℕ} (h : Work.Peluse.SupportIn f N) :
    Work.Peluse.SupportIn (fun x => star (f x)) N := by
  intro x hx
  show star (f x) = 0
  rw [h x hx, star_zero]

lemma diag_supportIn_mul {f g : ℤ → ℂ} {N M : ℕ} (hf : Work.Peluse.SupportIn f N)
    (hg : Work.Peluse.SupportIn g M) : Work.Peluse.SupportIn (f * g) (max N M) := by
  intro x hx
  have hN : N < x.natAbs := lt_of_le_of_lt (le_max_left _ _) hx
  rw [Pi.mul_apply, hf x hN, zero_mul]

/-- The difference `Δ'_{h,h'} f (u) = f (u+h) conj (f (u+h'))` of a finitely supported `f` is
finitely supported. -/
lemma diag_finSuppZ_mul_star_shift (f : ℤ → ℂ) (hf : Work.Peluse.FinSuppZ f) (h h' : ℤ) :
    Work.Peluse.FinSuppZ (fun u => f (u + h) * star (f (u + h'))) := by
  obtain ⟨N, hN⟩ := hf
  refine ⟨max (N + h.natAbs) (N + h'.natAbs), ?_⟩
  exact diag_supportIn_mul (diag_supportIn_shift hN h) (diag_supportIn_star (diag_supportIn_shift hN h'))

lemma diag_supportIn_ofReal_sq {g : ℤ → ℝ} {N : ℕ}
    (h : Work.Peluse.SupportIn (fun x => ((g x : ℝ) : ℂ)) N) :
    Work.Peluse.SupportIn (fun x => (((g x) ^ 2 : ℝ) : ℂ)) N := by
  intro x hx
  have hgx : g x = 0 := Complex.ofReal_eq_zero.mp (h x hx)
  simp [hgx]

lemma diag_finSuppZ_ofReal_sq {g : ℤ → ℝ}
    (h : Work.Peluse.FinSuppZ (fun x => ((g x : ℝ) : ℂ))) :
    Work.Peluse.FinSuppZ (fun x => (((g x) ^ 2 : ℝ) : ℂ)) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, diag_supportIn_ofReal_sq hN⟩

/-- Translation invariance of a `tsum` over `ℤ` for real-valued functions. -/
lemma diag_tsum_shift_add_real (g : ℤ → ℝ) (p : ℤ) : (∑' x : ℤ, g (x + p)) = ∑' x : ℤ, g x := by
  simpa [Equiv.coe_addRight] using Equiv.tsum_eq (Equiv.addRight p) g

/-- The power-mean (convexity) inequality for finitely many nonnegative reals. -/
lemma powMeanZ (s : Finset ℤ) {r : ℕ} (hr : 1 ≤ r) (u : ℤ → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i) :
    (∑ i ∈ s, u i) ^ r ≤ (s.card : ℝ) ^ (r - 1) * ∑ i ∈ s, (u i) ^ r := by
  have hp : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h' := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s (f := u) hp hu
  simp_rw [Real.rpow_natCast] at h'
  have hcast : ((r : ℝ) - 1) = ((r - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hr]; ring
  rw [hcast, Real.rpow_natCast] at h'
  exact h'

/-- The reciprocal of `H ^ m` is at most the product of the reciprocals of the cardinalities of
the nonempty sets `Q i`, each of cardinality at most `H ≥ 1`. -/
lemma cardBound {m : ℕ} {H : ℕ} (hH : 1 ≤ H) {Q : Fin m → Finset ℤ}
    (hQ : ∀ i : Fin m, (Q i).Nonempty) (hcard : ∀ i : Fin m, (Q i).card ≤ H) :
    (((H : ℝ) ^ m))⁻¹ ≤ ∏ i : Fin m, ((Q i).card : ℝ)⁻¹ := by
  have hle : ∀ i : Fin m, ((H : ℝ))⁻¹ ≤ ((Q i).card : ℝ)⁻¹ := by
    intro i
    have hc : (0 : ℝ) < ((Q i).card : ℝ) := by
      have h : 0 < (Q i).card := Finset.card_pos.mpr (hQ i)
      exact_mod_cast h
    have hcH : ((Q i).card : ℝ) ≤ (H : ℝ) := by exact_mod_cast hcard i
    exact inv_anti₀ hc hcH
  calc (((H : ℝ) ^ m))⁻¹ = ((H : ℝ)⁻¹) ^ m := by rw [inv_pow]
    _ = ∏ _i : Fin m, ((H : ℝ))⁻¹ := by
        rw [Finset.prod_const]; simp
    _ ≤ ∏ i : Fin m, ((Q i).card : ℝ)⁻¹ := by
        refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => hle i)
        positivity

/-! ## The level-one base case -/

/-- `inv_eq_inv_sq_mul` : `a⁻¹ = (a⁻¹)² · a` for any real `a` (valid also at `a = 0`). -/
lemma diag_inv_eq_inv_sq_mul (a : ℝ) : a⁻¹ = (a⁻¹) ^ 2 * a := by
  rcases eq_or_ne a 0 with h | h
  · simp [h]
  · rw [pow_two, mul_assoc, inv_mul_cancel₀ h, mul_one]

/-- **The level-one diagonal bound.**  For a nonnegative real `h` supported in `[-N,N]`, the
first box-norm power of `h` dominates the normalised `L²` mass of `h`, up to the factor `|Q|`. -/
lemma level_one_ge_base {N : ℕ} (Q S : Finset ℤ) (h : ℤ → ℝ) (hh : ∀ x, 0 ≤ h x)
    (hsupp : Work.Peluse.SupportIn (fun x => ((h x : ℝ) : ℂ)) N) :
    ((Q.card : ℝ))⁻¹ * ((∑' x : ℤ, (h x) ^ 2) / ((S.card : ℝ)))
      ≤ boxNormPow 1 (fun _ : Fin 1 => Q) S (fun x => ((h x : ℝ) : ℂ)) := by
  rw [boxNormPow_one_tsum Q S hsupp]
  have hterm : ∀ x : ℤ, ‖∑ a ∈ Q, ((h (x + a) : ℝ) : ℂ)‖ ^ 2
      = (∑ a ∈ Q, h (x + a)) ^ 2 := by
    intro x
    rw [← Complex.ofReal_sum, Complex.norm_of_nonneg (Finset.sum_nonneg fun a _ => hh _)]
  simp only [hterm]
  -- summability of the two families
  have hzero : ∀ (x : ℤ) (a : ℤ),
      x ∉ Finset.Icc (-(N : ℤ) - a) ((N : ℤ) - a) → h (x + a) = 0 := by
    intro x a hx
    have hab : (N : ℤ) < |x + a| := by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hnat : N < (x + a).natAbs := by
      rw [Int.abs_eq_natAbs] at hab
      exact_mod_cast hab
    exact Complex.ofReal_eq_zero.mp (hsupp (x + a) hnat)
  have hsum_a : ∀ a : ℤ, Summable (fun x : ℤ => (h (x + a)) ^ 2) := by
    intro a
    refine summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ) - a) ((N : ℤ) - a))
      (fun x hx => ?_)
    rw [hzero x a hx]; norm_num
  have hsumF : Summable (fun x : ℤ => ∑ a ∈ Q, (h (x + a)) ^ 2) :=
    summable_sum (fun a _ => hsum_a a)
  have hsumG : Summable (fun x : ℤ => (∑ a ∈ Q, h (x + a)) ^ 2) := by
    refine summable_of_ne_finset_zero
      (s := Q.biUnion (fun a => Finset.Icc (-(N : ℤ) - a) ((N : ℤ) - a))) (fun x hx => ?_)
    have hzero' : (∑ a ∈ Q, h (x + a)) = 0 := by
      refine Finset.sum_eq_zero (fun a ha => ?_)
      exact hzero x a (fun hmem => hx (Finset.mem_biUnion.mpr ⟨a, ha, hmem⟩))
    rw [hzero']; norm_num
  have hpt : ∀ x : ℤ, (∑ a ∈ Q, (h (x + a)) ^ 2) ≤ (∑ a ∈ Q, h (x + a)) ^ 2 := by
    intro x
    rw [pow_two, Finset.sum_mul_sum]
    refine Finset.sum_le_sum (fun a ha => ?_)
    rw [pow_two]
    exact Finset.single_le_sum (fun b _ => mul_nonneg (hh (x + a)) (hh (x + b))) ha
  have hI : (∑' x : ℤ, ∑ a ∈ Q, (h (x + a)) ^ 2) ≤ ∑' x : ℤ, (∑ a ∈ Q, h (x + a)) ^ 2 :=
    Summable.tsum_le_tsum hpt hsumF hsumG
  have hJ : (∑' x : ℤ, ∑ a ∈ Q, (h (x + a)) ^ 2) = ((Q.card : ℝ)) * ∑' x : ℤ, (h x) ^ 2 := by
    rw [Summable.tsum_finsetSum (fun a _ => hsum_a a)]
    rw [Finset.sum_congr rfl (fun a _ => diag_tsum_shift_add_real (fun x => (h x) ^ 2) a)]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hQT : ((Q.card : ℝ)) * (∑' x : ℤ, (h x) ^ 2)
      ≤ ∑' x : ℤ, (∑ a ∈ Q, h (x + a)) ^ 2 := by rw [← hJ]; exact hI
  have hkey : ((Q.card : ℝ))⁻¹ * (∑' x : ℤ, (h x) ^ 2)
      ≤ ((Q.card : ℝ))⁻¹ ^ 2 * ∑' x : ℤ, (∑ a ∈ Q, h (x + a)) ^ 2 := by
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hQT (sq_nonneg _))
    rw [← mul_assoc, ← diag_inv_eq_inv_sq_mul]
  rw [div_eq_mul_inv]
  calc ((Q.card : ℝ))⁻¹ * ((∑' x : ℤ, (h x) ^ 2) * ((S.card : ℝ))⁻¹)
      = ((S.card : ℝ))⁻¹ * (((Q.card : ℝ))⁻¹ * (∑' x : ℤ, (h x) ^ 2)) := by ring
    _ ≤ ((S.card : ℝ))⁻¹ * (((Q.card : ℝ))⁻¹ ^ 2 * ∑' x : ℤ, (∑ a ∈ Q, h (x + a)) ^ 2) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = ((S.card : ℝ))⁻¹ * ((Q.card : ℝ))⁻¹ ^ 2 * ∑' x : ℤ, (∑ a ∈ Q, h (x + a)) ^ 2 := by
        ring

/-! ## The diagonal peeling step -/

/-- **The diagonal of the peel identity.**  For `t ≥ 1`, the level-`(t+1)` box-norm power of `h`
dominates `|Q 0|⁻¹` times the level-`t` box-norm power of the square `h²`. -/
lemma diag_peel_succ {t : ℕ} (ht : 1 ≤ t) (Q : Fin (t+1) → Finset ℤ) (S : Finset ℤ) (h : ℤ → ℝ)
    (hh : ∀ x, 0 ≤ h x) (hfs : FinSuppZ (fun x => ((h x : ℝ) : ℂ)))
    (hQ0 : (Q 0).Nonempty) :
    ((Q 0).card : ℝ)⁻¹ * boxNormPow t (fun i : Fin t => Q i.succ) S
        (fun x => (((h x)^2 : ℝ) : ℂ))
      ≤ boxNormPow (t+1) Q S (fun x => ((h x : ℝ) : ℂ)) := by
  classical
  set G : ℤ → ℂ := fun x => ((h x : ℝ) : ℂ) with hG_def
  have hfsG : FinSuppZ G := hfs
  have hnt : 1 ≤ t + 1 := by omega
  set B : ℤ → ℤ → ℤ → ℂ := fun x y u => G (u + x) * star (G (u + y)) with hB_def
  have hBfs : ∀ x y : ℤ, FinSuppZ (B x y) := fun x y => diag_finSuppZ_mul_star_shift G hfsG x y
  have hinner : ∀ x ∈ Q 0, ∀ y ∈ Q 0,
      boxSumPow t (fun i : Fin t => Q i.succ) S (B x y)
        = ((boxNormPow t (fun i : Fin t => Q i.succ) S (B x y) : ℝ) : ℂ) :=
    fun x _ y _ => Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow ht (hBfs x y)
  have hreal : boxNormPow (t+1) Q S G = ((Q 0).card : ℝ)⁻¹ * ((Q 0).card : ℝ)⁻¹ *
      ∑ x ∈ Q 0, ∑ y ∈ Q 0, boxNormPow t (fun i : Fin t => Q i.succ) S (B x y) := by
    apply Complex.ofReal_inj.mp
    rw [show (↑(boxNormPow (t+1) Q S G) : ℂ) = boxSumPow (t+1) Q S G from
      (Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow hnt hfsG).symm]
    rw [boxSumPow_peel]
    rw [Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun y hy => hinner x hx y hy))]
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_sum,
      ← Complex.ofReal_mul]
  have hshift : ∀ x : ℤ, boxNormPow t (fun i : Fin t => Q i.succ) S (B x x)
      = boxNormPow t (fun i : Fin t => Q i.succ) S (fun u => (((h u)^2 : ℝ) : ℂ)) := by
    intro x
    have hfun : B x x = (fun u => (((h (u + x))^2 : ℝ) : ℂ)) := by
      funext u
      simp only [hB_def, hG_def]
      exact diag_ofReal_mul_star_self (h (u + x))
    rw [hfun]
    rw [show (fun u => (((h (u + x))^2 : ℝ) : ℂ))
        = Work.Peluse.shift x (fun u => (((h u)^2 : ℝ) : ℂ)) from rfl]
    rw [Work.Peluse.BoxNorm.boxNormPow_shift t (fun i : Fin t => Q i.succ) S
      (fun u => (((h u)^2 : ℝ) : ℂ)) x (diag_finSuppZ_ofReal_sq hfs)]
  have hsum_diag : ∑ x ∈ Q 0, boxNormPow t (fun i : Fin t => Q i.succ) S (B x x)
      = ((Q 0).card : ℝ) * boxNormPow t (fun i : Fin t => Q i.succ) S
          (fun u => (((h u)^2 : ℝ) : ℂ)) := by
    rw [Finset.sum_congr rfl (fun x _ => hshift x), Finset.sum_const, nsmul_eq_mul]
  have hnn : ∀ x y : ℤ, 0 ≤ boxNormPow t (fun i : Fin t => Q i.succ) S (B x y) :=
    fun x y => norm_nonneg _
  have hdiag : ∑ x ∈ Q 0, boxNormPow t (fun i : Fin t => Q i.succ) S (B x x)
      ≤ ∑ x ∈ Q 0, ∑ y ∈ Q 0, boxNormPow t (fun i : Fin t => Q i.succ) S (B x y) := by
    refine Finset.sum_le_sum fun x hx => ?_
    exact Finset.single_le_sum (fun y _ => hnn x y) hx
  have ha : (0:ℝ) < ((Q 0).card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hQ0
  have hSig : ((Q 0).card : ℝ) * boxNormPow t (fun i : Fin t => Q i.succ) S
      (fun u => (((h u)^2 : ℝ) : ℂ))
      ≤ ∑ x ∈ Q 0, ∑ y ∈ Q 0, boxNormPow t (fun i : Fin t => Q i.succ) S (B x y) := by
    rw [← hsum_diag]; exact hdiag
  rw [hreal]
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hSig (by positivity))
  rw [mul_assoc, ← mul_assoc ((Q 0).card : ℝ)⁻¹ ((Q 0).card : ℝ) _,
    inv_mul_cancel₀ (ne_of_gt ha), one_mul]

/-! ## The iterated diagonal bound -/

/-- **The level-`(n+1)` diagonal bound.**  Iterating `diag_peel_succ` (and the level-one base case
`level_one_ge_base`) `n` times: the box-norm power of order `n+1` of a nonnegative `h` supported in
`[-N,N]` dominates the product of the reciprocal cardinalities of the shift sets times the
normalised `L^{2^{n+1}}` mass of `h`. -/
lemma main_ge (n : ℕ) : ∀ (N : ℕ) (Q : Fin (n+1) → Finset ℤ) (S : Finset ℤ) (h : ℤ → ℝ),
    (∀ x, 0 ≤ h x) → Work.Peluse.SupportIn (fun x => ((h x : ℝ) : ℂ)) N →
    (∀ i : Fin (n+1), (Q i).Nonempty) →
    (∏ i : Fin (n+1), ((Q i).card : ℝ)⁻¹)
        * ((∑' x : ℤ, (h x) ^ (2^(n+1))) / (S.card : ℝ))
      ≤ boxNormPow (n+1) Q S (fun x => ((h x : ℝ) : ℂ)) := by
  induction n with
  | zero =>
      intro N Q S h hh hsupp hQ
      have hQeq : Q = (fun _ : Fin 1 => Q 0) := by
        funext i; rw [Fin.eq_zero i]
      rw [hQeq, Fin.prod_univ_one]
      have htwo : (2:ℕ) ^ (0+1) = 2 := by norm_num
      rw [htwo]
      exact level_one_ge_base (Q 0) S h hh hsupp
  | succ n ih =>
      intro N Q S h hh hsupp hQ
      have hstep := diag_peel_succ (t := n+1) (by omega) Q S h hh
        (Work.Peluse.FinSuppZ.of_supportIn hsupp) (hQ 0)
      have hih := ih N (fun i : Fin (n+1) => Q i.succ) S (fun x => (h x)^2)
        (fun x => sq_nonneg _) (diag_supportIn_ofReal_sq hsupp) (fun i => hQ i.succ)
      have hexp : ∀ x : ℤ, ((h x)^2) ^ (2^(n+1)) = (h x) ^ (2^((n+1)+1)) := by
        intro x
        rw [← pow_mul]
        congr 1
        rw [← Nat.pow_succ']
      rw [Fin.prod_univ_succ]
      calc ((Q 0).card : ℝ)⁻¹ * (∏ i : Fin (n+1), ((Q i.succ).card : ℝ)⁻¹)
            * ((∑' x : ℤ, (h x) ^ (2^((n+1)+1))) / ((S.card : ℝ)))
          = ((Q 0).card : ℝ)⁻¹ * ((∏ i : Fin (n+1), ((Q i.succ).card : ℝ)⁻¹)
            * ((∑' x : ℤ, ((h x)^2) ^ (2^(n+1))) / ((S.card : ℝ)))) := by
              rw [show (∑' x : ℤ, (h x) ^ (2^((n+1)+1)))
                  = ∑' x : ℤ, ((h x)^2) ^ (2^(n+1)) from
                tsum_congr (fun x => (hexp x).symm)]
              ring
        _ ≤ ((Q 0).card : ℝ)⁻¹ * boxNormPow (n+1) (fun i : Fin (n+1) => Q i.succ) S
              (fun x => (((h x)^2 : ℝ) : ℂ)) :=
              mul_le_mul_of_nonneg_left hih (by positivity)
        _ ≤ boxNormPow ((n+1)+1) Q S (fun x => ((h x : ℝ) : ℂ)) := hstep

/-! ## The target theorem -/

theorem boxNormPow_diag_ge {m : ℕ} (hm : 0 < m) {N H : ℕ} (Q : Fin m → Finset ℤ) (f : ℤ → ℂ)
    (hsup : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → f x = 0)
    (hpos : ∀ x : ℤ, f x = (((‖f x‖ : ℝ)) : ℂ))
    (hQ : ∀ i : Fin m, (Q i).Nonempty)
    (hcard : ∀ i : Fin m, (Q i).card ≤ H) (hH : 1 ≤ H) :
    ((H : ℝ) ^ m)⁻¹
        * ((∑ x ∈ Work.Peluse.symIcc N, ‖f x‖ ^ 2)
            / (((Work.Peluse.symIcc N).card : ℕ) : ℝ)) ^ (2 ^ (m - 1))
      ≤ Work.Peluse.boxNormPow m Q (Work.Peluse.symIcc N) f := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [show (n + 1) - 1 = n from by omega]
  set S : Finset ℤ := Work.Peluse.symIcc N with hSdef
  have hf_eq : (fun x : ℤ => ((‖f x‖ : ℝ) : ℂ)) = f := by
    funext x; exact (hpos x).symm
  have hh : ∀ x : ℤ, 0 ≤ ‖f x‖ := fun x => norm_nonneg _
  have hsupp : Work.Peluse.SupportIn (fun x => ((‖f x‖ : ℝ) : ℂ)) N := by
    intro x hx
    rw [hf_eq]
    refine hsup x (fun hmem => ?_)
    rw [diag_mem_symIcc] at hmem
    rw [Int.abs_eq_natAbs] at hmem
    have h2 : x.natAbs ≤ N := by exact_mod_cast hmem
    omega
  have hmain := main_ge n N Q S (fun x => ‖f x‖) hh hsupp hQ
  have hcardb := cardBound (m := n+1) hH hQ hcard
  have htsum : (∑' x : ℤ, ‖f x‖ ^ (2^(n+1))) = ∑ x ∈ S, ‖f x‖ ^ (2^(n+1)) :=
    tsum_eq_sum (s := S) (fun x hx => by
      have hfx : f x = 0 := by
        refine hsup x (fun hmem => ?_)
        exact hx (by rw [hSdef]; exact hmem)
      rw [hfx, norm_zero]
      exact zero_pow (by positivity : (2:ℕ)^(n+1) ≠ 0))
  have hcardpos : (0:ℝ) < (S.card : ℝ) := by
    have hmem : (0:ℤ) ∈ S := by
      rw [hSdef, diag_mem_symIcc]; simp
    have : 0 < S.card := Finset.card_pos.mpr ⟨0, hmem⟩
    exact_mod_cast this
  have hjensen : ((∑ x ∈ S, ‖f x‖ ^ 2) / (S.card : ℝ)) ^ (2^n)
      ≤ (∑ x ∈ S, ‖f x‖ ^ (2^(n+1))) / (S.card : ℝ) := by
    have hp := powMeanZ S (r := 2^n) (Nat.one_le_two_pow) (fun x => ‖f x‖ ^ 2)
      (fun x _ => sq_nonneg _)
    have hpow : ∀ x : ℤ, (‖f x‖ ^ 2) ^ (2^n) = ‖f x‖ ^ (2^(n+1)) := by
      intro x
      rw [← pow_mul]
      congr 1
      rw [← Nat.pow_succ']
    rw [Finset.sum_congr rfl (fun x _ => hpow x)] at hp
    rw [div_pow, div_le_div_iff₀ (pow_pos hcardpos _) hcardpos]
    rw [show (S.card : ℝ) ^ (2^n) = (S.card : ℝ) ^ (2^n - 1) * (S.card : ℝ) from by
      conv_lhs => rw [show (2:ℕ)^n = (2^n - 1) + 1 from (Nat.sub_add_cancel Nat.one_le_two_pow).symm]
      rw [pow_succ]]
    calc (∑ x ∈ S, ‖f x‖ ^ 2) ^ (2^n) * (S.card : ℝ)
        ≤ ((S.card : ℝ) ^ (2^n - 1) * ∑ x ∈ S, ‖f x‖ ^ (2^(n+1))) * (S.card : ℝ) :=
          mul_le_mul_of_nonneg_right hp (le_of_lt hcardpos)
      _ = (∑ x ∈ S, ‖f x‖ ^ (2^(n+1))) * ((S.card : ℝ) ^ (2^n - 1) * (S.card : ℝ)) := by
          ring
  have hmain' : (∏ i : Fin (n+1), ((Q i).card : ℝ)⁻¹)
      * ((∑ x ∈ S, ‖f x‖ ^ (2^(n+1))) / (S.card : ℝ)) ≤ boxNormPow (n+1) Q S f := by
    have h := hmain
    rw [htsum, hf_eq] at h
    exact h
  have hprod_nonneg : (0:ℝ) ≤ ∏ i : Fin (n+1), ((Q i).card : ℝ)⁻¹ :=
    Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  have hA_nonneg : (0:ℝ) ≤ (∑ x ∈ S, ‖f x‖ ^ 2) / (S.card : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (le_of_lt hcardpos)
  exact le_trans (mul_le_mul hcardb hjensen (pow_nonneg hA_nonneg _) hprod_nonneg) hmain'

end

end Work.Peluse.Peel
