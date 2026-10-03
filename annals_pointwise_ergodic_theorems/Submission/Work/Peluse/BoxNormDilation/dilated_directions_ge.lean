/-
# The dilation comparison for Peluse's box norms

For `t ≥ 2` and `m ≥ 2` there is `C > 0` such that for every `c ≠ 0`, every `L ≥ 1`, every window
`S` and every `1`-bounded finitely supported `f`,

`C * ‖f‖^{2^t}_{□^t_{(mc)[L]}(S)} ≤ ‖f‖^{2^t}_{□^t_{c[mL]}(S)}`,

i.e. the box-norm power with the *dilated* direction set `(mc)[L] = {mc, 2mc, …, Lmc}` is dominated
by the box-norm power with the *denser* direction set `c[mL] = {c, 2c, …, mLc}`.  (The two sets have
the same diameter `mLc`; the dilated one is the sublattice of step `mc`.)

## Proof

`t = 2` is the base case and is purely algebraic.  Expanding the level-`2` box norm in the
difference variables (`boxNormPow_two_eq`) writes it as

`|S|⁻¹|Q|⁻⁴ ∑_{a,b∈Q} ∑_x ‖∑_{k∈Q} f(x+a+k)·conj(f(x+b+k))‖²`,

and the inner double sum is monotone in the *outer* range `Q` (`pair_sum_mono`, proved by
re-expanding the quadruple sum and reading it in the other order).  Since `(mc)[L] ⊆ c[mL]`, taking
the outer range `Q = c[mL]` dominates `Q = (mc)[L]`, which gives the factor
`(|(mc)[L]|/|c[mL]|)⁴ = m⁻⁴`.

For `t > 2` we induct.  Peluse's recursion (`boxNormPow_succ_peel`, from
`Work.Peluse.Peel.boxSumPow_peel`) identifies the level-`(t+1)` box-norm power with the average, over
`h, h' ∈ Q`, of the level-`t` box-norm powers of the differences `Δ'_{h,h'} f = f(·+h)·conj(f(·+h'))`:

`‖f‖^{2^{t+1}}_{□^{t+1}_Q(S)} = |Q|⁻² ∑_{h,h'∈Q} ‖Δ'_{h,h'} f‖^{2^t}_{□^t_Q(S)}`.

All summands are nonnegative, so restricting the average to the dilated pair set `A` and applying
the induction hypothesis to each difference costs exactly the ratio `(|A|/|B|)²` with `A = (mc)[L]`,
`B = c[mL]`, i.e. `m⁻²`.  Iterating from `C₂ = m⁻⁴` gives `C_t = m^{-2t}`.

The window `S` enters only through global prefactors, so the estimate is uniform in `S`; the theorem
applies it with `S = symIcc N` and a function supported in `[-N,N]`.
-/
import Mathlib
import Submission.Work.Peluse.BoxNormDilation.boxNormPow_two_eq
import Submission.Work.Peluse.BoxNormDilation.pair_sum_mono

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.BoxNormDilation

noncomputable section

open Work.Peluse

lemma boxNormPow_nonneg (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    0 ≤ boxNormPow t Q S f := norm_nonneg _

/-! ## Cardinalities and inclusions of the arithmetic progressions `c[L]` -/

lemma card_arithIcc {c : ℤ} (hc : c ≠ 0) (L : ℕ) : (arithIcc c L).card = L := by
  rw [arithIcc, Finset.card_image_of_injOn]
  · simp
  · intro a _ b _ hab
    have : (a : ℤ) = (b : ℤ) := mul_left_cancel₀ hc hab
    exact_mod_cast this

lemma arithIcc_subset (m : ℕ) (hm : 1 ≤ m) (c : ℤ) (L : ℕ) :
    arithIcc (m * c) L ⊆ arithIcc c (m * L) := by
  intro x hx
  rw [arithIcc] at hx ⊢
  rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk2 : k ≤ L := (Finset.mem_Icc.mp hk).2
  exact Finset.mem_image.mpr
    ⟨m * k, Finset.mem_Icc.mpr
      ⟨by simpa using Nat.mul_le_mul hm hk1, Nat.mul_le_mul_left m hk2⟩,
      by push_cast; ring⟩

lemma mul_ne_zero_int {m : ℕ} {c : ℤ} (hm : m ≠ 0) (hc : c ≠ 0) : m * c ≠ 0 := by
  have : (m : ℤ) ≠ 0 := by exact_mod_cast hm
  exact mul_ne_zero this hc

/-! ## Peeling the box-norm power, in real form -/

private lemma finSuppZ_delta (f : ℤ → ℂ) (hf : FinSuppZ f) (h h' : ℤ) :
    FinSuppZ (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
  obtain ⟨N, hN⟩ := hf
  refine ⟨N + h.natAbs + h'.natAbs, fun u hu => ?_⟩
  by_cases h1 : f (u + h) = 0
  · simp [h1]
  by_cases h2 : f (u + h') = 0
  · simp [h2]
  exfalso
  have h1' : (u + h).natAbs ≤ N := by
    by_contra hc
    exact h1 (hN (u + h) (by omega))
  have habs : (u.natAbs : ℤ) ≤ ((u + h).natAbs : ℤ) + (h.natAbs : ℤ) := by
    have h3 : |u| ≤ |u + h| + |h| := by
      have h4 := abs_add_le (u + h) (-h)
      simpa [abs_neg] using h4
    rwa [Int.natCast_natAbs, Int.natCast_natAbs, Int.natCast_natAbs]
  have h1'' : ((u + h).natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast h1'
  have hh : (0 : ℤ) ≤ (h.natAbs : ℤ) := by positivity
  omega

/-- The level-`(t+1)` box-norm power is the average, over the pairs `h,h'` in the first direction
set, of the level-`t` box-norm powers of the differences `Δ'_{h,h'} f`. -/
lemma boxNormPow_succ_peel (t : ℕ) (ht : 1 ≤ t) (A S : Finset ℤ) {f : ℤ → ℂ}
    (hf : FinSuppZ f) :
    boxNormPow (t + 1) (fun _ : Fin (t + 1) => A) S f
      = ((A.card : ℝ))⁻¹ ^ 2 *
        ∑ h ∈ A, ∑ h' ∈ A,
          boxNormPow t (fun _ : Fin t => A) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
  have key : (((boxNormPow (t + 1) (fun _ : Fin (t + 1) => A) S f : ℝ)) : ℂ)
      = (((((A.card : ℝ))⁻¹ ^ 2 *
        ∑ h ∈ A, ∑ h' ∈ A,
          boxNormPow t (fun _ : Fin t => A) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))) : ℝ)) : ℂ) := by
    rw [← Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow (by omega) hf]
    rw [Work.Peluse.Peel.boxSumPow_peel]
    rw [Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ =>
      Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow ht (finSuppZ_delta f hf h h')))]
    push_cast
    ring
  exact Complex.ofReal_injective key

/-! ## The inductive statement -/

/-- `BoxP t m` is the dilation comparison at level `t`. -/
def BoxP (t : ℕ) (m : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (c : ℤ) (L : ℕ) (S : Finset ℤ) (f : ℤ → ℂ), c ≠ 0 → 1 ≤ L →
    (∀ x : ℤ, ‖f x‖ ≤ 1) → FinSuppZ f →
    C * boxNormPow t (fun _ : Fin t => arithIcc (m * c) L) S f
      ≤ boxNormPow t (fun _ : Fin t => arithIcc c (m * L)) S f

/-- The base case `t = 2`. -/
theorem boxP_two (m : ℕ) (hm : 2 ≤ m) : BoxP 2 m := by
  refine ⟨(((m : ℝ) ^ 4))⁻¹, by positivity, ?_⟩
  intro c L S f hc hL hf1 hf
  have hmc : m * c ≠ 0 := mul_ne_zero_int (by omega) hc
  have hAcard : ((arithIcc (m * c) L).card : ℝ) = (L : ℝ) := by
    rw [card_arithIcc hmc L]
  have hBcard : ((arithIcc c (m * L)).card : ℝ) = (m : ℝ) * (L : ℝ) := by
    rw [card_arithIcc hc (m * L)]
    push_cast
    ring
  have hsub : arithIcc (m * c) L ⊆ arithIcc c (m * L) := arithIcc_subset m (by omega) c L
  rw [boxNormPow_two_eq (arithIcc (m * c) L) S hf,
    boxNormPow_two_eq (arithIcc c (m * L)) S hf]
  set SA : ℝ := ∑ a ∈ arithIcc (m * c) L, ∑ b ∈ arithIcc (m * c) L, ∑' x : ℤ,
      ‖∑ k ∈ arithIcc (m * c) L, f (x + a + k) * star (f (x + b + k))‖ ^ 2 with hSA
  set SB : ℝ := ∑ a ∈ arithIcc c (m * L), ∑ b ∈ arithIcc c (m * L), ∑' x : ℤ,
      ‖∑ k ∈ arithIcc c (m * L), f (x + a + k) * star (f (x + b + k))‖ ^ 2 with hSB
  have hSAleSB : SA ≤ SB := by
    have h1 : SA ≤ ∑ a ∈ arithIcc (m * c) L, ∑ b ∈ arithIcc (m * c) L, ∑' x : ℤ,
        ‖∑ k ∈ arithIcc c (m * L), f (x + a + k) * star (f (x + b + k))‖ ^ 2 := by
      rw [hSA]
      exact pair_sum_mono hsub hf
    have hi : ∀ a : ℤ, (∑ b ∈ arithIcc (m * c) L, ∑' x : ℤ,
        ‖∑ k ∈ arithIcc c (m * L), f (x + a + k) * star (f (x + b + k))‖ ^ 2) ≤
        (∑ b ∈ arithIcc c (m * L), ∑' x : ℤ,
        ‖∑ k ∈ arithIcc c (m * L), f (x + a + k) * star (f (x + b + k))‖ ^ 2) := fun a =>
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ =>
        tsum_nonneg fun x => by positivity)
    have ho : (∑ a ∈ arithIcc (m * c) L, ∑ b ∈ arithIcc (m * c) L, ∑' x : ℤ,
        ‖∑ k ∈ arithIcc c (m * L), f (x + a + k) * star (f (x + b + k))‖ ^ 2) ≤
        (∑ a ∈ arithIcc (m * c) L, ∑ b ∈ arithIcc c (m * L), ∑' x : ℤ,
        ‖∑ k ∈ arithIcc c (m * L), f (x + a + k) * star (f (x + b + k))‖ ^ 2) :=
      Finset.sum_le_sum (fun a _ => hi a)
    have ho2 : (∑ a ∈ arithIcc (m * c) L, ∑ b ∈ arithIcc c (m * L), ∑' x : ℤ,
        ‖∑ k ∈ arithIcc c (m * L), f (x + a + k) * star (f (x + b + k))‖ ^ 2) ≤ SB := by
      rw [hSB]
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ =>
        Finset.sum_nonneg (fun b _ => tsum_nonneg fun x => by positivity))
    linarith
  have hBrel : ((arithIcc c (m * L)).card : ℝ) = (m : ℝ) * ((arithIcc (m * c) L).card : ℝ) := by
    rw [hAcard, hBcard]
  have hcoef : ((m : ℝ) ^ 4)⁻¹ * ((((arithIcc (m * c) L).card : ℝ))⁻¹ ^ 4)
      = (((arithIcc c (m * L)).card : ℝ))⁻¹ ^ 4 := by
    rw [hBrel, mul_inv, inv_pow]
    ring
  have hnn : (0 : ℝ) ≤ (((m : ℝ) ^ 4)⁻¹ *
      (((S.card : ℝ))⁻¹ * (((arithIcc (m * c) L).card : ℝ))⁻¹ ^ 4)) := by positivity
  calc ((m : ℝ) ^ 4)⁻¹ * (((S.card : ℝ))⁻¹ * (((arithIcc (m * c) L).card : ℝ))⁻¹ ^ 4 * SA)
      = (((m : ℝ) ^ 4)⁻¹ *
          (((S.card : ℝ))⁻¹ * (((arithIcc (m * c) L).card : ℝ))⁻¹ ^ 4)) * SA := by ring
    _ ≤ (((m : ℝ) ^ 4)⁻¹ *
          (((S.card : ℝ))⁻¹ * (((arithIcc (m * c) L).card : ℝ))⁻¹ ^ 4)) * SB :=
        mul_le_mul_of_nonneg_left hSAleSB hnn
    _ = ((S.card : ℝ))⁻¹ * (((arithIcc c (m * L)).card : ℝ))⁻¹ ^ 4 * SB := by
        rw [← hcoef]
        ring

/-- The induction step. -/
theorem boxP_succ (m : ℕ) (hm : 2 ≤ m) (t : ℕ) (ht : 2 ≤ t) (h : BoxP t m) :
    BoxP (t + 1) m := by
  obtain ⟨C, hC, hP⟩ := h
  refine ⟨C / (m : ℝ) ^ 2, by positivity, ?_⟩
  intro c L S f hc hL hf1 hf
  have hmc : m * c ≠ 0 := mul_ne_zero_int (by omega) hc
  have hAcard : ((arithIcc (m * c) L).card : ℝ) = (L : ℝ) := by
    rw [card_arithIcc hmc L]
  have hBcard : ((arithIcc c (m * L)).card : ℝ) = (m : ℝ) * (L : ℝ) := by
    rw [card_arithIcc hc (m * L)]
    push_cast
    ring
  have hsub : arithIcc (m * c) L ⊆ arithIcc c (m * L) := arithIcc_subset m (by omega) c L
  have hbdd : ∀ h h' : ℤ, ∀ u : ℤ, ‖f (u + h) * star (f (u + h'))‖ ≤ 1 := by
    intro h h' u
    rw [norm_mul, norm_star]
    calc ‖f (u + h)‖ * ‖f (u + h')‖ ≤ 1 * 1 :=
          mul_le_mul (hf1 _) (hf1 _) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  rw [boxNormPow_succ_peel t (by omega) (arithIcc (m * c) L) S hf,
    boxNormPow_succ_peel t (by omega) (arithIcc c (m * L)) S hf]
  set SA : ℝ := ∑ h ∈ arithIcc (m * c) L, ∑ h' ∈ arithIcc (m * c) L,
      boxNormPow t (fun _ : Fin t => arithIcc (m * c) L) S
        (fun u : ℤ => f (u + h) * star (f (u + h'))) with hSA
  set SB : ℝ := ∑ h ∈ arithIcc c (m * L), ∑ h' ∈ arithIcc c (m * L),
      boxNormPow t (fun _ : Fin t => arithIcc c (m * L)) S
        (fun u : ℤ => f (u + h) * star (f (u + h'))) with hSB
  have hstep2 : (∑ h ∈ arithIcc (m * c) L, ∑ h' ∈ arithIcc (m * c) L,
      boxNormPow t (fun _ : Fin t => arithIcc c (m * L)) S
        (fun u : ℤ => f (u + h) * star (f (u + h'))) ≤ SB) := by
    have hi : ∀ h : ℤ, (∑ h' ∈ arithIcc (m * c) L,
        boxNormPow t (fun _ : Fin t => arithIcc c (m * L)) S
          (fun u : ℤ => f (u + h) * star (f (u + h')))) ≤
        (∑ h' ∈ arithIcc c (m * L),
        boxNormPow t (fun _ : Fin t => arithIcc c (m * L)) S
          (fun u : ℤ => f (u + h) * star (f (u + h')))) := fun h =>
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun h' _ _ =>
        boxNormPow_nonneg t (fun _ : Fin t => arithIcc c (m * L)) S _)
    have ho : (∑ h ∈ arithIcc (m * c) L, ∑ h' ∈ arithIcc (m * c) L,
        boxNormPow t (fun _ : Fin t => arithIcc c (m * L)) S
          (fun u : ℤ => f (u + h) * star (f (u + h')))) ≤
        (∑ h ∈ arithIcc (m * c) L, ∑ h' ∈ arithIcc c (m * L),
        boxNormPow t (fun _ : Fin t => arithIcc c (m * L)) S
          (fun u : ℤ => f (u + h) * star (f (u + h')))) :=
      Finset.sum_le_sum (fun h _ => hi h)
    have ho2 : (∑ h ∈ arithIcc (m * c) L, ∑ h' ∈ arithIcc c (m * L),
        boxNormPow t (fun _ : Fin t => arithIcc c (m * L)) S
          (fun u : ℤ => f (u + h) * star (f (u + h')))) ≤ SB := by
      rw [hSB]
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun h _ _ =>
        Finset.sum_nonneg (fun h' _ =>
          boxNormPow_nonneg t (fun _ : Fin t => arithIcc c (m * L)) S _))
    linarith
  have hstep3 : (∑ h ∈ arithIcc (m * c) L, ∑ h' ∈ arithIcc (m * c) L,
      C * boxNormPow t (fun _ : Fin t => arithIcc (m * c) L) S
        (fun u : ℤ => f (u + h) * star (f (u + h')))
      ≤ ∑ h ∈ arithIcc (m * c) L, ∑ h' ∈ arithIcc (m * c) L,
      boxNormPow t (fun _ : Fin t => arithIcc c (m * L)) S
        (fun u : ℤ => f (u + h) * star (f (u + h')))) := by
    refine Finset.sum_le_sum (fun h _ => Finset.sum_le_sum (fun h' _ => ?_))
    exact hP c L S (fun u : ℤ => f (u + h) * star (f (u + h'))) hc hL (hbdd h h')
      (finSuppZ_delta f hf h h')
  have hCSA : C * SA ≤ SB := by
    have he : C * SA = ∑ h ∈ arithIcc (m * c) L, ∑ h' ∈ arithIcc (m * c) L,
        C * boxNormPow t (fun _ : Fin t => arithIcc (m * c) L) S
          (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
      rw [hSA, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun h _ => Finset.mul_sum _ _ _)
    rw [he]
    exact le_trans hstep3 hstep2
  have hBrel : ((arithIcc c (m * L)).card : ℝ) = (m : ℝ) * ((arithIcc (m * c) L).card : ℝ) := by
    rw [hAcard, hBcard]
  have hcoef : (C / (m : ℝ) ^ 2) * ((((arithIcc (m * c) L).card : ℝ))⁻¹ ^ 2)
      = C * ((((arithIcc c (m * L)).card : ℝ))⁻¹ ^ 2) := by
    rw [hBrel, mul_inv, inv_pow]
    ring
  calc C / (m : ℝ) ^ 2 *
        ((((arithIcc (m * c) L).card : ℝ))⁻¹ ^ 2 * SA)
      = ((C / (m : ℝ) ^ 2) * ((((arithIcc (m * c) L).card : ℝ))⁻¹ ^ 2)) * SA := by ring
    _ = (C * ((((arithIcc c (m * L)).card : ℝ))⁻¹ ^ 2)) * SA := by rw [hcoef]
    _ = (((arithIcc c (m * L)).card : ℝ))⁻¹ ^ 2 * (C * SA) := by ring
    _ ≤ (((arithIcc c (m * L)).card : ℝ))⁻¹ ^ 2 * SB :=
        mul_le_mul_of_nonneg_left hCSA (by positivity)

/-- `BoxP t m` holds for all `t ≥ 2`. -/
theorem boxP_of_le (m : ℕ) (hm : 2 ≤ m) : ∀ n : ℕ, BoxP (n + 2) m := by
  intro n
  induction n with
  | zero => simpa using boxP_two m hm
  | succ n ih =>
      have h := boxP_succ m hm (n + 2) (by omega) ih
      have heq : n + 1 + 2 = (n + 2) + 1 := by omega
      rwa [heq]

/-- **The dilation comparison for Peluse's box norms.** -/
theorem dilated_directions_ge {t : ℕ} (ht : 2 ≤ t) (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℤ) (L N : ℕ) (f : ℤ → ℂ), c ≠ 0 → 1 ≤ L →
      (∀ x : ℤ, ‖f x‖ ≤ 1) → Work.Peluse.SupportIn f N →
      C * Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc (m * c) L)
            (Work.Peluse.symIcc N) f
        ≤ Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc c (m * L))
            (Work.Peluse.symIcc N) f := by
  obtain ⟨C, hC, hP⟩ := boxP_of_le m hm (t - 2)
  have ht' : t - 2 + 2 = t := by omega
  rw [ht'] at hP
  exact ⟨C, hC, fun c L N f hc hL hf1 hfN =>
    hP c L (symIcc N) f hc hL hf1 (FinSuppZ.of_supportIn hfN)⟩

end

end Work.Peluse.BoxNormDilation
