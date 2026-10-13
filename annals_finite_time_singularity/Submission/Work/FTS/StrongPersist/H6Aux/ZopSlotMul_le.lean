import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop
import Submission.Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux

/-!
# The slot-product estimate for the radial multiplier `D_z = z ∂_z`

For two functions `φ, u : ℝ → ℝ` that are `C⁶` on `(0,∞)`, with the `DzdIter`-iterates of `φ`
up to order `6` bounded by `K`, and every `z > 0`, the weighted slot sum of the product
`φ·u` is bounded by a universal constant times `(1+K)²` times the weighted slot sum of `u`:

    `∑_{q ≤ 6} (D_z^q (φu)(z))² w(z)² ≤ C (1+K)² ∑_{q ≤ 6} (D_z^q u(z))² w(z)²`.

The proof is the one-variable Leibniz rule `dzdIter_mul_leibniz` for `DzdIter = (z∂_z)^q`
(which needs only the differentiability of the iterates, available from `C⁶`), followed by the
Cauchy–Schwarz binomial estimate `binom_sum_sq_le` and a triangle inequality over the seven
slots.  No weight is ever estimated: the factor `w(z)²` is common to all slots and is only
carried along.
-/

set_option autoImplicit false

/-! ## Smoothness of the `DzdIter`s of a `C^n` function of `z` alone -/

/-- `Dzd = z ∂_z` lowers the smoothness order by one on the open half-line. -/
private lemma contDiffOn_dzd_of_succ {u : ℝ → ℝ} {m : ℕ}
    (hu : ContDiffOn ℝ (m + 1) u (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ m (Work.Elliptic.Dzd u) (Set.Ioi (0 : ℝ)) := by
  have hd : ContDiffOn ℝ m (deriv u) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.CoercivityFix.Transfer.E1Parts.contDiffOn_deriv_of_succ hu
  show ContDiffOn ℝ m (fun z => z * deriv u z) (Set.Ioi (0 : ℝ))
  simpa only [id_eq] using
    (contDiffOn_id (𝕜 := ℝ) (n := (m : WithTop ℕ∞)) (s := Set.Ioi (0 : ℝ))).mul hd

/-- The iterates of `Dzd = z ∂_z` lose one smoothness order each: a `C^n` function has
`C^{n-b}` `Dzd`-iterates of order `b` on `(0,∞)`. -/
private lemma contDiffOn_dzdIter_of_contDiffOn {u : ℝ → ℝ} {n : ℕ}
    (hu : ContDiffOn ℝ n u (Set.Ioi (0 : ℝ))) :
    ∀ b : ℕ, b ≤ n →
      ContDiffOn ℝ (((n - b : ℕ) : WithTop ℕ∞)) (Work.Elliptic.DzdIter b u)
        (Set.Ioi (0 : ℝ)) := by
  intro b
  induction b with
  | zero => intro _; simpa using hu
  | succ b ih =>
      intro hb
      have hb' : b ≤ n := by omega
      have hle : 1 ≤ n - b := by omega
      have hprev : ContDiffOn ℝ (((n - b : ℕ) : WithTop ℕ∞)) (Work.Elliptic.DzdIter b u)
          (Set.Ioi (0 : ℝ)) := ih hb'
      have hprev' : ContDiffOn ℝ (((n - b - 1 + 1 : ℕ) : WithTop ℕ∞))
          (Work.Elliptic.DzdIter b u) (Set.Ioi (0 : ℝ)) := by
        rwa [Nat.sub_add_cancel hle]
      have hstep : ContDiffOn ℝ (((n - b - 1 : ℕ) : WithTop ℕ∞))
          (Work.Elliptic.Dzd (Work.Elliptic.DzdIter b u)) (Set.Ioi (0 : ℝ)) :=
        contDiffOn_dzd_of_succ (u := Work.Elliptic.DzdIter b u) (m := n - b - 1) hprev'
      rw [Work.Elliptic.DzdIter_succ, Nat.sub_succ]
      exact hstep

/-- Differentiability of the `Dzd`-iterates of a `C^n` function of `z` alone. -/
private lemma differentiableAt_dzdIter_of_contDiffOn {u : ℝ → ℝ} {n : ℕ}
    (hu : ContDiffOn ℝ n u (Set.Ioi (0 : ℝ))) {b : ℕ} (hb : b + 1 ≤ n) {z : ℝ}
    (hz : 0 < z) : DifferentiableAt ℝ (Work.Elliptic.DzdIter b u) z := by
  have h := contDiffOn_dzdIter_of_contDiffOn hu b (by omega)
  have hne : (((n - b : ℕ)) : WithTop ℕ∞) ≠ 0 := by
    have hb0 : (n - b : ℕ) ≠ 0 := by omega
    exact_mod_cast hb0
  exact (h.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)

/-- The binomial coefficients `C(i,b)` for `i ≤ 6` are bounded by `2⁶ = 64`. -/
private lemma choose_cast_abs_le (i b : ℕ) (hi : i ≤ 6) :
    |((i.choose b : ℕ) : ℝ)| ≤ 64 := by
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  have h1 : i.choose b ≤ 64 := by
    have h26 : (2 : ℕ) ^ 6 = 64 := by norm_num
    have := Nat.choose_le_two_pow i b
    have := Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hi
    omega
  exact_mod_cast h1

/-! ## The estimate -/

theorem ZopSlotMul_le : ∃ C : ℝ, 0 < C ∧ ∀ (φ u : ℝ → ℝ) (K : ℝ), 0 ≤ K →
    (∀ j ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Elliptic.DzdIter j φ z| ≤ K) →
    ContDiffOn ℝ 6 φ (Set.Ioi (0 : ℝ)) → ContDiffOn ℝ 6 u (Set.Ioi (0 : ℝ)) →
    ∀ z ∈ Set.Ioi (0 : ℝ),
      (∑ q ∈ Finset.range 7,
          (Work.Elliptic.DzdIter q (fun z' => φ z' * u z') z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ C * (1 + K) ^ 2 * (∑ q ∈ Finset.range 7,
            (Work.Elliptic.DzdIter q u z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  refine ⟨2000000, by norm_num, ?_⟩
  intro φ u K hK hφb hφ hu z hz
  set W : ℝ := (Work.Spaces.w z) ^ 2 with hWdef
  set S : ℝ := ∑ k ∈ Finset.range 7, (Work.Elliptic.DzdIter k u z) ^ 2 * W with hS
  have hW : 0 ≤ W := by rw [hWdef]; exact sq_nonneg _
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (sq_nonneg _) hW)
  -- the per-slot bound
  have hterm : ∀ q ≤ 6,
      (Work.Elliptic.DzdIter q (fun z' => φ z' * u z') z) ^ 2 * W ≤ 200704 * K ^ 2 * S := by
    intro q hq
    -- Leibniz
    have hleib := Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz q φ u
      (fun b hb z' hz' =>
        differentiableAt_dzdIter_of_contDiffOn (n := 6) hφ (b := b) (by omega) hz')
      (fun b hb z' hz' =>
        differentiableAt_dzdIter_of_contDiffOn (n := 6) hu (b := b) (by omega) hz') z hz
    -- Cauchy–Schwarz on the binomial sum
    have hcs := Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le (i := q) (D := 64) (K := K) hK
      (x := fun b => Work.Elliptic.DzdIter b φ z)
      (y := fun m => Work.Elliptic.DzdIter m u z)
      (fun b hb => hφb b (by omega) z hz)
      (fun b hb => choose_cast_abs_le q b hq)
    -- shrink the two factors of `hcs`
    have hq7 : ((q : ℝ) + 1) ≤ 7 := by
      have : q ≤ 6 := hq
      exact_mod_cast (by omega : q + 1 ≤ 7)
    have hfac : ((q : ℝ) + 1) * 64 * K ≤ 448 * K := by
      have h64 : ((q : ℝ) + 1) * 64 ≤ 448 := by
        nlinarith [hq7]
      nlinarith [h64, hK]
    have hfac2 : (((q : ℝ) + 1) * 64 * K) ^ 2 ≤ (448 * K) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hfac 2
    have hsum_le : ∑ m ∈ Finset.range (q + 1), (Work.Elliptic.DzdIter m u z) ^ 2
        ≤ ∑ m ∈ Finset.range 7, (Work.Elliptic.DzdIter m u z) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun m hm => Finset.mem_range.mpr (by
          have := Finset.mem_range.mp hm
          omega))
        (fun m _ _ => sq_nonneg _)
    have hstep : (∑ b ∈ Finset.range (q + 1),
          ((q.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b φ z
            * Work.Elliptic.DzdIter (q - b) u z)) ^ 2
        ≤ (448 * K) ^ 2 * (∑ m ∈ Finset.range 7, (Work.Elliptic.DzdIter m u z) ^ 2) := by
      refine hcs.trans ?_
      refine mul_le_mul hfac2 hsum_le (Finset.sum_nonneg fun m _ => sq_nonneg _)
        (sq_nonneg (448 * K))
    -- multiply by the weight
    have hSW : (∑ m ∈ Finset.range 7, (Work.Elliptic.DzdIter m u z) ^ 2) * W = S := by
      rw [hS, Finset.sum_mul]
    calc (Work.Elliptic.DzdIter q (fun z' => φ z' * u z') z) ^ 2 * W
        = (∑ b ∈ Finset.range (q + 1),
            ((q.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b φ z
              * Work.Elliptic.DzdIter (q - b) u z)) ^ 2 * W := by rw [hleib]
      _ ≤ ((448 * K) ^ 2 * (∑ m ∈ Finset.range 7, (Work.Elliptic.DzdIter m u z) ^ 2)) * W :=
          mul_le_mul_of_nonneg_right hstep hW
      _ = (448 * K) ^ 2 * ((∑ m ∈ Finset.range 7, (Work.Elliptic.DzdIter m u z) ^ 2) * W) := by
          ring
      _ = (448 * K) ^ 2 * S := by rw [hSW]
      _ = 200704 * K ^ 2 * S := by ring
  -- sum the seven slots
  calc ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' => φ z' * u z') z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ ∑ _q ∈ Finset.range 7, 200704 * K ^ 2 * S :=
        Finset.sum_le_sum (fun q hq => hterm q (by
          have := Finset.mem_range.mp hq
          omega))
    _ = 7 * (200704 * K ^ 2 * S) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ = 1404928 * K ^ 2 * S := by ring
    _ ≤ 2000000 * (1 + K) ^ 2 * S := by
        have hKsq : K ^ 2 ≤ (1 + K) ^ 2 := by nlinarith [hK]
        have h2 : 1404928 * K ^ 2 ≤ 2000000 * (1 + K) ^ 2 :=
          mul_le_mul (by norm_num) hKsq (sq_nonneg K) (by norm_num)
        exact mul_le_mul_of_nonneg_right h2 hSnn

end Work.FTS.StrongPersist.H6Aux
