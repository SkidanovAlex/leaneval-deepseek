import Mathlib
import Submission.Work.Peluse.WindowControl.boxNormPow_one_window

/-!
# The squared mean is bounded by the first box-norm power

For `f` supported in the symmetric window `S = symIcc N = [-N,N]` and for a slot set
`Q = arithIcc q L = {q, 2q, …, Lq}` all of whose elements have absolute value `≤ N`, the square of
the mean `|S|⁻¹ ∑_{x ∈ S} f x` is bounded by twice the first box-norm power over `Q` and `S`:

  `‖ |S|⁻¹ ∑_{x ∈ S} f x ‖² / 2 ≤ ‖f‖^{2}_{□¹_Q(S)}`.

## Proof

`boxNormPow_one_window` evaluates the level-one box-norm power as

  `‖f‖^{2}_{□¹_Q(S)} = |S|⁻¹ · |Q|⁻² · ∑_{x ∈ [-2N,2N]} ‖∑_{a ∈ Q} f (x+a)‖²`.

The `x`-sum runs over `4N+1 ≤ 2·|S|` points; Cauchy–Schwarz in squared form gives

  `∑_x ‖∑_a f (x+a)‖² ≥ ‖∑_x ∑_a f (x+a)‖² / (4N+1)`,

and since every `a ∈ Q` has `|a| ≤ N`, the inner sum over the window `[-2N,2N]` telescopes to the
full sum over `S`: `∑_{x ∈ [-2N,2N]} f (x+a) = ∑_{x ∈ S} f x`.  Hence

  `∑_x ∑_a f (x+a) = |Q| · ∑_{x ∈ S} f x`,

and the two `|Q|`-powers cancel, leaving `|S|⁻¹·|Q|⁻¹²·|Q|² = |S|⁻¹` and the numerical factor
`(4N+1)/2 ≤ |S| = 2N+1`.
-/

set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.Prop36SW

private lemma mem_symIcc_iff {N : ℕ} {x : ℤ} : x ∈ Work.Peluse.symIcc N ↔ x.natAbs ≤ N := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · intro h
    have h1 : |x| ≤ (N : ℤ) := abs_le.mpr h
    rw [← Int.natCast_natAbs] at h1
    exact_mod_cast h1
  · intro hx
    have h1 : (x.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hx
    rw [Int.natCast_natAbs] at h1
    exact abs_le.mp h1

private lemma card_symIcc' (L : ℕ) : (Work.Peluse.symIcc L).card = 2 * L + 1 := by
  rw [Work.Peluse.symIcc, Int.card_Icc]
  have h : (L : ℤ) + 1 - (-(L : ℤ)) = ((2 * L + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- Cauchy–Schwarz in squared form: `‖∑ v‖² ≤ |s| · ∑ ‖v‖²`. -/
private lemma norm_sum_sq_le_card_mul {ι : Type*} (s : Finset ι) (v : ι → ℂ) :
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, v i‖ ≤ ∑ i ∈ s, ‖v i‖ := norm_sum_le s v
  have h2 : (∑ i ∈ s, ‖v i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  exact le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2

/-- For `f` supported in `[-N,N]` and `|a| ≤ N`, the translated sum over the larger window
`[-2N,2N]` is the full sum over `[-N,N]`. -/
private lemma sum_shift_eq_sum_symIcc (N : ℕ) (a : ℤ) (ha : |a| ≤ (N : ℤ)) (f : ℤ → ℂ)
    (hsupp : Work.Peluse.SupportIn f N) :
    ∑ x ∈ Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)), f (x + a)
      = ∑ x ∈ Work.Peluse.symIcc N, f x := by
  classical
  set T : Finset ℤ := Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)) with hT
  have hinj : Set.InjOn (fun x : ℤ => x + a) ↑T := fun x _ y _ h => add_right_cancel h
  rw [← Finset.sum_image hinj]
  refine (Finset.sum_subset ?hsub ?hvan).symm
  · intro y hy
    rw [Finset.mem_image]
    refine ⟨y - a, ?_, ?_⟩
    · rw [hT, Finset.mem_Icc]
      have hy' := mem_symIcc_iff.mp hy
      have ha' := abs_le.mp ha
      constructor <;> omega
    · ring
  · intro y hyimg hyS
    rw [Finset.mem_image] at hyimg
    have h1 : ¬ (y.natAbs ≤ N) := fun h => hyS (mem_symIcc_iff.mpr h)
    exact hsupp y (by omega)

/-- The numerical core: with `cT ≤ 2 cS` and `cQ² An² ≤ cT M`, the normalised mean square is
dominated by `cS⁻¹ cQ⁻¹² M`. -/
private lemma arith_key (cS cQ cT An M : ℝ) (hS : 0 < cS) (hQ : 0 < cQ) (hM : 0 ≤ M)
    (hT2S : cT ≤ 2 * cS) (hMQ : cQ ^ 2 * An ^ 2 ≤ cT * M) :
    (cS⁻¹) ^ 2 * An ^ 2 / 2 ≤ cS⁻¹ * cQ⁻¹ ^ 2 * M := by
  have hmain : cQ ^ 2 * An ^ 2 ≤ 2 * cS * M := by
    calc cQ ^ 2 * An ^ 2 ≤ cT * M := hMQ
      _ ≤ (2 * cS) * M := mul_le_mul_of_nonneg_right hT2S hM
      _ = 2 * cS * M := by ring
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  field_simp
  linarith

theorem meanSq_le_boxNormPow_one (q : ℤ) (L N : ℕ) (f : ℤ → ℂ)
    (hL : 1 ≤ L)
    (hfit : ∀ v ∈ Work.Peluse.arithIcc q L, |v| ≤ (N : ℤ))
    (hsupp : Work.Peluse.SupportIn f N) :
    ‖(((Work.Peluse.symIcc N).card : ℂ))⁻¹ * ∑ x ∈ Work.Peluse.symIcc N, f x‖ ^ 2 / 2
      ≤ Work.Peluse.uNormPow 1 (Work.Peluse.arithIcc q L) (Work.Peluse.symIcc N) f := by
  classical
  set Q : Finset ℤ := Work.Peluse.arithIcc q L with hQ
  set S : Finset ℤ := Work.Peluse.symIcc N with hS
  set T : Finset ℤ := Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)) with hT
  set A : ℂ := ∑ x ∈ S, f x with hA
  have hfit' : ∀ v ∈ Q, |v| ≤ (N : ℤ) := hfit
  -- the level-one window form of the box norm
  have hwin := Work.Peluse.WindowControl.boxNormPow_one_window Q S f hfit' hsupp
  -- `Q` is nonempty because `L ≥ 1`
  have hQmem : (q * 1 : ℤ) ∈ Q := by
    rw [hQ]; exact Finset.mem_image.mpr ⟨1, by simp [hL], by ring⟩
  have hQpos : 0 < Q.card := Finset.card_pos.mpr ⟨_, hQmem⟩
  -- cardinality of the two windows
  have hSval : (S.card : ℝ) = 2 * (N : ℝ) + 1 := by
    rw [hS, card_symIcc']; push_cast; ring
  have hTval : (T.card : ℝ) = 4 * (N : ℝ) + 1 := by
    rw [hT, Int.card_Icc]
    have h : (2 * (N : ℤ) + 1 - -(2 * (N : ℤ))) = ((4 * N + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h, Int.toNat_natCast]; push_cast; ring
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by rw [hSval]; positivity
  have hT2S : (T.card : ℝ) ≤ 2 * (S.card : ℝ) := by rw [hTval, hSval]; linarith
  -- the translated sums telescope
  have hshift : ∀ a ∈ Q, ∑ x ∈ T, f (x + a) = A := by
    intro a ha
    rw [hA, hS, hT]
    exact sum_shift_eq_sum_symIcc N a (hfit a ha) f hsupp
  have hsum : ∑ x ∈ T, ∑ a ∈ Q, f (x + a) = (Q.card : ℂ) * A := by
    calc ∑ x ∈ T, ∑ a ∈ Q, f (x + a)
        = ∑ a ∈ Q, ∑ x ∈ T, f (x + a) := Finset.sum_comm
      _ = ∑ a ∈ Q, A := Finset.sum_congr rfl hshift
      _ = (Q.card : ℂ) * A := by rw [Finset.sum_const, nsmul_eq_mul]
  -- Cauchy–Schwarz
  have hCS := norm_sum_sq_le_card_mul T (fun x => ∑ a ∈ Q, f (x + a))
  have hnorm : ‖∑ x ∈ T, ∑ a ∈ Q, f (x + a)‖ = (Q.card : ℝ) * ‖A‖ := by
    rw [hsum, norm_mul, Complex.norm_natCast]
  have hMQ : ((Q.card : ℝ)) ^ 2 * ‖A‖ ^ 2
      ≤ (T.card : ℝ) * ∑ x ∈ T, ‖∑ a ∈ Q, f (x + a)‖ ^ 2 := by
    calc ((Q.card : ℝ)) ^ 2 * ‖A‖ ^ 2
        = ‖∑ x ∈ T, ∑ a ∈ Q, f (x + a)‖ ^ 2 := by rw [hnorm]; ring
      _ ≤ (T.card : ℝ) * ∑ x ∈ T, ‖∑ a ∈ Q, f (x + a)‖ ^ 2 := hCS
  have hkey := arith_key ((S.card : ℝ)) ((Q.card : ℝ)) ((T.card : ℝ)) ‖A‖
      (∑ x ∈ T, ‖∑ a ∈ Q, f (x + a)‖ ^ 2) hSpos (by exact_mod_cast hQpos) (by positivity) hT2S hMQ
  have hLHS : ‖((S.card : ℂ))⁻¹ * A‖ ^ 2 / 2 = ((S.card : ℝ))⁻¹ ^ 2 * ‖A‖ ^ 2 / 2 := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]; ring
  have hgoal : ‖((S.card : ℂ))⁻¹ * A‖ ^ 2 / 2
      ≤ Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Q) S f := by
    rw [hLHS, hwin]
    exact hkey
  simpa [hS, hQ, hA, Work.Peluse.uNormPow] using hgoal

end Work.Prop36SW
