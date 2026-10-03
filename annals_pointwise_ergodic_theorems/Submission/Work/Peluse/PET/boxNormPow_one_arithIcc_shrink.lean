import Mathlib
import Submission.Work.Peluse.Peel.boxNormPow_one_tsum
import Submission.Work.Peluse.Peel.windowSum_block_le
import Submission.Work.Peluse.Peel.arithIcc_sum_window_eq

set_option linter.unusedVariables false

namespace Work.Peluse.PET

noncomputable section

open scoped BigOperators

/-! ## Auxiliary lemmas about the arithmetic-progression shift set

These are the (public) specialisations of the interface lemmas of
`Submission.Work.Peluse.Peel.boxNormPow_one_tsum`, `…windowSum_block_le` and
`…arithIcc_sum_window_eq` to the real-valued nonnegative function
`g = fun x => ((a x : ℝ) : ℂ)` of the requested statement. -/

/-- For `d ≠ 0` the arithmetic progression `d[L] = arithIcc d L` has exactly `L` elements. -/
private lemma card_arithIcc {d : ℤ} (hd : d ≠ 0) (L : ℕ) :
    (Work.Peluse.arithIcc d L).card = L := by
  rw [Work.Peluse.arithIcc, Finset.card_image_of_injOn (Work.Peluse.Peel.injOn_arithIcc hd),
    Nat.card_Icc]
  omega

/-- For `d = 0` and `1 ≤ L` the arithmetic progression collapses to `{0}`. -/
private lemma arithIcc_zero {L : ℕ} (hL : 1 ≤ L) :
    Work.Peluse.arithIcc (0 : ℤ) L = ({0} : Finset ℤ) := by
  ext x
  simp only [Work.Peluse.arithIcc, Finset.mem_image, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨y, _, rfl⟩; ring
  · intro hx; exact ⟨1, ⟨le_refl 1, hL⟩, by rw [hx]; ring⟩

/-- **The window sum of the shift set, for nonnegative real functions.**  With
`g = fun x => ((a x : ℝ) : ℂ)`, `a ≥ 0` and `d ≠ 0`, the norm of the complex sum over the shift
set `d[L]` is the corresponding sum of the real values of `a`. -/
private lemma window_norm_sum {d : ℤ} (hd : d ≠ 0) {a : ℤ → ℝ} (ha : ∀ x, 0 ≤ a x)
    {g : ℤ → ℂ} (hg : ∀ z, g z = ((a z : ℝ) : ℂ)) (x : ℤ) (L : ℕ) :
    ‖∑ c ∈ Work.Peluse.arithIcc d L, g (x + c)‖ = ∑ y ∈ Finset.Icc 1 L, a (x + d * (y : ℤ)) := by
  rw [Work.Peluse.arithIcc, Finset.sum_image (Work.Peluse.Peel.injOn_arithIcc hd)]
  have hsum : (∑ y ∈ Finset.Icc 1 L, g (x + d * (y : ℤ)))
      = ∑ y ∈ Finset.Icc 1 L, (((a (x + d * (y : ℤ)) : ℝ)) : ℂ) :=
    Finset.sum_congr rfl fun y _ => hg _
  rw [hsum]
  exact Work.Peluse.Peel.norm_ofReal_sum_eq _ _ (fun i _ => ha _)

/-- **The level-one box-norm power along an arithmetic progression, for nonnegative real
functions.**  For `d ≠ 0`, `1 ≤ L` and `g = fun x => ((a x : ℝ) : ℂ)` with `a ≥ 0` and
`a` supported in `[-N,N]`,

  `boxNormPow 1 (fun _ => d[L]) [-N,N] g = (2N+1)⁻¹ L⁻² ∑_x (∑_{y ∈ [1,L]} a (x + d y))²`. -/
private lemma boxNormPow_one_arithIcc_eq {N L : ℕ} (hL : 1 ≤ L) {d : ℤ} (hd : d ≠ 0)
    {a : ℤ → ℝ} (ha : ∀ x, 0 ≤ a x) {g : ℤ → ℂ} (hg : ∀ z, g z = ((a z : ℝ) : ℂ))
    (hsupp : Work.Peluse.SupportIn g N) :
    Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Work.Peluse.arithIcc d L)
        (Work.Peluse.symIcc N) g
      = ((Work.Peluse.symIcc N).card : ℝ)⁻¹ * ((L : ℝ))⁻¹ ^ 2 *
          ∑' x : ℤ, (∑ y ∈ Finset.Icc 1 L, a (x + d * (y : ℤ))) ^ 2 := by
  rw [Work.Peluse.Peel.boxNormPow_one_tsum (N := N) (Work.Peluse.arithIcc d L)
    (Work.Peluse.symIcc N) hsupp, card_arithIcc hd L]
  have htsum : (∑' x : ℤ, ‖∑ c ∈ Work.Peluse.arithIcc d L, g (x + c)‖ ^ 2)
      = ∑' x : ℤ, (∑ y ∈ Finset.Icc 1 L, a (x + d * (y : ℤ))) ^ 2 :=
    tsum_congr fun x => by rw [window_norm_sum hd ha hg x L]
  rw [htsum]

/-! ## The requested statement -/

/-- Shrinking the window scale of the *first* box-norm power for a nonnegative real-valued
function, along an arithmetic-progression direction (the `M → H` transfer).

The function is `fun x => ((a x : ℝ) : ℂ)` with `a ≥ 0` (essential: for complex functions the
statement is false), so that the box-norm power at level one is
`|symIcc N|⁻¹ * L⁻² * ∑'_x (∑_{y ∈ [1,L]} a (x + d y))²` for every `1 ≤ L`
(this identity holds for `d = 0` too, where `arithIcc 0 L = {0}` and `|arithIcc 0 L| = 1`).  Then
`Work.Peluse.Peel.windowSum_block_le` (block decomposition, valid for `1 ≤ H ≤ M`) gives
`∑_x (∑_{y≤M} a(x+dy))² ≤ ((M+H)/H)² ∑_x (∑_{y≤H} a(x+dy))²`, and `M + H ≤ 2M` because `H ≤ M`.
The constant `4` may be replaced by anything `≥ ((M+H)/M)²`.  The file should live in namespace
`Work.Peluse.PET` (module `Submission.Work.Peluse.PET.boxNormPow_one_arithIcc_shrink`). -/
theorem boxNormPow_one_arithIcc_shrink {N H M : ℕ} (hH : 1 ≤ H) (hHM : H ≤ M) (d : ℤ)
    {a : ℤ → ℝ} (ha : ∀ x, 0 ≤ a x) (hsup : ∀ x, N < x.natAbs → a x = 0) :
    Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Work.Peluse.arithIcc d M) (Work.Peluse.symIcc N)
        (fun x => ((a x : ℝ) : ℂ))
      ≤ 4 * Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Work.Peluse.arithIcc d H)
        (Work.Peluse.symIcc N) (fun x => ((a x : ℝ) : ℂ)) := by
  classical
  set g : ℤ → ℂ := fun x => ((a x : ℝ) : ℂ) with hg
  have hg' : ∀ z, g z = ((a z : ℝ) : ℂ) := fun z => by rw [hg]
  have hnorm : ∀ z : ℤ, ‖g z‖ = a z := fun z => by
    rw [hg' z]; simpa using abs_of_nonneg (ha z)
  have hsupg : Work.Peluse.SupportIn g N := by
    intro x hx
    rw [hg' x, hsup x hx]
    norm_num
  have hM1 : 1 ≤ M := le_trans hH hHM
  rcases eq_or_ne d 0 with hd | hd
  · -- ## Case `d = 0` : both shift sets collapse to `{0}`, so the two sides are equal.
    subst hd
    rw [arithIcc_zero hM1, arithIcc_zero hH]
    exact le_mul_of_one_le_left (norm_nonneg _) (by norm_num)
  · -- ## Case `d ≠ 0` : both box-norm powers are the window energies, and blocks transfer.
    have hboxM := boxNormPow_one_arithIcc_eq (N := N) (L := M) hM1 (d := d) hd ha hg' hsupg
    have hboxH := boxNormPow_one_arithIcc_eq (N := N) (L := H) hH (d := d) hd ha hg' hsupg
    rw [hboxM, hboxH]
    set SM : ℝ := ∑' x : ℤ, (∑ y ∈ Finset.Icc 1 M, a (x + d * (y : ℤ))) ^ 2 with hSM
    set SH : ℝ := ∑' x : ℤ, (∑ y ∈ Finset.Icc 1 H, a (x + d * (y : ℤ))) ^ 2 with hSH
    have hSHnn : 0 ≤ SH := by rw [hSH]; exact tsum_nonneg fun x => sq_nonneg _
    have hA : 0 ≤ ((Work.Peluse.symIcc N).card : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    -- the block decomposition of `[1,M]` into blocks of length `H`
    have hblk := Work.Peluse.Peel.windowSum_block_le (N := N) (M := M) (L := H) hH hHM d hsupg
    have hMnorm : (∑' x : ℤ, (∑ y ∈ Finset.Icc 1 M, ‖g (x + d * (y : ℤ))‖) ^ 2) = SM := by
      rw [hSM]
      exact tsum_congr fun x =>
        congrArg (fun t => t ^ 2) (Finset.sum_congr rfl fun y _ => hnorm _)
    have hHnorm : (∑' x : ℤ, (∑ y ∈ Finset.Icc 1 H, ‖g (x + d * (y : ℤ))‖) ^ 2) = SH := by
      rw [hSH]
      exact tsum_congr fun x =>
        congrArg (fun t => t ^ 2) (Finset.sum_congr rfl fun y _ => hnorm _)
    rw [hMnorm, hHnorm] at hblk
    have hblk' : SM ≤ (((M : ℝ) + H) / (H : ℝ)) ^ 2 * SH := by
      rw [div_pow]
      exact hblk
    -- the constant: `H ≤ M` gives `((M+H)/H)² ≤ 4 M² / H²`
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
    have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
    have hconst : (((M : ℝ) + H) / (H : ℝ)) ^ 2 ≤ 4 * (M : ℝ) ^ 2 / (H : ℝ) ^ 2 := by
      have hle : ((M : ℝ) + H) ≤ 2 * (M : ℝ) := by
        have : (H : ℝ) ≤ (M : ℝ) := by exact_mod_cast hHM
        linarith
      have hsq : ((M : ℝ) + H) ^ 2 ≤ 4 * (M : ℝ) ^ 2 :=
        calc ((M : ℝ) + H) ^ 2 ≤ (2 * (M : ℝ)) ^ 2 :=
              pow_le_pow_left₀ (by linarith) hle 2
          _ = 4 * (M : ℝ) ^ 2 := by ring
      rw [div_pow]
      exact div_le_div_of_nonneg_right hsq (by positivity)
    calc ((Work.Peluse.symIcc N).card : ℝ)⁻¹ * ((M : ℝ))⁻¹ ^ 2 * SM
        ≤ ((Work.Peluse.symIcc N).card : ℝ)⁻¹ * ((M : ℝ))⁻¹ ^ 2 *
            ((((M : ℝ) + H) / (H : ℝ)) ^ 2 * SH) :=
          mul_le_mul_of_nonneg_left hblk' (by positivity)
      _ ≤ ((Work.Peluse.symIcc N).card : ℝ)⁻¹ * ((M : ℝ))⁻¹ ^ 2 *
            ((4 * (M : ℝ) ^ 2 / (H : ℝ) ^ 2) * SH) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hconst hSHnn) (by positivity)
      _ = 4 * (((Work.Peluse.symIcc N).card : ℝ)⁻¹ * ((H : ℝ))⁻¹ ^ 2 * SH) := by
          have hM0 : (M : ℝ) ≠ 0 := ne_of_gt hMpos
          have hH0 : (H : ℝ) ≠ 0 := ne_of_gt hHpos
          field_simp

end

end Work.Peluse.PET
