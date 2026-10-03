/-
# `Work.FIArea3.JointCount.maximal_piece_cover`

The maximal Gaussian-divisor pieces of `{z : ℤ[i] | d ∣ |z|²}` cover it:

  `d ∣ |z|²  ↔  ∃ w, GaussPieceMax d w ∧ w ∣ z`.

(`GaussPieceMax d w` says `w = gaussPieceGen d u` for some Gaussian divisor `u` of `d`
and that no piece generator properly divides `w`, i.e. `w` is a piece of minimal index.)

The proof is the natural descent in the norm: a piece generator `g ∣ z` which is not
maximal admits a piece generator `v ∣ g` with `g ∤ v`; equal norms would force `v ~ g`,
so `gnorm v < gnorm g` and strong induction in the norm produces a maximal piece
generator below `z`.  The converse is immediate from `gauss_divisor_cover`, since any
piece generator `gaussPieceGen d u` is a common multiple of `u` and `star (d/u)`.
-/
import Mathlib
import Submission.Work.FIArea3.JointCount.pieces
import Submission.Work.FIArea3.JointCount.gauss_divisor_cover

namespace Work.FIArea3.JointCount

open Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The Gaussian norm is multiplicative. -/
lemma gnorm_mul (a b : GaussianInt) : gnorm (a * b) = gnorm a * gnorm b := by
  simp only [gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- The Gaussian norm vanishes only at zero. -/
lemma gnorm_eq_zero_iff (z : GaussianInt) : gnorm z = 0 ↔ z = 0 := by
  simp only [gnorm, Int.natAbs_eq_zero]
  exact Zsqrtd.norm_eq_zero (by intro n hn; nlinarith [sq_nonneg n]) z

/-- The norm of a divisor divides the norm. -/
lemma gnorm_dvd_of_dvd {a b : GaussianInt} (h : a ∣ b) : gnorm a ∣ gnorm b := by
  obtain ⟨c, rfl⟩ := h
  rw [gnorm_mul]
  exact dvd_mul_right _ _

/-- In `ℤ[i]`, a divisor of the same positive norm divides back: `gnorm a = gnorm b` with
`a ∣ b ≠ 0` forces `a ~ b`, because the complementary factor has norm `1`, hence is a unit. -/
lemma dvd_of_dvd_of_gnorm_eq {a b : GaussianInt} (hab : a ∣ b) (hb : gnorm b ≠ 0)
    (heq : gnorm a = gnorm b) : b ∣ a := by
  obtain ⟨c, rfl⟩ := hab
  have hga : gnorm a ≠ 0 := by rw [heq]; exact hb
  have hpos : 0 < gnorm a := Nat.pos_of_ne_zero hga
  have hm : gnorm a * gnorm c = gnorm a * 1 := by
    rw [mul_one, show gnorm a * gnorm c = gnorm (a * c) from (gnorm_mul a c).symm]
    exact heq.symm
  have hc : gnorm c = 1 := Nat.mul_left_cancel hpos hm
  have hcd : c ∣ 1 := by
    refine ⟨star c, ?_⟩
    rw [mul_star_eq_gnorm, hc]
    norm_num
  obtain ⟨e, he⟩ := hcd
  exact ⟨e, by rw [mul_assoc, ← he, mul_one]⟩

/-- A proper divisor has strictly smaller norm. -/
lemma gnorm_lt_of_dvd_of_not_dvd {a b : GaussianInt} (hb : gnorm b ≠ 0) (hab : a ∣ b)
    (hba : ¬ b ∣ a) : gnorm a < gnorm b := by
  have hdvd : gnorm a ∣ gnorm b := gnorm_dvd_of_dvd hab
  have hne : gnorm a ≠ gnorm b := fun heq => hba (dvd_of_dvd_of_gnorm_eq hab hb heq)
  exact Nat.lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hb) hdvd) hne

/-- The generator of a piece of `{z | d ∣ |z|²}` is nonzero (for `d ≥ 1`): it divides the
product `u · star (d/u)` of two nonzero Gaussian integers. -/
lemma gaussPieceGen_ne_zero {d : ℕ} (hd : 1 ≤ d) {u : GaussianInt}
    (hud : u ∣ (d : GaussianInt)) : gaussPieceGen d u ≠ 0 := by
  intro hg
  have hd0 : d ≠ 0 := by omega
  have hdc : (d : GaussianInt) ≠ 0 := by exact_mod_cast hd0
  have hu0 : u ≠ 0 := by
    rintro rfl
    obtain ⟨c, hc⟩ := hud
    rw [zero_mul] at hc
    exact hdc hc
  have hdu : (d : GaussianInt) / u ≠ 0 := by
    intro h
    have h1 := EuclideanDomain.mul_div_cancel' hu0 hud
    rw [h, mul_zero] at h1
    exact hdc h1.symm
  have hst : star ((d : GaussianInt) / u) ≠ 0 := by simpa using hdu
  have hld : EuclideanDomain.lcm u (star ((d : GaussianInt) / u)) ∣
      u * star ((d : GaussianInt) / u) :=
    EuclideanDomain.lcm_dvd_iff.mpr ⟨dvd_mul_right _ _, dvd_mul_left _ _⟩
  have hg' : EuclideanDomain.lcm u (star ((d : GaussianInt) / u)) = 0 := hg
  rw [hg', zero_dvd_iff] at hld
  exact mul_ne_zero hu0 hst hld

/-- **The maximal Gaussian-divisor pieces cover the norm-divisibility locus.**
For `d ≥ 1`, a Gaussian integer `z` has `d ∣ |z|²` if and only if it is divisible by some
*maximal* piece generator `GaussPieceMax d w`. -/
theorem maximal_piece_cover (d : ℕ) (hd : 1 ≤ d) (z : GaussianInt) :
    d ∣ Work.FIPlan.gnorm z ↔
      ∃ w : GaussianInt, Work.FIArea3.JointCount.GaussPieceMax d w ∧ w ∣ z := by
  constructor
  · intro h
    -- `gauss_divisor_cover` splits `d` along a Gaussian divisor `u ∣ d`, giving a piece.
    obtain ⟨u, hud, huz, hduz⟩ := (gauss_divisor_cover d hd z).mp h
    have hig : IsPieceGen d (gaussPieceGen d u) := ⟨u, hud, rfl⟩
    have hmem : z ∈ gaussPiece d u := ⟨huz, hduz⟩
    have hgz : gaussPieceGen d u ∣ z := mem_gaussPiece_iff.mp hmem
    -- descent: any non-maximal piece generator admits a strictly smaller piece generator.
    have key : ∀ n : ℕ, ∀ g : GaussianInt, gnorm g = n → IsPieceGen d g → g ≠ 0 → g ∣ z →
        ∃ w : GaussianInt, GaussPieceMax d w ∧ w ∣ z := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro g hgn hig2 hg0 hgz2
        by_cases hmax : GaussPieceMax d g
        · exact ⟨g, hmax, hgz2⟩
        · have hnot : ¬ (∀ v : GaussianInt, IsPieceGen d v → v ∣ g → g ∣ v) := by
            intro hh; exact hmax ⟨hig2, hh⟩
          push Not at hnot
          obtain ⟨v, hv_piece, hvg, hgv⟩ := hnot
          have hgnne : gnorm g ≠ 0 := fun hh => hg0 ((gnorm_eq_zero_iff g).mp hh)
          have hlt : gnorm v < gnorm g := gnorm_lt_of_dvd_of_not_dvd hgnne hvg hgv
          have hv0 : v ≠ 0 := by
            rintro rfl
            obtain ⟨c, hc⟩ := hvg
            rw [zero_mul] at hc
            exact hg0 hc
          exact ih (gnorm v) (by rw [← hgn]; exact hlt) v rfl hv_piece hv0 (dvd_trans hvg hgz2)
    exact key (gnorm (gaussPieceGen d u)) (gaussPieceGen d u) rfl hig (gaussPieceGen_ne_zero hd hud) hgz
  · -- Conversely, a piece generator dividing `z` already forces `d ∣ |z|²`.
    rintro ⟨w, hw, hwz⟩
    obtain ⟨u, hud, rfl⟩ := hw.1
    refine (gauss_divisor_cover d hd z).mpr ⟨u, hud, ?_, ?_⟩
    · exact dvd_trans (EuclideanDomain.dvd_lcm_left _ _) hwz
    · exact (star_dvd_iff_dvd_star _ _).mp (dvd_trans (EuclideanDomain.dvd_lcm_right _ _) hwz)

end

end Work.FIArea3.JointCount
