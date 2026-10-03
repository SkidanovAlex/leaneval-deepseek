/-
# `Submission.Work.FIArea3.JointCount.SStructure` — the "interpolating" set `S` and the descent

For `d ≥ 1`, call a Gaussian integer `w` **interpolating** for `d` when `w ∣ d` and `d ∣ |w|²`;
write `IsSPt d w` for this.  The maximal pieces of `{z : d ∣ |z|²}` (the elements of
`maxPieceFinset d`) all lie in `S = {w | IsSPt d w}` (`IsSPt_of_mem_maxPieceFinset`), and they are
*minimal* in `S` for divisibility (`Smin_of_mem_maxPieceFinset`), because the maximal pieces cover
`{z | d ∣ |z|²}` (`maximal_piece_cover`).

The engine of the whole counting argument is the **descent**: if `w ∈ S` is minimal in `S` and
`ρ` is a Gaussian prime dividing `w`, then `d ∤ |w/ρ|²`.  Indeed, if `d ∣ |w/ρ|²` then `w/ρ` lies
in `S` again and divides `w` properly (its norm is smaller), contradicting minimality.

Two elementary `Nat.factorization` lemmas convert the descent into exponent bounds:
`factorization_le_of_not_dvd_div` (division by one prime) and
`factorization_le_succ_of_not_dvd_div_sq` (division by the square of a prime).
-/
import Mathlib
import Submission.Work.FIArea3.JointCount.maxPieceDefs
import Submission.Work.FIArea3.JointCount.pieces
import Submission.Work.FIArea3.JointCount.GaussPieceMax_arith
import Submission.Work.FIArea3.JointCount.maximal_piece_cover

namespace Work.FIArea3.JointCount

open Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `w` interpolates `d`: `w` divides `d` in `ℤ[i]` and `d` divides the norm `|w|²`. -/
def IsSPt (d : ℕ) (w : GaussianInt) : Prop := w ∣ (d : GaussianInt) ∧ d ∣ gnorm w

/-- Membership in `maxPieceFinset d`, unwound. -/
lemma mem_maxPieceFinset_iff {d : ℕ} {w : GaussianInt} :
    w ∈ maxPieceFinset d ↔
      w ∈ gBox (d : ℤ) ∧ GaussPieceMax d w ∧ 0 < w.re ∧ 0 ≤ w.im := by
  rw [maxPieceFinset, Finset.mem_filter]

/-- Every piece generator divides `d`: it is the lcm of two Gaussian divisors of `d`. -/
lemma IsPieceGen.dvd_natCast {d : ℕ} {w : GaussianInt} (h : IsPieceGen d w) :
    w ∣ (d : GaussianInt) := by
  obtain ⟨u, hud, rfl⟩ := h
  rw [gaussPieceGen]
  refine EuclideanDomain.lcm_dvd_iff.mpr ⟨hud, ?_⟩
  rcases eq_or_ne u 0 with rfl | hu0
  · rcases hud with ⟨c, hc⟩
    rw [zero_mul] at hc
    rw [hc]; exact dvd_zero _
  · obtain ⟨c, hc⟩ := hud
    have hq : (d : GaussianInt) / u = c :=
      (EuclideanDomain.eq_div_of_mul_eq_right hu0 hc.symm).symm
    rw [hq]
    exact ⟨star u, by
      calc (d : GaussianInt) = star ((d : GaussianInt)) := (star_natCast d).symm
        _ = star (u * c) := by rw [hc]
        _ = star c * star u := star_mul u c⟩

/-- Every element of `maxPieceFinset d` interpolates `d`. -/
lemma IsSPt_of_mem_maxPieceFinset (d : ℕ) (hd : 1 ≤ d) {w : GaussianInt}
    (hw : w ∈ maxPieceFinset d) : IsSPt d w := by
  rw [maxPieceFinset, Finset.mem_filter] at hw
  obtain ⟨-, hmax, -⟩ := hw
  obtain ⟨u, hud, hwu⟩ := hmax.1
  refine ⟨hmax.1.dvd_natCast, gaussPieceGen_dvd_gnorm d hd hud (by rw [hwu])⟩

/-- Every element of `maxPieceFinset d` is minimal in `S` for divisibility: any `v ∈ S` dividing
it is associate to it.  This uses the covering of `{z | d ∣ |z|²}` by maximal pieces. -/
lemma Smin_of_mem_maxPieceFinset (d : ℕ) (hd : 1 ≤ d) {w : GaussianInt}
    (hw : w ∈ maxPieceFinset d) :
    ∀ v : GaussianInt, IsSPt d v → v ∣ w → w ∣ v := by
  rw [maxPieceFinset, Finset.mem_filter] at hw
  obtain ⟨-, hmax, -⟩ := hw
  intro v hv hvw
  obtain ⟨u, hu, huv⟩ := (maximal_piece_cover d hd v).mp hv.2
  exact (hmax.2 u hu.1 (huv.trans hvw)).trans huv

/-- `S` is invariant under conjugation. -/
lemma star_IsSPt {d : ℕ} {w : GaussianInt} (h : IsSPt d w) : IsSPt d (star w) := by
  obtain ⟨hw, hdvd⟩ := h
  obtain ⟨c, hc⟩ := hw
  refine ⟨⟨star c, ?_⟩, ?_⟩
  · calc (d : GaussianInt) = star ((d : GaussianInt)) := (star_natCast d).symm
      _ = star (w * c) := by rw [hc]
      _ = star c * star w := star_mul w c
      _ = star w * star c := mul_comm _ _
  · rwa [GaussPieceMax_arith_gnorm_star]

/-- Minimality in `S` is preserved by conjugation. -/
lemma star_Smin {d : ℕ} {w : GaussianInt}
    (hmin : ∀ v : GaussianInt, IsSPt d v → v ∣ w → w ∣ v) :
    ∀ v : GaussianInt, IsSPt d v → v ∣ star w → star w ∣ v := by
  intro v hv hvsw
  have hsv : IsSPt d (star v) := star_IsSPt hv
  have hsvw : star v ∣ w := (star_dvd_iff_dvd_star v w).mpr hvsw
  have h1 : w ∣ star v := hmin (star v) hsv hsvw
  exact (star_dvd_iff_dvd_star w v).mpr h1

/-- The norm of an exact quotient: `|w/ρ|² · |ρ|² = |w|²` when `ρ ≠ 0` divides `w`. -/
lemma gnorm_div_mul {w ρ : GaussianInt} (hρ : ρ ≠ 0) (hρw : ρ ∣ w) :
    gnorm (w / ρ) * gnorm ρ = gnorm w := by
  rw [← gnorm_mul, mul_comm, EuclideanDomain.mul_div_cancel' hρ hρw]

/-- **The descent.**  If `w ∈ S` is minimal in `S` and `ρ` is a Gaussian prime dividing `w`, then
`d` does not divide the norm of the quotient `w/ρ`: otherwise `w/ρ` would be a strictly smaller
element of `S` dividing `w`, contradicting minimality. -/
lemma descent {d : ℕ} (hd : 1 ≤ d) {w : GaussianInt} (hS : IsSPt d w)
    (hmin : ∀ v : GaussianInt, IsSPt d v → v ∣ w → w ∣ v)
    (ρ : GaussianInt) (hρ : Prime ρ) (hρw : ρ ∣ w) : ¬ (d ∣ gnorm (w / ρ)) := by
  intro hdvd
  have hρ0 : ρ ≠ 0 := hρ.ne_zero
  have hw0 : w ≠ 0 := by
    intro h0
    obtain ⟨h1, -⟩ := hS
    rw [h0] at h1
    obtain ⟨c, hc⟩ := h1
    rw [zero_mul] at hc
    have : d = 0 := by exact_mod_cast hc
    omega
  have hmul : ρ * (w / ρ) = w := EuclideanDomain.mul_div_cancel' hρ0 hρw
  have hq0 : w / ρ ≠ 0 := by
    intro h; rw [h, mul_zero] at hmul; exact hw0 hmul.symm
  have hdiv : w / ρ ∣ w := ⟨ρ, by rw [mul_comm]; exact hmul.symm⟩
  have hS' : IsSPt d (w / ρ) := ⟨hdiv.trans hS.1, hdvd⟩
  have hwle : w ∣ w / ρ := hmin (w / ρ) hS' hdiv
  have hgn : gnorm w = gnorm (w / ρ) * gnorm ρ := by
    calc gnorm w = gnorm (ρ * (w / ρ)) := by rw [hmul]
      _ = gnorm ρ * gnorm (w / ρ) := gnorm_mul ρ (w / ρ)
      _ = gnorm (w / ρ) * gnorm ρ := mul_comm _ _
  have hA : 0 < gnorm (w / ρ) := Nat.pos_of_ne_zero (fun h => hq0 ((gnorm_eq_zero_iff _).mp h))
  have hB : 2 ≤ gnorm ρ := by
    have h2 : gnorm ρ ≠ 1 := fun h => hρ.not_isUnit (Zsqrtd.norm_eq_one_iff.mp h)
    have h1 : gnorm ρ ≠ 0 := fun h => hρ0 ((gnorm_eq_zero_iff ρ).mp h)
    omega
  have hlt : gnorm (w / ρ) < gnorm w := by
    rw [hgn]
    calc gnorm (w / ρ) < gnorm (w / ρ) * 2 := by omega
      _ ≤ gnorm (w / ρ) * gnorm ρ := Nat.mul_le_mul_left _ hB
  have hle : gnorm w ≤ gnorm (w / ρ) := by
    have hdvd2 : gnorm w ∣ gnorm (w / ρ) := gnorm_dvd_of_dvd hwle
    exact Nat.le_of_dvd hA hdvd2
  omega

/-! ## Two `Nat.factorization` lemmas turning the descent into exponent bounds -/

/-- If `d ∣ M`, `p` is a prime with `p * (M/p) = M`, and `d ∤ M/p`, then the exponent of `p`
in `M` is at most its exponent in `d`. -/
lemma factorization_le_of_not_dvd_div {p d M : ℕ} (hp : p.Prime) (hmp : M / p ≠ 0) (hd : d ≠ 0)
    (hex : p * (M / p) = M) (hdvd : d ∣ M) (h : ¬ d ∣ M / p) :
    M.factorization p ≤ d.factorization p := by
  have hM0 : M ≠ 0 := by
    rintro rfl; simp at hmp
  by_contra hcon
  push Not at hcon
  apply h
  refine (Nat.factorization_le_iff_dvd hd hmp).mp ?_
  have hle : d.factorization ≤ M.factorization :=
    (Nat.factorization_le_iff_dvd hd hM0).mpr hdvd
  intro r
  rcases eq_or_ne r p with h' | hr
  · rw [h']
    have hfac : M.factorization p = 1 + (M / p).factorization p := by
      conv_lhs => rw [← hex]
      rw [Nat.factorization_mul hp.ne_zero hmp, Nat.Prime.factorization hp]
      simp
    have := hle p
    omega
  · have hfac : (M / p).factorization r = M.factorization r := by
      conv_rhs => rw [← hex]
      rw [Nat.factorization_mul hp.ne_zero hmp, Nat.Prime.factorization hp]
      simp [Finsupp.single_eq_of_ne hr]
    rw [hfac]
    exact hle r

/-- If `d ∣ M`, `q` is a prime with `q^2 * (M/q^2) = M`, and `d ∤ M/q^2`, then the exponent of `q`
in `M` exceeds its exponent in `d` by at most one. -/
lemma factorization_le_succ_of_not_dvd_div_sq {q d M : ℕ} (hq : q.Prime) (hmq : M / q ^ 2 ≠ 0)
    (hd : d ≠ 0) (hex : q ^ 2 * (M / q ^ 2) = M) (hdvd : d ∣ M)
    (h : ¬ d ∣ M / q ^ 2) : M.factorization q ≤ d.factorization q + 1 := by
  have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq.ne_zero
  have hM0 : M ≠ 0 := by
    rintro rfl; simp at hmq
  have hq2dvd : q ^ 2 ∣ M := ⟨M / q ^ 2, hex.symm⟩
  have hfacq : 2 ≤ M.factorization q :=
    (hq.pow_dvd_iff_le_factorization hM0).mp (by simpa using hq2dvd)
  by_contra hcon
  push Not at hcon
  apply h
  refine (Nat.factorization_le_iff_dvd hd hmq).mp ?_
  have hle : d.factorization ≤ M.factorization :=
    (Nat.factorization_le_iff_dvd hd hM0).mpr hdvd
  intro r
  have hkk : M.factorization r = (q ^ 2).factorization r + (M / q ^ 2).factorization r := by
    have h1 := congrArg (fun f : ℕ →₀ ℕ => f r) (Nat.factorization_mul hq2 hmq)
    simp only [Finsupp.add_apply] at h1
    rwa [hex] at h1
  rcases eq_or_ne r q with h' | hr
  · rw [h'] at hkk ⊢
    have hq2f : (q ^ 2).factorization q = 2 := by
      rw [Nat.factorization_pow, Nat.Prime.factorization hq]
      simp
    rw [hq2f] at hkk
    have := hle q
    omega
  · have hq2f : (q ^ 2).factorization r = 0 := by
      rw [Nat.factorization_pow, Nat.Prime.factorization hq]
      simp [Finsupp.single_eq_of_ne hr]
    rw [hq2f, zero_add] at hkk
    rw [← hkk]
    exact hle r

end

end Work.FIArea3.JointCount
