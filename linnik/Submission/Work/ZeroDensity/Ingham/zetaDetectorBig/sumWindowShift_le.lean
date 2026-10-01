import Mathlib
import Submission.Work.ZeroDensity.Ingham.sumWindowIntegral_le

namespace Work.ZeroDensity.Ingham.zetaDetectorBig

/-- **Shifted-window overlap bound.**  The total integral of a continuous nonnegative `F`
over the length-`2L` windows centred at the points `z.im` (`z ∈ R`) is at most `(2 * L + 1)`
times the integral of `F` over the enclosing interval `[-(T + L), T + L]`.

Each window `[z.im - L, z.im + L]` lies in `[-(T + L), T + L]` because `|z.im| ≤ T`, and at
any fixed point at most `2 * L + 1` of the windows overlap, because the points `z.im` are
`1`-separated (a `1`-separated set inside an interval of length `2 * L` has at most
`2 * L + 1` points).  The `ℝ`-indexed assembly of these two facts is
`Work.ZeroDensity.Ingham.sumWindowIntegral_le`, applied here to the finset `R.image z.im`;
this lemma is the version in which each window is written `∫ v in (-L)..L, F (z.im + v)`. -/
theorem sumWindowShift_le (F : ℝ → ℝ) (R : Finset ℂ) {L T : ℝ}
    (hL : 1 ≤ L) (hT : 0 ≤ T) (hF : Continuous F) (hF0 : ∀ x, 0 ≤ F x)
    (hbd : ∀ z ∈ R, |z.im| ≤ T)
    (hsep : ∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → 1 ≤ |z.im - z'.im|) :
    (∑ z ∈ R, (∫ v in (-L)..L, F (z.im + v))) ≤ (2 * L + 1) * ∫ t in (-(T + L))..(T + L), F t := by
  classical
  -- `z ↦ z.im` is injective on `R`, since distinct points are `1`-separated.
  have hinj : Set.InjOn (fun z : ℂ => z.im) ↑R := by
    intro z hz z' hz' him
    by_contra hne
    have h := hsep z (Finset.mem_coe.mp hz) z' (Finset.mem_coe.mp hz') hne
    simp [him] at h
    linarith
  -- The imaginary parts form a `1`-separated finset of reals inside `[-T, T]`.
  have hbdS : ∀ y ∈ R.image (fun z : ℂ => z.im), |y| ≤ T := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact hbd z hz
  have hsepS : ∀ y ∈ R.image (fun z : ℂ => z.im), ∀ y' ∈ R.image (fun z : ℂ => z.im),
      y ≠ y' → 1 ≤ |y - y'| := by
    intro y hy y' hy' hne
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hy'
    exact hsep z hz z' hz' (fun h => hne (by rw [h]))
  have hmain := Work.ZeroDensity.Ingham.sumWindowIntegral_le F hL hT hF hF0 hbdS hsepS
  -- Re-express each shifted window integral as an integral centred at `z.im`.
  have hterm : ∀ z : ℂ, (∫ v in (-L)..L, F (z.im + v)) = ∫ t in (z.im - L)..(z.im + L), F t := by
    intro z
    have h := intervalIntegral.integral_comp_add_left (f := F) (a := -L) (b := L) (d := z.im)
    rw [h, show z.im + -L = z.im - L by ring]
  calc ∑ z ∈ R, (∫ v in (-L)..L, F (z.im + v))
      = ∑ z ∈ R, (∫ t in (z.im - L)..(z.im + L), F t) :=
        Finset.sum_congr rfl (fun z _ => hterm z)
    _ = ∑ y ∈ R.image (fun z : ℂ => z.im), (∫ t in (y - L)..(y + L), F t) :=
        (Finset.sum_image (s := R) (g := fun z : ℂ => z.im)
          (f := fun y : ℝ => ∫ t in (y - L)..(y + L), F t) hinj).symm
    _ ≤ (2 * L + 1) * ∫ t in (-(T + L))..(T + L), F t := hmain

end Work.ZeroDensity.Ingham.zetaDetectorBig
