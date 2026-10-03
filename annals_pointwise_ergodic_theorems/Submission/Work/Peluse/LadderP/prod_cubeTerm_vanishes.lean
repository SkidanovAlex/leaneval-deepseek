import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.LadderP

/-- Every element of the arithmetic progression `arithIcc q L = {q, 2q, …, Lq}` has absolute value at
most `q.natAbs * L`. -/
lemma natAbs_le_of_mem_arithIcc {q : ℤ} {L : ℕ} {y : ℤ}
    (hy : y ∈ Work.Peluse.arithIcc q L) : y.natAbs ≤ q.natAbs * L := by
  rw [Work.Peluse.arithIcc] at hy
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
  rw [Finset.mem_Icc] at hn
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ hn.2

/-- Triangular inequality in the `natAbs` scale: if `|b| ≤ R` and `M + R < |a|` then `M < |a + b|`. -/
lemma natAbs_add_of_le {a b : ℤ} {M R : ℕ} (hR : b.natAbs ≤ R) (hx : M + R < a.natAbs) :
    M < (a + b).natAbs := by
  have h1 : a.natAbs ≤ (a + b).natAbs + b.natAbs := by
    have h := Int.natAbs_add_le (a + b) (-b)
    have h4 : a + b + -b = a := by ring
    rw [h4, Int.natAbs_neg] at h
    exact h
  omega

/-- **Support of the cube term with a scaled corner shift.**  If `f` is supported in `[-M,M]` and
every direction `h i`, `h' i` lies in the arithmetic progression `arithIcc (q i) L`, then the cube
product `∏_ω star^[weight ω] (f (x + c · cornerShift h h' ω))` vanishes as soon as
`M + (∑ i, |q i|) * L * |c| < |x|`: each corner shift is by hypothesis a sum of `t` multiples of the
`q i` with multiplier in `[1,L]`, hence bounded by `(∑ i, |q i|) * L` in absolute value, so every
argument `x + c · cornerShift` is outside `[-M,M]` and every factor of the product is `0`. -/
theorem prod_cubeTerm_vanishes {t : ℕ} {c : ℤ} (hc : 0 < c) {q : Fin t → ℤ} {L M : ℕ} {f : ℤ → ℂ}
    (hM : Work.Peluse.SupportIn f M)
    (h h' : (i : Fin t) → {x : ℤ // x ∈ Work.Peluse.arithIcc (q i) L}) :
    ∀ x : ℤ, M + (∑ i, (q i).natAbs) * L * c.natAbs < x.natAbs →
      (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
        (f (x + c * Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))) = 0 := by
  intro x hx
  have _ : 0 < c := hc
  refine Finset.prod_eq_zero (Finset.mem_univ (fun _ : Fin t => false)) ?_
  have hw : Work.Peluse.weight (fun _ : Fin t => false) = 0 := by simp [Work.Peluse.weight]
  rw [hw, Function.iterate_zero_apply]
  apply hM
  -- the corner shift with `ω = fun _ => false` uses only the `h'` directions
  have hbound : (Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1)
      (fun _ : Fin t => false)).natAbs ≤ (∑ i, (q i).natAbs) * L := by
    have h1 : Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1)
        (fun _ : Fin t => false) = ∑ i : Fin t, (h' i).1 := by
      rw [Work.Peluse.cornerShift]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp
    rw [h1]
    calc (∑ i : Fin t, (h' i).1).natAbs
        ≤ ∑ i : Fin t, ((h' i).1).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ i : Fin t, (q i).natAbs * L :=
          Finset.sum_le_sum (fun i _ => natAbs_le_of_mem_arithIcc (h' i).2)
      _ = (∑ i : Fin t, (q i).natAbs) * L :=
          (Finset.sum_mul Finset.univ (fun i => (q i).natAbs) L).symm
  have hc0 : (c * Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1)
      (fun _ : Fin t => false)).natAbs ≤ c.natAbs * ((∑ i, (q i).natAbs) * L) := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul_left _ hbound
  have hxR : M + c.natAbs * ((∑ i, (q i).natAbs) * L) < x.natAbs := by
    have he : c.natAbs * ((∑ i, (q i).natAbs) * L) = (∑ i, (q i).natAbs) * L * c.natAbs := by
      ring
    rw [he]
    exact hx
  exact natAbs_add_of_le hc0 hxR

end Work.Peluse.LadderP
