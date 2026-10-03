import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Commons.NumberTheory.GaussianInt.ncard_assoc_norm_mul

namespace Work.FIArea6b

open Zsqrtd

/-- If `n` is squarefree and `d ∣ n`, then `d` and `n / d` are coprime.

Indeed, if `g = gcd d (n/d)` then `g * g ∣ d * (n/d) = n`, so `g` is a unit of `ℕ`,
i.e. `g = 1`. -/
lemma coprime_div_of_squarefree {n d : ℕ} (hsf : Squarefree n) (hd : d ∣ n) :
    Nat.Coprime d (n / d) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  set g := Nat.gcd d (n / d) with hg
  have hgd : g ∣ d := Nat.gcd_dvd_left _ _
  have hgn : g ∣ n / d := Nat.gcd_dvd_right _ _
  have hgg : g * g ∣ n := by
    have h1 : g * g ∣ d * (n / d) := mul_dvd_mul hgd hgn
    rwa [Nat.mul_div_cancel' hd] at h1
  have hu : IsUnit g := hsf g hgg
  rwa [Nat.isUnit_iff] at hu

/-- **Every divisor of `‖z‖` is the norm of a Gaussian divisor of `z`**, when `‖z‖` is
squarefree.

The witnessing map is `d ↦ gPart d z`, the part of `z` supported on the prime divisors
of `d`.  Since `‖z‖` is squarefree, `d` and `‖z‖ / d` are coprime, so
`norm_gPart_eq_and_associated` gives `‖gPart d z‖ = d`; and `gPart d z ∣ z` by
construction.  Injectivity is immediate because the norm of the image recovers `d`. -/
theorem gaussian_divisor_count (z : GaussianInt) (hz : z ≠ 0)
    (hsf : Squarefree (Work.FIPlan.gnorm z)) :
    ∃ f : (Work.FIPlan.gnorm z).divisors → GaussianInt,
      Function.Injective f ∧ ∀ d : (Work.FIPlan.gnorm z).divisors,
        f d ∣ z ∧ Work.FIPlan.gnorm (f d) = (d : ℕ) := by
  have hnorm : ∀ d : (Work.FIPlan.gnorm z).divisors,
      (Commons.NumberTheory.GaussianInt.gPart (d : ℕ) z).norm.natAbs = (d : ℕ) := by
    intro d
    have hdm : (d : ℕ) ∈ (Work.FIPlan.gnorm z).divisors := d.2
    rw [Nat.mem_divisors] at hdm
    obtain ⟨hdvd, hnne⟩ := hdm
    have hdpos : 1 ≤ (d : ℕ) := by
      rcases Nat.eq_zero_or_pos (d : ℕ) with h | h
      · exact absurd (zero_dvd_iff.mp (by rwa [h] at hdvd)) hnne
      · exact h
    have hndpos : 1 ≤ Work.FIPlan.gnorm z / (d : ℕ) := by
      have h : Work.FIPlan.gnorm z = (d : ℕ) * (Work.FIPlan.gnorm z / (d : ℕ)) :=
        (Nat.mul_div_cancel' hdvd).symm
      rcases Nat.eq_zero_or_pos (Work.FIPlan.gnorm z / (d : ℕ)) with h0 | h0
      · rw [h0, mul_zero] at h; exact absurd h hnne
      · exact h0
    have hcop : Nat.Coprime (d : ℕ) (Work.FIPlan.gnorm z / (d : ℕ)) :=
      coprime_div_of_squarefree hsf hdvd
    have hz' : (z.norm).natAbs = (d : ℕ) * (Work.FIPlan.gnorm z / (d : ℕ)) := by
      rw [Nat.mul_div_cancel' hdvd]; rfl
    exact (Commons.NumberTheory.GaussianInt.norm_gPart_eq_and_associated
      hdpos hndpos hcop hz').1
  refine ⟨fun d => Commons.NumberTheory.GaussianInt.gPart (d : ℕ) z, ?_, ?_⟩
  · intro d1 d2 heq
    apply Subtype.ext
    have h1 := hnorm d1
    have h2 := hnorm d2
    have h := congrArg (fun w : GaussianInt => w.norm.natAbs) heq
    rw [h1, h2] at h
    exact h
  · intro d
    exact ⟨Commons.NumberTheory.GaussianInt.gPart_dvd_left (d : ℕ) z, hnorm d⟩

end Work.FIArea6b
