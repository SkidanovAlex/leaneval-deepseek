import Mathlib
import Submission.Work.SynFFT.defs
import Submission.Work.SynFFT.kit
import Submission.Work.SynFFT.yMulGetD
import Submission.Work.SynFFT.yMulListGetD

/-!
# `yMulList` represents `yMul` (paper: the twiddle step of the synthetic FFT)

`Work.SynFFT.YMulListOK` is the pure-mathematics statement behind the twiddle word of the
synthetic FFT: the list operation `yMulList r e w` of `Submission/Work/SynFFT/kit.lean`
(split the coefficient list `w` of `r` fixed-point values at `(-e) mod r`, keep one half and
negate the other) represents multiplication by `y^e` in `R = ℂ[y]/(y^r+1)` at the level of
fixed-point values.

The proof is the combination of two independent facts:

* `Work.SynFFT.yMulGetD` : closed form of `yMul r e a j` for `|e| ≤ r` — the coefficient
  read off is `j + ((-e) fmod r)` (modulo `r`), and the sign is `-1` exactly when the shift
  wraps around;
* `Work.SynFFT.yMulListGetD` : the same index/sign description read off the list
  `yMulList r e w`.

The remaining step (here) is bookkeeping: `fxC` is `ℤ`-homogeneous, `vget` agrees with
`fxC` on the coefficient list, and both branch conditions agree.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

/-- `fxC` is homogeneous under an integer scaling of a coefficient pair. -/
private lemma fxC_sg (p : ℕ) (c : Prop) [Decidable c] (u v : ℤ) :
    HvdH.fxC p ((if c then (1 : ℤ) else -1) * u, (if c then (1 : ℤ) else -1) * v)
      = (if c then (1 : ℂ) else -1) * HvdH.fxC p (u, v) := by
  split_ifs with h
  · simp only [HvdH.fxC]; push_cast; ring
  · simp only [HvdH.fxC]; push_cast; ring

/-- `fxC` is homogeneous under an integer scaling of a coefficient pair, with the sign put
outside (`-sg` on the pair is the same as `sg` applied to the negated value). -/
private lemma fxC_sg_neg (p : ℕ) (c : Prop) [Decidable c] (u v : ℤ) :
    HvdH.fxC p (-((if c then (1 : ℤ) else -1) * u), -((if c then (1 : ℤ) else -1) * v))
      = (if c then (1 : ℂ) else -1) * (-(HvdH.fxC p (u, v))) := by
  split_ifs with h
  · simp only [HvdH.fxC]; push_cast; ring
  · simp only [HvdH.fxC]; push_cast; ring

/-- The list operation `yMulList` of the twiddle word represents multiplication by `y^e` in
`R = ℂ[y]/(y^r+1)` (paper Lemma 3.2 / Proposition 3.3, twiddle step). -/
theorem yMulListOK : Work.SynFFT.YMulListOK := by
  intro p r e w hw he j
  rcases Nat.eq_zero_or_pos r with h0 | hr
  · subst h0
    exact j.elim0
  · have hrne : (r : ℤ) ≠ 0 := by omega
    have hf_eq : (-e).fmod (r : ℤ) = (-e) % (r : ℤ) := by
      rw [Int.fmod_eq_emod, ite_eq_left (Or.inl (by positivity))]
      ring
    have hf0 : 0 ≤ (-e).fmod (r : ℤ) := hf_eq ▸ Int.emod_nonneg _ hrne
    have hflt : (-e).fmod (r : ℤ) < (r : ℤ) := hf_eq ▸ Int.emod_lt_of_pos _ (by exact_mod_cast hr)
    have hsto : (((-e).fmod (r : ℤ)).toNat : ℤ) = (-e).fmod (r : ℤ) := Int.toNat_of_nonneg hf0
    have hsr : ((-e).fmod (r : ℤ)).toNat < r := by omega
    rw [Work.SynFFT.yMulGetD r hr e he (fun c : Fin r => HvdH.fxC p (w.getD (c : ℕ) (0, 0))) j,
        Work.SynFFT.yMulListGetD r hr e w hw (j : ℕ) j.isLt]
    by_cases hcase : (j : ℕ) + ((-e).fmod (r : ℤ)).toNat < r
    · rw [ite_eq_left hcase, ite_eq_left hcase]
      have hv : HvdH.vget (fun c : Fin r => HvdH.fxC p (w.getD (c : ℕ) (0, 0)))
          ((j : ℕ) + ((-e).fmod (r : ℤ)).toNat)
          = HvdH.fxC p (w.getD ((j : ℕ) + ((-e).fmod (r : ℤ)).toNat) (0, 0)) := by
        simp [HvdH.vget, hcase]
      rw [hv, fxC_sg]
    · rw [ite_eq_right hcase, ite_eq_right hcase]
      have h2 : (j : ℕ) + ((-e).fmod (r : ℤ)).toNat - r < r := by omega
      have hv : HvdH.vget (fun c : Fin r => HvdH.fxC p (w.getD (c : ℕ) (0, 0)))
          ((j : ℕ) + ((-e).fmod (r : ℤ)).toNat - r)
          = HvdH.fxC p (w.getD ((j : ℕ) + ((-e).fmod (r : ℤ)).toNat - r) (0, 0)) := by
        simp [HvdH.vget, h2]
      rw [hv, fxC_sg_neg]

end Work.SynFFT
