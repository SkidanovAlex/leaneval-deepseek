import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Transform.bluesteinDefs
import Submission.Work.DFT.digitsBij
import Submission.Work.DFT.subDigitsFacts
import Submission.Work.DFT.expId
import Submission.Work.DFT.phaseLin
import Submission.Work.Transform.subIdxPerm
import Submission.Work.Transform.chirpCore

set_option autoImplicit false

namespace Work.Transform

open scoped BigOperators

/-- `HvdH.vget` at an in-range index (local copy; `Work.Resample.vget_of_lt` is the same). -/
private lemma bluesteinVget {n : ℕ} (u : Fin n → ℂ) {i : ℕ} (h : i < n) :
    HvdH.vget u i = u ⟨i, h⟩ := by
  simp [HvdH.vget, h]

/-- Paper (3.2), pointwise form: for the chirp `a_j = e^{πi Σᵢ jᵢ²/tᵢ}` and even `tᵢ`,
`ā_j · a_{j-k} · ā_k = e^{-2πi Σᵢ jᵢkᵢ/tᵢ}`, where `j - k` is the flat index `subIdx ts j k`.
This is the factor identity behind Bluestein's convolution formula. -/
theorem chirp_pair (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) (heven : ∀ t ∈ ts, Even t)
    (j k : Fin ts.prod) :
    star (chirp ts (j:ℕ)) * chirp ts (HvdH.subIdx ts (j:ℕ) (k:ℕ)) * star (chirp ts (k:ℕ))
      = Work.DFT.dftExp ts (-1) (j:ℕ) (k:ℕ) := by
  obtain ⟨hdig, -, -⟩ := subIdxPerm ts hpos
  have h1 : star (chirp ts (j:ℕ))
      = expPi (-(HvdH.phase ts (HvdH.digits ts (j:ℕ)) (HvdH.digits ts (j:ℕ)))) := star_chirp ts _
  have h2 : star (chirp ts (k:ℕ))
      = expPi (-(HvdH.phase ts (HvdH.digits ts (k:ℕ)) (HvdH.digits ts (k:ℕ)))) := star_chirp ts _
  have h3 : chirp ts (HvdH.subIdx ts (j:ℕ) (k:ℕ))
      = expPi (HvdH.phase ts (HvdH.digits ts (HvdH.subIdx ts (j:ℕ) (k:ℕ)))
          (HvdH.digits ts (HvdH.subIdx ts (j:ℕ) (k:ℕ)))) := chirp_eq_expPi ts _
  have hΦ : HvdH.phase ts (HvdH.digits ts (HvdH.subIdx ts (j:ℕ) (k:ℕ)))
        (HvdH.digits ts (HvdH.subIdx ts (j:ℕ) (k:ℕ)))
      = HvdH.phase ts (HvdH.subDigits ts (HvdH.digits ts (j:ℕ)) (HvdH.digits ts (k:ℕ)))
          (HvdH.subDigits ts (HvdH.digits ts (j:ℕ)) (HvdH.digits ts (k:ℕ))) := by
    rw [hdig (j:ℕ) (k:ℕ)]
  rw [h1, h2, h3, hΦ]
  rw [chirpCore ts hpos heven (HvdH.digits ts (j:ℕ)) (HvdH.digits ts (k:ℕ))
        (Work.DFT.digits_length ts (j:ℕ)) (Work.DFT.digits_length ts (k:ℕ))
        ((Work.DFT.digitsBij ts hpos).2.1 (k:ℕ) k.isLt)]
  rw [← expPi_add, ← expPi_add, dftExp_eq_expPi]
  congr 1
  push_cast
  ring

/-- Paper (3.1)/(3.2): Bluestein's identity.  With `a_j = e^{πi Σ_i j_i²/t_i}` (periodic in
each `j_i` with period `t_i`, as `t_i` is even), the normalised multidimensional DFT is
`dftMulti ts (-1) u = ā ⊙ convC ts a (ā ⊙ u)` (pointwise products). -/
theorem bluestein (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) (heven : ∀ t ∈ ts, Even t)
    (u : Fin ts.prod → ℂ) :
    HvdH.dftMulti ts (-1) u = fun j : Fin ts.prod =>
      star (Work.Transform.chirp ts (j : ℕ)) *
        HvdH.convC ts (fun k : Fin ts.prod => Work.Transform.chirp ts (k : ℕ))
          (fun k : Fin ts.prod => star (Work.Transform.chirp ts (k : ℕ)) * u k) j := by
  funext j
  rw [Work.DFT.dftMulti_apply]
  simp only [HvdH.convC]
  let σ : Fin ts.prod → Fin ts.prod :=
    fun k => ⟨HvdH.subIdx ts (j:ℕ) (k:ℕ), Work.DFT.subIdx_lt ts hpos (j:ℕ) (k:ℕ)⟩
  let Φ : Fin ts.prod → ℂ := fun m => chirp ts (σ m : ℕ) * (star (chirp ts (m:ℕ)) * u m)
  have hσval : ∀ k : Fin ts.prod, (σ (σ k) : ℕ) = (k:ℕ) :=
    fun k => subIdx_subIdx ts hpos (j:ℕ) (k:ℕ) k.isLt
  have hv : ∀ k : Fin ts.prod,
      HvdH.vget (fun k : Fin ts.prod => star (chirp ts (k:ℕ)) * u k) (HvdH.subIdx ts (j:ℕ) (k:ℕ))
        = star (chirp ts (σ k : ℕ)) * u (σ k) := by
    intro k
    rw [bluesteinVget _ (Work.DFT.subIdx_lt ts hpos (j:ℕ) (k:ℕ))]
  have hgen : ∀ G : Fin ts.prod → ℂ, (∑ k : Fin ts.prod, G (σ k)) = ∑ k : Fin ts.prod, G k := by
    intro G
    have h' : (∑ k : Fin ts.prod, G (σ k))
        = ∑ k : Fin ts.prod,
            G ⟨HvdH.subIdx ts (j:ℕ) (k:ℕ), Work.DFT.subIdx_lt ts hpos (j:ℕ) (k:ℕ)⟩ :=
      Finset.sum_congr rfl (fun k _ => congrArg G rfl)
    rw [h', subIdx_sum_perm ts hpos j G]
  have hsum : (∑ k : Fin ts.prod, chirp ts (k:ℕ) *
        HvdH.vget (fun k : Fin ts.prod => star (chirp ts (k:ℕ)) * u k) (HvdH.subIdx ts (j:ℕ) (k:ℕ)))
      = ∑ m : Fin ts.prod, Φ m := by
    have h1 : (∑ k : Fin ts.prod, chirp ts (k:ℕ) *
          HvdH.vget (fun k : Fin ts.prod => star (chirp ts (k:ℕ)) * u k) (HvdH.subIdx ts (j:ℕ) (k:ℕ)))
        = ∑ k : Fin ts.prod, chirp ts (k:ℕ) * (star (chirp ts (σ k : ℕ)) * u (σ k)) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hv k]
    have h2 : (∑ k : Fin ts.prod, chirp ts (k:ℕ) * (star (chirp ts (σ k : ℕ)) * u (σ k)))
        = ∑ k : Fin ts.prod, Φ (σ k) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      show chirp ts (k:ℕ) * (star (chirp ts (σ k : ℕ)) * u (σ k))
        = chirp ts (σ (σ k) : ℕ) * (star (chirp ts (σ k : ℕ)) * u (σ k))
      rw [hσval k]
    rw [h1, h2]
    exact hgen Φ
  have hpair2 : ∀ m : Fin ts.prod,
      star (chirp ts (j:ℕ)) * Φ m = Work.DFT.dftExp ts (-1) (j:ℕ) (m:ℕ) * u m := by
    intro m
    show star (chirp ts (j:ℕ)) * (chirp ts (σ m : ℕ) * (star (chirp ts (m:ℕ)) * u m))
      = Work.DFT.dftExp ts (-1) (j:ℕ) (m:ℕ) * u m
    rw [← mul_assoc, ← mul_assoc, chirp_pair ts hpos heven j m]
  have hS : star (chirp ts (j:ℕ)) * (∑ m : Fin ts.prod, Φ m)
      = ∑ m : Fin ts.prod, Work.DFT.dftExp ts (-1) (j:ℕ) (m:ℕ) * u m := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => hpair2 m)
  rw [hsum, ← hS]
  ring

end Work.Transform
