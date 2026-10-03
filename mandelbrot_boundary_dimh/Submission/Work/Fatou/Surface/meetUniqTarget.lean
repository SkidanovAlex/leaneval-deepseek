import Mathlib
import Submission.Work.Fatou.Surface.orbitDefs
import Submission.Work.Fatou.Qreg.fatouInjOnQ

namespace Work.Fatou.Surface

open Set Function

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

section MeetFwd

/-- **A meet with non-negative signed distance is an iterate of the base point.**  If `b ≤ a` and
the orbit of `s` meets the orbit of `z` inside `𝒬` with `F^[a] s = F^[b] z`, then `z` is the
`(a - b)`-th iterate of `s` under `F`. -/
theorem meet_fwd {s z : ℂ} {a b : ℕ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (h : Meet b₁ b₂ F s z a b) (hab : b ≤ a) : z = F^[a - b] s := by
  obtain ⟨heq, hs, hz⟩ := h
  have hpiece : Piece b₁ b₂ F (F^[a - b] s) b := by
    have h' : Piece b₁ b₂ F s ((a - b) + b) := by rwa [Nat.sub_add_cancel hab]
    exact piece_of_iterate h'
  have hiter : F^[b] (F^[a - b] s) = F^[b] z := by
    rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hab, heq]
  exact (iter_injOn hadm hF hpiece hz hiter).symm

end MeetFwd

section MeetBwd

/-- **A meet with non-positive signed distance is an iterate of the target point.**  If `a ≤ b` and
the orbit of `s` meets the orbit of `z` inside `𝒬` with `F^[a] s = F^[b] z`, then the `(b - a)`-th
iterate of `z` is `s`. -/
theorem meet_bwd {s z : ℂ} {a b : ℕ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (h : Meet b₁ b₂ F s z a b) (hab : a ≤ b) : F^[b - a] z = s := by
  obtain ⟨heq, hs, hz⟩ := h
  have hpiece : Piece b₁ b₂ F (F^[b - a] z) a := by
    have h' : Piece b₁ b₂ F z ((b - a) + a) := by rwa [Nat.sub_add_cancel hab]
    exact piece_of_iterate h'
  have hiter : F^[a] (F^[b - a] z) = F^[a] s := by
    rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hab, heq]
  exact iter_injOn hadm hF hpiece hs hiter

end MeetBwd

/-- **The meet-difference determines the point.** Two points `z, z'` whose orbits meet the orbit of the same point `s` at the same signed distance are equal. -/
theorem meetUniqTarget {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {s z z' : ℂ} {a b a' b' : ℕ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (h : Work.Fatou.Surface.Meet b₁ b₂ F s z a b)
    (h' : Work.Fatou.Surface.Meet b₁ b₂ F s z' a' b')
    (hd : (a : ℤ) - (b : ℤ) = (a' : ℤ) - (b' : ℤ)) : z = z' := by
  rcases le_total b a with hab | hab
  · -- non-negative signed distance: both points are iterates of `s`
    have hab' : b' ≤ a' := by omega
    have hsub : a - b = a' - b' := by omega
    rw [meet_fwd hadm hF h hab, meet_fwd hadm hF h' hab', hsub]
  · -- non-positive signed distance: both points iterate to `s`
    have hab' : a' ≤ b' := by omega
    have hsub : b - a = b' - a' := by omega
    have hz : F^[b - a] z = s := meet_bwd hadm hF h hab
    have hz' : F^[b - a] z' = s := by
      rw [hsub]; exact meet_bwd hadm hF h' hab'
    have hpiece : Piece b₁ b₂ F z (b - a) := piece_mono h.2.2 (Nat.sub_le b a)
    have hpiece' : Piece b₁ b₂ F z' (b - a) := by
      rw [hsub]; exact piece_mono h'.2.2 (Nat.sub_le b' a')
    exact iter_injOn hadm hF hpiece hpiece' (by rw [hz, hz'])

end

end Work.Fatou.Surface
