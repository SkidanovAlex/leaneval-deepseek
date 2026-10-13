import Mathlib
import Submission.Work.WilG0.Defs

namespace Work.WilG0

open WilkiesDesign

theorem projLastIter_mem (S : WilkiesDesign.SOMin) (n m F D : ℕ) (X : Set (Fin (n + m) → ℝ)) (hX : X ∈ S.Ω F D (n + m)) :
    projLastIter n m X ∈ S.Ω (F + m + n) D n := by
  -- Iterating the projection axiom `m` times: dimension `n+m → n`, format `F → F+m`.
  have key : ∀ m (F D : ℕ) (X : Set (Fin (n + m) → ℝ)),
      X ∈ S.Ω F D (n + m) → projLastIter n m X ∈ S.Ω (F + m) D n := by
    intro m
    induction m with
    | zero =>
      intro F D X hX
      simpa [projLastIter] using hX
    | succ m ih =>
      intro F D X hX
      have hX' : projLast X ∈ S.Ω (F + 1) D (n + m) := S.proj hX
      have hres : projLastIter n m (projLast X) ∈ S.Ω ((F + 1) + m) D n :=
        ih (F + 1) D (projLast X) hX'
      have heq : (F + 1) + m = F + (m + 1) := by omega
      change projLastIter n m (projLast X) ∈ S.Ω (F + (m + 1)) D n
      exact heq ▸ hres
  -- Bumping the format `F+m → F+m+n` by `mono_F`, one step at a time.
  have monoF : ∀ t (K : ℕ) (Y : Set (Fin n → ℝ)),
      Y ∈ S.Ω K D n → Y ∈ S.Ω (K + t) D n := by
    intro t
    induction t with
    | zero =>
      intro K Y hY
      simpa using hY
    | succ t ih =>
      intro K Y hY
      have hY' : Y ∈ S.Ω (K + 1) D n := S.mono_F hY
      have hres : Y ∈ S.Ω ((K + 1) + t) D n := ih (K + 1) Y hY'
      have heq : (K + 1) + t = K + (t + 1) := by omega
      exact heq ▸ hres
  exact monoF n (F + m) (projLastIter n m X) (key m F D X hX)

end Work.WilG0
