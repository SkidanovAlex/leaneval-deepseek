import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.LadderP

def dilatePi (c : ℤ) {t : ℕ} (q : Fin t → ℤ) (L : ℕ) :
    ((i : Fin t) → {x : ℤ // x ∈ Work.Peluse.arithIcc (q i) L}) →
      ((i : Fin t) → {x : ℤ // x ∈ Work.Peluse.arithIcc (c * q i) L}) :=
  fun h i => ⟨c * (h i).1, by
    obtain ⟨n, hn, hx⟩ := Finset.mem_image.mp (h i).2
    exact Finset.mem_image.mpr ⟨n, hn, by rw [← hx]; ring⟩⟩

/-! ## The dilation is a bijection

For a fixed anchor `a : ℤ`, multiplication by a nonzero `c` maps
`arithIcc a L` bijectively onto `arithIcc (c * a) L`.  -/

/-- The arithmetic-progression subtype at `a` is in bijection with the one at `c * a`,
via `x ↦ c * x` (inverse `y ↦ y / c`). -/
def dilateEquiv (c : ℤ) (hc : c ≠ 0) (a : ℤ) (L : ℕ) :
    {x : ℤ // x ∈ Work.Peluse.arithIcc a L} ≃
      {x : ℤ // x ∈ Work.Peluse.arithIcc (c * a) L} where
  toFun x := ⟨c * x.1, by
    obtain ⟨n, hn, hx⟩ := Finset.mem_image.mp x.2
    exact Finset.mem_image.mpr ⟨n, hn, by rw [← hx]; ring⟩⟩
  invFun y := ⟨y.1 / c, by
    obtain ⟨n, hn, hy⟩ := Finset.mem_image.mp y.2
    refine Finset.mem_image.mpr ⟨n, hn, ?_⟩
    rw [← hy]
    rw [show (c * a) * (n : ℤ) = c * (a * (n : ℤ)) by ring,
      Int.mul_ediv_cancel_left (a * (n : ℤ)) hc]⟩
  left_inv x := Subtype.ext (Int.mul_ediv_cancel_left x.1 hc)
  right_inv y := by
    apply Subtype.ext
    show c * (y.1 / c) = y.1
    obtain ⟨n, hn, hy⟩ := Finset.mem_image.mp y.2
    have hdiv : y.1 / c = a * (n : ℤ) := by
      rw [← hy]
      rw [show (c * a) * (n : ℤ) = c * (a * (n : ℤ)) by ring,
        Int.mul_ediv_cancel_left (a * (n : ℤ)) hc]
    rw [hdiv, ← hy]
    ring

/-- Coordinatewise dilation on the product of the progression subtypes. -/
def dilatePiEquiv (c : ℤ) (hc : c ≠ 0) {t : ℕ} (q : Fin t → ℤ) (L : ℕ) :
    ((i : Fin t) → {x : ℤ // x ∈ Work.Peluse.arithIcc (q i) L}) ≃
      ((i : Fin t) → {x : ℤ // x ∈ Work.Peluse.arithIcc (c * q i) L}) :=
  Equiv.piCongrRight (fun i => dilateEquiv c hc (q i) L)

theorem sum_pi_dilate {t : ℕ} {c : ℤ} (hc : c ≠ 0) (q : Fin t → ℤ) (L : ℕ)
    (F : ((i : Fin t) → {x : ℤ // x ∈ Work.Peluse.arithIcc (c * q i) L}) → ℂ) :
    ∑ H, F H = ∑ h : ((i : Fin t) → {x : ℤ // x ∈ Work.Peluse.arithIcc (q i) L}),
      F (dilatePi c q L h) := by
  have hd : dilatePi c q L = ⇑(dilatePiEquiv c hc q L) := by
    funext h i
    exact Subtype.ext rfl
  rw [hd]
  exact (Equiv.sum_comp (dilatePiEquiv c hc q L) F).symm

end Work.Peluse.LadderP
