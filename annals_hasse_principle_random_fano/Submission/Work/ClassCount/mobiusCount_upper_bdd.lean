import Mathlib
import Submission.Work.HP.HP2.ClassCountPrelude
import Submission.Work.HP.HP2.grid_coset_upper
import Submission.Work.HP.PFCountDefs
import Submission.Work.HP.HP2.exists_coset_rep
import Submission.Work.ClassCount.mobiusCount_le_coset_ncard
import Submission.Work.ClassCount.volume_thickNbd_coneRegion_le

namespace Work.ClassCount

open MeasureTheory

/-- The number of integer points of the coset `c + W ℤ^{n+1}` lying in the cone region of radius
`R/k` is at most `vol(thickNbd (coneRegion))/W^{n+1}`.  This is `Work.HP.HP2.grid_coset_upper`
with `m = n + 1`, after identifying the two descriptions of the thickened set. -/
theorem coset_ncard_le_thickNbd (d n : ℕ) (a : Work.HP.Mon d n → ℤ) (c : Fin (n + 1) → ℤ)
    (W k : ℕ) (α R : ℝ) (hW : 0 < W) :
    (({v : Fin (n + 1) → ℤ | (∀ i, (W : ℤ) ∣ v i - c i) ∧
        Work.HP.toR v ∈ Work.HP.coneRegion d n a α (R / (k : ℝ))} : Set (Fin (n + 1) → ℤ)).ncard : ℝ)
      ≤ (MeasureTheory.volume (Work.HP.HP2.thickNbd (n + 1)
          (8 * ((n : ℝ) + 1) * (W : ℝ))
          (Work.HP.coneRegion d n a α (R / (k : ℝ))))).toReal / (W : ℝ) ^ (n + 1) := by
  have h := Work.HP.HP2.grid_coset_upper (n + 1) (by omega) W hW c
      (Work.HP.coneRegion d n a α (R / (k : ℝ)))
      (Work.HP.HP2.isClosed_coneRegion d n a α _) (Work.HP.HP2.isBounded_coneRegion d n a α _)
  have hset : ({x : Fin (n + 1) → ℝ | ∃ y ∈ Work.HP.coneRegion d n a α (R / (k : ℝ)),
      Work.HP.rNorm (x - y) ≤ 8 * (((n + 1 : ℕ)) : ℝ) * (W : ℝ)} : Set (Fin (n + 1) → ℝ))
      = Work.HP.HP2.thickNbd (n + 1) (8 * ((n : ℝ) + 1) * (W : ℝ))
          (Work.HP.coneRegion d n a α (R / (k : ℝ))) := by
    ext x
    simp only [Work.HP.HP2.thickNbd, Set.mem_ofPred_eq]
    constructor <;> rintro ⟨y, hy, hle⟩ <;> exact ⟨y, hy, by push_cast at hle ⊢; linarith⟩
  rw [hset] at h
  exact h

/-- **Per-`k` upper bound for `mobiusCount`** (pointwise version).  Under the same hypotheses as
`mobiusCount_lower_bdd`, `mobiusCount ≤ (3/2)·vol(coneRegion R)/(W^{n+1} k^{n+1})`.

Route: with the same coset representative `c`, `mobiusCount`'s set is contained in the coset set
`{v | (∀ i, W ∣ v i - c i) ∧ toR v ∈ S}`, `S := coneRegion d n a α (R/k)`.  `grid_coset_upper`
bounds this by `vol(S ⊕ B(8(n+1)W))/W^{n+1}`; and
`S ⊕ B(8(n+1)W) ⊆ S ∪ (frontier S ⊕ B(8(n+1)W))` (the segment from a point of `S` to a point
outside `S` meets the frontier), so subadditivity and `TubeOk d n a α (R/k) W` give
`vol(S ⊕ B(8(n+1)W)) ≤ (3/2) vol S`.  Divide by `W^{n+1}` and use `coneRegion_volume_div`. -/
theorem mobiusCount_upper_bdd (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n)
    (a : Work.HP.Mon d n → ℤ) (b : Fin (n + 1) → ℤ) (W k : ℕ) (α R T₀ : ℝ)
    (hW : 0 < W) (hk1 : 1 ≤ k) (hα : 1 ≤ α) (hR1 : 1 ≤ R)
    (hcop : Nat.Coprime k W)
    (hnot0 : ¬ ∀ i, (W : ℤ) ∣ b i)
    (hT01 : 1 ≤ T₀) (hkT : (k : ℝ) * T₀ ≤ R)
    (hTube : Work.HP.TubeOk d n a α (R / (k : ℝ)) (W : ℝ)) :
    ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ)
      ≤ (3 / 2) * ((MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal / (W : ℝ) ^ (n + 1))
        / (k : ℝ) ^ (n + 1) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hα0 : (0 : ℝ) < α := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  obtain ⟨c, hc⟩ := Work.HP.HP2.exists_coset_rep W k b hcop
  have h1 : (Work.HP.mobiusCount d n a b W k α R : ℕ)
      ≤ ({v : Fin (n + 1) → ℤ | (∀ i, (W : ℤ) ∣ v i - c i) ∧
          Work.HP.toR v ∈ Work.HP.coneRegion d n a α (R / (k : ℝ))} : Set (Fin (n + 1) → ℤ)).ncard :=
    mobiusCount_le_coset_ncard d n a b c W k α R hc hcop
  have h1' : ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ)
      ≤ (({v : Fin (n + 1) → ℤ | (∀ i, (W : ℤ) ∣ v i - c i) ∧
          Work.HP.toR v ∈ Work.HP.coneRegion d n a α (R / (k : ℝ))} : Set (Fin (n + 1) → ℤ)).ncard : ℝ) :=
    Nat.cast_le.mpr h1
  have h2 := coset_ncard_le_thickNbd d n a c W k α R hW
  have h3 := volume_thickNbd_coneRegion_le d n a α (R / (k : ℝ)) (W : ℝ) hWpos.le hTube
  have h4 : (MeasureTheory.volume (Work.HP.coneRegion d n a α (R / (k : ℝ)))).toReal
      = (MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal / (k : ℝ) ^ (n + 1) :=
    Work.HP.HP2.coneRegion_volume_div d n a hα0 hR0 (by omega : 0 < k)
  have hWpow : (0 : ℝ) < (W : ℝ) ^ (n + 1) := pow_pos hWpos _
  refine le_trans h1' ?_
  refine le_trans h2 ?_
  refine le_trans (div_le_div_of_nonneg_right h3 hWpow.le) ?_
  rw [h4]
  refine le_of_eq ?_
  field_simp

end Work.ClassCount
