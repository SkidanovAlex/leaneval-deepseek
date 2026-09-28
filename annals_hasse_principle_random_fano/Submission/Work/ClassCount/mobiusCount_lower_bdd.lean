import Mathlib
import Submission.Work.HP.HP2.ClassCountPrelude
import Submission.Work.HP.HP2.grid_coset_lower
import Submission.Work.HP.HP2.coset_eq_mobiusSet
import Submission.Work.HP.HP2.exists_coset_rep
import Submission.Work.HP.PFCountDefs

namespace Work.ClassCount

/-- **Per-`k` lower bound for `mobiusCount`** (pointwise version).  With `W, k ≥ 1`,
`α, R, T₀ ≥ 1`, `k · T₀ ≤ R`, `Nat.Coprime k W`, `¬ ∀ i, W ∣ b i`, and the tube condition
`TubeOk d n a α (R/k) W`, the number of nonzero `z` with `k z ≡ b (mod W)`, `‖z‖ ≤ R/k`, in the
cone region is at least `(1/2)·vol(coneRegion R)/(W^{n+1} k^{n+1})`.

Route: since `Nat.Coprime k W`, fix a coset representative `c` with `W ∣ k c i - b i` for all `i`
(e.g. `c i` the integer representative of `(k : ZMod W)⁻¹ * (b i : ZMod W)`).  Then
`W ∣ k z i - b i  ⟺  W ∣ z i - c i` (Euclid, from `IsCoprime`).  Apply
`grid_coset_lower (n+1) _ W hW c S hclosed hbd hTube` with `S := coneRegion d n a α (R/k)`:
its counting set is `{v | (∀ i, W ∣ v i - c i) ∧ toR v ∈ S}`, which equals the `mobiusCount` set
because `toR v ∈ coneRegion` unfolds (via `mem_coneRegion_toR`) to `eNorm v ≤ R/k` plus the cone
condition, and because `0` is *not* in the coset (`¬ ∀ i, W ∣ c i`, since `W ∣ c i ⟹ W ∣ b i`).
Finally `vol(coneRegion (R/k)) = vol(coneRegion R)/k^{n+1}` (`coneRegion_volume_div`). -/
theorem mobiusCount_lower_bdd (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n)
    (a : Work.HP.Mon d n → ℤ) (b : Fin (n + 1) → ℤ) (W k : ℕ) (α R T₀ : ℝ)
    (hW : 0 < W) (hk1 : 1 ≤ k) (hα : 1 ≤ α) (hR1 : 1 ≤ R)
    (hcop : Nat.Coprime k W)
    (hnot0 : ¬ ∀ i, (W : ℤ) ∣ b i)
    (hT01 : 1 ≤ T₀) (hkT : (k : ℝ) * T₀ ≤ R)
    (hTube : Work.HP.TubeOk d n a α (R / (k : ℝ)) (W : ℝ)) :
    (1 / 2) * ((MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal / (W : ℝ) ^ (n + 1))
        / (k : ℝ) ^ (n + 1)
      ≤ ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hRpos : (0 : ℝ) < R := by linarith
  have hαpos : (0 : ℝ) < α := by linarith
  -- the tube condition, in the form required by `grid_coset_lower` for `m = n + 1`
  have hTube' : (MeasureTheory.volume {x : Fin (n + 1) → ℝ | ∃ y ∈
        frontier (Work.HP.coneRegion d n a α (R / (k : ℝ))),
        Work.HP.rNorm (x - y) ≤ 8 * ((n + 1 : ℕ) : ℝ) * (W : ℝ)}).toReal
      ≤ (1 / 2) * (MeasureTheory.volume (Work.HP.coneRegion d n a α (R / (k : ℝ)))).toReal := by
    simpa only [Work.HP.TubeOk, Nat.cast_add, Nat.cast_one] using hTube
  -- a representative `c` of the coset `k⁻¹ b` modulo `W`
  obtain ⟨c, hc⟩ := Work.HP.HP2.exists_coset_rep W k b hcop
  -- the lattice-point lower bound for the coset `c mod W`
  have hgrid := Work.HP.HP2.grid_coset_lower (n + 1) (by omega) W hW c
    (Work.HP.coneRegion d n a α (R / (k : ℝ)))
    (Work.HP.HP2.isClosed_coneRegion d n a α _)
    (Work.HP.HP2.isBounded_coneRegion d n a α _) hTube'
  -- the integer points of the coset are exactly the `mobiusCount` set
  have hset := Work.HP.HP2.coset_eq_mobiusSet (d := d) (n := n) a b c W k α (R / (k : ℝ))
    hc hcop hnot0
  rw [hset] at hgrid
  -- scaling of the cone region volume
  have hvol := Work.HP.HP2.coneRegion_volume_div d n a hαpos hRpos (k := k) (by omega)
  calc (1 / 2) * ((MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal
          / (W : ℝ) ^ (n + 1)) / (k : ℝ) ^ (n + 1)
      = (1 / 2) * (MeasureTheory.volume (Work.HP.coneRegion d n a α (R / (k : ℝ)))).toReal
          / (W : ℝ) ^ (n + 1) := by rw [hvol]; ring
    _ ≤ ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ) := by
        simpa only [Work.HP.mobiusCount] using hgrid

end Work.ClassCount
