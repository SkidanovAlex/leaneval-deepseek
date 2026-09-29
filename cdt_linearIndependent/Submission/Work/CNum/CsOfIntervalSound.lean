import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.IvMSpec
import Submission.Work.CNum.ratIvMem
import Submission.Work.CNum.cosTermStep
import Submission.Work.CNum.sinTermStep
import Submission.Work.CNum.cosT_bound

/-!
# `Work.CNum.CsOfIntervalSound` — the Taylor enclosures of `csOf` are sound

`cosP z 11` and `sinP z 11` are the `ℂ`-free partial sums
`∑_{i ≤ 11} (-1)^i z^{2i}/(2i)!` and `∑_{i ≤ 11} (-1)^i z^{2i+1}/(2i+1)!` of the cosine and sine
Taylor series (`Work.CNum.cosP`, `Work.CNum.sinP`), and `csOf m` is the interval value of the same
two partial sums at the interval `angIv m = [mπ/1024]`, computed with outward rounding
(`Work.CNum.tayAux`).

The theorem below says that the interval evaluation is a *sound* enclosure of the real evaluation:
whenever `z` lies in the angle interval `angIv m`, the two complex-interval components of `csOf m`
contain `cosP z 11` and `sinP z 11`.

The proof is the standard interval-arithmetic soundness induction for the iteration `tayAux`:
the accumulated sums `partC z i = ∑_{j ≤ i} (-1)^j z^{2j}/(2j)!` and
`partS z i = ∑_{j ≤ i} (-1)^j z^{2j+1}/(2j+1)!` are carried through `k` steps, each step using
soundness of the operations (`IvMSpec` for the four-corner product, `Iv.mem_add`, `Iv.mem_neg`,
`ratIvMem` for rational enclosures) and the exact term recurrences `cosTermStep`, `sinTermStep`.
-/

namespace Work.CNum

open Work.ANum

/-- The `i`-th term `(-1)^i z^{2i}/(2i)!` of the cosine series. -/
noncomputable def termC (z : ℝ) (i : ℕ) : ℝ := (-1 : ℝ) ^ i * z ^ (2 * i) / ((2 * i).factorial : ℝ)

/-- The `i`-th term `(-1)^i z^{2i+1}/(2i+1)!` of the sine series. -/
noncomputable def termS (z : ℝ) (i : ℕ) : ℝ :=
  (-1 : ℝ) ^ i * z ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)

/-- The partial sum `∑_{j ≤ i} (-1)^j z^{2j}/(2j)!` of the cosine series. -/
noncomputable def partC (z : ℝ) (i : ℕ) : ℝ := ∑ j ∈ Finset.range (i + 1), termC z j

/-- The partial sum `∑_{j ≤ i} (-1)^j z^{2j+1}/(2j+1)!` of the sine series. -/
noncomputable def partS (z : ℝ) (i : ℕ) : ℝ := ∑ j ∈ Finset.range (i + 1), termS z j

lemma partC_zero (z : ℝ) : partC z 0 = 1 := by simp [partC, termC]

lemma partS_zero (z : ℝ) : partS z 0 = z := by simp [partS, termS]

lemma partC_succ (z : ℝ) (i : ℕ) : partC z (i + 1) = partC z i + termC z (i + 1) := by
  simp only [partC]
  rw [Finset.sum_range_succ]

lemma partS_succ (z : ℝ) (i : ℕ) : partS z (i + 1) = partS z i + termS z (i + 1) := by
  simp only [partS]
  rw [Finset.sum_range_succ]

/-- One unfolding step of the interval Taylor iteration `tayAux`. -/
lemma tayAux_succ (y2 : Iv) (k i : ℕ) (tc ts sc ss : Iv) :
    tayAux y2 (k + 1) i tc ts sc ss =
      tayAux y2 k (i + 1)
        (IvM (Iv.neg (IvM tc y2)) (ratIv 1 ((2 * i + 1) * (2 * i + 2))))
        (IvM (Iv.neg (IvM ts y2)) (ratIv 1 ((2 * i + 2) * (2 * i + 3))))
        (Iv.add sc (IvM (Iv.neg (IvM tc y2)) (ratIv 1 ((2 * i + 1) * (2 * i + 2)))))
        (Iv.add ss (IvM (Iv.neg (IvM ts y2)) (ratIv 1 ((2 * i + 2) * (2 * i + 3))))) := rfl

/-- The cosine half of one iteration step of `tayAux` is sound. -/
lemma cosStepMem (y2 : Iv) (z : ℝ) (hz2 : y2.Mem (z * z)) (i : ℕ) (tc : Iv)
    (htc : tc.Mem (termC z i)) :
    (IvM (Iv.neg (IvM tc y2)) (ratIv 1 ((2 * i + 1) * (2 * i + 2)))).Mem (termC z (i + 1)) := by
  have h1 : (IvM tc y2).Mem (termC z i * (z * z)) := IvMSpec htc hz2
  have h2 : (Iv.neg (IvM tc y2)).Mem (-(termC z i * (z * z))) := Iv.mem_neg h1
  have h3 : (ratIv 1 ((2 * i + 1) * (2 * i + 2))).Mem
      (1 / (((2 * i + 1) * (2 * i + 2) : ℕ) : ℝ)) := by
    have h := ratIvMem (q := (2 * i + 1) * (2 * i + 2)) 1
      (Nat.mul_pos (Nat.succ_pos (2 * i)) (Nat.succ_pos (2 * i + 1)))
    simpa using h
  have h4 := IvMSpec h2 h3
  have hstep : termC z (i + 1)
      = -(termC z i * (z * z)) * (1 / (((2 * i + 1) * (2 * i + 2) : ℕ) : ℝ)) :=
    cosTermStep z i
  rw [hstep]
  exact h4

/-- The sine half of one iteration step of `tayAux` is sound. -/
lemma sinStepMem (y2 : Iv) (z : ℝ) (hz2 : y2.Mem (z * z)) (i : ℕ) (ts : Iv)
    (hts : ts.Mem (termS z i)) :
    (IvM (Iv.neg (IvM ts y2)) (ratIv 1 ((2 * i + 2) * (2 * i + 3)))).Mem (termS z (i + 1)) := by
  have h1 : (IvM ts y2).Mem (termS z i * (z * z)) := IvMSpec hts hz2
  have h2 : (Iv.neg (IvM ts y2)).Mem (-(termS z i * (z * z))) := Iv.mem_neg h1
  have h3 : (ratIv 1 ((2 * i + 2) * (2 * i + 3))).Mem
      (1 / (((2 * i + 2) * (2 * i + 3) : ℕ) : ℝ)) := by
    have h := ratIvMem (q := (2 * i + 2) * (2 * i + 3)) 1
      (Nat.mul_pos (Nat.succ_pos (2 * i + 1)) (Nat.succ_pos (2 * i + 2)))
    simpa using h
  have h4 := IvMSpec h2 h3
  have hstep : termS z (i + 1)
      = -(termS z i * (z * z)) * (1 / (((2 * i + 2) * (2 * i + 3) : ℕ) : ℝ)) :=
    sinTermStep z i
  rw [hstep]
  exact h4

/-- Soundness of the interval Taylor iteration: after `k` steps starting at index `i`, the two
accumulators of `tayAux` enclose the real partial sums `partC z (i+k)` and `partS z (i+k)`,
provided the state at index `i` encloses the corresponding terms and partial sums and
`y2` encloses `z * z`. -/
lemma tayAux_sound (y2 : Iv) (z : ℝ) (hz2 : y2.Mem (z * z)) :
    ∀ (k i : ℕ) (tc ts sc ss : Iv), tc.Mem (termC z i) → ts.Mem (termS z i) →
      sc.Mem (partC z i) → ss.Mem (partS z i) →
      (tayAux y2 k i tc ts sc ss).1.Mem (partC z (i + k)) ∧
      (tayAux y2 k i tc ts sc ss).2.Mem (partS z (i + k)) := by
  intro k
  induction k with
  | zero =>
    intro i tc ts sc ss htc hts hsc hss
    exact ⟨hsc, hss⟩
  | succ k ih =>
    intro i tc ts sc ss htc hts hsc hss
    rw [tayAux_succ]
    have htc' : (IvM (Iv.neg (IvM tc y2)) (ratIv 1 ((2 * i + 1) * (2 * i + 2)))).Mem (termC z (i + 1)) :=
      cosStepMem y2 z hz2 i tc htc
    have hts' : (IvM (Iv.neg (IvM ts y2)) (ratIv 1 ((2 * i + 2) * (2 * i + 3)))).Mem (termS z (i + 1)) :=
      sinStepMem y2 z hz2 i ts hts
    have hsc' : (Iv.add sc (IvM (Iv.neg (IvM tc y2)) (ratIv 1 ((2 * i + 1) * (2 * i + 2))))).Mem (partC z (i + 1)) := by
      rw [partC_succ]
      exact Iv.mem_add hsc htc'
    have hss' : (Iv.add ss (IvM (Iv.neg (IvM ts y2)) (ratIv 1 ((2 * i + 2) * (2 * i + 3))))).Mem (partS z (i + 1)) := by
      rw [partS_succ]
      exact Iv.mem_add hss hts'
    have h := ih (i + 1)
      (IvM (Iv.neg (IvM tc y2)) (ratIv 1 ((2 * i + 1) * (2 * i + 2))))
      (IvM (Iv.neg (IvM ts y2)) (ratIv 1 ((2 * i + 2) * (2 * i + 3))))
      (Iv.add sc (IvM (Iv.neg (IvM tc y2)) (ratIv 1 ((2 * i + 1) * (2 * i + 2)))))
      (Iv.add ss (IvM (Iv.neg (IvM ts y2)) (ratIv 1 ((2 * i + 2) * (2 * i + 3)))))
      htc' hts' hsc' hss'
    have hidx : i + (k + 1) = (i + 1) + k := by omega
    refine ⟨?_, ?_⟩
    · rw [hidx]; exact h.1
    · rw [hidx]; exact h.2

theorem CsOfIntervalSound {m : ℕ} {z : ℝ} (hz : (angIv m).Mem z) :
    (csOf m).re.Mem (cosP z 11) ∧ (csOf m).im.Mem (sinP z 11) := by
  have hz2 : (IvM (angIv m) (angIv m)).Mem (z * z) := IvMSpec hz hz
  have h1 : (ratIv 1 1).Mem (termC z 0) := by
    have h := ratIvMem 1 (by norm_num : (0 : ℕ) < 1)
    simpa [termC] using h
  have h2 : (angIv m).Mem (termS z 0) := by simpa [termS] using hz
  have h3 : (ratIv 1 1).Mem (partC z 0) := by
    have h := ratIvMem 1 (by norm_num : (0 : ℕ) < 1)
    simpa [partC, termC] using h
  have h4 : (angIv m).Mem (partS z 0) := by simpa [partS, termS] using hz
  have hmain := tayAux_sound (y2 := IvM (angIv m) (angIv m)) (z := z) hz2
    TAYN 0 (ratIv 1 1) (angIv m) (ratIv 1 1) (angIv m) h1 h2 h3 h4
  exact hmain

end Work.CNum
