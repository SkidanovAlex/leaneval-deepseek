import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.IvMSpec
import Submission.Work.CNum.cosT_bound

/-!
# `Work.CNum.ExpAux.csOfInterval_mem` — soundness of the Taylor enclosure `csOf`

`Work.CNum.csOf m` is the interval enclosure of `(cos y, sin y)` at `y = mπ/1024`, computed by
`TAYN = 11` steps of the Taylor iteration `tayAux`, run on the interval `angIv m` (which in turn is
an outward-rounded enclosure of `mπ/1024`).

The content of this file is that this is *sound at the level of the exact partial sums*: if
`z ∈ angIv m` is any real point of the interval, then

* `(csOf m).re` encloses `cosP z 11` (the Taylor partial sum `∑_{i ≤ 11} (-1)^i z^{2i}/(2i)!`), and
* `(csOf m).im` encloses `sinP z 11` (the Taylor partial sum `∑_{i ≤ 11} (-1)^i z^{2i+1}/(2i+1)!`).

No round-off/truncation step is involved: the statement is a pure interval-arithmetic identity, and
the proof is the induction over the `TAYN` Taylor steps of `tayAux`, using `IvMSpec` (soundness of
the four-corner interval product `IvM`), `Iv.mem_add`, `Iv.mem_neg` and the algebraic recursion
`cosTermStep`/`sinTermStep` relating consecutive terms of the series.
-/

namespace Work.CNum.ExpAux

open Work.CNum Work.ANum

/-! ## 1. The exact partial sums, as `cosP`/`sinP` read off the recursion -/

/-- The `i`-th term `(-1)^i z^{2i}/(2i)!` of the cosine series. -/
noncomputable def termC (z : ℝ) (i : ℕ) : ℝ :=
  (-1 : ℝ) ^ i * z ^ (2 * i) / ((2 * i).factorial : ℝ)

/-- The `i`-th term `(-1)^i z^{2i+1}/(2i+1)!` of the sine series. -/
noncomputable def termS (z : ℝ) (i : ℕ) : ℝ :=
  (-1 : ℝ) ^ i * z ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)

/-- The partial sum `∑_{j ≤ i} (-1)^j z^{2j}/(2j)!`. -/
noncomputable def partC (z : ℝ) (i : ℕ) : ℝ := ∑ j ∈ Finset.range (i + 1), termC z j

/-- The partial sum `∑_{j ≤ i} (-1)^j z^{2j+1}/(2j+1)!`. -/
noncomputable def partS (z : ℝ) (i : ℕ) : ℝ := ∑ j ∈ Finset.range (i + 1), termS z j

lemma partC_eq_cosP (z : ℝ) (P : ℕ) : partC z P = cosP z P := by
  simp only [partC, cosP, termC]

lemma partS_eq_sinP (z : ℝ) (P : ℕ) : partS z P = sinP z P := by
  simp only [partS, sinP, termS]

lemma partC_zero (z : ℝ) : partC z 0 = 1 := by simp [partC, termC]

lemma partS_zero (z : ℝ) : partS z 0 = z := by simp [partS, termS]

lemma partC_succ (z : ℝ) (i : ℕ) : partC z (i + 1) = partC z i + termC z (i + 1) := by
  simp only [partC]
  rw [Finset.sum_range_succ]

lemma partS_succ (z : ℝ) (i : ℕ) : partS z (i + 1) = partS z i + termS z (i + 1) := by
  simp only [partS]
  rw [Finset.sum_range_succ]

/-! ## 2. Elementary interval facts -/

/-- Soundness of `ratIv p q` at the rational point `p/q`. -/
lemma ratIvMem (p : ℤ) (q : ℕ) (hq : 0 < q) : (ratIv p q).Mem ((p : ℝ) / q) := by
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  constructor
  · show (Int.ediv (p * SC) (q : ℤ) : ℝ) / (SC : ℝ) ≤ (p : ℝ) / (q : ℝ)
    rw [div_le_div_iff₀ SC_posR hqR]
    have h' : (((Int.ediv (p * SC) (q : ℤ) : ℤ)) : ℝ) * (q : ℝ) ≤ (p : ℝ) * (SC : ℝ) := by
      exact_mod_cast Int.ediv_mul_le (p * SC) hqZ
    simpa using h'
  · show (p : ℝ) / (q : ℝ) ≤ m2r (-(Int.ediv (-(p * SC)) (q : ℤ)))
    rw [m2r, div_le_div_iff₀ hqR SC_posR, Int.cast_neg]
    have h2 : (((Int.ediv (-(p * SC)) (q : ℤ) : ℤ)) : ℝ) * (q : ℝ) ≤ -((p : ℝ) * (SC : ℝ)) := by
      have hc : ((Int.ediv (-(p * SC)) (q : ℤ) * (q : ℤ) : ℤ) : ℝ) ≤ ((-(p * SC) : ℤ) : ℝ) := by
        exact_mod_cast Int.ediv_mul_le (-(p * SC)) hqZ
      push_cast at hc
      simpa using hc
    linarith

/-! ## 3. The algebraic recursion of the Taylor terms -/

/-- One Taylor step for the cosine term: `cosTermStep`. -/
lemma cosTermStep (z : ℝ) (i : ℕ) :
    (-1 : ℝ) ^ (i + 1) * z ^ (2 * (i + 1)) / ((2 * (i + 1)).factorial : ℝ)
      = -(((-1 : ℝ) ^ i * z ^ (2 * i) / ((2 * i).factorial : ℝ)) * (z * z)) *
          (1 / (((2 * i + 1) * (2 * i + 2) : ℕ) : ℝ)) := by
  have hf : ((2 * (i + 1)).factorial : ℝ)
      = ((2 * i).factorial : ℝ) * ((2 * i + 1 : ℕ) : ℝ) * ((2 * i + 2 : ℕ) : ℝ) := by
    have h : 2 * (i + 1) = 2 * i + 2 := by ring
    rw [h, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [hf]
  have hD : (((2 * i + 1) * (2 * i + 2) : ℕ) : ℝ)
      = ((2 * i + 1 : ℕ) : ℝ) * ((2 * i + 2 : ℕ) : ℝ) := by push_cast; ring
  rw [hD]
  have h1 : (((2 * i).factorial : ℝ)) ≠ 0 := by positivity
  have h2 : ((2 * i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h3 : ((2 * i + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- One Taylor step for the sine term: `sinTermStep`. -/
lemma sinTermStep (z : ℝ) (i : ℕ) :
    (-1 : ℝ) ^ (i + 1) * z ^ (2 * (i + 1) + 1) / ((2 * (i + 1) + 1).factorial : ℝ)
      = -(((-1 : ℝ) ^ i * z ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)) * (z * z)) *
          (1 / (((2 * i + 2) * (2 * i + 3) : ℕ) : ℝ)) := by
  have hf : ((2 * (i + 1) + 1).factorial : ℝ)
      = ((2 * i + 1).factorial : ℝ) * ((2 * i + 2 : ℕ) : ℝ) * ((2 * i + 3 : ℕ) : ℝ) := by
    have h : 2 * (i + 1) + 1 = 2 * i + 3 := by ring
    rw [h, show 2 * i + 3 = (2 * i + 2) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [hf]
  have hD : (((2 * i + 2) * (2 * i + 3) : ℕ) : ℝ)
      = ((2 * i + 2 : ℕ) : ℝ) * ((2 * i + 3 : ℕ) : ℝ) := by push_cast; ring
  rw [hD]
  have h1 : (((2 * i + 1).factorial : ℝ)) ≠ 0 := by positivity
  have h2 : ((2 * i + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have h3 : ((2 * i + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-! ## 4. Soundness of the Taylor iteration `tayAux` -/

lemma tayAux_succ (y2 : Iv) (k i : ℕ) (tc ts sc ss : Iv) :
    tayAux y2 (k + 1) i tc ts sc ss =
      tayAux y2 k (i + 1)
        (IvM (Iv.neg (IvM tc y2)) (ratIv 1 ((2 * i + 1) * (2 * i + 2))))
        (IvM (Iv.neg (IvM ts y2)) (ratIv 1 ((2 * i + 2) * (2 * i + 3))))
        (Iv.add sc (IvM (Iv.neg (IvM tc y2)) (ratIv 1 ((2 * i + 1) * (2 * i + 2)))))
        (Iv.add ss (IvM (Iv.neg (IvM ts y2)) (ratIv 1 ((2 * i + 2) * (2 * i + 3))))) := rfl

lemma cosStepMem (y2 : Iv) (z : ℝ) (hz2 : y2.Mem (z * z)) (i : ℕ) (tc : Iv)
    (htc : tc.Mem (termC z i)) :
    (IvM (Iv.neg (IvM tc y2)) (ratIv 1 ((2 * i + 1) * (2 * i + 2)))).Mem (termC z (i + 1)) := by
  have h1 : (IvM tc y2).Mem (termC z i * (z * z)) := IvMSpec htc hz2
  have h2 : (Iv.neg (IvM tc y2)).Mem (-(termC z i * (z * z))) := Iv.mem_neg h1
  have h4 := IvMSpec h2 (ratIvMem 1 ((2 * i + 1) * (2 * i + 2)) (by positivity))
  have hstep : termC z (i + 1)
      = -(termC z i * (z * z)) * (1 / (((2 * i + 1) * (2 * i + 2) : ℕ) : ℝ)) :=
    cosTermStep z i
  rw [hstep]
  simpa using h4

lemma sinStepMem (y2 : Iv) (z : ℝ) (hz2 : y2.Mem (z * z)) (i : ℕ) (ts : Iv)
    (hts : ts.Mem (termS z i)) :
    (IvM (Iv.neg (IvM ts y2)) (ratIv 1 ((2 * i + 2) * (2 * i + 3)))).Mem (termS z (i + 1)) := by
  have h1 : (IvM ts y2).Mem (termS z i * (z * z)) := IvMSpec hts hz2
  have h2 : (Iv.neg (IvM ts y2)).Mem (-(termS z i * (z * z))) := Iv.mem_neg h1
  have h4 := IvMSpec h2 (ratIvMem 1 ((2 * i + 2) * (2 * i + 3)) (by positivity))
  have hstep : termS z (i + 1)
      = -(termS z i * (z * z)) * (1 / (((2 * i + 2) * (2 * i + 3) : ℕ) : ℝ)) :=
    sinTermStep z i
  rw [hstep]
  simpa using h4

/-- **Soundness of `tayAux`.**  If `y2` encloses `z * z` and the four running intervals enclose the
`i`-th term and the `i`-th partial sums, then after `k` Taylor steps the two sums enclose the
`(i+k)`-th partial sums. -/
lemma tayAux_sound (y2 : Iv) (z : ℝ) (hz2 : y2.Mem (z * z)) :
    ∀ (k i : ℕ) (tc ts sc ss : Iv), tc.Mem (termC z i) → ts.Mem (termS z i) →
      sc.Mem (partC z i) → ss.Mem (partS z i) →
      (tayAux y2 k i tc ts sc ss).1.Mem (partC z (i + k)) ∧
      (tayAux y2 k i tc ts sc ss).2.Mem (partS z (i + k)) := by
  intro k
  induction k with
  | zero =>
    intro i tc ts sc ss _ _ hsc hss
    exact ⟨hsc, hss⟩
  | succ k ih =>
    intro i tc ts sc ss htc hts hsc hss
    rw [tayAux_succ]
    have htc' : (IvM (Iv.neg (IvM tc y2)) (ratIv 1 ((2 * i + 1) * (2 * i + 2)))).Mem
        (termC z (i + 1)) := cosStepMem y2 z hz2 i tc htc
    have hts' : (IvM (Iv.neg (IvM ts y2)) (ratIv 1 ((2 * i + 2) * (2 * i + 3)))).Mem
        (termS z (i + 1)) := sinStepMem y2 z hz2 i ts hts
    have hsc' : (Iv.add sc (IvM (Iv.neg (IvM tc y2)) (ratIv 1 ((2 * i + 1) * (2 * i + 2))))).Mem
        (partC z (i + 1)) := by
      rw [partC_succ]
      exact Iv.mem_add hsc htc'
    have hss' : (Iv.add ss (IvM (Iv.neg (IvM ts y2)) (ratIv 1 ((2 * i + 2) * (2 * i + 3))))).Mem
        (partS z (i + 1)) := by
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

/-! ## 5. The main statement -/

theorem csOfInterval_mem {m : ℕ} {z : ℝ} (hz : Work.ANum.Iv.Mem (Work.CNum.angIv m) z) :
    Work.ANum.Iv.Mem (Work.CNum.csOf m).re (Work.CNum.cosP z 11) ∧
    Work.ANum.Iv.Mem (Work.CNum.csOf m).im (Work.CNum.sinP z 11) := by
  have hz2 : (IvM (angIv m) (angIv m)).Mem (z * z) := IvMSpec hz hz
  have h1 : (ratIv 1 1).Mem (termC z 0) := by
    have := ratIvMem 1 1 (by norm_num : (0 : ℕ) < 1)
    simpa [termC] using this
  have h2 : (angIv m).Mem (termS z 0) := by simpa [termS] using hz
  have h3 : (ratIv 1 1).Mem (partC z 0) := by
    have := ratIvMem 1 1 (by norm_num : (0 : ℕ) < 1)
    simpa [partC, termC] using this
  have h4 : (angIv m).Mem (partS z 0) := by simpa [partS, termS] using hz
  have hmain := tayAux_sound (IvM (angIv m) (angIv m)) z hz2
    TAYN 0 (ratIv 1 1) (angIv m) (ratIv 1 1) (angIv m) h1 h2 h3 h4
  have hre : Work.ANum.Iv.Mem (Work.CNum.csOf m).re (partC z 11) := hmain.1
  have him : Work.ANum.Iv.Mem (Work.CNum.csOf m).im (partS z 11) := hmain.2
  rw [partC_eq_cosP] at hre
  rw [partS_eq_sinP] at him
  exact ⟨hre, him⟩

end Work.CNum.ExpAux
