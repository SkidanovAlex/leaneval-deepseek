import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseRowQ2.chiLatticeParseval
import Submission.Work.BoseRowQ2.maskTailDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.tailIdentity` — the lattice tail of the sharp mask row as an explicit `tsum`

`Work.BoseRowQ2.Tail N i j` is *by definition* (`maskTailDefs`)

    `Tail N i j = Mc N i j − ∑ k : Lab N, Chat N k i * Chat N k j`,

i.e. the lattice Parseval matrix `Mc i j = χ̂²(vec (K i − K j))` corrected by the finite sum over
the fundamental cube.  The lattice Parseval identity `chiLatticeParseval` identifies the *full*
lattice sum `∑'_{m ∈ ℤ³}` with `Mc`, so splitting that sum at the cube `cube N` expresses the
correction as the honest infinite tail over the complement of the cube:

    `Tail N i j = ∑'_{m : ℤ³, m ∉ cube N} χ̂(vec (m − K i))·χ̂(vec (m − K j))`.

This is the statement the sharp mask row needs (FS l.3253); it is the same claim as the
neighbouring `Work.BoseRowQ2.tail_eq_tsum`, and for convenience the proof is written out in full
here, with only public inputs, so that this module is self-contained.

## The proof

* **Summability of the summand.**  The corpus bump is `C^∞` with compact support, so `χ̂` decays
  faster than any polynomial (`Work.BoseK15.ChiReg_corpus`, FS `lem:DecaychiHat`).  With
  `|χ̂| ≤ 1` (`chiHat_abs_le_one`) the summand is dominated by
  `C·(1 + ‖vec (m − K i)‖²)⁻⁵²`, which is summable (`Work.BoseK15.sum_inv_one_add_norm_le`,
  translated by the lattice shift).
* **The full lattice sum is `Mc`.**  Reindexing by `c ↦ c + K i` turns `∑'_{c} f c` into the
  correlation form `∑'_{m} χ̂(vec m)·χ̂(vec (m + K i − K j))`, which is `χ̂²(vec (K i − K j)) = Mc`
  by `chiLatticeParseval`.
* **The finite part over the cube is `ChatᵀChat`.**  `labVec : Lab N → cube N` is a bijection
  (`image_labVec_eq_cube`), so the finite sum over `cube N` reindexes to
  `∑ k : Lab N, Chat N k i * Chat N k j`.
* `Summable.sum_add_tsum_subtype_compl` then splits the lattice sum, and the definition of `Tail`
  reads off the difference.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowQ2

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Summability of the shifted `χ̂`-majorant.**  For every lattice shift `a : ℤ³` the shifted
decay majorant `m ↦ (1 + ‖vec (m − a)‖²)⁻⁵²` is summable: it is the translate of the summable
family `n ↦ (1 + ‖vec n‖²)⁻⁵²` (`Work.BoseK15.sum_inv_one_add_norm_le`). -/
private theorem summable_shift_majorant (a : Fin 3 → ℤ) :
    Summable (fun m : Fin 3 → ℤ => (((1 : ℝ) + ‖Work.BoseB4.vec (m - a)‖ ^ 2) ^ 52)⁻¹) := by
  obtain ⟨C0, _hC0nn, hC0⟩ := Work.BoseK15.sum_inv_one_add_norm_le 52 (by norm_num)
  have hbase : Summable (fun n : Fin 3 → ℤ => (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :=
    summable_of_sum_le (fun n => by positivity) hC0
  have h := (Equiv.summable_iff (Equiv.subRight a)
    (f := fun n : Fin 3 → ℤ => (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹)).mpr hbase
  exact h.congr (fun m => by simp [Function.comp, Equiv.subRight_apply])

theorem tailIdentity (N : ℕ) (i j : Work.BoseBoxFock.Lab N) :
    Work.BoseRowQ2.Tail N i j
      = tsum (fun m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N} =>
          Work.BoseRowQ2.chiHat (Work.BoseB4.vec (m.val - Work.BoseBoxFock.labVec N i))
            * Work.BoseRowQ2.chiHat (Work.BoseB4.vec (m.val - Work.BoseBoxFock.labVec N j))) := by
  set f : (Fin 3 → ℤ) → ℝ := fun m =>
    Work.BoseRowQ2.chiHat (Work.BoseB4.vec (m - Work.BoseBoxFock.labVec N i))
      * Work.BoseRowQ2.chiHat (Work.BoseB4.vec (m - Work.BoseBoxFock.labVec N j)) with hf
  -- ### Summability of the summand, from the Schwartz decay of the corpus `χ̂`
  have hsum : Summable f := by
    obtain ⟨Cchi, hCchi0, hChi⟩ := Work.BoseK15.ChiReg_corpus 52
    have hChat_le : ∀ p : E3,
        |Work.BoseRowQ2.chiHat p| ≤ Cchi * (((1 : ℝ) + ‖p‖ ^ 2) ^ 52)⁻¹ := by
      intro p
      have hD : 0 < (1 + ‖p‖ ^ 2) ^ 52 := by positivity
      rw [Work.BoseRowQ2.chiHat]
      calc |Work.BoseK15.corpusBox.hatChi p|
          = |Work.BoseK15.corpusBox.hatChi p| * (1 + ‖p‖ ^ 2) ^ 52
              * ((1 + ‖p‖ ^ 2) ^ 52)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hD), mul_one]
        _ ≤ Cchi * ((1 + ‖p‖ ^ 2) ^ 52)⁻¹ :=
            mul_le_mul_of_nonneg_right (hChi.1 p) (inv_nonneg.mpr hD.le)
    rw [hf]
    refine Summable.of_norm_bounded (g := fun m : Fin 3 → ℤ =>
      Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec (m - Work.BoseBoxFock.labVec N i)‖ ^ 2) ^ 52)⁻¹)
      ((summable_shift_majorant (Work.BoseBoxFock.labVec N i)).mul_left Cchi) ?_
    intro m
    rw [Real.norm_eq_abs, abs_mul]
    calc |Work.BoseRowQ2.chiHat (Work.BoseB4.vec (m - Work.BoseBoxFock.labVec N i))|
          * |Work.BoseRowQ2.chiHat (Work.BoseB4.vec (m - Work.BoseBoxFock.labVec N j))|
        ≤ (Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec (m - Work.BoseBoxFock.labVec N i)‖ ^ 2) ^ 52)⁻¹)
            * 1 :=
          mul_le_mul (hChat_le _) (Work.BoseRowQ2.chiHat_abs_le_one _) (abs_nonneg _)
            (mul_nonneg hCchi0 (inv_nonneg.mpr (by positivity)))
      _ = Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec (m - Work.BoseBoxFock.labVec N i)‖ ^ 2) ^ 52)⁻¹ := by
          ring
  -- ### The full lattice sum: the correlation form of Parseval
  have hfull : (∑' m : Fin 3 → ℤ, f m) = Work.BoseRowQ2.Mc N i j := by
    have hre : (∑' c : Fin 3 → ℤ, f c)
        = ∑' m : Fin 3 → ℤ,
            Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec m)
              * Work.BoseK15.corpusBox.hatChi
                  (Work.BoseB4.vec (m + (Work.BoseBoxFock.labVec N i
                    - Work.BoseBoxFock.labVec N j))) := by
      rw [← Equiv.tsum_eq (Equiv.addRight (Work.BoseBoxFock.labVec N i)) f]
      refine tsum_congr fun c => ?_
      simp only [hf, Work.BoseRowQ2.chiHat, Equiv.coe_addRight]
      have h1 : c + Work.BoseBoxFock.labVec N i - Work.BoseBoxFock.labVec N i = c := by
        funext t; simp only [Pi.add_apply, Pi.sub_apply]; ring
      have h2 : c + Work.BoseBoxFock.labVec N i - Work.BoseBoxFock.labVec N j
          = c + (Work.BoseBoxFock.labVec N i - Work.BoseBoxFock.labVec N j) := by
        funext t; simp only [Pi.add_apply, Pi.sub_apply]; ring
      rw [h1, h2]
    rw [hre, Work.BoseRowQ2.chiLatticeParseval]
    rfl
  -- ### The finite part over the cube is the matrix product `ChatᵀChat`
  have hfin : (∑ m ∈ Work.BoseRowQ2.cube N, f m)
      = ∑ k : Work.BoseBoxFock.Lab N,
          Work.BoseRowQ2.Chat N k i * Work.BoseRowQ2.Chat N k j := by
    rw [← Work.BoseRowQ2.image_labVec_eq_cube N]
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hf, Work.BoseRowQ2.Chat, Work.BoseRowQ2.chiHat]
    · intro x _ y _ hxy
      exact Work.BoseRowQ2.labVec_inj' N hxy
  -- ### Split the lattice sum and read off the difference
  have hsplit := hsum.sum_add_tsum_subtype_compl (s := Work.BoseRowQ2.cube N)
  rw [hfull, hfin] at hsplit
  have hEq : Work.BoseRowQ2.Mc N i j
      - (∑ k : Work.BoseBoxFock.Lab N,
          Work.BoseRowQ2.Chat N k i * Work.BoseRowQ2.Chat N k j)
      = ∑' m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N}, f m.val := by
    linarith
  simpa [Work.BoseRowQ2.Tail, hf] using hEq

end Work.BoseRowQ2
