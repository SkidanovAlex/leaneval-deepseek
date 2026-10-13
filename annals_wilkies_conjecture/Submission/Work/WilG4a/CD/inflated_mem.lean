import Mathlib
import Submission.Work.WilG4a.CD.Defs
import Submission.Work.WilG4a.CD.iota_pull
import Submission.Work.WilG4a.CD.inflCell_mem
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG1.Calc.pos_mem

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilG4a.CD

open WilkiesDesign

/-! ## 1. Reading the cell `inflCell` at the point `(z, δ, y)` -/

/-- At the point `(z, δ, y) = Fin.snoc (Fin.snoc z δ) y` the cell condition
`(y - z(last))² < δ²` is the defining inequality of `inflCell`. -/
lemma mem_inflCell_snoc (p : ℕ) (z : Fin (p + 1) → ℝ) (δ y : ℝ) :
    Fin.snoc (Fin.snoc z δ) y ∈ inflCell p ↔ (y - z (Fin.last p)) ^ 2 < δ ^ 2 := by
  simp only [inflCell, cyl, cdl, czt, Set.mem_ofPred_eq, Fin.snoc_last, Fin.snoc_castSucc]

/-! ## 2. The set identity

`inflatedAux` reads: there is a `δ > 0` such that for **every** `y`, the point `(z, δ, y)` is
*not* in `inflCell ∩ Xᵖᵘˡˡ`; the `∀ y` is `compl ∘ projLast ∘ compl` and the pullback is
`coordPre (iotaInfl p) X`, which by `iota_pull` reads `Fin.snoc (Fin.init z) y ∈ X`. -/

lemma inflated_eq (p : ℕ) (X : Set (Fin (p + 1) → ℝ)) :
    inflated p X = inflatedAux p X := by
  ext z
  constructor
  · rintro ⟨δ, hδ, hX⟩
    refine ⟨δ, ?_, ?_⟩
    · simpa only [posHalf_y, Set.mem_ofPred_eq, Fin.snoc_last] using hδ
    · rintro ⟨t, hcell, hpre⟩
      have h1 : (t - z (Fin.last p)) ^ 2 < δ ^ 2 := (mem_inflCell_snoc p z δ t).mp hcell
      have h2 : |t - z (Fin.last p)| < δ := by
        have h3 : |t - z (Fin.last p)| < |δ| := (sq_lt_sq).mp h1
        rwa [abs_of_pos hδ] at h3
      have h4 : Fin.snoc (Fin.init z) t ∈ X := hX t h2
      refine hpre ?_
      show (Fin.snoc (Fin.snoc z δ) t) ∘ iotaInfl p ∈ X
      rw [iota_pull]
      exact h4
  · rintro ⟨δ, hδ, hY⟩
    have hδ' : 0 < δ := by
      simpa only [posHalf_y, Set.mem_ofPred_eq, Fin.snoc_last] using hδ
    refine ⟨δ, hδ', ?_⟩
    intro y hy
    by_contra hyX
    have hcell : Fin.snoc (Fin.snoc z δ) y ∈ inflCell p := by
      rw [mem_inflCell_snoc, sq_lt_sq]
      rwa [abs_of_pos hδ']
    have hpre : Fin.snoc (Fin.snoc z δ) y ∉ Work.WilG5.coordPre (iotaInfl p) X := by
      intro h
      refine hyX ?_
      have h' := h
      simp only [Work.WilG5.coordPre, Set.mem_ofPred_eq] at h'
      rwa [iota_pull] at h'
    exact hY ⟨y, hcell, hpre⟩

/-! ## 3. `Ω`-bookkeeping for the intersection with the constant-degree piece `inflCell` -/

private theorem inter_mixed {S : SOMin} {n : ℕ} {a₁ a₂ c₁ c₂ D : ℕ} {X Y : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω a₁ c₁ n) (hY : Y ∈ S.Ω a₂ (D + c₂) n) :
    X ∩ Y ∈ S.Ω (max a₁ a₂ + 1) (D + (c₁ + c₂)) n := by
  have h1 : X ∈ S.Ω (max a₁ a₂) c₁ n :=
    Work.WilG1.Omega.mono hX (le_max_left a₁ a₂) le_rfl
  have h2 : Y ∈ S.Ω (max a₁ a₂) (D + c₂) n :=
    Work.WilG1.Omega.mono hY (le_max_right a₁ a₂) le_rfl
  have h := S.inter (F := max a₁ a₂) (n := n) (k := 2)
    (fun i : Fin 2 => if i = 0 then c₁ else D + c₂)
    (fun i : Fin 2 => if i = 0 then X else Y)
    (by
      intro i
      fin_cases i
      · simpa using h1
      · simpa using h2)
  have hsum : (∑ i : Fin 2, (if i = 0 then c₁ else D + c₂)) = D + (c₁ + c₂) := by
    have h0 : ((0 : Fin 2) = 0) := rfl
    have h1' : ¬ ((1 : Fin 2) = 0) := by decide
    rw [Fin.sum_univ_two, ite_eq_left h0, ite_eq_right h1']
    omega
  rw [hsum] at h
  rw [Work.WilG1.Omega.iInter_fin_two] at h
  exact h

/-! ## 4. The main theorem -/

/-- The "localisation in the last coordinate" of an `Ω`-set: for `X ⊆ ℝ^{p+1}`, the set of `z` such that some interval `(z(last) - δ, z(last) + δ)` (δ > 0, same parameter coordinates) is contained in `X`; it is `Ω`-definable with format and degree exceeding those of `X` by constants depending only on `p`.

Route: in `ℝ^{p+3}` with coordinates `(z, δ, y)`, pull `X` back along `ι = Fin.lastCases (Fin.last (p+2)) (Fin.castAdd 2)` (so `(v ∘ ι) = Fin.snoc (Fin.init z) y`), intersect with the polynomial set `{δ² - (y - z(last))² > 0}` (`Work.WilG1.Calc.pos_mem`, via `Work.WilG4a.posHalf_mem_y`-style rewriting), and use `compl ∘ projLast ∘ compl` for the `∀ y`, then `posHalf_y` for `δ > 0` and a final `projLast`. -/
theorem inflated_mem (S : WilkiesDesign.SOMin) (p : ℕ) :
    ∃ (A C : ℕ), ∀ (F D : ℕ) (X : Set (Fin (p + 1) → ℝ)), X ∈ S.Ω F D (p + 1) →
      {z : Fin (p + 1) → ℝ | ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y - z (Fin.last p)| < δ →
        Fin.snoc (Fin.init z) y ∈ X} ∈ S.Ω (F + A) (D + C) (p + 1) := by
  refine ⟨64 * (2 * p + 4) + 200, 32 * (2 * p + 4) + 200, ?_⟩
  intro F D X hX
  have hCell : inflCell p ∈ S.Ω (p + 5) 4 (p + 3) := by
    have h := inflCell_mem (S := S) p D
    simpa [Polynomial.eval_C] using h
  have hPre : Work.WilG5.coordPre (iotaInfl p) X ∈
      S.Ω (F + 64 * ((p + 3) + (p + 1)) + 64)
        (D + (32 * ((p + 3) + (p + 1)) + 32)) (p + 3) := by
    have h := Work.WilG5.coordPre_mem (S := S) (ι := iotaInfl p) hX
    simpa [Nat.add_assoc] using h
  have hPrec := S.compl hPre
  have hK := inter_mixed hCell hPrec
  have hL := S.proj hK
  have hLc := S.compl hL
  have hPos : posHalf_y (p + 2) (Fin.last (p + 1)) ∈ S.Ω (p + 4) 3 (p + 2) := by
    have h := posHalf_mem_y (S := S) (p + 2) (Fin.last (p + 1)) D
    simpa [Polynomial.eval_C, show (p + 2) + 2 = p + 4 from by omega] using h
  have hM := inter_mixed hPos hLc
  have hmain := S.proj hM
  show inflated p X ∈ S.Ω (F + (64 * (2 * p + 4) + 200)) (D + (32 * (2 * p + 4) + 200))
    (p + 1)
  rw [inflated_eq]
  exact Work.WilG1.Omega.mono hmain (by omega) (by omega)

end Work.WilG4a.CD
