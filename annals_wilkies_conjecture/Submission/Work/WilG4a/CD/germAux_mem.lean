import Mathlib
import Submission.Work.WilG4a.CD.germDefs

namespace Work.WilG4a.CD

open WilkiesDesign

/-- Binary intersection with explicit degree bookkeeping (constant degree polynomials). -/
private theorem inter₂' {S : SOMin} {n a₁ a₂ c₁ c₂ : ℕ} {X Y : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω a₁ c₁ n) (hY : Y ∈ S.Ω a₂ c₂ n) :
    X ∩ Y ∈ S.Ω (max a₁ a₂ + 1) (c₁ + c₂) n := by
  have h := Work.WilG1.Omega.inter₂ (S := S) (D := 0) (b₁ := Polynomial.C c₁)
    (b₂ := Polynomial.C c₂) (by simpa using hX) (by simpa using hY)
  simpa [Polynomial.eval_C] using h

/-- The `Ω`-membership of the punctured fibre germ.  Route as in `inflated_mem`, but the
body is `germBody p X = bTneX p ∩ inflCell p ∩ coordPre (iotaInfl p) X`: the pullback of `X`
along `iotaInfl p`, the cell condition `(y - z(last))² < δ²`, and the inequality
`y ≠ z(last)` (a degree-`1` hypersurface complement).  Then `proj ∘ compl` gives `∀ y`, the
half-space `δ > 0` is `posHalf_y`, and a final `projLast` gives `∃ δ > 0`. -/
theorem germAux_mem (S : WilkiesDesign.SOMin) (p : ℕ) :
    ∃ (A C : ℕ), ∀ (F D : ℕ) (X : Set (Fin (p + 1) → ℝ)), X ∈ S.Ω F D (p + 1) →
      Work.WilG4a.CD.germAux p X ∈ S.Ω (F + A) (D + C) (p + 1) := by
  refine ⟨64 * (2 * p + 4) + 69, 32 * (2 * p + 4) + 40, ?_⟩
  intro F D X hX
  -- Pull `X` back along `iotaInfl p` into `ℝ^{p+3}`.
  have hPre : Work.WilG5.coordPre (iotaInfl p) X ∈
      S.Ω (F + (64 * (2 * p + 4) + 64)) (D + (32 * (2 * p + 4) + 32)) (p + 3) := by
    have h := Work.WilG5.coordPre_mem (S := S) (m := p + 1) (N := p + 3)
      (ι := iotaInfl p) (A := X) hX
    refine Work.WilG1.Omega.mono h ?_ ?_ <;> omega
  -- The atom `y ≠ z(last)` as the complement of a degree-`1` hypersurface.
  have hBE : {x : Fin (p + 3) → ℝ | x (cyl p) = x (czt p)} ∈ S.Ω (p + 3) 1 (p + 3) := by
    have h := Work.WilG1.Omega.coordEq_mem (S := S) (n := p + 3) 0 (cyl p) (czt p)
    simpa [Polynomial.eval_C] using h
  have hB : bTneX p ∈ S.Ω (p + 4) 1 (p + 3) := by
    have h := S.compl hBE
    have hset : ({x : Fin (p + 3) → ℝ | x (cyl p) = x (czt p)})ᶜ = bTneX p := by
      ext x; simp [bTneX]
    rw [hset] at h
    refine Work.WilG1.Omega.mono h ?_ ?_ <;> omega
  -- The cell condition `(y - z(last))² < δ²`.
  have hCell : inflCell p ∈ S.Ω (p + 5) 4 (p + 3) := by
    have h := inflCell_mem (S := S) p 0
    simpa [Polynomial.eval_C] using h
  have hBI : (bTneX p ∩ inflCell p) ∈ S.Ω (p + 6) 5 (p + 3) := by
    have h := inter₂' hB hCell
    refine Work.WilG1.Omega.mono h ?_ ?_ <;> omega
  -- The body `germBody p X`.
  have hBody : germBody p X ∈ S.Ω (F + (64 * (2 * p + 4) + 64) + 1)
      (D + (32 * (2 * p + 4) + 32) + 5) (p + 3) := by
    have h := inter₂' hBI hPre
    change (bTneX p ∩ inflCell p) ∩ Work.WilG5.coordPre (iotaInfl p) X ∈
      S.Ω _ _ (p + 3)
    refine Work.WilG1.Omega.mono h ?_ ?_ <;> omega
  -- `(∀ y)` is `compl ∘ projLast`.
  have hProj : projLast (germBody p X) ∈ S.Ω (F + (64 * (2 * p + 4) + 64) + 2)
      (D + (32 * (2 * p + 4) + 32) + 5) (p + 2) := by
    have h := S.proj hBody
    refine Work.WilG1.Omega.mono h ?_ ?_ <;> omega
  have hProjc : (projLast (germBody p X))ᶜ ∈ S.Ω (F + (64 * (2 * p + 4) + 64) + 3)
      (D + (32 * (2 * p + 4) + 32) + 5) (p + 2) := by
    have h := S.compl hProj
    refine Work.WilG1.Omega.mono h ?_ ?_ <;> omega
  -- The half-space `δ > 0`.
  have hPos : posHalf_y (p + 2) (Fin.last (p + 1)) ∈ S.Ω (p + 4) 3 (p + 2) := by
    have h := posHalf_mem_y (S := S) (p + 2) (Fin.last (p + 1)) 0
    refine Work.WilG1.Omega.mono h (by omega) (by simp)
  have hInt : posHalf_y (p + 2) (Fin.last (p + 1)) ∩ (projLast (germBody p X))ᶜ ∈
      S.Ω (F + (64 * (2 * p + 4) + 64) + 4) (D + (32 * (2 * p + 4) + 32) + 8)
        (p + 2) := by
    have h := inter₂' hPos hProjc
    refine Work.WilG1.Omega.mono h ?_ ?_ <;> omega
  -- `(∃ δ > 0)` is a final projection.
  have hRes : projLast (posHalf_y (p + 2) (Fin.last (p + 1)) ∩
      (projLast (germBody p X))ᶜ) ∈ S.Ω (F + (64 * (2 * p + 4) + 64) + 5)
      (D + (32 * (2 * p + 4) + 32) + 8) (p + 1) := by
    have h := S.proj hInt
    refine Work.WilG1.Omega.mono h ?_ ?_ <;> omega
  exact Work.WilG1.Omega.mono hRes (by omega) (by omega)

end Work.WilG4a.CD
