import Mathlib
import Submission.Work.WilE8.Basic
import Submission.Work.WilE10.Psi

namespace Work.WilE8.StarR

open WilkiesDesign WilkiesDesign.E

/-! ## Auxiliary facts about `psi`, `psiV`, `Fin.snoc` and `Fin.init` -/

/-- `psiV` always lands in the open cube `(-1,1)^n`. -/
lemma psiV_mem_ocube {n : ℕ} (x : Fin n → ℝ) :
    WilkiesDesign.E.psiV x ∈ Work.WilE8.ocube n :=
  fun i => Work.WilE10.psi_abs_lt_one (x i)

/-- `psiV` commutes with `Fin.snoc`. -/
lemma psiV_snoc {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    WilkiesDesign.E.psiV (Fin.snoc x t) =
      Fin.snoc (WilkiesDesign.E.psiV x) (psi t) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp only [WilkiesDesign.E.psiV, Fin.snoc_last]
  · intro j
    simp only [Fin.snoc_castSucc, WilkiesDesign.E.psiV]

/-- `Fin.init` commutes with `psiV`. -/
lemma init_psiV {n : ℕ} (z : Fin (n + 1) → ℝ) :
    Fin.init (WilkiesDesign.E.psiV z) = WilkiesDesign.E.psiV (Fin.init z) := by
  funext i; rfl

/-- `psi` is a left inverse of `psiInv` on `(-1,1)`. -/
lemma psi_psiInv {u : ℝ} (hu : |u| < 1) : psi (Work.WilE8.psiInv u) = u := by
  simpa [Work.WilE8.psiInv, Work.WilE10.psiR] using Work.WilE10.psi_psiR hu

/-! ## The main identity -/

theorem psiV_preimage_init_ocube {n : ℕ} {Z : Set (Fin (n + 1) → ℝ)} :
    WilkiesDesign.E.psiV ⁻¹'
        (Fin.init '' (WilkiesDesign.E.cubeC (n + 1) ∩ (Z ∩ Work.WilE8.ocube (n + 1))))
      = WilkiesDesign.projLast (WilkiesDesign.E.psiV ⁻¹' Z) := by
  ext x
  constructor
  · -- `psiV x` is the `Fin.init` of a point of `cubeC ∩ Z ∩ ocube`; that point is
    -- `Fin.snoc (Fin.init y) (y (last n))`, and `y (last n) = psi (psiInv (y (last n)))`.
    rintro ⟨y, ⟨hycube, hyZ, hyocube⟩, hinit⟩
    refine ⟨Work.WilE8.psiInv (y (Fin.last n)), ?_⟩
    have hpsi : psi (Work.WilE8.psiInv (y (Fin.last n))) = y (Fin.last n) :=
      psi_psiInv (hyocube (Fin.last n))
    show WilkiesDesign.E.psiV (Fin.snoc x (Work.WilE8.psiInv (y (Fin.last n)))) ∈ Z
    rw [psiV_snoc, hpsi, ← hinit, Fin.snoc_init_self]
    exact hyZ
  · -- `psiV (Fin.snoc x t)` lies in `cubeC ∩ Z ∩ ocube`, and its `Fin.init` is `psiV x`.
    rintro ⟨t, ht⟩
    exact ⟨WilkiesDesign.E.psiV (Fin.snoc x t),
      ⟨WilkiesDesign.E.psiV_mem_cube _, ht, psiV_mem_ocube _⟩,
      by rw [init_psiV, Fin.init_snoc]⟩

end Work.WilE8.StarR
