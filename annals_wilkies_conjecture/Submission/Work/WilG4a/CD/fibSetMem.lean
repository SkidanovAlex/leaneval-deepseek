/-
  WilG4a / CD / `fibSetMem` — the `Ω`-bookkeeping for the `Ω`-approximation `R = fibMainSet`.

  * `fibLimitSet_mem` / `fibCauchySet_mem` are the two generic fibre constructions of
    `Submission.Work.WilG4a.CD.fibreLimitEqMem` / `fibreLimitMem`, restated in the vocabulary of
    `fibDerivDefs`.
  * `fibValLim_mem` / `fibValC_mem` specialise the value limit to the family itself.
  * `fibMainSet_mem_of_germ` assembles the four conjuncts of `R` — the fibre germ, the fibre
    continuity of `f`, the limit of the `j`-th joint `x`-derivative along the fibre, and the
    existence of the limits of the lower ones — with all format/degree bookkeeping: the extra
    atoms cost only constants in the format, and the degree is a fixed polynomial in `(D, j)`
    (the `Fin j`-indexed intersection costs the *count* `j` times the degree bound, which is
    absorbed by multiplying the polynomial by `X 1`).
-/
import Mathlib
import Submission.Work.WilG4a.CD.fibDerivDefs
import Submission.Work.WilG4a.CD.fibreLimitEqMem
import Submission.Work.WilG4a.CD.fibreLimitMem
import Submission.Work.WilG4a.CD.badLoci_cellDecomp
import Submission.Work.WilG0.API

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical
namespace Work.WilG4a.CD
open WilkiesDesign

variable {S : WilkiesDesign.SOMin}

/-! ## Monotonicity of the degree polynomials -/

/-- The evaluation of a two-variable polynomial with natural coefficients is monotone in the
pointwise order on the evaluation points. -/
theorem mv2_eval_le {b : MvPolynomial (Fin 2) ℕ} {D j D' j' : ℕ} (hD : D ≤ D') (hj : j ≤ j') :
    MvPolynomial.eval ![D, j] b ≤ MvPolynomial.eval ![D', j'] b :=
  eval_le_eval_of_le (fun s => by fin_cases s <;> simp [hD, hj]) b

/-- The evaluation of a univariate polynomial with natural coefficients is monotone. -/
theorem poly_eval_mono (b : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : b.eval x ≤ b.eval y := by
  have h1 : b.eval x = MvPolynomial.eval ![x, 0]
      (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) b) := by
    rw [eval_eval₂_C]; simp
  have h2 : b.eval y = MvPolynomial.eval ![y, 0]
      (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) b) := by
    rw [eval_eval₂_C]; simp
  rw [h1, h2]
  exact mv2_eval_le h le_rfl

/-! ## The two generic fibre constructions -/

theorem fibLimitSet_mem {p : ℕ} :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ {F D : ℕ} (A : Set (Fin (p + 2) → ℝ)), A ∈ S.Ω F D (p + 2) →
        fibLimitSet A ∈ S.Ω (F + a) (b.eval D) (p + 2) :=
  fibreLimitEqMem (p := p)

theorem fibCauchySet_mem {p : ℕ} :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ {F D : ℕ} (A : Set (Fin (p + 2) → ℝ)), A ∈ S.Ω F D (p + 2) →
        fibCauchySet A ∈ S.Ω (F + a) (b.eval D) (p + 1) :=
  fibreLimitMem (p := p)

/-! ## The value limit of the family itself -/

theorem fibValLim_mem (p F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        fibValLim f ∈ S.Ω (F0 + a) (b.eval D) (p + 1 + 1) := by
  obtain ⟨a, b, h⟩ := fibLimitSet_mem (S := S) (p := p)
  exact ⟨a, b, fun D f hf => h (Work.WilG4a.graphFam f) hf⟩

theorem fibValC_mem (p F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        fibValC f ∈ S.Ω a (b.eval D) (p + 1) := by
  obtain ⟨a, b, h⟩ := fibValLim_mem (S := S) p F0
  refine ⟨F0 + a + 2, (b + Polynomial.X) + (b + Polynomial.X), ?_⟩
  intro D f hf
  have hL : fibValLim f ∈ S.Ω (F0 + a) (b.eval D) (p + 2) := h D hf
  have hL' : fibValLim f ∈ S.Ω (F0 + a) (b.eval D + D) (p + 2) :=
    Work.WilG0.Omega_mono_D (by omega) hL
  have hG' : Work.WilG4a.graphFam f ∈ S.Ω (F0 + a) (b.eval D + D) (p + 2) :=
    Work.WilG0.Omega_mono_FD (by omega) (by omega) hf
  have hI : fibValLim f ∩ Work.WilG4a.graphFam f ∈
      S.Ω (F0 + a + 1) ((b.eval D + D) + (b.eval D + D)) (p + 2) :=
    Work.WilG0.Omega_inter2 hL' hG'
  have hdeg : (b.eval D + D) + (b.eval D + D) =
      Polynomial.eval D ((b + Polynomial.X) + (b + Polynomial.X)) := by
    simp only [Polynomial.eval_add, Polynomial.eval_X]
  exact Work.WilG0.Omega_mono_FD (by omega) (le_of_eq hdeg) (S.proj hI)

/-! ## The `Ω`-approximation `R` -/

theorem fibMainSet_mem_of_germ (hder : WilkiesDesign.SOMin.SharpDeriv S) (p F0 : ℕ)
    (aG : ℕ) (bG : MvPolynomial (Fin 2) ℕ)
    (hgerm : ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ},
      Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        fibGerm f j ∈ S.Ω aG (MvPolynomial.eval ![D, j] bG) (p + 1)) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ},
        Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        fibMainSet f j ∈ S.Ω a (MvPolynomial.eval ![D, j] b) (p + 2) := by
  obtain ⟨aLim, bLim, hLim⟩ := fibLimitSet_mem (S := S) (p := p)
  obtain ⟨aV, bV, hV⟩ := fibValC_mem (S := S) p F0
  obtain ⟨aDg, bDg, hDg⟩ := Work.WilG4a.derivGraphSet_mem S hder p F0
  refine ⟨((aG + 1) + (aV + 1) + (aDg + aLim + 3) + 1) + 3,
    bG + Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) bV
      + Polynomial.eval₂ MvPolynomial.C bDg bLim
      + MvPolynomial.X 1 * Polynomial.eval₂ MvPolynomial.C bDg bLim, ?_⟩
  intro D j f hf
  have hBg : MvPolynomial.eval ![D, j]
      (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) bV) = bV.eval D := by
    rw [eval_eval₂_C]; simp
  have hBl : MvPolynomial.eval ![D, j] (Polynomial.eval₂ MvPolynomial.C bDg bLim) =
      bLim.eval (MvPolynomial.eval ![D, j] bDg) :=
    eval_eval₂_C bDg bLim D j
  -- the four pieces of `R`
  have h1 : {w : Fin (p + 2) → ℝ | Fin.init w ∈ fibGerm f j} ∈
      S.Ω (aG + 1) (MvPolynomial.eval ![D, j] bG) (p + 2) :=
    S.prod_right (hgerm D j hf)
  have h2 : {w : Fin (p + 2) → ℝ | Fin.init w ∈ fibValC f} ∈
      S.Ω (aV + 1) (bV.eval D) (p + 2) :=
    S.prod_right (hV D hf)
  have h2' : {w : Fin (p + 2) → ℝ | Fin.init w ∈ fibValC f} ∈
      S.Ω (aV + 1) (MvPolynomial.eval ![D, j]
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) bV)) (p + 2) :=
    Work.WilG0.Omega_mono_FD le_rfl (le_of_eq hBg.symm) h2
  have h3 : fibLimSet f j ∈ S.Ω (aDg + aLim)
      (bLim.eval (MvPolynomial.eval ![D, j] bDg)) (p + 2) :=
    hLim (Work.WilG4a.derivGraphSet f j) (hDg D j hf)
  have h3' : fibLimSet f j ∈ S.Ω (aDg + aLim)
      (MvPolynomial.eval ![D, j] (Polynomial.eval₂ MvPolynomial.C bDg bLim)) (p + 2) :=
    Work.WilG0.Omega_mono_FD le_rfl (le_of_eq hBl.symm) h3
  -- the `Fin j`-indexed intersection over the lower derivative limits
  have hfam : ∀ m : Fin j,
      {w : Fin (p + 2) → ℝ | Fin.init w ∈ projLast (fibLimSet f ((m : ℕ) + 1))} ∈
        S.Ω (aDg + aLim + 2)
          (MvPolynomial.eval ![D, j] (Polynomial.eval₂ MvPolynomial.C bDg bLim)) (p + 2) := by
    intro m
    have hDm : Work.WilG4a.derivGraphSet f ((m : ℕ) + 1) ∈
        S.Ω aDg (MvPolynomial.eval ![D, (m : ℕ) + 1] bDg) (p + 2) :=
      hDg D ((m : ℕ) + 1) hf
    have hLm : fibLimSet f ((m : ℕ) + 1) ∈ S.Ω (aDg + aLim)
        (bLim.eval (MvPolynomial.eval ![D, (m : ℕ) + 1] bDg)) (p + 2) :=
      hLim (Work.WilG4a.derivGraphSet f ((m : ℕ) + 1)) hDm
    have hPm : projLast (fibLimSet f ((m : ℕ) + 1)) ∈ S.Ω (aDg + aLim + 1)
        (bLim.eval (MvPolynomial.eval ![D, (m : ℕ) + 1] bDg)) (p + 1) :=
      S.proj hLm
    have hPm' : {w : Fin (p + 2) → ℝ | Fin.init w ∈ projLast (fibLimSet f ((m : ℕ) + 1))} ∈
        S.Ω (aDg + aLim + 2)
          (bLim.eval (MvPolynomial.eval ![D, (m : ℕ) + 1] bDg)) (p + 2) :=
      S.prod_right hPm
    refine Work.WilG0.Omega_mono_FD (by omega) ?_ hPm'
    rw [hBl]
    exact poly_eval_mono bLim (mv2_eval_le le_rfl (by omega))
  have h4 : (⋂ m : Fin j,
      {w : Fin (p + 2) → ℝ | Fin.init w ∈ projLast (fibLimSet f ((m : ℕ) + 1))}) ∈
      S.Ω (aDg + aLim + 3) (j * MvPolynomial.eval ![D, j]
        (Polynomial.eval₂ MvPolynomial.C bDg bLim)) (p + 2) := by
    have hinter := S.inter (fun _ : Fin j => MvPolynomial.eval ![D, j]
        (Polynomial.eval₂ MvPolynomial.C bDg bLim))
      (fun m : Fin j => {w : Fin (p + 2) → ℝ | Fin.init w ∈ projLast (fibLimSet f ((m : ℕ) + 1))})
      hfam
    have hsum : (∑ _ : Fin j, MvPolynomial.eval ![D, j]
        (Polynomial.eval₂ MvPolynomial.C bDg bLim)) = j * MvPolynomial.eval ![D, j]
          (Polynomial.eval₂ MvPolynomial.C bDg bLim) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [hsum] at hinter
    exact Work.WilG0.Omega_mono_FD (by omega) le_rfl hinter
  -- raise everything to the common format
  have h1F := Work.WilG0.Omega_mono_FD (F := (aG + 1))
    (F' := (aG + 1) + (aV + 1) + (aDg + aLim + 3) + 1) (by omega) le_rfl h1
  have h2F := Work.WilG0.Omega_mono_FD (F := (aV + 1))
    (F' := (aG + 1) + (aV + 1) + (aDg + aLim + 3) + 1) (by omega) le_rfl h2'
  have h3F := Work.WilG0.Omega_mono_FD (F := (aDg + aLim))
    (F' := (aG + 1) + (aV + 1) + (aDg + aLim + 3) + 1) (by omega) le_rfl h3'
  have h4F := Work.WilG0.Omega_mono_FD (F := (aDg + aLim + 3))
    (F' := (aG + 1) + (aV + 1) + (aDg + aLim + 3) + 1) (by omega) le_rfl h4
  have hi1 := Work.WilG0.Omega_inter2 h1F h2F
  have h3F' := Work.WilG0.Omega_mono_FD
    (F' := (aG + 1) + (aV + 1) + (aDg + aLim + 3) + 1 + 1) (by omega) le_rfl h3F
  have hi2 := Work.WilG0.Omega_inter2 hi1 h3F'
  have h4F' := Work.WilG0.Omega_mono_FD
    (F' := (aG + 1) + (aV + 1) + (aDg + aLim + 3) + 1 + 1 + 1) (by omega) le_rfl h4F
  have hi3 := Work.WilG0.Omega_inter2 hi2 h4F'
  -- identify the intersection with `fibMainSet`
  have hkey : fibMainSet f j =
      ((({w : Fin (p + 2) → ℝ | Fin.init w ∈ fibGerm f j} ∩
          {w : Fin (p + 2) → ℝ | Fin.init w ∈ fibValC f}) ∩ fibLimSet f j) ∩
        (⋂ m : Fin j,
          {w : Fin (p + 2) → ℝ | Fin.init w ∈ projLast (fibLimSet f ((m : ℕ) + 1))})) := by
    ext w
    simp only [fibMainSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_Icc]
    constructor
    · rintro ⟨g1, g2, g3, g4⟩
      exact ⟨⟨⟨g1, g2⟩, g3⟩, fun m => g4 _ (by omega)⟩
    · rintro ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩
      refine ⟨g1, g2, g3, fun m hm => ?_⟩
      have h := g4 ⟨m - 1, by omega⟩
      simpa [Nat.sub_add_cancel hm.1] using h
  rw [hkey]
  refine Work.WilG0.Omega_mono_FD (by omega) ?_ hi3
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X]
  simp

end Work.WilG4a.CD
