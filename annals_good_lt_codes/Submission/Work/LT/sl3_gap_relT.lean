import Mathlib
import Submission.Work.LT.Defs
import Submission.Work.LT.relT_defs
import Submission.Work.LT.relT_l2
import Submission.Work.LT.relT_chi
import Submission.Work.LT.relT_fourier
import Submission.Work.LT.relT_smooth
import Submission.Work.LT.relT_sl3E_basic
import Submission.Work.LT.relT_sl3E_conj
import Submission.Work.LT.mgg_bowtie
import Submission.Work.LT.relT_fhat_conj
import Submission.Work.LT.relT_avg_id
import Submission.Work.LT.stdAddChar_sin

namespace Work.LT

open Finset

variable {p : ℕ}

/-- Every off-diagonal position occurs in the list `offDiag` of the six elementary positions. -/
lemma offDiag_exists (i j : Fin 3) (h : i ≠ j) : ∃ k : Fin 6, offDiag k = (i, j) := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | decide

/-- The generator `E_ij(1)` (for `i ≠ j`) is one of the twelve generators `sl3Gen p ·`. -/
lemma exists_sl3Gen_eq_one (i j : Fin 3) (h : i ≠ j) :
    ∃ k : Fin 6 × Bool, sl3Gen p k = sl3E p i j 1 := by
  obtain ⟨k, hk⟩ := offDiag_exists i j h
  refine ⟨(k, true), ?_⟩
  simp [sl3Gen, hk]

/-- `E_ij(0) = 1`, unconditionally. -/
lemma sl3E_zero (i j : Fin 3) : sl3E p i j 0 = 1 := (relT_sl3E_basic).1 p i j

/-- `colU p a b c (1,0) = E_ac(1)`. -/
lemma colU_one_zero (a b c : Fin 3) : colU p a b c (1, 0) = sl3E p a c 1 := by
  simp [colU, sl3E_zero]

/-- `colU p a b c (0,1) = E_bc(1)`. -/
lemma colU_zero_one (a b c : Fin 3) : colU p a b c (0, 1) = sl3E p b c 1 := by
  simp [colU, sl3E_zero]

/-- The column subgroup is closed under multiplication. -/
lemma colU_mul (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (st st' : ZMod p × ZMod p) :
    colU p a b c st * colU p a b c st' = colU p a b c (st + st') := by
  obtain ⟨-, -, -, -, hprod⟩ := relT_sl3E_basic
  exact hprod p hab hac hbc st.1 st'.1 st.2 st'.2

/-- The column subgroup is abelian. -/
lemma colU_mul_comm (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (st st' : ZMod p × ZMod p) :
    colU p a b c st * colU p a b c st' = colU p a b c st' * colU p a b c st := by
  rw [colU_mul a b c hab hac hbc st st', colU_mul a b c hab hac hbc st' st]
  congr 1
  exact Prod.ext (add_comm _ _) (add_comm _ _)

/-- Left translation by `U` commutes with the Fourier coefficient: translating the function or
translating the argument give the same value. -/
lemma fhat_translate [NeZero p] (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ) (z st : ZMod p × ZMod p)
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) :
    fhat p a b c z (fun x => f (colU p a b c st * x)) g
      = fhat p a b c z f (colU p a b c st * g) := by
  simp only [fhat]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [← mul_assoc, colU_mul_comm a b c hab hac hbc st x, mul_assoc]

/-- `chi p z (1,0) = ω ^ (z.1)`. -/
lemma chi_one_zero [NeZero p] (z : ZMod p × ZMod p) : chi p z (1, 0) = ZMod.stdAddChar z.1 := by
  simp [chi]

/-- `chi p z (0,1) = ω ^ (z.2)`. -/
lemma chi_zero_one [NeZero p] (z : ZMod p × ZMod p) : chi p z (0, 1) = ZMod.stdAddChar z.2 := by
  simp [chi]

/-- `fhat` is additive in its function argument. -/
lemma fhat_add [NeZero p] (a b c : Fin 3) (z : ZMod p × ZMod p)
    (h₁ h₂ : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ) :
    fhat p a b c z (h₁ + h₂) = fhat p a b c z h₁ + fhat p a b c z h₂ := by
  funext g
  simp only [fhat, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_div]

/-- `fhat` is `ℂ`-homogeneous in its function argument. -/
lemma fhat_smul [NeZero p] (a b c : Fin 3) (z : ZMod p × ZMod p) (r : ℂ)
    (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ) :
    fhat p a b c z (r • h) = r • fhat p a b c z h := by
  funext g
  have h1 : (∑ x, star (chi p z x) * (r * h (colU p a b c x * g)))
      = r * (∑ st, star (chi p z st) * h (colU p a b c st * g)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  simp only [fhat, Pi.smul_apply, smul_eq_mul]
  rw [h1, mul_div_assoc]

/-- `fhat` is additive in its function argument (differences). -/
lemma fhat_sub [NeZero p] (a b c : Fin 3) (z : ZMod p × ZMod p)
    (h₁ h₂ : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ) :
    fhat p a b c z (h₁ - h₂) = fhat p a b c z h₁ - fhat p a b c z h₂ := by
  funext g
  simp only [fhat, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_div]

end Work.LT

namespace Work.LT

open Finset

variable {p : ℕ}

/-- **Concentration from the `U`-generator Dirichlet form.**
Difference the eigenrelation for the element `u = colU p a b c st = y` against the definition of
`fhat`, expand by Plancherel, and use `‖χ_z(u) − 1‖² = 4 sin²(π c z / p) ≥ 2` on the "far" set
`{z | p ≤ 4 (c z)}`. -/
lemma fourier_concentration [NeZero p] {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
    (hinv : ∀ (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
      (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
      ∑ z : ZMod p × ZMod p, fhat p a b c z h g = h g)
    (hplanch : ∀ (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ) (B : Finset (ZMod p × ZMod p)),
      l2sq (fun g => ∑ z ∈ B, fhat p a b c z h g) = ∑ z ∈ B, l2sq (fhat p a b c z h))
    (heigen : ∀ (st z : ZMod p × ZMod p) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
      fhat p a b c z f (colU p a b c st * g) = chi p z st * fhat p a b c z f g)
    (st : ZMod p × ZMod p) (cn : ZMod p × ZMod p → ℕ) (y : Matrix.SpecialLinearGroup (Fin 3) (ZMod p))
    (hy : colU p a b c st = y)
    (hc : ∀ z, p ≤ 4 * cn z → 2 ≤ Complex.normSq (chi p z st - 1))
    (D : ℝ) (hD : l2sq (fun g => f (y * g) - f g) ≤ D) :
    ∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p => p ≤ 4 * cn z),
        l2sq (fhat p a b c z f) ≤ D / 2 := by
  set h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ := fun g => f (y * g) - f g with hh
  -- the `z`-th Fourier component of `h` is `(χ_z(u) - 1) • f_z`
  have hlin : ∀ z : ZMod p × ZMod p,
      fhat p a b c z h = (chi p z st - 1) • fhat p a b c z f := by
    intro z
    have hy' : (fun g => f (y * g)) = (fun g => f (colU p a b c st * g)) := by rw [hy]
    have hsub : fhat p a b c z h
        = fhat p a b c z (fun g => f (y * g)) - fhat p a b c z f := by
      rw [← fhat_sub]; rfl
    have heig : fhat p a b c z (fun g => f (colU p a b c st * g))
        = chi p z st • fhat p a b c z f := by
      funext g
      rw [fhat_translate a b c hab hac hbc f z st g, Pi.smul_apply, smul_eq_mul]
      exact heigen st z g
    rw [hsub, hy', heig]
    funext g
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- hence the component norms
  have hnorm : ∀ z : ZMod p × ZMod p,
      l2sq (fhat p a b c z h) = Complex.normSq (chi p z st - 1) * l2sq (fhat p a b c z f) := by
    intro z
    rw [hlin z, l2sq_smul]
  -- Plancherel for `h`
  have hpl : l2sq h
      = ∑ z : ZMod p × ZMod p, Complex.normSq (chi p z st - 1) * l2sq (fhat p a b c z f) := by
    have hh_eq : h = fun g => ∑ z ∈ (Finset.univ : Finset (ZMod p × ZMod p)), fhat p a b c z h g := by
      funext g
      rw [show (∑ z ∈ (Finset.univ : Finset (ZMod p × ZMod p)), fhat p a b c z h g)
            = ∑ z, fhat p a b c z h g from rfl]
      exact (hinv h g).symm
    rw [hh_eq, hplanch h Finset.univ]
    exact Finset.sum_congr rfl fun z _ => hnorm z
  -- on the far set the character is far from `1`
  have hpt : ∀ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p => p ≤ 4 * cn z),
      2 * l2sq (fhat p a b c z f)
        ≤ Complex.normSq (chi p z st - 1) * l2sq (fhat p a b c z f) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    exact mul_le_mul_of_nonneg_right (hc z hz.2) (l2sq_nonneg _)
  have h1 : ∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p => p ≤ 4 * cn z),
        2 * l2sq (fhat p a b c z f)
      ≤ ∑ z : ZMod p × ZMod p, Complex.normSq (chi p z st - 1) * l2sq (fhat p a b c z f) := by
    refine le_trans (Finset.sum_le_sum hpt) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro z _ _
    exact mul_nonneg (Complex.normSq_nonneg _) (l2sq_nonneg _)
  have h2 : (∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p => p ≤ 4 * cn z),
        2 * l2sq (fhat p a b c z f))
      = 2 * ∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p => p ≤ 4 * cn z),
        l2sq (fhat p a b c z f) := by
    rw [Finset.mul_sum]
  rw [h2] at h1
  rw [← hpl] at h1
  linarith

end Work.LT

namespace Work.LT

open Finset

variable {p : ℕ}

/-- **Main assembly.** Given the Fourier facts, the sin-bounds, the six generator Dirichlet
bounds and the bow-tie estimate (with constant `C`), the column Dirichlet form of `f` is bounded
by `2 * C * p² * D`. -/
lemma sl3_relT_master [Fact p.Prime] {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (C : ℝ)
    (hC : ∀ (m : ZMod p × ZMod p → ℝ), (∀ z, 0 ≤ m z) → ∀ ε : ℝ, 0 ≤ ε →
      (∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p =>
          p ≤ 4 * (ZMod.valMinAbs z.1).natAbs), m z) ≤ ε ^ 2 / 2 →
      (∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p =>
          p ≤ 4 * (ZMod.valMinAbs z.2).natAbs), m z) ≤ ε ^ 2 / 2 →
      (∀ B : Finset (ZMod p × ZMod p),
        |(∑ z ∈ B.image (fun z => (z.1 + z.2, z.2)), m z) - ∑ z ∈ B, m z| ≤
          2 * ε * Real.sqrt (∑ z ∈ B, m z) + ε ^ 2) →
      (∀ B : Finset (ZMod p × ZMod p),
        |(∑ z ∈ B.image (fun z => (z.1 - z.2, z.2)), m z) - ∑ z ∈ B, m z| ≤
          2 * ε * Real.sqrt (∑ z ∈ B, m z) + ε ^ 2) →
      (∀ B : Finset (ZMod p × ZMod p),
        |(∑ z ∈ B.image (fun z => (z.1, z.2 + z.1)), m z) - ∑ z ∈ B, m z| ≤
          2 * ε * Real.sqrt (∑ z ∈ B, m z) + ε ^ 2) →
      (∀ B : Finset (ZMod p × ZMod p),
        |(∑ z ∈ B.image (fun z => (z.1, z.2 - z.1)), m z) - ∑ z ∈ B, m z| ≤
          2 * ε * Real.sqrt (∑ z ∈ B, m z) + ε ^ 2) →
      ∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p => z ≠ 0), m z ≤ C * ε ^ 2)
    (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hfourier : ∀ (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ),
      (∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p),
          ∑ z : ZMod p × ZMod p, fhat p a b c z h g = h g) ∧
      (∀ B : Finset (ZMod p × ZMod p),
          l2sq (fun g => ∑ z ∈ B, fhat p a b c z h g) = ∑ z ∈ B, l2sq (fhat p a b c z h)))
    (heigen : ∀ (st z : ZMod p × ZMod p) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
      fhat p a b c z f (colU p a b c st * g) = chi p z st * fhat p a b c z f g)
    (hsm : ∀ B : Finset (ZMod p × ZMod p),
      |(∑ z ∈ B.image (fun z => (z.1 + z.2, z.2)), l2sq (fhat p a b c z f))
          - ∑ z ∈ B, l2sq (fhat p a b c z f)|
        ≤ 2 * l2norm (fun g => f (sl3E p b a (-1) * g) - f g)
            * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f))
          + l2sq (fun g => f (sl3E p b a (-1) * g) - f g)
      ∧ |(∑ z ∈ B.image (fun z => (z.1 - z.2, z.2)), l2sq (fhat p a b c z f))
          - ∑ z ∈ B, l2sq (fhat p a b c z f)|
        ≤ 2 * l2norm (fun g => f (sl3E p b a 1 * g) - f g)
            * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f))
          + l2sq (fun g => f (sl3E p b a 1 * g) - f g)
      ∧ |(∑ z ∈ B.image (fun z => (z.1, z.2 + z.1)), l2sq (fhat p a b c z f))
          - ∑ z ∈ B, l2sq (fhat p a b c z f)|
        ≤ 2 * l2norm (fun g => f (sl3E p a b (-1) * g) - f g)
            * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f))
          + l2sq (fun g => f (sl3E p a b (-1) * g) - f g)
      ∧ |(∑ z ∈ B.image (fun z => (z.1, z.2 - z.1)), l2sq (fhat p a b c z f))
          - ∑ z ∈ B, l2sq (fhat p a b c z f)|
        ≤ 2 * l2norm (fun g => f (sl3E p a b 1 * g) - f g)
            * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f))
          + l2sq (fun g => f (sl3E p a b 1 * g) - f g))
    (havg : ∑ st : ZMod p × ZMod p, l2sq (fun g => f (colU p a b c st * g) - f g)
      = 2 * (p : ℝ) ^ 2 * ∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p => z ≠ 0),
          l2sq (fhat p a b c z f))
    (hsin1 : ∀ z : ZMod p × ZMod p,
      p ≤ 4 * (ZMod.valMinAbs z.1).natAbs → 2 ≤ Complex.normSq (chi p z (1, 0) - 1))
    (hsin2 : ∀ z : ZMod p × ZMod p,
      p ≤ 4 * (ZMod.valMinAbs z.2).natAbs → 2 ≤ Complex.normSq (chi p z (0, 1) - 1))
    (hDac : l2sq (fun g => f (sl3E p a c 1 * g) - f g) ≤ D)
    (hDbc : l2sq (fun g => f (sl3E p b c 1 * g) - f g) ≤ D)
    (hDab1 : l2sq (fun g => f (sl3E p a b 1 * g) - f g) ≤ D)
    (hDabm : l2sq (fun g => f (sl3E p a b (-1) * g) - f g) ≤ D)
    (hDba1 : l2sq (fun g => f (sl3E p b a 1 * g) - f g) ≤ D)
    (hDbam : l2sq (fun g => f (sl3E p b a (-1) * g) - f g) ≤ D) :
    (∑ st : ZMod p × ZMod p, l2sq (fun g => f (colU p a b c st * g) - f g))
      ≤ (2 * C) * (p : ℝ) ^ 2 * D := by
  have hsqrtD : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD
  have hDnn : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
  have hm0 : ∀ z : ZMod p × ZMod p, 0 ≤ l2sq (fhat p a b c z f) := fun z => l2sq_nonneg _
  have hinv : ∀ (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
      (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
      ∑ z : ZMod p × ZMod p, fhat p a b c z h g = h g := fun h g => (hfourier h).1 g
  have hplanch : ∀ (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
      (B : Finset (ZMod p × ZMod p)),
      l2sq (fun g => ∑ z ∈ B, fhat p a b c z h g) = ∑ z ∈ B, l2sq (fhat p a b c z h) :=
    fun h B => (hfourier h).2 B
  -- concentration
  have hconc1 := fourier_concentration hab hac hbc f hinv hplanch heigen (1, 0)
    (fun z => (ZMod.valMinAbs z.1).natAbs) (sl3E p a c 1) (colU_one_zero a b c) hsin1 D hDac
  have hconc2 := fourier_concentration hab hac hbc f hinv hplanch heigen (0, 1)
    (fun z => (ZMod.valMinAbs z.2).natAbs) (sl3E p b c 1) (colU_zero_one a b c) hsin2 D hDbc
  have hconc1' : (∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p =>
        p ≤ 4 * (ZMod.valMinAbs z.1).natAbs), l2sq (fhat p a b c z f))
      ≤ Real.sqrt D ^ 2 / 2 := by rw [hsqrtD]; exact hconc1
  have hconc2' : (∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p =>
        p ≤ 4 * (ZMod.valMinAbs z.2).natAbs), l2sq (fhat p a b c z f))
      ≤ Real.sqrt D ^ 2 / 2 := by rw [hsqrtD]; exact hconc2
  -- convert the smoothness estimates to the bow-tie form with `ε = √D`
  have hnorm_le : ∀ y : Matrix.SpecialLinearGroup (Fin 3) (ZMod p),
      l2sq (fun g => f (y * g) - f g) ≤ D → l2norm (fun g => f (y * g) - f g) ≤ Real.sqrt D :=
    fun y hy => by rw [l2norm]; exact Real.sqrt_le_sqrt hy
  have hbound : ∀ B : Finset (ZMod p × ZMod p),
      |(∑ z ∈ B.image (fun z => (z.1 + z.2, z.2)), l2sq (fhat p a b c z f))
          - ∑ z ∈ B, l2sq (fhat p a b c z f)|
        ≤ 2 * Real.sqrt D * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f)) + Real.sqrt D ^ 2 := by
    intro B
    have h := (hsm B).1
    have h1 := hnorm_le (sl3E p b a (-1)) hDbam
    have h2 : l2sq (fun g => f (sl3E p b a (-1) * g) - f g) ≤ Real.sqrt D ^ 2 := by
      rw [hsqrtD]; exact hDbam
    have h3 : (0:ℝ) ≤ Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f)) := Real.sqrt_nonneg _
    nlinarith [h, h1, h2, h3]
  have hbound' : ∀ B : Finset (ZMod p × ZMod p),
      |(∑ z ∈ B.image (fun z => (z.1 - z.2, z.2)), l2sq (fhat p a b c z f))
          - ∑ z ∈ B, l2sq (fhat p a b c z f)|
        ≤ 2 * Real.sqrt D * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f)) + Real.sqrt D ^ 2 := by
    intro B
    have h := (hsm B).2.1
    have h1 := hnorm_le (sl3E p b a 1) hDba1
    have h2 : l2sq (fun g => f (sl3E p b a 1 * g) - f g) ≤ Real.sqrt D ^ 2 := by
      rw [hsqrtD]; exact hDba1
    have h3 : (0:ℝ) ≤ Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f)) := Real.sqrt_nonneg _
    nlinarith [h, h1, h2, h3]
  have hbound'' : ∀ B : Finset (ZMod p × ZMod p),
      |(∑ z ∈ B.image (fun z => (z.1, z.2 + z.1)), l2sq (fhat p a b c z f))
          - ∑ z ∈ B, l2sq (fhat p a b c z f)|
        ≤ 2 * Real.sqrt D * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f)) + Real.sqrt D ^ 2 := by
    intro B
    have h := (hsm B).2.2.1
    have h1 := hnorm_le (sl3E p a b (-1)) hDabm
    have h2 : l2sq (fun g => f (sl3E p a b (-1) * g) - f g) ≤ Real.sqrt D ^ 2 := by
      rw [hsqrtD]; exact hDabm
    have h3 : (0:ℝ) ≤ Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f)) := Real.sqrt_nonneg _
    nlinarith [h, h1, h2, h3]
  have hbound''' : ∀ B : Finset (ZMod p × ZMod p),
      |(∑ z ∈ B.image (fun z => (z.1, z.2 - z.1)), l2sq (fhat p a b c z f))
          - ∑ z ∈ B, l2sq (fhat p a b c z f)|
        ≤ 2 * Real.sqrt D * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f)) + Real.sqrt D ^ 2 := by
    intro B
    have h := (hsm B).2.2.2
    have h1 := hnorm_le (sl3E p a b 1) hDab1
    have h2 : l2sq (fun g => f (sl3E p a b 1 * g) - f g) ≤ Real.sqrt D ^ 2 := by
      rw [hsqrtD]; exact hDab1
    have h3 : (0:ℝ) ≤ Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f)) := Real.sqrt_nonneg _
    nlinarith [h, h1, h2, h3]
  have hbow := hC (fun z => l2sq (fhat p a b c z f)) hm0 (Real.sqrt D) hDnn
    hconc1' hconc2' hbound hbound' hbound'' hbound'''
  rw [hsqrtD] at hbow
  rw [havg]
  calc 2 * (p : ℝ) ^ 2 * (∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p => z ≠ 0),
          l2sq (fhat p a b c z f))
      ≤ 2 * (p : ℝ) ^ 2 * (C * D) := mul_le_mul_of_nonneg_left hbow (by positivity)
    _ = (2 * C) * (p : ℝ) ^ 2 * D := by ring

end Work.LT

namespace Work.LT

open Finset

variable {p : ℕ}

/-- The generator `E_ij(-1)` (for `i ≠ j`) is one of the twelve generators `sl3Gen p ·`. -/
lemma exists_sl3Gen_eq_neg_one (i j : Fin 3) (h : i ≠ j) :
    ∃ k : Fin 6 × Bool, sl3Gen p k = sl3E p i j (-1) := by
  obtain ⟨k, hk⟩ := offDiag_exists i j h
  exact ⟨(k, false), by simp [sl3Gen, hk]⟩

/-- `colU` is the product of the two transvections. -/
lemma colU_eq_prod (a b c : Fin 3) (st : ZMod p × ZMod p) :
    colU p a b c st = sl3E p a c st.1 * sl3E p b c st.2 := rfl

end Work.LT

namespace Work.LT

open Finset

variable {p : ℕ}

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- **Relative property (T) for a column subgroup, finite form.**

`G = SL₃(ℤ/p)`, `U = {E_ac(s)·E_bc(t)} ≅ (ℤ/p)²` the column-`c` unipotent subgroup (`a,b,c`
pairwise distinct). The column Dirichlet form of a real `f : G → ℝ` is bounded by the
12-generator Dirichlet form `D(f) = ∑_k ∑_g (f (S_k g) − f g)²`, with a constant uniform in the
odd prime `p`.

The proof complexifies `f`, decomposes along the characters of `U`
(`relT_fourier`: inversion, orthogonality/Plancherel, eigenrelation), which turns the
`U`-Dirichlet form into `2 p² ∑_{z ≠ 0} l2sq (fhat_z f)` (`relT_avg_id`). Concentration of the
Fourier mass near the two coordinate axes comes from the `U`-generators (`fourier_concentration`,
using `stdAddChar_sin`), and the Lipschitz ("smoothness") estimate under the four dual
transvections comes from the `SL₂` part (`relT_smooth`, using `relT_fhat_conj`). The
Margulis–Gabber–Galil bow-tie lemma (`mgg_bowtie`) then bounds the total off-origin Fourier mass
by `O(D)`. The complexification does not change any of the `ℓ²`-quantities (`hnorm`). -/
theorem sl3_gap_relT :
    ∃ K : ℝ, 0 < K ∧ ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
      ∀ f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℝ,
        ∑ s : ZMod p, ∑ t : ZMod p, ∑ g, (f (sl3E p a c s * sl3E p b c t * g) - f g) ^ 2 ≤
          K * (p : ℝ) ^ 2 * ∑ k, ∑ g, (f (sl3Gen p k * g) - f g) ^ 2 := by
  obtain ⟨C, hCpos, hCbound⟩ := mgg_bowtie
  refine ⟨2 * C, by positivity, ?_⟩
  intro p hpF hp2 a b c hab hac hbc f
  haveI : Fact p.Prime := hpF
  set D : ℝ := ∑ k : Fin 6 × Bool,
    l2sq (fun g => ((f (sl3Gen p k * g) : ℂ)) - ((f g : ℂ))) with hDdef
  have hD : 0 ≤ D := by
    rw [hDdef]
    exact Finset.sum_nonneg fun k _ => l2sq_nonneg _
  -- complexification preserves the `ℓ²`-data
  have hnorm : ∀ u : Matrix.SpecialLinearGroup (Fin 3) (ZMod p),
      l2sq (fun g => ((f (u * g) : ℂ)) - ((f g : ℂ))) = ∑ g, (f (u * g) - f g) ^ 2 := by
    intro u
    have hpt : ∀ g, Complex.normSq (((f (u * g) : ℂ)) - ((f g : ℂ))) = (f (u * g) - f g) ^ 2 := by
      intro g
      rw [← Complex.ofReal_sub, Complex.normSq_ofReal]
      ring
    simp only [l2sq]
    exact Finset.sum_congr rfl fun g _ => hpt g
  -- each single generator contributes at most the full Dirichlet form
  have hgen : ∀ (i j : Fin 3) (hij : i ≠ j) (s : ZMod p), s = 1 ∨ s = -1 →
      l2sq (fun g => ((f (sl3E p i j s * g) : ℂ)) - ((f g : ℂ))) ≤ D := by
    intro i j hij s hs
    have hsingle : ∀ k : Fin 6 × Bool,
        l2sq (fun g => ((f (sl3Gen p k * g) : ℂ)) - ((f g : ℂ)))
          ≤ ∑ k' : Fin 6 × Bool, l2sq (fun g => ((f (sl3Gen p k' * g) : ℂ)) - ((f g : ℂ))) := by
      intro k
      exact Finset.single_le_sum
        (f := fun k' => l2sq (fun g => ((f (sl3Gen p k' * g) : ℂ)) - ((f g : ℂ))))
        (fun k' _ => l2sq_nonneg _) (Finset.mem_univ k)
    rcases hs with rfl | rfl
    · obtain ⟨k, hk⟩ := exists_sl3Gen_eq_one i j hij
      rw [hDdef, ← hk]
      exact hsingle k
    · obtain ⟨k, hk⟩ := exists_sl3Gen_eq_neg_one i j hij
      rw [hDdef, ← hk]
      exact hsingle k
  have hfour : ∀ (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ),
      (∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p),
          ∑ z : ZMod p × ZMod p, fhat p a b c z h g = h g) ∧
      (∀ B : Finset (ZMod p × ZMod p),
          l2sq (fun g => ∑ z ∈ B, fhat p a b c z h g) = ∑ z ∈ B, l2sq (fhat p a b c z h)) := by
    intro h
    exact ⟨(_root_.Work.LT.relT_fourier p hab hac hbc h).1,
      fun B => (_root_.Work.LT.relT_fourier p hab hac hbc h).2.1 h B⟩
  have heigen : ∀ (st z : ZMod p × ZMod p) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
      fhat p a b c z (fun x => ((f x : ℂ))) (colU p a b c st * g)
        = chi p z st * fhat p a b c z (fun x => ((f x : ℂ))) g := by
    intro st z g
    exact (_root_.Work.LT.relT_fourier p hab hac hbc (fun x => ((f x : ℂ)))).2.2 st z g
  have hsm : ∀ B : Finset (ZMod p × ZMod p),
      |(∑ z ∈ B.image (fun z => (z.1 + z.2, z.2)), l2sq (fhat p a b c z (fun x => ((f x : ℂ)))))
          - ∑ z ∈ B, l2sq (fhat p a b c z (fun x => ((f x : ℂ))))|
        ≤ 2 * l2norm (fun g => ((f (sl3E p b a (-1) * g) : ℂ)) - ((f g : ℂ)))
            * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z (fun x => ((f x : ℂ)))))
          + l2sq (fun g => ((f (sl3E p b a (-1) * g) : ℂ)) - ((f g : ℂ)))
      ∧ |(∑ z ∈ B.image (fun z => (z.1 - z.2, z.2)), l2sq (fhat p a b c z (fun x => ((f x : ℂ)))))
          - ∑ z ∈ B, l2sq (fhat p a b c z (fun x => ((f x : ℂ))))|
        ≤ 2 * l2norm (fun g => ((f (sl3E p b a 1 * g) : ℂ)) - ((f g : ℂ)))
            * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z (fun x => ((f x : ℂ)))))
          + l2sq (fun g => ((f (sl3E p b a 1 * g) : ℂ)) - ((f g : ℂ)))
      ∧ |(∑ z ∈ B.image (fun z => (z.1, z.2 + z.1)), l2sq (fhat p a b c z (fun x => ((f x : ℂ)))))
          - ∑ z ∈ B, l2sq (fhat p a b c z (fun x => ((f x : ℂ))))|
        ≤ 2 * l2norm (fun g => ((f (sl3E p a b (-1) * g) : ℂ)) - ((f g : ℂ)))
            * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z (fun x => ((f x : ℂ)))))
          + l2sq (fun g => ((f (sl3E p a b (-1) * g) : ℂ)) - ((f g : ℂ)))
      ∧ |(∑ z ∈ B.image (fun z => (z.1, z.2 - z.1)), l2sq (fhat p a b c z (fun x => ((f x : ℂ)))))
          - ∑ z ∈ B, l2sq (fhat p a b c z (fun x => ((f x : ℂ))))|
        ≤ 2 * l2norm (fun g => ((f (sl3E p a b 1 * g) : ℂ)) - ((f g : ℂ)))
            * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z (fun x => ((f x : ℂ)))))
          + l2sq (fun g => ((f (sl3E p a b 1 * g) : ℂ)) - ((f g : ℂ))) := by
    intro B
    exact _root_.Work.LT.relT_smooth p hab hac hbc (fun x => ((f x : ℂ)))
      (fun h g => (hfour h).1 g) (fun h B => (hfour h).2 B)
      (fun k z g => (relT_fhat_conj p hab hac hbc k (fun x => ((f x : ℂ))) z).1 g)
      (fun k z g => (relT_fhat_conj p hab hac hbc k (fun x => ((f x : ℂ))) z).2 g) B
  have havg : ∑ st : ZMod p × ZMod p,
        l2sq (fun g => ((f (colU p a b c st * g) : ℂ)) - ((f g : ℂ)))
      = 2 * (p : ℝ) ^ 2 * ∑ z ∈ Finset.univ.filter (fun z : ZMod p × ZMod p => z ≠ 0),
          l2sq (fhat p a b c z (fun x => ((f x : ℂ)))) := by
    have hpl : ∀ (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ),
        l2sq h = ∑ z : ZMod p × ZMod p, l2sq (fhat p a b c z h) := by
      intro h
      have hfun : (fun g => ∑ z ∈ (Finset.univ : Finset (ZMod p × ZMod p)),
          fhat p a b c z h g) = h := by
        funext g
        rw [show (∑ z ∈ (Finset.univ : Finset (ZMod p × ZMod p)), fhat p a b c z h g)
              = ∑ z, fhat p a b c z h g from rfl]
        exact (hfour h).1 g
      calc l2sq h = l2sq (fun g => ∑ z ∈ (Finset.univ : Finset (ZMod p × ZMod p)),
              fhat p a b c z h g) := congrArg l2sq hfun.symm
        _ = ∑ z ∈ (Finset.univ : Finset (ZMod p × ZMod p)), l2sq (fhat p a b c z h) :=
              (hfour h).2 Finset.univ
        _ = ∑ z : ZMod p × ZMod p, l2sq (fhat p a b c z h) := rfl
    exact relT_avg_id p hab hac hbc (fun x => ((f x : ℂ))) hpl
      (fun st z g => (_root_.Work.LT.relT_fourier p hab hac hbc (fun x => ((f x : ℂ)))).2.2 st z g)
  have hsin1 : ∀ z : ZMod p × ZMod p,
      p ≤ 4 * (ZMod.valMinAbs z.1).natAbs
        → 2 ≤ Complex.normSq (chi p z (1, 0) - 1) := by
    intro z hz
    rw [chi_one_zero, (stdAddChar_sin p z.1).1]
    exact (stdAddChar_sin p z.1).2 hz
  have hsin2 : ∀ z : ZMod p × ZMod p,
      p ≤ 4 * (ZMod.valMinAbs z.2).natAbs
        → 2 ≤ Complex.normSq (chi p z (0, 1) - 1) := by
    intro z hz
    rw [chi_zero_one, (stdAddChar_sin p z.2).1]
    exact (stdAddChar_sin p z.2).2 hz
  have hmaster := sl3_relT_master (a := a) (b := b) (c := c) hab hac hbc C
    (hCbound p hp2) (fun g => ((f g : ℂ))) D hD
    hfour heigen hsm havg hsin1 hsin2
    (hgen a c hac 1 (Or.inl rfl)) (hgen b c hbc 1 (Or.inl rfl))
    (hgen a b hab 1 (Or.inl rfl)) (hgen a b hab (-1) (Or.inr rfl))
    (hgen b a (Ne.symm hab) 1 (Or.inl rfl)) (hgen b a (Ne.symm hab) (-1) (Or.inr rfl))
  have hgoal : (∑ s : ZMod p, ∑ t : ZMod p, ∑ g, (f (sl3E p a c s * sl3E p b c t * g) - f g) ^ 2)
      = ∑ st : ZMod p × ZMod p,
          l2sq (fun g => ((f (colU p a b c st * g) : ℂ)) - ((f g : ℂ))) := by
    rw [Fintype.sum_prod_type (f := fun st : ZMod p × ZMod p =>
      l2sq (fun g => ((f (colU p a b c st * g) : ℂ)) - ((f g : ℂ))))]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    rw [hnorm (colU p a b c (s, t))]
    rfl
  have hDgoal : (∑ k : Fin 6 × Bool, ∑ g, (f (sl3Gen p k * g) - f g) ^ 2) = D := by
    rw [hDdef]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hnorm (sl3Gen p k)]
  rw [hgoal, hDgoal]
  exact hmaster

end Work.LT
