import Submission.Work.EKLC6Core.Basic

/-!
# `EKLC6Core.Covariant` — the multiplicative structure of the leaf-wise measures

Pisa 7.16 + 7.18 in the normalisation of the frozen contract (`ν x (Box1 U) = 1`):
for a leaf-wise system carried by `U`, the covariance under the diagonal flow `a = aDiag t`
telescopes.  In multiplicative (division-free) form, one step is

`ν (a^{-1}.y) C * ν y (conjBox U t) = ν y (conjBy t C)`,

and iterating it along the `a`-orbit gives

`ν x (conjBox U (-n t)) * ∏_{j<n} ν (a^{j+1}.x) (conjBox U t) = 1`.

Taking logarithms turns this into the statement that the limit defining the entropy
contribution `D_μ(a,U)(x) = lim_n log μ_x^U(a^{-n} B₁ a^n)/n` of Pisa 7.6 is a Birkhoff
average of `growthFun U ν t` along the `a`-orbit.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Conjugation, measurability and preimages -/

theorem measurable_conj (t : Fin 3 → ℝ) :
    Measurable (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) :=
  ((continuous_const.mul continuous_id).mul continuous_const).measurable

/-- `(aDiag t)⁻¹ = aDiag (-t)`. -/
theorem aDiag_inv_eq_neg (t : Fin 3 → ℝ) : (aDiag t)⁻¹ = aDiag (-t) :=
  inv_eq_of_mul_eq_one_left (aDiag_neg_mul t)

/-- `aDiag (-t)` is the inverse of `aDiag t`. -/
theorem aDiag_neg_eq_inv (t : Fin 3 → ℝ) : aDiag (-t) = (aDiag t)⁻¹ :=
  (aDiag_inv_eq_neg t).symm

/-- The preimage of `D` under conjugation by `aDiag (-t)` is the image of `D` under
conjugation by `aDiag t`. -/
theorem preimage_conj_neg (t : Fin 3 → ℝ) (D : Set SL3) :
    (fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹) ⁻¹' D = conjBy t D := by
  have h1 : aDiag (-t) = (aDiag t)⁻¹ := aDiag_neg_eq_inv t
  ext g
  simp only [Set.mem_preimage, conjBy, Set.mem_image]
  constructor
  · intro hg
    refine ⟨aDiag (-t) * g * (aDiag (-t))⁻¹, hg, ?_⟩
    rw [h1]
    group
  · rintro ⟨h, hh, rfl⟩
    have hval : aDiag (-t) * (aDiag t * h * (aDiag t)⁻¹) * (aDiag (-t))⁻¹ = h := by
      rw [h1]
      group
    rw [hval]
    exact hh

/-- `conjBy` is compatible with the boxes. -/
theorem conjBy_conjBox (U : Subgroup SL3) (s t : Fin 3 → ℝ) :
    conjBy t (conjBox U s) = conjBox U (t + s) := by
  show conjBy t (conjBy s (Box1 U)) = conjBy (t + s) (Box1 U)
  rw [← conjBy_add]

/-! ## Arithmetic of the exponent vectors -/

theorem succ_smul (j : ℕ) (t : Fin 3 → ℝ) : (((j : ℝ) + 1) • t) = (j : ℝ) • t + t := by
  rw [add_smul, one_smul]

theorem succ_succ_smul (j : ℕ) (t : Fin 3 → ℝ) :
    (((j : ℝ) + 1) • t) + t = ((((j : ℝ) + 1) + 1) • t) := by
  ext i
  simp only [Pi.add_apply, Pi.smul_apply]
  ring

/-- `t + (-(n+1)t) = -nt`. -/
theorem add_neg_succ_smul (n : ℕ) (t : Fin 3 → ℝ) :
    t + (-(((n : ℝ) + 1) • t)) = -((n : ℝ) • t) := by
  ext i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply]
  ring

/-! ## The one-step covariance -/

/-- **One step of Pisa 7.16/7.18** in division-free (normalised) form. -/
theorem covariant_step {μ : Measure X3} {U : Subgroup SL3} {ν : X3 → Measure SL3}
    {X' X'' : Set X3} (hL : IsLeafwise μ U ν X') (hcov : ACovariant ν X'')
    (hBox1 : MeasurableSet (Box1 U)) (t : Fin 3 → ℝ) {y : X3}
    (hy : y ∈ X' ∩ X'') (hy' : aDiag (-t) • y ∈ X' ∩ X'')
    {C : Set SL3} (hC : MeasurableSet C) :
    ν (aDiag (-t) • y) C * ν y (conjBox U t) = ν y (conjBy t C) := by
  obtain ⟨c, -, -, hceq⟩ := hcov (-t) y hy.2 hy'.2
  have hmap : Measurable (fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹) :=
    measurable_conj _
  have key : ∀ {D : Set SL3}, MeasurableSet D →
      ν (aDiag (-t) • y) D = c * ν y (conjBy t D) := by
    intro D hD
    rw [hceq, Measure.smul_apply, smul_eq_mul, Measure.map_apply hmap hD, preimage_conj_neg]
  have h1 : ν (aDiag (-t) • y) (Box1 U) = c * ν y (conjBox U t) := key hBox1
  have h2 : ν (aDiag (-t) • y) (Box1 U) = 1 := hL.normalised _ hy'.1
  calc ν (aDiag (-t) • y) C * ν y (conjBox U t)
      = (c * ν y (conjBy t C)) * ν y (conjBox U t) := by rw [key hC]
    _ = (c * ν y (conjBox U t)) * ν y (conjBy t C) := by ac_rfl
    _ = ν y (conjBy t C) := by rw [← h1, h2, one_mul]

/-! ## The telescoping identity -/

/-- **Pisa 7.16 + 7.18 (normalised form).**  Along the `a`-orbit of `x` the boxes telescope:
the mass of the big box `conjBox U (-n t)` at `x` is the reciprocal of the product of the masses
of the contracted box `conjBox U t` along the orbit. -/
theorem covariant_mul {μ : Measure X3} {U : Subgroup SL3} {ν : X3 → Measure SL3}
    {X' X'' : Set X3} (hL : IsLeafwise μ U ν X') (hcov : ACovariant ν X'')
    (hBox : ∀ w : Fin 3 → ℝ, MeasurableSet (conjBox U w)) (t : Fin 3 → ℝ) :
    ∀ (n : ℕ) (x : X3),
      (∀ j : ℕ, j ≤ n + 2 → aDiag ((j : ℝ) • t) • x ∈ X' ∩ X'') →
      ν x (conjBox U (-((n : ℝ) • t))) *
        ∏ j ∈ Finset.range n,
          ν (aDiag (((j : ℝ) + 1) • t) • x) (conjBox U t) = 1 := by
  intro n
  induction n with
  | zero =>
    intro x hx
    simp only [Finset.range_zero, Finset.prod_empty, mul_one, Nat.cast_zero, zero_smul,
      neg_zero]
    have hxX' : x ∈ X' := by
      have h := (hx 0 (by omega)).1
      simpa [aDiag_zero, one_smul] using h
    rw [conjBox_zero, hL.normalised x hxX']
  | succ n ih =>
    intro x hx
    set y : X3 := aDiag t • x with hy_def
    have hy : y ∈ X' ∩ X'' := by
      have h := hx 1 (by omega)
      simpa [hy_def] using h
    have hx' : x ∈ X' ∩ X'' := by
      have h := hx 0 (by omega)
      simpa [aDiag_zero, one_smul] using h
    have hyx : ∀ j : ℕ, j ≤ n + 2 → aDiag ((j : ℝ) • t) • y ∈ X' ∩ X'' := by
      intro j hj
      have h := hx (j + 1) (by omega)
      have heq : aDiag ((j : ℝ) • t) • y = aDiag (((j : ℝ) + 1) • t) • x := by
        rw [hy_def, aDiag_smul_mul, succ_smul]
      rw [heq]
      simpa using h
    have hIH := ih y hyx
    have hyx0 : aDiag (-t) • y = x := by
      rw [hy_def, aDiag_smul_mul]
      have hzero : -t + t = (0 : Fin 3 → ℝ) := by funext i; simp
      rw [hzero, aDiag_zero, one_smul]
    have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
    have hstep := covariant_step hL hcov (by simpa using hBox 0) t hy (by rw [hyx0]; exact hx')
      (C := conjBox U (-(((n : ℝ) + 1) • t))) (hBox _)
    rw [hyx0] at hstep
    have hstep' : ν x (conjBox U (-(((n : ℝ) + 1) • t))) * ν y (conjBox U t) =
        ν y (conjBox U (-((n : ℝ) • t))) := by
      rw [hstep, conjBy_conjBox]
      rw [add_neg_succ_smul n t]
    have hprod : (∏ j ∈ Finset.range (n + 1),
          ν (aDiag (((j : ℝ) + 1) • t) • x) (conjBox U t)) =
        ν y (conjBox U t) *
          ∏ j ∈ Finset.range n, ν (aDiag (((j : ℝ) + 1) • t) • y) (conjBox U t) := by
      rw [Finset.prod_range_succ', mul_comm]
      congr 1
      · rw [hy_def]
        simp only [Nat.cast_zero, zero_add, one_smul]
      · apply Finset.prod_congr rfl
        intro j _
        have hv : ((((j + 1 : ℕ) : ℝ) + 1) • t : Fin 3 → ℝ) = ((j : ℝ) + 1) • t + t := by
          ext i
          simp only [Pi.add_apply, Pi.smul_apply]
          push_cast
          ring
        have heq : aDiag ((((j + 1 : ℕ) : ℝ) + 1) • t) • x =
            aDiag (((j : ℝ) + 1) • t) • y := by
          rw [hy_def, aDiag_smul_mul, hv]
        rw [heq]
    rw [hcast, hprod, ← mul_assoc, hstep', hIH]

end Work.EKLC6Core

end
