import Mathlib
import Submission.Work.TMC7Core.Fourier.ldt_setup
import Submission.Work.TMC7Core.Fourier.tail_L2_aux

/-!
# TMC7Core: Fourier coefficients of the moving average

The `m`-th Fourier coefficient of the normalised moving average
`R⁻² ∑_{j,j'} G(· + (j - j') α)` of an integrable function `G` on the circle is the product of
the `m`-th Fourier coefficient of `G` with the Fejér kernel `fejerKer R (m α)`.

The proof is the standard one: by linearity of the Fourier coefficient the double sum can be moved
outside, each translation multiplies the coefficient by the corresponding character
(`fourierCoeff_translate`), and the resulting double geometric sum is
`‖∑_{j<R} e^{2πi j (mα)}‖²/R² = fejerKer R (m α)`.
-/

open MeasureTheory Finset

noncomputable section

namespace Work.TMC7Core.Fourier

/-- Linearity of the Fourier coefficient over a finite sum of functions. -/
private lemma fourierCoeff_sum_fun {ι : Type*} (s : Finset ι) (F : ι → AddCircle (1 : ℝ) → ℂ)
    (hF : ∀ i ∈ s, Integrable (F i) AddCircle.haarAddCircle) (m : ℤ) :
    fourierCoeff (fun t => ∑ i ∈ s, F i t) m = ∑ i ∈ s, fourierCoeff (F i) m := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      simp [fourierCoeff]
  | insert a s ha ih =>
      have hFa : Integrable (F a) AddCircle.haarAddCircle := hF a (Finset.mem_insert_self a s)
      have hFs : ∀ i ∈ s, Integrable (F i) AddCircle.haarAddCircle :=
        fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hsumint : Integrable (fun t => ∑ i ∈ s, F i t) AddCircle.haarAddCircle :=
        MeasureTheory.integrable_finsetSum s hFs
      have hsplit : (fun t => ∑ i ∈ insert a s, F i t) = (F a + fun t => ∑ i ∈ s, F i t) := by
        funext t
        rw [Finset.sum_insert ha]
        rfl
      rw [Finset.sum_insert ha, hsplit, fourierCoeff.add hFa hsumint]
      simp only [Pi.add_apply]
      rw [ih hFs]

/-- Translation of an integrable function on the circle is integrable, by invariance of the Haar
measure. -/
private lemma mave_translate_integrable (G : AddCircle (1 : ℝ) → ℂ)
    (hG : Integrable G AddCircle.haarAddCircle) (c : ℝ) :
    Integrable (fun t : AddCircle (1 : ℝ) => G (t + (c : AddCircle (1 : ℝ))))
      AddCircle.haarAddCircle := by
  have hmp : MeasurePreserving (fun t : AddCircle (1 : ℝ) => t + (c : AddCircle (1 : ℝ)))
      AddCircle.haarAddCircle AddCircle.haarAddCircle :=
    MeasureTheory.MeasurePreserving.add_right AddCircle.haarAddCircle (c : AddCircle (1 : ℝ))
      (MeasurePreserving.id AddCircle.haarAddCircle)
  exact hmp.integrable_comp_of_integrable hG

/-- The double sum of the characters `fourier m ((j - j') α)` collapses to the Fejér kernel. -/
private lemma sum_fourier_shift_aux (R : ℕ) (α : ℝ) (m : ℤ) :
    ((R : ℂ) ^ 2)⁻¹ * ∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
        (fourier m ((((j : ℝ) - (j' : ℝ)) * α : ℝ) : AddCircle (1 : ℝ)))
      = (fejerKer R ((m : ℝ) * α) : ℂ) := by
  have hterm : ∀ (j j' : ℕ), (fourier m ((((j:ℝ)-(j':ℝ))*α : ℝ) : AddCircle (1:ℝ)))
      = Complex.exp (2 * Real.pi * Complex.I * (j:ℝ) * ((m:ℝ)*α))
        * (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (j':ℝ) * ((m:ℝ)*α))) := by
    intro j j'
    rw [fourier_coe_apply]
    have hconj : (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (j':ℝ) * ((m:ℝ)*α)))
        = Complex.exp (-(2 * Real.pi * Complex.I * (j':ℝ) * ((m:ℝ)*α))) := by
      rw [← Complex.exp_conj]
      congr 1
      have h : (2 * Real.pi * Complex.I * (j':ℝ) * ((m:ℝ)*α))
          = ((2 * Real.pi * (j':ℝ) * ((m:ℝ)*α) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [h, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [hconj, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  set Z : ℂ := ∑ j ∈ Finset.range R,
    Complex.exp (2 * Real.pi * Complex.I * (j:ℝ) * ((m:ℝ)*α)) with hZdef
  have hconjsum : (∑ j' ∈ Finset.range R,
        (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (j':ℝ) * ((m:ℝ)*α))))
      = (starRingEnd ℂ) Z := by
    rw [hZdef]
    exact (map_sum (starRingEnd ℂ)
      (fun x : ℕ => Complex.exp (2 * Real.pi * Complex.I * (x:ℝ) * ((m:ℝ)*α)))
      (Finset.range R)).symm
  have hmiddle : (∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
        (Complex.exp (2 * Real.pi * Complex.I * (j:ℝ) * ((m:ℝ)*α))
          * (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (j':ℝ) * ((m:ℝ)*α)))))
      = Z * (starRingEnd ℂ) Z := by
    have h1 : ∀ j ∈ Finset.range R, (∑ j' ∈ Finset.range R,
          (Complex.exp (2 * Real.pi * Complex.I * (j:ℝ) * ((m:ℝ)*α))
            * (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (j':ℝ) * ((m:ℝ)*α)))))
        = Complex.exp (2 * Real.pi * Complex.I * (j:ℝ) * ((m:ℝ)*α)) * (starRingEnd ℂ) Z := by
      intro j _
      rw [← Finset.mul_sum, hconjsum]
    calc (∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
          (Complex.exp (2 * Real.pi * Complex.I * (j:ℝ) * ((m:ℝ)*α))
            * (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (j':ℝ) * ((m:ℝ)*α)))))
        = ∑ j ∈ Finset.range R, (Complex.exp (2 * Real.pi * Complex.I * (j:ℝ) * ((m:ℝ)*α))
            * (starRingEnd ℂ) Z) := Finset.sum_congr rfl h1
      _ = (∑ j ∈ Finset.range R, Complex.exp (2 * Real.pi * Complex.I * (j:ℝ) * ((m:ℝ)*α)))
            * (starRingEnd ℂ) Z := (Finset.sum_mul _ _ _).symm
      _ = Z * (starRingEnd ℂ) Z := by rw [← hZdef]
  have hZ : Z * (starRingEnd ℂ) Z = ((‖Z‖^2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hZeq : (∑ j ∈ Finset.range R,
        Complex.exp (2 * Real.pi * Complex.I * (j : ℝ) * (((m:ℝ)*α : ℝ) : ℂ))) = Z := by
    rw [hZdef]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    push_cast
    ring
  have hfej : (fejerKer R ((m:ℝ)*α) : ℂ) = ((R:ℂ)^2)⁻¹ * ((‖Z‖^2 : ℝ) : ℂ) := by
    rw [fejerKer_def', hZeq]
    rw [norm_div, Complex.norm_natCast, div_pow]
    push_cast
    rw [div_eq_inv_mul]
  calc ((R:ℂ)^2)⁻¹ * ∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
        (fourier m ((((j:ℝ)-(j':ℝ))*α : ℝ) : AddCircle (1:ℝ)))
      = ((R:ℂ)^2)⁻¹ * (∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
          (Complex.exp (2 * Real.pi * Complex.I * (j:ℝ) * ((m:ℝ)*α))
            * (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (j':ℝ) * ((m:ℝ)*α))))) := by
        congr 1
        exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => hterm j j'))
    _ = ((R:ℂ)^2)⁻¹ * (Z * (starRingEnd ℂ) Z) := by rw [hmiddle]
    _ = ((R:ℂ)^2)⁻¹ * ((‖Z‖^2 : ℝ) : ℂ) := by rw [hZ]
    _ = (fejerKer R ((m:ℝ)*α) : ℂ) := hfej.symm

theorem mave_coeff2 (G : AddCircle (1 : ℝ) → ℂ) (hG : MeasureTheory.Integrable G AddCircle.haarAddCircle)
    (α : ℝ) (R : ℕ) (hR : 1 ≤ R) (m : ℤ) :
    fourierCoeff (fun t : AddCircle (1 : ℝ) =>
        ((R : ℂ) ^ 2)⁻¹ * ∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
          G (t + ((((j : ℝ) - (j' : ℝ)) * α : ℝ) : AddCircle (1 : ℝ)))) m
      = fourierCoeff G m * (fejerKer R ((m : ℝ) * α) : ℂ) := by
  have htr : ∀ c : ℝ, Integrable (fun t : AddCircle (1:ℝ) =>
      G (t + (c : AddCircle (1:ℝ)))) AddCircle.haarAddCircle :=
    fun c => mave_translate_integrable G hG c
  rw [fourierCoeff.const_mul]
  have hInt : ∀ j ∈ Finset.range R, Integrable (fun t : AddCircle (1:ℝ) =>
      ∑ j' ∈ Finset.range R, G (t + ((((j:ℝ)-(j':ℝ))*α : ℝ) : AddCircle (1:ℝ))))
      AddCircle.haarAddCircle := by
    intro j _
    exact MeasureTheory.integrable_finsetSum (Finset.range R) (fun j' _ => htr (((j:ℝ)-(j':ℝ))*α))
  rw [fourierCoeff_sum_fun (Finset.range R)
      (fun j => fun t : AddCircle (1:ℝ) => ∑ j' ∈ Finset.range R,
        G (t + ((((j:ℝ)-(j':ℝ))*α : ℝ) : AddCircle (1:ℝ)))) hInt m]
  have hinner : ∀ j ∈ Finset.range R, fourierCoeff (fun t : AddCircle (1:ℝ) =>
        ∑ j' ∈ Finset.range R, G (t + ((((j:ℝ)-(j':ℝ))*α : ℝ) : AddCircle (1:ℝ)))) m
      = ∑ j' ∈ Finset.range R,
          (fourier m ((((j:ℝ)-(j':ℝ))*α : ℝ) : AddCircle (1:ℝ)) * fourierCoeff G m) := by
    intro j _
    rw [fourierCoeff_sum_fun (Finset.range R)
        (fun j' => fun t : AddCircle (1:ℝ) =>
          G (t + ((((j:ℝ)-(j':ℝ))*α : ℝ) : AddCircle (1:ℝ))))
        (fun _ _ => htr _) m]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    rw [fourierCoeff_translate G (((j:ℝ)-(j':ℝ))*α) m]
  rw [Finset.sum_congr rfl hinner]
  have hfactor : (∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
        (fourier m ((((j:ℝ)-(j':ℝ))*α : ℝ) : AddCircle (1:ℝ)) * fourierCoeff G m))
      = (∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
        (fourier m ((((j:ℝ)-(j':ℝ))*α : ℝ) : AddCircle (1:ℝ)))) * fourierCoeff G m := by
    calc (∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
          (fourier m ((((j:ℝ)-(j':ℝ))*α : ℝ) : AddCircle (1:ℝ)) * fourierCoeff G m))
        = ∑ j ∈ Finset.range R, ((∑ j' ∈ Finset.range R,
            fourier m ((((j:ℝ)-(j':ℝ))*α : ℝ) : AddCircle (1:ℝ))) * fourierCoeff G m) :=
          Finset.sum_congr rfl (fun j _ => (Finset.sum_mul _ _ _).symm)
      _ = (∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
            fourier m ((((j:ℝ)-(j':ℝ))*α : ℝ) : AddCircle (1:ℝ))) * fourierCoeff G m :=
          (Finset.sum_mul _ _ _).symm
  rw [hfactor]
  rw [show ((R:ℂ)^2)⁻¹ * ((∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
        fourier m ((((j:ℝ)-(j':ℝ))*α : ℝ) : AddCircle (1:ℝ))) * fourierCoeff G m)
      = fourierCoeff G m * (((R:ℂ)^2)⁻¹ * (∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
        fourier m ((((j:ℝ)-(j':ℝ))*α : ℝ) : AddCircle (1:ℝ)))) by ring]
  rw [sum_fourier_shift_aux R α m]

end Work.TMC7Core.Fourier
