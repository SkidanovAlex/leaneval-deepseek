import Mathlib
import Submission.Work.Cert.LeafAux

namespace Work.Cert

/-- Reverse of `norm_cx_le_of_sq_le`: a LOWER bound on `‖cx x y‖` from `m² ≤ x² + y²`. -/
lemma norm_cx_ge_of_sq_le (x y m : ℤ) (hm : 0 ≤ m) (h : m * m ≤ x * x + y * y) :
    (m : ℝ) / (S : ℝ) ≤ ‖cx x y‖ := by
  have hcast : (m : ℝ) ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 := by
    have h' : ((m * m : ℤ) : ℝ) ≤ ((x * x + y * y : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    simpa [sq] using h'
  have hmR : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2 : ((m : ℝ) / (S : ℝ)) ^ 2 ≤ ‖cx x y‖ ^ 2 := by
    rw [norm_cx_sq, div_pow]
    exact div_le_div_of_nonneg_right hcast (sq_nonneg _)
  calc (m : ℝ) / (S : ℝ)
      = Real.sqrt (((m : ℝ) / (S : ℝ)) ^ 2) := (Real.sqrt_sq (div_nonneg hmR S_posR.le)).symm
    _ ≤ Real.sqrt (‖cx x y‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖cx x y‖ := Real.sqrt_sq (norm_nonneg _)

set_option maxRecDepth 100000 in
theorem theta_bounds (hT : Work.Cert.ThetaEncl) (qr qi rq mU m aU bL : ℤ)
    (hm : m = mU + rq + 1) (hmU : 0 ≤ mU) (hq : qr * qr + qi * qi ≤ mU * mU) (hrq : 0 ≤ rq)
    (hokm : m ≤ Work.Cert.fdiv (79 * Work.Cert.S) 100)
    (haU : 0 ≤ aU) (hA : (Work.Cert.Acell qr qi rq m).Ar ^ 2 + (Work.Cert.Acell qr qi rq m).Ai ^ 2 ≤ aU ^ 2)
    (hbL : 0 ≤ bL) (hB : bL ^ 2 ≤ (Work.Cert.Bcell qr qi rq m).Br ^ 2 + (Work.Cert.Bcell qr qi rq m).Bi ^ 2)
    (q : ℂ) (hqmem : ‖q - Work.Cert.cx qr qi‖ ≤ (rq : ℝ) / (Work.Cert.S : ℝ)) :
    ‖Work.Cert.thetaA q‖ ≤ ((Work.Cert.AupZ qr qi rq m aU : ℤ) : ℝ) / (Work.Cert.S : ℝ) ∧
      ((Work.Cert.BloZ qr qi rq m bL : ℤ) : ℝ) / (Work.Cert.S : ℝ) ≤ ‖Work.Cert.thetaB q‖ := by
  subst hm
  -- the enclosures, restated with the `Acell`/`Bcell` abbreviations
  have hTA :
      ‖thetaA q - cx (Acell qr qi rq (mU + rq + 1)).Ar (Acell qr qi rq (mU + rq + 1)).Ai‖
        ≤ (((Acell qr qi rq (mU + rq + 1)).dA + tailAZ qr qi rq (mU + rq + 1) : ℤ) : ℝ)
            / (S : ℝ) :=
    (hT qr qi rq mU hmU hq hrq hokm q hqmem).1
  have hTB :
      ‖thetaB q - cx (Bcell qr qi rq (mU + rq + 1)).Br (Bcell qr qi rq (mU + rq + 1)).Bi‖
        ≤ (((Bcell qr qi rq (mU + rq + 1)).dB + tailBZ qr qi rq (mU + rq + 1) : ℤ) : ℝ)
            / (S : ℝ) :=
    (hT qr qi rq mU hmU hq hrq hokm q hqmem).2
  refine ⟨?_, ?_⟩
  · -- upper bound for `‖thetaA q‖`
    have hAnorm :
        ‖cx (Acell qr qi rq (mU + rq + 1)).Ar (Acell qr qi rq (mU + rq + 1)).Ai‖
          ≤ (aU : ℝ) / (S : ℝ) :=
      norm_cx_le_of_sq_le _ _ _ haU (by simpa [pow_two] using hA)
    have htri : ‖thetaA q‖
        ≤ ‖thetaA q - cx (Acell qr qi rq (mU + rq + 1)).Ar (Acell qr qi rq (mU + rq + 1)).Ai‖
          + ‖cx (Acell qr qi rq (mU + rq + 1)).Ar (Acell qr qi rq (mU + rq + 1)).Ai‖ := by
      simpa only [sub_add_cancel] using
        norm_add_le
          (thetaA q - cx (Acell qr qi rq (mU + rq + 1)).Ar (Acell qr qi rq (mU + rq + 1)).Ai)
          (cx (Acell qr qi rq (mU + rq + 1)).Ar (Acell qr qi rq (mU + rq + 1)).Ai)
    have hsum := add_le_add hTA hAnorm
    have heq : (((Acell qr qi rq (mU + rq + 1)).dA + tailAZ qr qi rq (mU + rq + 1) : ℤ) : ℝ)
          / (S : ℝ) + (aU : ℝ) / (S : ℝ)
        = ((AupZ qr qi rq (mU + rq + 1) aU : ℤ) : ℝ) / (S : ℝ) := by
      simp only [AupZ]; push_cast; ring
    linarith [htri, hsum, heq]
  · -- lower bound for `‖thetaB q‖`
    have hBnorm :
        (bL : ℝ) / (S : ℝ)
          ≤ ‖cx (Bcell qr qi rq (mU + rq + 1)).Br (Bcell qr qi rq (mU + rq + 1)).Bi‖ :=
      norm_cx_ge_of_sq_le _ _ _ hbL (by simpa [pow_two] using hB)
    have htri : ‖cx (Bcell qr qi rq (mU + rq + 1)).Br (Bcell qr qi rq (mU + rq + 1)).Bi‖
        ≤ ‖thetaB q‖
          + ‖thetaB q - cx (Bcell qr qi rq (mU + rq + 1)).Br (Bcell qr qi rq (mU + rq + 1)).Bi‖ := by
      simpa only [sub_sub_cancel] using
        norm_sub_le (thetaB q)
          (thetaB q - cx (Bcell qr qi rq (mU + rq + 1)).Br (Bcell qr qi rq (mU + rq + 1)).Bi)
    have heq : (bL : ℝ) / (S : ℝ)
          - (((Bcell qr qi rq (mU + rq + 1)).dB + tailBZ qr qi rq (mU + rq + 1) : ℤ) : ℝ)
              / (S : ℝ)
        = ((BloZ qr qi rq (mU + rq + 1) bL : ℤ) : ℝ) / (S : ℝ) := by
      simp only [BloZ]; push_cast; ring
    linarith [hBnorm, htri, hTB, heq]

end Work.Cert
