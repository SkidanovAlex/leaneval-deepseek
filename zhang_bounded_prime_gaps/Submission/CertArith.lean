import Mathlib
import Submission.CertAnalytic
import Submission.CertJValue

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

open MeasureTheory Finset
open scoped BigOperators

/-!
# The two arithmetic identities of the `k = 50` certificate

This module reduces the two quadratic forms of the certificate,

  `I = IFuncOrth 50 certFun`,  `J = ∑ i, JFunc 50 i (24/25) certFun`,

to *integer* double sums over the certificate basis (`certISum`, `certJSum`), with all the
denominators cleared.  The remaining obligations are the two integer identities

  `certDI * certISum = certLam * certqI`,  `certDJ * certJSum = certLamJ * certqJ`,

where `certqI/certDI` and `certqJ/certDJ` are the exact rational values computed by
`Submission/numerics/exact.py` (stored in `Submission/CertData.lean`).
-/

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

/-- **The `I`-value of the certificate in the symmetric-monomial normalisation.** -/
theorem IFuncOrth_certFun_certCs :
    IFuncOrth 50 certFun
      = (certK : ℝ) * (certK : ℝ) *
          (∑ j : Fin 1780, ∑ j' : Fin 1780,
            (certCs j : ℝ) * (certCs j' : ℝ) *
              (((26 : ℝ) / 25) ^ (50 + certD j j') * ((certAA j j').factorial : ℝ) *
                (Ssum (certSig j) (certSig j') 50 : ℝ) /
                  (((certD j j' + 50).factorial : ℕ) : ℝ))) := by
  have hsum : (∑ j : Fin 1780, ∑ j' : Fin 1780,
        (certCl j : ℝ) * (certCl j' : ℝ) *
          ((theta (certSig j) : ℝ) * (theta (certSig j') : ℝ)) *
          (((26 : ℝ) / 25) ^ (50 + certD j j') * ((certAA j j').factorial : ℝ) *
            (Ssum (certSig j) (certSig j') 50 : ℝ) /
              (((certD j j' + 50).factorial : ℕ) : ℝ)))
      = ((certK : ℝ) * (certK : ℝ)) *
          (∑ j : Fin 1780, ∑ j' : Fin 1780,
            (certCs j : ℝ) * (certCs j' : ℝ) *
              (((26 : ℝ) / 25) ^ (50 + certD j j') * ((certAA j j').factorial : ℝ) *
                (Ssum (certSig j) (certSig j') 50 : ℝ) /
                  (((certD j j' + 50).factorial : ℕ) : ℝ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    have h1 : (certCl j : ℝ) * (theta (certSig j) : ℝ) = (certK : ℝ) * (certCs j : ℝ) := by
      exact_mod_cast certLab_rel j
    have h2 : (certCl j' : ℝ) * (theta (certSig j') : ℝ) = (certK : ℝ) * (certCs j' : ℝ) := by
      exact_mod_cast certLab_rel j'
    calc (certCl j : ℝ) * (certCl j' : ℝ)
          * ((theta (certSig j) : ℝ) * (theta (certSig j') : ℝ))
          * (((26 : ℝ) / 25) ^ (50 + certD j j') * ((certAA j j').factorial : ℝ) *
            (Ssum (certSig j) (certSig j') 50 : ℝ) / (((certD j j' + 50).factorial : ℕ) : ℝ))
        = ((certCl j : ℝ) * (theta (certSig j) : ℝ))
            * ((certCl j' : ℝ) * (theta (certSig j') : ℝ))
            * (((26 : ℝ) / 25) ^ (50 + certD j j') * ((certAA j j').factorial : ℝ) *
              (Ssum (certSig j) (certSig j') 50 : ℝ) / (((certD j j' + 50).factorial : ℕ) : ℝ)) := by
          ring
      _ = ((certK : ℝ) * (certCs j : ℝ)) * ((certK : ℝ) * (certCs j' : ℝ))
            * (((26 : ℝ) / 25) ^ (50 + certD j j') * ((certAA j j').factorial : ℝ) *
              (Ssum (certSig j) (certSig j') 50 : ℝ) / (((certD j j' + 50).factorial : ℕ) : ℝ)) := by
          rw [h1, h2]
      _ = ((certK : ℝ) * (certK : ℝ)) *
            ((certCs j : ℝ) * (certCs j' : ℝ) *
              (((26 : ℝ) / 25) ^ (50 + certD j j') * ((certAA j j').factorial : ℝ) *
                (Ssum (certSig j) (certSig j') 50 : ℝ) /
                  (((certD j j' + 50).factorial : ℕ) : ℝ))) := by ring
  rw [IFuncOrth_certFun_Ssum, hsum]

/-- The signature weight plus the `a`-exponent is at most `25` for the certificate basis. -/
theorem certA_add_sigsum_le (j : Fin 1780) : certA j + (certSig j).sum ≤ 25 := by
  have h := of_decide_eq_true (List.all_eq_true.mp certBasis_sum_le (certBasisAt j)
    (List.get_mem _ _))
  rw [certA, certSig]
  omega

theorem certD_le (j j' : Fin 1780) : certD j j' ≤ 50 := by
  have h := certA_add_sigsum_le j
  have h' := certA_add_sigsum_le j'
  rw [certD]
  omega

/-- `100! / (D+50)!` (the falling factorial `(D+51)⋯100`). -/
def certIFall (D : ℕ) : ℕ := (100).factorial / (D + 50).factorial

theorem certIFall_cast (D : ℕ) (hD : D ≤ 50) :
    ((certIFall D : ℕ) : ℝ) = ((100).factorial : ℝ) / (((D + 50).factorial : ℕ) : ℝ) := by
  have hdvd : (D + 50).factorial ∣ (100).factorial :=
    Nat.factorial_dvd_factorial (by omega)
  rw [certIFall, Nat.cast_div hdvd (by positivity)]

/-- The clearing denominator `Λ = 25^100 · 100!` of the `I`-form. -/
def certLam : ℤ := (25 : ℤ) ^ 100 * ((100).factorial : ℤ)

theorem certLam_ne_zero : certLam ≠ 0 := by
  rw [certLam]; positivity

theorem certDI_ne_zero : certDI ≠ 0 := by decide

/-- The cleared `I`-kernel `Λ·(26/25)^{50+D}A!/(D+50)!` as an integer. -/
def certIKern (j j' : Fin 1780) : ℤ :=
  (26 : ℤ) ^ (50 + certD j j') * (certIFall (certD j j') : ℤ) *
    ((certAA j j').factorial : ℤ) * (25 : ℤ) ^ (50 - certD j j')

/-- The cleared `I` quadratic form (an integer). -/
def certISum : ℤ := ∑ j : Fin 1780, ∑ j' : Fin 1780,
  certCs j * certCs j' * certIKern j j' * (Ssum (certSig j) (certSig j') 50 : ℤ)

theorem certLam_spec : (certLam : ℝ) = (25 : ℝ) ^ 100 * ((100).factorial : ℝ) := by
  rw [certLam]; push_cast; norm_num

/-- The cleared kernel is `Λ` times the rational kernel. -/
theorem certIKern_spec (j j' : Fin 1780) :
    ((certIKern j j' : ℤ) : ℝ)
      = (certLam : ℝ) * (((26 : ℝ) / 25) ^ (50 + certD j j') *
          ((certAA j j').factorial : ℝ) / (((certD j j' + 50).factorial : ℕ) : ℝ)) := by
  have hle := certD_le j j'
  have h25 : (25 : ℝ) ≠ 0 := by norm_num
  rw [certLam_spec, certIKern]
  push_cast
  rw [certIFall_cast (certD j j') (by omega), div_pow]
  rw [show (25 : ℝ) ^ 100
      = (25 : ℝ) ^ (50 + certD j j') * (25 : ℝ) ^ (50 - certD j j') from by
    rw [← pow_add]; congr 1; omega]
  field_simp

/-- **The `I`-value of the certificate**, from the arithmetic identity `certDI·certISum =
Λ·certqI`. -/
theorem IFuncOrth_certFun_value (h : certDI * certISum = certLam * certqI) :
    IFuncOrth 50 certFun = (certK : ℝ) * (certK : ℝ) * ((certqI : ℝ) / (certDI : ℝ)) := by
  rw [IFuncOrth_certFun_certCs]
  have hpair : ∀ j j' : Fin 1780, (certCs j : ℝ) * (certCs j' : ℝ) *
        (((26 : ℝ) / 25) ^ (50 + certD j j') * ((certAA j j').factorial : ℝ) *
          (Ssum (certSig j) (certSig j') 50 : ℝ) / (((certD j j' + 50).factorial : ℕ) : ℝ))
      = ((certCs j : ℝ) * (certCs j' : ℝ) * (certIKern j j' : ℝ) *
          (Ssum (certSig j) (certSig j') 50 : ℝ)) / (certLam : ℝ) := by
    intro j j'
    rw [certIKern_spec j j']
    have hL : (certLam : ℝ) ≠ 0 := by exact_mod_cast certLam_ne_zero
    field_simp
  have hsum1 : (∑ j : Fin 1780, ∑ j' : Fin 1780,
        (certCs j : ℝ) * (certCs j' : ℝ) *
          (((26 : ℝ) / 25) ^ (50 + certD j j') * ((certAA j j').factorial : ℝ) *
            (Ssum (certSig j) (certSig j') 50 : ℝ) /
              (((certD j j' + 50).factorial : ℕ) : ℝ)))
      = (certISum : ℝ) / (certLam : ℝ) := by
    rw [show (∑ j : Fin 1780, ∑ j' : Fin 1780,
          (certCs j : ℝ) * (certCs j' : ℝ) *
            (((26 : ℝ) / 25) ^ (50 + certD j j') * ((certAA j j').factorial : ℝ) *
              (Ssum (certSig j) (certSig j') 50 : ℝ) /
                (((certD j j' + 50).factorial : ℕ) : ℝ)))
        = (certLam : ℝ)⁻¹ * (∑ j : Fin 1780, ∑ j' : Fin 1780,
            (certCs j : ℝ) * (certCs j' : ℝ) * (certIKern j j' : ℝ) *
              (Ssum (certSig j) (certSig j') 50 : ℝ)) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      rw [hpair j j', div_eq_inv_mul]]
    rw [show (∑ j : Fin 1780, ∑ j' : Fin 1780,
          (certCs j : ℝ) * (certCs j' : ℝ) * (certIKern j j' : ℝ) *
            (Ssum (certSig j) (certSig j') 50 : ℝ)) = (certISum : ℝ) from by
      rw [certISum]; push_cast; rfl]
    rw [div_eq_inv_mul]
  have hsum2 : (∑ j : Fin 1780, ∑ j' : Fin 1780,
        (certCs j : ℝ) * (certCs j' : ℝ) *
          (((26 : ℝ) / 25) ^ (50 + certD j j') * ((certAA j j').factorial : ℝ) *
            (Ssum (certSig j) (certSig j') 50 : ℝ) /
              (((certD j j' + 50).factorial : ℕ) : ℝ)))
      = (certqI : ℝ) / (certDI : ℝ) := by
    rw [hsum1,
      div_eq_div_iff (by exact_mod_cast certLam_ne_zero) (by exact_mod_cast certDI_ne_zero)]
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at h2
    linarith [h2]
  rw [hsum2]

/-! ## The `J`-side clearing -/

/-- The exponent `ã = a + v + 1` of a `(j,v)`-term is at most `26`. -/
theorem certJHv_le (j : Fin 1780) (v : ℕ)
    (hv : v ∈ (0 :: (certSig j).dedup).toFinset) : v ≤ (certSig j).sum := by
  rw [List.mem_toFinset, List.mem_cons] at hv
  rcases hv with h0 | hmem
  · rw [h0]; omega
  · exact List.le_sum_of_mem (List.mem_dedup.mp hmem)

theorem certJExp_le (j : Fin 1780) (v : ℕ)
    (hv : v ∈ (0 :: (certSig j).dedup).toFinset) : certJExp j v ≤ 26 := by
  have h := certA_add_sigsum_le j
  have hvle := certJHv_le j v hv
  rw [certJExp]
  omega

/-- The clearing denominator of the `J`-form: `25^160 · 197! · (50!)²`. -/
def certJLam : ℤ := (25 : ℤ) ^ 160 * ((197).factorial : ℤ) * (((50).factorial : ℤ)) ^ 2

theorem certJLam_ne_zero : certJLam ≠ 0 := by
  rw [certJLam]; positivity

/-- `50! · κ(a,v)` as a natural number. -/
def certJKappaN' (j : Fin 1780) (v : ℕ) : ℕ :=
  (certA j).factorial * v.factorial * ((50).factorial / (certA j + v + 1).factorial)

/-- `50! · κ(a,v)`, as an integer. -/
def certJKappaN (j : Fin 1780) (v : ℕ) : ℤ := (certJKappaN' j v : ℤ)

theorem certJKappaN_spec (j : Fin 1780) (v : ℕ)
    (hv : v ∈ (0 :: (certSig j).dedup).toFinset) :
    ((certJKappaN j v : ℤ) : ℝ) = ((50).factorial : ℝ) * kappa (certA j) v := by
  have hle := certA_add_sigsum_le j
  have hvle := certJHv_le j v hv
  have hdvd : (certA j + v + 1).factorial ∣ (50).factorial :=
    Nat.factorial_dvd_factorial (by omega)
  have hcast : ((certJKappaN' j v : ℕ) : ℝ) = ((50).factorial : ℝ) * kappa (certA j) v := by
    rw [certJKappaN', kappa]
    push_cast
    rw [Nat.cast_div hdvd (by positivity)]
    field_simp
  simpa only [certJKappaN, Int.cast_natCast] using hcast

/-- The weight sum `L = |β| + |β'|` of a pair of `certH`-terms. -/
def certJLM (j : Fin 1780) (v : ℕ) (j' : Fin 1780) (v' : ℕ) : ℕ :=
  (certJBeta j v).sum + (certJBeta j' v').sum

theorem certJN_le (j : Fin 1780) (v : ℕ) (hv : v ∈ (0 :: (certSig j).dedup).toFinset)
    (j' : Fin 1780) (v' : ℕ) (hv' : v' ∈ (0 :: (certSig j').dedup).toFinset) :
    certJN j v j' v' ≤ 52 := by
  have h := certJExp_le j v hv
  have h' := certJExp_le j' v' hv'
  rw [certJN]
  omega

theorem certJLM_le (j : Fin 1780) (v : ℕ) (j' : Fin 1780) (v' : ℕ) :
    certJLM j v j' v' ≤ 50 := by
  have h := certJBeta_sum_le j v
  have h' := certJBeta_sum_le j' v'
  rw [certJLM]
  omega

/-- A single cleared `Ψ`-term. -/
def certJPsiTermN (N L jj : ℕ) : ℕ :=
  N.choose jj * 2 ^ jj * 24 ^ (49 + N - jj + L) * (N - jj).factorial * 25 ^ (111 - N - L) *
    ((197).factorial / ((N - jj) + L + 49).factorial)

/-- The cleared `Ψ`-sum of a pair of `certH`-terms, as a natural number. -/
def certJPsiN (j : Fin 1780) (v : ℕ) (j' : Fin 1780) (v' : ℕ) : ℕ :=
  ∑ jj ∈ Finset.range (certJN j v j' v' + 1),
    certJPsiTermN (certJN j v j' v') (certJLM j v j' v') jj

/-- The cleared `J` quadratic form (an integer). -/
def certJSum : ℤ := ∑ j : Fin 1780, ∑ j' : Fin 1780,
  ∑ v ∈ (0 :: (certSig j).dedup).toFinset,
  ∑ v' ∈ (0 :: (certSig j').dedup).toFinset,
    certCs j * certCs j' * certJKappaN j v * certJKappaN j' v' *
      (Ssum (certJBeta j v) (certJBeta j' v') 49 : ℤ) * (certJPsiN j v j' v' : ℤ)

theorem certJLam_spec :
    (certJLam : ℝ) = (25 : ℝ) ^ 160 * ((197).factorial : ℝ) * ((50).factorial : ℝ) ^ 2 := by
  rw [certJLam]; push_cast; norm_num

/-- The cleared `Ψ`-sum is `25^160·197!` times the rational one. -/
theorem certJPsiN_spec (j : Fin 1780) (v : ℕ) (hv : v ∈ (0 :: (certSig j).dedup).toFinset)
    (j' : Fin 1780) (v' : ℕ) (hv' : v' ∈ (0 :: (certSig j').dedup).toFinset) :
    ((certJPsiN j v j' v' : ℕ) : ℝ) = ((25 : ℝ) ^ 160 * ((197).factorial : ℝ)) *
      certJPsi j v j' v' := by
  have h2N : certJN j v j' v' ≤ 52 := certJN_le j v hv j' v' hv'
  have h2L : certJLM j v j' v' ≤ 50 := certJLM_le j v j' v'
  have hdvd : ∀ k : ℕ, k + 49 ≤ 197 →
      (k + 49).factorial ∣ (197).factorial := fun k hk => Nat.factorial_dvd_factorial hk
  have hE1 : ∀ k L : ℕ, 49 + k + L = 49 + k + L := fun _ _ => rfl
  have hsplit : ∀ (x : ℝ) (k L : ℕ), x ^ (49 + k + L) = x ^ 49 * x ^ k * x ^ L := by
    intro x k L
    rw [pow_add, pow_add]
  rw [certJPsiN, certJPsi, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun jj hjj => ?_)
  rw [Finset.mem_range] at hjj
  have hjle : jj ≤ certJN j v j' v' := by omega
  rw [certJPsiTermN, certJLM,
    show (49 + certJN j v j' v' - jj + ((certJBeta j v).sum + (certJBeta j' v').sum))
      = 49 + (certJN j v j' v' - jj) + ((certJBeta j v).sum + (certJBeta j' v').sum) from by omega,
    show (certJN j v j' v' - jj + ((certJBeta j v).sum + (certJBeta j' v').sum) + 49)
      = 49 + (certJN j v j' v' - jj) + ((certJBeta j v).sum + (certJBeta j' v').sum) from by omega]
  have hc : certJN j v j' v' - jj ≤ 52 := le_trans (Nat.sub_le _ _) h2N
  have hLsum : ((certJBeta j v).sum + (certJBeta j' v').sum) ≤ 50 := by
    have hh := h2L
    rw [certJLM] at hh
    exact hh
  have hd : (49 + (certJN j v j' v' - jj) + ((certJBeta j v).sum + (certJBeta j' v').sum)).factorial
      ∣ (197).factorial := Nat.factorial_dvd_factorial (by omega)
  have h160 : (25 : ℝ) ^ 160 = (25 : ℝ) ^ jj * (25 : ℝ) ^ 49 * (25 : ℝ) ^ (certJN j v j' v' - jj)
      * (25 : ℝ) ^ ((certJBeta j v).sum + (certJBeta j' v').sum)
      * (25 : ℝ) ^ (111 - certJN j v j' v' - ((certJBeta j v).sum + (certJBeta j' v').sum)) := by
    rw [show (160 : ℕ) = jj + (49 + (certJN j v j' v' - jj)
        + ((certJBeta j v).sum + (certJBeta j' v').sum))
        + (111 - certJN j v j' v' - ((certJBeta j v).sum + (certJBeta j' v').sum)) from by
      have h1 : jj + (certJN j v j' v' - jj) = certJN j v j' v' := Nat.add_sub_cancel' hjle
      have h2 : certJN j v j' v' + ((certJBeta j v).sum + (certJBeta j' v').sum) ≤ 111 := by omega
      omega,
      pow_add, pow_add, pow_add, pow_add]
    ring
  push_cast
  rw [Nat.cast_div hd (by positivity), div_pow, div_pow,
    hsplit ((24 : ℝ)) (certJN j v j' v' - jj) ((certJBeta j v).sum + (certJBeta j' v').sum),
    h160]
  rw [show (certJN j v j' v' - jj + (certJBeta j v).sum + (certJBeta j' v').sum + 49)
      = 49 + (certJN j v j' v' - jj) + ((certJBeta j v).sum + (certJBeta j' v').sum) from by omega,
    show (49 + (certJN j v j' v' - jj) + (certJBeta j v).sum + (certJBeta j' v').sum)
      = 49 + (certJN j v j' v' - jj) + ((certJBeta j v).sum + (certJBeta j' v').sum) from by omega,
    hsplit ((25 : ℝ)) (certJN j v j' v' - jj) ((certJBeta j v).sum + (certJBeta j' v').sum)]
  field_simp
  rw [hsplit ((24 : ℝ)) (certJN j v j' v' - jj) ((certJBeta j v).sum + (certJBeta j' v').sum)]
  ring

theorem certDJ_ne_zero : certDJ ≠ 0 := by decide

/-- **The `J`-value of the certificate**, from the arithmetic identity `certDJ·certJSum =
certJLam·certqJ`. -/
theorem sum_JFunc_certFun_value (h : certDJ * certJSum = certJLam * certqJ) :
    ∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) certFun
      = 50 * (certK : ℝ) * (certK : ℝ) * ((certqJ : ℝ) / (certDJ : ℝ)) := by
  rw [sum_JFunc_certFun_certCs]
  have hpair : ∀ (j : Fin 1780) (v : ℕ) (hv : v ∈ (0 :: (certSig j).dedup).toFinset)
      (j' : Fin 1780) (v' : ℕ) (hv' : v' ∈ (0 :: (certSig j').dedup).toFinset),
      (certCs j : ℝ) * (certCs j' : ℝ) * (kappa (certA j) v * kappa (certA j') v') *
          (Ssum (certJBeta j v) (certJBeta j' v') 49 : ℝ) * certJPsi j v j' v'
        = ((certCs j : ℝ) * (certCs j' : ℝ) * ((certJKappaN j v : ℤ) : ℝ)
            * ((certJKappaN j' v' : ℤ) : ℝ) *
            (Ssum (certJBeta j v) (certJBeta j' v') 49 : ℝ)
            * ((certJPsiN j v j' v' : ℕ) : ℝ)) / (certJLam : ℝ) := by
    intro j v hv j' v' hv'
    rw [certJKappaN_spec j v hv, certJKappaN_spec j' v' hv', certJPsiN_spec j v hv j' v' hv',
      certJLam_spec]
    field_simp
  have hsum1 : (∑ j : Fin 1780, ∑ j' : Fin 1780,
        ∑ v ∈ (0 :: (certSig j).dedup).toFinset,
        ∑ v' ∈ (0 :: (certSig j').dedup).toFinset,
          (certCs j : ℝ) * (certCs j' : ℝ) * (kappa (certA j) v * kappa (certA j') v') *
            (Ssum (certJBeta j v) (certJBeta j' v') 49 : ℝ) * certJPsi j v j' v')
      = (certJSum : ℝ) / (certJLam : ℝ) := by
    rw [show (∑ j : Fin 1780, ∑ j' : Fin 1780,
          ∑ v ∈ (0 :: (certSig j).dedup).toFinset,
          ∑ v' ∈ (0 :: (certSig j').dedup).toFinset,
            (certCs j : ℝ) * (certCs j' : ℝ) * (kappa (certA j) v * kappa (certA j') v') *
              (Ssum (certJBeta j v) (certJBeta j' v') 49 : ℝ) * certJPsi j v j' v')
        = (certJLam : ℝ)⁻¹ * (∑ j : Fin 1780, ∑ j' : Fin 1780,
            ∑ v ∈ (0 :: (certSig j).dedup).toFinset,
            ∑ v' ∈ (0 :: (certSig j').dedup).toFinset,
              (certCs j : ℝ) * (certCs j' : ℝ) * ((certJKappaN j v : ℤ) : ℝ)
                * ((certJKappaN j' v' : ℤ) : ℝ) *
                (Ssum (certJBeta j v) (certJBeta j' v') 49 : ℝ)
                * ((certJPsiN j v j' v' : ℕ) : ℝ)) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v hv => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v' hv' => by
        rw [hpair j v hv j' v' hv', div_eq_inv_mul])]
    rw [show (∑ j : Fin 1780, ∑ j' : Fin 1780,
          ∑ v ∈ (0 :: (certSig j).dedup).toFinset,
          ∑ v' ∈ (0 :: (certSig j').dedup).toFinset,
            (certCs j : ℝ) * (certCs j' : ℝ) * ((certJKappaN j v : ℤ) : ℝ)
              * ((certJKappaN j' v' : ℤ) : ℝ) *
              (Ssum (certJBeta j v) (certJBeta j' v') 49 : ℝ)
              * ((certJPsiN j v j' v' : ℕ) : ℝ)) = (certJSum : ℝ) from by
      rw [certJSum]; push_cast; rfl]
    rw [div_eq_inv_mul]
  have hsum2 : (∑ j : Fin 1780, ∑ j' : Fin 1780,
        ∑ v ∈ (0 :: (certSig j).dedup).toFinset,
        ∑ v' ∈ (0 :: (certSig j').dedup).toFinset,
          (certCs j : ℝ) * (certCs j' : ℝ) * (kappa (certA j) v * kappa (certA j') v') *
            (Ssum (certJBeta j v) (certJBeta j' v') 49 : ℝ) * certJPsi j v j' v')
      = (certqJ : ℝ) / (certDJ : ℝ) := by
    rw [hsum1,
      div_eq_div_iff (by exact_mod_cast certJLam_ne_zero) (by exact_mod_cast certDJ_ne_zero)]
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at h2
    linarith [h2]
  rw [hsum2]

end

end Commons.NumberTheory.MaynardSieve
