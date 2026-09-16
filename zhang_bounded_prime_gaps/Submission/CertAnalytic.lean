import Mathlib
import Submission.CertData
import Submission.SimplexMono
import Submission.SlabTheta
import Submission.MaynardFunctionals

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open MeasureTheory Finset
open scoped BigOperators

/-!
# The analytic certificate: `IFuncOrth` of the labelled certificate function

The certificate of `Submission/CertData.lean` is the symmetric polynomial

  `F(t) = Σ_{j < 1780} c_j · (1 + 1/25 - Σ_i t_i)^{a_j} · m_{α_j}(t)`

restricted to the simplex `(1 + 1/25)·R^{50}`.  This module defines its *labelled* version
(`certFun`, using `lmono` and the integer labelled coefficients `certCoefLab`) and proves the
master expansion

  `IFuncOrth 50 certFun = Σ_{j,j'} c_j c_{j'} (26/25)^{50+D} A! Slab(α_j,α_{j'},50) / (D+50)!`

from the termwise formula `simplex_integral_lmono`.  The remaining arithmetic (contracting this
double sum with `Ssum`, `Submission/numerics/exact.py`) is the packed-aggregation task.
-/

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

/-- The `j`-th element of the certificate basis (`j < 1780 = certBasis.length`). -/
def certBasisAt (j : Fin 1780) : ℕ × List ℕ :=
  certBasis.get ⟨(j : ℕ), by simpa [certBasis_length] using j.isLt⟩

/-- The `(1+ε-P₁)`-exponent of the `j`-th basis element. -/
def certA (j : Fin 1780) : ℕ := (certBasisAt j).1

/-- The signature of the `j`-th basis element. -/
def certSig (j : Fin 1780) : List ℕ := (certBasisAt j).2

/-- The labelled coefficient of the `j`-th basis element. -/
def certCl (j : Fin 1780) : ℤ :=
  certCoefLab.get ⟨(j : ℕ), by simpa [certCoefLab_length] using j.isLt⟩

/-- The total degree `D = (a_j + |α_j|) + (a_{j'} + |α_{j'}|)` of a basis pair. -/
def certD (j j' : Fin 1780) : ℕ :=
  (certA j + (certSig j).sum) + (certA j' + (certSig j').sum)

/-- The numerator exponent `A = a_j + a_{j'}` of a basis pair. -/
def certAA (j j' : Fin 1780) : ℕ := certA j + certA j'

/-- The certificate polynomial, *without* the simplex indicator. -/
def certPoly (t : Fin 50 → ℝ) : ℝ :=
  ∑ j : Fin 1780, (certCl j : ℝ) * ((26 : ℝ) / 25 - ∑ i, t i) ^ (certA j) *
    lmono (certSig j) 50 t

/-- The certificate function: the polynomial, cut off on the enlarged simplex
`(26/25)·R^{50} = {t ≥ 0, Σ t ≤ 26/25}`. -/
def certFun (t : Fin 50 → ℝ) : ℝ := (simplexC 50 ((26 : ℝ) / 25)).indicator certPoly t

/-- `lmono` is continuous (it is a polynomial). -/
theorem continuous_lmono (α : List ℕ) (k : ℕ) : Continuous (lmono α k) := by
  unfold lmono
  refine continuous_finsetSum _ (fun e _ => ?_)
  refine continuous_finsetProd _ (fun i _ => ?_)
  exact (continuous_apply (e i)).pow _

/-- The `j`-th summand of the certificate polynomial. -/
def certTerm (j : Fin 1780) (t : Fin 50 → ℝ) : ℝ :=
  (certCl j : ℝ) * ((26 : ℝ) / 25 - ∑ i, t i) ^ (certA j) * lmono (certSig j) 50 t

theorem certPoly_eq (t : Fin 50 → ℝ) : certPoly t = ∑ j : Fin 1780, certTerm j t := rfl

theorem continuous_certTerm (j : Fin 1780) : Continuous (certTerm j) := by
  unfold certTerm
  refine Continuous.mul (Continuous.mul continuous_const ?_) ?_
  · exact (continuous_const.sub (continuous_finsetSum _ (fun i _ => continuous_apply i))).pow _
  · exact continuous_lmono _ _

/-- **The master expansion of the certificate's `IFuncOrth`.** -/
theorem IFuncOrth_certFun :
    IFuncOrth 50 certFun
      = ∑ j : Fin 1780, ∑ j' : Fin 1780,
          (certCl j : ℝ) * (certCl j' : ℝ) *
            (((26 : ℝ) / 25) ^ (50 + certD j j') * ((certAA j j').factorial : ℝ) *
              (Slab (certSig j) (certSig j') 50 : ℝ) /
                (((certD j j' + 50).factorial : ℕ) : ℝ)) := by
  classical
  have hc : (0 : ℝ) < (26 : ℝ) / 25 := by norm_num
  have hs : MeasurableSet (simplexC 50 ((26 : ℝ) / 25)) := (isClosed_simplexC 50 _).measurableSet
  have h1 : IFuncOrth 50 certFun
      = ∫ t in simplexC 50 ((26 : ℝ) / 25), (certPoly t) ^ 2 := by
    have hfun : (fun t : Fin 50 → ℝ => (certFun t) ^ 2)
        = (simplexC 50 ((26 : ℝ) / 25)).indicator (fun t => (certPoly t) ^ 2) := by
      funext t
      rw [certFun, Set.indicator_apply, Set.indicator_apply]
      by_cases ht : t ∈ simplexC 50 ((26 : ℝ) / 25) <;> simp [ht]
    rw [IFuncOrth, hfun, MeasureTheory.integral_indicator hs]
  rw [h1]
  have h2 : ∀ t : Fin 50 → ℝ, (certPoly t) ^ 2
      = ∑ j : Fin 1780, ∑ j' : Fin 1780, certTerm j t * certTerm j' t := by
    intro t
    rw [certPoly_eq, sq, Finset.sum_mul_sum]
  rw [show (∫ t in simplexC 50 ((26 : ℝ) / 25), (certPoly t) ^ 2)
      = ∫ t in simplexC 50 ((26 : ℝ) / 25),
          ∑ j : Fin 1780, ∑ j' : Fin 1780, certTerm j t * certTerm j' t from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h2)]
  have h3 : (∫ t in simplexC 50 ((26 : ℝ) / 25),
        ∑ j : Fin 1780, ∑ j' : Fin 1780, certTerm j t * certTerm j' t)
      = ∑ j : Fin 1780, ∫ t in simplexC 50 ((26 : ℝ) / 25),
          ∑ j' : Fin 1780, certTerm j t * certTerm j' t :=
    MeasureTheory.integral_finsetSum Finset.univ (fun j _ =>
      MeasureTheory.integrable_finsetSum Finset.univ (fun j' _ =>
        ((continuous_certTerm j).mul (continuous_certTerm j')).continuousOn.integrableOn_compact
          (isCompact_simplexC 50 _)))
  rw [h3]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h4 : (∫ t in simplexC 50 ((26 : ℝ) / 25),
        ∑ j' : Fin 1780, certTerm j t * certTerm j' t)
      = ∑ j' : Fin 1780, ∫ t in simplexC 50 ((26 : ℝ) / 25),
          certTerm j t * certTerm j' t :=
    MeasureTheory.integral_finsetSum Finset.univ (fun j' _ =>
      ((continuous_certTerm j).mul (continuous_certTerm j')).continuousOn.integrableOn_compact
        (isCompact_simplexC 50 _))
  rw [h4]
  refine Finset.sum_congr rfl (fun j' _ => ?_)
  have hpt : ∀ t : Fin 50 → ℝ, certTerm j t * certTerm j' t
      = ((certCl j : ℝ) * (certCl j' : ℝ)) *
          (((26 : ℝ) / 25 - ∑ i, t i) ^ (certA j + certA j') *
            lmono (certSig j) 50 t * lmono (certSig j') 50 t) := by
    intro t
    unfold certTerm
    rw [pow_add]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul]
  have hSlab : (∫ a in simplexC 50 ((26 : ℝ) / 25),
        ((26 : ℝ) / 25 - ∑ i, a i) ^ (certA j + certA j') *
          lmono (certSig j) 50 a * lmono (certSig j') 50 a)
      = ((26 : ℝ) / 25) ^ (50 + (certA j + certA j') + (certSig j).sum + (certSig j').sum) *
          ((certA j + certA j').factorial : ℝ) * (Slab (certSig j) (certSig j') 50 : ℝ) /
          (((certA j + certA j' + (certSig j).sum + (certSig j').sum + 50).factorial : ℕ) : ℝ) :=
    simplex_integral_lmono 50 ((26 : ℝ) / 25) hc (certA j + certA j') (certSig j) (certSig j')
  rw [hSlab]
  have hD1 : (50 : ℕ) + (certA j + certA j') + (certSig j).sum + (certSig j').sum
      = 50 + certD j j' := by
    rw [certD]; ring
  have hD2 : ((certA j + certA j') + (certSig j).sum + (certSig j').sum) + 50
      = certD j j' + 50 := by
    rw [certD]; ring
  rw [hD1, hD2, show certA j + certA j' = certAA j j' from by rw [certAA]]

/-! ## Data facts about the certificate basis, and the `Ssum` form -/

theorem certBasis_zero : certBasis.all (fun p => decide (0 ∉ p.2)) = true := by decide

theorem certBasis_sum_le : certBasis.all (fun p => decide (p.2.sum + p.1 ≤ 25)) = true := by decide

theorem certSig_notMem_zero (j : Fin 1780) : 0 ∉ certSig j :=
  of_decide_eq_true (List.all_eq_true.mp certBasis_zero (certBasisAt j) (List.get_mem _ _))

theorem certSig_sum_le (j : Fin 1780) : (certSig j).sum ≤ 50 := by
  have h := of_decide_eq_true (List.all_eq_true.mp certBasis_sum_le (certBasisAt j) (List.get_mem _ _))
  have h' : (certSig j).sum + certA j ≤ 25 := h
  omega

/-- The master expansion with `Slab` replaced by `theta · theta · Ssum` (the form the packed
aggregation consumes). -/
theorem IFuncOrth_certFun_Ssum :
    IFuncOrth 50 certFun
      = ∑ j : Fin 1780, ∑ j' : Fin 1780,
          (certCl j : ℝ) * (certCl j' : ℝ) *
            ((theta (certSig j) : ℝ) * (theta (certSig j') : ℝ)) *
            (((26 : ℝ) / 25) ^ (50 + certD j j') * ((certAA j j').factorial : ℝ) *
              (Ssum (certSig j) (certSig j') 50 : ℝ) /
                (((certD j j' + 50).factorial : ℕ) : ℝ)) := by
  rw [IFuncOrth_certFun]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))
  rw [Slab_eq_theta_mul 50 (certSig j) (certSig j') (certSig_notMem_zero j)
    (certSig_notMem_zero j') (le_trans (certSig_sum_le j) (by norm_num))
    (le_trans (certSig_sum_le j') (by norm_num)) 50]
  push_cast
  ring

/-- The list of labelling factors `θ(α_j)` of the certificate basis. -/
def certTheta : List ℕ := certBasis.map (fun p => theta p.2)

theorem certTheta_length : certTheta.length = 1780 := by
  rw [certTheta, List.length_map, certBasis_length]

/-- **The labelled coefficients are `certK / θ` times the symmetric ones.** -/
theorem certLab_rel_all :
    (certCoefLab.zip (certCoefSym.zip certTheta)).all
      (fun p => decide (p.1 * (p.2.2 : ℤ) = certK * p.2.1)) = true := by
  decide

/-- The `j`-th symmetric coefficient. -/
def certCs (j : Fin 1780) : ℤ :=
  certCoefSym.get ⟨(j : ℕ), by simpa [certCoefSym_length] using j.isLt⟩

theorem certCl_eq_getElem (j : Fin 1780) : certCl j = certCoefLab[(j : ℕ)] := rfl

theorem certCs_eq_getElem (j : Fin 1780) : certCs j = certCoefSym[(j : ℕ)] := rfl

theorem certSig_eq_getElem (j : Fin 1780) : certSig j = (certBasis[(j : ℕ)]).2 := rfl

/-- **The labelled coefficients are `certK / θ` times the symmetric ones**, indexwise. -/
theorem certLab_rel (j : Fin 1780) :
    certCl j * (theta (certSig j) : ℤ) = certK * certCs j := by
  have hj : (j : ℕ) < 1780 := j.isLt
  have hlen : (j : ℕ) < (certCoefLab.zip (certCoefSym.zip certTheta)).length := by
    rw [List.length_zip, certCoefLab_length, List.length_zip, certCoefSym_length, certTheta_length]
    exact hj
  have h := List.all_eq_true.mp certLab_rel_all _ (List.getElem_mem hlen)
  rw [List.getElem_zip, List.getElem_zip] at h
  simp only [certTheta, List.getElem_map] at h
  rw [certCl_eq_getElem, certCs_eq_getElem, certSig_eq_getElem]
  exact of_decide_eq_true h

/-! ## Permutation invariance of `lmono` (needed for `J_i(F) = J_{i'}(F)`) -/

theorem lmono_perm (α : List ℕ) (k : ℕ) (σ : Equiv.Perm (Fin k)) (t : Fin k → ℝ) :
    lmono α k (t ∘ σ) = lmono α k t := by
  unfold lmono
  refine Fintype.sum_equiv (Equiv.embeddingCongr (Equiv.refl (Fin α.length)) σ) _ _ ?_
  intro e
  rfl

/-! ## The monomial symmetric polynomial `m_α` (the profile sum)

This is the object `exact.py` uses: `lmono α k = theta α · m_α`, and `m_α` has the coordinate
decomposition with coefficient `1` that the J-side formula needs. -/

/-- The monomial symmetric polynomial of the exponent signature `α`, written as the sum over the
profiles of `α` (each monomial `t^f` once, with multiplicity one). -/
def mfun (α : List ℕ) (k : ℕ) (t : Fin k → ℝ) : ℝ :=
  ∑ f ∈ (Fintype.piFinset (fun _ : Fin k => Finset.range (α.sum + 1))).filter (IsProfile α),
    ∏ c : Fin k, (t c) ^ (f c)

/-- Sanity check of `mfun`: the empty signature gives the constant monomial `1`.  (The relation
`lmono α k = theta α * mfun α k` needs the `M`-generalised commons `sum_preimage_expOf`; the
commons version available now is `ℕ`-valued.  See the roadmap SESSION 49 §6.) -/
theorem mfun_nil (k : ℕ) (t : Fin k → ℝ) : mfun [] k t = 1 := by
  unfold mfun
  have hset : (Fintype.piFinset (fun _ : Fin k => Finset.range (([] : List ℕ).sum + 1))).filter
      (IsProfile ([] : List ℕ)) = {fun _ : Fin k => 0} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_singleton]
    rw [Fintype.mem_piFinset]
    simp only [List.sum_nil, Nat.reduceAdd, Finset.mem_range]
    constructor
    · rintro ⟨h, -⟩
      funext c
      exact Nat.lt_one_iff.mp (h c)
    · intro h
      subst h
      exact ⟨fun c => Nat.zero_lt_one,
        ⟨fun v hv => absurd hv (by simp), fun c => Or.inl rfl⟩⟩
  rw [hset, Finset.sum_singleton]
  exact Finset.prod_eq_one (fun c _ => pow_zero _)

end

end Commons.NumberTheory.MaynardSieve
