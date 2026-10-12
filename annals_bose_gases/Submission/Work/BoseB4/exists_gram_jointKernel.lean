import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB4.BoxGram
import Submission.Work.BoseB4.realIP_thetaExp_qVec
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.exists_gram_jointKernel` — the χ-modes and the θ-modes in one coordinate system

Node `B4`'s box side has two families of one-particle vectors in `L²(Λ)`:

* the localised plane waves with the condensate removed, `qVec ℓ k = Q(e^{ikx}χ_Λ)`,
  whose Gram matrix is FS `eq:Commutator_general`'s kernel
  `ℓ³·boxKernel ℓ k k' = ℓ³·ccrKernel ℓ χ̂² χ̂ k k'`
  (`Work.BoseB4.realIP_qVec_qVec`, `Work.BoseB4.BoxGram`);
* the θ-modes `thetaExp ℓ s = e^{isx}θ`, which for lattice momenta `s ≠ 0` are
  orthogonal to each other and to the condensate `θ`, with
  `‖e^{isx}θ‖² = ℓ³` (`horth`, `horthC` of the statement).

The `TildeData` instance of node `B7A` needs **both** families in a *single*
coordinate space: the χ-modes with their commutator kernel, the θ-modes
orthonormal, and the cross Gram products the FS cross kernel
`[ã_s, a_k†] = χ̂((k−s)ℓ)` — in unnormalised form
`realIP (thetaExp ℓ s) (qVec ℓ k) = ℓ³ χ̂(ℓ(k−s))`
(`Work.BoseB4.BoxData.realIP_thetaExp_qVec`, using only `horthC`, i.e. the lattice
orthogonality of the θ-mode with the condensate).

This module proves that such a joint coordinate model exists.  The construction is
the honest one: on the index set `Mode ⊕ Mode` take the vectors
`V (inl k) = qVec ℓ (kmom k)`, `V (inr s) = thetaExp ℓ (kmom s)`; the joint kernel
`K p q = realIP (V p) (V q)` is symmetric (`realIP_comm`) and positive
semidefinite (`realIP_sum_sum_nonneg`, whose pairwise-integrability hypothesis is
supplied by the two new `BoxData` lemmas below plus the two already in the
corpus), so `Work.BoseB4.Exists_gram_iff` produces coordinates
`u : Mode ⊕ Mode → Fin m → ℝ` with `gram (u p) (u q) = K p q`.  Rescaling each
coordinate by `c = (ℓ³)^{-1/2}` turns the unnormalised inner products into the
normalised kernels (`c²·ℓ³ = 1`), and the three blocks give the three claimed
identities.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary facts about `realIP` -/

/-- `Re(conj z · w) = Re(conj w · z)`: the integrand of `realIP` is symmetric. -/
lemma re_conj_mul_comm (z w : ℂ) :
    ((starRingEnd ℂ) z * w).re = ((starRingEnd ℂ) w * z).re := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The real inner product of `Work.BoseB4.BoxChi` is symmetric, with no
integrability hypothesis: the two integrands are *the same function*. -/
lemma realIP_comm (B : BoxData) (f g : ℝ³ → ℂ) : B.realIP f g = B.realIP g f := by
  rw [BoxData.realIP_apply, BoxData.realIP_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => re_conj_mul_comm _ _)

namespace BoxData

variable (B : BoxData)

/-! ## Integrability of the θ/χ integrands

`realIP_sum_sum_nonneg` needs the pairwise integrands of a family of vectors; for
the joint family `{qVec, thetaExp}` the missing two cases are supplied here
(`conj θ · θ` and `conj θ · qVec`; the reversed orders follow by
`re_conj_mul_comm`).  Both integrands are explicit compactly supported
trigonometric functions, exactly as in `Work.BoseB4.BoxKernel`. -/

/-- The integrand of `realIP (thetaExp ℓ s) (thetaExp ℓ t)`: the box indicator
times `cos⟪t−s,x⟫` (each θ-mode is `e^{i·x}θ` with `θ` a `0/1`-valued function). -/
lemma conj_thetaExp_mul_thetaExp_re (ℓ : ℝ) (s t : ℝ³) (x : ℝ³) :
    ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.thetaExp ℓ t x).re
      = (B.boxL ℓ).indicator (fun x : ℝ³ => Real.cos (inner ℝ (t - s) x)) x := by
  by_cases hx : x ∈ B.boxL ℓ
  · rw [Set.indicator_of_mem hx]
    simp only [Work.BoseB4.BoxData.thetaExp_apply, Work.BoseB4.BoxData.thetaFun_apply, hx, if_true,
      mul_one]
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    have hsre : (Complex.exp (Complex.I * ((inner ℝ s x : ℝ) : ℂ))).re
        = Real.cos (inner ℝ s x) := by
      rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_re]
    have hsim : (Complex.exp (Complex.I * ((inner ℝ s x : ℝ) : ℂ))).im
        = Real.sin (inner ℝ s x) := by
      rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_im]
    have htre : (Complex.exp (Complex.I * ((inner ℝ t x : ℝ) : ℂ))).re
        = Real.cos (inner ℝ t x) := by
      rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_re]
    have htim : (Complex.exp (Complex.I * ((inner ℝ t x : ℝ) : ℂ))).im
        = Real.sin (inner ℝ t x) := by
      rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_im]
    rw [hsre, hsim, htre, htim, inner_sub_left, Real.cos_sub]
    ring
  · rw [Set.indicator_of_notMem hx]
    simp only [Work.BoseB4.BoxData.thetaExp_apply, Work.BoseB4.BoxData.thetaFun_apply, hx, if_false,
      mul_zero, map_zero, Complex.zero_re]

/-- The θ-mode/θ-mode integrand is integrable. -/
lemma integrable_conj_thetaExp_thetaExp {ℓ : ℝ} (s t : ℝ³) :
    Integrable fun x : ℝ³ =>
      ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.thetaExp ℓ t x).re :=
  (B.integrable_indicator_cos ℓ (t - s)).congr
    (Filter.Eventually.of_forall fun x => (B.conj_thetaExp_mul_thetaExp_re ℓ s t x).symm)

/-- The θ-mode/χ-mode integrand is integrable: `qVec ℓ k = modeVec ℓ k − χ̂(kℓ)·θ`
splits into the two pieces already handled by
`Work.BoseB4.realIP_thetaExp_qVec`. -/
lemma integrable_conj_thetaExp_qVec {ℓ : ℝ} (hℓ : 0 < ℓ) (s k : ℝ³) :
    Integrable fun x : ℝ³ => ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.qVec ℓ k x).re := by
  have hint1 : Integrable fun x : ℝ³ =>
      ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.modeVec ℓ k x).re :=
    (B.integrable_chiLam_mul_cos hℓ (k - s)).congr
      (Filter.Eventually.of_forall fun x => (B.conj_thetaExp_mul_modeVec_re hℓ s k x).symm)
  have hint2 : Integrable fun x : ℝ³ =>
      ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.thetaFun ℓ x).re :=
    B.integrable_conj_thetaExp_thetaFun ℓ s
  have hfun : (fun x : ℝ³ => ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.qVec ℓ k x).re)
      = fun x : ℝ³ => ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.modeVec ℓ k x).re
          - B.hatChi (ℓ • k) * ((starRingEnd ℂ) (B.thetaExp ℓ s x) * B.thetaFun ℓ x).re := by
    funext x
    rw [BoxData.qVec_apply, BoxData.conj_mul_sub_re]
  rw [hfun]
  exact hint1.sub (hint2.const_mul _)

/-- The reversed θ-mode/χ-mode integrand is integrable (same function as
`integrable_conj_thetaExp_qVec` up to `re_conj_mul_comm`). -/
lemma integrable_conj_qVec_thetaExp {ℓ : ℝ} (hℓ : 0 < ℓ) (k s : ℝ³) :
    Integrable fun x : ℝ³ => ((starRingEnd ℂ) (B.qVec ℓ k x) * B.thetaExp ℓ s x).re :=
  (B.integrable_conj_thetaExp_qVec hℓ s k).congr
    (Filter.Eventually.of_forall fun _ => re_conj_mul_comm _ _)

end BoxData

/-! ## The coordinate Gram product under rescaling -/

lemma gram_smul_smul {m : ℕ} (c d : ℝ) (a b : Fin m → ℝ) :
    gram (c • a) (d • b) = c * d * gram a b := by
  simp only [gram, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-! ## The joint Gram model -/

theorem exists_gram_jointKernel (B : Work.BoseB4.BoxData) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (kmom : Mode → EuclideanSpace ℝ (Fin 3))
    (had : ∀ i j : Mode, kmom (i - j) = kmom i - kmom j)
    (horth : ∀ s t : Mode, s ≠ 0 → t ≠ 0 →
      B.realIP (B.thetaExp ℓ (kmom s)) (B.thetaExp ℓ (kmom t)) = if s = t then ℓ ^ 3 else 0)
    (horthC : ∀ s : Mode, s ≠ 0 →
      B.realIP (B.thetaExp ℓ (kmom s)) (B.thetaFun ℓ) = 0) :
    ∃ m : ℕ, ∃ f g : Mode → Fin m → ℝ,
      (∀ i j : Mode, Work.BoseB4.gram (f i) (f j)
        = Work.BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))
      ∧ (∀ s t : Mode, s ≠ 0 → t ≠ 0 →
          Work.BoseB4.gram (g s) (g t) = if s = t then 1 else 0)
      ∧ (∀ s k : Mode, s ≠ 0 →
          Work.BoseB4.gram (g s) (f k) = B.hatChi (ℓ • (kmom k - kmom s))) := by
  classical
  -- `had` records the additivity of the lattice momenta; the construction below
  -- only needs its immediate consequence `kmom 0 = 0`.
  have _hzero : kmom 0 = 0 := by simpa using had 0 0
  -- the joint two-block family: χ-modes on `inl`, θ-modes on `inr`
  let V : Mode ⊕ Mode → ℝ³ → ℂ :=
    Sum.elim (fun k => B.qVec ℓ (kmom k)) (fun s => B.thetaExp ℓ (kmom s))
  have hSym : ∀ p q : Mode ⊕ Mode, B.realIP (V p) (V q) = B.realIP (V q) (V p) :=
    fun p q => realIP_comm B _ _
  have hInt : ∀ p q : Mode ⊕ Mode,
      Integrable fun x => ((starRingEnd ℂ) (V p x) * V q x).re := by
    rintro (i | i) (j | j)
    · exact B.integrable_conj_qVec_qVec hℓ (kmom i) (kmom j)
    · exact B.integrable_conj_qVec_thetaExp hℓ (kmom i) (kmom j)
    · exact B.integrable_conj_thetaExp_qVec hℓ (kmom i) (kmom j)
    · exact B.integrable_conj_thetaExp_thetaExp (kmom i) (kmom j)
  -- the joint kernel is positive semidefinite: it is the Gram kernel of `V`
  have hPSD : ∀ v : Mode ⊕ Mode → ℝ,
      0 ≤ ∑ i, ∑ j, v i * B.realIP (V i) (V j) * v j := by
    intro v
    have h := realIP_sum_sum_nonneg B V v hInt
    have heq : (∑ p, ∑ q, v p * v q * B.realIP (V p) (V q))
        = ∑ p, ∑ q, v p * B.realIP (V p) (V q) * v q := by
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
    rw [heq] at h
    exact h
  obtain ⟨m, u, hu⟩ :=
    (Exists_gram_iff (fun p q : Mode ⊕ Mode => B.realIP (V p) (V q))).mpr ⟨hSym, hPSD⟩
  -- the normalisation `c = (ℓ³)^{-1/2}`, so that `c²·ℓ³ = 1`
  set c : ℝ := Real.sqrt ((ℓ ^ 3)⁻¹) with hcdef
  have hc3 : c * c * ℓ ^ 3 = 1 := by
    have hsq : c * c = (ℓ ^ 3)⁻¹ := by
      rw [show c * c = c ^ 2 by ring, hcdef, Real.sq_sqrt (by positivity)]
    rw [hsq, inv_mul_cancel₀ (by positivity : ℓ ^ 3 ≠ 0)]
  have hcancel : ∀ Y : ℝ, c * c * (ℓ ^ 3 * Y) = Y := by
    intro Y
    rw [show c * c * (ℓ ^ 3 * Y) = (c * c * ℓ ^ 3) * Y by ring, hc3, one_mul]
  refine ⟨m, fun k => c • u (Sum.inl k), fun s => c • u (Sum.inr s), ?_, ?_, ?_⟩
  · -- the χ-block: FS `eq:Commutator_general`
    intro i j
    have h1 : B.realIP (V (Sum.inl i)) (V (Sum.inl j))
        = ℓ ^ 3 * B.boxKernel ℓ (kmom i) (kmom j) := by
      simpa only [V, Sum.elim_inl] using realIP_qVec_qVec B hℓ (kmom i) (kmom j)
    rw [gram_smul_smul, hu (Sum.inl i) (Sum.inl j), h1]
    simp only [BoxData.boxKernel, BoseB7.ccrKernel]
    exact hcancel _
  · -- the θ-block: orthonormal for the non-zero lattice momenta
    intro s t hs ht
    have h1 : B.realIP (V (Sum.inr s)) (V (Sum.inr t)) = if s = t then ℓ ^ 3 else 0 := by
      simpa only [V, Sum.elim_inr] using horth s t hs ht
    rw [gram_smul_smul, hu (Sum.inr s) (Sum.inr t), h1]
    by_cases h : s = t
    · rw [if_pos h, if_pos h]
      exact hc3
    · rw [if_neg h, if_neg h, mul_zero]
  · -- the cross block: the FS cross kernel `χ̂(ℓ(k−s))`
    intro s k hs
    have h1 : B.realIP (V (Sum.inr s)) (V (Sum.inl k))
        = ℓ ^ 3 * B.hatChi (ℓ • (kmom k - kmom s)) := by
      simpa only [V, Sum.elim_inr, Sum.elim_inl] using
        BoxData.realIP_thetaExp_qVec B hℓ (kmom s) (kmom k) (horthC s hs)
    rw [gram_smul_smul, hu (Sum.inr s) (Sum.inl k), h1]
    exact hcancel _

end Work.BoseB4
