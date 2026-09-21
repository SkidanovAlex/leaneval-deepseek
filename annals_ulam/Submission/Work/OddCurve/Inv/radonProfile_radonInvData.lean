import Mathlib
import Submission.Work.OddCurve.Inv.Defs
import Submission.Work.OddCurve.Inv.abelNu_abelNuInv
import Submission.Work.OddCurve.Inv.abelTrans_negHalf_eq_abelNu
import Submission.Work.OddCurve.Inv.abelTrans_negHalf_radonInvData
import Submission.Work.OddCurve.Inv.eq_of_abelReduceIter_eq_of_eqOn
import Submission.Work.OddRadon.Abel
import Submission.Work.OddRadon.abelTrans_hasDerivAt_direct
import Submission.Work.OddRadon.hasDerivAt_abelTrans
import Submission.Work.OddRadon.AbelInversion
import Submission.Work.OddRadon.abelReduceIter_abelTrans
import Submission.Work.OddRadon.radonProfile_eq_abelTrans
import Submission.Work.OddRadon.sphereArea_pos

/-!
# The explicit Radon inversion of the odd case, on the cap `(0,1)`

`radonProfile_radonInvData`: if `F` agrees with the Radon profile `radonProfile (2n+1) γ₀` of an
even `C¹` profile `γ₀` on a neighbourhood `(0,c₀)` of `0`, and the Abel right inverse
`abelNuInv` inverts the datum (`habel`), then the explicit inverse `radonInvData n F` reproduces
`F` on the whole of `(0,1)`:

`radonProfile (2n+1) (radonInvData n F) = F` on `(0,1)`.

The proof is the one of `PLAN_M2.md` §2, made robust at the two places where the hypotheses are
only available on the *open* interval `(-1,1)` (the library's `abelReduceIter_abelTrans` and
`radonProfile_eq_abelTrans` ask for `C¹` on the closed `[0,1]`, which no honest profile satisfies):

1. `T_{-1/2} γ = abelDatum n F` on `(0,1)` (`abelTrans_negHalf_radonInvData`, from `habel`);
2. on `(0,c₀)`: `K = T_{n-3/2} γ₀` (from `hF` and `radonProfile_eq_abelTrans`), hence
   `abelDatum n F = T_{-1/2} γ₀`, hence (Abel inversion, via a scaling to `[0,1]`)
   `γ = γ₀` on `(0,c₀)`;
3. so `T_{n-3/2} γ = K` on `(0,c₀)`, while on `(0,1)` the two have the same `(n-1)`-fold Abel
   reduction `T_{-1/2} γ = abelDatum n F`; the reduction is injective modulo the polynomials in
   `c²`, and a polynomial vanishing near `0` is zero;
4. `radonProfile (2n+1) γ c = 2|S^{2n-2}| c^{2-2n} T_{n-3/2} γ c = 2|S^{2n-2}| c^{2-2n} K c = F c`.
-/

namespace Work.OddCurve.Inv

open MeasureTheory Set Filter
open scoped Topology Interval

noncomputable section

/-! ## Scaling of the Abel transform (reduces the open-interval statements to closed ones) -/

/-- **Scaling of the Abel transform.**  For `b > 0` and `x > 0`,
`T_α (G ∘ (b·)) x = b^{-(2α+1)} T_α G (b x)`. -/
lemma abelTrans_scale (α : ℝ) {b : ℝ} (hb : 0 < b) (G : ℝ → ℝ) {x : ℝ} (hx : 0 < x) :
    Work.OddRadon.abelTrans α (fun u => G (b * u)) x
      = b ^ (-(2 * α + 1)) * Work.OddRadon.abelTrans α G (b * x) := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  rw [Work.OddRadon.AbelDirect.abelTrans_eq_integral_comp_mul α (fun u => G (b * u)) hx,
    Work.OddRadon.AbelDirect.abelTrans_eq_integral_comp_mul α G (mul_pos hb hx)]
  have hInt : (∫ t in (0:ℝ)..1, G (b * (x * t)) * (1 - t ^ 2) ^ α)
      = ∫ t in (0:ℝ)..1, G ((b * x) * t) * (1 - t ^ 2) ^ α := by
    apply intervalIntegral.integral_congr
    intro t _
    show G (b * (x * t)) * (1 - t ^ 2) ^ α = G ((b * x) * t) * (1 - t ^ 2) ^ α
    rw [show b * (x * t) = (b * x) * t by ring]
  rw [hInt]
  have hpow : b ^ (-(2 * α + 1)) * (b * x) ^ (2 * α + 1) = x ^ (2 * α + 1) := by
    rw [Real.mul_rpow hb.le hx.le, Real.rpow_neg hb.le (2 * α + 1), ← mul_assoc,
      inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hb _)), one_mul]
  rw [← hpow]
  ring

/-! ## The exponent recursion at interior points -/

/-- **The recursion `T_α' = 2 α c T_{α-1}` at an interior point**, with the regularity assumed
only on the open interval `(-1,1)`. -/
theorem deriv_abelTrans_local {α : ℝ} (hα : 0 < α) {G : ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G (Set.Ioo (-1 : ℝ) 1)) {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (Work.OddRadon.abelTrans α G) c = 2 * α * c * Work.OddRadon.abelTrans (α - 1) G c := by
  obtain ⟨b, hcb, hb1⟩ : ∃ b : ℝ, c < b ∧ b < 1 :=
    ⟨(c + 1) / 2, by linarith [hc.1, hc.2], by linarith [hc.1, hc.2]⟩
  have hb : 0 < b := lt_trans hc.1 hcb
  have hb0 : b ≠ 0 := ne_of_gt hb
  -- `G ∘ (b·)` is `C¹` on `[0,1]`
  have hGb : ContDiffOn ℝ 1 (fun u : ℝ => G (b * u)) (Set.Icc (0 : ℝ) 1) := by
    have hmono : ContDiffOn ℝ 1 G (Set.Icc 0 b) :=
      hG.mono (by
        intro y hy
        rw [Set.mem_Icc] at hy
        exact ⟨by linarith [hy.1, hy.2, hb1, hb], by linarith [hy.2, hb1]⟩)
    have hcomp : ContDiffOn ℝ 1 (fun u : ℝ => G (b * u)) (Set.Icc (0:ℝ) 1) :=
      hmono.comp (t := Set.Icc 0 b) (s := Set.Icc (0:ℝ) 1)
        (by fun_prop : ContDiffOn ℝ 1 (fun u : ℝ => b * u) (Set.Icc (0:ℝ) 1))
        (by
          intro u hu
          rw [Set.mem_Icc] at hu
          exact ⟨mul_nonneg hb.le hu.1, by nlinarith [hu.2, hb1, hb.le]⟩)
    exact hcomp
  have hx0 : 0 < c / b := div_pos hc.1 hb
  have hx1 : c / b < 1 := by rw [div_lt_one hb]; exact hcb
  have hd := Work.OddRadon.AbelDirect.hasDerivAt_abelTrans_direct (α := α) hα hGb ⟨hx0, hx1⟩
  -- transfer the scaling
  have hev : (fun y : ℝ => b ^ (-(2 * α + 1)) * Work.OddRadon.abelTrans α G (b * y))
      =ᶠ[𝓝 (c / b)] (Work.OddRadon.abelTrans α fun u => G (b * u)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx0] with y hy
    exact (abelTrans_scale α hb G hy).symm
  have hd1 : HasDerivAt (fun y : ℝ => b ^ (-(2 * α + 1)) * Work.OddRadon.abelTrans α G (b * y))
      (2 * α * (c / b) * Work.OddRadon.abelTrans (α - 1) (fun u => G (b * u)) (c / b))
      (c / b) :=
    hd.congr_of_eventuallyEq hev
  have hd2 : HasDerivAt (fun y : ℝ => Work.OddRadon.abelTrans α G (b * y))
      (b ^ (2 * α + 1) *
        (2 * α * (c / b) * Work.OddRadon.abelTrans (α - 1) (fun u => G (b * u)) (c / b)))
      (c / b) := by
    have h := hd1.const_mul (b ^ (2 * α + 1))
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [← mul_assoc, ← Real.rpow_add hb (2 * α + 1) (-(2 * α + 1)),
      show 2 * α + 1 + -(2 * α + 1) = 0 by ring, Real.rpow_zero, one_mul]
  have hinner : HasDerivAt (fun y : ℝ => y / b) (1 / b) c := by
    simpa using (hasDerivAt_id c).div_const b
  have hd3 : HasDerivAt (fun y : ℝ => Work.OddRadon.abelTrans α G (b * (y / b)))
      ((b ^ (2 * α + 1) *
        (2 * α * (c / b) * Work.OddRadon.abelTrans (α - 1) (fun u => G (b * u)) (c / b)))
        * (1 / b)) c := by
    exact hd2.comp c hinner
  have hfun2 : (fun y : ℝ => Work.OddRadon.abelTrans α G (b * (y / b)))
      = Work.OddRadon.abelTrans α G := by
    funext y
    rw [show b * (y / b) = y by field_simp]
  rw [hfun2] at hd3
  rw [hd3.deriv]
  -- arithmetic
  have hT : Work.OddRadon.abelTrans (α - 1) (fun u => G (b * u)) (c / b)
      = b ^ (-(2 * (α - 1) + 1)) * Work.OddRadon.abelTrans (α - 1) G c := by
    have h := abelTrans_scale (α - 1) hb G hx0
    rw [mul_div_cancel₀ c hb0] at h
    exact h
  rw [hT]
  have hcomb : b ^ (2 * α + 1) * b ^ (-(2 * (α - 1) + 1)) * b ^ (-1:ℝ) = b := by
    rw [← Real.rpow_add hb (2 * α + 1) (-(2 * (α - 1) + 1)),
      show 2 * α + 1 + -(2 * (α - 1) + 1) = 2 by ring, ← Real.rpow_add hb 2 (-1),
      show (2:ℝ) + (-1) = 1 by ring, Real.rpow_one]
  have hcomb' : b ^ (2 * α + 1) * b ^ (-(2 * (α - 1) + 1)) * b⁻¹ = b := by
    rw [← Real.rpow_neg_one b]
    exact hcomb
  calc (b ^ (2 * α + 1) *
        (2 * α * (c / b) * (b ^ (-(2 * (α - 1) + 1)) * Work.OddRadon.abelTrans (α - 1) G c)))
        * (1 / b)
      = (2 * α * (c / b) * Work.OddRadon.abelTrans (α - 1) G c) *
        (b ^ (2 * α + 1) * b ^ (-(2 * (α - 1) + 1)) * b⁻¹) := by ring
    _ = 2 * α * c * Work.OddRadon.abelTrans (α - 1) G c := by
        rw [hcomb']
        field_simp

/-- One exponent-reduction step, on `(0,1)`, with `C¹` only on `(-1,1)`. -/
lemma abelReduce_abelTrans_local {α : ℝ} (hα : 0 < α) {G : ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G (Set.Ioo (-1 : ℝ) 1)) :
    Set.EqOn (Work.OddRadon.abelReduce α (Work.OddRadon.abelTrans α G))
      (Work.OddRadon.abelTrans (α - 1) G) (Set.Ioo (0 : ℝ) 1) := by
  intro c hc
  simp only [Work.OddRadon.abelReduce]
  rw [deriv_abelTrans_local hα hG hc]
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hc0 : c ≠ 0 := ne_of_gt hc.1
  field_simp

/-- **The iterated reduction at the open-interval regularity.** -/
theorem abelReduceIter_abelTrans_local {G : ℝ → ℝ} (hG : ContDiffOn ℝ 1 G (Set.Ioo (-1 : ℝ) 1))
    {k : ℕ} {α : ℝ} (hα : (k : ℝ) - 1 < α) :
    Set.EqOn (Work.OddRadon.abelReduceIter α k (Work.OddRadon.abelTrans α G))
      (Work.OddRadon.abelTrans (α - k) G) (Set.Ioo (0 : ℝ) 1) := by
  induction k generalizing α with
  | zero => intro c hc; simp
  | succ k ih =>
      intro c hc
      rw [Work.OddRadon.abelReduceIter_succ]
      have hk : ((k : ℝ)) < α := by
        have h' : ((k : ℝ) + 1) - 1 < α := by exact_mod_cast hα
        linarith
      have hαk : (k : ℝ) - 1 < α - 1 := by linarith
      have hstep := abelReduce_abelTrans_local (α := α) (by linarith) hG
      have hred : Work.OddRadon.abelReduceIter (α - 1) k
            (Work.OddRadon.abelReduce α (Work.OddRadon.abelTrans α G)) c
          = Work.OddRadon.abelReduceIter (α - 1) k (Work.OddRadon.abelTrans (α - 1) G) c :=
        Work.OddRadon.abelReduceIter_congr hstep (α - 1) k hc
      rw [hred, ih hαk hc]
      have : (α - 1) - (k : ℝ) = α - ((k + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [this]

/-! ## Injectivity of the `(n-1)`-fold reduction on `(0,1)` -/

/-- One step of regularity for the exponent reduction, on the open interval. -/
private lemma contDiffOn_abelReduce_succ_Ioo {α : ℝ} (hα : α ≠ 0) {m : ℕ} {h : ℝ → ℝ}
    (hh : ContDiffOn ℝ (m + 1 : ℕ) h (Set.Ioo (0 : ℝ) 1)) :
    ContDiffOn ℝ (m : ℕ) (Work.OddRadon.abelReduce α h) (Set.Ioo (0 : ℝ) 1) := by
  have hderiv : ContDiffOn ℝ (m : ℕ) (deriv h) (Set.Ioo (0 : ℝ) 1) :=
    hh.deriv_of_isOpen isOpen_Ioo (by simp)
  have h2 : ContDiffOn ℝ (m : ℕ) (fun c : ℝ => (2 * α * c)⁻¹) (Set.Ioo (0 : ℝ) 1) := by
    apply ContDiffOn.inv
    · fun_prop
    · intro c hc
      exact mul_ne_zero (mul_ne_zero (by norm_num) hα) (ne_of_gt hc.1)
  have h : Work.OddRadon.abelReduce α h = fun c : ℝ => deriv h c * (2 * α * c)⁻¹ := by
    funext c; rfl
  rw [h]
  exact hderiv.mul h2

private lemma eqOn_Ioo_of_abelReduceIter_eqOn_aux : ∀ (k : ℕ) (α : ℝ),
    (k = 0 ∨ (k : ℝ) - 1 < α) →
    ∀ {f g : ℝ → ℝ}, ContDiffOn ℝ (k : ℕ) f (Set.Ioo (0 : ℝ) 1) →
      ContDiffOn ℝ (k : ℕ) g (Set.Ioo (0 : ℝ) 1) →
      Set.EqOn (Work.OddRadon.abelReduceIter α k f) (Work.OddRadon.abelReduceIter α k g)
        (Set.Ioo (0 : ℝ) 1) →
      ∀ {c₀ : ℝ}, 0 < c₀ → c₀ ≤ 1 → Set.EqOn f g (Set.Ioo (0 : ℝ) c₀) →
        Set.EqOn f g (Set.Ioo (0 : ℝ) 1) := by
  intro k
  induction k with
  | zero =>
      intro α _ f g _ _ hred c₀ _ _ _
      simpa using hred
  | succ k ih =>
      intro α hα f g hf hg hred c₀ hc₀ hc₀1 hcap
      have hαlt : (k : ℝ) < α := by
        rcases hα with h | h
        · exact absurd h (by simp)
        · push_cast at h; linarith
      have hαne : α ≠ 0 := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      have hf1 : ContDiffOn ℝ (k : ℕ) (Work.OddRadon.abelReduce α f) (Set.Ioo 0 1) :=
        contDiffOn_abelReduce_succ_Ioo hαne hf
      have hg1 : ContDiffOn ℝ (k : ℕ) (Work.OddRadon.abelReduce α g) (Set.Ioo 0 1) :=
        contDiffOn_abelReduce_succ_Ioo hαne hg
      have hred1 : Set.EqOn (Work.OddRadon.abelReduceIter (α - 1) k
            (Work.OddRadon.abelReduce α f))
          (Work.OddRadon.abelReduceIter (α - 1) k (Work.OddRadon.abelReduce α g))
          (Set.Ioo 0 1) := by
        intro c hc
        have hc' := hred hc
        rwa [Work.OddRadon.abelReduceIter_succ, Work.OddRadon.abelReduceIter_succ] at hc'
      have hcap1 : Set.EqOn (Work.OddRadon.abelReduce α f) (Work.OddRadon.abelReduce α g)
          (Set.Ioo 0 c₀) := by
        intro c hc
        simp only [Work.OddRadon.abelReduce]
        congr 1
        exact (hcap.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hc)).deriv_eq
      have hk0 : k = 0 ∨ (k : ℝ) - 1 < α - 1 := by
        rcases eq_or_ne k 0 with hk | hk
        · exact Or.inl hk
        · exact Or.inr (by linarith)
      have hxy : Set.EqOn (Work.OddRadon.abelReduce α f) (Work.OddRadon.abelReduce α g)
          (Set.Ioo 0 1) := ih (α - 1) hk0 hf1 hg1 hred1 hc₀ hc₀1 hcap1
      have hder : Set.EqOn (deriv f) (deriv g) (Set.Ioo 0 1) := by
        intro x hx
        have h := hxy hx
        simp only [Work.OddRadon.abelReduce] at h
        have hb : (2 * α * x) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) hαne) (ne_of_gt hx.1)
        have h2 := congrArg (fun y : ℝ => y * (2 * α * x)) h
        rwa [div_mul_cancel₀ _ hb, div_mul_cancel₀ _ hb] at h2
      have hfd : DifferentiableOn ℝ f (Set.Ioo 0 1) := hf.differentiableOn (by simp)
      have hgd : DifferentiableOn ℝ g (Set.Ioo 0 1) := hg.differentiableOn (by simp)
      have hu : DifferentiableOn ℝ (f - g) (Set.Ioo 0 1) := hfd.sub hgd
      have hu' : Set.EqOn (deriv (f - g)) 0 (Set.Ioo 0 1) := by
        intro x hx
        have h1 : deriv (f - g) x = deriv f x - deriv g x :=
          deriv_sub (hfd.differentiableAt (isOpen_Ioo.mem_nhds hx))
            (hgd.differentiableAt (isOpen_Ioo.mem_nhds hx))
        simp [h1, hder hx]
      intro y hy
      have hm : c₀ / 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      have hcst := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hu hu' hy hm
      have hz : (f - g) y = 0 := by
        rw [hcst, Pi.sub_apply, hcap ⟨by linarith, by linarith⟩, sub_self]
      exact sub_eq_zero.mp hz

/-- **Injectivity of the iterated Abel reduction on `(0,1)`.**

If `f`, `g` are `C^k` on `(0,1)`, their `k`-fold abreductions agree on `(0,1)` (with all exponents
strictly positive: `(k:ℝ) - 1 < α`) and `f = g` on a nondegenerate initial interval
`(0,c₀)`, `c₀ ≤ 1`, then `f = g` on `(0,1)`. -/
theorem eqOn_Ioo_of_abelReduceIter_eqOn {α : ℝ} {k : ℕ} (hα : (k : ℝ) - 1 < α)
    {f g : ℝ → ℝ} (hf : ContDiffOn ℝ k f (Set.Ioo (0 : ℝ) 1))
    (hg : ContDiffOn ℝ k g (Set.Ioo (0 : ℝ) 1))
    (hred : Set.EqOn (Work.OddRadon.abelReduceIter α k f) (Work.OddRadon.abelReduceIter α k g)
      (Set.Ioo (0 : ℝ) 1))
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀1 : c₀ ≤ 1) (hcap : Set.EqOn f g (Set.Ioo (0 : ℝ) c₀)) :
    Set.EqOn f g (Set.Ioo (0 : ℝ) 1) :=
  eqOn_Ioo_of_abelReduceIter_eqOn_aux k α (Or.inr hα) hf hg hred hc₀ hc₀1 hcap

/-! ## Injectivity of `T_{-1/2}` on a cap -/

/-- **Injectivity of the classical Abel transform on a cap.**  If `φ₁`, `φ₂` are `C¹` on
`(-1,1)` and `T_{-1/2} φ₁ = T_{-1/2} φ₂` on `(0,c₀)` with `0 < c₀ ≤ 1`, then `φ₁ = φ₂` there.
(The proof rescales the interval to `[0,1]`, which is the form in which the library's Abel
inversion `abel_inversion_odd` is available.) -/
theorem eqOn_of_abelTrans_negHalf_eqOn {φ₁ φ₂ : ℝ → ℝ}
    (h₁ : ContDiffOn ℝ 1 φ₁ (Set.Ioo (-1 : ℝ) 1)) (h₂ : ContDiffOn ℝ 1 φ₂ (Set.Ioo (-1 : ℝ) 1))
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀1 : c₀ ≤ 1)
    (h : Set.EqOn (Work.OddRadon.abelTrans (-(1 / 2)) φ₁) (Work.OddRadon.abelTrans (-(1 / 2)) φ₂)
      (Set.Ioo (0 : ℝ) c₀)) :
    Set.EqOn φ₁ φ₂ (Set.Ioo (0 : ℝ) c₀) := by
  have hdata : ∀ (Ψ : ℝ → ℝ) (u : ℝ),
      Work.OddRadon.abelInverseData 1 Ψ u = Work.OddRadon.abelInvert Ψ u := by
    intro Ψ u
    unfold Work.OddRadon.abelInverseData
    rw [show (1 - 1 : ℕ) = 0 by omega, Work.OddRadon.abelReduceIter_zero]
  intro w hw
  obtain ⟨b, hwb, hb1⟩ : ∃ b : ℝ, w < b ∧ b < 1 :=
    ⟨(w + 1) / 2, by linarith [hw.1, hw.2, hc₀1], by linarith [hw.1, hw.2, hc₀1]⟩
  have hb : 0 < b := lt_trans hw.1 hwb
  have hb0 : b ≠ 0 := ne_of_gt hb
  have rescale : ∀ {e : ℝ → ℝ}, ContDiffOn ℝ 1 e (Set.Ioo (-1 : ℝ) 1) →
      ContDiffOn ℝ 1 (fun u : ℝ => e (b * u)) (Set.Icc (0 : ℝ) 1) := by
    intro e he
    have hmono : ContDiffOn ℝ 1 e (Set.Icc 0 b) :=
      he.mono (by
        intro y hy
        rw [Set.mem_Icc] at hy
        exact ⟨by linarith [hy.1, hy.2, hb1, hb], by linarith [hy.2, hb1]⟩)
    exact hmono.comp (t := Set.Icc 0 b) (s := Set.Icc (0 : ℝ) 1)
      (by fun_prop : ContDiffOn ℝ 1 (fun u : ℝ => b * u) (Set.Icc (0 : ℝ) 1))
      (by
        intro u hu
        rw [Set.mem_Icc] at hu
        exact ⟨mul_nonneg hb.le hu.1, by nlinarith [hu.2, hb1, hb.le]⟩)
  have hu : w / b ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨div_pos hw.1 hb, by rw [div_lt_one hb]; exact hwb⟩
  have hinv₁ := Work.OddRadon.abel_inversion_odd (n := 1) (by norm_num) (rescale h₁) hu
  have hinv₂ := Work.OddRadon.abel_inversion_odd (n := 1) (by norm_num) (rescale h₂) hu
  have hα1 : (((1 : ℕ)) : ℝ) - 3 / 2 = -(1 / 2) := by norm_num
  rw [hα1] at hinv₁ hinv₂
  rw [hdata] at hinv₁ hinv₂
  have hL : φ₁ (b * (w / b)) = φ₁ w := by rw [mul_div_cancel₀ w hb0]
  have hL₂ : φ₂ (b * (w / b)) = φ₂ w := by rw [mul_div_cancel₀ w hb0]
  rw [hL] at hinv₁
  rw [hL₂] at hinv₂
  rw [hinv₁, hinv₂]
  apply Work.OddRadon.abelInvert_congr_of_eqOn hu.1
    (by rw [div_lt_div_iff_of_pos_right hb]; exact hw.2)
  intro x hx
  rw [Set.mem_Ioo] at hx
  have hs₁ := abelTrans_scale (-(1 / 2)) hb φ₁ hx.1
  have hs₂ := abelTrans_scale (-(1 / 2)) hb φ₂ hx.1
  rw [hs₁, hs₂]
  have hexp : (2 * (-(1 / 2) : ℝ) + 1) = 0 := by norm_num
  simp only [hexp, neg_zero, Real.rpow_zero, one_mul]
  apply h
  refine ⟨?_, ?_⟩
  · exact mul_pos hb hx.1
  · rw [← mul_div_cancel₀ c₀ hb0]
    exact mul_lt_mul_of_pos_left hx.2 hb

/-! ## The profile identity without a continuity hypothesis on the closed interval -/

/-- `radonProfile_eq_abelTrans` with the continuity hypothesis dropped (it is unused in the
library's proof): for an even profile it is the Abel transform up to an explicit factor. -/
theorem radonProfile_eq_abelTrans_of_even (n : ℕ) (hn : 1 ≤ n) {γ : ℝ → ℝ}
    (heven : ∀ t, γ (-t) = γ t) {c : ℝ} (hc : 0 < c) :
    Work.OddRadon.radonProfile (2 * n + 1) γ c
      = 2 * Work.OddRadon.sphereArea (2 * n - 2) * (c ^ (2 * n - 2))⁻¹
          * Work.OddRadon.abelTrans ((n : ℝ) - 3 / 2) γ c := by
  set α : ℝ := (n : ℝ) - 3 / 2 with hαdef
  have hcast : ((2 * n + 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 1 := by push_cast; ring
  have hexp : ((2 * n + 1 : ℕ) : ℝ) / 2 - 2 = α := by rw [hαdef, hcast]; ring
  have hsub : 2 * n + 1 - 3 = 2 * n - 2 := by omega
  have hnat : ((2 * n - 2 : ℕ) : ℝ) = 2 * (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * n)]; push_cast; ring
  have h2a : 2 * α + 1 = ((2 * n - 2 : ℕ) : ℝ) := by rw [hαdef, hnat]; ring
  have hpow : c ^ (-(2 * α + 1)) = (c ^ (2 * n - 2))⁻¹ := by
    rw [Real.rpow_neg hc.le, h2a, Real.rpow_natCast]
  have habel : (∫ u in (0 : ℝ)..c, (c ^ 2 - u ^ 2) ^ α * γ u)
      = Work.OddRadon.abelTrans α γ c := by
    rw [Work.OddRadon.abelTrans]
    exact intervalIntegral.integral_congr fun x _ => by ring
  simp only [Work.OddRadon.radonProfile, hsub, hexp]
  rw [Work.OddRadon.integral_neg_one_one_eq (G := γ) (α := α) hc]
  rw [Work.OddRadon.integral_even_neg_eq_two_mul (f := fun u => (c ^ 2 - u ^ 2) ^ α * γ u) ?_ hc]
  · rw [habel, hpow]
    ring
  · intro t
    rw [neg_sq, heven t]

/-! ## The main theorem -/

theorem radonProfile_radonInvData (n : ℕ) (hn : 1 ≤ n) {F γ₀ : ℝ → ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀1 : c₀ ≤ 1) (hF : ∀ c ∈ Set.Ioo (0:ℝ) c₀, F c = Work.OddRadon.radonProfile (2 * n + 1) γ₀ c) (hγ₀ : ContDiffOn ℝ 1 γ₀ (Set.Icc (-1:ℝ) 1)) (hγ₀e : ∀ t, γ₀ (-t) = γ₀ t) (hK : ContDiffOn ℝ (n : ℕ) (fun c : ℝ => (2 * Work.OddRadon.sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * F c) (Set.Ioi (0:ℝ))) (habel : ∀ ν ∈ Set.Ioo (0:ℝ) 1, Work.OddCurve.Inv.abelNu (Work.OddCurve.Inv.abelNuInv (Work.OddCurve.Inv.abelDatumNu n F)) ν = Work.OddCurve.Inv.abelDatumNu n F ν) (hγsm : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Work.OddCurve.Inv.radonInvData n F) (Set.Ioo (-1:ℝ) 1)) (hfsm : ContDiffOn ℝ (n : ℕ) (fun c : ℝ => Work.OddRadon.abelTrans ((n : ℝ) - 3 / 2) (Work.OddCurve.Inv.radonInvData n F) c) (Set.Ioi (0:ℝ))) : ∀ c ∈ Set.Ioo (0:ℝ) 1, Work.OddRadon.radonProfile (2 * n + 1) (Work.OddCurve.Inv.radonInvData n F) c = F c := by
  intro c hc
  set α : ℝ := (n : ℝ) - 3 / 2 with hαdef
  set γ : ℝ → ℝ := Work.OddCurve.Inv.radonInvData n F with hγdef
  set K : ℝ → ℝ := fun x : ℝ => (2 * Work.OddRadon.sphereArea (2 * n - 2))⁻¹ * x ^ (2 * n - 2) * F x
    with hKdef
  have hγeven : ∀ u, γ (-u) = γ u := by
    intro u
    rw [hγdef]
    simp
  -- (1) `T_{-1/2} γ = abelDatum n F` on `(0,1)`
  have hstep1 : Set.EqOn (Work.OddRadon.abelTrans (-(1 / 2)) γ) (abelDatum n F)
      (Set.Ioo (0 : ℝ) 1) := by
    intro x hx
    rw [hγdef]
    exact abelTrans_negHalf_radonInvData n hn habel x hx
  -- (2a) `K = T_α γ₀` on `(0,c₀)`
  have hKabel : Set.EqOn K (Work.OddRadon.abelTrans α γ₀) (Set.Ioo (0 : ℝ) c₀) := by
    intro x hx
    have hx1 := hF x hx
    have hx2 := Work.OddRadon.radonProfile_eq_abelTrans n hn hγ₀.continuousOn hγ₀e hx.1
    have hS : Work.OddRadon.sphereArea (2 * n - 2) ≠ 0 :=
      ne_of_gt (Work.OddRadon.sphereArea_pos (2 * n - 2))
    have hxpow : x ^ (2 * n - 2) ≠ 0 := pow_ne_zero _ (ne_of_gt hx.1)
    simp only [hKdef, hαdef]
    rw [hx1, hx2]
    field_simp
  -- (2b) `abelDatum n F = T_{-1/2} γ₀` on `(0,c₀)`
  have hγ₀' : ContDiffOn ℝ 1 γ₀ (Set.Icc 0 1) :=
    hγ₀.mono (by intro x hx; exact ⟨by linarith [hx.1], hx.2⟩)
  have hcast' : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; norm_num
  have hαcond : (((n - 1 : ℕ)) : ℝ) - 1 < α := by
    rw [hαdef, hcast']; linarith
  have hexp' : α - (((n - 1 : ℕ)) : ℝ) = -(1 / 2) := by
    rw [hαdef, hcast']; ring
  have hredγ₀ : Set.EqOn (Work.OddRadon.abelReduceIter α (n - 1)
        (Work.OddRadon.abelTrans α γ₀)) (Work.OddRadon.abelTrans (-(1 / 2)) γ₀)
      (Set.Ioo (0 : ℝ) 1) := by
    have h := Work.OddRadon.abelReduceIter_abelTrans (G := γ₀) hγ₀' (k := n - 1)
      (α := (n : ℝ) - 3 / 2) (by rw [← hαdef]; exact hαcond)
    have hexp2 : ((n : ℝ) - 3 / 2) - (((n - 1 : ℕ)) : ℝ) = -(1 / 2) := by
      rw [hcast']; ring
    intro x hx
    have hx' := h hx
    rw [hexp2] at hx'
    simpa only [hαdef] using hx'
  have hDabel : Set.EqOn (abelDatum n F) (Work.OddRadon.abelTrans (-(1 / 2)) γ₀)
      (Set.Ioo (0 : ℝ) c₀) := by
    intro x hx
    have hx1 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_lt_of_le hx.2 hc₀1⟩
    have hcongr : ∀ y ∈ Set.Ioo (0 : ℝ) c₀, Work.OddRadon.abelReduceIter α (n - 1) K y
        = Work.OddRadon.abelReduceIter α (n - 1) (Work.OddRadon.abelTrans α γ₀) y :=
      fun y hy => (Work.OddRadon.abelReduceIter_congr_open (s := Set.Ioo (0 : ℝ) c₀)
        isOpen_Ioo (n - 1) α hKabel) hy
    have hdef : abelDatum n F x = Work.OddRadon.abelReduceIter α (n - 1) K x := by
      simp only [abelDatum, hαdef, hKdef]
    rw [hdef]
    exact (hcongr x hx).trans (hredγ₀ hx1)
  -- (3) `γ = γ₀` on `(0,c₀)`
  have hγsm1 : ContDiffOn ℝ 1 γ (Set.Ioo (-1 : ℝ) 1) := by
    rw [hγdef]
    exact hγsm.of_le (by exact_mod_cast hn)
  have hγ₀sm : ContDiffOn ℝ 1 γ₀ (Set.Ioo (-1 : ℝ) 1) :=
    hγ₀.mono (by intro x hx; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hγγ₀ : Set.EqOn γ γ₀ (Set.Ioo (0 : ℝ) c₀) :=
    eqOn_of_abelTrans_negHalf_eqOn hγsm1 hγ₀sm hc₀ hc₀1 (by
      intro x hx
      have hx1 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_lt_of_le hx.2 hc₀1⟩
      rw [hstep1 hx1, hDabel hx])
  -- (4) `T_α γ = K` on `(0,c₀)`
  have hTαK : Set.EqOn (Work.OddRadon.abelTrans α γ) K (Set.Ioo (0 : ℝ) c₀) := by
    intro x hx
    have hcongr : (∫ u in (0 : ℝ)..x, γ u * (x ^ 2 - u ^ 2) ^ α)
        = ∫ u in (0 : ℝ)..x, γ₀ u * (x ^ 2 - u ^ 2) ^ α := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with u hu
      rw [Set.uIoc_of_le hx.1.le] at hu
      rw [hγγ₀ ⟨hu.1, lt_of_le_of_lt hu.2 hx.2⟩]
    rw [hKabel hx]
    rw [Work.OddRadon.abelTrans, Work.OddRadon.abelTrans]
    exact hcongr
  -- (5) the reduced iterates agree on `(0,1)`
  have hred : Set.EqOn (Work.OddRadon.abelReduceIter α (n - 1)
        (Work.OddRadon.abelTrans α γ)) (Work.OddRadon.abelReduceIter α (n - 1) K)
      (Set.Ioo (0 : ℝ) 1) := by
    have h1 := abelReduceIter_abelTrans_local (G := γ) hγsm1 (k := n - 1) (α := α) hαcond
    rw [hexp'] at h1
    intro x hx
    have hdef : abelDatum n F x = Work.OddRadon.abelReduceIter α (n - 1) K x := by
      simp only [abelDatum, hαdef, hKdef]
    rw [h1 hx, hstep1 hx, hdef]
  -- (6) injectivity of the reduction on `(0,1)`
  have hfsm' : ContDiffOn ℝ (((n : ℕ)) : WithTop ℕ∞) (fun x : ℝ => Work.OddRadon.abelTrans α γ x)
      (Set.Ioi (0 : ℝ)) := by
    rw [hαdef, hγdef]
    exact hfsm
  have hKsm : ContDiffOn ℝ (((n : ℕ)) : WithTop ℕ∞) K (Set.Ioi (0 : ℝ)) := by
    rw [hKdef]
    exact hK
  have hf : ContDiffOn ℝ (((n - 1 : ℕ)) : WithTop ℕ∞)
      (fun x : ℝ => Work.OddRadon.abelTrans α γ x) (Set.Ioo (0 : ℝ) 1) :=
    (hfsm'.of_le (by exact_mod_cast Nat.sub_le n 1)).mono (by intro x hx; exact hx.1)
  have hg : ContDiffOn ℝ (((n - 1 : ℕ)) : WithTop ℕ∞) K (Set.Ioo (0 : ℝ) 1) :=
    (hKsm.of_le (by exact_mod_cast Nat.sub_le n 1)).mono (by intro x hx; exact hx.1)
  have hTK : Set.EqOn (Work.OddRadon.abelTrans α γ) K (Set.Ioo (0 : ℝ) 1) :=
    eqOn_Ioo_of_abelReduceIter_eqOn hαcond hf hg hred hc₀ hc₀1 hTαK
  -- (7) conclude
  have hTKc : Work.OddRadon.abelTrans ((n : ℝ) - 3 / 2) γ c = K c := by
    rw [← hαdef]
    exact hTK hc
  rw [radonProfile_eq_abelTrans_of_even n hn hγeven hc.1, hTKc, hKdef]
  have hS : (2 * Work.OddRadon.sphereArea (2 * n - 2)) ≠ 0 := by
    have hpos := Work.OddRadon.sphereArea_pos (2 * n - 2)
    positivity
  have hxpow : c ^ (2 * n - 2) ≠ 0 := pow_ne_zero _ (ne_of_gt hc.1)
  have hS' : Work.OddRadon.sphereArea (2 * n - 2) ≠ 0 :=
    ne_of_gt (Work.OddRadon.sphereArea_pos (2 * n - 2))
  field_simp

end

end Work.OddCurve.Inv
