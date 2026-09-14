import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Submission.Commons.Analysis.Calculus.exists_primitive_tsupport_subset

namespace Commons.Analysis.Calculus

open MeasureTheory Set Filter Function
open scoped Topology

/-- If `f` is locally integrable on a set `U`, and `g` is a continuous function with compact
support contained in `U`, then `g • f` is integrable. -/
theorem integrable_smul_of_locallyIntegrableOn_of_tsupport_subset {f g : ℝ → ℝ} {U : Set ℝ}
    (hf : LocallyIntegrableOn f U volume) (hg : Continuous g) (h'g : HasCompactSupport g)
    (hU : tsupport g ⊆ U) :
    Integrable (fun x => g x • f x) volume := by
  let K := tsupport g
  have hK : IsCompact K := h'g
  have hfK : IntegrableOn f K volume := hf.integrableOn_compact_subset hU hK
  have hind : K.indicator (fun x => g x • f x) = (fun x => g x • f x) := by
    apply indicator_eq_self.2
    apply Function.support_subset_iff'.2
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← hind, indicator_smul]
  have hfK_ind : Integrable (K.indicator f) volume := by
    rw [integrable_indicator_iff hK.measurableSet]; exact hfK
  have hgLp : MemLp g ⊤ volume := hg.memLp_top_of_hasCompactSupport h'g volume
  exact Integrable.smul_of_top_right hfK_ind hgLp

/-- A smooth bump function supported inside an open interval `(a,b)`. -/
noncomputable def intervalBump (a b : ℝ) (hab : a < b) : ContDiffBump ((a + b) / 2 : ℝ) :=
  ⟨(b - a) / 6, (b - a) / 3, by linarith, by linarith⟩

theorem intervalBump_tsupport_subset {a b : ℝ} (hab : a < b) :
    tsupport (intervalBump a b hab : ℝ → ℝ) ⊆ Set.Ioo a b := by
  intro x hx
  have h1 : x ∈ Metric.closedBall ((a + b) / 2 : ℝ) (intervalBump a b hab).rOut := by
    rw [← (intervalBump a b hab).tsupport_eq]; exact hx
  rw [Metric.mem_closedBall, Real.dist_eq] at h1
  have h2 := abs_le.mp h1
  constructor <;> simp only [intervalBump] at h2 <;> linarith [h2.1, h2.2]

/-- **du Bois-Reymond lemma** (scalar version).  A locally integrable function on an open interval
whose integrals against the derivatives of all smooth compactly supported test functions (with
support inside the interval) vanish is almost everywhere constant there. -/
theorem duBoisReymond_scalar {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : MeasureTheory.LocallyIntegrableOn f (Set.Ioo a b) MeasureTheory.volume)
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Set.Ioo a b →
      MeasureTheory.integral MeasureTheory.volume (fun t => deriv ψ t * f t) = 0) :
    ∃ c : ℝ, Filter.Eventually (fun t => t ∈ Set.Ioo a b → f t = c)
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  set θ : ℝ → ℝ := (intervalBump a b hab : ℝ → ℝ) with hθ
  have hθcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ := by
    rw [hθ]; exact (intervalBump a b hab).contDiff
  have hθcs : HasCompactSupport θ := by
    rw [hθ]; exact (intervalBump a b hab).hasCompactSupport
  have hθts : tsupport θ ⊆ Set.Ioo a b := by
    rw [hθ]; exact intervalBump_tsupport_subset hab
  have hθpos : 0 < ∫ x, θ x := by
    rw [hθ]; exact (intervalBump a b hab).integral_pos (μ := volume)
  have hθf_int : Integrable (fun x => θ x • f x) volume :=
    integrable_smul_of_locallyIntegrableOn_of_tsupport_subset hf hθcd.continuous hθcs hθts
  set J : ℝ := ∫ x, θ x with hJ
  set L : ℝ := ∫ x, θ x • f x with hL
  have hJne : J ≠ 0 := by rw [hJ]; exact ne_of_gt hθpos
  have hkey : ∀ g : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ Set.Ioo a b → ∫ x, g x • (f x - L / J) = 0 := by
    intro g hgcd hgcs hgts
    set Jg : ℝ := ∫ x, g x with hJg
    set k : ℝ := Jg / J with hk
    set φ : ℝ → ℝ := g - k • θ with hφ
    have hg_int : Integrable g volume :=
      hgcd.continuous.integrable_of_hasCompactSupport hgcs
    have hkθ_cs : HasCompactSupport (k • θ) := hθcs.smul_left (f := fun _ : ℝ => k)
    have hkθ_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (k • θ) :=
      hθcd.const_smul k
    have hkθ_ts : tsupport (k • θ) ⊆ Set.Ioo a b :=
      (tsupport_smul_subset_right (fun _ : ℝ => k) θ).trans hθts
    have hφcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := by
      rw [hφ]; exact hgcd.sub hkθ_cd
    have hφcs : HasCompactSupport φ := by
      rw [hφ]; exact hgcs.sub hkθ_cs
    have hφts : tsupport φ ⊆ Set.Ioo a b := by
      rw [hφ]
      refine (tsupport_sub g (k • θ)).trans (Set.union_subset hgts hkθ_ts)
    have hφint : (∫ x, φ x) = 0 := by
      rw [hφ]
      have hkθ_int : Integrable (fun x => (k • θ) x) volume :=
        hkθ_cd.continuous.integrable_of_hasCompactSupport hkθ_cs
      rw [show (fun x => (g - k • θ) x) = (fun x => g x - (k • θ) x) from by
        ext x; rw [Pi.sub_apply]]
      rw [integral_sub hg_int hkθ_int]
      have hkk : (∫ x, (k • θ) x) = k * J := by
        rw [show (fun x => (k • θ) x) = (fun x => k * θ x) from by ext x; rw [Pi.smul_apply, smul_eq_mul]]
        rw [integral_const_mul, hJ]
      rw [hkk, hk, div_mul_cancel₀ Jg hJne, sub_self]
    have hφf : (∫ x, φ x • f x) = 0 := by
      obtain ⟨ψ, hψcd, hψcs, hψts, hψderiv⟩ :=
        exists_primitive_tsupport_subset hφcd hφcs hφts hφint
      have hh := h ψ hψcd hψcs hψts
      rw [hψderiv] at hh
      simpa [smul_eq_mul] using hh
    have hgf_int : Integrable (fun x => g x • f x) volume :=
      integrable_smul_of_locallyIntegrableOn_of_tsupport_subset hf hgcd.continuous hgcs hgts
    have hkθf_int : Integrable (fun x => (k • θ) x • f x) volume :=
      integrable_smul_of_locallyIntegrableOn_of_tsupport_subset hf hkθ_cd.continuous hkθ_cs hkθ_ts
    have hsplit : (∫ x, φ x • f x) = (∫ x, g x • f x) - (Jg / J) * L := by
      rw [hφ]
      rw [show (fun x => (g - k • θ) x • f x) = (fun x => g x • f x - (k • θ) x • f x) from by
        ext x; rw [Pi.sub_apply, sub_smul]]
      rw [integral_sub hgf_int hkθf_int]
      congr 1
      have hkL : (∫ x, (k • θ) x • f x) = k * L := by
        rw [hL]
        rw [show (fun x => (k • θ) x • f x) = (fun x => k * (θ x • f x)) from by
          ext x; rw [Pi.smul_apply, smul_assoc, smul_eq_mul]]
        rw [integral_const_mul]
      rw [hkL, hk]
    have hgf : (∫ x, g x • f x) = (L / J) * Jg := by
      rw [hsplit] at hφf
      have h1 : (∫ x, g x • f x) = (Jg / J) * L := sub_eq_zero.mp hφf
      rw [h1]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_comm Jg L]
    have hgc_int : Integrable (fun x => g x • (L / J)) volume := by
      have := hg_int.mul_const (L / J)
      simpa [smul_eq_mul] using this
    have hgL : (∫ x, g x • (L / J)) = Jg * (L / J) := by
      rw [show (fun x => g x • (L / J)) = (fun x => g x * (L / J)) from by
        ext x; rw [smul_eq_mul]]
      rw [integral_mul_const, ← hJg]
    rw [show (fun x => g x • (f x - L / J)) = (fun x => g x • f x - g x • (L / J)) from by
      ext x; rw [smul_sub]]
    rw [integral_sub hgf_int hgc_int, hgf, hgL]
    ring
  have hmain := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (f := fun x => f x - L / J)
    (μ := volume) (U := Set.Ioo a b) isOpen_Ioo (hf.sub (locallyIntegrableOn_const (L / J))) hkey
  exact ⟨L / J, by
    filter_upwards [hmain] with x hx hxU
    exact sub_eq_zero.mp (hx hxU)⟩

end Commons.Analysis.Calculus