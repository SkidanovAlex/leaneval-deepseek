/-
Interior regularity of `bslOp α` (weight `(5+α)/α`): the distribution `Td f` of an integrable
function, and the small API that the local Sobolev tower needs.

`Td f hf = Lp.toTemperedDistribution hf.toLp`, so `Td f hf ψ = ∫ x, ψ x • f x`.  Because the
underlying `Lp` class only depends on the almost-everywhere class of `f`, all the lemmas are
stated with an explicit (but irrelevant) integrability witness.

The main facts proved here:

* `Td_smul`: multiplication of `Td f` by a smooth multiplier `g` is `Td (g · f)`;
* `lineDerivOp_eq_d0`, `lineDerivOp_eq_d1`: the distributional derivative `∂_{e_i}` of a
  Schwartz function is the pointwise `d0`/`d1`;
* `Td_memSobolev_of_smooth_compact`: the distribution of a compactly supported `C^∞` function
  lies in every Bessel potential space `H^s`;
* `integrable_mul_of_cc`: an integrable function times a compactly supported smooth function
  is integrable.
-/
import Mathlib.Analysis.Distribution.Sobolev
import Submission.Work.EllipticEst.InteriorRegularity.VT.Basic
import Submission.Work.EllipticEst.InteriorRegularity.VT.DerivAux
import Submission.Work.EllipticEst.InteriorRegularity.Q0.SobChain
import Submission.Work.EllipticEst.InteriorRegularity.memSobolev_neg_two

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology SchwartzMap

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The tempered distribution of an integrable function on `E2`. -/
def Td (f : E2 → ℂ) (hf : Integrable f) : 𝓢'(E2, ℂ) :=
  Lp.toTemperedDistribution (memLp_one_iff_integrable.mpr hf).toLp

theorem Td_apply (f : E2 → ℂ) (hf : Integrable f) (ψ : 𝓢(E2, ℂ)) :
    Td f hf ψ = ∫ x, ψ x • f x := by
  rw [Td, Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_one_iff_integrable.mpr hf).coeFn_toLp] with x hx
  rw [hx]

theorem Td_congr {f g : E2 → ℂ} (hf : Integrable f) (hg : Integrable g)
    (h : f =ᵐ[volume] g) : Td f hf = Td g hg := by
  ext ψ
  rw [Td_apply, Td_apply]
  exact integral_congr_ae (h.mono fun x hx => by simp only []; rw [hx])

theorem lineDerivOp_eq_d0 (φ : 𝓢(E2, ℂ)) :
    (⇑(LineDeriv.lineDerivOp e0 φ) : E2 → ℂ) = fun x => d0 (φ : E2 → ℂ) x := by
  funext x
  rw [SchwartzMap.lineDerivOp_apply]
  rfl

theorem lineDerivOp_eq_d1 (φ : 𝓢(E2, ℂ)) :
    (⇑(LineDeriv.lineDerivOp e1 φ) : E2 → ℂ) = fun x => d1 (φ : E2 → ℂ) x := by
  funext x
  rw [SchwartzMap.lineDerivOp_apply]
  rfl

/-- A compactly supported `C^∞` function has temperate growth. -/
theorem hasTemperateGrowth_of_cc {f : E2 → ℂ} (hc : HasCompactSupport f)
    (hs : ∀ n : ℕ, ContDiff ℝ n f) : Function.HasTemperateGrowth f := by
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_infty.mpr hs
  have hcoe : (⇑(hc.toSchwartzMap hfs) : E2 → ℂ) = f :=
    funext (HasCompactSupport.toSchwartzMap_toFun hc hfs)
  have h := (hc.toSchwartzMap hfs).hasTemperateGrowth
  rwa [hcoe] at h

theorem Td_smul {g : E2 → ℂ} (hg : Function.HasTemperateGrowth g) {f : E2 → ℂ}
    (hf : Integrable f) (hgf : Integrable (fun x => g x * f x)) :
    TemperedDistribution.smulLeftCLM ℂ g (Td f hf) = Td (fun x => g x * f x) hgf := by
  ext ψ
  rw [TemperedDistribution.smulLeftCLM_apply_apply, Td_apply, Td_apply]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg]
  simp only [smul_eq_mul]
  ring

/-- The distribution of a compactly supported `C^∞` function lies in every `H^s`. -/
theorem Td_memSobolev_of_smooth_compact {f : E2 → ℂ} (hint : Integrable f)
    (hc : HasCompactSupport f) (hs : ∀ n : ℕ, ContDiff ℝ n f) (s : ℝ) :
    TemperedDistribution.MemSobolev s 2 (Td f hint) := by
  have hf1 : MemLp f 1 volume := memLp_one_iff_integrable.mpr hint
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_infty.mpr hs
  have hcoe : (⇑(hc.toSchwartzMap hfs) : E2 → ℂ) = f :=
    funext (HasCompactSupport.toSchwartzMap_toFun hc hfs)
  have hf2 : MemLp f 2 volume := by
    have h := (hc.toSchwartzMap hfs).memLp 2 volume
    rwa [hcoe] at h
  have hmain : TemperedDistribution.MemSobolev s 2
      (Lp.toTemperedDistribution hf2.toLp) := Q0.ccMemSobolev (s := s) (f := f) (hf := hf2) hc hs
  have heq : Lp.toTemperedDistribution hf1.toLp = Lp.toTemperedDistribution hf2.toLp := by
    ext ψ
    rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards [hf1.coeFn_toLp, hf2.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  rw [Td, heq]
  exact hmain

/-- A bound for a continuous compactly supported function. -/
theorem exists_norm_bound_of_cc {g : E2 → ℂ} (hc : HasCompactSupport g)
    (hs : ∀ n : ℕ, ContDiff ℝ n g) : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hc.isCompact.exists_bound_of_continuousOn
    ((hs 0).continuous.continuousOn)
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ tsupport g
  · exact le_trans (hC x hx) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact le_max_right _ _

/-- An integrable function times a compactly supported smooth function is integrable. -/
theorem integrable_mul_of_cc {f : E2 → ℂ} (hf : Integrable f) {g : E2 → ℂ}
    (hc : HasCompactSupport g) (hs : ∀ n : ℕ, ContDiff ℝ n g) :
    Integrable (fun x => g x * f x) := by
  obtain ⟨C, hC⟩ := exists_norm_bound_of_cc hc hs
  refine Integrable.mono' (hf.norm.const_mul C) ?_ ?_
  · exact ((hs 0).continuous.aestronglyMeasurable).mul hf.aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- `L¹ ⊂ H^{-2}` in the `Td` notation (dimension `2 ≤ 3`). -/
theorem Td_memSobolev_neg_two {f : E2 → ℂ} (hf : Integrable f) :
    TemperedDistribution.MemSobolev (-2) 2 (Td f hf) := by
  rw [Td]
  exact memSobolev_neg_two (E := E2) (by rw [finrank_E2]; norm_num)
    (memLp_one_iff_integrable.mpr hf)

/- The distribution `Td f` of an integrable function is kept opaque for elaboration: this
keeps the unification of the large expressions in the Sobolev tower cheap.  All the lemmas about
`Td` are proved above, before the attribute is set. -/
attribute [irreducible] Td

end Work.EllipticEst.InteriorRegularity.VT
