/-
Interior regularity of `bslOp α` (weight `(5+α)/α`): from the local Sobolev tower to a local
`C^∞` representative of the transported unknown on the strip.

The main results are

* `weakLoc`: the localized weak identity for the pair `(χ · Vc, χ · Gc)`;
* `localSmooth_r`: for every `x₀` in the strip and every `m`, the transported unknown
  `Vc α Ψ` agrees a.e. on some ball around `x₀` with a function of class `C^m`
  (Sobolev embedding `H^{m+2} ⊆ C^m` + the fundamental lemma of the calculus of variations);
* `localSmooth_all`: the same with `C^∞` (all orders) on the ball;
* `interiorSmooth`: gluing these local representatives gives a single function which is `C^∞`
  on the whole strip and agrees a.e. with `Vc α Ψ` there.
-/
import Mathlib.Analysis.Distribution.DerivNotation
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.InteriorRegularity.VT.Tower
import Submission.Work.EllipticEst.InteriorRegularity.exists_contDiffOn_of_memSobolev
import Submission.Work.EllipticEst.InteriorRegularity.IR.localSmoothGlue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology SchwartzMap LineDeriv ContDiff

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem Kop_eq_zero_of_notMem_tsupport {ψ : E2 → ℂ} (hψs : ∀ n : ℕ, ContDiff ℝ n ψ) {x : E2}
    (hx : x ∉ tsupport ψ) : Kop ψ x = 0 := by
  have hd0 : d0 ψ x = 0 := d0_eq_zero_of_notMem_tsupport hψs hx
  have hd1 : d1 ψ x = 0 := d1_eq_zero_of_notMem_tsupport hψs hx
  have hd0' : d0 (d0 ψ) x = 0 :=
    d0_eq_zero_of_notMem_tsupport (fun k => contDiff_d0 hψs k)
      (fun h => hx ((tsupport_d0_subset hψs) h))
  have hd1' : d1 (d1 ψ) x = 0 :=
    d1_eq_zero_of_notMem_tsupport (fun k => contDiff_d1 hψs k)
      (fun h => hx ((tsupport_d1_subset hψs) h))
  have hψ0 : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
  simp only [Kop, hd0, hd1, hd0', hd1', hψ0, mul_zero, add_zero, sub_zero, zero_add, neg_zero]

/-- **The localized weak identity.**  If `(Vc, Gc)` satisfies the strip weak formulation, then
the cut-off pair `(χ · Vc, χ · Gc)` satisfies the weak identity for every test function whose
support lies in `{χ = 1}`. -/
theorem weakLoc {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hSW : StripWeak (Vc α Ψ) (Gc α F))
    {χ : E2 → ℂ} (hχs : ∀ n : ℕ, ContDiff ℝ n χ) (hχsub : tsupport χ ⊆ stripE) :
    ∀ ψ : E2 → ℂ, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      Function.support ψ ⊆ {x | χ x = 1} →
      ∫ x, (χ x * Vc α Ψ x) * Kop ψ x = ∫ x, (χ x * Gc α F x) * ψ x := by
  intro ψ hψs hψc hψsub
  have hclosed : IsClosed {x : E2 | χ x = 1} :=
    isClosed_eq (hχs 0).continuous continuous_const
  have hts : tsupport ψ ⊆ {x : E2 | χ x = 1} := by
    rw [tsupport]
    exact (closure_mono hψsub).trans (le_of_eq hclosed.closure_eq)
  have hKop : Function.support (Kop ψ) ⊆ {x : E2 | χ x = 1} := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxn
    exact hx (Kop_eq_zero_of_notMem_tsupport hψs (fun h => hxn (hts h)))
  have hstrip : Function.support ψ ⊆ stripE := fun x hx =>
    hχsub (subset_closure (by
      rw [Function.mem_support]
      rw [hψsub hx]
      exact one_ne_zero))
  calc ∫ x, (χ x * Vc α Ψ x) * Kop ψ x
      = ∫ x, (χ x * Kop ψ x) * Vc α Ψ x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    _ = ∫ x, Kop ψ x * Vc α Ψ x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        by_cases hx : Kop ψ x = 0
        · simp [hx]
        · have h1 : χ x = 1 := hKop (Function.mem_support.mpr hx)
          simp only [h1, one_mul]
    _ = ∫ x, Vc α Ψ x * Kop ψ x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    _ = ∫ x, Gc α F x * ψ x := hSW ψ hψs hψc hstrip
    _ = ∫ x, Gc α F x * (χ x * ψ x) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        by_cases hx : ψ x = 0
        · simp [hx]
        · have h1 : χ x = 1 := hψsub (Function.mem_support.mpr hx)
          simp only [h1, one_mul]
    _ = ∫ x, (χ x * Gc α F x) * ψ x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-- A compactly supported function times a function continuous on an open set containing its
support is integrable. -/
theorem integrable_mul_of_continuousOn {g Φ : E2 → ℂ} (hgc : HasCompactSupport g)
    (hgs : ∀ n : ℕ, ContDiff ℝ n g) {U : Set E2} (hU : IsOpen U) (hsub : tsupport g ⊆ U)
    (hΦ : ContinuousOn Φ U) : Integrable (fun x => g x * Φ x) := by
  have hOn : IntegrableOn (fun x => g x * Φ x) (tsupport g) :=
    (integrable_of_smooth_compact hgc hgs).integrableOn.mul_continuousOn
      (hΦ.mono hsub) hgc
  have hsupp : Function.support (fun x => g x * Φ x) ⊆ tsupport g := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxg
    rw [image_eq_zero_of_notMem_tsupport hxg, zero_mul] at hx
    exact hx rfl
  have hind : Integrable ((tsupport g).indicator (fun x => g x * Φ x)) :=
    (integrable_indicator_iff (show IsCompact (tsupport g) from hgc).measurableSet).mpr hOn
  rwa [indicator_eq_self.mpr hsupp] at hind


theorem tsupport_ofReal_subset {c : E2 → ℝ} :
    tsupport (fun x : E2 => ((c x : ℝ) : ℂ)) ⊆ tsupport c := by
  rw [tsupport, tsupport]
  refine closure_mono ?_
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro h0
  exact hx (by rw [h0]; simp)

theorem hasCompactSupport_ofReal {c : E2 → ℝ} (hc : HasCompactSupport c) :
    HasCompactSupport (fun x : E2 => ((c x : ℝ) : ℂ)) :=
  IsCompact.of_isClosed_subset (show IsCompact (tsupport c) from hc) (isClosed_tsupport _)
    tsupport_ofReal_subset

/-- A compactly supported smooth *real* function times a function continuous on an open set
containing its support is integrable. -/
theorem integrable_smul_of_continuousOn {c : E2 → ℝ} (hcc : HasCompactSupport c)
    (hcs : ∀ n : ℕ, ContDiff ℝ n c) {Φ : E2 → ℂ} {U : Set E2} (hU : IsOpen U)
    (hsub : tsupport c ⊆ U) (hΦ : ContinuousOn Φ U) :
    Integrable (fun x => c x • Φ x) := by
  have hcs' : ∀ n : ℕ, ContDiff ℝ n (fun x : E2 => ((c x : ℝ) : ℂ)) :=
    fun n => Complex.ofRealCLM.contDiff.comp (hcs n)
  refine (integrable_mul_of_continuousOn (hasCompactSupport_ofReal hcc) hcs' hU
    (tsupport_ofReal_subset.trans hsub) hΦ).congr
    (Filter.Eventually.of_forall fun x => ?_)
  exact (Complex.real_smul : c x • Φ x = ((c x : ℝ) : ℂ) * Φ x).symm

/-- A compactly supported smooth *real* function times an integrable function is integrable. -/
theorem integrable_smul_of_cc {V : E2 → ℂ} (hV : Integrable V) {c : E2 → ℝ}
    (hcc : HasCompactSupport c) (hcs : ∀ n : ℕ, ContDiff ℝ n c) :
    Integrable (fun x => c x • V x) := by
  have hcs' : ∀ n : ℕ, ContDiff ℝ n (fun x : E2 => ((c x : ℝ) : ℂ)) :=
    fun n => Complex.ofRealCLM.contDiff.comp (hcs n)
  refine (integrable_mul_of_cc hV (hasCompactSupport_ofReal hcc) hcs').congr
    (Filter.Eventually.of_forall fun x => ?_)
  exact (Complex.real_smul : c x • V x = ((c x : ℝ) : ℂ) * V x).symm

end Work.EllipticEst.InteriorRegularity.VT
