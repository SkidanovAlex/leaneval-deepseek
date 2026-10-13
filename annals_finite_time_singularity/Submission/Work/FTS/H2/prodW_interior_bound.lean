import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.psi_mw_le
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.FTS.H2.Q.Base

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-! ## The Leibniz calculus of `∂_z^k D_θ^j` in the interior class `SmoothQuad`

`Work.FTS.LocData.SmoothQuad` is genuine `C^∞` on the open quadrant
`z > -1, 0 < θ < π/2`; on this class the `θ`-Leibniz rule is
`Work.FTS.LocData.DthIter_mul_smoothQuad` and the `z`-Leibniz rule is
`Work.FTS.H2.Q.pzIter_mul_local_sm`.  Combining the two gives the mixed Leibniz expansion of a
product, which is the `SmoothQuad` counterpart of `Work.Spaces.pz_DthIter_mul_eq` (whose
hypothesis is `SmoothInt`). -/

/-- The `z`-slices of the `D_θ`-iterates of a `SmoothQuad` function are `C^∞` at every
`z ∈ [0,∞)`, for `θ ∈ (0,π/2)`. -/
theorem sqm_dthIter_zslice_contDiffAt {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) (a : ℕ) :
    ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => Work.Spaces.DthIter a f z' θ) z := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hzIoi : z ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith)
  exact ((hf.DthIter a).curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hzIoi)

/-- At a fixed angle `θ ∈ (0,π/2)` the `D_θ`-Leibniz expansion of a product agrees with
`D_θ^j (f g)` on a neighbourhood of every `z ∈ [0,∞)`. -/
theorem sqm_DthIter_mul_zslice_eventuallyEq (j : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g) {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (fun z' => Work.Spaces.DthIter j (fun z θ => f z θ * g z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ)
          * (Work.Spaces.DthIter a f z' θ * Work.Spaces.DthIter (j - a) g z' θ)) := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hzIoi : z ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith)
  filter_upwards [isOpen_Ioi.mem_nhds hzIoi] with z' hz'
  exact Work.FTS.LocData.DthIter_mul_smoothQuad j f g hθ (hf.curry_θ hz') (hg.curry_θ hz')

/-- **The mixed Leibniz identity in the interior class**: for `SmoothQuad` functions `f, g`,
every `z ∈ [0,∞)` and `θ ∈ (0,π/2)`,
`∂_z^k D_θ^j (f g) = ∑_{a≤j} ∑_{c≤k} C(j,a) C(k,c) ∂_z^c D_θ^a f · ∂_z^{k-c} D_θ^{j-a} g`. -/
theorem sqm_pz_DthIter_mul_eq (k j : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ
        = ∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (k + 1),
            ((j.choose a : ℝ) * (k.choose c : ℝ))
              * (Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ
                  * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ) := by
  intro z hz θ hθ
  have hslice : ∀ (h : ℝ → ℝ → ℝ), Work.FTS.LocData.SmoothQuad h → ∀ a : ℕ,
      ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => Work.Spaces.DthIter a h z' θ) z :=
    fun h hh a => sqm_dthIter_zslice_contDiffAt hh hθ hz a
  have hleib := sqm_DthIter_mul_zslice_eventuallyEq j f g hf hg hz hθ
  rw [Work.Spaces.pzIter_eq_iteratedDeriv k _ z θ, Filter.EventuallyEq.iteratedDeriv_eq k hleib]
  have hsum := Work.Spaces.iteratedDeriv_sum_const_mul (s := Finset.range (j + 1))
    (c := fun a => (j.choose a : ℝ))
    (F := fun a z' => Work.Spaces.DthIter a f z' θ * Work.Spaces.DthIter (j - a) g z' θ) k z
    (fun a _ => ((hslice f hf a).mul (hslice g hg (j - a))).of_le
      (by rw [Work.Stability.smoothOrder]; simp))
  rw [hsum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hfun : (fun z' => Work.Spaces.DthIter a f z' θ * Work.Spaces.DthIter (j - a) g z' θ)
      = (fun z' => Work.Spaces.DthIter a f z' θ)
        * (fun z' => Work.Spaces.DthIter (j - a) g z' θ) := by
    funext z'; rfl
  rw [hfun]
  have hmul := iteratedDeriv_mul (f := fun z' => Work.Spaces.DthIter a f z' θ)
    (g := fun z' => Work.Spaces.DthIter (j - a) g z' θ) (x := z) (n := k)
    ((hslice f hf a).of_le (by rw [Work.Stability.smoothOrder]; simp))
    ((hslice g hg (j - a)).of_le (by rw [Work.Stability.smoothOrder]; simp))
  rw [hmul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Work.Spaces.pzIter_eq_iteratedDeriv c (Work.Spaces.DthIter a f) z θ,
    ← Work.Spaces.pzIter_eq_iteratedDeriv (k - c) (Work.Spaces.DthIter (j - a) g) z θ]
  ring

/-- **The Leibniz bound in the interior class**, with the explicit constant `257` of
`Work.Spaces.one_add_choose_double_sum_le` (the `SmoothQuad` counterpart of
`Work.Spaces.pz_mixed_mul_le_4`). -/
theorem sqm_pz_DthIter_mul_le_4 (k j : ℕ) (hk : k ≤ 4) (hj : j ≤ 4)
    (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ| ≤
        (257 : ℝ) * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
          |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ| *
            |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ| := by
  intro z hz θ hθ
  rw [sqm_pz_DthIter_mul_eq k j f g hf hg z hz θ hθ]
  have h1 := Work.Spaces.abs_binom_double_sum_le k j
    (fun a c => Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ)
    (fun a c => Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ)
  have hT : (0 : ℝ) ≤ ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
      |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ| *
        |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ| :=
    Finset.sum_nonneg fun c _ =>
      Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  exact h1.trans (mul_le_mul_of_nonneg_right
    (Work.Spaces.one_add_choose_double_sum_le k j hk hj) hT)

/-! ## Nonnegativity of the `𝒲^{l,∞}`-norm -/

/-- The `𝒲^{l,∞}`-norm is nonnegative whenever it is honest. -/
theorem sqm_WlInf_nonneg (α : ℝ) (l : ℕ) (h : ℝ → ℝ → ℝ) (hmem : Work.Spaces.WlInfMem α l h) :
    0 ≤ Work.Spaces.WlInf α l h := by
  rw [Work.Spaces.WlInf]
  exact add_nonneg (Work.Spaces.wlZSum_nonneg α l h hmem)
    (Work.Spaces.wlThSum_nonneg α l h hmem)

/-! ## The pointwise bound for one summand of the angular Leibniz expansion -/

/-- One summand of the angular Leibniz expansion, bounded by the product of the two
`𝒲^{4,∞}`-norms: for `c ≤ k`, `a ≤ j`, `1 ≤ j`, `k + j ≤ 4`,

`|(z+1)^c ∂_z^c D_θ^a f| · |(z+1)^{k-c} ∂_z^{k-c} D_θ^{j-a} g| · sin(2θ)^{-α/5}/(α+sin 2θ)
   ≤ 2 |f|_𝒲 |g|_𝒲`. -/
theorem sqm_ang_summand_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f g : ℝ → ℝ → ℝ) (hmf : Work.Spaces.WlInfMem α 4 f) (hmg : Work.Spaces.WlInfMem α 4 g)
    (c a k j : ℕ) (hc : c ≤ k) (ha : a ≤ j) (hj : 1 ≤ j) (hkj : k + j ≤ 4)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |(z + 1) ^ c * Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
        * |(z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ 2 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hspos : 0 < α + Real.sin (2 * θ) := by linarith
  have hWfnn : 0 ≤ Work.Spaces.WlInf α 4 f := sqm_WlInf_nonneg α 4 f hmf
  have hWgnn : 0 ≤ Work.Spaces.WlInf α 4 g := sqm_WlInf_nonneg α 4 g hmg
  have hWWnn : 0 ≤ Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g := mul_nonneg hWfnn hWgnn
  have hψa : 0 ≤ (if a = 0 then (1 : ℝ)
      else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    by_cases h : a = 0
    · rw [if_pos h]; norm_num
    · rw [if_neg h]; exact mul_nonneg (by linarith) (Real.rpow_nonneg hs0 _)
  have hψb : 0 ≤ (if j - a = 0 then (1 : ℝ)
      else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    by_cases h : j - a = 0
    · rw [if_pos h]; norm_num
    · rw [if_neg h]; exact mul_nonneg (by linarith) (Real.rpow_nonneg hs0 _)
  have hZnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
    div_nonneg (Real.rpow_nonneg hs0 _) (le_of_lt hspos)
  have hFA := Work.Spaces.factor_bound α hα f hmf c a (by omega) (fun _ => by omega) z θ hz hθI
  have hGA := Work.Spaces.factor_bound α hα g hmg (k - c) (j - a) (by omega) (fun _ => by omega)
    z θ hz hθI
  have hpsi := Work.Spaces.psi_mw_le α hα hα1 θ hθI a j ha hj
  have hstep : |(z + 1) ^ c * Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
        * |(z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|
      ≤ (Work.Spaces.WlInf α 4 f * (if a = 0 then (1 : ℝ)
            else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
        * (Work.Spaces.WlInf α 4 g * (if j - a = 0 then (1 : ℝ)
            else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
    mul_le_mul hFA hGA (abs_nonneg _) (mul_nonneg hWfnn hψa)
  calc |(z + 1) ^ c * Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
          * |(z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ ((Work.Spaces.WlInf α 4 f * (if a = 0 then (1 : ℝ)
            else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
        * (Work.Spaces.WlInf α 4 g * (if j - a = 0 then (1 : ℝ)
            else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_right hstep hZnn
    _ = (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g)
          * ((if a = 0 then (1 : ℝ)
              else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            * (if j - a = 0 then (1 : ℝ)
              else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
    _ ≤ (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) * 2 :=
          mul_le_mul_of_nonneg_left hpsi hWWnn
    _ = 2 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by ring

/-! ## The interior part of `ProdW` -/

/-- The **interior** part of `Work.FTS.H2.ProdW`: on the *open* quadrant, where the `z`-slices
of a `SmoothQuad` function are `C^∞` (`Work.FTS.LocData.SmoothQuad.curry_z`), the Leibniz
expansion is available for both `∂_z^k` and `D_θ^j`, and hence the weighted derivatives of the
product are bounded by `|f|_𝒲 |g|_𝒲`:

* radial: `|(z+1)^k ∂_z^k (fg)| ≤ C |f|_𝒲 |g|_𝒲` for `k ≤ 4`;
* angular: `|(z+1)^k ∂_z^k D_θ^j (fg) · sin(2θ)^{-α/5}/(α+sin 2θ)| ≤ C |f|_𝒲 |g|_𝒲` for
  `1 ≤ j`, `k+j ≤ 4`.

The pointwise factor bounds are `Work.Spaces.WlInf_z_bound` and `Work.Spaces.factor_bound`
(which is `Work.Spaces.WlInf_mixed_bound` after the weight cancellation), and the sharing of the
single angular weight between the two factors of each Leibniz summand is
`Work.Spaces.psi_mw_le`.  The Leibniz expansions at the genuine smooth order are
`Work.FTS.H2.Q.pzIter_mul_local_sm` (for `∂_z^k`) and `Work.FTS.LocData.DthIter_mul_smoothQuad`
(for `D_θ^j`). -/
theorem prodW_interior_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.LocData.SmoothQuad f → Work.FTS.LocData.SmoothQuad g →
      Work.Spaces.WlInfMem α 4 f → Work.Spaces.WlInfMem α 4 g →
      (∀ k ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
        |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => f z θ * g z θ) z θ|
          ≤ C * Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) ∧
      (∀ j k : ℕ, 1 ≤ j → k + j ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
        |(z + 1) ^ k * Work.Spaces.pzIter k
              (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
          ≤ C * Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by
  refine ⟨100000, by norm_num, ?_⟩
  intro α f g hα hα1 hf hg hmf hmg
  have hWfnn : 0 ≤ Work.Spaces.WlInf α 4 f := sqm_WlInf_nonneg α 4 f hmf
  have hWgnn : 0 ≤ Work.Spaces.WlInf α 4 g := sqm_WlInf_nonneg α 4 g hmg
  have hWWnn : 0 ≤ Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g := mul_nonneg hWfnn hWgnn
  constructor
  · -- the radial part
    intro k hk z hz θ hθ
    have hz0 : (0 : ℝ) ≤ z := hz
    have hzIoi : z ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith)
    have hzp : 0 ≤ (z + 1) ^ k := pow_nonneg (by linarith) k
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hzu : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => f z' θ) z :=
      (hf.curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hzIoi)
    have hgv : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => g z' θ) z :=
      (hg.curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hzIoi)
    have hleib := Work.FTS.H2.Q.pzIter_mul_local_sm (u := f) (v := g) k hzu hgv
    have h1 : |Work.Spaces.pzIter k (fun z θ => f z θ * g z θ) z θ|
        ≤ ∑ c ∈ Finset.range (k + 1),
            (k.choose c : ℝ)
              * (|Work.Spaces.pzIter c f z θ| * |Work.Spaces.pzIter (k - c) g z θ|) := by
      rw [hleib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun c _ => ?_)
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), abs_mul]
    have hstep : ∀ c ∈ Finset.range (k + 1),
        (z + 1) ^ k * (|Work.Spaces.pzIter c f z θ| * |Work.Spaces.pzIter (k - c) g z θ|)
          ≤ Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g := by
      intro c hc
      have hc_le : c ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
      have hc4 : c ≤ 4 := by omega
      have hkc4 : k - c ≤ 4 := by omega
      have hc0 : (0 : ℝ) ≤ (z + 1) ^ c := pow_nonneg (by linarith) c
      have hkc0 : (0 : ℝ) ≤ (z + 1) ^ (k - c) := pow_nonneg (by linarith) (k - c)
      have hA := Work.Spaces.WlInf_z_bound α 4 f hmf c hc4 z θ hz hθI
      have hB := Work.Spaces.WlInf_z_bound α 4 g hmg (k - c) hkc4 z θ hz hθI
      rw [abs_mul, abs_of_nonneg hc0] at hA
      rw [abs_mul, abs_of_nonneg hkc0] at hB
      have heq : (z + 1) ^ k
            * (|Work.Spaces.pzIter c f z θ| * |Work.Spaces.pzIter (k - c) g z θ|)
          = ((z + 1) ^ c * |Work.Spaces.pzIter c f z θ|)
            * ((z + 1) ^ (k - c) * |Work.Spaces.pzIter (k - c) g z θ|) := by
        rw [show (z + 1) ^ k = (z + 1) ^ c * (z + 1) ^ (k - c) by
          rw [← pow_add, Nat.add_sub_cancel' hc_le]]
        ring
      rw [heq]
      exact mul_le_mul hA hB (mul_nonneg hkc0 (abs_nonneg _)) hWfnn
    calc |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => f z θ * g z θ) z θ|
        = (z + 1) ^ k * |Work.Spaces.pzIter k (fun z θ => f z θ * g z θ) z θ| := by
          rw [abs_mul, abs_of_nonneg hzp]
      _ ≤ (z + 1) ^ k * (∑ c ∈ Finset.range (k + 1),
            (k.choose c : ℝ)
              * (|Work.Spaces.pzIter c f z θ| * |Work.Spaces.pzIter (k - c) g z θ|)) :=
          mul_le_mul_of_nonneg_left h1 hzp
      _ = ∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ)
            * ((z + 1) ^ k
                * (|Work.Spaces.pzIter c f z θ| * |Work.Spaces.pzIter (k - c) g z θ|)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ ∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ)
            * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) :=
          Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_left (hstep c hc) (Nat.cast_nonneg _)
      _ = (∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ))
            * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by rw [Finset.sum_mul]
      _ = (2 : ℝ) ^ k * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by
          have h2 : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
          have hc : (∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ)) = (2 : ℝ) ^ k := by
            rw [← Nat.cast_sum, Nat.sum_range_choose k, h2]
          rw [hc]
      _ ≤ 16 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by
          apply mul_le_mul_of_nonneg_right _ hWWnn
          calc (2 : ℝ) ^ k ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hk
            _ = 16 := by norm_num
      _ ≤ 100000 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by
          apply mul_le_mul_of_nonneg_right _ hWWnn; norm_num
      _ = 100000 * Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g := by ring
  · -- the angular part
    intro j k hj hkj z hz θ hθ
    have hz0 : (0 : ℝ) ≤ z := hz
    have hzp : 0 ≤ (z + 1) ^ k := pow_nonneg (by linarith) k
    have hk4 : k ≤ 4 := by omega
    have hj4 : j ≤ 4 := by omega
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    have hspos : 0 < α + Real.sin (2 * θ) := by linarith
    have hZnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
      div_nonneg (Real.rpow_nonneg hs0 _) (le_of_lt hspos)
    have hleib := sqm_pz_DthIter_mul_le_4 k j hk4 hj4 f g hf hg z hz θ hθ
    have hLHS : |(z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
        = (z + 1) ^ k * |Work.Spaces.pzIter k
              (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
      rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hzp,
        abs_of_nonneg (Real.rpow_nonneg hs0 _), abs_of_pos hspos]
      ring
    have hbound1 : (z + 1) ^ k * |Work.Spaces.pzIter k
            (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ|
        ≤ 257 * ((z + 1) ^ k * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
              |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
                * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|) := by
      have h1 := mul_le_mul_of_nonneg_left hleib hzp
      calc (z + 1) ^ k * |Work.Spaces.pzIter k
              (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ|
          ≤ (z + 1) ^ k * (257 * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
                  * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|) := h1
        _ = 257 * ((z + 1) ^ k * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
                  * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|) := by ring
    have hbound2 : (z + 1) ^ k * (∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
            |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
              * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|)
        = ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
            (z + 1) ^ k * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
              * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
    have hstep : ∀ c ∈ Finset.range (k + 1), ∀ a ∈ Finset.range (j + 1),
        (z + 1) ^ k * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
              * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|)
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          ≤ 2 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by
      intro c hc a ha
      have hc_le : c ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
      have ha_le : a ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
      have heq : (z + 1) ^ k * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
              * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|)
          = |(z + 1) ^ c * Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
            * |(z + 1) ^ (k - c)
                * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ| := by
        have hz1 : (0 : ℝ) < z + 1 := by linarith
        have hp1 : (0 : ℝ) ≤ (z + 1) ^ c := pow_nonneg (le_of_lt hz1) c
        have hp2 : (0 : ℝ) ≤ (z + 1) ^ (k - c) := pow_nonneg (le_of_lt hz1) (k - c)
        rw [abs_mul, abs_of_nonneg hp1, abs_mul, abs_of_nonneg hp2]
        rw [show (z + 1) ^ k = (z + 1) ^ c * (z + 1) ^ (k - c) by
          rw [← pow_add, Nat.add_sub_cancel' hc_le]]
        ring
      rw [heq]
      exact sqm_ang_summand_bound α hα hα1 f g hmf hmg c a k j hc_le ha_le hj hkj hz hθ
    have hsum : (∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
            (z + 1) ^ k * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
              * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|))
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        = ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
            (z + 1) ^ k * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
              * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|)
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_mul]
    have hsumle : ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
            (z + 1) ^ k * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
              * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|)
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
            2 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) :=
      Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun a ha => hstep c hc a ha
    calc |(z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
        = (z + 1) ^ k * |Work.Spaces.pzIter k
              (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := hLHS
      _ ≤ 257 * ((z + 1) ^ k * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
              |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
                * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|)
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_right hbound1 hZnn
      _ = 257 * ((∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
              (z + 1) ^ k * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
                * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|))
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by
          rw [hbound2]
          ring
      _ ≤ 257 * (∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
              2 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          rw [hsum]
          exact hsumle
      _ = 257 * (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ))
            * (2 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g)) := by
          rw [Finset.sum_const, Finset.card_range, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, nsmul_eq_mul]
          ring
      _ ≤ 100000 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by
          have hk1 : ((k + 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (show k + 1 ≤ 5 by omega)
          have hj1 : ((j + 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (show j + 1 ≤ 5 by omega)
          have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          have hj0 : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          have hu : 257 * (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) * 2 ≤ 100000 := by nlinarith
          calc 257 * (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ))
                * (2 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g))
              = (257 * (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) * 2)
                * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by ring
            _ ≤ 100000 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) :=
                mul_le_mul_of_nonneg_right hu hWWnn
      _ = 100000 * Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g := by ring

end Work.FTS.H2
