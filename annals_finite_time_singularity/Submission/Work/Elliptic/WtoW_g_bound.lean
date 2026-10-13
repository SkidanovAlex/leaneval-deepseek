/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `g`-side bound of Lemma `WtoW`

Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021), Lemma `WtoW`
(tex 1255).  The estimate proved here is the "one extra angular derivative" bound:
for `0 < α ≤ 1`, `g` smooth on a neighbourhood of the closed quadrant with honest
`𝒲^{5,∞}`-norm and `m + q ≤ 4`,

  `|(z+1)^m ∂_z^m D_θ^q(∂_θ g)(z,θ)| · sin(2θ)
     ≤ K · |g|_{𝒲^{5,∞}} · (α + sin 2θ) · sin(2θ)^{α/5}`.

The proof rests on the identity (`WtoW_g_ident`)

  `sin(2θ)·D_θ^q(∂_θ g) = Σ_{j ≤ q} c_{q,j}(θ)·D_θ^{j+1} g`,

whose coefficients `c_{q,j}` are bounded (`WtoW_g_coeff_bound`); differentiating it
`m` times in `z` and using the pointwise consequence
`WlInf_terms.pz_Dth_sup_bound` of `WlInfMem α 5 g` finishes the proof.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.WtoWAux
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.pz_aux
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.Elliptic.WtoHAux
import Submission.Work.Elliptic.WtoW_g_defs
import Submission.Work.Elliptic.WtoW_g_coeff_rec
import Submission.Work.Elliptic.WtoW_g_coeff_self
import Submission.Work.Elliptic.WtoW_g_coeff_bound
import Submission.Work.Elliptic.WtoW_pzIter_sum_theta
import Submission.Work.Elliptic.WtoW_Dth_mul_theta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Elementary analytic facts -/

/-- `∂_θ (sin 2·) = 2 cos 2· = X`. -/
theorem WtoW_hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (WtoW_X θ) θ := by
  have hg : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h1 : HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (Real.cos (2 * θ) * 2) θ := by
    simpa [Function.comp_def] using (Real.hasDerivAt_sin (2 * θ)).comp θ hg
  have h2 : WtoW_X θ = Real.cos (2 * θ) * 2 := by simp [WtoW_X]; ring
  rw [show (fun θ : ℝ => Real.sin (2 * θ)) = fun x : ℝ => Real.sin (2 * x) from rfl, h2]
  exact h1

/-- `∂_θ (sin 2·) = 2 cos 2· = X`. -/
theorem WtoW_deriv_sin_two (θ : ℝ) :
    deriv (fun θ : ℝ => Real.sin (2 * θ)) θ = WtoW_X θ :=
  (WtoW_hasDerivAt_sin_two θ).deriv

/-- Linearity of `D_θ` over finite sums. -/
theorem WtoW_g_Dth_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun θ' => F i z θ') θ) :
    Work.Spaces.Dth (fun z θ => ∑ i ∈ s, F i z θ) z θ
      = ∑ i ∈ s, Work.Spaces.Dth (F i) z θ := by
  show Real.sin (2 * θ) * deriv (fun θ' => ∑ i ∈ s, F i z θ') θ
      = ∑ i ∈ s, Real.sin (2 * θ) * deriv (fun θ' => F i z θ') θ
  have hfun : (fun θ' => ∑ i ∈ s, F i z θ') = ∑ i ∈ s, (fun θ' => F i z θ') := by
    funext θ'; rw [Finset.sum_apply]
  rw [hfun, deriv_sum (fun i hi => h i hi), Finset.mul_sum]

/-- The `θ`-slice of a `SmoothNbhd` function is `C^n` at every point of `nbhU`. -/
theorem WtoW_g_theta_slice_contDiffAt {f : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd f) (n : ℕ∞)
    {z θ : ℝ} (hy : (z, θ) ∈ Work.Spaces.nbhU) : ContDiffAt ℝ n (fun θ' => f z θ') θ := by
  have h1 : ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ) :=
    h.contDiffAt (Work.Spaces.isOpen_nbhU.mem_nhds hy)
  have h2 : ContDiffAt ℝ ⊤ (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  have h3 : ContDiffAt ℝ ⊤ (fun θ' : ℝ => f z θ') θ := by
    have h1' : ContDiffAt ℝ ⊤ ((fun p : ℝ × ℝ => f p.1 p.2) ∘ (fun θ' : ℝ => (z, θ'))) θ :=
      h1.comp θ h2
    simpa [Function.comp_def] using h1'
  exact h3.of_le le_top

/-- The `z`-slice of a `SmoothNbhd` function is `C^n` at every point of the quadrant. -/
theorem WtoW_g_z_slice_contDiffAt {f : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd f) (n : ℕ∞)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    ContDiffAt ℝ n (fun z' => f z' θ) z :=
  (Work.Spaces.SmoothInt.contDiffAt_z_slice (WtoW_SmoothInt h) hz hθ).of_le le_top

/-- **Congruence of `D_θ` for the `θ`-slices at a fixed `z`.** -/
theorem WtoW_g_Dth_congr {u v : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ θ' : ℝ, (z, θ') ∈ Work.Spaces.nbhU → u z θ' = v z θ')
    (hy : (z, θ) ∈ Work.Spaces.nbhU) :
    Work.Spaces.Dth u z θ = Work.Spaces.Dth v z θ := by
  show Real.sin (2 * θ) * deriv (fun θ' => u z θ') θ
      = Real.sin (2 * θ) * deriv (fun θ' => v z θ') θ
  congr 1
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ Work.Spaces.nbhU :=
    (Continuous.prodMk_right z).continuousAt.eventually
      (Work.Spaces.isOpen_nbhU.mem_nhds hy)
  have heq : (fun θ' => u z θ') =ᶠ[𝓝 θ] (fun θ' => v z θ') :=
    hnb.mono fun θ' hθ' => h θ' hθ'
  exact heq.deriv_eq

/-- **Shift of a finite sum.**  `Σ_{i<n} c_i e_{i+1} = Σ_{j<n+1} (j=0 ? 0 : c_{j-1}) e_j`. -/
theorem WtoW_g_sum_range_shift (n : ℕ) (c : ℕ → ℝ) (e : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, c i * e (i + 1))
      = ∑ j ∈ Finset.range (n + 1), (if j = 0 then 0 else c (j - 1)) * e j := by
  induction n with
  | zero => simp
  | succ n ih =>
      conv_rhs => rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ, ih]
      simp

/-- **Extension of a finite sum.**  `Σ_{i<n} f i = Σ_{j<n+1} (j=n ? 0 : f j)`. -/
theorem WtoW_g_sum_range_ext (n : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, f i) = ∑ j ∈ Finset.range (n + 1), (if j = n then 0 else f j) := by
  conv_rhs => rw [Finset.sum_range_succ]
  rw [if_pos rfl, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [if_neg (by omega)]

/-! ## The coefficients vanish above the diagonal -/

theorem WtoW_AB_gt : ∀ q j : ℕ, q < j → WtoW_AB q j = (0, 0) := by
  intro q
  refine Nat.strong_induction_on q ?_
  intro n ih j hj
  rcases n with _ | n
  · have hj0 : j ≠ 0 := by omega
    simp [WtoW_AB, hj0]
  · have h1 : WtoW_AB n (j - 1) = (0, 0) := ih n (by omega) (j - 1) (by omega)
    have h2 : WtoW_AB n j = (0, 0) := ih n (by omega) j (by omega)
    have hj0 : j ≠ 0 := by omega
    simp [WtoW_AB, hj0, h1, h2]

/-- The coefficient `c_{q,j}` vanishes identically for `j > q`. -/
theorem WtoW_g_coeff_gt (q j : ℕ) (h : q < j) : WtoW_ccoeff q j = fun _ => 0 := by
  have hAB := WtoW_AB_gt q j h
  funext θ
  simp [WtoW_ccoeff, WtoW_cA, WtoW_cB, hAB]

/-! ## The algebraic core of the induction step -/

/-- **The algebraic step of the identity.**  If the coefficients satisfy the recurrence of
`WtoW_g_coeff_rec` and `c_{q,q+1} = 0`, then the expression produced by differentiating
`sin(2θ)·D_θ^q(∂_θ g) = Σ_i c_{q,i}D_θ^{i+1}g` once more equals `Σ_j c_{q+1,j} e_j`. -/
theorem WtoW_g_alg (q : ℕ) (θ X : ℝ) (e : ℕ → ℝ)
    (hrec : ∀ j : ℕ, WtoW_ccoeff (q + 1) j θ
      = Real.sin (2 * θ) * deriv (WtoW_ccoeff q j) θ - X * WtoW_ccoeff q j θ
        + (if j = 0 then 0 else WtoW_ccoeff q (j - 1) θ))
    (hvan : WtoW_ccoeff q (q + 1) = fun _ => 0) :
    (∑ i ∈ Finset.range (q + 1),
        (WtoW_ccoeff q i θ * e (i + 1)
          + (Real.sin (2 * θ) * deriv (WtoW_ccoeff q i) θ) * e i))
      - X * (∑ i ∈ Finset.range (q + 1), WtoW_ccoeff q i θ * e i)
    = ∑ j ∈ Finset.range (q + 2), WtoW_ccoeff (q + 1) j θ * e j := by
  have hzero : WtoW_ccoeff q (q + 1) θ = 0 := by rw [hvan]
  have hderiv0 : deriv (WtoW_ccoeff q (q + 1)) θ = 0 := by
    rw [hvan]; simp only [deriv_const]
  -- (1) the right hand side as a single sum of the common coefficient shape
  have hR : (∑ j ∈ Finset.range (q + 2), WtoW_ccoeff (q + 1) j θ * e j)
      = ∑ j ∈ Finset.range (q + 2),
          (((if j = 0 then 0 else WtoW_ccoeff q (j - 1) θ)
            + Real.sin (2 * θ) * deriv (WtoW_ccoeff q j) θ - X * WtoW_ccoeff q j θ) * e j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hrec j]; ring
  -- (2) the left hand side
  have hshift : (∑ i ∈ Finset.range (q + 1), WtoW_ccoeff q i θ * e (i + 1))
      = ∑ j ∈ Finset.range (q + 2),
          (if j = 0 then 0 else WtoW_ccoeff q (j - 1) θ) * e j :=
    WtoW_g_sum_range_shift (q + 1) (fun i => WtoW_ccoeff q i θ) e
  have hmul : X * (∑ i ∈ Finset.range (q + 1), WtoW_ccoeff q i θ * e i)
      = ∑ i ∈ Finset.range (q + 1), (X * WtoW_ccoeff q i θ) * e i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hext : (∑ i ∈ Finset.range (q + 1),
        ((Real.sin (2 * θ) * deriv (WtoW_ccoeff q i) θ) * e i))
      - (∑ i ∈ Finset.range (q + 1), (X * WtoW_ccoeff q i θ) * e i)
      = ∑ j ∈ Finset.range (q + 2),
          (if j = q + 1 then 0
            else ((Real.sin (2 * θ) * deriv (WtoW_ccoeff q j) θ) * e j
              - (X * WtoW_ccoeff q j θ) * e j)) := by
    rw [← Finset.sum_sub_distrib]
    exact WtoW_g_sum_range_ext (q + 1)
      (fun i => (Real.sin (2 * θ) * deriv (WtoW_ccoeff q i) θ) * e i
        - (X * WtoW_ccoeff q i θ) * e i)
  have hL : (∑ i ∈ Finset.range (q + 1),
        (WtoW_ccoeff q i θ * e (i + 1)
          + (Real.sin (2 * θ) * deriv (WtoW_ccoeff q i) θ) * e i))
      - X * (∑ i ∈ Finset.range (q + 1), WtoW_ccoeff q i θ * e i)
      = ∑ j ∈ Finset.range (q + 2),
          (((if j = 0 then 0 else WtoW_ccoeff q (j - 1) θ)
            + Real.sin (2 * θ) * deriv (WtoW_ccoeff q j) θ - X * WtoW_ccoeff q j θ) * e j) := by
    rw [Finset.sum_add_distrib, hmul,
      show (∑ i ∈ Finset.range (q + 1), WtoW_ccoeff q i θ * e (i + 1))
            + (∑ i ∈ Finset.range (q + 1),
                (Real.sin (2 * θ) * deriv (WtoW_ccoeff q i) θ) * e i)
            - (∑ i ∈ Finset.range (q + 1), (X * WtoW_ccoeff q i θ) * e i)
          = (∑ i ∈ Finset.range (q + 1), WtoW_ccoeff q i θ * e (i + 1))
            + ((∑ i ∈ Finset.range (q + 1),
                (Real.sin (2 * θ) * deriv (WtoW_ccoeff q i) θ) * e i)
              - (∑ i ∈ Finset.range (q + 1), (X * WtoW_ccoeff q i θ) * e i))
        from by ring]
    rw [hshift, hext, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    by_cases hjq : j = q + 1
    · subst hjq
      rw [if_pos rfl, hzero, hderiv0]
      ring
    · rw [if_neg hjq]
      ring
  rw [hL, hR]

/-! ## The identity `sin(2θ) D_θ^q(∂_θ g) = Σ_j c_{q,j} D_θ^{j+1} g` -/

theorem WtoW_g_ident : ∀ q : ℕ, ∀ g : ℝ → ℝ → ℝ, Work.Spaces.SmoothNbhd g →
    ∀ z θ : ℝ, (z, θ) ∈ Work.Spaces.nbhU →
      Real.sin (2 * θ) * Work.Spaces.DthIter q (Work.Spaces.pth g) z θ
        = ∑ i ∈ Finset.range (q + 1),
            WtoW_ccoeff q i θ * Work.Spaces.DthIter (i + 1) g z θ := by
  intro q
  induction q with
  | zero =>
      intro g hg z θ hy
      rw [Finset.sum_range_one]
      simp [WtoW_ccoeff_zero_zero, Work.Spaces.DthIter_succ, Work.Spaces.Dth,
        Work.Spaces.pth]
  | succ q ih =>
      intro g hg z θ hy
      have hIH : ∀ θ' : ℝ, (z, θ') ∈ Work.Spaces.nbhU →
          Real.sin (2 * θ') * Work.Spaces.DthIter q (Work.Spaces.pth g) z θ'
            = ∑ i ∈ Finset.range (q + 1),
                WtoW_ccoeff q i θ' * Work.Spaces.DthIter (i + 1) g z θ' :=
        fun θ' hθ' => ih g hg z θ' hθ'
      have hFSθ := hIH θ hy
      have hDth_eq := WtoW_g_Dth_congr
        (u := fun z' θ' => Real.sin (2 * θ') * Work.Spaces.DthIter q (Work.Spaces.pth g) z' θ')
        (v := fun z' θ' => ∑ i ∈ Finset.range (q + 1),
            WtoW_ccoeff q i θ' * Work.Spaces.DthIter (i + 1) g z' θ') hIH hy
      have hdiff_sf : DifferentiableAt ℝ (fun θ : ℝ => Real.sin (2 * θ)) θ :=
        (WtoW_hasDerivAt_sin_two θ).differentiableAt
      have hdiff_h : DifferentiableAt ℝ
          (fun θ' => Work.Spaces.DthIter q (Work.Spaces.pth g) z θ') θ :=
        (WtoW_g_theta_slice_contDiffAt
          (Work.Spaces.SmoothNbhd.DthIter (Work.Spaces.SmoothNbhd.pth hg) q) ⊤ hy).differentiableAt
          (by simp)
      have hpr := WtoW_Dth_mul_theta (fun θ : ℝ => Real.sin (2 * θ))
        (Work.Spaces.DthIter q (Work.Spaces.pth g)) hdiff_sf hdiff_h
      have hkey : Real.sin (2 * θ) * Work.Spaces.DthIter (q + 1) (Work.Spaces.pth g) z θ
          = Work.Spaces.Dth
              (fun z θ => ∑ i ∈ Finset.range (q + 1),
                WtoW_ccoeff q i θ * Work.Spaces.DthIter (i + 1) g z θ) z θ
            - WtoW_X θ * (∑ i ∈ Finset.range (q + 1),
                WtoW_ccoeff q i θ * Work.Spaces.DthIter (i + 1) g z θ) := by
        rw [← hDth_eq, hpr, ← Work.Spaces.DthIter_succ, WtoW_deriv_sin_two, ← hFSθ]
        ring
      have hDthS : Work.Spaces.Dth
            (fun z θ => ∑ i ∈ Finset.range (q + 1),
              WtoW_ccoeff q i θ * Work.Spaces.DthIter (i + 1) g z θ) z θ
          = ∑ i ∈ Finset.range (q + 1),
              (WtoW_ccoeff q i θ * Work.Spaces.DthIter (i + 2) g z θ
                + (Real.sin (2 * θ) * deriv (WtoW_ccoeff q i) θ)
                    * Work.Spaces.DthIter (i + 1) g z θ) := by
        rw [WtoW_g_Dth_sum (Finset.range (q + 1))
          (fun i z θ => WtoW_ccoeff q i θ * Work.Spaces.DthIter (i + 1) g z θ)
          (fun i hi =>
            ((WtoW_hasDerivAt_ccoeff q i θ).differentiableAt).mul
              ((WtoW_g_theta_slice_contDiffAt
                (Work.Spaces.SmoothNbhd.DthIter hg (i + 1)) ⊤ hy).differentiableAt (by simp)))]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [WtoW_Dth_mul_theta (WtoW_ccoeff q i) (Work.Spaces.DthIter (i + 1) g)
          ((WtoW_hasDerivAt_ccoeff q i θ).differentiableAt)
          ((WtoW_g_theta_slice_contDiffAt
            (Work.Spaces.SmoothNbhd.DthIter hg (i + 1)) ⊤ hy).differentiableAt (by simp))]
        simp only [Work.Spaces.DthIter_succ]
      rw [hkey, hDthS]
      exact WtoW_g_alg q θ (WtoW_X θ) (fun j => Work.Spaces.DthIter (j + 1) g z θ)
        (fun j => WtoW_g_coeff_rec q j θ)
        (WtoW_g_coeff_gt q (q + 1) (by omega))

/-! ## Pushing `∂_z^m` through the identity -/

/-- `pzIter` only sees the `θ`-slice at the fixed angle: a function that ignores its second
argument may be replaced by the function it is a slice of. -/
theorem WtoW_g_slice_pzIter (m : ℕ) (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter m (fun z' _ => u z' θ) z θ = Work.Spaces.pzIter m u z θ :=
  pzIter_congr_nhds m (Filter.Eventually.of_forall fun z' => rfl)

/-! ## The final estimate -/

theorem WtoW_g_bound : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.SmoothNbhd g → Work.Spaces.WlInfMem α 5 g →
    ∀ (m q : ℕ), m + q ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ m * Work.Spaces.pzIter m (Work.Spaces.DthIter q (Work.Spaces.pth g)) z θ|
          * Real.sin (2 * θ)
        ≤ K * Work.Spaces.WlInf α 5 g * (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
  refine ⟨10000, by norm_num, ?_⟩
  intro α g hα hα1 hg hmem m q hmq z hz θ hθ
  have hy : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hz hθ
  have hznn : (0 : ℝ) ≤ z := hz
  have hzpnn : (0 : ℝ) ≤ (z + 1) ^ m := pow_nonneg (by linarith) m
  have hzpm : 0 < (z + 1) ^ m := pow_pos (by linarith) m
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ Work.Spaces.nbhU :=
    (Continuous.prodMk_left θ).continuousAt.eventually
      (Work.Spaces.isOpen_nbhU.mem_nhds hy)
  have hWnn : 0 ≤ Work.Spaces.WlInf α 5 g := Work.Spaces.WlInf_nonneg α 5 g hmem
  have hs0 : 0 ≤ Real.sin (2 * θ) := WtoW_sin2_nonneg hθ
  have hspow : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hs0 _
  have hαs : 0 ≤ α + Real.sin (2 * θ) := by linarith
  -- the pointwise consequence of `WlInfMem α 5 g`
  have hterm : ∀ i ≤ q, (z + 1) ^ m * |Work.Spaces.pzIter m (Work.Spaces.DthIter (i + 1) g) z θ|
      ≤ Work.Spaces.WlInf α 5 g * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    intro i hi
    have hb := Work.Spaces.pz_Dth_sup_bound α hα 5 g hmem (i + 1) m (by omega) (by omega) z θ hz hθ
    have h2 : Work.Spaces.WlInf α 5 g / (z + 1) ^ m
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * (z + 1) ^ m
        = Work.Spaces.WlInf α 5 g * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
      field_simp
    calc (z + 1) ^ m * |Work.Spaces.pzIter m (Work.Spaces.DthIter (i + 1) g) z θ|
        = |Work.Spaces.pzIter m (Work.Spaces.DthIter (i + 1) g) z θ| * (z + 1) ^ m := by ring
      _ ≤ Work.Spaces.WlInf α 5 g / (z + 1) ^ m
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * (z + 1) ^ m :=
          mul_le_mul_of_nonneg_right hb (le_of_lt hzpm)
      _ = Work.Spaces.WlInf α 5 g * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := h2
  -- the identity, differentiated `m` times in `z`
  have hA : Real.sin (2 * θ) * Work.Spaces.pzIter m (Work.Spaces.DthIter q (Work.Spaces.pth g)) z θ
      = Work.Spaces.pzIter m (fun z θ' => ∑ i ∈ Finset.range (q + 1),
          WtoW_ccoeff q i θ' * Work.Spaces.DthIter (i + 1) g z θ') z θ := by
    rw [← WtoW_g_slice_pzIter m (Work.Spaces.DthIter q (Work.Spaces.pth g)) z θ]
    rw [← WtoW_pzIter_mul_theta m (fun _ => Real.sin (2 * θ))
      (fun z' _ => Work.Spaces.DthIter q (Work.Spaces.pth g) z' θ) z θ]
    have h1 : Work.Spaces.pzIter m (fun z θ' => Real.sin (2 * θ)
          * (fun z' _ => Work.Spaces.DthIter q (Work.Spaces.pth g) z' θ) z θ') z θ
        = Work.Spaces.pzIter m (fun z θ' => Real.sin (2 * θ')
            * Work.Spaces.DthIter q (Work.Spaces.pth g) z θ') z θ :=
      pzIter_congr_nhds m (Filter.Eventually.of_forall fun z' => rfl)
    rw [h1]
    exact pzIter_congr_nhds m (by
      filter_upwards [hnb] with z' hz'
      exact WtoW_g_ident q g hg z' θ hz')
  have hB : Work.Spaces.pzIter m (fun z θ' => ∑ i ∈ Finset.range (q + 1),
        WtoW_ccoeff q i θ' * Work.Spaces.DthIter (i + 1) g z θ') z θ
      = ∑ i ∈ Finset.range (q + 1),
          WtoW_ccoeff q i θ * Work.Spaces.pzIter m (Work.Spaces.DthIter (i + 1) g) z θ :=
    WtoW_pzIter_sum_theta (Finset.range (q + 1)) (fun i θ' => WtoW_ccoeff q i θ')
      (fun i => Work.Spaces.DthIter (i + 1) g) m
      (fun i _ => WtoW_g_z_slice_contDiffAt (Work.Spaces.SmoothNbhd.DthIter hg (i + 1))
        (m : ℕ∞) hz hθ)
  have hmain : Real.sin (2 * θ) * Work.Spaces.pzIter m (Work.Spaces.DthIter q (Work.Spaces.pth g)) z θ
      = ∑ i ∈ Finset.range (q + 1),
          WtoW_ccoeff q i θ * Work.Spaces.pzIter m (Work.Spaces.DthIter (i + 1) g) z θ := by
    rw [hA, hB]
  -- the arithmetic of the constant
  have harith : (q + 1 : ℝ)
        * ((3 * (5 : ℝ) ^ q)
          * (Work.Spaces.WlInf α 5 g * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
      ≤ 10000 * (Work.Spaces.WlInf α 5 g
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
    have hq : q ≤ 4 := by omega
    have hq1 : (q + 1 : ℝ) ≤ 5 := by
      have : (q : ℝ) ≤ 4 := by exact_mod_cast hq
      linarith
    have h5q : (5 : ℝ) ^ q ≤ 5 ^ 4 := pow_le_pow_right₀ (by norm_num) hq
    have hXnn : 0 ≤ Work.Spaces.WlInf α 5 g
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
      mul_nonneg hWnn (mul_nonneg hαs hspow)
    have hcoef : (q + 1 : ℝ) * (3 * (5 : ℝ) ^ q) ≤ 10000 := by
      have := mul_le_mul hq1 (by linarith : (3 : ℝ) * 5 ^ q ≤ 3 * 5 ^ 4) (by positivity) (by norm_num)
      linarith [this]
    nlinarith [hcoef, hXnn]
  calc |(z + 1) ^ m * Work.Spaces.pzIter m (Work.Spaces.DthIter q (Work.Spaces.pth g)) z θ|
        * Real.sin (2 * θ)
      = |(z + 1) ^ m * (Real.sin (2 * θ)
          * Work.Spaces.pzIter m (Work.Spaces.DthIter q (Work.Spaces.pth g)) z θ)| := by
        simp only [abs_mul, abs_of_nonneg hs0, abs_of_nonneg hzpnn]
        ring
    _ = |(z + 1) ^ m * (∑ i ∈ Finset.range (q + 1),
          WtoW_ccoeff q i θ * Work.Spaces.pzIter m (Work.Spaces.DthIter (i + 1) g) z θ)| := by
        rw [hmain]
    _ ≤ (z + 1) ^ m * (∑ i ∈ Finset.range (q + 1),
          |WtoW_ccoeff q i θ| * |Work.Spaces.pzIter m (Work.Spaces.DthIter (i + 1) g) z θ|) := by
        rw [abs_mul, abs_of_nonneg hzpnn]
        refine mul_le_mul_of_nonneg_left ?_ (hzpnn)
        calc |∑ i ∈ Finset.range (q + 1),
              WtoW_ccoeff q i θ * Work.Spaces.pzIter m (Work.Spaces.DthIter (i + 1) g) z θ|
            ≤ ∑ i ∈ Finset.range (q + 1),
                |WtoW_ccoeff q i θ * Work.Spaces.pzIter m (Work.Spaces.DthIter (i + 1) g) z θ| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i ∈ Finset.range (q + 1),
                |WtoW_ccoeff q i θ| * |Work.Spaces.pzIter m (Work.Spaces.DthIter (i + 1) g) z θ| := by
              refine Finset.sum_congr rfl fun i hi => ?_
              rw [abs_mul]
    _ = ∑ i ∈ Finset.range (q + 1), (z + 1) ^ m
          * (|WtoW_ccoeff q i θ| * |Work.Spaces.pzIter m (Work.Spaces.DthIter (i + 1) g) z θ|) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (q + 1), (3 * (5 : ℝ) ^ q)
          * (Work.Spaces.WlInf α 5 g * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi_le : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        calc (z + 1) ^ m
              * (|WtoW_ccoeff q i θ| * |Work.Spaces.pzIter m (Work.Spaces.DthIter (i + 1) g) z θ|)
            = |WtoW_ccoeff q i θ|
                * ((z + 1) ^ m * |Work.Spaces.pzIter m (Work.Spaces.DthIter (i + 1) g) z θ|) := by ring
          _ ≤ (3 * (5 : ℝ) ^ q)
                * (Work.Spaces.WlInf α 5 g
                  * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
              mul_le_mul (WtoW_g_coeff_bound q i θ) (hterm i hi_le) (by positivity) (by positivity)
    _ = (q + 1 : ℝ)
          * ((3 * (5 : ℝ) ^ q)
            * (Work.Spaces.WlInf α 5 g
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 10000 * (Work.Spaces.WlInf α 5 g
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := harith
    _ = 10000 * Work.Spaces.WlInf α 5 g * (α + Real.sin (2 * θ))
          * (Real.sin (2 * θ)) ^ (α / 5) := by ring

end Work.Elliptic
