import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.UopHk.L12_contDiffOn_reg
import Submission.Work.FTS.EllipticEst.UopHk.removingL12Honest
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.DzIter_mul_of_radial
import Submission.Work.FTS.EllipticEst.DthIter_mul_of_angular
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.ThetaSliceIdent
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Slice data for the residual `EllResid α F Ψ` in the interior class `EllHypQ`

`Work.Elliptic.EllResid α F Ψ = Ψ - (1/(4α)) sin 2θ · L₁₂(F)` is a `C^∞` function of `θ` minus a
*radial* factor `κ(z) = -(1/(4α)) L₁₂(F)(z)` times the *angular* factor `sin 2θ`.  In the
interior class `EllHypQ` the radial factor is only known to be `C^k` on `(0,∞)`, so the residual
is *not* `C^∞` on the open quadrant; nevertheless every slice `θ ↦ D_z^j (EllResid α F Ψ) z θ`
with `j ≤ k` is `C^∞` on `(0,π/2)` (the `θ`-smoothness comes from `Ψ` alone), continuous on the
closed `Iθ` and vanishes at both endpoints.  All four pointwise identities relating the
`θ`-derivatives of the slice to the mixed operators `D_z^j D_θ^i (∂_θ^r …)` follow from the same
decomposition, the `Ψ`-half being Clairaut on the open quadrant and the radial ⊗ angular half
being an unconditional computation.

Everything here is `sorry`-free.
-/

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

noncomputable section

namespace Work.FTS.EllipticEst.UopHk

/-! ## Additivity of the operators along a sum -/

/-- `D_z^j` is additive on the slices, provided the slices of the summands of all lower orders
are differentiable in `z`. -/
theorem DzIter_add_of_diffOn (f g : ℝ → ℝ → ℝ) (j : ℕ) (θ : ℝ)
    (hf : ∀ m < j, DifferentiableOn ℝ (fun z => Work.Spaces.DzIter m f z θ) (Set.Ioi 0))
    (hg : ∀ m < j, DifferentiableOn ℝ (fun z => Work.Spaces.DzIter m g z θ) (Set.Ioi 0)) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.DzIter j (f + g) z θ
        = Work.Spaces.DzIter j f z θ + Work.Spaces.DzIter j g z θ := by
  induction j with
  | zero => intro z hz; rfl
  | succ j ih =>
      intro z hz
      have hF : DifferentiableOn ℝ (fun z => Work.Spaces.DzIter j f z θ) (Set.Ioi 0) :=
        hf j (Nat.lt_succ_self j)
      have hG : DifferentiableOn ℝ (fun z => Work.Spaces.DzIter j g z θ) (Set.Ioi 0) :=
        hg j (Nat.lt_succ_self j)
      have ihf := ih (fun m hm => hf m (Nat.lt_trans hm (Nat.lt_succ_self j)))
        (fun m hm => hg m (Nat.lt_trans hm (Nat.lt_succ_self j)))
      rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ]
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      have hev : (fun z' => Work.Spaces.DzIter j (f + g) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter j f z' θ + Work.Spaces.DzIter j g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz''
        exact ihf z' hz''
      rw [hev.deriv_eq]
      rw [show deriv (fun z' => Work.Spaces.DzIter j f z' θ + Work.Spaces.DzIter j g z' θ) z
          = deriv ((fun z' => Work.Spaces.DzIter j f z' θ)
              + fun z' => Work.Spaces.DzIter j g z' θ) z from rfl]
      rw [deriv_add (hF.differentiableAt (isOpen_Ioi.mem_nhds hz))
        (hG.differentiableAt (isOpen_Ioi.mem_nhds hz))]
      ring

/-- `D_θ^i` is additive on the slices, provided the slices of the summands of all lower orders
are differentiable in `θ`. -/
theorem DthIter_add_of_diffOn (f g : ℝ → ℝ → ℝ) (i : ℕ) (z : ℝ)
    (hf : ∀ m < i, DifferentiableOn ℝ (fun θ => Work.Spaces.DthIter m f z θ)
      (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ m < i, DifferentiableOn ℝ (fun θ => Work.Spaces.DthIter m g z θ)
      (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.DthIter i (f + g) z θ
        = Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => intro θ hθ; rfl
  | succ i ih =>
      intro θ hθ
      have hF : DifferentiableOn ℝ (fun θ => Work.Spaces.DthIter i f z θ)
          (Set.Ioo 0 (Real.pi / 2)) := hf i (Nat.lt_succ_self i)
      have hG : DifferentiableOn ℝ (fun θ => Work.Spaces.DthIter i g z θ)
          (Set.Ioo 0 (Real.pi / 2)) := hg i (Nat.lt_succ_self i)
      have ihi := ih (fun m hm => hf m (Nat.lt_trans hm (Nat.lt_succ_self i)))
        (fun m hm => hg m (Nat.lt_trans hm (Nat.lt_succ_self i)))
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ]
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      have hev : (fun θ' => Work.Spaces.DthIter i (f + g) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter i f z θ' + Work.Spaces.DthIter i g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ihi θ' hθ'
      rw [hev.deriv_eq]
      rw [show deriv (fun θ' => Work.Spaces.DthIter i f z θ' + Work.Spaces.DthIter i g z θ') θ
          = deriv ((fun θ' => Work.Spaces.DthIter i f z θ')
              + fun θ' => Work.Spaces.DthIter i g z θ') θ from rfl]
      rw [deriv_add (hF.differentiableAt (isOpen_Ioo.mem_nhds hθ))
        (hG.differentiableAt (isOpen_Ioo.mem_nhds hθ))]
      ring

/-- `∂_θ^n` is additive on the slices, provided the slices of the summands of all lower orders
are differentiable in `θ`. -/
theorem pthIter_add_of_diffOn (f g : ℝ → ℝ → ℝ) (n : ℕ) (z : ℝ)
    (hf : ∀ m < n, DifferentiableOn ℝ (fun θ => Work.Spaces.pthIter m f z θ)
      (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ m < n, DifferentiableOn ℝ (fun θ => Work.Spaces.pthIter m g z θ)
      (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pthIter n (f + g) z θ
        = Work.Spaces.pthIter n f z θ + Work.Spaces.pthIter n g z θ := by
  induction n with
  | zero => intro θ hθ; rfl
  | succ n ih =>
      intro θ hθ
      have hF : DifferentiableOn ℝ (fun θ => Work.Spaces.pthIter n f z θ)
          (Set.Ioo 0 (Real.pi / 2)) := hf n (Nat.lt_succ_self n)
      have hG : DifferentiableOn ℝ (fun θ => Work.Spaces.pthIter n g z θ)
          (Set.Ioo 0 (Real.pi / 2)) := hg n (Nat.lt_succ_self n)
      have ihi := ih (fun m hm => hf m (Nat.lt_trans hm (Nat.lt_succ_self n)))
        (fun m hm => hg m (Nat.lt_trans hm (Nat.lt_succ_self n)))
      rw [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ]
      simp only [Work.Spaces.pth]
      have hev : (fun θ' => Work.Spaces.pthIter n (f + g) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pthIter n f z θ' + Work.Spaces.pthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ihi θ' hθ'
      rw [hev.deriv_eq]
      rw [show deriv (fun θ' => Work.Spaces.pthIter n f z θ' + Work.Spaces.pthIter n g z θ') θ
          = deriv ((fun θ' => Work.Spaces.pthIter n f z θ')
              + fun θ' => Work.Spaces.pthIter n g z θ') θ from rfl]
      rw [deriv_add (hF.differentiableAt (isOpen_Ioo.mem_nhds hθ))
        (hG.differentiableAt (isOpen_Ioo.mem_nhds hθ))]

/-- The plain angular derivative is additive at a point where both slices are differentiable. -/
theorem pth_add_of_diff (f g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hf : DifferentiableAt ℝ (fun θ' => f z θ') θ)
    (hg : DifferentiableAt ℝ (fun θ' => g z θ') θ) :
    Work.Spaces.pth (f + g) z θ = Work.Spaces.pth f z θ + Work.Spaces.pth g z θ := by
  simp only [Work.Spaces.pth, Pi.add_apply]
  rw [show deriv (fun θ' => f z θ' + g z θ') θ
      = deriv ((fun θ' => f z θ') + fun θ' => g z θ') θ from rfl]
  rw [deriv_add hf hg]

/-- `D_z^j` only sees the values of the function at the fixed angle `θ`. -/
theorem DzIter_eq_of_eqOn_slice (f g : ℝ → ℝ → ℝ) (θ : ℝ)
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), f z θ = g z θ) :
    ∀ j : ℕ, ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.DzIter j f z θ = Work.Spaces.DzIter j g z θ := by
  intro j
  induction j with
  | zero => intro z hz; exact h z hz
  | succ j ih =>
      intro z hz
      rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.Dz]
      simp only [Work.Spaces.pz]
      have hev : (fun z' => Work.Spaces.DzIter j f z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter j g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' hz'
      rw [hev.deriv_eq]

/-! ## The iterated radial operator on a one-variable function -/

/-- `rDzIter m g` inherits the smoothness of `g`, losing one order per iteration. -/
theorem contDiffOn_rDzIter {κ : ℝ → ℝ} {k : ℕ}
    (hκ : ContDiffOn ℝ (k : ℕ∞ω) κ (Set.Ioi 0)) :
    ∀ m : ℕ, m ≤ k →
      ContDiffOn ℝ ((k - m : ℕ) : ℕ∞ω) (Work.FTS.EllipticEst.rDzIter m κ) (Set.Ioi 0) := by
  intro m
  induction m with
  | zero => intro _; simpa using hκ
  | succ m ih =>
      intro hm
      have hmk : m ≤ k := by omega
      have hlt : m < k := by omega
      have hprev : ContDiffOn ℝ ((k - m : ℕ) : ℕ∞ω)
          (Work.FTS.EllipticEst.rDzIter m κ) (Set.Ioi 0) := ih hmk
      have hcast : ((k - (m + 1) : ℕ) : ℕ∞ω) + 1 ≤ ((k - m : ℕ) : ℕ∞ω) := by
        have h1 : k - (m + 1) + 1 = k - m := by omega
        rw [← h1, Nat.cast_add, Nat.cast_one]
      have hder : ContDiffOn ℝ ((k - (m + 1) : ℕ) : ℕ∞ω)
          (deriv (Work.FTS.EllipticEst.rDzIter m κ)) (Set.Ioi 0) :=
        hprev.deriv_of_isOpen isOpen_Ioi hcast
      have hmul : ContDiffOn ℝ ((k - (m + 1) : ℕ) : ℕ∞ω)
          (fun z => z * deriv (Work.FTS.EllipticEst.rDzIter m κ) z) (Set.Ioi 0) :=
        contDiffOn_id.mul hder
      rw [Work.FTS.EllipticEst.rDzIter_succ]
      exact hmul

/-- `rDzIter m κ` is differentiable on `(0,∞)` as soon as `m < k` and `κ` is `C^k` there. -/
theorem differentiableOn_rDzIter {κ : ℝ → ℝ} {k : ℕ}
    (hκ : ContDiffOn ℝ (k : ℕ∞ω) κ (Set.Ioi 0)) {m : ℕ} (hm : m < k) :
    DifferentiableOn ℝ (Work.FTS.EllipticEst.rDzIter m κ) (Set.Ioi 0) := by
  have h := contDiffOn_rDzIter hκ m (le_of_lt hm)
  have hne : ((k - m : ℕ) : ℕ∞ω) ≠ 0 := by
    have : 0 < k - m := by omega
    exact_mod_cast (Nat.pos_iff_ne_zero.mp this)
  exact h.differentiableOn hne

/-! ## The boundary limits of the slices of a `RegQ` datum -/

/-- **A datum of the interior class `RegQ` has vanishing slice limits at both angular
endpoints.**  This is the structural content of `BdryTraces`: the trace
`sin(2θ)^{1-γ} f(z,θ)² → 0` together with `1 - γ = -α/10 < 0` forces `f(z,θ) → 0`. -/
theorem tendsto_DzIter_slice_zero {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hreg : Work.FTS.Nonlin.RegQ α k f) {j : ℕ} (hj : j ≤ k) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun θ => Work.Spaces.DzIter j f z θ) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun θ => Work.Spaces.DzIter j f z θ) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hgam : (1 : ℝ) - Work.Spaces.gam α < 0 := by
    rw [show Work.Spaces.gam α = 1 + α / 10 from rfl]; linarith
  have hpair := (hreg.2.2 0 j (by omega)).2 z hz
  have hevR : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Set.Ioo 0 (π / 2) := by
    refine inter_mem self_mem_nhdsWithin ?_
    exact (Filter.le_def.mp nhdsWithin_le_nhds) (Set.Iio (π / 2))
      (Iio_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2))
  have hevL : ∀ᶠ θ in 𝓝[<] (π / 2), θ ∈ Set.Ioo 0 (π / 2) := by
    refine inter_mem ?_ self_mem_nhdsWithin
    exact (Filter.le_def.mp nhdsWithin_le_nhds) (Set.Ioi (0 : ℝ))
      (Ioi_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2))
  have key : ∀ {l : Filter ℝ} (hl : ∀ᶠ θ in l, θ ∈ Set.Ioo 0 (π / 2)),
      Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.DzIter j f z θ) ^ 2) l (𝓝 0) →
      Tendsto (fun θ => Work.Spaces.DzIter j f z θ) l (𝓝 0) := by
    intro l hl hB
    have hsq : Tendsto (fun θ => (Work.Spaces.DzIter j f z θ) ^ 2) l (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun θ => sq_nonneg _) ?_ hB
      filter_upwards [hl] with θ hθ
      have hs : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
      have hle : 1 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hs (Real.sin_le_one (2 * θ)) (le_of_lt hgam)
        simpa using h
      nlinarith [sq_nonneg (Work.Spaces.DzIter j f z θ)]
    have hroot : Tendsto (fun θ => |Work.Spaces.DzIter j f z θ|) l (𝓝 0) := by
      have h := hsq.sqrt
      simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] using h
    exact (tendsto_zero_iff_norm_tendsto_zero).mpr (by simpa using hroot)
  exact ⟨key hevR hpair.1, key hevL hpair.2⟩

/-! ## The angular profiles `sin 2θ`, `2cos 2θ`, `-4 sin 2θ` -/

theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
  simpa [Function.comp_def, mul_comm] using
    (Real.hasDerivAt_sin (2 * θ)).comp θ
      ((hasDerivAt_const (x := θ) (c := (2 : ℝ))).mul (hasDerivAt_id θ))

theorem deriv_sin_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) :=
  (hasDerivAt_sin_two θ).deriv

theorem deriv_two_cos_two (θ : ℝ) :
    deriv (fun θ' : ℝ => 2 * Real.cos (2 * θ')) θ = -(4 * Real.sin (2 * θ)) := by
  have h1 : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-(2 * Real.sin (2 * θ))) θ := by
    simpa [Function.comp_def, mul_comm, mul_assoc] using
      (Real.hasDerivAt_cos (2 * θ)).comp θ
        ((hasDerivAt_const (x := θ) (c := (2 : ℝ))).mul (hasDerivAt_id θ))
  have h2 := h1.const_mul (2 : ℝ)
  rw [h2.deriv]
  ring

/-! ## The singular part of the residual as a radial ⊗ angular product -/

/-- `κ(z) = -(1/(4α)) L₁₂(F)(z)`: the radial factor of the singular term of `EllResid`. -/
def singKappa (α : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => -(1 / (4 * α)) * Work.Elliptic.L12 F z

/-- The singular term `-(1/(4α)) sin 2θ · L₁₂(F)(z) = singKappa α F z · sin 2θ`. -/
def singFun (α : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => singKappa α F z * Real.sin (2 * θ)

/-- The angular profile `2 cos 2θ`. -/
def cosTwo : ℝ → ℝ := fun θ => 2 * Real.cos (2 * θ)

/-- The angular profile `-4 sin 2θ`. -/
def negSinFour : ℝ → ℝ := fun θ => -(4 * Real.sin (2 * θ))

theorem EllResid_eq_add_sing (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) :
    Work.Elliptic.EllResid α F Ψ = Ψ + singFun α F := by
  funext z θ
  simp only [Pi.add_apply, Work.Elliptic.EllResid, singFun, singKappa]
  ring

theorem singFun_pth (α : ℝ) (F : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (singFun α F) = fun z θ => singKappa α F z * cosTwo θ := by
  funext z θ
  simp only [Work.Spaces.pth, singFun, cosTwo]
  rw [deriv_const_mul_field (u := singKappa α F z) (v := fun θ' : ℝ => Real.sin (2 * θ'))
    (x := θ), deriv_sin_two]

theorem singFun_pth2 (α : ℝ) (F : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter 2 (singFun α F) = fun z θ => singKappa α F z * negSinFour θ := by
  funext z θ
  show deriv (fun θ' => Work.Spaces.pth (singFun α F) z θ') θ = singKappa α F z * negSinFour θ
  have h1 : (fun θ' => Work.Spaces.pth (singFun α F) z θ')
      = (fun θ' => singKappa α F z * (2 * Real.cos (2 * θ'))) := by
    funext θ'
    rw [show Work.Spaces.pth (singFun α F) z θ' = singKappa α F z * cosTwo θ'
      from congrFun (congrFun (singFun_pth α F) z) θ']
    rfl
  rw [h1, deriv_const_mul_field (u := singKappa α F z)
    (v := fun θ' : ℝ => 2 * Real.cos (2 * θ')) (x := θ), deriv_two_cos_two]
  simp only [negSinFour]

theorem singFun_DzIter (α : ℝ) (F : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (singFun α F)
      = fun z θ => Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * Real.sin (2 * θ) :=
  Work.FTS.EllipticEst.DzIter_radial_mul j _ _

theorem singFun_DzIter_pth (α : ℝ) (F : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (Work.Spaces.pth (singFun α F))
      = fun z θ => Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * cosTwo θ := by
  rw [singFun_pth, Work.FTS.EllipticEst.DzIter_radial_mul]

theorem singFun_DzIter_pth2 (α : ℝ) (F : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (Work.Spaces.pthIter 2 (singFun α F))
      = fun z θ => Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * negSinFour θ := by
  rw [singFun_pth2, Work.FTS.EllipticEst.DzIter_radial_mul]

/-- The `D_θ`-iterate of the singular part of the residual. -/
theorem singFun_DthIter (α : ℝ) (F : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (singFun α F)
      = fun z θ => singKappa α F z
          * Work.Spaces.DthIter i (fun _ θ' => Real.sin (2 * θ')) 0 θ := by
  funext z θ
  exact Work.FTS.EllipticEst.DthIter_mul_of_angular i (singKappa α F)
    (fun θ' => Real.sin (2 * θ')) z θ

/-- Commutation of `D_θ^i` and `D_z^j` on the `∂_θ`-derivative of the singular part. -/
theorem singFun_Dth_Dz_comm_pth (α : ℝ) (F : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (Work.Spaces.DzIter j (Work.Spaces.pth (singFun α F))) z θ
      = Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.pth (singFun α F))) z θ := by
  rw [singFun_DzIter_pth]
  rw [Work.FTS.EllipticEst.DthIter_mul_of_angular]
  rw [show Work.Spaces.DthIter i (Work.Spaces.pth (singFun α F))
      = fun z θ => singKappa α F z * Work.Spaces.DthIter i (fun _ θ' => cosTwo θ') 0 θ from by
    rw [singFun_pth]
    funext a b
    rw [Work.FTS.EllipticEst.DthIter_mul_of_angular]]
  rw [Work.FTS.EllipticEst.DzIter_radial_mul]

/-- Commutation of `D_θ^i` and `D_z^j` on the second `∂_θ`-derivative of the singular part. -/
theorem singFun_Dth_Dz_comm_pth2 (α : ℝ) (F : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 (singFun α F))) z θ
      = Work.Spaces.DzIter j
          (Work.Spaces.DthIter i (Work.Spaces.pthIter 2 (singFun α F))) z θ := by
  rw [singFun_DzIter_pth2]
  rw [Work.FTS.EllipticEst.DthIter_mul_of_angular]
  rw [show Work.Spaces.DthIter i (Work.Spaces.pthIter 2 (singFun α F))
      = fun z θ => singKappa α F z * Work.Spaces.DthIter i (fun _ θ' => negSinFour θ') 0 θ from by
    rw [singFun_pth2]
    funext a b
    rw [Work.FTS.EllipticEst.DthIter_mul_of_angular]]
  rw [Work.FTS.EllipticEst.DzIter_radial_mul]

/-! ## The second `θ`-derivative of a slice, on an arbitrary open set -/

/-- **The second `θ`-derivative of the slice `θ' ↦ D_z^j f z θ'` of a `C^∞` datum on an open set
`V` is the slice of `D_z^j (∂_θ² f)`.**  The `C^∞` version of `SliceAux.sliceV_DzIter`. -/
theorem sliceV_DzIter_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) V) (j : ℕ) {y : ℝ × ℝ} (hy : y ∈ V) :
    Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f y.1 θ') y.2
      = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) y.1 y.2 := by
  have hnb : (fun θ' : ℝ => (y.1, θ')) ⁻¹' V ∈ 𝓝 y.2 :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hV.mem_nhds hy)
  have hcomm1 : (fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j f) y.1 θ')
      =ᶠ[𝓝 y.2] (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) y.1 θ') := by
    filter_upwards [hnb] with θ' hθ'
    exact Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen hV hf j hθ'
  have e1 : Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f y.1 θ') y.2
      = deriv (fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j f) y.1 θ') y.2 := rfl
  rw [e1, hcomm1.deriv_eq]
  have e2 : deriv (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) y.1 θ') y.2
      = Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.pth f)) y.1 y.2 := rfl
  rw [e2]
  have hf' : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth f)) V := fun n =>
    contDiffOn_infty.mp (Work.FTS.LocData.contDiffOn_pth hV (contDiffOn_infty.mpr hf)) n
  have h3 : Work.Spaces.pthIter 2 f = Work.Spaces.pth (Work.Spaces.pth f) := rfl
  rw [h3]
  exact Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen hV hf' j hy

/-! ## Continuity on the closed angular interval from the open interval and the two limits -/

/-- A function which is continuous on `(0,π/2)` and has vanishing one-sided limits at the two
endpoints is continuous on the closed interval `Iθ`. -/
theorem continuousOn_Iθ_of_Ioo {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)))
    (hl0 : ContinuousWithinAt f (Set.Ioi 0) 0)
    (hl1 : ContinuousWithinAt f (Set.Iio (Real.pi / 2)) (Real.pi / 2)) :
    ContinuousOn f Work.Spaces.Iθ := by
  intro x hx
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hx
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hx with hx0 | hx1 | hx2
  · subst hx0
    exact (continuousWithinAt_Icc_iff_Ici (by linarith [Real.pi_pos] : (0:ℝ) < π/2)).mpr
      ((continuousWithinAt_Ioi_iff_Ici).mp hl0)
  · subst hx1
    exact (continuousWithinAt_Icc_iff_Iic (by linarith [Real.pi_pos] : (0:ℝ) < π/2)).mpr
      ((continuousWithinAt_Iio_iff_Iic).mp hl1)
  · exact ((hf.continuousWithinAt hx2).continuousAt (isOpen_Ioo.mem_nhds hx2)).continuousWithinAt


/-! ## The iterates of the one-variable angular operator `Lop` -/

/-- Every iterate of `Lop` of a smooth one-variable function is smooth. -/
theorem contDiffOn_LopIter {v : ℝ → ℝ}
    (hv : ContDiffOn ℝ Work.Stability.smoothOrder v (Set.Ioo 0 (Real.pi / 2))) (m : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Work.FTS.EllipticEst.LopIter m v)
      (Set.Ioo 0 (Real.pi / 2)) := by
  induction m with
  | zero => simpa [Work.FTS.EllipticEst.LopIter] using hv
  | succ m ih =>
      rw [Work.FTS.EllipticEst.LopIter_succ]
      have hso : Work.Stability.smoothOrder + 1 = Work.Stability.smoothOrder := rfl
      have hder : ContDiffOn ℝ Work.Stability.smoothOrder
          (deriv (Work.FTS.EllipticEst.LopIter m v)) (Set.Ioo 0 (Real.pi / 2)) :=
        ih.deriv_of_isOpen isOpen_Ioo (le_of_eq hso)
      have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin (2 * θ))
          (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
      exact hsin.mul hder

/-- The iterates of `Lop` are differentiable on `(0,π/2)` for a smooth datum. -/
theorem differentiableOn_LopIter {v : ℝ → ℝ}
    (hv : ContDiffOn ℝ Work.Stability.smoothOrder v (Set.Ioo 0 (Real.pi / 2))) (m : ℕ) :
    DifferentiableOn ℝ (Work.FTS.EllipticEst.LopIter m v) (Set.Ioo 0 (Real.pi / 2)) :=
  (contDiffOn_LopIter hv m).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero

theorem contDiffOn_cosTwo : ContDiffOn ℝ Work.Stability.smoothOrder cosTwo
    (Set.Ioo 0 (Real.pi / 2)) := by
  rw [show cosTwo = fun θ : ℝ => 2 * Real.cos (2 * θ) from rfl]
  fun_prop

theorem contDiffOn_negSinFour : ContDiffOn ℝ Work.Stability.smoothOrder negSinFour
    (Set.Ioo 0 (Real.pi / 2)) := by
  rw [show negSinFour = fun θ : ℝ => -(4 * Real.sin (2 * θ)) from rfl]
  fun_prop

/-! ## The residual vanishes on the two angular boundaries -/

theorem vanishTheta_EllResid_aux (α : ℝ) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    Work.Spaces.VanishTheta (Work.Elliptic.EllResid α F Ψ) := by
  constructor
  · intro z
    simp [Work.Elliptic.EllResid, hsol.2.1 z]
  · intro z
    have h : Real.sin (2 * (Real.pi / 2)) = 0 := by
      rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
    simp [Work.Elliptic.EllResid, hsol.2.2.1 z, h]

/-! ## The decomposition of the radial derivatives of the residual -/

/-- The open quadrant `(0,∞) × (0,π/2)` on which the residual is smooth. -/
def esdQuad : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- **`D_z^j (EllResid α F Ψ) = D_z^j Ψ + (D_z^j κ) · sin 2θ`.**  The singular part of the
residual is a radial factor `κ = -(1/(4α))L₁₂(F)` times the angular profile `sin 2θ`, so each
radial derivative acts on `κ` alone; the only input is that `κ` is differentiable up to the
order `j` on `(0,∞)` (`ContDiffOn ℝ k (singKappa α F) (Ioi 0)`, `j ≤ k`). -/
theorem DzIter_EllResid_eq_Ioo {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} {k : ℕ}
    (hκ : ContDiffOn ℝ (k : ℕ∞ω) (singKappa α F) (Set.Ioi 0))
    (hSmΨ : Work.FTS.LocData.SmoothQuad Ψ) :
    ∀ j : ℕ, j ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ
        = Work.Spaces.DzIter j Ψ z θ
          + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * Real.sin (2 * θ) := by
  have hΨz : ∀ (m : ℕ) {θ : ℝ}, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      DifferentiableOn ℝ (fun z => Work.Spaces.DzIter m Ψ z θ) (Set.Ioi 0) := by
    intro m θ hθ
    have h := (hSmΨ.DzIter m).curry_z hθ
    refine (h.differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).mono ?_
    intro z hz
    simp only [Set.mem_Ioi] at hz ⊢
    linarith
  have hQz : ∀ (m : ℕ), m < k → DifferentiableOn ℝ
      (fun z => Work.FTS.EllipticEst.rDzIter m (singKappa α F) z) (Set.Ioi 0) :=
    fun m hm => differentiableOn_rDzIter hκ hm
  intro j
  induction j with
  | zero =>
      intro hj z hz θ hθ
      rw [Work.Spaces.DzIter_zero, Work.Spaces.DzIter_zero, Work.FTS.EllipticEst.rDzIter_zero]
      rw [EllResid_eq_add_sing]
      rfl
  | succ j ih =>
      intro hj z hz θ hθ
      have hj' : j ≤ k := by omega
      have hjlt : j < k := by omega
      have ihj := ih hj'
      have hA : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter j Ψ z' θ) z :=
        (hΨz j hθ).differentiableAt (isOpen_Ioi.mem_nhds hz)
      have hB : DifferentiableAt ℝ
          (fun z' => Work.FTS.EllipticEst.rDzIter j (singKappa α F) z' * Real.sin (2 * θ)) z :=
        ((hQz j hjlt).mul_const (Real.sin (2 * θ))).differentiableAt (isOpen_Ioi.mem_nhds hz)
      rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
      simp only [Work.Spaces.pz]
      have hev : (fun z' => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter j Ψ z' θ
              + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z' * Real.sin (2 * θ)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ihj z' hz' θ hθ
      rw [hev.deriv_eq]
      rw [show deriv (fun z' => Work.Spaces.DzIter j Ψ z' θ
            + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z' * Real.sin (2 * θ)) z
          = deriv ((fun z' => Work.Spaces.DzIter j Ψ z' θ)
            + fun z' => Work.FTS.EllipticEst.rDzIter j (singKappa α F) z' * Real.sin (2 * θ)) z
          from rfl]
      rw [deriv_add hA hB]
      rw [Work.FTS.EllipticEst.deriv_mul_radial]
      rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.FTS.EllipticEst.rDzIter_succ,
        Work.FTS.EllipticEst.rDz]
      simp only [Work.Spaces.pz]
      ring

/-- The same decomposition on the closed angular interval `Iθ`: at the two endpoints both sides
vanish. -/
theorem DzIter_EllResid_eq_Iθ {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} {k : ℕ}
    (hκ : ContDiffOn ℝ (k : ℕ∞ω) (singKappa α F) (Set.Ioi 0))
    (hSmΨ : Work.FTS.LocData.SmoothQuad Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    ∀ j : ℕ, j ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ
        = Work.Spaces.DzIter j Ψ z θ
          + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * Real.sin (2 * θ) := by
  have hvan : Work.Spaces.VanishTheta (Work.Elliptic.EllResid α F Ψ) :=
    vanishTheta_EllResid_aux α hsol
  have hvanΨ : Work.Spaces.VanishTheta Ψ := ⟨hsol.2.1, hsol.2.2.1⟩
  have hs0 : Real.sin (2 * (0 : ℝ)) = 0 := by
    rw [show 2 * (0 : ℝ) = 0 from by ring, Real.sin_zero]
  have hs1 : Real.sin (2 * (Real.pi / 2)) = 0 := by
    rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
  intro j hj z hz θ hθ
  have hb := Work.FTS.EllipticEst.DzIter_boundary_zero hvan j
  have hbΨ := Work.FTS.EllipticEst.DzIter_boundary_zero hvanΨ j
  have hz0 : (0 : ℝ) < z := hz
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hθ with h0 | h1 | h2
  · subst h0
    rw [hb.1 z (by linarith), hbΨ.1 z (by linarith), hs0]
    ring
  · subst h1
    rw [hb.2 z (by linarith), hbΨ.2 z (by linarith), hs1]
    ring
  · exact DzIter_EllResid_eq_Ioo hκ hSmΨ j hj z hz0 θ h2


/-! ## The `D_θ`-iterates of the singular part as radial ⊗ angular products -/

theorem singFun_DthIter_pth (α : ℝ) (F : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (Work.Spaces.pth (singFun α F))
      = fun z θ => singKappa α F z * Work.FTS.EllipticEst.LopIter i cosTwo θ := by
  rw [singFun_pth]
  funext z θ
  rw [Work.FTS.EllipticEst.DthIter_mul_of_angular]
  have hL : (fun θ' => Work.Spaces.DthIter i (fun _ θ'' => cosTwo θ'') 0 θ')
      = Work.FTS.EllipticEst.LopIter i cosTwo := by
    funext θ'
    rw [Work.Spaces.DthIter_eq_iterate_Lop]
    rfl
  rw [← hL]

theorem singFun_DthIter_pth2 (α : ℝ) (F : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (Work.Spaces.pthIter 2 (singFun α F))
      = fun z θ => singKappa α F z * Work.FTS.EllipticEst.LopIter i negSinFour θ := by
  rw [singFun_pth2]
  funext z θ
  rw [Work.FTS.EllipticEst.DthIter_mul_of_angular]
  have hL : (fun θ' => Work.Spaces.DthIter i (fun _ θ'' => negSinFour θ'') 0 θ')
      = Work.FTS.EllipticEst.LopIter i negSinFour := by
    funext θ'
    rw [Work.Spaces.DthIter_eq_iterate_Lop]
    rfl
  rw [← hL]

/-- `D_θ^m` of `D_z^j (∂_θ (singFun α F))` is the radial ⊗ angular product with profile
`LopIter m cosTwo`. -/
theorem singFun_Dth_Dz_pth_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (j m : ℕ) :
    Work.Spaces.DthIter m (Work.Spaces.DzIter j (Work.Spaces.pth (singFun α F)))
      = fun z θ => Work.FTS.EllipticEst.rDzIter j (singKappa α F) z
          * Work.FTS.EllipticEst.LopIter m cosTwo θ := by
  rw [singFun_DzIter_pth]
  funext z θ
  rw [Work.FTS.EllipticEst.DthIter_mul_of_angular]
  have hL : (fun θ' => Work.Spaces.DthIter m (fun _ θ'' => cosTwo θ'') 0 θ')
      = Work.FTS.EllipticEst.LopIter m cosTwo := by
    funext θ'
    rw [Work.Spaces.DthIter_eq_iterate_Lop]
    rfl
  rw [← hL]

/-- `D_θ^m` of `D_z^j (∂_θ² (singFun α F))` is the radial ⊗ angular product with profile
`LopIter m negSinFour`. -/
theorem singFun_Dth_Dz_pth2_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (j m : ℕ) :
    Work.Spaces.DthIter m (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 (singFun α F)))
      = fun z θ => Work.FTS.EllipticEst.rDzIter j (singKappa α F) z
          * Work.FTS.EllipticEst.LopIter m negSinFour θ := by
  rw [singFun_DzIter_pth2]
  funext z θ
  rw [Work.FTS.EllipticEst.DthIter_mul_of_angular]
  have hL : (fun θ' => Work.Spaces.DthIter m (fun _ θ'' => negSinFour θ'') 0 θ')
      = Work.FTS.EllipticEst.LopIter m negSinFour := by
    funext θ'
    rw [Work.Spaces.DthIter_eq_iterate_Lop]
    rfl
  rw [← hL]


/-- `D_θ^i` only sees the values of the function at the fixed radial level `z`. -/
theorem DthIter_eq_of_eqOn_slice (X Y : ℝ → ℝ → ℝ) (z : ℝ)
    (h : ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2), X z θ' = Y z θ') :
    ∀ i : ℕ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.DthIter i X z θ = Work.Spaces.DthIter i Y z θ := by
  intro i
  induction i with
  | zero => intro θ hθ; exact h θ hθ
  | succ i ih =>
      intro θ hθ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.Dth,
        Work.Spaces.pth, Work.Spaces.pth]
      have hev : (fun θ' => Work.Spaces.DthIter i X z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter i Y z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih θ' hθ'
      rw [hev.deriv_eq]

/-- The `D_θ`-iterates of a radial ⊗ angular product. -/
theorem DthIter_radAng (j i : ℕ) (κ : ℝ → ℝ) (v : ℝ → ℝ) :
    Work.Spaces.DthIter i
        (fun z θ => Work.FTS.EllipticEst.rDzIter j κ z * v θ)
      = fun z θ => Work.FTS.EllipticEst.rDzIter j κ z
          * Work.FTS.EllipticEst.LopIter i v θ := by
  funext z θ
  rw [Work.FTS.EllipticEst.DthIter_mul_of_angular]
  congr 1
  rw [Work.Spaces.DthIter_eq_iterate_Lop]
  rfl

/-- `D_z^j` of the `D_θ^i`-iterate of the singular part's `∂_θ`-derivative. -/
theorem singFun_DzIter_DthIter_pth (α : ℝ) (F : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.pth (singFun α F)))
      = fun z θ => Work.FTS.EllipticEst.rDzIter j (singKappa α F) z
          * Work.FTS.EllipticEst.LopIter i cosTwo θ := by
  rw [singFun_DthIter_pth]
  exact Work.FTS.EllipticEst.DzIter_radial_mul j _ _

/-- `D_z^j` of the `D_θ^i`-iterate of the singular part's `∂_θ²`-derivative. -/
theorem singFun_DzIter_DthIter_pth2 (α : ℝ) (F : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.pthIter 2 (singFun α F)))
      = fun z θ => Work.FTS.EllipticEst.rDzIter j (singKappa α F) z
          * Work.FTS.EllipticEst.LopIter i negSinFour θ := by
  rw [singFun_DthIter_pth2]
  exact Work.FTS.EllipticEst.DzIter_radial_mul j _ _

/-- The `θ`-derivative of a `z`-slice is the plain partial derivative `∂_θ`, by definition. -/
theorem deriv_slice_eq_pth (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    deriv (fun θ' => X z θ') θ = Work.Spaces.pth X z θ := rfl

/-- The plain partial derivative `∂_θ` is the derivative of the `z`-slice, by definition. -/
theorem pth_eq_deriv_slice (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth X z θ = deriv (fun θ' => X z θ') θ := rfl

/-- The second `θ`-derivative of a `z`-slice is the slice of `∂_θ²`, by definition. -/
theorem FTS_sliceV_eq_pthIter_two (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.EllipticEst.sliceV (fun θ' => X z θ') θ = Work.Spaces.pthIter 2 X z θ := rfl

theorem EllResid_slice_data : ∀ k : ℕ, 2 ≤ k → ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.EllHypQ α k F Ψ →
    Work.Elliptic.OrthCond (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) →
    (∀ j : ℕ, j ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ),
        ContDiffOn ℝ Work.Stability.smoothOrder
            (fun θ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ)
            (Set.Ioo 0 (Real.pi / 2)) ∧
        ContinuousOn (fun θ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ)
            Work.Spaces.Iθ ∧
        Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z 0 = 0 ∧
        Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z (Real.pi / 2) = 0) ∧
    (∀ j : ℕ, j ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        deriv (fun θ' => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ') θ
          = Work.Spaces.DzIter j (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)) z θ) ∧
    (∀ j : ℕ, j ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.sliceV
            (fun θ' => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ') θ
          = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) z θ) ∧
    (∀ (j i : ℕ), 1 ≤ i → i + j ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.LopIter i
            (deriv (fun θ' => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ')) θ
          = Work.Spaces.mixed j i (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)) z θ) ∧
    (∀ (j i : ℕ), 1 ≤ i → i + j ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.LopIter i
            (Work.FTS.EllipticEst.sliceV
              (fun θ' => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ')) θ
          = Work.Spaces.mixed j i (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) z θ) := by
  intro k hk α F Ψ hα hα4 hHyp hOrth
  have hα1 : α ≤ 1 := by linarith
  have hL12 : ContDiffOn ℝ (k : ℕ∞ω) (Work.Elliptic.L12 F) (Set.Ioi 0) :=
    EllHypQ.contDiffOn_L12 hα hα1 hk hHyp
  have hκ : ContDiffOn ℝ (k : ℕ∞ω) (singKappa α F) (Set.Ioi 0) := by
    rw [show singKappa α F = fun z => (-(1 / (4 * α))) * Work.Elliptic.L12 F z from rfl]
    exact contDiffOn_const.mul hL12
  have hSmΨ : Work.FTS.LocData.SmoothQuad Ψ := hHyp.quadPsi
  have hsol : Work.Elliptic.IsBslSol α F Ψ := hHyp.sol
  have hvanΨ : Work.Spaces.VanishTheta Ψ := ⟨hsol.2.1, hsol.2.2.1⟩
  have hvanR : Work.Spaces.VanishTheta (Work.Elliptic.EllResid α F Ψ) :=
    vanishTheta_EllResid_aux α hsol
  have hquad : IsOpen esdQuad := isOpen_Ioi.prod isOpen_Ioo
  have hsub : esdQuad ⊆ Work.Spaces.quadU := by
    intro p hp
    have h1 : (0 : ℝ) < p.1 := hp.1
    exact ⟨show (-1 : ℝ) < p.1 by linarith, hp.2⟩
  have hΨquad : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Ψ) esdQuad :=
    hSmΨ.mono hsub
  have hΨs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) esdQuad :=
    fun n => contDiffOn_infty.mp hΨquad n
  have hSmPthΨ : Work.FTS.LocData.SmoothQuad (Work.Spaces.pth Ψ) :=
    Work.FTS.LocData.contDiffOn_pth Work.FTS.LocData.isOpen_quadU hSmΨ
  have hSmPth2Ψ : Work.FTS.LocData.SmoothQuad (Work.Spaces.pthIter 2 Ψ) := by
    rw [show Work.Spaces.pthIter 2 Ψ = Work.Spaces.pth (Work.Spaces.pth Ψ) from rfl]
    exact Work.FTS.LocData.contDiffOn_pth Work.FTS.LocData.isOpen_quadU hSmPthΨ
  have hpthΨsm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth Ψ)) esdQuad := hSmPthΨ.mono hsub
  have hpthΨs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth Ψ)) esdQuad :=
    fun n => contDiffOn_infty.mp hpthΨsm n
  have hpth2Ψsm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pthIter 2 Ψ)) esdQuad := hSmPth2Ψ.mono hsub
  have hpth2Ψs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 Ψ)) esdQuad :=
    fun n => contDiffOn_infty.mp hpth2Ψsm n
  have hdiffDz : ∀ (A : ℝ → ℝ → ℝ), Work.FTS.LocData.SmoothQuad A → ∀ (m : ℕ) {θ' : ℝ},
      θ' ∈ Set.Ioo 0 (Real.pi / 2) →
      DifferentiableOn ℝ (fun z => Work.Spaces.DzIter m A z θ') (Set.Ioi 0) := by
    intro A hA m θ' hθ'
    have h := (hA.DzIter m).curry_z hθ'
    refine (h.differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).mono ?_
    intro z hz
    simp only [Set.mem_Ioi] at hz ⊢
    linarith
  have hdiffDth : ∀ (A : ℝ → ℝ → ℝ), Work.FTS.LocData.SmoothQuad A → ∀ (m : ℕ) {z : ℝ},
      -1 < z → DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter m A z θ')
        (Set.Ioo 0 (Real.pi / 2)) := by
    intro A hA m z hz
    exact ((hA.DthIter m).curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero
  have hQDz : ∀ (m : ℕ), m < k → ∀ (v : ℝ → ℝ) (θ' : ℝ),
      DifferentiableOn ℝ (fun z => Work.Spaces.DzIter m
        (fun z θ => singKappa α F z * v θ) z θ') (Set.Ioi 0) := by
    intro m hm v θ'
    have hEq : (fun z => Work.Spaces.DzIter m (fun z θ => singKappa α F z * v θ) z θ')
        = fun z => Work.FTS.EllipticEst.rDzIter m (singKappa α F) z * v θ' := by
      funext z
      exact congrFun (congrFun (Work.FTS.EllipticEst.DzIter_radial_mul m (singKappa α F) v) z) θ'
    rw [hEq]
    exact (differentiableOn_rDzIter hκ hm).mul_const (v θ')
  have hQDth : ∀ (m : ℕ) (v : ℝ → ℝ),
      ContDiffOn ℝ Work.Stability.smoothOrder v (Set.Ioo 0 (Real.pi / 2)) → ∀ z,
      DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter m
        (fun z θ => singKappa α F z * v θ) z θ') (Set.Ioo 0 (Real.pi / 2)) := by
    intro m v hv z
    have hEq : (fun θ' => Work.Spaces.DthIter m (fun z θ => singKappa α F z * v θ) z θ')
        = fun θ' => singKappa α F z * Work.FTS.EllipticEst.LopIter m v θ' := by
      funext θ'
      rw [Work.FTS.EllipticEst.DthIter_mul_of_angular]
      congr 1
      rw [Work.Spaces.DthIter_eq_iterate_Lop]
      rfl
    rw [hEq]
    exact (differentiableOn_LopIter hv m).const_mul _
  have hQDthDz : ∀ (j' m : ℕ) (v : ℝ → ℝ),
      ContDiffOn ℝ Work.Stability.smoothOrder v (Set.Ioo 0 (Real.pi / 2)) → ∀ z,
      DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter m
        (Work.Spaces.DzIter j' (fun z θ => singKappa α F z * v θ)) z θ')
        (Set.Ioo 0 (Real.pi / 2)) := by
    intro j' m v hv z
    have hEq : (fun θ' => Work.Spaces.DthIter m
        (Work.Spaces.DzIter j' (fun z θ => singKappa α F z * v θ)) z θ')
        = fun θ' => Work.FTS.EllipticEst.rDzIter j' (singKappa α F) z
            * Work.FTS.EllipticEst.LopIter m v θ' := by
      funext θ'
      rw [Work.FTS.EllipticEst.DzIter_radial_mul,
        Work.FTS.EllipticEst.DthIter_mul_of_angular]
      congr 1
      rw [Work.Spaces.DthIter_eq_iterate_Lop]
      rfl
    rw [hEq]
    exact (differentiableOn_LopIter hv m).const_mul _
  have hcosTwo : ContDiffOn ℝ Work.Stability.smoothOrder cosTwo (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_cosTwo
  have hnegSinFour : ContDiffOn ℝ Work.Stability.smoothOrder negSinFour
      (Set.Ioo 0 (Real.pi / 2)) := contDiffOn_negSinFour
  -- the two pointwise identities for the angular derivatives of the residual
  have hpthR : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) z θ
        = (Work.Spaces.pth Ψ + Work.Spaces.pth (singFun α F)) z θ := by
    intro z hz θ hθ
    have hz0 : (0 : ℝ) < z := hz
    have hz1 : (-1 : ℝ) < z := by linarith
    rw [EllResid_eq_add_sing]
    simp only [Pi.add_apply]
    refine pth_add_of_diff _ _ z θ ?_ ?_
    · exact (((hSmΨ.curry_θ hz1)).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)
    · rw [show (fun θ' => singFun α F z θ')
          = (fun θ' => singKappa α F z * Real.sin (2 * θ')) from rfl]
      exact (differentiableAt_const _).mul (hasDerivAt_sin_two θ).differentiableAt
  have hpth2R : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z θ
        = (Work.Spaces.pthIter 2 Ψ + Work.Spaces.pthIter 2 (singFun α F)) z θ := by
    intro z hz θ hθ
    have hz0 : (0 : ℝ) < z := hz
    have hz1 : (-1 : ℝ) < z := by linarith
    show deriv (fun θ' => Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) z θ') θ = _
    have hev : (fun θ' => Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) z θ')
        =ᶠ[𝓝 θ] (fun θ' => (Work.Spaces.pth Ψ + Work.Spaces.pth (singFun α F)) z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      exact hpthR z hz θ' hθ'
    rw [hev.deriv_eq]
    rw [show (fun θ' => (Work.Spaces.pth Ψ + Work.Spaces.pth (singFun α F)) z θ')
        = (fun θ' => Work.Spaces.pth Ψ z θ' + singKappa α F z * cosTwo θ') from by
      funext θ'
      simp only [Pi.add_apply]
      rw [show Work.Spaces.pth (singFun α F) z θ'
          = singKappa α F z * cosTwo θ'
        from congrFun (congrFun (singFun_pth α F) z) θ']]
    have hA : HasDerivAt (fun θ' => Work.Spaces.pth Ψ z θ')
        (Work.Spaces.pthIter 2 Ψ z θ) θ :=
      ((((hSmPthΨ.curry_θ hz1)).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
    have hB : HasDerivAt (fun θ' => singKappa α F z * cosTwo θ')
        (singKappa α F z * deriv cosTwo θ) θ :=
      ((by fun_prop : DifferentiableAt ℝ (fun θ' : ℝ => 2 * Real.cos (2 * θ')) θ)).hasDerivAt.const_mul _
    have hsum : HasDerivAt (fun θ' => Work.Spaces.pth Ψ z θ' + singKappa α F z * cosTwo θ')
        (Work.Spaces.pthIter 2 Ψ z θ + singKappa α F z * deriv cosTwo θ) θ := by
      convert hA.add hB using 1
    rw [hsum.deriv]
    simp only [Pi.add_apply]
    rw [singFun_pth2]
    congr 1
    rw [show cosTwo = (fun θ' : ℝ => 2 * Real.cos (2 * θ')) from rfl, deriv_two_cos_two]
    simp only [negSinFour]
  -- the decomposition of the `z`-derivatives of the angular derivatives
  have hDzPth : ∀ j : ℕ, j ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.DzIter j (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)) z θ
        = Work.Spaces.DzIter j (Work.Spaces.pth Ψ) z θ
          + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * cosTwo θ := by
    intro j hj z hz θ hθ
    have hz0 : (0 : ℝ) < z := hz
    have hptw : ∀ z' ∈ Set.Ioi (0 : ℝ),
        Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) z' θ
          = (Work.Spaces.pth Ψ + Work.Spaces.pth (singFun α F)) z' θ :=
      fun z' hz' => hpthR z' hz' θ hθ
    rw [DzIter_eq_of_eqOn_slice _ _ θ hptw j z hz0]
    rw [DzIter_add_of_diffOn (Work.Spaces.pth Ψ) (Work.Spaces.pth (singFun α F)) j θ
      (fun m hm => hdiffDz (Work.Spaces.pth Ψ) hSmPthΨ m hθ)
      (fun m hm => by
        rw [singFun_pth]
        exact hQDz m (Nat.lt_of_lt_of_le hm hj) cosTwo θ)
      z hz0]
    simp only [singFun_DzIter_pth, Pi.add_apply]
  have hDzPth2 : ∀ j : ℕ, j ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.DzIter j (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) z θ
        = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ) z θ
          + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * negSinFour θ := by
    intro j hj z hz θ hθ
    have hz0 : (0 : ℝ) < z := hz
    have hptw : ∀ z' ∈ Set.Ioi (0 : ℝ),
        Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z' θ
          = (Work.Spaces.pthIter 2 Ψ + Work.Spaces.pthIter 2 (singFun α F)) z' θ :=
      fun z' hz' => hpth2R z' hz' θ hθ
    rw [DzIter_eq_of_eqOn_slice _ _ θ hptw j z hz0]
    rw [DzIter_add_of_diffOn (Work.Spaces.pthIter 2 Ψ) (Work.Spaces.pthIter 2 (singFun α F)) j θ
      (fun m hm => hdiffDz (Work.Spaces.pthIter 2 Ψ) hSmPth2Ψ m hθ)
      (fun m hm => by
        rw [singFun_pth2]
        exact hQDz m (Nat.lt_of_lt_of_le hm hj) negSinFour θ)
      z hz0]
    simp only [singFun_DzIter_pth2, Pi.add_apply]
  -- identity 2
  have hderiv : ∀ j : ℕ, j ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun θ' => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ') θ
        = Work.Spaces.DzIter j (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)) z θ := by
    intro j hj z hz θ hθ
    have hz0 : (0 : ℝ) < z := hz
    have hz1 : (-1 : ℝ) < z := by linarith
    have hyq : (z, θ) ∈ esdQuad := ⟨hz0, hθ⟩
    have hL : deriv (fun θ' => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ') θ
        = Work.Spaces.DzIter j (Work.Spaces.pth Ψ) z θ
          + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * cosTwo θ := by
      have hslice : (fun θ' => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DzIter j Ψ z θ'
            + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * Real.sin (2 * θ')) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact DzIter_EllResid_eq_Ioo hκ hSmΨ j hj z hz0 θ' hθ'
      rw [hslice.deriv_eq]
      have hA : HasDerivAt (fun θ' => Work.Spaces.DzIter j Ψ z θ')
          (Work.Spaces.pth (Work.Spaces.DzIter j Ψ) z θ) θ :=
        ((((hSmΨ.DzIter j).curry_θ hz1).differentiableOn
          Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
      have hB : HasDerivAt
          (fun θ' => Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * Real.sin (2 * θ'))
          (Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * (2 * Real.cos (2 * θ))) θ :=
        (hasDerivAt_sin_two θ).const_mul _
      have hsum : HasDerivAt (fun θ' => Work.Spaces.DzIter j Ψ z θ'
            + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * Real.sin (2 * θ'))
          (Work.Spaces.pth (Work.Spaces.DzIter j Ψ) z θ
            + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * (2 * Real.cos (2 * θ))) θ := by
        convert hA.add hB using 1
      rw [hsum.deriv]
      have hcl : Work.Spaces.pth (Work.Spaces.DzIter j Ψ) z θ
          = Work.Spaces.DzIter j (Work.Spaces.pth Ψ) z θ :=
        Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen hquad hΨs j hyq
      rw [hcl]
      simp only [cosTwo]
    rw [hL, hDzPth j hj z hz θ hθ]
  -- identity 3
  have hderiv2 : ∀ j : ℕ, j ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pthIter 2 (Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ)) z θ
        = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) z θ := by
    intro j hj z hz θ hθ
    have hz0 : (0 : ℝ) < z := hz
    have hz1 : (-1 : ℝ) < z := by linarith
    have hyq : (z, θ) ∈ esdQuad := ⟨hz0, hθ⟩
    have hstep : Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.DzIter j
          (Work.Elliptic.EllResid α F Ψ))) z θ
        = Work.Spaces.pth (Work.Spaces.DzIter j
            (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ))) z θ := by
      have hev : (fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j
              (Work.Elliptic.EllResid α F Ψ)) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DzIter j
              (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)) z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact hderiv j hj z hz θ' hθ'
      exact hev.deriv_eq
    show deriv (fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j
        (Work.Elliptic.EllResid α F Ψ)) z θ') θ = _
    rw [deriv_slice_eq_pth, hstep]
    have hL : Work.Spaces.pth (Work.Spaces.DzIter j
          (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ))) z θ
        = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ) z θ
          + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * negSinFour θ := by
      have hev : (fun θ' => Work.Spaces.DzIter j
              (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth Ψ) z θ'
            + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * cosTwo θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact hDzPth j hj z hz θ' hθ'
      rw [pth_eq_deriv_slice, hev.deriv_eq]
      have hA : HasDerivAt (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth Ψ) z θ')
          (Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.pth Ψ)) z θ) θ :=
        (((hSmPthΨ.DzIter j).curry_θ hz1).differentiableOn
          Work.FTS.LocData.smoothOrder_ne_zero |>.differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
      have hB : HasDerivAt
          (fun θ' => Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * cosTwo θ')
          (Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * deriv cosTwo θ) θ :=
        (((by fun_prop : DifferentiableAt ℝ (fun θ' : ℝ => 2 * Real.cos (2 * θ')) θ)).hasDerivAt).const_mul _
      have hsum : HasDerivAt (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth Ψ) z θ'
            + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * cosTwo θ')
          (Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.pth Ψ)) z θ
            + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * deriv cosTwo θ) θ := by
        convert hA.add hB using 1
      rw [hsum.deriv]
      have hcl : Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.pth Ψ)) z θ
          = Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.pth Ψ)) z θ :=
        Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen hquad hpthΨs j hyq
      rw [hcl, show Work.Spaces.pthIter 2 Ψ = Work.Spaces.pth (Work.Spaces.pth Ψ) from rfl]
      congr 1
      rw [show cosTwo = (fun θ' : ℝ => 2 * Real.cos (2 * θ')) from rfl, deriv_two_cos_two]
      simp only [negSinFour]
    rw [hL, hDzPth2 j hj z hz θ hθ]
  -- the radial-form differentiability of the singular half
  have hQDzRad : ∀ (m : ℕ), m < k → ∀ (v : ℝ → ℝ) (θ' : ℝ),
      DifferentiableOn ℝ (fun z => Work.FTS.EllipticEst.rDzIter m (singKappa α F) z * v θ')
        (Set.Ioi 0) :=
    fun m hm v θ' => (differentiableOn_rDzIter hκ hm).mul_const (v θ')
  have hQDthRad : ∀ (j' m : ℕ) (v : ℝ → ℝ),
      ContDiffOn ℝ Work.Stability.smoothOrder v (Set.Ioo 0 (Real.pi / 2)) → ∀ z : ℝ,
      DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter m
        (fun z θ => Work.FTS.EllipticEst.rDzIter j' (singKappa α F) z * v θ) z θ')
        (Set.Ioo 0 (Real.pi / 2)) := by
    intro j' m v hv z
    have hEq : (fun θ' => Work.Spaces.DthIter m
        (fun z θ => Work.FTS.EllipticEst.rDzIter j' (singKappa α F) z * v θ) z θ')
        = fun θ' => Work.FTS.EllipticEst.rDzIter j' (singKappa α F) z
            * Work.FTS.EllipticEst.LopIter m v θ' := by
      funext θ'
      rw [Work.FTS.EllipticEst.DthIter_mul_of_angular]
      congr 1
      rw [Work.Spaces.DthIter_eq_iterate_Lop]
      rfl
    rw [hEq]
    exact (differentiableOn_LopIter hv m).const_mul _
  have hQDzDth : ∀ (m i' : ℕ), m < k → ∀ z θ' : ℝ,
      DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter m
        (Work.Spaces.DthIter i' (Work.Spaces.pth (singFun α F))) z' θ') (Set.Ioi 0) := by
    intro m i' hm z θ'
    have hEq : (fun z' => Work.Spaces.DzIter m
        (Work.Spaces.DthIter i' (Work.Spaces.pth (singFun α F))) z' θ')
        = fun z' => Work.FTS.EllipticEst.rDzIter m (singKappa α F) z'
            * Work.FTS.EllipticEst.LopIter i' cosTwo θ' := by
      funext z'
      exact congrFun (congrFun (singFun_DzIter_DthIter_pth α F m i') z') θ'
    rw [hEq]
    exact hQDzRad m hm (Work.FTS.EllipticEst.LopIter i' cosTwo) θ'
  have hQDzDth2 : ∀ (m i' : ℕ), m < k → ∀ z θ' : ℝ,
      DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter m
        (Work.Spaces.DthIter i' (Work.Spaces.pthIter 2 (singFun α F))) z' θ') (Set.Ioi 0) := by
    intro m i' hm z θ'
    have hEq : (fun z' => Work.Spaces.DzIter m
        (Work.Spaces.DthIter i' (Work.Spaces.pthIter 2 (singFun α F))) z' θ')
        = fun z' => Work.FTS.EllipticEst.rDzIter m (singKappa α F) z'
            * Work.FTS.EllipticEst.LopIter i' negSinFour θ' := by
      funext z'
      exact congrFun (congrFun (singFun_DzIter_DthIter_pth2 α F m i') z') θ'
    rw [hEq]
    exact hQDzRad m hm (Work.FTS.EllipticEst.LopIter i' negSinFour) θ'
  -- identity 4
  have hLop : ∀ (j i : ℕ), 1 ≤ i → i + j ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ),
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.LopIter i
          (deriv (fun θ' => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ')) θ
        = Work.Spaces.mixed j i (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)) z θ := by
    intro j i hi hij z hz θ hθ
    have hz0 : (0 : ℝ) < z := hz
    have hz1 : (-1 : ℝ) < z := by linarith
    have hyq : (z, θ) ∈ esdQuad := ⟨hz0, hθ⟩
    have hjk : j ≤ k := by omega
    have h1 : Work.FTS.EllipticEst.LopIter i
        (deriv (fun θ' => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ')) θ
        = Work.Spaces.DthIter i (Work.Spaces.DzIter j
            (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ))) z θ := by
      have hev : (deriv (fun θ' => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ'))
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DzIter j
              (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)) z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact hderiv j hjk z hz θ' hθ'
      rw [Work.FTS.EllipticEst.LopIter_congr_nhds hev i]
      exact congrFun (Work.FTS.EllipticEst.LopIter_slice i (fun z θ => Work.Spaces.DzIter j
        (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)) z θ) z) θ
    rw [h1]
    have hL : Work.Spaces.DthIter i (Work.Spaces.DzIter j
          (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ))) z θ
        = Work.Spaces.mixed j i (Work.Spaces.pth Ψ) z θ
          + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z
              * Work.FTS.EllipticEst.LopIter i cosTwo θ := by
      have heq : ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
          Work.Spaces.DzIter j (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)) z θ'
            = (Work.Spaces.DzIter j (Work.Spaces.pth Ψ)
              + fun z θ => Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * cosTwo θ) z θ' := by
        intro θ' hθ'
        simp only [Pi.add_apply]
        exact hDzPth j hjk z hz θ' hθ'
      rw [DthIter_eq_of_eqOn_slice _ _ z heq i θ hθ]
      rw [DthIter_add_of_diffOn (Work.Spaces.DzIter j (Work.Spaces.pth Ψ))
        (fun z θ => Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * cosTwo θ) i z
        (fun m hm => hdiffDth (Work.Spaces.DzIter j (Work.Spaces.pth Ψ)) (hSmPthΨ.DzIter j) m hz1)
        (fun m hm => hQDthRad j m cosTwo hcosTwo z) θ hθ]
      have hcl : Work.Spaces.DthIter i (Work.Spaces.DzIter j (Work.Spaces.pth Ψ)) z θ
          = Work.Spaces.mixed j i (Work.Spaces.pth Ψ) z θ :=
        Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen hquad hpthΨs j i hyq
      rw [hcl]
      simp only [DthIter_radAng, Pi.add_apply, Work.Spaces.mixed]
    have hR : Work.Spaces.mixed j i (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)) z θ
        = Work.Spaces.mixed j i (Work.Spaces.pth Ψ) z θ
          + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z
              * Work.FTS.EllipticEst.LopIter i cosTwo θ := by
      rw [Work.Spaces.mixed]
      have hptw : ∀ z' ∈ Set.Ioi (0 : ℝ),
          Work.Spaces.DthIter i (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)) z' θ
            = (Work.Spaces.DthIter i (Work.Spaces.pth Ψ)
              + Work.Spaces.DthIter i (Work.Spaces.pth (singFun α F))) z' θ := by
        intro z' hz'
        have hz0' : (0 : ℝ) < z' := hz'
        have hz1' : (-1 : ℝ) < z' := by linarith
        have hloc : ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
            Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) z' θ'
              = (Work.Spaces.pth Ψ + Work.Spaces.pth (singFun α F)) z' θ' :=
          fun θ' hθ' => hpthR z' hz' θ' hθ'
        rw [DthIter_eq_of_eqOn_slice _ _ z' hloc i θ hθ]
        refine DthIter_add_of_diffOn (Work.Spaces.pth Ψ) (Work.Spaces.pth (singFun α F)) i z'
          (fun m hm => hdiffDth (Work.Spaces.pth Ψ) hSmPthΨ m hz1') ?_ θ hθ
        intro m hm
        rw [singFun_pth]
        exact hQDth m cosTwo hcosTwo z'
      rw [DzIter_eq_of_eqOn_slice _ _ θ hptw j z hz0]
      rw [DzIter_add_of_diffOn (Work.Spaces.DthIter i (Work.Spaces.pth Ψ))
        (Work.Spaces.DthIter i (Work.Spaces.pth (singFun α F))) j θ
        (fun m hm => hdiffDz (Work.Spaces.DthIter i (Work.Spaces.pth Ψ))
          (hSmPthΨ.DthIter i) m hθ)
        (fun m hm => hQDzDth m i (Nat.lt_of_lt_of_le hm hjk) z θ)
        z hz0]
      simp only [singFun_DzIter_DthIter_pth, Pi.add_apply, Work.Spaces.mixed]
    rw [hL, hR]
  -- identity 5
  have hLop2 : ∀ (j i : ℕ), 1 ≤ i → i + j ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ),
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.LopIter i
          (Work.FTS.EllipticEst.sliceV
            (fun θ' => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ')) θ
        = Work.Spaces.mixed j i (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) z θ := by
    intro j i hi hij z hz θ hθ
    have hz0 : (0 : ℝ) < z := hz
    have hz1 : (-1 : ℝ) < z := by linarith
    have hyq : (z, θ) ∈ esdQuad := ⟨hz0, hθ⟩
    have hjk : j ≤ k := by omega
    have h1 : Work.FTS.EllipticEst.LopIter i
        (Work.FTS.EllipticEst.sliceV
          (fun θ' => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ')) θ
        = Work.Spaces.DthIter i (Work.Spaces.DzIter j
            (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))) z θ := by
      have hev : (fun θ' => Work.Spaces.pthIter 2
            (Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ)) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DzIter j
              (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact hderiv2 j hjk z hz θ' hθ'
      have hslice : (fun t => Work.FTS.EllipticEst.sliceV
            (fun θ' => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ') t)
          = fun t => Work.Spaces.pthIter 2 (Work.Spaces.DzIter j
              (Work.Elliptic.EllResid α F Ψ)) z t := by
        funext t
        exact FTS_sliceV_eq_pthIter_two _ z t
      rw [show Work.FTS.EllipticEst.LopIter i (Work.FTS.EllipticEst.sliceV
            (fun θ' => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ'))
          = Work.FTS.EllipticEst.LopIter i (fun t => Work.FTS.EllipticEst.sliceV
              (fun θ' => Work.Spaces.DzIter j (Work.Elliptic.EllResid α F Ψ) z θ') t)
          from rfl]
      rw [hslice]
      rw [Work.FTS.EllipticEst.LopIter_congr_nhds hev i]
      exact congrFun (Work.FTS.EllipticEst.LopIter_slice i (fun z θ => Work.Spaces.DzIter j
        (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) z θ) z) θ
    rw [h1]
    have hL : Work.Spaces.DthIter i (Work.Spaces.DzIter j
          (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))) z θ
        = Work.Spaces.mixed j i (Work.Spaces.pthIter 2 Ψ) z θ
          + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z
              * Work.FTS.EllipticEst.LopIter i negSinFour θ := by
      have heq : ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
          Work.Spaces.DzIter j (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) z θ'
            = (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ)
              + fun z θ => Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * negSinFour θ) z θ' := by
        intro θ' hθ'
        simp only [Pi.add_apply]
        exact hDzPth2 j hjk z hz θ' hθ'
      rw [DthIter_eq_of_eqOn_slice _ _ z heq i θ hθ]
      rw [DthIter_add_of_diffOn (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ))
        (fun z θ => Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * negSinFour θ) i z
        (fun m hm => hdiffDth (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ))
          (hSmPth2Ψ.DzIter j) m hz1)
        (fun m hm => hQDthRad j m negSinFour hnegSinFour z) θ hθ]
      have hcl : Work.Spaces.DthIter i (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ)) z θ
          = Work.Spaces.mixed j i (Work.Spaces.pthIter 2 Ψ) z θ :=
        Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen hquad hpth2Ψs j i hyq
      rw [hcl]
      simp only [DthIter_radAng, Pi.add_apply, Work.Spaces.mixed]
    have hR : Work.Spaces.mixed j i (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) z θ
        = Work.Spaces.mixed j i (Work.Spaces.pthIter 2 Ψ) z θ
          + Work.FTS.EllipticEst.rDzIter j (singKappa α F) z
              * Work.FTS.EllipticEst.LopIter i negSinFour θ := by
      rw [Work.Spaces.mixed]
      have hptw : ∀ z' ∈ Set.Ioi (0 : ℝ),
          Work.Spaces.DthIter i (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) z' θ
            = (Work.Spaces.DthIter i (Work.Spaces.pthIter 2 Ψ)
              + Work.Spaces.DthIter i (Work.Spaces.pthIter 2 (singFun α F))) z' θ := by
        intro z' hz'
        have hz0' : (0 : ℝ) < z' := hz'
        have hz1' : (-1 : ℝ) < z' := by linarith
        have hloc : ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
            Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z' θ'
              = (Work.Spaces.pthIter 2 Ψ + Work.Spaces.pthIter 2 (singFun α F)) z' θ' :=
          fun θ' hθ' => hpth2R z' hz' θ' hθ'
        rw [DthIter_eq_of_eqOn_slice _ _ z' hloc i θ hθ]
        refine DthIter_add_of_diffOn (Work.Spaces.pthIter 2 Ψ)
          (Work.Spaces.pthIter 2 (singFun α F)) i z'
          (fun m hm => hdiffDth (Work.Spaces.pthIter 2 Ψ) hSmPth2Ψ m hz1') ?_ θ hθ
        intro m hm
        rw [singFun_pth2]
        exact hQDth m negSinFour hnegSinFour z'
      rw [DzIter_eq_of_eqOn_slice _ _ θ hptw j z hz0]
      rw [DzIter_add_of_diffOn (Work.Spaces.DthIter i (Work.Spaces.pthIter 2 Ψ))
        (Work.Spaces.DthIter i (Work.Spaces.pthIter 2 (singFun α F))) j θ
        (fun m hm => hdiffDz (Work.Spaces.DthIter i (Work.Spaces.pthIter 2 Ψ))
          (hSmPth2Ψ.DthIter i) m hθ)
        (fun m hm => hQDzDth2 m i (Nat.lt_of_lt_of_le hm hjk) z θ)
        z hz0]
      simp only [singFun_DzIter_DthIter_pth2, Pi.add_apply, Work.Spaces.mixed]
    rw [hL, hR]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj z hz
    have hz0 : (0 : ℝ) < z := hz
    have hz1 : (-1 : ℝ) < z := by linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hA : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun θ => Work.Spaces.DzIter j Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
        (hSmΨ.DzIter j).curry_θ hz1
      have hB : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun θ => Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * Real.sin (2 * θ))
          (Set.Ioo 0 (Real.pi / 2)) := by
        have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin (2 * θ))
            (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
        exact contDiffOn_const.mul hsin
      refine (hA.add hB).congr ?_
      intro θ hθ
      exact DzIter_EllResid_eq_Ioo hκ hSmΨ j hj z hz0 θ hθ
    · have hA : ContinuousOn (fun θ => Work.Spaces.DzIter j Ψ z θ) Work.Spaces.Iθ := by
        have hsm : ContDiffOn ℝ Work.Stability.smoothOrder
            (fun θ => Work.Spaces.DzIter j Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
          (hSmΨ.DzIter j).curry_θ hz1
        refine continuousOn_Iθ_of_Ioo hsm.continuousOn ?_ ?_
        · rw [ContinuousWithinAt]
          have hl := (tendsto_DzIter_slice_zero hα hHyp.regPsi hj hz).1
          have hb := (Work.FTS.EllipticEst.DzIter_boundary_zero hvanΨ j).1 z hz1
          simpa [hb] using hl
        · rw [ContinuousWithinAt]
          have hl := (tendsto_DzIter_slice_zero hα hHyp.regPsi hj hz).2
          have hb := (Work.FTS.EllipticEst.DzIter_boundary_zero hvanΨ j).2 z hz1
          simpa [hb] using hl
      have hB : ContinuousOn
          (fun θ => Work.FTS.EllipticEst.rDzIter j (singKappa α F) z * Real.sin (2 * θ))
          Work.Spaces.Iθ := by
        have hsin : Continuous (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
        exact continuousOn_const.mul hsin.continuousOn
      refine (hA.add hB).congr ?_
      intro θ hθ
      exact DzIter_EllResid_eq_Iθ hκ hSmΨ hsol j hj z hz0 θ hθ
    · exact (Work.FTS.EllipticEst.DzIter_boundary_zero hvanR j).1 z hz1
    · exact (Work.FTS.EllipticEst.DzIter_boundary_zero hvanR j).2 z hz1
  · exact hderiv
  · intro j hj z hz θ hθ
    rw [FTS_sliceV_eq_pthIter_two]
    exact hderiv2 j hj z hz θ hθ
  · exact hLop
  · exact hLop2

end Work.FTS.EllipticEst.UopHk
