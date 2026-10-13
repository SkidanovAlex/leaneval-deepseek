import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongEps.H5.Data
import Submission.Work.FTS.StrongEps.H5.DataW
import Submission.Work.FTS.StrongPersist.c2m_L12Fstar_W6
import Submission.Work.FTS.StrongPersist.dthU_c2m_bound6
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.Atoms

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary derivative facts

The two functions that occur as the *radial* factor of the two derivatives of
`f_α(z,θ) = c₂(θ)·L₁₂(F_*)(z)` are

* `invH α = z ↦ 2α/(1+z)` (the radial factor of `f_α` and of `D_θf_α`), and
* `z ↦ -2α z/(1+z)² = -2α·hKer z` (the radial factor of `D_zf_α`).

Their weighted `z`-derivatives are controlled by the two ready-made bounds
`FstarPkg.c2mInv_radial` and `Spaces.pzIter_hKer_bound`; the only derivative actually
computed by hand is `d/dz (2α/(1+z))` (and, through `deriv_iter_const_mul`, the passage to
`-2α·hKer`). -/

/-- `deriv (z ↦ 2α/(1+z)) z = -2α/(1+z)²` for `z ≠ -1`. -/
private theorem deriv_invH (α z : ℝ) (hz : 1 + z ≠ 0) :
    deriv (fun z : ℝ => 2 * α / (1 + z)) z = -2 * α / (1 + z) ^ 2 := by
  have hd : deriv (fun z : ℝ => 1 + z) z = 1 := by
    rw [deriv_const_add, deriv_id'']
  rw [deriv_const_div (2 * α) (by fun_prop) hz, hd]
  ring

/-- The iterated `deriv` of a constant multiple: `deriv^[k] (c·b) = c·deriv^[k] b`. -/
private theorem deriv_iter_const_mul (c : ℝ) (k : ℕ) :
    ∀ b : ℝ → ℝ, deriv^[k] (fun z => c * b z) = fun z => c * deriv^[k] b z := by
  induction k with
  | zero => intro b; rfl
  | succ k ih =>
      intro b
      have h1 : deriv^[k+1] (fun z => c * b z) = deriv^[k] (deriv (fun z => c * b z)) :=
        Function.iterate_succ_apply deriv k (fun z => c * b z)
      rw [h1, show deriv (fun z => c * b z) = fun z => c * deriv b z from
        funext fun z => Work.Spaces.deriv_const_mul' c z b, ih (deriv b),
        show deriv^[k+1] b = deriv^[k] (deriv b) from Function.iterate_succ_apply deriv k b]

/-- The weighted `z`-derivative bound for `hKer z = z/(1+z)²`. -/
private theorem hKer_weighted_bound (k : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z| ≤ (k.factorial : ℝ) * (k + 1) :=
  Work.Spaces.pzIter_hKer_bound k z hz

/-! ## Separable products: the radial and mixed `SupFinite` slots

Every slot of `WlInfMem` of a separable product `(z,θ) ↦ a(θ)·b(z)` is, after
`pzIter_decomp` / `DthIter_decomp`, the product of an iterate of `a` with a weighted
`z`-derivative of `b` (times the angular weight `sin(2θ)^{-α/5}/(α+sin 2θ)` in the mixed
case).  The `SupFinite` requirement of `WlInfMem` is therefore discharged by pointwise
bounds, the only non-trivial step being the elementary `sin²(2θ)·sin(2θ)^{-α/5}/(α+sin 2θ) ≤ 1`
(`FstarPkg.sinWeight_le_one`). -/

/-- The radial `SupFinite` slots of a separable product. -/
private theorem supFinite_sep_radial {a b : ℝ → ℝ} {k : ℕ} {A B : ℝ}
    (hA : ∀ θ, |a θ| ≤ A) (hB : ∀ z, 0 ≤ z → |(z + 1) ^ k * deriv^[k] b z| ≤ B) :
    Work.Spaces.SupFinite
      (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => a θ * b z) z θ) := by
  have hAnn : 0 ≤ A := le_trans (abs_nonneg (a 0)) (hA 0)
  refine ⟨A * B, ?_⟩
  rintro y ⟨z, hz, θ, hθ, rfl⟩
  show |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => a θ * b z) z θ| ≤ A * B
  rw [Work.Spaces.pzIter_decomp k a b z θ]
  rw [show (z + 1) ^ k * (a θ * deriv^[k] b z)
      = a θ * ((z + 1) ^ k * deriv^[k] b z) by ring, abs_mul]
  exact mul_le_mul (hA θ) (hB z hz) (abs_nonneg _) hAnn

/-- The mixed `SupFinite` slots of a separable product. -/
private theorem supFinite_sep_mixed {a b : ℝ → ℝ} {α : ℝ} {j k : ℕ} {C B : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hCnn : 0 ≤ C)
    (hC : ∀ θ, |(Work.Spaces.dthU^[j]) a θ| ≤ C * Real.sin (2 * θ) ^ 2)
    (hB : ∀ z, 0 ≤ z → |(z + 1) ^ k * deriv^[k] b z| ≤ B) :
    Work.Spaces.SupFinite (fun z θ => (z + 1) ^ k *
      Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => a θ * b z)) z θ
      * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
  refine ⟨C * B, ?_⟩
  rintro y ⟨z, hz, θ, hθ, rfl⟩
  show |(z + 1) ^ k * Work.Spaces.pzIter k
      (Work.Spaces.DthIter j (fun z θ => a θ * b z)) z θ
      * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ C * B
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 le_rfl)
  have h1 : Work.Spaces.DthIter j (fun z θ => a θ * b z)
      = fun z θ => (Work.Spaces.dthU^[j]) a θ * b z := by
    funext z θ
    exact Work.Spaces.DthIter_decomp j a b z θ
  rw [h1, Work.Spaces.pzIter_decomp k ((Work.Spaces.dthU^[j]) a) b z θ]
  have hs0 : 0 ≤ Real.sin (2 * θ) := by
    refine Real.sin_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hden : (0 : ℝ) < α + Real.sin (2 * θ) := by linarith
  have hw : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
    div_nonneg (Real.rpow_nonneg hs0 _) hden.le
  have hsinw : (Real.sin (2 * θ)) ^ 2
      * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ 1 := by
    have h := Work.FTS.Nonlinear.FstarPkg.sinWeight_le_one α (Real.sin (2 * θ)) hα hα1 hs0 hs1
    rwa [mul_div_assoc] at h
  rw [show (z + 1) ^ k * ((Work.Spaces.dthU^[j]) a θ * deriv^[k] b z)
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
      = (Work.Spaces.dthU^[j]) a θ * ((z + 1) ^ k * deriv^[k] b z)
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg hw]
  calc |(Work.Spaces.dthU^[j]) a θ| * |(z + 1) ^ k * deriv^[k] b z|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ (C * (Real.sin (2 * θ)) ^ 2) * B
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
        refine mul_le_mul_of_nonneg_right ?_ hw
        exact mul_le_mul (hC θ) (hB z hz) (abs_nonneg _) (mul_nonneg hCnn (sq_nonneg _))
    _ = C * B * ((Real.sin (2 * θ)) ^ 2
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
    _ ≤ C * B * 1 := mul_le_mul_of_nonneg_left hsinw (mul_nonneg hCnn hBnn)
    _ = C * B := by ring

/-- `WlInfMem` of a separable product `a(θ)·b(z)` from a uniform angular bound on `a`, a
`sin(2θ)²`-bound on its `D_θ`-iterates and uniform weighted `z`-derivative bounds on `b`. -/
private theorem WlInfMem_sep {α : ℝ} {a b : ℝ → ℝ} {l : ℕ} {A C : ℝ} {Bf : ℕ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hCnn : 0 ≤ C)
    (hA : ∀ θ, |a θ| ≤ A)
    (hC : ∀ j, 1 ≤ j → j ≤ l → ∀ θ, |(Work.Spaces.dthU^[j]) a θ| ≤ C * Real.sin (2 * θ) ^ 2)
    (hB : ∀ k ≤ l, ∀ z, 0 ≤ z → |(z + 1) ^ k * deriv^[k] b z| ≤ Bf k) :
    Work.Spaces.WlInfMem α l (fun z θ => a θ * b z) := by
  refine ⟨?_, ?_⟩
  · intro k hk
    exact supFinite_sep_radial (hA := hA) (hB := hB k hk)
  · intro j hj k hk hj1 hjk
    exact supFinite_sep_mixed (j := j) (k := k) (C := C) (B := Bf k) hα hα1 hCnn
      (hC j hj1 hj) (hB k hk)

/-! ## `SmoothOpen` of the atom -/

/-- `c₂(θ)·L₁₂(F_*)(z)` is `C^∞` on the open quadrant (it is the explicit separated product
`c₂(θ)·2α/(1+z)` there). -/
private theorem c2mL12Fstar_smoothOpen {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.c2m θ *
      Work.Construction.L12 (Work.Construction.Fstar α) z) := by
  have hexp : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z))) := by
    change ContDiffOn ℝ Work.Stability.smoothOrder
      ((fun p : ℝ × ℝ => Work.Construction.c2m p.2) *
        (fun p : ℝ × ℝ => 2 * α / (1 + p.1))) Work.FTS.EllipticEst.Q0
    refine ContDiffOn.mul ?_ ?_
    · have hc : ContDiff ℝ Work.Stability.smoothOrder
          (fun θ : ℝ => Work.Construction.c2m θ) := by
        rw [show (fun θ : ℝ => Work.Construction.c2m θ)
            = fun θ => Real.cos (2 * θ) - Real.sin θ ^ 2 from by
              funext θ; rw [Work.Construction.c2m_eq]]
        fun_prop
      exact hc.comp_contDiffOn contDiffOn_snd
    · have hden : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun p : ℝ × ℝ => 1 + p.1) Work.FTS.EllipticEst.Q0 := by fun_prop
      have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, 1 + p.1 ≠ 0 := by
        intro p hp
        have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
        linarith
      have hinv := hden.inv hne
      have hmul : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun p : ℝ × ℝ => (2 * α) * (1 + p.1)⁻¹) Work.FTS.EllipticEst.Q0 :=
        ContDiffOn.mul contDiffOn_const hinv
      refine hmul.congr ?_
      intro p _
      simp only [div_eq_mul_inv]
  refine ContDiffOn.congr hexp ?_
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry]
  rw [Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 (by linarith)]

/-! ## The `D_z`- and `D_θ`-slots of the atom

Both `D_zf` and `D_θf` are separable products on `(-1,∞) × ℝ`:

* `D_zf_α(z,θ) = c₂(θ)·(-2α·hKer z)` (since `L₁₂(F_*)` agrees with `2α/(1+z)` on `(-1,∞)`),
* `D_θf_α(z,θ) = (dthU c₂)(θ)·invH α z`.

`WlInfMem` (and the `𝒲`-norm) only depend on the values on the right half-plane
(`FstarPkg.WlInf_congr`), so the two membership statements reduce to `WlInfMem_sep` applied
to these separable products. -/

/-- `WlInfMem α 4` of `D_z(c₂·L₁₂(F_*))`. -/
private theorem c2mL12Fstar_Dz_WlInfMem {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInfMem α 4 (Work.Spaces.Dz (fun z θ => Work.Construction.c2m θ *
      Work.Construction.L12 (Work.Construction.Fstar α) z)) := by
  have hpt : ∀ z, -1 < z → ∀ θ,
      Work.Spaces.Dz (fun z θ => Work.Construction.c2m θ *
        Work.Construction.L12 (Work.Construction.Fstar α) z) z θ
      = Work.Construction.c2m θ * (-(2 * α) * Work.Spaces.hKer z) := by
    intro z hz θ
    show z * deriv (fun z' => Work.Construction.c2m θ *
      Work.Construction.L12 (Work.Construction.Fstar α) z') z
      = Work.Construction.c2m θ * (-(2 * α) * Work.Spaces.hKer z)
    rw [Work.Spaces.deriv_const_mul']
    have hder : deriv (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z') z
        = deriv (Work.FTS.Nonlinear.FstarPkg.invH α) z :=
      Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioi hz)
        fun z' hz' => Work.FTS.Nonlinear.FstarPkg.eqOn_L12_invH α hα hα1 hz')
    have hd : deriv (Work.FTS.Nonlinear.FstarPkg.invH α) z = -2 * α / (1 + z) ^ 2 := by
      show deriv (fun z : ℝ => 2 * α / (1 + z)) z = -2 * α / (1 + z) ^ 2
      exact deriv_invH α z (by linarith)
    rw [hder, hd]
    show z * (Work.Construction.c2m θ * (-2 * α / (1 + z) ^ 2))
      = Work.Construction.c2m θ * (-(2 * α) * (z / (1 + z) ^ 2))
    ring
  refine (Work.FTS.Nonlinear.FstarPkg.WlInf_congr (f := Work.Spaces.Dz (fun z θ =>
      Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z))
    (g := fun z θ => Work.Construction.c2m θ * (-(2 * α) * Work.Spaces.hKer z)) hpt α 4).2.mpr ?_
  refine WlInfMem_sep (a := Work.Construction.c2m)
    (b := fun z => -(2 * α) * Work.Spaces.hKer z) (l := 4) (A := 2) (C := 1000)
    (Bf := fun k => 2 * α * (k.factorial : ℝ) * (k + 1)) hα hα1 (by norm_num) ?_ ?_ ?_
  · exact Work.FTS.Nonlinear.FstarPkg.abs_c2m_le_two
  · intro j hj1 hj4 θ
    exact Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound j hj1 hj4 θ
  · intro k hk z hz
    have h := hKer_weighted_bound k z hz
    rw [deriv_iter_const_mul (-(2 * α)) k Work.Spaces.hKer]
    rw [show (z + 1) ^ k * ((-(2 * α)) * deriv^[k] Work.Spaces.hKer z)
        = (-(2 * α)) * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z) by ring]
    rw [abs_mul,
      show |(-(2 * α) : ℝ)| = 2 * α from by rw [abs_neg, abs_of_pos (by linarith : (0:ℝ) < 2 * α)]]
    calc 2 * α * |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|
        ≤ 2 * α * ((k.factorial : ℝ) * (k + 1)) :=
          mul_le_mul_of_nonneg_left h (by linarith)
      _ = 2 * α * (k.factorial : ℝ) * (k + 1) := by ring

/-- `WlInfMem α 4` of `D_θ(c₂·L₁₂(F_*))`. -/
private theorem c2mL12Fstar_Dth_WlInfMem {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (fun z θ => Work.Construction.c2m θ *
      Work.Construction.L12 (Work.Construction.Fstar α) z)) := by
  obtain ⟨C6, hC6pos, hC6⟩ := Work.FTS.StrongPersist.dthU_c2m_bound6
  have hpt : ∀ z, -1 < z → ∀ θ,
      Work.Spaces.Dth (fun z θ => Work.Construction.c2m θ *
        Work.Construction.L12 (Work.Construction.Fstar α) z) z θ
      = (Work.Spaces.dthU Work.Construction.c2m) θ * Work.FTS.Nonlinear.FstarPkg.invH α z := by
    intro z hz θ
    show Real.sin (2 * θ) * deriv (fun θ' => Work.Construction.c2m θ' *
      Work.Construction.L12 (Work.Construction.Fstar α) z) θ
      = (Work.Spaces.dthU Work.Construction.c2m) θ * Work.FTS.Nonlinear.FstarPkg.invH α z
    rw [show (fun θ' => Work.Construction.c2m θ' *
          Work.Construction.L12 (Work.Construction.Fstar α) z)
        = (fun θ' => Work.Construction.c2m θ' * Work.FTS.Nonlinear.FstarPkg.invH α z) from
        funext fun θ' => congrArg (fun y => Work.Construction.c2m θ' * y)
          (Work.FTS.Nonlinear.FstarPkg.eqOn_L12_invH α hα hα1 hz)]
    rw [Work.Spaces.deriv_mul_const']
    show Real.sin (2 * θ) * (deriv Work.Construction.c2m θ *
        Work.FTS.Nonlinear.FstarPkg.invH α z)
      = (Work.Spaces.dthU Work.Construction.c2m) θ * Work.FTS.Nonlinear.FstarPkg.invH α z
    rw [Work.Spaces.dthU_apply]
    ring
  refine (Work.FTS.Nonlinear.FstarPkg.WlInf_congr (f := Work.Spaces.Dth (fun z θ =>
      Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z))
    (g := fun z θ => (Work.Spaces.dthU Work.Construction.c2m) θ *
      Work.FTS.Nonlinear.FstarPkg.invH α z) hpt α 4).2.mpr ?_
  refine WlInfMem_sep (a := Work.Spaces.dthU Work.Construction.c2m)
    (b := Work.FTS.Nonlinear.FstarPkg.invH α) (l := 4) (A := 1000) (C := C6)
    (Bf := fun k => 2 * α * (k.factorial : ℝ)) hα hα1 hC6pos.le ?_ ?_ ?_
  · intro θ
    have h := Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound 1 le_rfl (by norm_num) θ
    have hsin : Real.sin (2 * θ) ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq (2 * θ), sq_nonneg (Real.cos (2 * θ))]
    have h1 : (Work.Spaces.dthU Work.Construction.c2m) θ
        = Work.Spaces.dthU^[1] Work.Construction.c2m θ := by rw [Function.iterate_one]
    rw [h1]
    calc |Work.Spaces.dthU^[1] Work.Construction.c2m θ|
        ≤ 1000 * Real.sin (2 * θ) ^ 2 := h
      _ ≤ 1000 * 1 := by nlinarith
      _ = 1000 := by ring
  · intro j hj1 hj4 θ
    have h := hC6 (j + 1) (by omega) (by omega) θ
    rw [show (Work.Spaces.dthU^[j]) (Work.Spaces.dthU Work.Construction.c2m)
        = Work.Spaces.dthU^[j+1] Work.Construction.c2m from
        (Function.iterate_succ_apply Work.Spaces.dthU j Work.Construction.c2m).symm]
    exact h
  · intro k hk z hz
    exact Work.FTS.Nonlinear.FstarPkg.c2mInv_radial α hα k z hz

/-- **The `W5` data of the fixed profile `c₂(θ)·L₁₂(F_*)(z)`** (note `L₁₂(F_*)(z) = 2α/(1+z)`,
`Work.Construction.L12_Fstar_eq`).  `W5 α F a` is `SmoothOpen` + `WlInfMem α 4` +
`WlInf α 4 (·) ≤ a` for `F`, `Dz F`, `Dth F`; the `F`-part is available from
`Work.FTS.StrongPersist.c2m_L12Fstar_W6` (which gives `WlInfMem α 6` with norm `≤ Cα`, hence the
level-4 data by monotonicity), so the new facts are `WlInfMem α 4` of
`Dz (c₂·L₁₂(F_*))` and of `Dth (c₂·L₁₂(F_*))`, plus their two `WlInf`-bounds.

Route.  On the open quadrant, `Dz (c₂·L₁₂(F_*)) = c₂ · Dz (L₁₂(F_*))` and
`Dth (c₂·L₁₂(F_*)) = (Dth c₂) · L₁₂(F_*)`.  After the Leibniz-type identities for `pzIter` and
`DthIter`, every slot of the two `WlInf α 4` sums is a product of a `DthIter`-iterate of `c₂`
(bounded by `Work.FTS.Nonlinear.Pieces.DthIter_c2m_le` / `Work.FTS.StrongPersist.dthU_c2m_bound6`)
with a `pzIter`-iterate of `z ↦ L₁₂(F_*)(z) = 2α/(1+z)` — an explicit rational function whose
`(z+1)^k ∂_z^k` are uniformly bounded — multiplied by the single weight
`sin(2θ)^{-α/5}/(α + sin 2θ)`; bound the slots directly and conclude with `Work.Spaces.supAbs_le`.
`a` may depend on `α`. -/
theorem W5C2mL12Fstar : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
    Work.FTS.StrongEps.H5.W5 α (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) a := by
  intro α hαIoc
  obtain ⟨hα, hα1⟩ := hαIoc
  obtain ⟨_, _, hFacts⟩ := Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W
  have hFmem : Work.Spaces.WlInfMem α 4 (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) := (hFacts α hα hα1).1
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) := c2mL12Fstar_smoothOpen hα hα1
  have hDzmem := c2mL12Fstar_Dz_WlInfMem hα hα1
  have hDthmem := c2mL12Fstar_Dth_WlInfMem hα hα1
  set A : ℝ := Work.Spaces.WlInf α 4 (fun z θ => Work.Construction.c2m θ
    * Work.Construction.L12 (Work.Construction.Fstar α) z) with hAdef
  set B : ℝ := Work.Spaces.WlInf α 4 (Work.Spaces.Dz (fun z θ => Work.Construction.c2m θ
    * Work.Construction.L12 (Work.Construction.Fstar α) z)) with hBdef
  set C : ℝ := Work.Spaces.WlInf α 4 (Work.Spaces.Dth (fun z θ => Work.Construction.c2m θ
    * Work.Construction.L12 (Work.Construction.Fstar α) z)) with hCdef
  refine ⟨|A| + |B| + |C| + 1, by positivity, ?_⟩
  refine ⟨hsm, hFmem, ?_, hsm.Dz, hDzmem, ?_, hsm.Dth, hDthmem, ?_⟩
  · have h0 := le_abs_self A
    have h1 := abs_nonneg B
    have h2 := abs_nonneg C
    linarith
  · have h0 := le_abs_self B
    have h1 := abs_nonneg A
    have h2 := abs_nonneg C
    linarith
  · have h0 := le_abs_self C
    have h1 := abs_nonneg A
    have h2 := abs_nonneg B
    linarith

end Work.FTS.StrongEps.H5.Atoms
