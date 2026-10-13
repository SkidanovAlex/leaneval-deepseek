import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.Lgs_barrier` — E4b: `Lgs` of the barrier `(M + δφ)(z/L)^{-k} + η`

`Lgs α` is the ground-state-transformed operator of `Defs.lean`,
`Lgs α u = -α² D_z²u - 5α D_zu - ∂_θ²u - (4cot 2θ - tan θ)∂_θu`; it is *Euler-homogeneous*
in `z` and, applied to the separated barrier `u = A(θ)·(z/L)^{-k} + η` with `A = M + δφ`, it
returns `(z/L)^{-k}` times the one-dimensional expression

`α k (5 - αk)·A(θ) + δ·(𝓐φ(θ))`,  `𝓐φ = -φ'' - (4cot 2θ - tan θ)φ'`.

This is the exact computation `E4b` of the SB2/SB5 leaf plan: it identifies `Lgs` on the
barrier with `αk(5-αk)(M+δφ) + δ𝓐φ` and is what allows the maximum principle
(`Lgs_nonneg_of_max`) to be applied to a barrier built from a super-solution `φ` of
`𝓐φ ≥ -C` (`phiB_barrier`/`sb5_barrier`).

The only calculus input is that `z ↦ (z/L)^{-k}` is an eigenfunction of the Euler operator
with eigenvalue `-k` (`z·(z/L)^{-k}' = -k (z/L)^{-k}`) — here in the form
`x ∂_x` and `(x∂_x)²`, i.e. the two lemmas `mul_deriv_rpow_div_const` and
`mul_deriv_mul_deriv_rpow_div_const`.  **No differentiability of `φ` is used**: Mathlib's
`deriv` is totalised, and `∂_θ` sees only the factor `A(θ) = M + δφ(θ)`, so all the
angular identities hold unconditionally (`deriv_const_add`, `deriv_const_mul_field`).
-/

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false

/-! ## The Euler eigenfunction `z ↦ (z / L) ^ (-k)` -/

/-- `∂_x (x/L)^{-k} = -k (x/L)^{-k-1}/L` for `x ≠ 0`, `L ≠ 0` (chain rule). -/
private lemma deriv_rpow_div_const (k L x : ℝ) (hL : L ≠ 0) (hx : x ≠ 0) :
    deriv (fun y : ℝ => (y / L) ^ (-k)) x = (-k) * (x / L) ^ (-k - 1) / L := by
  have hx' : x / L ≠ 0 := div_ne_zero hx hL
  have h1 : HasDerivAt (fun y : ℝ => y ^ (-k)) ((-k) * (x / L) ^ (-k - 1)) (x / L) :=
    Real.hasDerivAt_rpow_const (Or.inl hx')
  have h2 : HasDerivAt (fun y : ℝ => y / L) (1 / L) x := (hasDerivAt_id x).div_const L
  have h3 := h1.comp x h2
  have h4 : deriv (fun y : ℝ => (y / L) ^ (-k)) x
      = ((-k) * (x / L) ^ (-k - 1)) * (1 / L) := by
    simpa [Function.comp_def] using h3.deriv
  rw [h4]; ring

/-- **`D_z`-eigenfunction**: `x · ∂_x (x/L)^{-k} = -k (x/L)^{-k}` for `x ≠ 0`, `L ≠ 0`. -/
lemma mul_deriv_rpow_div_const (k L x : ℝ) (hL : L ≠ 0) (hx : x ≠ 0) :
    x * deriv (fun y : ℝ => (y / L) ^ (-k)) x = -k * (x / L) ^ (-k) := by
  rw [deriv_rpow_div_const k L x hL hx,
    show x * ((-k) * (x / L) ^ (-k - 1) / L) = -k * ((x / L) ^ (-k - 1) * (x / L)) from by
      field_simp]
  have hq : x / L ≠ 0 := div_ne_zero hx hL
  rw [show (x / L) ^ (-k - 1) * (x / L) = (x / L) ^ (-k) from by
    rw [← Real.rpow_add_one hq (-k - 1)]; norm_num]

/-- **`D_z²`-eigenfunction**: `x · ∂_x (x ∂_x (x/L)^{-k}) = k² (x/L)^{-k}` for `x ≠ 0`,
`L ≠ 0`.  (Away from `0` the function `x ∂_x (x/L)^{-k}` agrees with `-k (x/L)^{-k}`,
which is differentiable there.) -/
lemma mul_deriv_mul_deriv_rpow_div_const (k L x : ℝ) (hL : L ≠ 0) (hx : x ≠ 0) :
    x * deriv (fun y : ℝ => y * deriv (fun y' : ℝ => (y' / L) ^ (-k)) y) x
      = k ^ 2 * (x / L) ^ (-k) := by
  have hev : (fun y : ℝ => y * deriv (fun y' : ℝ => (y' / L) ^ (-k)) y)
      =ᶠ[nhds x] (fun y : ℝ => -k * (y / L) ^ (-k)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hx)] with y hy
    exact mul_deriv_rpow_div_const k L y hL hy
  rw [hev.deriv_eq, deriv_const_mul_field]
  rw [show x * (-k * deriv (fun y' : ℝ => (y' / L) ^ (-k)) x)
      = -k * (x * deriv (fun y' : ℝ => (y' / L) ^ (-k)) x) from by ring,
    mul_deriv_rpow_div_const k L x hL hx]
  ring

/-! ## The statement -/

/-- **E4b `Lgs_barrier`**: the ground-state-transformed operator on the barrier
`u = (M + δφ(θ))(z/L)^{-k} + η` equals `(z/L)^{-k}` times `αk(5-αk)(M+δφ) + δ𝓐φ`. -/
theorem Lgs_barrier (α k L M δ η : ℝ) :
    Work.FTS_StreamBdry.SB25.LgsBarrier α k L M δ η := by
  intro φ hφ hL z θ hQd
  have hz : 0 < z := Qd_pos hQd
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hL0 : L ≠ 0 := ne_of_gt hL
  unfold Work.FTS_StreamBdry.SB25.Lgs
  -- angular derivative of the barrier: only the factor `A θ = M + δφθ` reacts
  have hpth : ∀ t : ℝ,
      Work.Spaces.pth (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) z t
        = (δ * (z / L) ^ (-k)) * deriv φ t := by
    intro t
    change deriv (fun t' : ℝ => (M + δ * φ t') * (z / L) ^ (-k) + η) t
      = (δ * (z / L) ^ (-k)) * deriv φ t
    rw [show (fun t' : ℝ => (M + δ * φ t') * (z / L) ^ (-k) + η)
        = (fun t' : ℝ => (η + M * (z / L) ^ (-k)) + (δ * (z / L) ^ (-k)) * φ t') from by
          funext t'; ring,
      deriv_const_add, deriv_const_mul_field]
  have hpth2 : Work.Spaces.pthIter 2 (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) z θ
      = (δ * (z / L) ^ (-k)) * deriv (deriv φ) θ := by
    change deriv (fun t : ℝ =>
      Work.Spaces.pth (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) z t) θ = _
    rw [show (fun t : ℝ =>
          Work.Spaces.pth (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) z t)
        = (fun t : ℝ => (δ * (z / L) ^ (-k)) * deriv φ t) from by funext t; exact hpth t,
      deriv_const_mul_field]
  -- radial derivative: only the factor `B z = (z/L)^{-k}` reacts
  have hpz : ∀ x : ℝ,
      Work.Spaces.pz (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) x θ
        = (M + δ * φ θ) * deriv (fun y : ℝ => (y / L) ^ (-k)) x := by
    intro x
    change deriv (fun x' : ℝ => (M + δ * φ θ) * (x' / L) ^ (-k) + η) x = _
    rw [show (fun x' : ℝ => (M + δ * φ θ) * (x' / L) ^ (-k) + η)
        = (fun x' : ℝ => η + (M + δ * φ θ) * (x' / L) ^ (-k)) from by funext x'; ring,
      deriv_const_add, deriv_const_mul_field]
  have hDz : Work.Spaces.Dz (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) z θ
      = -k * (M + δ * φ θ) * (z / L) ^ (-k) := by
    change z * Work.Spaces.pz (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) z θ = _
    rw [hpz z]
    rw [show z * ((M + δ * φ θ) * deriv (fun y : ℝ => (y / L) ^ (-k)) z)
        = (M + δ * φ θ) * (z * deriv (fun y : ℝ => (y / L) ^ (-k)) z) from by ring,
      mul_deriv_rpow_div_const k L z hL0 hz0]
    ring
  have hDz2 : Work.Spaces.DzIter 2 (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) z θ
      = k ^ 2 * (M + δ * φ θ) * (z / L) ^ (-k) := by
    change z * Work.Spaces.pz
      (Work.Spaces.Dz (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η)) z θ = _
    have hfun : (fun y : ℝ => Work.Spaces.Dz
          (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) y θ)
        = (fun y : ℝ => (M + δ * φ θ) * (y * deriv (fun y' : ℝ => (y' / L) ^ (-k)) y)) := by
      funext y
      change y * Work.Spaces.pz (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) y θ = _
      rw [hpz y]; ring
    change z * deriv (fun y : ℝ => Work.Spaces.Dz
      (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) y θ) z = _
    rw [hfun, deriv_const_mul_field]
    rw [show z * ((M + δ * φ θ) * deriv
          (fun y : ℝ => y * deriv (fun y' : ℝ => (y' / L) ^ (-k)) y) z)
        = (M + δ * φ θ) * (z * deriv
          (fun y : ℝ => y * deriv (fun y' : ℝ => (y' / L) ^ (-k)) y) z) from by ring,
      mul_deriv_mul_deriv_rpow_div_const k L z hL0 hz0]
    ring
  rw [hDz, hDz2, hpth θ, hpth2]
  ring

end Work.FTS_StreamBdry.SB25
