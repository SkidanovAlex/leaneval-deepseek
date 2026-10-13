import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.ConstructionInstance.profile_add_z_pz_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology
open scoped Topology

namespace Work.FTS.Regularity

/-- `|a + b| ≤ |a| + |b|` for reals. -/
private theorem abs_add_le_aux {a b : ℝ} : |a + b| ≤ |a| + |b| := by
  simpa [Real.norm_eq_abs] using norm_add_le a b

/-- The polar angle satisfies `|θ(x)| ∈ [0,π/2]`. -/
private theorem abs_theta_mem_Iθ_aux (y : R3) : |Work.Cyl.theta y| ∈ Work.Spaces.Iθ := by
  refine ⟨abs_nonneg _, ?_⟩
  rw [abs_le]
  rw [Work.Cyl.theta]
  exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _), le_of_lt (Real.arctan_lt_pi_div_two _)⟩

/-- The azimuthal frame vector is a unit vector (and `0` on the axis). -/
private theorem norm_eTheta_le_one_aux (x : R3) : ‖Work.Cyl.eTheta x‖ ≤ 1 := by
  by_cases h : Work.Cyl.radial x = 0
  · rw [Work.Cyl.eTheta, h, div_zero, zero_smul, norm_zero]
    norm_num
  · rw [Work.Cyl.norm_eTheta x h]

/-! ## Auxiliary objects for the physical vorticity's time derivative

The physical vorticity is `ω(x,τ) = A(τ)⁻¹ • (F(ρ(x)^{3α}/B(τ), θ(x), τ) • e_θ(x))`, where
`F = F_* + g = profFull` and the profile is extended oddly in `θ`.  We record (i) the odd
extension `profOdd` of `profFull` and its identification with `ConstructionInstance.profile`,
(ii) the resulting product form of `physVort`, (iii) the `z`-derivative box of `F_*`, and
(iv) the two chain rules (in `z` and along the curve `s ↦ (ρ^{3α}/B(s), s)`). -/

/-- The odd extension in `θ` of the full profile `F = F_* + g`. -/
def profOdd (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (z θ τ : ℝ) : ℝ :=
  if 0 ≤ θ then profFull α g z θ τ else -profFull α g z (-θ) τ

/-- `ConstructionInstance.profile (pExp α) (gSlice g τ)` is the odd extension of `profFull`. -/
theorem profile_eq_profOdd (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ z θ : ℝ) :
    Work.ConstructionInstance.profile (pExp α) (gSlice g τ) z θ = profOdd α g z θ τ := by
  by_cases hθ : 0 ≤ θ
  · rw [Work.ConstructionInstance.profile_of_nonneg hθ, profOdd, if_pos hθ]
    rfl
  · rw [Work.ConstructionInstance.profile_of_neg hθ, profOdd, if_neg hθ]
    simp

/-- **Product form of the physical vorticity**: `ω(x,τ) = A(τ)⁻¹ • (F(z,θ,τ) • e_θ(x))` with
`z = ρ(x)^{3α}/B(τ)`, `θ = θ(x)` and the odd extension of the full profile. -/
theorem physVort_eq_smul (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (x : R3) (τ : ℝ) :
    physVort α A B g x τ
      = (A τ)⁻¹ • (profOdd α g (Work.Cyl.rho x ^ pExp α / B τ) (Work.Cyl.theta x) τ
          • Work.Cyl.eTheta x) := by
  rw [physVort_apply, Work.ConstructionInstance.omegaSz_apply, profile_eq_profOdd]

/-- **The `z`-derivative box of `F_*`**: `|∂_zF_*(z,θ)| ≤ 20p` for `0 < p ≤ 1`, `z ≥ 0` and
`θ ∈ Iθ`.  (`∂_zF_* = p(Γ(θ)/c(p))·2(1-z)/(1+z)³`, `Γ/c ≤ 10` and the rational factor is `≤ 2`
in absolute value on `z ≥ 0`.) -/
theorem pzFstar_abs_le_aux {p z θ : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.pz (Work.Construction.Fstar p) z θ| ≤ 20 * p := by
  have hc := (Work.Spaces.c_bounds p hp hp1).1
  have hcpos : 0 < Work.Spaces.c p := by linarith
  have hG0 : 0 ≤ Work.Spaces.Gam p θ := (Work.Spaces.Gam_bounds p θ hp hθ).1
  have hDz : Work.Spaces.pz (Work.Construction.Fstar p) z θ
      = p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * (2 * (1 - z) / (1 + z) ^ 3) := by
    have hfun : (fun z' => Work.Construction.Fstar p z' θ)
        = fun z' => (p * (Work.Spaces.Gam p θ / Work.Spaces.c p)) * Work.FM.Fstar z' := by
      funext z'; rw [Work.Construction.Fstar]
    rw [Work.Spaces.pz, hfun, deriv_const_mul_field, Work.FM.deriv_Fstar z (by linarith)]
  have hgb0 : 0 ≤ Work.Spaces.Gam p θ / Work.Spaces.c p := div_nonneg hG0 hcpos.le
  have hgle : Work.Spaces.Gam p θ / Work.Spaces.c p ≤ 10 := by
    rw [div_le_iff₀ hcpos]; nlinarith [(Work.Spaces.Gam_bounds p θ hp hθ).2]
  have hfrac : |2 * (1 - z) / (1 + z) ^ 3| ≤ 2 := by
    have h1z : (0 : ℝ) < (1 + z) ^ 3 := by positivity
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos h1z,
      div_le_iff₀ h1z]
    have h3 : |1 - z| ≤ (1 + z) ^ 3 := by
      have h4 : |1 - z| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
      have h5 : (1 : ℝ) ≤ 1 + z := by linarith
      nlinarith [sq_nonneg (1 + z), h5]
    linarith
  rw [hDz, abs_mul, abs_mul, abs_of_nonneg hp.le, abs_of_nonneg hgb0]
  calc p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * |2 * (1 - z) / (1 + z) ^ 3|
      ≤ p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * 2 :=
        mul_le_mul_of_nonneg_left hfrac (mul_nonneg hp.le hgb0)
    _ ≤ p * 10 * 2 := by
        have h : p * (Work.Spaces.Gam p θ / Work.Spaces.c p) ≤ p * 10 :=
          mul_le_mul_of_nonneg_left hgle hp.le
        linarith
    _ = 20 * p := by ring

/-! ### The two chain rules -/

/-- **Chain rule for the perturbation along a curve.**  If `G : ℝ × ℝ → ℝ` is `C¹` on the open
strip `Ioi(-1) ×ˢ Ioo(-1)(S+1)` and `zfun` has derivative `z'` at `τ`, then
`s ↦ g (zfun s) θ s` (= `G (zfun s, s)` with `G q = g q.1 θ q.2`) has derivative
`z'·∂_zg + ∂_τg` at `τ`. -/
theorem gComp_hasDerivAt_aux {g : ℝ → ℝ → ℝ → ℝ} {θ S τ z' : ℝ} (_hθ : θ ∈ Work.Spaces.Iθ)
    (hcont : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hτ : τ ∈ Set.Ioo (-1) (S + 1)) {zfun : ℝ → ℝ} (hz : -1 < zfun τ)
    (hzfun : HasDerivAt zfun z' τ) :
    HasDerivAt (fun s => g (zfun s) θ s)
      (z' * Work.Spaces.pz (gSlice g τ) (zfun τ) θ
        + deriv (fun t => g (zfun τ) θ t) τ) τ := by
  set G : ℝ × ℝ → ℝ := fun q => g q.1 θ q.2 with hGdef
  have hopen : IsOpen (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (S + 1)) :=
    (isOpen_Ioi : IsOpen (Set.Ioi (-1 : ℝ))).prod
      (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) (S + 1)))
  have hmem : (zfun τ, τ) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1) := ⟨hz, hτ⟩
  have hnhds : (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)) ∈ 𝓝 (zfun τ, τ) :=
    hopen.mem_nhds (x := (zfun τ, τ)) hmem
  have hdiff : DifferentiableAt ℝ G (zfun τ, τ) :=
    (hcont.contDiffAt hnhds).differentiableAt (by norm_num)
  have hF : HasFDerivAt G (fderiv ℝ G (zfun τ, τ)) (zfun τ, τ) := hdiff.hasFDerivAt
  set L : ℝ × ℝ →L[ℝ] ℝ := fderiv ℝ G (zfun τ, τ) with hLdef
  have hcurve : HasDerivAt (fun s : ℝ => (zfun s, s)) ((z', (1 : ℝ)) : ℝ × ℝ) τ :=
    hzfun.prodMk (hasDerivAt_id τ)
  have hcomp : HasDerivAt (G ∘ fun s : ℝ => (zfun s, s)) (L (z', 1)) τ :=
    hF.comp_hasDerivAt (f := fun s : ℝ => (zfun s, s)) τ hcurve
  have hcomp' : HasDerivAt (fun s => g (zfun s) θ s) (L (z', 1)) τ := by
    simpa [hGdef, Function.comp_def] using hcomp
  -- the two partial derivatives, identified with `L (1,0)` and `L (0,1)`
  have hL1 : L (1, 0) = Work.Spaces.pz (gSlice g τ) (zfun τ) θ := by
    have h := hF.comp_hasDerivAt (f := fun s : ℝ => (s, τ)) (zfun τ)
      (HasDerivAt.prodMk (hasDerivAt_id (zfun τ)) (hasDerivAt_const (zfun τ) τ))
    have hd : deriv (fun s => G (s, τ)) (zfun τ) = L (1, 0) := h.deriv
    have hev : deriv (fun s => G (s, τ)) (zfun τ)
        = Work.Spaces.pz (gSlice g τ) (zfun τ) θ := by
      simp [hGdef, Work.Spaces.pz]
    exact hd.symm.trans hev
  have hL2 : L (0, 1) = deriv (fun t => g (zfun τ) θ t) τ := by
    have h := hF.comp_hasDerivAt (f := fun s : ℝ => (zfun τ, s)) τ
      (HasDerivAt.prodMk (hasDerivAt_const τ (zfun τ)) (hasDerivAt_id τ))
    have hd : deriv ((fun q : ℝ × ℝ => g q.1 θ q.2) ∘ fun s : ℝ => (zfun τ, s)) τ
        = L (0, 1) := h.deriv
    simpa [hGdef, Function.comp_def] using hd.symm
  have hval : L (z', 1) = z' * Work.Spaces.pz (gSlice g τ) (zfun τ) θ
      + deriv (fun t => g (zfun τ) θ t) τ := by
    have hsplit : ((z', (1 : ℝ)) : ℝ × ℝ) = z' • ((1, 0) : ℝ × ℝ) + (1 : ℝ) • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    rw [hsplit, map_add, map_smul, map_smul, hL1, hL2]
    simp
  rw [hval] at hcomp'
  exact hcomp'

/-- **The `z`-derivative of the full profile splits.**  If `(z',τ) ↦ g z' θ τ` is `C¹` on the
open strip, then `∂_z(F_* + g) = ∂_zF_* + ∂_zg` for `z > -1`. -/
theorem profFull_deriv_z_aux {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {θ z τ : ℝ}
    (hcont : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hz : -1 < z) (hτ : τ ∈ Set.Ioo (-1) (S + 1)) :
    deriv (fun z' => profFull α g z' θ τ) z
      = Work.Spaces.pz (Work.Construction.Fstar (pExp α)) z θ
        + Work.Spaces.pz (gSlice g τ) z θ := by
  set G : ℝ × ℝ → ℝ := fun q => g q.1 θ q.2 with hGdef
  have hopen : IsOpen (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (S + 1)) :=
    (isOpen_Ioi : IsOpen (Set.Ioi (-1 : ℝ))).prod
      (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) (S + 1)))
  have hmem : (z, τ) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1) := ⟨hz, hτ⟩
  have hnhds : (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)) ∈ 𝓝 (z, τ) :=
    hopen.mem_nhds (x := (z, τ)) hmem
  have hdiff : DifferentiableAt ℝ G (z, τ) :=
    (hcont.contDiffAt hnhds).differentiableAt (by norm_num)
  have hGdiff : DifferentiableAt ℝ (fun z' => g z' θ τ) z := by
    have hp : DifferentiableAt ℝ (fun z' : ℝ => (z', τ)) z := by fun_prop
    simpa [hGdef, Function.comp_def] using hdiff.comp z hp
  have hF : HasDerivAt (fun z' => Work.Construction.Fstar (pExp α) z' θ)
      (Work.Spaces.pz (Work.Construction.Fstar (pExp α)) z θ) z :=
    Work.ConstructionInstance.hasDerivAt_Fstar_z z θ hz
  have hG : HasDerivAt (fun z' => g z' θ τ) (deriv (fun z' => g z' θ τ) z) z :=
    hGdiff.hasDerivAt
  have hsum := hF.add hG
  have hfun : (fun z' => profFull α g z' θ τ)
      = fun z' => Work.Construction.Fstar (pExp α) z' θ + g z' θ τ := by
    funext z'; rw [profFull_apply]
  have hval : Work.Spaces.pz (gSlice g τ) z θ = deriv (fun z' => g z' θ τ) z := rfl
  rw [hfun, hval]
  exact hsum.deriv

/-! ### The bookkeeping functions of the derivative -/

/-- The slope of the self-similar variable `s ↦ ρ^{3α}/B(s)` at time `τ`. -/
def zSlope (α : ℝ) (B : ℝ → ℝ) (ρ τ : ℝ) : ℝ :=
  -(ρ ^ pExp α * deriv B τ / (B τ) ^ 2)

/-- The `z`-derivative of the full profile `F = F_* + g` at a `τ`-slice, written as the sum of
the two summands' `z`-derivatives. -/
def pzProf (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (z θ τ : ℝ) : ℝ :=
  Work.Spaces.pz (Work.Construction.Fstar (pExp α)) z θ + Work.Spaces.pz (gSlice g τ) z θ

/-- The `τ`-derivative of the odd extension of the profile along the curve
`s ↦ (ρ^{3α}/B(s), s)`, as a function of `(ρ, θ, τ)`. -/
def dProfOdd (α : ℝ) (B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (ρ θ τ : ℝ) : ℝ :=
  if 0 ≤ θ then zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) θ τ
      + deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ
  else -(zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) (-θ) τ
      + deriv (fun t => g (ρ ^ pExp α / B τ) (-θ) t) τ)

/-- The value of `∂_τω(x,τ)`. -/
def vortDt (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (x : R3) (τ : ℝ) : R3 :=
  (A τ)⁻¹ • (dProfOdd α B g (Work.Cyl.rho x) (Work.Cyl.theta x) τ • Work.Cyl.eTheta x)
    + (-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (Work.Cyl.rho x ^ pExp α / B τ)
        (Work.Cyl.theta x) τ • Work.Cyl.eTheta x)

/-! ### The bound on the profile and its two derivatives -/

/-- `|F(z,θ,τ)| ≤ 20·3α + Ng` on the domain. -/
private theorem profFull_abs_le_aux {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {Ng : ℝ}
    (hp : 0 < pExp α) (hp1 : pExp α ≤ 1) (hNg : Jet α S Ng g) {z θ τ : ℝ} (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Icc 0 S) :
    |profFull α g z θ τ| ≤ 20 * pExp α + Ng := by
  have hα0 : 0 ≤ α := by
    have h : pExp α / 3 = α := by rw [pExp]; ring
    rw [← h]; positivity
  have hF : |Work.Construction.Fstar (pExp α) z θ| ≤ 20 * pExp α := by
    have h1 := Work.ConstructionInstance.Fstar_abs_le (p := pExp α) hp hp1 hz hθ
    have h2 : Work.FTS.Regularity.Gamma (pExp α / 3) θ ≤ 1 := by
      rw [show pExp α / 3 = α by rw [pExp]; ring]
      exact Work.ConstructionInstance.Gamma_le_one hα0 hθ
    calc |Work.Construction.Fstar (pExp α) z θ|
        ≤ 20 * pExp α * Work.FTS.Regularity.Gamma (pExp α / 3) θ := h1
      _ ≤ 20 * pExp α * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 20 * pExp α := by ring
  have hg : |g z θ τ| ≤ Ng := hNg.abs_le hz hθ hτ
  calc |profFull α g z θ τ| = |Work.Construction.Fstar (pExp α) z θ + g z θ τ| := by
        rw [profFull_apply]
    _ ≤ 20 * pExp α + Ng := abs_add_le_aux.trans (add_le_add hF hg)

/-- `|F(z,θ,τ)| ≤ 20·3α + Ng` for the odd extension, `|θ| ∈ Iθ`. -/
private theorem profOdd_abs_le_aux {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {Ng : ℝ}
    (hp : 0 < pExp α) (hp1 : pExp α ≤ 1) (hNg : Jet α S Ng g) {z θ τ : ℝ} (hz : 0 ≤ z)
    (hθ : |θ| ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Icc 0 S) :
    |profOdd α g z θ τ| ≤ 20 * pExp α + Ng := by
  rw [profOdd]
  split_ifs with hθ0
  · exact profFull_abs_le_aux hp hp1 hNg hz ⟨hθ0, le_trans (le_abs_self θ) hθ.2⟩ hτ
  · rw [abs_neg]
    have hθ₁ : -θ ∈ Work.Spaces.Iθ := by
      have h : -θ = |θ| := (abs_of_neg (not_le.mp hθ0)).symm
      rw [h]; exact hθ
    exact profFull_abs_le_aux hp hp1 hNg hz hθ₁ hτ

/-- **The z-derivative of the profile is bounded, jointly with the support**: on the support
region `z ≤ L` this is the two global boxes, and for `z > L` the profile vanishes identically in
`z`, so its `z`-derivative does too. -/
private theorem pzProf_mul_abs_le_aux {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {L Npz : ℝ}
    (hp : 0 < pExp α) (hp1 : pExp α ≤ 1) (hL0 : 0 < L)
    (hsupp : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z → profFull α g z θ τ = 0)
    (hcont : ∀ θ' ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ' q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hnpz : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (gSlice g τ) z θ| ≤ Npz)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |z * pzProf α g z θ τ| ≤ max L 1 * (20 * pExp α + Npz) := by
  have hNpz0 : 0 ≤ Npz :=
    le_trans (abs_nonneg _) (hnpz τ hτ 0 0 le_rfl ⟨le_rfl, by linarith [Real.pi_pos]⟩)
  rcases le_or_gt z L with hzL | hzL
  · have hstar := pzFstar_abs_le_aux hp hp1 hz hθ
    have hsum : |pzProf α g z θ τ| ≤ 20 * pExp α + Npz := by
      rw [pzProf]
      exact abs_add_le_aux.trans (add_le_add hstar (hnpz τ hτ z θ hz hθ))
    calc |z * pzProf α g z θ τ| = z * |pzProf α g z θ τ| := by
          rw [abs_mul, abs_of_nonneg hz]
      _ ≤ L * (20 * pExp α + Npz) := mul_le_mul hzL hsum (abs_nonneg _) hL0.le
      _ ≤ max L 1 * (20 * pExp α + Npz) :=
          mul_le_mul_of_nonneg_right (le_max_left L 1) (by linarith)
  · have hzero : pzProf α g z θ τ = 0 := by
      have hz1 : -1 < z := by linarith
      have hτmem : τ ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      have hsplit := profFull_deriv_z_aux (α := α) (S := S) (g := g) (θ := θ) (z := z) (τ := τ)
        (hcont θ hθ) hz1 hτmem
      have hev : (fun z' : ℝ => profFull α g z' θ τ) =ᶠ[𝓝 z] (fun _ => 0) := by
        filter_upwards [(isOpen_Ioi : IsOpen (Set.Ioi L)).mem_nhds hzL] with z' hz'
        exact hsupp τ hτ z' θ hz'.le
      have h0 : deriv (fun z' : ℝ => profFull α g z' θ τ) z = 0 := by
        rw [Filter.EventuallyEq.deriv_eq hev]
        simp
      rw [pzProf, ← hsplit]
      exact h0
    rw [hzero, mul_zero, abs_zero]
    exact mul_nonneg (le_trans zero_le_one (le_max_right L 1)) (by linarith)

/-- **The bound on the `τ`-derivative of the profile along the curve.**  Only the combination
`z·∂_zF` (with `z = ρ^{3α}/B τ`) enters, so the compact support of the profile enters through
`hpzProf` and the rest is the two-sided clock box. -/
private theorem profFull_curve_deriv_bound_aux {α : ℝ} {B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    {ρ θ τ b₀ b₂ Npz Nd L : ℝ} (hρ : 0 ≤ ρ) (hθ : θ ∈ Work.Spaces.Iθ)
    (hBpos : 0 < B τ) (hb₀pos : 0 < b₀) (hb₀ : b₀ ≤ B τ) (hb₂ : |deriv B τ| ≤ b₂)
    (hb₂0 : 0 ≤ b₂) (hNd0 : 0 ≤ Nd)
    (hpzProf : |(ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) θ τ|
      ≤ max L 1 * (20 * pExp α + Npz))
    (hnd : |deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ| ≤ Nd) :
    |zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) θ τ
        + deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ|
      ≤ (b₂ / b₀) * (max L 1 * (20 * pExp α + Npz)) + Nd := by
  have hBne : B τ ≠ 0 := ne_of_gt hBpos
  have hz0 : 0 ≤ ρ ^ pExp α / B τ := div_nonneg (Real.rpow_nonneg hρ _) hBpos.le
  have hsl : |zSlope α B ρ τ| = (ρ ^ pExp α / B τ) * (|deriv B τ| / B τ) := by
    rw [zSlope, abs_neg, abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg hρ _),
      abs_of_pos (pow_pos hBpos 2)]
    field_simp
  have hcoef : |deriv B τ| / B τ ≤ b₂ / b₀ :=
    (div_le_div_of_nonneg_right hb₂ hBpos.le).trans
      (div_le_div_of_nonneg_left hb₂0 hb₀pos hb₀)
  calc |zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) θ τ
        + deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ|
      ≤ |zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) θ τ|
          + |deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ| := abs_add_le _ _
    _ = |zSlope α B ρ τ| * |pzProf α g (ρ ^ pExp α / B τ) θ τ|
          + |deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ| := by
          rw [abs_mul]
    _ = (|deriv B τ| / B τ)
          * |(ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) θ τ|
          + |deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ| := by
          rw [hsl, abs_mul, abs_of_nonneg hz0]
          ring
    _ ≤ (b₂ / b₀) * (max L 1 * (20 * pExp α + Npz)) + Nd := by
          refine add_le_add ?_ hnd
          exact mul_le_mul hcoef hpzProf (abs_nonneg _) (div_nonneg hb₂0 hb₀pos.le)

/-! ### The chain rule for the odd-extended profile along the curve -/

/-- **The `τ`-derivative of the profile along `s ↦ (ρ^{3α}/B(s), s)`**, with the explicit value
`dProfOdd`.  This is the chain rule in the two variables `(z, τ)` — the diagonal curve moves in
both at once, so the joint `C¹` data `hcont` (not separate partial differentiability) is what is
used. -/
private theorem profOdd_hasDerivAt_aux {α S : ℝ} {B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {ρ θ τ : ℝ}
    (hθabs : |θ| ≤ Real.pi / 2) (hρ : 0 ≤ ρ)
    (hcont : ∀ θ' ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ' q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hτ : τ ∈ Set.Ioo (-1) (S + 1)) (hBpos : 0 < B τ) (hBd : HasDerivAt B (deriv B τ) τ) :
    HasDerivAt (fun s => profOdd α g (ρ ^ pExp α / B s) θ s) (dProfOdd α B g ρ θ τ) τ := by
  have hBne : B τ ≠ 0 := ne_of_gt hBpos
  have hz0 : 0 ≤ ρ ^ pExp α / B τ := div_nonneg (Real.rpow_nonneg hρ _) hBpos.le
  have hz1 : -1 < ρ ^ pExp α / B τ := by linarith
  have hz : HasDerivAt (fun s : ℝ => ρ ^ pExp α / B s) (zSlope α B ρ τ) τ := by
    have h := (hasDerivAt_const τ (ρ ^ pExp α)).div hBd hBne
    rw [zSlope]
    exact h.congr_deriv (by ring)
  -- the core: the derivative for a fixed angle in `Iθ`
  have hcore : ∀ θ₁ : ℝ, θ₁ ∈ Work.Spaces.Iθ →
      HasDerivAt (fun s => profFull α g (ρ ^ pExp α / B s) θ₁ s)
        (zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) θ₁ τ
          + deriv (fun t => g (ρ ^ pExp α / B τ) θ₁ t) τ) τ := by
    intro θ₁ hθ₁
    have hF : HasDerivAt (fun s => Work.Construction.Fstar (pExp α) (ρ ^ pExp α / B s) θ₁)
        (Work.Spaces.pz (Work.Construction.Fstar (pExp α)) (ρ ^ pExp α / B τ) θ₁
          * zSlope α B ρ τ) τ :=
      HasDerivAt.comp (h := fun s : ℝ => ρ ^ pExp α / B s) τ
        (Work.ConstructionInstance.hasDerivAt_Fstar_z (ρ ^ pExp α / B τ) θ₁ hz1) hz
    have hG := gComp_hasDerivAt_aux hθ₁ (hcont θ₁ hθ₁) hτ hz1 hz
    have hsum := hF.add hG
    have heq : (fun s : ℝ => profFull α g (ρ ^ pExp α / B s) θ₁ s)
        = fun s => Work.Construction.Fstar (pExp α) (ρ ^ pExp α / B s) θ₁
            + g (ρ ^ pExp α / B s) θ₁ s := by
      funext s; exact profFull_apply α g _ θ₁ s
    rw [heq]
    refine hsum.congr_deriv ?_
    rw [pzProf]
    ring
  rw [dProfOdd]
  by_cases hθ0 : 0 ≤ θ
  · rw [if_pos hθ0]
    have hθ₁ : θ ∈ Work.Spaces.Iθ := ⟨hθ0, le_trans (le_abs_self θ) hθabs⟩
    have heq : (fun s : ℝ => profOdd α g (ρ ^ pExp α / B s) θ s)
        = fun s => profFull α g (ρ ^ pExp α / B s) θ s := by
      funext s; rw [profOdd, if_pos hθ0]
    rw [heq]
    exact hcore θ hθ₁
  · rw [if_neg hθ0]
    have hθ₁ : -θ ∈ Work.Spaces.Iθ :=
      ⟨by linarith [not_le.mp hθ0], by linarith [neg_le_abs θ, hθabs]⟩
    have hneg := (hcore (-θ) hθ₁).neg
    have heq : (fun s : ℝ => profOdd α g (ρ ^ pExp α / B s) θ s)
        = fun s => -profFull α g (ρ ^ pExp α / B s) (-θ) s := by
      funext s; rw [profOdd, if_neg hθ0]
    rw [heq]
    exact hneg

/-! ### The main theorem -/

theorem physVort_hasDerivAt_and_bound {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.Regularity.RegPkg α S A B g) :
    (∀ x : Work.FTS.Regularity.R3, ∀ τ ∈ Set.Icc 0 S,
        HasDerivAt (fun s => Work.FTS.Regularity.physVort α A B g x s)
          (FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x τ) τ) ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ x : Work.FTS.Regularity.R3,
        ‖FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x τ‖ ≤ M) := by
  classical
  obtain ⟨a₀, a₁, ha₀pos, hAb⟩ := h.hAb
  obtain ⟨b₀, b₁, hb₀pos, hBb⟩ := h.hBb
  obtain ⟨a₂, hAd⟩ := h.hAd
  obtain ⟨b₂, hBd⟩ := h.hBd
  obtain ⟨Ng, hNg⟩ := h.hg
  obtain ⟨Npz, hNpz⟩ := h.hpz
  obtain ⟨Nd, hNd⟩ := h.hgdoth
  obtain ⟨L, hLpos, hLsupp⟩ := h.hsupp
  have hp : 0 < pExp α := h.pExp_pos
  have hp1 : pExp α ≤ 1 := h.pExp_le_one
  have hS0 : 0 ≤ S := h.hS.le
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) S := ⟨le_rfl, hS0⟩
  have hNg0 : 0 ≤ Ng := hNg.1
  have hNpz0 : 0 ≤ Npz := hNpz.1
  have hNd0 : 0 ≤ Nd := hNd.1
  have ha₂0 : 0 ≤ a₂ := le_trans (abs_nonneg _) (hAd 0 h0mem)
  have hb₂0 : 0 ≤ b₂ := le_trans (abs_nonneg _) (hBd 0 h0mem)
  set M : ℝ := a₀⁻¹ * (b₂ / b₀ * (max L 1 * (20 * pExp α + Npz)) + Nd)
      + (a₂ / a₀ ^ 2) * (20 * pExp α + Ng) with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have h1 : (0 : ℝ) ≤ max L 1 := le_trans zero_le_one (le_max_right L 1)
    have h2 : (0 : ℝ) ≤ 20 * pExp α + Npz := by linarith
    have h3 : (0 : ℝ) ≤ 20 * pExp α + Ng := by linarith
    positivity
  -- the three constants of the derivative bound
  have hdu : ∀ τ ∈ Set.Icc 0 S, ∀ ρ θ : ℝ, 0 ≤ ρ → |θ| ∈ Work.Spaces.Iθ →
      |dProfOdd α B g ρ θ τ|
        ≤ (b₂ / b₀) * (max L 1 * (20 * pExp α + Npz)) + Nd := by
    intro τ hτ ρ θ hρ hθmem
    have hθabs : |θ| ≤ Real.pi / 2 := hθmem.2
    have hBτ : 0 < B τ := h.hB τ hτ
    have hBτ₀ : b₀ ≤ B τ := (hBb τ hτ).1
    have hz0 : 0 ≤ ρ ^ pExp α / B τ := div_nonneg (Real.rpow_nonneg hρ _) hBτ.le
    have hpzProf : ∀ θ₁ ∈ Work.Spaces.Iθ,
        |(ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) θ₁ τ|
          ≤ max L 1 * (20 * pExp α + Npz) := fun θ₁ hθ₁ =>
      pzProf_mul_abs_le_aux hp hp1 hLpos hLsupp h.hcont
        (fun τ' hτ' z θ' hz' hθ' => hNpz.abs_le hz' hθ' hτ') hτ hz0 hθ₁
    rw [dProfOdd]
    split_ifs with hθ0
    · exact profFull_curve_deriv_bound_aux hρ ⟨hθ0, le_trans (le_abs_self θ) hθabs⟩ hBτ hb₀pos
        hBτ₀ (hBd τ hτ) hb₂0 hNd0
        (hpzProf θ ⟨hθ0, le_trans (le_abs_self θ) hθabs⟩)
        (hNd.abs_le hz0 ⟨hθ0, le_trans (le_abs_self θ) hθabs⟩ hτ)
    · rw [abs_neg]
      have hθ₁ : -θ ∈ Work.Spaces.Iθ :=
        ⟨by linarith [not_le.mp hθ0], by linarith [neg_le_abs θ, hθabs]⟩
      exact profFull_curve_deriv_bound_aux hρ hθ₁ hBτ hb₀pos hBτ₀ (hBd τ hτ) hb₂0 hNd0
        (hpzProf (-θ) hθ₁) (hNd.abs_le hz0 hθ₁ hτ)
  -- the derivative
  have hder : ∀ x : R3, ∀ τ ∈ Set.Icc 0 S,
      HasDerivAt (fun s => physVort α A B g x s) (vortDt α A B g x τ) τ := by
    intro x τ hτ
    have hmem : τ ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2, h.hS]⟩
    have hscal := profOdd_hasDerivAt_aux (α := α) (S := S) (B := B) (g := g)
      (ρ := Work.Cyl.rho x) (θ := Work.Cyl.theta x) (τ := τ)
      (abs_theta_mem_Iθ_aux x).2 (Work.Cyl.rho_nonneg x) h.hcont hmem
      (h.hB τ hτ) (h.hBdiff τ hτ)
    have hvec := hscal.smul_const (Work.Cyl.eTheta x)
    have hAinv : HasDerivAt (fun s : ℝ => (A s)⁻¹) (-(deriv A τ) / (A τ) ^ 2) τ :=
      (h.hAdiff τ hτ).inv (ne_of_gt (h.hA τ hτ))
    have hprod := hAinv.smul hvec
    have heq : (fun s : ℝ => physVort α A B g x s)
        = fun s : ℝ => (A s)⁻¹ • (profOdd α g (Work.Cyl.rho x ^ pExp α / B s)
            (Work.Cyl.theta x) s • Work.Cyl.eTheta x) := by
      funext s; rw [physVort_eq_smul]
    rw [heq, vortDt]
    exact hprod
  have htimeDeriv : ∀ x : R3, ∀ τ ∈ Set.Icc 0 S,
      FiniteTimeSingularity.timeDeriv (physVort α A B g) x τ = vortDt α A B g x τ := by
    intro x τ hτ
    rw [physVort_timeDeriv]
    exact (hder x τ hτ).deriv
  refine ⟨?_, ⟨M, hM0, ?_⟩⟩
  · intro x τ hτ
    rw [htimeDeriv x τ hτ]
    exact hder x τ hτ
  · intro τ hτ x
    have hAτ : 0 < A τ := h.hA τ hτ
    rw [htimeDeriv x τ hτ, vortDt]
    set ρ := Work.Cyl.rho x with hρdef
    set θ := Work.Cyl.theta x with hθdef
    set e : R3 := Work.Cyl.eTheta x with hedef
    have hρ0 : 0 ≤ ρ := Work.Cyl.rho_nonneg x
    have hθmem : |θ| ∈ Work.Spaces.Iθ := by rw [hθdef]; exact abs_theta_mem_Iθ_aux x
    have he1 : ‖e‖ ≤ 1 := by rw [hedef]; exact norm_eTheta_le_one_aux x
    have hAinv_le : (A τ)⁻¹ ≤ a₀⁻¹ := (inv_le_inv₀ hAτ ha₀pos).mpr ((hAb τ hτ).1)
    have hA2_le : |deriv A τ| / (A τ) ^ 2 ≤ a₂ / a₀ ^ 2 := by
      refine (div_le_div_of_nonneg_right (hAd τ hτ) (pow_pos hAτ 2).le).trans ?_
      exact div_le_div_of_nonneg_left ha₂0 (pow_pos ha₀pos 2)
        (pow_le_pow_left₀ ha₀pos.le (hAb τ hτ).1 2)
    have hu : ‖profOdd α g (ρ ^ pExp α / B τ) θ τ • e‖ ≤ 20 * pExp α + Ng :=
      calc ‖profOdd α g (ρ ^ pExp α / B τ) θ τ • e‖
          = |profOdd α g (ρ ^ pExp α / B τ) θ τ| * ‖e‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ |profOdd α g (ρ ^ pExp α / B τ) θ τ| * 1 :=
            mul_le_mul_of_nonneg_left he1 (abs_nonneg _)
        _ = |profOdd α g (ρ ^ pExp α / B τ) θ τ| := mul_one _
        _ ≤ 20 * pExp α + Ng :=
            profOdd_abs_le_aux hp hp1 hNg
              (div_nonneg (Real.rpow_nonneg hρ0 _) (h.hB τ hτ).le) hθmem hτ
    have hduE : ‖dProfOdd α B g ρ θ τ • e‖
        ≤ (b₂ / b₀) * (max L 1 * (20 * pExp α + Npz)) + Nd :=
      calc ‖dProfOdd α B g ρ θ τ • e‖ = |dProfOdd α B g ρ θ τ| * ‖e‖ := by
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ |dProfOdd α B g ρ θ τ| * 1 := mul_le_mul_of_nonneg_left he1 (abs_nonneg _)
        _ = |dProfOdd α B g ρ θ τ| := mul_one _
        _ ≤ (b₂ / b₀) * (max L 1 * (20 * pExp α + Npz)) + Nd := hdu τ hτ ρ θ hρ0 hθmem
    have hcoef1 : 0 ≤ b₂ / b₀ * (max L 1 * (20 * pExp α + Npz)) + Nd := by
      have h : 0 ≤ b₂ / b₀ * (max L 1 * (20 * pExp α + Npz)) :=
        mul_nonneg (div_nonneg hb₂0 hb₀pos.le)
          (mul_nonneg (le_trans zero_le_one (le_max_right L 1)) (by linarith))
      linarith
    have hcoef2 : 0 ≤ 20 * pExp α + Ng := by linarith
    calc ‖(A τ)⁻¹ • (dProfOdd α B g ρ θ τ • e)
          + (-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (ρ ^ pExp α / B τ) θ τ • e)‖
        ≤ ‖(A τ)⁻¹ • (dProfOdd α B g ρ θ τ • e)‖
            + ‖(-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (ρ ^ pExp α / B τ) θ τ • e)‖ :=
          norm_add_le _ _
      _ = (A τ)⁻¹ * ‖dProfOdd α B g ρ θ τ • e‖
            + |deriv A τ| / (A τ) ^ 2 * ‖profOdd α g (ρ ^ pExp α / B τ) θ τ • e‖ := by
          congr 1
          · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hAτ.le)]
          · rw [norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (pow_pos hAτ 2)]
      _ ≤ a₀⁻¹ * (b₂ / b₀ * (max L 1 * (20 * pExp α + Npz)) + Nd)
            + (a₂ / a₀ ^ 2) * (20 * pExp α + Ng) :=
          add_le_add (mul_le_mul hAinv_le hduE (norm_nonneg _) (inv_nonneg.mpr ha₀pos.le))
            (mul_le_mul hA2_le hu (norm_nonneg _) (div_nonneg ha₂0 (pow_pos ha₀pos 2).le))
      _ = M := by rw [hMdef]

end Work.FTS.Regularity
