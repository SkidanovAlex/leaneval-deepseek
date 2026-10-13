import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row22
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row23
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.fk_contDiffOn_four
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar
import Submission.Work.FTS.Nonlinear.FstarPkg.DthFstar_W
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.LocData.SmoothQuad_hLoc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-! ## `D_z`-iterates of a `C^n` function on `(0,∞)` -/

/-- **`DzdIter b u` is `C^{n-b}` when `u` is `C^n` on `(0,∞)`.**  The proof is the induction on
`b`: `DzdIter (b+1) u = z·(DzdIter b u)'`, the derivative lowers the order by one
(`ContDiffOn.derivWithin`) and multiplication by `z` is `C^∞`. -/
theorem contDiffOn_dzdIter_of {n : ℕ} {u : ℝ → ℝ} (hu : ContDiffOn ℝ n u (Set.Ioi 0)) :
    ∀ b : ℕ, b ≤ n →
      ContDiffOn ℝ (n - b) (Work.Elliptic.DzdIter b u) (Set.Ioi 0) := by
  intro b
  induction b with
  | zero =>
      intro _
      simpa using hu
  | succ b ih =>
      intro hb
      have hb' : b ≤ n := by omega
      have hcast : ((n - b : ℕ) : WithTop ℕ∞) = ((n - (b + 1) : ℕ) : WithTop ℕ∞) + 1 := by
        have h : n - b = (n - (b + 1)) + 1 := by omega
        rw [h, Nat.cast_add, Nat.cast_one]
      have h1 : ContDiffOn ℝ ((n - b : ℕ) : WithTop ℕ∞) (Work.Elliptic.DzdIter b u)
          (Set.Ioi 0) := ih hb'
      have h2 : ContDiffOn ℝ ((n - (b + 1) : ℕ) : WithTop ℕ∞)
          (deriv (Work.Elliptic.DzdIter b u)) (Set.Ioi 0) := by
        have hd := h1.derivWithin (isOpen_Ioi.uniqueDiffOn (𝕜 := ℝ))
          (m := ((n - (b + 1) : ℕ) : WithTop ℕ∞)) (by rw [← hcast])
        exact hd.congr (fun x hx => (derivWithin_of_isOpen isOpen_Ioi hx).symm)
      have h3 : ContDiffOn ℝ ((n - (b + 1) : ℕ) : WithTop ℕ∞)
          (fun z : ℝ => z * deriv (Work.Elliptic.DzdIter b u) z) (Set.Ioi 0) :=
        contDiffOn_id.mul h2
      rw [Work.Elliptic.DzdIter_succ]
      exact h3

/-! ## Differentiability of the `D_z`-iterates of the angular moment `FK g` -/

/-- **`DzdIter b (FK g)` is differentiable on `(0,∞)` for `b ≤ 3`.**  `FK g` is `C⁴` on `(0,∞)`
when `g` is `SmoothQuad` with `HkMem α 6 g` (`fk_contDiffOn_four`), and the `D_z`-iterates up to
order three only involve four derivatives. -/
theorem fk_dzdIter_diff {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 6 g)
    (b : ℕ) (hb : b ≤ 3) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Construction.FK g)) z := by
  have h4 : ContDiffOn ℝ 4 (fun z => Work.Construction.FK g z) (Set.Ioi 0) :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.fk_contDiffOn_four hα hα1 hsm hmem
  have hC : ContDiffOn ℝ (4 - b) (Work.Elliptic.DzdIter b (Work.Construction.FK g))
      (Set.Ioi 0) := contDiffOn_dzdIter_of h4 b (le_trans hb (by norm_num))
  have hne : ((4 - b : ℕ) : WithTop ℕ∞) ≠ 0 := by
    have hpos : 0 < 4 - b := by omega
    exact_mod_cast (ne_of_gt hpos)
  intro z hz
  exact (hC.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)

/-! ## The angular-profile bound `|D_θ^i(sin²θ·Γ(θ))| ≤ B·sin(2θ)^{α/5}` -/

/-- **The `D_θ`-iterates of `sin²θ·Γ(θ)` are bounded by `B·sin(2θ)^{α/5}`.**  The profile
`sin²θ·Γ(θ)` is the angular factor of `N₅^{gs}` (through `F_* = α(Γ/c)·2z/(1+z)²`).  The proof
is the Leibniz rule for `dthU` on the open interval (`dthU_iter_mul_Ioo`, applied to
`sin²·Γ`), the sharp bound `|dthU^j Γ| ≤ 100000·α·Γ` (`dthU_iter_Gam_abs_bound` +
`Tfun_abs_le`) together with `Γ ≤ sin(2θ)^{α/5}` (`Gam_le_sin_two_rpow`), and the bound
`|dthU^a(sin²)| ≤ B·sin(2θ)` of `angProfile_sinSq`.  At the two endpoints both sides vanish. -/
theorem dthSinSqGam_le : ∃ B : ℝ, 0 < B ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 θ|
        ≤ B * (Real.sin (2 * θ)) ^ (α / 5) := by
  obtain ⟨Bs, hBspos, -, hSinLe, hSinDth⟩ :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
  refine ⟨16 * (100000 + Bs * 100000) + 1, by positivity, ?_⟩
  intro α hα hα1 i hi1 hi4 θ hθ
  have hsnn : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsα : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hsnn _
  have hsle : Real.sin (2 * θ) ≤ (Real.sin (2 * θ)) ^ (α / 5) := by
    rcases eq_or_lt_of_le hsnn with h0 | h0
    · rw [← h0, Real.zero_rpow (by positivity : α / 5 ≠ 0)]
    · have hle : α / 5 ≤ 1 := by linarith
      have h := Real.rpow_le_rpow_of_exponent_ge (x := Real.sin (2 * θ)) (y := (1 : ℝ))
        (z := α / 5) h0 hs1 hle
      simpa using h
  have hGam : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
    Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθ
  have hαGam : α * Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) := by
    calc α * Work.Spaces.Gam α θ
        ≤ α * (Real.sin (2 * θ)) ^ (α / 5) := mul_le_mul_of_nonneg_left hGam hα.le
      _ ≤ 1 * (Real.sin (2 * θ)) ^ (α / 5) := mul_le_mul_of_nonneg_right hα1 hsα
      _ = (Real.sin (2 * θ)) ^ (α / 5) := one_mul _
  have hT : ∀ j : ℕ, j ≤ 4 → ∀ θ' ∈ Work.Spaces.Iθ,
      |Work.Spaces.Tfun (j - 1) α θ'| ≤ 100000 :=
    fun j hj θ' _ => Work.FTS.LocData.Tfun_abs_le (j - 1) (by omega) α hα hα1 θ'
  have hGamJ : ∀ j : ℕ, 1 ≤ j → j ≤ 4 →
      |Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t) θ|
        ≤ 100000 * (Real.sin (2 * θ)) ^ (α / 5) := by
    intro j hj hj4
    have h := Work.Spaces.dthU_iter_Gam_abs_bound j hj α hα 100000 (hT j hj4) θ hθ
    calc |Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * 100000 * Work.Spaces.Gam α θ := h
      _ = 100000 * (α * Work.Spaces.Gam α θ) := by ring
      _ ≤ 100000 * (Real.sin (2 * θ)) ^ (α / 5) :=
          mul_le_mul_of_nonneg_left hαGam (by norm_num)
  have hSin1 : ∀ a : ℕ, 1 ≤ a → a ≤ 4 →
      |Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ| ≤ Bs * Real.sin (2 * θ) := by
    intro a ha ha4
    have h := hSinDth a ha ha4 θ hθ
    have hconv : Work.Spaces.DthIter a (fun _ (θ' : ℝ) => -(Real.sin θ' ^ 2)) 0 θ
        = -(Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ) := by
      rw [Work.FTS.LocData.DthIter_rad_eq a (fun θ' => -(Real.sin θ' ^ 2)) 0 θ]
      have h2 := congrFun (Work.Spaces.dthU_iter_const_mul a (-1)
        (fun θ' => Real.sin θ' ^ 2)) θ
      simpa using h2
    rw [hconv, abs_neg] at h
    exact h
  -- the endpoint cases
  rcases eq_or_lt_of_le hθ.1 with h0 | h0pos
  · subst h0
    have hzero : Work.Spaces.DthIter i
        (fun _ (θ' : ℝ) => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 0 = 0 := by
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi1)
      subst hj
      simp [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
    rw [hzero]
    norm_num [Real.zero_rpow (show α / 5 ≠ 0 by positivity)]
  · rcases eq_or_lt_of_le hθ.2 with hpi | hpilt
    · subst hpi
      have h2pi : 2 * (Real.pi / 2) = Real.pi := by ring
      have hzero : Work.Spaces.DthIter i
          (fun _ (θ' : ℝ) => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 (Real.pi / 2) = 0 := by
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi1)
        subst hj
        simp [Work.Spaces.DthIter_succ, Work.Spaces.Dth, h2pi, Real.sin_pi]
      have hs0 : Real.sin (2 * (Real.pi / 2)) = 0 := by rw [h2pi, Real.sin_pi]
      rw [hzero, hs0]
      norm_num [Real.zero_rpow (show α / 5 ≠ 0 by positivity)]
    · -- the interior: the Leibniz rule and the term-by-term bounds
      have hioo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h0pos, hpilt⟩
      have hsmith : ContDiffOn ℝ ⊤ (fun θ' : ℝ => Real.sin θ' ^ 2)
          (Set.Ioo 0 (Real.pi / 2)) :=
        ((Real.contDiff_sin (n := ⊤)).pow 2).contDiffOn
      have hleib := Work.FTS.Nonlinear.FstarPkg.DthAux.dthU_iter_mul_Ioo i
        (fun θ' => Real.sin θ' ^ 2) (fun θ' => Work.Spaces.Gam α θ') hioo hsmith
        (Work.FTS.Nonlinear.FstarPkg.DthAux.contDiffOn_Gam_Ioo' α)
      have hDth : Work.Spaces.DthIter i
          (fun _ (θ' : ℝ) => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 θ
          = ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) *
              (Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ
                * Work.Spaces.dthU^[i - a] (fun t => Work.Spaces.Gam α t) θ) := by
        rw [Work.FTS.LocData.DthIter_rad_eq i
          (fun θ' => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 θ]
        exact hleib
      have hsin2 : |Real.sin θ ^ 2| ≤ 1 := by
        rw [abs_of_nonneg (sq_nonneg _)]
        calc Real.sin θ ^ 2 = |Real.sin θ| ^ 2 := by rw [sq_abs]
          _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_le_one θ) 2
          _ = 1 := by norm_num
      have hterm : ∀ a ∈ Finset.range (i + 1),
          |(i.choose a : ℝ) * (Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ
              * Work.Spaces.dthU^[i - a] (fun t => Work.Spaces.Gam α t) θ)|
            ≤ (i.choose a : ℝ) * ((100000 + Bs * 100000)
                * (Real.sin (2 * θ)) ^ (α / 5)) := by
        intro a ha
        have hai : a ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        rcases Nat.eq_zero_or_pos a with ha0 | hapos
        · -- `a = 0`: the `Γ`-iterate
          subst ha0
          rw [Function.iterate_zero_apply, Nat.sub_zero]
          have hΓ := hGamJ i hi1 hi4
          calc |Real.sin θ ^ 2 * Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
              = |Real.sin θ ^ 2| * |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ| :=
                abs_mul _ _
            _ ≤ 1 * (100000 * (Real.sin (2 * θ)) ^ (α / 5)) :=
                mul_le_mul hsin2 hΓ (abs_nonneg _) (by norm_num)
            _ ≤ (100000 + Bs * 100000) * (Real.sin (2 * θ)) ^ (α / 5) := by
                have hBnn : (0 : ℝ) ≤ Bs * 100000 := by positivity
                nlinarith [hsα, hBnn]
        · have hsinA := hSin1 a hapos (le_trans hai hi4)
          rcases Nat.eq_zero_or_pos (i - a) with hia0 | hiapos
          · -- `i = a`: the bare `Γ`
            have hΓ : Work.Spaces.dthU^[i - a] (fun t => Work.Spaces.Gam α t) θ
                = Work.Spaces.Gam α θ := by rw [hia0]; rfl
            have hGle : |Work.Spaces.Gam α θ| ≤ 1 := by
              rw [abs_of_nonneg (Work.Spaces.Gam_bounds α θ hα hθ).1]
              exact (Work.Spaces.Gam_bounds α θ hα hθ).2
            rw [hΓ]
            calc |Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ * Work.Spaces.Gam α θ|
                = |Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ| * |Work.Spaces.Gam α θ| :=
                  abs_mul _ _
              _ ≤ (Bs * Real.sin (2 * θ)) * 1 :=
                  mul_le_mul hsinA hGle (abs_nonneg _) (by positivity)
              _ = Bs * Real.sin (2 * θ) := by ring
              _ ≤ (100000 + Bs * 100000) * (Real.sin (2 * θ)) ^ (α / 5) := by
                  have h1 : Bs * Real.sin (2 * θ) ≤ Bs * (Real.sin (2 * θ)) ^ (α / 5) :=
                    mul_le_mul_of_nonneg_left hsle hBspos.le
                  have h2 : Bs * (Real.sin (2 * θ)) ^ (α / 5)
                      ≤ (100000 + Bs * 100000) * (Real.sin (2 * θ)) ^ (α / 5) := by
                    apply mul_le_mul_of_nonneg_right _ hsα
                    nlinarith [hBspos.le]
                  linarith
          · -- both iterates are positive
            have hΓ := hGamJ (i - a) hiapos (by omega)
            calc |Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ
                  * Work.Spaces.dthU^[i - a] (fun t => Work.Spaces.Gam α t) θ|
                = |Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ|
                  * |Work.Spaces.dthU^[i - a] (fun t => Work.Spaces.Gam α t) θ| := abs_mul _ _
              _ ≤ (Bs * Real.sin (2 * θ)) * (100000 * (Real.sin (2 * θ)) ^ (α / 5)) :=
                  mul_le_mul hsinA hΓ (abs_nonneg _) (by positivity)
              _ = Bs * 100000 * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
              _ ≤ Bs * 100000 * (Real.sin (2 * θ)) ^ (α / 5) := by
                  have h1 : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (α / 5)
                      ≤ 1 * (Real.sin (2 * θ)) ^ (α / 5) :=
                    mul_le_mul_of_nonneg_right hs1 hsα
                  have h2 : (1:ℝ) * (Real.sin (2 * θ)) ^ (α / 5)
                      = (Real.sin (2 * θ)) ^ (α / 5) := one_mul _
                  have h3 : (0:ℝ) ≤ Bs * 100000 := by positivity
                  nlinarith [h1, h2, h3, hsα]
              _ ≤ (100000 + Bs * 100000) * (Real.sin (2 * θ)) ^ (α / 5) := by
                  have h1 : (0:ℝ) ≤ 100000 * (Real.sin (2 * θ)) ^ (α / 5) := by positivity
                  nlinarith [hBspos.le, hsα]
      rw [hDth]
      calc |∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) *
              (Work.Spaces.dthU^[a] (fun θ' => Real.sin θ' ^ 2) θ
                * Work.Spaces.dthU^[i - a] (fun t => Work.Spaces.Gam α t) θ)|
          ≤ ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) *
              ((100000 + Bs * 100000) * (Real.sin (2 * θ)) ^ (α / 5)) :=
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
        _ = (∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ))
              * ((100000 + Bs * 100000) * (Real.sin (2 * θ)) ^ (α / 5)) := by
            rw [Finset.sum_mul]
        _ = (2 : ℝ) ^ i * ((100000 + Bs * 100000) * (Real.sin (2 * θ)) ^ (α / 5)) := by
            rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
        _ ≤ 16 * ((100000 + Bs * 100000) * (Real.sin (2 * θ)) ^ (α / 5)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have h2i : (2 : ℝ) ^ i ≤ 16 := by
              calc (2 : ℝ) ^ i ≤ (2 : ℝ) ^ 4 :=
                    pow_le_pow_right₀ (by norm_num) hi4
                _ = 16 := by norm_num
            exact h2i
        _ ≤ (16 * (100000 + Bs * 100000) + 1) * (Real.sin (2 * θ)) ^ (α / 5) := by
            have h1 : (0:ℝ) ≤ (Real.sin (2 * θ)) ^ (α / 5) := hsα
            nlinarith [h1]

/-! ## `SmoothInt` for the two profiles of `N₅^{sg}` -/

/-- `z ↦ c·hKer z` (extended to a function of `(z,θ)`) is `SmoothInt`: `hKer z = z/(1+z)²` is
analytic on `(-1,∞)`. -/
theorem smoothInt_const_hKer (c : ℝ) :
    Work.Spaces.SmoothInt (fun z _ => c * Work.Spaces.hKer z) := by
  have hbase : ContDiffOn ℝ ⊤ (fun z : ℝ => c * Work.Spaces.hKer z) (Set.Ioi (-1)) := by
    have h1 : (fun z : ℝ => c * Work.Spaces.hKer z)
        = fun z : ℝ => c * (z / (1 + z) ^ 2) := by
      funext z; rw [Work.Spaces.hKer_apply]
    rw [h1]
    refine contDiffOn_const.mul (ContDiffOn.div contDiffOn_id
      ((contDiffOn_const.add contDiffOn_id).pow 2) ?_)
    intro z hz
    have hz1 : (0 : ℝ) < 1 + z := by
      have := Set.mem_Ioi.mp hz; linarith
    exact pow_ne_zero 2 (ne_of_gt hz1)
  refine ⟨?_, fun θ _ => hbase⟩
  show ContDiffOn ℝ ⊤ (Function.uncurry (fun z (_ : ℝ) => c * Work.Spaces.hKer z))
    (Set.Ioi (-1) ×ˢ Set.Ioo 0 (Real.pi / 2))
  have hfun : Function.uncurry (fun z (_ : ℝ) => c * Work.Spaces.hKer z)
      = fun p : ℝ × ℝ => c * Work.Spaces.hKer p.1 := rfl
  rw [hfun]
  exact hbase.comp contDiffOn_fst (fun p hp => hp.1)

/-- `SmoothInt` is stable under multiplication by a constant. -/
theorem smoothInt_const_mul {f : ℝ → ℝ → ℝ} {c : ℝ} (hf : Work.Spaces.SmoothInt f) :
    Work.Spaces.SmoothInt (fun z θ => c * f z θ) := by
  constructor
  · have h1 : Function.uncurry (fun z θ => c * f z θ)
        = fun p : ℝ × ℝ => c * Function.uncurry f p := rfl
    rw [h1]
    exact contDiffOn_const.mul hf.1
  · intro θ hθ
    exact contDiffOn_const.mul (hf.2 θ hθ)

theorem row25 {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gs α g)
        + Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5sg α g)
        ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCipos, -⟩ := hN.pos
  obtain ⟨Bdth, hBdthpos, hdth⟩ := dthSinSqGam_le
  obtain ⟨Bsin, hBsinpos, hSinSmooth, hSinLe, hSinDth⟩ :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
  refine ⟨10 ^ 26 * (1 + Bdth) * (Ci + 1) + (10 ^ 6 * Bsin * Ci ^ 2 + 1) + 1,
    by positivity, ?_⟩
  intro α g Φs Φg hgal hstar hell hα hα1 hαα₂
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hreg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hreg6 : Work.FTS.Nonlin.RegQ α 6 g := hgal.reg
  have hsm : Work.FTS.LocData.SmoothQuad g := hreg4.1
  have hmem6 : Work.Spaces.HkMem α 6 g := hreg6.2.1
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hc1 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  obtain ⟨hFkmem, hFkle⟩ := hN.fkH α hIoc g hreg4 hgal.l12
  have hSqrtPos : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hAlphaSqrt : α / Real.sqrt α = Real.sqrt α := by
    rw [div_eq_iff (ne_of_gt hSqrtPos)]
    simpa [pow_two] using (Real.sq_sqrt hα.le).symm
  -- ## The angular moment is an `ℋ⁴`-function of controlled norm
  have hRintint : MeasureTheory.IntegrableOn
      (Work.FTS.Nonlinear.RadialProd.Rint (Work.Construction.FK g)) Work.Spaces.Iz :=
    Work.FTS.Nonlinear.RadialProd.integrable_Rint α (Work.Construction.FK g) hFkmem
  have hRr_le : (∫ z in Work.Spaces.Iz,
        Work.FTS.Nonlinear.RadialProd.Rint (Work.Construction.FK g) z)
      ≤ (Ci * Work.FTS.Nonlin.Xn α g) ^ 2 := by
    have h2 : (∫ z in Work.Spaces.Iz, Work.FTS.Nonlinear.RadialProd.Rint
        (Work.Construction.FK g) z)
        ≤ Work.Spaces.HkSq α 4 (fun z _ => Work.Construction.FK g z) :=
      Work.FTS.Nonlinear.RadialProd.Rr_le_HkSq α (Work.Construction.FK g)
    have h3 : Work.Spaces.HkSq α 4 (fun z _ => Work.Construction.FK g z)
        = (Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z)) ^ 2 := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 _)]
    rw [h3] at h2
    exact h2.trans (pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 _) hFkle 2)
  have hRint_le : ∀ z ∈ Work.Spaces.Iz,
      Work.FTS.Nonlinear.RadialProd.Rint (fun z => Work.FM.Fstar z * Work.Construction.FK g z) z
        ≤ (6400 * 200000 ^ 2)
          * Work.FTS.Nonlinear.RadialProd.Rint (Work.Construction.FK g) z := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
    · subst h0
      simp [Work.FTS.Nonlinear.RadialProd.Rint, Work.Spaces.w]
    · exact Work.FTS.Nonlinear.Pieces.Rint_mul_le Work.FM.Fstar (Work.Construction.FK g)
        (by norm_num)
        (fun k hk z hz' =>
          Work.FTS.Nonlinear.Pieces.dzdIter_Fstar_bound k (by omega) z (le_of_lt hz'))
        (fun b hb z hz' => Work.FTS.Nonlinear.Pieces.differentiableAt_dzdIter_Fstar b hz')
        (fun b hb z hz' => fk_dzdIter_diff hα hα1 hsm hmem6 b hb z hz') hzpos
  -- ## The angular profile
  set aG : ℝ → ℝ := fun θ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ with haG
  have haG0 : ∀ θ ∈ Work.Spaces.Iθ, |aG θ| ≤ 1 := by
    intro θ hθ
    have hG := Work.Spaces.Gam_bounds α θ hα hθ
    have h1 : Real.sin θ ^ 2 ≤ 1 := by
      calc Real.sin θ ^ 2 = |Real.sin θ| ^ 2 := by rw [sq_abs]
        _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_le_one θ) 2
        _ = 1 := by norm_num
    rw [haG, abs_of_nonneg (mul_nonneg (sq_nonneg _) hG.1)]
    calc Real.sin θ ^ 2 * Work.Spaces.Gam α θ ≤ 1 * 1 :=
          mul_le_mul h1 hG.2 hG.1 (by norm_num)
      _ = 1 := by norm_num
  have haG1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => aG θ') 0 θ|
        ≤ Bdth * (Real.sin (2 * θ)) ^ (α / 5) := by
    intro i hi1 hi4 θ hθ
    simpa only [haG] using hdth α hα hα1 i hi1 hi4 θ hθ
  -- ## The pointwise integrand bound
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.HkIntegrand α 4
          (fun z θ => aG θ * (Work.FM.Fstar z * Work.Construction.FK g z)) z θ
        ≤ (6400 * 200000 ^ 2) * Work.FTS.Nonlinear.RadialProd.Rint
            (Work.Construction.FK g) z
          * (1 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
            + 4 * Bdth ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) := by
    intro z hz θ hθ
    have h1 := Work.FTS.Nonlinear.Pieces.HkIntegrand_ang_rad_sin_le α aG
      (fun z => Work.FM.Fstar z * Work.Construction.FK g z)
      (B0 := 1) (B1 := Bdth) (κ := α / 5) (by norm_num) hBdthpos.le haG0 haG1 (z := z) hθ
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_right (hRint_le z hz) ?_
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsmE : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ :=
      Work.FTS.Nonlinear.RadialProd.smE_nonneg hθI
    have hs : 0 ≤ Real.sin (2 * θ) :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])).le
    have hr : 0 ≤ (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α) :=
      Real.rpow_nonneg hs _
    positivity
  -- ## The angular exponents
  have hexp1 : -1 < 2 * (α / 5) - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hexp2 : 2 * (α / 5) - Work.Spaces.gam α ≤ 0 := by rw [Work.Spaces.gam]; linarith
  have hI1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α))
      Work.Spaces.Iθ := (Work.Spaces.sin_two_rpow _ hexp1 hexp2).1
  have hm1 : ∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α) ≤ 1000 / (3 * α) := by
    have h := (Work.Spaces.sin_two_rpow _ hexp1 hexp2).2
    have hden : 2 * (α / 5) - Work.Spaces.gam α + 1 = 3 * α / 10 := by
      rw [Work.Spaces.gam]; ring
    rw [hden] at h
    have h2 : (100 : ℝ) / (3 * α / 10) = 1000 / (3 * α) := by
      field_simp
      ring
    linarith [h, le_of_eq h2]
  have hsq := Work.FTS.Nonlinear.Pieces.HkSq_ang_rad_of_le α hα aG
    (fun z θ => Work.FM.Fstar z * Work.Construction.FK g z) (Work.Construction.FK g)
    (B0 := 1) (B1 := Bdth) (κ := α / 5) (M1 := 1000 / (3 * α)) (C := 6400 * 200000 ^ 2)
    (by norm_num) hBdthpos.le (by positivity) (by norm_num) hpt hI1 hm1 hRintint
  -- ## The `N₅^{gs}` estimate
  have hXar : Work.FTS.Nonlin.Xn α
      (fun z θ => aG θ * (Work.FM.Fstar z * Work.Construction.FK g z))
      ≤ (10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth))
          * (Ci * Work.FTS.Nonlin.Xn α g / Real.sqrt α) := by
    set D : ℝ := 10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth) with hD
    have hDpos : 0 < D := by rw [hD]; positivity
    have hsqb : Work.Spaces.HkSq α 4
        (fun z θ => aG θ * (Work.FM.Fstar z * Work.Construction.FK g z))
        ≤ (D * (Ci * Work.FTS.Nonlin.Xn α g / Real.sqrt α)) ^ 2 := by
      have hCpos : (0 : ℝ) < 6400 * 200000 ^ 2 := by norm_num
      have hstep : Work.Spaces.HkSq α 4
          (fun z θ => aG θ * (Work.FM.Fstar z * Work.Construction.FK g z))
          ≤ (6400 * 200000 ^ 2) * (1 ^ 2 * 10000
              + 4 * Bdth ^ 2 * (1000 / (3 * α))) * ((Ci * Work.FTS.Nonlin.Xn α g) ^ 2) := by
        refine hsq.trans ?_
        exact mul_le_mul_of_nonneg_left hRr_le (by positivity)
      refine hstep.trans ?_
      have hfac : (D * (Ci * Work.FTS.Nonlin.Xn α g / Real.sqrt α)) ^ 2
          = D ^ 2 * (Ci * Work.FTS.Nonlin.Xn α g) ^ 2 / α := by
        rw [mul_pow, div_pow, Real.sq_sqrt hα.le]
        ring
      rw [hfac, hD]
      have hkey : 1 ^ 2 * 10000 + 4 * Bdth ^ 2 * (1000 / (3 * α))
          ≤ (10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth)) ^ 2 / α
            / (6400 * 200000 ^ 2) := by
        have hcore : 10 ^ 4 * α + 4000 * Bdth ^ 2 / 3
            ≤ 10 ^ 18 * (6400 * 200000 ^ 2) * (1 + Bdth) ^ 2 := by
          have h1 : Bdth ^ 2 ≤ (1 + Bdth) ^ 2 := by nlinarith [hBdthpos.le]
          have h2 : (1 : ℝ) ≤ (1 + Bdth) ^ 2 := by nlinarith [hBdthpos.le]
          nlinarith [h1, h2, hBdthpos.le, hα1, hα]
        rw [le_div_iff₀ hCpos, le_div_iff₀ hα]
        have he : (1 ^ 2 * 10000 + 4 * Bdth ^ 2 * (1000 / (3 * α)))
              * (6400 * 200000 ^ 2) * α
            = (6400 * 200000 ^ 2) * (10 ^ 4 * α + 4000 * Bdth ^ 2 / 3) := by
          field_simp
          try ring
        rw [he]
        have he2 : (10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth)) ^ 2
            = (6400 * 200000 ^ 2)
              * (10 ^ 18 * (6400 * 200000 ^ 2) * (1 + Bdth) ^ 2) := by
          ring
        rw [he2]
        exact mul_le_mul_of_nonneg_left hcore (by norm_num)
      calc (6400 * 200000 ^ 2) * (1 ^ 2 * 10000 + 4 * Bdth ^ 2 * (1000 / (3 * α)))
            * (Ci * Work.FTS.Nonlin.Xn α g) ^ 2
          ≤ (6400 * 200000 ^ 2)
              * ((10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth)) ^ 2 / α
                / (6400 * 200000 ^ 2)) * (Ci * Work.FTS.Nonlin.Xn α g) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey hCpos.le) (by positivity)
        _ = (10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth)) ^ 2
              * (Ci * Work.FTS.Nonlin.Xn α g) ^ 2 / α := by
            field_simp
            try ring
    calc Work.FTS.Nonlin.Xn α (fun z θ => aG θ * (Work.FM.Fstar z * Work.Construction.FK g z))
        = Real.sqrt (Work.Spaces.HkSq α 4
            (fun z θ => aG θ * (Work.FM.Fstar z * Work.Construction.FK g z))) := rfl
      _ ≤ Real.sqrt ((D * (Ci * Work.FTS.Nonlin.Xn α g / Real.sqrt α)) ^ 2) :=
          Real.sqrt_le_sqrt hsqb
      _ = D * (Ci * Work.FTS.Nonlin.Xn α g / Real.sqrt α) :=
          Real.sqrt_sq (by positivity)
  have hgs_eq : Work.FTS.Nonlin.N5gs α g = fun z θ =>
      -(α / Work.Spaces.c α) * (aG θ * (Work.FM.Fstar z * Work.Construction.FK g z)) := by
    funext z θ
    rw [Work.FTS.Nonlin.N5gs, Work.Construction.Fstar, haG, Work.FM.Fstar]
    field_simp
    try ring
  have hA : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gs α g)
      ≤ 10 ^ 26 * (1 + Bdth) * (Ci + 1) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
    rw [hgs_eq, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul]
    have hAc : |-(α / Work.Spaces.c α)| ≤ 10 * α := by
      rw [abs_neg, abs_of_nonneg (div_nonneg hα.le hcpos.le), div_le_iff₀ hcpos]
      nlinarith [hc1, hα]
    refine (mul_le_mul hAc hXar (Work.Spaces.HkNorm_nonneg α 4 _) (by positivity)).trans ?_
    have hstep : (10 * α) * ((10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth))
          * (Ci * Work.FTS.Nonlin.Xn α g / Real.sqrt α))
        = (10 * (10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth)) * Ci
            * (α / Real.sqrt α)) * Work.FTS.Nonlin.Xn α g := by ring
    rw [hstep, hAlphaSqrt]
    have hcoef : 10 * (10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth)) * Ci
        ≤ 10 ^ 26 * (1 + Bdth) * (Ci + 1) := by
      nlinarith [hBdthpos.le, hCipos]
    calc (10 * (10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth)) * Ci * Real.sqrt α)
          * Work.FTS.Nonlin.Xn α g
        = (10 * (10 ^ 9 * (6400 * 200000 ^ 2) * (1 + Bdth)) * Ci)
            * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by ring
      _ ≤ (10 ^ 26 * (1 + Bdth) * (Ci + 1))
            * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
  -- ## The `N₅^{sg}` estimate
  set lam : ℝ := Ci / (2 * Bsin) with hlam
  set cco : ℝ := 4 * Bsin * α / Ci with hcco
  set asq : ℝ → ℝ := fun θ => lam * (-(Real.sin θ ^ 2)) with hasq
  set hh : ℝ → ℝ → ℝ := fun z _ => cco * Work.Spaces.hKer z with hhh
  have hlam_pos : 0 < lam := by rw [hlam]; positivity
  have hSIA : Work.Spaces.SmoothInt (fun _ (θ : ℝ) => asq θ) := by
    have h := smoothInt_const_mul (c := lam) hSinSmooth
    have heq : (fun _ (θ : ℝ) => asq θ)
        = fun (z : ℝ) (θ : ℝ) => lam * (-(Real.sin θ ^ 2)) := by
      funext z θ; rw [hasq]
    rw [heq]; exact h
  have hSIH : Work.Spaces.SmoothInt hh := by
    have heq : hh = fun z (_ : ℝ) => cco * Work.Spaces.hKer z := by
      funext z θ; rw [hhh]
    rw [heq]; exact smoothInt_const_hKer cco
  have hAS0 : ∀ θ ∈ Work.Spaces.Iθ, |asq θ| ≤ Ci := by
    intro θ hθ
    have h2 : |-(Real.sin θ ^ 2)| ≤ Bsin := by
      simpa using hSinLe θ hθ
    have h3 : lam * Bsin = Ci / 2 := by rw [hlam]; field_simp
    rw [hasq, abs_mul, abs_of_nonneg hlam_pos.le]
    calc lam * |-(Real.sin θ ^ 2)| ≤ lam * Bsin :=
          mul_le_mul_of_nonneg_left h2 hlam_pos.le
      _ = Ci / 2 := h3
      _ ≤ Ci := by linarith [hCipos]
  have hAS1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => asq θ') 0 θ| ≤ Ci * Real.sin (2 * θ) := by
    intro i hi1 hi4 θ hθ
    have h1 : Work.Spaces.DthIter i (fun _ (θ' : ℝ) => asq θ')
        = fun z (θ' : ℝ) => lam * (Work.Spaces.DthIter i
            (fun _ (θ' : ℝ) => -(Real.sin θ' ^ 2)) z θ') := by
      rw [hasq]
      exact Work.FTS.Nonlinear.Pieces.RowsN0Aux.DthIter_const_mul i lam
        (fun _ (θ' : ℝ) => -(Real.sin θ' ^ 2))
    rw [h1, abs_mul, abs_of_nonneg hlam_pos.le]
    have h2 := hSinDth i hi1 hi4 θ hθ
    have hsnn : 0 ≤ Real.sin (2 * θ) :=
      Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
    calc lam * |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => -(Real.sin θ' ^ 2)) 0 θ|
        ≤ lam * (Bsin * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left h2 hlam_pos.le
      _ = Ci / 2 * Real.sin (2 * θ) := by rw [hlam]; field_simp; try ring
      _ ≤ Ci * Real.sin (2 * θ) := by nlinarith [hCipos, hsnn]
  have hHmem : Work.Spaces.WlInfMem α 4 hh := by
    have heq : hh = fun z (_ : ℝ) => cco * Work.Spaces.hKer z := by
      funext z θ; rw [hhh]
    rw [heq]
    exact (Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α cco).1
  have hwang := hN.wang α hIoc asq hh hSIA hSIH hAS0 hAS1 hHmem
  have hFle : Work.Spaces.WlInf α 4 (fun z (θ : ℝ) => asq θ * hh z θ)
      ≤ 800 * Bsin * Ci * α := by
    have hWh : Work.Spaces.WlInf α 4 hh ≤ 200 * |cco| := by
      have heq : hh = fun z (_ : ℝ) => cco * Work.Spaces.hKer z := by
        funext z θ; rw [hhh]
      rw [heq]
      exact (Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α cco).2
    have h1 : Ci * Ci * Work.Spaces.WlInf α 4 hh ≤ Ci * Ci * (200 * |cco|) :=
      mul_le_mul_of_nonneg_left hWh (by positivity)
    have h2 : Ci * Ci * (200 * |cco|) = 800 * Bsin * Ci * α := by
      rw [hcco, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * Bsin * α / Ci)]
      field_simp
      try ring
    linarith [hwang.2, h1, le_of_eq h2]
  have hFsm : Work.FTS.LocData.SmoothQuad (fun z (θ : ℝ) => asq θ * hh z θ) := by
    refine Work.FTS.LocData.smoothQuad_mul ?_ ?_
    · refine Work.FTS.LocData.smoothQuad_of_snd ?_
      exact contDiffOn_const.mul
        (((Real.contDiff_sin (n := Work.Stability.smoothOrder)).pow 2).neg.contDiffOn)
    · have heq : hh = fun z (_ : ℝ) => cco * Work.Spaces.hKer z := by
        funext z θ; rw [hhh]
      rw [heq]
      have heq2 : (fun z (_ : ℝ) => cco * Work.Spaces.hKer z)
          = fun z (_ : ℝ) => (cco / 2) * Work.FM.Fstar z := by
        funext z θ; rw [Work.Spaces.hKer_apply, Work.FM.Fstar]; ring
      rw [heq2]
      show ContDiffOn ℝ Work.Stability.smoothOrder
        (Function.uncurry (fun z (_ : ℝ) => (cco / 2) * Work.FM.Fstar z))
        (Set.Ioi (-1) ×ˢ Set.Ioo 0 (Real.pi / 2))
      have hun : Function.uncurry (fun z (_ : ℝ) => (cco / 2) * Work.FM.Fstar z)
          = fun p : ℝ × ℝ => (cco / 2)
              * Function.uncurry (fun z (_ : ℝ) => Work.FM.Fstar z) p := rfl
      rw [hun]
      exact contDiffOn_const.mul Work.FTS.Nonlinear.Pieces.smoothQuad_Fstar
  have hwprod := hN.wprod α hIoc (fun z (θ : ℝ) => asq θ * hh z θ) g hFsm hwang.1 hreg4
  have hsg_eq : Work.FTS.Nonlin.N5sg α g
      = fun z θ => (asq θ * hh z θ) * g z θ := by
    funext z θ
    simp only [Work.FTS.Nonlin.N5sg, Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1,
      hasq, hhh, hlam, hcco, Work.Spaces.hKer_apply]
    field_simp
    try ring
  have hB : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5sg α g)
      ≤ (10 ^ 6 * Bsin * Ci ^ 2 + 1) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
    rw [hsg_eq]
    refine hwprod.2.trans ?_
    have h2 : Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4
          (fun z (θ : ℝ) => asq θ * hh z θ) * Work.FTS.Nonlin.Xn α g
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (800 * Bsin * Ci * α)
          * Work.FTS.Nonlin.Xn α g :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hFle (mul_nonneg hCipos.le
          (Real.rpow_nonneg hα.le _))) hX0
    refine h2.trans ?_
    have hpow : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
      rw [Real.sqrt_eq_rpow]
      have h := Real.rpow_add hα (-(1 / 2 : ℝ)) (1 : ℝ)
      rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, Real.rpow_one] at h
      exact h.symm
    have hstep : Ci * α ^ (-(1 / 2 : ℝ)) * (800 * Bsin * Ci * α)
          * Work.FTS.Nonlin.Xn α g
        = (Ci * (800 * Bsin * Ci) * (α ^ (-(1 / 2 : ℝ)) * α))
          * Work.FTS.Nonlin.Xn α g := by ring
    rw [hstep, hpow]
    have hcoef : Ci * (800 * Bsin * Ci) ≤ 10 ^ 6 * Bsin * Ci ^ 2 + 1 := by
      nlinarith [hCipos, hBsinpos.le]
    calc (Ci * (800 * Bsin * Ci) * Real.sqrt α) * Work.FTS.Nonlin.Xn α g
        = (Ci * (800 * Bsin * Ci)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by ring
      _ ≤ (10 ^ 6 * Bsin * Ci ^ 2 + 1) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hnn : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g := by positivity
  linarith [hA, hB, hnn]

end Work.FTS.Nonlinear.Pieces.RNP
