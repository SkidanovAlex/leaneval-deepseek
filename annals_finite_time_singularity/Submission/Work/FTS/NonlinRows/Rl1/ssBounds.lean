import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.NonlinRows.Rl1.starUopBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.NonlinRows.Rl1

/-
The five `ss` rows (both factors are star/concrete, none of them is the datum `g`).
Route (unprimed sibling: `Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss` +
`Work.FTS.Nonlinear.Pieces.Rl1.EssBound`):

* `N1ss = 2ℛ(Φ̃_*)F_*` and `N3ss = -2α𝒱(Φ̃_*)D_zF_*`: `star_Rop_le`/`star_Vop_le` give
  `|ℛ(Φ̃_*)|,|𝒱(Φ̃_*)| ≤ max Cs 0·α`, the profiles are bounded pointwise
  (`Fstar_pt`, `DzFstar_pt`), so the pointwise bound is `C·max Cs 0·α²·r/(1+r)²` and
  `Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep` gives `Fa ≤ ofReal (4C)`.
* `N2ss = -2𝒰(Φ̃_*)∂_θF_*`: `StarPkgo` bounds `K θ·𝒰(Φ̃_*)` but never `𝒰(Φ̃_*)`, so the
  factor `K θ` is paired with `∂_θF_*` through the *profile* bound
  `|∂_θF_*| ≤ 20α|Γ'|·r/(1+r)²` and the angular bound `|K θ|·|Γ'| ≤ 2α`; the coefficient
  factor is bounded by the mean-value bound `Work.FTS.NonlinRows.Rl1.starUopBound`.  Then
  `rowStep`.
* `N4ss = -(1/2)sin2θ FK(F_*) ∂_θF_*`: `FK_Fstar_pt` gives `FK(F_*) = α·2r/(1+r)²` and the
  same `∂_θF_*`-pairing as row `N₂`, so `|K θ·N4ss| ≤ 40α³·r/(1+r)²`; `rowStep`.
* `N5ss = -sin²θ FK(F_*) F_*`: `|K θ·N5ss| ≤ 3·(α2r/(1+r)²)(20αr/(1+r)²) ≤ 120α²r/(1+r)²`;
  `rowStep`.

All five rates are `≤ C·α² ≤ C·Env α g` (since `α ≤ 1` and `Env ≥ α²`).

Everything is *pointwise*: no `HkMem`-type hypothesis is needed, only the pointwise
coefficient bounds of `StarPkgo` (`star_Rop_le`, `star_Vop_le`, `starUopBound`) with the
explicit profile bounds of `F_*`, and the generic `L₁₂`-step `rl1Pieces.rowStep`.
-/

/-- `K θ·|Γ'(θ)| ≤ 2α` on `Iθ` (this is what lets the factor `K θ` be paired with the
angular derivative of the profile instead of with the profile itself). -/
theorem ss_K_deriv_le {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ| * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| ≤ 2 * α := by
  rw [abs_of_nonneg (Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_K_nonneg hθ)]
  exact Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_K_deriv_le hα hθ

/-- `|∂_θF_*| ≤ 20α|Γ'|·r/(1+r)²` (`hKer`-free form of `Pss_pth_Fstar_le`). -/
theorem ss_abs_pth_Fstar_le {α r θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hr : 0 ≤ r) :
    |Work.Spaces.pth (Work.Construction.Fstar α) r θ|
      ≤ 20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| * (r / (1 + r) ^ 2) := by
  have h := Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_pth_Fstar_le α r θ hα hα1 hr
  rwa [Work.Spaces.hKer_apply] at h

/-- `|FK(F_*)(r)| = α·2r/(1+r)²`. -/
theorem ss_abs_FK_Fstar {α r : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hr : 0 < r) :
    |Work.Construction.FK (Work.Construction.Fstar α) r| = α * (2 * (r / (1 + r) ^ 2)) := by
  rw [FK_Fstar_pt hα hα1, abs_of_nonneg (mul_nonneg hα.le (by positivity))]
  ring

/-- `r/(1+r)² ≤ 1` for `r > 0` (`hKer`-free form of `Pss_hKer_le_one`). -/
theorem ss_hker_le_one {r : ℝ} (hr : 0 < r) : r / (1 + r) ^ 2 ≤ 1 := by
  have h := Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_hKer_le_one hr.le
  rwa [Work.Spaces.hKer_apply] at h

/-! ## The five pointwise bounds -/

/-- Row `N₁^{ss} = 2ℛ(Φ̃_*)F_*`. -/
theorem ss_N1_pt {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs r θ|
        ≤ 120 * max Cs 0 * α ^ 2 * r / (1 + r) ^ 2 := by
  intro r hr θ hθ
  have hr0 : 0 < r := hr
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hm : 0 ≤ max Cs 0 := le_max_right Cs 0
  have h1 := Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_K_abs_le hθI
  have h2 := star_Rop_le hα hs r hr0 θ hθ
  have h3 := Fstar_pt hα hα1 hr0 hθI
  have hb1 : (0 : ℝ) ≤ max Cs 0 * α := mul_nonneg hm hα.le
  have hb3 : (0 : ℝ) ≤ 20 * α * r / (1 + r) ^ 2 := by positivity
  show |Work.Spaces.K θ * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
      * Work.Construction.Fstar α r θ)| ≤ 120 * max Cs 0 * α ^ 2 * r / (1 + r) ^ 2
  calc |Work.Spaces.K θ * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
        * Work.Construction.Fstar α r θ)|
      = (|Work.Spaces.K θ|
          * (2 * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|))
          * |Work.Construction.Fstar α r θ| := by
        simp only [abs_mul]
        norm_num
        ring
    _ ≤ (3 * (2 * (max Cs 0 * α))) * (20 * α * r / (1 + r) ^ 2) := by
        refine mul_le_mul (mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (by norm_num))
          (by positivity) (by norm_num)) h3 (abs_nonneg _)
          (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hb1))
    _ = 120 * max Cs 0 * α ^ 2 * r / (1 + r) ^ 2 := by ring

/-- Row `N₂^{ss} = -2𝒰(Φ̃_*)∂_θF_*`. -/
theorem ss_N2_pt {α Cs MU : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hα1 : α ≤ 1) (hMU : 0 ≤ MU)
    (hU : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ MU) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N2ss α Φs r θ|
        ≤ 80 * MU * α ^ 2 * r / (1 + r) ^ 2 := by
  intro r hr θ hθ
  have hr0 : 0 < r := hr
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hU0 := hU r θ hr0 hθI
  have hP := ss_abs_pth_Fstar_le (α := α) (r := r) (θ := θ) hα hα1 hr0.le
  have hKΓ := ss_K_deriv_le (α := α) (θ := θ) hα hθI
  show |Work.Spaces.K θ * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
      * Work.Spaces.pth (Work.Construction.Fstar α) r θ)|
      ≤ 80 * MU * α ^ 2 * r / (1 + r) ^ 2
  calc |Work.Spaces.K θ * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
        * Work.Spaces.pth (Work.Construction.Fstar α) r θ)|
      = (|Work.Spaces.K θ|
          * (2 * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|))
          * |Work.Spaces.pth (Work.Construction.Fstar α) r θ| := by
        simp only [abs_mul]
        norm_num
        ring
    _ ≤ (|Work.Spaces.K θ| * (2 * MU))
          * (20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| * (r / (1 + r) ^ 2)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hU0 (by norm_num)) (abs_nonneg _)) hP
          (abs_nonneg _) (mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) hMU))
    _ = (2 * MU * (20 * α * (r / (1 + r) ^ 2)))
          * (|Work.Spaces.K θ| * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|) := by ring
    _ ≤ (2 * MU * (20 * α * (r / (1 + r) ^ 2))) * (2 * α) := by
        refine mul_le_mul_of_nonneg_left hKΓ ?_
        exact mul_nonneg (mul_nonneg (by norm_num) hMU) (by positivity)
    _ = 80 * MU * α ^ 2 * r / (1 + r) ^ 2 := by ring_nf

/-- Row `N₃^{ss} = -2α𝒱(Φ̃_*)D_zF_*`. -/
theorem ss_N3_pt {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N3ss α Φs r θ|
        ≤ 120 * max Cs 0 * α ^ 3 * r / (1 + r) ^ 2 := by
  intro r hr θ hθ
  have hr0 : 0 < r := hr
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hm : 0 ≤ max Cs 0 := le_max_right Cs 0
  have h1 := Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_K_abs_le hθI
  have hV := star_Vop_le hα hs r hr0 θ hθ
  have hDz := DzFstar_pt hα hα1 hr0 hθI
  have hb1 : (0 : ℝ) ≤ max Cs 0 * α := mul_nonneg hm hα.le
  have hb3 : (0 : ℝ) ≤ 20 * α * (r / (1 + r) ^ 2) := by positivity
  show |Work.Spaces.K θ * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ
      * Work.Spaces.Dz (Work.Construction.Fstar α) r θ)|
      ≤ 120 * max Cs 0 * α ^ 3 * r / (1 + r) ^ 2
  calc |Work.Spaces.K θ * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ
        * Work.Spaces.Dz (Work.Construction.Fstar α) r θ)|
      = (|Work.Spaces.K θ|
          * (2 * α * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ|))
          * |Work.Spaces.Dz (Work.Construction.Fstar α) r θ| := by
        simp only [abs_mul, abs_of_nonneg hα.le]
        ring
    _ ≤ (3 * (2 * α * (max Cs 0 * α))) * (20 * α * (r / (1 + r) ^ 2)) := by
        refine mul_le_mul (mul_le_mul h1 (mul_le_mul_of_nonneg_left hV (by positivity))
          (by positivity) (by norm_num)) hDz (abs_nonneg _)
          (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) hα.le)
            (mul_nonneg hm hα.le)))
    _ = 120 * max Cs 0 * α ^ 3 * r / (1 + r) ^ 2 := by ring_nf

/-- Row `N₄^{ss} = -(1/2)sin2θ FK(F_*) ∂_θF_*`. -/
theorem ss_N4_pt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N4ss α r θ|
        ≤ 40 * α ^ 3 * r / (1 + r) ^ 2 := by
  intro r hr θ hθ
  have hr0 : 0 < r := hr
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hker0 : 0 ≤ r / (1 + r) ^ 2 := by positivity
  have hker1 : r / (1 + r) ^ 2 ≤ 1 := ss_hker_le_one hr0
  have hs2 : |Work.Construction.s2 θ| ≤ 1 := by
    rw [show Work.Construction.s2 θ = Real.sin (2 * θ) from rfl]
    exact abs_le.mpr ⟨Real.neg_one_le_sin (2 * θ), Real.sin_le_one (2 * θ)⟩
  have hFK := ss_abs_FK_Fstar (α := α) (r := r) hα hα1 hr0
  have hP := ss_abs_pth_Fstar_le (α := α) (r := r) (θ := θ) hα hα1 hr0.le
  have hKΓ := ss_K_deriv_le (α := α) (θ := θ) hα hθI
  show |Work.Spaces.K θ * (-(1 / 2) * Work.Construction.s2 θ
      * Work.Construction.FK (Work.Construction.Fstar α) r
      * Work.Spaces.pth (Work.Construction.Fstar α) r θ)|
      ≤ 40 * α ^ 3 * r / (1 + r) ^ 2
  calc |Work.Spaces.K θ * (-(1 / 2) * Work.Construction.s2 θ
        * Work.Construction.FK (Work.Construction.Fstar α) r
        * Work.Spaces.pth (Work.Construction.Fstar α) r θ)|
      = (1 / 2) * |Work.Construction.s2 θ|
          * |Work.Construction.FK (Work.Construction.Fstar α) r|
          * (|Work.Spaces.K θ| * |Work.Spaces.pth (Work.Construction.Fstar α) r θ|) := by
        simp only [abs_mul]
        norm_num
        ring
    _ ≤ (1 / 2) * 1 * (α * (2 * (r / (1 + r) ^ 2)))
          * (|Work.Spaces.K θ|
            * (20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|
              * (r / (1 + r) ^ 2))) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hs2 (by norm_num)) hFK.le
          (abs_nonneg _) (by norm_num)) (mul_le_mul_of_nonneg_left hP (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
    _ = 20 * α ^ 2 * (r / (1 + r) ^ 2) * (r / (1 + r) ^ 2)
          * (|Work.Spaces.K θ| * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|) := by ring
    _ ≤ 20 * α ^ 2 * (r / (1 + r) ^ 2) * (r / (1 + r) ^ 2) * (2 * α) := by
        refine mul_le_mul_of_nonneg_left hKΓ ?_
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg α)) hker0) hker0
    _ ≤ 20 * α ^ 2 * (r / (1 + r) ^ 2) * 1 * (2 * α) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hker1
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg α)) hker0)
    _ = 40 * α ^ 3 * r / (1 + r) ^ 2 := by ring_nf

/-- Row `N₅^{ss} = -sin²θ FK(F_*) F_*`. -/
theorem ss_N5_pt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N5ss α r θ|
        ≤ 120 * α ^ 2 * r / (1 + r) ^ 2 := by
  intro r hr θ hθ
  have hr0 : 0 < r := hr
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hker0 : 0 ≤ r / (1 + r) ^ 2 := by positivity
  have hker1 : r / (1 + r) ^ 2 ≤ 1 := ss_hker_le_one hr0
  have hsin : (Real.sin θ) ^ 2 ≤ 1 := pow_le_one₀
    (Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩)
    (Real.sin_le_one θ)
  have hFK := ss_abs_FK_Fstar (α := α) (r := r) hα hα1 hr0
  have hK := Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_K_abs_le hθI
  have hF := Fstar_pt hα hα1 hr0 hθI
  show |Work.Spaces.K θ * (-(Real.sin θ) ^ 2
      * Work.Construction.FK (Work.Construction.Fstar α) r
      * Work.Construction.Fstar α r θ)| ≤ 120 * α ^ 2 * r / (1 + r) ^ 2
  calc |Work.Spaces.K θ * (-(Real.sin θ) ^ 2
        * Work.Construction.FK (Work.Construction.Fstar α) r
        * Work.Construction.Fstar α r θ)|
      = (Real.sin θ) ^ 2 * |Work.Construction.FK (Work.Construction.Fstar α) r|
          * (|Work.Spaces.K θ| * |Work.Construction.Fstar α r θ|) := by
        simp only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin θ))]
        ring
    _ ≤ 1 * (α * (2 * (r / (1 + r) ^ 2))) * (3 * (20 * α * r / (1 + r) ^ 2)) := by
        refine mul_le_mul (mul_le_mul hsin hFK.le (abs_nonneg _) (by norm_num))
          (mul_le_mul hK hF (abs_nonneg _) (by norm_num))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (mul_nonneg (by norm_num) (mul_nonneg hα.le (by positivity)))
    _ = 120 * α ^ 2 * (r / (1 + r) ^ 2) * (r / (1 + r) ^ 2) := by ring_nf
    _ ≤ 120 * α ^ 2 * (r / (1 + r) ^ 2) * 1 := by
        exact mul_le_mul_of_nonneg_left hker1
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg α)) hker0)
    _ = 120 * α ^ 2 * r / (1 + r) ^ 2 := by ring_nf

/-- **The five `ss` rows.**  All five `L₁₂`-densities are bounded by `K·Env α g` with a
single `K` depending only on `Cs` (and on the universal constant of `starUopBound`). -/
theorem ssBounds {Cs : ℝ} : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs : Work.FTS.Galerkin.Fn},
    0 < α → α ≤ 1 → Work.FTS.Nonlin.GalClass α g → Work.FTS.VocabO.StarPkgo α Cs Φs →
    Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1ss α Φs)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2ss α Φs)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3ss α Φs)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N4ss α)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N5ss α)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) := by
  obtain ⟨CU, hCUpos, hCUb⟩ := starUopBound
  set Kc : ℝ := (3000 + 700 * CU) * max Cs 0 + (3000 + 700 * CU) with hKcdef
  have hm : 0 ≤ max Cs 0 := le_max_right Cs 0
  have hCU0 : 0 ≤ CU := hCUpos.le
  have hKcpos : 0 < Kc := by
    rw [hKcdef]
    have h1 : 0 < 3000 + 700 * CU := by linarith
    have h2 : 0 ≤ (3000 + 700 * CU) * max Cs 0 := mul_nonneg h1.le hm
    linarith
  have hKc0 : 0 ≤ Kc := hKcpos.le
  have hKc3000 : 3000 ≤ Kc := by
    rw [hKcdef]
    have h1 : 0 ≤ 3000 + 700 * CU := by linarith
    have h2 : 0 ≤ (3000 + 700 * CU) * max Cs 0 := mul_nonneg h1 hm
    linarith
  have hKc480 : 480 * max Cs 0 ≤ Kc := by
    rw [hKcdef]
    have h2 : 0 ≤ 3000 * max Cs 0 := mul_nonneg (by norm_num) hm
    have h3 : 0 ≤ 700 * CU * max Cs 0 := mul_nonneg (by linarith) hm
    have h4 : 0 ≤ 3000 + 700 * CU := by linarith
    nlinarith [h2, h3, h4]
  have hKc320 : 320 * CU * max Cs 0 ≤ Kc := by
    rw [hKcdef]
    have h3 : 0 ≤ 700 * CU * max Cs 0 := mul_nonneg (by linarith) hm
    have h4 : 0 ≤ 3000 + 700 * CU := by linarith
    have h5 : 0 ≤ 3000 * max Cs 0 := mul_nonneg (by norm_num) hm
    nlinarith [h3, h4, h5]
  refine ⟨Kc, hKcpos, ?_⟩
  intro α g Φs hα hα1 hGal hStar
  have hEnv : α ^ 2 ≤ Env α g := by
    rw [Env]
    have h1 : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
      mul_nonneg (Real.sqrt_nonneg α) (Work.Spaces.HkNorm_nonneg α 4 g)
    have h2 : 0 ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
    linarith
  have hα3 : α ^ 3 ≤ α ^ 2 :=
    pow_le_pow_of_le_one hα.le hα1 (show (2 : ℕ) ≤ 3 by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hC1 : 0 ≤ 120 * max Cs 0 * α ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hm) (sq_nonneg α)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N1ss α Φs) (C := 120 * max Cs 0 * α ^ 2) hC1
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => ss_N1_pt hα hα1 hStar r hr θ hθ))
    have h1 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1ss α Φs)
        ≤ ENNReal.ofReal ((4 : ℝ) * (120 * max Cs 0 * α ^ 2)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (480 : ℝ) * max Cs 0 * α ^ 2 ≤ Kc * α ^ 2 :=
      mul_le_mul_of_nonneg_right hKc480 (sq_nonneg α)
    have h3 : Kc * α ^ 2 ≤ Kc * Env α g := mul_le_mul_of_nonneg_left hEnv hKc0
    have h4 : (4 : ℝ) * (120 * max Cs 0 * α ^ 2) = 480 * max Cs 0 * α ^ 2 := by ring
    linarith
  · have hMU : 0 ≤ CU * max Cs 0 * α := mul_nonneg (mul_nonneg hCU0 hm) hα.le
    have hC2 : 0 ≤ 80 * (CU * max Cs 0 * α) * α ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hMU) (sq_nonneg α)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N2ss α Φs) (C := 80 * (CU * max Cs 0 * α) * α ^ 2) hC2
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => ss_N2_pt (Cs := Cs) hα hα1 hMU
          (fun z θ' hz hθ'I => hCUb hα hα1 hStar z hz θ' hθ'I) r hr θ hθ))
    have h1 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2ss α Φs)
        ≤ ENNReal.ofReal ((4 : ℝ) * (80 * (CU * max Cs 0 * α) * α ^ 2)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (320 : ℝ) * CU * max Cs 0 * α ^ 3 ≤ 320 * CU * max Cs 0 * α ^ 2 :=
      mul_le_mul_of_nonneg_left hα3 (mul_nonneg (mul_nonneg (by norm_num) hCU0) hm)
    have h3 : (320 : ℝ) * CU * max Cs 0 * α ^ 2 ≤ Kc * α ^ 2 :=
      mul_le_mul_of_nonneg_right hKc320 (sq_nonneg α)
    have h4 : Kc * α ^ 2 ≤ Kc * Env α g := mul_le_mul_of_nonneg_left hEnv hKc0
    have h5 : (4 : ℝ) * (80 * (CU * max Cs 0 * α) * α ^ 2)
        = 320 * CU * max Cs 0 * α ^ 3 := by ring
    linarith
  · have hC3 : 0 ≤ 120 * max Cs 0 * α ^ 3 :=
      mul_nonneg (mul_nonneg (by norm_num) hm) (pow_nonneg hα.le 3)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N3ss α Φs) (C := 120 * max Cs 0 * α ^ 3) hC3
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => ss_N3_pt hα hα1 hStar r hr θ hθ))
    have h1 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3ss α Φs)
        ≤ ENNReal.ofReal ((4 : ℝ) * (120 * max Cs 0 * α ^ 3)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (480 : ℝ) * max Cs 0 * α ^ 3 ≤ 480 * max Cs 0 * α ^ 2 :=
      mul_le_mul_of_nonneg_left hα3 (mul_nonneg (by norm_num) hm)
    have h3 : (480 : ℝ) * max Cs 0 * α ^ 2 ≤ Kc * α ^ 2 :=
      mul_le_mul_of_nonneg_right hKc480 (sq_nonneg α)
    have h4 : Kc * α ^ 2 ≤ Kc * Env α g := mul_le_mul_of_nonneg_left hEnv hKc0
    have h5 : (4 : ℝ) * (120 * max Cs 0 * α ^ 3) = 480 * max Cs 0 * α ^ 3 := by ring
    linarith
  · have hC4 : 0 ≤ 40 * α ^ 3 := mul_nonneg (by norm_num) (pow_nonneg hα.le 3)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N4ss α) (C := 40 * α ^ 3) hC4
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => ss_N4_pt hα hα1 r hr θ hθ))
    have h1 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N4ss α)
        ≤ ENNReal.ofReal ((4 : ℝ) * (40 * α ^ 3)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (160 : ℝ) * α ^ 3 ≤ 160 * α ^ 2 := by nlinarith [hα3, hα.le]
    have h3 : (160 : ℝ) * α ^ 2 ≤ Kc * α ^ 2 := by
      have h160 : (160 : ℝ) ≤ Kc := by linarith [hKc3000]
      exact mul_le_mul_of_nonneg_right h160 (sq_nonneg α)
    have h4 : Kc * α ^ 2 ≤ Kc * Env α g := mul_le_mul_of_nonneg_left hEnv hKc0
    have h5 : (4 : ℝ) * (40 * α ^ 3) = 160 * α ^ 3 := by ring
    linarith
  · have hC5 : 0 ≤ 120 * α ^ 2 := mul_nonneg (by norm_num) (sq_nonneg α)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N5ss α) (C := 120 * α ^ 2) hC5
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => ss_N5_pt hα hα1 r hr θ hθ))
    have h1 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N5ss α)
        ≤ ENNReal.ofReal ((4 : ℝ) * (120 * α ^ 2)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (480 : ℝ) * α ^ 2 ≤ Kc * α ^ 2 := by
      have h480 : (480 : ℝ) ≤ Kc := by linarith [hKc3000]
      exact mul_le_mul_of_nonneg_right h480 (sq_nonneg α)
    have h3 : Kc * α ^ 2 ≤ Kc * Env α g := mul_le_mul_of_nonneg_left hEnv hKc0
    have h4 : (4 : ℝ) * (120 * α ^ 2) = 480 * α ^ 2 := by ring
    linarith

end Work.FTS.NonlinRows.Rl1
