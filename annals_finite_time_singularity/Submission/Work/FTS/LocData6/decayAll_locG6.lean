/-
# `decayAll_locG6` — the decay clause of the order-`6` localised datum

The perturbation `locG α L β (hLoc α) = locData α L β (hLoc α) - F_*` of the N9 datum is
*separable*: `locG α L β (hLoc α) = locR α L β(z)·Γ(θ)` (`LocDataExt.locG_eq_locR_Gam`), and its
radial factor becomes the plain profile beyond `max (2L) (7/4)`:
`locR α L β z = -(α/c)·FM.Fstar z` there (`LocDataExt.locR_eq_of_ge`, because the cut-off factor
`1 - χ(z/L)` is `1` for `z ≥ 2L` and the bump `bumpZ` dies at `7/4`).

Consequently every plain derivative `∂_z^j∂_θ^i` and every mixed derivative `D_z^bD_θ^a` of
`locG` factors into an angular factor (a fixed number, for a fixed `θ`) times an iterate applied
to `locR` — `Work.FTS.GalBasis.pthIter_mul_zonly_thetaonly`,
`Work.FTS.GalBasis.pzIter_mul_zonly_thetaonly`, `LocDataExt.mixed_sepGam` — and beyond the
localisation scale `locR` is a constant multiple of `FM.Fstar`.  The decay therefore reduces to
the two elementary facts that the iterates of the plain profile `FM.Fstar z = 2z/(1+z)²` tend to
`0` at `z = ∞`:

* `tendsto_deriv_iter_Fstar` — `∂^j F_* → 0`;
* `tendsto_DzIter_Fstar` — `D_z^b F_* → 0`.

Both are proved here from the *closed form* of the derivatives,
`deriv^[j] F_* z = 2·(-1)^j·j!·(z-j)/(1+z)^(j+2)` (`deriv_iter_Fstar_eq`, by induction, using
only Mathlib), whose right-hand side is dominated by `2·j!·(j+1)/(1+z)` (`Fstar_deriv_abs_le`).
The `D_z`-iterate is then expanded into the `z^k ∂^k` (Stirling) combination
(`Work.Spaces.DzIter_eq_sum_scoef`; the analyticity hypothesis it asks for holds because
`F_*` is a rational function with its only pole at `z = -1`), each summand of which vanishes by
the weighted bound `Fstar_zpow_deriv_abs_le`.

Note that the argument is *order-independent*: it gives
`DecayAll n (locG α L β (hLoc α))` for every `n`, and no hypothesis on `α` or `β` is needed —
only `L ≥ 1`, which makes the localisation scale `max (2L) (7/4)` positive.

(Do **not** replace the two local radial lemmas by `LocData.FstarAux`-based ones: the workspace
has two competing definitions of `Work.FTS.LocData.T1`, and any module importing
`Submission.Work.FTS.LocData.FstarAux` clashes with `LocData6.Defs`, which pulls in
`Submission.Work.FTS.LocData.DzIter_bumpZ_bound`.)

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.Stability.HkSqZfar
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocDataExt.SepFactor
import Submission.Work.FTS.GalBasis.FamEAux.Basic
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The radial profile `FM.Fstar z = 2z/(1+z)²`: closed form of the derivatives -/

/-- `F_*` is a rational function whose only pole is at `z = -1`, hence analytic (order `⊤`) on
the half-line `(-1,∞)`. -/
private theorem contDiffOn_Fstar_analytic :
    ContDiffOn ℝ ⊤ (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi (-1)) := by
  have hnum : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun z : ℝ => 2 * z) (Set.Ioi (-1)) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have h := hnum.div hden
    (fun z hz => pow_ne_zero 2 (by have hz' : (-1 : ℝ) < z := hz; linarith))
  change ContDiffOn ℝ (⊤ : WithTop ℕ∞) ((fun z : ℝ => 2 * z) / (fun z : ℝ => (1 + z) ^ 2))
    (Set.Ioi (-1))
  exact h

/-- **The one-step derivative of the closed form**: with
`φ_j(w) = 2·(-1)^j·j!·(w-j)/(1+w)^(j+2)`, one has `φ_j' = φ_{j+1}`. -/
private theorem hasDerivAt_Fstar_formula (j : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    HasDerivAt (fun w : ℝ => 2 * (-1 : ℝ) ^ j * (j.factorial : ℝ) * (w - (j : ℝ))
        / (1 + w) ^ (j + 2))
      (2 * (-1 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ) * (z - ((j + 1 : ℕ) : ℝ))
        / (1 + z) ^ (j + 1 + 2)) z := by
  have hz' : (1 : ℝ) + z ≠ 0 := by simp only [Set.mem_Ioi] at hz; linarith
  have hnum : HasDerivAt (fun w : ℝ => 2 * (-1 : ℝ) ^ j * (j.factorial : ℝ) * (w - (j : ℝ)))
      (2 * (-1 : ℝ) ^ j * (j.factorial : ℝ)) z := by
    have h : HasDerivAt (fun w : ℝ => w - ((j : ℕ) : ℝ)) 1 z :=
      (hasDerivAt_id z).sub_const ((j : ℕ) : ℝ)
    have h2 := h.const_mul (2 * (-1 : ℝ) ^ j * (j.factorial : ℝ))
    simpa [mul_assoc] using h2
  have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ (j + 2))
      (((j + 2 : ℕ) : ℝ) * (1 + z) ^ (j + 1)) z := by
    have h : HasDerivAt (fun w : ℝ => 1 + w) 1 z := (hasDerivAt_id z).const_add 1
    have h2 := h.pow (j + 2)
    rw [show (fun w : ℝ => (1 + w) ^ (j + 2)) = (fun w : ℝ => 1 + w) ^ (j + 2) from by
      funext w; simp [Pi.pow_apply]]
    simpa using h2
  have hdiv := hnum.div hden (pow_ne_zero _ hz')
  convert hdiv using 1
  · have h1 : (1 + z) ^ (j + 1 + 2) = (1 + z) ^ (j + 1) * (1 + z) ^ 2 := by
      rw [show j + 1 + 2 = (j + 1) + 2 by omega, pow_add]
    have h2 : ((1 + z) ^ (j + 2)) ^ 2 = (1 + z) ^ (j + 2) * (1 + z) ^ (j + 2) := pow_two _
    have h3 : (1 + z) ^ (j + 2) = (1 + z) ^ (j + 1) * (1 + z) := by
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
    rw [h1, h2, h3]
    have hu : (1 + z) ^ (j + 1) ≠ 0 := pow_ne_zero _ hz'
    field_simp
    rw [show (-1 : ℝ) ^ (j + 1) = -(-1) ^ j by rw [pow_succ]; ring]
    rw [show ((j + 1).factorial : ℝ) = ((j : ℝ) + 1) * (j.factorial : ℝ) by
      rw [Nat.factorial_succ]; push_cast; ring]
    push_cast
    ring

/-- **The closed form of the iterated derivatives of the plain profile**:
`∂^j F_* z = 2·(-1)^j·j!·(z-j)/(1+z)^(j+2)` on `(-1,∞)`. -/
private theorem deriv_iter_Fstar_eq (j : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    deriv^[j] (fun z => Work.FM.Fstar z) z
      = 2 * (-1 : ℝ) ^ j * (j.factorial : ℝ) * (z - (j : ℝ)) / (1 + z) ^ (j + 2) := by
  induction j generalizing z with
  | zero =>
      rw [Function.iterate_zero_apply]
      simp only [Work.FM.Fstar]
      norm_num
  | succ n ih =>
      have hEqOn : Set.EqOn (deriv^[n] (fun z => Work.FM.Fstar z))
          (fun w : ℝ => 2 * (-1 : ℝ) ^ n * (n.factorial : ℝ) * (w - (n : ℝ))
            / (1 + w) ^ (n + 2)) (Set.Ioi (-1)) := fun w hw => ih hw
      rw [Function.iterate_succ_apply', hEqOn.deriv isOpen_Ioi hz]
      exact (hasDerivAt_Fstar_formula n hz).deriv

/-! ## The decay bounds -/

/-- **`∂^j F_*` decays like `1/z`**: `|∂^j F_* z| ≤ 2·j!·(j+1)/(1+z)` for `z ≥ 1`. -/
private theorem Fstar_deriv_abs_le (j : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    |deriv^[j] (fun z => Work.FM.Fstar z) z|
      ≤ 2 * (j.factorial : ℝ) * ((j : ℝ) + 1) / (1 + z) := by
  have hzI : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have hpos : (0 : ℝ) < 1 + z := by linarith
  have hden : (0 : ℝ) < (1 + z) ^ (j + 2) := pow_pos hpos _
  have hfac : (0 : ℝ) ≤ (j.factorial : ℝ) := by positivity
  rw [deriv_iter_Fstar_eq j hzI]
  have habs : |2 * (-1 : ℝ) ^ j * (j.factorial : ℝ) * (z - (j : ℝ)) / (1 + z) ^ (j + 2)|
      = 2 * (j.factorial : ℝ) * |z - (j : ℝ)| / (1 + z) ^ (j + 2) := by
    rw [abs_div, abs_of_pos hden, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hfac]
    ring
  rw [habs, div_le_div_iff₀ hden hpos]
  have hkey : |z - (j : ℝ)| ≤ ((j : ℝ) + 1) * (1 + z) := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    rw [abs_le]
    constructor <;> nlinarith [hz, hj]
  have hstep1 : 2 * (j.factorial : ℝ) * |z - (j : ℝ)| * (1 + z)
      ≤ 2 * (j.factorial : ℝ) * (((j : ℝ) + 1) * (1 + z)) * (1 + z) := by
    gcongr
  have hstep2 : 2 * (j.factorial : ℝ) * (((j : ℝ) + 1) * (1 + z)) * (1 + z)
      = 2 * (j.factorial : ℝ) * ((j : ℝ) + 1) * (1 + z) ^ 2 := by ring
  have hstep3 : 2 * (j.factorial : ℝ) * ((j : ℝ) + 1) * (1 + z) ^ 2
      ≤ 2 * (j.factorial : ℝ) * ((j : ℝ) + 1) * (1 + z) ^ (j + 2) := by
    have hle : (1 + z) ^ 2 ≤ (1 + z) ^ (j + 2) :=
      pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + z) (by omega : 2 ≤ j + 2)
    have hnn : (0 : ℝ) ≤ 2 * (j.factorial : ℝ) * ((j : ℝ) + 1) := by positivity
    exact mul_le_mul_of_nonneg_left hle hnn
  linarith [hstep1, hstep2.le, hstep2.ge, hstep3]

/-- **The weighted derivatives `z^k ∂^k F_*` decay like `1/z`**:
`|z^k ∂^k F_* z| ≤ 2·k!·(k+1)/(1+z)` for `z ≥ 1`. -/
private theorem Fstar_zpow_deriv_abs_le (k : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    |z ^ k * deriv^[k] (fun z => Work.FM.Fstar z) z|
      ≤ 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) / (1 + z) := by
  have hzI : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have hpos : (0 : ℝ) < 1 + z := by linarith
  have hden : (0 : ℝ) < (1 + z) ^ (k + 2) := pow_pos hpos _
  have hfac : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
  have hmain : |z ^ k * deriv^[k] (fun z => Work.FM.Fstar z) z|
      = 2 * (k.factorial : ℝ) * z ^ k * |z - (k : ℝ)| / (1 + z) ^ (k + 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ z ^ k), deriv_iter_Fstar_eq k hzI,
      abs_div, abs_of_pos hden, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hfac]
    ring
  rw [hmain, div_le_div_iff₀ hden hpos]
  have hkey : |z - (k : ℝ)| ≤ ((k : ℝ) + 1) * (1 + z) := by
    have hj : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [abs_le]
    constructor <;> nlinarith [hz, hj]
  have hzk : z ^ k ≤ (1 + z) ^ k :=
    pow_le_pow_left₀ (by linarith) (by linarith) k
  have hmul : z ^ k * |z - (k : ℝ)| ≤ (1 + z) ^ k * (((k : ℝ) + 1) * (1 + z)) :=
    mul_le_mul hzk hkey (abs_nonneg _) (by positivity)
  have hstep1 : 2 * (k.factorial : ℝ) * z ^ k * |z - (k : ℝ)| * (1 + z)
      ≤ 2 * (k.factorial : ℝ) * (1 + z) ^ k * (((k : ℝ) + 1) * (1 + z)) * (1 + z) := by
    have h1 : 2 * (k.factorial : ℝ) * z ^ k * |z - (k : ℝ)| * (1 + z)
        = (2 * (k.factorial : ℝ)) * (z ^ k * |z - (k : ℝ)|) * (1 + z) := by ring
    have h2 : 2 * (k.factorial : ℝ) * (1 + z) ^ k * (((k : ℝ) + 1) * (1 + z)) * (1 + z)
        = (2 * (k.factorial : ℝ)) * ((1 + z) ^ k * (((k : ℝ) + 1) * (1 + z))) * (1 + z) := by
      ring
    rw [h1, h2]
    gcongr
  have hstep2 : 2 * (k.factorial : ℝ) * (1 + z) ^ k * (((k : ℝ) + 1) * (1 + z)) * (1 + z)
      = 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) * (1 + z) ^ (k + 2) := by
    rw [pow_add]
    ring
  linarith [hstep1, hstep2.le, hstep2.ge]

/-! ## The two radial limits -/

/-- A function dominated by `C/(1+z)` eventually tends to `0` at `∞`. -/
private theorem tendsto_of_abs_le_div (f : ℝ → ℝ) (C : ℝ)
    (h : ∀ᶠ z in atTop, |f z| ≤ C / (1 + z)) : Tendsto f atTop (𝓝 0) := by
  have h1z : Tendsto (fun z : ℝ => (1 : ℝ) + z) atTop atTop :=
    tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
  have hup : Tendsto (fun z : ℝ => C / (1 + z)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h1z
  have habs : Tendsto (fun z : ℝ => |f z|) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ h
    filter_upwards with z
    exact abs_nonneg (f z)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habs

/-- **The plain derivatives of the profile decay**: `∂^j F_* z → 0` as `z → ∞`. -/
private theorem tendsto_deriv_iter_Fstar (j : ℕ) :
    Tendsto (fun z : ℝ => deriv^[j] (fun z => Work.FM.Fstar z) z) atTop (𝓝 0) := by
  refine tendsto_of_abs_le_div _ (2 * (j.factorial : ℝ) * ((j : ℝ) + 1)) ?_
  filter_upwards [eventually_ge_atTop 1] with z hz
  exact Fstar_deriv_abs_le j hz

/-- **The weighted derivatives of the profile decay**: `z^k ∂^k F_* z → 0` as `z → ∞`. -/
private theorem tendsto_zpow_deriv_iter_Fstar (k : ℕ) :
    Tendsto (fun z : ℝ => z ^ k * deriv^[k] (fun z => Work.FM.Fstar z) z) atTop (𝓝 0) := by
  refine tendsto_of_abs_le_div _ (2 * (k.factorial : ℝ) * ((k : ℝ) + 1)) ?_
  filter_upwards [eventually_ge_atTop 1] with z hz
  exact Fstar_zpow_deriv_abs_le k hz

/-- **The `D_z`-iterates of the profile decay**: `D_z^b F_* z → 0` as `z → ∞`, for every angle
(the second variable of `fun z _ => F_* z` is a dummy). -/
private theorem tendsto_DzIter_Fstar (b : ℕ) (θ : ℝ) :
    Tendsto (fun z : ℝ => Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ)
      atTop (𝓝 0) := by
  rw [show (fun z : ℝ => Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ)
      = fun z : ℝ => Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z 0 from
    funext (fun z => Work.FTS.LocDataExt.DzIter_z_only_apply (fun z => Work.FM.Fstar z) b z θ)]
  have hsmooth : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ ⊤ (fun z => (fun z _ => Work.FM.Fstar z) z θ) (Set.Ioi (-1)) :=
    fun θ hθ => contDiffOn_Fstar_analytic
  have hpt : ∀ z : ℝ, 1 ≤ z → (∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ)
        * (z ^ k * deriv^[k] (fun z => Work.FM.Fstar z) z))
      = Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z 0 := by
    intro z hz
    rw [Work.Spaces.DzIter_eq_sum_scoef hsmooth b z
      (by simp only [Set.mem_Ioi]; linarith) 0 Work.Spaces.zero_mem_Iθ]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    congr 1
    rw [Work.FTS.GalBasis.pzIter_apply_eq_iterate_deriv]
  have hterm : ∀ k ∈ Finset.range (b + 1), Tendsto (fun z : ℝ => (Work.Spaces.scoef b k : ℝ)
      * (z ^ k * deriv^[k] (fun z => Work.FM.Fstar z) z)) atTop (𝓝 (0 : ℝ)) := by
    intro k hk
    simpa using (tendsto_zpow_deriv_iter_Fstar k).const_mul (Work.Spaces.scoef b k : ℝ)
  have hsum : Tendsto (fun z : ℝ => ∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ)
      * (z ^ k * deriv^[k] (fun z => Work.FM.Fstar z) z)) atTop (𝓝 0) := by
    have := tendsto_finsetSum (s := Finset.range (b + 1)) (a := fun _ => (0 : ℝ)) hterm
    simpa using this
  refine Filter.Tendsto.congr' ?_ hsum
  filter_upwards [eventually_ge_atTop 1] with z hz
  exact hpt z hz

/-! ## Transfer of iterated derivatives along equality in a right half-line -/

/-- Iterated plain `z`-derivatives of two functions which agree on the open half-line
`(Z,∞)` agree at every point of that half-line. -/
private theorem deriv_iter_eq_of_gt {ρ σ : ℝ → ℝ} {Z : ℝ} (h : ∀ z, Z < z → ρ z = σ z) :
    ∀ j : ℕ, ∀ z, Z < z → deriv^[j] ρ z = deriv^[j] σ z := by
  intro j
  induction j with
  | zero => intro z hz; exact h z hz
  | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      refine Filter.EventuallyEq.deriv_eq ?_
      refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz) (fun z' hz' => ih z' hz')

/-- Iterated weighted `z`-derivatives `D_z^j` of two `θ`-independent functions which agree on
the open half-line `(Z,∞)` agree at every point of that half-line (all `θ`). -/
private theorem DzIter_zonly_eq_of_gt {ρ σ : ℝ → ℝ} {Z : ℝ}
    (h : ∀ z, Z < z → ρ z = σ z) :
    ∀ j : ℕ, ∀ z, Z < z → ∀ θ, Work.Spaces.DzIter j (fun z _ => ρ z) z θ
      = Work.Spaces.DzIter j (fun z _ => σ z) z θ := by
  intro j
  induction j with
  | zero => intro z hz θ; exact h z hz
  | succ n ih =>
      intro z hz θ
      show Work.Spaces.Dz (Work.Spaces.DzIter n (fun z _ => ρ z)) z θ
        = Work.Spaces.Dz (Work.Spaces.DzIter n (fun z _ => σ z)) z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      congr 1
      refine Filter.EventuallyEq.deriv_eq ?_
      refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz) (fun z' hz' => ih z' hz' θ)

/-! ## The factorisations of `locG` along the two families of iterated derivatives -/

/-- The plain iterated derivatives of the perturbation factor through its radial factor `locR`
and the angular factor `Γ`. -/
private theorem pzIter_pthIter_locG (α L β : ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter j (Work.Spaces.pthIter i
        (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α))) z θ
      = deriv^[j] (Work.FTS.LocDataExt.locR α L β) z
        * deriv^[i] (Work.Spaces.Gam α) θ := by
  have h1 : Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)
      = fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ :=
    Work.FTS.LocDataExt.locG_eq_locR_Gam α L β
  have h2 : Work.Spaces.pthIter i (fun z θ => Work.FTS.LocDataExt.locR α L β z
        * Work.Spaces.Gam α θ)
      = fun z θ => Work.FTS.LocDataExt.locR α L β z * deriv^[i] (Work.Spaces.Gam α) θ := by
    funext z θ
    exact Work.FTS.GalBasis.pthIter_mul_zonly_thetaonly i _ _ z θ
  have h3 : Work.Spaces.pzIter j (fun z θ => Work.FTS.LocDataExt.locR α L β z
        * deriv^[i] (Work.Spaces.Gam α) θ)
      = fun z θ => deriv^[j] (Work.FTS.LocDataExt.locR α L β) z
          * deriv^[i] (Work.Spaces.Gam α) θ := by
    funext z θ
    exact Work.FTS.GalBasis.pzIter_mul_zonly_thetaonly j _ _ z θ
  rw [h1, h2, h3]

/-- The mixed iterated derivatives of the perturbation factor through `locR` and `Γ`. -/
private theorem mixed_locG (α L β : ℝ) (b a : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed b a (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) z θ
      = Work.Spaces.DzIter b (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ
        * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ := by
  rw [Work.FTS.LocDataExt.locG_eq_locR_Gam α L β,
    Work.FTS.LocDataExt.mixed_sepGam α (Work.FTS.LocDataExt.locR α L β) b a]

/-! ## The two limits of the radial factor `locR` -/

/-- **The plain `z`-derivatives of the radial factor decay.**  Beyond the localisation scale
`locR` is the constant multiple `-(α/c)·FM.Fstar` of the plain profile, whose derivatives tend
to `0`. -/
private theorem tendsto_deriv_iter_locR (α L β : ℝ) (hL : 0 < L) (j : ℕ) :
    Tendsto (fun z : ℝ => deriv^[j] (Work.FTS.LocDataExt.locR α L β) z) atTop (𝓝 0) := by
  have hbase : Tendsto (fun z : ℝ => -(α / Work.Spaces.c α)
      * deriv^[j] (fun w => Work.FM.Fstar w) z) atTop (𝓝 0) := by
    simpa using (tendsto_deriv_iter_Fstar j).const_mul (-(α / Work.Spaces.c α))
  refine Filter.Tendsto.congr' ?_ hbase
  filter_upwards [eventually_gt_atTop (max (2 * L) (7 / 4))] with z hz
  have hfun : ∀ z' : ℝ, max (2 * L) (7 / 4) < z' →
      Work.FTS.LocDataExt.locR α L β z'
        = -(α / Work.Spaces.c α) * Work.FM.Fstar z' :=
    fun z' hz' => Work.FTS.LocDataExt.locR_eq_of_ge hL
      (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hz'))
      (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz'))
  exact ((deriv_iter_eq_of_gt hfun j z hz).trans
    (Work.FTS.GalBasis.iterate_deriv_const_mul j (-(α / Work.Spaces.c α))
      (fun w => Work.FM.Fstar w) z)).symm

/-- **The weighted `z`-derivatives `D_z^b` of the radial factor decay.**  Same reduction as
above, with the `D_z`-iterates. -/
private theorem tendsto_DzIter_locR (α L β : ℝ) (hL : 0 < L) (b : ℕ) (θ : ℝ) :
    Tendsto (fun z : ℝ => Work.Spaces.DzIter b (fun z _ => Work.FTS.LocDataExt.locR α L β z)
      z θ) atTop (𝓝 0) := by
  have hbase : Tendsto (fun z : ℝ => -(α / Work.Spaces.c α)
      * Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ) atTop (𝓝 0) := by
    simpa using (tendsto_DzIter_Fstar b θ).const_mul (-(α / Work.Spaces.c α))
  refine Filter.Tendsto.congr' ?_ hbase
  filter_upwards [eventually_gt_atTop (max (2 * L) (7 / 4))] with z hz
  have hfun : ∀ z' : ℝ, max (2 * L) (7 / 4) < z' →
      Work.FTS.LocDataExt.locR α L β z'
        = -(α / Work.Spaces.c α) * Work.FM.Fstar z' :=
    fun z' hz' => Work.FTS.LocDataExt.locR_eq_of_ge hL
      (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hz'))
      (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz'))
  have hcm := congrFun (congrFun (Work.FTS.LocDataExt.DzIter_const_mul (-(α / Work.Spaces.c α))
    (fun z _ => Work.FM.Fstar z) b) z) θ
  exact ((DzIter_zonly_eq_of_gt hfun b z hz θ).trans hcm).symm

/-! ## The deliverable -/

/-- **The order-`6` localised datum decays**: every plain partial derivative `∂_z^j∂_θ^i` and
every mixed derivative `D_z^bD_θ^a` with `i + j ≤ 6` resp. `a + b ≤ 6` tends to `0` as
`z → ∞`, at every fixed angle `θ ∈ [0,π/2]`. -/
theorem decayAll_locG6 (α L β : ℝ) (hL : 1 ≤ L) :
    Work.Spaces.DecayAll 6 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · intro j i hij θ hθ
    rw [show (fun z : ℝ => Work.Spaces.pzIter j (Work.Spaces.pthIter i
          (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α))) z θ)
        = fun z : ℝ => deriv^[j] (Work.FTS.LocDataExt.locR α L β) z
            * deriv^[i] (Work.Spaces.Gam α) θ from
      funext (fun z => pzIter_pthIter_locG α L β j i z θ)]
    simpa using (tendsto_deriv_iter_locR α L β hL0 j).mul_const
      (deriv^[i] (Work.Spaces.Gam α) θ)
  · intro a b hab θ hθ
    rw [show (fun z : ℝ => Work.Spaces.mixed b a
          (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) z θ)
        = fun z : ℝ => Work.Spaces.DzIter b (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ
            * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ from
      funext (fun z => mixed_locG α L β b a z θ)]
    simpa using (tendsto_DzIter_locR α L β hL0 b θ).mul_const
      (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)

end Work.FTS.LocData6
