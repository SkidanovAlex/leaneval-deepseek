import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.HkAux
import Submission.Work.Spaces.pz_aux
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.H2.Q.Base
import Submission.Work.FTS.H2.prodW_interior_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Rstar_WlInf`: de-weighting the `𝒲^{4,∞}`-bound on `ℛ(Φ̃_*)`

`Work.FTS.Nonlin.StarPkg α Cs Φs` controls the *weighted* coefficient
`H := ((z+1)/z)·ℛ(Φ̃_*)` of the self-similar vorticity equation in `𝒲^{4,∞}`, with
`|H|_{𝒲^{4,∞}} ≤ Cs·α` (`StarPkg.R`).  Row 10 of the design table needs the same control for
the *unweighted* coefficient `ℛ(Φ̃_*)`, truncated off the open quadrant in the angle.

Since `ℛ(Φ̃_*) = φ·H` with the de-weighting factor `φ z = z/(1+z)`, and the weighted
derivatives of `φ` are bounded on `[0,∞)` by `m!` (`phi_deriv_bound`), the Leibniz rule for
`∂_z^k` (`Work.FTS.H2.Q.pzIter_mul_local_sm`) gives

`|(z+1)^k ∂_z^k ℛ(Φ̃_*)| ≤ (∑_{c≤k} C(k,c) c!) · |H|_{𝒲^{4,∞}}` for `z > 0`,

and the same bound at `z = 0` by continuity of the `z`-derivatives of the `D_θ`-iterates of a
`SmoothQuad` function (`Work.FTS.H2.sqm_dthIter_zslice_contDiffAt`).  On the two angular
boundary lines the truncation vanishes (radial part) resp. the `𝒲^{4,∞}`-weight kills the
mixed part.
-/

noncomputable section

open scoped Real Topology ContDiff
open Set Filter MeasureTheory

namespace Work.FTS.Nonlinear.Pieces.RNP.row10aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The de-weighting factor `z ↦ z/(1+z)` and its derivatives -/

/-- The `m`-th derivative of `z ↦ (1+z)⁻¹` is `(-1)^m m! (1+z)^{-(m+1)}` on `(-1,∞)`. -/
lemma iteratedDeriv_inv_one_add_eqOn (m : ℕ) :
    Set.EqOn (iteratedDeriv m (fun z : ℝ => (1 + z)⁻¹))
      (fun z => (-1) ^ m * (m.factorial : ℝ) * ((1 + z)⁻¹) ^ (m + 1))
      (Set.Ioi (-1)) := by
  induction m with
  | zero => intro z hz; simp
  | succ m ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz)
        (fun w hw => ih hw))]
      rw [deriv_const_mul_field]
      have hψ : HasDerivAt (fun w : ℝ => (1 + w)⁻¹) (-((1 + z)⁻¹) ^ 2) z := by
        have h1 : HasDerivAt (fun w : ℝ => 1 + w) 1 z := (hasDerivAt_id z).const_add 1
        have hne : (1 : ℝ) + z ≠ 0 := by
          have := Set.mem_Ioi.mp hz; linarith
        have h := h1.inv hne
        rw [inv_pow]
        convert h using 1
        ring
      rw [show deriv (fun w : ℝ => (1 + w)⁻¹ ^ (m + 1)) z
            = ((m + 1 : ℕ) : ℝ) * (1 + z)⁻¹ ^ (m + 1 - 1) * (-((1 + z)⁻¹) ^ 2)
          from (hψ.pow (m + 1)).deriv]
      rw [Nat.add_sub_cancel]
      change (-1) ^ m * ↑m.factorial
            * (↑(m + 1) * (1 + z)⁻¹ ^ m * -(1 + z)⁻¹ ^ 2)
          = (-1) ^ (m + 1) * ↑((m + 1).factorial) * (1 + z)⁻¹ ^ (m + 1 + 1)
      have hxR : (1 + z)⁻¹ ^ (m + 1 + 1) = (1 + z)⁻¹ ^ m * (1 + z)⁻¹ ^ 2 := by
        rw [pow_succ, pow_succ, pow_two]; ring
      rw [hxR]
      rw [show (-1 : ℝ) ^ (m + 1) = (-1) ^ m * (-1) from by rw [pow_succ]]
      rw [show (((m + 1).factorial : ℕ) : ℝ) = (m.factorial : ℝ) * ((m + 1 : ℕ) : ℝ) from by
            rw [Nat.factorial_succ, Nat.cast_mul]; ring]
      ring

/-- The `m`-th derivative of `φ z = z/(1+z)` for `m ≥ 1`:
`φ^{(m)}(z) = (-1)^{m+1} m! (1+z)^{-(m+1)}`. -/
lemma iteratedDeriv_phi (m : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) (hm : 1 ≤ m) :
    iteratedDeriv m (fun z : ℝ => z / (1 + z)) z
      = (-1) ^ (m + 1) * (m.factorial : ℝ) * ((1 + z)⁻¹) ^ (m + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hz_ne : z ≠ -1 := by
    have := Set.mem_Ioi.mp hz; linarith
  have hmem : {w : ℝ | w ≠ -1} ∈ 𝓝 z :=
    isOpen_compl_singleton.mem_nhds (by simpa using hz_ne)
  have hcongr : (fun w : ℝ => w / (1 + w)) =ᶠ[𝓝 z] (fun w : ℝ => 1 - (1 + w)⁻¹) :=
    Filter.eventually_of_mem hmem (fun w hw => by
      have h1 : (1 : ℝ) + w ≠ 0 := by
        intro hc; exact hw (by linarith)
      rw [eq_sub_iff_add_eq, add_comm]
      field_simp)
  rw [Filter.EventuallyEq.iteratedDeriv_eq (k + 1) hcongr]
  rw [iteratedDeriv_const_sub (by omega : 0 < k + 1) (1 : ℝ), iteratedDeriv_neg]
  rw [iteratedDeriv_inv_one_add_eqOn (k + 1) hz]
  rw [show (-1 : ℝ) ^ (k + 1 + 1) = (-1) ^ (k + 1) * (-1) from by rw [pow_succ]]
  ring

/-- **The weighted derivatives of the de-weighting factor are bounded by `m!`** on `[0,∞)`:
`(z+1)^m |φ^{(m)}(z)| ≤ m!` for `φ z = z/(1+z)`. -/
theorem phi_deriv_bound (m : ℕ) {z : ℝ} (hz : z ∈ Set.Ici (0 : ℝ)) :
    (z + 1) ^ m * |iteratedDeriv m (fun z : ℝ => z / (1 + z)) z| ≤ (m.factorial : ℝ) := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have hx1 : (0 : ℝ) < 1 + z := by linarith
  have hzI : z ∈ Set.Ioi (-1) := by
    simp only [Set.mem_Ioi]; linarith
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [pow_zero, one_mul, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one]
    rw [abs_of_nonneg (by positivity), div_le_one hx1]
    linarith
  · rw [iteratedDeriv_phi m hzI hm]
    have h1 : |(-1 : ℝ) ^ (m + 1)| = 1 := by rw [abs_pow]; simp
    have h2 : |((1 + z)⁻¹) ^ (m + 1)| = ((1 + z)⁻¹) ^ (m + 1) :=
      abs_of_nonneg (pow_nonneg (le_of_lt (inv_pos.mpr hx1)) _)
    rw [abs_mul, abs_mul, h1, abs_of_nonneg (Nat.cast_nonneg m.factorial), h2, one_mul]
    have hkey : (z + 1) ^ m * ((1 + z)⁻¹) ^ (m + 1) = (1 + z)⁻¹ := by
      have hzeq : (z + 1) = (1 + z) := by ring
      rw [hzeq, pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (ne_of_gt hx1), one_pow,
        one_mul]
    have hxle : (1 + z)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hx1]
      linarith
    calc (z + 1) ^ m * ((m.factorial : ℝ) * ((1 + z)⁻¹) ^ (m + 1))
        = (m.factorial : ℝ) * ((z + 1) ^ m * ((1 + z)⁻¹) ^ (m + 1)) := by ring
      _ = (m.factorial : ℝ) * (1 + z)⁻¹ := by rw [hkey]
      _ ≤ (m.factorial : ℝ) * 1 := mul_le_mul_of_nonneg_left hxle (Nat.cast_nonneg _)
      _ = (m.factorial : ℝ) := by ring

/-- The arithmetic constant of the de-weighting: `∑_{c≤k} C(k,c) c! ≤ 65` for `k ≤ 4`
(the values are `1, 2, 5, 16, 65` for `k = 0,1,2,3,4`). -/
lemma choose_fact_sum_le_nat (k : ℕ) (hk : k ≤ 4) :
    ∑ c ∈ Finset.range (k + 1), k.choose c * c.factorial ≤ 65 := by
  interval_cases k <;> decide

lemma choose_fact_sum_le (k : ℕ) (hk : k ≤ 4) :
    ∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ) * (c.factorial : ℝ) ≤ 65 := by
  have h := choose_fact_sum_le_nat k hk
  have hcast : ∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ) * (c.factorial : ℝ)
      = ((∑ c ∈ Finset.range (k + 1), k.choose c * c.factorial : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun c _ => by rw [Nat.cast_mul])
  rw [hcast]
  exact_mod_cast h

/-! ## `D_θ`-iterates of a product with a factor depending only on `z` -/

/-- `D_θ^j` of a product with a `z`-only factor: the factor comes out. -/
theorem DthIter_mul_radial (j : ℕ) (φ : ℝ → ℝ) (G : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter j (fun z θ => φ z * G z θ)
      = fun z θ => φ z * Work.Spaces.DthIter j G z θ := by
  induction j with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field (φ z)]
      ring

/-- The `z/(1+z)` instance of `DthIter_mul_radial`. -/
lemma DthIter_mul_phi (j : ℕ) (H : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter j (fun z θ => z / (1 + z) * H z θ)
      = fun z θ => z / (1 + z) * Work.Spaces.DthIter j H z θ := by
  simpa using DthIter_mul_radial j (fun z : ℝ => z / (1 + z)) H

/-- `D_θ^j` of two functions which agree on an open subset of the quadrant agree there. -/
theorem DthIter_congr_nhds {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ∀ p ∈ V, u p.1 p.2 = v p.1 p.2) :
    ∀ j z θ, (z, θ) ∈ V → Work.Spaces.DthIter j u z θ = Work.Spaces.DthIter j v z θ := by
  intro j
  induction j with
  | zero => intro z θ hzθ; exact h (z, θ) hzθ
  | succ n ih =>
      intro z θ hzθ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ]
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      congr 1
      refine Filter.EventuallyEq.deriv_eq ?_
      have hmaps : Tendsto (fun θ' : ℝ => ((z, θ') : ℝ × ℝ)) (𝓝 θ) (𝓝 (z, θ)) :=
        (continuous_const.prodMk continuous_id).continuousAt
      refine Filter.eventually_of_mem (hmaps.eventually (hV.mem_nhds hzθ)) (fun θ' hθ' => ?_)
      exact ih z θ' hθ'

/-! ## Two general tools: a limit bound at `z = 0`, and vanishing of a zero slice -/

/-- A bound on `(0,∞)` together with one-sided continuity at `0` gives the bound at `0`. -/
lemma abs_le_of_continuousWithinAt {g : ℝ → ℝ} {C : ℝ}
    (hcont : ContinuousWithinAt g (Set.Ioi 0) 0) (h : ∀ z ∈ Set.Ioi 0, |g z| ≤ C) :
    |g 0| ≤ C := by
  have h2 : ∀ᶠ z in 𝓝[>] (0 : ℝ), |g z| ≤ C := by
    rw [eventually_nhdsWithin_iff]
    exact Filter.Eventually.of_forall (fun z hz => h z hz)
  exact le_of_tendsto (x := 𝓝[>] (0 : ℝ)) (f := fun z => |g z|) (hcont.abs) h2

/-- A function whose `θ`-slice vanishes identically has vanishing `z`-derivatives there. -/
lemma pzIter_eq_zero_of_slice_zero {u : ℝ → ℝ → ℝ} {θ : ℝ} (h : ∀ z, u z θ = 0)
    (k : ℕ) (z : ℝ) : Work.Spaces.pzIter k u z θ = 0 := by
  rw [Work.Spaces.pzIter_eq_iteratedDeriv]
  rw [show (fun z' : ℝ => u z' θ) = fun _ => (0 : ℝ) from funext h,
    Work.Spaces.iteratedDeriv_zero_fun]

/-- Nonnegativity of the `𝒲^{l,∞}`-norm. -/
lemma wlInf_nonneg_of_mem {α : ℝ} {l : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.WlInfMem α l f) : 0 ≤ Work.Spaces.WlInf α l f := by
  rw [Work.Spaces.WlInf]
  refine add_nonneg (Finset.sum_nonneg fun k hk => ?_)
    (Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun k hk => ?_)
  · exact Work.Spaces.supAbs_nonneg (h.1 k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
  · by_cases hcond : 1 ≤ j ∧ k + j ≤ l
    · rw [if_pos hcond]
      exact Work.Spaces.supAbs_nonneg (h.2 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
        k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hcond.1 hcond.2)
    · rw [if_neg hcond]

/-! ## The de-weighting Leibniz bound -/

/-- **The de-weighting Leibniz bound.**  If `|(z+1)^m ∂_z^m X|·σ ≤ W` for every `m ≤ k`, then
the same holds for the Leibniz expansion of `∂_z^k ((z/(1+z))·X)`, with the constant
`∑_{c≤k} C(k,c) c! ≤ 65`. -/
lemma deweight_leibniz_sum_le {k : ℕ} (hk : k ≤ 4) {X : ℝ → ℝ → ℝ} {W σ z θ : ℝ}
    (hσnn : 0 ≤ σ) (hzz : (0 : ℝ) ≤ z) (hWnn : 0 ≤ W)
    (hper : ∀ c ≤ k, |(z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) X z θ * σ| ≤ W) :
    |(z + 1) ^ k * (∑ c ∈ Finset.range (k + 1),
        (k.choose c : ℝ) * (Work.Spaces.pzIter c (fun z θ => z / (1 + z)) z θ
          * Work.Spaces.pzIter (k - c) X z θ)) * σ| ≤ 65 * W := by
  have hpc0 : (0 : ℝ) ≤ z + 1 := by linarith
  rw [Finset.mul_sum, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs
    (fun c => (z + 1) ^ k * ((k.choose c : ℝ)
      * (Work.Spaces.pzIter c (fun z θ => z / (1 + z)) z θ
        * Work.Spaces.pzIter (k - c) X z θ)) * σ) _) ?_
  have hterm : ∀ c ∈ Finset.range (k + 1),
      |(z + 1) ^ k * ((k.choose c : ℝ)
          * (Work.Spaces.pzIter c (fun z θ => z / (1 + z)) z θ
            * Work.Spaces.pzIter (k - c) X z θ)) * σ|
        ≤ ((k.choose c : ℝ) * (c.factorial : ℝ)) * W := by
    intro c hc
    have hcle : c ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
    have hch : (0 : ℝ) ≤ (k.choose c : ℝ) := Nat.cast_nonneg _
    have hfac : (0 : ℝ) ≤ (c.factorial : ℝ) := Nat.cast_nonneg _
    have hpc : (0 : ℝ) ≤ (z + 1) ^ c := pow_nonneg hpc0 c
    have hqc : (0 : ℝ) ≤ (z + 1) ^ (k - c) := pow_nonneg hpc0 _
    have hβ : Work.Spaces.pzIter c (fun z θ => z / (1 + z)) z θ
        = iteratedDeriv c (fun z' : ℝ => z' / (1 + z')) z := by
      rw [Work.Spaces.pzIter_eq_iteratedDeriv]
    have hφb : (z + 1) ^ c * |iteratedDeriv c (fun z' : ℝ => z' / (1 + z')) z|
        ≤ (c.factorial : ℝ) := phi_deriv_bound c (Set.mem_Ici.mpr hzz)
    have hsplit : (z + 1) ^ k = (z + 1) ^ c * (z + 1) ^ (k - c) := by
      rw [← pow_add, Nat.add_sub_cancel' hcle]
    have hkey : |(z + 1) ^ k * ((k.choose c : ℝ)
          * (Work.Spaces.pzIter c (fun z θ => z / (1 + z)) z θ
            * Work.Spaces.pzIter (k - c) X z θ)) * σ|
        = ((z + 1) ^ c * |iteratedDeriv c (fun z' : ℝ => z' / (1 + z')) z|)
          * ((k.choose c : ℝ)
            * ((z + 1) ^ (k - c) * |Work.Spaces.pzIter (k - c) X z θ| * σ)) := by
      rw [hβ, hsplit]
      simp only [abs_mul, abs_of_nonneg hpc, abs_of_nonneg hqc, abs_of_nonneg hch,
        abs_of_nonneg hσnn]
      ring
    rw [hkey]
    have hper' := hper c hcle
    have habsper : |(z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) X z θ * σ|
        = (z + 1) ^ (k - c) * |Work.Spaces.pzIter (k - c) X z θ| * σ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hqc, abs_of_nonneg hσnn]
    rw [habsper] at hper'
    calc ((z + 1) ^ c * |iteratedDeriv c (fun z' : ℝ => z' / (1 + z')) z|)
          * ((k.choose c : ℝ)
            * ((z + 1) ^ (k - c) * |Work.Spaces.pzIter (k - c) X z θ| * σ))
        ≤ (c.factorial : ℝ) * ((k.choose c : ℝ) * W) :=
          mul_le_mul hφb (mul_le_mul_of_nonneg_left hper' hch)
            (mul_nonneg hch (mul_nonneg (mul_nonneg hqc (abs_nonneg _)) hσnn)) hfac
      _ = ((k.choose c : ℝ) * (c.factorial : ℝ)) * W := by ring
  calc ∑ c ∈ Finset.range (k + 1),
        |(z + 1) ^ k * ((k.choose c : ℝ)
          * (Work.Spaces.pzIter c (fun z θ => z / (1 + z)) z θ
            * Work.Spaces.pzIter (k - c) X z θ)) * σ|
      ≤ ∑ c ∈ Finset.range (k + 1), ((k.choose c : ℝ) * (c.factorial : ℝ)) * W :=
        Finset.sum_le_sum hterm
    _ = (∑ c ∈ Finset.range (k + 1), ((k.choose c : ℝ) * (c.factorial : ℝ))) * W := by
        rw [Finset.sum_mul]
    _ ≤ 65 * W := mul_le_mul_of_nonneg_right (choose_fact_sum_le k hk) hWnn

/-! ## The smoothness of the de-weighted function on the open half-quadrant `z > 0` -/

/-- The de-weighting factor is `C^∞` at every `z > 0`. -/
lemma contDiffAt_phi {z : ℝ} (hz : (0 : ℝ) < z) :
    ContDiffAt ℝ Work.Stability.smoothOrder (fun z' : ℝ => z' / (1 + z')) z :=
  contDiffAt_id.div (contDiffAt_const.add contDiffAt_id) (by linarith)

/-- The de-weighted function `(z+1)/z · R` is `C^∞` on `(0,∞) × (0,π/2)` whenever `R` is. -/
theorem deweight_smooth {R : ℝ → ℝ → ℝ} (hR : Work.FTS.LocData.SmoothQuad R) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ => (z + 1) / z * R z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hfun : Function.uncurry (fun z θ => (z + 1) / z * R z θ)
      = (fun p : ℝ × ℝ => (p.1 + 1) / p.1) * Function.uncurry R := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  refine ContDiffOn.mul (ContDiffOn.div ?_ ?_ ?_) ?_
  · exact contDiffOn_fst.add contDiffOn_const
  · exact contDiffOn_fst
  · intro p hp; exact ne_of_gt hp.1
  · refine hR.mono ?_
    intro p hp
    obtain ⟨z, θ⟩ := p
    simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2⟩

/-- The `z`-slices of the `D_θ`-iterates of the de-weighted function are `C^∞` at `z > 0`,
for `θ ∈ (0,π/2)`. -/
theorem deweight_DthIter_slice_contDiffAt {R : ℝ → ℝ → ℝ}
    (hR : Work.FTS.LocData.SmoothQuad R) (j : ℕ) {z θ : ℝ}
    (hz : z ∈ Set.Ioi 0) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiffAt ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.DthIter j (fun z θ => (z + 1) / z * R z θ) z' θ) z := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.DthIter j (fun z θ => (z + 1) / z * R z θ)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.LocData.contDiffOn_DthIter (isOpen_Ioi.prod isOpen_Ioo) (deweight_smooth hR) j
  exact (Work.FTS.LocData.contDiffOn_slice_z h1 hθ).contDiffAt (isOpen_Ioi.mem_nhds hz)

/-- **One-sided continuity at `z = 0`.**  For a `SmoothQuad` function `R` and `θ ∈ (0,π/2)`,
the `z`-derivatives of the `z`-slices of the `D_θ`-iterates of `R` are continuous at `z = 0`
from the right. -/
theorem continuousWithinAt_pzIter_DthIter {R : ℝ → ℝ → ℝ}
    (hR : Work.FTS.LocData.SmoothQuad R) (j k : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousWithinAt (fun z => Work.Spaces.pzIter k (Work.Spaces.DthIter j R) z θ)
      (Set.Ioi 0) 0 := by
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.DthIter j R z' θ) (Set.Ioi (-1)) :=
    Work.FTS.LocData.contDiffOn_slice_z (s := Set.Ioi (-1)) (t := Set.Ioo 0 (Real.pi / 2))
      (Work.FTS.LocData.contDiffOn_DthIter Work.Spaces.isOpen_quadU hR j) hθ
  have hcont : ContinuousWithinAt
      (fun z => iteratedDerivWithin k (fun z' => Work.Spaces.DthIter j R z' θ) (Set.Ioi (-1)) z)
      (Set.Ioi 0) 0 :=
    ((hslice.continuousOn_iteratedDerivWithin (by simp [Work.Stability.smoothOrder])
      (uniqueDiffOn_Ioi (-1))).continuousWithinAt (Set.mem_Ioi.mpr (by norm_num))).mono
      (fun z hz => Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hz]))
  have hval : ∀ z ∈ Set.Ici (0 : ℝ),
      iteratedDerivWithin k (fun z' => Work.Spaces.DthIter j R z' θ) (Set.Ioi (-1)) z
        = iteratedDeriv k (fun z' => Work.Spaces.DthIter j R z' θ) z := by
    intro z hz
    have hz' : z ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith [Set.mem_Ici.mp hz])
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi (-1))
      ((hslice.contDiffAt (isOpen_Ioi.mem_nhds hz')).of_le
        (by simp [Work.Stability.smoothOrder])) hz'
  have h1 : (fun z => iteratedDeriv k (fun z' => Work.Spaces.DthIter j R z' θ) z)
      =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
      (fun z => iteratedDerivWithin k (fun z' => Work.Spaces.DthIter j R z' θ) (Set.Ioi (-1)) z) :=
    Filter.eventually_of_mem self_mem_nhdsWithin
      (fun z hz => (hval z (le_of_lt (Set.mem_Ioi.mp hz))).symm)
  have h2 : iteratedDeriv k (fun z' => Work.Spaces.DthIter j R z' θ) 0
      = iteratedDerivWithin k (fun z' => Work.Spaces.DthIter j R z' θ) (Set.Ioi (-1)) 0 :=
    (hval 0 (Set.mem_Ici.mpr le_rfl)).symm
  have h3 : ContinuousWithinAt
      (fun z => iteratedDeriv k (fun z' => Work.Spaces.DthIter j R z' θ) z) (Set.Ioi 0) 0 :=
    hcont.congr_of_eventuallyEq h1 h2
  have hfun : (fun z => Work.Spaces.pzIter k (Work.Spaces.DthIter j R) z θ)
      = fun z => iteratedDeriv k (fun z' => Work.Spaces.DthIter j R z' θ) z := by
    funext z; rw [Work.Spaces.pzIter_eq_iteratedDeriv]
  rw [hfun]
  exact h3

theorem Rstar_WlInf :
    ∃ K : ℝ, 0 < K ∧ ∀ {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.LocData.SmoothQuad
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) →
      Work.Spaces.WlInfMem α 4 (fun z θ => if θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
          then Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ else 0) ∧
      Work.Spaces.WlInf α 4 (fun z θ => if θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
          then Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ else 0)
        ≤ K * (max Cs 0 * α) := by
  refine ⟨2000, by norm_num, ?_⟩
  intro α Cs Φs hα hα1 hs hsm
  set R : ℝ → ℝ → ℝ := Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) with hRdef
  set Rc : ℝ → ℝ → ℝ :=
    fun z θ => if θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) then R z θ else 0 with hRcdef
  set H : ℝ → ℝ → ℝ := fun z θ => (z + 1) / z * R z θ with hHdef
  set σ : ℝ → ℝ :=
    fun θ => (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) with hσdef
  -- the `𝒲^{4,∞}`-bound of `StarPkg`, in terms of `H`
  have hHmem : Work.Spaces.WlInfMem α 4 H := by
    rw [hHdef, hRdef]
    exact hs.R.1
  have hHle : Work.Spaces.WlInf α 4 H ≤ Cs * α := by
    rw [hHdef, hRdef]
    exact hs.R.2
  have hMnn : 0 ≤ Work.Spaces.WlInf α 4 H := wlInf_nonneg_of_mem hHmem
  have hMle : Work.Spaces.WlInf α 4 H ≤ max Cs 0 * α :=
    le_trans hHle (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le)
  -- `σ` is nonnegative on the angular interval
  have hσ_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ := by
    intro θ hθ
    rw [hσdef]
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    exact div_nonneg (Real.rpow_nonneg hs0 _) (by linarith)
  -- ### the pointwise bounds at an interior angle and `z > 0`
  have hZpos : ∀ k : ℕ, k ≤ 4 → ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(z + 1) ^ k * Work.Spaces.pzIter k R z θ| ≤ 65 * Work.Spaces.WlInf α 4 H := by
    intro k hk4 z hz θ hθ
    have hzle : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    have hθle : θ ∈ Work.Spaces.Iθ := Set.mem_Icc.mpr ⟨hθ.1.le, hθ.2.le⟩
    have hslice : (fun z' : ℝ => R z' θ) =ᶠ[𝓝 z]
        (fun z' : ℝ => z' / (1 + z') * H z' θ) := by
      refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz) (fun z' hz' => ?_)
      have hz'pos : (0 : ℝ) < z' := Set.mem_Ioi.mp hz'
      have hz'ne : z' ≠ 0 := ne_of_gt hz'pos
      have hz'1 : (1 : ℝ) + z' ≠ 0 := by positivity
      rw [hHdef]
      field_simp
      ring
    have e1 : Work.Spaces.pzIter k R z θ
        = Work.Spaces.pzIter k (fun z θ => z / (1 + z) * H z θ) z θ := by
      rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv]
      exact Filter.EventuallyEq.iteratedDeriv_eq k hslice
    rw [e1, Work.FTS.H2.Q.pzIter_mul_local_sm k (contDiffAt_phi hz)
      (by simpa using deweight_DthIter_slice_contDiffAt hsm 0 hz hθ)]
    have h := deweight_leibniz_sum_le (X := H) (W := Work.Spaces.WlInf α 4 H) (σ := 1)
      hk4 zero_le_one hz.le hMnn (fun c hc => by
        have h' := Work.Spaces.WlInf_z_bound α 4 H hHmem (k - c) (by omega) z θ hzle hθle
        simpa using h')
    simpa using h
  have hTpos : ∀ j : ℕ, 1 ≤ j → ∀ k : ℕ, k + j ≤ 4 → ∀ z ∈ Set.Ioi 0,
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j R) z θ * σ θ|
        ≤ 65 * Work.Spaces.WlInf α 4 H := by
    intro j hj1 k hkj z hz θ hθ
    have hzle : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    have hθle : θ ∈ Work.Spaces.Iθ := Set.mem_Icc.mpr ⟨hθ.1.le, hθ.2.le⟩
    have hk4 : k ≤ 4 := by omega
    have hV : ∀ p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2),
        R p.1 p.2 = p.1 / (1 + p.1) * H p.1 p.2 := by
      rintro ⟨z', θ'⟩ ⟨hz', hθ'⟩
      have hz'pos : (0 : ℝ) < z' := Set.mem_Ioi.mp hz'
      have hz'ne : z' ≠ 0 := ne_of_gt hz'pos
      have hz'1 : (1 : ℝ) + z' ≠ 0 := by positivity
      rw [hHdef]
      field_simp
      ring
    have e1 : Work.Spaces.pzIter k (Work.Spaces.DthIter j R) z θ
        = Work.Spaces.pzIter k
            (fun z θ => z / (1 + z) * Work.Spaces.DthIter j H z θ) z θ := by
      rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv]
      refine Filter.EventuallyEq.iteratedDeriv_eq k ?_
      refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz) (fun z' hz' => ?_)
      show Work.Spaces.DthIter j R z' θ
        = z' / (1 + z') * Work.Spaces.DthIter j H z' θ
      rw [DthIter_congr_nhds (u := R) (v := fun z θ => z / (1 + z) * H z θ)
            (V := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) (isOpen_Ioi.prod isOpen_Ioo) hV
            j z' θ ⟨hz', hθ⟩,
        DthIter_mul_phi]
    rw [e1, Work.FTS.H2.Q.pzIter_mul_local_sm k (contDiffAt_phi hz)
      (by simpa using deweight_DthIter_slice_contDiffAt hsm j hz hθ)]
    have h := deweight_leibniz_sum_le (X := Work.Spaces.DthIter j H)
      (W := Work.Spaces.WlInf α 4 H) (σ := σ θ) hk4 (hσ_nn θ hθle) hz.le hMnn
      (fun c hc => by
        have h' := Work.Spaces.WlInf_mixed_bound α 4 H hHmem j (k - c) hj1 (by omega)
          z θ hzle hθle
        simpa only [hσdef, ← mul_div_assoc] using h')
    simpa [hσdef] using h
  -- ### the pointwise bounds on the whole domain
  have hZ : ∀ k : ℕ, k ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k Rc z θ| ≤ 65 * Work.Spaces.WlInf α 4 H := by
    intro k hk4 z hz θ hθ
    by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hslice : (fun z' : ℝ => Rc z' θ) = fun z' : ℝ => R z' θ := by
        funext z'; rw [hRcdef]; exact if_pos hθi
      have e1 : Work.Spaces.pzIter k Rc z θ = Work.Spaces.pzIter k R z θ := by
        rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv, hslice]
      rw [e1]
      by_cases hz0 : z = 0
      · subst hz0
        refine abs_le_of_continuousWithinAt
          (g := fun z : ℝ => (z + 1) ^ k * Work.Spaces.pzIter k R z θ) ?_
          (fun z hz' => hZpos k hk4 z hz' θ hθi)
        have hcont := continuousWithinAt_pzIter_DthIter hsm 0 k hθi
        exact ((continuousWithinAt_id.add continuousWithinAt_const).pow k).mul hcont
      · exact hZpos k hk4 z (lt_of_le_of_ne hz (Ne.symm hz0)) θ hθi
    · have e0 : Work.Spaces.pzIter k Rc z θ = 0 :=
        pzIter_eq_zero_of_slice_zero (u := Rc) (θ := θ)
          (fun z' => by rw [hRcdef]; exact if_neg hθi) k z
      rw [e0]
      simp only [mul_zero, zero_mul, abs_zero]
      exact mul_nonneg (by norm_num) hMnn
  have hT : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ k : ℕ, k + j ≤ 4 → ∀ z ∈ Work.Spaces.Iz,
      ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j Rc) z θ * σ θ|
        ≤ 65 * Work.Spaces.WlInf α 4 H := by
    intro j hj1 hj4 k hkj z hz θ hθ
    by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hpp : ∀ z' : ℝ,
          Work.Spaces.DthIter j Rc z' θ = Work.Spaces.DthIter j R z' θ := fun z' =>
        DthIter_congr_nhds (u := Rc) (v := R)
          (V := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) (isOpen_univ.prod isOpen_Ioo)
          (fun p hp => by rw [hRcdef]; exact if_pos hp.2) j z' θ ⟨trivial, hθi⟩
      have e1 : Work.Spaces.pzIter k (Work.Spaces.DthIter j Rc) z θ
          = Work.Spaces.pzIter k (Work.Spaces.DthIter j R) z θ := by
        rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv]
        congr 1
        funext z'
        exact hpp z'
      rw [e1]
      by_cases hz0 : z = 0
      · subst hz0
        refine abs_le_of_continuousWithinAt (g := fun z : ℝ =>
          (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j R) z θ * σ θ) ?_
          (fun z hz' => hTpos j hj1 k hkj z hz' θ hθi)
        have hcont := continuousWithinAt_pzIter_DthIter hsm j k hθi
        exact (((continuousWithinAt_id.add continuousWithinAt_const).pow k).mul hcont).mul
          continuousWithinAt_const
      · exact hTpos j hj1 k hkj z (lt_of_le_of_ne hz (Ne.symm hz0)) θ hθi
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hsin : Real.sin (2 * θ) = 0 :=
        Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
      have e0 : Work.Spaces.pzIter k (Work.Spaces.DthIter (j' + 1) Rc) z θ = 0 :=
        pzIter_eq_zero_of_slice_zero (u := Work.Spaces.DthIter (j' + 1) Rc) (θ := θ)
          (fun z' => Work.Spaces.DthIter_succ_eq_zero_of_sin_eq_zero j' Rc hsin) k z
      rw [e0]
      simp only [mul_zero, zero_mul, abs_zero]
      exact mul_nonneg (by norm_num) hMnn
  -- ### assembly
  constructor
  · rw [Work.Spaces.WlInfMem]
    refine ⟨fun k hk => ⟨65 * Work.Spaces.WlInf α 4 H, fun y hy => ?_⟩,
      fun j hj k hk hj1 hjk => ⟨65 * Work.Spaces.WlInf α 4 H, fun y hy => ?_⟩⟩
    · rcases hy with ⟨z, hz, θ, hθ, rfl⟩
      exact hZ k hk z hz θ hθ
    · rcases hy with ⟨z, hz, θ, hθ, rfl⟩
      simpa only [hσdef, ← mul_div_assoc] using hT j hj1 (by omega) k hjk z hz θ hθ
  · rw [Work.Spaces.WlInf]
    have e1 : (∑ k ∈ Finset.range 5,
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k Rc z θ))
        ≤ 5 * (65 * Work.Spaces.WlInf α 4 H) := by
      calc _ ≤ ∑ _k ∈ Finset.range 5, 65 * Work.Spaces.WlInf α 4 H :=
            Finset.sum_le_sum (fun k hk =>
              Work.Spaces.supAbs_le (fun z hz θ hθ =>
                hZ k (by have := Finset.mem_range.mp hk; omega) z hz θ hθ))
        _ = 5 * (65 * Work.Spaces.WlInf α 4 H) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
    have e2 : (∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
          if 1 ≤ j ∧ k + j ≤ 4 then
            Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
              * Work.Spaces.pzIter k (Work.Spaces.DthIter j Rc) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          else 0)
        ≤ 25 * (65 * Work.Spaces.WlInf α 4 H) := by
      have hinner : ∀ j ∈ Finset.range 5, ∀ k ∈ Finset.range 5,
          (if 1 ≤ j ∧ k + j ≤ 4 then
            Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
              * Work.Spaces.pzIter k (Work.Spaces.DthIter j Rc) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          else 0) ≤ 65 * Work.Spaces.WlInf α 4 H := by
        intro j hj k hk
        by_cases hcond : 1 ≤ j ∧ k + j ≤ 4
        · rw [if_pos hcond]
          refine Work.Spaces.supAbs_le (fun z hz θ hθ => ?_)
          have hj4 : j ≤ 4 := by have := Finset.mem_range.mp hj; omega
          have h' := hT j hcond.1 hj4 k hcond.2 z hz θ hθ
          simpa only [hσdef, ← mul_div_assoc] using h'
        · rw [if_neg hcond]
          exact mul_nonneg (by norm_num) hMnn
      calc _ ≤ ∑ _j ∈ Finset.range 5, ∑ _k ∈ Finset.range 5,
            65 * Work.Spaces.WlInf α 4 H :=
            Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun k hk => hinner j hj k hk))
        _ = 25 * (65 * Work.Spaces.WlInf α 4 H) := by
            rw [Finset.sum_const, Finset.card_range, Finset.sum_const, Finset.card_range,
              nsmul_eq_mul]
            ring
    have hfinal : 5 * (65 * Work.Spaces.WlInf α 4 H)
        + 25 * (65 * Work.Spaces.WlInf α 4 H) ≤ 2000 * (max Cs 0 * α) := by
      have h0 : (0 : ℝ) ≤ max Cs 0 * α := mul_nonneg (le_max_right _ _) hα.le
      nlinarith [hMle, hMnn, h0]
    linarith [e1, e2, hfinal]

end Work.FTS.Nonlinear.Pieces.RNP.row10aux
