import Mathlib
import Submission.Work.RPCore.Defs
import Submission.Work.RPCore.Flow.bounded_of_periodic_of_eq_on_slab
import Submission.Work.RPCore.Flow.fderiv_eq_of_periodic
import Submission.Work.RPCore.Flow.norm_fderiv_pair_le

/-!
# Bounds for the time-clamped Hamiltonian field (`Work.RPCore.Flow.clampedField_bounds`)

Let `H` be a compactly supported `2π`-periodic Hamiltonian (`Work.RPV.CptPerHam`) and let
`ψ : ℝ → ℝ` be a `C⁴` time-change with bounded value and bounded derivative (a *clamp*).  The
autonomous field

`z ↦ autoVF (fun t x => H (ψ t) x) z = (1, X_{H ∘ ψ}(z))`

on `ℝ × PS` is `C³`, bounded in norm, and has bounded Fréchet derivative.

The point of the clamp is that, although `H` itself is only compactly supported in the *space*
variable with bounds that may depend on `t` in an uncontrolled way, the *parameter* `ψ t` of `H`
ranges in a bounded set (`|ψ t| ≤ B`), so all derivatives of `H` are uniformly bounded along the
clamped family.  Concretely, the field is `W ∘ A` where

* `A z = (ψ z.1, z.2)` is the time-change, whose derivative is bounded by `max ‖ψ'‖ 1`
  (`norm_fderiv_pair_le`),
* `W (s, x) = (1, X_{H s} x)` is the unclamped field at the fixed parameter `s`; it is continuous,
  `2π`-periodic in `q₂`, and *constant* off the support slab `{|q₁|+|p₁|+|p₂| > R}` of `H`
  (it equals `(1,0)` there, because `H s` vanishes on a neighbourhood).  Hence `W` and `fderiv W`
  are uniformly bounded on the strip `{|s| ≤ B}` (`bounded_of_periodic_of_eq_on_slab`), which is
  all one needs.

The auxiliary facts used are

* `bounded_of_periodic_of_eq_on_slab` : a continuous function on `ℝ × PS` which is `2π`-periodic
  in `q₂` and constant off the slab is bounded on every strip `{|z.1| ≤ B}`;
* `fderiv_eq_of_periodic`          : the derivative of a translation-invariant function is
  translation-invariant;
* `norm_fderiv_pair_le`            : the derivative of the time-change `z ↦ (ψ z.1, z.2)` is bounded.

Nothing here is specific to the rectangular-peg problem beyond the definitions of `PS` and `hamVF`.
-/

open RectangularPegProblem Manifold Complex Real
open scoped ContDiff Topology
open Filter

set_option autoImplicit false

noncomputable section

namespace Work.RPCore.Flow

open Work.RPV

/-! ## Auxiliary facts -/

/-- The translation vector of the deck transformation `Tk 1` on `PS` (shift of `q₂` by `2π`). -/
def tkShift : PS := ((0, 2 * π), (0, 0))

theorem Tk_one_eq_add (x : PS) : Tk 1 x = x + tkShift := by
  ext <;> simp [Tk, tkShift]

/-- If `W` vanishes in a neighbourhood of `x`, then its Hamiltonian vector field vanishes at `x`.
Immediate from `fderiv` of a function which is eventually `0`. -/
theorem hamVF_eq_zero_of_eventuallyEq_zero {W : PS → ℝ} {x : PS} (h : W =ᶠ[𝓝 x] 0) :
    hamVF W x = 0 := by
  have hd : fderiv ℝ W x = 0 := by
    rw [h.fderiv_eq]
    simp
  simp only [hamVF, hd]
  simp

/-- If `W` is invariant under the deck transformation `Tk 1` then so is `hamVF W`. -/
theorem hamVF_eq_of_Tk {W : PS → ℝ} (hWd : Differentiable ℝ W)
    (hW : ∀ x, W (Tk 1 x) = W x) (x : PS) : hamVF W (Tk 1 x) = hamVF W x := by
  have h : fderiv ℝ W (Tk 1 x) = fderiv ℝ W x := by
    rw [Tk_one_eq_add]
    exact fderiv_eq_of_periodic W hWd (fun y => by rw [← Tk_one_eq_add]; exact hW y) x
  simp only [hamVF, h]

/-- The partial Hamiltonian vector field of a `C^{n+1}` Hamiltonian is `C^n`:
`z ↦ hamVF (H z.1) z.2` is `C^n` when `(t,x) ↦ H t x` is `C^{n+1}`. -/
theorem contDiff_hamVF_partial (n : ℕ) (U : ℝ × PS → ℝ) (hU : ContDiff ℝ (n + 1) U) :
    ContDiff ℝ n (fun z : ℝ × PS => hamVF (fun y : PS => U (z.1, y)) z.2) := by
  set D : ℝ × PS → (PS →L[ℝ] ℝ) := fun z => fderiv ℝ (fun y : PS => U (z.1, y)) z.2 with hDdef
  have hD : ContDiff ℝ n D := by
    have h1 : ContDiff ℝ (n + 1) (fun p : (ℝ × PS) × PS => U (p.1.1, p.2)) := by
      have hL : ContDiff ℝ (n + 1) (fun p : (ℝ × PS) × PS => (p.1.1, p.2)) := by fun_prop
      exact hU.comp hL
    have h2 : ContDiff ℝ n (fun z : ℝ × PS => z.2) := contDiff_snd.of_le le_top
    exact ContDiff.fderiv (n := n) h1 h2 le_rfl
  have hev (v : PS) : ContDiff ℝ n (fun z : ℝ × PS => D z v) := by
    have h : ContDiff ℝ n ((ContinuousLinearMap.apply ℝ ℝ) v) :=
      (ContinuousLinearMap.apply ℝ ℝ v).contDiff.of_le le_top
    exact h.comp hD
  have heq : (fun z : ℝ × PS => hamVF (fun y : PS => U (z.1, y)) z.2)
      = fun z => ((D z ((0, 0), (1, 0)), D z ((0, 0), (0, 1))),
          (-D z ((1, 0), (0, 0)), -D z ((0, 1), (0, 0)))) := by
    funext z
    simp [hamVF, hDdef]
  rw [heq]
  exact ((hev _).prodMk (hev _)).prodMk ((hev _).neg.prodMk (hev _).neg)

/-! ## The main statement -/

theorem clampedField_bounds (Hh : Work.RPV.CptPerHam) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 4 ψ)
    (hψb : ∃ B : ℝ, ∀ t, |ψ t| ≤ B) (hψ' : ∃ B' : ℝ, ∀ t, |deriv ψ t| ≤ B') :
    ContDiff ℝ 3 (Work.RPCore.autoVF (fun t x => Hh.H (ψ t) x)) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℝ × Work.RPV.PS,
      ‖Work.RPCore.autoVF (fun t x => Hh.H (ψ t) x) z‖ ≤ M) ∧
    (∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ × Work.RPV.PS,
      ‖fderiv ℝ (Work.RPCore.autoVF (fun t x => Hh.H (ψ t) x)) z‖ ≤ K) := by
  obtain ⟨B, hB⟩ := hψb
  obtain ⟨B', hB'⟩ := hψ'
  -- the uncurried Hamiltonian and the two bounds for `ψ`
  set U : ℝ × PS → ℝ := fun z => Hh.H z.1 z.2 with hUdef
  have hU : ContDiff ℝ 4 U := Hh.smooth
  have hUd : Differentiable ℝ U := hU.differentiable (by norm_num)
  -- the partial Hamiltonian vector field of `H`, as a function of `(s,x)`
  set Φ : ℝ × PS → PS := fun z => hamVF (fun y : PS => U (z.1, y)) z.2 with hΦdef
  have hΦ : ContDiff ℝ 3 Φ := contDiff_hamVF_partial 3 U hU
  -- `Φ` is `2π`-periodic in `q₂`
  have hΦper : ∀ z : ℝ × PS, Φ (z.1, Tk 1 z.2) = Φ z := by
    intro z
    have hWd : Differentiable ℝ (fun y : PS => U (z.1, y)) := by fun_prop
    show hamVF (fun y : PS => U (z.1, y)) (Tk 1 z.2) = hamVF (fun y : PS => U (z.1, y)) z.2
    exact hamVF_eq_of_Tk hWd (fun y => Hh.per z.1 y) z.2
  -- `Φ` vanishes strictly outside the support slab of `H`
  have hΦsupp : ∀ z : ℝ × PS, Hh.R < |z.2.1.1| + |z.2.2.1| + |z.2.2.2| → Φ z = 0 := by
    intro z hz
    have hcont : Continuous fun y : PS => |y.1.1| + |y.2.1| + |y.2.2| := by fun_prop
    have hopen : {y : PS | Hh.R < |y.1.1| + |y.2.1| + |y.2.2|} ∈ 𝓝 z.2 :=
      (isOpen_lt continuous_const hcont).mem_nhds hz
    have hev : (fun y : PS => U (z.1, y)) =ᶠ[𝓝 z.2] 0 := by
      filter_upwards [hopen] with y hy
      exact Hh.supp z.1 y hy.le
    show hamVF (fun y : PS => U (z.1, y)) z.2 = 0
    exact hamVF_eq_zero_of_eventuallyEq_zero hev
  -- the unclamped field `W s = (1, X_{H s})` on `ℝ × PS`
  set W : ℝ × PS → ℝ × PS := fun z => (1, Φ z) with hWdef
  have hW : ContDiff ℝ 3 W := contDiff_const.prodMk hΦ
  have hWper : ∀ z : ℝ × PS, W (z.1, Tk 1 z.2) = W z := by
    intro z; simp [W, hΦper z]
  have hWconst : ∀ z : ℝ × PS, Hh.R < |z.2.1.1| + |z.2.2.1| + |z.2.2.2| → W z = (1, 0) := by
    intro z hz; simp [W, hΦsupp z hz]
  -- `W` is bounded on the strip `{|s| ≤ B}`
  obtain ⟨M, hM0, hMbd⟩ := bounded_of_periodic_of_eq_on_slab W hW.continuous hWper hWconst B
  -- ... and so is its derivative
  have hWd : Differentiable ℝ W := hW.differentiable (by norm_num)
  have hgper : ∀ z : ℝ × PS, fderiv ℝ W (z.1, Tk 1 z.2) = fderiv ℝ W z := by
    rintro ⟨z1, z2⟩
    show fderiv ℝ W (z1, Tk 1 z2) = fderiv ℝ W (z1, z2)
    have hshift : ∀ w : ℝ × PS, W (w + (0, tkShift)) = W w := by
      rintro ⟨w1, w2⟩
      have : (w1, w2) + ((0 : ℝ), tkShift) = (w1, Tk 1 w2) := by simp [Tk_one_eq_add]
      rw [this]
      exact hWper (w1, w2)
    have h2 := fderiv_eq_of_periodic W hWd hshift (z1, z2)
    have hz : (z1, z2) + ((0 : ℝ), tkShift) = (z1, Tk 1 z2) := by simp [Tk_one_eq_add]
    rw [hz] at h2
    exact h2
  have hgc : Continuous (fderiv ℝ W) := hW.continuous_fderiv (by norm_num)
  have hgsupp : ∀ z : ℝ × PS, Hh.R < |z.2.1.1| + |z.2.2.1| + |z.2.2.2| →
      fderiv ℝ W z = 0 := by
    intro z hz
    have hcont : Continuous fun y : ℝ × PS => |y.2.1.1| + |y.2.2.1| + |y.2.2.2| := by fun_prop
    have hopen : {y : ℝ × PS | Hh.R < |y.2.1.1| + |y.2.2.1| + |y.2.2.2|} ∈ 𝓝 z :=
      (isOpen_lt continuous_const hcont).mem_nhds hz
    have hev : W =ᶠ[𝓝 z] (fun _ => (1, (0 : PS))) := by
      filter_upwards [hopen] with y hy
      exact hWconst y hy
    rw [hev.fderiv_eq]
    simp
  obtain ⟨M', hM'0, hM'bd⟩ :=
    bounded_of_periodic_of_eq_on_slab (fderiv ℝ W) hgc hgper hgsupp B
  -- the derivative of the time-change `z ↦ (ψ z.1, z.2)` is bounded
  obtain ⟨K₁, hK₁0, hK₁⟩ := norm_fderiv_pair_le ψ hψ hB'
  -- the clamped field is `W ∘ A`
  set A : ℝ × PS → ℝ × PS := fun z => (ψ z.1, z.2) with hAdef
  have hA : ContDiff ℝ 4 A := (hψ.comp contDiff_fst).prodMk contDiff_snd
  have hfield : autoVF (fun t x => Hh.H (ψ t) x) = fun z : ℝ × PS => W (A z) := by
    funext z
    simp [autoVF, W, A, Φ, U]
  refine ⟨?_, ?_, ?_⟩
  · -- smoothness
    rw [hfield]
    exact hW.comp (hA.of_le (by norm_num))
  · -- bound on the field
    exact ⟨M, hM0, fun z => by rw [hfield]; exact hMbd (A z) (hB z.1)⟩
  · -- bound on the derivative of the field
    refine ⟨M' * K₁, mul_nonneg hM'0 hK₁0, fun z => ?_⟩
    have hchain : fderiv ℝ (autoVF (fun t x => Hh.H (ψ t) x)) z
        = (fderiv ℝ W (A z)) ∘L (fderiv ℝ A z) := by
      rw [hfield]
      exact fderiv_comp z hWd.differentiableAt ((hA.differentiable (by norm_num)).differentiableAt)
    rw [hchain]
    calc ‖(fderiv ℝ W (A z)) ∘L (fderiv ℝ A z)‖
        ≤ ‖fderiv ℝ W (A z)‖ * ‖fderiv ℝ A z‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M' * K₁ := mul_le_mul (hM'bd (A z) (hB z.1)) (hK₁ z) (norm_nonneg _) hM'0

end Work.RPCore.Flow
