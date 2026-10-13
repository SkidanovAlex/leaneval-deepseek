import Mathlib
import Submission.Work.WilG4c.tnorm_curve_of_surrogate_germ
import Submission.Work.WilG4c.Defs

/-!
# The shrunken-chart jet bound `CdpT1Curve`

Let `F(t) = h (α₀ + β₀ * t 0)` be the un-shrunken surrogate on the one-dimensional cube
`openCube 1 = (0,1)`, and let

`g(s) = h (α₀ + β₀ * (cc + s / 4))`

be its *shrunken-chart* avatar, the affine reparametrisation `t = cc + s/4` of `F` written in
the single coordinate `s ∈ ℝ`.  The lemma says that if `F` is `C^{r+1}` on the open cube with
all operator norms of its iterated derivatives of order `≤ r + 1` bounded by `1` there, and if
`0 ≤ cc ≤ 3/4` and `0 < x < 1`, then `g` is `C^{r+1}` at `x` and all its iterated derivatives
of order `≤ r + 1` at `x` have operator norm `≤ 1` as well.

The point of the numerical hypotheses is that the shrunk point still lies in the cube:

`cc + x/4 ∈ (0, 1)` because `0 ≤ cc ≤ 3/4` and `0 < x < 1`.

The formal content is then the affine chain rule.  Writing `B` for the *linear equivalence*
`ℝ ≃L[ℝ] (Fin 1 → ℝ)`, `B y = fun _ => 4⁻¹ * y`, and `b` for the constant point `fun _ => cc`,
we have `g = F ∘ (b + B ·)`, and for a continuous linear equivalence the chain rule for the
iterated derivative (Faà di Bruno with all higher corrections vanishing) is unconditional:

`‖D^m (F ∘ (b + B ·)) x‖ ≤ ‖D^m F (b + B x)‖ * ‖B‖^m`,

see `itd_comp_affine_equiv_le` below.  Since `‖B‖ = 4⁻¹ ≤ 1` and `b + B x = fun _ => cc + x/4`
lies in the cube, the jet hypothesis `hjet` bounds the right hand side by `1`.  The same
decomposition gives `ContDiffAt` by the ordinary chain rule for `ContDiffAt`.
-/

namespace Work.WilG4c

open scoped Topology

/-- The open cube in dimension `1`, as a single `Ioo`-condition on the only coordinate. -/
private lemma openCube_one_eq :
    WilkiesDesign.openCube 1 = {t : Fin 1 → ℝ | t 0 ∈ Set.Ioo (0 : ℝ) 1} := by
  ext t
  simp [WilkiesDesign.openCube, Fin.forall_fin_one]

/-- The open cube in dimension `1` is open. -/
private lemma isOpen_openCube_one : IsOpen (WilkiesDesign.openCube 1) := by
  rw [openCube_one_eq]
  exact (continuous_apply (0 : Fin 1) : Continuous fun p : Fin 1 → ℝ => p 0).isOpen_preimage
    (Set.Ioo (0 : ℝ) 1) isOpen_Ioo

/-- Chain rule for the iterated derivative of a composition with a continuous linear
*equivalence* on the right, in the special shape needed here: the source is `ℝ` and the target
is `Fin M → ℝ`.  Because the inner map is a linear equivalence, the formula holds without any
smoothness assumption on `f`, and the operator norm picks up the factor `‖e‖ ^ m`. -/
private theorem itd_comp_equiv_le {M : ℕ} (e : ℝ ≃L[ℝ] (Fin M → ℝ)) (f : (Fin M → ℝ) → ℝ)
    (x : ℝ) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y : ℝ => f (e y)) x‖ ≤
      ‖iteratedFDeriv ℝ m f (e x)‖ * ‖(e : ℝ →L[ℝ] (Fin M → ℝ))‖ ^ m := by
  have hchain : iteratedFDeriv ℝ m (fun y : ℝ => f (e y)) x =
      (iteratedFDeriv ℝ m f (e x)).compContinuousLinearMap
        (fun _ : Fin m => (e : ℝ →L[ℝ] (Fin M → ℝ))) := by
    have hw := ContinuousLinearEquiv.iteratedFDerivWithin_comp_right (𝕜 := ℝ) e f
      (s := Set.univ) uniqueDiffOn_univ (Set.mem_univ (e x)) m
    simpa only [Set.preimage_univ, iteratedFDerivWithin_univ, Function.comp_def] using hw
  rw [hchain]
  calc _ ≤ ‖iteratedFDeriv ℝ m f (e x)‖ * ∏ _i : Fin m, ‖(e : ℝ →L[ℝ] (Fin M → ℝ))‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ m f (e x)‖ * ‖(e : ℝ →L[ℝ] (Fin M → ℝ))‖ ^ m := by simp

/-- The affine version of `itd_comp_equiv_le`: composing with `y ↦ b + e y` instead of `e`.
The translation by the constant `b` is removed by `iteratedFDeriv_comp_add_left`. -/
private theorem itd_comp_affine_equiv_le {M : ℕ} (e : ℝ ≃L[ℝ] (Fin M → ℝ))
    (f : (Fin M → ℝ) → ℝ) (b : Fin M → ℝ) (x : ℝ) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y : ℝ => f (b + e y)) x‖ ≤
      ‖iteratedFDeriv ℝ m f (b + e x)‖ * ‖(e : ℝ →L[ℝ] (Fin M → ℝ))‖ ^ m := by
  have hmain := itd_comp_equiv_le e (fun z : Fin M → ℝ => f (b + z)) x m
  rw [iteratedFDeriv_comp_add_left m b (e x)] at hmain
  simpa using hmain

theorem CdpT1Curve {r : ℕ} (hr : 1 ≤ r) (h : ℝ → ℝ) (α₀ β₀ cc x : ℝ)
    (hβ : 0 < β₀) (hcc0 : 0 ≤ cc) (hcc3 : cc ≤ 3 / 4) (hx : x ∈ Work.WilkG4c.I)
    (hC : ContDiffOn ℝ (r + 1) (fun t : Fin 1 → ℝ => h (α₀ + β₀ * t 0))
      (WilkiesDesign.openCube 1))
    (hjet : ∀ q ≤ r + 1, ∀ t ∈ WilkiesDesign.openCube 1,
      ‖iteratedFDeriv ℝ q (fun t : Fin 1 → ℝ => h (α₀ + β₀ * t 0)) t‖ ≤ 1) :
    ContDiffAt ℝ (r + 1) (fun s : ℝ => h (α₀ + β₀ * (cc + s / 4))) x ∧
    (∀ q ≤ r + 1, ‖iteratedFDeriv ℝ q (fun s : ℝ => h (α₀ + β₀ * (cc + s / 4))) x‖ ≤ 1) := by
  -- `x` lies in the open unit interval: `0 < x < 1`.
  have hxI : 0 < x ∧ x < 1 := by
    simpa only [Work.WilkG4c.I, Set.mem_Ioo] using hx
  -- The linear equivalence `B y = fun _ => 4⁻¹ * y`, built from the pair of mutually inverse
  -- continuous linear maps `y ↦ 4⁻¹ y` and `z ↦ 4 * z 0`.
  let fwd : ℝ →L[ℝ] (Fin 1 → ℝ) :=
    (4:ℝ)⁻¹ • ContinuousLinearMap.pi (fun _ : Fin 1 => (1 : ℝ →L[ℝ] ℝ))
  let bwd : (Fin 1 → ℝ) →L[ℝ] ℝ :=
    (4:ℝ) • (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ)
  have hfwd : ∀ y : ℝ, fwd y = fun _ : Fin 1 => 4⁻¹ * y := by
    intro y
    ext i
    simp only [fwd, smul_apply]
    rfl
  have hbwd : ∀ z : (Fin 1 → ℝ), bwd z = 4 * z 0 := by
    intro z
    simp only [bwd, smul_apply]
    rfl
  have hleft : Function.LeftInverse bwd fwd := by
    intro y
    rw [hbwd, hfwd y]
    show 4 * (4⁻¹ * y) = y
    ring
  have hright : Function.RightInverse bwd fwd := by
    intro z
    ext i
    fin_cases i
    rw [hfwd (bwd z), hbwd z]
    show 4⁻¹ * (4 * z 0) = z 0
    ring
  let B : ℝ ≃L[ℝ] (Fin 1 → ℝ) := ContinuousLinearEquiv.equivOfInverse fwd bwd hleft hright
  have hBval : ∀ y : ℝ, B y = fun _ : Fin 1 => 4⁻¹ * y := fun y => hfwd y
  -- The equivalence is `4⁻¹`-Lipschitz, in particular `‖B‖ ≤ 1`.
  have hBnorm : ‖(B : ℝ →L[ℝ] (Fin 1 → ℝ))‖ ≤ 1 := by
    rw [show (B : ℝ →L[ℝ] (Fin 1 → ℝ)) = fwd from rfl]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y => ?_)
    rw [one_mul, hfwd y]
    rw [show ‖(fun _ : Fin 1 => 4⁻¹ * y)‖ = |4⁻¹ * y| from by simp]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4⁻¹), Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg y) (by norm_num)
  -- The affine point `b + B y` has coordinate `cc + y / 4`.
  have hpt_all : ∀ y : ℝ, (((fun _ : Fin 1 => cc) + B y) 0) = cc + y / 4 := by
    intro y
    rw [Pi.add_apply, hBval y]
    show cc + 4⁻¹ * y = cc + y / 4
    ring
  have hpt : (fun _ : Fin 1 => cc) + B x = fun _ : Fin 1 => cc + x / 4 := by
    ext i
    fin_cases i
    simpa using hpt_all x
  -- The shrunk point is still inside the cube.
  have hmem : (fun _ : Fin 1 => cc + x / 4) ∈ WilkiesDesign.openCube 1 := by
    rw [openCube_one_eq]
    show cc + x / 4 ∈ Set.Ioo (0 : ℝ) 1
    rw [Set.mem_Ioo]
    constructor <;> linarith [hxI.1, hxI.2, hcc0, hcc3]
  -- `g` is the composite `F ∘ (b + B ·)`.
  have hfun : (fun s : ℝ => h (α₀ + β₀ * (cc + s / 4)))
      = (fun y : ℝ => (fun t : Fin 1 → ℝ => h (α₀ + β₀ * t 0))
          ((fun _ : Fin 1 => cc) + B y)) := by
    funext y
    simp only [hpt_all y]
  -- `F` is `C^{r+1}` at the shrunk point, which is interior to the cube.
  have hF_at : ContDiffAt ℝ (r + 1) (fun t : Fin 1 → ℝ => h (α₀ + β₀ * t 0))
      ((fun _ : Fin 1 => cc) + B x) := by
    rw [hpt]
    exact hC.contDiffAt (isOpen_openCube_one.mem_nhds hmem)
  have hinner : ContDiffAt ℝ (r + 1) (fun y : ℝ => (fun _ : Fin 1 => cc) + B y) x := by
    have h1 : ContDiffAt ℝ (r + 1) (fun _ : ℝ => (fun _ : Fin 1 => cc)) x := contDiffAt_const
    have h2 : ContDiffAt ℝ (r + 1) (fun y : ℝ => B y) x :=
      (ContinuousLinearMap.contDiff (B : ℝ →L[ℝ] (Fin 1 → ℝ))).contDiffAt
    simpa using h1.add h2
  have hCd : ContDiffAt ℝ (r + 1) (fun s : ℝ => h (α₀ + β₀ * (cc + s / 4))) x := by
    rw [hfun]
    show ContDiffAt ℝ (r + 1) ((fun t : Fin 1 → ℝ => h (α₀ + β₀ * t 0))
      ∘ (fun y : ℝ => (fun _ : Fin 1 => cc) + B y)) x
    exact hF_at.comp x hinner
  refine ⟨hCd, ?_⟩
  intro q hq
  rw [hfun]
  -- The affine chain rule bounds the `q`-th jet of `g` by the `q`-th jet of `F` at the shrunk
  -- point, times `‖B‖^q ≤ 1`.
  have hchain := itd_comp_affine_equiv_le (M := 1) B
      (fun t : Fin 1 → ℝ => h (α₀ + β₀ * t 0)) (fun _ : Fin 1 => cc) x q
  have hjet_p : ‖iteratedFDeriv ℝ q (fun t : Fin 1 → ℝ => h (α₀ + β₀ * t 0))
      ((fun _ : Fin 1 => cc) + B x)‖ ≤ 1 := by
    rw [hpt]
    exact hjet q hq (fun _ : Fin 1 => cc + x / 4) hmem
  calc ‖iteratedFDeriv ℝ q (fun y : ℝ => (fun t : Fin 1 → ℝ => h (α₀ + β₀ * t 0))
          ((fun _ : Fin 1 => cc) + B y)) x‖
      ≤ ‖iteratedFDeriv ℝ q (fun t : Fin 1 → ℝ => h (α₀ + β₀ * t 0))
          ((fun _ : Fin 1 => cc) + B x)‖ * ‖(B : ℝ →L[ℝ] (Fin 1 → ℝ))‖ ^ q := hchain
    _ ≤ 1 * 1 := mul_le_mul hjet_p (pow_le_one₀ (norm_nonneg _) hBnorm)
        (pow_nonneg (norm_nonneg _) q) (by norm_num)
    _ = 1 := by norm_num

end Work.WilG4c
