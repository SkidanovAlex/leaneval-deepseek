import Mathlib
import Submission.Work.Pert.bounded_on_upper_halfplane
import Submission.Work.Pert.exists_line_bound_lt

/-!
# Maximum modulus on a periodic half-plane (upper end)

If `D : ℂ → ℂ` is holomorphic on the closed half-plane `{w | y ≤ im w}`, is `1`-periodic
(`D (w + 1) = D w`) and has a limit `L` as `im w → +∞` (uniformly in `re w`), and if `‖D‖ < δ`
on the boundary line `im w = y`, then `‖D‖ < δ` on the whole half-plane.

The proof rotates the half-plane to the right half-plane via `ζ ↦ I·ζ + y·I` and applies the
Phragmén–Lindelöf principle in the right half-plane
(`PhragmenLindelof.right_half_plane_of_bounded_on_real`). Periodicity is what upgrades the
pointwise strict boundary bound to a uniform bound `M < δ` (the level line is compact modulo
periodicity), and it also gives the global boundedness needed for the growth hypothesis.
-/

namespace Work.Pert

theorem norm_le_periodic_halfplane2 (D : ℂ → ℂ) {y δ : ℝ} (hδ : 0 < δ)
    (hper : ∀ w : ℂ, D (w + 1) = D w)
    (hdiff : DifferentiableOn ℂ D {w : ℂ | y ≤ w.im})
    (hend : ∃ L : ℂ, Filter.Tendsto D (Filter.comap Complex.im Filter.atTop) (nhds L))
    (hline : ∀ w : ℂ, w.im = y → ‖D w‖ < δ) :
    ∀ w : ℂ, y ≤ w.im → ‖D w‖ < δ := by
  have hcont : ContinuousOn D {w : ℂ | y ≤ w.im} := hdiff.continuousOn
  -- Uniform strict bound `M < δ` on the boundary line, and a global bound on the half-plane.
  obtain ⟨M, hMlt, hMle⟩ : ∃ M : ℝ, M < δ ∧ ∀ w : ℂ, w.im = y → ‖D w‖ ≤ M :=
    exists_line_bound_lt D hper hcont hline
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ w : ℂ, y ≤ w.im → ‖D w‖ ≤ C :=
    bounded_on_upper_halfplane D hper hcont hend
  -- Rotate to the right half-plane: `g ζ = D (I · ζ + y · I)`.
  let g : ℂ → ℂ := fun ζ => D (Complex.I * ζ + (y : ℂ) * Complex.I)
  have him_phi : ∀ ζ : ℂ, (Complex.I * ζ + (y:ℂ) * Complex.I).im = ζ.re + y := by
    intro ζ; simp
  -- `g` is differentiable on the open right half-plane and continuous on its closure.
  have hd_pos : DiffContOnCl ℂ g {z : ℂ | 0 < z.re} := by
    constructor
    · have hφd : DifferentiableOn ℂ (fun ζ : ℂ => Complex.I * ζ + (y:ℂ) * Complex.I)
          {z : ℂ | 0 < z.re} := by fun_prop
      have hmap : Set.MapsTo (fun ζ : ℂ => Complex.I * ζ + (y:ℂ) * Complex.I)
          {z : ℂ | 0 < z.re} {w : ℂ | y ≤ w.im} := by
        intro ζ hζ
        have hζ' : 0 < ζ.re := hζ
        change y ≤ (Complex.I * ζ + (y:ℂ) * Complex.I).im
        rw [him_phi]; linarith
      exact hdiff.comp hφd hmap
    · rw [Complex.closure_setOfPred_lt_re 0]
      have hφc : ContinuousOn (fun ζ : ℂ => Complex.I * ζ + (y:ℂ) * Complex.I)
          {z : ℂ | 0 ≤ z.re} := by fun_prop
      have hmap : Set.MapsTo (fun ζ : ℂ => Complex.I * ζ + (y:ℂ) * Complex.I)
          {z : ℂ | 0 ≤ z.re} {w : ℂ | y ≤ w.im} := by
        intro ζ hζ
        have hζ' : 0 ≤ ζ.re := hζ
        change y ≤ (Complex.I * ζ + (y:ℂ) * Complex.I).im
        rw [him_phi]; linarith
      exact hcont.comp hφc hmap
  -- Growth hypothesis: `g` is bounded, hence dominated by `exp (0 * ‖z‖ ^ 0) = 1`.
  have hgrowth : ∃ c < (2:ℝ), ∃ B,
      g =O[Bornology.cobounded ℂ ⊓ Filter.principal {z : ℂ | 0 < z.re}]
        fun z => Real.exp (B * ‖z‖ ^ c) := by
    refine ⟨0, by norm_num, 0, ?_⟩
    refine Asymptotics.IsBigO.of_bound C ?_
    rw [Filter.eventually_inf_principal]
    refine Filter.Eventually.of_forall fun z hz => ?_
    show ‖D (Complex.I * z + (y:ℂ)*Complex.I)‖ ≤ C * ‖Real.exp (0 * ‖z‖ ^ (0:ℝ))‖
    have hz' : 0 < z.re := hz
    have hzwe : y ≤ (Complex.I * z + (y:ℂ)*Complex.I).im := by rw [him_phi]; linarith
    have hD := hC _ hzwe
    have h1 : ‖Real.exp (0 * ‖z‖ ^ (0:ℝ))‖ = 1 := by simp
    rw [h1, mul_one]; exact hD
  -- Boundedness along the positive real axis (from the limit at `+∞`).
  have hre : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun x : ℝ => ‖g x‖) := by
    obtain ⟨L, hL⟩ := hend
    have hx : Filter.Tendsto (fun x : ℝ => Complex.I * (x:ℂ) + (y:ℂ)*Complex.I)
        Filter.atTop (Filter.comap Complex.im Filter.atTop) := by
      rw [Filter.tendsto_comap_iff]
      have heq : (Complex.im ∘ fun x : ℝ => Complex.I * (x:ℂ) + (y:ℂ)*Complex.I)
          = fun x => x + y := by
        funext x; rw [Function.comp_apply, him_phi]; simp
      rw [heq]
      exact Filter.tendsto_atTop_add_const_right _ y Filter.tendsto_id
    have hL2 : Filter.Tendsto (fun x : ℝ => g x) Filter.atTop (nhds L) := hL.comp hx
    exact (hL2.norm).isBoundedUnder_le
  -- `M` bounds `g` on the imaginary axis (which is the boundary line `im w = y`).
  have him : ∀ x : ℝ, ‖g ((x:ℝ) * Complex.I)‖ ≤ M := by
    intro x
    show ‖D (Complex.I * ((x:ℝ)*Complex.I) + (y:ℂ)*Complex.I)‖ ≤ M
    apply hMle
    rw [him_phi]; simp
  have hPL : ∀ z : ℂ, 0 ≤ z.re → ‖g z‖ ≤ M :=
    fun z hz => PhragmenLindelof.right_half_plane_of_bounded_on_real hd_pos hgrowth hre him hz
  -- Transport back: any `w` with `im w ≥ y` is `g ζ` for `ζ = (im w - y) - (re w) i`, `re ζ ≥ 0`.
  intro w hw
  set ζ : ℂ := ((w.im - y : ℝ) : ℂ) + ((-(w.re) : ℝ) : ℂ) * Complex.I with hζdef
  have hζre : 0 ≤ ζ.re := by rw [hζdef]; simp; linarith
  have hPLζ : ‖g ζ‖ ≤ M := hPL ζ hζre
  have hg : g ζ = D w := by
    rw [hζdef]
    show D (Complex.I * (((w.im - y : ℝ):ℂ) + ((-(w.re):ℝ):ℂ)*Complex.I) + (y:ℂ)*Complex.I) = D w
    congr 1
    apply Complex.ext <;> simp
  rw [hg] at hPLζ
  linarith

end Work.Pert
