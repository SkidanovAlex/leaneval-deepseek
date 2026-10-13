/-
Copyright: work module for the Elgindi finite-time singularity project.

# The "easy" part of the `SpecialTransport` pairing

This file contains the pointwise estimates for `EasyF = H4PairInt α (f ∂_θ g) g - HardF`,
where `HardF` is the (f-form) collection of the five order-five terms.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.H2.STSigma
import Submission.Work.FTS.H2.STDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The unified `f`-bound -/

/-- `|D_z^b D_θ^a f| ≤ 4·10^5 · sin(2θ) · |∂_θ f|_𝒲` for `1 ≤ a+b ≤ 4`, `z > 0`. -/
theorem abs_mixed_f_le' {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothInt f)
    (hcont : ContinuousOn (Function.uncurry f) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hvt : Work.Spaces.VanishTheta f) (hα : 0 < α) (hα1 : α ≤ 1)
    (hW : Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f)) :
    ∀ a b : ℕ, 1 ≤ a + b → a + b ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.mixed b a f z θ|
        ≤ 400000 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by
  intro a b hab hab4 z hz θ hθ
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have h1 := abs_DzIter_f_le hsm hcont hvt hW b (by omega) z hz θ hθI
    have hWnn : 0 ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := WlInf_nonneg hW
    have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθI
    calc |Work.Spaces.mixed b 0 f z θ| = |Work.Spaces.DzIter b f z θ| := rfl
      _ ≤ 10000 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := h1
      _ ≤ 400000 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by
          nlinarith [mul_nonneg hS hWnn]
  · exact abs_mixed_f_le hsm hα hα1 hW a b hpos hab4 z hz θ hθ

/-! ## `∂_θ` commutes with `D_z^j` -/

theorem pth_dzIter_comm {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hX : ContDiffOn ℝ ⊤ (Function.uncurry X) V) :
    ∀ j : ℕ, Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j X)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth X))) V := by
  intro j
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
    intro p hp
    show Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j X)) p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Spaces.pth X)) p.1 p.2
    show deriv (fun θ' => p.1 * Work.Spaces.pz (Work.Spaces.DzIter j X) p.1 θ') p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Spaces.pth X)) p.1 p.2
    rw [deriv_const_mul_field p.1]
    congr 1
    have hsmj : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter j X)) V :=
      Work.Spaces.DzIterSmoothOn hV hX j
    have h2 : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter j X)) p :=
      (hsmj.contDiffAt (hV.mem_nhds hp)).of_le (by norm_num)
    change Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.DzIter j X)) p.1 p.2
        = Work.Spaces.pz (Work.Spaces.DzIter j (Work.Spaces.pth X)) p.1 p.2
    rw [← Work.Spaces.pz_pth_comm h2]
    exact Work.Spaces.pz_congr_of_isOpen hV ih hp

/-- `∂_θ (D_z^j g) = D_z^j (∂_θ g)` on `nbhU`. -/
theorem pth_dzIter_eq (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth g)))
      (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j g))) Work.Spaces.nbhU :=
  (pth_dzIter_comm Work.Spaces.isOpen_nbhU hg j).symm

/-! ## The exact `sin(2θ)·∂_θ(D_z^jD_θ^ig) = D_z^jD_θ^{i+1}g` -/

theorem sin_mul_pth_mixed (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) (j i : ℕ)
    {z θ : ℝ} (hstrp : (z, θ) ∈ Work.Spaces.nbhU) :
    Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed j i g) z θ
      = Work.Spaces.mixed j (i + 1) g z θ := by
  have h : Work.Spaces.Dth (Work.Spaces.mixed j i g) z θ
      = Work.Spaces.mixed j (i + 1) g z θ := by
    have hcomm := Work.Spaces.Dth_DzIter_comm_eqOn (Work.Spaces.smoothNbhd_DthIter hg i) j hstrp
    show Work.Spaces.Dth (Work.Spaces.DzIter j (Work.Spaces.DthIter i g)) z θ
        = Work.Spaces.DzIter j (Work.Spaces.DthIter (i + 1) g) z θ
    change Work.Spaces.Dth (Work.Spaces.DzIter j (Work.Spaces.DthIter i g)) z θ
        = Work.Spaces.DzIter j (Work.Spaces.Dth (Work.Spaces.DthIter i g)) z θ
    exact hcomm
  exact h

/-! ## The commutator bound -/

/-- `sin(2θ)·(∂_θ D_z^jD_θ^ig - D_z^jD_θ^i(∂_θg))` is bounded by the lower slots. -/
theorem comm_bound (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) (j i : ℕ) (hi : i ≤ 4)
    {z θ : ℝ} (hstrp : (z, θ) ∈ Work.Spaces.nbhU) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Real.sin (2 * θ) * (Work.Spaces.mixed j i (Work.Spaces.pth g) z θ
        - Work.Spaces.pth (Work.Spaces.mixed j i g) z θ)|
      ≤ (∑ r ∈ Finset.range i, ((i.choose (r + 1) : ℝ) * Asin (r + 1) * Bz (i - (r + 1))))
        * ∑ m ∈ Finset.Icc 1 i, |Work.Spaces.mixed j m g z θ| := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθI
  have hexp := mixed_succ_expansion g hg i j hstrp
  have hpth := sin_mul_pth_mixed g hg j i hstrp
  have hkey : Real.sin (2 * θ) * (Work.Spaces.mixed j i (Work.Spaces.pth g) z θ
        - Work.Spaces.pth (Work.Spaces.mixed j i g) z θ)
      = -(∑ r ∈ Finset.range i,
          ((i.choose (r + 1) : ℝ) * Work.Spaces.DthIter (r + 1) Sfun 0 θ)
            * Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ) := by
    rw [mul_sub, hpth]
    linarith [hexp]
  set T : ℝ := ∑ m ∈ Finset.Icc 1 i, |Work.Spaces.mixed j m g z θ| with hT
  have hTnn : 0 ≤ T := Finset.sum_nonneg fun m _ => abs_nonneg _
  have hterm : ∀ r ∈ Finset.range i,
      |((i.choose (r + 1) : ℝ) * Work.Spaces.DthIter (r + 1) Sfun 0 θ)
          * Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ|
        ≤ ((i.choose (r + 1) : ℝ) * Asin (r + 1) * Bz (i - (r + 1))) * T := by
    intro r hr
    simp only [Finset.mem_range] at hr
    have hrle : r + 1 ≤ 4 := by omega
    have hlt : i - (r + 1) ≤ 3 := by omega
    have hAs := abs_DthIter_Sfun_le (r + 1) (by omega) 0 hθI
    have hCnn : (0 : ℝ) ≤ (i.choose (r + 1) : ℝ) := Nat.cast_nonneg _
    have hsig := sigma_z_bound g hg (i - (r + 1)) hlt j z θ hstrp hθ
    have hsub : Finset.Icc 1 (i - (r + 1) + 1) ⊆ Finset.Icc 1 i := by
      intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    have hTle : (∑ m ∈ Finset.Icc 1 (i - (r + 1) + 1), |Work.Spaces.mixed j m g z θ|) ≤ T := by
      rw [hT]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun m => |Work.Spaces.mixed j m g z θ|) hsub (fun m _ _ => abs_nonneg _)
    rw [abs_mul, abs_mul, abs_of_nonneg hCnn]
    calc (i.choose (r + 1) : ℝ) * |Work.Spaces.DthIter (r + 1) Sfun 0 θ|
          * |Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ|
        ≤ (i.choose (r + 1) : ℝ) * (Asin (r + 1) * Real.sin (2 * θ))
          * |Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left hAs hCnn
      _ = ((i.choose (r + 1) : ℝ) * Asin (r + 1))
          * (Real.sin (2 * θ)
              * |Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ|) := by ring
      _ ≤ ((i.choose (r + 1) : ℝ) * Asin (r + 1)) * (Bz (i - (r + 1)) * T) :=
          mul_le_mul_of_nonneg_left
            (le_trans hsig (mul_le_mul_of_nonneg_left hTle (Bz_nonneg _)))
            (mul_nonneg (Nat.cast_nonneg _) (Asin_pos _).le)
      _ = ((i.choose (r + 1) : ℝ) * Asin (r + 1) * Bz (i - (r + 1))) * T := by ring
  have hsumabs : |-(∑ r ∈ Finset.range i,
        ((i.choose (r + 1) : ℝ) * Work.Spaces.DthIter (r + 1) Sfun 0 θ)
          * Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ)|
      ≤ ∑ r ∈ Finset.range i,
          ((i.choose (r + 1) : ℝ) * Asin (r + 1) * Bz (i - (r + 1))) * T := by
    rw [abs_neg]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
  rw [hkey]
  refine le_trans hsumabs ?_
  rw [Finset.sum_mul]

end Work.FTS.H2
