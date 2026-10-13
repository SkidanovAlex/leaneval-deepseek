/-
# `Bv(θ) = 2αΓ(θ)/c(α)` is in `𝒲^{4,∞}` with norm `O(α)`

Row 11 of the `N4` table needs the *angular* factor

  `Bv α θ = 2 α Γ(θ) / c(α)`,

where `Γ(θ) = (sin θ · cos²θ)^{α/3}` and `c(α) = ∫_{[0,π/2]} Γ K` is the normalisation
constant of the paper.  This module proves that, uniformly for `0 < α ≤ 1`, the function
`fun _ θ => Bv α θ` (constant in the radial variable `z`) belongs to `𝒲^{4,∞}` and that its
`𝒲^{4,∞}`-norm is `≤ C α` for a universal constant `C`.

## The mathematics

Since `Bv α` depends on `θ` alone,

* every radial derivative `∂_z^k (Bv α)` with `k ≥ 1` vanishes;
* the angular derivatives factor through the univariate operator `dthU φ = sin(2θ)·φ'`
  (`Work.Spaces.dthU`), which is the restriction of `D_θ` to functions of `θ`.

The whole content is therefore the two pointwise estimates

* `|Bv α θ| ≤ 20 α` (from `Γ ≤ 1` and `c(α) ≥ 1/10`), and, for `j ≥ 1`,
* `|D_θ^j (Bv α)(θ)| · sin(2θ)^{-α/5}/(α + sin(2θ)) ≤ 20 α · tBound (j-1) 0`,

where `tBound` is the (universal) coefficient sequence of `Work.Spaces.Gamma_WlInf` with
`|D_θ^j Γ(θ)| ≤ α · tBound (j-1) 0 · Γ(θ)`.  Multiplying the second estimate by the extra
scalar `2α/c(α) ≤ 20 α` of `Bv`, and using the key angular bound
`α Γ(θ) sin(2θ)^{-α/5}/(α+sin(2θ)) ≤ 1` (`Work.Spaces.Gam_mul_weight_le`), produces the
`α`-linear factor required by the statement.

The passage from the two pointwise estimates to the `𝒲^{4,∞}`-norm (the two finite sums
occurring in `Work.Spaces.WlInf`, with 5 resp. 25 terms) is isolated in the general lemma
`WlInf_z_indep_le`, which is applied here with `g = Bv α`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row11Defs
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.HkAux

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

/-! ## `Bv` as a scalar multiple of `Γ` -/

/-- `Bv α` is the constant multiple `2α/c(α)` of `Γ(α,·)`. -/
lemma Bv_eq_const_mul (α : ℝ) :
    Bv α = fun θ => (2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ := by
  funext θ
  simp only [Bv]
  ring

/-! ## Functions of `θ` alone: their radial derivatives vanish, their angular
derivatives are the univariate iterates of `dthU` -/

/-- The `(m+1)`-st iterated `z`-derivative of a function of `θ` alone vanishes. -/
lemma pzIter_z_indep_succ_zero (g : ℝ → ℝ) (m : ℕ) :
    Work.Spaces.pzIter (m + 1) (fun _ (θ : ℝ) => g θ) = fun _ _ => (0 : ℝ) := by
  induction m with
  | zero => ext z θ; simp [Work.Spaces.pz, deriv_const]
  | succ m ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      ext z θ
      simp [Work.Spaces.pz, deriv_const]

/-- The `k`-th iterated `z`-derivative of a function of `θ` alone vanishes for `k ≠ 0`. -/
lemma pzIter_z_indep_ne_zero (g : ℝ → ℝ) (k : ℕ) (hk : k ≠ 0) :
    Work.Spaces.pzIter k (fun _ (θ : ℝ) => g θ) = fun _ _ => (0 : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  exact pzIter_z_indep_succ_zero g m

/-- The iterated `D_θ`-derivative of a function of `θ` alone is the corresponding iterate
of the univariate operator `dthU`. -/
lemma DthIter_z_indep (g : ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter j (fun _ (θ' : ℝ) => g θ') z θ = Work.Spaces.dthU^[j] g θ := by
  have h := Work.Spaces.DthIter_decomp j g (fun _ : ℝ => (1 : ℝ)) z θ
  simpa using h

/-! ## The two pointwise estimates for `Bv α` -/

/-- `|Bv α θ| ≤ 20 α` on `Iθ`, for `0 < α ≤ 1`. -/
lemma Bv_abs_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Bv α θ| ≤ 20 * α := by
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hfac : 2 * α / Work.Spaces.c α ≤ 20 * α := by
    rw [div_le_iff₀ hcpos]
    nlinarith [hc, hα]
  have hfac0 : 0 ≤ 2 * α / Work.Spaces.c α := by positivity
  have hG := (Work.Spaces.Gam_bounds α θ hα hθ).2
  have hG0 := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rw [show Bv α θ = (2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ from
        congrFun (Bv_eq_const_mul α) θ,
      abs_mul, abs_of_nonneg hfac0, abs_of_nonneg hG0]
  calc (2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ
      ≤ (2 * α / Work.Spaces.c α) * 1 := mul_le_mul_of_nonneg_left hG hfac0
    _ ≤ 20 * α := by rw [mul_one]; exact hfac

/-- The angular `𝒲^{4,∞}`-estimate for `Bv α`: for `1 ≤ j` and `θ ∈ Iθ`,
`|D_θ^j (Bv α)(θ) · sin(2θ)^{-α/5}/(α+sin 2θ)| ≤ 20 α · tBound (j-1) 0`. -/
lemma Bv_dthIter_weight_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (j : ℕ) (hj : 1 ≤ j)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[j] (fun t => Bv α t) θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
      ≤ 20 * α * Work.Spaces.tBound (j - 1) 0 := by
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hfac : 2 * α / Work.Spaces.c α ≤ 20 * α := by
    rw [div_le_iff₀ hcpos]
    nlinarith [hc, hα]
  have hfac0 : 0 ≤ 2 * α / Work.Spaces.c α := by positivity
  -- the signs of the angular factors
  have hs2 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) := Real.rpow_nonneg hs2 _
  have hd : 0 < α + Real.sin (2 * θ) := by linarith
  -- pull the constant factor `2α/c(α)` out of the iterated `dthU`
  have hA : Work.Spaces.dthU^[j] (fun t => Bv α t) θ
      = (2 * α / Work.Spaces.c α)
          * Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t) θ := by
    have h : (fun t => Bv α t)
        = fun t => (2 * α / Work.Spaces.c α) * Work.Spaces.Gam α t := by
      funext t
      exact congrFun (Bv_eq_const_mul α) t
    rw [h, Work.Spaces.dthU_iter_const_mul]
  have hGle := Work.Spaces.dthU_Gam_le j hj α hα hα1 θ hθ
  have hGw := Work.Spaces.Gam_mul_weight_le α θ hα hθ
  have hT0 := Work.Spaces.tBound_nonneg (j - 1) 0
  -- `α Γ(θ) sin(2θ)^{-α/5} ≤ α + sin(2θ)`
  have hGamW : α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
      ≤ α + Real.sin (2 * θ) := by
    have := (div_le_iff₀ hd).mp hGw
    simpa using this
  rw [hA, abs_div, abs_mul]
  rw [abs_mul, abs_of_nonneg hfac0, abs_of_nonneg hs0, abs_of_nonneg (le_of_lt hd)]
  rw [div_le_iff₀ hd]
  calc (2 * α / Work.Spaces.c α)
        * |Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t) θ|
        * (Real.sin (2 * θ)) ^ (-(α / 5))
      ≤ (2 * α / Work.Spaces.c α)
        * (α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ)
        * (Real.sin (2 * θ)) ^ (-(α / 5)) := by
        apply mul_le_mul_of_nonneg_right _ hs0
        exact mul_le_mul_of_nonneg_left hGle hfac0
    _ = (2 * α / Work.Spaces.c α) * Work.Spaces.tBound (j - 1) 0
        * (α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))) := by ring
    _ ≤ (2 * α / Work.Spaces.c α) * Work.Spaces.tBound (j - 1) 0
        * (α + Real.sin (2 * θ)) :=
        mul_le_mul_of_nonneg_left hGamW (mul_nonneg hfac0 hT0)
    _ ≤ (20 * α) * Work.Spaces.tBound (j - 1) 0 * (α + Real.sin (2 * θ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfac hT0) (le_of_lt hd)
    _ = (20 * α * Work.Spaces.tBound (j - 1) 0) * (α + Real.sin (2 * θ)) := by ring

/-! ## From pointwise estimates to the `𝒲^{4,∞}`-norm, for a function of `θ` alone -/

/-- If `g : ℝ → ℝ` satisfies `|g θ| ≤ C₀` and the angular weighted estimate with constant
`C₁` on `Iθ`, then the function `fun _ θ => g θ` of the two self-similar variables belongs
to `𝒲^{4,∞}` with norm bounded by `5 C₀ + 25 C₁` (the first sum has 5 terms, the second 25,
and each of them is bounded by `C₀` resp. `C₁`). -/
lemma WlInf_z_indep_le (α : ℝ) (g : ℝ → ℝ) (C0 C1 : ℝ)
    (h0 : ∀ θ ∈ Work.Spaces.Iθ, |g θ| ≤ C0)
    (h1 : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.dthU^[j] g θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ C1)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) :
    Work.Spaces.WlInfMem α 4 (fun _ (θ : ℝ) => g θ) ∧
      Work.Spaces.WlInf α 4 (fun _ (θ : ℝ) => g θ) ≤ 5 * C0 + 25 * C1 := by
  classical
  have hpz : ∀ (h : ℝ → ℝ) (k : ℕ), 1 ≤ k →
      Work.Spaces.pzIter k (fun _ (θ : ℝ) => h θ) = fun _ _ => (0 : ℝ) :=
    fun h k hk => pzIter_z_indep_ne_zero h k (by omega)
  have hDth : ∀ j : ℕ,
      Work.Spaces.DthIter j (fun _ (θ' : ℝ) => g θ') = fun _ θ => Work.Spaces.dthU^[j] g θ := by
    intro j
    funext z θ
    exact DthIter_z_indep g j z θ
  constructor
  · constructor
    · intro k hk
      rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        refine Work.Spaces.supFinite_of_pointwise (C := C0) (fun z hz θ hθ => ?_)
        simpa using h0 θ hθ
      · rw [hpz g k (by omega)]
        exact Work.Spaces.supFinite_of_pointwise (C := 0) (fun z hz θ hθ => by simp)
    · intro j hj k hk hj1 hkj
      have hj4 : j ≤ 4 := by omega
      rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        refine Work.Spaces.supFinite_of_pointwise (C := C1) (fun z hz θ hθ => ?_)
        simpa [hDth j] using h1 j hj1 hj4 θ hθ
      · rw [hDth j, hpz (fun θ => Work.Spaces.dthU^[j] g θ) k (by omega)]
        exact Work.Spaces.supFinite_of_pointwise (C := 0) (fun z hz θ hθ => by simp)
  · rw [Work.Spaces.WlInf]
    have hZ : ∀ k ∈ Finset.range (4 + 1),
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
          * Work.Spaces.pzIter k (fun _ (θ' : ℝ) => g θ') z θ) ≤ C0 := by
      intro k hk
      rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        refine Work.Spaces.supAbs_le (fun z hz θ hθ => ?_)
        simpa using h0 θ hθ
      · rw [hpz g k (by omega)]
        refine Work.Spaces.supAbs_le (fun z hz θ hθ => ?_)
        have hz0 : |(z + 1) ^ k * (fun _ _ => (0 : ℝ)) z θ| = 0 := by simp
        rw [hz0]
        exact hC0
    have hTh : ∀ j ∈ Finset.range (4 + 1), ∀ k ∈ Finset.range (4 + 1),
        (if 1 ≤ j ∧ k + j ≤ 4 then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun _ (θ' : ℝ) => g θ')) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0) ≤ C1 := by
      intro j hj k hk
      by_cases hcond : 1 ≤ j ∧ k + j ≤ 4
      · rw [ite_eq_left hcond]
        obtain ⟨hj1, hkj⟩ := hcond
        have hj4 : j ≤ 4 := by omega
        rcases eq_or_ne k 0 with hk0 | hk0
        · subst hk0
          refine Work.Spaces.supAbs_le (fun z hz θ hθ => ?_)
          simpa [hDth j] using h1 j hj1 hj4 θ hθ
        · rw [hDth j, hpz (fun θ => Work.Spaces.dthU^[j] g θ) k (by omega)]
          refine Work.Spaces.supAbs_le (fun z hz θ hθ => ?_)
          have hz0 : |(z + 1) ^ k * (fun _ _ => (0 : ℝ)) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| = 0 := by simp
          rw [hz0]
          exact hC1
      · rw [ite_eq_right hcond]
        exact hC1
    have h1sum : (∑ k ∈ Finset.range (4 + 1),
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
          * Work.Spaces.pzIter k (fun _ (θ' : ℝ) => g θ') z θ)) ≤ 5 * C0 := by
      calc (∑ k ∈ Finset.range (4 + 1),
            Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
              * Work.Spaces.pzIter k (fun _ (θ' : ℝ) => g θ') z θ))
          ≤ ∑ _k ∈ Finset.range (4 + 1), C0 := Finset.sum_le_sum hZ
        _ = 5 * C0 := by
            rw [Finset.sum_const, Finset.card_range]
            norm_num [nsmul_eq_mul]
    have h2sum : (∑ j ∈ Finset.range (4 + 1), ∑ k ∈ Finset.range (4 + 1),
        (if 1 ≤ j ∧ k + j ≤ 4 then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun _ (θ' : ℝ) => g θ')) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0)) ≤ 25 * C1 := by
      calc (∑ j ∈ Finset.range (4 + 1), ∑ k ∈ Finset.range (4 + 1),
            (if 1 ≤ j ∧ k + j ≤ 4 then
              Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
                * Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun _ (θ' : ℝ) => g θ')) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
            else 0))
          ≤ ∑ _j ∈ Finset.range (4 + 1), ∑ _k ∈ Finset.range (4 + 1), C1 :=
            Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun k hk => hTh j hj k hk))
        _ = 25 * C1 := by
            rw [Finset.sum_const, Finset.card_range, Finset.sum_const, Finset.card_range]
            norm_num [nsmul_eq_mul]
            ring
    exact add_le_add h1sum h2sum

/-! ## The target -/

theorem Bv_WlInf : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 4 (fun _ (θ : ℝ) => Work.FTS.Nonlinear.Pieces.RNP.Bv α θ) ∧
    Work.Spaces.WlInf α 4 (fun _ (θ : ℝ) => Work.FTS.Nonlinear.Pieces.RNP.Bv α θ) ≤ C * α := by
  refine ⟨100 + 25 * (20 * ((∑ j ∈ Finset.range 4, (Work.Spaces.tBound j 0 + 1)) + 1)),
    ?_, ?_⟩
  · have hS : 0 ≤ ∑ j ∈ Finset.range 4, (Work.Spaces.tBound j 0 + 1) :=
      Finset.sum_nonneg (fun j _ => by linarith [Work.Spaces.tBound_nonneg j 0])
    linarith
  · intro α hα hα1
    set TB : ℝ := (∑ j ∈ Finset.range 4, (Work.Spaces.tBound j 0 + 1)) + 1 with hTBdef
    have hTB0 : 0 ≤ TB := by
      have hS : 0 ≤ ∑ j ∈ Finset.range 4, (Work.Spaces.tBound j 0 + 1) :=
        Finset.sum_nonneg (fun j _ => by linarith [Work.Spaces.tBound_nonneg j 0])
      rw [hTBdef]; linarith
    have hTBle : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → Work.Spaces.tBound (j - 1) 0 ≤ TB := by
      intro j hj1 hj4
      have hmem : j - 1 ∈ Finset.range 4 := Finset.mem_range.mpr (by omega)
      have hsingle : Work.Spaces.tBound (j - 1) 0 + 1
          ≤ ∑ i ∈ Finset.range 4, (Work.Spaces.tBound i 0 + 1) :=
        Finset.single_le_sum (f := fun i : ℕ => Work.Spaces.tBound i 0 + 1)
          (fun i _ => by linarith [Work.Spaces.tBound_nonneg i 0]) hmem
      rw [hTBdef]; linarith
    have hres := WlInf_z_indep_le α (fun θ => Bv α θ) (20 * α) (20 * α * TB)
      (fun θ hθ => Bv_abs_le α hα hα1 hθ)
      (fun j hj1 hj4 θ hθ => ?_)
      (by positivity) (mul_nonneg (by positivity) hTB0)
    · refine ⟨hres.1, ?_⟩
      have key : 5 * (20 * α) + 25 * (20 * α * TB) = (100 + 25 * (20 * TB)) * α := by ring
      rw [← key]
      exact hres.2
    · exact le_trans (Bv_dthIter_weight_le α hα hα1 j hj1 hθ)
        (mul_le_mul_of_nonneg_left (hTBle j hj1 hj4) (by positivity))

end Work.FTS.Nonlinear.Pieces.RNP
