/-
# The `c2m · D_z F_*` package at order six

The angular coefficient `c2m(θ) = cos 2θ - sin²θ` multiplies `D_z F_*` in the `N₀`-rows of the
strong-persistence route, and `D_z F_*` separates as `(α/c) · Γ(θ) · H(z)` with
`H = Hz` (`Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz`).  Hence

  `c2m θ · D_z F_*(z,θ) = (α/c) · (c2m θ · Γ(θ)) · H(z)`   for `z > -1`,

i.e. it is again a separated product, this time with the angular factor `ψ = c2m · Γ`.  This
file proves

  `c2m · D_z F_* ∈ 𝒲^{6,∞}`,  `|c2m · D_z F_*|_{𝒲^{6,∞}} ≤ C α`,  `C` universal,  `0 < α ≤ 1`.

The estimate is the general `𝒲^{l,∞}`-bound for a separated product
`D · (A ⊗ H)` (`WlInfAngRadial`), whose hypotheses are the two pointwise angular inputs

* `|A θ| ≤ KA` on `Iθ` (here `|ψ| ≤ 2`);
* `|D_θ^j A θ| · sin(2θ)^{-α/5}/(α + sin 2θ) ≤ Kc` on `Iθ`, `1 ≤ j ≤ l`
  (here from `H6N_GammaTerm_Lop_bound` and the two weight inequalities
  `sin²(2θ)·Γ·Wt ≤ 1`, `α·Γ·Wt ≤ 1`, giving `Kc = 2 · 10⁹`);

together with the radial input `|(z+1)^k H^{(k)}(z)| ≤ HB k` (`Hz_deriv_bound`).  The final
constant is `10 · (Σ_{k≤6} 2·HB k + Σ_{j,k≤6, j≥1, j+k≤6} HB k · Kc) + 1`, the factor `10`
coming from `|α/c| ≤ 10α`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.DzFstar_W6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.c2mGam_Wt_bound
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.WlInfAngRadial

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false

theorem c2mDzFstar_W6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 6 (fun z θ => Work.Construction.c2m θ
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ∧
    Work.Spaces.WlInf α 6 (fun z θ => Work.Construction.c2m θ
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ C * α := by
  obtain ⟨Kc, hKcpos, hKc⟩ := c2mGam_Wt_bound
  -- the universal constant, built from the radial bounds `HB` and the angular bound `Kc`
  set S1 : ℝ := ∑ k ∈ Finset.range 7, 2 * Work.FTS.Nonlinear.FstarPkg.HB k with hS1
  set S2 : ℝ := ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7,
      (if 1 ≤ j ∧ k + j ≤ 6 then Work.FTS.Nonlinear.FstarPkg.HB k * Kc else 0) with hS2
  have hS1nn : 0 ≤ S1 := by
    rw [hS1]
    exact Finset.sum_nonneg fun k _ => by
      have := Work.FTS.Nonlinear.FstarPkg.HB_nonneg k; linarith
  have hS2nn : 0 ≤ S2 := by
    rw [hS2]
    refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
    split_ifs with h
    · exact mul_nonneg (Work.FTS.Nonlinear.FstarPkg.HB_nonneg k) hKcpos.le
    · norm_num
  have hSS : 0 ≤ S1 + S2 := add_nonneg hS1nn hS2nn
  refine ⟨10 * (S1 + S2) + 1, by linarith, fun α hα hα1 => ?_⟩
  -- `|α/c| ≤ 10α`
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcoef : |α / Work.Spaces.c α| ≤ 10 * α := by
    rw [abs_of_nonneg (div_nonneg hα.le hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  -- `𝒲^{l,∞}` only sees `z > -1`, where `D_z F_*` is the separated product
  -- `(α/c) · Γ ⊗ Hz`
  have hcongr := Work.FTS.Nonlinear.FstarPkg.WlInf_congr
    (f := fun z θ => Work.Construction.c2m θ
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
    (g := fun z θ => (α / Work.Spaces.c α)
      * ((Work.Construction.c2m θ * Work.Spaces.Gam α θ)
        * Work.FTS.Nonlinear.FstarPkg.Hz z))
    (fun z hz θ => by
      rw [Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα hz]
      ring) α 6
  -- the angular input `|ψ| ≤ 2`
  have hA : ∀ θ ∈ Work.Spaces.Iθ, |Work.Construction.c2m θ * Work.Spaces.Gam α θ| ≤ 2 := by
    intro θ hθ
    have hGam1 : |Work.Spaces.Gam α θ| ≤ 1 := by
      rw [abs_of_nonneg (Work.Spaces.Gam_bounds α θ hα hθ).1]
      exact (Work.Spaces.Gam_bounds α θ hα hθ).2
    have h1 : |Work.Construction.c2m θ| ≤ 2 := by
      rw [Work.Construction.c2m_eq]
      calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
          = |Real.cos (2 * θ) + -(Real.sin θ ^ 2)| := by ring_nf
        _ ≤ |Real.cos (2 * θ)| + |-(Real.sin θ ^ 2)| := abs_add_le _ _
        _ = |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := by rw [abs_neg]
        _ ≤ 1 + 1 := by
            have hs : |Real.sin θ ^ 2| ≤ 1 := by
              rw [abs_of_nonneg (sq_nonneg _)]
              exact Real.sin_sq_le_one θ
            have hc2 := Real.abs_cos_le_one (2 * θ)
            linarith
        _ = 2 := by norm_num
    rw [abs_mul]
    calc |Work.Construction.c2m θ| * |Work.Spaces.Gam α θ| ≤ 2 * 1 :=
          mul_le_mul h1 hGam1 (abs_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  -- the weighted angular input, from `c2mGam_Wt_bound`
  have hKstep : ∀ j : ℕ, 1 ≤ j → j ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Spaces.dthU^[j]) (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ Kc := by
    intro j hj hj6 θ hθ
    have h := hKc α hα hα1 j hj hj6 θ hθ
    have h' : |(Work.Spaces.dthU^[j])
          (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ|
        * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ ≤ Kc := h
    simpa only [Work.FTS.Nonlinear.FstarPkg.DthAux.Wt] using h'
  -- the separated `𝒲^{6,∞}`-bound
  obtain ⟨hmem, hbound⟩ := WlInfAngRadial (l := 6) (α := α)
    (A := fun t => Work.Construction.c2m t * Work.Spaces.Gam α t)
    (Hc := Work.FTS.Nonlinear.FstarPkg.Hz) (B := Work.FTS.Nonlinear.FstarPkg.HB)
    (D := α / Work.Spaces.c α) (KA := 2) (Kc := Kc) hα hA hKstep
    (fun k _ z hz => Work.FTS.Nonlinear.FstarPkg.Hz_deriv_bound k z hz)
  refine ⟨hcongr.2.mpr hmem, ?_⟩
  rw [hcongr.1]
  have hb : Work.Spaces.WlInf α 6 (fun z θ => (α / Work.Spaces.c α)
      * ((Work.Construction.c2m θ * Work.Spaces.Gam α θ)
        * Work.FTS.Nonlinear.FstarPkg.Hz z)) ≤ |α / Work.Spaces.c α| * (S1 + S2) := by
    rw [hS1, hS2]
    exact hbound
  calc Work.Spaces.WlInf α 6 (fun z θ => (α / Work.Spaces.c α)
        * ((Work.Construction.c2m θ * Work.Spaces.Gam α θ)
          * Work.FTS.Nonlinear.FstarPkg.Hz z))
      ≤ |α / Work.Spaces.c α| * (S1 + S2) := hb
    _ ≤ 10 * α * (S1 + S2) := mul_le_mul_of_nonneg_right hcoef hSS
    _ = (10 * (S1 + S2)) * α := by ring
    _ ≤ (10 * (S1 + S2) + 1) * α := by nlinarith [hSS, hα]

end Work.FTS.StrongPersist.H6Pair6Aux
