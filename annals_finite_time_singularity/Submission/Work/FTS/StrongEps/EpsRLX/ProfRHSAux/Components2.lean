/-
Copyright: work module for the Elgindi finite-time singularity project.

# `ProfRHSAux/Components2` — the vanishing of `N₀`, `N`, `gRHS` and `profRHS`

Continues `ProfRHSAux/Components`:

* `tendsto_N0`: the six summands of `N₀ α (F_* + W) W` each carry a mixed derivative of `F_*`,
  of `W` or of `F = F_* + W` (all of which vanish at the endpoint) or the factor `Γ`;
* `tendsto_N`: the five summands of `N α (F_* + W) (Φs + Φg)` are bounded by the pointwise bounds
  of `ProfRHSAux/Bounds` against a vanishing factor (`F`, `D_θF` or `D_zF`);
* `tendsto_gRHS`, `tendsto_profRHS`: the assembly.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Components

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The quadratic-in-`(F_*, W)` term `N₀` -/

/-- **`N₀ α (F_* + W) W → 0`.**  Unfolding `N₀` at `F = F_* + W`, `g = W` gives the six summands

`(3/2α)(sin 2θ)L₁₂(F_*)∂_θF_*`, `-c₂ₘL₁₂(F_*)D_zF_*`, `(1/α)L₁₂(W)W`,
`(3/2α)(sin 2θ)L₁₂(W)∂_θF`, `-c₂ₘL₁₂(W)D_zF`, `-c₂ₘL₁₂(F_*)D_zW`,

each of which is a (bounded) constant or the bounded factor `c₂ₘ` times a vanishing mixed
derivative: `∂_θF_*`, `D_zF_*`, `W`, `∂_θF`, `D_zF`, `D_zW`. -/
theorem tendsto_N0 {α : ℝ} {W : Fn} (hW : Work.FTS.ClassC.ClassC α W) {l : Filter ℝ} {z : ℝ}
    (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Construction.N0 α (Work.Construction.Ftot α W) W z θ)
      l (𝓝 0) := by
  set A : ℝ := Work.Construction.L12 (Work.Construction.Fstar α) z with hA
  set L : ℝ := Work.Construction.L12 W z with hL
  have hfun : (fun θ : ℝ => Work.Construction.N0 α (Work.Construction.Ftot α W) W z θ)
      = fun θ : ℝ =>
          (3 / (2 * α)) * A * Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          + (-Work.Construction.c2m θ * A * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
          + (1 / α) * L * W z θ
          + (3 / (2 * α)) * L * Work.Spaces.Dth (Work.Construction.Ftot α W) z θ
          + (-Work.Construction.c2m θ * L * Work.Spaces.Dz (Work.Construction.Ftot α W) z θ)
          + (-Work.Construction.c2m θ * A * Work.Spaces.Dz W z θ) := by
    funext θ
    simp only [Work.Construction.N0, A, L, Work.Spaces.Dth, Work.Construction.s2] <;> ring
  -- the six summands
  have n1 : Filter.Tendsto (fun θ : ℝ =>
      (3 / (2 * α)) * A * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) l (𝓝 0) := by
    simpa using (tendsto_Dth_Fstar hc).const_mul ((3 / (2 * α)) * A)
  have hbA : ∀ᶠ θ in l, |-(Work.Construction.c2m θ) * A| ≤ 2 * |A| := by
    filter_upwards with θ
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right (abs_c2m_le_two θ) (abs_nonneg A)
  have hbL : ∀ᶠ θ in l, |-(Work.Construction.c2m θ) * L| ≤ 2 * |L| := by
    filter_upwards with θ
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right (abs_c2m_le_two θ) (abs_nonneg L)
  have n2 : Filter.Tendsto (fun θ : ℝ => -Work.Construction.c2m θ * A
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) l (𝓝 0) :=
    tendsto_mul_comm_of_eventually_bounded (tendsto_Dz_Fstar hc) hbA
  have n3 : Filter.Tendsto (fun θ : ℝ => (1 / α) * L * W z θ) l (𝓝 0) := by
    have h : Filter.Tendsto (fun θ : ℝ => ((1 / α) * L) * Work.Spaces.mixed 0 0 W z θ)
        l (𝓝 0) := by
      simpa using (hc.slot 0 0 (by norm_num)).const_mul ((1 / α) * L)
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero, mul_assoc]
      using h
  have n4 : Filter.Tendsto (fun θ : ℝ =>
      (3 / (2 * α)) * L * Work.Spaces.Dth (Work.Construction.Ftot α W) z θ) l (𝓝 0) := by
    simpa using (tendsto_Dth_Ftot hW hc).const_mul ((3 / (2 * α)) * L)
  have n5 : Filter.Tendsto (fun θ : ℝ => -Work.Construction.c2m θ * L
      * Work.Spaces.Dz (Work.Construction.Ftot α W) z θ) l (𝓝 0) :=
    tendsto_mul_comm_of_eventually_bounded (tendsto_Dz_Ftot hW hc) hbL
  have n6 : Filter.Tendsto (fun θ : ℝ => -Work.Construction.c2m θ * A
      * Work.Spaces.mixed 1 0 W z θ) l (𝓝 0) :=
    tendsto_mul_comm_of_eventually_bounded (hc.slot 0 1 (by norm_num)) hbA
  have h6 : Filter.Tendsto (fun θ : ℝ => -Work.Construction.c2m θ * A
      * Work.Spaces.Dz W z θ) l (𝓝 0) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero, Work.Spaces.Dz, Work.Spaces.pz] using n6
  rw [hfun]
  simpa using ((((n1.add n2).add n3).add n4).add n5).add h6

/-! ## The elliptic-correction term `N` -/

/-- **`N α (F_* + W) (Φs + Φg) → 0`.**  The five summands of `N`, reassociated so that the
stream-function factor carries the bounds of `ProfRHSAux/Bounds`,

`2ℛ(Φ̃)F`, `-2U(Φ̃)∂_θF`, `-2αV(Φ̃)D_zF`, `-(1/2)(sin 2θ)(F,K)∂_θF`, `-sin²θ (F,K) F`,

all carry the vanishing factor `F`, `D_θF` or `D_zF`; the first through `|ℛ(Φ̃)| ≤ CR`, the
second through `|U(Φ̃)| ≤ CU·|sin 2θ|` (which converts `∂_θF` into `D_θF`), the third through
`|V(Φ̃)| ≤ CV`. -/
theorem tendsto_N {α Cs Ce : ℝ} (hα : α ∈ Set.Ioc 0 1) {Φs W Φg : Fn}
    (hW : Work.FTS.ClassC.ClassC α W) (hell : Work.FTS.VocabO.EllPkgGo α Ce W Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {l : Filter ℝ} {z : ℝ}
    (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Construction.N α (Work.Construction.Ftot α W)
      (fun z θ => Φs z θ + Φg z θ) z θ) l (𝓝 0) := by
  obtain ⟨CR, hCR0, hCR⟩ := RopPsiBound hα hW hell hstar hc.hz
  obtain ⟨CU, hCU0, hCU⟩ := UopPsiBound hα hW hell hstar hc.hz
  obtain ⟨CV, hCV0, hCV⟩ := VopPsiBound hα hW hell hstar hc.hz
  have hbR : ∀ᶠ θ in l, |2 * Work.Construction.Rop α (PsiTot α Φs W Φg) z θ| ≤ 2 * CR := by
    filter_upwards [hc.hquad] with θ hθ
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (hCR θ hθ.1 hθ.2) (by norm_num)
  have hbV : ∀ᶠ θ in l, |-(2 * α) * Work.Construction.Vop (PsiTot α Φs W Φg) z θ|
      ≤ 2 * α * CV := by
    filter_upwards [hc.hquad] with θ hθ
    have h2a : (0 : ℝ) ≤ 2 * α := by linarith [hα.1]
    calc |-(2 * α) * Work.Construction.Vop (PsiTot α Φs W Φg) z θ|
        = (2 * α) * |Work.Construction.Vop (PsiTot α Φs W Φg) z θ| := by
          rw [abs_mul, abs_neg, abs_of_nonneg h2a]
      _ ≤ (2 * α) * CV := mul_le_mul_of_nonneg_left (hCV θ hθ.1 hθ.2) h2a
  -- the five summands
  have t1 : Filter.Tendsto (fun θ : ℝ => 2 * (Work.Construction.Rop α (PsiTot α Φs W Φg) z θ
      * Work.Construction.Ftot α W z θ)) l (𝓝 0) := by
    have h := tendsto_mul_comm_of_eventually_bounded (tendsto_Ftot hc) hbR
    simpa only [mul_assoc] using h
  have hbU : ∀ᶠ θ in l, |-(2 : ℝ) * (Work.Construction.Uop α (PsiTot α Φs W Φg) z θ
      * Work.Spaces.pth (Work.Construction.Ftot α W) z θ)|
      ≤ |(2 * CU) * Work.Spaces.Dth (Work.Construction.Ftot α W) z θ| := by
    filter_upwards [hc.hquad] with θ hθ
    have hs2 : Work.Construction.s2 θ ≠ 0 := by
      have h2θ : 0 < 2 * θ := by linarith [hθ.1]
      have h2π : 2 * θ < Real.pi := by linarith [hθ.2, Real.pi_pos]
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h2θ h2π)
    have hUop : |Work.Construction.Uop α (PsiTot α Φs W Φg) z θ|
        ≤ CU * |Work.Construction.s2 θ| := by
      calc |Work.Construction.Uop α (PsiTot α Φs W Φg) z θ|
          = |(Work.Construction.Uop α (PsiTot α Φs W Φg) z θ / Work.Construction.s2 θ)
              * Work.Construction.s2 θ| := by rw [div_mul_cancel₀ _ hs2]
        _ = |Work.Construction.Uop α (PsiTot α Φs W Φg) z θ / Work.Construction.s2 θ|
              * |Work.Construction.s2 θ| := by rw [abs_mul]
        _ ≤ CU * |Work.Construction.s2 θ| := by
            have hq : |Work.Construction.Uop α (PsiTot α Φs W Φg) z θ
                / Work.Construction.s2 θ| ≤ CU := by
              rw [abs_div]
              exact (div_le_iff₀ (abs_pos.mpr hs2)).mpr (hCU θ hθ.1 hθ.2)
            exact mul_le_mul_of_nonneg_right hq
              (abs_nonneg (Work.Construction.s2 θ))
    have hp : (0 : ℝ) ≤ |Work.Spaces.pth (Work.Construction.Ftot α W) z θ| := abs_nonneg _
    calc |-(2 : ℝ) * (Work.Construction.Uop α (PsiTot α Φs W Φg) z θ
          * Work.Spaces.pth (Work.Construction.Ftot α W) z θ)|
        = 2 * (|Work.Construction.Uop α (PsiTot α Φs W Φg) z θ|
            * |Work.Spaces.pth (Work.Construction.Ftot α W) z θ|) := by
          rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
      _ ≤ 2 * ((CU * |Work.Construction.s2 θ|)
            * |Work.Spaces.pth (Work.Construction.Ftot α W) z θ|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hUop hp)
            (by norm_num : (0 : ℝ) ≤ 2)
      _ = |(2 * CU) * Work.Spaces.Dth (Work.Construction.Ftot α W) z θ| := by
          have h2CU : (0 : ℝ) ≤ 2 * CU := by linarith
          rw [Work.Spaces.Dth, Work.Construction.s2, abs_mul, abs_of_nonneg h2CU, abs_mul]
          ring
  have t2 : Filter.Tendsto (fun θ : ℝ => -(2 : ℝ) * (Work.Construction.Uop α (PsiTot α Φs W Φg) z θ
      * Work.Spaces.pth (Work.Construction.Ftot α W) z θ)) l (𝓝 0) :=
    tendsto_zero_of_eventually_abs_le
      (by simpa using (tendsto_Dth_Ftot hW hc).const_mul (2 * CU)) hbU
  have t3 : Filter.Tendsto (fun θ : ℝ => -(2 * α) * (Work.Construction.Vop (PsiTot α Φs W Φg) z θ
      * Work.Spaces.Dz (Work.Construction.Ftot α W) z θ)) l (𝓝 0) := by
    have h := tendsto_mul_comm_of_eventually_bounded (tendsto_Dz_Ftot hW hc) hbV
    simpa only [mul_assoc] using h
  have t4 : Filter.Tendsto (fun θ : ℝ =>
      -(1 / 2) * Work.Construction.FK (Work.Construction.Ftot α W) z
      * Work.Spaces.Dth (Work.Construction.Ftot α W) z θ) l (𝓝 0) := by
    simpa using (tendsto_Dth_Ftot hW hc).const_mul
      (-(1 / 2) * Work.Construction.FK (Work.Construction.Ftot α W) z)
  have t5 : Filter.Tendsto (fun θ : ℝ => -(Real.sin θ ^ 2)
      * Work.Construction.FK (Work.Construction.Ftot α W) z
      * Work.Construction.Ftot α W z θ) l (𝓝 0) := by
    have hb5 : ∀ᶠ θ in l, |-(Real.sin θ ^ 2)
        * Work.Construction.FK (Work.Construction.Ftot α W) z| ≤ 1 * |Work.Construction.FK (Work.Construction.Ftot α W) z| := by
      filter_upwards with θ
      have h1 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
      rw [abs_mul, abs_neg]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      nlinarith [h1, abs_nonneg (Real.sin θ)]
    have h := tendsto_mul_comm_of_eventually_bounded (tendsto_Ftot hc) hb5
    simpa only [mul_assoc, one_mul] using h
  have hfun : (fun θ : ℝ => Work.Construction.N α (Work.Construction.Ftot α W)
      (fun z θ => Φs z θ + Φg z θ) z θ)
      = fun θ : ℝ =>
          2 * (Work.Construction.Rop α (PsiTot α Φs W Φg) z θ
              * Work.Construction.Ftot α W z θ)
          + (-(2 : ℝ) * (Work.Construction.Uop α (PsiTot α Φs W Φg) z θ
              * Work.Spaces.pth (Work.Construction.Ftot α W) z θ))
          + (-(2 * α) * (Work.Construction.Vop (PsiTot α Φs W Φg) z θ
              * Work.Spaces.Dz (Work.Construction.Ftot α W) z θ))
          + (-(1 / 2) * Work.Construction.FK (Work.Construction.Ftot α W) z
              * Work.Spaces.Dth (Work.Construction.Ftot α W) z θ)
          + (-(Real.sin θ ^ 2) * Work.Construction.FK (Work.Construction.Ftot α W) z
              * Work.Construction.Ftot α W z θ) := by
    funext θ
    simp only [Work.Construction.N, PsiTot, Work.Spaces.Dth, Work.Construction.s2]
    ring
  rw [hfun]
  simpa using (((t1.add t2).add t3).add t4).add t5

/-! ## The assembly -/

/-- **`gRHS α μ λ (F_* + W) (Φs + Φg) W → 0`** for any constants `μ, λ`. -/
theorem tendsto_gRHS {α Cs Ce mu lam : ℝ} (hα : α ∈ Set.Ioc 0 1) {Φs W Φg : Fn}
    (hW : Work.FTS.ClassC.ClassC α W) (hell : Work.FTS.VocabO.EllPkgGo α Ce W Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {l : Filter ℝ} {z : ℝ}
    (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Construction.gRHS α mu lam
      (Work.Construction.Ftot α W) (fun z θ => Φs z θ + Φg z θ) W z θ) l (𝓝 0) := by
  set mb : ℝ := Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α W) W)
      (Work.Construction.N α (Work.Construction.Ftot α W) (fun z θ => Φs z θ + Φg z θ)) with hmb
  have hAK : Filter.Tendsto (fun θ : ℝ => (-mb) * Work.Construction.AK α z θ) l (𝓝 0) := by
    simpa using (tendsto_AK hc).const_mul (-mb)
  have hN0 := tendsto_N0 hW hc
  have hN := tendsto_N hα hW hell hstar hc
  have hNs := tendsto_Nstar hc mu lam
  have h12 : Filter.Tendsto (fun θ : ℝ => (-mb) * Work.Construction.AK α z θ
      + Work.Construction.N0 α (Work.Construction.Ftot α W) W z θ) l (𝓝 0) := by
    simpa using hAK.add hN0
  have h123 : Filter.Tendsto (fun θ : ℝ => (-mb) * Work.Construction.AK α z θ
      + Work.Construction.N0 α (Work.Construction.Ftot α W) W z θ
      + Work.Construction.N α (Work.Construction.Ftot α W)
          (fun z θ => Φs z θ + Φg z θ) z θ) l (𝓝 0) := by
    simpa using h12.add hN
  have hfun : (fun θ : ℝ => Work.Construction.gRHS α mu lam
      (Work.Construction.Ftot α W) (fun z θ => Φs z θ + Φg z θ) W z θ)
      = fun θ : ℝ =>
          (-mb) * Work.Construction.AK α z θ
          + Work.Construction.N0 α (Work.Construction.Ftot α W) W z θ
          + Work.Construction.N α (Work.Construction.Ftot α W)
              (fun z θ => Φs z θ + Φg z θ) z θ
          + Work.Construction.Nstar mu lam W z θ := by
    funext θ
    simp only [Work.Construction.gRHS, mb] <;> ring
  rw [hfun]
  simpa using h123.add hNs

/-- **`profRHS α Φs E W → 0`** at the fixed `z > 0`, along the endpoint filter `l`. -/
theorem tendsto_profRHS {α Ce Cs : ℝ} (hα : α ∈ Set.Ioc 0 1) {Φs W : Fn} {E : Fn → Fn}
    (hW : Work.FTS.ClassC.ClassC α W) (hell : Work.FTS.VocabO.EllPkgGo α Ce W (E W))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {l : Filter ℝ} {z : ℝ}
    (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W z θ)
      l (𝓝 0) := by
  have hsplit : (fun θ : ℝ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W z θ)
      = fun θ : ℝ => -(Work.Coercivity.LGammaT α W z θ)
          + Work.Construction.gRHS α
              (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E
                  (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)))
                (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)) 0)
              (Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E
                  (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)))
                (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)) 0)
              (Work.Construction.Ftot α W) (fun z θ => Φs z θ + E W z θ) W z θ := rfl
  rw [hsplit]
  have h1 : Filter.Tendsto (fun θ : ℝ => -(Work.Coercivity.LGammaT α W z θ)) l (𝓝 0) := by
    simpa using (tendsto_LGammaT hc).neg
  have h2 : Filter.Tendsto (fun θ : ℝ => Work.Construction.gRHS α
      (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E
          (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)))
        (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)) 0)
      (Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E
          (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)))
        (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)) 0)
      (Work.Construction.Ftot α W) (fun z θ => Φs z θ + E W z θ) W z θ) l (𝓝 0) :=
    tendsto_gRHS hα hW hell hstar hc
  simpa using h1.add h2

end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
