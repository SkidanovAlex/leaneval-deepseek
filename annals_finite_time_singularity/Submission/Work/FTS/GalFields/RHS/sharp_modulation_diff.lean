import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.GalFields.Norm.Basic
import Submission.Work.FTS.Nonlinear.Open.Main
import Submission.Work.FTS.GalFields.Norm.abs_mubar_le
import Submission.Work.FTS.GalFields.RHS.SharpMod.N0_L12_diff
import Submission.Work.FTS.GalFields.RHS.SharpMod.N_L12_diff
import Submission.Work.FTS.GalFields.RHS.SharpMod.transport_L12_diff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.GalFields.RHS.sharp_modulation_diff`

The **difference (Lipschitz) estimate for the two modulation constants**

  `μ  = mufunS α (N₀ α (F_tot α g) g) (N α (F_tot α g) (Φ_s + EllSol g)) g`,
  `μ̄  = mubar (N₀ α (F_tot α g) g) (N α (F_tot α g) (Φ_s + EllSol g))`

of the modulation problem (Elgindi, Annals **194** (3) 2021, §Modulation, tex 1366/1380), in the
*sharp* (linear-in-the-difference) form consumed by the `RHSData.lip` clause of
`Submission/Work/FTS/GalFields/Defs.lean`.

Both constants are, by definition (`Construction/Defs.lean`, `Construction/MufunS.lean`),

  `μ̄ = L₁₂(N₀)(0) + L₁₂(N)(0)`,
  `μ  = (1/(2α))·(L₁₂(N₀)(0) + L₁₂(N)(0) + L₁₂(3 D_θ g/(1+z))(0))`,

so the difference of the two modulation constants is the explicit linear combination

  `μ(g) − μ(g') = (1/(2α))·(ΔN₀ + ΔN + ΔT)`,   `μ̄(g) − μ̄(g') = ΔN₀ + ΔN`

of the three `L₁₂`-differences

  `ΔN₀ = L₁₂(N₀ α (F_tot α g) g)(0) − L₁₂(N₀ α (F_tot α g') g')(0)`,
  `ΔN  = L₁₂(N α (F_tot α g) (Φ_s+EllSol g))(0) − L₁₂(N α (F_tot α g') (Φ_s+EllSol g'))(0)`,
  `ΔT  = L₁₂(3 D_θ g/(1+z))(0) − L₁₂(3 D_θ g'/(1+z))(0)`,

each bounded by `K·(1 + |g|_{ℋ⁵} + |g'|_{ℋ⁵})·|g−g'|_{ℋ⁵}` by the three pieces
`SharpMod.N0_L12_diff`, `SharpMod.N_L12_diff` and `SharpMod.transport_L12_diff`.  The proof below
is the assembly: unfold the two definitions with `simp only`, `ring`, and apply the triangle
inequality to the three available bounds.

The `ℋ⁵`-pricing of the difference is not a defect: `ℋ⁴` of `D_z g`, `D_θ g` is only controlled by
`ℋ⁵` of `g` (`GalFields/Defs.lean`, `Norm/Basic.lean`).
-/

namespace Work.FTS.GalFields.RHS

theorem sharp_modulation_diff {α α₂ Ci Ct Ce Cs : ℝ}
    {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hEllSub : ∀ g g' : Work.FTS.Galerkin.Fn,
      EllSol (fun z θ => g z θ - g' z θ) = fun z θ => EllSol g z θ - EllSol g' z θ)
    (hα : 0 < α) (hαα₂ : α ≤ α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ g g' h : Work.FTS.Galerkin.Fn,
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.GalClass α g' →
      Work.FTS.Nonlin.GalClass α h →
      (∀ z θ, h z θ = g z θ - g' z θ) → α ≤ 1 →
      |Work.Construction.mufunS α
          (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
          (Work.Construction.N α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + EllSol g z θ)) g
        - Work.Construction.mufunS α
          (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
          (Work.Construction.N α (Work.Construction.Ftot α g')
            (fun z θ => Φs z θ + EllSol g' z θ)) g'|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h ∧
      |Work.Construction.mubar
          (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
          (Work.Construction.N α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + EllSol g z θ))
        - Work.Construction.mubar
          (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
          (Work.Construction.N α (Work.Construction.Ftot α g')
            (fun z θ => Φs z θ + EllSol g' z θ))|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h := by
  -- the three `L₁₂`-difference estimates
  obtain ⟨K1, hK1pos, hK1⟩ := SharpMod.N0_L12_diff hN hE hstar hell hEllSub hα hαα₂
  obtain ⟨K2, hK2pos, hK2⟩ := SharpMod.N_L12_diff hN hE hstar hell hEllSub hα hαα₂
  obtain ⟨K3, hK3pos, hK3⟩ := SharpMod.transport_L12_diff hN hE hstar hell hα hαα₂
  have hS3 : 0 < K1 + K2 + K3 := by linarith
  have hfac : (0 : ℝ) < 1 / (2 * α) := by positivity
  have hmuK : 0 < (1 / (2 * α)) * (K1 + K2 + K3) + (K1 + K2) + 1 := by
    have h1 : 0 < (1 / (2 * α)) * (K1 + K2 + K3) := mul_pos hfac hS3
    have h2 : 0 ≤ K1 + K2 := by linarith
    linarith
  refine ⟨(1 / (2 * α)) * (K1 + K2 + K3) + (K1 + K2) + 1, hmuK, ?_⟩
  intro g g' h hg hg' hh hdiff hα1
  have hb1 := hK1 g g' h hg hg' hh hdiff hα1
  have hb2 := hK2 g g' h hg hg' hh hdiff hα1
  have hb3 := hK3 g g' h hg hg' hh hdiff hα1
  have hXh0 : 0 ≤ Work.FTS.GalFields.Xn5 α h := Work.Spaces.HkNorm_nonneg α 5 h
  have hXg0 : 0 ≤ Work.FTS.GalFields.Xn5 α g := Work.Spaces.HkNorm_nonneg α 5 g
  have hXg'0 : 0 ≤ Work.FTS.GalFields.Xn5 α g' := Work.Spaces.HkNorm_nonneg α 5 g'
  -- the common right-hand side
  set T : ℝ := (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
      * Work.FTS.GalFields.Xn5 α h with hT
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact mul_nonneg (by linarith) hXh0
  -- the three `L₁₂`-differences as atoms
  set A : ℝ := Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0
      - Work.Construction.L12
          (Work.Construction.N0 α (Work.Construction.Ftot α g') g') 0 with hAdef
  set B : ℝ := Work.Construction.L12
        (Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ)) 0
      - Work.Construction.L12
        (Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ)) 0 with hBdef
  set C : ℝ := Work.Construction.L12
        (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0
      - Work.Construction.L12
        (fun z θ => 3 * Work.Spaces.Dth g' z θ / (1 + z)) 0 with hCdef
  have hAb : |A| ≤ K1 * T := by
    rw [hAdef, hT]
    linarith [hb1]
  have hBb : |B| ≤ K2 * T := by
    rw [hBdef, hT]
    linarith [hb2]
  have hCb : |C| ≤ K3 * T := by
    rw [hCdef, hT]
    linarith [hb3]
  -- the triangle inequalities
  have hAB : |A + B| ≤ (K1 + K2) * T := by
    calc |A + B| ≤ |A| + |B| := abs_add_le A B
      _ ≤ K1 * T + K2 * T := add_le_add hAb hBb
      _ = (K1 + K2) * T := by ring
  have hABC : |A + B + C| ≤ (K1 + K2 + K3) * T := by
    calc |A + B + C| ≤ |A + B| + |C| := abs_add_le (A + B) C
      _ ≤ (K1 + K2) * T + K3 * T := add_le_add hAB hCb
      _ = (K1 + K2 + K3) * T := by ring
  -- the two modulation differences in terms of `A`, `B`, `C`
  have hbarid : Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
        (Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ))
      - Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
        (Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ)) = A + B := by
    rw [hAdef, hBdef]
    simp only [Work.Construction.mubar]
    ring
  have hmuid : Work.Construction.mufunS α
        (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
        (Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ)) g
      - Work.Construction.mufunS α
        (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
        (Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ)) g'
      = (1 / (2 * α)) * (A + B + C) := by
    rw [hAdef, hBdef, hCdef]
    simp only [Work.Construction.mufunS]
    ring
  constructor
  · -- the `mufunS` clause
    rw [hmuid, abs_mul, abs_of_pos hfac]
    calc (1 / (2 * α)) * |A + B + C|
        ≤ (1 / (2 * α)) * ((K1 + K2 + K3) * T) := mul_le_mul_of_nonneg_left hABC hfac.le
      _ ≤ ((1 / (2 * α)) * (K1 + K2 + K3) + (K1 + K2) + 1) * T := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by linarith [hK1pos, hK2pos]) hT0
      _ = ((1 / (2 * α)) * (K1 + K2 + K3) + (K1 + K2) + 1)
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h := by
        rw [hT]
        ring
  · -- the `mubar` clause
    rw [hbarid]
    calc |A + B| ≤ (K1 + K2) * T := hAB
      _ ≤ ((1 / (2 * α)) * (K1 + K2 + K3) + (K1 + K2) + 1) * T := by
        have h1 : 0 < (1 / (2 * α)) * (K1 + K2 + K3) := mul_pos hfac hS3
        have h2 : 0 ≤ K1 + K2 := by linarith
        nlinarith [hT0]
      _ = ((1 / (2 * α)) * (K1 + K2 + K3) + (K1 + K2) + 1)
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h := by
        rw [hT]
        ring

end Work.FTS.GalFields.RHS
