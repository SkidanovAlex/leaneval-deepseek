/-
  Subproject WilE9G / Assembly — `lagStratumAE_mem` (D4b of the assembly).

  Every Lagrange point `(z, μ, μ₀)` of the ambient `Good` stratum `S` at which `lagJac` is
  invertible lies in the set of the boundary-compatible Lagrange stratum `lagStratumAE S Φ c`.

  The point of the construction: the disjuncts of `lagStratumAE` are indexed by the *basics* of
  `S.X`, so a point `z ∈ S.X.set` is witnessed by one of them; the lifted equations `h_a` and the
  lifted inequalities `B.pos` evaluate through `pad` to their values at `z`, the multiplier
  coordinates of `lagPoint` are `μ`, `μ₀`, the equation part `lagEqs` reproduces the Lagrange
  equations and the normalisation, and the only polynomial inequality is `lagDet² > 0`, which holds
  because at a Lagrange point `lagDet` evaluates to `± det (lagJac …) ≠ 0`.  Since `S.X.set` is
  contained in the *closed* cube, `lagPoint` lands in the closed cube of the stratum's ambient
  space; this is exactly why the interior conditions had to be dropped.
-/
import Mathlib
import Submission.Work.WilE9G.Assembly.Defs
import Submission.Work.WilE9G.Lagrange.exists_lagrange_stratum

set_option autoImplicit false
noncomputable section

namespace Work.WilE9G.Assembly
open WilkiesDesign WilkiesDesign.E Work.WilE9G Work.WilE9G.Lagrange

/-- A Lagrange point whose base-and-fibre part lies in the *closed* cube and whose multipliers are
normalised lies in the closed cube of the stratum's ambient space.  (The companion
`Lagrange.lagPoint_mem_cubeC` assumes the open cube.) -/
theorem lagPoint_mem_cubeC_le {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (hz : ∀ i : Fin (n + (1 + m)), |z i| ≤ 1) (hNorm : Work.WilE9G.LagNorm mu mu0) :
    lagPoint z mu mu0 ∈ cubeC (n + (1 + (m + S.j + 1))) := by
  intro i
  obtain ⟨htake, hcast, hmu, hmu0⟩ :=
    lagPoint_apply (n := n) (m := m) (j := S.j) (by omega) z mu mu0
  rcases lt_or_ge i.val (n + (1 + m)) with h | h
  · have he : Fin.castLE (by omega : n + (1 + m) ≤ n + (1 + (m + S.j + 1))) ⟨i.val, h⟩ = i :=
      Fin.ext rfl
    rw [← he, hcast ⟨i.val, h⟩]
    exact hz _
  · have hd : i.val - (n + (1 + m)) < S.j + 1 := by
      have hi : i.val < n + (1 + m) + (S.j + 1) := by
        have := i.isLt
        omega
      omega
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hlt' | heq
    · have he : muIdx n m (⟨i.val - (n + (1 + m)), hlt'⟩ : Fin S.j) = i := by
        apply Fin.ext
        simp only [muIdx_val]
        omega
      rw [← he, hmu ⟨i.val - (n + (1 + m)), hlt'⟩]
      exact abs_mu_le_one hNorm _
    · have he : mu0Idx n m S.j = i := by
        apply Fin.ext
        simp only [mu0Idx_val]
        omega
      rw [← he, hmu0]
      exact abs_mu0_le_one hNorm

theorem lagStratumAE_mem {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (hS : S.Good) (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (hz : z ∈ S.X.set)
    (hEq : Work.WilE9G.LagEq S Phi c z mu mu0) (hNorm : Work.WilE9G.LagNorm mu mu0)
    (hdet : (Work.WilE9G.lagJac S Phi c z mu mu0).det ≠ 0) :
    Work.WilE9G.lagPoint z mu mu0 ∈ (Work.WilE9G.Assembly.lagStratumAE S Phi c).X.set := by
  -- Unfold the membership in the semi-Pfaffian set of the stratum and its definition.
  rw [WilkiesDesign.E.SemiPf.set, Set.mem_ofPred_eq]
  simp only [Work.WilE9G.Assembly.lagStratumAE]
  -- The point `z` is witnessed by a basic `B` of `S.X` and lies in the closed cube.
  have hzcube : z ∈ cubeC (n + (1 + m)) := hz.1
  obtain ⟨B, hBmem, hBholds⟩ := hz.2
  obtain ⟨hH, hL, hN⟩ := lagEqs_eval S Phi c z mu mu0
  refine ⟨lagPoint_mem_cubeC_le S z mu mu0 (fun i => hzcube i) hNorm, ?_⟩
  -- Choose the disjunct of `lagStratumAE` indexed by `B`.
  refine ⟨⟨List.ofFn (lagEqs S Phi c) ++ B.eqs.map (Work.WilE7.EAPoly.pad (by omega)),
    [lagDet S Phi c * lagDet S Phi c] ++ B.pos.map (Work.WilE7.EAPoly.pad (by omega))⟩,
    ?_, ?_⟩
  · -- Membership of the chosen disjunct among the strata's basics.
    exact List.mem_map.mpr ⟨B, hBmem, rfl⟩
  · -- The equations and inequalities of the disjunct hold at `lagPoint z mu mu0`.
    refine ⟨?_, ?_⟩
    · intro f hf
      rw [List.mem_append] at hf
      rcases hf with hf | hf
      · -- the equations `lagEqs` of the construction
        rw [List.mem_ofFn] at hf
        obtain ⟨a, rfl⟩ := hf
        rcases lt_or_ge a.val (1 + m) with ha | ha
        · rw [lagEqs_apply_of_lt S Phi c a ha, hL ⟨a.val, ha⟩, hEq ⟨a.val, ha⟩]
          ring
        · by_cases ha2 : a.val < 1 + m + S.j
          · rw [lagEqs_apply_of_mid S Phi c a ha ha2, hH ⟨a.val - (1 + m), by omega⟩,
              AmbStratum_eq_zero S hS hz ⟨a.val - (1 + m), by omega⟩]
          · have hlast : a.val = 1 + m + S.j := by
              have := a.isLt
              omega
            rw [lagEqs_apply_of_last S Phi c a hlast, hN]
            have hnorm : (∑ a : Fin S.j, (mu a) ^ 2) + mu0 ^ 2 = 1 := hNorm
            linarith
      · -- the lifted equations of `S`
        rw [List.mem_map] at hf
        obtain ⟨g, hg, rfl⟩ := hf
        rw [lagEval_pad S g z mu mu0]
        exact hBholds.1 g hg
    · intro g hg
      rw [List.mem_append] at hg
      rcases hg with hg | hg
      · -- the nonvanishing of `lagDet`
        rw [List.mem_singleton] at hg
        rw [hg, lagEval_mul]
        have hne : eaEval (lagChain S) (lagDet S Phi c) (lagPoint z mu mu0) ≠ 0 :=
          lagDet_eval_ne_zero S Phi c z mu mu0 hEq hNorm hdet
        exact (mul_self_pos).mpr hne
      · -- the lifted inequalities of `S`
        rw [List.mem_map] at hg
        obtain ⟨g', hg', rfl⟩ := hg
        rw [lagEval_pad S g' z mu mu0]
        exact hBholds.2 g' hg'

end Work.WilE9G.Assembly
