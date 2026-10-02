import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.RepNorm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

/-- `RepNorm` only inspects `Ψ` on the far-left half-plane `{u | u.re < -R/2}` for large `R`;
hence it is insensitive to changing `Ψ` on a sufficiently far-left half-plane. -/
theorem repNorm_congr_left {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    {Ψ Ψ' : ℂ → ℂ} (N : ℝ) (hEq : ∀ u : ℂ, u.re < -N → Ψ' u = Ψ u)
    (h : Work.PARIMPL2.Lavaurs.RepNorm P Ψ) : Work.PARIMPL2.Lavaurs.RepNorm P Ψ' := by
  obtain ⟨sr, N', K, hN', hK, hmain⟩ := h
  refine ⟨sr, max N' (2 * N + 1), K, lt_of_lt_of_le hN' (le_max_left _ _), hK, ?_⟩
  intro R hR H hRH z hz
  have hR' : R ≥ N' := le_trans (le_max_left _ _) hR
  have hR2 : 2 * N + 1 ≤ R := le_trans (le_max_right _ _) hR
  obtain ⟨u, hu, hzu, hdist⟩ := hmain R hR' H hRH z hz
  have huN : u.re < -N := by nlinarith [hu, hR2]
  exact ⟨u, hu, by rw [hEq u huN]; exact hzu, hdist⟩

end Work.FlowerGlue2
