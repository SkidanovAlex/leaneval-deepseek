/-
# `Work.SeedFatou.exists_critImm` — the packaged immediate-basin datum of the seed

Lemma **B3** of `NOTES_LEAD_mandelbar_final2.md` §2.2 (steps A2–A5): for **every**
`S : Work.SeedExist.RootSeedData` there is a critical point `w` of `F c = (T_c)^[10]`
lying in the **immediate basin** `Ω = immBasin (F c) z₁ p₀` of the parabolic point `z₁`
through a petal point `p₀`, with `Ω` preconnected, `F c`-invariant and contained in
`interior (basin (F c) z₁)`, and with the half-petal `Pg` of the Leau–Fatou flower of the
seed inside `Ω`.

## The route (no numerics, no certificate)

1. `z₁` is a **simple** parabolic fixed point of `F c` (`S.g_fix`, `S.mult_one`
   unfolded through `Work.Landing.multiplier2`, `S.simple`); hence
   `Work.FatouParabolic2.exists_petalData_of_simple` supplies petal data `pd` at `z₁`.
2. Take `p ∈ pd.Pa` (`pd.nonempty`).  Its orbit converges to `z₁` (`pd.tendsto_Pa`) and
   never attains `z₁` (`pd.mapsTo_Pa` + `pd.z₀_not_mem`), so the flower's `enters_Pg`
   produces `n` with `p₀ := F^[n] p ∈ Pg`; by `mapsTo_iterate_of_mapsTo` also `p₀ ∈ pd.Pa`.
3. `Work.FatouParabolic2.exists_criticalPoint_in_immBasin` (the Liouville/covering step)
   gives `w ∈ Ω := immBasin F z₁ p₀` with `deriv F w = 0`.
4. `Pg ⊆ Ω`: `Pg` is open with all its orbits converging to `z₁` (`fl.tendsto_Pg`), hence
   `Pg ⊆ interior (basin F z₁)` (`interior_maximal`), and `Pg` is preconnected and contains
   `p₀ ∈ Pg`, so `IsPreconnected.subset_connectedComponentIn` gives `Pg ⊆ Ω`.
5. `Ω ⊆ interior (basin F z₁)` is `connectedComponentIn_subset`, its preconnectedness is
   `isPreconnected_connectedComponentIn`, and its `F`-invariance is
   `Work.FatouParabolic2.mapsTo_immBasin`.
-/
import Mathlib
import Submission.Work.SeedFatou.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedFatou

open Classical Filter Function Set
open scoped Topology

noncomputable section

theorem exists_critImm (S : Work.SeedExist.RootSeedData) :
    Nonempty (Work.SeedFatou.CritImmData S) := by
  classical
  -- ### `z₁` is a simple parabolic fixed point of `F = (Tsq S.c)^[5] = (T_c)^[10]`
  have hfix : Work.FSeed.F S.c S.z₁ = S.z₁ :=
    Work.Final.Tantibar_five_fix S.g_fix
  have hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo (Work.FSeed.F S.c) :=
    Work.FatouParabolic.Poly.tsq_iterate_isPolynomialMap S.c (by norm_num)
  have hFdiff : Differentiable ℂ (Work.FSeed.F S.c) :=
    Work.FatouParabolic.Poly.isPolynomialMap_differentiable hF
  have hderiv : deriv (Work.FSeed.F S.c) S.z₁ = 1 := S.mult_one
  -- ### petal data at `z₁` (Fatou's theorem, simple case)
  obtain ⟨pd⟩ := Work.FatouParabolic2.exists_petalData_of_simple hFdiff hfix hderiv S.simple
  -- ### a point of the petal whose orbit enters the half-petal `Pg` of the flower
  obtain ⟨p, hp⟩ := pd.nonempty
  have hne : ∀ m : ℕ, (Work.FSeed.F S.c)^[m] p ≠ S.z₁ := by
    intro m hm
    have hmem : (Work.FSeed.F S.c)^[m] p ∈ pd.Pa :=
      Work.FatouCoord.mapsTo_iterate_of_mapsTo pd.mapsTo_Pa m hp
    exact pd.z₀_not_mem (by rw [hm] at hmem; exact hmem)
  obtain ⟨n, hn⟩ := (Work.SeedExist.flowerOf S).enters_Pg p (pd.tendsto_Pa p hp) hne
  -- ### the critical point of `F` in the immediate basin of `p₀ = F^[n] p`
  obtain ⟨w, hwΩ, hwcrit⟩ :=
    Work.FatouParabolic2.exists_criticalPoint_in_immBasin hF hfix pd
      (Work.FatouCoord.mapsTo_iterate_of_mapsTo pd.mapsTo_Pa n hp)
  -- ### `Pg` lies in the immediate basin
  have hPg_int : (Work.SeedExist.flowerOf S).Pg ⊆
      interior (Work.FatouParabolic.basin (Work.FSeed.F S.c) S.z₁) :=
    interior_maximal
      (fun z hz => Work.FatouParabolic.mem_basin.mpr ((Work.SeedExist.flowerOf S).tendsto_Pg hz))
      (Work.SeedExist.flowerOf S).isOpen_Pg
  have hPgΩ : (Work.SeedExist.flowerOf S).Pg ⊆
      Work.FatouParabolic.Core.immBasin (Work.FSeed.F S.c) S.z₁ ((Work.FSeed.F S.c)^[n] p) :=
    (Work.SeedExist.flowerOf S).isPreconnected_Pg.subset_connectedComponentIn hn hPg_int
  exact ⟨{ Ω := Work.FatouParabolic.Core.immBasin (Work.FSeed.F S.c) S.z₁
              ((Work.FSeed.F S.c)^[n] p)
           w := w
           isPreconnected_Ω := isPreconnected_connectedComponentIn
           Ω_subset := connectedComponentIn_subset _ _
           mapsTo_Ω := Work.FatouParabolic2.mapsTo_immBasin hF pd
             (Work.FatouCoord.mapsTo_iterate_of_mapsTo pd.mapsTo_Pa n hp)
           Pg_subset := hPgΩ
           w_mem := hwΩ
           deriv_w_eq_zero := hwcrit }⟩

end

end Work.SeedFatou
