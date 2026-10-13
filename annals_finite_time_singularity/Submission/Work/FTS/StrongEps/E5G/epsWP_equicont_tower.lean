import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.E5G.mixed_rect_L2_bounds_level
import Submission.Work.FTS.StrongEps.E5G.morrey_step_four
import Submission.Work.FTS_EllLimOK.box_of_compact_inside_Q0
import Submission.Work.FTS.StrongLWP.Sobolev.EqcAux.exists_cutoff_rect_C2
import Submission.Work.FTS.StrongLWP.Sobolev.holder_half_of_W22

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

/-!
# `Work.FTS.StrongEps.E5G.epsWP_equicont_tower`

The Hölder-`1/2` equicontinuity of the tower family `n ↦ epsWP α ρ (ε n) Φs E (G n)` on every
compact `K ⊆ Q0`, uniformly in the piece index `n` and in the fake time `s ∈ [0,T]`, with the
constant `(1 + B4)` coming from the uniform `ℋ⁴`-ball `B4`.

## Route

1. **Morrey at level 4 on a compact.**  A compact `K ⊆ Q0 = (0,∞)×(0,π/2)` sits in a box
   `[zlo,zhi] × [tlo,thi]` whose two-fold enlargement `[zlo/2, zhi+1] × [tlo/2, (thi+π/2)/2]`
   still lies in `Q0` (`FTS_EllLimOK.box_of_compact_inside_Q0` plus padding); a `C²` cut-off `χ`
   equal to `1` on the box and vanishing outside the enlargement
   (`Sobolev.EqcAux.exists_cutoff_rect_C2`) makes `χ · F` a `C²` function with compact support,
   to which Morrey `W^{2,2}(ℝ²) ⊂ C^{0,1/2}` (`Sobolev.holder_half_of_W22_real`) applies.
2. **The two `L²`-inputs of Morrey.**  On the enlargement the plain partials of `F` up to order
   two — `F`, `pz F`, `pth F`, `pz(pz F)`, `pz(pth F)`, `pth(pz F)`, `pth(pth F)` — are
   dominated by `C · HkSq α 4 F`: this is `E5G.mixed_rect_L2_bounds_level` at `k = 4`,
   `(j,i) = (0,0)` (which in turn inverts the plain partials into the mixed slots via
   `LocUnif.mixed_partials_of_smoothOpen` and dominates each slot pointwise by
   `HkIntegrand α 4 F`).  Feeding these seven bounds into `E5G.morrey_step_four` (the slot-`(0,0)`
   level-`4` Morrey step) yields the bound with an `α`- and `F`-free constant.
3. **Assembly.**  The constant is chosen before `n`, `s`, `F`; the only remaining step is
   `HkNorm α 4 F ≤ B4` and square-root bookkeeping (`dist p q ^ (1/2:ℝ) = √‖p-q‖`).

`T` (and hence the time interval), the scale sequence `ε`, and the family `G` enter only through
the three hypotheses `hsm`, `hmem`, `hb`, so the result is uniform in the tower.
-/

/-- **Morrey's estimate at level `4` on a compact subset of the open quadrant.**

For a compact `K ⊆ Q0` there is a constant `C > 0` such that every `F` which is `C^∞` on the
open quadrant and lies in `ℋ⁴` satisfies, for all `p, q ∈ K`,

  `|F p - F q| ≤ C · (1 + |F|_{ℋ⁴}) · √‖p - q‖`.

This is the `χ`-cut-off version of the classical `W^{2,2}(ℝ²) ⊂ C^{0,1/2}` Morrey estimate with
the `W^{2,2}`-norm priced by `|F|_{ℋ⁴}`: at level `4` the only slot whose *second* derivatives are
still controlled is the value `D_z^0D_θ^0 F`. -/
private theorem holder_on_compact_of_HkMem_four {α : ℝ} (hα : 0 < α)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen F →
      Work.Spaces.HkMem α 4 F → ∀ p ∈ K, ∀ q ∈ K,
        |F p.1 p.2 - F q.1 q.2| ≤ C * (1 + Work.Spaces.HkNorm α 4 F)
          * Real.sqrt ‖p - q‖ := by
  classical
  rcases Set.eq_empty_or_nonempty K with hKe | hne
  · subst hKe
    exact ⟨1, one_pos, fun F _ _ p hp => absurd hp (by simp)⟩
  · -- ## the box containing `K`, and its two-fold enlargement
    obtain ⟨zlo, zhi, tlo, thi, hzlopos, hzlole, htlopos, htlole, hthilt, hKbox⟩ :=
      Work.FTS_EllLimOK.box_of_compact_inside_Q0 hK hKQ hne
    have hzlo'pos : 0 < zlo / 2 := by linarith
    have hzlo'lt : zlo / 2 < zlo := by linarith
    have hzhi'lt : zhi < zhi + 1 := by linarith
    have hzlo'le : zlo / 2 ≤ zhi + 1 := by linarith
    have htlo'pos : 0 < tlo / 2 := by linarith
    have htlo'lt : tlo / 2 < tlo := by linarith
    have hthi'lt : thi < (thi + Real.pi / 2) / 2 := by linarith [Real.pi_pos]
    have hthi'pi : (thi + Real.pi / 2) / 2 < Real.pi / 2 := by linarith
    have hboxsub : Set.Icc (zlo / 2) (zhi + 1) ×ˢ Set.Icc (tlo / 2) ((thi + Real.pi / 2) / 2)
        ⊆ Work.FTS.EllipticEst.Q0 := by
      rintro ⟨z, θ⟩ ⟨hz, hθ⟩
      exact Work.FTS.EllipticEst.mem_Q0.mpr
        ⟨by linarith [hz.1], by linarith [hθ.1], by linarith [hθ.2]⟩
    -- ## the cut-off
    obtain ⟨χ, M, hMpos, hχsm, hχcs, hχnn, hχle1, hχone, hχzero, hM1, hM2⟩ :=
      Work.FTS.StrongLWP.Sobolev.EqcAux.exists_cutoff_rect_C2
        (a := zlo) (b := zhi) (c := tlo) (d := thi)
        (a' := zlo / 2) (b' := zhi + 1) (c' := tlo / 2) (d' := (thi + Real.pi / 2) / 2)
        hzlo'pos hzlo'lt hzlole hzhi'lt htlo'pos htlo'lt htlole hthi'lt hthi'pi
    have hχ2 : ContDiff ℝ 2 χ := by simpa using hχsm 2
    -- ## the level-`4` rectangle bounds on the support of `χ`
    obtain ⟨Cl, hClpos, hClbound⟩ :=
      mixed_rect_L2_bounds_level (a := zlo / 2) (b := zhi + 1) (c := tlo / 2)
        (d := (thi + Real.pi / 2) / 2) hzlo'pos hzlo'le htlo'pos hthi'pi
    -- ## Morrey
    obtain ⟨Km, hKmpos, hMor⟩ := Work.FTS.StrongLWP.Sobolev.holder_half_of_W22_real
    refine ⟨Km * (2 * Real.sqrt (Cl + 3 * Cl * (16 + 17 * M ^ 2))) + 1, by positivity, ?_⟩
    intro F hFsm hFmem p hp q hq
    obtain ⟨hmix, hpz1, hpth1, hpz2, hpzpth, hpthpz, hpth2⟩ :=
      hClbound 4 α hα F hFsm hFmem 0 0 (by norm_num)
    have hm := morrey_step_four (χ := χ) (F := F) (α := α) (C := Cl)
      (C₀ := Work.Spaces.HkNorm α 4 F) (M := M) (Km := Km)
      (a := zlo) (b := zhi) (c := tlo) (d := thi)
      (a' := zlo / 2) (b' := zhi + 1) (c' := tlo / 2) (d' := (thi + Real.pi / 2) / 2)
      hMor (le_of_lt hKmpos) hα hClpos (Work.Spaces.HkNorm_nonneg α 4 F) hχ2 hχcs hχnn
      hχle1 hχone hχzero hM1 hM2 hboxsub hFsm hFmem le_rfl
      ⟨hmix, hpz1, hpth1,
        by simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
          Work.Spaces.DzIter_zero, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using hpz2,
        hpzpth, hpthpz,
        by simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
          Work.Spaces.DzIter_zero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hpth2⟩
      p (hKbox hp) q (hKbox hq)
    have hdist : dist p q ^ (1 / 2 : ℝ) = Real.sqrt ‖p - q‖ := by
      rw [Real.sqrt_eq_rpow, dist_eq_norm]
    have hAnn : 0 ≤ Km * (2 * Real.sqrt (Cl + 3 * Cl * (16 + 17 * M ^ 2))) := by positivity
    have hMnn : 0 ≤ Work.Spaces.HkNorm α 4 F := Work.Spaces.HkNorm_nonneg α 4 F
    calc |F p.1 p.2 - F q.1 q.2|
        ≤ Km * (2 * Real.sqrt (Cl + 3 * Cl * (16 + 17 * M ^ 2)) * Work.Spaces.HkNorm α 4 F)
            * dist p q ^ (1 / 2 : ℝ) := hm
      _ = Km * (2 * Real.sqrt (Cl + 3 * Cl * (16 + 17 * M ^ 2)))
            * Work.Spaces.HkNorm α 4 F * Real.sqrt ‖p - q‖ := by rw [hdist]; ring
      _ ≤ (Km * (2 * Real.sqrt (Cl + 3 * Cl * (16 + 17 * M ^ 2))) + 1)
            * (1 + Work.Spaces.HkNorm α 4 F) * Real.sqrt ‖p - q‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          nlinarith [hAnn, hMnn]

theorem epsWP_equicont_tower {α B4 T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam}
    {K : Set (ℝ × ℝ)}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hK : IsCompact K)
    (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    (hsm : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s))
    (hmem : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s))
    (hb : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) ≤ B4) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ p ∈ K, ∀ q ∈ K,
      |Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s p.1 p.2
        - Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s q.1 q.2|
        ≤ C * (1 + B4) * Real.sqrt ‖p - q‖ := by
  obtain ⟨C, hCpos, hkey⟩ := holder_on_compact_of_HkMem_four (α := α) hα.1 hK hKQ
  refine ⟨C, hCpos, ?_⟩
  intro n s hs p hp q hq
  have hbF : Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) ≤ B4 :=
    hb n s hs
  have hB4nn : 0 ≤ B4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 _) hbF
  have h := hkey (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) (hsm n s hs)
    (hmem n s hs) p hp q hq
  have h1 : 1 + Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)
      ≤ 1 + B4 := by linarith
  have h2 : C * (1 + Work.Spaces.HkNorm α 4
        (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) ≤ C * (1 + B4) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt hCpos)
  exact h.trans (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _))

end Work.FTS.StrongEps.E5G
