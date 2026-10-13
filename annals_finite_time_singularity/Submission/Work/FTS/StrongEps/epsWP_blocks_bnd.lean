import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.classC_mixed_sup_le_four
import Submission.Work.FTS.StrongEps.HQo_mixed_abs_le_on_compact
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.StrongEps.blocks.Fstar_AK_bnd
import Submission.Work.FTS.StrongEps.blocks.star_blocks_bnd
import Submission.Work.FTS.StrongEps.blocks.HQo_mixed_abs_le_on_compact_uniform
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS_EllLimOK.box_of_compact_inside_Q0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.StrongEps

set_option maxHeartbeats 2000000

theorem epsWP_blocks_bnd {α C₀ Cs Ce T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hε : ε ∈ Set.Ioc 0 1) (hT : 0 ≤ T)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hC : ∀ s ∈ Set.Icc 0 T,
      Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))
    (hb4 : ∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ Ce)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc 0 T, ∀ z θ : ℝ, (z, θ) ∈ K →
      |Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s z θ|
        + |Work.Spaces.pth (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ|
        + |Work.Spaces.Dz (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ|
        + |Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s z θ|
        + |Work.Spaces.Dz (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ|
        + |Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        + |Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
        + |Work.Construction.Rop α (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ ε g)) s)) z θ|
        + |Work.Construction.Uop α (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ ε g)) s)) z θ|
        + |Work.Construction.Vop (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ ε g)) s)) z θ|
        + |Work.Construction.AK α z θ| ≤ B := by
  classical
  rcases Set.eq_empty_or_nonempty K with hKe | hne
  · subst hKe
    exact ⟨0, le_refl 0, fun s hs z θ hp => absurd hp (by simp)⟩
  obtain ⟨zlo, zhi, tlo, thi, hzlo, hzlole, htlo, htlole, hthilt, hKbox⟩ :=
    Work.FTS_EllLimOK.box_of_compact_inside_Q0 hK hKQ hne
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  obtain ⟨Cx, hCxpos, hCx⟩ := Work.FTS.StrongEps.classC_mixed_sup_le_four
  obtain ⟨Cq, hCqpos, hCq⟩ := blocks.HQo_mixed_abs_le_on_compact_uniform (K := K) hK hKQ
  obtain ⟨CF, hCFpos, hCF⟩ := blocks.Fstar_AK_bnd hα0 hα1 htlo htlole hthilt
  obtain ⟨CS, hCSpos, hCS⟩ := blocks.star_blocks_bnd (α := α) (Cs := Cs) (c := tlo) hstar htlo
  refine ⟨(CF + Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0)
      + (CF + (Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0)
          / (4 / Real.pi * min tlo (Real.pi / 2 - thi)))
      + (CF + Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0)
      + (Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0)
      + (Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0)
      + CF + CF
      + (CS + Cq * (max Ce 0 * max Ce 0))
      + (CS + Cq * (max Ce 0 * max Ce 0))
      + (CS + Cq * (max Ce 0 * max Ce 0))
      + CF, ?_, ?_⟩
  · -- nonnegativity
    have hγ1 : 0 < Work.Spaces.gam α - 1 := by
      rw [Work.Spaces.gam]; linarith
    have hK1 : 0 ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) :=
      (div_pos hCxpos (Real.sqrt_pos.mpr hγ1)).le
    have hCe : 0 ≤ max Ce 0 := le_max_right _ _
    have hmm : 0 < min tlo (Real.pi / 2 - thi) := lt_min htlo (by linarith)
    have hsLB : 0 < 4 / Real.pi * min tlo (Real.pi / 2 - thi) := by positivity
    have h1 : 0 ≤ CF + Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := by
      have := mul_nonneg hK1 hCe; linarith
    have h2 : 0 ≤ CF + (Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0)
        / (4 / Real.pi * min tlo (Real.pi / 2 - thi)) := by
      have h0 : 0 ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := mul_nonneg hK1 hCe
      have := div_nonneg h0 hsLB.le; linarith
    have h3 : 0 ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := mul_nonneg hK1 hCe
    have h4 : 0 ≤ CS + Cq * (max Ce 0 * max Ce 0) := by
      have := mul_nonneg hCqpos.le (mul_nonneg hCe hCe); linarith
    linarith [hCFpos, hCSpos, h1, h2, h3, h4]
  · intro s hs z θ hzθ
    obtain ⟨hzQ, hθQ1, hθQ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hzθ)
    obtain ⟨hzb, hθb⟩ := hKbox hzθ
    have htloθ : tlo ≤ θ := hθb.1
    have hθthi : θ ≤ thi := hθb.2
    -- the angular lower bound
    have hsinLB : 4 / Real.pi * min tlo (Real.pi / 2 - thi) ≤ Real.sin (2 * θ) := by
      have h1 : min tlo (Real.pi / 2 - thi) ≤ min θ (Real.pi / 2 - θ) :=
        le_min (le_trans (min_le_left _ _) htloθ)
          (le_trans (min_le_right _ _) (by linarith))
      have h2 := Work.FTS.H2.sin_two_ge_min θ ⟨le_of_lt hθQ1, le_of_lt hθQ2⟩
      exact le_trans (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
    -- abbreviations
    let Gs : Fn := slice (Work.FTS.StrongEps.JfamP ρ ε g) s
    have hgsC : Work.FTS.ClassC.ClassC α Gs := hC s hs
    have hgsS : Work.FTS.EllipticEst.SmoothOpen Gs := hgsC.reg
    have hgs4 : Work.Spaces.HkMem α 4 Gs :=
      Work.FTS.OpenPkg.HkMem_mono_open hgsS 4 (by norm_num) hgsC.mem
    have hn6 : Work.Spaces.HkNorm α 6 Gs ≤ max Ce 0 :=
      le_trans (hb6 s hs) (le_max_left _ _)
    have hgo : Work.FTS.VocabO.EllPkgGo α Ce Gs (E Gs) := (hEll Gs hgsC).1
    have hk6 : Work.FTS.ClassC.EllPkgK α 6 Ce Gs (E Gs) := (hEll Gs hgsC).2
    have hFstarS : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
      Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
    have hPsiS : Work.FTS.EllipticEst.SmoothOpen
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) :=
      Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil_star hα0 hα1 hstar
    have hXiS : Work.FTS.EllipticEst.SmoothOpen
        (Work.Construction.PhiTil α Gs (E Gs)) :=
      Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα0 hgo
    -- constants
    have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam]; linarith
    have hK1nn : 0 ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) :=
      (div_pos hCxpos (Real.sqrt_pos.mpr hγ1)).le
    have hCenn : 0 ≤ max Ce 0 := le_max_right _ _
    have hsLBpos : 0 < 4 / Real.pi * min tlo (Real.pi / 2 - thi) := by positivity
    -- ### the eleven blocks
    -- (6),(7),(11): the star profile
    have eF : |Work.Construction.Fstar α z θ| ≤ CF := by
      have h := hCF z θ hzQ htloθ hθthi
      have h2 := abs_nonneg (Work.Spaces.pth (Work.Construction.Fstar α) z θ)
      have h3 := abs_nonneg (Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
      have h4 := abs_nonneg (Work.Construction.AK α z θ)
      linarith
    have eFp : |Work.Spaces.pth (Work.Construction.Fstar α) z θ| ≤ CF := by
      have h := hCF z θ hzQ htloθ hθthi
      have h2 := abs_nonneg (Work.Construction.Fstar α z θ)
      have h3 := abs_nonneg (Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
      have h4 := abs_nonneg (Work.Construction.AK α z θ)
      linarith
    have eFz : |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ CF := by
      have h := hCF z θ hzQ htloθ hθthi
      have h2 := abs_nonneg (Work.Construction.Fstar α z θ)
      have h3 := abs_nonneg (Work.Spaces.pth (Work.Construction.Fstar α) z θ)
      have h4 := abs_nonneg (Work.Construction.AK α z θ)
      linarith
    have eAK : |Work.Construction.AK α z θ| ≤ CF := by
      have h := hCF z θ hzQ htloθ hθthi
      have h2 := abs_nonneg (Work.Construction.Fstar α z θ)
      have h3 := abs_nonneg (Work.Spaces.pth (Work.Construction.Fstar α) z θ)
      have h4 := abs_nonneg (Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
      linarith
    -- (4),(5): the slots of `Gs`
    have hslot : ∀ (b a : ℕ), a + b ≤ 4 →
        |Work.Spaces.mixed b a Gs z θ| ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := by
      intro b a hab
      have h := hCx α hα hgsC b a hab ⟨hzQ, hθQ1, hθQ2⟩
      exact le_trans h (mul_le_mul_of_nonneg_left hn6 hK1nn)
    have eG : |slice (Work.FTS.StrongEps.JfamP ρ ε g) s z θ|
        ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := by
      have h := hslot 0 0 (by norm_num)
      simpa only [Gs, Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
    have eGz : |Work.Spaces.Dz (slice (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ|
        ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := by
      have h := hslot 1 0 (by norm_num)
      simpa only [Gs, Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ,
        Work.Spaces.DzIter_zero] using h
    -- (1): `Ftau = F* + Gs`
    have e1 : |Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s z θ|
        ≤ CF + Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := by
      rw [show Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s z θ
          = Work.Construction.Fstar α z θ + Gs z θ from rfl]
      exact le_trans (abs_add_le _ _) (add_le_add eF eG)
    -- (2): `pth Ftau = pth F* + pth Gs`
    have eGp : |Work.Spaces.pth Gs z θ|
        ≤ (Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0)
          / (4 / Real.pi * min tlo (Real.pi / 2 - thi)) := by
      have hsinpos : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hmix : |Work.Spaces.Dth Gs z θ| ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := by
        have h := hslot 0 1 (by norm_num)
        simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
          Work.Spaces.DthIter_zero, Work.Spaces.Dth] using h
      have hmul : Real.sin (2 * θ) * |Work.Spaces.pth Gs z θ|
          ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := by
        rw [Work.Spaces.Dth, abs_mul, abs_of_pos hsinpos] at hmix
        exact hmix
      have h1 : |Work.Spaces.pth Gs z θ|
          ≤ Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 / Real.sin (2 * θ) := by
        rw [le_div_iff₀ hsinpos, mul_comm]
        exact hmul
      refine le_trans h1 (div_le_div_of_nonneg_left (mul_nonneg hK1nn hCenn) hsLBpos hsinLB)
    have e2 : |Work.Spaces.pth (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ|
        ≤ CF + (Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0)
          / (4 / Real.pi * min tlo (Real.pi / 2 - thi)) := by
      rw [show Work.Spaces.pth (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ
          = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth Gs z θ from ?_]
      · exact le_trans (abs_add_le _ _) (add_le_add eFp eGp)
      · exact Work.FTS.GalFields.RHS.Sharp.pth_add_Q0 hFstarS hgsS z θ hzQ hθQ1 hθQ2
    -- (3): `Dz Ftau = Dz F* + Dz Gs`
    have e3 : |Work.Spaces.Dz (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ|
        ≤ CF + Cx / Real.sqrt (Work.Spaces.gam α - 1) * max Ce 0 := by
      have hpz := Work.FTS.GalFields.RHS.Sharp.pz_add_Q0 hFstarS hgsS z θ hzQ hθQ1 hθQ2
      rw [show Work.Spaces.Dz (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ
          = Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + Gs z θ) z θ from rfl]
      rw [show Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + Gs z θ) z θ
          = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz Gs z θ from ?_]
      · exact le_trans (abs_add_le _ _) (add_le_add eFz (by
          have h := hslot 1 0 (by norm_num)
          simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ,
            Work.Spaces.DzIter_zero] using h))
      · simp only [Work.Spaces.Dz, hpz]; ring
    -- (8),(9),(10): the `PhiTil` split
    have hpot : ∀ z' θ' : ℝ, 0 < z' →
        Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + Gs z θ)
            (fun z θ => Φs z θ + E Gs z θ) z' θ'
          = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ'
            + Work.Construction.PhiTil α Gs (E Gs) z' θ' := by
      intro z' θ' hz'
      have hL := blocks.L12_Fstar_add_open hα0 hα1 hgsS hgs4 (z := z') (le_of_lt hz')
      simp only [Work.Construction.PhiTil, Work.Construction.Theta]
      rw [hL]
      ring
    have hXinorm : Work.Spaces.HkNorm α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α Gs (E Gs)))
        ≤ max Ce 0 * max Ce 0 := by
      refine le_trans hk6.R.2 ?_
      by_cases hCe : 0 ≤ Ce
      · have hCe' : max Ce 0 = Ce := max_eq_left hCe
        have hn6' : Work.Spaces.HkNorm α 6 Gs ≤ Ce := by rw [← hCe']; exact hn6
        rw [hCe']
        exact mul_le_mul_of_nonneg_left hn6' hCe
      · have hCe' : max Ce 0 = 0 := max_eq_right (not_le.mp hCe).le
        have h1 : Work.Spaces.HkNorm α 6 Gs ≤ 0 := le_trans hn6 (le_of_eq hCe')
        have h2 : 0 ≤ Work.Spaces.HkNorm α 6 Gs := Work.Spaces.HkNorm_nonneg α 6 Gs
        rw [hCe']
        nlinarith [h1, h2, hCe]
    have hXiUnorm : Work.Spaces.HkNorm α 6 (fun z θ =>
          Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ
            / Work.Construction.s2 θ) ≤ max Ce 0 * max Ce 0 := by
      refine le_trans hk6.U.2 ?_
      by_cases hCe : 0 ≤ Ce
      · have hCe' : max Ce 0 = Ce := max_eq_left hCe
        have hn6' : Work.Spaces.HkNorm α 6 Gs ≤ Ce := by rw [← hCe']; exact hn6
        rw [hCe']
        exact mul_le_mul_of_nonneg_left hn6' hCe
      · have hCe' : max Ce 0 = 0 := max_eq_right (not_le.mp hCe).le
        have h1 : Work.Spaces.HkNorm α 6 Gs ≤ 0 := le_trans hn6 (le_of_eq hCe')
        have h2 : 0 ≤ Work.Spaces.HkNorm α 6 Gs := Work.Spaces.HkNorm_nonneg α 6 Gs
        rw [hCe']
        nlinarith [h1, h2, hCe]
    have hXiVnorm : Work.Spaces.HkNorm α 6 (Work.Construction.Vop (Work.Construction.PhiTil α Gs (E Gs)))
        ≤ max Ce 0 * max Ce 0 := by
      refine le_trans hk6.V.2 ?_
      by_cases hCe : 0 ≤ Ce
      · have hCe' : max Ce 0 = Ce := max_eq_left hCe
        have hn6' : Work.Spaces.HkNorm α 6 Gs ≤ Ce := by rw [← hCe']; exact hn6
        rw [hCe']
        exact mul_le_mul_of_nonneg_left hn6' hCe
      · have hCe' : max Ce 0 = 0 := max_eq_right (not_le.mp hCe).le
        have h1 : Work.Spaces.HkNorm α 6 Gs ≤ 0 := le_trans hn6 (le_of_eq hCe')
        have h2 : 0 ≤ Work.Spaces.HkNorm α 6 Gs := Work.Spaces.HkNorm_nonneg α 6 Gs
        rw [hCe']
        nlinarith [h1, h2, hCe]
    -- the star part
    have eS : |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        + |Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        + |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        ≤ CS := hCS z θ hzQ htloθ hθQ2
    have eSR : |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ| ≤ CS := by
      have h2 := abs_nonneg (Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
      have h3 := abs_nonneg (Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
      linarith
    have eSU : |Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ| ≤ CS := by
      have h2 := abs_nonneg (Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
      have h3 := abs_nonneg (Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
      linarith
    have eSV : |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ| ≤ CS := by
      have h2 := abs_nonneg (Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
      have h3 := abs_nonneg (Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
      linarith
    -- the `EllPkgK` part
    have eXR : |Work.Construction.Rop α (Work.Construction.PhiTil α Gs (E Gs)) z θ|
        ≤ Cq * (max Ce 0 * max Ce 0) := by
      have h := hCq α hα0 hα1 (Work.Construction.Rop α (Work.Construction.PhiTil α Gs (E Gs)))
        hk6.R.1 0 0 (by norm_num) z θ hzθ
      have h' : |Work.Construction.Rop α (Work.Construction.PhiTil α Gs (E Gs)) z θ|
          ≤ Cq * Work.Spaces.HkNorm α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α Gs (E Gs))) := by
        simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
      exact le_trans h' (mul_le_mul_of_nonneg_left hXinorm hCqpos.le)
    have eXU : |Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ|
        ≤ Cq * (max Ce 0 * max Ce 0) := by
      have h := hCq α hα0 hα1 (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ
          / Work.Construction.s2 θ) hk6.U.1 0 0 (by norm_num) z θ hzθ
      have h' : |Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ
          / Work.Construction.s2 θ| ≤ Cq * (max Ce 0 * max Ce 0) := by
        have h'' : |(fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ
            / Work.Construction.s2 θ) z θ| ≤ Cq *
            Work.Spaces.HkNorm α 6 (fun z θ => Work.Construction.Uop α
              (Work.Construction.PhiTil α Gs (E Gs)) z θ / Work.Construction.s2 θ) := by
          simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
        exact le_trans h'' (mul_le_mul_of_nonneg_left hXiUnorm hCqpos.le)
      have hs2pos : 0 < Work.Construction.s2 θ :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hs2le : Work.Construction.s2 θ ≤ 1 := by
        simp only [Work.Construction.s2]; exact Real.sin_le_one _
      have hs2nn : 0 ≤ Work.Construction.s2 θ := le_of_lt hs2pos
      rw [show Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ
          = (Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ
              / Work.Construction.s2 θ) * Work.Construction.s2 θ from by
        field_simp]
      calc |(Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ
            / Work.Construction.s2 θ) * Work.Construction.s2 θ|
          = |Work.Construction.Uop α (Work.Construction.PhiTil α Gs (E Gs)) z θ
              / Work.Construction.s2 θ| * |Work.Construction.s2 θ| := abs_mul _ _
        _ ≤ (Cq * (max Ce 0 * max Ce 0)) * 1 :=
            mul_le_mul h' (by rw [abs_of_nonneg hs2nn]; exact hs2le) (abs_nonneg _)
              (mul_nonneg hCqpos.le (mul_nonneg hCenn hCenn))
        _ = Cq * (max Ce 0 * max Ce 0) := by ring
    have eXV : |Work.Construction.Vop (Work.Construction.PhiTil α Gs (E Gs)) z θ|
        ≤ Cq * (max Ce 0 * max Ce 0) := by
      have h := hCq α hα0 hα1 (Work.Construction.Vop (Work.Construction.PhiTil α Gs (E Gs)))
        hk6.V.1 0 0 (by norm_num) z θ hzθ
      have h' : |Work.Construction.Vop (Work.Construction.PhiTil α Gs (E Gs)) z θ|
          ≤ Cq * Work.Spaces.HkNorm α 6 (Work.Construction.Vop (Work.Construction.PhiTil α Gs (E Gs))) := by
        simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
      exact le_trans h' (mul_le_mul_of_nonneg_left hXiVnorm hCqpos.le)
    -- the three operator blocks
    have e8 : |Work.Construction.Rop α (Work.Construction.PhiTil α
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) s)) z θ|
        ≤ CS + Cq * (max Ce 0 * max Ce 0) := by
      have hcongr := Work.FTS.GalFields.RHS.Sharp.Rop_congr_Q0
        (α := α)
        (f := Work.Construction.PhiTil α (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) s))
        (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Work.Construction.PhiTil α Gs (E Gs) z θ)
        (fun z' θ' hz' _ _ => hpot z' θ' hz') z θ hzQ hθQ1 hθQ2
      rw [hcongr, Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0 hPsiS hXiS z θ hzQ hθQ1 hθQ2]
      exact le_trans (abs_add_le _ _) (add_le_add eSR eXR)
    have e9 : |Work.Construction.Uop α (Work.Construction.PhiTil α
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) s)) z θ|
        ≤ CS + Cq * (max Ce 0 * max Ce 0) := by
      have hcongr := Work.FTS.GalFields.RHS.Sharp.Uop_congr_Q0
        (α := α)
        (f := Work.Construction.PhiTil α (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) s))
        (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Work.Construction.PhiTil α Gs (E Gs) z θ)
        (fun z' θ' hz' _ _ => hpot z' θ' hz') z θ hzQ hθQ1 hθQ2
      rw [hcongr, Work.FTS.GalFields.RHS.Sharp.Uop_add_Q0 hPsiS hXiS z θ hzQ hθQ1 hθQ2]
      exact le_trans (abs_add_le _ _) (add_le_add eSU eXU)
    have e10 : |Work.Construction.Vop (Work.Construction.PhiTil α
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) s)) z θ|
        ≤ CS + Cq * (max Ce 0 * max Ce 0) := by
      have hcongr := Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0
        (f := Work.Construction.PhiTil α (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) s)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) s))
        (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Work.Construction.PhiTil α Gs (E Gs) z θ)
        (fun z' θ' hz' _ _ => hpot z' θ' hz') z θ hzQ hθQ1 hθQ2
      rw [hcongr, Work.FTS.GalFields.RHS.Sharp.Vop_add_Q0 hPsiS hXiS z θ hzQ hθQ1 hθQ2]
      exact le_trans (abs_add_le _ _) (add_le_add eSV eXV)
    -- ### assembly
    exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add (add_le_add (add_le_add (add_le_add e1 e2) e3) eG) eGz) eFp) eFz)
      e8) e9) e10) eAK

end Work.FTS.StrongEps
