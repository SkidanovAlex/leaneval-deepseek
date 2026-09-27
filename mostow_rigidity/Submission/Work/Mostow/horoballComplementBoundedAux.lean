import Mathlib
import Submission.Work.Mostow.geomFiniteThickThinDefs
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.thinTubeDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.hptOfLevelYc
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.cuspCocompactAllLevels
import Submission.Work.Mostow.cuspCocompactAtLevel
import Submission.Mostow.HLDefs
import Submission.Mostow.GapADefs
import Submission.Work.Mostow.HL_of_escapeShort
import Submission.Work.Mostow.gapA_all_aux
import Submission.Work.Mostow.geomFiniteParabolicClass
import Submission.Work.Mostow.stabHorosphere
import Submission.Work.Mostow.orbitFree_stab_busemann

/-!
# Auxiliary lemmas for `Work.Mostow.horoballComplementBounded`

This module contains the escape analysis behind `Work.Mostow.horoballComplementBounded`
(`no_escaping_dirichlet`), the assembly `horoballComplementBounded_aux` which reduces that
statement to two geometric inputs (HL and the cocompactness of cusp stabilisers on horospheres)
and two chart computations, and the helper lemmas they rest on.

The requested statement itself lives in `Submission/Work/Mostow/horoballComplementBounded.lean`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Filter

noncomputable section

variable {n : ℕ}

/-- The Busemann cocycle of an element fixing a parabolic fixed point vanishes, for an equivariant
height. -/
lemma bCocy_eq_zero_of_isEquivHeight (Γ : Subgroup (PO n 1)) (ht : E n → ℝ)
    (heq : IsEquivHeight Γ (parFixed Γ) ht) (γ : Γ) (ξ : E n) (hξ : ξ ∈ parFixed Γ)
    (hfix : bd (γ : PO n 1) ξ = ξ) : bCocy (γ : PO n 1) ξ = 0 := by
  have h := heq γ ξ hξ
  rw [hfix] at h
  linarith

/-- The identity `tpart u = (1 + L² (1 + ‖yc ξ u‖²)) / (2 L)` where `L = lev ξ u`. -/
lemma tpart_eq_of_lev_yc (hI : HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) :
    tpart u = (1 + (lev ξ u) ^ 2 * (1 + ‖yc ξ u‖ ^ 2)) / (2 * lev ξ u) := by
  have hL : 0 < lev ξ u := lev_pos ξ hξ u
  have h1 := one_add_norm_wc_sq hξ u
  have hwc : ‖wc ξ u‖ ^ 2 = (lev ξ u) ^ 2 * ‖yc ξ u‖ ^ 2 := by
    have hsm : wc ξ u = lev ξ u • yc ξ u := by
      rw [yc, smul_smul, mul_inv_cancel₀ (ne_of_gt hL), one_smul]
    rw [hsm, norm_smul, Real.norm_eq_abs, abs_of_pos hL, mul_pow]
  rw [hwc] at h1
  have hin : tpart u + inner ℝ u ξ = 2 * tpart u - lev ξ u := by
    rw [lev]; ring
  rw [hin] at h1
  rw [eq_div_iff (by positivity)]
  linarith

/-- **The flat coordinate of a Dirichlet point at a cusp is bounded.**  For a lattice `Γ`, a
parabolic fixed point `ξ` and a point of `Dirichlet Γ`, the flat coordinate `yc ξ ·` is bounded
by a constant depending only on `Γ`, `ξ` and the compact fundamental set of `Γ_ξ` on the
horosphere. -/
lemma dirichlet_flat_coord_bounded (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n)
    (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1)) (ξ : E n) (hξ : ξ ∈ parFixed Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ parFixed Γ → bd (γ : PO n 1) η = η → bCocy (γ : PO n 1) η = 0)
    (hcoc : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, lev ξ u = 1 →
      ∃ γ : Γ, bd (γ : PO n 1) ξ = ξ ∧ (γ : PO n 1) • u ∈ K) :
    ∃ C : ℝ, ∀ z : E n, z ∈ Dirichlet Γ → ‖yc ξ z‖ ≤ C := by
  have hP : POBasic n := POBasic.ofProp hA
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have hξS : ξ ∈ Sph n := hξ.1
  obtain ⟨K, hKc, hK⟩ := hcoc
  have hyccont : Continuous (fun u : E n => yc ξ u) := by
    have htpart : Continuous (fun u : E n => tpart u) := by
      simp only [tpart]
      fun_prop
    have hlev : Continuous (fun u : E n => lev ξ u) := by
      simp only [lev]
      exact htpart.sub (continuous_inner.comp (continuous_id.prodMk continuous_const))
    have hwc : Continuous (fun u : E n => wc ξ u) := by
      simp only [wc]
      fun_prop
    exact (hlev.inv₀ (fun u => ne_of_gt (lev_pos ξ hξS u))).smul hwc
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hyccont.continuousOn
  refine ⟨C, fun z hz => ?_⟩
  have hyc0 : yc ξ (0 : E n) = 0 := by simp [yc, wc, lev, tpart]
  have hlev0 : lev ξ (0 : E n) = 1 := by simp [lev, tpart]
  have hlevfix : ∀ (γ : Γ), bd (γ : PO n 1) ξ = ξ → ∀ u : E n,
      lev ξ ((γ : PO n 1) • u) = lev ξ u := by
    intro γ hγ u
    have h := lev_smul_self hId hP ξ hξS (γ : PO n 1) u hγ
    have h1 : lev ξ ((γ : PO n 1) • (0 : E n)) = 1 := by
      have h2 : lev ξ ((γ : PO n 1) • (0 : E n)) = Real.exp (bCocy (γ : PO n 1) ξ) := by
        rw [bCocy, lev_eq_exp hξS, hγ]
      rw [h2, hvan γ ξ hξ hγ, Real.exp_zero]
    rw [h, h1, mul_one]
  set L := lev ξ z with hL
  set y := yc ξ z with hy
  have hLpos : 0 < L := lev_pos ξ hξS z
  have hyperp : inner ℝ y ξ = 0 := by rw [hy]; exact inner_yc hξS z
  have hlev1 : lev ξ (hptOf ξ y 1) = 1 := (hptOf_level ξ hξS 1 one_pos y hyperp).1
  obtain ⟨γ, hγbd, hγK⟩ := hK (hptOf ξ y 1) hlev1
  have hkey : yc ξ ((γ : PO n 1) • z) = yc ξ ((γ : PO n 1) • hptOf ξ y 1) := by
    rw [← yc_smul_hptOf_levelIndep hA hI ξ hξS (γ : PO n 1) hγbd (hlevfix γ hγbd) y hyperp
      L 1 hLpos one_pos]
    rw [hptOf_yc ξ hξS L hLpos z rfl]
  have hbound : ‖yc ξ ((γ : PO n 1) • z)‖ ≤ C := by rw [hkey]; exact hC _ hγK
  have hdirle : hdist (0 : E n) z ≤ hdist (0 : E n) ((γ : PO n 1) • z) := hz γ
  have hfl1 : Real.cosh (hdist (0 : E n) z) = Real.cosh (Real.log L) + (L / 2) * ‖y‖ ^ 2 := by
    have h := levYcFormula hξS z (0 : E n)
    rw [hI.2.1 z 0] at h
    rw [hyc0, hlev0, mul_one, sub_zero] at h
    rw [← hL, ← hy] at h
    simpa using h
  have hfl2 : Real.cosh (hdist (0 : E n) ((γ : PO n 1) • z)) =
      Real.cosh (Real.log L) + (L / 2) * ‖yc ξ ((γ : PO n 1) • z)‖ ^ 2 := by
    have h := levYcFormula hξS ((γ : PO n 1) • z) (0 : E n)
    rw [hI.2.1 ((γ : PO n 1) • z) 0] at h
    rw [hyc0, hlev0, mul_one, sub_zero] at h
    rw [hlevfix γ hγbd z] at h
    rw [← hL] at h
    simpa using h
  have hcosh : Real.cosh (hdist (0 : E n) z) ≤
      Real.cosh (hdist (0 : E n) ((γ : PO n 1) • z)) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (hI.1 _ _), abs_of_nonneg (hI.1 _ _)]
    exact hdirle
  rw [hfl1, hfl2] at hcosh
  have hsq : ‖y‖ ^ 2 ≤ ‖yc ξ ((γ : PO n 1) • z)‖ ^ 2 := by
    nlinarith [hcosh, hLpos, sq_nonneg ‖y‖, sq_nonneg ‖yc ξ ((γ : PO n 1) • z)‖]
  have hnorm : ‖y‖ ≤ ‖yc ξ ((γ : PO n 1) • z)‖ := by
    have h1 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg y), Real.sqrt_sq (norm_nonneg _)] at h1
  rw [hy] at hnorm
  linarith

/-- **No escaping Dirichlet sequence above the cusp heights.**  Given the two geometric inputs
(HL and the cocompactness of cusp stabilisers on horospheres) and the two chart computations
(the Busemann limit along an escaping sequence and the fact that a large level with bounded flat
coordinate points away from the cusp), a sequence of Dirichlet points satisfying the height
conditions cannot escape to infinity. -/
lemma no_escaping_dirichlet (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ) (ht : E n → ℝ)
    (heq : IsEquivHeight Γ (parFixed Γ) ht)
    (hHL : ∀ (ζ : E n), ζ ∈ Sph n → ∀ s : ℝ,
      (∀ γ : Γ, (γ : PO n 1) • (0 : E n) ∉ horoball ζ s) →
      ∃ q : Γ, IsParabolic (q : PO n 1) ∧ bd (q : PO n 1) ζ = ζ)
    (hcoc : ∀ (ξ : E n), ξ ∈ parFixed Γ →
      (∀ (γ : Γ) η, η ∈ parFixed Γ → bd (γ : PO n 1) η = η → bCocy (γ : PO n 1) η = 0) →
      ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, lev ξ u = 1 →
        ∃ γ : Γ, bd (γ : PO n 1) ξ = ξ ∧ (γ : PO n 1) • u ∈ K)
    (hbus : ∀ (z : ℕ → E n) (ζ : E n), ζ ∈ Sph n → Tendsto (fun k => ‖z k‖) atTop atTop →
      Tendsto (fun k => (‖z k‖)⁻¹ • z k) atTop (nhds ζ) → ∀ w : E n,
      Tendsto (fun k => hdist w (z k) - hdist (0 : E n) (z k)) atTop (nhds (busemann ζ w)))
    (hfar : ∀ (ξ : E n), ξ ∈ Sph n → ∀ C : ℝ, 1 < C → ∃ ε : ℝ, 0 < ε ∧ ∃ L₀ : ℝ,
      ∀ u : E n, L₀ ≤ lev ξ u → ‖yc ξ u‖ ≤ C →
      inner ℝ ((‖u‖)⁻¹ • u) ξ ≤ 1 - ε)
    (z : ℕ → E n) (hzD : ∀ k, z k ∈ Dirichlet Γ)
    (hzS : ∀ k ξ, ξ ∈ parFixed Γ → ht ξ ≤ busemann ξ (z k))
    (hesc : Tendsto (fun k => hdist (0 : E n) (z k)) atTop atTop) : False := by
  classical
  have hvan : ∀ (γ : Γ) η, η ∈ parFixed Γ → bd (γ : PO n 1) η = η → bCocy (γ : PO n 1) η = 0 :=
    fun γ η hη hfix => bCocy_eq_zero_of_isEquivHeight Γ ht heq γ η hη hfix
  -- points of the sequence are eventually non-zero; drop the first `K` of them
  have hone : ∀ᶠ k in atTop, (1 : ℝ) ≤ hdist (0 : E n) (z k) := hesc.eventually (Filter.eventually_ge_atTop 1)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → z k ≠ 0 := by
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hone
    refine ⟨K, fun k hk hzero => ?_⟩
    have h := hK k hk
    rw [hzero] at h
    have h0 : hdist (0 : E n) (0 : E n) = 0 := (hI.2.2.1 0 0).mpr rfl
    linarith
  set w : ℕ → E n := fun k => z (k + K) with hw
  have hwD : ∀ k, w k ∈ Dirichlet Γ := fun k => hzD _
  have hwS : ∀ k ξ, ξ ∈ parFixed Γ → ht ξ ≤ busemann ξ (w k) := fun k ξ hξ => hzS _ ξ hξ
  have hwesc : Tendsto (fun k => hdist (0 : E n) (w k)) atTop atTop :=
    hesc.comp (Filter.tendsto_add_atTop_nat K)
  have hwne : ∀ k, w k ≠ 0 := fun k => hK _ (Nat.le_add_left K k)
  -- the norm tends to infinity
  have hwnorm : Tendsto (fun k => ‖w k‖) atTop atTop :=
    tendsto_atTop_mono (fun k => hdist_zero_le_norm (w k)) hwesc
  -- directions lie on the sphere, so a subsequence converges to some `ζ`
  have hdirmem : ∀ k, (‖w k‖)⁻¹ • w k ∈ Sph n := by
    intro k
    rw [Sph, Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hwne k))]
  obtain ⟨ζ, hζS, φ, hφmono, hφtend⟩ :=
    (isCompact_sphere (0 : E n) 1).tendsto_subseq hdirmem
  -- restrict to the subsequence
  set u : ℕ → E n := fun k => w (φ k) with hu
  have huD : ∀ k, u k ∈ Dirichlet Γ := fun k => hwD _
  have huS : ∀ k ξ, ξ ∈ parFixed Γ → ht ξ ≤ busemann ξ (u k) := fun k ξ hξ => hwS _ ξ hξ
  have hunorm : Tendsto (fun k => ‖u k‖) atTop atTop :=
    hwnorm.comp hφmono.tendsto_atTop
  have huresc : Tendsto (fun k => hdist (0 : E n) (u k)) atTop atTop :=
    hwesc.comp hφmono.tendsto_atTop
  have hudir : Tendsto (fun k => (‖u k‖)⁻¹ • u k) atTop (nhds ζ) := hφtend
  -- the orbit of the base point avoids the horoball at `ζ` of level `0`
  have hbnonneg : ∀ γ : Γ, 0 ≤ busemann ζ ((γ : PO n 1) • (0 : E n)) := by
    intro γ
    have hb := hbus u ζ hζS hunorm hudir ((γ : PO n 1) • (0 : E n))
    refine ge_of_tendsto hb (Filter.Eventually.of_forall (fun k => ?_))
    have hdir := huD k γ⁻¹
    have hiso : hdist (0 : E n) (((γ⁻¹ : Γ) : PO n 1) • (u k)) =
        hdist ((γ : PO n 1) • (0 : E n)) (u k) := by
      calc hdist (0 : E n) (((γ⁻¹ : Γ) : PO n 1) • (u k))
          = hdist ((γ : PO n 1) • (0 : E n))
              ((γ : PO n 1) • (((γ⁻¹ : Γ) : PO n 1) • (u k))) :=
            (hI.2.2.2.2.2.2.1 (γ : PO n 1) 0 _).symm
        _ = hdist ((γ : PO n 1) • (0 : E n)) (u k) := by
            congr 1
            rw [← hA.2.2.2.2.1]
            have hmul : (γ : PO n 1) * (((γ⁻¹ : Γ)) : PO n 1) = 1 := by
              rw [show (((γ⁻¹ : Γ)) : PO n 1) = (γ : PO n 1)⁻¹ from rfl, mul_inv_cancel]
            rw [hmul, hA.2.2.2.1]
    linarith [hdir, hiso]
  have hfree : ∀ γ : Γ, (γ : PO n 1) • (0 : E n) ∉ horoball ζ 0 := by
    intro γ
    rw [horoball, Set.mem_ofPred_eq, not_lt]
    exact hbnonneg γ
  -- HL: `ζ` is a parabolic fixed point
  obtain ⟨q, hqpar, hqbd⟩ := hHL ζ hζS 0 hfree
  have hζpar : ζ ∈ parFixed Γ := ⟨hζS, q, hqpar, hqbd⟩
  -- the flat coordinate of the Dirichlet points at `ζ` is bounded
  obtain ⟨C, hC⟩ := dirichlet_flat_coord_bounded n hn hA hI Γ ζ hζpar hvan (hcoc ζ hζpar hvan)
  set C' : ℝ := max C 1 + 1 with hC'
  have hC'1 : 1 < C' := by rw [hC']; have := le_max_right C 1; linarith
  have hC'max : C ≤ C' := by rw [hC']; have := le_max_left C 1; linarith
  have hycle : ∀ k, ‖yc ζ (u k)‖ ≤ C' := fun k => le_trans (hC _ (huD k)) hC'max
  -- the height condition at `ξ = ζ` bounds the level from below
  have hlevge : ∀ k, Real.exp (ht ζ) ≤ lev ζ (u k) := by
    intro k
    have h := huS k ζ hζpar
    rw [lev_eq_exp hζS]
    exact Real.exp_le_exp.mpr h
  -- the level at `ζ` tends to infinity
  have htpt : Tendsto (fun k => tpart (u k)) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) hunorm
    rw [tpart]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖u k‖])
  have hLtend : Tendsto (fun k => lev ζ (u k)) atTop atTop := by
    set A : ℝ := 1 + C' ^ 2 with hAdef
    have hApos : 0 < A := by rw [hAdef]; nlinarith [sq_nonneg C']
    have hA1 : 1 < A := by rw [hAdef]; nlinarith [sq_nonneg C', hC'1]
    have hlim : Tendsto (fun k => tpart (u k) / (2 * A)) atTop atTop :=
      Filter.Tendsto.atTop_div_const (by linarith [hApos]) htpt
    refine Filter.tendsto_atTop_mono' atTop ?_ hlim
    refine (htpt.eventually (Filter.eventually_ge_atTop
      (2 * A / Real.exp (ht ζ)))).mono (fun k hk => ?_)
    have hLpos : 0 < lev ζ (u k) := lev_pos ζ hζS (u k)
    have hL0pos : 0 < Real.exp (ht ζ) := Real.exp_pos _
    have hge := hlevge k
    have hYle : ‖yc ζ (u k)‖ ^ 2 ≤ C' ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hycle k) 2
    have hid := tpart_eq_of_lev_yc hI hζS (u k)
    have hkey : 2 * lev ζ (u k) * tpart (u k) =
        1 + (lev ζ (u k)) ^ 2 * (1 + ‖yc ζ (u k)‖ ^ 2) := by
      rw [hid]; field_simp
    have hTnonneg : 0 ≤ tpart (u k) := le_of_lt (lt_of_lt_of_le zero_lt_one (one_le_tpart (u k)))
    -- it is enough to show `T / A ≤ L`, since `T / (2 * A) ≤ T / A`
    have hmain : tpart (u k) / A ≤ lev ζ (u k) := by
      by_contra hcon
      push_neg at hcon
      have hLT : A * lev ζ (u k) < tpart (u k) := by
        have := (lt_div_iff₀ hApos).mp hcon
        linarith [this]
      have h2 : 0 ≤ A * (lev ζ (u k)) ^ 2 - 2 * tpart (u k) * lev ζ (u k) + 1 := by
        rw [hAdef]
        nlinarith [hkey, hYle, sq_nonneg (lev ζ (u k))]
      have hk' : 2 * A ≤ tpart (u k) * Real.exp (ht ζ) := by
        have h := mul_le_mul_of_nonneg_right hk (le_of_lt hL0pos)
        rw [div_mul_cancel₀ _ (ne_of_gt hL0pos)] at h
        linarith [h]
      have hprod : tpart (u k) * Real.exp (ht ζ) ≤ tpart (u k) * lev ζ (u k) :=
        mul_le_mul_of_nonneg_left hge hTnonneg
      have hTL : tpart (u k) * lev ζ (u k) < 1 := by nlinarith [h2, hLT, hLpos]
      nlinarith [hk', hprod, hTL, hA1]
    have hfin : tpart (u k) / (2 * A) ≤ tpart (u k) / A := by
      rw [div_le_div_iff₀ (by linarith [hApos]) hApos]
      nlinarith [hTnonneg, hA1]
    linarith [hmain, hfin]
  have hsub_aux : Tendsto (fun k => (‖u k‖)⁻¹ • u k - ζ) atTop (nhds ((0 : E n))) := by
    have h2 : Tendsto (fun _ : ℕ => ζ) atTop (nhds ζ) := tendsto_const_nhds
    have h := hudir.sub h2
    simpa using h
  -- the direction's inner product with `ζ` tends to `1`
  obtain ⟨ε, hεpos, L₁, hL₁⟩ := hfar ζ hζS C' hC'1
  have hlevL : ∀ᶠ k in atTop, L₁ ≤ lev ζ (u k) := hLtend.eventually (Filter.eventually_ge_atTop L₁)
  have hinner : Tendsto (fun k => inner ℝ ((‖u k‖)⁻¹ • u k) ζ) atTop (nhds (inner ℝ ζ ζ)) := by
    have hdist0 : Tendsto (fun k => dist ((‖u k‖)⁻¹ • u k) ζ) atTop (nhds 0) := by
      have h2 : Tendsto (fun _ : ℕ => ζ) atTop (nhds ζ) := tendsto_const_nhds
      have h3 := hudir.dist h2
      simpa using h3
    have hbnd : Tendsto (fun k => dist ((‖u k‖)⁻¹ • u k) ζ * ‖ζ‖) atTop (nhds 0) := by
      have h2 : Tendsto (fun _ : ℕ => ‖ζ‖) atTop (nhds ‖ζ‖) := tendsto_const_nhds
      have h := hdist0.mul h2
      simpa using h
    have hdiff : Tendsto (fun k => inner ℝ ((‖u k‖)⁻¹ • u k) ζ - inner ℝ ζ ζ) atTop (nhds 0) := by
      refine squeeze_zero_norm (fun k => ?_) hbnd
      have h1 : inner ℝ ((‖u k‖)⁻¹ • u k) ζ - inner ℝ ζ ζ
          = inner ℝ ((‖u k‖)⁻¹ • u k - ζ) ζ := by rw [inner_sub_left]
      rw [h1, Real.norm_eq_abs, dist_eq_norm]
      exact abs_real_inner_le_norm _ _
    have h2 : Tendsto (fun _ : ℕ => inner ℝ ζ ζ) atTop (nhds (inner ℝ ζ ζ)) := tendsto_const_nhds
    have h := hdiff.add h2
    simpa using h
  have hζζ : inner ℝ ζ ζ = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have h1 : ‖ζ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hζS
    rw [h1]; norm_num
  rw [hζζ] at hinner
  have hle : (1 : ℝ) ≤ 1 - ε :=
    le_of_tendsto hinner (hlevL.mono (fun k hk => hL₁ (u k) hk (hycle k)))
  linarith

/-- **The horoball lemma (HL) from GAP-A.**  For a lattice `Γ ≤ PO(n,1)` with `n ≥ 3`, an
orbit-free horoball at `ζ ∈ Sph n` is a cuspidal horoball: `ζ` is fixed by a parabolic element of
`Γ`.

This is the lead's `Work.Mostow.HL_of_escapeShort`, fed with

* the Margulis/classification chapter (`margulisCusp_all`, `margulisLox_all`, `pairStab_all`,
  `classify_all` of `gapA_all_aux`, and `geomFiniteParabolicClass`),
* the vanishing of the Busemann cocycle on horospherical stabilisers (`stabHorosphere`),
* GAP-A (`GapAProp Γ`, i.e. far from `Γ•K` some infinite-order element is short), which supplies
  the near-identity infinite-order elements along an escaping ray,
* `orbitFree_stab_busemann`, which is the `hβζ` hypothesis of `HL_of_escapeShort`. -/
theorem hlInput_of_gapA (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ)
    (hesc : GapAProp Γ) :
    ∀ (ζ : E n), ζ ∈ Sph n → ∀ s : ℝ,
      (∀ γ : Γ, (γ : PO n 1) • (0 : E n) ∉ horoball ζ s) →
      ∃ q : Γ, IsParabolic (q : PO n 1) ∧ bd (q : PO n 1) ζ = ζ := by
  intro ζ hζ s hfree
  exact HL_of_escapeShort n hn hA hI (margulisCusp_all n (by omega))
    (margulisLox_all n (by omega)) (pairStab_all n (by omega)) (classify_all n (by omega))
    (fun g hg => ⟨(geomFiniteParabolicClass n (by omega) hA hI g hg).1,
      (geomFiniteParabolicClass n (by omega) hA hI g hg).2.1⟩)
    Γ hΓ.1
    (fun ξ hξS hpar γ hγ => by
      have h := stabHorosphere n (by omega) hA hI hBb Γ hΓ γ ξ ⟨hξS, hpar⟩ hγ
      rw [bCocy, hγ] at h
      exact h)
    hesc ζ hζ s hfree
    (fun γ hγ => orbitFree_stab_busemann n (by omega) hA hI Γ 0 ζ hζ s hfree γ hγ)

/-- **Assembly.**  With the two geometric inputs (HL and the cocompactness of cusp stabilisers
on horospheres) and the two chart computations, the conclusion of `horoballComplementBounded`
follows: if the set of Dirichlet points above all the cusp heights were unbounded, a sequence of
such points would escape to infinity, contradicting `no_escaping_dirichlet`. -/
lemma horoballComplementBounded_aux (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n)
    (hI : HypIsometryProp n) (hBb : ∀ m, BieberbachProp m) (Γ : Subgroup (PO n 1))
    (hΓ : HypLattice Γ) (ht : E n → ℝ) (heq : IsEquivHeight Γ (parFixed Γ) ht)
    (hHL : ∀ (ζ : E n), ζ ∈ Sph n → ∀ s : ℝ,
      (∀ γ : Γ, (γ : PO n 1) • (0 : E n) ∉ horoball ζ s) →
      ∃ q : Γ, IsParabolic (q : PO n 1) ∧ bd (q : PO n 1) ζ = ζ)
    (hcoc : ∀ (ξ : E n), ξ ∈ parFixed Γ →
      (∀ (γ : Γ) η, η ∈ parFixed Γ → bd (γ : PO n 1) η = η → bCocy (γ : PO n 1) η = 0) →
      ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, lev ξ u = 1 →
        ∃ γ : Γ, bd (γ : PO n 1) ξ = ξ ∧ (γ : PO n 1) • u ∈ K)
    (hbus : ∀ (z : ℕ → E n) (ζ : E n), ζ ∈ Sph n → Tendsto (fun k => ‖z k‖) atTop atTop →
      Tendsto (fun k => (‖z k‖)⁻¹ • z k) atTop (nhds ζ) → ∀ w : E n,
      Tendsto (fun k => hdist w (z k) - hdist (0 : E n) (z k)) atTop (nhds (busemann ζ w)))
    (hfar : ∀ (ξ : E n), ξ ∈ Sph n → ∀ C : ℝ, 1 < C → ∃ ε : ℝ, 0 < ε ∧ ∃ L₀ : ℝ,
      ∀ u : E n, L₀ ≤ lev ξ u → ‖yc ξ u‖ ≤ C →
      inner ℝ ((‖u‖)⁻¹ • u) ξ ≤ 1 - ε) :
    ∃ R : ℝ, ∀ z : E n, z ∈ Dirichlet Γ →
      (∀ ξ ∈ parFixed Γ, ht ξ ≤ busemann ξ z) → hdist (0 : E n) z ≤ R := by
  by_contra hcon
  push_neg at hcon
  have hcon' : ∀ k : ℕ, ∃ z : E n, z ∈ Dirichlet Γ ∧
      (∀ ξ ∈ parFixed Γ, ht ξ ≤ busemann ξ z) ∧ (k : ℝ) < hdist (0 : E n) z := by
    intro k
    obtain ⟨z, h1, h2, h3⟩ := hcon (k : ℝ)
    exact ⟨z, h1, h2, h3⟩
  choose z hz using hcon'
  refine (no_escaping_dirichlet n hn hA hI hBb Γ hΓ ht heq hHL hcoc hbus hfar z
    (fun k => (hz k).1) (fun k ξ hξ => (hz k).2.1 ξ hξ) ?_).elim
  exact tendsto_atTop_mono (fun k => le_of_lt (hz k).2.2) tendsto_natCast_atTop_atTop

end

end Work.Mostow
