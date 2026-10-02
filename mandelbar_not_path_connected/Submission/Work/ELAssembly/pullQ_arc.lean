import Mathlib
import Submission.Work.ELAssembly.PullInputs
import Submission.Work.ELPull.nearArcsCover_Q

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open Classical Set

-- Shell: `namespace Work.ELAssembly` (area `Submission/Work/ELAssembly/`), `open LeanEval.ComplexAnalysis (Tantibar)`.

/-! ## Two elementary angular facts -/

/-- `arcLen α₁ α₂ = α₂ - α₁`. -/
private theorem arcLen_alpha : Work.EL.arcLen Work.ELNest.alpha1 Work.ELNest.alpha2
    = Work.ELNest.alpha2 - Work.ELNest.alpha1 := by
  rw [Work.EL.arcLen, Int.fract_eq_self.mpr
    ⟨by norm_num [Work.ELNest.alpha1, Work.ELNest.alpha2],
     by norm_num [Work.ELNest.alpha1, Work.ELNest.alpha2]⟩]

/-- `arcLen βₙ' (βₙ + 1) = βₙ + 1 - βₙ'`. -/
private theorem arcLen_bAng (n : ℕ) :
    Work.EL.arcLen (Work.ELNest.bAng' n) (Work.ELNest.bAng n + 1)
      = Work.ELNest.bAng n + 1 - Work.ELNest.bAng' n := by
  have hα : Work.ELNest.alpha1 < Work.ELNest.alpha2 := by
    norm_num [Work.ELNest.alpha1, Work.ELNest.alpha2]
  have hlt : Work.ELNest.bAng n < Work.ELNest.bAng' n :=
    lt_of_le_of_lt (Work.ELNest.bAng_le_alpha1 n)
      (lt_of_lt_of_le hα (Work.ELNest.alpha2_le_bAng' n))
  have hpos : 0 ≤ Work.ELNest.bAng n + 1 - Work.ELNest.bAng' n := by
    have h1 := Work.ELNest.bAng'_lt_one n
    have h2 := Work.ELNest.bAng_pos n
    linarith
  rw [Work.EL.arcLen, Int.fract_eq_self.mpr ⟨hpos, by linarith⟩]

/-- A closed-arc membership is refuted by a fractional part strictly larger than the length. -/
private theorem not_inClosedArc_of_lt {y a b : ℝ} (h : Work.EL.arcLen a b < Int.fract (y - a)) :
    ¬ Work.EL.InClosedArc y a b := fun hc => absurd hc.2 (not_le.mpr h)

/-! ## The main theorem -/

/-- **The angle map `T^[10]` carries the near arcs of the level-`(n+1)` `z₁`-polygon into the
near arcs of the level-`n` polygon.**  The `α`-pair is `(α₁, α₂) = (371/1023, 404/1023)` and the
level-`n` pair is `(βₙ', βₙ + 1) = (α₂ + (β₀'-α₂)/1024ⁿ, α₁ - (α₁-β₀)/1024ⁿ + 1)`.  The
hypotheses say `x` is outside the two closed *far* arcs of the polygon `[P₀, Qp(n+1)]`, i.e. in
its two near arcs; the conclusion says `T^[10] x` is in the two near arcs of `[P₀, Qp n]`.
`Work.EL.T^[10]` is `Work.ELPull.angMul 5` (`θ ↦ fract (1024 θ)`); the content is the rational
certificate `Work.ELPull.InArc_angMul5_Q0`/`Q1` scaled by `1024^n`. -/
theorem pullQ_arc (n : ℕ) (x : ℝ)
    (hx : ¬ Work.EL.InClosedArc x (Work.ELNest.bAng' (n + 1)) (Work.ELNest.bAng (n + 1) + 1))
    (hx' : ¬ Work.EL.InClosedArc x Work.EL.alpha1 Work.EL.alpha2) :
    ¬ Work.EL.InClosedArc ((Work.EL.T)^[10] x) (Work.ELNest.bAng' n) (Work.ELNest.bAng n + 1) ∧
    ¬ Work.EL.InClosedArc ((Work.EL.T)^[10] x) Work.EL.alpha1 Work.EL.alpha2 := by
  have hx'' : ¬ Work.EL.InClosedArc x Work.ELNest.alpha1 Work.ELNest.alpha2 := hx'
  change ¬ Work.EL.InClosedArc ((Work.EL.T)^[10] x) (Work.ELNest.bAng' n)
        (Work.ELNest.bAng n + 1) ∧
      ¬ Work.EL.InClosedArc ((Work.EL.T)^[10] x) Work.ELNest.alpha1 Work.ELNest.alpha2
  -- ## elementary numeric data
  have hD0 : Work.ELNest.beta0' - Work.ELNest.alpha2 = (417 : ℝ) / 1047552 := by
    norm_num [Work.ELNest.beta0', Work.ELNest.alpha2]
  have hE0 : Work.ELNest.alpha1 - Work.ELNest.beta0 = (45 : ℝ) / 1047552 := by
    norm_num [Work.ELNest.alpha1, Work.ELNest.beta0]
  have hαd : Work.ELNest.alpha2 - Work.ELNest.alpha1 = (33 : ℝ) / 1023 := by
    norm_num [Work.ELNest.alpha1, Work.ELNest.alpha2]
  have hα12 : Work.ELNest.alpha1 < Work.ELNest.alpha2 := by
    norm_num [Work.ELNest.alpha1, Work.ELNest.alpha2]
  have hα1lt : Work.ELNest.alpha1 < 1 := by norm_num [Work.ELNest.alpha1]
  have hα2pos : 0 < Work.ELNest.alpha2 := by norm_num [Work.ELNest.alpha2]
  have hα2lt : Work.ELNest.alpha2 + (417 : ℝ) / 1047552 < 1 := by norm_num [Work.ELNest.alpha2]
  have hnum2 : (33 : ℝ) / 1023 + (417 : ℝ) / 1047552 < 1 := by norm_num
  have h1024a2 : (1024 : ℝ) * Work.ELNest.alpha2 = Work.ELNest.alpha2 + 404 := by
    norm_num [Work.ELNest.alpha2]
  have h1024α : (1024 : ℝ) * (Work.ELNest.alpha2 - Work.ELNest.alpha1)
      = 33 + (33 : ℝ) / 1023 := by norm_num [Work.ELNest.alpha1, Work.ELNest.alpha2]
  -- the two gaps of the nest and their level-`n` sizes
  set Dn : ℝ := (Work.ELNest.beta0' - Work.ELNest.alpha2) / (1024 : ℝ) ^ n with hDn
  set En : ℝ := (Work.ELNest.alpha1 - Work.ELNest.beta0) / (1024 : ℝ) ^ n with hEn
  have hpow1 : (1 : ℝ) ≤ (1024 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hDn_pos : 0 < Dn := by
    rw [hDn]; exact div_pos (by rw [hD0]; norm_num) (by positivity)
  have hEn_pos : 0 < En := by
    rw [hEn]; exact div_pos (by rw [hE0]; norm_num) (by positivity)
  have hDn_le : Dn ≤ (417 : ℝ) / 1047552 := by
    rw [hDn, hD0, div_le_iff₀ (by positivity : (0 : ℝ) < (1024 : ℝ) ^ n)]
    nlinarith [hpow1]
  have hEn_le : En ≤ (45 : ℝ) / 1047552 := by
    rw [hEn, hE0, div_le_iff₀ (by positivity : (0 : ℝ) < (1024 : ℝ) ^ n)]
    nlinarith [hpow1]
  have hDn_lt1 : Dn < 1 := by linarith [hDn_le]
  have hEn_lt1 : En < 1 := by linarith [hEn_le]
  have hEn_lt_alpha1 : En < Work.ELNest.alpha1 := by
    rw [Work.ELNest.alpha1]; linarith [hEn_le]
  -- ## the nest angles of the two levels
  have hbAng' : Work.ELNest.bAng' n = Work.ELNest.alpha2 + Dn := by
    rw [Work.ELNest.bAng', hDn]
  have hbAng : Work.ELNest.bAng n = Work.ELNest.alpha1 - En := by
    rw [Work.ELNest.bAng, hEn]
  have hDn_div : Dn / 1024
      = (Work.ELNest.beta0' - Work.ELNest.alpha2) / (1024 : ℝ) ^ (n + 1) := by
    rw [hDn, pow_succ, div_div]
  have hEn_div : En / 1024
      = (Work.ELNest.alpha1 - Work.ELNest.beta0) / (1024 : ℝ) ^ (n + 1) := by
    rw [hEn, pow_succ, div_div]
  have hbAng'_succ : Work.ELNest.bAng' (n + 1) = Work.ELNest.alpha2 + Dn / 1024 := by
    rw [Work.ELNest.bAng', hDn_div]
  have hbAng_succ : Work.ELNest.bAng (n + 1) = Work.ELNest.alpha1 - En / 1024 := by
    rw [Work.ELNest.bAng, hEn_div]
  -- ## `x` lies in the α-near arc: `x = α₂ + k + u`
  have hx'mem : x ∈ {θ : ℝ | ¬ Work.EL.InClosedArc θ Work.ELNest.alpha1 Work.ELNest.alpha2} :=
    hx''
  rw [Work.ELTop.notInClosedArc_eq_iUnion] at hx'mem
  simp only [Set.mem_iUnion, Set.mem_Ioo] at hx'mem
  obtain ⟨k, hk1, hk2⟩ := hx'mem
  rw [arcLen_alpha] at hk1
  set u : ℝ := x - Work.ELNest.alpha2 - (k : ℝ) with hu
  have hu_pos : 0 < u := by rw [hu]; linarith
  have hu_lt : u < 1 - (Work.ELNest.alpha2 - Work.ELNest.alpha1) := by rw [hu]; linarith
  have hx_split : x = Work.ELNest.alpha2 + (k : ℝ) + u := by rw [hu]; ring
  -- ## `x` lies in the level-`(n+1)` near arc
  have hxmem : x ∈ {θ : ℝ | ¬ Work.EL.InClosedArc θ (Work.ELNest.bAng' (n + 1))
      (Work.ELNest.bAng (n + 1) + 1)} := hx
  rw [Work.ELTop.notInClosedArc_eq_iUnion] at hxmem
  simp only [Set.mem_iUnion, Set.mem_Ioo] at hxmem
  obtain ⟨m, hm1, hm2⟩ := hxmem
  rw [arcLen_bAng] at hm1
  have hm1' : Work.ELNest.bAng (n + 1) + 1 + (m : ℝ) < x := by linarith
  have hm2' : x < Work.ELNest.bAng' (n + 1) + (m : ℝ) + 1 := by linarith
  -- ## the difference `j = m - k + 1` is `0` or `1`
  set j : ℤ := m - k + 1 with hj
  have hu_jd : u < (j : ℝ) + Dn / 1024 := by
    have h := hm2'
    rw [hbAng'_succ] at h
    rw [hx_split] at h
    rw [hj]; push_cast; linarith
  have hu_j33 : (j : ℝ) - (Work.ELNest.alpha2 - Work.ELNest.alpha1) - En / 1024 < u := by
    have h := hm1'
    rw [hbAng_succ] at h
    rw [hx_split] at h
    rw [hj]; push_cast; linarith
  have hj_ge : (0 : ℤ) ≤ j := by
    have h : (-1 : ℤ) < j := by
      have h' : (-1 : ℝ) < (j : ℝ) := by
        have hd : Dn / 1024 < 1 := by linarith [hDn_lt1]
        linarith [hu_pos, hu_jd, hd]
      exact_mod_cast h'
    omega
  have hj_le : j ≤ 1 := by
    have h : j < 2 := by
      have h' : (j : ℝ) < 2 := by
        have he : En / 1024 < 1 := by linarith [hEn_lt1]
        linarith [hu_lt, hu_j33, he]
      exact_mod_cast h'
    omega
  have hj01 : j = 0 ∨ j = 1 := by omega
  -- ## the image angle
  set y : ℝ := (Work.EL.T)^[10] x with hy
  have hy_fract : y = Int.fract (Work.ELNest.alpha2 + 1024 * u) := by
    rw [hy, Work.ELNest.T_iterate_ten]
    have h : (1024 : ℝ) * x
        = (Work.ELNest.alpha2 + 1024 * u) + ((404 + 1024 * k : ℤ) : ℝ) := by
      rw [hx_split]; push_cast; linarith [h1024a2]
    rw [h, Int.fract_add_intCast]
  rcases hj01 with hj0 | hj1
  · -- ## Case I: `u < Dn/1024`, so `y = α₂ + 1024u` with `1024u ∈ (0, Dn)`
    have hu_lt_dn : u < Dn / 1024 := by
      have := hu_jd; rw [hj0] at this; push_cast at this; linarith
    have hv_pos : 0 < 1024 * u := by linarith [hu_pos]
    have hv_lt : 1024 * u < Dn := by linarith [hu_lt_dn]
    have hyI : y = Work.ELNest.alpha2 + 1024 * u := by
      rw [hy_fract]
      refine Int.fract_eq_self.mpr ⟨by linarith [hα2pos, hv_pos], ?_⟩
      linarith [hv_lt, hDn_le, hα2lt]
    refine ⟨?_, ?_⟩
    · -- the level-`n` far arc of the nest is avoided
      apply not_inClosedArc_of_lt
      have hfr : Int.fract (y - Work.ELNest.bAng' n) = 1 + 1024 * u - Dn := by
        have h1 : y - Work.ELNest.bAng' n = (1 + 1024 * u - Dn) + ((-1 : ℤ) : ℝ) := by
          rw [hyI, hbAng']; ring
        rw [h1, Int.fract_add_intCast,
          Int.fract_eq_self.mpr ⟨by linarith [hv_pos, hDn_lt1], by linarith [hv_lt]⟩]
      rw [hfr, arcLen_bAng, hbAng, hbAng']
      linarith [hv_pos, hEn_pos, hαd]
    · -- the α far arc is avoided
      apply not_inClosedArc_of_lt
      have hfr : Int.fract (y - Work.ELNest.alpha1) = (33 : ℝ) / 1023 + 1024 * u := by
        have h1 : y - Work.ELNest.alpha1 = (33 : ℝ) / 1023 + 1024 * u := by
          rw [hyI]; linarith [hαd]
        rw [h1, Int.fract_eq_self.mpr ⟨by linarith [hv_pos], by linarith [hv_lt, hDn_le, hnum2]⟩]
      rw [hfr, arcLen_alpha]; linarith [hv_pos, hαd]
  · -- ## Case II: `1 - 33/1023 - En/1024 < u < 1 - 33/1023`
    have hu_gt : 1 - (Work.ELNest.alpha2 - Work.ELNest.alpha1) - En / 1024 < u := by
      have := hu_j33; rw [hj1] at this; push_cast at this; linarith
    have hv_gt : 991 - (33 : ℝ) / 1023 - En < 1024 * u := by
      linarith [hu_gt, h1024α]
    have hv_lt : 1024 * u < 991 - (33 : ℝ) / 1023 := by
      linarith [hu_lt, h1024α]
    have hyII : y = Work.ELNest.alpha2 + 1024 * u - 991 := by
      rw [hy_fract]
      refine Int.fract_eq_iff.mpr ⟨?_, ?_, ⟨991, ?_⟩⟩
      · have h : 0 < Work.ELNest.alpha1 - En := by linarith [hEn_lt_alpha1]
        have h2 : Work.ELNest.alpha1 = Work.ELNest.alpha2 - (33 : ℝ) / 1023 := by linarith [hαd]
        linarith [hv_gt, h, h2]
      · have h2 : Work.ELNest.alpha1 = Work.ELNest.alpha2 - (33 : ℝ) / 1023 := by linarith [hαd]
        linarith [hv_lt, h2, hα1lt]
      · push_cast; ring
    refine ⟨?_, ?_⟩
    · -- the level-`n` far arc of the nest is avoided
      apply not_inClosedArc_of_lt
      have hfr : Int.fract (y - Work.ELNest.bAng' n) = 1024 * u - 990 - Dn := by
        have h1 : y - Work.ELNest.bAng' n = (1024 * u - 990 - Dn) + ((-1 : ℤ) : ℝ) := by
          rw [hyII, hbAng']; ring
        rw [h1, Int.fract_add_intCast]
        refine Int.fract_eq_self.mpr ⟨?_, ?_⟩
        · linarith [hv_gt, hEn_le, hDn_le]
        · linarith [hv_lt, hDn_pos]
      rw [hfr, arcLen_bAng, hbAng, hbAng']
      linarith [hv_gt, hαd]
    · -- the α far arc is avoided
      apply not_inClosedArc_of_lt
      have hfr : Int.fract (y - Work.ELNest.alpha1) = 1 + ((33 : ℝ) / 1023 + 1024 * u - 991) := by
        have h1 : y - Work.ELNest.alpha1
            = (1 + ((33 : ℝ) / 1023 + 1024 * u - 991)) + ((-1 : ℤ) : ℝ) := by
          rw [hyII]; push_cast; linarith [hαd]
        rw [h1, Int.fract_add_intCast]
        refine Int.fract_eq_self.mpr ⟨?_, ?_⟩
        · linarith [hv_gt, hEn_lt1]
        · linarith [hv_lt]
      rw [hfr, arcLen_alpha]
      have h990 : (990 : ℝ) < 1024 * u := by
        have h2 : (990 : ℝ) < 991 - (33 : ℝ) / 1023 - En := by
          have h3 : (0 : ℝ) < 1 - (33 : ℝ) / 1023 - (45 : ℝ) / 1047552 := by norm_num
          linarith [hEn_le, h3]
        linarith [hv_gt, h2]
      linarith [hαd, h990]

end Work.ELAssembly
