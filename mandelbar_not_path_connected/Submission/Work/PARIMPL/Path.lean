/-
Copyright: subproject `Submission/Work/PARIMPL/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.Path` — PATH: `noPath`, the `hLB` of the endgame

Item §1.5 of `Submission/Work/NOTES_LEAD_mandelbar_residuals.md`: the assembly of the **path form**
of "no `Mb`-path approaches `c₀` through the implosion side",

  `noPath : ∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ Mb) → c₀ ∉ closure (range γ ∩ Nm)`,

which is the `hLB` consumed by the endgame
(`Work.TopJordan.mandelbar_not_isPathConnected_of_twoSidedPinch`).

## The argument (§1.5)

1. a sequence of *times* whose images lie on the path, in `Nm`, and converge to `c₀` (from the
   closure hypothesis); compactness of the unit interval gives a limit time `t*` with `γ t* = c₀`,
   and `c₀ ∉ Nm` because `a₂ c₀ = 0`;
2. by continuity, the path stays in the normal-form ball on the segment from `t_n` to `t*`; the
   **exit time** (the first zero of `a₂ ∘ γ` on that segment, taken from the `Nm` end) lies on the
   parabolic locus, and the half-open segment from the `Nm` end to it lies in `Nm`;
3. on that half-open segment the **transit coordinate** `transU ∘ γ` is continuous and its real
   part tends to `−∞` at the exit (the **phase blow-up**,
   `Work.PARIMPL.TransitData.blowup`), while its imaginary part stays `≤ r₀/4` (the **height**,
   `Work.PARIMPL.TransitData.height`); hence by the intermediate value theorem it meets the leak
   point modulo `ℤ`;
4. at the crossing time, `trans_escape` of `Work.PARIMPL.LeakData` puts the parameter *outside*
   the mandelbar — contradicting the hypothesis that the path lies in `Mb`.

## Main results

* `Work.PARIMPL.notMem_Mandelbar_of_notMem_K` — an escaping iterate of the critical point kills
  the parameter;
* `Work.PARIMPL.transit_crossing` — the crossing lemma (steps 2–4);
* **`Work.PARIMPL.noPath`** — the theorem.
-/
import Submission.Work.PARIMPL.Leak

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c₀ : ℂ}

/-- Monotonicity of balls in the radius, as a membership statement. -/
theorem mem_ball_mono {c x : ℂ} {r r' : ℝ} (h : x ∈ ball c r) (hr : r ≤ r') : x ∈ ball c r' := by
  rw [mem_ball] at h ⊢
  linarith

/-! ## The escape criterion -/

/-- If an iterate of the critical point `c = T_c 0` lies outside the filled Julia set of `T_c`,
then the critical orbit of `0` is unbounded and `c` is not a parameter of the mandelbar. -/
theorem notMem_Mandelbar_of_notMem_K {c : ℂ} {n : ℕ}
    (h : (Ft c)^[n] c ∉ Work.EL.K c) : c ∉ Mandelbar := by
  intro hc
  obtain ⟨M, hM⟩ := hc
  refine h ⟨M, fun k => ?_⟩
  have hshift : (Ft c)^[n] c = (Tantibar c)^[10 * n + 1] 0 := by
    calc (Ft c)^[n] c = ((Tantibar c)^[10])^[n] c := by rw [Ft_eq_tantibar]
      _ = (Tantibar c)^[10 * n] c := by rw [Function.iterate_mul]
      _ = (Tantibar c)^[10 * n] ((Tantibar c) 0) := by
            rw [show (Tantibar c) 0 = c from by
              simp [LeanEval.ComplexAnalysis.Tantibar]]
      _ = (Tantibar c)^[10 * n + 1] 0 := by
            have h' := Function.iterate_add_apply (f := (Tantibar c)) (10 * n) 1 0
            rw [Function.iterate_one] at h'
            exact h'.symm
  show ‖(Tantibar c)^[k] ((Ft c)^[n] c)‖ ≤ M
  rw [hshift, ← Function.iterate_add_apply]
  exact hM (k + (10 * n + 1))

/-! ## The crossing lemma (steps 2–4 of §1.5) -/

/-- **The transit crossing.**  Let `Γ` be a continuous path, `a < b`, `Γ a ∈ Nm` on the implosion
side, `Γ b ∉ Nm` (`b` is outside; in the application `Γ b` is on the parabolic locus), and
`Γ` maps the segment `[a,b]` into `ball c₀ ρ`.

Then `Γ` cannot be a path in the mandelbar.  Indeed the *exit time* `s` (the first zero of
`a₂ ∘ Γ` after `a`) satisfies: `Γ` maps `[a,s)` into `Nm`, `a₂ (Γ s) = 0`, and the transit
coordinate sweeps the leak on `[a,s)`, so some parameter of the segment escapes.

The hypotheses `hH` and `hLesc` are the conclusions of `Work.PARIMPL.TransitData.height` and
`Work.PARIMPL.LeakData.escape` at the radii `ρH`, `ρL`. -/
theorem transit_crossing {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa : ℂ → ℂ} {Ψ : ℂ → ℂ}
    {M : MatchData d P Pa φa Ψ} {T : TransitData d P Pa φa Ψ M}
    (L : LeakData d P Pa φa Ψ M T)
    {Γ : ℝ → ℂ} {a b ρ ρH ρL : ℝ} (hab : a < b) (hΓ : Continuous Γ)
    (hΓmem : ∀ u ∈ Set.Icc a b, Γ u ∈ Mandelbar)
    (haNm : Γ a ∈ P.Nm) (hbNm : Γ b ∉ P.Nm)
    (hballI : ∀ u ∈ Set.Icc a b, dist (Γ u) c₀ < ρ)
    (hρH : ρ ≤ ρH) (hρL : ρ ≤ ρL) (hρT : ρ ≤ T.ρ₁) (hρP : ρ ≤ P.ρ₀)
    (hH : ∀ c ∈ P.Nm ∩ ball c₀ ρH, |(transU P M.nIn c).im| ≤ L.r₀ / 4)
    (hLesc : ∀ c ∈ P.Nm ∩ ball c₀ ρL,
      distZ (transU P M.nIn c) ((L.liftRe : ℝ) : ℂ) < L.r₀ / 2 → c ∉ Mandelbar) : False := by
  -- `Γ` stays in the normal-form ball
  have hballab : ∀ u ∈ Set.Icc a b, Γ u ∈ ball c₀ P.ρ₀ :=
    fun u hu => mem_ball_mono (by rw [mem_ball]; exact hballI u hu) hρP
  have hbale : 0 ≤ P.a2 (Γ b) := by
    by_contra hcon
    exact hbNm ⟨hballab b ⟨hab.le, le_refl b⟩, lt_of_not_ge hcon⟩
  -- the exit time: the first zero of `a₂ ∘ Γ` after `a`
  have hcont2 : ContinuousOn (fun u : ℝ => P.a2 (Γ u)) (Set.Icc a b) :=
    P.cont_a2.comp hΓ.continuousOn (fun u hu => hballab u hu)
  have hzero : ∃ u ∈ Set.Icc a b, P.a2 (Γ u) = 0 := by
    have hmem : (0 : ℝ) ∈ Set.Icc (P.a2 (Γ a)) (P.a2 (Γ b)) :=
      ⟨le_of_lt haNm.2, hbale⟩
    exact intermediate_value_Icc hab.le hcont2 hmem
  set A : Set ℝ := {u : ℝ | u ∈ Set.Icc a b ∧ P.a2 (Γ u) = 0} with hA
  have hAclosed : IsClosed A := by
    rw [hA]
    have h := hcont2.preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_singleton (x := (0 : ℝ)))
    convert h using 2
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
  have hAne : A.Nonempty := hzero
  have hAbdd : BddBelow A := ⟨a, fun u hu => hu.1.1⟩
  set s : ℝ := sInf A with hs
  have hsA : s ∈ A := hAclosed.csInf_mem hAne hAbdd
  have has : a ≤ s := hsA.1.1
  have hsb : s ≤ b := hsA.1.2
  have hs0 : P.a2 (Γ s) = 0 := hsA.2
  have haslt : a < s := by
    rcases lt_or_eq_of_le has with h | h
    · exact h
    · exfalso
      rw [← h] at hs0
      linarith [haNm.2]
  -- the open segment is inside `Nm`
  have hsegNm : ∀ u ∈ Set.Ioo a s, Γ u ∈ P.Nm ∩ ball c₀ ρ := by
    intro u hu
    have huI : u ∈ Set.Icc a b := ⟨hu.1.le, le_trans hu.2.le hsb⟩
    refine ⟨⟨hballab u huI, ?_⟩, by rw [mem_ball]; exact hballI u huI⟩
    have hle : P.a2 (Γ u) ≤ 0 := by
      by_contra hcon
      have hpos : 0 < P.a2 (Γ u) := lt_of_not_ge hcon
      have hcont' : ContinuousOn (fun w : ℝ => P.a2 (Γ w)) (Set.Icc a u) :=
        hcont2.mono (by intro w hw; exact ⟨hw.1, le_trans hw.2 (le_trans hu.2.le hsb)⟩)
      have hmem : (0 : ℝ) ∈ Set.Icc (P.a2 (Γ a)) (P.a2 (Γ u)) := ⟨le_of_lt haNm.2, hpos.le⟩
      obtain ⟨v, hv, hv0⟩ := intermediate_value_Icc hu.1.le hcont' hmem
      have hvA : v ∈ A := ⟨⟨hv.1, le_trans hv.2 (le_trans hu.2.le hsb)⟩, hv0⟩
      have hsv : s ≤ v := csInf_le hAbdd hvA
      exact absurd hu.2 (not_lt.mpr (le_trans hsv hv.2))
    have hne : P.a2 (Γ u) ≠ 0 := by
      intro h0
      have huA : u ∈ A := ⟨huI, h0⟩
      have hsu : s ≤ u := csInf_le hAbdd huA
      exact absurd hsu (not_le.mpr hu.2)
    exact lt_of_le_of_ne hle hne
  -- the crossing
  obtain ⟨K, hK⟩ := exists_int_gt (L.liftRe - (transU P M.nIn (Γ a)).re)
  set tgt : ℝ := L.liftRe - (K : ℝ) with htgt
  have htgt_lt : tgt < (transU P M.nIn (Γ a)).re := by rw [htgt]; linarith
  have hB : ∀ᶠ c in 𝓝[P.Nm] (Γ s), (transU P M.nIn c).re ≤ tgt - 1 :=
    tendsto_atBot.mp (T.blowup (Γ s) hs0 (hballab s ⟨has, hsb⟩)) _
  rw [eventually_nhdsWithin_iff] at hB
  obtain ⟨ε, hεpos, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℂ,
      dist x (Γ s) < ε → (x ∈ P.Nm → (transU P M.nIn x).re ≤ tgt - 1) :=
    Metric.eventually_nhds_iff.mp hB
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ,
      dist x s < δ → dist (Γ x) (Γ s) < ε :=
    Metric.continuousAt_iff.mp hΓ.continuousAt ε hεpos
  set δ₁ : ℝ := min (δ / 2) ((s - a) / 2) with hδ₁
  have hδ₁pos : 0 < δ₁ := lt_min (by linarith) (by linarith)
  set u₁ : ℝ := s - δ₁ with hu₁
  have hu₁lt : u₁ < s := by rw [hu₁]; linarith
  have hau₁ : a < u₁ := by
    rw [hu₁]
    have := min_le_right (δ / 2) ((s - a) / 2)
    linarith
  have hu₁dist : dist u₁ s < δ := by
    rw [Real.dist_eq, hu₁, abs_of_neg (by linarith)]
    have := min_le_left (δ / 2) ((s - a) / 2)
    linarith
  have hu₁seg : Γ u₁ ∈ P.Nm ∩ ball c₀ ρ := hsegNm u₁ ⟨hau₁, hu₁lt⟩
  have hu₁le : (transU P M.nIn (Γ u₁)).re ≤ tgt - 1 := by
    have h1 : dist (Γ u₁) (Γ s) < ε := hδ u₁ hu₁dist
    have h2 : Γ u₁ ∈ P.Nm := hu₁seg.1
    exact hε (Γ u₁) h1 h2
  have hu₁lt' : (transU P M.nIn (Γ u₁)).re < tgt := by linarith
  -- continuity of the transit coordinate on `[a, u₁]`
  have hmap : MapsTo Γ (Set.uIcc a u₁) (P.Nm ∩ ball c₀ T.ρ₁) := by
    intro u hu
    rw [Set.uIcc_of_le hau₁.le] at hu
    have huI : u ∈ Set.Icc a b := ⟨hu.1, le_trans hu.2 (le_trans hu₁lt.le hsb)⟩
    have hb : Γ u ∈ ball c₀ T.ρ₁ := by
      rw [mem_ball]
      exact lt_of_lt_of_le (hballI u huI) hρT
    rcases lt_or_eq_of_le hu.1 with hltu | heq
    · exact ⟨(hsegNm u ⟨hltu, lt_of_le_of_lt hu.2 hu₁lt⟩).1, hb⟩
    · subst heq; exact ⟨haNm, hb⟩
  have hcont1 : ContinuousOn (fun u : ℝ => transU P M.nIn (Γ u)) (Set.uIcc a u₁) := by
    have h := T.cont.comp hΓ.continuousOn hmap
    simpa only [Function.comp_def] using h
  have hcont' : ContinuousOn (fun u : ℝ => (transU P M.nIn (Γ u)).re) (Set.uIcc a u₁) := by
    simpa only [Function.comp_def] using Complex.continuous_re.comp_continuousOn hcont1
  -- the intermediate value theorem
  have hmem : tgt ∈ Set.uIcc ((fun u : ℝ => (transU P M.nIn (Γ u)).re) a)
      ((fun u : ℝ => (transU P M.nIn (Γ u)).re) u₁) :=
    Set.mem_uIcc.mpr (Or.inr ⟨hu₁lt'.le, htgt_lt.le⟩)
  obtain ⟨u, hu, hfu⟩ := intermediate_value_uIcc hcont' hmem
  rw [Set.uIcc_of_le hau₁.le] at hu
  -- the crossing parameter escapes
  have huNm : Γ u ∈ P.Nm ∩ ball c₀ ρ := by
    rcases lt_or_eq_of_le hu.1 with hltu | heq
    · exact hsegNm u ⟨hltu, lt_of_le_of_lt hu.2 hu₁lt⟩
    · subst heq; exact ⟨haNm, by rw [mem_ball]; exact hballI a ⟨le_refl a, hab.le⟩⟩
  have huH : |(transU P M.nIn (Γ u)).im| ≤ L.r₀ / 4 :=
    hH (Γ u) ⟨huNm.1, mem_ball_mono (x := Γ u) huNm.2 hρH⟩
  have hdist : ‖transU P M.nIn (Γ u) - (((L.liftRe - (K : ℝ)) : ℝ) : ℂ)‖ < L.r₀ / 2 := by
    have hsub : transU P M.nIn (Γ u) - (((L.liftRe - (K : ℝ)) : ℝ) : ℂ)
        = (((transU P M.nIn (Γ u)).im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [Complex.sub_re, hfu, htgt]
      · simp [Complex.sub_im]
    rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    linarith [L.hr₀]
  have hZ : distZ (transU P M.nIn (Γ u)) ((L.liftRe : ℝ) : ℂ) < L.r₀ / 2 := by
    refine lt_of_le_of_lt (distZ_le _ _ K) ?_
    have hsum : (transU P M.nIn (Γ u) + (K : ℂ)) - ((L.liftRe : ℝ) : ℂ)
        = transU P M.nIn (Γ u) - (((L.liftRe - (K : ℝ)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [dist_eq_norm, hsum]
    exact hdist
  exact (hLesc (Γ u) ⟨huNm.1, mem_ball_mono (x := Γ u) huNm.2 hρL⟩ hZ)
    (hΓmem u ⟨hu.1, le_trans hu.2 (le_trans hu₁lt.le hsb)⟩)

/-! ## `noPath` (step 1 and the assembly of §1.5) -/

/-- **PATH / `hLB`**: no path in the mandelbar approaches the root parameter `c₀` through the
implosion side `Nm`.  This is the `hLB` consumed by
`Work.TopJordan.mandelbar_not_isPathConnected_of_twoSidedPinch`.

The proof is the §1.5 argument: the path meets `Nm` at times whose images converge to `c₀`; a
limit time `t*` satisfies `γ t* = c₀` (and `c₀ ∉ Nm` because `a₂ c₀ = 0`); the segment from the
`Nm` end to the exit time lies in `Nm` and carries the transit crossing
(`Work.PARIMPL.transit_crossing`), one of whose parameters escapes the mandelbar.

The two hypotheses `hPa`, `hφa`, `hentry₀`, `hcrit` feed the *derived* height bound
`Work.PARIMPL.TransitData.height` (namely: `Pa` is open, `φa` is differentiable on it, the entry
point of the critical orbit at `c₀` lies in `Pa`, and the critical Écalle height vanishes). -/
theorem noPath {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    {Pa : Set ℂ} {φa : ℂ → ℂ} {Ψ : ℂ → ℂ}
    (M : MatchData d P Pa φa Ψ) (T : TransitData d P Pa φa Ψ M)
    (L : LeakData d P Pa φa Ψ M T)
    (hPa : IsOpen Pa) (hφa : DifferentiableOn ℂ φa Pa)
    (hentry₀ : entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (entryPt P M.nIn c₀)).im = 0) :
    ∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ Mandelbar) →
      c₀ ∉ closure (Set.range γ ∩ P.Nm) := by
  intro γ hγ hmem
  -- the three radii
  obtain ⟨ρH, hρHpos, hρHle, hH⟩ :=
    T.height hPa hφa hentry₀ hcrit (L.r₀ / 4) (by linarith [L.hr₀])
  obtain ⟨ρL, hρLpos, hLesc⟩ := L.escape_one
  set ρ : ℝ := min (min ρH ρL) (min T.ρ₁ P.ρ₀) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact lt_min (lt_min hρHpos hρLpos) (lt_min T.hρ₁ P.hρ₀)
  have hρH' : ρ ≤ ρH := by
    rw [hρdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hρL' : ρ ≤ ρL := by
    rw [hρdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hρT' : ρ ≤ T.ρ₁ := by
    rw [hρdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hρP' : ρ ≤ P.ρ₀ := by
    rw [hρdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  -- the path, reparametrised on `ℝ`
  set Γ : ℝ → ℂ := fun t => γ (Set.projIcc (0 : ℝ) 1 (by norm_num) t) with hΓdef
  have hΓcont : Continuous Γ := γ.continuous.comp continuous_projIcc
  have hΓmem01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Γ t ∈ Mandelbar := by
    intro t ht
    change γ (Set.projIcc (0 : ℝ) 1 (by norm_num) t) ∈ Mandelbar
    rw [Set.projIcc_of_mem (by norm_num) ht]
    exact hγ ⟨t, ht⟩
  -- a sequence of parameters in `Nm` whose images converge to `c₀`
  have hseq : ∀ n : ℕ, ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ Γ t ∈ P.Nm ∧
      dist (Γ t) c₀ < 1 / (n + 1) := by
    intro n
    have hε : 0 < (1 : ℝ) / (n + 1) := by positivity
    obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp hmem ((1 : ℝ) / (n + 1)) hε
    obtain ⟨t, ht⟩ := Set.mem_range.mp hy.1
    refine ⟨(t : ℝ), t.2, ?_, ?_⟩
    · change γ (Set.projIcc (0 : ℝ) 1 (by norm_num) (t : ℝ)) ∈ P.Nm
      rw [Set.projIcc_of_mem (by norm_num) t.2, ht]
      exact hy.2
    · change dist (γ (Set.projIcc (0 : ℝ) 1 (by norm_num) (t : ℝ))) c₀ < 1 / (n + 1)
      rw [Set.projIcc_of_mem (by norm_num) t.2, ht, dist_comm]
      exact hd
  choose t htI htNm htD using hseq
  obtain ⟨tstar, htstarI, φ, hφmono, hφtend⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).tendsto_subseq htI
  -- the limit time
  have hΓt : Tendsto (fun n => Γ (t n)) atTop (𝓝 c₀) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
    have h2 : (1 : ℝ) / (N + 1) < ε := by
      have h3 : (1 : ℝ) / ε < (N : ℝ) + 1 := by
        have hN' : (1 : ℝ) / ε < (N : ℝ) := hN
        linarith
      have h4 : ε * (1 / ε) < ε * ((N : ℝ) + 1) := mul_lt_mul_of_pos_left h3 hε
      have h5 : ε * (1 / ε) = 1 := by field_simp
      rw [h5] at h4
      rw [div_lt_iff₀ (by positivity)]
      linarith
    exact lt_of_lt_of_le (htD n) (le_of_lt (lt_of_le_of_lt h1 h2))
  have hΓstar : Γ tstar = c₀ := by
    have h1 : Tendsto (fun n => Γ (t (φ n))) atTop (𝓝 (Γ tstar)) :=
      (hΓcont.tendsto tstar).comp hφtend
    have h2 : Tendsto (fun n => Γ (t (φ n))) atTop (𝓝 c₀) :=
      hΓt.comp hφmono.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  -- the segment from a nearby parameter to the limit time stays in the `ρ`-ball
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ,
      dist x tstar < δ → dist (Γ x) (Γ tstar) < ρ / 2 :=
    Metric.continuousAt_iff.mp hΓcont.continuousAt (ρ / 2) (by linarith)
  have hev : ∀ᶠ n in atTop, dist (t (φ n)) tstar < δ / 2 :=
    (Metric.tendsto_nhds.mp hφtend) (δ / 2) (by linarith)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hev
  set τ : ℝ := t (φ n₀) with hτdef
  have hτI : τ ∈ Set.Icc (0 : ℝ) 1 := htI (φ n₀)
  have hτclose : dist τ tstar < δ / 2 := hn₀ n₀ le_rfl
  have hsegball : ∀ u ∈ Set.uIcc τ tstar, dist (Γ u) c₀ < ρ := by
    intro u hu
    have h1 : dist u tstar ≤ dist τ tstar := by
      rcases Set.mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith),
          abs_of_nonpos (by linarith)]
        linarith
      · rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (by linarith),
          abs_of_nonneg (by linarith)]
        linarith
    have h2 : dist (Γ u) (Γ tstar) < ρ / 2 := hδ u (lt_of_le_of_lt h1 (by linarith))
    rw [hΓstar] at h2
    linarith
  -- the two endpoints
  have hτNm : Γ τ ∈ P.Nm := htNm (φ n₀)
  have htsNm : Γ tstar ∉ P.Nm := by
    intro hcon
    rw [hΓstar, ParNormal.mem_Nm, P.a2₀] at hcon
    exact absurd hcon.2 (lt_irrefl 0)
  have hne : τ ≠ tstar := fun h => htsNm (h ▸ hτNm)
  -- the crossing
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine transit_crossing (Γ := Γ) (a := τ) (b := tstar) (ρ := ρ) (ρH := ρH) (ρL := ρL)
      L hlt hΓcont ?_ hτNm htsNm ?_ hρH' hρL' hρT' hρP' hH hLesc
    · intro u hu
      exact hΓmem01 u ⟨le_trans hτI.1 hu.1, le_trans hu.2 htstarI.2⟩
    · intro u hu
      exact hsegball u (Set.mem_uIcc.mpr (Or.inl hu))
  · -- `tstar < τ`: reverse the parameterisation
    set Γ' : ℝ → ℂ := fun u => Γ (τ + tstar - u) with hΓ'def
    have hΓ'cont : Continuous Γ' :=
      hΓcont.comp ((continuous_const.add continuous_const).sub continuous_id)
    have hΓ'mem : ∀ u ∈ Set.Icc tstar τ, Γ' u ∈ Mandelbar := by
      intro u hu
      have h1 : τ + tstar - u ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [hu.2, htstarI.1], by linarith [hu.1, hτI.2]⟩
      simpa only [hΓ'def] using hΓmem01 _ h1
    have hΓ'ball : ∀ u ∈ Set.Icc tstar τ, dist (Γ' u) c₀ < ρ := by
      intro u hu
      have h1 : τ + tstar - u ∈ Set.uIcc τ tstar :=
        Set.mem_uIcc.mpr (Or.inr ⟨by linarith [hu.2], by linarith [hu.1]⟩)
      simpa only [hΓ'def] using hsegball _ h1
    refine transit_crossing (Γ := Γ') (a := tstar) (b := τ) (ρ := ρ) (ρH := ρH) (ρL := ρL)
      L hgt hΓ'cont hΓ'mem ?_ ?_ hΓ'ball hρH' hρL' hρT' hρP' hH hLesc
    · show Γ (τ + tstar - tstar) ∈ P.Nm
      rw [show τ + tstar - tstar = τ by ring]
      exact hτNm
    · show Γ (τ + tstar - τ) ∉ P.Nm
      rw [show τ + tstar - τ = tstar by ring]
      exact htsNm

end Work.PARIMPL
