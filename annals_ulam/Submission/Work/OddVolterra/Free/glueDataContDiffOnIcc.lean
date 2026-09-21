import Mathlib
import Submission.Work.OddCurve.LowSlope.GlueDefs
import Submission.Work.OddCurve.LowSlope.Datum
import Submission.Work.OddCurve.LowSlope.contDiffOn_radonPhi_Icc

/-!
# Smoothness of the glued low-slope data on `[0,1]`

`GlueF n ρ` and `GlueG n ρ` are the glued Radon data of the paper's Step 3, as even functions of
`u = cos α`:

`GlueF n ρ u = gluedPhi n (radonPhi n ρ) |u|`,   `GlueG n ρ u = gluedPsi (radonPsi n ρ) |u|`,

where `gluedPhi`/`gluedPsi` keep the anchor's data on the cap `|c| < 4/5` and replace them by the
ball's data below (`gluedPhi`), respectively by `0` (`gluedPsi`).  The junction hypothesis

`hjun : ∀ c ∈ (4/5 - 1/100, 4/5 + 1/100), radonPhi n ρ c = ballPhiData n c ∧ radonPsi n ρ c = 0`

says that the anchor's two data *already* agree with the ball's on the junction window.

This file proves that both glued data are `C^∞` on the *closed* interval `[0,1]`, which is the
form needed by the endgame (`Φ_h`, `Ψ_h` are evaluated at `u = cos α` for `α ∈ [0, π/2]`, i.e.
at every `u ∈ [0,1]`, endpoints included).

## The proof

The absolute value `u ↦ |u|` is only a nuisance at `u = 0`, and there the glued data agree with the
anchor's data.  Two closed pieces cover `[0,1]`:

* on `[0, 161/200]` (through the junction at `4/5 = 160/200`) the glued data are the *anchor's*
  Radon data: below `4/5` by the definition of the glue, at and above `4/5` (up to `161/200`,
  which is strictly inside the window `(79/100, 81/100)`) by `hjun`.  The anchor's data are `C^∞`
  on `[0,b]` for every `b < 1` by the closed-interval Radon smoothness
  `Work.OddCurve.Free.contDiffOn_radonProfile_Icc_gen` (which needs no behaviour of `ρ` at `±1`
  and, in particular, handles `c = 0`).
* on `[159/200, 1]` they are the *ball's*: `ballPhiData n` is the polynomial
  `(2n+2)|B^{2n-1}|·ballInertiaConst n · c²` there, and `gluedPsi` is `0` (again using `hjun`
  below `4/5`, and the definition of the glue above it).

The two pieces overlap on `[159/200, 161/200] ∋ 4/5` and cover `[0,1]`.
-/

namespace Work.OddVolterra.Free

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Work.OddCurve.LowSlope (GlueF GlueG radonPhi radonPsi ballPhiData gluedPhi gluedPsi
  gluedPhi_of_lt gluedPhi_of_ge gluedPsi_of_lt gluedPsi_of_ge ballPhiData_eq ballVol
  ballInertiaConst)

noncomputable section

/-! ## Closed-interval smoothness of a one-variable Radon profile

The one-variable Radon profile of a profile `γ` smooth on `(-1,1)`,
`radonProfile (2n+1) γ c = |S^{2n-2}| ∫_{-π/2}^{π/2} cos^{2n-2}θ · γ (c sin θ) dθ`, is smooth on
every closed interval `[0,b]`, `b < 1`, *without* any hypothesis on `γ` at the endpoints `±1`:
the integrand only ever evaluates `γ` at `c sin θ ∈ (-R,R) ⊂ (-1,1)`, so one may replace `γ` by a
global smooth function agreeing with it near `[0,b]` and differentiate under the integral sign
(`Commons.Analysis.Calculus.taylorExtend`, `Work.Analysis.Calculus.contDiff_intervalIntegral_fixed`).
This holds in particular at `c = 0`, which is what we need for the left endpoint `u = 0` of
`Icc 0 1` (where `|u|` has no two-sided smoothness).

`ρ ∈ C^∞(-1,1)` gives the two profiles `u ↦ u²ρ(u)^{2n+2}` and `u ↦ uρ(u)^{2n+1}`, so this
covers both `radonPhi n ρ` and `radonPsi n ρ`.
-/

/-- The one-variable Radon profile of a profile smooth on `(-1,1)` is `C^∞` on `[0,b]`, `b < 1`. -/
private lemma contDiffOn_radonProfile_Icc_local (n : ℕ) (hn : 1 ≤ n) {γ : ℝ → ℝ} {b : ℝ}
    (hb : b < 1) (hγ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c : ℝ => Work.OddRadon.radonProfile (2 * n + 1) γ c) (Set.Icc 0 b) := by
  rw [contDiffOn_infty]
  intro N
  -- at each point `x ∈ [0,b]` we work on an open neighbourhood `(-R,R)` with `|x| < R < 1`
  refine contDiffOn_of_locally_contDiffOn (fun x hx => ?_)
  obtain ⟨hx0, hxb⟩ := hx
  have hx1 : x < 1 := lt_of_le_of_lt hxb hb
  set R : ℝ := (x + 1) / 2 with hR
  have hxR : x < R := by rw [hR]; linarith
  have hR1 : R < 1 := by rw [hR]; linarith
  refine ⟨Set.Ioo (-R) R, isOpen_Ioo, ⟨by linarith, hxR⟩, ?_⟩
  have hsub : Set.Icc (-R) R ⊆ Set.Ioo (-1 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1, hR1], by linarith [ht.2, hR1]⟩
  have hγR : ContDiffOn ℝ ((N : ℕ∞) : WithTop ℕ∞) γ (Set.Icc (-R) R) :=
    (hγ.mono hsub).of_le (by exact_mod_cast (le_top : (N : ℕ∞) ≤ (⊤ : ℕ∞)))
  -- a globally `C^N` function agreeing with the profile on `[-R,R]`
  obtain ⟨G, hGsm, hGeq⟩ : ∃ G : ℝ → ℝ, ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞) G ∧
      Set.EqOn G γ (Set.Icc (-R) R) :=
    ⟨Commons.Analysis.Calculus.taylorExtend γ N (-R) R,
      Commons.Analysis.Calculus.contDiff_taylorExtend N (by linarith) hγR,
      Commons.Analysis.Calculus.taylorExtend_eqOn_Icc⟩
  set F : ℝ → ℝ → ℝ := fun c θ => Real.cos θ ^ (2 * n - 2) * G (c * Real.sin θ) with hF
  have hFsm : ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => F p.1 p.2) := by
    rw [hF]
    exact ((Real.contDiff_cos.comp contDiff_snd).pow (2 * n - 2)).mul
      (hGsm.comp (contDiff_fst.mul (Real.contDiff_sin.comp contDiff_snd)))
  have hK : ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞)
      (fun c : ℝ => ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), F c θ) :=
    Work.Analysis.Calculus.contDiff_intervalIntegral_fixed N hFsm
  -- the smooth integral coincides with the datum on `[0,b] ∩ (-R,R)`
  refine ((hK.const_smul (Work.OddRadon.sphereArea (2 * n - 2))).contDiffOn).congr
    (fun c hc => ?_)
  obtain ⟨hc1, hc2⟩ := hc
  have hc0 : 0 ≤ c := hc1.1
  have hcR : c < R := hc2.2
  rw [Work.OddCurve.LowSlope.radonProfile_eq_cos_any n hn γ c]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  rw [hF]
  simp only
  have hsin : |Real.sin θ| ≤ 1 := by
    rw [abs_le]; exact ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hle : |c * Real.sin θ| ≤ R := by
    rw [abs_mul, abs_of_nonneg hc0]
    calc c * |Real.sin θ| ≤ c * 1 := mul_le_mul_of_nonneg_left hsin hc0
      _ = c := by ring
      _ ≤ R := hcR.le
  have hmem : c * Real.sin θ ∈ Set.Icc (-R) R :=
    ⟨le_trans (neg_le_neg hle) (neg_abs_le _), le_trans (le_abs_self _) hle⟩
  rw [hGeq hmem]

/-! ## The junction levels -/

/-- `4/5 ≤ u ≤ 161/200` puts `u` strictly inside the junction window `(79/100, 81/100)`. -/
private lemma mem_junction_of_le_161 (u : ℝ) (hu : u ≤ 161 / 200) (h : 4 / 5 ≤ u) :
    u ∈ Set.Ioo (4 / 5 - 1 / 100 : ℝ) (4 / 5 + 1 / 100) :=
  ⟨by linarith, by linarith⟩

/-- `159/200 ≤ u < 4/5` puts `u` strictly inside the junction window `(79/100, 81/100)`. -/
private lemma mem_junction_of_ge_159 (u : ℝ) (hu : 159 / 200 ≤ u) (h : u < 4 / 5) :
    u ∈ Set.Ioo (4 / 5 - 1 / 100 : ℝ) (4 / 5 + 1 / 100) :=
  ⟨by linarith, by linarith⟩

/-! ## The glued data as the anchor's on `[0, 161/200]` and as the ball's on `[159/200, 1]` -/

/-- On `[0, 161/200]` the glued first datum equals the anchor's. -/
private lemma GlueF_eq_radonPhi_of_le_161 {n : ℕ} {ρ : ℝ → ℝ}
    (hjun : ∀ c ∈ Set.Ioo (4 / 5 - 1 / 100 : ℝ) (4 / 5 + 1 / 100),
      radonPhi n ρ c = ballPhiData n c ∧ radonPsi n ρ c = 0)
    {u : ℝ} (hu : u ∈ Set.Icc 0 (161 / 200)) : GlueF n ρ u = radonPhi n ρ u := by
  unfold GlueF
  rw [abs_of_nonneg hu.1]
  rcases lt_or_ge u (4 / 5) with h | h
  · exact gluedPhi_of_lt hu.1 h
  · rw [gluedPhi_of_ge hu.1 h]
    exact (hjun u (mem_junction_of_le_161 u hu.2 h)).1.symm

/-- On `[0, 161/200]` the glued second datum equals the anchor's. -/
private lemma GlueG_eq_radonPsi_of_le_161 {n : ℕ} {ρ : ℝ → ℝ}
    (hjun : ∀ c ∈ Set.Ioo (4 / 5 - 1 / 100 : ℝ) (4 / 5 + 1 / 100),
      radonPhi n ρ c = ballPhiData n c ∧ radonPsi n ρ c = 0)
    {u : ℝ} (hu : u ∈ Set.Icc 0 (161 / 200)) : GlueG n ρ u = radonPsi n ρ u := by
  unfold GlueG
  rw [abs_of_nonneg hu.1]
  rcases lt_or_ge u (4 / 5) with h | h
  · exact gluedPsi_of_lt hu.1 h
  · rw [gluedPsi_of_ge hu.1 h]
    exact (hjun u (mem_junction_of_le_161 u hu.2 h)).2.symm

/-- On `[159/200, 1]` the glued first datum equals the ball's. -/
private lemma GlueF_eq_ballPhiData_of_ge_159 {n : ℕ} {ρ : ℝ → ℝ}
    (hjun : ∀ c ∈ Set.Ioo (4 / 5 - 1 / 100 : ℝ) (4 / 5 + 1 / 100),
      radonPhi n ρ c = ballPhiData n c ∧ radonPsi n ρ c = 0)
    {u : ℝ} (hu : u ∈ Set.Icc (159 / 200) 1) : GlueF n ρ u = ballPhiData n u := by
  have hu0 : 0 ≤ u := by linarith [hu.1]
  unfold GlueF
  rw [abs_of_nonneg hu0]
  rcases lt_or_ge u (4 / 5) with h | h
  · rw [gluedPhi_of_lt hu0 h]
    exact (hjun u (mem_junction_of_ge_159 u hu.1 h)).1
  · exact gluedPhi_of_ge hu0 h

/-- On `[159/200, 1]` the glued second datum vanishes. -/
private lemma GlueG_eq_zero_of_ge_159 {n : ℕ} {ρ : ℝ → ℝ}
    (hjun : ∀ c ∈ Set.Ioo (4 / 5 - 1 / 100 : ℝ) (4 / 5 + 1 / 100),
      radonPhi n ρ c = ballPhiData n c ∧ radonPsi n ρ c = 0)
    {u : ℝ} (hu : u ∈ Set.Icc (159 / 200) 1) : GlueG n ρ u = 0 := by
  have hu0 : 0 ≤ u := by linarith [hu.1]
  unfold GlueG
  rw [abs_of_nonneg hu0]
  rcases lt_or_ge u (4 / 5) with h | h
  · rw [gluedPsi_of_lt hu0 h]
    exact (hjun u (mem_junction_of_ge_159 u hu.1 h)).2
  · exact gluedPsi_of_ge hu0 h

/-! ## The two pieces of the cover, and the assembly -/

/-- The ball's first datum is smooth on `[159/200, 1]`, where it is the polynomial
`(2n+2)|B^{2n-1}|·ballInertiaConst n · c²`. -/
private lemma contDiffOn_ballPhiData_Icc (n : ℕ) (hn : 1 ≤ n) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ballPhiData n) (Set.Icc (159 / 200 : ℝ) 1) := by
  have hpoly : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c : ℝ => (2 * (n : ℝ) + 2) * ballVol (2 * n - 1) * ballInertiaConst n * c ^ 2)
      (Set.Icc (159 / 200 : ℝ) 1) := by fun_prop
  exact hpoly.congr (fun c hc =>
    ballPhiData_eq n hn (by linarith [hc.1]) (by linarith [hc.2]))

theorem glueDataContDiffOnIcc (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hjun : ∀ c ∈ Set.Ioo (4 / 5 - 1 / 100 : ℝ) (4 / 5 + 1 / 100),
      Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c ∧
      Work.OddCurve.LowSlope.radonPsi n ρ c = 0) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.GlueF n ρ) (Set.Icc 0 1) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.GlueG n ρ) (Set.Icc 0 1) := by
  -- smoothness of the two anchor profiles on `(-1,1)`
  have hφ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) (Set.Ioo (-1 : ℝ) 1) :=
    (contDiffOn_id.pow 2).mul (hρ.pow (2 * n + 2))
  have hψ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => u * ρ u ^ (2 * n + 1)) (Set.Ioo (-1 : ℝ) 1) :=
    contDiffOn_id.mul (hρ.pow (2 * n + 1))
  -- the anchor's two Radon data are smooth on the closed interval `[0, 161/200]`
  have hPhiC : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (radonPhi n ρ) (Set.Icc 0 (161 / 200)) :=
    contDiffOn_radonProfile_Icc_local n hn (b := (161 / 200 : ℝ)) (by norm_num) hφ
  have hPsiC : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (radonPsi n ρ) (Set.Icc 0 (161 / 200)) :=
    contDiffOn_radonProfile_Icc_local n hn (b := (161 / 200 : ℝ)) (by norm_num) hψ
  -- the ball's first datum is smooth on `[159/200, 1]`
  have hball : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ballPhiData n) (Set.Icc (159 / 200) 1) :=
    contDiffOn_ballPhiData_Icc n hn
  -- the two closed pieces
  have hFC : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (GlueF n ρ) (Set.Icc 0 (161 / 200)) :=
    hPhiC.congr (fun u hu => GlueF_eq_radonPhi_of_le_161 hjun hu)
  have hGC : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (GlueG n ρ) (Set.Icc 0 (161 / 200)) :=
    hPsiC.congr (fun u hu => GlueG_eq_radonPsi_of_le_161 hjun hu)
  have hFB : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (GlueF n ρ) (Set.Icc (159 / 200) 1) :=
    hball.congr (fun u hu => GlueF_eq_ballPhiData_of_ge_159 hjun hu)
  have hGB : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (GlueG n ρ) (Set.Icc (159 / 200) 1) :=
    (contDiff_const (c := (0 : ℝ))).contDiffOn.congr
      (fun u hu => GlueG_eq_zero_of_ge_159 hjun hu)
  -- the two pieces cover `[0,1]`, so any `x ∈ [0,1]` is covered by one of them
  have key : ∀ f : ℝ → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Icc 0 (161 / 200)) →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Icc (159 / 200) 1) →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Icc 0 1) := by
    intro f h1 h2 x hx
    by_cases hx1 : x < 161 / 200
    · refine (h1 x ⟨hx.1, le_of_lt hx1⟩).mono_of_mem_nhdsWithin ?_
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Set.Iio ((x + 161 / 200) / 2),
        IsOpen.mem_nhds isOpen_Iio (by rw [Set.mem_Iio]; linarith), ?_⟩
      rintro y ⟨hy1, hy2⟩
      have hy1' : y < (x + 161 / 200) / 2 := hy1
      exact ⟨hy2.1, by linarith⟩
    · have hx1' : (161 / 200 : ℝ) ≤ x := not_lt.mp hx1
      have hx2 : (159 / 200 : ℝ) ≤ x := by linarith
      refine (h2 x ⟨hx2, hx.2⟩).mono_of_mem_nhdsWithin ?_
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Set.Ioi ((x + 159 / 200) / 2),
        IsOpen.mem_nhds isOpen_Ioi (by rw [Set.mem_Ioi]; linarith), ?_⟩
      rintro y ⟨hy1, hy2⟩
      have hy1' : (x + 159 / 200) / 2 < y := hy1
      exact ⟨by linarith, hy2.2⟩
  exact ⟨key _ hFC hFB, key _ hGC hGB⟩

end

end Work.OddVolterra.Free
