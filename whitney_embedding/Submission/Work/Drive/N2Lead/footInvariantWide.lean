import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.saddleScaled
import Submission.Work.Drive.N2.footMapDefs
import Submission.Work.Drive.N2.footInvariant_of_mem_C
import Submission.Work.Drive.N2.im_sq_foot_ge_of_mem_C
import Submission.Work.Drive.N2.saddlePack
import Submission.Work.Drive.N2.levelBoundsOfJourney
import Submission.Work.Drive.N2.swlLanding

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff in
/-- Auxiliary brick of `footInvariantWide`: a point `z` of the closed chart region `C j` whose chart
norm is at least `ρ j` (i.e. `8 lam0`) and whose value lies in the `ηb`-band of `f p` has invariant
at least `c₀`.  The proof is the fourth-power identity
`‖φ' z‖⁴ = Re ((Zs z)²)² + Im ((Zs z)²)²` together with the level law for `Re`. -/
lemma footInvariantWide_normBound {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))} {Zs Z : M → ℂ} {lam0 : ℝ}
    (hlam0pos : 0 < lam0) (hlam0 : lam0 = D.ρ D.j / 8)
    (hZs : ∀ y : M, Zs y = ((φ' y 0 : ℝ) : ℂ) + ((φ' y 1 : ℝ) : ℂ) * Complex.I)
    (hZrel : ∀ y : M, Zs y = (lam0 : ℂ) * Z y)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re)
    {c₀ ηb : ℝ} (hηb1 : ηb ^ 2 ≤ 1) (hc₀nn : 0 ≤ c₀) (hc₀2 : c₀ < 2)
    {z : M} (hzC : z ∈ D.C D.j) (hznorm : D.ρ D.j ≤ ‖φ' z‖)
    (hzlev : |f z - f p| ≤ lam0 ^ 2 * ηb) :
    c₀ ≤ |((Z z) ^ 2).im| := by
  have hρ8 : D.ρ D.j = 8 * lam0 := by rw [hlam0]; ring
  have hzsrc : z ∈ (D.φ D.j).source := D.hCsub D.j hzC
  have hsq : (Zs z) ^ 2 = (((lam0 ^ 2 : ℝ)) : ℂ) * (Z z) ^ 2 := by
    rw [hZrel z, mul_pow, ← Complex.ofReal_pow]
  have hre : ((Zs z) ^ 2).re = f z - f p := by
    rw [hsq, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    rw [hlev z hzsrc]
    ring
  have him : ((Zs z) ^ 2).im = lam0 ^ 2 * ((Z z) ^ 2).im := by
    rw [hsq, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hfour : ‖φ' z‖ ^ 4 = ((Zs z) ^ 2).re ^ 2 + ((Zs z) ^ 2).im ^ 2 :=
    Work.Drive.N2.swlL_Zs_fourth φ' Zs hZs z
  have hzn8 : 8 * lam0 ≤ ‖φ' z‖ := by rw [← hρ8]; exact hznorm
  have h1 : (8 * lam0) ^ 4 ≤ ((Zs z) ^ 2).re ^ 2 + ((Zs z) ^ 2).im ^ 2 := by
    rw [← hfour]
    exact pow_le_pow_left₀ (by positivity) hzn8 4
  have h2 : ((Zs z) ^ 2).re ^ 2 ≤ (lam0 ^ 2 * ηb) ^ 2 := by
    rw [hre, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hzlev 2
  have h3 : (8 * lam0) ^ 4 - (lam0 ^ 2 * ηb) ^ 2 = lam0 ^ 4 * (4096 - ηb ^ 2) := by ring
  have hkey : lam0 ^ 4 * 4095 ≤ ((Zs z) ^ 2).im ^ 2 := by
    have h6 : lam0 ^ 4 * 4095 ≤ lam0 ^ 4 * (4096 - ηb ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith [h1, h2, h3, h6]
  have hIm2 : 4095 ≤ ((Z z) ^ 2).im ^ 2 := by
    have h2' : lam0 ^ 4 * ((Z z) ^ 2).im ^ 2 = ((Zs z) ^ 2).im ^ 2 := by
      rw [him]; ring
    have h3' : lam0 ^ 4 * 4095 ≤ lam0 ^ 4 * ((Z z) ^ 2).im ^ 2 := by rw [h2']; exact hkey
    exact le_of_mul_le_mul_left h3' (by positivity : (0 : ℝ) < lam0 ^ 4)
  have h4 : c₀ ^ 2 ≤ ((Z z) ^ 2).im ^ 2 := by
    have h5 : c₀ ^ 2 < 4 := by nlinarith [hc₀2, hc₀nn]
    linarith
  have h6 := (sq_le_sq).mp h4
  rwa [abs_of_nonneg hc₀nn] at h6

open scoped Manifold ContDiff in
/-- Auxiliary brick of `footInvariantWide`: the invariant `Im ((Z ·)²)` is constant along a
chart-confined trace. -/
lemma footInvariantWide_im_eq {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {Zs Z : M → ℂ} {lam0 : ℝ}
    (hlam0pos : 0 < lam0) (hZrel : ∀ y : M, Zs y = (lam0 : ℂ) * Z y)
    (him : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im)
    {y : M} {t₀ t₁ : ℝ} (h : t₀ ≤ t₁)
    (hconf : ∀ u ∈ Set.Icc t₀ t₁, D.Φ (u, y) ∈ D.C D.j) :
    ((Z (D.Φ (t₁, y))) ^ 2).im = ((Z (D.Φ (t₀, y))) ^ 2).im := by
  have htrans := Work.Drive.N2.swlL_im_eq D Zs him h hconf
  have hrel : ∀ w : M, ((Zs w) ^ 2).im = lam0 ^ 2 * ((Z w) ^ 2).im := by
    intro w
    have h1 : (Zs w) ^ 2 = (((lam0 ^ 2 : ℝ)) : ℂ) * (Z w) ^ 2 := by
      rw [hZrel w, mul_pow, ← Complex.ofReal_pow]
    rw [h1, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h2 : lam0 ^ 2 * ((Z (D.Φ (t₁, y))) ^ 2).im
      = lam0 ^ 2 * ((Z (D.Φ (t₀, y))) ^ 2).im := by
    rw [← hrel (D.Φ (t₁, y)), ← hrel (D.Φ (t₀, y)), htrans]
  exact mul_left_cancel₀ (ne_of_gt (pow_pos hlam0pos 2)) h2

open scoped Manifold ContDiff in
/-- R4 of the D2 design (`NOTES_LEAD_saddlePacket.md` §2), wide form: the foot invariant of the saddle window for the band `(f p - lam0² ηb, f p + lam0² ηb)` around the critical value `f p`, with the anchor level `f p - lam0² ηs ≤ f p`.  This is `Work.Drive.N2Lead.footInvariant_of_mem_C` (`N2h/footInvariant_of_mem_C.lean`) with the band parameter `ηb` decoupled from the anchor offset `ηs`; the sub-case `f y < f p - lam0² ηs` runs the trajectory forward in time, and the region hypothesis is the model-ball region
`{y | y ∈ modelBall (φ_j) (ρ_j) ∧ |Im (Z y)²| < c₀}`.  Proof template for the backward case: `N2h/footInvariant_of_mem_C.lean` with `η` replaced by `ηb` (the exit-level bound uses `ηs ≤ ηb`); for the forward case: the same first/last-exit argument on `[0, τ]` (`τ = (f p - lam0² ηs) - f y > 0`), the trace being in `D.C D.j` on the terminal interval `[t₂, τ]` where `t₂ = sSup {t ∈ Icc 0 τ | Φ (t,y) ∉ D.C D.j}`, and the bound at `Φ (t₂,y)` coming from `hCop` (`‖φ_j ·‖ ≥ ρ_j` at the exit points) together with `hlev` and the band. -/
theorem footInvariantWide {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsgn : D.s₁ D.j = - D.s₂ D.j)
    {φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))} {Zs Z : M → ℂ} {lam0 : ℝ}
    (hlam0pos : 0 < lam0) (hlam0 : lam0 = D.ρ D.j / 8)
    (hsrc : φ'.source = (D.φ D.j).source)
    (hball : ∀ r : ℝ, Work.Drive.N2.modelBall φ' r = Work.Drive.N2.modelBall (D.φ D.j) r)
    (hZs : ∀ y : M, Zs y = ((φ' y 0 : ℝ) : ℂ) + ((φ' y 1 : ℝ) : ℂ) * Complex.I)
    (hZrel : ∀ y : M, Zs y = (lam0 : ℂ) * Z y)
    (hZsm : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z (D.φ D.j).source)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re)
    (him : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im)
    {ηs ηb δ c₀ : ℝ} (hηs : 0 < ηs) (hηs' : ηs < 1 / 10) (hηb : ηs ≤ ηb) (hηb' : ηb < 1 / 10)
    (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hc₀ : 2 - 2 * δ < c₀) (hc₀' : c₀ < 2)
    (hsep : (D.ρ D.j / 8) ^ 2 * ηb < 2 * D.ηd)
    {y : M}
    (hyD : y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀)
    (hyb : f y ∈ Set.Ioo (f p - lam0 ^ 2 * ηb) (f p + lam0 ^ 2 * ηb))
    (hyC : Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) y ∈ D.C D.j) :
    c₀ ≤ |((Z (Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) y)) ^ 2).im| := by
  classical
  -- ## Basic numerical facts
  have hηbpos : 0 < ηb := lt_of_lt_of_le hηs hηb
  have hηb1 : ηb ^ 2 ≤ 1 := by nlinarith [hηbpos, hηb']
  have hc₀nn : 0 ≤ c₀ := by linarith [hc₀, hδ]
  have hlam0nn : 0 ≤ lam0 := hlam0pos.le
  have hlam0sqpos : 0 < lam0 ^ 2 := by positivity
  have hlam0sqne : lam0 ^ 2 ≠ 0 := ne_of_gt hlam0sqpos
  have hγ : Continuous fun t : ℝ => D.Φ (t, y) :=
    D.hΦsm.continuous.comp (continuous_id.prodMk continuous_const)
  have hCclosed : IsClosed (D.C D.j) := D.hCclosed D.j
  -- ## The band bound at `y`
  have hyband : |f y - f p| ≤ lam0 ^ 2 * ηb := by
    rw [abs_le]
    exact ⟨by linarith [hyb.1], by linarith [hyb.2]⟩
  -- ## The invariant relation `Zs ↔ Z`
  have imRel : ∀ w : M, ((Zs w) ^ 2).im = lam0 ^ 2 * ((Z w) ^ 2).im := by
    intro w
    have h1 : (Zs w) ^ 2 = (((lam0 ^ 2 : ℝ)) : ℂ) * (Z w) ^ 2 := by
      rw [hZrel w, mul_pow, ← Complex.ofReal_pow]
    rw [h1, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    ring
  -- ## The foot point
  set τ : ℝ := f p - lam0 ^ 2 * ηs - f y with hτdef
  have hfootτ : Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) y = D.Φ (τ, y) := by
    rw [Work.Drive.N2.footMap, hτdef]
  have hyCτ : D.Φ (τ, y) ∈ D.C D.j := by rw [← hfootτ]; exact hyC
  -- ## The fourth-power bound at a chart-real point
  have auxNorm : ∀ z : M, z ∈ D.C D.j → D.ρ D.j ≤ ‖φ' z‖ →
      |f z - f p| ≤ lam0 ^ 2 * ηb → c₀ ≤ |((Z z) ^ 2).im| :=
    fun z hzC hznorm hzlev =>
      footInvariantWide_normBound D hlam0pos hlam0 hZs hZrel hlev hηb1 hc₀nn hc₀' hzC hznorm hzlev
  -- ## The invariant bound at `y` (region condition)
  have hyBound : y ∈ D.C D.j → c₀ ≤ |((Z y) ^ 2).im| := by
    intro hyCj
    by_cases hmb : y ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)
    · by_contra hcon
      exact hyD ⟨hmb, not_le.mp hcon⟩
    · have hysrc : y ∈ (D.φ D.j).source := D.hCsub D.j hyCj
      have hnormj : D.ρ D.j ≤ ‖D.φ D.j y‖ := by
        by_contra hcon
        exact hmb ⟨hysrc, not_le.mp hcon⟩
      have hnorm : D.ρ D.j ≤ ‖φ' y‖ := by
        rw [← Work.Drive.N2.swlL_norm_eq_of_modelBall_eq (D.φ D.j) φ' hsrc hball hysrc]
        exact hnormj
      exact auxNorm y hyCj hnorm hyband
  rcases le_or_gt τ 0 with hτle | hτgt
  · -- ============ Case A: the anchor level is below `f y` (backward journey) ============
    set S : Set ℝ := {t : ℝ | t ∈ Set.Icc τ 0 ∧ D.Φ (t, y) ∉ D.C D.j} with hSdef
    have hSmem : ∀ t : ℝ, t ∈ S ↔ (t ∈ Set.Icc τ 0 ∧ D.Φ (t, y) ∉ D.C D.j) := by
      intro t
      rw [hSdef]
      exact Iff.rfl
    have hτnotS : τ ∉ S := fun h => h.2 hyCτ
    by_cases hSne : S.Nonempty
    · -- the trace leaves `C j`: the first exit
      set t₁ : ℝ := sInf S with ht₁def
      have hSbdd : BddBelow S := ⟨τ, fun t ht => ((hSmem t).mp ht).1.1⟩
      have ht₁ge : τ ≤ t₁ := le_csInf hSne (fun t ht => ((hSmem t).mp ht).1.1)
      have ht₁le : t₁ ≤ 0 := by
        obtain ⟨s, hs⟩ := hSne
        exact le_trans (csInf_le hSbdd hs) ((hSmem s).mp hs).1.2
      have ht₁notS : t₁ ∉ S := by
        intro htS
        rcases eq_or_lt_of_le ht₁ge with heq | hlt
        · rw [← heq] at htS
          exact hτnotS htS
        · have hnb : ((fun t : ℝ => D.Φ (t, y)) ⁻¹' (D.C D.j)ᶜ) ∈ nhds t₁ :=
            hγ.continuousAt.preimage_mem_nhds (hCclosed.isOpen_compl.mem_nhds htS.2)
          obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hnb
          set u : ℝ := max τ (t₁ - ε / 2) with hudef
          have hult : u < t₁ := max_lt hlt (by linarith)
          have hmem : u ∈ S := by
            refine (hSmem u).mpr ⟨⟨le_max_left _ _, hult.le.trans ht₁le⟩, ?_⟩
            refine hε ?_
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]
            have h2 : t₁ - ε / 2 ≤ u := le_max_right _ _
            constructor <;> linarith
          linarith [csInf_le hSbdd hmem, hult]
      have ht₁C : D.Φ (t₁, y) ∈ D.C D.j := by
        by_contra hbad
        exact ht₁notS ((hSmem t₁).mpr ⟨⟨ht₁ge, ht₁le⟩, hbad⟩)
      have hconf : ∀ u ∈ Set.Icc τ t₁, D.Φ (u, y) ∈ D.C D.j := by
        intro u hu
        rcases eq_or_lt_of_le hu.2 with h | h
        · rw [h]; exact ht₁C
        · by_contra hbad
          have hmem : u ∈ S := (hSmem u).mpr ⟨⟨hu.1, h.le.trans ht₁le⟩, hbad⟩
          linarith [csInf_le hSbdd hmem, h]
      have hzcl : D.Φ (t₁, y) ∈ closure ((D.C D.j)ᶜ) := by
        have hcl : t₁ ∈ closure S := by
          rw [Metric.mem_closure_iff]
          intro ε hε
          obtain ⟨s, hsS, hslt⟩ : ∃ s ∈ S, s < t₁ + ε := by
            by_contra hcon
            push Not at hcon
            have hcontra : t₁ + ε ≤ t₁ := le_csInf hSne hcon
            linarith
          refine ⟨s, hsS, ?_⟩
          rw [Real.dist_eq, abs_lt]
          have hge : t₁ ≤ s := csInf_le hSbdd hsS
          constructor <;> linarith
        have himg : D.Φ (t₁, y) ∈ closure ((fun t : ℝ => D.Φ (t, y)) '' S) :=
          image_closure_subset_closure_image hγ ⟨t₁, hcl, rfl⟩
        refine closure_mono ?_ himg
        rintro z ⟨s, hs, rfl⟩
        exact ((hSmem s).mp hs).2
      have hznorm : D.ρ D.j ≤ ‖φ' (D.Φ (t₁, y))‖ :=
        Work.Drive.N2.swlL_norm_ge_rho_of_closure_compl D φ' hsrc hball ht₁C hzcl
      have hzlev : |f (D.Φ (t₁, y)) - f p| ≤ lam0 ^ 2 * ηb := by
        have hb := Work.Drive.N2.levelBoundsOfJourney D (x := y) (τ := t₁) ht₁le
        have h2 : f y + τ = f p - lam0 ^ 2 * ηs := by rw [hτdef]; ring
        have h3 : f p - lam0 ^ 2 * ηb ≤ f p - lam0 ^ 2 * ηs := by
          have h4 := mul_le_mul_of_nonneg_left hηb (by positivity : (0 : ℝ) ≤ lam0 ^ 2)
          linarith
        have h5 : f p - lam0 ^ 2 * ηb ≤ f (D.Φ (t₁, y)) := by linarith [hb.1, ht₁ge, h2, h3]
        have h6 : f (D.Φ (t₁, y)) < f p + lam0 ^ 2 * ηb := lt_of_le_of_lt hb.2 hyb.2
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have hbound : c₀ ≤ |((Z (D.Φ (t₁, y))) ^ 2).im| := auxNorm _ ht₁C hznorm hzlev
      have hZim : ((Z (D.Φ (t₁, y))) ^ 2).im = ((Z (D.Φ (τ, y))) ^ 2).im :=
        footInvariantWide_im_eq D hlam0pos hZrel him ht₁ge hconf
      rw [hfootτ, ← hZim]
      exact hbound
    · -- the trace stays inside `C j`
      have hconf : ∀ u ∈ Set.Icc τ 0, D.Φ (u, y) ∈ D.C D.j := by
        intro u hu
        by_contra hbad
        exact hSne ⟨u, (hSmem u).mpr ⟨hu, hbad⟩⟩
      have hyCj : y ∈ D.C D.j := by
        have h := hconf 0 ⟨hτle, le_rfl⟩
        rwa [D.hΦ0 y] at h
      have hbound : c₀ ≤ |((Z y) ^ 2).im| := hyBound hyCj
      have hZim : ((Z (D.Φ (τ, y))) ^ 2).im = ((Z y) ^ 2).im := by
        have h : ((Z (D.Φ (0, y))) ^ 2).im = ((Z (D.Φ (τ, y))) ^ 2).im :=
          footInvariantWide_im_eq D hlam0pos hZrel him hτle hconf
        rw [D.hΦ0 y] at h
        exact h.symm
      rw [hfootτ, hZim]
      exact hbound
  · -- ============ Case B: the anchor level is above `f y` (forward journey) ============
    set S : Set ℝ := {t : ℝ | t ∈ Set.Icc 0 τ ∧ D.Φ (t, y) ∉ D.C D.j} with hSdef
    have hSmem : ∀ t : ℝ, t ∈ S ↔ (t ∈ Set.Icc 0 τ ∧ D.Φ (t, y) ∉ D.C D.j) := by
      intro t
      rw [hSdef]
      exact Iff.rfl
    have hτnotS : τ ∉ S := fun h => h.2 hyCτ
    by_cases hSne : S.Nonempty
    · -- the trace leaves `C j`: the last exit
      set t₂ : ℝ := sSup S with ht₂def
      have hSbdd : BddAbove S := ⟨τ, fun t ht => ((hSmem t).mp ht).1.2⟩
      have ht₂ge : 0 ≤ t₂ := by
        obtain ⟨s, hs⟩ := hSne
        exact le_trans ((hSmem s).mp hs).1.1 (le_csSup hSbdd hs)
      have ht₂le : t₂ ≤ τ := csSup_le hSne (fun t ht => ((hSmem t).mp ht).1.2)
      have ht₂clS : t₂ ∈ closure S := by
        rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨s, hsS, hslt⟩ : ∃ s ∈ S, t₂ - ε < s := by
          by_contra hcon
          push Not at hcon
          have hcontra : t₂ ≤ t₂ - ε := csSup_le hSne hcon
          linarith
        refine ⟨s, hsS, ?_⟩
        rw [Real.dist_eq, abs_lt]
        have hle : s ≤ t₂ := le_csSup hSbdd hsS
        constructor <;> linarith
      have ht₂C : D.Φ (t₂, y) ∈ D.C D.j := by
        rcases eq_or_lt_of_le ht₂le with heq | hlt
        · rw [heq]; exact hyCτ
        · by_contra hbad
          have hnb : ((fun t : ℝ => D.Φ (t, y)) ⁻¹' (D.C D.j)ᶜ) ∈ nhds t₂ :=
            hγ.continuousAt.preimage_mem_nhds (hCclosed.isOpen_compl.mem_nhds hbad)
          obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hnb
          set u : ℝ := min τ (t₂ + ε / 2) with hudef
          have ht₂ltu : t₂ < u := lt_min hlt (by linarith)
          have hmem : u ∈ S := by
            refine (hSmem u).mpr ⟨⟨le_trans ht₂ge ht₂ltu.le, min_le_left _ _⟩, ?_⟩
            refine hε ?_
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]
            have h2 : u ≤ t₂ + ε / 2 := min_le_right _ _
            constructor <;> linarith
          linarith [le_csSup hSbdd hmem, ht₂ltu]
      have hconf : ∀ u ∈ Set.Icc t₂ τ, D.Φ (u, y) ∈ D.C D.j := by
        intro u hu
        rcases eq_or_lt_of_le hu.1 with h | h
        · rw [← h]; exact ht₂C
        · by_contra hbad
          have hmem : u ∈ S := (hSmem u).mpr ⟨⟨le_trans ht₂ge h.le, hu.2⟩, hbad⟩
          linarith [le_csSup hSbdd hmem, h]
      have hzcl : D.Φ (t₂, y) ∈ closure ((D.C D.j)ᶜ) := by
        have himg : D.Φ (t₂, y) ∈ closure ((fun t : ℝ => D.Φ (t, y)) '' S) :=
          image_closure_subset_closure_image hγ ⟨t₂, ht₂clS, rfl⟩
        refine closure_mono ?_ himg
        rintro z ⟨s, hs, rfl⟩
        exact ((hSmem s).mp hs).2
      have hznorm : D.ρ D.j ≤ ‖φ' (D.Φ (t₂, y))‖ :=
        Work.Drive.N2.swlL_norm_ge_rho_of_closure_compl D φ' hsrc hball ht₂C hzcl
      have hzlev : |f (D.Φ (t₂, y)) - f p| ≤ lam0 ^ 2 * ηb := by
        have hb := Work.Drive.N2.orbit_pair_bound D y 0 t₂ ht₂ge
        rw [D.hΦ0 y] at hb
        have hmono := D.hmono y (le_refl (0 : ℝ)) ht₂ge ht₂ge
        change f (D.Φ (0, y)) ≤ f (D.Φ (t₂, y)) at hmono
        rw [D.hΦ0 y] at hmono
        have h2 : f y + τ = f p - lam0 ^ 2 * ηs := by rw [hτdef]; ring
        have h3 : f p - lam0 ^ 2 * ηs ≤ f p := by
          have h4 : 0 ≤ lam0 ^ 2 * ηs := mul_nonneg (by positivity) hηs.le
          linarith
        have htop : f (D.Φ (t₂, y)) ≤ f p := by linarith [hb, ht₂le, h2, h3]
        have hnb : (0 : ℝ) ≤ lam0 ^ 2 * ηb := mul_nonneg (by positivity) hηbpos.le
        exact abs_le.mpr ⟨by linarith [hmono, hyb.1], by linarith [htop, hnb]⟩
      have hbound : c₀ ≤ |((Z (D.Φ (t₂, y))) ^ 2).im| := auxNorm _ ht₂C hznorm hzlev
      have hZim : ((Z (D.Φ (τ, y))) ^ 2).im = ((Z (D.Φ (t₂, y))) ^ 2).im :=
        footInvariantWide_im_eq D hlam0pos hZrel him ht₂le hconf
      rw [hfootτ, hZim]
      exact hbound
    · -- the trace stays inside `C j`
      have hconf : ∀ u ∈ Set.Icc 0 τ, D.Φ (u, y) ∈ D.C D.j := by
        intro u hu
        by_contra hbad
        exact hSne ⟨u, (hSmem u).mpr ⟨hu, hbad⟩⟩
      have hyCj : y ∈ D.C D.j := by
        have h := hconf 0 ⟨le_rfl, hτgt.le⟩
        rwa [D.hΦ0 y] at h
      have hbound : c₀ ≤ |((Z y) ^ 2).im| := hyBound hyCj
      have hZim : ((Z (D.Φ (τ, y))) ^ 2).im = ((Z y) ^ 2).im := by
        have h : ((Z (D.Φ (τ, y))) ^ 2).im = ((Z (D.Φ (0, y))) ^ 2).im :=
          footInvariantWide_im_eq D hlam0pos hZrel him hτgt.le hconf
        rw [D.hΦ0 y] at h
        exact h
      rw [hfootτ, hZim]
      exact hbound

end Work.Drive.N2Lead
