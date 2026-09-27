import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.saddleWindowBlock
import Submission.Work.Drive.N2Lead.saddlePacket
import Submission.Work.Drive.N2Lead.saddleMarkedCurve
import Submission.Work.Drive.N2Lead.saddlePinFunction
import Submission.Work.Drive.N2Lead.saddleArcs
import Submission.Work.Drive.N2Lead.polarArc_eq_sqrt
import Submission.Work.Drive.N2C.arcImmersion
import Submission.Work.Drive.N2.modelBall
import Submission.Work.Drive.N2.saddleCollarRow
import Submission.Work.Drive.N2.anchorModelFacts

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-- `γ i` is `1`-periodic, hence invariant under integer shifts of the parameter. -/
lemma levelCurves_gamma_add_int {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {b : ℝ} {n : ℕ} (L : Work.Drive.N2C.LevelCurves f b n)
    (i : Fin n) (k : ℤ) (s : ℝ) : L.γ i (s + k) = L.γ i s := by
  have hper : Function.Periodic (L.γ i) (1 : ℝ) := L.per i
  simpa using (hper.int_mul k) s

/-- The parked round circle has third coordinate `1`. -/
lemma farCurve_apply_two (n : ℕ) (j : Fin n) (t : ℝ) : (farCurve n j t) 2 = 1 := by
  rw [farCurve_eq]
  simp [farPos, Work.Drive.N2.ang, Work.Drive.N2.roundPic, PiLp.add_apply]

/-- The lower arc point is again in the marked chart source. -/
lemma arcDnPt_mem_source {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {lam0 η w : ℝ}
    (hball : ‖arcZ η w‖ < 8) (hlam0pos : 0 < lam0) (hlam0 : lam0 = D.ρ D.j / 8) :
    arcDnPt D lam0 η w ∈ (D.φ D.j).source := by
  refine (D.φ D.j).map_target ?_
  refine Work.Drive.N2.windowBall_subset_target D D.j ?_
  rw [show -((lam0 : ℂ) * arcZ η w) = (lam0 : ℂ) * (-(arcZ η w)) by ring,
    cE2_norm, norm_mul, Complex.norm_of_nonneg hlam0pos.le, hlam0, norm_neg]
  nlinarith [hball, D.hρ D.j]

/-- The pin function equals `1` at the upper arc point. -/
lemma pinTheta_arcUpPt {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ}
    {lam0 ηs m w : ℝ} (hlam0pos : 0 < lam0) (hlam0 : lam0 = D.ρ D.j / 8)
    (hZrel : ∀ x : M, chartCplx D x = (lam0 : ℂ) * Z x)
    (hm : 1 < m) (hm2 : m < 2) (hηs : 0 < ηs) (hηs1 : ηs < 1 / 10)
    (hball : ‖arcZ ηs w‖ < 8) (hw : |w| ≤ m) :
    pinTheta D Z m (arcUpPt D lam0 ηs w) = 1 := by
  have hsrc := arcUpPt_mem_source D hball hlam0
  rw [pinTheta_eq_one_iff D hm2 hsrc]
  refine ⟨?_, ?_⟩
  · rw [Z_arcUpPt D hball hlam0pos hlam0 hZrel, arcZ_sq_im]
    exact hw
  · rw [Z_arcUpPt D hball hlam0pos hlam0 hZrel, norm_arcZ_sq]
    have hw2 : w ^ 2 ≤ m ^ 2 := by
      have h := abs_le.mp hw
      nlinarith [h.1, h.2]
    have hsum : ηs ^ 2 + w ^ 2 ≤ 16 := by nlinarith [hηs, hηs1, hw2, hm2]
    calc Real.sqrt (ηs ^ 2 + w ^ 2) ≤ Real.sqrt 16 := Real.sqrt_le_sqrt hsum
      _ = 4 := by norm_num

/-- The pin function equals `1` at the lower arc point. -/
lemma pinTheta_arcDnPt {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ}
    {lam0 ηs m w : ℝ} (hlam0pos : 0 < lam0) (hlam0 : lam0 = D.ρ D.j / 8)
    (hZrel : ∀ x : M, chartCplx D x = (lam0 : ℂ) * Z x)
    (hm : 1 < m) (hm2 : m < 2) (hηs : 0 < ηs) (hηs1 : ηs < 1 / 10)
    (hball : ‖arcZ ηs w‖ < 8) (hw : |w| ≤ m) :
    pinTheta D Z m (arcDnPt D lam0 ηs w) = 1 := by
  have hsrc := arcDnPt_mem_source D hball hlam0pos hlam0
  rw [pinTheta_eq_one_iff D hm2 hsrc]
  refine ⟨?_, ?_⟩
  · rw [Work.Drive.N2C.Z_arcDnPt D hball hlam0pos hlam0 hZrel, neg_sq, arcZ_sq_im]
    exact hw
  · rw [Work.Drive.N2C.Z_arcDnPt D hball hlam0pos hlam0 hZrel, norm_neg, norm_arcZ_sq]
    have hw2 : w ^ 2 ≤ m ^ 2 := by
      have h := abs_le.mp hw
      nlinarith [h.1, h.2]
    have hsum : ηs ^ 2 + w ^ 2 ≤ 16 := by nlinarith [hηs, hηs1, hw2, hm2]
    calc Real.sqrt (ηs ^ 2 + w ^ 2) ≤ Real.sqrt 16 := Real.sqrt_le_sqrt hsum
      _ = 4 := by norm_num

end

open scoped Manifold ContDiff Topology in
open Set Filter in
/-- **The packet rows of the saddle window** (`NOTES_LEAD_saddlePacket.md` §3.3 item 4): from the
radial profile `r`, the angle function `Θ` and the two arc parametrisations `τU`, `τL` with their
prescription rows, the packet picture `A` of `Work.Drive.N2Lead.packetPicture` has the five rows
`hAsm`, `hAinj`, `hAimm`, `hApin`, `hAoff` consumed by `Work.Drive.N2Lead.saddleWindow_of_packet_band_off`
(with `c := f p`, `lam := lam0 ^ 2`, `η := ηs`, `θ := pinTheta D Z m`, `U := modelBall (D.φ D.j) (D.ρ D.j)`).

The picture is `cE3 (r (Θ t) * exp (i Θ t))` on the marked component `γ i` and the parked circles
`farCurve n j` on the others (`packetCurves` + `packetPicture`); the marked curve's five rows come
from `saddleMarkedCurve`.  The two rows with content are

* `hApin`: `θ x = 1` at the anchor level gives `|Im (Z x)²| ≤ m` and `‖Z x‖ ≤ 2 < 8`, hence
  `x ∈ saddlePin D (f p - lam0² ηs) m` (`saddlePin_eq_scaled`), so `Z x = ± arcZ ηs (Im (Z x)²)`
  (`pin_eq_arc`); injectivity of `Z` on the source (`hZinj`) turns `x` into the arc point
  `arcUpPt`/`arcDnPt`, i.e. `x = γ i (τU w)` / `γ i (τL w)`, and there `A x = C (τU w)` and the
  polar point of the profile at the prescribed angle is exactly the model arc point
  (`Work.Drive.N2Lead.polarArc_eq_sqrt`, whose two clauses are the rows `hrArcU` and `hrArcL`), while
  `saddlePsi ηs δ` is the identity on the anchor level
  (`saddleCollar_aux_saddlePsi_eq_self_of_re_sq_neg_eta`);
* `hAoff`: for `θ x < 1` at the anchor level, `x` is either on another component (a parked circle,
  of norm `≥ 19`, so that `c₀ + 2 * ηs < 361 ≤ ‖A x‖ ^ 2`), or on `γ i` at a parameter `t` whose
  class modulo the period `1` of `γ i` is disjoint from the `ℤ`-orbits of `τU '' [-m, m]` and
  `τL '' [-m, m]` (otherwise `θ x = 1`), where the bridge row `hoff` gives
  `c₀ + 2 * ηs < r (Θ t) ^ 2 = ‖A x‖ ^ 2`; `hoff` is quantified modulo that period (the excluded
  parameters are the full `ℤ`-orbits, else `t := τU 0 + 1` would force `c₀ < 0`). -/
theorem saddlePacketRows {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f) {p : M}
    (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ}
    {lam0 ηs δ c₀ m R : ℝ} {n : ℕ}
    (L : Work.Drive.N2C.LevelCurves f (f p - lam0 ^ 2 * ηs) n) (i : Fin n)
    {r Θ τU τL : ℝ → ℝ}
    (hreg : ∀ x : M, f x = f p - lam0 ^ 2 * ηs → ¬ Work.Drive.Morse.IsCritical f x)
    (hlam0pos : 0 < lam0) (hlam0 : lam0 = D.ρ D.j / 8)
    (hZrel : ∀ x : M, Work.Drive.N2Lead.chartCplx D x = (lam0 : ℂ) * Z x)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re)
    (hZinj : ∀ x ∈ (D.φ D.j).source, ∀ y ∈ (D.φ D.j).source, Z x = Z y → x = y)
    (hηs : 0 < ηs) (hηs1 : ηs < 1 / 10) (hδ : 0 < δ) (hδ1 : δ < 1 / 10)
    (hm : 1 < m) (hm2 : m < 2) (hR : 2 ≤ R) (hR19 : R < 19)
    (hc19 : c₀ + 2 * ηs < 19 ^ 2)
    (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r) (hrpos : ∀ φ : ℝ, 0 < r φ)
    (hrper : ∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ) (hrR : ∀ φ : ℝ, r φ ≤ R)
    (hrArcU : ∀ w ∈ Set.Icc (-m) m,
      r (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))
        = Real.sqrt (ηs / -Real.cos (2 * (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs)))))
    (hrArcL : ∀ w ∈ Set.Icc (-m) m,
      r (-(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))
        = Real.sqrt (ηs / -Real.cos (2 * (-(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs)))))
    (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ) (hΘmono : StrictMono Θ)
    (hΘderiv : ∀ t : ℝ, deriv Θ t ≠ 0) (hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi)
    (hΘU : ∀ w ∈ Set.Icc (-m) m, Θ (τU w) = Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))
    (hΘL : ∀ w ∈ Set.Icc (-m) m, Θ (τL w) = -(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))
    (hτU : ∀ w ∈ Set.Icc (-m) m, L.γ i (τU w) = Work.Drive.N2Lead.arcUpPt D lam0 ηs w)
    (hτL : ∀ w ∈ Set.Icc (-m) m, L.γ i (τL w) = Work.Drive.N2Lead.arcDnPt D lam0 ηs w)
    (hpinNorm : ∀ w ∈ Set.Icc (-m) m, ‖Work.Drive.N2Lead.arcZ ηs w‖ < 8)
    (hoff : ∀ t : ℝ, (∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τU w + k) →
      (∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τL w + k) → c₀ + 2 * ηs < r (Θ t) ^ 2) :
    ∃ A : M → EuclideanSpace ℝ (Fin 3),
      (∀ x : M, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A x) ∧
      (∀ x y : M, f x = f p - lam0 ^ 2 * ηs → f y = f p - lam0 ^ 2 * ηs → A x = A y → x = y) ∧
      (∀ x : M, f x = f p - lam0 ^ 2 * ηs → ∀ v : TangentSpace (𝓡 2) x,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
        mfderiv (𝓡 2) (𝓡 3) A x v = 0 → v = 0) ∧
      (∀ x : M, f x = f p - lam0 ^ 2 * ηs → Work.Drive.N2Lead.pinTheta D Z m x = 1 →
        A x = Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi ηs δ (Z x))) ∧
      (∀ x : M, f x = f p - lam0 ^ 2 * ηs → Work.Drive.N2Lead.pinTheta D Z m x < 1 →
        (A x) 2 ≠ 0 ∨ c₀ + 2 * ηs < ‖A x‖ ^ 2) := by
  classical
  -- ## the marked polar curve and the packet family of curves
  let C : ℝ → EuclideanSpace ℝ (Fin 3) :=
    fun t => Work.Drive.N2.cE3 (r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))
  obtain ⟨hCsm, hCper, hCinj, hCder, hCnorm⟩ :=
    saddleMarkedCurve (r := r) (Θ := Θ) (R := R) hr hrpos hrper hrR hΘ hΘmono hΘderiv hΘper
  let c : Fin n → ℝ → EuclideanSpace ℝ (Fin 3) :=
    fun j => if j = i then C else farCurve n j
  have hci : c i = C := by
    show (if i = i then C else farCurve n i) = C
    rw [if_pos rfl]
  have hcj : ∀ j : Fin n, j ≠ i → c j = farCurve n j := by
    intro j hj
    show (if j = i then C else farCurve n j) = farCurve n j
    rw [if_neg hj]
  have hcsm : ∀ j : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c j) := by
    intro j
    by_cases hj : j = i
    · have hji : c j = C := by
        show (if j = i then C else farCurve n j) = C
        rw [if_pos hj]
      rw [hji]; exact hCsm
    · rw [hcj j hj]; exact farCurve_contDiff n j
  have hcper : ∀ (j : Fin n) (t : ℝ), c j (t + 1) = c j t := by
    intro j t
    by_cases hj : j = i
    · have hji : c j = C := by
        show (if j = i then C else farCurve n j) = C
        rw [if_pos hj]
      rw [hji]
      show Work.Drive.N2.cE3 (r (Θ (t + 1))
          * Complex.exp (((Θ (t + 1) : ℝ) : ℂ) * Complex.I))
        = Work.Drive.N2.cE3 (r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))
      rw [hCper t]
    · rw [hcj j hj]; exact farCurve_period n j t
  have hcinj : ∀ (j k : Fin n) (s t : ℝ), c j s = c k t → j = k ∧ ∃ m : ℤ, s = t + m := by
    intro j k s t hst
    change (if j = i then C else farCurve n j) s = (if k = i then C else farCurve n k) t at hst
    by_cases hj : j = i
    · rw [if_pos hj] at hst
      by_cases hk : k = i
      · rw [if_pos hk] at hst
        exact ⟨hj.trans hk.symm, hCinj s t (Work.Drive.N2.cE3_injective hst)⟩
      · rw [if_neg hk] at hst
        exact absurd hst (marked_far_ne hCnorm hR19 s t)
    · rw [if_neg hj] at hst
      by_cases hk : k = i
      · rw [if_pos hk] at hst
        exact absurd hst.symm (marked_far_ne hCnorm hR19 t s)
      · rw [if_neg hk] at hst
        exact farCurve_inj hst
  have hcder : ∀ (j : Fin n) (t : ℝ), deriv (c j) t ≠ 0 := by
    intro j t
    by_cases hj : j = i
    · have hji : c j = C := by
        show (if j = i then C else farCurve n j) = C
        rw [if_pos hj]
      rw [hji]; exact hCder t
    · rw [hcj j hj]; exact deriv_farCurve_ne_zero n j t
  -- ## the anchor picture
  obtain ⟨A, hAsm, hAcurve, hAinj, hAimm⟩ :=
    packetPicture (f := f) (a := f p - lam0 ^ 2 * ηs) (n := n) (c := c) L hf hreg
      hcsm hcper hcinj hcder
  refine ⟨A, fun x => hAsm.contMDiffAt, hAinj, hAimm, ?_, ?_⟩
  · -- ## the pin row
    intro x hxf hθ1
    have hxsrc : x ∈ (D.φ D.j).source := by
      by_contra hx
      rw [pinTheta_apply_of_notMem D (Z := Z) (m := m) hx] at hθ1
      norm_num at hθ1
    obtain ⟨himle, hnorm4⟩ := (pinTheta_eq_one_iff D hm2 hxsrc).mp hθ1
    have hre : ((Z x) ^ 2).re = -ηs := by
      have h := hlev x hxsrc
      rw [hxf] at h
      have h2 : lam0 ^ 2 * ((Z x) ^ 2).re = lam0 ^ 2 * (-ηs) := by linarith
      exact mul_left_cancel₀ (by positivity : (lam0 : ℝ) ^ 2 ≠ 0) h2
    have hPsi : Work.Drive.N2.saddlePsi ηs δ (Z x) = Z x :=
      Work.Drive.N2.saddlePsi_eq_self_of_re_sq_neg_eta hηs hδ (by linarith) hre
    have hn8 : ‖Z x‖ < 8 := by nlinarith [norm_nonneg (Z x), hnorm4]
    have hxpin : x ∈ saddlePin D (f p - lam0 ^ 2 * ηs) m := by
      rw [saddlePin_eq_scaled D hlam0pos hlam0 hZrel]
      exact ⟨hxsrc, hn8, hxf, himle⟩
    have hwIcc : ((Z x) ^ 2).im ∈ Set.Icc (-m) m := abs_le.mp himle
    have hball := hpinNorm _ hwIcc
    have hyup : arcUpPt D lam0 ηs ((Z x) ^ 2).im ∈ (D.φ D.j).source :=
      arcUpPt_mem_source D hball hlam0
    have hydn : arcDnPt D lam0 ηs ((Z x) ^ 2).im ∈ (D.φ D.j).source :=
      arcDnPt_mem_source D hball hlam0pos hlam0
    rw [hPsi]
    rcases pin_eq_arc D hlam0pos hlam0 hZrel hlev hxpin with harc | harc
    · -- the upper arc
      rw [harc]
      have hy : Z (arcUpPt D lam0 ηs ((Z x) ^ 2).im) = Z x := by
        rw [Z_arcUpPt D hball hlam0pos hlam0 hZrel]
        exact harc.symm
      have hxy : arcUpPt D lam0 ηs ((Z x) ^ 2).im = x := hZinj _ hyup x hxsrc hy
      have hval : r (Θ (τU ((Z x) ^ 2).im))
            * Complex.exp (((Θ (τU ((Z x) ^ 2).im) : ℝ) : ℂ) * Complex.I)
          = arcZ ηs ((Z x) ^ 2).im := by
        rw [hΘU _ hwIcc, hrArcU _ hwIcc, arcZ]
        exact (polarArc_eq_sqrt hηs ((Z x) ^ 2).im).1
      calc A x = A (arcUpPt D lam0 ηs ((Z x) ^ 2).im) := by rw [hxy]
        _ = A (L.γ i (τU ((Z x) ^ 2).im)) := by rw [← hτU ((Z x) ^ 2).im hwIcc]
        _ = c i (τU ((Z x) ^ 2).im) := hAcurve i _
        _ = C (τU ((Z x) ^ 2).im) := by rw [hci]
        _ = Work.Drive.N2.cE3 (arcZ ηs ((Z x) ^ 2).im) := by
              show Work.Drive.N2.cE3 (r (Θ (τU ((Z x) ^ 2).im))
                * Complex.exp (((Θ (τU ((Z x) ^ 2).im) : ℝ) : ℂ) * Complex.I)) = _
              rw [hval]
    · -- the lower arc
      rw [harc]
      have hy : Z (arcDnPt D lam0 ηs ((Z x) ^ 2).im) = Z x := by
        rw [Work.Drive.N2C.Z_arcDnPt D hball hlam0pos hlam0 hZrel]
        exact harc.symm
      have hxy : arcDnPt D lam0 ηs ((Z x) ^ 2).im = x := hZinj _ hydn x hxsrc hy
      have hval : r (Θ (τL ((Z x) ^ 2).im))
            * Complex.exp (((Θ (τL ((Z x) ^ 2).im) : ℝ) : ℂ) * Complex.I)
          = -arcZ ηs ((Z x) ^ 2).im := by
        rw [hΘL _ hwIcc, hrArcL _ hwIcc, arcZ]
        exact (polarArc_eq_sqrt hηs ((Z x) ^ 2).im).2.1
      calc A x = A (arcDnPt D lam0 ηs ((Z x) ^ 2).im) := by rw [hxy]
        _ = A (L.γ i (τL ((Z x) ^ 2).im)) := by rw [← hτL ((Z x) ^ 2).im hwIcc]
        _ = c i (τL ((Z x) ^ 2).im) := hAcurve i _
        _ = C (τL ((Z x) ^ 2).im) := by rw [hci]
        _ = Work.Drive.N2.cE3 (-arcZ ηs ((Z x) ^ 2).im) := by
              show Work.Drive.N2.cE3 (r (Θ (τL ((Z x) ^ 2).im))
                * Complex.exp (((Θ (τL ((Z x) ^ 2).im) : ℝ) : ℂ) * Complex.I)) = _
              rw [hval]
  · -- ## the off-pin row
    intro x hxf hθlt
    obtain ⟨j, t, hxt⟩ := L.cover x hxf
    have hAx : A x = c j t := by rw [hxt]; exact hAcurve j t
    by_cases hji : j = i
    · -- the marked component: the parameter avoids the two arcs
      have hjc : c j = C := by rw [hji]; exact hci
      have hnotU : ∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τU w + k := by
        intro w k hw ht
        have hxarc : x = arcUpPt D lam0 ηs w := by
          rw [hxt, ht, levelCurves_gamma_add_int L j k (τU w), hji]
          exact hτU w hw
        have h1 : pinTheta D Z m x = 1 := by
          rw [hxarc]
          exact pinTheta_arcUpPt D hlam0pos hlam0 hZrel hm hm2 hηs hηs1
            (hpinNorm w hw) (abs_le.mpr hw)
        exact absurd h1 (ne_of_lt hθlt)
      have hnotL : ∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τL w + k := by
        intro w k hw ht
        have hxarc : x = arcDnPt D lam0 ηs w := by
          rw [hxt, ht, levelCurves_gamma_add_int L j k (τL w), hji]
          exact hτL w hw
        have h1 : pinTheta D Z m x = 1 := by
          rw [hxarc]
          exact pinTheta_arcDnPt D hlam0pos hlam0 hZrel hm hm2 hηs hηs1
            (hpinNorm w hw) (abs_le.mpr hw)
        exact absurd h1 (ne_of_lt hθlt)
      right
      have hbr := hoff t hnotU hnotL
      have hnorm : ‖C t‖ ^ 2 = r (Θ t) ^ 2 := by
        have h1 : ‖C t‖ = r (Θ t) := by
          show ‖Work.Drive.N2.cE3 (r (Θ t)
            * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))‖ = r (Θ t)
          rw [norm_cE3_marked, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
            Complex.norm_of_nonneg (le_of_lt (hrpos (Θ t)))]
        rw [h1]
      rw [hAx, hjc, hnorm]
      exact hbr
    · -- another component: a parked circle, whose third coordinate is `1`
      left
      rw [hAx, hcj j hji, farCurve_apply_two]
      norm_num

end Work.Drive.N2Lead
