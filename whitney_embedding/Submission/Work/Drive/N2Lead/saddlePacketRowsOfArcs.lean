import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.saddleWindowBlock
import Submission.Work.Drive.N2Lead.saddlePacket
import Submission.Work.Drive.N2Lead.saddleMarkedCurve
import Submission.Work.Drive.N2Lead.saddlePinFunction
import Submission.Work.Drive.N2Lead.saddleArcs
import Submission.Work.Drive.N2Lead.saddlePacketRows
import Submission.Work.Drive.N2.modelBall

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-- The squared modulus of the model arc point is at most `4`, for `0 < ηs < 1/10` and `|w| ≤ m`
with `1 < m < 2`.  This is the norm row that makes `pinChi (‖Z ·‖²) = 1` on the anchor arcs. -/
lemma arcZ_normSq_le_four {ηs m w : ℝ} (hηs : 0 < ηs) (hηs1 : ηs < 1 / 10)
    (hm : 1 < m) (hm2 : m < 2) (hw : w ∈ Set.Icc (-m) m) : ‖arcZ ηs w‖ ^ 2 ≤ 4 := by
  rw [norm_arcZ_sq]
  have hsum : ηs ^ 2 + w ^ 2 ≤ 16 := by nlinarith [hηs, hηs1, hm, hm2, hw.1, hw.2]
  calc Real.sqrt (ηs ^ 2 + w ^ 2) ≤ Real.sqrt 16 := Real.sqrt_le_sqrt hsum
    _ = 4 := by norm_num

/-- **The pin function equals `1` at the upper anchor arc** (`Z (αU w) = arcZ ηs w`), for
`|w| ≤ m`: the two factors `pinBeta` and `pinChi` are both `1`. -/
lemma pinTheta_arcU {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ} {ηs m w : ℝ}
    {αU : ℝ → M}
    (hηs : 0 < ηs) (hηs1 : ηs < 1 / 10) (hm : 1 < m) (hm2 : m < 2)
    (hsrc : αU w ∈ (D.φ D.j).source) (hZ : Z (αU w) = arcZ ηs w)
    (hw : w ∈ Set.Icc (-m) m) : pinTheta D Z m (αU w) = 1 := by
  rw [pinTheta_eq_one_iff D hm2 hsrc]
  refine ⟨?_, ?_⟩
  · rw [hZ, arcZ_sq_im]
    exact abs_le.mpr hw
  · rw [hZ]
    exact arcZ_normSq_le_four hηs hηs1 hm hm2 hw

/-- **The pin function equals `1` at the lower anchor arc** (`Z (αD w) = -arcZ ηs w`). -/
lemma pinTheta_arcD {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ} {ηs m w : ℝ}
    {αD : ℝ → M}
    (hηs : 0 < ηs) (hηs1 : ηs < 1 / 10) (hm : 1 < m) (hm2 : m < 2)
    (hsrc : αD w ∈ (D.φ D.j).source) (hZ : Z (αD w) = -arcZ ηs w)
    (hw : w ∈ Set.Icc (-m) m) : pinTheta D Z m (αD w) = 1 := by
  rw [pinTheta_eq_one_iff D hm2 hsrc]
  refine ⟨?_, ?_⟩
  · rw [hZ, neg_sq, arcZ_sq_im]
    exact abs_le.mpr hw
  · rw [hZ, norm_neg]
    exact arcZ_normSq_le_four hηs hηs1 hm hm2 hw

end

open scoped Manifold ContDiff Topology in
open Set Filter in
/-- **The packet rows of the saddle window, in sign-free (abstract-arc) form.**  This is
`Work.Drive.N2Lead.saddlePacketRows` with the two arc families supplied *abstractly* — `αU`, `αD` are
the anchor arcs through the `Z`-coordinate (`Z (αU w) = arcZ ηs w`, `Z (αD w) = -arcZ ηs w`) and the
pin is described by the dictionary `hpinZ` — instead of through the datum chart `D.φ D.j`.

The point is `Submission/Work/Drive/N2/NOTES_dichotomy_hspan_and_packet.md` §3: `saddlePack`'s `Z`
satisfies the *level* law `f = f p + lam0 ^ 2 * Re (Z ·) ^ 2` in both sign cases `s₁ = ±1`, but the
relation to the datum chart is `chartCplx = lam0 * Z` in the `s₁ = 1` case and
`chartCplx = -(I * lam0) * Z` in the `s₁ = -1` case.  The pin condition `|Im (Z ·) ^ 2| ≤ m` and the
level condition are *the same in both cases* (a rotation of `Z` flips both `Re` and `Im` of `Z ^ 2`
simultaneously), so the whole packet argument is sign-free once stated in terms of `Z` and the arc
points, which is what this statement does.

The five rows are the ones consumed by `Work.Drive.N2Lead.saddleWindow_of_packet_band_off` (with
`c := f p`, `lam := lam0 ^ 2`, `η := ηs`, `θ := pinTheta D Z m`); the picture is built from the polar
curve `t ↦ cE3 (r (Θ t) * exp (i Θ t))` on the marked component and the parked circles on the
others.  Compare `Work.Drive.N2Lead.saddlePacketRows` (the `chartCplx = lam0 * Z` form, PROVED), whose
proof is the template: the only changes are that `hpinZ` replaces `hZrel`, that the arc-source rows
`hαsrcU`/`hαsrcD` replace `hpinNorm` (they are what makes `pinTheta (αU w) = 1`), and that
`pin_eq_arc` is re-derived from `hpinZ` and `hlev` (`(Z x) ^ 2 = -ηs + I * Im ((Z x) ^ 2)`), with no
chart involved. -/
theorem saddlePacketRowsOfArcs {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f) {p : M}
    (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ}
    {lam0 ηs δ c₀ m R : ℝ} {n : ℕ}
    (L : Work.Drive.N2C.LevelCurves f (f p - lam0 ^ 2 * ηs) n) (i : Fin n)
    {r Θ τU τL : ℝ → ℝ} {αU αD : ℝ → M}
    (hreg : ∀ x : M, f x = f p - lam0 ^ 2 * ηs → ¬ Work.Drive.Morse.IsCritical f x)
    (hlam0pos : 0 < lam0)
    (hZsm : ∀ x ∈ (D.φ D.j).source,
      ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z x)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re)
    (hpinZ : ∀ x : M, x ∈ Work.Drive.N2Lead.saddlePin D (f p - lam0 ^ 2 * ηs) m ↔
      x ∈ (D.φ D.j).source ∧ ‖Z x‖ < 8 ∧ f x = f p - lam0 ^ 2 * ηs ∧ |((Z x) ^ 2).im| ≤ m)
    (hZinj : ∀ w ∈ Set.Icc (-m) m, ∀ x ∈ (D.φ D.j).source, Z x = Z (αU w) → x = αU w)
    (hZinjD : ∀ w ∈ Set.Icc (-m) m, ∀ x ∈ (D.φ D.j).source, Z x = Z (αD w) → x = αD w)
    (hαsrcU : ∀ w ∈ Set.Icc (-m) m, αU w ∈ (D.φ D.j).source)
    (hαsrcD : ∀ w ∈ Set.Icc (-m) m, αD w ∈ (D.φ D.j).source)
    (hZU : ∀ w ∈ Set.Icc (-m) m, Z (αU w) = Work.Drive.N2Lead.arcZ ηs w)
    (hZD : ∀ w ∈ Set.Icc (-m) m, Z (αD w) = -Work.Drive.N2Lead.arcZ ηs w)
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
    (hτU : ∀ w ∈ Set.Icc (-m) m, L.γ i (τU w) = αU w)
    (hτL : ∀ w ∈ Set.Icc (-m) m, L.γ i (τL w) = αD w)
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
    obtain ⟨himle, _hnorm4⟩ := (pinTheta_eq_one_iff D hm2 hxsrc).mp hθ1
    have hre : ((Z x) ^ 2).re = -ηs := by
      have h := hlev x hxsrc
      rw [hxf] at h
      have h2 : lam0 ^ 2 * ((Z x) ^ 2).re = lam0 ^ 2 * (-ηs) := by linarith
      exact mul_left_cancel₀ (by positivity : (lam0 : ℝ) ^ 2 ≠ 0) h2
    have hPsi : Work.Drive.N2.saddlePsi ηs δ (Z x) = Z x :=
      Work.Drive.N2.saddlePsi_eq_self_of_re_sq_neg_eta hηs hδ (by linarith) hre
    have hwIcc : ((Z x) ^ 2).im ∈ Set.Icc (-m) m := abs_le.mp himle
    have hsq : (Z x) ^ 2 = (arcZ ηs (((Z x) ^ 2).im)) ^ 2 := by
      refine Complex.ext ?_ ?_
      · rw [hre, arcZ_sq_re]
      · rw [arcZ_sq_im]
    rw [hPsi]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with harc | harc
    · -- the upper arc
      have hy : Z (αU (((Z x) ^ 2).im)) = Z x := by
        rw [hZU _ hwIcc]; exact harc.symm
      have hxy : x = αU (((Z x) ^ 2).im) := hZinj _ hwIcc x hxsrc hy.symm
      have hval : r (Θ (τU (((Z x) ^ 2).im)))
            * Complex.exp (((Θ (τU (((Z x) ^ 2).im)) : ℝ) : ℂ) * Complex.I)
          = arcZ ηs (((Z x) ^ 2).im) := by
        rw [hΘU _ hwIcc, hrArcU _ hwIcc, arcZ]
        exact (polarArc_eq_sqrt hηs (((Z x) ^ 2).im)).1
      calc A x = A (αU (((Z x) ^ 2).im)) := congrArg A hxy
        _ = A (L.γ i (τU (((Z x) ^ 2).im))) := by rw [← hτU _ hwIcc]
        _ = c i (τU (((Z x) ^ 2).im)) := hAcurve i _
        _ = C (τU (((Z x) ^ 2).im)) := by rw [hci]
        _ = Work.Drive.N2.cE3 (arcZ ηs (((Z x) ^ 2).im)) := by
              show Work.Drive.N2.cE3 (r (Θ (τU (((Z x) ^ 2).im)))
                * Complex.exp (((Θ (τU (((Z x) ^ 2).im)) : ℝ) : ℂ) * Complex.I)) = _
              rw [hval]
        _ = Work.Drive.N2.cE3 (Z x) := congrArg Work.Drive.N2.cE3 harc.symm
    · -- the lower arc
      have hy : Z (αD (((Z x) ^ 2).im)) = Z x := by
        rw [hZD _ hwIcc]; exact harc.symm
      have hxy : x = αD (((Z x) ^ 2).im) := hZinjD _ hwIcc x hxsrc hy.symm
      have hval : r (Θ (τL (((Z x) ^ 2).im)))
            * Complex.exp (((Θ (τL (((Z x) ^ 2).im)) : ℝ) : ℂ) * Complex.I)
          = -arcZ ηs (((Z x) ^ 2).im) := by
        rw [hΘL _ hwIcc, hrArcL _ hwIcc, arcZ]
        exact (polarArc_eq_sqrt hηs (((Z x) ^ 2).im)).2.1
      calc A x = A (αD (((Z x) ^ 2).im)) := congrArg A hxy
        _ = A (L.γ i (τL (((Z x) ^ 2).im))) := by rw [← hτL _ hwIcc]
        _ = c i (τL (((Z x) ^ 2).im)) := hAcurve i _
        _ = C (τL (((Z x) ^ 2).im)) := by rw [hci]
        _ = Work.Drive.N2.cE3 (-arcZ ηs (((Z x) ^ 2).im)) := by
              show Work.Drive.N2.cE3 (r (Θ (τL (((Z x) ^ 2).im)))
                * Complex.exp (((Θ (τL (((Z x) ^ 2).im)) : ℝ) : ℂ) * Complex.I)) = _
              rw [hval]
        _ = Work.Drive.N2.cE3 (Z x) := congrArg Work.Drive.N2.cE3 harc.symm
  · -- ## the off-pin row
    intro x hxf hθlt
    obtain ⟨j, t, hxt⟩ := L.cover x hxf
    have hAx : A x = c j t := by rw [hxt]; exact hAcurve j t
    by_cases hji : j = i
    · -- the marked component: the parameter avoids the two arcs
      have hjc : c j = C := by rw [hji]; exact hci
      have hnotU : ∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τU w + k := by
        intro w k hw ht
        have hxarc : x = αU w := by
          rw [hxt, ht, levelCurves_gamma_add_int L j k (τU w), hji]
          exact hτU w hw
        have h1 : pinTheta D Z m x = 1 := by
          rw [hxarc]
          exact pinTheta_arcU D hηs hηs1 hm hm2 (hαsrcU w hw) (hZU w hw) hw
        exact absurd h1 (ne_of_lt hθlt)
      have hnotL : ∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τL w + k := by
        intro w k hw ht
        have hxarc : x = αD w := by
          rw [hxt, ht, levelCurves_gamma_add_int L j k (τL w), hji]
          exact hτL w hw
        have h1 : pinTheta D Z m x = 1 := by
          rw [hxarc]
          exact pinTheta_arcD D hηs hηs1 hm hm2 (hαsrcD w hw) (hZD w hw) hw
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
