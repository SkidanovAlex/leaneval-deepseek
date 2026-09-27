import Mathlib
import Submission.Work.Drive.N2Lead.angleFunction
import Submission.Work.Drive.N2Lead.exists_psi_of_arc
import Submission.Work.Drive.N2Lead.exists_strictMono_extension
import Submission.Work.Drive.N2C.arcLiftSaddle

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology in
open Set Filter in
/-- **The angle function of the saddle packet (split case).**  From the two arc lifts `τU`, `τL` of
`Work.Drive.N2C.exists_arcReparam_up` / `exists_arcReparam_dn` — both strictly *antitone* on
`Ioo (-3) 3` (the split case: the two arcs are traversed in the same `w`-direction), with the four
endpoints in cyclic order — produce the `1`-periodic angle function `Θ` of the packet: `C^∞`, strictly
increasing, `deriv Θ ≠ 0`, `Θ (t + 1) = Θ t + 2 π`, and with the two prescriptions

* `Θ (τU w) = π/2 - (1/2) arctan (w/ηs)` (the argument of the model arc `arcZ ηs w`),
* `Θ (τL w) = -π/2 - (1/2) arctan (w/ηs)` (the argument of `-arcZ ηs w`)

for `|w| ≤ m`.  The engine is `Work.Drive.N2Lead.angleFunction_periodOne`; the two prescriptions
are made global by extending the arc lifts (`Work.Drive.N2Lead.exists_strictMono_extension`,
`Work.Drive.N2Lead.exists_contDiff_extension_of_Icc`) and `Work.Drive.N2Lead.exists_psi_of_arc`
(`ε = δ = -1`, both decreasing), and the four cyclic-order inequalities of the values follow from
`arctan (m/ηs) ∈ (0, π/2)`.

This is the input `hΘU`/`hΘL` of `Work.Drive.N2Lead.saddlePacketRows` (and, through `saddleMarkedCurve`,
the marked curve of the packet). -/
theorem saddleAngleFunction {ηs m : ℝ} (hηs : 0 < ηs) (hm : 0 < m) (hm3 : m < 3)
    {τU τL : ℝ → ℝ}
    (hτUsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τU (Set.Ioo (-3) 3))
    (hτUd : ∀ w ∈ Set.Ioo (-3) 3, deriv τU w ≠ 0)
    (hτUanti : StrictAntiOn τU (Set.Ioo (-3) 3))
    (hτLsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τL (Set.Ioo (-3) 3))
    (hτLd : ∀ w ∈ Set.Ioo (-3) 3, deriv τL w ≠ 0)
    (hτLanti : StrictAntiOn τL (Set.Ioo (-3) 3))
    (hord : τL m < τL (-m) ∧ τL (-m) < τU m ∧ τU m < τU (-m) ∧ τU (-m) < τL m + 1) :
    ∃ Θ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧ StrictMono Θ ∧
      (∀ t : ℝ, deriv Θ t ≠ 0) ∧ (∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi) ∧
      (∀ w ∈ Set.Icc (-m) m, Θ (τU w) = Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs)) ∧
      (∀ w ∈ Set.Icc (-m) m, Θ (τL w) = -(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs)) := by
  classical
  have hmm : -m < m := by linarith
  have hIcc_sub : Set.Icc (-m) m ⊆ Set.Ioo (-3 : ℝ) 3 := by
    intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- ### The arcs are strictly decreasing on `(-3,3)`
  have hderUn : ∀ w ∈ Set.Ioo (-3 : ℝ) 3, deriv τU w < 0 := by
    intro w hw
    have h1 : derivWithin τU (Set.Ioo (-3 : ℝ) 3) w ≤ 0 :=
      (hτUanti.antitoneOn).derivWithin_nonpos
    rw [derivWithin_of_isOpen isOpen_Ioo hw] at h1
    exact lt_of_le_of_ne h1 (hτUd w hw)
  have hderLn : ∀ w ∈ Set.Ioo (-3 : ℝ) 3, deriv τL w < 0 := by
    intro w hw
    have h1 : derivWithin τL (Set.Ioo (-3 : ℝ) 3) w ≤ 0 :=
      (hτLanti.antitoneOn).derivWithin_nonpos
    rw [derivWithin_of_isOpen isOpen_Ioo hw] at h1
    exact lt_of_le_of_ne h1 (hτLd w hw)
  -- ### Globalise the two arc lifts
  obtain ⟨αU, hαUsm, hαUval, hαUder⟩ :=
    exists_contDiff_extension_of_Icc (J := Set.Ioo (-3 : ℝ) 3) isOpen_Ioo hIcc_sub hτUsm hmm
  obtain ⟨αL, hαLsm, hαLval, hαLder⟩ :=
    exists_contDiff_extension_of_Icc (J := Set.Ioo (-3 : ℝ) 3) isOpen_Ioo hIcc_sub hτLsm hmm
  have hαUn : ∀ s : ℝ, |s| ≤ m → deriv αU s < 0 := by
    intro s hs
    have hsI : s ∈ Set.Icc (-m) m := abs_le.mp hs
    rw [hαUder s hsI]
    exact hderUn s (hIcc_sub hsI)
  have hαLn : ∀ s : ℝ, |s| ≤ m → deriv αL s < 0 := by
    intro s hs
    have hsI : s ∈ Set.Icc (-m) m := abs_le.mp hs
    rw [hαLder s hsI]
    exact hderLn s (hIcc_sub hsI)
  -- ### The two model prescriptions
  set ϑU : ℝ → ℝ := fun w : ℝ => Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs) with hϑU
  set ϑL : ℝ → ℝ := fun w : ℝ => -(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs) with hϑL
  have hϑU' : ∀ w : ℝ, ϑU w = Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs) :=
    fun w => by rw [hϑU]
  have hϑL' : ∀ w : ℝ, ϑL w = -(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs) :=
    fun w => by rw [hϑL]
  have hϑUsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ϑU := by
    rw [hϑU]
    exact contDiff_const.sub (contDiff_const.mul (Real.contDiff_arctan.comp (by fun_prop)))
  have hϑLsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ϑL := by
    rw [hϑL]
    exact contDiff_const.sub (contDiff_const.mul (Real.contDiff_arctan.comp (by fun_prop)))
  have hϑUn : ∀ s : ℝ, |s| ≤ m → deriv ϑU s < 0 := by
    intro s hs
    have hinner : HasDerivAt (fun t : ℝ => t / ηs) (1 / ηs) s := by
      simpa using (hasDerivAt_id s).div_const ηs
    have hcomp : HasDerivAt (fun t : ℝ => Real.arctan (t / ηs))
        ((1 + (s / ηs) ^ 2)⁻¹ * (1 / ηs)) s := by
      simpa [Function.comp_def] using (Real.hasDerivAt_arctan' (s / ηs)).comp s hinner
    have hmain : HasDerivAt (fun w : ℝ => Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))
        (-(1 / 2 * ((1 + (s / ηs) ^ 2)⁻¹ * (1 / ηs)))) s :=
      HasDerivAt.const_sub (Real.pi / 2) (hcomp.const_mul (1 / 2))
    rw [hϑU, hmain.deriv]
    have hpos : 0 < (1 + (s / ηs) ^ 2)⁻¹ * (1 / ηs) := by positivity
    linarith
  have hϑLn : ∀ s : ℝ, |s| ≤ m → deriv ϑL s < 0 := by
    intro s hs
    have hinner : HasDerivAt (fun t : ℝ => t / ηs) (1 / ηs) s := by
      simpa using (hasDerivAt_id s).div_const ηs
    have hcomp : HasDerivAt (fun t : ℝ => Real.arctan (t / ηs))
        ((1 + (s / ηs) ^ 2)⁻¹ * (1 / ηs)) s := by
      simpa [Function.comp_def] using (Real.hasDerivAt_arctan' (s / ηs)).comp s hinner
    have hmain : HasDerivAt (fun w : ℝ => -(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))
        (-(1 / 2 * ((1 + (s / ηs) ^ 2)⁻¹ * (1 / ηs)))) s :=
      HasDerivAt.const_sub (-(Real.pi / 2)) (hcomp.const_mul (1 / 2))
    rw [hϑL, hmain.deriv]
    have hpos : 0 < (1 + (s / ηs) ^ 2)⁻¹ * (1 / ηs) := by positivity
    linarith
  -- ### The two globally increasing functions prescribed on the arcs
  obtain ⟨ψU, hψUsm, hψUder, hψUeq⟩ :=
    exists_psi_of_arc (ε := -1) (δ := -1) (L := m)
      hm hαUsm hϑUsm (Or.inr rfl) (Or.inr rfl)
      (fun s hs => by have := hαUn s hs; linarith)
      (fun s hs => by have := hϑUn s hs; linarith)
  obtain ⟨ψL, hψLsm, hψLder, hψLeq⟩ :=
    exists_psi_of_arc (ε := -1) (δ := -1) (L := m)
      hm hαLsm hϑLsm (Or.inr rfl) (Or.inr rfl)
      (fun s hs => by have := hαLn s hs; linarith)
      (fun s hs => by have := hϑLn s hs; linarith)
  have hψUpos : ∀ x : ℝ, 0 < deriv ψU x := by
    intro x; have := hψUder x; simpa using this
  have hψLpos : ∀ x : ℝ, 0 < deriv ψL x := by
    intro x; have := hψLder x; simpa using this
  -- ### The four endpoint values
  have hmI : m ∈ Set.Icc (-m) m := ⟨by linarith, le_rfl⟩
  have hnmI : -m ∈ Set.Icc (-m) m := ⟨le_rfl, by linarith⟩
  have hψUm : ψU (τU m) = ϑU m := by
    have h := hψUeq m (by rw [abs_le]; exact ⟨by linarith, le_rfl⟩)
    rwa [hαUval m hmI] at h
  have hψUnm : ψU (τU (-m)) = ϑU (-m) := by
    have h := hψUeq (-m) (by rw [abs_le]; exact ⟨by linarith, by linarith⟩)
    rwa [hαUval (-m) hnmI] at h
  have hψLm : ψL (τL m) = ϑL m := by
    have h := hψLeq m (by rw [abs_le]; exact ⟨by linarith, le_rfl⟩)
    rwa [hαLval m hmI] at h
  have hψLnm : ψL (τL (-m)) = ϑL (-m) := by
    have h := hψLeq (-m) (by rw [abs_le]; exact ⟨by linarith, by linarith⟩)
    rwa [hαLval (-m) hnmI] at h
  have htpos : 0 < Real.arctan (m / ηs) := Real.arctan_pos.mpr (div_pos hm hηs)
  have htpi' : Real.arctan (m / ηs) < Real.pi := by
    have := Real.arctan_lt_pi_div_two (m / ηs); linarith [Real.pi_pos]
  have harm : Real.arctan ((-m) / ηs) = -Real.arctan (m / ηs) := by
    rw [show (-m) / ηs = -(m / ηs) by ring, Real.arctan_neg]
  have hUi : ϑU m = Real.pi / 2 - (1 / 2) * Real.arctan (m / ηs) := hϑU' m
  have hUin : ϑU (-m) = Real.pi / 2 + (1 / 2) * Real.arctan (m / ηs) := by
    rw [hϑU', harm]; ring
  have hLi : ϑL m = -(Real.pi / 2) - (1 / 2) * Real.arctan (m / ηs) := hϑL' m
  have hLin : ϑL (-m) = -(Real.pi / 2) + (1 / 2) * Real.arctan (m / ηs) := by
    rw [hϑL', harm]; ring
  -- ### The cyclic order of the four values
  have hAB : ϑL m < ϑL (-m) := by rw [hLi, hLin]; linarith [htpos]
  have hBC : ϑL (-m) < ϑU m := by rw [hLin, hUi]; linarith [htpi']
  have hCD : ϑU m < ϑU (-m) := by rw [hUi, hUin]; linarith [htpos]
  have hDA : ϑU (-m) < ϑL m + 2 * Real.pi := by rw [hUin, hLi]; linarith [htpi']
  -- ### The engine
  obtain ⟨Θ, hΘsm, hΘder, hΘper, hΘLrec, hΘUrec⟩ :=
    angleFunction_periodOne (a := τL m) (b := τL (-m)) (c := τU m)
      (d := τU (-m)) (A := ϑL m) (B := ϑL (-m)) (C := ϑU m) (D := ϑU (-m))
      hord.1 hord.2.1 hord.2.2.1 hord.2.2.2 hAB hBC hCD hDA
      hψLsm hψLpos hψUsm hψUpos hψLm hψLnm hψUm hψUnm
  refine ⟨Θ, hΘsm, strictMono_of_deriv_pos hΘder, fun t => ne_of_gt (hΘder t), hΘper, ?_, ?_⟩
  · intro w hw
    have hmem : τU w ∈ Set.Icc (τU m) (τU (-m)) := by
      have himg : τU '' Set.Icc (-m) m = Set.Icc (τU m) (τU (-m)) :=
        ContinuousOn.image_Icc_of_antitoneOn (by linarith)
          (hτUsm.continuousOn.mono hIcc_sub) (hτUanti.antitoneOn.mono hIcc_sub)
      rw [← himg]; exact ⟨w, hw, rfl⟩
    rw [hΘUrec (τU w) hmem, ← hαUval w hw, hψUeq w (abs_le.mpr hw), hϑU' w]
  · intro w hw
    have hmem : τL w ∈ Set.Icc (τL m) (τL (-m)) := by
      have himg : τL '' Set.Icc (-m) m = Set.Icc (τL m) (τL (-m)) :=
        ContinuousOn.image_Icc_of_antitoneOn (by linarith)
          (hτLsm.continuousOn.mono hIcc_sub) (hτLanti.antitoneOn.mono hIcc_sub)
      rw [← himg]; exact ⟨w, hw, rfl⟩
    rw [hΘLrec (τL w) hmem, ← hαLval w hw, hψLeq w (abs_le.mpr hw), hϑL' w]

end Work.Drive.N2Lead
