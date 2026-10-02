import Mathlib
import Submission.Work.LANDCL.Defs
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.family_repelling_expansion
import Submission.Work.LandLeaves.rayAccum_entry
import Submission.Work.LandLeaves.critBottcher_injOn_critDomain
import Submission.Work.LandLeaves.critBottcher_image
import Submission.Work.LandLeaves.boundedOrbit_of_ball
import Submission.Work.Landing.Angle.angDouble_iterate_succ
import Submission.Work.Bottcher.Inverse.continuousOn_inverse_of_bottcher
import Submission.Work.Landing.Rays.rayDirection_eq_of_sub_int
import Submission.Work.LandLeaves.tantibar_family_continuous
import Submission.Work.LandLeaves.deriv_tantibar_family_continuous
import Submission.Work.NAKANE.All
import Submission.Work.SeedDyn.Main
import Submission.Work.ParamRaysCrit.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Set Classical
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-! ## The point of the critical ray at a given level -/

/-- A (junk-valued) right inverse of the critical Böttcher coordinate. -/
noncomputable def invVarphi (f : ℂ) (w : ℂ) : ℂ :=
  if h : ∃ z : ℂ, z ∈ Work.ParamRays.critDomain f ∧ Work.Bottcher.varphiCrit f z = w
  then Classical.choose h else 0

theorem invVarphi_spec {f w : ℂ}
    (h : ∃ z : ℂ, z ∈ Work.ParamRays.critDomain f ∧ Work.Bottcher.varphiCrit f z = w) :
    invVarphi f w ∈ Work.ParamRays.critDomain f ∧
      Work.Bottcher.varphiCrit f (invVarphi f w) = w := by
  rw [invVarphi, dif_pos h]
  exact Classical.choose_spec h

theorem exists_varphiCrit_eq {f w : ℂ}
    (hw : Real.exp (Work.ParamRays.greenFun f 0) < ‖w‖) :
    ∃ z : ℂ, z ∈ Work.ParamRays.critDomain f ∧ Work.Bottcher.varphiCrit f z = w := by
  have himg := Work.LandLeaves.critBottcher_image f
  have : w ∈ Work.Bottcher.varphiCrit f '' Work.ParamRays.critDomain f := by
    rw [himg]; exact hw
  obtain ⟨z, hz, hzw⟩ := this
  exact ⟨z, hz, hzw⟩

theorem invVarphi_spec_of_lt {f w : ℂ}
    (hw : Real.exp (Work.ParamRays.greenFun f 0) < ‖w‖) :
    invVarphi f w ∈ Work.ParamRays.critDomain f ∧
      Work.Bottcher.varphiCrit f (invVarphi f w) = w :=
  invVarphi_spec (exists_varphiCrit_eq hw)

theorem continuousOn_invVarphi (f : ℂ) :
    ContinuousOn (invVarphi f) {w : ℂ | Real.exp (Work.ParamRays.greenFun f 0) < ‖w‖} :=
  Work.Bottcher.Inverse.continuousOn_of_rightInverse (Work.ParamRays.isOpen_critDomain f)
    (Work.Bottcher.analyticOnNhd_varphiCrit f)
    (Work.LandLeaves.critBottcher_injOn_critDomain f)
    (fun w hw => invVarphi_spec_of_lt hw)

/-- The point of the critical ray of `T_f` at angle `θ` and level `t` (junk value when the
level is below the critical level `exp (G_f 0)`). -/
noncomputable def rayPt (f : ℂ) (θ : ℝ) (t : ℝ) : ℂ :=
  invVarphi f ((t : ℂ) * Work.ParamRays.rayDir θ)

theorem norm_rayPt_arg (t : ℝ) (θ : ℝ) (ht : 0 < t) :
    ‖(t : ℂ) * Work.ParamRays.rayDir θ‖ = t := by
  rw [norm_mul, Work.ParamRays.norm_rayDir, mul_one, Complex.norm_of_nonneg ht.le]

theorem rayPt_spec {f : ℂ} {θ t : ℝ} (ht : Real.exp (Work.ParamRays.greenFun f 0) < t) :
    rayPt f θ t ∈ Work.ParamRays.critDomain f ∧
      Work.Bottcher.varphiCrit f (rayPt f θ t) = (t : ℂ) * Work.ParamRays.rayDir θ := by
  have ht0 : 0 < t := lt_of_le_of_lt (Real.exp_pos _).le ht
  refine invVarphi_spec_of_lt ?_
  rw [norm_rayPt_arg t θ ht0]
  exact ht

theorem rayPt_unique {f : ℂ} {θ t : ℝ} {z : ℂ} (hz : z ∈ Work.ParamRays.critDomain f)
    (h : Work.Bottcher.varphiCrit f z = (t : ℂ) * Work.ParamRays.rayDir θ)
    (ht : Real.exp (Work.ParamRays.greenFun f 0) < t) : z = rayPt f θ t := by
  have h2 := (rayPt_spec (f := f) (θ := θ) (t := t) ht).2
  exact Work.LandLeaves.critBottcher_injOn_critDomain f hz (rayPt_spec (f := f) (θ := θ) ht).1
    (by rw [h, (rayPt_spec (f := f) (θ := θ) ht).2])

theorem continuousOn_rayPt (f : ℂ) (θ : ℝ) :
    ContinuousOn (fun t : ℝ => rayPt f θ t) (Set.Ioi (Real.exp (Work.ParamRays.greenFun f 0))) := by
  unfold rayPt
  refine (continuousOn_invVarphi f).comp ?_ ?_
  · fun_prop
  · intro t ht
    rw [Set.mem_setOf_eq, norm_rayPt_arg t θ (lt_of_le_of_lt (Real.exp_pos _).le ht)]
    exact ht

/-! ## Angle bookkeeping -/

theorem rayDir_eq_of_sub_int' {θ θ' : ℝ} (h : ∃ n : ℤ, θ' = θ + n) :
    Work.ParamRays.rayDir θ' = Work.ParamRays.rayDir θ :=
  Work.Landing.Rays.rayDirection_eq_of_sub_int h

theorem rayDir_pow (θ : ℝ) (n : ℕ) :
    (Work.ParamRays.rayDir θ) ^ n = Work.ParamRays.rayDir ((n : ℝ) * θ) := by
  have hz : Work.ParamRays.rayDir θ
      = Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) := rfl
  rw [hz, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem exists_int_sub_of_fract_eq {a b : ℝ} (h : Int.fract a = Int.fract b) :
    ∃ n : ℤ, a = b + n := by
  have key : a - (⌊a⌋ : ℝ) = b - (⌊b⌋ : ℝ) := by
    rw [Int.self_sub_floor a, Int.self_sub_floor b, h]
  exact ⟨⌊a⌋ - ⌊b⌋, by push_cast; linarith⟩

theorem rayDir_four_pow {θ : ℝ} {k q : ℕ}
    (hper : Work.Landing.PeriodicAngle (Int.fract θ) (2 * (k * q))) :
    Work.ParamRays.rayDir (((4 : ℝ) ^ (k * q)) * θ) = Work.ParamRays.rayDir θ := by
  rcases Nat.eq_zero_or_pos (k * q) with hkq | hkq
  · rw [hkq, pow_zero, one_mul]
  have h2 : 1 ≤ 2 * (k * q) := by omega
  have h1 : (Work.Landing.angDouble)^[2 * (k * q)] (Int.fract θ) = Int.fract θ := hper
  have h3 : (Work.Landing.angDouble)^[(2 * (k * q) - 1) + 1] (Int.fract θ)
      = Int.fract (((-2 : ℝ) ^ ((2 * (k * q) - 1) + 1)) * Int.fract θ) :=
    Work.Landing.Angle.angDouble_iterate_succ _ _
  rw [Nat.sub_add_cancel h2, h1] at h3
  have h4 : ((-2 : ℝ) ^ (2 * (k * q))) = (4 : ℝ) ^ (k * q) := by
    rw [pow_mul]; norm_num
  rw [h4] at h3
  have h5 : Int.fract (((4 : ℝ) ^ (k * q)) * θ) = Int.fract θ := by
    have hh : ((4 : ℝ) ^ (k * q)) * θ
        = ((4 : ℝ) ^ (k * q)) * Int.fract θ
          + (((4 : ℤ) ^ (k * q)) * ⌊θ⌋ : ℤ) := by
      have h := Int.self_sub_floor θ
      have hth : θ = Int.fract θ + (⌊θ⌋ : ℝ) := by linarith [h]
      nth_rewrite 1 [hth]
      push_cast
      ring
    calc Int.fract (((4 : ℝ) ^ (k * q)) * θ)
        = Int.fract (((4 : ℝ) ^ (k * q)) * Int.fract θ
            + (((4 : ℤ) ^ (k * q)) * ⌊θ⌋ : ℤ)) := by rw [hh]
      _ = Int.fract (((4 : ℝ) ^ (k * q)) * Int.fract θ) := Int.fract_add_intCast _ _
      _ = Int.fract θ := h3.symm
  obtain ⟨n, hn⟩ := exists_int_sub_of_fract_eq h5
  exact rayDir_eq_of_sub_int' ⟨n, hn⟩

/-! ## The return identity for the level point -/

theorem tsq_mem_critDomain {f z : ℂ} (hz : z ∈ Work.ParamRays.critDomain f) :
    Work.Landing.Tsq f z ∈ Work.ParamRays.critDomain f := by
  have h1 : Work.Landing.Tsq f z = (Tantibar f)^[2] z := by rw [Tsq_eq_iterate_two]
  rw [h1]
  exact Work.ParamRays.Tantibar_mem_critDomain (Work.ParamRays.Tantibar_mem_critDomain hz)

theorem varphiCrit_iterate_Tsq {f : ℂ} {m : ℕ} {z : ℂ}
    (hz : z ∈ Work.ParamRays.critDomain f) :
    Work.Bottcher.varphiCrit f ((Work.Landing.Tsq f)^[m] z)
      = (Work.Bottcher.varphiCrit f z) ^ (4 ^ m) := by
  have hmem : ∀ j : ℕ, (Work.Landing.Tsq f)^[j] z ∈ Work.ParamRays.critDomain f := by
    intro j
    induction j with
    | zero => simpa using hz
    | succ j ih => rw [Function.iterate_succ_apply']; exact tsq_mem_critDomain ih
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have hstep : Work.Landing.Tsq f ((Work.Landing.Tsq f)^[m] z)
        = (Tantibar f)^[2] ((Work.Landing.Tsq f)^[m] z) := by rw [Tsq_eq_iterate_two]
    have htwo : (Tantibar f)^[2] ((Work.Landing.Tsq f)^[m] z)
        = Tantibar f (Tantibar f ((Work.Landing.Tsq f)^[m] z)) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one]
    rw [hstep, htwo,
      Work.Bottcher.varphiCrit_comm_Tantibar (Work.ParamRays.Tantibar_mem_critDomain (hmem m)),
      Work.Bottcher.varphiCrit_comm_Tantibar (hmem m), ih]
    simp only [map_pow, starRingEnd_apply, star_star]
    rw [← pow_mul, ← pow_mul, ← pow_succ]

theorem tsq_iterate_eq (f : ℂ) (m : ℕ) :
    (Work.Landing.Tsq f)^[m] = (Tantibar f)^[2 * m] := by
  rw [Tsq_eq_iterate_two, Function.iterate_mul]

theorem rayPt_iterate {f : ℂ} {θ : ℝ} {k q : ℕ} {t : ℝ}
    (hper : Work.Landing.PeriodicAngle (Int.fract θ) (2 * (k * q)))
    (ht : Real.exp (Work.ParamRays.greenFun f 0) < t) :
    (Tantibar f)^[2 * (k * q)] (rayPt f θ t) = rayPt f θ (t ^ (4 ^ (k * q))) := by
  have ht1 : 1 < t := lt_of_le_of_lt (Real.one_le_exp (Work.ParamRays.greenFun_nonneg f 0)) ht
  obtain ⟨hzmem, hzφ⟩ := rayPt_spec (f := f) (θ := θ) ht
  set z : ℂ := rayPt f θ t with hzdef
  have h1 : Work.Bottcher.varphiCrit f ((Work.Landing.Tsq f)^[k * q] z)
      = (Work.Bottcher.varphiCrit f z) ^ (4 ^ (k * q)) := varphiCrit_iterate_Tsq hzmem
  have hpow : (Work.Bottcher.varphiCrit f z) ^ (4 ^ (k * q))
      = ((t ^ (4 ^ (k * q)) : ℝ) : ℂ) * Work.ParamRays.rayDir θ := by
    rw [hzφ, mul_pow]
    have h1 : (Work.ParamRays.rayDir θ) ^ (4 ^ (k * q)) = Work.ParamRays.rayDir θ := by
      rw [rayDir_pow]
      have hcast : ((4 ^ (k * q) : ℕ) : ℝ) = (4 : ℝ) ^ (k * q) := by push_cast; ring
      rw [hcast]
      exact rayDir_four_pow hper
    rw [h1, ← Complex.ofReal_pow]
  have hval : Work.Bottcher.varphiCrit f ((Work.Landing.Tsq f)^[k * q] z)
      = ((t ^ (4 ^ (k * q)) : ℝ) : ℂ) * Work.ParamRays.rayDir θ := by
    rw [h1, hpow]
  have hmem : ((Work.Landing.Tsq f)^[k * q] z) ∈ Work.ParamRays.critDomain f := by
    rw [tsq_iterate_eq]
    exact Work.ParamRays.orbit_mem_critDomain hzmem (2 * (k * q))
  have htgt : Real.exp (Work.ParamRays.greenFun f 0) < t ^ (4 ^ (k * q)) := by
    have h1' : t ≤ t ^ (4 ^ (k * q)) := by
      have h2 : (1 : ℝ) ≤ t := le_of_lt ht1
      calc t = t ^ (1 : ℕ) := (pow_one t).symm
        _ ≤ t ^ (4 ^ (k * q)) := pow_le_pow_right₀ h2 (Nat.one_le_pow _ _ (by norm_num))
    exact lt_of_lt_of_le ht h1'
  have hz' : ((Work.Landing.Tsq f)^[k * q] z) = rayPt f θ (t ^ (4 ^ (k * q))) :=
    rayPt_unique hmem hval htgt
  rw [tsq_iterate_eq] at hz'
  exact hz'

/-! ## The descent: from the anchor to the whole interval -/

theorem descent_membership {D : ℝ → ℝ} {a ℓ η κ ρ Λ : ℝ}
    (hΛ : 1 < Λ) (ha1 : 1 ≤ a) (haℓ : a < ℓ) (hℓη : ℓ < η) (hρ : 0 < ρ)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hℓΛ : ℓ ^ Λ ≤ η)
    (hcont : ∀ s ∈ Set.Ioc a η, ContinuousAt D s)
    (hanchor : ∀ t ∈ Set.Icc ℓ η, D t ≤ ρ)
    (hstep : ∀ t, a < t → t ^ Λ ≤ η → D t ≤ ρ → D t ≤ κ * D (t ^ Λ)) :
    ∀ t, a < t → t ≤ η → D t ≤ ρ := by
  intro t hat htη
  by_contra hcon
  push Not at hcon
  set G : Set ℝ := {s | a < s ∧ s ≤ η ∧ ∀ r ∈ Set.Icc s η, D r ≤ ρ} with hG
  have hηG : η ∈ G := by
    refine ⟨lt_of_lt_of_le haℓ hℓη.le, le_rfl, ?_⟩
    intro r hr
    have hreq : r = η := le_antisymm hr.2 hr.1
    rw [hreq]
    exact hanchor η ⟨le_of_lt hℓη, le_rfl⟩
  have hGne : G.Nonempty := ⟨η, hηG⟩
  have hGdown : ∀ s ∈ G, a < s := fun s hs => hs.1
  have hlow : ∀ s ∈ G, a ≤ s := fun s hs => le_of_lt (hGdown s hs)
  have hGup : ∀ s ∈ G, ∀ s' ∈ Set.Icc s η, s' ∈ G := by
    intro s hs s' hs'
    exact ⟨lt_of_lt_of_le hs.1 hs'.1, hs'.2, fun r hr =>
      hs.2.2 r ⟨le_trans hs'.1 hr.1, hr.2⟩⟩
  set s0 : ℝ := sInf G with hs0def
  have hs0leℓ : s0 ≤ ℓ :=
    csInf_le ⟨a, hlow⟩ ⟨haℓ, le_of_lt hℓη, hanchor⟩
  have hs0leη : s0 ≤ η := by rw [hs0def]; exact csInf_le ⟨a, hlow⟩ hηG
  have has0 : a ≤ s0 := le_csInf hGne hlow
  have hgt : ∀ s, s0 < s → s ≤ η → D s ≤ ρ := by
    intro s hs hsη
    obtain ⟨g, hgG, hgs⟩ := exists_lt_of_csInf_lt hGne (show s0 < s from hs)
    exact (hGup g hgG s ⟨le_of_lt hgs, hsη⟩).2.2 s ⟨le_rfl, hsη⟩
  rcases eq_or_lt_of_le has0 with h | h
  · -- s0 = a: then t ∈ G by the up-property
    have htG : t ∈ G := by
      obtain ⟨g, hgG, hgt'⟩ := exists_lt_of_csInf_lt hGne (show s0 < t from h ▸ hat)
      exact hGup g hgG t ⟨le_of_lt hgt', htη⟩
    exact absurd (htG.2.2 t ⟨le_rfl, htη⟩) (not_le.mpr hcon)
  · -- a < s0: contradict the minimality of s0
    have hs0mem : s0 ∈ Set.Ioc a η := ⟨h, hs0leη⟩
    have hD0 : D s0 ≤ ρ := by
      set δ : ℝ := (η - s0) / 2 with hδdef
      have hδpos : 0 < δ := by rw [hδdef]; linarith
      have hseq : ∀ n : ℕ, D (s0 + δ * (1 / (n + 1))) ≤ ρ := by
        intro n
        apply hgt
        · have h1 : 0 < δ * (1 / (n + 1 : ℝ)) := by positivity
          linarith
        · have h2 : δ * (1 / (n + 1 : ℝ)) ≤ δ :=
            mul_le_of_le_one_right hδpos.le (by
              rw [div_le_one (by positivity)]; push_cast; linarith)
          calc s0 + δ * (1 / (n + 1 : ℝ)) ≤ s0 + δ := by linarith
            _ = (s0 + η) / 2 := by rw [hδdef]; ring
            _ ≤ η := by linarith
      have hmem : ∀ n : ℕ, s0 + δ * (1 / (n + 1)) ∈ Set.Ioc a η := by
        intro n
        refine ⟨by
          have h1 : 0 < δ * (1 / (n + 1 : ℝ)) := by positivity
          linarith, ?_⟩
        have h2 : δ * (1 / (n + 1 : ℝ)) ≤ δ :=
          mul_le_of_le_one_right hδpos.le (by
            rw [div_le_one (by positivity)]; push_cast; linarith)
        calc s0 + δ * (1 / (n + 1 : ℝ)) ≤ s0 + δ := by linarith
          _ = (s0 + η) / 2 := by rw [hδdef]; ring
          _ ≤ η := by linarith
      have htendl : Tendsto (fun n : ℕ => s0 + δ * (1 / (n + 1))) atTop (𝓝 s0) := by
        have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h3 : Tendsto (fun n : ℕ => s0 + δ * (1 / (n + 1 : ℝ))) atTop (𝓝 (s0 + δ * 0)) :=
          tendsto_const_nhds.add (tendsto_const_nhds.mul h1)
        simpa using h3
      have hmeme : ∀ᶠ n : ℕ in atTop, s0 + δ * (1 / (n + 1)) ∈ Set.Ioc a η :=
        Eventually.of_forall hmem
      have hDlim : Tendsto (fun n : ℕ => D (s0 + δ * (1 / (n + 1)))) atTop (𝓝 (D s0)) :=
        (hcont s0 hs0mem).tendsto.comp htendl
      exact le_of_tendsto hDlim (Eventually.of_forall hseq)
    have hlt : D s0 < ρ := by
      have hs0Λ : s0 ^ Λ ≤ η := by
        calc s0 ^ Λ ≤ ℓ ^ Λ := Real.rpow_le_rpow (by linarith) hs0leℓ (by linarith)
          _ ≤ η := hℓΛ
      have hstep0 : D s0 ≤ κ * D (s0 ^ Λ) := hstep s0 h hs0Λ hD0
      have hs0lt : s0 < s0 ^ Λ := by
        calc s0 = s0 ^ (1 : ℝ) := (Real.rpow_one s0).symm
          _ < s0 ^ Λ := Real.rpow_lt_rpow_of_exponent_lt (by linarith) hΛ
      have hD1 : D (s0 ^ Λ) ≤ ρ := hgt (s0 ^ Λ) hs0lt hs0Λ
      nlinarith [hstep0, hD1, hκ0, hκ1, hρ]
    obtain ⟨ε, hεpos, hε⟩ := (Metric.continuousAt_iff.mp (hcont s0 hs0mem)) (ρ - D s0)
      (by linarith)
    set ε' : ℝ := min ε (s0 - a) / 2 with hε'def
    have hε'pos : 0 < ε' := by
      rw [hε'def]; have : 0 < s0 - a := by linarith
      positivity
    have hε'ε : ε' < ε := by
      rw [hε'def]
      have h1 : min ε (s0 - a) ≤ ε := min_le_left _ _
      linarith
    have hε'a : ε' < s0 - a := by
      rw [hε'def]
      have h1 : min ε (s0 - a) ≤ s0 - a := min_le_right _ _
      linarith
    set s' : ℝ := s0 - ε' with hs'def
    have hs'a : a < s' := by rw [hs'def]; linarith
    have hs's0 : s' < s0 := by rw [hs'def]; linarith
    have hs'G : s' ∈ G := by
      refine ⟨hs'a, le_trans hs's0.le hs0leη, ?_⟩
      intro r hr
      by_cases hle : r ≤ s0
      · have hmem : r ∈ Set.Ioc a η := ⟨lt_of_lt_of_le hs'a hr.1, hr.2⟩
        have hdist : dist r s0 < ε := by
          rw [Real.dist_eq, abs_of_nonpos (by linarith)]
          linarith [hr.1, hε'ε]
        have h3 : dist (D r) (D s0) < ρ - D s0 := hε hdist
        rw [Real.dist_eq] at h3
        have h4 := (abs_lt.mp h3).2
        linarith
      · exact hgt r (lt_of_not_ge hle) hr.2
    have : s0 ≤ s' := csInf_le ⟨a, hlow⟩ hs'G
    linarith


end

end Work.LandLeaves
