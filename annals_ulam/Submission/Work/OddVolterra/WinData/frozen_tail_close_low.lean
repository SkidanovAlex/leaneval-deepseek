import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.Anchor.ThetaM_close
import Submission.Work.OddVolterra.Existence.aw_contDiffOn_awGodd

/-!
# The frozen tail of the odd transition-slope system, at low slopes

The perturbation `h` of Ryabogin's odd case is supported in `[1 - 2τ, 1 - τ] = [4/5, 9/10]`, so
`h` vanishes on `(-∞, 4/5) ∪ (9/10, ∞)`.  The *frozen tail* of the transition-slope system is

`∫_{19/20}^{1} (ΘM n h s σ (baseState σ) - ΘM n 0 s σ (baseState σ)) dσ`,

i.e. the `σ`-integral of the defect of the manifest kernel on the tail where the state is frozen
to the unperturbed state.  This file proves that it is `O(δ)` in the `C^{n+2}`-norm `δ` of the
bump, uniformly in `s ∈ [1/4, 7/10]`.

The two structural facts used, both new here, are

* `KvecM_deriv_eq_of_lt_high` (locality): for `a < 4/5 < 9/10 < σ` the manifest kernel
  `KvecM n h · σ z` agrees with `KvecM n 0 · σ z` as a *germ* at `a`, hence its first-slot
  derivative at `a` is the same.  This is what lets the derivative-difference estimate be used
  on the whole moving interval `[s - 1/100, σ]` even when `s < 1/2`, where
  `Work.Anchor.KvecM_deriv_diff` (stated for `a ≥ 1/2`) does not apply: on the part `a < 4/5`
  the two kernels are literally equal.
* `KvecM_slice_bound_wide`: uniform bounds for a component of `KvecM n h · σ z` and of its
  first-slot derivative on the box `a ∈ [1/5, 3/2]`, for a `C^∞` perturbation with
  `|h| ≤ 1/100`, `|h'| ≤ 1/100` (so that the radicand is bounded below on that box); the moving
  point of the Abel average may be as small as `s - 1/100 = 6/25 > 1/5`.

The last two sections mirror `Work.Anchor.G2M_deriv_close` and
`Work.OddVolterra.Existence.aw_frozen_tail_close`, with the slope range `[1/2, 19/20]` replaced
by `[1/4, 7/10]`.
-/

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Work.OddVolterra

noncomputable section

/-! ## 1. Locality of the manifest kernel above the support of the perturbation -/

/-- The set of exponent triples `(s, σ, t)` with `s < 4/5` and `9/10 < σ`. -/
def LocHigh : Set (ℝ × ℝ × ℝ) := {p | p.1 < 4 / 5 ∧ 9 / 10 < p.2.1}

lemma isOpen_LocHigh : IsOpen LocHigh := by
  have h1 : Continuous (fun p : ℝ × ℝ × ℝ => p.1) := continuous_fst
  have h2 : Continuous (fun p : ℝ × ℝ × ℝ => p.2.1) := continuous_fst.comp continuous_snd
  exact (isOpen_lt h1 continuous_const).inter (isOpen_lt continuous_const h2)

lemma deriv_eq_zero_of_lt_val {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) {x : ℝ}
    (hx : x < 4 / 5) : deriv h x = 0 := by
  have hev : h =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) :=
    Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Iio hx) (fun y hy => hz y hy)
  rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]

/-- `line h s · = line 0 s ·` whenever `h s = 0`. -/
lemma line_eq_of_eq_zero {h : ℝ → ℝ} {s : ℝ} (hs : h s = 0) (t : ℝ) :
    line h s t = line 0 s t := by
  unfold line
  rw [hs]
  simp

/-- `lineSlope h s · = lineSlope 0 s ·` whenever `h` vanishes below `s`. -/
lemma lineSlope_eq_of_lt_val {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) {s : ℝ}
    (hs : s < 4 / 5) (t : ℝ) : lineSlope h s t = lineSlope 0 s t := by
  unfold lineSlope
  rw [deriv_eq_zero_of_lt_val hz hs]
  simp

/-- `Zrad h` and `Zrad 0` agree on `LocHigh`. -/
lemma Zrad_eqOn_high {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0)
    (hz' : ∀ x : ℝ, 9 / 10 < x → h x = 0) :
    Set.EqOn (KernelExt.Zrad h) (KernelExt.Zrad 0) LocHigh := by
  intro p hp
  have hp1 : p.1 < 4 / 5 := hp.1
  have hp2 : 9 / 10 < p.2.1 := hp.2
  simp only [KernelExt.Zrad]
  rw [line_eq_of_eq_zero (hz' p.2.1 hp2) p.2.2, line_eq_of_eq_zero (hz p.1 hp1) p.2.2]

/-- The recursive Bell numerator is local: if the two radicands agree on the open set `LocHigh`
and the two `init` agree there, then all the numerators agree there. -/
lemma Rnu_eqOn_high {ν : ℝ} {h g : ℝ → ℝ} {init init' : ℝ × ℝ × ℝ → ℝ}
    (hZ : Set.EqOn (KernelExt.Zrad h) (KernelExt.Zrad g) LocHigh)
    (hi : Set.EqOn init init' LocHigh) (m : ℕ) :
    Set.EqOn (KernelExt.Rnu ν h init m) (KernelExt.Rnu ν g init' m) LocHigh := by
  induction m with
  | zero => intro p hp; exact hi hp
  | succ m ih =>
      intro p hp
      rw [KernelExt.Rnu]
      show KernelExt.Zrad h p * (fderiv ℝ (KernelExt.Rnu ν h init m) p) (1, 0, 0)
          + (ν - (m : ℝ)) * (fderiv ℝ (KernelExt.Zrad h) p) (1, 0, 0)
              * KernelExt.Rnu ν h init m p
        = KernelExt.Zrad g p * (fderiv ℝ (KernelExt.Rnu ν g init' m) p) (1, 0, 0)
          + (ν - (m : ℝ)) * (fderiv ℝ (KernelExt.Zrad g) p) (1, 0, 0)
              * KernelExt.Rnu ν g init' m p
      have hevR : KernelExt.Rnu ν h init m =ᶠ[𝓝 p] KernelExt.Rnu ν g init' m :=
        Filter.eventually_of_mem (isOpen_LocHigh.mem_nhds hp) (fun q hq => ih hq)
      have hevZ : KernelExt.Zrad h =ᶠ[𝓝 p] KernelExt.Zrad g :=
        Filter.eventually_of_mem (isOpen_LocHigh.mem_nhds hp) (fun q hq => hZ hq)
      rw [Filter.EventuallyEq.fderiv_eq hevR, Filter.EventuallyEq.fderiv_eq hevZ,
        hZ hp, ih hp]

lemma J1M_eq_of_lt_high (n : ℕ) {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0)
    (hz' : ∀ x : ℝ, 9 / 10 < x → h x = 0) {a σ t : ℝ} (ha : a < 4 / 5) (hσ : 9 / 10 < σ) :
    KernelExt.J1M n h a σ t = KernelExt.J1M n 0 a σ t :=
  Rnu_eqOn_high (Zrad_eqOn_high hz hz') (fun _ _ => rfl) (n + 1) ⟨ha, hσ⟩

lemma lineSlope_eqOn_high {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) :
    Set.EqOn (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2)
      (fun p : ℝ × ℝ × ℝ => lineSlope 0 p.1 p.2.2) LocHigh := by
  intro p hp
  exact lineSlope_eq_of_lt_val hz hp.1 p.2.2

lemma J2M_eq_of_lt_high (n : ℕ) {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0)
    (hz' : ∀ x : ℝ, 9 / 10 < x → h x = 0) {a σ t : ℝ} (ha : a < 4 / 5) (hσ : 9 / 10 < σ) :
    KernelExt.J2M n h a σ t = KernelExt.J2M n 0 a σ t :=
  Rnu_eqOn_high (Zrad_eqOn_high hz hz') (lineSlope_eqOn_high hz) n ⟨ha, hσ⟩

/-- `hquot h a σ = 0` when `h` vanishes at `a` and above `9/10`, with `a < 4/5 < 9/10 < σ`. -/
lemma hquot_eq_zero_of_lt_high {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) (hz' : ∀ x : ℝ, 9 / 10 < x → h x = 0)
    {a σ : ℝ} (ha : a < 4 / 5) (hσ : 9 / 10 < σ) : hquot h a σ = 0 := by
  have h1 : h σ - h a = (σ - a) * hquot h a σ :=
    sub_mul_hquot (hh.of_le (by norm_num)) a σ
  have hprod : (σ - a) * hquot h a σ = 0 := by
    rw [← h1, hz' σ hσ, hz a ha, sub_zero]
  have hne : (σ - a) ≠ 0 := by
    have : a < σ := lt_trans ha (lt_trans (by norm_num) hσ)
    linarith
  exact (mul_eq_zero.mp hprod).resolve_left hne

lemma Kden_eq_of_lt_high {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) (hz' : ∀ x : ℝ, 9 / 10 < x → h x = 0)
    {a σ t : ℝ} (ha : a < 4 / 5) (hσ : 9 / 10 < σ) : Kden h a σ t = Kden 0 a σ t := by
  unfold Kden
  rw [hquot_eq_zero_of_lt_high hh hz hz' ha hσ,
    Work.OddExistence.Manifest.AW.hquot_zero,
    line_eq_of_eq_zero (hz' σ hσ) t, line_eq_of_eq_zero (hz a ha) t]

lemma K1M_eq_of_lt_high (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) (hz' : ∀ x : ℝ, 9 / 10 < x → h x = 0)
    {a σ t : ℝ} (ha : a < 4 / 5) (hσ : 9 / 10 < σ) :
    KernelExt.K1M n h a σ t = KernelExt.K1M n 0 a σ t := by
  unfold KernelExt.K1M
  rw [J1M_eq_of_lt_high n hz hz' ha hσ, Kden_eq_of_lt_high hh hz hz' ha hσ]

lemma K2M_eq_of_lt_high (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) (hz' : ∀ x : ℝ, 9 / 10 < x → h x = 0)
    {a σ t : ℝ} (ha : a < 4 / 5) (hσ : 9 / 10 < σ) :
    KernelExt.K2M n h a σ t = KernelExt.K2M n 0 a σ t := by
  unfold KernelExt.K2M
  rw [J2M_eq_of_lt_high n hz hz' ha hσ, Kden_eq_of_lt_high hh hz hz' ha hσ]

/-- The manifest kernel agrees with its unperturbed counterpart at every slope `a < 4/5`. -/
lemma KvecM_eq_of_lt_high (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) (hz' : ∀ x : ℝ, 9 / 10 < x → h x = 0)
    {a σ : ℝ} (ha : a < 4 / 5) (hσ : 9 / 10 < σ) (x y x' y' : ℝ) :
    KernelExt.KvecM n h a σ x y x' y' = KernelExt.KvecM n 0 a σ x y x' y' := by
  funext i
  fin_cases i <;>
    simp [KernelExt.KvecM, K1M_eq_of_lt_high n hh hz hz' ha hσ,
      K2M_eq_of_lt_high n hh hz hz' ha hσ]

/-- **Locality of the first-slot derivative of the manifest kernel below `4/5`.** -/
lemma KvecM_deriv_eq_of_lt_high (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) (hz' : ∀ x : ℝ, 9 / 10 < x → h x = 0)
    {σ : ℝ} (hσ : 9 / 10 < σ) {a : ℝ} (ha : a < 4 / 5) (z : St) (i : Fin 2) :
    deriv (fun u : ℝ => (KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) i) a =
      deriv (fun u : ℝ => (KernelExt.KvecM n 0 u σ (z 0) (z 1) (z 2) (z 3)) i) a := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [IsOpen.mem_nhds isOpen_Iio ha] with u hu
  exact congrArg (fun v : Fin 2 → ℝ => v i)
    (KvecM_eq_of_lt_high n hh hz hz' hu hσ (z 0) (z 1) (z 2) (z 3))


/-! ## 2. Bounds for the manifest kernel on the box `[1/5, 3/2]` -/

lemma iteratedDeriv_one_small {b : ℝ → ℝ} (hb0 : ∀ x : ℝ, |b x| ≤ 1 / 100)
    (hb1 : ∀ x : ℝ, |deriv b x| ≤ 1 / 100) :
    ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k b s| ≤ 1 / 100 := by
  intro k hk s
  rcases Nat.lt_or_ge k 1 with h | h
  · have hk0 : k = 0 := by omega
    subst hk0
    simpa using hb0 s
  · have hk1 : k = 1 := by omega
    subst hk1
    simpa [iteratedDeriv_one] using hb1 s

/-- Positivity of both Abel radicands on the box `a ∈ [1/5, 3/2]`. -/
lemma Icc_subset_Ksl_wide {b : ℝ → ℝ}
    (hbsupp : Function.support b ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hb0 : ∀ x : ℝ, |b x| ≤ 1 / 100) (hb1 : ∀ x : ℝ, |deriv b x| ≤ 1 / 100)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (19 / 20 : ℝ) 1) {z : St}
    (hz0 : (1 / 5 : ℝ) ≤ z 0) (hz1 : (1 / 5 : ℝ) ≤ z 1)
    (_hz3 : ∀ i : Fin 4, |z i| ≤ 3 / 2) :
    Set.Icc (1 / 5 : ℝ) (3 / 2) ⊆ Work.Anchor.Ksl b σ z := by
  intro a ha
  have hsmall := iteratedDeriv_one_small hb0 hb1
  have hS : (1 / 10 : ℝ) < σ + a := by linarith [hσ.1, ha.1]
  refine ⟨?_, ?_⟩
  · refine Work.OddVolterra.Existence.krad_pos_of_add_pos hbsupp hsmall hS ?_
    rw [abs_neg]
    exact le_trans hz0 (le_abs_self (z 0))
  · exact Work.OddVolterra.Existence.krad_pos_of_add_pos hbsupp hsmall hS
      (le_trans hz1 (le_abs_self (z 1)))

/-- **Bounds for the manifest kernel on the box `a ∈ [1/5, 3/2]`.**  For any `C^∞` perturbation
`b` with `|b| ≤ 1/100`, `|b'| ≤ 1/100`, supported in the transition window, any `σ ∈ [19/20, 1]`
and any state `z` with the chord endpoints at distance `≥ 1/5` from the axis and `|z i| ≤ 3/2`,
a component of `KvecM n b · σ z` and its first-slot derivative are bounded on `[1/5, 3/2]`. -/
theorem KvecM_slice_bound_wide (n : ℕ) :
    ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ x : ℝ, |h x| ≤ 1 / 100) → (∀ x : ℝ, |deriv h x| ≤ 1 / 100) →
      ∀ σ ∈ Set.Icc (19 / 20 : ℝ) 1, ∀ z : St,
        (1 / 5 : ℝ) ≤ z 0 → (1 / 5 : ℝ) ≤ z 1 → (∀ i : Fin 4, |z i| ≤ 3 / 2) →
        ∀ i : Fin 2, ∃ M : ℝ, 0 < M ∧ ∀ a ∈ Set.Icc (1 / 5 : ℝ) (3 / 2),
          ‖(KernelExt.KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) i‖ ≤ M ∧
          ‖deriv (fun a' : ℝ =>
            (KernelExt.KvecM n h a' σ (z 0) (z 1) (z 2) (z 3)) i) a‖ ≤ M := by
  intro h hh hsupp hh0 hh1 σ hσ z hz0 hz1 hz3 i
  have hopen : IsOpen (Work.Anchor.Ksl h σ z) := Work.Anchor.isOpen_Ksl hh σ z
  have hsub : Set.Icc (1 / 5 : ℝ) (3 / 2) ⊆ Work.Anchor.Ksl h σ z :=
    Icc_subset_Ksl_wide hsupp hh0 hh1 hσ hz0 hz1 hz3
  have hcd : ContDiffOn ℝ (⊤ : ℕ∞) (Work.Anchor.Kw n h σ z i) (Work.Anchor.Ksl h σ z) :=
    Work.Anchor.contDiffOn_Kw (n := n) hh σ z i
  have hc1 : ContinuousOn (Work.Anchor.Kw n h σ z i) (Set.Icc (1 / 5 : ℝ) (3 / 2)) :=
    hcd.continuousOn.mono hsub
  have hc2 : ContinuousOn (deriv (Work.Anchor.Kw n h σ z i)) (Set.Icc (1 / 5 : ℝ) (3 / 2)) :=
    (hcd.continuousOn_deriv_of_isOpen hopen (by norm_num)).mono hsub
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  refine ⟨max (max M1 M2) 1, by positivity, ?_⟩
  intro a ha
  refine ⟨le_trans (hM1 a ha) (le_max_of_le_left (le_max_left _ _)),
    le_trans (hM2 a ha) (le_max_of_le_left (le_max_right _ _))⟩

/-! ## 3. Closeness of the first-slot derivative of `G₂M` on the frozen tail -/

/-- **Closeness of the first-slot derivative of a component of `G₂M`.**  If the first-slot
derivative of the `i`-th component of the manifest kernel differs from its unperturbed value by
at most `Ck * δ` along the whole moving point `s + τ(σ - s)` of the Abel average, then the same
holds for the `s`-derivative of the `i`-th component of `G₂M`, with constant `π * Ck + 1`. -/
lemma G2M_deriv_close_low (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    {δ Ck : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    (hjet : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) (hCk : 0 < Ck)
    {s σ : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ))
    (hσ : σ ∈ Set.Icc (19 / 20 : ℝ) 1) {z : St}
    (hz0 : (1 / 5 : ℝ) ≤ z 0) (hz1 : (1 / 5 : ℝ) ≤ z 1) (hz3 : ∀ i : Fin 4, |z i| ≤ 3 / 2)
    (i : Fin 2)
    (hd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      |deriv (Work.Anchor.Kw n h σ z i) (s + τ * (σ - s)) -
       deriv (Work.Anchor.Kw n 0 σ z i) (s + τ * (σ - s))| ≤ Ck * δ) :
    |deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) i) s -
     deriv (fun u : ℝ => (KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) i) s| ≤
      (Real.pi * Ck + 1) * δ := by
  have hh0 : ∀ x : ℝ, |h x| ≤ 1 / 100 := fun x => le_trans (hjet 0 (by omega) x) hδ1
  have hh1 : ∀ x : ℝ, |deriv h x| ≤ 1 / 100 := fun x => by
    simpa [iteratedDeriv_one] using le_trans (hjet 1 (by omega) x) hδ1
  have hsupp0 : Function.support (0 : ℝ → ℝ) ⊆ Set.Icc (1 - 2 * tau) (1 - tau) := by
    intro x hx
    rw [Function.mem_support] at hx
    exact absurd rfl hx
  obtain ⟨Mh, hMh0, hMh⟩ :=
    KvecM_slice_bound_wide n h hh hsupp hh0 hh1 σ hσ z hz0 hz1 hz3 i
  obtain ⟨M0, hM00, hM0⟩ := KvecM_slice_bound_wide n (0 : ℝ → ℝ) contDiff_const hsupp0
    (fun x => by norm_num) (fun x => by simp) σ hσ z hz0 hz1 hz3 i
  -- the moving point stays in the box `[1/5, 3/2]`
  have hconv : ∀ x ∈ Set.Ioo (s - 1 / 100) (s + 1 / 100), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      x + τ * (σ - x) ∈ Set.Icc (1 / 5 : ℝ) (3 / 2) := by
    intro x hx τ hτ
    have hxlo : (1 / 5 : ℝ) < x := by linarith [hx.1, hs.1]
    have hxhi : x < 1 := by linarith [hx.2, hs.2]
    have hσlo : (1 / 5 : ℝ) ≤ σ := by linarith [hσ.1]
    have hσhi : σ ≤ 3 / 2 := by linarith [hσ.2]
    have h1 : 0 ≤ 1 - τ := by linarith [hτ.2]
    have heq : x + τ * (σ - x) = (1 - τ) * x + τ * σ := by ring
    rw [heq]
    constructor
    · nlinarith [mul_nonneg h1 (by linarith : (0 : ℝ) ≤ x - 1 / 5),
        mul_nonneg hτ.1 (by linarith : (0 : ℝ) ≤ σ - 1 / 5)]
    · nlinarith [mul_nonneg h1 (by linarith : (0 : ℝ) ≤ 3 / 2 - x),
        mul_nonneg hτ.1 (by linarith : (0 : ℝ) ≤ 3 / 2 - σ)]
  have hsIoo : s ∈ Set.Ioo (s - 1 / 100) (s + 1 / 100) := ⟨by linarith, by linarith⟩
  -- the analytic hypotheses of differentiation under the Abel integral
  have hbdK : ∀ x ∈ Set.Ioo (s - 1 / 100) (s + 1 / 100), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      ‖Work.Anchor.Kw n h σ z i (x + τ * (σ - x))‖ ≤ Mh :=
    fun x hx τ hτ => (hMh _ (hconv x hx τ ⟨hτ.1, le_of_lt hτ.2⟩)).1
  have hbdK0 : ∀ x ∈ Set.Ioo (s - 1 / 100) (s + 1 / 100), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      ‖Work.Anchor.Kw n 0 σ z i (x + τ * (σ - x))‖ ≤ M0 :=
    fun x hx τ hτ => (hM0 _ (hconv x hx τ ⟨hτ.1, le_of_lt hτ.2⟩)).1
  have hdiff : ∀ x ∈ Set.Ioo (s - 1 / 100) (s + 1 / 100), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      DifferentiableAt ℝ (Work.Anchor.Kw n h σ z i) (x + τ * (σ - x)) := by
    intro x hx τ hτ
    have hmem := hconv x hx τ ⟨hτ.1, le_of_lt hτ.2⟩
    have hmem' : x + τ * (σ - x) ∈ Work.Anchor.Ksl h σ z :=
      Icc_subset_Ksl_wide hsupp hh0 hh1 hσ hz0 hz1 hz3 hmem
    exact ((Work.Anchor.contDiffOn_Kw (n := n) hh σ z i).differentiableOn
      (by simp)).differentiableAt ((Work.Anchor.isOpen_Ksl hh σ z).mem_nhds hmem')
  have hdiff0 : ∀ x ∈ Set.Ioo (s - 1 / 100) (s + 1 / 100), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      DifferentiableAt ℝ (Work.Anchor.Kw n 0 σ z i) (x + τ * (σ - x)) := by
    intro x hx τ hτ
    have hmem := hconv x hx τ ⟨hτ.1, le_of_lt hτ.2⟩
    have hmem' : x + τ * (σ - x) ∈ Work.Anchor.Ksl 0 σ z :=
      Icc_subset_Ksl_wide hsupp0 (fun x => by norm_num) (fun x => by simp) hσ hz0 hz1 hz3 hmem
    exact ((Work.Anchor.contDiffOn_Kw (n := n) contDiff_const σ z i).differentiableOn
      (by simp)).differentiableAt ((Work.Anchor.isOpen_Ksl contDiff_const σ z).mem_nhds hmem')
  have hbound : ∀ x ∈ Set.Ioo (s - 1 / 100) (s + 1 / 100), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖(1 - τ) * deriv (Work.Anchor.Kw n h σ z i) (x + τ * (σ - x))‖ ≤ Mh := by
    intro x hx τ hτ
    have hmem := hconv x hx τ hτ
    have h1 : 0 ≤ 1 - τ := by linarith [hτ.2]
    have h2 : (1 : ℝ) - τ ≤ 1 := by linarith [hτ.1]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1]
    calc (1 - τ) * |deriv (Work.Anchor.Kw n h σ z i) (x + τ * (σ - x))|
        ≤ 1 * Mh := mul_le_mul h2 (hMh _ hmem).2 (abs_nonneg _) (by norm_num)
      _ = Mh := one_mul Mh
  have hbound0 : ∀ x ∈ Set.Ioo (s - 1 / 100) (s + 1 / 100), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖(1 - τ) * deriv (Work.Anchor.Kw n 0 σ z i) (x + τ * (σ - x))‖ ≤ M0 := by
    intro x hx τ hτ
    have hmem := hconv x hx τ hτ
    have h1 : 0 ≤ 1 - τ := by linarith [hτ.2]
    have h2 : (1 : ℝ) - τ ≤ 1 := by linarith [hτ.1]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1]
    calc (1 - τ) * |deriv (Work.Anchor.Kw n 0 σ z i) (x + τ * (σ - x))|
        ≤ 1 * M0 := mul_le_mul h2 (hM0 _ hmem).2 (abs_nonneg _) (by norm_num)
      _ = M0 := one_mul M0
  -- the two derivative identities
  have hDh := Work.Anchor.deriv_G2M_eq_integral (n := n) (b := h) hh z i hMh0.le hbdK hdiff hbound
  have hD0 := Work.Anchor.deriv_G2M_eq_integral (n := n) (b := (0 : ℝ → ℝ)) contDiff_const z i
    hM00.le hbdK0 hdiff0 hbound0
  rw [hDh, hD0, ← Real.norm_eq_abs]
  -- integrability of the two integrands
  have hwmeas : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) :=
    (Work.OddVolterra.measurable_sqrt_real.comp
      (measurable_id.mul (measurable_const.sub measurable_id))).inv
  have hlinmeas : Measurable (fun τ : ℝ => 1 - τ) := measurable_const.sub measurable_id
  have hFH_int : IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * deriv (Work.Anchor.Kw n h σ z i) (s + τ * (σ - s)))) volume (0 : ℝ) 1 := by
    refine (Work.OddExistence.Manifest.AW.intervalIntegrable_abel_weight_one_sub.mul_const Mh).mono_fun' ?_ ?_
    · refine (hwmeas.mul (hlinmeas.mul ?_)).aestronglyMeasurable
      exact (measurable_deriv (Work.Anchor.Kw n h σ z i)).comp
        (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
      have hτIcc : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hτ.1, hτ.2⟩
      have hmem := hconv s hsIoo τ hτIcc
      have h1 : 0 ≤ 1 - τ := by linarith [hτIcc.2]
      have h2 : (1 : ℝ) - τ ≤ 1 := by linarith [hτIcc.1]
      have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      have hdH : |deriv (Work.Anchor.Kw n h σ z i) (s + τ * (σ - s))| ≤ Mh := by
        simpa only [Work.Anchor.Kw_def, Real.norm_eq_abs] using (hMh _ hmem).2
      simp only [Real.norm_eq_abs]
      rw [abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg h1,
        show (Real.sqrt (τ * (1 - τ)))⁻¹ * (1 - τ) * Mh
          = (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * Mh) from by ring]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdH h1) hw
  have hF0_int : IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * deriv (Work.Anchor.Kw n 0 σ z i) (s + τ * (σ - s)))) volume (0 : ℝ) 1 := by
    refine (Work.OddExistence.Manifest.AW.intervalIntegrable_abel_weight_one_sub.mul_const M0).mono_fun' ?_ ?_
    · refine (hwmeas.mul (hlinmeas.mul ?_)).aestronglyMeasurable
      exact (measurable_deriv (Work.Anchor.Kw n 0 σ z i)).comp
        (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
      have hτIcc : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hτ.1, hτ.2⟩
      have hmem := hconv s hsIoo τ hτIcc
      have h1 : 0 ≤ 1 - τ := by linarith [hτIcc.2]
      have h2 : (1 : ℝ) - τ ≤ 1 := by linarith [hτIcc.1]
      have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      have hdH : |deriv (Work.Anchor.Kw n 0 σ z i) (s + τ * (σ - s))| ≤ M0 := by
        simpa only [Work.Anchor.Kw_def, Real.norm_eq_abs] using (hM0 _ hmem).2
      simp only [Real.norm_eq_abs]
      rw [abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg h1,
        show (Real.sqrt (τ * (1 - τ)))⁻¹ * (1 - τ) * M0
          = (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * M0) from by ring]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdH h1) hw
  have hbound_int : IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * (1 - τ) * (Ck * δ)) volume (0 : ℝ) 1 :=
    (Work.OddExistence.Manifest.AW.intervalIntegrable_abel_weight_one_sub).mul_const (Ck * δ)
  rw [← intervalIntegral.integral_sub hFH_int hF0_int]
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1)
    (Filter.Eventually.of_forall ?_) hbound_int) ?_
  · intro τ hτ
    rw [Set.mem_Ioc] at hτ
    have hτIcc : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hτ.1, hτ.2⟩
    have h1 : 0 ≤ 1 - τ := by linarith [hτIcc.2]
    have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hkey : (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (Work.Anchor.Kw n h σ z i) (s + τ * (σ - s)))
        - (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (Work.Anchor.Kw n 0 σ z i) (s + τ * (σ - s)))
        = (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) *
            (deriv (Work.Anchor.Kw n h σ z i) (s + τ * (σ - s))
              - deriv (Work.Anchor.Kw n 0 σ z i) (s + τ * (σ - s)))) := by ring
    simp only [Real.norm_eq_abs]
    rw [hkey, abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg h1,
      show (Real.sqrt (τ * (1 - τ)))⁻¹ * (1 - τ) * (Ck * δ)
        = (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * (Ck * δ)) from by ring]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hd τ hτIcc) h1) hw
  · have h1 := Work.OddExistence.Manifest.AW.aw_abel_weight_integral
    rw [intervalIntegral.integral_mul_const]
    have h2 : 0 ≤ Ck * δ := mul_nonneg hCk.le hδ.le
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    have h4 : Real.pi * (Ck * δ) ≤ (Real.pi * Ck + 1) * δ := by
      nlinarith [hδ.le, hCk.le, Real.pi_pos]
    linarith


/-! ## 4. Pointwise `O(δ)`-closeness of the manifest `Θ` on the frozen tail -/

/-- `h` vanishes strictly below the transition window `[1 - 2τ, 1 - τ] = [4/5, 9/10]`. -/
lemma h_eq_zero_of_lt_window {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {x : ℝ}
    (hx : x < 4 / 5) : h x = 0 := by
  by_contra hne
  have hmem := hsupp (Function.mem_support.mpr hne)
  have h1 : (1 : ℝ) - 2 * tau = 4 / 5 := by rw [tau]; norm_num
  rw [h1] at hmem
  linarith [hmem.1]

/-- `h` vanishes strictly above the transition window `[4/5, 9/10]`. -/
lemma h_eq_zero_of_gt_window {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {x : ℝ}
    (hx : 9 / 10 < x) : h x = 0 := by
  by_contra hne
  have hmem := hsupp (Function.mem_support.mpr hne)
  have h2 : (1 : ℝ) - tau = 9 / 10 := by rw [tau]; norm_num
  rw [h2] at hmem
  linarith [hmem.2]

/-- **Pointwise `O(δ)`-closeness of the manifest `Θ` on the frozen tail.**  For
`s ∈ [1/4, 7/10]` and `σ ∈ [19/20, 1]` the last two rows of `ThetaM n h s σ (baseState σ)` differ
from the unperturbed ones by at most `K δ`, uniformly in `h` (supported in `[1 - 2τ, 1 - τ]`,
`δ`-small in `C^{n+2}`). -/
theorem thetaM_tail_bound_low (n : ℕ) (hn : 1 ≤ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : ℝ → ℝ) (D : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < D → D ≤ 1 / 100 →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ D) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ), ∀ σ ∈ Set.Icc (19 / 20 : ℝ) 1,
        ‖KernelExt.ThetaM n h s σ (baseState σ) - KernelExt.ThetaM n 0 s σ (baseState σ)‖
          ≤ K * D := by
  obtain ⟨Ck, hCk, hKv⟩ := Work.Anchor.KvecM_deriv_diff n hn
  refine ⟨Real.pi * Ck + 1, by positivity, ?_⟩
  intro h D hh hDpos hD100 hsupp hjet s hs σ hσ
  set z : St := baseState σ with hzdef
  have hzball : z ∈ Metric.closedBall (baseState σ) (1 / 2) := by
    rw [hzdef, Metric.mem_closedBall, dist_self]
    norm_num
  obtain ⟨hz0, hz1, hz3⟩ := Work.Anchor.z_coords ⟨by linarith [hσ.1], hσ.2⟩ hzball
  have hzlow : ∀ x : ℝ, x < 4 / 5 → h x = 0 := fun x hx => h_eq_zero_of_lt_window hsupp hx
  have hzhigh : ∀ x : ℝ, 9 / 10 < x → h x = 0 := fun x hx => h_eq_zero_of_gt_window hsupp hx
  have hzσ : (9 / 10 : ℝ) < σ := by linarith [hσ.1]
  have hσIcc : σ ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨by linarith [hσ.1], hσ.2⟩
  -- the pointwise kernel-derivative bound along the moving point
  have hd : ∀ i : Fin 2, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      |deriv (Work.Anchor.Kw n h σ z i) (s + τ * (σ - s)) -
       deriv (Work.Anchor.Kw n 0 σ z i) (s + τ * (σ - s))| ≤ Ck * D := by
    intro i τ hτ
    set a : ℝ := s + τ * (σ - s) with hadef
    by_cases ha : (1 / 2 : ℝ) ≤ a
    · have haIcc : a ∈ Set.Icc (1 / 2 : ℝ) 1 := by
        refine ⟨ha, ?_⟩
        have heq : a = (1 - τ) * s + τ * σ := by rw [hadef]; ring
        rw [heq]
        nlinarith [mul_nonneg (sub_nonneg.mpr hτ.2) (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
          mul_nonneg hτ.1 (by linarith [hσ.2] : (0 : ℝ) ≤ 1 - σ)]
      have h := hKv h hh D hDpos hD100 hjet a haIcc σ hσIcc (z 0) (z 1) (z 2) (z 3)
        hz0 hz1 (hz3 0) (hz3 1) (hz3 2) (hz3 3) i
      simpa only [Work.Anchor.Kw_def] using h
    · have ha45 : a < 4 / 5 := by linarith [not_le.mp ha]
      have heq := KvecM_deriv_eq_of_lt_high n hh hzlow hzhigh hzσ ha45 z i
      have hzero : deriv (Work.Anchor.Kw n h σ z i) a
          = deriv (Work.Anchor.Kw n 0 σ z i) a := by
        simpa only [Work.Anchor.Kw_def] using heq
      rw [hzero, sub_self, abs_zero]
      exact mul_nonneg hCk.le hDpos.le
  have hTheta : ‖KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n 0 s σ z‖
      ≤ (Real.pi * Ck + 1) * D := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun j => ?_)
    fin_cases j
    · show ‖(KernelExt.ThetaM n h s σ z) 0 - (KernelExt.ThetaM n 0 s σ z) 0‖
          ≤ (Real.pi * Ck + 1) * D
      rw [show (KernelExt.ThetaM n h s σ z) 0 = -(z 2) from rfl,
        show (KernelExt.ThetaM n 0 s σ z) 0 = -(z 2) from rfl]
      simp only [sub_self, norm_zero]
      positivity
    · show ‖(KernelExt.ThetaM n h s σ z) 1 - (KernelExt.ThetaM n 0 s σ z) 1‖
          ≤ (Real.pi * Ck + 1) * D
      rw [show (KernelExt.ThetaM n h s σ z) 1 = -(z 3) from rfl,
        show (KernelExt.ThetaM n 0 s σ z) 1 = -(z 3) from rfl]
      simp only [sub_self, norm_zero]
      positivity
    · show ‖(KernelExt.ThetaM n h s σ z) 2 - (KernelExt.ThetaM n 0 s σ z) 2‖
          ≤ (Real.pi * Ck + 1) * D
      rw [show (KernelExt.ThetaM n h s σ z) 2 =
          -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s)
          from rfl,
        show (KernelExt.ThetaM n 0 s σ z) 2 =
          -(deriv (fun u : ℝ => (KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 0) s)
          from rfl]
      have hkey : -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s)
            - (-(deriv (fun u : ℝ => (KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 0) s))
          = -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s
              - deriv (fun u : ℝ => (KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 0) s) :=
        by ring
      rw [hkey, norm_neg]
      exact G2M_deriv_close_low n hh hsupp hDpos hD100 hjet hCk hs hσ hz0 hz1 hz3 0 (hd 0)
    · show ‖(KernelExt.ThetaM n h s σ z) 3 - (KernelExt.ThetaM n 0 s σ z) 3‖
          ≤ (Real.pi * Ck + 1) * D
      rw [show (KernelExt.ThetaM n h s σ z) 3 =
          -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s)
          from rfl,
        show (KernelExt.ThetaM n 0 s σ z) 3 =
          -(deriv (fun u : ℝ => (KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 1) s)
          from rfl]
      have hkey : -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s)
            - (-(deriv (fun u : ℝ => (KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 1) s))
          = -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s
              - deriv (fun u : ℝ => (KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 1) s) :=
        by ring
      rw [hkey, norm_neg]
      exact G2M_deriv_close_low n hh hsupp hDpos hD100 hjet hCk hs hσ hz0 hz1 hz3 1 (hd 1)
  rw [hzdef] at hTheta
  calc ‖KernelExt.ThetaM n h s σ (baseState σ) - KernelExt.ThetaM n 0 s σ (baseState σ)‖
      ≤ (Real.pi * Ck + 1) * D := hTheta

/-! ## 5. The frozen tail is small -/

theorem frozen_tail_close_low (n : ℕ) (hn : 1 ≤ n) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ),
        ‖(∫ σ in (19 / 20 : ℝ)..(1 : ℝ),
            (Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.baseState σ) -
             Work.OddVolterra.KernelExt.ThetaM n 0 s σ (Work.OddVolterra.baseState σ)))‖ < ε := by
  obtain ⟨K, hK0, hK⟩ := thetaM_tail_bound_low n hn
  intro ε hε
  set δ : ℝ := min (1 / 100) (20 * ε / (K + 1)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (by norm_num) (by positivity)
  have hδ100 : δ ≤ 1 / 100 := by rw [hδdef]; exact min_le_left _ _
  refine ⟨δ, hδpos, ?_⟩
  intro h hh hsupp hjet s hs
  have hpt : ∀ σ ∈ Set.uIoc (19 / 20 : ℝ) 1,
      ‖(Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.baseState σ) -
        Work.OddVolterra.KernelExt.ThetaM n 0 s σ (Work.OddVolterra.baseState σ))‖ ≤ K * δ := by
    intro σ hσ
    rw [Set.uIoc_of_le (by norm_num : (19 : ℝ) / 20 ≤ 1)] at hσ
    exact hK h δ hh hδpos hδ100 hsupp hjet s hs σ ⟨le_of_lt hσ.1, hσ.2⟩
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (19 / 20 : ℝ)) (b := 1) (C := K * δ) hpt
  have hlen : |(1 : ℝ) - 19 / 20| = 1 / 20 := by
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 - 19 / 20)]
    norm_num
  rw [hlen] at hmain
  refine lt_of_le_of_lt hmain ?_
  have hle : δ ≤ 20 * ε / (K + 1) := by rw [hδdef]; exact min_le_right _ _
  have h1 : K * δ ≤ K * (20 * ε / (K + 1)) := mul_le_mul_of_nonneg_left hle hK0
  have h2 : K * (20 * ε / (K + 1)) / 20 = ε * (K / (K + 1)) := by
    field_simp
  have h3 : K / (K + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have h4 : ε * (K / (K + 1)) < ε * 1 := mul_lt_mul_of_pos_left h3 hε
  linarith [h1, h2, h4]

end

end Work.OddVolterra.WinData
