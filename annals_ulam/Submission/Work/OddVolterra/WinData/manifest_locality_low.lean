import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddCurveB.Existence.Explicit

/-!
# Locality of the odd Volterra data below the transition window

The perturbation `h` of the odd transition-slope argument is supported in the window
`[1 - 2τ, 1 - τ] = [4/5, 9/10]`, so `h` vanishes on `(-∞, 4/5)`.  Every object attached to
slopes `s, σ < 4/5` — the manifest kernel `KvecM`/`G2M`/`ThetaM` and the paper's diagonal datum
`Godd` — depends on `h` only through values of `h` and its derivatives *at points below* `4/5`,
hence it coincides with the same object built from `h ≡ 0`.

The two structural facts used are

* `Rnu_eqOn`: the recursive Bell numerator `Rnu` is local in `Zrad`, i.e. if two radicands agree
  on an open set `U` (and the two `init` agree there) then the numerators agree on `U` — this is
  the induction step `R_{m+1} = Z ∂_s R_m + (ν-m)(∂_s Z) R_m` using that `fderiv` is a local
  operation (`Filter.EventuallyEq.fderiv_eq`);
* `Godd_eq_GoddDiag` (`Work.OddCurveB.Existence.Explicit`): `Godd n h s z` depends on `h` only
  through `h s` and `h'(s)`, and both vanish for `s < 4/5`.
-/

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Work.OddVolterra

noncomputable section

/-! ## Elementary facts about `h` vanishing below `4/5` -/

lemma deriv_zero_fun {x : ℝ} : deriv (0 : ℝ → ℝ) x = 0 := by simp

lemma deriv_eq_zero_of_lt {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) {x : ℝ}
    (hx : x < 4 / 5) : deriv h x = 0 := by
  have hev : h =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) :=
    Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Iio hx) (fun y hy => hz y hy)
  rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]

/-- A convex combination of `u` and `σ` is at most `max u σ`. -/
lemma convex_le_max (u σ τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    u + τ * (σ - u) ≤ max u σ := by
  rcases le_total u σ with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

/-- The open region `{s < 4/5} × {σ < 4/5}` of exponent pairs, on which the radicand
`Zrad` built from `h` and from `h ≡ 0` agree. -/
def LocLow : Set (ℝ × ℝ × ℝ) := {p | p.1 < 4 / 5 ∧ p.2.1 < 4 / 5}

lemma isOpen_LocLow : IsOpen LocLow := by
  have h1 : Continuous (fun p : ℝ × ℝ × ℝ => p.1) := continuous_fst
  have h2 : Continuous (fun p : ℝ × ℝ × ℝ => p.2.1) := continuous_fst.comp continuous_snd
  exact (isOpen_lt h1 continuous_const).inter (isOpen_lt h2 continuous_const)

lemma line_eq_of_lt {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) {s : ℝ}
    (hs : s < 4 / 5) (t : ℝ) : line h s t = line 0 s t := by
  unfold line
  rw [hz s hs]
  simp

lemma lineSlope_eq_of_lt {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) {s : ℝ}
    (hs : s < 4 / 5) (t : ℝ) : lineSlope h s t = lineSlope 0 s t := by
  unfold lineSlope
  rw [deriv_eq_zero_of_lt hz hs, deriv_zero_fun]

/-- `Zrad h` and `Zrad 0` agree on `LocLow`. -/
lemma Zrad_eqOn {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) :
    Set.EqOn (KernelExt.Zrad h) (KernelExt.Zrad 0) LocLow := by
  intro p hp
  have hp1 : p.1 < 4 / 5 := hp.1
  have hp2 : p.2.1 < 4 / 5 := hp.2
  simp only [KernelExt.Zrad]
  rw [line_eq_of_lt hz hp2 p.2.2, line_eq_of_lt hz hp1 p.2.2]

lemma hquot_eq_of_lt {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) {s σ : ℝ}
    (hs : s < 4 / 5) (hσ : σ < 4 / 5) : hquot h s σ = hquot 0 s σ := by
  unfold hquot
  apply intervalIntegral.integral_congr
  intro τ hτ
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
  simp only []
  rw [deriv_eq_zero_of_lt hz
        (lt_of_le_of_lt (convex_le_max s σ τ hτ.1 hτ.2) (max_lt hs hσ)), deriv_zero_fun]

lemma Kden_eq_of_lt {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) {s σ t : ℝ}
    (hs : s < 4 / 5) (hσ : σ < 4 / 5) : Kden h s σ t = Kden 0 s σ t := by
  unfold Kden
  rw [hquot_eq_of_lt hz hs hσ, line_eq_of_lt hz hσ t, line_eq_of_lt hz hs t]

/-! ## Locality of the recursive numerator `Rnu` -/

/-- The recursive Bell numerator is local: if the two radicands agree on an open set `U` and the
two `init` agree on `U`, then all the numerators agree on `U`. -/
lemma Rnu_eqOn {ν : ℝ} {h g : ℝ → ℝ} {init init' : ℝ × ℝ × ℝ → ℝ}
    (hZ : Set.EqOn (KernelExt.Zrad h) (KernelExt.Zrad g) LocLow)
    (hi : Set.EqOn init init' LocLow) (m : ℕ) :
    Set.EqOn (KernelExt.Rnu ν h init m) (KernelExt.Rnu ν g init' m) LocLow := by
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
        Filter.eventually_of_mem (isOpen_LocLow.mem_nhds hp) (fun q hq => ih hq)
      have hevZ : KernelExt.Zrad h =ᶠ[𝓝 p] KernelExt.Zrad g :=
        Filter.eventually_of_mem (isOpen_LocLow.mem_nhds hp) (fun q hq => hZ hq)
      rw [Filter.EventuallyEq.fderiv_eq hevR, Filter.EventuallyEq.fderiv_eq hevZ,
        hZ hp, ih hp]

lemma J1M_eq_of_lt (n : ℕ) {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) {s σ t : ℝ}
    (hs : s < 4 / 5) (hσ : σ < 4 / 5) :
    KernelExt.J1M n h s σ t = KernelExt.J1M n 0 s σ t :=
  Rnu_eqOn (Zrad_eqOn hz) (fun _ _ => rfl) (n + 1) ⟨hs, hσ⟩

lemma lineSlope_eqOn {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) :
    Set.EqOn (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2)
      (fun p : ℝ × ℝ × ℝ => lineSlope 0 p.1 p.2.2) LocLow := by
  intro p hp
  exact lineSlope_eq_of_lt hz hp.1 p.2.2

lemma J2M_eq_of_lt (n : ℕ) {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) {s σ t : ℝ}
    (hs : s < 4 / 5) (hσ : σ < 4 / 5) :
    KernelExt.J2M n h s σ t = KernelExt.J2M n 0 s σ t :=
  Rnu_eqOn (Zrad_eqOn hz) (lineSlope_eqOn hz) n ⟨hs, hσ⟩

/-! ## Locality of the manifest kernel -/

lemma K1M_eq_of_lt (n : ℕ) {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) {s σ t : ℝ}
    (hs : s < 4 / 5) (hσ : σ < 4 / 5) :
    KernelExt.K1M n h s σ t = KernelExt.K1M n 0 s σ t := by
  unfold KernelExt.K1M
  rw [J1M_eq_of_lt n hz hs hσ, Kden_eq_of_lt hz hs hσ]

lemma K2M_eq_of_lt (n : ℕ) {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) {s σ t : ℝ}
    (hs : s < 4 / 5) (hσ : σ < 4 / 5) :
    KernelExt.K2M n h s σ t = KernelExt.K2M n 0 s σ t := by
  unfold KernelExt.K2M
  rw [J2M_eq_of_lt n hz hs hσ, Kden_eq_of_lt hz hs hσ]

lemma KvecM_eq_of_lt (n : ℕ) {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) {s σ : ℝ}
    (hs : s < 4 / 5) (hσ : σ < 4 / 5) (x y x' y' : ℝ) :
    KernelExt.KvecM n h s σ x y x' y' = KernelExt.KvecM n 0 s σ x y x' y' := by
  funext i
  fin_cases i <;>
    simp [KernelExt.KvecM, K1M_eq_of_lt n hz hs hσ, K2M_eq_of_lt n hz hs hσ]

lemma G2M_eq_of_lt (n : ℕ) {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) {s σ : ℝ}
    (hs : s < 4 / 5) (hσ : σ < 4 / 5) (x y x' y' : ℝ) :
    KernelExt.G2M n h s σ x y x' y' = KernelExt.G2M n 0 s σ x y x' y' := by
  funext i
  simp only [KernelExt.G2M]
  apply intervalIntegral.integral_congr
  intro τ hτ
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
  simp only []
  rw [KvecM_eq_of_lt n hz
    (lt_of_le_of_lt (convex_le_max s σ τ hτ.1 hτ.2) (max_lt hs hσ)) hσ x y x' y']

/-- Eventually-equal form of `G2M_eq_of_lt` at a fixed left endpoint `s < 4/5`. -/
lemma G2M_eventuallyEq (n : ℕ) {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0) {s σ : ℝ}
    (hs : s < 4 / 5) (hσ : σ < 4 / 5) (x y x' y' : ℝ) :
    (fun u => KernelExt.G2M n h u σ x y x' y') =ᶠ[𝓝 s]
      (fun u => KernelExt.G2M n 0 u σ x y x' y') :=
  Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Iio hs)
    (fun _ hu => G2M_eq_of_lt n hz hu hσ x y x' y')

lemma ThetaM_eq_of_lt (n : ℕ) {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0)
    {s σ : ℝ} (hs : s < 4 / 5) (hσ : σ < 4 / 5) (z : St) :
    KernelExt.ThetaM n h s σ z = KernelExt.ThetaM n 0 s σ z := by
  have hc : ∀ i : Fin 2,
      deriv (fun u => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) i) s =
      deriv (fun u => (KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) i) s := by
    intro i
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [G2M_eventuallyEq n hz hs hσ (z 0) (z 1) (z 2) (z 3)] with u hu
    exact congrArg (fun v : Fin 2 → ℝ => v i) hu
  funext j
  fin_cases j <;> simp [KernelExt.ThetaM, hc]

/-! ## Locality of `Godd` -/

lemma Godd_eq_of_lt (n : ℕ) {h : ℝ → ℝ} (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0)
    {s : ℝ} (hs : s < 4 / 5) (z : St) : Godd n h s z = Godd n 0 s z := by
  rw [Work.OddCurveB.Existence.Godd_eq_GoddDiag n h s z,
      Work.OddCurveB.Existence.Godd_zero_eq n s z, hz s hs, deriv_eq_zero_of_lt hz hs]

theorem manifest_locality_low (n : ℕ) {h : ℝ → ℝ}
    (hz : ∀ x : ℝ, x < 4 / 5 → h x = 0)
    {s σ : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ))
    (hσ : σ ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ)) (z : Work.OddVolterra.St) :
    (Work.OddVolterra.KernelExt.ThetaM n h s σ z =
        Work.OddVolterra.KernelExt.ThetaM n 0 s σ z) ∧
      (Work.OddVolterra.Godd n h s z = Work.OddVolterra.Godd n 0 s z) := by
  have hs' : s < 4 / 5 := by linarith [hs.2]
  have hσ' : σ < 4 / 5 := by linarith [hσ.2]
  exact ⟨ThetaM_eq_of_lt n hz hs' hσ' z, Godd_eq_of_lt n hz hs' z⟩

end

end Work.OddVolterra.WinData
