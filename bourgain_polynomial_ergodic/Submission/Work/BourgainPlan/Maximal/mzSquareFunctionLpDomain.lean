import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.mz_square_function

open MeasureTheory
open scoped ENNReal BigOperators

set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger (rademacher_two_stage_lower rademacher_one_stage_upper
  mzAux_lintegral_fintype_sum mzAux_finset_sum_lintegral_le mzAux_key_ennreal)

/-! ## Helper lemmas: coefficient functions of `Lp`-linear combinations -/

/-- The (chosen) coefficient function of a finite sum of scalar multiples of `Lp` elements is a.e.
the pointwise sum of the scalar multiples of the coefficient functions. -/
lemma mzLp_coeFn_finset_smul_sum {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ENNReal}
    {β : Type*} (s : Finset β) (c : β → ℂ) (g : β → Lp ℂ q μ) :
    (((∑ b ∈ s, c b • g b : Lp ℂ q μ)) : α → ℂ) =ᵐ[μ]
      fun x => ∑ b ∈ s, c b * ((g b : Lp ℂ q μ) x) := by
  classical
  filter_upwards [Lp.coeFn_fun_finsetSum s (fun b => c b • g b),
    (Finset.eventually_all s).2 (fun b _ => Lp.coeFn_smul (c b) (g b))] with x hx hy
  rw [hx]
  exact Finset.sum_congr rfl fun b hb => by
    have hbb := hy b hb
    simpa only [Pi.smul_apply, smul_eq_mul] using hbb

/-- The coefficient function of a double sum of scalar multiples of `Lp` elements, a.e. -/
lemma mzLp_coeFn_sum_smul_sum_smul {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ENNReal}
    {β γ : Type*} (s : Finset β) (t : Finset γ) (c : β → ℂ) (d : β → γ → ℂ)
    (g : β → γ → Lp ℂ q μ) :
    (((∑ b ∈ s, c b • ∑ k ∈ t, d b k • g b k : Lp ℂ q μ)) : α → ℂ) =ᵐ[μ]
      fun x => ∑ b ∈ s, ∑ k ∈ t, c b * d b k * ((g b k : Lp ℂ q μ) x) := by
  classical
  filter_upwards [mzLp_coeFn_finset_smul_sum s c (fun b => ∑ k ∈ t, d b k • g b k),
    (Finset.eventually_all s).2 (fun b _ => mzLp_coeFn_finset_smul_sum t (d b) (g b))] with x hx hy
  rw [hx]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [hy b hb, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Marcinkiewicz–Zygmund for operators defined on `Lp`** (MST Lemma 2.30 / Tao `mz` with the
domain and target being `Lp`, not a pointwise function space).

`Work.BourgainPlan.IonescuWainger.mz_square_function` states the same estimate for operators that are
`IsLinearMap ℂ` on a genuine *pointwise* function space `X → ℂ`.  That hypothesis is unavailable for
the operators this corpus actually uses (`annulusConv`, `BoundaryLayer.multiplier`): the Bochner
integral is `0` off the integrable functions, and `↑(g₁ + g₂) ≠ ↑g₁ + ↑g₂` for `Lp` elements (only
a.e. equality).  Here the operators are honest `ℂ`-linear maps on `Lp ℂ (ofReal p)`, and both the
hypothesis and the conclusion are written in terms of the `lintegral` of the pointwise norms of
representatives — which is what the applications need.

Route (per the existing pointwise proof): copy the proof of
`Work.BourgainPlan.IonescuWainger.mz_square_function` (or of its `_dom` variant), replacing the
pointwise linearity identities by a.e. congruence (`Lp.coeFn_add`, `Lp.coeFn_smul`,
`Lp.coeFn_finset_sum`, which suffice since every step is an `∫⁻`); the two-stage Khintchine input is
`Work.BourgainPlan.IonescuWainger.rademacher_two_stage_lower` /
`rademacher_one_stage_upper`; `S_ω(F_η) = Σ_{i,t} ω_i η_t • T_i f_t` is now `Lp`-linearity.  Do
**not** try to reuse `mz_square_function_dom`: it needs a `ℂ`-linear `ρ : M →ₗ[ℂ] (X → ℂ)`, which
does not exist for `Lp`.  Internally one may need `haveI : Fact (1 ≤ ENNReal.ofReal p)` from `hp`. -/
theorem mzSquareFunctionLpDomain {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι κ : Type*} [Fintype ι] [Fintype κ]
      (T : ι → (MeasureTheory.Lp ℂ (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        →ₗ[ℂ] MeasureTheory.Lp ℂ (ENNReal.ofReal p)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)))
      (A : ℝ) (hA : 0 ≤ A)
      (hT : ∀ (ε : ι → Bool)
        (g : MeasureTheory.Lp ℂ (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ)),
        ∫⁻ y, ‖((∑ i : ι, (if ε i then (1 : ℂ) else -1) • T i g
            : MeasureTheory.Lp ℂ (ENNReal.ofReal p)
              (MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ → ℂ) y‖ₑ ^ p
          ≤ ENNReal.ofReal (A ^ p)
            * ∫⁻ x, ‖(g : ℝ → ℂ) x‖ₑ ^ p)
      (f : κ → MeasureTheory.Lp ℂ (ENNReal.ofReal p)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)),
      ∫⁻ y, (∑ i : ι, ∑ t : κ,
          ‖((T i (f t)) : ℝ → ℂ) y‖ₑ ^ (2 : ℝ)) ^ (p / 2)
        ≤ ENNReal.ofReal (C * A ^ p)
          * ∫⁻ x, (∑ t : κ, ‖((f t) : ℝ → ℂ) x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
  obtain ⟨c, hcpos, hc⟩ := rademacher_two_stage_lower p hp
  obtain ⟨Ck, hCkpos, hCk⟩ := rademacher_one_stage_upper p hp
  refine ⟨(1 / c) * Ck, by positivity, ?_⟩
  intro ι κ _ _ T A hA hT f
  classical
  set F : (κ → Bool) → Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
    fun η => ∑ t : κ, (if η t then (1 : ℂ) else -1) • f t with hF
  set V : (ι → Bool) → (κ → Bool) → Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
    fun ε η => ∑ i : ι, (if ε i then (1 : ℂ) else -1) • T i (F η) with hV
  set S : ℝ → ENNReal :=
    fun y => (∑ i : ι, ∑ t : κ, ‖((T i (f t)) : ℝ → ℂ) y‖ₑ ^ (2 : ℝ)) ^ (p / 2) with hS
  set G : ℝ → ENNReal :=
    fun x => (∑ t : κ, ‖((f t) : ℝ → ℂ) x‖ₑ ^ (2 : ℝ)) ^ (p / 2) with hG
  set P : ENNReal := ∫⁻ y, S y with hP
  set Q : ENNReal := ∫⁻ x, G x with hQ
  change P ≤ ENNReal.ofReal (((1 / c) * Ck) * A ^ p) * Q
  -- ## The hypothesis applied to the Rademacher combinations
  have hVbound : ∀ (ε : ι → Bool) (η : κ → Bool),
      ∫⁻ y, ‖(((V ε η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) y‖ₑ ^ p
        ≤ ENNReal.ofReal (A ^ p)
          * ∫⁻ x, ‖(((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x‖ₑ ^ p := by
    intro ε η
    have h := hT ε (F η)
    simpa only [hV] using h
  -- ## a.e. computation of `V` in terms of the `T i (f t)`
  have hVcoe : ∀ (ε : ι → Bool) (η : κ → Bool),
      (((V ε η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) =ᵐ[volume]
        fun y => ∑ i : ι, ∑ t : κ, (if ε i then (1 : ℂ) else -1)
          * (if η t then (1 : ℂ) else -1)
          * (((T i (f t) : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) y) := by
    intro ε η
    have hTsum : ∀ i : ι, T i (F η) = ∑ t : κ, (if η t then (1 : ℂ) else -1) • T i (f t) := by
      intro i
      have h1 : F η = ∑ t : κ, (if η t then (1 : ℂ) else -1) • f t := rfl
      rw [h1, map_sum]
      exact Finset.sum_congr rfl fun t _ => (map_smul (T i) (if η t then (1 : ℂ) else -1) (f t))
    have hEq : V ε η = ∑ i : ι, (if ε i then (1 : ℂ) else -1)
        • (∑ t : κ, (if η t then (1 : ℂ) else -1) • T i (f t)) := by
      simp only [hV]
      exact Finset.sum_congr rfl fun i _ => by rw [hTsum i]
    rw [hEq]
    refine (mzLp_coeFn_sum_smul_sum_smul Finset.univ Finset.univ
      (fun i : ι => if ε i then (1 : ℂ) else -1)
      (fun (_ : ι) (t : κ) => if η t then (1 : ℂ) else -1)
      (fun (i : ι) (t : κ) => T i (f t))).trans ?_
    filter_upwards with y
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => rfl
  -- ## Two-stage Khintchine, almost everywhere
  have hpt : ∀ᵐ y ∂volume, ENNReal.ofReal c * S y ≤
      (∑ ε : ι → Bool, ∑ η : κ → Bool,
          ‖(((V ε η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) y‖ₑ ^ p)
        * ((Fintype.card (ι → Bool) : ENNReal) * (Fintype.card (κ → Bool) : ENNReal))⁻¹ := by
    have hVall : ∀ᵐ y ∂volume, ∀ ε : ι → Bool, ∀ η : κ → Bool,
        (((V ε η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) y
          = ∑ i : ι, ∑ t : κ, (if ε i then (1 : ℂ) else -1) * (if η t then (1 : ℂ) else -1)
              * (((T i (f t) : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) y) :=
      Filter.eventually_all.mpr (fun ε => Filter.eventually_all.mpr (fun η => hVcoe ε η))
    filter_upwards [hVall] with y hy
    have h := hc (fun (i : ι) (t : κ) =>
      (((T i (f t) : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) y))
    have hS_y : S y = (∑ i : ι, ∑ t : κ,
        ‖(((T i (f t) : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) y)‖ₑ ^ (2 : ℝ))
          ^ (p / 2) := rfl
    rw [hS_y]
    have hsum_eq : (∑ ε : ι → Bool, ∑ η : κ → Bool,
        ‖∑ i : ι, ∑ t : κ, (if ε i then (1 : ℂ) else -1) * (if η t then (1 : ℂ) else -1)
          * (((T i (f t) : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) y)‖ₑ ^ p)
        = ∑ ε : ι → Bool, ∑ η : κ → Bool,
            ‖(((V ε η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) y‖ₑ ^ p := by
      refine Finset.sum_congr rfl fun ε _ => Finset.sum_congr rfl fun η _ => ?_
      rw [hy ε η]
    rw [hsum_eq] at h
    exact h
  -- ## The averaging step
  have hNa : ((Fintype.card (ι → Bool) : ENNReal) * (Fintype.card (κ → Bool) : ENNReal))⁻¹
      * ((Fintype.card (ι → Bool) : ENNReal) * (Fintype.card (κ → Bool) : ENNReal)) = 1 :=
    ENNReal.inv_mul_cancel (by simp [mul_eq_zero]) (by simp [ENNReal.mul_ne_top])
  have hint1 : ∫⁻ y, ENNReal.ofReal c * S y = ENNReal.ofReal c * P :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hmeasV : ∀ (ε : ι → Bool) (η : κ → Bool),
      AEMeasurable (fun y =>
        ‖(((V ε η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) y‖ₑ ^ p) volume :=
    fun ε η => (Lp.aestronglyMeasurable (V ε η)).enorm.pow_const p
  have hint2 : (∑ ε : ι → Bool, ∑ η : κ → Bool,
        ∫⁻ y, ‖(((V ε η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) y‖ₑ ^ p)
      = ∫⁻ y, ∑ ε : ι → Bool, ∑ η : κ → Bool,
          ‖(((V ε η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) y‖ₑ ^ p := by
    rw [mzAux_lintegral_fintype_sum (fun ε y => ∑ η : κ → Bool,
      ‖(((V ε η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) y‖ₑ ^ p)
      (fun ε => Finset.aemeasurable_fun_sum Finset.univ (fun η _ => hmeasV ε η))]
    apply Finset.sum_congr rfl
    intro ε _
    rw [mzAux_lintegral_fintype_sum (fun η y =>
      ‖(((V ε η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) y‖ₑ ^ p)
      (fun η => hmeasV ε η)]
  have hInt1 : ENNReal.ofReal c * P ≤
      ((Fintype.card (ι → Bool) : ENNReal) * (Fintype.card (κ → Bool) : ENNReal))⁻¹
        * ∑ ε : ι → Bool, ∑ η : κ → Bool,
            ∫⁻ y, ‖(((V ε η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) y‖ₑ ^ p := by
    calc ENNReal.ofReal c * P
        = ∫⁻ y, ENNReal.ofReal c * S y := hint1.symm
      _ ≤ ∫⁻ y, (∑ ε : ι → Bool, ∑ η : κ → Bool,
              ‖(((V ε η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) y‖ₑ ^ p)
            * ((Fintype.card (ι → Bool) : ENNReal)
              * (Fintype.card (κ → Bool) : ENNReal))⁻¹ := lintegral_mono_ae hpt
      _ = ∫⁻ y, ((Fintype.card (ι → Bool) : ENNReal)
              * (Fintype.card (κ → Bool) : ENNReal))⁻¹
            * (∑ ε : ι → Bool, ∑ η : κ → Bool,
              ‖(((V ε η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) y‖ₑ ^ p) := by
          apply lintegral_congr
          intro y
          exact mul_comm _ _
      _ = ((Fintype.card (ι → Bool) : ENNReal)
              * (Fintype.card (κ → Bool) : ENNReal))⁻¹
            * ∫⁻ y, ∑ ε : ι → Bool, ∑ η : κ → Bool,
              ‖(((V ε η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) y‖ₑ ^ p := by
          rw [lintegral_const_mul' _ _
            (ENNReal.inv_ne_top.mpr (by simp [mul_eq_zero]))]
      _ = _ := by rw [hint2]
  -- ## The `X`-side (input) Khintchine bound
  have hXcoe : ∀ η : κ → Bool,
      (((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) =ᵐ[volume]
        fun x => ∑ t : κ, (if η t then (1 : ℂ) else -1)
          * (((f t : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) x) := by
    intro η
    simpa only [hF] using
      mzLp_coeFn_finset_smul_sum (μ := (volume : Measure ℝ)) Finset.univ
        (fun t : κ => (if η t then (1 : ℂ) else -1)) f
  have hXsum2 : (∑ ε : ι → Bool, ∑ η : κ → Bool,
        ∫⁻ y, ‖(((V ε η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) y‖ₑ ^ p)
      ≤ ENNReal.ofReal (A ^ p) * ((Fintype.card (ι → Bool) : ENNReal)
          * (∑ η : κ → Bool,
            ∫⁻ x, ‖(((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x‖ₑ ^ p)) := by
    calc ∑ ε : ι → Bool, ∑ η : κ → Bool,
          ∫⁻ y, ‖(((V ε η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) y‖ₑ ^ p
        ≤ ∑ ε : ι → Bool, ∑ η : κ → Bool,
            ENNReal.ofReal (A ^ p)
              * ∫⁻ x, ‖(((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x‖ₑ ^ p :=
          Finset.sum_le_sum fun ε _ => Finset.sum_le_sum fun η _ => hVbound ε η
      _ = ∑ ε : ι → Bool, ENNReal.ofReal (A ^ p)
            * (∑ η : κ → Bool,
              ∫⁻ x, ‖(((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x‖ₑ ^ p) := by
          apply Finset.sum_congr rfl
          intro ε _
          rw [Finset.mul_sum]
      _ = (Fintype.card (ι → Bool) : ENNReal)
            * (ENNReal.ofReal (A ^ p) * (∑ η : κ → Bool,
              ∫⁻ x, ‖(((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x‖ₑ ^ p)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ENNReal.ofReal (A ^ p) * ((Fintype.card (ι → Bool) : ENNReal)
            * (∑ η : κ → Bool,
              ∫⁻ x, ‖(((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x‖ₑ ^ p)) := by
          ring
  have hXpt : ∀ᵐ x ∂volume, (∑ η : κ → Bool,
        ‖(((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x‖ₑ ^ p)
      ≤ (Fintype.card (κ → Bool) : ENNReal) * (ENNReal.ofReal Ck * G x) := by
    have hFall : ∀ᵐ x ∂volume, ∀ η : κ → Bool,
        (((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x
          = ∑ t : κ, (if η t then (1 : ℂ) else -1)
              * (((f t : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) x) :=
      Filter.eventually_all.mpr (fun η => hXcoe η)
    filter_upwards [hFall] with x hx
    have h := hCk (fun t : κ =>
      (((f t : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) x))
    have hsum_eq : (∑ η : κ → Bool, ‖∑ t : κ, (if η t then (1 : ℂ) else -1)
          * (((f t : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) x)‖ₑ ^ p)
        = ∑ η : κ → Bool,
          ‖(((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x‖ₑ ^ p := by
      refine Finset.sum_congr rfl fun η _ => ?_
      rw [hx η]
    rw [hsum_eq] at h
    have hGx : G x = (∑ t : κ,
        ‖(((f t : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) x)‖ₑ ^ (2 : ℝ))
          ^ (p / 2) := rfl
    have h' : (∑ η : κ → Bool,
          ‖(((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x‖ₑ ^ p)
          * (Fintype.card (κ → Bool) : ENNReal)⁻¹
        ≤ ENNReal.ofReal Ck * G x := h
    clear h
    calc ∑ η : κ → Bool,
          ‖(((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x‖ₑ ^ p
        = 1 * (∑ η : κ → Bool,
          ‖(((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x‖ₑ ^ p) :=
          (one_mul _).symm
      _ = ((Fintype.card (κ → Bool) : ENNReal)⁻¹ * (Fintype.card (κ → Bool) : ENNReal))
            * (∑ η : κ → Bool,
              ‖(((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x‖ₑ ^ p) := by
          rw [ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _)]
      _ = (Fintype.card (κ → Bool) : ENNReal)
            * ((∑ η : κ → Bool,
                ‖(((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x‖ₑ ^ p)
              * (Fintype.card (κ → Bool) : ENNReal)⁻¹) := by ring
      _ ≤ (Fintype.card (κ → Bool) : ENNReal)
            * (ENNReal.ofReal Ck * (∑ t : κ,
                ‖(((f t : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) x)‖ₑ ^ (2 : ℝ))
                  ^ (p / 2)) := mul_le_mul_right h' _
      _ = (Fintype.card (κ → Bool) : ENNReal) * (ENNReal.ofReal Ck * G x) := by rw [hGx]
  have hXsum : (∑ η : κ → Bool,
        ∫⁻ x, ‖(((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x‖ₑ ^ p)
      ≤ (Fintype.card (κ → Bool) : ENNReal) * (ENNReal.ofReal Ck * Q) := by
    calc ∑ η : κ → Bool,
          ∫⁻ x, ‖(((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x‖ₑ ^ p
        ≤ ∫⁻ x, ∑ η : κ → Bool,
          ‖(((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x‖ₑ ^ p :=
          mzAux_finset_sum_lintegral_le Finset.univ _
      _ ≤ ∫⁻ x, (Fintype.card (κ → Bool) : ENNReal) * (ENNReal.ofReal Ck * G x) :=
          lintegral_mono_ae hXpt
      _ = (Fintype.card (κ → Bool) : ENNReal) * (ENNReal.ofReal Ck * ∫⁻ x, G x) := by
          rw [lintegral_const_mul' (Fintype.card (κ → Bool) : ENNReal)
            (fun x => ENNReal.ofReal Ck * G x) (ENNReal.natCast_ne_top _),
            lintegral_const_mul' (ENNReal.ofReal Ck) G ENNReal.ofReal_ne_top]
      _ = (Fintype.card (κ → Bool) : ENNReal) * (ENNReal.ofReal Ck * Q) := by rw [hQ]
  -- ## Putting the pieces together
  have hchain : ENNReal.ofReal c * P ≤ ENNReal.ofReal (A ^ p) * ENNReal.ofReal Ck * Q := by
    calc ENNReal.ofReal c * P
        ≤ ((Fintype.card (ι → Bool) : ENNReal)
              * (Fintype.card (κ → Bool) : ENNReal))⁻¹
            * (∑ ε : ι → Bool, ∑ η : κ → Bool,
                ∫⁻ y, ‖(((V ε η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) y‖ₑ ^ p) :=
          hInt1
      _ ≤ ((Fintype.card (ι → Bool) : ENNReal)
              * (Fintype.card (κ → Bool) : ENNReal))⁻¹
            * (ENNReal.ofReal (A ^ p) * ((Fintype.card (ι → Bool) : ENNReal)
                * (∑ η : κ → Bool,
                  ∫⁻ x, ‖(((F η : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))) : ℝ → ℂ) x‖ₑ ^ p))) :=
          mul_le_mul_right hXsum2 _
      _ ≤ ((Fintype.card (ι → Bool) : ENNReal)
              * (Fintype.card (κ → Bool) : ENNReal))⁻¹
            * (ENNReal.ofReal (A ^ p) * ((Fintype.card (ι → Bool) : ENNReal)
                * ((Fintype.card (κ → Bool) : ENNReal) * (ENNReal.ofReal Ck * Q)))) := by
          refine mul_le_mul_right ?_ _
          refine mul_le_mul_right ?_ _
          exact mul_le_mul_right hXsum _
      _ = ENNReal.ofReal (A ^ p) * (ENNReal.ofReal Ck * Q) :=
          mzAux_key_ennreal _ _ _ _ hNa
      _ = ENNReal.ofReal (A ^ p) * ENNReal.ofReal Ck * Q := by ring
  have hfin : P ≤ ENNReal.ofReal (((1 / c) * Ck) * A ^ p) * Q := by
    have hc0 : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hcpos)
    have hct : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
    have h1 : P = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * P) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
    have h2 : (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal (A ^ p) * ENNReal.ofReal Ck * Q)
        = ENNReal.ofReal (((1 / c) * Ck) * A ^ p) * Q := by
      rw [one_div, ENNReal.ofReal_mul (le_of_lt (mul_pos (inv_pos.mpr hcpos) hCkpos)),
        ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hcpos)), ENNReal.ofReal_inv_of_pos hcpos]
      ring
    calc P = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * P) := h1
      _ ≤ (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal (A ^ p) * ENNReal.ofReal Ck * Q) :=
          mul_le_mul_right hchain _
      _ = ENNReal.ofReal (((1 / c) * Ck) * A ^ p) * Q := h2
  exact hfin

end Work.BourgainPlan.Maximal
