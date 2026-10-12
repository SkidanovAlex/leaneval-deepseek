import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.SlotProjAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

set_option autoImplicit false

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-!
## Measure-theoretic and topological inputs for the single-slot projection

The proofs below are the measurable/bounded twins of those in
`Submission/Work/BoseBoxFock/slotProj1_idem_comm.lean` (which assumes `Φ` continuous and
compactly supported).  Here `Φ` is only measurable and bounded, so the two-variable integrand of
the Fubini argument is no longer continuous: it is a *continuous compactly supported kernel* times
a *bounded measurable state*, and its integrability is
`integrable_mul_of_continuous_hasCompactSupport_of_bounded` (`SlotProjAux`).
-/

/-- `PV e a ·` is compactly supported when the modes are. -/
theorem hasCompactSupport_PV_snd {m : ℕ} (e : Fin m → Ω → ℂ)
    (hec : ∀ l, HasCompactSupport (e l)) (a : Ω) :
    HasCompactSupport (fun y : Ω => PV e a y) := by
  refine HasCompactSupport.intro (isCompact_iUnion (fun l : Fin m => (hec l).isCompact)) ?_
  intro y hy
  exact PV_eq_zero_of_factors e
    (fun l => image_eq_zero_of_notMem_tsupport (fun h => hy (Set.mem_iUnion.mpr ⟨l, h⟩)))

/-- `PV e w v` vanishes when `v` lies outside the support of every mode. -/
theorem PV_eq_zero_of_notMem_iUnion {m : ℕ} (e : Fin m → Ω → ℂ) {w v : Ω}
    (hv : v ∉ ⋃ l : Fin m, tsupport (e l)) : PV e w v = 0 :=
  PV_eq_zero_of_factors e
    (fun l => image_eq_zero_of_notMem_tsupport (fun h => hv (Set.mem_iUnion.mpr ⟨l, h⟩)))

/-- `(w, v) ↦ PV e a w * PV e b v` is compactly supported. -/
theorem hasCompactSupport_PV_prod {m : ℕ} (e : Fin m → Ω → ℂ)
    (hec : ∀ l, HasCompactSupport (e l)) (a b : Ω) :
    HasCompactSupport (fun p : Ω × Ω => PV e a p.1 * PV e b p.2) := by
  refine HasCompactSupport.intro
    ((hasCompactSupport_PV_snd e hec a).isCompact.prod
      (hasCompactSupport_PV_snd e hec b).isCompact) ?_
  rintro ⟨w, v⟩ hpv
  by_cases hw : w ∈ tsupport (fun y : Ω => PV e a y)
  · have hv : v ∉ tsupport (fun y : Ω => PV e b y) := fun hv => hpv ⟨hw, hv⟩
    simp [image_eq_zero_of_notMem_tsupport hv]
  · simp [image_eq_zero_of_notMem_tsupport hw]

/-- `(w, v) ↦ PV e a w * PV e w v` is compactly supported. -/
theorem hasCompactSupport_PV_mul_self {m : ℕ} (e : Fin m → Ω → ℂ)
    (hec : ∀ l, HasCompactSupport (e l)) (a : Ω) :
    HasCompactSupport (fun p : Ω × Ω => PV e a p.1 * PV e p.1 p.2) := by
  refine HasCompactSupport.intro
    ((hasCompactSupport_PV_snd e hec a).isCompact.prod
      (isCompact_iUnion (fun l : Fin m => (hec l).isCompact))) ?_
  rintro ⟨w, v⟩ hpv
  by_cases hw : w ∈ tsupport (fun y : Ω => PV e a y)
  · have hv : v ∉ ⋃ l : Fin m, tsupport (e l) := fun hv => hpv ⟨hw, hv⟩
    simp [PV_eq_zero_of_notMem_iUnion e hv]
  · simp [image_eq_zero_of_notMem_tsupport hw]

/-- `(w, v) ↦ PV e a w * PV e b v` is continuous. -/
theorem continuous_PV_prod {m : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l)) (a b : Ω) :
    Continuous (fun p : Ω × Ω => PV e a p.1 * PV e b p.2) :=
  ((continuous_PV_snd e he a).comp continuous_fst).mul
    ((continuous_PV_snd e he b).comp continuous_snd)

/-- `(w, v) ↦ PV e a w * PV e w v` is continuous. -/
theorem continuous_PV_mul_self {m : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l)) (a : Ω) :
    Continuous (fun p : Ω × Ω => PV e a p.1 * PV e p.1 p.2) :=
  ((continuous_PV_snd e he a).comp continuous_fst).mul (continuous_PV_uncurry e he)

/-- A continuous compactly supported kernel times a bounded measurable state is integrable. -/
theorem integrable_uncurry_of_cont_cs {g h : Ω × Ω → ℂ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hm : Measurable h)
    (hb : ∃ C, ∀ p, ‖h p‖ ≤ C) :
    Integrable (fun p : Ω × Ω => g p * h p) (volume.prod volume) :=
  integrable_mul_of_continuous_hasCompactSupport_of_bounded hg hgc hm.aestronglyMeasurable hb

/-- The mode overlaps are integrable (the `hint` of `integral_PV_mul_PV`). -/
theorem integrable_star_mul_mode {m : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l)) :
    ∀ l l' : Fin m, Integrable (fun z : Ω => star (e l z) * e l' z) := by
  intro l l'
  have hcont : Continuous (fun z : Ω => star (e l z) * e l' z) :=
    (continuous_star.comp (he l)).mul (he l')
  have hcs : HasCompactSupport (fun z : Ω => star (e l z) * e l' z) :=
    ((hec l).comp_left (g := star) (by simp : star (0 : ℂ) = 0)).mul_right (f' := e l')
  exact hcont.integrable_of_hasCompactSupport hcs

/-- The map `p ↦ Function.update x i p.2` is measurable. -/
theorem measurable_update_snd {ι : Type*} [DecidableEq ι] (x : ι → Ω) (i : ι) :
    Measurable (fun p : Ω × Ω => Function.update x i p.2) :=
  (measurable_update (f := x) (a := i)).comp measurable_snd

/-- The map `p ↦ Function.update (Function.update x j p.2) i p.1` is measurable. -/
theorem measurable_update_update {ι : Type*} [DecidableEq ι] (x : ι → Ω) (i j : ι) :
    Measurable (fun p : Ω × Ω => Function.update (Function.update x j p.2) i p.1) := by
  rw [measurable_pi_iff]
  intro k
  by_cases hk : k = i
  · subst hk; simpa using measurable_fst
  · by_cases hk' : k = j
    · subst hk'; simpa [hk] using measurable_snd
    · simp [hk, hk']

/-- The two-variable integrand of the idempotence computation is integrable. -/
theorem integrable_uncurry_idem {m : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    {ι : Type*} [DecidableEq ι] (Φ : (ι → Ω) → ℂ) (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ y, ‖Φ y‖ ≤ C) (x : ι → Ω) (i : ι) :
    Integrable (Function.uncurry (fun w v : Ω =>
      PV e (x i) w * (PV e w v * Φ (Function.update x i v)))) (volume.prod volume) := by
  refine (integrable_uncurry_of_cont_cs (g := fun p : Ω × Ω => PV e (x i) p.1 * PV e p.1 p.2)
    (continuous_PV_mul_self e he (x i)) (hasCompactSupport_PV_mul_self e hec (x i))
    (hΦm.comp (measurable_update_snd x i)) ?_).congr ?_
  · obtain ⟨C, hC⟩ := hΦb
    exact ⟨C, fun p => hC _⟩
  · filter_upwards with p
    simp only [Function.uncurry, Function.comp_apply]
    ring

/-- The two-variable integrand of the commutation computation is integrable. -/
theorem integrable_uncurry_comm {m : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    {ι : Type*} [DecidableEq ι] (Φ : (ι → Ω) → ℂ) (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ y, ‖Φ y‖ ≤ C) (x : ι → Ω) (i j : ι) :
    Integrable (Function.uncurry (fun w v : Ω =>
      PV e (x i) w * (PV e (x j) v * Φ (Function.update (Function.update x j v) i w))))
      (volume.prod volume) := by
  refine (integrable_uncurry_of_cont_cs (g := fun p : Ω × Ω => PV e (x i) p.1 * PV e (x j) p.2)
    (continuous_PV_prod e he (x i) (x j)) (hasCompactSupport_PV_prod e hec (x i) (x j))
    (hΦm.comp (measurable_update_update x i j)) ?_).congr ?_
  · obtain ⟨C, hC⟩ := hΦb
    exact ⟨C, fun p => hC _⟩
  · filter_upwards with p
    simp only [Function.uncurry, Function.comp_apply]
    ring

/-! ## Idempotence and commutation of the single-slot projections -/

/-- **Idempotence of the single-slot projection**, for a bounded measurable state. -/
theorem slotProj1_idemMB {m : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    {ι : Type*} [DecidableEq ι] (Φ : (ι → Ω) → ℂ) (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ y, ‖Φ y‖ ≤ C) (i : ι) :
    slotProj1 e i (slotProj1 e i Φ) = slotProj1 e i Φ := by
  classical
  have hint : ∀ l l' : Fin m, Integrable (fun z : Ω => star (e l z) * e l' z) :=
    integrable_star_mul_mode e he hec
  funext x
  have h1 : slotProj1 e i (slotProj1 e i Φ) x
      = ∫ w, PV e (x i) w * (∫ v, PV e w v * Φ (Function.update x i v)) := by
    rw [slotProj1]
    apply integral_congr_ae
    filter_upwards with w
    have hstep : slotProj1 e i Φ (Function.update x i w)
        = ∫ v, PV e w v * Φ (Function.update x i v) := by
      rw [slotProj1]
      apply integral_congr_ae
      filter_upwards with v
      rw [Function.update_self, Function.update_idem]
    rw [hstep, ← integral_const_mul]
  have h2 : (∫ w, PV e (x i) w * (∫ v, PV e w v * Φ (Function.update x i v)))
      = ∫ w, ∫ v, PV e (x i) w * (PV e w v * Φ (Function.update x i v)) := by
    apply integral_congr_ae
    filter_upwards with w
    rw [integral_const_mul]
  have h3 : (∫ w, ∫ v, PV e (x i) w * (PV e w v * Φ (Function.update x i v)))
      = ∫ v, ∫ w, PV e (x i) w * (PV e w v * Φ (Function.update x i v)) :=
    integral_integral_swap (integrable_uncurry_idem e he hec Φ hΦm hΦb x i)
  have h4 : (∫ v, ∫ w, PV e (x i) w * (PV e w v * Φ (Function.update x i v)))
      = ∫ v, PV e (x i) v * Φ (Function.update x i v) := by
    apply integral_congr_ae
    filter_upwards with v
    rw [show (fun w : Ω => PV e (x i) w * (PV e w v * Φ (Function.update x i v)))
        = (fun w : Ω => (PV e (x i) w * PV e w v) * Φ (Function.update x i v))
      from funext fun w => by ring]
    rw [integral_mul_const, integral_PV_mul_PV e horth hint (x i) v]
  calc slotProj1 e i (slotProj1 e i Φ) x
      = ∫ w, PV e (x i) w * (∫ v, PV e w v * Φ (Function.update x i v)) := h1
    _ = ∫ w, ∫ v, PV e (x i) w * (PV e w v * Φ (Function.update x i v)) := h2
    _ = ∫ v, ∫ w, PV e (x i) w * (PV e w v * Φ (Function.update x i v)) := h3
    _ = ∫ v, PV e (x i) v * Φ (Function.update x i v) := h4
    _ = slotProj1 e i Φ x := rfl

/-- **Commutation of two distinct single-slot projections**, for a bounded measurable state. -/
theorem slotProj1_commMB {m : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    {ι : Type*} [DecidableEq ι] (Φ : (ι → Ω) → ℂ) (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ y, ‖Φ y‖ ≤ C) (i j : ι) (hij : i ≠ j) :
    slotProj1 e i (slotProj1 e j Φ) = slotProj1 e j (slotProj1 e i Φ) := by
  classical
  funext x
  have h1 : slotProj1 e i (slotProj1 e j Φ) x
      = ∫ w, PV e (x i) w * (∫ v, PV e (x j) v *
          Φ (Function.update (Function.update x j v) i w)) := by
    rw [slotProj1]
    apply integral_congr_ae
    filter_upwards with w
    have hstep : slotProj1 e j Φ (Function.update x i w)
        = ∫ v, PV e (x j) v * Φ (Function.update (Function.update x j v) i w) := by
      rw [slotProj1]
      apply integral_congr_ae
      filter_upwards with v
      rw [Function.update_of_ne (Ne.symm hij) w x, Function.update_comm hij w v x]
    rw [hstep, ← integral_const_mul]
  have h2 : (∫ w, PV e (x i) w * (∫ v, PV e (x j) v *
          Φ (Function.update (Function.update x j v) i w)))
      = ∫ w, ∫ v, PV e (x i) w * (PV e (x j) v *
          Φ (Function.update (Function.update x j v) i w)) := by
    apply integral_congr_ae
    filter_upwards with w
    rw [integral_const_mul]
  have h3 : (∫ w, ∫ v, PV e (x i) w * (PV e (x j) v *
          Φ (Function.update (Function.update x j v) i w)))
      = ∫ v, ∫ w, PV e (x i) w * (PV e (x j) v *
          Φ (Function.update (Function.update x j v) i w)) :=
    integral_integral_swap (integrable_uncurry_comm e he hec Φ hΦm hΦb x i j)
  have h4 : (∫ v, ∫ w, PV e (x i) w * (PV e (x j) v *
          Φ (Function.update (Function.update x j v) i w)))
      = ∫ v, PV e (x j) v * (∫ w, PV e (x i) w *
          Φ (Function.update (Function.update x j v) i w)) := by
    apply integral_congr_ae
    filter_upwards with v
    rw [show (fun w : Ω => PV e (x i) w * (PV e (x j) v *
            Φ (Function.update (Function.update x j v) i w)))
        = (fun w : Ω => PV e (x j) v * (PV e (x i) w *
            Φ (Function.update (Function.update x j v) i w)))
      from funext fun w => by ring]
    rw [integral_const_mul]
  have h5 : (∫ v, PV e (x j) v * (∫ w, PV e (x i) w *
          Φ (Function.update (Function.update x j v) i w)))
      = ∫ v, PV e (x j) v * (slotProj1 e i Φ) (Function.update x j v) := by
    apply integral_congr_ae
    filter_upwards with v
    congr 1
    rw [slotProj1]
    apply integral_congr_ae
    filter_upwards with w
    rw [Function.update_of_ne hij v x]
  calc slotProj1 e i (slotProj1 e j Φ) x
      = ∫ w, PV e (x i) w * (∫ v, PV e (x j) v *
          Φ (Function.update (Function.update x j v) i w)) := h1
    _ = ∫ w, ∫ v, PV e (x i) w * (PV e (x j) v *
          Φ (Function.update (Function.update x j v) i w)) := h2
    _ = ∫ v, ∫ w, PV e (x i) w * (PV e (x j) v *
          Φ (Function.update (Function.update x j v) i w)) := h3
    _ = ∫ v, PV e (x j) v * (∫ w, PV e (x i) w *
          Φ (Function.update (Function.update x j v) i w)) := h4
    _ = ∫ v, PV e (x j) v * (slotProj1 e i Φ) (Function.update x j v) := h5
    _ = slotProj1 e j (slotProj1 e i Φ) x := rfl

-- namespace `Work.BoseBoxFock`; imports `Submission.Work.BoseBoxFock.SlotProjAux`.
/-- SINGLE SLOT FACTS, measurable/bounded form.  With `Ω = EuclideanSpace ℝ (Fin 3)` and
`slotProj1 e i Ψ x = ∫ w : Ω, PV e (x i) w * Ψ (Function.update x i w)`, the single slot
projections are idempotent and commute (the modes are orthonormal, `horth`).  The state is assumed
only measurable and bounded (NOT continuous, NOT compactly supported).

Route: expand both `slotProj1`s (`Function.update_idem`, `(Function.update x i w) i = w`), pull the
factor constant in the inner variable out with `integral_const_mul`, swap the two integrals with
`MeasureTheory.integral_integral_swap` — the needed `Integrable` follows from
`integrable_mul_of_continuous_hasCompactSupport_of_bounded` in `SlotProjAux` applied to the
continuous compactly supported two-variable kernel
`(w,v) ↦ PV e (x i) w * PV e w v` (its support is contained in
`tsupport (fun y => PV e (x i) y) × (⋃ l, tsupport (e l))`) and the bounded measurable state — and
finally use `Work.BoseBoxFock.integral_PV_mul_PV` (with the `hint` from `he`, `hec`).
For the commuting conjunct use `Function.update_comm` for `i ≠ j` before the swap. -/
theorem slotProj1_idem_commMB {m : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    {ι : Type*} [DecidableEq ι]
    (Φ : (ι → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ y, ‖Φ y‖ ≤ C) :
    (∀ i : ι, slotProj1 e i (slotProj1 e i Φ) = slotProj1 e i Φ) ∧
    (∀ i j : ι, i ≠ j → slotProj1 e i (slotProj1 e j Φ) = slotProj1 e j (slotProj1 e i Φ)) := by
  exact ⟨fun i => slotProj1_idemMB e he hec horth Φ hΦm hΦb i,
    fun i j hij => slotProj1_commMB e he hec Φ hΦm hΦb i j hij⟩

end Work.BoseBoxFock
