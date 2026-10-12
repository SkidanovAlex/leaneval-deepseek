import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SecAux.slotExact_pair_form
import Submission.Work.BoseBoxFock.SecAux.slotProj_finset_sum
import Submission.Work.BoseBoxFock.slotExact_sum_eq
import Submission.Work.BoseBoxFock.slotProj_sum_comp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-!
# `Work.BoseBoxFock.slotExact_comp` — the composition law of the `S`-sectors

Writing `P_T := slotProj e T` for the projection of the slots of `T` onto `V = span{e l}`, the two
ingredients of the box ↔ model bridge are

* **composition**: `P_T (P_U Φ) = P_{T ∪ U} Φ` (`slotInt_comp`, exported for sums by
  `slotProj_sum_comp`),
* **linearity** of `P_T` in its state argument over finite sums of bounded measurable states
  (`SecAux.slotProj_finset_sum`).

With these, the sectors `A_S := slotExact e S = ∑_{T ⊇ S} (-1)^{|T|−|S|} P_T` compose as the
orthogonal projections of the commuting family `{Q_i = P_{{i}}}` one expects:

* `A_S A_S = A_S` (idempotence),
* `A_S A_{S'} = 0` for `S ≠ S'` (orthogonality),

which is `slotExact_comp` below.  Orthogonality is the "peel one slot" argument of
`SecAux.slotExact_pair_form`: for `i ∈ S' \ S` the pairs `T`, `T ∪ {i}` of the inclusion–exclusion
cancel because `Q_i (A_{S'} Φ) = A_{S'} Φ` (`sx_absorb`); the case `i ∈ S \ S'` is reduced to it by
the commutation `A_S A_{S'} = A_{S'} A_S` (`sx_exact_comm`).  Idempotence is then read off from the
resolution of the identity `∑_S A_S = 1` (`slotExact_sum_eq`): enter the sum with `A_S` and use the
orthogonality of all the cross terms.
-/

/-! ## Measurability and boundedness of the slot projections and of the sectors -/

/-- `slotProj e T Φ` is measurable and bounded when `Φ` is (`slotInt_measurable_bounded`, in the
`slotProj` spelling). -/
theorem sx_proj_mb {m n : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l)) (T : Finset (Fin n)) (Φ : (Fin n → Ω) → ℂ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    Measurable (slotProj e T Φ) ∧ ∃ C, ∀ x, ‖slotProj e T Φ x‖ ≤ C := by
  have h := slotInt_measurable_bounded e he hec T Φ hΦm hΦb
  rwa [← slotProj_eq_slotInt_fun] at h

/-- `slotExact e S Φ` is measurable and bounded when `Φ` is: it is a finite linear combination of
the `slotProj e T Φ`. -/
theorem sx_exact_mb {m n : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l)) (S : Finset (Fin n)) (Φ : (Fin n → Ω) → ℂ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    Measurable (slotExact e S Φ) ∧ ∃ C, ∀ x, ‖slotExact e S Φ x‖ ≤ C := by
  classical
  choose C hC using fun T : Finset (Fin n) => (sx_proj_mb e he hec T Φ hΦm hΦb).2
  have hmeas : Measurable (slotExact e S Φ) := by
    have hexp : slotExact e S Φ = fun a : Fin n → Ω =>
        ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
          (-1 : ℂ) ^ (T.card - S.card) • slotProj e T Φ a := by
      funext a
      simp only [slotExact, Finset.sum_apply, Pi.smul_apply]
    rw [hexp]
    exact Finset.measurable_sum _
      (fun T _ => (sx_proj_mb e he hec T Φ hΦm hΦb).1.const_smul ((-1 : ℂ) ^ (T.card - S.card)))
  refine ⟨hmeas, ∑ T : Finset (Fin n), ‖(-1 : ℂ) ^ (T.card - S.card)‖ * max (C T) 0, fun x => ?_⟩
  calc ‖slotExact e S Φ x‖
      = ‖∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
            (-1 : ℂ) ^ (T.card - S.card) • slotProj e T Φ x‖ := by
        simp only [slotExact, Finset.sum_apply, Pi.smul_apply]
    _ ≤ ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
            ‖(-1 : ℂ) ^ (T.card - S.card) • slotProj e T Φ x‖ := norm_sum_le _ _
    _ ≤ ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
            ‖(-1 : ℂ) ^ (T.card - S.card)‖ * max (C T) 0 := by
        refine Finset.sum_le_sum fun T _ => ?_
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left ((hC T x).trans (le_max_left _ _)) (norm_nonneg _)
    _ ≤ ∑ T : Finset (Fin n), ‖(-1 : ℂ) ^ (T.card - S.card)‖ * max (C T) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun T _ _ => mul_nonneg (norm_nonneg _) (le_max_right _ _))

/-! ## Absorption, composition, commutation -/

/-- **Absorption.**  If `A ⊆ B` then projecting the slots of `A` after the sector `A_B` changes
nothing: every superset `T ⊇ B` of the inclusion–exclusion already contains `A`. -/
theorem sx_absorb {m n : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (A B : Finset (Fin n)) (hAB : A ⊆ B) (Φ : (Fin n → Ω) → ℂ) (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    slotProj e A (slotExact e B Φ) = slotExact e B Φ := by
  have hexp : slotExact e B Φ = fun x : Fin n → Ω =>
      ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => B ⊆ T),
        (-1 : ℂ) ^ (T.card - B.card) • slotProj e T Φ x := by
    funext x
    simp only [slotExact, Finset.sum_apply, Pi.smul_apply]
  rw [hexp, slotProj_sum_comp e he hec horth A _ (fun T => (-1 : ℂ) ^ (T.card - B.card)) Φ
    hΦm hΦb]
  funext x
  refine Finset.sum_congr rfl fun T hT => ?_
  have hsub : B ⊆ T := (Finset.mem_filter.mp hT).2
  rw [Finset.union_eq_right.mpr (hAB.trans hsub)]

/-- **Composition of two slot projections**: `P_A (P_B Φ) = P_{A ∪ B} Φ` (the `slotInt_comp` of
`slotProj_idem_and_comm`, transported to `slotProj`). -/
theorem sx_proj_comp {m n : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (A B : Finset (Fin n)) (Φ : (Fin n → Ω) → ℂ) (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    slotProj e A (slotProj e B Φ) = slotProj e (A ∪ B) Φ := by
  simpa only [slotProj_eq_slotInt_fun] using slotInt_comp e he hec horth Φ hΦm hΦb A B

/-- **The double-sum expansion of a composition of sectors** (the hypotheses on the states are
those making `SecAux.slotProj_finset_sum` applicable). -/
theorem sx_exact_double {m n : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (A B : Finset (Fin n)) (Φ : (Fin n → Ω) → ℂ) (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) (x : Fin n → Ω) :
    slotExact e A (slotExact e B Φ) x =
      ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => A ⊆ T),
        ∑ V ∈ Finset.univ.filter (fun V : Finset (Fin n) => B ⊆ V),
          ((-1 : ℂ) ^ (T.card - A.card) * (-1 : ℂ) ^ (V.card - B.card)) •
            slotProj e (T ∪ V) Φ x := by
  have hΨm : Measurable (slotExact e B Φ) := (sx_exact_mb e he hec B Φ hΦm hΦb).1
  have hΨb : ∃ C, ∀ x, ‖slotExact e B Φ x‖ ≤ C := (sx_exact_mb e he hec B Φ hΦm hΦb).2
  have hexp : slotExact e B Φ = fun y : Fin n → Ω =>
      ∑ V ∈ Finset.univ.filter (fun V : Finset (Fin n) => B ⊆ V),
        (-1 : ℂ) ^ (V.card - B.card) • slotProj e V Φ y := by
    funext y
    simp only [slotExact, Finset.sum_apply, Pi.smul_apply]
  have h1 : slotExact e A (slotExact e B Φ) x =
      ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => A ⊆ T),
        (-1 : ℂ) ^ (T.card - A.card) • slotProj e T (slotExact e B Φ) x := by
    simp only [slotExact, Finset.sum_apply, Pi.smul_apply]
  rw [h1]
  refine Finset.sum_congr rfl fun T _ => ?_
  have hkey := congrFun (slotProj_sum_comp e he hec horth T
    (Finset.univ.filter (fun V : Finset (Fin n) => B ⊆ V))
    (fun V => (-1 : ℂ) ^ (V.card - B.card)) Φ hΦm hΦb) x
  have harg : slotProj e T (slotExact e B Φ)
      = slotProj e T (fun y : Fin n → Ω =>
          ∑ V ∈ Finset.univ.filter (fun V : Finset (Fin n) => B ⊆ V),
            (-1 : ℂ) ^ (V.card - B.card) • slotProj e V Φ y) := by
    rw [hexp]
  rw [harg, hkey, Finset.smul_sum]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [smul_smul]

/-- **The sectors commute**: `A_S A_{S'} = A_{S'} A_S`, read off from the symmetric double-sum
expansion (`sx_exact_double`). -/
theorem sx_exact_comm {m n : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (S S' : Finset (Fin n)) (Φ : (Fin n → Ω) → ℂ) (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    slotExact e S (slotExact e S' Φ) = slotExact e S' (slotExact e S Φ) := by
  funext x
  calc slotExact e S (slotExact e S' Φ) x
      = ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
          ∑ V ∈ Finset.univ.filter (fun V : Finset (Fin n) => S' ⊆ V),
            ((-1 : ℂ) ^ (T.card - S.card) * (-1 : ℂ) ^ (V.card - S'.card)) •
              slotProj e (T ∪ V) Φ x := sx_exact_double e he hec horth S S' Φ hΦm hΦb x
    _ = ∑ V ∈ Finset.univ.filter (fun V : Finset (Fin n) => S' ⊆ V),
          ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
            ((-1 : ℂ) ^ (T.card - S.card) * (-1 : ℂ) ^ (V.card - S'.card)) •
              slotProj e (T ∪ V) Φ x := Finset.sum_comm
    _ = ∑ V ∈ Finset.univ.filter (fun V : Finset (Fin n) => S' ⊆ V),
          ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
            ((-1 : ℂ) ^ (V.card - S'.card) * (-1 : ℂ) ^ (T.card - S.card)) •
              slotProj e (V ∪ T) Φ x := by
        refine Finset.sum_congr rfl fun V _ => Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.union_comm, mul_comm]
    _ = slotExact e S' (slotExact e S Φ) x :=
        (sx_exact_double e he hec horth S' S Φ hΦm hΦb x).symm

/-! ## Linearity of the sector in its state argument -/

/-- **Linearity of `slotExact e S`** in its state argument over a finite linear combination of
bounded measurable states (from `SecAux.slotProj_finset_sum`). -/
theorem sx_lin_exact {m n : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l)) (S : Finset (Fin n)) (s : Finset (Finset (Fin n)))
    (c : Finset (Fin n) → ℂ) (Ψ : Finset (Fin n) → (Fin n → Ω) → ℂ)
    (hΨm : ∀ U, Measurable (Ψ U)) (hΨb : ∀ U, ∃ C, ∀ x, ‖Ψ U x‖ ≤ C) :
    slotExact e S (fun x => ∑ U ∈ s, c U • Ψ U x) =
      fun x => ∑ U ∈ s, c U • slotExact e S (Ψ U) x := by
  have hinner : slotExact e S (fun x => ∑ U ∈ s, c U • Ψ U x)
      = fun x : Fin n → Ω =>
          ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
            (-1 : ℂ) ^ (T.card - S.card) •
              slotProj e T (fun x => ∑ U ∈ s, c U • Ψ U x) x := by
    funext x
    simp only [slotExact, Finset.sum_apply, Pi.smul_apply]
  rw [hinner]
  funext x
  calc ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
          (-1 : ℂ) ^ (T.card - S.card) •
            slotProj e T (fun x => ∑ U ∈ s, c U • Ψ U x) x
      = ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
          ∑ U ∈ s, ((-1 : ℂ) ^ (T.card - S.card) * c U) • slotProj e T (Ψ U) x := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [congrFun (SecAux.slotProj_finset_sum e he hec T s c Ψ hΨm hΨb) x, Finset.smul_sum]
        refine Finset.sum_congr rfl fun U _ => ?_
        rw [smul_smul]
    _ = ∑ U ∈ s, ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
          ((-1 : ℂ) ^ (T.card - S.card) * c U) • slotProj e T (Ψ U) x := Finset.sum_comm
    _ = ∑ U ∈ s, c U • ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
          (-1 : ℂ) ^ (T.card - S.card) • slotProj e T (Ψ U) x := by
        refine Finset.sum_congr rfl fun U _ => ?_
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [smul_smul, mul_comm]
    _ = ∑ U ∈ s, c U • slotExact e S (Ψ U) x := by
        refine Finset.sum_congr rfl fun U _ => ?_
        congr 1
        simp only [slotExact, Finset.sum_apply, Pi.smul_apply]

/-! ## The vanishing of the mixed sectors -/

/-- **The mixed sector with `i ∉ S` and `i ∈ S'` vanishes.**  `SecAux.slotExact_pair_form` writes
`A_S` as a sum over the pairs `T`, `T ∪ {i}` (`T ⊇ S`, `i ∉ T`), and since `i ∈ S'` the state
`A_{S'} Φ` is absorbed by the slot projection `Q_i = P_{{i}}`, so `P_T (A_{S'} Φ) = P_{T ∪ {i}}
(A_{S'} Φ)` and every pair cancels. -/
theorem sx_zero {m n : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (S S' : Finset (Fin n)) (Φ : (Fin n → Ω) → ℂ) (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) (i : Fin n) (hiS : i ∉ S) (hiS' : i ∈ S') :
    slotExact e S (slotExact e S' Φ) = 0 := by
  have hΨm : Measurable (slotExact e S' Φ) := (sx_exact_mb e he hec S' Φ hΦm hΦb).1
  have hΨb : ∃ C, ∀ x, ‖slotExact e S' Φ x‖ ≤ C := (sx_exact_mb e he hec S' Φ hΦm hΦb).2
  rw [SecAux.slotExact_pair_form e S i hiS (slotExact e S' Φ)]
  refine Finset.sum_eq_zero fun T hT => ?_
  have habs : slotProj e ({i} : Finset (Fin n)) (slotExact e S' Φ) = slotExact e S' Φ :=
    sx_absorb e he hec horth {i} S' (Finset.singleton_subset_iff.mpr hiS') Φ hΦm hΦb
  have hsub : slotProj e T (slotExact e S' Φ) = slotProj e (insert i T) (slotExact e S' Φ) := by
    calc slotProj e T (slotExact e S' Φ)
        = slotProj e T (slotProj e ({i} : Finset (Fin n)) (slotExact e S' Φ)) := by rw [habs]
      _ = slotProj e (T ∪ ({i} : Finset (Fin n))) (slotExact e S' Φ) :=
            sx_proj_comp e he hec horth T {i} (slotExact e S' Φ) hΨm hΨb
      _ = slotProj e (insert i T) (slotExact e S' Φ) := by
            rw [Finset.union_comm, ← Finset.insert_eq]
  rw [hsub, sub_self, smul_zero]

/-- **The mixed sectors vanish**: `A_S A_{S'} = 0` for `S ≠ S'`, by picking `i ∈ S △ S'` and
reducing to `sx_zero` (with the commutation of the sectors when `i ∈ S \ S'`). -/
theorem sx_zero_ne {m n : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (S S' : Finset (Fin n)) (Φ : (Fin n → Ω) → ℂ) (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) (hne : S ≠ S') :
    slotExact e S (slotExact e S' Φ) = 0 := by
  by_cases hsub : S ⊆ S'
  · have hss : S ⊂ S' := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
    obtain ⟨i, hiS', hiS⟩ := Finset.exists_of_ssubset hss
    exact sx_zero e he hec horth S S' Φ hΦm hΦb i hiS hiS'
  · obtain ⟨i, hiS, hiS'⟩ := Finset.not_subset.mp hsub
    rw [sx_exact_comm e he hec horth S S' Φ hΦm hΦb]
    exact sx_zero e he hec horth S' S Φ hΦm hΦb i hiS' hiS

/-! ## The composition law -/

theorem slotExact_comp {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (S S' : Finset (Fin n)) (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    slotExact e S (slotExact e S' Φ) = if S = S' then slotExact e S Φ else 0 := by
  by_cases h : S = S'
  · -- `S = S'`: enter the resolution of the identity `∑_U A_U = 1` with `A_S`; the cross terms
    -- vanish by `sx_zero_ne`, leaving `A_S = A_S A_S`.
    rw [if_pos h]
    subst h
    have hstep : slotExact e S Φ = slotExact e S (slotExact e S Φ) := by
      have hF : (fun x : Fin n → Ω =>
            ∑ U ∈ Finset.univ, (1 : ℂ) • slotExact e U Φ x) = Φ := by
        funext x
        rw [← congrFun (slotExact_sum_eq e Φ) x]
        simp only [Finset.sum_apply, one_smul]
      conv_lhs => rw [← hF]
      rw [sx_lin_exact e he hec S Finset.univ (fun _ => (1 : ℂ)) (fun U => slotExact e U Φ)
        (fun U => (sx_exact_mb e he hec U Φ hΦm hΦb).1)
        (fun U => (sx_exact_mb e he hec U Φ hΦm hΦb).2)]
      funext x
      rw [Finset.sum_eq_single S]
      · simp
      · intro U _ hU
        rw [sx_zero_ne e he hec horth S U Φ hΦm hΦb (Ne.symm hU)]
        simp
      · intro hh
        exact absurd (Finset.mem_univ S) hh
    exact hstep.symm
  · rw [if_neg h]
    exact sx_zero_ne e he hec horth S S' Φ hΦm hΦb h

end Work.BoseBoxFock
