import Mathlib.MeasureTheory.Measure.Haar.Unique
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Measure.Orthant

open MeasureTheory Set
open scoped BigOperators

/-- The two-point sign function `{0,1} → {1,-1}`. -/
private def sign2 : Fin 2 → ℝ := fun t => if t = 0 then (1 : ℝ) else -1

private lemma sign2_eq (s : Fin 2) : sign2 s = 1 ∨ sign2 s = -1 := by
  fin_cases s <;> simp [sign2]

private lemma eq_zero_of_sign2_mul_nonneg {y : ℝ} (hy : 0 < y) {s : Fin 2}
    (h : 0 ≤ sign2 s * y) : s = 0 := by
  fin_cases s
  · rfl
  · simp [sign2] at h; linarith

private lemma eq_one_of_sign2_mul_nonneg {y : ℝ} (hy : y < 0) {s : Fin 2}
    (h : 0 ≤ sign2 s * y) : s = 1 := by
  fin_cases s
  · simp [sign2] at h; linarith
  · rfl

private lemma sign2_zero_mul_nonneg {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ sign2 (0 : Fin 2) * y := by
  simpa [sign2] using hy

private lemma sign2_one_mul_nonneg {y : ℝ} (hy : y ≤ 0) :
    0 ≤ sign2 (1 : Fin 2) * y := by
  have : (0 : ℝ) ≤ -y := by linarith
  simpa [sign2] using this

/-- The positive orthant of `Fin n → ℝ`. -/
private def orthant (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ : Fin n => Set.Ici (0 : ℝ))

private lemma mem_orthant {n : ℕ} {u : Fin n → ℝ} :
    u ∈ orthant n ↔ ∀ i, 0 ≤ u i := by
  rw [orthant, Set.mem_pi]
  exact ⟨fun h i => h i (Set.mem_univ i), fun h i _ => h i⟩

private lemma measurableSet_orthant (n : ℕ) : MeasurableSet (orthant n) := by
  rw [orthant]
  exact MeasurableSet.pi (s := Set.univ) (t := fun _ : Fin n => Set.Ici (0 : ℝ))
    Set.countable_univ (fun _ _ => measurableSet_Ici)

/-- The coordinatewise sign flip attached to a sign pattern `t : Fin n → Fin 2`. -/
private def flip {n : ℕ} (t : Fin n → Fin 2) (u : Fin n → ℝ) : Fin n → ℝ :=
  fun i => sign2 (t i) * u i

private lemma flip_apply {n : ℕ} (t : Fin n → Fin 2) (u : Fin n → ℝ) :
    flip t u = fun i => sign2 (t i) * u i := rfl

private lemma flip_measurePreserving {n : ℕ} (t : Fin n → Fin 2) :
    MeasurePreserving (flip t) volume volume := by
  have h : MeasurePreserving (fun (u : Fin n → ℝ) => fun i => sign2 (t i) * u i)
      volume volume := by
    have hsgn : ∀ i : Fin n, MeasurePreserving (fun x : ℝ => sign2 (t i) * x) volume volume := by
      intro i
      rcases sign2_eq (t i) with hc | hc
      · rw [show (fun x : ℝ => sign2 (t i) * x) = id by funext x; rw [hc]; simp]
        exact MeasurePreserving.id (volume : Measure ℝ)
      · rw [show (fun x : ℝ => sign2 (t i) * x) = Neg.neg by funext x; rw [hc]; ring]
        exact Measure.measurePreserving_neg (volume : Measure ℝ)
    simpa only using MeasureTheory.volume_preserving_pi (α' := fun _ : Fin n => ℝ)
      (β' := fun _ : Fin n => ℝ) (f := fun i x => sign2 (t i) * x) hsgn
  exact h

private lemma volume_coord_eq_zero {n : ℕ} (i : Fin n) :
    volume {u : Fin n → ℝ | u i = 0} = 0 := by
  have hvol : (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) =
      (volume : Measure (Fin n → ℝ)) := rfl
  have key := Measure.pi_eval_preimage_null (fun _ : Fin n => (volume : Measure ℝ)) (i := i)
    (s := ({0} : Set ℝ)) (measure_singleton 0)
  rw [hvol] at key
  have hset : Function.eval i ⁻¹' ({0} : Set ℝ) = {u : Fin n → ℝ | u i = 0} := by
    ext u; simp [Function.eval]
  rwa [hset] at key

private lemma volume_setOf_exists_eq_zero (n : ℕ) :
    volume {u : Fin n → ℝ | ∃ i, u i = 0} = 0 := by
  have hset : {u : Fin n → ℝ | ∃ i, u i = 0} = ⋃ i, {u : Fin n → ℝ | u i = 0} := by
    ext u; simp
  rw [hset]
  exact measure_iUnion_null (fun i => volume_coord_eq_zero i)

/-- **The orthant integral is `2^{-n}` of the full integral** for a function on
`Fin n → ℝ` invariant under coordinate sign flips.  (`volume` on `Fin n → ℝ`
is the product of the Lebesgue measures; the `2^n` orthants are related by the
measure-preserving sign-flip maps.) -/
theorem integral_orthant_eq_inv_pow {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hint : Integrable F volume)
    (hsym : ∀ (ε : Fin n → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) → ∀ u,
      F (fun i => ε i * u i) = F u) :
    ∫ u in (Set.pi Set.univ (fun _ : Fin n => Set.Ici (0 : ℝ))), F u
      = ((2 : ℝ) ^ n)⁻¹ * ∫ u, F u := by
  change ∫ u in orthant n, F u = ((2 : ℝ) ^ n)⁻¹ * ∫ u, F u
  set G : (Fin n → ℝ) → ℝ := (orthant n).indicator F with hG
  have hGint : Integrable G volume := by
    rw [hG]; exact hint.indicator (measurableSet_orthant n)
  -- The sign flip acts trivially on `F`.
  have hsym_flip : ∀ (t : Fin n → Fin 2) (u : Fin n → ℝ), F (flip t u) = F u := by
    intro t u
    have := hsym (fun i => sign2 (t i)) (fun i => sign2_eq (t i)) u
    simpa only [flip_apply] using this
  have hInt_t : ∀ t : Fin n → Fin 2, Integrable (fun u => G (flip t u)) volume := by
    intro t
    have hmp := flip_measurePreserving (n := n) t
    exact (hmp.integrable_comp hGint.aestronglyMeasurable).mpr hGint
  have hInt_eq : ∀ t : Fin n → Fin 2, ∫ u, G (flip t u) = ∫ u, G u := by
    intro t
    have hmp := flip_measurePreserving (n := n) t
    have key : ∫ y, G y ∂Measure.map (flip t) volume = ∫ u, G (flip t u) :=
      integral_map hmp.aemeasurable (f := G)
        (by rw [hmp.map_eq]; exact hGint.aestronglyMeasurable)
    rw [hmp.map_eq] at key
    exact key.symm
  -- Off the union of the coordinate hyperplanes, exactly one sign-flipped image of `u`
  -- lies in the orthant, so the sum of the indicators telescopes to `F u`.
  have hpoint : ∀ u : Fin n → ℝ, (∀ i, u i ≠ 0) →
      F u = ∑ t : Fin n → Fin 2, G (flip t u) := by
    intro u hne
    let t0 : Fin n → Fin 2 := fun i => if 0 ≤ u i then 0 else 1
    have ht0mem : flip t0 u ∈ orthant n := by
      rw [mem_orthant]
      intro i
      change 0 ≤ sign2 (t0 i) * u i
      by_cases h : 0 ≤ u i
      · have ht0 : t0 i = 0 := by simp [t0, h]
        rw [ht0]; exact sign2_zero_mul_nonneg h
      · have ht0 : t0 i = 1 := by simp [t0, h]
        rw [ht0]; exact sign2_one_mul_nonneg (le_of_lt (lt_of_not_ge h))
    have huniq : ∀ t : Fin n → Fin 2, flip t u ∈ orthant n → t = t0 := by
      intro t ht
      funext i
      have hti : 0 ≤ sign2 (t i) * u i := by
        have := (mem_orthant.mp ht) i
        simpa only [flip_apply] using this
      by_cases h : 0 ≤ u i
      · have hpos : 0 < u i := lt_of_le_of_ne h (hne i).symm
        have hti0 : t i = 0 := eq_zero_of_sign2_mul_nonneg hpos hti
        rw [hti0]; simp [t0, h]
      · have hlt : u i < 0 := lt_of_not_ge h
        have hti1 : t i = 1 := eq_one_of_sign2_mul_nonneg hlt hti
        rw [hti1]; simp [t0, h]
    have hsum : ∑ t : Fin n → Fin 2, G (flip t u) = G (flip t0 u) := by
      refine Finset.sum_eq_single t0 ?_ ?_
      · intro b _ hb
        have hmem : flip b u ∉ orthant n := fun hmem => hb (huniq b hmem)
        rw [hG]
        exact Set.indicator_of_notMem hmem F
      · intro h; exact absurd (Finset.mem_univ t0) h
    rw [hsum, hG, Set.indicator_of_mem ht0mem]
    exact (hsym_flip t0 u).symm
  have hae : F =ᵐ[volume] fun u => ∑ t : Fin n → Fin 2, G (flip t u) := by
    change ∀ᵐ u ∂volume, F u = ∑ t : Fin n → Fin 2, G (flip t u)
    rw [MeasureTheory.ae_iff]
    apply measure_mono_null _ (volume_setOf_exists_eq_zero n)
    intro u hu
    by_contra hN
    exact hu (hpoint u (fun i hi => hN ⟨i, hi⟩))
  have hmain : ∫ u, F u = (2 : ℝ) ^ n * ∫ u, G u := by
    calc
      ∫ u, F u = ∫ u, ∑ t : Fin n → Fin 2, G (flip t u) := integral_congr_ae hae
      _ = ∑ t : Fin n → Fin 2, ∫ u, G (flip t u) :=
        integral_finsetSum Finset.univ (fun t _ => hInt_t t)
      _ = ∑ t : Fin n → Fin 2, ∫ u, G u := Finset.sum_congr rfl (fun t _ => hInt_eq t)
      _ = (2 : ℝ) ^ n * ∫ u, G u := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin]
        simp [nsmul_eq_mul]
  rw [hmain, hG, integral_indicator (measurableSet_orthant n),
    inv_mul_cancel_left₀ (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0))]

end Commons.Measure.Orthant
