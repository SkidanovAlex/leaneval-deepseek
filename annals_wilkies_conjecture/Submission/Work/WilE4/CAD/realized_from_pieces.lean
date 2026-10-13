/-
  WilE4 / CAD — the assembly of the "clopen" argument for realisability of a sign vector.

  This module contains the *clean* part of the former
  `realized_const_of_signConst_bdd.lean`: the sign-stability preparation, the openness and
  closedness of realisability in the subspace `C`, and the assembly `realized_const_from_pieces`,
  which derives the dichotomy on a preconnected `C` from the two halves as explicit hypotheses.

  The *statement* `realized_const_of_signConst_bdd` that used to follow (the dichotomy from the
  bounded coefficient/resultant data alone) was **refuted** with an exact counterexample and has
  been retired: see the RETIRED file of the same former name for the record, and `NOTES.md` §1.
  A downstream user must supply the two halves (`hA`, `hB`); `syl_minor_type_const` supplies them
  from the (polynomial-size) subresultant data.
-/
import Mathlib
import Submission.Work.WilE4.CAD.Proj
import Submission.Work.WilE4.CAD.resultant_spec
import Submission.Work.WilE4.CAD.signConst_data

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Classical
open MvPolynomial Polynomial Filter Topology
open Work.WilE4 (rot spec)

namespace Work.WilE4.CAD

variable {m k : ℕ}

/-! ## Sign stability and continuity

Preparation for the "openness" half: if a continuous function has no zero on `[a,b]`, its sign is
constant there, and the signs of the specialisations of a member are stable on a compact interval
under small changes of the parameter. -/

/-- A continuous function with no zero on `[a,b]` has the same sign as at `a` throughout `[a,b]`. -/
theorem eq_sign_of_no_root_bdd {F : ℝ → ℝ} (hF : Continuous F) {a b : ℝ} (hab : a ≤ b)
    (hne : ∀ t ∈ Set.Icc a b, F t ≠ 0) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    SignType.sign (F t) = SignType.sign (F a) := by
  have ha : F a ≠ 0 := hne a ⟨le_rfl, hab⟩
  have hat : a ≤ t := ht.1
  have hsub : ∀ c ∈ Set.Icc a t, c ∈ Set.Icc a b := fun c hc => ⟨hc.1, le_trans hc.2 ht.2⟩
  rcases lt_trichotomy (F a) 0 with hlt | heq | hgt
  · have hFt : F t < 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc hat hF.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (F a) (F t) from ⟨le_of_lt hlt, hcon⟩)
      exact hne c (hsub c hc) hcv
    rw [sign_neg hlt, sign_neg hFt]
  · exact absurd heq ha
  · have hFt : 0 < F t := by
      by_contra hcon
      push Not at hcon
      obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc' hat hF.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (F t) (F a) from ⟨hcon, le_of_lt hgt⟩)
      exact hne c (hsub c hc) hcv
    rw [sign_pos hgt, sign_pos hFt]

/-- Two points of a compact interval on which a continuous function has no zero have the same
sign. -/
theorem eq_sign_of_no_root_bdd' {F : ℝ → ℝ} (hF : Continuous F) {a b : ℝ} (hab : a ≤ b)
    (hne : ∀ t ∈ Set.Icc a b, F t ≠ 0) {x y : ℝ} (hx : x ∈ Set.Icc a b)
    (hy : y ∈ Set.Icc a b) : SignType.sign (F x) = SignType.sign (F y) :=
  (eq_sign_of_no_root_bdd hF hab hne hx).trans (eq_sign_of_no_root_bdd hF hab hne hy).symm

/-- The evaluation map `(x,t) ↦ (spec Q x).eval t` is continuous. -/
theorem continuous_spec_eval_bdd {m : ℕ} (Q : MvPolynomial (Fin (m+1)) ℝ) :
    Continuous fun p : (Fin m → ℝ) × ℝ => (spec Q p.1).eval p.2 := by
  have h1 : Continuous fun p : (Fin m → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (m+1) → ℝ) := by
    rw [continuous_pi_iff]
    intro j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨l, rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc]
      exact (continuous_apply l).comp continuous_fst
    · simp only [Fin.snoc_last]
      exact continuous_snd
  have h2 : Continuous fun p : (Fin m → ℝ) × ℝ =>
      MvPolynomial.eval (Fin.snoc p.1 p.2) Q := (MvPolynomial.continuous_eval Q).comp h1
  convert h2 using 1
  funext p
  exact spec_eval_snoc Q p.1 p.2

/-! ## The two halves of the clopen argument -/

/-- **Openness.**  If a sign vector is realised at `x₀` and the vanishing pattern of the witness
persists locally (hypothesis `hA`), then it is realised on a neighbourhood: the members vanishing at
`(x₀,t₀)` keep vanishing at the perturbed witness, and the others keep their sign by continuity. -/
theorem pattern_nhds_of_pattern {P : Fin k → MvPolynomial (Fin (m+1)) ℝ}
    {C : Set (Fin m → ℝ)}
    (hA : ∀ (x₀ : Fin m → ℝ), x₀ ∈ C → ∀ (t₀ : ℝ) (ε : ℝ), 0 < ε →
      ∃ U ∈ nhds x₀, ∀ x' ∈ U ∩ C, ∃ t, |t - t₀| < ε ∧
        ∀ i, (spec (P i) x₀).eval t₀ = 0 → (spec (P i) x').eval t = 0)
    {v : Fin k → SignType} {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ C)
    (hv : ∃ t, ∀ i, SignType.sign ((spec (P i) x₀).eval t) = v i) :
    ∃ U ∈ nhds x₀, ∀ x ∈ U ∩ C, ∃ t, ∀ i, SignType.sign ((spec (P i) x).eval t) = v i := by
  classical
  obtain ⟨t₀, ht₀⟩ := hv
  set S : Finset (Fin k) := Finset.univ.filter (fun i => v i ≠ 0) with hS
  -- the members with `v i ≠ 0` do not vanish at the witness
  have hSne : ∀ i ∈ S, (spec (P i) x₀).eval t₀ ≠ 0 := by
    intro i hi h0
    have h1 : SignType.sign ((spec (P i) x₀).eval t₀) = 0 := by rw [h0, sign_zero]
    rw [ht₀ i] at h1
    exact (Finset.mem_filter.mp hi).2 h1
  obtain ⟨δ, hδpos, hδ⟩ := exists_pos_eval_ne (s := S.image (fun i => spec (P i) x₀)) (y := t₀)
    (by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      exact hSne i hi)
  have hhalf : 0 < δ / 2 := by linarith
  have hnoz : ∀ i ∈ S, ∀ z ∈ Set.Icc (t₀ - δ / 2) (t₀ + δ / 2), (spec (P i) x₀).eval z ≠ 0 := by
    intro i hi z hz
    refine hδ (spec (P i) x₀) (Finset.mem_image_of_mem _ hi) z ?_
    rw [abs_lt]
    constructor <;> linarith [hz.1, hz.2]
  have hIcc : ∀ i ∈ S, ∀ t ∈ Set.Icc (t₀ - δ / 2) (t₀ + δ / 2),
      SignType.sign ((spec (P i) x₀).eval t) = v i := by
    intro i hi t ht
    have h1 : SignType.sign ((spec (P i) x₀).eval t) =
        SignType.sign ((spec (P i) x₀).eval t₀) :=
      eq_sign_of_no_root_bdd' (Polynomial.continuous _) (by linarith : t₀ - δ / 2 ≤ t₀ + δ / 2)
        (hnoz i hi) ht ⟨by linarith, by linarith⟩
    rw [h1, ht₀ i]
  -- stability of these signs in the parameter
  have hstab : ∀ᶠ x in nhds x₀, ∀ i ∈ S, ∀ t ∈ Set.Icc (t₀ - δ / 2) (t₀ + δ / 2),
      SignType.sign ((spec (P i) x).eval t) = v i := by
    refine (eventually_all_finset S).mpr fun i hi => ?_
    refine (sign_stable_Icc (continuous_spec_eval_bdd (P i))
      (fun y hy => hnoz i hi y hy)).mono fun x hx t ht => ?_
    rw [hx t ht, hIcc i hi t ht]
  obtain ⟨U₂, hU₂, hU₂'⟩ := hA x₀ hx₀ t₀ (δ / 2) hhalf
  refine ⟨_, Filter.inter_mem hstab hU₂, ?_⟩
  intro x hx
  obtain ⟨⟨hxs, hxU₂⟩, hxC⟩ := hx
  obtain ⟨t, ht, hvan⟩ := hU₂' x ⟨hxU₂, hxC⟩
  refine ⟨t, fun i => ?_⟩
  have htI : t ∈ Set.Icc (t₀ - δ / 2) (t₀ + δ / 2) := by
    rw [abs_lt] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  by_cases hi : v i = 0
  · have hz : (spec (P i) x₀).eval t₀ = 0 := by
      have h1 : SignType.sign ((spec (P i) x₀).eval t₀) = 0 := by rw [ht₀ i, hi]
      exact sign_eq_zero_iff.mp h1
    rw [hvan i hz, sign_zero, hi]
  · exact hxs i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩) t htI

/-- The set of parameters realising `v` is open in the subspace `C`. -/
theorem realized_open_subtype {P : Fin k → MvPolynomial (Fin (m+1)) ℝ}
    {C : Set (Fin m → ℝ)} {v : Fin k → SignType}
    (hA : ∀ (x₀ : Fin m → ℝ), x₀ ∈ C → ∀ (t₀ : ℝ) (ε : ℝ), 0 < ε →
      ∃ U ∈ nhds x₀, ∀ x' ∈ U ∩ C, ∃ t, |t - t₀| < ε ∧
        ∀ i, (spec (P i) x₀).eval t₀ = 0 → (spec (P i) x').eval t = 0) :
    IsOpen {x : C | ∃ t, ∀ i, SignType.sign ((spec (P i) x.val).eval t) = v i} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, hU, hU'⟩ := pattern_nhds_of_pattern hA x.property hx
  have h1 : Subtype.val ⁻¹' U ∈ nhds x := by
    rw [nhds_subtype]
    exact ⟨U, hU, subset_rfl⟩
  refine Filter.mem_of_superset h1 ?_
  intro y hy
  exact hU' y.val ⟨hy, y.property⟩

/-- The set of parameters realising `v` is closed in the subspace `C`, using the sequential
closedness supplied by `hB`. -/
theorem realized_closed_subtype {P : Fin k → MvPolynomial (Fin (m+1)) ℝ}
    {C : Set (Fin m → ℝ)} {v : Fin k → SignType}
    (hB : ∀ (v' : Fin k → SignType), ∀ (x : ℕ → Fin m → ℝ), (∀ n, x n ∈ C) →
      ∀ x₀ ∈ C, Tendsto x atTop (nhds x₀) →
      (∀ n, ∃ t, ∀ i, SignType.sign ((spec (P i) (x n)).eval t) = v' i) →
      ∃ t, ∀ i, SignType.sign ((spec (P i) x₀).eval t) = v' i) :
    IsClosed {x : C | ∃ t, ∀ i, SignType.sign ((spec (P i) x.val).eval t) = v i} := by
  rw [← isSeqClosed_iff_isClosed]
  refine fun {u} {p} hu hp => ?_
  obtain ⟨t, ht⟩ := hB v (fun n => (u n).val) (fun n => (u n).property) p.val p.property
    ((continuous_subtype_val.tendsto p).comp hp) (fun n => hu n)
  exact ⟨t, ht⟩

/-- **Assembly.**  If the vanishing pattern of a witness persists locally (`hA`) and realisability
is sequentially closed along `C` (`hB`), then the realisability of a fixed sign vector is constant
on a preconnected `C`. -/
theorem realized_const_from_pieces (P : Fin k → MvPolynomial (Fin (m+1)) ℝ) (C : Set (Fin m → ℝ))
    (hC : IsPreconnected C)
    (hA : ∀ (x₀ : Fin m → ℝ), x₀ ∈ C → ∀ (t₀ : ℝ) (ε : ℝ), 0 < ε →
      ∃ U ∈ nhds x₀, ∀ x' ∈ U ∩ C, ∃ t, |t - t₀| < ε ∧
        ∀ i, (spec (P i) x₀).eval t₀ = 0 → (spec (P i) x').eval t = 0)
    (hB : ∀ (v' : Fin k → SignType), ∀ (x : ℕ → Fin m → ℝ), (∀ n, x n ∈ C) →
      ∀ x₀ ∈ C, Tendsto x atTop (nhds x₀) →
      (∀ n, ∃ t, ∀ i, SignType.sign ((spec (P i) (x n)).eval t) = v' i) →
      ∃ t, ∀ i, SignType.sign ((spec (P i) x₀).eval t) = v' i)
    (v : Fin k → SignType) :
    (∀ x ∈ C, ∃ t : ℝ, ∀ i, SignType.sign ((spec (P i) x).eval t) = v i) ∨
      (∀ x ∈ C, ¬ ∃ t : ℝ, ∀ i, SignType.sign ((spec (P i) x).eval t) = v i) := by
  classical
  haveI : PreconnectedSpace C := (isPreconnected_iff_preconnectedSpace).mp hC
  have hcl : IsClopen {x : C | ∃ t, ∀ i, SignType.sign ((spec (P i) x.val).eval t) = v i} :=
    ⟨realized_closed_subtype (v := v) hB, realized_open_subtype (v := v) hA⟩
  rcases (isClopen_iff.mp hcl) with h | h
  · right
    intro x hx hcon
    have hmem : (⟨x, hx⟩ : C) ∈
        {x : C | ∃ t, ∀ i, SignType.sign ((spec (P i) x.val).eval t) = v i} := hcon
    rw [h] at hmem
    exact hmem
  · left
    intro x hx
    have hmem : (⟨x, hx⟩ : C) ∈
        {x : C | ∃ t, ∀ i, SignType.sign ((spec (P i) x.val).eval t) = v i} := by
      rw [h]; trivial
    exact hmem

end Work.WilE4.CAD
