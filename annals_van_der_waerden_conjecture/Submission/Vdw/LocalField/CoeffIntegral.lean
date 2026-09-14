import Mathlib
import Submission.Vdw.LocalField.ScalarNorm
import Submission.Vdw.LocalField.WUnramified

open Classical
open scoped NumberField WithZero Valued

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Local-field chapter (G3, (b2)): coefficient integrality and p-divisibility (L-A, L-B)

For the Teichmüller subfield `W = ℚ_p(ζ)` (`ζ := teich p P α`, `α ≠ 0` a
generator of `κ^×`, `hgen`), a tuple `c : Fin f → ℚ_p` of coefficients
(`f := P.inertiaDeg ℤ`) determines the element

    wSum p P α c := Σ_{i<f} (c i : K_P) · ζ^i ∈ K_P.

The two coefficient lemmas of the `e(W)=1` argument (Roadmap Session-91):

* `coeffs_integral_of_norm_le_one` (L-A): `‖wSum c‖ ≤ 1 ⟹ ∀ i, ‖c i‖ ≤ 1`
  — an integral combination has integral coefficients.  Proof: if a
  coefficient were non-integral, scale by a coefficient `M := c m` of
  maximal norm; the ratios `c i / M` are integral (`norm_div` +
  maximality), lift to `ℤ_[p]` (`liftCoeff` — `qpAdic_norm_le_one_iff_mem_int`),
  and the order element `u := orderSum d` has a unit coefficient at `m`
  (ratio `1`), so `‖u‖ = 1` (`orderSum_norm_eq_one_of_unitCoeff`); but
  `u = (wSum c)/M` (`orderSum_image_eq` + `map_div₀` + `Finset.sum_mul`) has
  norm `≤ 1/‖M‖ < 1` (`scalar_norm_le_one_iff` contrapositive) —
  contradiction.
* `coeffs_p_divisible_of_norm_lt_one` (L-B): with integral coefficients,
  `‖wSum c‖ < 1 ⟹ ∀ i, ‖c i‖ ≤ ‖p‖` — the coefficients are divisible by
  `p` (norm form).  Proof: lift to `ℤ_[p]`; the order element has norm < 1,
  so its reduction vanishes (`mem_maximalIdeal_iff_norm_lt_one` +
  `orderSum_coeffs_of_mk_zero`); each coefficient lies in `mR = (p)`
  (`qpReduction_eq_zero_iff` + `qpIntMaximalIdeal_eq_span_p` +
  `Ideal.mem_span_singleton`), so it is `p·(integral element)` with norm
  `≤ ‖p‖` (`qpInt_norm_le_one`).

Supporting facts (reusable): `qpAdic_norm_le_one_iff_mem_int` (membership
in `ℤ_[p]` ⟺ norm ≤ 1), `qpInt_coe_injective`, `qpInt_norm_le_one`,
`liftCoeff`/`liftCoeff_spec`, `orderSum_image_eq` (the order element's value
is the scalar-value coefficient sum).

These are the tuple-level statements: the `OW_ker ≤ Ideal.span {pOW}`
inclusion (`e(W)=1`) applies them to an element `w ∈ 𝒪_W` via the power
basis `{1,…,ζ^{f−1}}` of `W` (coefficients `pb.basis.repr w`, image
equalities) — recorded in Roadmap Session-92.

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- the value in K_P of the Teichmüller order combination
`Σ_{i<f} (c i) · ζ^i`, `c : Fin f → QpAdic`. -/
def wSum (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (c : Fin (P.inertiaDeg ℤ) → QpAdic p) : kpAdic p P :=
  ∑ i : Fin (P.inertiaDeg ℤ),
    (algebraMap (QpAdic p) (kpAdic p P) (c i)) *
      (((teich p P α : kpInt p P) : kpAdic p P) ^ (i : ℕ))

/-- integrality in ℚ_p = membership in ℤ_[p]. -/
theorem qpAdic_norm_le_one_iff_mem_int (p : ℕ) [Fact (Nat.Prime p)] (c : QpAdic p) :
    (∃ d : QpInt p, (d : QpAdic p) = c) ↔ ‖c‖ ≤ 1 := by
  classical
  constructor
  · rintro ⟨d, rfl⟩
    rw [norm_le_one_iff_val_qp]
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (R := ℤ) ℚ (qprime p)).mp d.2
  · intro h
    rw [norm_le_one_iff_val_qp] at h
    refine ⟨⟨c, (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (R := ℤ) ℚ (qprime p)).mpr h⟩, rfl⟩

/-- the embedding ℤ_[p] → ℚ_p is injective. -/
lemma qpInt_coe_injective (p : ℕ) [Fact (Nat.Prime p)] :
    Function.Injective (fun d : QpInt p => (d : QpAdic p)) := by
  intro a b h
  apply Subtype.ext
  exact h

/-- norm of a scalar: ‖(d : QpAdic)‖ ≤ 1 for integral d. -/
lemma qpInt_norm_le_one (p : ℕ) [Fact (Nat.Prime p)] (d : QpInt p) :
    ‖(d : QpAdic p)‖ ≤ 1 := by
  exact (qpAdic_norm_le_one_iff_mem_int p (d : QpAdic p)).mp ⟨d, rfl⟩

/-- coefficient lifting: an integral coefficient is the value of an integral
element of ℤ_[p]; the lift agrees with the coefficient. -/
noncomputable def liftCoeff (p : ℕ) [Fact (Nat.Prime p)] (c : QpAdic p) (hc : ‖c‖ ≤ 1) : QpInt p :=
  Classical.choose ((qpAdic_norm_le_one_iff_mem_int p c).mpr hc)

theorem liftCoeff_spec (p : ℕ) [Fact (Nat.Prime p)] (c : QpAdic p) (hc : ‖c‖ ≤ 1) :
    ((liftCoeff p c hc : QpInt p) : QpAdic p) = c :=
  Classical.choose_spec ((qpAdic_norm_le_one_iff_mem_int p c).mpr hc)

/-- the order element's value is the coefficient sum with the same scalar values. -/
theorem orderSum_image_eq (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (d : Fin (P.inertiaDeg ℤ) → QpInt p) :
    ((orderSum p P α d : kpInt p P) : kpAdic p P)
      = ∑ i : Fin (P.inertiaDeg ℤ),
          (algebraMap (QpAdic p) (kpAdic p P) ((d i : QpInt p) : QpAdic p)) *
            (((teich p P α : kpInt p P) : kpAdic p P) ^ (i : ℕ)) := by
  simp [orderSum]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- (L-A) an integral coefficient combination has integral coefficients:
`‖Σ (c i)·ζ^i‖ ≤ 1 ⟹ ∀ i, ‖c i‖ ≤ 1`.  Proof: if some coefficient were
non-integral, scale by a coefficient of maximal norm; the scaled element
lies in the order `ℤ_p[ζ]` with a unit coefficient, so has norm 1
(`orderSum_norm_eq_one_of_unitCoeff`), yet its norm is `≤ 1/‖M‖ < 1`
(`scalar_norm_le_one_iff` makes the image of a non-integral scalar
non-integral) — contradiction. -/
theorem coeffs_integral_of_norm_le_one (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (c : Fin (P.inertiaDeg ℤ) → QpAdic p)
    (hw : ‖wSum p P α c‖ ≤ 1) : ∀ i : Fin (P.inertiaDeg ℤ), ‖c i‖ ≤ 1 := by
  classical
  intro i0
  by_contra hnot
  have hgt : 1 < ‖c i0‖ := lt_of_not_ge hnot
  have hfpos : 0 < P.inertiaDeg ℤ := Ideal.inertiaDeg_pos P ℤ
  haveI : Nonempty (Fin (P.inertiaDeg ℤ)) := ⟨⟨0, hfpos⟩⟩
  have hunivn : (Finset.univ : Finset (Fin (P.inertiaDeg ℤ))).Nonempty := by
    exact Finset.univ_nonempty
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (P.inertiaDeg ℤ))) (fun i : Fin (P.inertiaDeg ℤ) => ‖c i‖) hunivn
  have hMgt : 1 < ‖c m‖ := lt_of_lt_of_le hgt (hmax i0 (by simp))
  let M : QpAdic p := c m
  have hM0 : M ≠ 0 := by
    intro hz
    have hzm : c m = 0 := by simpa [M] using hz
    rw [hzm] at hMgt
    norm_num at hMgt
  have hratio : ∀ i : Fin (P.inertiaDeg ℤ), ‖c i / M‖ ≤ 1 := by
    intro i
    rw [norm_div]
    rw [div_le_one₀ (norm_pos_iff.mpr hM0)]
    exact hmax i (by simp)
  let d : Fin (P.inertiaDeg ℤ) → QpInt p :=
    fun i => liftCoeff p (c i / M) (hratio i)
  have hdspec : ∀ i : Fin (P.inertiaDeg ℤ), ((d i : QpInt p) : QpAdic p) = c i / M :=
    fun i => liftCoeff_spec p (c i / M) (hratio i)
  have hdm : d m = (1 : QpInt p) := by
    apply qpInt_coe_injective p
    calc
      ((d m : QpInt p) : QpAdic p) = c m / M := hdspec m
      _ = 1 := by
        dsimp [M]
        exact div_self hM0
  have hu1 : ‖(orderSum p P α d : kpAdic p P)‖ = 1 := by
    have hunit : ∃ i : Fin (P.inertiaDeg ℤ), qpReductionHom p (d i) ≠ 0 := by
      refine ⟨m, ?_⟩
      rw [hdm]
      have h1 : (qpReductionHom p (1 : QpInt p)) = (1 : ZMod p) := by simp
      rw [h1]
      have hz1 : (1 : ZMod p) ≠ 0 := by
        exact one_ne_zero
      exact hz1
    exact orderSum_norm_eq_one_of_unitCoeff p P hα hgen d hunit
  -- image equality: (orderSum d) = wSum c / (image of M)
  have hu_eq : ((orderSum p P α d : kpInt p P) : kpAdic p P)
      = (wSum p P α c) / (algebraMap (QpAdic p) (kpAdic p P) M) := by
    rw [orderSum_image_eq]
    calc
      (∑ i : Fin (P.inertiaDeg ℤ),
          algebraMap (QpAdic p) (kpAdic p P) ((d i : QpInt p) : QpAdic p) *
            (((teich p P α : kpInt p P) : kpAdic p P) ^ (i : ℕ)))
          = (∑ i : Fin (P.inertiaDeg ℤ),
              algebraMap (QpAdic p) (kpAdic p P) (c i / M) *
                (((teich p P α : kpInt p P) : kpAdic p P) ^ (i : ℕ))) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hdspec i]
      _ = (wSum p P α c) / (algebraMap (QpAdic p) (kpAdic p P) M) := by
            dsimp [wSum]
            calc
              (∑ i : Fin (P.inertiaDeg ℤ), (algebraMap (QpAdic p) (kpAdic p P) (c i / M)) *
                  (((teich p P α : kpInt p P) : kpAdic p P) ^ (i : ℕ)))
                  = ∑ i : Fin (P.inertiaDeg ℤ),
                      ((algebraMap (QpAdic p) (kpAdic p P) (c i)) *
                        (((teich p P α : kpInt p P) : kpAdic p P) ^ (i : ℕ))) *
                        ((algebraMap (QpAdic p) (kpAdic p P) M)⁻¹) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [map_div₀]
                    ring
              _ = (∑ i : Fin (P.inertiaDeg ℤ), (algebraMap (QpAdic p) (kpAdic p P) (c i)) *
                    (((teich p P α : kpInt p P) : kpAdic p P) ^ (i : ℕ))) *
                      ((algebraMap (QpAdic p) (kpAdic p P) M)⁻¹) := by
                    exact (Finset.sum_mul (s := Finset.univ)
                      (f := fun i : Fin (P.inertiaDeg ℤ) => (algebraMap (QpAdic p) (kpAdic p P) (c i)) *
                        (((teich p P α : kpInt p P) : kpAdic p P) ^ (i : ℕ))))
                      (a := ((algebraMap (QpAdic p) (kpAdic p P) M)⁻¹)).symm
              _ = (∑ i : Fin (P.inertiaDeg ℤ), (algebraMap (QpAdic p) (kpAdic p P) (c i)) *
                    (((teich p P α : kpInt p P) : kpAdic p P) ^ (i : ℕ))) /
                    (algebraMap (QpAdic p) (kpAdic p P) M) := by
                    rw [div_eq_mul_inv]
  have hMim1 : 1 < ‖(algebraMap (QpAdic p) (kpAdic p P) M)‖ := by
    have hnle : ¬ ‖(algebraMap (QpAdic p) (kpAdic p P) M)‖ ≤ 1 := by
      rw [scalar_norm_le_one_iff p P M]
      exact (not_le_of_gt (by simpa [M] using hMgt))
    exact lt_of_not_ge hnle
  have hMim0 : ‖(algebraMap (QpAdic p) (kpAdic p P) M)‖ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hMim1)
  have hu2 : ‖(orderSum p P α d : kpAdic p P)‖ < 1 := by
    rw [hu_eq]
    rw [norm_div]
    calc
      ‖wSum p P α c‖ / ‖(algebraMap (QpAdic p) (kpAdic p P) M)‖
          ≤ 1 / ‖(algebraMap (QpAdic p) (kpAdic p P) M)‖ := by
            exact div_le_div_of_nonneg_right hw (norm_nonneg _)
      _ < 1 := by
            have hpos : 0 < ‖(algebraMap (QpAdic p) (kpAdic p P) M)‖ := lt_trans zero_lt_one hMim1
            simpa using ((inv_lt_one₀ hpos).mpr hMim1)
  have hbad : (1 : ℝ) < 1 := by
    rw [hu1] at hu2
    exact hu2
  exact (lt_irrefl (1 : ℝ)) hbad
/-- (L-B) an integral coefficient combination of norm < 1 has all
coefficients divisible by p (norm form): `‖Σ (c i)·ζ^i‖ < 1 ⟹ ∀ i,
‖c i‖ ≤ ‖p‖`.  Proof: lift the coefficients to `ℤ_[p]` (`liftCoeff`), the
order element has norm < 1 so its reduction vanishes
(`orderSum_coeffs_of_mk_zero`), each coefficient lies in `mR = (p)`
(`qpReduction_eq_zero_iff` + `qpIntMaximalIdeal_eq_span_p`), so each
coefficient is `p·(integral element)` and has norm `≤ ‖p‖`. -/
theorem coeffs_p_divisible_of_norm_lt_one (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (c : Fin (P.inertiaDeg ℤ) → QpAdic p)
    (hc : ∀ i : Fin (P.inertiaDeg ℤ), ‖c i‖ ≤ 1)
    (hw : ‖wSum p P α c‖ < 1) :
    ∀ i : Fin (P.inertiaDeg ℤ), ‖c i‖ ≤ ‖(p : QpAdic p)‖ := by
  classical
  let d : Fin (P.inertiaDeg ℤ) → QpInt p := fun i => liftCoeff p (c i) (hc i)
  have hdspec : ∀ i : Fin (P.inertiaDeg ℤ), ((d i : QpInt p) : QpAdic p) = c i :=
    fun i => liftCoeff_spec p (c i) (hc i)
  -- u := orderSum d: image = wSum c and norm < 1
  have himg : ((orderSum p P α d : kpInt p P) : kpAdic p P) = wSum p P α c := by
    calc
      ((orderSum p P α d : kpInt p P) : kpAdic p P)
          = ∑ i : Fin (P.inertiaDeg ℤ),
              (algebraMap (QpAdic p) (kpAdic p P) ((d i : QpInt p) : QpAdic p)) *
                (((teich p P α : kpInt p P) : kpAdic p P) ^ (i : ℕ)) :=
                orderSum_image_eq p P α d
      _ = wSum p P α c := by
            dsimp [wSum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [hdspec i]
  have hu1 : ‖(orderSum p P α d : kpAdic p P)‖ < 1 := by
    rw [himg]
    exact hw
  have hmem : (orderSum p P α d) ∈ IsLocalRing.maximalIdeal (kpInt p P) := by
    rw [mem_maximalIdeal_iff_norm_lt_one]
    exact hu1
  have hmk0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P))
      (orderSum p P α d) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem (I := IsLocalRing.maximalIdeal (kpInt p P))).mpr hmem
  have hall := orderSum_coeffs_of_mk_zero (p := p) (P := P) (α := α) hα hgen d hmk0
  intro i
  -- d i ∈ mR = (p): ∃ e, d i = (p : QpInt) * e
  have hqi : qpReduction p P (d i) = 0 := by
    rw [qpReduction_eq_algebraMap_qpReductionHom]
    rw [hall i]
    simp
  have hmemR : (d i) ∈ IsLocalRing.maximalIdeal (QpInt p) :=
    (qpReduction_eq_zero_iff p P (d i)).mp hqi
  have hspan : (d i) ∈ Ideal.span ({(p : QpInt p)} : Set (QpInt p)) := by
    rw [qpIntMaximalIdeal_eq_span_p p] at hmemR
    exact hmemR
  rcases (Ideal.mem_span_singleton.mp hspan) with ⟨e, he⟩
  -- ‖c i‖ = ‖(d i : QpAdic)‖ ≤ ‖p‖·1
  have hpe : ‖(e : QpAdic p)‖ ≤ 1 := qpInt_norm_le_one p e
  calc
    ‖c i‖ = ‖((d i : QpInt p) : QpAdic p)‖ := by rw [hdspec i]
    _ = ‖((p : QpInt p) : QpAdic p) * ((e : QpInt p) : QpAdic p)‖ := by
          rw [he]
          rfl
    _ = ‖(p : QpAdic p)‖ * ‖((e : QpInt p) : QpAdic p)‖ := by
          rw [norm_mul]
          have hnat : ((p : QpInt p) : QpAdic p) = (p : QpAdic p) := by rfl
          rw [hnat]
    _ ≤ ‖(p : QpAdic p)‖ * 1 := by
          exact mul_le_mul_of_nonneg_left hpe (norm_nonneg _)
    _ = ‖(p : QpAdic p)‖ := by simp

theorem coeffs_p_dvd_exact (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (c : Fin (P.inertiaDeg ℤ) → QpAdic p)
    (hc : ∀ i : Fin (P.inertiaDeg ℤ), ‖c i‖ ≤ 1)
    (hw : ‖wSum p P α c‖ < 1) :
    ∀ i : Fin (P.inertiaDeg ℤ),
      ∃ e : QpInt p, (c i : QpAdic p) = (p : QpAdic p) * ((e : QpInt p) : QpAdic p) := by
  classical
  intro i
  let d : Fin (P.inertiaDeg ℤ) → QpInt p := fun j => liftCoeff p (c j) (hc j)
  have hdspec : ∀ j : Fin (P.inertiaDeg ℤ), ((d j : QpInt p) : QpAdic p) = c j :=
    fun j => liftCoeff_spec p (c j) (hc j)
  have himg : ((orderSum p P α d : kpInt p P) : kpAdic p P) = wSum p P α c := by
    calc
      ((orderSum p P α d : kpInt p P) : kpAdic p P)
          = ∑ j : Fin (P.inertiaDeg ℤ),
              (algebraMap (QpAdic p) (kpAdic p P) ((d j : QpInt p) : QpAdic p)) *
                (((teich p P α : kpInt p P) : kpAdic p P) ^ (j : ℕ)) :=
                orderSum_image_eq p P α d
      _ = wSum p P α c := by
            dsimp [wSum]
            apply Finset.sum_congr rfl
            intro j hj
            rw [hdspec j]
  have hu1 : ‖(orderSum p P α d : kpAdic p P)‖ < 1 := by
    rw [himg]
    exact hw
  have hmem : (orderSum p P α d) ∈ IsLocalRing.maximalIdeal (kpInt p P) := by
    rw [mem_maximalIdeal_iff_norm_lt_one]
    exact hu1
  have hmk0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P))
      (orderSum p P α d) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem (I := IsLocalRing.maximalIdeal (kpInt p P))).mpr hmem
  have hall := orderSum_coeffs_of_mk_zero (p := p) (P := P) (α := α) hα hgen d hmk0
  have hqi : qpReduction p P (d i) = 0 := by
    rw [qpReduction_eq_algebraMap_qpReductionHom]
    rw [hall i]
    simp
  have hmemR : (d i) ∈ IsLocalRing.maximalIdeal (QpInt p) :=
    (qpReduction_eq_zero_iff p P (d i)).mp hqi
  have hspan : (d i) ∈ Ideal.span ({(p : QpInt p)} : Set (QpInt p)) := by
    rw [qpIntMaximalIdeal_eq_span_p p] at hmemR
    exact hmemR
  rcases (Ideal.mem_span_singleton.mp hspan) with ⟨e, he⟩
  refine ⟨e, ?_⟩
  have hnat : ((p : QpInt p) : QpAdic p) = (p : QpAdic p) := by rfl
  calc
    (c i : QpAdic p) = ((d i : QpInt p) : QpAdic p) := (hdspec i).symm
    _ = (((p : QpInt p) * (e : QpInt p) : QpInt p) : QpAdic p) := by rw [he]
    _ = ((p : QpInt p) : QpAdic p) * ((e : QpInt p) : QpAdic p) := by rfl
    _ = (p : QpAdic p) * ((e : QpInt p) : QpAdic p) := by rw [hnat]

end
end Submission.Vdw.LocalField
