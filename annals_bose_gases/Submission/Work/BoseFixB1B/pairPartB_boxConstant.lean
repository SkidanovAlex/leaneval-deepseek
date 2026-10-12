import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Word.potWord_pair_prod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

/-! ## 1. Two-slot peel of the centred box integral -/

/-- **Two-slot peel of the centred box.**  For distinct slots `i, j`, the box integral of a
kernel that sees only those two slots factors as the volume of the remaining `n - 2` slots
times the double integral over the centred cube.  Unconditional in `B`. -/
theorem aboxPairPeel {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {B : E3 → E3 → ℝ} :
    (∫ x in Submission.BoseGases.abox n ℓ, B (x i) (x j))
      = (ℓ ^ 3) ^ (n - 2)
        * (∫ p in (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ), B p.1 p.2) := by
  have h2 : 2 ≤ n := by
    by_contra h
    exact hij (Fin.ext (by have := i.isLt; have := j.isLt; omega))
  obtain ⟨k, hk⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  subst hk
  obtain ⟨b', hb'⟩ : ∃ b' : Fin (k + 1), i.succAbove b' = j :=
    Fin.exists_succAbove_eq (x := j) (y := i) hij.symm
  rw [← hb']
  set ν : Measure E3 := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ) with hν
  haveI : SigmaFinite ν := by rw [hν]; infer_instance
  have hvol : ν.real Set.univ = ℓ ^ 3 := by
    rw [hν, Measure.real, Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity)]
  have hrestrict : (volume : Measure (Submission.BoseGases.X (k + 2))).restrict
      (Submission.BoseGases.abox (k + 2) ℓ) = Measure.pi (fun _ : Fin (k + 2) => ν) := by
    rw [hν]
    exact Submission.BoseGases.restrict_abox_eq_pi (k + 2) ℓ
  rw [hrestrict]
  have hLHS : (∫ x : Fin (k + 2) → E3,
        B (x i) (x (i.succAbove b')) ∂(Measure.pi (fun _ : Fin (k + 2) => ν)))
      = ∫ x : Fin (k + 2) → E3,
          B (x i) (x (i.succAbove b')) * ∏ l : Fin (k + 2), (1 : ℝ)
            ∂(Measure.pi (fun _ : Fin (k + 2) => ν)) := by
    apply integral_congr_ae
    filter_upwards with x
    simp
  rw [hLHS, Work.BoseKinLoc.Word.pair_peel ν k i b' (fun _ : E3 => (1 : ℝ)) (fun a b => B a b)]
  have hz : (∫ z : E3, (1 : ℝ) ∂ν) = ℓ ^ 3 := by
    rw [integral_const, hvol]
    simp
  have hprod : ν.prod ν = (volume : Measure (E3 × E3)).restrict
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) := by
    rw [hν, Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hp : (∫ p : E3 × E3, B p.1 p.2 * 1 * 1 ∂(ν.prod ν))
      = ∫ p in (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ), B p.1 p.2 := by
    rw [hprod]
    simp
  rw [hz, hp, Nat.add_sub_cancel]

/-! ## 2. `boxQInd = 0` forces the state to be box-constant -/

/-- **The vanishing box-excited projection makes the state constant on the box.**  If
`Q_{B,i}Φ = 0` pointwise for every slot `i` (`boxQInd`, FS's mean-free box projection with the
indicators), then `Φ` takes the same value at any two configurations of the box `abox n ℓ`.

Unfolding `boxQInd` at `x` with `xᵢ ∈ acube ℓ` gives
`Φ x = (1/ℓ³)∫_{z ∈ acube ℓ} Φ (xᵢ ↦ z)`, whose right side is independent of `xᵢ`; applying the
same identity at `xᵢ ↦ z` yields `Φ (xᵢ ↦ z) = Φ x`.  Chaining these one-slot moves over the
coordinates gives the claim. -/
theorem boxQIndZero_boxConstant {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hconst : ∀ i : Fin n,
      Work.UBBInputs8.boxQInd (ℓ ^ 3) (Submission.BoseGases.acube ℓ) i Φ = 0) :
    ∀ x ∈ Submission.BoseGases.abox n ℓ, ∀ y ∈ Submission.BoseGases.abox n ℓ, Φ x = Φ y := by
  have hmean : ∀ (i : Fin n) (x : Submission.BoseGases.X n),
      x i ∈ Submission.BoseGases.acube ℓ →
      Φ x = (1 / ℓ ^ 3) * ∫ z in Submission.BoseGases.acube ℓ, Φ (Function.update x i z) := by
    intro i x hx
    have h := congrFun (hconst i) x
    simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd] at h
    rw [Set.indicator_of_mem hx] at h
    have h' := sub_eq_zero.mp h
    simpa using h'
  have hstep : ∀ (i : Fin n) (x : Submission.BoseGases.X n),
      x i ∈ Submission.BoseGases.acube ℓ → ∀ z ∈ Submission.BoseGases.acube ℓ,
      Φ (Function.update x i z) = Φ x := by
    intro i x hx z hz
    have h1 := hmean i x hx
    have h2 := hmean i (Function.update x i z) (by rw [Function.update_self]; exact hz)
    rw [h1, h2]
    congr 1
    exact setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun z' _ => by rw [Function.update_idem])
  intro x hx y hy
  have key : ∀ s : Finset (Fin n), Φ (fun k => if k ∈ s then y k else x k) = Φ x := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert i s hi ih =>
      have hx' : (fun k : Fin n => if k ∈ s then y k else x k) i
          ∈ Submission.BoseGases.acube ℓ := by
        by_cases h : i ∈ s
        · simpa [h] using hy i
        · simpa [h] using hx i
      have hfun : (fun k : Fin n => if k ∈ insert i s then y k else x k)
          = Function.update (fun k : Fin n => if k ∈ s then y k else x k) i (y i) := by
        funext k
        rw [Function.update_apply]
        by_cases hk : k = i
        · subst hk; simp
        · rw [if_neg hk]
          simp only [Finset.mem_insert, hk, false_or]
      rw [hfun, hstep i _ hx' (y i) (hy i), ih]
  have hall := key Finset.univ
  rw [show (fun k : Fin n => if k ∈ (Finset.univ : Finset (Fin n)) then y k else x k) = y from by
    funext k; simp] at hall
  exact hall.symm

/-! ## 3. The pair part at a box-constant state -/

theorem pairPartB_boxConstant {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hconst : ∀ i : Fin n,
      Work.UBBInputs8.boxQInd (ℓ ^ 3) (Submission.BoseGases.acube ℓ) i Φ = 0)
    (hInt : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wLoc ℓ v 0 p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) :
    Work.BoseKinLoc.pairPartB n v ℓ Φ
      = (1 / 2) * ((n : ℝ) * ((n : ℝ) - 1))
          * ((∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) / ℓ ^ 6)
          * (∫ p in (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ),
              Submission.BoseGases.wLoc ℓ v 0 p.1 p.2) := by
  set K : ℝ := ∫ p in (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ),
      Submission.BoseGases.wLoc ℓ v 0 p.1 p.2 with hK
  set c : ℝ := Φ (fun _ : Fin n => 0) with hc
  -- the state is constant on the box, with value `c`
  have hcst : ∀ x ∈ Submission.BoseGases.abox n ℓ, Φ x = c := by
    intro x hx
    rw [hc]
    exact boxQIndZero_boxConstant hℓ hconst x hx (fun _ => 0)
      (fun _ => Submission.BoseGases.zero_mem_acube hℓ.le)
  -- per-pair integrability over the box
  have hIntOn : ∀ (a b : Fin n), a ≠ b →
      IntegrableOn (fun x : Submission.BoseGases.X n => Submission.BoseGases.wLoc ℓ v 0 (x a) (x b))
        (Submission.BoseGases.abox n ℓ) := by
    intro a b hab
    have h2 : 2 ≤ n := by
      by_contra h
      exact hab (Fin.ext (by have := a.isLt; have := b.isLt; omega))
    obtain ⟨k, hk⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    subst hk
    obtain ⟨b', hb'⟩ : ∃ b' : Fin (k + 1), a.succAbove b' = b :=
      Fin.exists_succAbove_eq (x := b) (y := a) hab.symm
    rw [← hb']
    exact Work.ESYRound5.Energy.integrableOn_abox_comp_pair_coord hℓ.le a b' hInt
  -- the box mass of the state
  have hΦ2 : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) = c ^ 2 * (ℓ ^ 3) ^ n := by
    have h1 : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
        = ∫ x in Submission.BoseGases.abox n ℓ, c ^ 2 := by
      apply setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
      intro x hx
      simp only [hcst x hx]
    rw [h1, integral_const]
    have hvol2 : ((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)).real Set.univ = (ℓ ^ 3) ^ n := by
      rw [Measure.real, Measure.restrict_apply_univ, Submission.BoseGases.abox_volume n ℓ hℓ.le,
        ENNReal.toReal_ofReal (by positivity)]
    rw [hvol2, smul_eq_mul]
    ring
  rw [Work.BoseKinLoc.pairPartB]
  -- replace the state by its box value
  have hA : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
          Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2)))
      = ∫ x in Submission.BoseGases.abox n ℓ, c ^ 2 *
        (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
          Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2)) := by
    apply setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
    intro x hx
    simp only [hcst x hx]
  rw [hA, integral_const_mul]
  -- push the pair sum out of the box integral
  have hC : (∫ x in Submission.BoseGases.abox n ℓ,
        (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
          Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2)))
      = ∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
          ∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2) := by
    exact MeasureTheory.integral_finsetSum Finset.univ
      (fun ij _ => hIntOn ij.1.1 ij.1.2 (ne_of_lt ij.2))
  rw [hC]
  -- evaluate each pair integral and count the pairs
  have hD : ∀ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
      (∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2))
        = (ℓ ^ 3) ^ (n - 2) * K := by
    intro ij
    rw [hK]
    exact aboxPairPeel hℓ (ne_of_lt ij.2)
  rw [Finset.sum_congr rfl (fun ij _ => hD ij), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Work.BoseKinLoc.Word.card_pair_subtype_real]
  rw [hK, hΦ2]
  rcases n with _ | _ | m
  · norm_num
  · norm_num
  · have hpow : (ℓ ^ 3 : ℝ) ^ (m + 1 + 1) = (ℓ ^ 3) ^ m * ℓ ^ 6 := by
      rw [show (m + 1 + 1 : ℕ) = m + 2 from by omega, pow_add]
      ring
    have hcancel : (c ^ 2 * (ℓ ^ 3) ^ (m + 1 + 1)) / ℓ ^ 6 = c ^ 2 * (ℓ ^ 3) ^ m := by
      rw [div_eq_iff (by positivity : (ℓ : ℝ) ^ 6 ≠ 0), hpow]
      ring
    rw [hcancel]
    simp only [show m + 1 + 1 - 2 = m from by omega]
    ring

end

end Work.BoseFixB1B
