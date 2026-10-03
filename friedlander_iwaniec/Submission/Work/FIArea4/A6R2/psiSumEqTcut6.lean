/-
# Area 4 (round 6): `PsiSumEqTcut6` — the identification of the `ψ`-cut sum with `Tcut`

This is the round-6 analogue of the frozen `Work.FIArea4.S15psiSum_eq_TcutMod`: the round-6
`Tcut` of `Work.FITop4.Defs6` with the round-6 cut `A6cut ψ X j` (and the round-6 ratio symbol
`(z₂/z₁|d)`, the round-6 logarithm `logFac6` and the round-6 index set `S15ixSet`) is exactly the
relaxed `ψ`-cut sum `psiSum6`.

The proof has the same three ingredients as the frozen one:

* the index-set sum is re-arranged by `sum_S15ixSet` into the pair-first form;
* the inner `d`-sum of `Tcut`, over `Sset z1 z2 = {d ≤ |Δ|/4+1 : 4d ∣ |Δ|}`, is relaxed to the
  pair-independent window `X < d ≤ S15Y Pa X j` (`psiSum6Sum_eq_relaxed`): a modulus above the
  window makes the `ψ`-argument `|Δ|/(4X2^jd) ≤ 1/2`, where `ψ` vanishes;
* `|S15x z₁ z₂|·S15y = |Δ|/(4X2^jd)` (`abs_S15x_mul_S15y`), and a pair with `Δ = 0` contributes
  nothing, because then `Sset z1 z2 = {1}` and `X < 1` is false
  (`psiSum6Sum_eq_zero_of_absDelta_eq_zero`).

The elementary Gaussian-number estimates (`int_natAbs_cast`, `abs_S15x_mul_S15y`,
`abs_re_le_sqrt_gnorm`, `abs_re_le_sqrt_two_N`, `absDelta_le_two_N`, `sum_filter_product`,
`sum_product_pair`, `sum_S15ixSet`) are reproduced here in the `A6R2` namespace, so that this
module's import closure stays inside the stable `§15` vocabulary and does not drag in the
in-flight `S15psiAux`/`S15expSumng` work.
-/
import Mathlib
import Submission.Work.FIArea4.A6R2.Defs
import Submission.Work.FIArea4.VcutMod_le_pair_crude
import Submission.Work.FIArea4.S15delta

set_option autoImplicit false

namespace Work.FIArea4.A6R2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

set_option maxHeartbeats 4000000

/-! ## 0. The elementary `§15` estimates (self-contained copies) -/

lemma int_natAbs_cast (m : ℤ) : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

/-- `|x(z₁,z₂)|·y = |Δ(z₁,z₂)|/(4X2^jd)`: the `ψ`-argument of the relaxed index set is the
`ψ`-argument of `A6cut`. -/
lemma abs_S15x_mul_S15y {X j d : ℕ} {z1 z2 : GaussianInt} (h1 : z1.re ≠ 0) (h2 : z2.re ≠ 0)
    (hX : 0 < X) (hd : 0 < d) :
    |S15x z1 z2| * S15y X j d z1 z2
      = (Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * (2 : ℝ) ^ j * (d : ℝ)) := by
  have hr1 : (z1.re : ℝ) ≠ 0 := by exact_mod_cast h1
  have hr2 : (z2.re : ℝ) ≠ 0 := by exact_mod_cast h2
  have hB : ((z1.re : ℝ) * (z2.re : ℝ)) ≠ 0 := mul_ne_zero hr1 hr2
  have h4 : (0:ℝ) < 4 * (X : ℝ) * (2:ℝ)^j * (d:ℝ) := by
    have hX' : (0:ℝ) < (X:ℝ) := by exact_mod_cast hX
    have hd' : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
    positivity
  have hnum : S15x z1 z2 = ((z1.im : ℝ) * (z2.re : ℝ) - (z1.re : ℝ) * (z2.im : ℝ))
      / ((z1.re : ℝ) * (z2.re : ℝ)) := by
    rw [S15x, div_sub_div _ _ hr1 hr2]
  have habs : (Work.FIPlan.absDelta z1 z2 : ℝ)
      = |(z1.im : ℝ) * (z2.re : ℝ) - (z1.re : ℝ) * (z2.im : ℝ)| := by
    rw [Work.FIPlan.absDelta, int_natAbs_cast]
    have hD : ((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ)
        = -((z1.im : ℝ) * (z2.re : ℝ) - (z1.re : ℝ) * (z2.im : ℝ)) := by
      rw [Work.FIArea4.Delta_eq]; push_cast; ring
    rw [hD, abs_neg]
  have habsr : ((z1.re * z2.re).natAbs : ℝ) = |(z1.re : ℝ) * (z2.re : ℝ)| := by
    rw [int_natAbs_cast]; push_cast; ring_nf
  simp only [S15y]
  rw [hnum, abs_div, habsr, habs]
  field_simp

lemma abs_re_le_sqrt_gnorm (z : GaussianInt) :
    |(z.re : ℝ)| ≤ Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
  have h1 : ‖(z : ℂ)‖ = Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) :=
    crude_norm_toComplex_eq_sqrt z
  have h2 : |(z.re : ℝ)| ≤ ‖(z : ℂ)‖ := by
    simpa using Complex.abs_re_le_norm (z : ℂ)
  rw [h1] at h2; exact h2

lemma abs_re_le_sqrt_two_N (Pa : Work.FITop.Params) {φ : ℝ} {z : GaussianInt}
    (hz : Work.FITop3.InPolarBox Pa φ z) :
    |(z.re : ℝ)| ≤ Real.sqrt (2 * Pa.N) := by
  have hθ1 : Pa.θ ≤ 1 := theta_le_one Pa
  have hg : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * Pa.N := by
    nlinarith [hz.2.2.1, Pa.hN1]
  exact le_trans (abs_re_le_sqrt_gnorm z) (Real.sqrt_le_sqrt hg)

/-- `|Δ| ≤ 2N` for a pair of the polar box. -/
lemma absDelta_le_two_N (Pa : Work.FITop.Params) {φ : ℝ} {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2) :
    ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ 2 * Pa.N := by
  have hθ1 : Pa.θ ≤ 1 := theta_le_one Pa
  have hg1 : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ 2 * Pa.N := by
    nlinarith [h1.2.2.1, Pa.hN1]
  have hg2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ 2 * Pa.N := by
    nlinarith [h2.2.2.1, Pa.hN1]
  calc ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      ≤ Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) := crude_absDelta_le_sqrt_gnorm z1 z2
    _ ≤ 2 * Pa.N := crude_sqrt_gnorm_mul_le Pa.N z1 z2 hg1 hg2

lemma sum_filter_product {γ α M : Type} [AddCommMonoid M] (s : Finset γ) (t : Finset α)
    (P : γ × α → Prop) [DecidablePred P] (f : γ → α → M) :
    (∑ p ∈ (s.product t).filter P, f p.1 p.2)
      = ∑ c ∈ s, ∑ a ∈ t.filter (fun a => P (c,a)), f c a := by
  rw [Finset.sum_filter]
  refine (Finset.sum_finset_product' (s.product t) s (fun _ => t) (fun p => Finset.mem_product)
    (f := fun c a => if P (c,a) then f c a else 0)).trans ?_
  refine Finset.sum_congr rfl (fun c hc => ?_)
  rw [Finset.sum_filter]

lemma sum_product_pair {M : Type} [AddCommMonoid M] (s t : Finset GaussianInt)
    (F : GaussianInt × GaussianInt → M) :
    (∑ p ∈ s.product t, F p) = ∑ z1 ∈ s, ∑ z2 ∈ t, F (z1,z2) :=
  Finset.sum_finset_product' (s.product t) s (fun _ => t) (fun _p => Finset.mem_product)
    (f := fun z1 z2 => F (z1,z2))

/-- The triples of `S15ixSet`, summed in the "pair first" form. -/
lemma sum_S15ixSet (Pa : Work.FITop.Params) (X j : ℕ) (g : GaussianInt → GaussianInt → ℕ → ℂ) :
    (∑ i ∈ S15ixSet Pa X j, g i.1.1 i.1.2 i.2)
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.GaussCoprime z1 z2 ∧ 0 < Work.FIPlan.absDelta z1 z2 then
            ∑ d ∈ ((Finset.Icc 1 (S15Y Pa X j)).filter
                  (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2)).filter (fun d => X < d),
              g z1 z2 d
          else 0) := by
  rw [S15ixSet,
    sum_filter_product ((Work.FITop.boxN Pa).product (Work.FITop.boxN Pa))
      (Finset.Icc 1 (S15Y Pa X j))
      (fun q : (GaussianInt × GaussianInt) × ℕ =>
        Work.FIPlan.GaussCoprime q.1.1 q.1.2 ∧ X < q.2 ∧
          4 * q.2 ∣ Work.FIPlan.absDelta q.1.1 q.1.2 ∧ 0 < Work.FIPlan.absDelta q.1.1 q.1.2)
      (fun p d => g p.1 p.2 d)]
  rw [sum_product_pair]
  refine Finset.sum_congr rfl (fun z1 hz1 => Finset.sum_congr rfl (fun z2 hz2 => ?_))
  by_cases hp : Work.FIPlan.GaussCoprime z1 z2 ∧ 0 < Work.FIPlan.absDelta z1 z2
  · rw [if_pos hp]
    refine Finset.sum_congr ?_ (fun d hd => rfl)
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    tauto
  · rw [if_neg hp]
    refine Finset.sum_eq_zero (fun d hd => ?_)
    exact absurd ⟨(Finset.mem_filter.mp hd).2.1, (Finset.mem_filter.mp hd).2.2.2.2⟩ hp

/-! ## 1. The `psiSum6Sum` presentation of `Tcut` and the relaxation of the modulus range -/

/-- The inner `d`-sum of the round-6 `Tcut` with the round-6 cut `A6cut ψ X j`, as a real number
(the round-6 analogue of `Work.FIArea4.psiCutSum`). -/
def psiSum6Sum (ψ : ℝ → ℝ) (X j : ℕ) (z1 z2 : GaussianInt) : ℝ :=
  ∑ d ∈ Work.FITop4.Sset z1 z2,
    ((Nat.totient d : ℝ) / (d : ℝ)) * A6cut ψ X j z1 z2 d *
      (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2

/-- Membership in `Work.FITop4.Sset`. -/
lemma mem_Sset {z1 z2 : GaussianInt} {d : ℕ} :
    d ∈ Work.FITop4.Sset z1 z2 ↔
      1 ≤ d ∧ d ≤ Work.FIPlan.absDelta z1 z2 / 4 + 1 ∧
        4 * d ∣ Work.FIPlan.absDelta z1 z2 := by
  simp only [Work.FITop4.Sset, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-- `A6cut` evaluated. -/
lemma A6cut_apply (ψ : ℝ → ℝ) (X j : ℕ) (z1 z2 : GaussianInt) (d : ℕ) :
    A6cut ψ X j z1 z2 d
      = if X < d then
          ψ ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * 2 ^ j * (d : ℝ)))
        else 0 := rfl

/-- The definitional identification of the round-6 `Tcut` with the `psiSum6Sum` presentation. -/
lemma Tcut_A6cut_eq (Pa : Work.FITop.Params) (X j : ℕ) (ψ : ℝ → ℝ)
    (β : GaussianInt → ℂ) :
    Work.FITop4.Tcut (Work.FITop.radN Pa) (A6cut ψ X j) β
      = 2 * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            (if Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * star (β z2)) * ((psiSum6Sum ψ X j z1 z2 : ℝ) : ℂ) else 0) := by
  rw [Work.FITop4.Tcut]
  congr 1
  refine Finset.sum_congr rfl (fun z1 hz1 => ?_)
  refine Finset.sum_congr rfl (fun z2 hz2 => ?_)
  by_cases hGC : Work.FIPlan.GaussCoprime z1 z2
  · rw [if_pos hGC, if_pos hGC, psiSum6Sum, Complex.ofReal_sum]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    push_cast
    ring
  · rw [if_neg hGC, if_neg hGC]

/-- A pair with `Δ = 0` contributes nothing to `Tcut`: then `Sset z1 z2 = {1}` and `X < 1` is
false, so the cut vanishes. -/
lemma psiSum6Sum_eq_zero_of_absDelta_eq_zero {ψ : ℝ → ℝ} {X j : ℕ} {z1 z2 : GaussianInt}
    (h : Work.FIPlan.absDelta z1 z2 = 0) (hX : 1 ≤ X) :
    psiSum6Sum ψ X j z1 z2 = 0 := by
  refine Finset.sum_eq_zero (fun d hd => ?_)
  rw [mem_Sset] at hd
  obtain ⟨hd1, hdle, -⟩ := hd
  have hdle1 : d ≤ 1 := by simpa [h] using hdle
  rw [A6cut_apply, if_neg (by omega : ¬ X < d)]
  ring

/-- **The relaxation of the modulus range** (the round-6 `psiCutSum_eq_relaxed`): the inner sum of
`Tcut` over `Sset z1 z2 = {d ≤ |Δ|/4+1 : 4d ∣ |Δ|}` equals the sum over the pair-independent
window `X < d ≤ S15Y Pa X j`, because above the window the argument of `ψ` is `≤ 1/2`. -/
lemma psiSum6Sum_eq_relaxed (Pa : Work.FITop.Params) (X j : ℕ) (ψ : ℝ → ℝ)
    (hψsup : ∀ y : ℝ, (y ≤ 1 / 2 ∨ 5 / 2 ≤ y) → ψ y = 0)
    (hX : 1 ≤ X) {z1 z2 : GaussianInt}
    (hΔle : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ 2 * Pa.N) :
    psiSum6Sum ψ X j z1 z2
      = ∑ d ∈ ((Finset.Icc 1 (S15Y Pa X j)).filter
            (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2)).filter (fun d => X < d),
          ((Nat.totient d : ℝ) / (d : ℝ)) * ψ ((Work.FIPlan.absDelta z1 z2 : ℝ)
            / (4 * (X : ℝ) * 2 ^ j * (d : ℝ))) *
            (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 := by
  have hL : psiSum6Sum ψ X j z1 z2
      = ∑ d ∈ (Work.FITop4.Sset z1 z2).filter (fun d => X < d),
          ((Nat.totient d : ℝ) / (d : ℝ)) *
            ψ ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * 2 ^ j * (d : ℝ))) *
            (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 := by
    rw [psiSum6Sum]
    have hstep : ∀ d : ℕ,
        ((Nat.totient d : ℝ) / (d : ℝ)) * A6cut ψ X j z1 z2 d *
          (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2
        = (if X < d then
            ((Nat.totient d : ℝ) / (d : ℝ)) *
              ψ ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * 2 ^ j * (d : ℝ))) *
              (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 else 0) := by
      intro d
      rw [A6cut_apply]
      by_cases hXd : X < d
      · rw [if_pos hXd, if_pos hXd]
      · rw [if_neg hXd, if_neg hXd]; ring
    rw [Finset.sum_congr rfl (fun d _ => hstep d)]
    rw [← Finset.sum_filter]
  have h1 : ∑ d ∈ (Work.FITop4.Sset z1 z2).filter (fun d => X < d),
          ((Nat.totient d : ℝ) / (d : ℝ)) *
            ψ ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * 2 ^ j * (d : ℝ))) *
            (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2
      = ∑ d ∈ (Work.FITop4.Sset z1 z2).filter (fun d => X < d) ∪
          ((Finset.Icc 1 (S15Y Pa X j)).filter
            (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2)).filter (fun d => X < d),
          ((Nat.totient d : ℝ) / (d : ℝ)) *
            ψ ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * 2 ^ j * (d : ℝ))) *
            (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 := by
    refine Finset.sum_subset Finset.subset_union_left (fun d hdK hdD => ?_)
    have hd2 : d ∈ ((Finset.Icc 1 (S15Y Pa X j)).filter
            (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2)).filter (fun d => X < d) := by
      rcases Finset.mem_union.mp hdK with h | h
      · exact absurd h hdD
      · exact h
    rw [Finset.mem_filter, Finset.mem_filter] at hd2
    obtain ⟨⟨hdI, hd4⟩, hdX⟩ := hd2
    have hΔ0 : Work.FIPlan.absDelta z1 z2 = 0 := by
      by_contra hne
      have hle : 4 * d ≤ Work.FIPlan.absDelta z1 z2 :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd4
      have hmem : d ∈ (Work.FITop4.Sset z1 z2).filter (fun d => X < d) := by
        rw [Finset.mem_filter, mem_Sset]
        exact ⟨⟨(Finset.mem_Icc.mp hdI).1, Nat.le_of_lt_succ (by omega), hd4⟩, hdX⟩
      exact hdD hmem
    rw [hΔ0]
    simp [hψsup 0 (Or.inl (by norm_num : (0:ℝ) ≤ 1/2))]
  have h2 : ∑ d ∈ ((Finset.Icc 1 (S15Y Pa X j)).filter
            (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2)).filter (fun d => X < d),
          ((Nat.totient d : ℝ) / (d : ℝ)) *
            ψ ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * 2 ^ j * (d : ℝ))) *
            (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2
      = ∑ d ∈ (Work.FITop4.Sset z1 z2).filter (fun d => X < d) ∪
          ((Finset.Icc 1 (S15Y Pa X j)).filter
            (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2)).filter (fun d => X < d),
          ((Nat.totient d : ℝ) / (d : ℝ)) *
            ψ ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * 2 ^ j * (d : ℝ))) *
            (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 := by
    refine Finset.sum_subset Finset.subset_union_right (fun d hdK hdD => ?_)
    have hd1 : d ∈ (Work.FITop4.Sset z1 z2).filter (fun d => X < d) := by
      rcases Finset.mem_union.mp hdK with h | h
      · exact h
      · exact absurd h hdD
    rw [Finset.mem_filter, mem_Sset] at hd1
    obtain ⟨⟨hd1', hdle, hd4⟩, hdX⟩ := hd1
    have hY : (S15Y Pa X j : ℝ) < (d : ℝ) := by
      by_contra hcon
      push_neg at hcon
      apply hdD
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨hd1', by exact_mod_cast hcon⟩, hd4⟩, hdX⟩
    have hYge : (Pa.N : ℝ) ≤ (X : ℝ) * 2 ^ j * (S15Y Pa X j : ℝ) := by
      have h1 : Pa.N / ((X : ℝ) * 2 ^ j) ≤ (S15Y Pa X j : ℝ) := by
        have := Nat.le_ceil (Pa.N / ((X : ℝ) * 2 ^ j))
        simp only [S15Y]
        push_cast
        linarith
      rw [div_le_iff₀ (by positivity)] at h1
      linarith [h1]
    have hdgt : (Pa.N : ℝ) < (X : ℝ) * 2 ^ j * (d : ℝ) := by
      have : (X : ℝ) * 2 ^ j * (S15Y Pa X j : ℝ) < (X : ℝ) * 2 ^ j * (d : ℝ) := by
        have hpos : (0 : ℝ) < (X : ℝ) * 2 ^ j := by positivity
        exact mul_lt_mul_of_pos_left hY hpos
      linarith
    have hargle : (Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * 2 ^ j * (d : ℝ))
        ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hΔle, hdgt]
    rw [hψsup _ (Or.inl hargle)]
    ring
  rw [hL, h1, ← h2]

/-! ## 2. The identification -/

theorem psiSumEqTcut6 : Work.FIArea4.A6R2.PsiSumEqTcut6 := by
  intro Pa X j ψ hψsup hX φ β hβ
  rw [Tcut_A6cut_eq Pa X j ψ β]
  rw [show psiSum6 Pa X j ψ β = ∑ i ∈ S15ixSet Pa X j,
      coef6 β i * ((Work.FITop4.logFac6 i.1.1 i.1.2 : ℝ) : ℂ) *
        ((ψ (|S15x i.1.1 i.1.2| * S15y X j i.2 i.1.1 i.1.2) : ℝ) : ℂ) from rfl]
  rw [sum_S15ixSet Pa X j (fun z1 z2 d =>
      coef6 β ((z1, z2), d) * ((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ) *
        ((ψ (|S15x z1 z2| * S15y X j d z1 z2) : ℝ) : ℂ))]
  rw [show Work.FITop.boxN Pa = Work.FIPlan.gBox (Work.FITop.radN Pa) from rfl]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z1 hz1 => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z2 hz2 => ?_)
  by_cases hGC : Work.FIPlan.GaussCoprime z1 z2
  · by_cases hΔ0 : Work.FIPlan.absDelta z1 z2 = 0
    · rw [if_pos hGC,
        if_neg (show ¬ (Work.FIPlan.GaussCoprime z1 z2 ∧
            0 < Work.FIPlan.absDelta z1 z2) from fun h => absurd h.2 (by omega))]
      rw [psiSum6Sum_eq_zero_of_absDelta_eq_zero (ψ := ψ) (X := X) (j := j)
        (z1 := z1) (z2 := z2) hΔ0 hX]
      simp
    · have hpair : Work.FIPlan.GaussCoprime z1 z2 ∧ 0 < Work.FIPlan.absDelta z1 z2 :=
        ⟨hGC, Nat.pos_of_ne_zero hΔ0⟩
      rw [if_pos hGC, if_pos hpair]
      by_cases hb1 : β z1 = 0
      · simp only [coef6, hb1, zero_mul, mul_zero, Finset.sum_const_zero]
      · by_cases hb2 : β z2 = 0
        · simp only [coef6, hb2, star_zero, zero_mul, mul_zero, Finset.sum_const_zero]
        · have hpo1 := hβ.inPolarBox hb1
          have hpo2 := hβ.inPolarBox hb2
          have hΔle := absDelta_le_two_N Pa hpo1 hpo2
          have hz1r : z1.re ≠ 0 := fun h => by
            have hodd := hpo1.1.1
            rw [h] at hodd
            exact absurd hodd (by decide)
          have hz2r : z2.re ≠ 0 := fun h => by
            have hodd := hpo2.1.1
            rw [h] at hodd
            exact absurd hodd (by decide)
          rw [psiSum6Sum_eq_relaxed Pa X j ψ hψsup hX hΔle]
          rw [Complex.ofReal_sum]
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun d hd => ?_)
          have hdX : X < d := (Finset.mem_filter.mp hd).2
          have hdpos : 0 < d := by omega
          have harg := abs_S15x_mul_S15y (j := j) hz1r hz2r (by omega : 0 < X) hdpos
          rw [coef6, w6, harg]
          push_cast
          ring
  · rw [if_neg hGC,
      if_neg (show ¬ (Work.FIPlan.GaussCoprime z1 z2 ∧
          0 < Work.FIPlan.absDelta z1 z2) from fun h => hGC h.1)]
    simp

end

end Work.FIArea4.A6R2
