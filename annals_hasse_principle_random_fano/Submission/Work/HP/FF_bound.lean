/-
`FF_bound`: the average bound `F_{d,n}(B) ≪ B² / (log B)^{1/2}` of
Browning--Le Boudec--Sawin (Lemma F of the paper), in the form requested for
`Submission/Work/HP/det_averages.lean`.

PERFORMANCE NOTE (2026-09-28).  As previously written this file was a single
559-line proof under `set_option maxHeartbeats 200000000`; a clean elaboration
took over 80 minutes at ~12 GB, so it never produced an olean and everything
above it was blocked.  The cause was located by per-tactic profiling: the
application of `dyadic_summation_pub` in the `F2` part wrote the filtered
finset `S.filter (fun p => ¬ (gcdMinors2 p.1 p.2 ∣ Wr))` directly, and the
unification of the goal with the (instantiated) hypothesis re-elaborated that
filter together with its `Decidable` instances: ~537 s in a single `refine`.
Binding the filtered finset once (`set S₂ ... with hS₂`, plus `hS₂mem`) and
using `S₂` everywhere in the `F2` part removes that unification.  Three smaller
latent errors were fixed at the same time: the coercion ascription in the
`ncard` step of `hcount`, `Real.one_rpow` (was `one_rpow`), and the final
`calc` step (was `div_le_div_iff_of_pos` with a goal it could not match).
The statement of `FF_bound` is unchanged, and the whole file now elaborates in
~19 s under `set_option maxHeartbeats 400000`.
-/
import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.detLAux
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.Lat.span_pair_lattice
import Submission.Work.HP.EEupper.gcdMinors_veronese
import Submission.Work.HP.Sig2.nu_indep
import Submission.Work.HP.det_gam_gen
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.DyadicSum.dyadic_summation_pub
import Submission.Work.HP.w_arith
import Submission.Work.HP.EE.ellXY_two_pub
import Submission.Work.HP.detGam_pt
import Submission.Work.HP.F1_arith
import Submission.Work.HP.F1_arith2

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Finset Filter

namespace Work.HP

/-! ## Auxiliary facts -/

section Aux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma wedgeNorm_nonneg' (v w : ι → ℤ) : 0 ≤ wedgeNorm v w := by
  rw [wedgeNorm]; exact Real.sqrt_nonneg _

/-- `dmin r S ≤ detL L` for a rank-`r` lattice `L` containing `S`. -/
private lemma dmin_le_detL {r : ℕ} {S : Set (ι → ℤ)} {L : Submodule ℤ (ι → ℤ)}
    (hr : rk L = r) (hS : S ⊆ L) : dmin r S ≤ detL L := by
  rw [dmin]
  exact csInf_le ⟨0, fun D ⟨M, _, _, hM⟩ => hM ▸ detL_nonneg_gram M⟩ ⟨L, hr, hS, rfl⟩

/-- `𝔡₂(x,y) ≤ ‖x‖‖y‖`. -/
private lemma dmin_two_le_mul (x y : ι → ℤ) (h : LinearIndependent ℤ ![x, y]) :
    dmin 2 ({x, y} : Set (ι → ℤ)) ≤ eNorm x * eNorm y := by
  obtain ⟨L, hL, hxL, hyL, hdet⟩ := Lat.span_pair_lattice x y h
  refine le_trans (dmin_le_detL hL ?_) hdet
  rintro z (rfl | rfl)
  · exact hxL
  · exact hyL

/-- `1 ≤ 𝔡₂(x,y)`. -/
private lemma one_le_dmin_two (x y : ι → ℤ) (h : LinearIndependent ℤ ![x, y]) :
    1 ≤ dmin 2 ({x, y} : Set (ι → ℤ)) := by
  rw [dmin]
  refine le_csInf ⟨detL (Submodule.span ℤ (Set.range ![x, y])),
    Submodule.span ℤ (Set.range ![x, y]), ?_, ?_, rfl⟩ ?_
  · rw [rk, Module.finrank_eq_card_basis (Module.Basis.span h)]; simp
  · rintro z (rfl | rfl)
    · exact Submodule.subset_span (Set.mem_range_self 0)
    · exact Submodule.subset_span (Set.mem_range_self 1)
  · rintro D ⟨L, -, -, rfl⟩
    exact Lat.detL_ge_one L

/-- Two primitive integer vectors that are not equal up to sign are `ℤ`-linearly independent. -/
private lemma linearIndependent_of_isPrim {x y : ι → ℤ} (hx : IsPrim x) (hy : IsPrim y)
    (h1 : x ≠ y) (h2 : x ≠ -y) : LinearIndependent ℤ ![x, y] := by
  classical
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hcomp : ∀ i, a * x i + b * y i = 0 := by
    intro i
    have := congrFun hab i
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
  by_cases ha : a = 0
  · subst ha
    simp only [zero_mul, zero_add] at hcomp
    refine ⟨rfl, ?_⟩
    by_contra hb
    exact isPrim_ne_zero hy (funext fun i => (mul_eq_zero.mp (hcomp i)).resolve_left hb)
  · by_cases hb : b = 0
    · subst hb
      simp only [zero_mul, add_zero] at hcomp
      exact absurd (funext fun i => (mul_eq_zero.mp (hcomp i)).resolve_left ha) (isPrim_ne_zero hx)
    · exfalso
      have hb_dvd : b ∣ normalize a := by
        have hd : b ∣ Finset.univ.gcd (fun i => a * x i) :=
          Finset.dvd_gcd (fun i _ => ⟨-y i, by
            have h := hcomp i
            linear_combination h⟩)
        rwa [Finset.gcd_mul_left, hx, mul_one] at hd
      have ha_dvd : a ∣ normalize b := by
        have hd : a ∣ Finset.univ.gcd (fun i => b * y i) :=
          Finset.dvd_gcd (fun i _ => ⟨-x i, by
            have h := hcomp i
            linear_combination h⟩)
        rwa [Finset.gcd_mul_left, hy, mul_one] at hd
      have h1n : b.natAbs ∣ a.natAbs := by
        have h := Int.natAbs_dvd_natAbs.mpr hb_dvd
        simpa [Int.abs_eq_normalize, Int.natAbs_abs] using h
      have h2n : a.natAbs ∣ b.natAbs := by
        have h := Int.natAbs_dvd_natAbs.mpr ha_dvd
        simpa [Int.abs_eq_normalize, Int.natAbs_abs] using h
      have heq : a.natAbs = b.natAbs := (Nat.dvd_antisymm h1n h2n).symm
      have hax : ∀ i, a * x i = -(b * y i) := by
        intro i; have h := hcomp i; linarith
      rcases Int.natAbs_eq_natAbs_iff.mp heq with h | h
      · refine h2 (funext fun i => ?_)
        have hh := hax i
        rw [h] at hh
        have hb0 : b * (x i + y i) = 0 := by nlinarith [hh]
        have hx0 : x i + y i = 0 := (mul_eq_zero.mp hb0).resolve_left hb
        simp only [Pi.neg_apply]; linarith
      · refine h1 (funext fun i => ?_)
        have hh := hax i
        rw [h] at hh
        have hb0 : b * (y i - x i) = 0 := by nlinarith [hh]
        have hy0 : y i - x i = 0 := (mul_eq_zero.mp hb0).resolve_left hb
        linarith

end Aux


/-! ## Lemma F -/

private lemma eNorm_sq' {ι : Type*} [Fintype ι] (x : ι → ℤ) :
    eNorm x ^ 2 = ∑ i, ((x i : ℝ)) ^ 2 := by
  rw [eNorm, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]

private lemma wedgeNorm_le_mul {ι : Type*} [Fintype ι] (x y : ι → ℤ) :
    wedgeNorm x y ≤ eNorm x * eNorm y := by
  have h1 : eNorm x ^ 2 * eNorm y ^ 2 - (dotR (toR x) (toR y)) ^ 2 ≤ eNorm x ^ 2 * eNorm y ^ 2 := by
    nlinarith [sq_nonneg (dotR (toR x) (toR y))]
  rw [wedgeNorm]
  refine le_trans (Real.sqrt_le_sqrt h1) ?_
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (eNorm_nonneg x), Real.sqrt_sq (eNorm_nonneg y)]

private lemma gcdMinors2_pos {ι : Type*} [Fintype ι] [DecidableEq ι] {x y : ι → ℤ}
    (h : LinearIndependent ℤ ![x, y]) : 0 < gcdMinors2 x y := by
  obtain ⟨h1, -⟩ := det_gam_gen x y h
  have hD : 1 ≤ detL (latOrth x ⊓ latOrth y) := Lat.detL_ge_one _
  rw [h1] at hD
  have h : (0 : ℝ) < (gcdMinors2 x y : ℝ) := by
    rcases lt_or_ge (gcdMinors2 x y : ℝ) 0 with hlt | hge
    · have hw : 0 ≤ wedgeNorm x y := wedgeNorm_nonneg' x y
      have := div_nonpos_of_nonneg_of_nonpos hw hlt.le
      linarith
    · rcases eq_or_lt_of_le hge with heq | hgt
      · rw [← heq, div_zero] at hD
        linarith
      · exact hgt
  exact_mod_cast h

private lemma omega_finite (d n : ℕ) (B : ℝ) : (Omega d n B).Finite :=
  (MDBasic.finite_sets d n B B (fun _ => True)).2.2

private lemma mem_omega {d n : ℕ} {B : ℝ} {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)}
    (hp : p ∈ Omega d n B) :
    IsPrim p.1 ∧ IsPrim p.2 ∧ p.1 ≠ p.2 ∧ p.1 ≠ -p.2 ∧
      eNorm p.1 ≤ B ^ (1 / ((n : ℝ) + 1 - d)) ∧
      eNorm p.2 ≤ B ^ (1 / ((n : ℝ) + 1 - d)) :=
  ⟨hp.1.1, hp.2.1.1, hp.2.2.1, hp.2.2.2, hp.1.2, hp.2.1.2⟩

/-- Generic form of the `min(1,Δ²/α²)` part of Lemma F, summed over a finite set. -/
private lemma F1_sum_bound (d : ℕ) (hd : 2 ≤ d) {γ : Type*} (S : Finset γ) (α : ℝ) (hα : 1 ≤ α)
    (Dv : γ → ℝ) (x y D Δ : γ → ℝ) (C₁ C₂ : ℝ) (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂)
    (hDv : ∀ p ∈ S, 0 < Dv p)
    (h1 : ∀ p ∈ S, 1 ≤ x p ∧ 1 ≤ y p ∧ 1 ≤ D p ∧ 0 ≤ Δ p)
    (h2 : ∀ p ∈ S, 1 / Dv p ≤ C₁ / (D p * x p ^ (d - 1) * y p ^ (d - 1)))
    (h3 : ∀ p ∈ S, Δ p * D p ≤ C₂ * (x p * y p)) :
    ∃ K : ℝ, 0 < K ∧ (∑ p ∈ S, min 1 ((Δ p / α) ^ 2) * (1 / Dv p))
      ≤ K * C₁ * C₂ * α ^ (-(1 / 2) : ℝ)
        * (∑ p ∈ S, 1 / (D p ^ ((3 : ℝ) / 2) * x p ^ ((d : ℝ) - 3 / 2)
            * y p ^ ((d : ℝ) - 3 / 2))) := by
  obtain ⟨Cfd, hCfdpos, hCfd⟩ := F1_arith2 d hd
  refine ⟨Cfd, hCfdpos, ?_⟩
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun p hp => ?_)
  obtain ⟨ha, hb, hc, hd0⟩ := h1 p hp
  have hden : 0 < D p * x p ^ (d - 1) * y p ^ (d - 1) := by
    have h1' : 0 < D p := by linarith
    have h2' : 0 < x p ^ (d - 1) := pow_pos (by linarith) _
    have h3' : 0 < y p ^ (d - 1) := pow_pos (by linarith) _
    positivity
  have hγpos : 0 < Dv p := hDv p hp
  have hkey := hCfd α (x p) (y p) (D p) (Δ p) (Dv p) C₁ C₂ hα ha hb hc hd0 hγpos hC₁ hC₂
    (h2 p hp) (h3 p hp)
  calc min 1 ((Δ p / α) ^ 2) * (1 / Dv p)
      ≤ Cfd * C₁ * C₂ * α ^ (-(1 / 2) : ℝ)
        / (D p ^ ((3 : ℝ) / 2) * x p ^ ((d : ℝ) - 3 / 2) * y p ^ ((d : ℝ) - 3 / 2)) := hkey
    _ = Cfd * C₁ * C₂ * α ^ (-(1 / 2) : ℝ)
        * (1 / (D p ^ ((3 : ℝ) / 2) * x p ^ ((d : ℝ) - 3 / 2) * y p ^ ((d : ℝ) - 3 / 2))) := by
      ring

/-- Generic form of the indicator part of Lemma F, summed over a finite set. -/
private lemma F2_sum_bound {γ : Type*} (S : Finset γ) (Dv : γ → ℝ) (x y D : γ → ℝ) (C : ℝ)
    (h2 : ∀ p ∈ S, 1 / Dv p ≤ C / (D p * x p * y p)) :
    (∑ p ∈ S, 1 / Dv p) ≤ C * (∑ p ∈ S, 1 / (D p * x p * y p)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun p hp => ?_)
  refine le_trans (h2 p hp) (le_of_eq ?_)
  rw [mul_one_div]

theorem FF_bound (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2)) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ B : ℝ, B₀ ≤ B →
      FF d n B ≤ K * B ^ 2 / Real.log B ^ ((1 : ℝ) / 2) := by
  have hn3 : 3 ≤ n := by
    rcases eq_or_ne d 2 with h | h
    · subst h
      have h2 : n ≠ 2 := fun hn => h22 (by simp [hn])
      omega
    · omega
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdnR : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  obtain ⟨Cpt, hCptpos, hCpt⟩ := detGam_pt d n hd
  obtain ⟨Kc, hKcpos, hKc⟩ := ellXY_two_pub n (by omega)
  obtain ⟨Cfd, hCfdpos, hCfd⟩ := F1_arith2 d hd
  have hCD1 : (0:ℝ) ≤ (d:ℝ) - 3/2 := by linarith
  have hCT1 : (0:ℝ) < 3/2 := by norm_num
  have hCN1 : (3:ℝ)/2 < (n:ℝ) - 1 := by linarith
  have hCS1 : (d:ℝ) - 3/2 + 3/2 ≤ (n:ℝ) := by linarith
  obtain ⟨Cd1, hCd1pos, hCd1⟩ := dyadic_summation_pub n hn3 ((d:ℝ) - 3/2) (3/2) hCD1 hCT1 hCN1 hCS1
  have hCD2 : (0:ℝ) ≤ (d:ℝ) - 1 := by linarith
  have hCN2 : (1:ℝ) < (n:ℝ) - 1 := by linarith
  have hCS2 : (d:ℝ) - 1 + 1 ≤ (n:ℝ) := by linarith
  obtain ⟨Cd2, hCd2pos, hCd2⟩ := dyadic_summation_pub n hn3 ((d:ℝ) - 1) 1 hCD2 (by norm_num) hCN2 hCS2
  obtain ⟨hw1, hw2⟩ := w_arith n hn3
  obtain ⟨Bw, hBw⟩ := eventually_atTop.mp hw2
  refine ⟨Cfd * (max Cpt 1) ^ 2 * Cd1 * Kc + Cpt * Cd2 * Kc + 1,
    max 3 (max (Real.exp 2) (max Bw (Real.exp (Real.exp 1)))),
    by positivity, ?_⟩
  intro B hB
  have hB3 : 3 ≤ B := le_trans (le_max_left _ _) hB
  have hBexp : Real.exp 2 ≤ B :=
    le_trans (le_trans (le_max_left _ _) (le_max_right (3 : ℝ) _)) hB
  have hBBw : Bw ≤ B :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right (Real.exp 2) _))
      (le_max_right (3 : ℝ) _)) hB
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 < B := by linarith
  set T : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hT
  set α : ℝ := Real.log B with hα
  set w : ℝ := wOf B with hwdef
  have hkpos : 0 < (n : ℝ) + 1 - d := by linarith
  have hT1 : 1 ≤ T := by
    rw [hT]; exact Real.one_le_rpow hB1 (by positivity)
  have hα2 : 2 ≤ α := by
    rw [hα]; exact (Real.le_log_iff_exp_le hB0).mpr hBexp
  have hα1 : 1 ≤ α := by linarith
  have hαpos : 0 < α := by linarith
  have hw1' : 1 ≤ w := by
    rw [hwdef, wOf, ← hα]
    have hlogα : 0 < Real.log α := Real.log_pos (by linarith)
    rw [le_div_iff₀ hlogα]
    linarith [Real.log_le_sub_one_of_pos hαpos]
  have hwrel : α ^ ((1 : ℝ) / 2) ≤ w ^ (n - 2) := by
    rw [hα, hwdef]; exact hBw B hBBw
  have hfin : (Omega d n B).Finite := omega_finite d n B
  set S : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) := hfin.toFinset with hSdef
  have hmem : ∀ p ∈ S, p ∈ Omega d n B := by
    intro p hp
    rw [hSdef, Set.Finite.mem_toFinset] at hp
    exact hp
  have hFF : FF d n B = ∑ p ∈ S, errXY d n B p.1 p.2 / detL (Gam d n p.1 p.2) := by
    rw [FF, hSdef]
    exact finsum_mem_eq_finite_toFinset_sum _ hfin
  have hpt : ∀ p ∈ S, IsPrim p.1 ∧ IsPrim p.2 ∧ p.1 ≠ p.2 ∧ p.1 ≠ -p.2 ∧
      eNorm p.1 ≤ T ∧ eNorm p.2 ≤ T := by
    intro p hp
    obtain ⟨a, b, c, e, f, g⟩ := mem_omega (hmem p hp)
    exact ⟨a, b, c, e, by rw [hT]; exact f, by rw [hT]; exact g⟩
  have hli : ∀ p ∈ S, LinearIndependent ℤ ![p.1, p.2] := by
    intro p hp
    obtain ⟨a, b, c, e, -, -⟩ := hpt p hp
    exact linearIndependent_of_isPrim a b c e
  have hone : ∀ p ∈ S, 1 ≤ eNorm p.1 ∧ 1 ≤ eNorm p.2 ∧
      1 ≤ dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) := by
    intro p hp
    obtain ⟨a, b, c, e, -, -⟩ := hpt p hp
    exact ⟨one_le_eNorm_of_ne_zero (isPrim_ne_zero a), one_le_eNorm_of_ne_zero (isPrim_ne_zero b),
      one_le_dmin_two p.1 p.2 (hli p hp)⟩
  have hDmul : ∀ p ∈ S, dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ eNorm p.1 * eNorm p.2 :=
    fun p hp => dmin_two_le_mul p.1 p.2 (hli p hp)
  have hptb : ∀ p ∈ S,
      (1 / detL (Gam d n p.1 p.2) ≤ Cpt / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))
          * eNorm p.1 ^ (d - 1) * eNorm p.2 ^ (d - 1))) ∧
      (DeltaXY d n p.1 p.2 * dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))
          ≤ Cpt * (eNorm p.1 * eNorm p.2)) := by
    intro p hp
    obtain ⟨a, b, c, e, -, -⟩ := hpt p hp
    exact hCpt p.1 p.2 a b c e
  have hptb' : ∀ p ∈ S,
      (1 / detL (Gam d n p.1 p.2) ≤ max Cpt 1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))
          * eNorm p.1 ^ (d - 1) * eNorm p.2 ^ (d - 1))) ∧
      (DeltaXY d n p.1 p.2 * dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))
          ≤ max Cpt 1 * (eNorm p.1 * eNorm p.2)) := by
    intro p hp
    obtain ⟨hb1, hb2⟩ := hptb p hp
    obtain ⟨hh1, hh2, hh3⟩ := hone p hp
    refine ⟨le_trans hb1 ?_, le_trans hb2 ?_⟩
    · refine div_le_div_of_nonneg_right (le_max_left _ _) ?_
      have hx : 0 < eNorm p.1 ^ (d - 1) := pow_pos (by linarith) _
      have hy : 0 < eNorm p.2 ^ (d - 1) := pow_pos (by linarith) _
      positivity
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hcount : ∀ A Bb Δ : ℝ, 1 ≤ A → 1 ≤ Bb → 0 < Δ →
      ((S.filter (fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ Bb ∧
        dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ)).card : ℝ)
      ≤ Kc * A ^ 2 * Bb ^ 2 * Δ ^ (n - 1) := by
    intro A Bb Δ hA hBb hΔ
    by_cases hΔ1 : 1 ≤ Δ
    · have hsub : (((S.filter (fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ Bb ∧
            dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ)) : Finset _) : Set _) ⊆
          {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) |
            LinearIndependent ℤ ![p.1, p.2] ∧ eNorm p.1 ≤ A ∧ eNorm p.2 ≤ Bb ∧
              dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ} := by
        intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter] at hp
        exact ⟨hli p hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩
      have hfinite : ({p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) |
            LinearIndependent ℤ ![p.1, p.2] ∧ eNorm p.1 ≤ A ∧ eNorm p.2 ≤ Bb ∧
              dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ}).Finite := by
        refine ((MDBasic.finite_eNorm_le (max A 0)).prod
          (MDBasic.finite_eNorm_le (max Bb 0))).subset ?_
        intro p hp
        exact ⟨le_trans hp.2.1 (le_max_left _ _), le_trans hp.2.2.1 (le_max_left _ _)⟩
      have hcard := Set.ncard_le_ncard hsub hfinite
      have hcard' : (((S.filter (fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ Bb ∧
            dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ)).card : ℕ) : ℝ)
          ≤ (({p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) |
              LinearIndependent ℤ ![p.1, p.2] ∧ eNorm p.1 ≤ A ∧ eNorm p.2 ≤ Bb ∧
                dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ}).ncard : ℝ) := by
        rw [← Set.ncard_coe_finset]
        exact_mod_cast hcard
      exact le_trans hcard' (hKc A Bb Δ hA hBb hΔ1)
    · have hlt1 : Δ < 1 := not_le.mp hΔ1
      have hempty : (S.filter (fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ Bb ∧
          dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro p hp hcond
        have h3 := (hone p hp).2.2
        linarith [hcond.2.2, h3]
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      positivity
  -- F1
  have hF1 : (∑ p ∈ S, min 1 ((DeltaXY d n p.1 p.2 / α) ^ 2) / detL (Gam d n p.1 p.2))
      ≤ Cfd * (max Cpt 1) ^ 2 * α ^ (-(1 / 2) : ℝ) * (∑ p ∈ S,
          1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ ((3 : ℝ) / 2)
            * eNorm p.1 ^ ((d : ℝ) - 3 / 2) * eNorm p.2 ^ ((d : ℝ) - 3 / 2))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    obtain ⟨h1, h2, h3⟩ := hone p hp
    obtain ⟨hb1, hb2⟩ := hptb' p hp
    have hΔnn : 0 ≤ DeltaXY d n p.1 p.2 := by
      rw [DeltaXY]
      exact div_nonneg (mul_nonneg (eNorm_nonneg _) (eNorm_nonneg _)) (wedgeNorm_nonneg' _ _)
    have hγpos : 0 < detL (Gam d n p.1 p.2) := lt_of_lt_of_le zero_lt_one (Lat.detL_ge_one _)
    have hCp1 : 1 ≤ max Cpt 1 := le_max_right _ _
    have hca := hCfd α (eNorm p.1) (eNorm p.2) (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)))
      (DeltaXY d n p.1 p.2) (detL (Gam d n p.1 p.2)) (max Cpt 1) (max Cpt 1) hα1 h1 h2 h3 hΔnn
      hγpos hCp1 hCp1 hb1 hb2
    calc min 1 ((DeltaXY d n p.1 p.2 / α) ^ 2) / detL (Gam d n p.1 p.2)
        = min 1 ((DeltaXY d n p.1 p.2 / α) ^ 2) * (1 / detL (Gam d n p.1 p.2)) := by ring
      _ ≤ Cfd * max Cpt 1 * max Cpt 1 * α ^ (-(1 / 2) : ℝ)
            / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ ((3 : ℝ) / 2)
              * eNorm p.1 ^ ((d : ℝ) - 3 / 2) * eNorm p.2 ^ ((d : ℝ) - 3 / 2)) := hca
      _ = Cfd * (max Cpt 1) ^ 2 * α ^ (-(1 / 2) : ℝ)
            * (1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ ((3 : ℝ) / 2)
              * eNorm p.1 ^ ((d : ℝ) - 3 / 2) * eNorm p.2 ^ ((d : ℝ) - 3 / 2))) := by ring
  have hF1sum : (∑ p ∈ S, 1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ ((3 : ℝ) / 2)
        * eNorm p.1 ^ ((d : ℝ) - 3 / 2) * eNorm p.2 ^ ((d : ℝ) - 3 / 2)))
      ≤ Cd1 * Kc * T ^ (2 * ((n : ℝ) + 1 - ((d : ℝ) - 3 / 2) - 3 / 2))
          / (1 : ℝ) ^ ((n : ℝ) - 1 - 3 / 2) := by
    refine hCd1 S (fun p => eNorm p.1) (fun p => eNorm p.2)
      (fun p => dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) Kc 1 T hKcpos (by norm_num) hT1 ?_ hcount
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hone p hp
    obtain ⟨-, -, -, -, h5, h6⟩ := hpt p hp
    exact ⟨h1, h2, h3, by rw [mul_one]; exact hDmul p hp, h5, h6⟩
  have hTpow : T ^ (2 * ((n : ℝ) + 1 - d)) = B ^ 2 := by
    rw [hT]
    rw [← Real.rpow_mul (le_of_lt hB0)]
    have hexp : (1 / ((n : ℝ) + 1 - d)) * (2 * ((n : ℝ) + 1 - d)) = 2 := by
      field_simp
    rw [hexp, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hTpow1 : T ^ (2 * ((n : ℝ) + 1 - ((d : ℝ) - 3 / 2) - 3 / 2)) = B ^ 2 := by
    have : 2 * ((n : ℝ) + 1 - ((d : ℝ) - 3 / 2) - 3 / 2) = 2 * ((n : ℝ) + 1 - d) := by ring
    rw [this, hTpow]
  have hTpow2 : T ^ (2 * ((n : ℝ) + 1 - ((d : ℝ) - 1) - 1)) = B ^ 2 := by
    have : 2 * ((n : ℝ) + 1 - ((d : ℝ) - 1) - 1) = 2 * ((n : ℝ) + 1 - d) := by ring
    rw [this, hTpow]
  -- F2
  set Wr : ℤ := ((bigW (wOf B) / radW (wOf B) : ℕ) : ℤ) with hWrdef
  set S₂ : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
    S.filter (fun p => ¬ (gcdMinors2 p.1 p.2 ∣ Wr)) with hS₂
  have hS₂mem : ∀ p ∈ S₂, p ∈ S := by
    intro p hp
    rw [hS₂, Finset.mem_filter] at hp
    exact hp.1
  have hF2eq : (∑ p ∈ S, (if gcdMinors2 p.1 p.2 ∣ Wr then 0 else 1) / detL (Gam d n p.1 p.2))
      = (∑ p ∈ S₂, 1 / detL (Gam d n p.1 p.2)) := by
    rw [hS₂, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : gcdMinors2 p.1 p.2 ∣ Wr <;> simp [h]
  have hF2pt : ∀ p ∈ S₂,
      1 / detL (Gam d n p.1 p.2) ≤ Cpt * (1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ (1 : ℝ)
          * eNorm p.1 ^ ((d : ℝ) - 1) * eNorm p.2 ^ ((d : ℝ) - 1))) := by
    intro p hp
    obtain ⟨hb1, -⟩ := hptb p (hS₂mem p hp)
    have hxr : eNorm p.1 ^ ((d : ℝ) - 1) = eNorm p.1 ^ (d - 1) := by
      rw [show ((d : ℝ) - 1) = ((d - 1 : ℕ) : ℝ) by
        rw [Nat.cast_sub hd1]; ring, Real.rpow_natCast]
    have hyr : eNorm p.2 ^ ((d : ℝ) - 1) = eNorm p.2 ^ (d - 1) := by
      rw [show ((d : ℝ) - 1) = ((d - 1 : ℕ) : ℝ) by
        rw [Nat.cast_sub hd1]; ring, Real.rpow_natCast]
    rw [hxr, hyr, Real.rpow_one]
    calc 1 / detL (Gam d n p.1 p.2)
        ≤ Cpt / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * eNorm p.1 ^ (d - 1)
            * eNorm p.2 ^ (d - 1)) := hb1
      _ = Cpt * (1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * eNorm p.1 ^ (d - 1)
            * eNorm p.2 ^ (d - 1))) := by ring
  have hF2count : ∀ A Bb Δ : ℝ, 1 ≤ A → 1 ≤ Bb → 0 < Δ →
      ((S₂.filter
        (fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ Bb ∧
          dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ)).card : ℝ)
      ≤ Kc * A ^ 2 * Bb ^ 2 * Δ ^ (n - 1) := by
    intro A Bb Δ hA hBb hΔ
    refine le_trans (by
      have hle : (S₂.filter
            (fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ Bb ∧
              dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ)).card
          ≤ (S.filter (fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ Bb ∧
              dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ)).card :=
        Finset.card_le_card (by
          intro p hp
          obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
          exact Finset.mem_filter.mpr ⟨hS₂mem p hp1, hp2⟩)
      exact_mod_cast hle) (hcount A Bb Δ hA hBb hΔ)
  have hF2V : ∀ p ∈ S₂,
      dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * w ≤ eNorm p.1 * eNorm p.2 := by
    intro p hp
    rw [hS₂] at hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpS, hnot⟩ := hp
    have hgpos : 0 < gcdMinors2 p.1 p.2 := gcdMinors2_pos (hli p hpS)
    have hDpos : 0 < dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) :=
      lt_of_lt_of_le zero_lt_one (hone p hpS).2.2
    have hwap : dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (gcdMinors2 p.1 p.2 : ℝ)
        = wedgeNorm p.1 p.2 := by
      obtain ⟨hA, hB⟩ := det_gam_gen p.1 p.2 (hli p hpS)
      rw [hB, hA, mul_comm]
      exact mul_div_cancel₀ _ (by exact_mod_cast (ne_of_gt hgpos))
    have hm1 : 1 ≤ (gcdMinors2 p.1 p.2).natAbs := by
      have h1 : (1 : ℤ) ≤ gcdMinors2 p.1 p.2 := by omega
      omega
    have hmlt : w < ((gcdMinors2 p.1 p.2).natAbs : ℝ) := by
      by_contra hcon
      rw [not_lt] at hcon
      refine hnot ?_
      have hdvd := hw1 w (le_of_lt (lt_of_lt_of_le zero_lt_one hw1'))
        (gcdMinors2 p.1 p.2).natAbs hm1 hcon
      have h2 : (((gcdMinors2 p.1 p.2).natAbs : ℤ)) ∣ Wr := by
        have h3 := Int.natCast_dvd_natCast.mpr hdvd
        simpa [hWrdef] using h3
      rwa [Int.natAbs_of_nonneg (le_of_lt hgpos)] at h2
    have hwle : w ≤ (gcdMinors2 p.1 p.2 : ℝ) := by
      have h3 : (((gcdMinors2 p.1 p.2).natAbs : ℤ) : ℝ) = (gcdMinors2 p.1 p.2 : ℝ) := by
        have h4 : (((gcdMinors2 p.1 p.2).natAbs : ℕ) : ℤ) = gcdMinors2 p.1 p.2 :=
          Int.natAbs_of_nonneg (le_of_lt hgpos)
        rw [h4]
      have h5 : ((gcdMinors2 p.1 p.2).natAbs : ℝ)
          = (((gcdMinors2 p.1 p.2).natAbs : ℤ) : ℝ) := by norm_num
      linarith [hmlt.le, h3.le, h3.ge, h5.le, h5.ge]
    calc dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * w
        ≤ dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (gcdMinors2 p.1 p.2 : ℝ) :=
          mul_le_mul_of_nonneg_left hwle hDpos.le
      _ = wedgeNorm p.1 p.2 := hwap
      _ ≤ eNorm p.1 * eNorm p.2 := wedgeNorm_le_mul p.1 p.2
  have hF2sum : (∑ p ∈ S₂,
        1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ (1 : ℝ)
          * eNorm p.1 ^ ((d : ℝ) - 1) * eNorm p.2 ^ ((d : ℝ) - 1)))
      ≤ Cd2 * Kc * T ^ (2 * ((n : ℝ) + 1 - ((d : ℝ) - 1) - 1)) / w ^ ((n : ℝ) - 1 - 1) := by
    refine hCd2 S₂ (fun p => eNorm p.1)
      (fun p => eNorm p.2) (fun p => dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)))
      Kc w T hKcpos hw1' hT1 ?_ hF2count
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hone p (hS₂mem p hp)
    obtain ⟨-, -, -, -, h5, h6⟩ := hpt p (hS₂mem p hp)
    exact ⟨h1, h2, h3, hF2V p hp, h5, h6⟩
  -- assemble
  have hsplit : FF d n B
      = (∑ p ∈ S, min 1 ((DeltaXY d n p.1 p.2 / α) ^ 2) / detL (Gam d n p.1 p.2))
        + (∑ p ∈ S, (if gcdMinors2 p.1 p.2 ∣ Wr then 0 else 1) / detL (Gam d n p.1 p.2)) := by
    rw [hFF, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [errXY, hα, hWrdef, div_pow, add_div]
  have hmain1 : (∑ p ∈ S, min 1 ((DeltaXY d n p.1 p.2 / α) ^ 2) / detL (Gam d n p.1 p.2))
      ≤ Cfd * (max Cpt 1) ^ 2 * Cd1 * Kc * B ^ 2 / α ^ ((1 : ℝ) / 2) := by
    have h2 : (∑ p ∈ S, 1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ ((3 : ℝ) / 2)
          * eNorm p.1 ^ ((d : ℝ) - 3 / 2) * eNorm p.2 ^ ((d : ℝ) - 3 / 2)))
        ≤ Cd1 * Kc * B ^ 2 := by
      have := hF1sum
      rw [hTpow1] at this
      have h1p : (1:ℝ) ^ ((n:ℝ) - 1 - 3/2) = 1 := by rw [Real.one_rpow]
      rw [h1p, div_one] at this
      exact this
    have h3 : (∑ p ∈ S, 1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ ((3 : ℝ) / 2)
          * eNorm p.1 ^ ((d : ℝ) - 3 / 2) * eNorm p.2 ^ ((d : ℝ) - 3 / 2))) ≤ Cd1 * Kc * B ^ 2 := h2
    calc (∑ p ∈ S, min 1 ((DeltaXY d n p.1 p.2 / α) ^ 2) / detL (Gam d n p.1 p.2))
        ≤ Cfd * (max Cpt 1) ^ 2 * α ^ (-(1 / 2) : ℝ) * (∑ p ∈ S,
            1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ ((3 : ℝ) / 2)
              * eNorm p.1 ^ ((d : ℝ) - 3 / 2) * eNorm p.2 ^ ((d : ℝ) - 3 / 2))) := hF1
      _ ≤ Cfd * (max Cpt 1) ^ 2 * α ^ (-(1 / 2) : ℝ) * (Cd1 * Kc * B ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = Cfd * (max Cpt 1) ^ 2 * Cd1 * Kc * B ^ 2 / α ^ ((1 : ℝ) / 2) := by
          rw [Real.rpow_neg hαpos.le, one_div]
          ring
  have hmain2 : (∑ p ∈ S, (if gcdMinors2 p.1 p.2 ∣ Wr then 0 else 1) / detL (Gam d n p.1 p.2))
      ≤ Cpt * Cd2 * Kc * B ^ 2 / w ^ (n - 2) := by
    rw [hF2eq]
    have h2 : (∑ p ∈ S₂,
        1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ (1 : ℝ)
          * eNorm p.1 ^ ((d : ℝ) - 1) * eNorm p.2 ^ ((d : ℝ) - 1))) ≤ Cd2 * Kc * B ^ 2 / w ^ (n - 2) := by
      have := hF2sum
      rw [hTpow2] at this
      have hwpow : w ^ ((n:ℝ) - 1 - 1) = w ^ (n - 2) := by
        rw [show ((n:ℝ) - 1 - 1) = ((n - 2 : ℕ) : ℝ) by rw [Nat.cast_sub (by omega : 2 ≤ n)]; ring,
          Real.rpow_natCast]
      rw [hwpow] at this
      exact this
    have hpt2 : (∑ p ∈ S₂, 1 / detL (Gam d n p.1 p.2))
        ≤ Cpt * (∑ p ∈ S₂,
            1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ (1 : ℝ)
              * eNorm p.1 ^ ((d : ℝ) - 1) * eNorm p.2 ^ ((d : ℝ) - 1))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun p hp => hF2pt p hp)
    calc (∑ p ∈ S₂, 1 / detL (Gam d n p.1 p.2))
        ≤ Cpt * (∑ p ∈ S₂,
            1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ (1 : ℝ)
              * eNorm p.1 ^ ((d : ℝ) - 1) * eNorm p.2 ^ ((d : ℝ) - 1))) := hpt2
      _ ≤ Cpt * (Cd2 * Kc * B ^ 2 / w ^ (n - 2)) := mul_le_mul_of_nonneg_left h2 hCptpos.le
      _ = Cpt * Cd2 * Kc * B ^ 2 / w ^ (n - 2) := by ring
  have hstep2 : Cpt * Cd2 * Kc * B ^ 2 / w ^ (n - 2)
      ≤ Cpt * Cd2 * Kc * B ^ 2 / α ^ ((1 : ℝ) / 2) :=
    div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hαpos _) hwrel
  calc FF d n B
      = (∑ p ∈ S, min 1 ((DeltaXY d n p.1 p.2 / α) ^ 2) / detL (Gam d n p.1 p.2))
        + (∑ p ∈ S, (if gcdMinors2 p.1 p.2 ∣ Wr then 0 else 1) / detL (Gam d n p.1 p.2)) := hsplit
    _ ≤ Cfd * (max Cpt 1) ^ 2 * Cd1 * Kc * B ^ 2 / α ^ ((1 : ℝ) / 2)
          + Cpt * Cd2 * Kc * B ^ 2 / α ^ ((1 : ℝ) / 2) := by linarith [hmain1, hmain2, hstep2]
    _ = (Cfd * (max Cpt 1) ^ 2 * Cd1 * Kc + Cpt * Cd2 * Kc) * B ^ 2 / α ^ ((1 : ℝ) / 2) := by ring
    _ ≤ (Cfd * (max Cpt 1) ^ 2 * Cd1 * Kc + Cpt * Cd2 * Kc + 1) * B ^ 2
          / Real.log B ^ ((1 : ℝ) / 2) := by
      rw [hα]
      have hα12pos : 0 < Real.log B ^ ((1 : ℝ) / 2) :=
        Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg B)) hα12pos.le

end Work.HP
