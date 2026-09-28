import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MDEstimates.rk_projScale
import Submission.Work.HP.MDEstimates.exists_lift_norm

/-!
# `Work.HP.MDEstimates.lam_projScale_le`: successive minima under the scaled projection

Let `L ⊆ ℤ^ι` be an integral lattice, `u ∈ L` a nonzero *shortest* vector of `L` and
`projScale u = ‖u‖² · π` the scaled orthogonal projection onto `u^⊥` (`MinkDefs.projScale`).
Write `L' = projScale u '' L`, a lattice of rank `rk L - 1`.  The theorem proved here is the
successive-minima comparison

`(√3/2) · ‖u‖² · λ_{j+1}(L) ≤ λ_j(L')`   for `1 ≤ j ≤ rk L - 1`,

which is the inductive step of a proof of Minkowski's second theorem.

The constant `√3/2` is optimal and comes from the two facts

* *lifting*: every `y ∈ L'` lifts to `x ∈ L` with `projScale u x = y` and
  `‖x‖² ≤ ‖y‖²/‖u‖⁴ + ‖u‖²/4` (`MDEstimates.exists_lift_norm`);
* *minimality*: `‖u‖ ≤ ‖v‖` for every nonzero `v ∈ L`.

Suppose `λ_j(L') < (√3/2)‖u‖²λ_{j+1}(L)`.  Then there are `y_1,…,y_j ∈ L'` linearly
independent with `‖y_k‖ ≤ s < (√3/2)‖u‖²λ_{j+1}(L)`; lifting them gives `x_k ∈ L` with
`projScale u x_k = y_k` and `‖x_k‖² ≤ s²/‖u‖⁴ + ‖u‖²/4`.  The `j+1` vectors
`u, x_1, …, x_j` are linearly independent (the projection kills `u` and is injective on the
projected part), so `λ_{j+1}(L) ≤ max(‖u‖, ‖x_1‖, …, ‖x_j‖)`.  If `‖u‖ < λ_{j+1}(L)` then
this maximum is `< λ_{j+1}(L)`, a contradiction; and if `‖u‖ = λ_{j+1}(L)` then
`‖x_1‖² < (3/4)λ_{j+1}(L)² + ‖u‖²/4 = ‖u‖²`, contradicting the minimality of `u`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Finset

namespace Work.HP.MDEstimates

open Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Adding the kernel vector back: if the images of a family `x` under the scaled projection
`projScale u` are linearly independent, then `u` together with `x` is linearly independent. -/
lemma linIndep_fin_cons_projScale (u : ι → ℤ) (hu0 : u ≠ 0) {n : ℕ}
    (f x : Fin n → (ι → ℤ)) (hf : LinearIndependent ℤ f)
    (hpx : ∀ k, projScale u (x k) = f k) :
    LinearIndependent ℤ (Fin.cons u x : Fin (n + 1) → (ι → ℤ)) := by
  -- name the family, so that its members have a fixed type
  let Y : Fin (n + 1) → (ι → ℤ) := Fin.cons u x
  have hY0 : Y 0 = u := rfl
  have hYs : ∀ k : Fin n, Y k.succ = x k := fun k => rfl
  have hpu : projScale u u = 0 := by rw [projScale_apply]; simp
  have hf' := hf
  rw [Fintype.linearIndependent_iff] at hf'
  have key : ∀ a : Fin (n + 1) → ℤ, (∑ i, a i • Y i) = 0 → ∀ i, a i = 0 := by
    intro a ha
    -- project the relation along `projScale u`: the `u`-component dies
    have hproj : (∑ k : Fin n, a k.succ • f k) = 0 := by
      have h := congrArg (fun z : ι → ℤ => projScale u z) ha
      rw [map_sum, map_zero] at h
      have h2 : (∑ i : Fin (n + 1), projScale u (a i • Y i))
          = ∑ i : Fin (n + 1), a i • projScale u (Y i) :=
        Finset.sum_congr rfl fun i _ => map_smul (projScale u) (a i) (Y i)
      rw [h2] at h
      rw [Fin.sum_univ_succ] at h
      simp only [hY0, hYs, hpx, hpu, smul_zero, zero_add] at h
      exact h
    have hzero : ∀ k : Fin n, a k.succ = 0 := fun k => hf' (fun k => a k.succ) hproj k
    have ha0smul : a 0 • u = 0 := by
      have h := ha
      rw [Fin.sum_univ_succ] at h
      have hz : (∑ k : Fin n, a k.succ • Y k.succ) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hzero k, zero_smul]
      rw [hY0, hz, add_zero] at h
      exact h
    have ha0 : a 0 = 0 := by
      by_contra hne
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hu0
      have h := congrFun ha0smul i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
      exact absurd h (mul_ne_zero hne hi)
    intro i
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨k, hk⟩
    · rw [h]; exact ha0
    · rw [hk]; exact hzero k
  change LinearIndependent ℤ Y
  rw [Fintype.linearIndependent_iff]
  exact key

/-- `λ_n(L) ≤ ρ` as soon as `L` contains `n` linearly independent vectors of norm `≤ ρ`. -/
lemma lam_le_of_norms (L : Submodule ℤ (ι → ℤ)) {n : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    {f : Fin n → (ι → ℤ)} (hfL : ∀ i, f i ∈ L) (hfI : LinearIndependent ℤ f)
    (hfn : ∀ i, eNorm (f i) ≤ ρ) : lam L n ≤ ρ := by
  rw [lam_eq_sInf]
  exact csInf_le (bddBelow_lamSet L n) ⟨hρ, f, hfL, hfI, hfn⟩

/-- A shortest nonzero vector of `L` lies on the first successive minimum from above:
`‖u‖ ≤ λ_1(L)`. -/
lemma le_lam_one_of_shortest (L : Submodule ℤ (ι → ℤ)) {u : ι → ℤ} (hu : u ∈ L) (hu0 : u ≠ 0)
    (hshort : ∀ v ∈ L, v ≠ 0 → eNorm u ≤ eNorm v) : eNorm u ≤ lam L 1 := by
  rw [lam_eq_sInf]
  refine le_csInf ?hne ?hlower
  · exact ⟨eNorm u, eNorm_nonneg u, (fun _ : Fin 1 => u), (fun _ => hu),
      linearIndependent_unique_iff.mpr hu0, fun _ => le_rfl⟩
  · rintro r ⟨-, f, hfL, hfI, hfr⟩
    exact (hshort (f 0) (hfL 0) (hfI.ne_zero 0)).trans (hfr 0)

/-- Arithmetic of the "`‖u‖ < λ_{j+1}(L)`" case: if `s < (√3/2)A²t`, `s ≥ 0`, `0 < A < t`,
then `s²/A⁴ + A²/4 < t²`. -/
private lemma arith_case_lt {A t s : ℝ} (hA : 0 < A) (ht : 0 < t) (hAt : A < t)
    (hs : 0 ≤ s) (hsc : s < Real.sqrt 3 / 2 * A ^ 2 * t) :
    s ^ 2 / A ^ 4 + A ^ 2 / 4 < t ^ 2 := by
  have hA4 : (0 : ℝ) < A ^ 4 := by positivity
  have hsq : s ^ 2 < 3 / 4 * (A ^ 4 * t ^ 2) := by
    have h1 : s ^ 2 < (Real.sqrt 3 / 2 * A ^ 2 * t) ^ 2 :=
      pow_lt_pow_left₀ hsc hs (by norm_num)
    have h2 : (Real.sqrt 3 / 2 * A ^ 2 * t) ^ 2 = 3 / 4 * (A ^ 4 * t ^ 2) := by
      rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    linarith [h1, h2]
  have h3 : s ^ 2 / A ^ 4 < 3 / 4 * t ^ 2 := by
    rw [div_lt_iff₀ hA4]
    nlinarith [hsq]
  nlinarith [h3, hA, hAt]

/-- Arithmetic of the "`‖u‖ = λ_{j+1}(L)`" case: if `s < (√3/2)A²·A` and `s ≥ 0` then
`s²/A⁴ + A²/4 < A²`. -/
private lemma arith_case_eq {A s : ℝ} (hA : 0 < A) (hs : 0 ≤ s)
    (hsc : s < Real.sqrt 3 / 2 * A ^ 2 * A) :
    s ^ 2 / A ^ 4 + A ^ 2 / 4 < A ^ 2 := by
  have hA4 : (0 : ℝ) < A ^ 4 := by positivity
  have hsq : s ^ 2 < 3 / 4 * (A ^ 4 * A ^ 2) := by
    have h1 : s ^ 2 < (Real.sqrt 3 / 2 * A ^ 2 * A) ^ 2 :=
      pow_lt_pow_left₀ hsc hs (by norm_num)
    have h2 : (Real.sqrt 3 / 2 * A ^ 2 * A) ^ 2 = 3 / 4 * (A ^ 4 * A ^ 2) := by
      rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    linarith [h1, h2]
  have h3 : s ^ 2 / A ^ 4 < 3 / 4 * A ^ 2 := by
    rw [div_lt_iff₀ hA4]
    nlinarith [hsq]
  linarith [h3]

/-- **Successive minima under the scaled projection.**  If `u` is a shortest nonzero vector of
the integral lattice `L`, then for `1 ≤ j ≤ rk L - 1` the `j`-th successive minimum of the
projected lattice `projScale u '' L` is at least `(√3/2)‖u‖²` times the `(j+1)`-st successive
minimum of `L`. -/
theorem lam_projScale_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (u : ι → ℤ) (hu : u ∈ L) (hu0 : u ≠ 0)
    (hshort : ∀ v ∈ L, v ≠ 0 → Work.HP.eNorm u ≤ Work.HP.eNorm v) (j : ℕ) (hj : 1 ≤ j)
    (hjR : j ≤ Work.HP.rk L - 1) :
    Real.sqrt 3 / 2 * Work.HP.eNorm u ^ 2 * Work.HP.lam L (j + 1) ≤
      Work.HP.lam (Submodule.map (Work.HP.projScale u) L) j := by
  classical
  set A : ℝ := eNorm u with hA
  set t : ℝ := lam L (j + 1) with ht
  set Lp : Submodule ℤ (ι → ℤ) := Submodule.map (projScale u) L with hLp
  set c : ℝ := Real.sqrt 3 / 2 * A ^ 2 * t with hc
  have hApos : 0 < A := by rw [hA]; exact eNorm_pos_of_ne_zero hu0
  have hshortA : ∀ v ∈ L, v ≠ 0 → A ≤ eNorm v := fun v hv hv0 => by
    rw [hA]; exact hshort v hv hv0
  have hrkLp : rk Lp = rk L - 1 := by rw [hLp]; exact rk_projScale L u hu hu0 hshort
  have hjLp : j ≤ rk Lp := by omega
  have hAle : A ≤ t := by
    rw [ht, hA]
    exact (le_lam_one_of_shortest L hu hu0 hshort).trans
      (lam_mono L (i := 1) (j := j + 1) (by omega) (by omega))
  have htpos : 0 < t := by
    rw [ht]
    exact lam_pos L (by omega) (by omega)
  have hcpos : 0 < c := by rw [hc]; positivity
  by_contra hcon
  push_neg at hcon
  -- `s` strictly between `λ_j(L')` and `c`
  set s : ℝ := (lam Lp j + c) / 2 with hs
  have hlam_lt_s : lam Lp j < s := by rw [hs]; linarith
  have hs_lt_c : s < c := by rw [hs]; linarith
  have hs_nonneg : 0 ≤ s := by
    rw [hs]
    have h := lam_nonneg Lp j
    linarith
  obtain ⟨f, hfLp, hfI, hfn⟩ := lam_witness Lp hjLp hlam_lt_s
  -- lift the projected vectors
  have hlift : ∀ k : Fin j, ∃ x ∈ L, projScale u x = f k ∧
      eNorm x ^ 2 ≤ eNorm (f k) ^ 2 / A ^ 4 + A ^ 2 / 4 := by
    intro k
    obtain ⟨x, hxL, hxeq, hxbd⟩ := exists_lift_norm L u hu hu0 (hfLp k)
    rw [← hA] at hxbd
    exact ⟨x, hxL, hxeq, hxbd⟩
  choose g hgL hgproj hgbd using hlift
  have hgbd' : ∀ k : Fin j, eNorm (g k) ^ 2 ≤ s ^ 2 / A ^ 4 + A ^ 2 / 4 := by
    intro k
    have h1 : eNorm (f k) ^ 2 ≤ s ^ 2 := by
      nlinarith [eNorm_nonneg (f k), hfn k, hs_nonneg]
    have h2 : eNorm (f k) ^ 2 / A ^ 4 ≤ s ^ 2 / A ^ 4 :=
      div_le_div_of_nonneg_right h1 (by positivity)
    linarith [hgbd k, h2]
  have hgI : LinearIndependent ℤ (Fin.cons u g) :=
    linIndep_fin_cons_projScale u hu0 f g hfI hgproj
  rcases lt_or_ge A t with hAt | hAt
  · -- Case `‖u‖ < λ_{j+1}(L)`: the lifted family is too short.
    let fam : Fin (j + 1) → (ι → ℤ) := Fin.cons u g
    have hfamI : LinearIndependent ℤ fam := hgI
    have hgn : ∀ k : Fin j, eNorm (g k) < t := by
      intro k
      have h1 : eNorm (g k) ^ 2 < t ^ 2 := by
        have h2 : s ^ 2 / A ^ 4 + A ^ 2 / 4 < t ^ 2 :=
          arith_case_lt hApos htpos hAt hs_nonneg hs_lt_c
        linarith [hgbd' k, h2]
      have h3 : |eNorm (g k)| < |t| := sq_lt_sq.mp h1
      rwa [abs_of_nonneg (eNorm_nonneg (g k)), abs_of_pos htpos] at h3
    have hfam_lt : ∀ i : Fin (j + 1), eNorm (fam i) < t := by
      intro i
      dsimp only [fam]
      rcases Fin.eq_zero_or_eq_succ i with h | ⟨k, hk⟩
      · rw [h, Fin.cons_zero]; exact hAt
      · rw [hk, Fin.cons_succ]; exact hgn k
    have hne : (Finset.univ : Finset (Fin (j + 1))).Nonempty :=
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    -- a vector of `L` of maximal norm among the lifted family
    obtain ⟨i₀, -, hmax⟩ :=
      (Finset.univ : Finset (Fin (j + 1))).exists_max_image (fun i => eNorm (fam i)) hne
    have hMlt : eNorm (fam i₀) < t := hfam_lt i₀
    have hle : t ≤ eNorm (fam i₀) := by
      have hfamL : ∀ i : Fin (j + 1), fam i ∈ L := by
        intro i
        dsimp only [fam]
        rcases Fin.eq_zero_or_eq_succ i with h | ⟨k, hk⟩
        · rw [h, Fin.cons_zero]; exact hu
        · rw [hk, Fin.cons_succ]; exact hgL k
      rw [ht]
      exact lam_le_of_norms L (eNorm_nonneg (fam i₀)) hfamL hfamI
        (fun i => hmax i (Finset.mem_univ i))
    exact absurd hle (not_le.mpr hMlt)
  · -- Case `λ_{j+1}(L) ≤ ‖u‖`, hence `‖u‖ = λ_{j+1}(L)`: one lift is too short.
    have hAeq : A = t := le_antisymm hAle hAt
    set k0 : Fin j := ⟨0, by omega⟩ with hk0def
    have hgn0 : eNorm (g k0) < A := by
      have h1 : eNorm (g k0) ^ 2 < A ^ 2 := by
        have h2 : s ^ 2 / A ^ 4 + A ^ 2 / 4 < A ^ 2 := by
          refine arith_case_eq hApos hs_nonneg ?_
          have hsc := hs_lt_c
          rw [hc, ← hAeq] at hsc
          exact hsc
        linarith [hgbd' k0, h2]
      have h3 : |eNorm (g k0)| < |A| := sq_lt_sq.mp h1
      rwa [abs_of_nonneg (eNorm_nonneg (g k0)), abs_of_pos hApos] at h3
    have hg0ne : g k0 ≠ 0 := by
      intro h0
      have h1 : f k0 = 0 := by rw [← hgproj k0, h0, map_zero]
      exact hfI.ne_zero k0 h1
    have hmin0 := hshortA (g k0) (hgL k0) hg0ne
    linarith

end Work.HP.MDEstimates
