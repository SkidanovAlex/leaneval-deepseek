import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Psi
import Submission.Work.HP.tau_basic
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.isPrim_veronese
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.MMReindex

/-!
# `N_V^loc(B) ≥ (1/2)·(log B·W/‖a‖)·#𝒯 / (√N_{d,n}·R^d)`

The localised counting function
`N_V^loc(B) = (1/2)·(log B·W(w(B))/‖a‖)·Σ_{x ∈ Z_y} ‖ν(x)‖^{-1}`
dominates the (rescaled) number of lattice points in the set
`𝒯 = {x : x prim, ‖x‖ ≤ R, W ∣ f_a(x), a ∈ 𝒞_{ν(x)}^{(log B)}}`, where `R = B^{1/(n+1-d)}`.

Indeed `Z_y ∩ {‖x‖ ≤ R} = 𝒯`, and for every `x ∈ 𝒯` the `d`-homogeneity of the Veronese
map together with `‖x‖ ≤ R` gives `‖ν(x)‖ ≤ √(N_{d,n})·R^d`, while primitivity makes
`ν(x) ≠ 0`.  Summing the resulting lower bound `‖ν(x)‖^{-1} ≥ (√N_{d,n}·R^d)^{-1}` over
`#𝒯` points and multiplying by the (nonnegative, for `B > 1`) prefactor gives the claim.
For `B ≤ 1` the prefactor is `≤ 0` and the cone condition `a ∈ 𝒞_{ν(x)}^{(γ)}` with `γ ≤ 0`
forces `ν(x) = 0`, hence `Z_y = ∅` unless `γ = 0`, in which case the prefactor vanishes.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.HP2

/-! ## Auxiliary lemmas -/

/-- The Euclidean norm of an integer vector vanishes only for the zero vector. -/
lemma NVle_eNorm_eq_zero_iff {ι : Type*} [Fintype ι] (v : ι → ℤ) : eNorm v = 0 ↔ v = 0 := by
  rw [eNorm_eq_rNorm_toR, rNorm_eq_zero]
  constructor
  · intro h
    funext i
    have h2 : ((v i : ℤ) : ℝ) = ((0 : ℤ) : ℝ) := by simpa [toR] using congrFun h i
    exact_mod_cast h2
  · intro h
    subst h
    funext i
    simp [toR]

/-- The Veronese vector of a primitive vector is nonzero (for every `d`, including `d = 0`). -/
lemma NVle_veronese_ne_zero (d n : ℕ) {x : Fin (n + 1) → ℤ} (hx : IsPrim x) :
    veronese d n x ≠ 0 := by
  have hxne : x ≠ 0 := by
    intro h0
    rw [IsPrim, h0] at hx
    have hz : (Finset.univ.gcd (0 : Fin (n + 1) → ℤ)) = 0 :=
      Finset.gcd_eq_zero_iff.mpr fun i _ => rfl
    rw [hz] at hx
    exact one_ne_zero hx.symm
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hxne (funext h)
  intro hzero
  have h1 : veronese d n x (monDiHP d n j) = 0 := by rw [hzero]; rfl
  rw [veronese_monDiHP] at h1
  exact pow_ne_zero d hj h1

/-- `‖ν(x)‖ > 0` for a primitive `x`. -/
lemma NVle_isPrim_veronese_pos (d n : ℕ) {x : Fin (n + 1) → ℤ} (hx : IsPrim x) :
    0 < eNorm (veronese d n x) := by
  refine lt_of_le_of_ne (eNorm_toR_nonneg _) (Ne.symm fun h0 => ?_)
  exact NVle_veronese_ne_zero d n hx ((NVle_eNorm_eq_zero_iff _).mp h0)

/-- `‖ν(x)‖ ≤ √(N_{d,n})·R^d` whenever `‖x‖ ≤ R` and `R ≥ 0`. -/
lemma NVle_eNorm_veronese_le_sqrt (d n : ℕ) (x : Fin (n + 1) → ℤ) {R : ℝ}
    (hx : eNorm x ≤ R) : eNorm (veronese d n x) ≤ Real.sqrt ((NN d n : ℕ) : ℝ) * R ^ d := by
  have h1 : eNorm (veronese d n x) ≤ Real.sqrt ((NN d n : ℕ) : ℝ) * eNorm x ^ d := by
    rw [eNorm_eq_rNorm_toR, toR_veronese, eNorm_eq_rNorm_toR]
    exact veronese_rNorm_upper d n (toR x)
  have h2 : eNorm x ^ d ≤ R ^ d := pow_le_pow_left₀ (eNorm_toR_nonneg x) hx d
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))

/-- For `γ < 0` the cone `𝒞_v^{(γ)}` contains only vectors whose `v`-coordinate is `0`. -/
lemma NVle_rNorm_eq_zero_of_mem_Cgam {ι : Type*} [Fintype ι] {v t : ι → ℝ} {γ : ℝ}
    (hγ : γ < 0) (ht : t ≠ 0) (h : t ∈ Cgam v γ) : rNorm v = 0 := by
  rw [Cgam, Set.mem_ofPred_eq] at h
  have ht0 : 0 < rNorm t :=
    lt_of_le_of_ne (rNorm_nonneg t) (Ne.symm fun h0 => ht (rNorm_eq_zero.mp h0))
  have hden : 2 * γ < 0 := by linarith
  have hle : rNorm v * rNorm t / (2 * γ) ≤ 0 :=
    div_nonpos_of_nonneg_of_nonpos (mul_nonneg (rNorm_nonneg v) (le_of_lt ht0)) (le_of_lt hden)
  have habs : |dotR v t| = 0 := le_antisymm (le_trans h hle) (abs_nonneg _)
  have hge : 0 ≤ rNorm v * rNorm t / (2 * γ) := by rw [← habs]; exact h
  have hzero : rNorm v * rNorm t / (2 * γ) = 0 := le_antisymm hle hge
  have hprod : rNorm v * rNorm t = 0 := by
    rcases div_eq_zero_iff.mp hzero with h' | h'
    · exact h'
    · exact absurd h' (ne_of_lt hden)
  rcases mul_eq_zero.mp hprod with h' | h'
  · exact h'
  · exact absurd h' (ne_of_gt ht0)

/-- A finite sum of numbers bounded below by `c` is at least `#s · c`. -/
lemma NVle_card_le_finsum {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℝ) {c : ℝ}
    (hf : ∀ x ∈ s, c ≤ f x) : (s.ncard : ℝ) * c ≤ ∑ᶠ x ∈ s, f x := by
  rw [finsum_mem_eq_finite_toFinset_sum f hs]
  calc (s.ncard : ℝ) * c = (hs.toFinset.card : ℝ) * c := by rw [Set.ncard_eq_toFinset_card s hs]
    _ = ∑ x ∈ hs.toFinset, c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ hs.toFinset, f x :=
        Finset.sum_le_sum fun x hx => hf x ((Set.Finite.mem_toFinset hs).mp hx)

/-! ## The main estimate -/

theorem NVloc_ge_ncard (d n : ℕ) (a : Work.HP.Mon d n → ℤ) (B R : ℝ)
    (hR : R = B ^ (1 / ((n : ℝ) + 1 - d))) (hRpos : 0 < R) (ha : 0 < Work.HP.eNorm a) :
    (1 / 2) * (Real.log B * (Work.HP.bigW (Work.HP.wOf B) : ℝ) / Work.HP.eNorm a) *
        ((({x : Fin (n + 1) → ℤ | Work.HP.IsPrim x ∧ Work.HP.eNorm x ≤ R ∧
            ((Work.HP.bigW (Work.HP.wOf B) : ℕ) : ℤ) ∣ Work.HP.formEval d n a x ∧
            (Work.HP.toR a) ∈ Work.HP.Cgam (Work.HP.toR (Work.HP.veronese d n x))
              (Real.log B)} : Set (Fin (n + 1) → ℤ))).ncard : ℝ)
        / (Real.sqrt ((Work.HP.NN d n : ℕ) : ℝ) * R ^ d)
      ≤ Work.HP.NVloc d n a B := by
  classical
  have hWpos : (0 : ℝ) < (bigW (wOf B) : ℝ) := by
    have h : 0 < bigW (wOf B) := lt_of_lt_of_le Nat.zero_lt_one (one_le_bigW (wOf B))
    exact_mod_cast h
  have hNNpos : (0 : ℝ) < (NN d n : ℝ) := by
    have h := one_le_NN d n
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h)
  have hDpos : 0 < Real.sqrt ((NN d n : ℕ) : ℝ) * R ^ d :=
    mul_pos (Real.sqrt_pos_of_pos hNNpos) (pow_pos hRpos d)
  have ha_ne : toR a ≠ 0 := by
    intro h0
    have h1 : eNorm a = 0 := by
      rw [eNorm_eq_rNorm_toR]
      exact rNorm_eq_zero.mpr h0
    exact absurd h1 (ne_of_gt ha)
  rw [NVloc]
  set S : Set (Fin (n + 1) → ℤ) := {x ∈ Xi d n B |
      ((bigW (wOf B) : ℕ) : ℤ) ∣ formEval d n a x ∧
      toR a ∈ Cgam (toR (veronese d n x)) (Real.log B)} with hSdef
  set T : Set (Fin (n + 1) → ℤ) := {x : Fin (n + 1) → ℤ | IsPrim x ∧ eNorm x ≤ R ∧
      ((bigW (wOf B) : ℕ) : ℤ) ∣ formEval d n a x ∧
      toR a ∈ Cgam (toR (veronese d n x)) (Real.log B)} with hTdef
  set D : ℝ := Real.sqrt ((NN d n : ℕ) : ℝ) * R ^ d with hDdef
  set c : ℝ := (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a) with hcdef
  have hSfin : S.Finite := by
    rw [hSdef]
    exact (Xi_finite d n B).subset fun x hx => hx.1
  have hmemS : ∀ x ∈ S, IsPrim x ∧ eNorm x ≤ R ∧
      (((bigW (wOf B) : ℕ) : ℤ) ∣ formEval d n a x ∧
        toR a ∈ Cgam (toR (veronese d n x)) (Real.log B)) := by
    intro x hx
    have hx' := hx
    rw [hSdef] at hx'
    exact ⟨hx'.1.1, by rw [hR]; exact hx'.1.2, hx'.2⟩
  have hST : T = S := by
    rw [hTdef, hSdef]
    ext x
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, by rw [← hR]; exact h2⟩, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1.1, by rw [hR]; exact h1.2, h2⟩
  by_cases hlog : 0 < Real.log B
  · have hcpos : 0 < c := by
      have h3 : 0 < (Real.log B * (bigW (wOf B) : ℝ)) / eNorm a := by
        rw [div_eq_mul_inv]
        exact mul_pos (mul_pos hlog hWpos) (inv_pos.mpr ha)
      rw [hcdef]
      exact mul_pos (by norm_num) h3
    have hmain : (T.ncard : ℝ) * (1 / D) ≤ ∑ᶠ x ∈ S, 1 / eNorm (veronese d n x) := by
      rw [hST]
      exact NVle_card_le_finsum hSfin (fun x => 1 / eNorm (veronese d n x))
        (fun x hx => one_div_le_one_div_of_le (NVle_isPrim_veronese_pos d n (hmemS x hx).1)
          (NVle_eNorm_veronese_le_sqrt d n x (hmemS x hx).2.1))
    have hstep : c * (T.ncard : ℝ) / D = c * ((T.ncard : ℝ) * (1 / D)) := by
      rw [div_eq_mul_inv, one_div]; ring
    rw [hstep]
    exact mul_le_mul_of_nonneg_left hmain (le_of_lt hcpos)
  · have hlog0 : Real.log B ≤ 0 := not_lt.mp hlog
    have hright : c * ∑ᶠ x ∈ S, 1 / eNorm (veronese d n x) = 0 := by
      rcases lt_or_eq_of_le hlog0 with hlt | heq
      · have hsum0 : ∑ᶠ x ∈ S, 1 / eNorm (veronese d n x) = 0 := by
          rw [finsum_mem_eq_finite_toFinset_sum _ hSfin]
          refine Finset.sum_eq_zero fun x hx => ?_
          have hxS : x ∈ S := (Set.Finite.mem_toFinset hSfin).mp hx
          have hm := hmemS x hxS
          have hrz : rNorm (toR (veronese d n x)) = 0 :=
            NVle_rNorm_eq_zero_of_mem_Cgam hlt ha_ne hm.2.2.2
          have he0 : eNorm (veronese d n x) = 0 := by
            rw [eNorm_eq_rNorm_toR]; exact hrz
          rw [he0, div_zero]
        rw [hsum0, mul_zero]
      · rw [hcdef, heq]; ring
    have hleft : c * (T.ncard : ℝ) / D ≤ 0 := by
      have h2 : c ≤ 0 := by
        have h4 : Real.log B * (bigW (wOf B) : ℝ) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hlog0 (le_of_lt hWpos)
        have h3 : (Real.log B * (bigW (wOf B) : ℝ)) / eNorm a ≤ 0 := by
          rw [div_eq_mul_inv]
          exact mul_nonpos_of_nonpos_of_nonneg h4 (inv_nonneg.mpr (le_of_lt ha))
        rw [hcdef]
        exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) h3
      have h1 : 0 ≤ (T.ncard : ℝ) / D := div_nonneg (Nat.cast_nonneg _) (le_of_lt hDpos)
      calc c * (T.ncard : ℝ) / D = c * ((T.ncard : ℝ) / D) := by rw [mul_div_assoc]
        _ ≤ 0 * ((T.ncard : ℝ) / D) := mul_le_mul_of_nonneg_right h2 h1
        _ = 0 := by rw [zero_mul]
    rw [hright]
    exact hleft

end Work.HP.HP2
