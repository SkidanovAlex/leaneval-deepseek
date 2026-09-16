import Submission.ZagierHoffmanProof.Carlitz
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Order

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial
open scoped BigOperators

/-!
# The Carlitz logarithm

Let `F` be a finite field, `q = Nat.card F`, `A = F[X]` (`θ = X`) and `K = RatFunc F`.
This file constructs the *Carlitz logarithm*
```
log_C(z) = ∑_{i ≥ 0} z ^ (q ^ i) / L_i ,      L_i = ∏_{j = 1}^{i} (θ - θ ^ (q ^ j))
```
(the denominators `carlitzL` introduced in `Submission.ZagierHoffmanProof.Carlitz`) and proves its
two basic theorems:

* **the functional equation** `log_C(θ z + z ^ q) = θ · log_C(z)` — the statement that `log_C`
  linearises the Carlitz module `C_θ(z) = θ z + z ^ q`;
* ★ **`log_C ∘ e_C = id`**: the Carlitz logarithm is the left inverse of the Carlitz exponential
  `e_C(z) = ∑ z ^ (q ^ i) / D_i`.

The proof of the second does *not* proceed by a direct coefficient computation on the composition
(which over a field of characteristic `p` is not accessible through finite sums), but through the
functional equations: the composite `W = log_C ∘ e_C` satisfies `W(θ z) = θ W(z)` (because
`e_C(θ z) = θ e_C(z) + e_C(z) ^ q` and `log_C` linearises `C_θ`), so comparing coefficients gives
`(θ ^ n - θ) · [z ^ n] W = 0`; since `θ ^ n ≠ θ` for `n ≠ 1` and `[z] W = 1` it follows that
`W = z`.

The key technical device is `coeff_subst_sparse`: the coefficients of the substitution of the
Carlitz series `θ z + z ^ q` into a series whose coefficients are supported on the `q`-powers.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

section LogCoeff


noncomputable def carlitzLCoeff (n : ℕ) : RatFunc F := by
  classical
  exact if h : ∃ i, n = Nat.card F ^ i then
    (((carlitzL F h.choose : F[X]) : RatFunc F))⁻¹ else 0

lemma carlitzLCoeff_pow (i : ℕ) :
    carlitzLCoeff F (Nat.card F ^ i) = (((carlitzL F i : F[X]) : RatFunc F))⁻¹ := by
  classical
  have hex : ∃ j, Nat.card F ^ i = Nat.card F ^ j := ⟨i, rfl⟩
  unfold carlitzLCoeff
  rw [dif_pos hex]
  rw [show hex.choose = i from
    Nat.pow_right_injective (carlitz_card_ge_two F) (Classical.choose_spec hex).symm]

lemma carlitzLCoeff_eq_zero {n : ℕ} (h : ∀ i, n ≠ Nat.card F ^ i) : carlitzLCoeff F n = 0 := by
  unfold carlitzLCoeff
  rw [dif_neg (fun hh => h hh.choose hh.choose_spec)]

noncomputable def carlitzLog : PowerSeries (RatFunc F) := PowerSeries.mk (carlitzLCoeff F)

@[simp]
lemma carlitzLog_coeff (n : ℕ) : (carlitzLog F).coeff n = carlitzLCoeff F n :=
  PowerSeries.coeff_mk n (carlitzLCoeff F)

lemma carlitzLog_coeff_pow (i : ℕ) :
    (carlitzLog F).coeff (Nat.card F ^ i) = (((carlitzL F i : F[X]) : RatFunc F))⁻¹ := by
  rw [carlitzLog_coeff, carlitzLCoeff_pow]

lemma carlitzLog_coeff_eq_zero {n : ℕ} (h : ∀ i, n ≠ Nat.card F ^ i) :
    (carlitzLog F).coeff n = 0 := by
  rw [carlitzLog_coeff, carlitzLCoeff_eq_zero F h]

lemma carlitzLog_coeff_zero : (carlitzLog F).coeff 0 = 0 :=
  carlitzLog_coeff_eq_zero F (fun i hi => by
    have h := pow_pos (by have := carlitz_card_ge_two F; omega : 0 < Nat.card F) i
    omega)

lemma carlitzLog_coeff_one : (carlitzLog F).coeff 1 = 1 := by
  have h := carlitzLog_coeff_pow F 0
  rw [pow_zero] at h
  rw [h, carlitzL_zero,
    show ((1 : F[X]) : RatFunc F) = 1 from by
      show (algebraMap F[X] (RatFunc F)) 1 = 1
      rw [map_one]]
  exact inv_one

lemma carlitzL_coe_ne_zero (i : ℕ) : (((carlitzL F i : F[X]) : RatFunc F)) ≠ 0 :=
  (map_ne_zero_iff (algebraMap F[X] (RatFunc F)) (RatFunc.algebraMap_injective F)).mpr
    (carlitzL_ne_zero F i)

lemma carlitzL_coe_rec (i : ℕ) :
    (((carlitzL F (i + 1) : F[X]) : RatFunc F))
      = (((carlitzL F i : F[X]) : RatFunc F))
        * (carlitzTheta F - (carlitzTheta F) ^ (Nat.card F ^ (i + 1))) := by
  rw [carlitzL_succ, carlitz_coe_mul, carlitz_coe_sub, carlitz_coe_pow]
  rfl

/-- The recursion of the Carlitz logarithm coefficients: `l_{i+1} (θ - θ ^ (q ^ (i+1))) = l_i`. -/
lemma carlitzLog_coeff_rec (i : ℕ) :
    (carlitzLog F).coeff (Nat.card F ^ (i + 1))
        * (carlitzTheta F - (carlitzTheta F) ^ (Nat.card F ^ (i + 1)))
      = (carlitzLog F).coeff (Nat.card F ^ i) := by
  have hfac : carlitzTheta F - (carlitzTheta F) ^ (Nat.card F ^ (i + 1)) ≠ 0 := by
    intro h
    have h1 : (((carlitzL F (i + 1) : F[X]) : RatFunc F))
        = (((carlitzL F i : F[X]) : RatFunc F))
          * (carlitzTheta F - (carlitzTheta F) ^ (Nat.card F ^ (i + 1))) :=
      carlitzL_coe_rec F i
    rw [h, mul_zero] at h1
    exact carlitzL_coe_ne_zero F (i + 1) h1
  rw [carlitzLog_coeff_pow, carlitzLog_coeff_pow, carlitzL_coe_rec F i]
  have hLi : (((carlitzL F i : F[X]) : RatFunc F)) ≠ 0 := carlitzL_coe_ne_zero F i
  field_simp

end LogCoeff

section Subst


instance instCharPowerSeries (p : ℕ) [CharP (RatFunc F) p] :
    CharP (PowerSeries (RatFunc F)) p where
  cast_eq_zero_iff n := by
    rw [show ((n : PowerSeries (RatFunc F))) = PowerSeries.C (n : RatFunc F) from
      map_natCast PowerSeries.C n,
      show (0 : PowerSeries (RatFunc F)) = PowerSeries.C 0 from (map_zero PowerSeries.C).symm,
      PowerSeries.C_injective.eq_iff]
    exact CharP.cast_eq_zero_iff (RatFunc F) p n

lemma ps_add_pow_card (u v : PowerSeries (RatFunc F)) :
    (u + v) ^ (Nat.card F) = u ^ (Nat.card F) + v ^ (Nat.card F) := by
  obtain ⟨e, hprime, hcard⟩ := card_eq_ringChar_pow F
  haveI : CharP (PowerSeries (RatFunc F)) (ringChar F) := instCharPowerSeries F (ringChar F)
  haveI : Fact (Nat.Prime (ringChar F)) := ⟨hprime⟩
  rw [hcard]
  exact add_pow_char_pow u v (ringChar F) e

lemma ps_C_mul_X_pow_pow_card (u : RatFunc F) (i : ℕ) :
    (PowerSeries.C u * (PowerSeries.X : PowerSeries (RatFunc F)) ^ (Nat.card F ^ i)) ^ (Nat.card F)
      = PowerSeries.C (u ^ (Nat.card F))
        * (PowerSeries.X : PowerSeries (RatFunc F)) ^ (Nat.card F ^ (i + 1)) := by
  rw [mul_pow, ← map_pow, ← pow_mul, pow_succ]

lemma ps_X_pow_pow_card (i : ℕ) :
    ((PowerSeries.X : PowerSeries (RatFunc F)) ^ (Nat.card F ^ i)) ^ (Nat.card F)
      = (PowerSeries.X : PowerSeries (RatFunc F)) ^ (Nat.card F ^ (i + 1)) := by
  rw [← pow_mul, pow_succ]

/-- The Carlitz-substitution series `θ z + z ^ q`. -/
noncomputable def carlitzSubst : PowerSeries (RatFunc F) :=
  PowerSeries.C (carlitzTheta F) * (PowerSeries.X : PowerSeries (RatFunc F))
    + (PowerSeries.X : PowerSeries (RatFunc F)) ^ (Nat.card F)

lemma carlitzSubst_constantCoeff : (carlitzSubst F).constantCoeff = 0 := by
  rw [carlitzSubst, map_add, map_mul, map_pow, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X, zero_pow (by have := carlitz_card_ge_two F; omega)]
  ring

lemma hasSubst_carlitzSubst : PowerSeries.HasSubst (carlitzSubst F) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (carlitzSubst_constantCoeff F)

/-- The powers of the Carlitz-substitution series: `(θ z + z ^ q) ^ (q ^ i)
= θ ^ (q ^ i) z ^ (q ^ i) + z ^ (q ^ (i+1))`. -/
lemma carlitzSubst_pow (i : ℕ) :
    (carlitzSubst F) ^ (Nat.card F ^ i)
      = PowerSeries.C ((carlitzTheta F) ^ (Nat.card F ^ i))
          * (PowerSeries.X : PowerSeries (RatFunc F)) ^ (Nat.card F ^ i)
        + (PowerSeries.X : PowerSeries (RatFunc F)) ^ (Nat.card F ^ (i + 1)) := by
  induction i with
  | zero => simp [carlitzSubst]
  | succ i ih =>
      conv_lhs => rw [show Nat.card F ^ (i + 1) = Nat.card F ^ i * Nat.card F from pow_succ _ _]
      rw [pow_mul, ih, ps_add_pow_card F, ps_C_mul_X_pow_pow_card F, ps_X_pow_pow_card F]
      rw [show ((carlitzTheta F) ^ (Nat.card F ^ i)) ^ (Nat.card F)
            = (carlitzTheta F) ^ (Nat.card F ^ (i + 1)) from by rw [← pow_mul, pow_succ]]

lemma coeff_carlitzSubst_pow (i n : ℕ) :
    ((carlitzSubst F) ^ (Nat.card F ^ i)).coeff n
      = (if n = Nat.card F ^ i then (carlitzTheta F) ^ (Nat.card F ^ i) else 0)
        + (if n = Nat.card F ^ (i + 1) then 1 else 0) := by
  rw [carlitzSubst_pow, map_add, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X_pow]

lemma carlitzSubst_pow_coeff_eq_zero {i n : ℕ} (h1 : n ≠ Nat.card F ^ i)
    (h2 : n ≠ Nat.card F ^ (i + 1)) :
    ((carlitzSubst F) ^ (Nat.card F ^ i)).coeff n = 0 := by
  rw [coeff_carlitzSubst_pow, if_neg h1, if_neg h2, add_zero]

lemma card_pow_injective {a b : ℕ} (h : Nat.card F ^ a = Nat.card F ^ b) : a = b :=
  Nat.pow_right_injective (carlitz_card_ge_two F) h

lemma carlitzSubst_pow_coeff_ne_zero {i n : ℕ}
    (h : ((carlitzSubst F) ^ (Nat.card F ^ i)).coeff n ≠ 0) :
    n = Nat.card F ^ i ∨ n = Nat.card F ^ (i + 1) := by
  by_contra hc
  push_neg at hc
  exact h (carlitzSubst_pow_coeff_eq_zero F hc.1 hc.2)

/-- Substituting `θ z + z ^ q` into a series whose coefficients are supported on the `q`-powers. -/
lemma coeff_subst_sparse {l : ℕ → RatFunc F}
    (hl : ∀ n, (∀ i, n ≠ Nat.card F ^ i) → l n = 0) (N : ℕ) :
    PowerSeries.coeff (Nat.card F ^ N) ((PowerSeries.mk l).subst (carlitzSubst F))
      = l (Nat.card F ^ N) * (carlitzTheta F) ^ (Nat.card F ^ N)
        + (if N = 0 then 0 else l (Nat.card F ^ (N - 1))) := by
  have ha := hasSubst_carlitzSubst F
  rw [PowerSeries.coeff_subst' ha]
  simp only [PowerSeries.coeff_mk, smul_eq_mul]
  have hsupp : Function.support (fun d => l d * ((carlitzSubst F) ^ d).coeff (Nat.card F ^ N))
      ⊆ ↑((Finset.range (N + 1)).image (fun i => Nat.card F ^ i)) := by
    intro d hd
    rw [Function.mem_support] at hd
    obtain ⟨hl0, hc0⟩ := mul_ne_zero_iff.mp hd
    have hd' : ∃ i, d = Nat.card F ^ i := by
      by_contra h
      exact hl0 (hl d (fun i hi => h ⟨i, hi⟩))
    obtain ⟨i, rfl⟩ := hd'
    rw [Finset.mem_coe, Finset.mem_image]
    refine ⟨i, ?_, rfl⟩
    rw [Finset.mem_range]
    by_contra hle
    rw [not_lt] at hle
    rw [carlitzSubst_pow_coeff_eq_zero F
        (fun hc => absurd (card_pow_injective F hc) (by omega))
        (fun hc => absurd (card_pow_injective F hc) (by omega))] at hc0
    exact hc0 rfl
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [Finset.sum_image (fun x _ y _ hxy => Nat.pow_right_injective (carlitz_card_ge_two F) hxy)]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rw [Finset.sum_range_one, coeff_carlitzSubst_pow]
    have hq : Nat.card F ^ 0 ≠ Nat.card F ^ (0 + 1) :=
      fun h => absurd (card_pow_injective F h) (by omega)
    rw [if_pos rfl, if_neg hq, add_zero, if_pos rfl, add_zero]
  · have hsub : ({N, N - 1} : Finset ℕ) ⊆ Finset.range (N + 1) := by
      intro x hx
      rw [Finset.mem_range]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h <;> omega
    have hzero : ∀ x ∈ Finset.range (N + 1), x ∉ ({N, N - 1} : Finset ℕ) →
        (l (Nat.card F ^ x) * ((carlitzSubst F) ^ (Nat.card F ^ x)).coeff (Nat.card F ^ N)) = 0 := by
      intro x hx hx'
      rw [coeff_carlitzSubst_pow,
        if_neg (fun h => hx' (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          left
          have h1 : N = x := card_pow_injective F h
          omega)),
        if_neg (fun h => hx' (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          right
          have h1 : N = x + 1 := card_pow_injective F h
          omega)),
        add_zero, mul_zero]
    rw [if_neg (Nat.pos_iff_ne_zero.mp hN), ← Finset.sum_subset hsub hzero]
    rw [Finset.sum_pair (by omega)]
    have hN1 : Nat.card F ^ N ≠ Nat.card F ^ (N + 1) :=
      fun h => absurd (card_pow_injective F h) (by omega)
    have hNm : Nat.card F ^ N ≠ Nat.card F ^ (N - 1) :=
      fun h => absurd (card_pow_injective F h) (by omega)
    rw [coeff_carlitzSubst_pow, coeff_carlitzSubst_pow, show N - 1 + 1 = N from by omega]
    rw [if_pos rfl, if_neg hN1, if_neg hNm, if_pos rfl]
    ring


lemma carlitzLCoeff_one : carlitzLCoeff F 1 = 1 := by
  have h := carlitzLog_coeff_one F
  rwa [carlitzLog_coeff] at h

lemma carlitzExp_coeff_one : (carlitzExp F).coeff 1 = 1 := by
  rw [carlitzExp, PowerSeries.coeff_mk,
    show (1 : ℕ) = Nat.card F ^ 0 from (pow_zero (Nat.card F)).symm, carlitzECoeff_pow F 0,
    carlitzFact_zero]
  rw [show ((1 : F[X]) : RatFunc F) = 1 from by
      show (algebraMap F[X] (RatFunc F)) 1 = 1
      rw [map_one]]
  simp

lemma carlitzTheta_pow_eq_iff {n : ℕ} : (carlitzTheta F) ^ n = carlitzTheta F ↔ n = 1 := by
  constructor
  · intro h
    have h' : ((X ^ n : F[X]) : RatFunc F) = ((X : F[X]) : RatFunc F) := by
      show (algebraMap F[X] (RatFunc F)) (X ^ n) = (algebraMap F[X] (RatFunc F)) X
      rw [map_pow]
      exact h
    have h2 : (X ^ n : F[X]) = X := RatFunc.algebraMap_injective F h'
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [pow_zero] at h2
      have h3 := congrArg (fun p : F[X] => p.natDegree) h2
      rw [Polynomial.natDegree_one, Polynomial.natDegree_X] at h3
      exact absurd h3 (by norm_num)
    · have h3 := congrArg (fun p : F[X] => p.natDegree) h2
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] at h3
      omega
  · intro h
    subst h
    rw [pow_one]



lemma hasSubst_carlitzExp : PowerSeries.HasSubst (carlitzExp F) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by
    rw [carlitzExp, PowerSeries.constantCoeff_mk,
      carlitzECoeff_eq_zero F (fun i h => by
        have h1 : 0 < Nat.card F ^ i := pow_pos (by have := carlitz_card_ge_two F; omega) i
        omega)])

lemma hasSubst_C_mul_X :
    PowerSeries.HasSubst (PowerSeries.C (carlitzTheta F) * (PowerSeries.X : PowerSeries (RatFunc F))) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by
    rw [map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, mul_zero])

lemma subst_C_mul_X_eq_rescale (f : PowerSeries (RatFunc F)) (r : RatFunc F) :
    f.subst (PowerSeries.C r * (PowerSeries.X : PowerSeries (RatFunc F))) = PowerSeries.rescale r f := by
  rw [show PowerSeries.C r * (PowerSeries.X : PowerSeries (RatFunc F)) = r • PowerSeries.X from by
    rw [Algebra.smul_def]; congr 1,
    ← PowerSeries.rescale_eq_subst]

lemma carlitzSubst_subst {g : PowerSeries (RatFunc F)} (hg : PowerSeries.HasSubst g) :
    (carlitzSubst F).subst g = PowerSeries.C (carlitzTheta F) * g + g ^ (Nat.card F) := by
  rw [carlitzSubst, PowerSeries.subst_add hg, PowerSeries.subst_mul hg, PowerSeries.subst_C,
    PowerSeries.subst_X hg, PowerSeries.subst_pow hg, PowerSeries.subst_X hg]
  rfl

lemma coeff_subst_sparse_of_not_pow {l : ℕ → RatFunc F}
    (hl : ∀ n, (∀ i, n ≠ Nat.card F ^ i) → l n = 0) {n : ℕ}
    (hn : ∀ i, n ≠ Nat.card F ^ i) :
    PowerSeries.coeff n ((PowerSeries.mk l).subst (carlitzSubst F)) = 0 := by
  have ha := hasSubst_carlitzSubst F
  rw [PowerSeries.coeff_subst' ha, finsum_eq_zero_of_forall_eq_zero]
  intro d
  simp only [PowerSeries.coeff_mk, smul_eq_mul]
  by_cases hd : ∃ i, d = Nat.card F ^ i
  · obtain ⟨i, rfl⟩ := hd
    rw [carlitzSubst_pow_coeff_eq_zero F (fun h => hn i h) (fun h => hn (i + 1) h), mul_zero]
  · rw [hl d (fun i hi => hd ⟨i, hi⟩), zero_mul]

lemma carlitzL_coe_zero : ((carlitzL F 0 : F[X]) : RatFunc F) = 1 := by
  rw [carlitzL_zero]
  show (algebraMap F[X] (RatFunc F)) 1 = 1
  rw [map_one]

/-- **The functional equation of the Carlitz logarithm**:
`log_C(θ z + z ^ q) = θ · log_C(z)`. -/
theorem carlitzLog_functional :
    (carlitzLog F).subst (carlitzSubst F) = PowerSeries.C (carlitzTheta F) * carlitzLog F := by
  ext n
  rw [PowerSeries.coeff_C_mul]
  by_cases hn : ∃ N, n = Nat.card F ^ N
  · obtain ⟨N, rfl⟩ := hn
    conv_lhs => rw [show carlitzLog F = PowerSeries.mk (carlitzLCoeff F) from rfl]
    rw [coeff_subst_sparse F (l := carlitzLCoeff F) (fun n hn => carlitzLCoeff_eq_zero F hn) N]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      rw [if_pos rfl, add_zero, pow_zero, carlitzLCoeff_one F, one_mul, pow_one,
        carlitzLog_coeff_one F, mul_one]
    · rw [if_neg (Nat.pos_iff_ne_zero.mp hN), carlitzLCoeff_pow F N, carlitzLCoeff_pow F (N - 1),
        carlitzLog_coeff_pow F N]
      have hrec := carlitzLog_coeff_rec F (N - 1)
      rw [show Nat.card F ^ (N - 1 + 1) = Nat.card F ^ N from by
        rw [show N - 1 + 1 = N from by omega], carlitzLog_coeff_pow, carlitzLog_coeff_pow] at hrec
      rw [← hrec]
      ring
  · conv_lhs => rw [show carlitzLog F = PowerSeries.mk (carlitzLCoeff F) from rfl]
    rw [coeff_subst_sparse_of_not_pow F (l := carlitzLCoeff F)
        (fun n hn => carlitzLCoeff_eq_zero F hn) (fun i h => hn ⟨i, h⟩),
      carlitzLog_coeff_eq_zero F (fun i h => hn ⟨i, h⟩), mul_zero]

/-- ★ **The Carlitz logarithm inverts the Carlitz exponential**: `log_C(e_C(z)) = z`. -/
theorem carlitzLog_subst_exp : (carlitzLog F).subst (carlitzExp F) = PowerSeries.X := by
  let W : PowerSeries (RatFunc F) := PowerSeries.subst (carlitzExp F) (carlitzLog F)
  change W = PowerSeries.X
  have hW : W.subst (PowerSeries.C (carlitzTheta F) * (PowerSeries.X : PowerSeries (RatFunc F)))
      = PowerSeries.C (carlitzTheta F) * W := by
    dsimp only [W]
    rw [PowerSeries.subst_comp_subst_apply (a := carlitzExp F) (b := PowerSeries.C (carlitzTheta F)
        * (PowerSeries.X : PowerSeries (RatFunc F))) (f := carlitzLog F)
        (hasSubst_carlitzExp F) (hasSubst_C_mul_X F)]
    rw [subst_C_mul_X_eq_rescale, carlitzExp_functional]
    rw [← carlitzSubst_subst F (hasSubst_carlitzExp F)]
    rw [← PowerSeries.subst_comp_subst_apply (a := carlitzSubst F) (b := carlitzExp F)
      (f := carlitzLog F) (hasSubst_carlitzSubst F) (hasSubst_carlitzExp F)]
    rw [carlitzLog_functional, PowerSeries.subst_mul (hasSubst_carlitzExp F), PowerSeries.subst_C]
    rfl
  have hcoeff : ∀ n : ℕ, (carlitzTheta F) ^ n * W.coeff n = (carlitzTheta F) * W.coeff n := by
    intro n
    have h := congrArg (fun z : PowerSeries (RatFunc F) => PowerSeries.coeff n z) hW
    rw [subst_C_mul_X_eq_rescale, PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul] at h
    exact h
  have hzero : ∀ n : ℕ, n ≠ 1 → W.coeff n = 0 := by
    intro n hn
    have h := hcoeff n
    have h2 : ((carlitzTheta F) ^ n - carlitzTheta F) * W.coeff n = 0 := by
      rw [sub_mul, h, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd ((carlitzTheta_pow_eq_iff F).mp (sub_eq_zero.mp h3)) hn
    · exact h3
  have hone : W.coeff 1 = 1 := by
    dsimp only [W]
    rw [PowerSeries.coeff_subst' (hasSubst_carlitzExp F), finsum_eq_single _ 1]
    · simp only [smul_eq_mul, carlitzLog_coeff, carlitzLCoeff_one F, one_mul, pow_one,
        carlitzExp_coeff_one F, mul_one]
    · intro d hd
      simp only [smul_eq_mul]
      by_cases hd0 : d = 0
      · subst hd0
        rw [carlitzLog_coeff_zero, zero_mul]
      · have hd2 : 2 ≤ d := by omega
        rw [PowerSeries.coeff_of_lt_order 1 (lt_of_lt_of_le (by exact_mod_cast hd2)
          (PowerSeries.le_order_pow_of_constantCoeff_eq_zero d (by
            rw [carlitzExp, PowerSeries.constantCoeff_mk,
              carlitzECoeff_eq_zero F (fun i h => by
                have h1 : 0 < Nat.card F ^ i := pow_pos (by have := carlitz_card_ge_two F; omega) i
                omega)]))), mul_zero]
  ext n
  rw [PowerSeries.coeff_X]
  by_cases hn : n = 1
  · subst hn
    rw [hone, if_pos rfl]
  · rw [hzero n hn, if_neg hn]

end Subst

end ZagierHoffmanPositiveChar
