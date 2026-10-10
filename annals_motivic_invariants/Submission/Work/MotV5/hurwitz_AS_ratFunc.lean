import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Deriv.deriv_aeval
import Submission.Work.Genus.Deriv.deriv_add
import Submission.Work.Genus.Deriv.deriv_algebraMap
import Submission.Work.Genus.Deriv.deriv_mul
import Submission.Work.Genus.CharP.DescentBasic
import Submission.Work.Genus.CharP.size_lt_of_pow_eq
import Submission.Work.Genus.CharP.exists_pow_eq_of_deriv_eq_zero
import Submission.Work.Genus.Order.ord_aeval_of_neg
import Submission.Work.Genus.Order.ord_deriv_ge
import Submission.Work.Genus.Order.ord_deriv_nonneg
import Submission.Work.Genus.Order.ord_mul
import Submission.Work.Genus.Order.ord_pow
import Submission.Work.Genus.Order.ord_add_eq_of_lt
import Submission.Work.Genus.Order.ord_C_mul
import Submission.Work.Genus.Order.ord_div
import Submission.Work.Genus.Order.ord_sum_gt
import Submission.Work.Genus.Order.min_ord_le_ord_add
import Submission.Work.Genus.Order.exists_algebraMap_eq_of_ord_nonneg
import Submission.Work.Genus.OrderInf.ordInf_aeval_of_neg
import Submission.Work.Genus.OrderInf.ordInf_deriv_ge
import Submission.Work.Genus.OrderInf.two_le_ordInf_deriv
import Submission.Work.Genus.OrderInf.ordInf_add_eq_of_lt
import Submission.Work.Genus.OrderInf.min_ordInf_le_ordInf_add
import Submission.Work.Genus.OrderInf.ordInf_mul
import Submission.Work.Genus.OrderInf.ordInf_pow
import Submission.Work.Genus.OrderInf.ordInf_div
import Submission.Work.Genus.OrderInf.ordInf_polynomial
import Submission.Work.Genus.OrderInf.ordInf_C_mul
import Submission.Work.Genus.Main.exists_ord_neg_or_ordInf_neg
import Submission.Work.Genus.Main.exists_algebraMap_eq_of_natDegree_eq_zero
import Submission.Work.MotV5.valuation_ordInf
import Submission.Work.MotV5.valuation_ord
import Submission.Work.MotV5.exists_fifthRootPoly
import Submission.Work.MotV5.two_le_ordInf_deriv_of_pole

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial

namespace Work.MotV5

/-! ## The finite-place derivative bound

(The place-at-infinity analogue is the imported `Work.MotV5.two_le_ordInf_deriv_of_pole`;
the finite-place version is proved here, where it is needed, from the order theory of
`Submission.Work.Genus`.) -/

/-- The non-archimedean triangle inequality at a finite place, in lower-bound form: if a
non-positive integer `c` bounds the orders of `f` and `g`, it bounds the order of `f + g`. -/
private lemma le_ord_add_of_nonpos {M : Type*} [Field M] {π : Polynomial M} (hπ : Irreducible π)
    {f g : RatFunc M} {c : ℤ} (hc : c ≤ 0) (hf : c ≤ Work.Genus.ord π f)
    (hg : c ≤ Work.Genus.ord π g) : c ≤ Work.Genus.ord π (f + g) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_add]; exact hg
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [add_zero]; exact hf
  rcases eq_or_ne (f + g) 0 with hfg | hfg
  · rw [hfg, Work.Genus.Order.ord_zero]; exact hc
  · exact le_trans (le_min hf hg) (Work.Genus.Order.min_ord_le_ord_add hπ hf0 hg0 hfg)

/-- The order of vanishing at a finite place is unchanged by negation. -/
private lemma ord_neg_eq {M : Type*} [Field M] {π : Polynomial M} (f : RatFunc M) :
    Work.Genus.ord π (-f) = Work.Genus.ord π f := by
  have hh := Work.Genus.Order.ord_C_mul (π := π) (c := (-1 : M)) (by norm_num) f
  rw [map_neg, map_one, neg_one_mul] at hh
  exact hh

/-- The formal derivative kills `0`. -/
private lemma deriv_zero_eq {M : Type*} [Field M] : Work.Genus.deriv (0 : RatFunc M) = 0 := by
  simp [Work.Genus.deriv]

/-- A function regular at `π` has a regular fifth power. -/
private lemma ord_pow_five_nonneg {M : Type*} [Field M] {π : Polynomial M} (hπ : Irreducible π)
    {u : RatFunc M} (hu : 0 ≤ Work.Genus.ord π u) : 0 ≤ Work.Genus.ord π (u ^ 5) := by
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [zero_pow (by norm_num : 5 ≠ 0), Work.Genus.Order.ord_zero]
  · rw [Work.Genus.Order.ord_pow hπ hu0 5]; nlinarith

/-- At a pole of order `k`, `u ^ 5` dominates `u`. -/
private lemma ord_pow_five_sub_self_of_neg {M : Type*} [Field M] {π : Polynomial M}
    (hπ : Irreducible π) {u : RatFunc M} (hu : Work.Genus.ord π u < 0) :
    Work.Genus.ord π (u ^ 5 - u) = 5 * Work.Genus.ord π u := by
  have hu0 : u ≠ 0 := by
    intro h0; rw [h0, Work.Genus.Order.ord_zero] at hu; exact lt_irrefl 0 hu
  have hp : Work.Genus.ord π (u ^ 5) = 5 * Work.Genus.ord π u := by
    rw [Work.Genus.Order.ord_pow hπ hu0 5]; ring
  have hlt : Work.Genus.ord π (u ^ 5) < Work.Genus.ord π (-u) := by
    rw [hp, ord_neg_eq]; linarith
  rw [sub_eq_add_neg, Work.Genus.Order.ord_add_eq_of_lt hπ (pow_ne_zero 5 hu0) hlt, hp]

/-- **The derivative vanishes at a finite pole at which the Artin–Schreier problem is
solvable.**  If `π` is a finite place at which `r` has a pole, `2 ≤ deg A`, `5 ∤ deg A` and
`A(r) - (u⁵ - u)` is regular at `π`, then `deriv r ≠ 0` forces `deriv r` to vanish at `π` with
order at least `2`. -/
private theorem two_le_ord_deriv_of_pole_aux {M : Type*} [Field M] [CharP M 5] {π : Polynomial M}
    (hπ : Irreducible π) {A : Polynomial M} (hA2 : 2 ≤ A.natDegree) (hA5 : ¬ 5 ∣ A.natDegree)
    {r u : RatFunc M} (hr : Work.Genus.ord π r < 0)
    (h : 0 ≤ Work.Genus.ord π (Polynomial.aeval r A - (u ^ 5 - u)))
    (hd : Work.Genus.deriv r ≠ 0) :
    2 ≤ Work.Genus.ord π (Work.Genus.deriv r) := by
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0, Work.Genus.Order.ord_zero] at hr; exact lt_irrefl 0 hr
  have hApos : 0 < A.natDegree := by omega
  have hd2 : (2 : ℤ) ≤ (A.natDegree : ℤ) := by exact_mod_cast hA2
  have h5d : ¬ (5 : ℤ) ∣ (A.natDegree : ℤ) := fun hc => hA5 (Int.natCast_dvd_natCast.mp hc)
  set s : RatFunc M := Polynomial.aeval r A - (u ^ 5 - u) with hs
  have hs' : 0 ≤ Work.Genus.ord π s := h
  have hAord : Work.Genus.ord π (Polynomial.aeval r A)
      = (A.natDegree : ℤ) * Work.Genus.ord π r :=
    Work.Genus.Order.ord_aeval_of_neg hπ hApos hr0 hr
  have hAeval : Polynomial.aeval r A = (u ^ 5 - u) + s := by rw [hs]; ring
  have hc0 : (A.natDegree : ℤ) * Work.Genus.ord π r ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hr.le
  rcases lt_or_ge (Work.Genus.ord π u) 0 with hu | hu
  · -- ## Case 1: `u` also has a pole at `π`
    have hu0 : u ≠ 0 := by
      intro h0; rw [h0, Work.Genus.Order.ord_zero] at hu; exact lt_irrefl 0 hu
    have hu5ord : Work.Genus.ord π (u ^ 5 - u) = 5 * Work.Genus.ord π u :=
      ord_pow_five_sub_self_of_neg hπ hu
    -- the ramification equation `deg A * ord π r = 5 * ord π u`
    have hkey : (A.natDegree : ℤ) * Work.Genus.ord π r = 5 * Work.Genus.ord π u := by
      refine le_antisymm ?_ ?_
      · have hsplit : u ^ 5 - u = Polynomial.aeval r A + (-s) := by rw [hAeval]; ring
        rw [← hu5ord, hsplit]
        exact le_ord_add_of_nonpos hπ hc0 (le_of_eq hAord.symm)
          (by rw [ord_neg_eq]; exact le_trans hc0 hs')
      · rw [← hAord, hAeval]
        exact le_ord_add_of_nonpos hπ (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hu.le)
          (le_of_eq hu5ord.symm)
          (le_trans (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hu.le) hs')
    -- consequently `5 ∣ ord π r` and `ord π r ≤ -5`
    have h5a : (5 : ℤ) ∣ Work.Genus.ord π r := by
      have hdvd : (5 : ℤ) ∣ (A.natDegree : ℤ) * Work.Genus.ord π r := by
        rw [hkey]; exact ⟨Work.Genus.ord π u, rfl⟩
      rcases (show Prime (5 : ℤ) by norm_num).dvd_mul.mp hdvd with h' | h'
      · exact absurd h' h5d
      · exact h'
    have ha5 : Work.Genus.ord π r ≤ -5 := by
      obtain ⟨k, hk⟩ := h5a
      have hklt : k < 0 := by nlinarith [hk, hr]
      omega
    have hub2 : Work.Genus.ord π u ≤ -2 := by nlinarith [hkey, ha5, hd2]
    -- ## the differentiated relation `A'(r) * r' = -u' + s'`
    have hnd : ((Polynomial.derivative A).natDegree : ℤ) = (A.natDegree : ℤ) - 1 := by
      rw [natDegree_derivative_eq_of_not_dvd hA5]; omega
    have hpos : 0 < (Polynomial.derivative A).natDegree := by
      rw [natDegree_derivative_eq_of_not_dvd hA5]; omega
    have hA'ord : Work.Genus.ord π (Polynomial.aeval r (Polynomial.derivative A))
        = ((Polynomial.derivative A).natDegree : ℤ) * Work.Genus.ord π r :=
      Work.Genus.Order.ord_aeval_of_neg hπ hpos hr0 hr
    have hA'ne : Polynomial.aeval r (Polynomial.derivative A) ≠ 0 := by
      intro h0
      rw [h0, Work.Genus.Order.ord_zero] at hA'ord
      have hneg : ((Polynomial.derivative A).natDegree : ℤ) * Work.Genus.ord π r < 0 :=
        mul_neg_of_pos_of_neg (by exact_mod_cast hpos) hr
      omega
    have hder : Polynomial.aeval r (Polynomial.derivative A) * Work.Genus.deriv r
        = - Work.Genus.deriv u + Work.Genus.deriv s := by
      conv_lhs => rw [← Work.Genus.Deriv.deriv_aeval (A := A) (x := r)]
      rw [hAeval, Work.Genus.Deriv.deriv_add, deriv_pow_five_sub_self]
    -- the right-hand side has order at least `ord π u - 1`
    have hrhs : Work.Genus.ord π u - 1
        ≤ Work.Genus.ord π (- Work.Genus.deriv u + Work.Genus.deriv s) := by
      refine le_ord_add_of_nonpos hπ (by linarith) ?_ ?_
      · rw [ord_neg_eq]
        rcases eq_or_ne (Work.Genus.deriv u) 0 with h0 | h0
        · rw [h0, Work.Genus.Order.ord_zero]; linarith
        · exact Work.Genus.Order.ord_deriv_ge hπ hu0 h0
      · rcases eq_or_ne (Work.Genus.deriv s) 0 with h0 | h0
        · rw [h0, Work.Genus.Order.ord_zero]; linarith
        · have hs0 : s ≠ 0 := fun hz => h0 (by rw [hz, deriv_zero_eq])
          have := Work.Genus.Order.ord_deriv_nonneg hπ hs0 h0 hs'; linarith
    have hX : Work.Genus.ord π u - 1
        - ((Polynomial.derivative A).natDegree : ℤ) * Work.Genus.ord π r
        ≤ Work.Genus.ord π (Work.Genus.deriv r) := by
      have h1 : Work.Genus.ord π u - 1
          ≤ ((Polynomial.derivative A).natDegree : ℤ) * Work.Genus.ord π r
            + Work.Genus.ord π (Work.Genus.deriv r) := by
        rw [← hA'ord, ← Work.Genus.Order.ord_mul hπ hA'ne hd, hder]
        exact hrhs
      linarith
    rw [hnd] at hX
    nlinarith [hkey, ha5, hd2, hX]
  · -- ## Case 2: `u` has no pole at `π` — impossible
    exfalso
    have hu5 : 0 ≤ Work.Genus.ord π (u ^ 5 - u) := by
      rw [sub_eq_add_neg]
      exact le_ord_add_of_nonpos hπ le_rfl (ord_pow_five_nonneg hπ hu)
        (by rw [ord_neg_eq]; exact hu)
    have h0 : 0 ≤ Work.Genus.ord π (Polynomial.aeval r A) := by
      rw [hAeval]
      exact le_ord_add_of_nonpos hπ le_rfl hu5 hs'
    rw [hAord] at h0
    have hneg : (A.natDegree : ℤ) * Work.Genus.ord π r < 0 :=
      mul_neg_of_pos_of_neg (by exact_mod_cast hApos) hr
    omega

/-! ## Elementary helper lemmas -/

/-- The image of `c : M` in `M(t)` is the constant polynomial `C c` viewed in the fraction field. -/
private lemma algebraMap_const_eq {M : Type*} [Field M] (c : M) :
    algebraMap M (RatFunc M) c = algebraMap (Polynomial M) (RatFunc M) (Polynomial.C c) := by
  rw [Polynomial.C_eq_algebraMap c,
    IsScalarTower.algebraMap_apply M (Polynomial M) (RatFunc M) c]

/-- A constant is a unit at every finite place. -/
private lemma ord_algebraMap_eq_zero {M : Type*} [Field M] {π : Polynomial M} (c : M) :
    Work.Genus.ord π (algebraMap M (RatFunc M) c) = 0 := by
  by_cases hc : c = 0
  · subst hc
    rw [map_zero, Work.Genus.Order.ord_zero]
  · have h1 : Work.Genus.ord π (1 : RatFunc M) = 0 := by
      simp [Work.Genus.ord, RatFunc.num_one, RatFunc.denom_one]
    rw [← mul_one (algebraMap M (RatFunc M) c),
      Work.Genus.Order.ord_C_mul hc (1 : RatFunc M), h1]

/-- A constant is a unit at the place at infinity. -/
private lemma ordInf_algebraMap_eq_zero {M : Type*} [Field M] (c : M) :
    Work.Genus.ordInf (algebraMap M (RatFunc M) c) = 0 := by
  rw [algebraMap_const_eq, Work.Genus.OrderInf.ordInf_polynomial, Polynomial.natDegree_C]
  simp

/-- A rational function of `Size` zero is a constant. -/
private lemma size_eq_zero_imp_const {M : Type*} [Field M] {z : RatFunc M}
    (h : Work.Genus.CharP.Size z = 0) : ∃ c : M, z = algebraMap M (RatFunc M) c := by
  have h1 : z.num.natDegree = 0 := by
    have h' := h
    simp only [Work.Genus.CharP.Size] at h'
    omega
  have h2 : z.denom.natDegree = 0 := by
    have h' := h
    simp only [Work.Genus.CharP.Size] at h'
    omega
  exact Work.Genus.Main.exists_algebraMap_eq_of_natDegree_eq_zero h1 h2

/-- A rational function with no poles anywhere is a constant. -/
private lemma exists_const_of_no_pole {M : Type*} [Field M] {z : RatFunc M}
    (hfin : ∀ π : Polynomial M, Irreducible π → 0 ≤ Work.Genus.ord π z)
    (hinf : 0 ≤ Work.Genus.ordInf z) :
    ∃ c : M, z = algebraMap M (RatFunc M) c := by
  obtain ⟨p, hp⟩ := Work.Genus.Order.exists_algebraMap_eq_of_ord_nonneg hfin
  have hdeg : p.natDegree = 0 := by
    have h2 : 0 ≤ Work.Genus.ordInf (algebraMap (Polynomial M) (RatFunc M) p) := by
      rw [← hp]; exact hinf
    rw [Work.Genus.OrderInf.ordInf_polynomial] at h2
    omega
  refine ⟨p.coeff 0, ?_⟩
  rw [hp]
  conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
  exact (algebraMap_const_eq (M := M) (p.coeff 0)).symm

/-! ## The local Artin–Schreier solvability predicate -/

/-- `HasLocalSol A r` says that at every pole of `r` (finite place or infinity) the value `A(r)`
is congruent modulo the valuation ring to an Artin–Schreier value `u ^ 5 - u`. -/
def HasLocalSol {M : Type*} [Field M] (A : Polynomial M) (r : RatFunc M) : Prop :=
  (∀ π : Polynomial M, Irreducible π → Work.Genus.ord π r < 0 →
      ∃ u : RatFunc M, 0 ≤ Work.Genus.ord π (Polynomial.aeval r A - (u ^ 5 - u))) ∧
  (Work.Genus.ordInf r < 0 →
      ∃ u : RatFunc M, 0 ≤ Work.Genus.ordInf (Polynomial.aeval r A - (u ^ 5 - u)))

/-! ## The Frobenius descent of the local condition -/

/-- If `r = ρ ^ 5` and `A₀` is the coefficientwise fifth root of `A`
(`(aeval x A₀) ^ 5 = aeval (x ^ 5) A`), then the local condition for `(A, r)` descends to `(A₀, ρ)`:
from `A(r) - (u ^ 5 - u) = R₀` one gets `A₀(ρ) - (w ^ 5 - w) = R₀` with `w = u - A₀(ρ)`. -/
private lemma descent_ord {M : Type*} [Field M] [CharP M 5] {A A₀ : Polynomial M}
    {r ρ : RatFunc M} (hρ : r = ρ ^ 5)
    (hA : ∀ x : RatFunc M, (Polynomial.aeval x A₀) ^ 5 = Polynomial.aeval (x ^ 5) A)
    {π : Polynomial M} {u : RatFunc M}
    (h : 0 ≤ Work.Genus.ord π (Polynomial.aeval r A - (u ^ 5 - u))) :
    ∃ w : RatFunc M, 0 ≤ Work.Genus.ord π (Polynomial.aeval ρ A₀ - (w ^ 5 - w)) := by
  refine ⟨u - Polynomial.aeval ρ A₀, ?_⟩
  have hpow : (Polynomial.aeval ρ A₀) ^ 5 = Polynomial.aeval r A := by
    rw [hA ρ, hρ]
  have hsub : (u - Polynomial.aeval ρ A₀) ^ 5
      = u ^ 5 - (Polynomial.aeval ρ A₀) ^ 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact sub_pow_char_of_commute 5 (Commute.all u _)
  have key : Polynomial.aeval ρ A₀
      - ((u - Polynomial.aeval ρ A₀) ^ 5 - (u - Polynomial.aeval ρ A₀))
      = Polynomial.aeval r A - (u ^ 5 - u) := by
    rw [hsub, hpow]; ring
  rw [key]; exact h

/-- The place-at-infinity version of `descent_ord`. -/
private lemma descent_ordInf {M : Type*} [Field M] [CharP M 5] {A A₀ : Polynomial M}
    {r ρ : RatFunc M} (hρ : r = ρ ^ 5)
    (hA : ∀ x : RatFunc M, (Polynomial.aeval x A₀) ^ 5 = Polynomial.aeval (x ^ 5) A)
    {u : RatFunc M}
    (h : 0 ≤ Work.Genus.ordInf (Polynomial.aeval r A - (u ^ 5 - u))) :
    ∃ w : RatFunc M, 0 ≤ Work.Genus.ordInf (Polynomial.aeval ρ A₀ - (w ^ 5 - w)) := by
  refine ⟨u - Polynomial.aeval ρ A₀, ?_⟩
  have hpow : (Polynomial.aeval ρ A₀) ^ 5 = Polynomial.aeval r A := by
    rw [hA ρ, hρ]
  have hsub : (u - Polynomial.aeval ρ A₀) ^ 5
      = u ^ 5 - (Polynomial.aeval ρ A₀) ^ 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact sub_pow_char_of_commute 5 (Commute.all u _)
  have key : Polynomial.aeval ρ A₀
      - ((u - Polynomial.aeval ρ A₀) ^ 5 - (u - Polynomial.aeval ρ A₀))
      = Polynomial.aeval r A - (u ^ 5 - u) := by
    rw [hsub, hpow]; ring
  rw [key]; exact h

/-! ## The main induction -/

/-- **No non-constant `r` satisfies the local Artin–Schreier condition** (strong induction on
`Size`). -/
private theorem main_aux {M : Type*} [Field M] [IsAlgClosed M] [CharP M 5] (D : ℕ) :
    ∀ (A : Polynomial M) (r : RatFunc M),
      Work.Genus.CharP.Size r ≤ D → 2 ≤ A.natDegree → ¬ 5 ∣ A.natDegree →
      ((∃ π : Polynomial M, Irreducible π ∧ Work.Genus.ord π r < 0) ∨ Work.Genus.ordInf r < 0) →
      ¬ HasLocalSol A r := by
  induction D using Nat.strong_induction_on with
  | h D ih =>
    intro A r hD hA2 hA5 hp hsol
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hrnz : r ≠ 0 := by
      rcases hp with ⟨π, hπ, hπr⟩ | hinfr
      · intro h0
        rw [h0, Work.Genus.Order.ord_zero] at hπr
        exact lt_irrefl 0 hπr
      · intro h0
        rw [h0] at hinfr
        simp [Work.Genus.ordInf] at hinfr
    -- Step 1: the derivative of `r` vanishes identically.
    have hderiv : Work.Genus.deriv r = 0 := by
      by_contra hd
      have hfin : ∀ π : Polynomial M, Irreducible π →
          0 ≤ Work.Genus.ord π (Work.Genus.deriv r) := by
        intro π hπ
        by_cases hc : Work.Genus.ord π r < 0
        · obtain ⟨u, hu⟩ := hsol.1 π hπ hc
          have := two_le_ord_deriv_of_pole_aux hπ hA2 hA5 hc hu hd
          linarith
        · exact Work.Genus.Order.ord_deriv_nonneg hπ hrnz hd (not_lt.mp hc)
      have hinf : 0 ≤ Work.Genus.ordInf (Work.Genus.deriv r) := by
        by_cases hc : Work.Genus.ordInf r < 0
        · obtain ⟨u, hu⟩ := hsol.2 hc
          have := two_le_ordInf_deriv_of_pole hA2 hA5 hc hu hd
          linarith
        · have h0 : 0 ≤ Work.Genus.ordInf r := not_lt.mp hc
          have := Work.Genus.OrderInf.ordInf_deriv_ge hrnz hd
          linarith
      obtain ⟨c, hc⟩ := exists_const_of_no_pole hfin hinf
      rcases hp with ⟨π, hπ, hπr⟩ | hinfr
      · obtain ⟨u, hu⟩ := hsol.1 π hπ hπr
        have h2 := two_le_ord_deriv_of_pole_aux hπ hA2 hA5 hπr hu hd
        rw [hc, ord_algebraMap_eq_zero] at h2
        omega
      · obtain ⟨u, hu⟩ := hsol.2 hinfr
        have h2 := two_le_ordInf_deriv_of_pole hA2 hA5 hinfr hu hd
        rw [hc, ordInf_algebraMap_eq_zero] at h2
        omega
    -- Step 2: `r` is a fifth power.
    obtain ⟨ρ, hρ⟩ := Work.Genus.CharP.exists_pow_eq_of_deriv_eq_zero (p := 5) hderiv
    have hρnz : ρ ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by norm_num : 5 ≠ 0)] at hρ
      exact hrnz hρ
    -- Step 3: the descent decreases the `Size`.
    have hsize0 : 0 < Work.Genus.CharP.Size r := by
      by_contra h
      have h0 : Work.Genus.CharP.Size r = 0 := Nat.eq_zero_of_not_pos h
      obtain ⟨c, hc⟩ := size_eq_zero_imp_const h0
      rcases hp with ⟨π, hπ, hπr⟩ | hinfr
      · rw [hc, ord_algebraMap_eq_zero] at hπr
        exact lt_irrefl 0 hπr
      · rw [hc, ordInf_algebraMap_eq_zero] at hinfr
        exact lt_irrefl 0 hinfr
    have hsize : Work.Genus.CharP.Size ρ < Work.Genus.CharP.Size r :=
      Work.Genus.CharP.size_lt_of_pow_eq hρ hsize0
    obtain ⟨A₀, hA₀deg, hA₀val⟩ := exists_fifthRootPoly A
    have hA₀2 : 2 ≤ A₀.natDegree := by rw [hA₀deg]; exact hA2
    have hA₀5 : ¬ 5 ∣ A₀.natDegree := by rw [hA₀deg]; exact hA5
    -- poles of `ρ` are the poles of `r`
    have hpρ : (∃ π : Polynomial M, Irreducible π ∧ Work.Genus.ord π ρ < 0) ∨
        Work.Genus.ordInf ρ < 0 := by
      rcases hp with ⟨π, hπ, hπr⟩ | hinfr
      · refine Or.inl ⟨π, hπ, ?_⟩
        have h5 : Work.Genus.ord π r = 5 * Work.Genus.ord π ρ := by
          rw [hρ]; exact Work.Genus.Order.ord_pow hπ hρnz 5
        nlinarith [h5, hπr]
      · refine Or.inr ?_
        have h5 : Work.Genus.ordInf r = 5 * Work.Genus.ordInf ρ := by
          rw [hρ]; exact Work.Genus.OrderInf.ordInf_pow hρnz 5
        nlinarith [h5, hinfr]
    have hsolρ : HasLocalSol A₀ ρ := by
      constructor
      · intro π hπ hπρ
        have h5 : Work.Genus.ord π r = 5 * Work.Genus.ord π ρ := by
          rw [hρ]; exact Work.Genus.Order.ord_pow hπ hρnz 5
        have hπr : Work.Genus.ord π r < 0 := by nlinarith [h5, hπρ]
        obtain ⟨u, hu⟩ := hsol.1 π hπ hπr
        exact descent_ord hρ hA₀val hu
      · intro hπρ
        have h5 : Work.Genus.ordInf r = 5 * Work.Genus.ordInf ρ := by
          rw [hρ]; exact Work.Genus.OrderInf.ordInf_pow hρnz 5
        have hπr : Work.Genus.ordInf r < 0 := by nlinarith [h5, hπρ]
        obtain ⟨u, hu⟩ := hsol.2 hπr
        exact descent_ordInf hρ hA₀val hu
    exact ih (Work.Genus.CharP.Size ρ) (by omega) A₀ ρ le_rfl hA₀2 hA₀5 hpρ hsolρ

/-! ## The theorem -/

theorem hurwitz_AS_ratFunc {M : Type*} [Field M] [IsAlgClosed M] [CharP M 5]
    (f : Polynomial M) (hf2 : 2 ≤ f.natDegree) (hf5 : ¬ 5 ∣ f.natDegree) (r : RatFunc M)
    (hr : ∀ v : Valuation (RatFunc M) (WithZero (Multiplicative ℤ)), Work.MotV.TrivOn M v → 1 < v r →
      ∃ u, v (Polynomial.aeval r f - (u ^ 5 - u)) ≤ 1) :
    ∃ c : M, algebraMap M _ c = r := by
  -- the local Artin-Schreier condition holds at every pole
  have hsol : HasLocalSol f r := by
    constructor
    · intro π hπ hπr
      obtain ⟨v, htriv, hvle, hvlt⟩ := valuation_ord π hπ
      obtain ⟨u, hu⟩ := hr v htriv ((hvlt r).mpr hπr)
      exact ⟨u, (hvle _).mp hu⟩
    · intro hinfr
      obtain ⟨v, htriv, hvle, hvlt⟩ := valuation_ordInf (M := M)
      obtain ⟨u, hu⟩ := hr v htriv ((hvlt r).mpr hinfr)
      exact ⟨u, (hvle _).mp hu⟩
  by_cases hp : (∃ π : Polynomial M, Irreducible π ∧ Work.Genus.ord π r < 0) ∨
      Work.Genus.ordInf r < 0
  · exact absurd hsol (main_aux (Work.Genus.CharP.Size r) f r le_rfl hf2 hf5 hp)
  · have hfin : ∀ π : Polynomial M, Irreducible π → 0 ≤ Work.Genus.ord π r := by
      intro π hπ
      by_contra h
      exact hp (Or.inl ⟨π, hπ, not_le.mp h⟩)
    have hinf : 0 ≤ Work.Genus.ordInf r := by
      by_contra h
      exact hp (Or.inr (not_le.mp h))
    obtain ⟨c, hc⟩ := exists_const_of_no_pole hfin hinf
    exact ⟨c, hc.symm⟩

end Work.MotV5
