import Mathlib
import Submission.Vdw.PolyIndex
import Submission.Vdw.ResidueIndex
import Submission.Vdw.BoxFourierIndex
import Submission.Vdw.FourierPrime
import Submission.Vdw.MultiPrimeFourier
import Submission.Vdw.DoubleDisc

open Polynomial UniqueFactorizationMonoid
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# Translation invariance of Bhargava's index and the Weil-bound route to `ftgen2`

The §4 Fourier input of the paper (`MIndexBound`, `FourierPrime.lean`) is the
bound `‖Σ_{v ∈ T_{p,k}} stdAddChar (a·v)‖ ≤ C·p^{n-k-1/2}` for the Fourier
transform of the *index-`≥ k` residue set* over `F_p`.

The key new observation formalised here is that `T_{p,k}` is **invariant under
the translation action** `f(X) ↦ f(X + c)` on monic degree-`n` polynomials
(translation permutes the irreducible factors, hence preserves the index), and
that the orbits of this action are exactly the "translate families"
`{f(X + c) : c ∈ F_p}`.  Summing the character over an orbit gives a *complete
exponential sum* `Σ_{c ∈ F_p} stdAddChar (Q(c))` in a polynomial `Q` of degree
`≤ n`, so the classical **Weil bound** for polynomial exponential sums yields
the required square-root cancellation:

    `‖Σ_{v ∈ T} χ(a·v)‖ ≤ (1/p)·|T|·max_v ‖Σ_c χ(a·(transVec c v))‖
                    ≤ (1/p)·|T|·C_W·n·√p ≤ C_W·n·2^{(n+1)^4}·p^{n-k-1/2}`,

using `|T| ≤ 2^{(n+1)^4}·p^{n-k}` (CI-1).  Hence

    `WeilPolyBound n → MIndexBound n`,

where `WeilPolyBound n` is the honest classical statement

    `‖Σ_{c ∈ F_p} stdAddChar (Q(c))‖ ≤ C·deg Q·√p`   (`1 ≤ deg Q ≤ n < p`),

i.e. the Weil bound for exponential sums of non-constant polynomials of degree
`≤ n` over `F_p` (equivalently: the Riemann hypothesis for the Artin–Schreier
curve `y^p - y = Q(x)`).

This replaces the paper's splitting-type analysis: no `w_{p,σ}`, no Möbius
inversion over types, no per-`σ` counting — only the index invariance, the
orbit decomposition and the Weil bound.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. Translation invariance of the index -/

omit [DecidableEq F] in
theorem comp_X_sub_C_comp_X_add_C (c : F) (r : F[X]) :
    (r.comp (X - C c)).comp (X + C c) = r := by
  rw [show (X : F[X]) + C c = X - C (-c) by simp, Polynomial.comp_assoc]; simp

omit [DecidableEq F] in
theorem comp_X_add_C_comp_X_sub_C (c : F) (r : F[X]) :
    (r.comp (X + C c)).comp (X - C c) = r := by
  rw [Polynomial.comp_assoc]; simp

omit [DecidableEq F] in
theorem comp_X_sub_C_ne_zero_iff (c : F) (r : F[X]) : r.comp (X - C c) ≠ 0 ↔ r ≠ 0 := by
  have h : (X : F[X]) - C c = X + C (-c) := by rw [sub_eq_add_neg, ← map_neg]
  rw [h, Polynomial.comp_X_add_C_ne_zero_iff]

omit [DecidableEq F] in
theorem X_add_C_neg (c : F) : (X : F[X]) + C (-c) = X - C c := by
  rw [sub_eq_add_neg, ← map_neg]

omit [DecidableEq F] in
theorem irreducible_comp_X_add_C (c : F) (r : F[X]) :
    Irreducible (r.comp (X + C c)) ↔ Irreducible r := by
  have h : r.comp (X + C c) = (algEquivAevalXAddC c) r := rfl
  rw [h, MulEquiv.irreducible_iff]

omit [DecidableEq F] in
theorem monic_comp_X_add_C (c : F) (r : F[X]) : (r.comp (X + C c)).Monic ↔ r.Monic := by
  rw [Monic.def, Monic.def,
    leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero)]
  simp

omit [DecidableEq F] in
theorem natDegree_comp_X_add_C (c : F) (r : F[X]) :
    (r.comp (X + C c)).natDegree = r.natDegree := by
  rw [natDegree_comp, natDegree_X_add_C, mul_one]

theorem mem_normalizedFactors_comp_X_add_C (c : F) {f r : F[X]} (hf : f ≠ 0) (hr : r ≠ 0) :
    r.comp (X + C c) ∈ normalizedFactors (f.comp (X + C c)) ↔ r ∈ normalizedFactors f := by
  have hfc : f.comp (X + C c) ≠ 0 := Polynomial.comp_X_add_C_ne_zero_iff.mpr hf
  have hrc : r.comp (X + C c) ≠ 0 := Polynomial.comp_X_add_C_ne_zero_iff.mpr hr
  rw [Polynomial.mem_normalizedFactors_iff hfc, Polynomial.mem_normalizedFactors_iff (q := f) hf]
  have hirr := irreducible_comp_X_add_C (F := F) c r
  have hmon := monic_comp_X_add_C (F := F) c r
  have hdvd : r.comp (X + C c) ∣ f.comp (X + C c) ↔ r ∣ f := by
    rw [Polynomial.dvd_comp_X_add_C_iff, comp_X_add_C_comp_X_sub_C]
  rw [hirr, hmon, hdvd]

/-- The product of the distinct monic irreducible factors of `f` commutes with
the translation `X ↦ X + c`. -/
theorem monicRadical_comp_X_add_C (c : F) (f : F[X]) :
    monicRadical (f.comp (X + C c)) = (monicRadical f).comp (X + C c) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp [monicRadical]
  classical
  set s : Finset F[X] := (normalizedFactors f).toFinset with hsdef
  set t : Finset F[X] := (normalizedFactors (f.comp (X + C c))).toFinset with htdef
  have hmem : ∀ r : F[X], r ≠ 0 → (r.comp (X + C c) ∈ t ↔ r ∈ s) := by
    intro r hr
    rw [htdef, hsdef, Multiset.mem_toFinset, Multiset.mem_toFinset]
    exact mem_normalizedFactors_comp_X_add_C c hf hr
  have hne : ∀ q : F[X], q ∈ t → q ≠ 0 := by
    intro q hq
    exact ne_zero_of_mem_normalizedFactors (by rwa [htdef, Multiset.mem_toFinset] at hq)
  have hmem2 : ∀ r : F[X], r ≠ 0 → (r ∈ t ↔ r.comp (X - C c) ∈ s) := by
    intro r hr
    have h1 := hmem (r.comp (X - C c)) ((comp_X_sub_C_ne_zero_iff (F := F) c r).mpr hr)
    rwa [comp_X_sub_C_comp_X_add_C] at h1
  have hrad1 : monicRadical (f.comp (X + C c)) = t.prod id := rfl
  have hrad2 : monicRadical f = s.prod id := rfl
  rw [hrad1, hrad2]
  have hmain : t.prod id = (s.prod (fun p : F[X] => p.comp (X + C c))) := by
    refine Finset.prod_bij (fun q _ => q.comp (X - C c)) ?_ ?_ ?_ ?_
    · intro q hq
      exact (hmem2 q (hne q hq)).mp hq
    · intro q1 hq1 q2 hq2 heq
      have h2 := congrArg (fun z : F[X] => z.comp (X + C c)) heq
      simpa [comp_X_sub_C_comp_X_add_C] using h2
    · intro p hp
      have hp0 : p ≠ 0 :=
        ne_zero_of_mem_normalizedFactors (by rwa [hsdef, Multiset.mem_toFinset] at hp)
      refine ⟨p.comp (X + C c), ?_, comp_X_add_C_comp_X_sub_C c p⟩
      rw [htdef, Multiset.mem_toFinset]
      exact (mem_normalizedFactors_comp_X_add_C c hf hp0).mpr
        (by rwa [hsdef, Multiset.mem_toFinset] at hp)
    · intro q _
      exact (comp_X_sub_C_comp_X_add_C c q).symm
  rw [hmain]
  exact (map_prod (algEquivAevalXAddC c) (fun p : F[X] => p) s).symm

/-- The UFD radical commutes with the translation `X ↦ X + c`. -/
theorem radical_comp_X_add_C (c : F) (f : F[X]) :
    UniqueFactorizationMonoid.radical (f.comp (X + C c)) =
      (UniqueFactorizationMonoid.radical f).comp (X + C c) := by
  rw [← monicRadical_eq_radical, ← monicRadical_eq_radical]
  exact monicRadical_comp_X_add_C c f

/-- **Translation invariance of Bhargava's index**: `ind (f(X+c)) = ind f`. -/
theorem polyIndex_comp_X_add_C (c : F) (f : F[X]) :
    polyIndex (f.comp (X + C c)) = polyIndex f := by
  have hdeg : (f.comp (X + C c)).natDegree = f.natDegree := natDegree_comp_X_add_C c f
  have hraddeg : (UniqueFactorizationMonoid.radical (f.comp (X + C c))).natDegree =
      (UniqueFactorizationMonoid.radical f).natDegree := by
    rw [radical_comp_X_add_C, natDegree_comp, natDegree_X_add_C, mul_one]
  dsimp only [polyIndex]
  rw [hdeg, hraddeg]

/-! ## 2. The translation action on trailing coefficient vectors -/

section Translate

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The trailing-coefficient vector of the translate `f(X + c)` of the monic
degree-`n` polynomial with trailing vector `v`. -/
def transVec (n : ℕ) (c : ZMod p) (v : Fin n → ZMod p) : Fin n → ZMod p :=
  Polynomial.toFn n ((monicOfTrail n v).comp (X + C c))

theorem monicOfTrail_transVec (n : ℕ) (c : ZMod p) (v : Fin n → ZMod p) :
    monicOfTrail n (transVec p n c v) = (monicOfTrail n v).comp (X + C c) := by
  rw [transVec, monicOfTrail_toFn]
  · exact (monic_comp_X_add_C c (monicOfTrail n v)).mpr (monicOfTrail_monic n v)
  · rw [natDegree_comp_X_add_C, monicOfTrail_natDegree]

/-- **The index is invariant under the translation action** on trailing
coefficient vectors. -/
theorem indexClass_transVec (n k : ℕ) (c : ZMod p) (v : Fin n → ZMod p) :
    indexClass (F := ZMod p) n k (transVec p n c v) ↔ indexClass (F := ZMod p) n k v := by
  dsimp only [indexClass]
  rw [monicOfTrail_transVec, polyIndex_comp_X_add_C]

theorem transVec_neg_transVec (n : ℕ) (c : ZMod p) (v : Fin n → ZMod p) :
    transVec p n (-c) (transVec p n c v) = v := by
  have h : monicOfTrail n (transVec p n (-c) (transVec p n c v)) = monicOfTrail n v := by
    rw [monicOfTrail_transVec, monicOfTrail_transVec, X_add_C_neg,
      comp_X_add_C_comp_X_sub_C]
  calc transVec p n (-c) (transVec p n c v)
      = Polynomial.toFn n (monicOfTrail n (transVec p n (-c) (transVec p n c v))) :=
        (toFn_monicOfTrail n _).symm
    _ = Polynomial.toFn n (monicOfTrail n v) := by rw [h]
    _ = v := toFn_monicOfTrail n v

theorem transVec_injective (n : ℕ) (c : ZMod p) :
    Function.Injective (transVec p n c) := by
  intro v w hvw
  have := congrArg (transVec p n (-c)) hvw
  rwa [transVec_neg_transVec, transVec_neg_transVec] at this

/-- **The orbit-sum identity**: for any function `g` on the coefficient space,
the sum of `g` over the index-`≥ k` set is `1/p` times the sum over
translates, because the set is translation invariant. -/
theorem translate_sum_identity (n k : ℕ) (g : (Fin n → ZMod p) → ℂ) :
    (p : ℂ) * ∑ v ∈ indexClassFinset p n k, g v
      = ∑ v ∈ indexClassFinset p n k, ∑ c : ZMod p, g (transVec p n c v) := by
  rw [Finset.sum_comm]
  have hinv : ∀ c : ZMod p, ∑ v ∈ indexClassFinset p n k, g (transVec p n c v)
      = ∑ v ∈ indexClassFinset p n k, g v := by
    intro c
    refine Finset.sum_bij (fun v _ => transVec p n c v) ?_ ?_ ?_ ?_
    · intro v hv
      rw [mem_indexClassFinset] at hv ⊢
      exact (indexClass_transVec p n k c v).mpr hv
    · intro v1 hv1 v2 hv2 heq
      exact transVec_injective p n c heq
    · intro w hw
      rw [mem_indexClassFinset] at hw
      refine ⟨transVec p n (-c) w, ?_, ?_⟩
      · rw [mem_indexClassFinset]
        exact (indexClass_transVec p n k (-c) w).mpr hw
      · simpa using transVec_neg_transVec p n (-c) w
    · intro v _
      rfl
  simp only [hinv]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

end Translate

/-! ## 3. The shift polynomial `c ↦ Σ_i a_i [x^i] f(X + c)` -/

section Shift

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- A prime dividing `N!` is at most `N`. -/
theorem prime_dvd_factorial_le {m N : ℕ} (hm : m.Prime) (h : m ∣ Nat.factorial N) : m ≤ N := by
  induction N with
  | zero =>
    have h1 : m ≤ 1 := Nat.le_of_dvd (by norm_num) (by simpa using h)
    have h2 : 2 ≤ m := hm.two_le
    omega
  | succ N ih =>
    rw [Nat.factorial_succ] at h
    rcases hm.dvd_mul.mp h with h1 | h2
    · have := Nat.le_of_dvd (Nat.succ_pos N) h1; omega
    · have := ih h2; omega

/-- `(n.choose k : ZMod p) ≠ 0` when `n < p`. -/
theorem zmod_choose_ne_zero {n k : ℕ} (hn : n < p) (hk : k ≤ n) :
    ((n.choose k : ℕ) : ZMod p) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff (ZMod p) p] at h
  have hfac : n.choose k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n :=
    Nat.choose_mul_factorial_mul_factorial hk
  have hdvd : p ∣ Nat.factorial n := by
    rw [← hfac]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h (Nat.factorial k)) _
  have hle : p ≤ n := prime_dvd_factorial_le (Fact.out : Nat.Prime p) hdvd
  omega

/-- The polynomial `Q(c) = Σ_i a_i·[x^i] f(X + c)` in the variable `c`. -/
def shiftPoly (n : ℕ) (a : Fin n → ZMod p) (f : (ZMod p)[X]) : (ZMod p)[X] :=
  ∑ i : Fin n, Polynomial.C (a i) * Polynomial.hasseDeriv (i : ℕ) f

theorem shiftPoly_eval (n : ℕ) (a : Fin n → ZMod p) (f : (ZMod p)[X]) (c : ZMod p) :
    (shiftPoly p n a f).eval c = ∑ i : Fin n, a i * (f.comp (X + C c)).coeff i := by
  rw [shiftPoly, ← Polynomial.coe_evalRingHom c, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.coe_evalRingHom c, Polynomial.eval_mul, Polynomial.eval_C,
    ← Polynomial.taylor_apply c f, Polynomial.taylor_coeff]

theorem shiftPoly_natDegree_le (n : ℕ) (a : Fin n → ZMod p) (f : (ZMod p)[X])
    (hdeg : f.natDegree = n) : (shiftPoly p n a f).natDegree ≤ n := by
  rw [shiftPoly]
  refine Polynomial.natDegree_sum_le_of_forall_le (s := Finset.univ) (n := n)
    (f := fun i : Fin n => Polynomial.C (a i) * Polynomial.hasseDeriv (i : ℕ) f) ?_
  intro i _
  refine (Polynomial.natDegree_C_mul_le (a i) _).trans
    ((Polynomial.natDegree_hasseDeriv_le f (i : ℕ)).trans ?_)
  rw [hdeg]
  exact Nat.sub_le n i

theorem shiftPoly_natDegree_pos (n : ℕ) (a : Fin n → ZMod p) (ha : a ≠ 0)
    (f : (ZMod p)[X]) (hf : f.Monic) (hdeg : f.natDegree = n) (hp : n < p) :
    1 ≤ (shiftPoly p n a f).natDegree := by
  classical
  have hex : ∃ i : Fin n, a i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact ha (funext h)
  let S : Finset (Fin n) := Finset.univ.filter (fun i => a i ≠ 0)
  have hS : S.Nonempty :=
    ⟨Classical.choose hex, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Classical.choose_spec hex⟩⟩
  let i0 : Fin n := S.min' hS
  have hi0mem : i0 ∈ S := Finset.min'_mem S hS
  have hi0 : a i0 ≠ 0 := (Finset.mem_filter.mp hi0mem).2
  have hmin : ∀ i : Fin n, a i ≠ 0 → i0 ≤ i := fun i hi =>
    Finset.min'_le S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have hcoeff : (shiftPoly p n a f).coeff (n - (i0 : ℕ)) ≠ 0 := by
    rw [shiftPoly, coeff_finset_sum]
    rw [Finset.sum_eq_single i0]
    · rw [Polynomial.coeff_C_mul, Polynomial.hasseDeriv_coeff, Nat.sub_add_cancel i0.isLt.le]
      have hfn : f.coeff n = 1 := by
        have : f.coeff f.natDegree = 1 := hf
        rwa [hdeg] at this
      rw [hfn, mul_one]
      exact mul_ne_zero hi0 (zmod_choose_ne_zero p hp (Nat.le_of_lt i0.isLt))
    · intro i _ hne
      rw [Polynomial.coeff_C_mul, Polynomial.hasseDeriv_coeff]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hai : a i = 0 := by
          by_contra hc
          exact absurd (hmin i hc) (not_le.mpr hlt)
        rw [hai, zero_mul]
      · have hlt2 : f.natDegree < n - (i0 : ℕ) + i := by rw [hdeg]; omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt2]
        ring
    · intro h
      exact absurd (Finset.mem_univ i0) h
  calc 1 ≤ n - (i0 : ℕ) := by omega
    _ ≤ (shiftPoly p n a f).natDegree := Polynomial.le_natDegree_of_ne_zero hcoeff

end Shift

/-! ## 4. A power-saving exponential-sum bound implies the per-prime index bound

The Fourier input is used only through a *power saving* for complete
exponential sums of polynomial phases over `F_p`.  We therefore state the input
in the general form `ExpSumBound n θ : ‖Σ_{c∈F_p} χ(Q(c))‖ ≤ C·p^{1-θ}` for
non-constant `Q` of degree `≤ n` (`p > n`), and derive the per-prime index
bound with the same saving.  `θ = 1/2` is the Weil bound (`WeilPolyBound`,
which is `ExpSumBound n θ` with the constant normalised by `deg Q·√p`); the
elementary Weyl bound supplies `θ = 2^{-n}` (see the Roadmap Session-152
block for why any `θ > 0` suffices for the whole development, at the price of
a smaller Case-I threshold `δ ≈ θ/n`). -/

/-- **The Weil bound for polynomial exponential sums over `F_p`** (the Riemann
hypothesis for the Artin–Schreier curve `y^p - y = Q(x)`): for `p > n`, the
complete exponential sum of a non-constant polynomial `Q` of degree `≤ n` is
bounded by `C·deg(Q)·√p`. -/
def WeilPolyBound (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℕ) [Fact (Nat.Prime p)], n < p → ∀ Q : (ZMod p)[X],
    1 ≤ Q.natDegree → Q.natDegree ≤ n →
      ‖∑ c : ZMod p, ZMod.stdAddChar (Q.eval c)‖ ≤ C * (Q.natDegree : ℝ) * Real.sqrt p

/-- **Power-saving bound for complete exponential sums of polynomial phases**:
for `p > n`, the sum of `χ(Q(c))` over `F_p` for a non-constant `Q` of degree
`≤ n` is `O(p^{1-θ})`.  The Weil bound is the case `θ = 1/2`; the elementary
Weyl bound gives `θ = 2^{-n}`. -/
def ExpSumBound (n : ℕ) (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℕ) [Fact (Nat.Prime p)], n < p → ∀ Q : (ZMod p)[X],
    1 ≤ Q.natDegree → Q.natDegree ≤ n →
      ‖∑ c : ZMod p, ZMod.stdAddChar (Q.eval c)‖ ≤ C * (p : ℝ) ^ (1 - θ)

/-- The Weil bound is the `θ = 1/2` case of `ExpSumBound`. -/
theorem expSumBound_half_of_weilPolyBound (n : ℕ) (h : WeilPolyBound n) :
    ExpSumBound n (1 / 2) := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C * (n : ℝ), by positivity, ?_⟩
  intro p _inst hpn Q h1 h2
  have hsq : Real.sqrt (p : ℝ) = (p : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow p
  refine (hb p hpn Q h1 h2).trans ?_
  rw [hsq, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC)
    (Real.rpow_nonneg (by positivity) _)
  exact_mod_cast h2

section Assembly

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The orbit-sum identity turns the Fourier coefficient into `1/p` times a sum
of complete exponential sums. -/
theorem norm_indexFourierCoeff_le (n k : ℕ) (a : Fin n → ZMod p) :
    ‖indexFourierCoeff p n k a‖
      ≤ (1 / (p : ℝ)) * ∑ v ∈ indexClassFinset p n k,
          ‖∑ c : ZMod p, ZMod.stdAddChar (∑ i, a i * (transVec p n c v) i)‖ := by
  have hpc : (p : ℂ) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hid := translate_sum_identity p n k
    (fun v : Fin n → ZMod p => ZMod.stdAddChar (∑ i, a i * v i))
  have hI : indexFourierCoeff p n k a
      = ((p : ℂ))⁻¹ * ∑ v ∈ indexClassFinset p n k,
          ∑ c : ZMod p, ZMod.stdAddChar (∑ i, a i * (transVec p n c v) i) := by
    rw [indexFourierCoeff, eq_inv_mul_iff_mul_eq₀ hpc]
    exact hid
  rw [hI, norm_mul]
  have hnp : ‖((p : ℂ))⁻¹‖ = 1 / (p : ℝ) := by
    rw [norm_inv, Complex.norm_natCast, one_div]
  rw [hnp]
  refine mul_le_mul_of_nonneg_left (norm_sum_le _ _) ?_
  positivity

end Assembly

/-- `p^(n-k)·p^{-θ} = p^(n-k-θ)`. -/
theorem rpow_mul_rpow_neg (p n k : ℕ) (hp0 : (0 : ℝ) < p) (hk : k ≤ n) (θ : ℝ) :
    (p : ℝ) ^ (n - k) * (p : ℝ) ^ (-θ) = (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) := by
  rw [← Real.rpow_natCast (p : ℝ) (n - k), ← Real.rpow_add hp0, Nat.cast_sub hk]
  exact congrArg (fun e : ℝ => (p : ℝ) ^ e) (by ring)

/-- `(1/p)·p^{1-θ} = p^{-θ}`. -/
theorem inv_mul_rpow_one_sub (p : ℕ) (hp0 : (0 : ℝ) < p) (θ : ℝ) :
    (1 / (p : ℝ)) * (p : ℝ) ^ (1 - θ) = (p : ℝ) ^ (-θ) := by
  have h1 : (1 / (p : ℝ)) = (p : ℝ) ^ (-1 : ℝ) := by
    rw [one_div, Real.rpow_neg_one]
  rw [h1, ← Real.rpow_add hp0]
  exact congrArg (fun e : ℝ => (p : ℝ) ^ e) (by ring)

/-- `p^(n-k) = p^(n-k-θ)·p^θ`. -/
theorem rpow_split (p n k : ℕ) (hp0 : (0 : ℝ) < p) (hk : k ≤ n) (θ : ℝ) :
    (p : ℝ) ^ (n - k) = (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) * (p : ℝ) ^ θ := by
  rw [← Real.rpow_natCast (p : ℝ) (n - k), ← Real.rpow_add hp0, Nat.cast_sub hk]
  congr 1
  ring

/-- **A power-saving exponential-sum bound gives the per-prime index bound with
the same saving.**  For every `θ > 0`, `ExpSumBound n θ` implies
`‖indexFourierCoeff p n k a‖ ≤ C·p^{n-k-θ}` for `a ≠ 0`. -/
theorem mIndexSaving_of_expSumBound (n : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (hE : ExpSumBound n θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ), k ≤ n →
      ∀ a : Fin n → ZMod p, a ≠ 0 →
        ‖indexFourierCoeff p n k a‖ ≤ C * (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) := by
  classical
  obtain ⟨CE, hCE0, hEb⟩ := hE
  refine ⟨max (CE * (2 : ℝ) ^ ((n + 1) ^ 4)) ((2 : ℝ) ^ ((n + 1) ^ 4) * (n : ℝ) ^ θ),
    by positivity, ?_⟩
  intro p _inst k hk a ha
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have h : 1 ≤ p := (Fact.out : Nat.Prime p).one_lt.le
    exact_mod_cast h
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le one_pos hp1
  have h2p : (0 : ℝ) ≤ (2 : ℝ) ^ ((n + 1) ^ 4) := by positivity
  have hcardR : ((indexClassFinset p n k).card : ℝ)
      ≤ (2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ (n - k) := by
    have h := indexClassFinset_card_le p n k hk
    calc ((indexClassFinset p n k).card : ℝ)
        ≤ ((2 ^ ((n + 1) ^ 4) * p ^ (n - k) : ℕ) : ℝ) := by exact_mod_cast h
      _ = (2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ (n - k) := by push_cast; ring
  by_cases hpn : n < p
  · -- the exponential-sum branch
    have hinner : ∀ v : Fin n → ZMod p,
        ‖∑ c : ZMod p, ZMod.stdAddChar (∑ i, a i * (transVec p n c v) i)‖
          ≤ CE * (p : ℝ) ^ (1 - θ) := by
      intro v
      have hpoly : ∀ c : ZMod p, (∑ i : Fin n, a i * (transVec p n c v) i)
          = (shiftPoly p n a (monicOfTrail n v)).eval c := by
        intro c
        rw [shiftPoly_eval]
        refine Finset.sum_congr rfl fun i _ => ?_
        have h1 : (transVec p n c v) i
            = ((monicOfTrail n v).comp (X + C c)).coeff (i : ℕ) := by
          rw [← monicOfTrail_coeff n (transVec p n c v) (i : Fin n).isLt,
            monicOfTrail_transVec]
        rw [h1]
      have hsum : (∑ c : ZMod p, ZMod.stdAddChar (∑ i, a i * (transVec p n c v) i))
          = ∑ c : ZMod p,
              ZMod.stdAddChar ((shiftPoly p n a (monicOfTrail n v)).eval c) :=
        Finset.sum_congr rfl fun c _ => by rw [hpoly c]
      rw [hsum]
      have hpos := shiftPoly_natDegree_pos p n a ha (monicOfTrail n v)
        (monicOfTrail_monic n v) (monicOfTrail_natDegree n v) hpn
      have hle := shiftPoly_natDegree_le p n a (monicOfTrail n v)
        (monicOfTrail_natDegree n v)
      exact hEb p hpn _ hpos hle
    have h1 : ∑ v ∈ indexClassFinset p n k,
        ‖∑ c : ZMod p, ZMod.stdAddChar (∑ i, a i * (transVec p n c v) i)‖
        ≤ ((indexClassFinset p n k).card : ℝ) * (CE * (p : ℝ) ^ (1 - θ)) := by
      refine (Finset.sum_le_sum fun v _ => hinner v).trans (le_of_eq ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
    have hmain := norm_indexFourierCoeff_le p n k a
    have h3 : (1 / (p : ℝ)) * (((indexClassFinset p n k).card : ℝ)
            * (CE * (p : ℝ) ^ (1 - θ)))
        ≤ (1 / (p : ℝ)) * (((2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ (n - k))
            * (CE * (p : ℝ) ^ (1 - θ))) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcardR ?_) (by positivity)
      positivity
    have h4 : CE * (2 : ℝ) ^ ((n + 1) ^ 4)
        ≤ max (CE * (2 : ℝ) ^ ((n + 1) ^ 4))
          ((2 : ℝ) ^ ((n + 1) ^ 4) * (n : ℝ) ^ θ) := le_max_left _ _
    have h5 : (1 / (p : ℝ)) * (((2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ (n - k))
            * (CE * (p : ℝ) ^ (1 - θ)))
        = CE * (2 : ℝ) ^ ((n + 1) ^ 4)
          * ((p : ℝ) ^ (n - k) * ((1 / (p : ℝ)) * (p : ℝ) ^ (1 - θ))) := by ring
    refine le_trans (le_trans hmain (mul_le_mul_of_nonneg_left h1 (by positivity))) ?_
    refine le_trans h3 ?_
    rw [h5, inv_mul_rpow_one_sub p hp0 θ, rpow_mul_rpow_neg p n k hp0 hk θ]
    exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hp0.le _)
  · -- the trivial branch `p ≤ n`
    have hple : p ≤ n := not_lt.mp hpn
    have hnorm : ‖indexFourierCoeff p n k a‖ ≤ ((indexClassFinset p n k).card : ℝ) := by
      rw [indexFourierCoeff]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      have h1 : ∀ v ∈ indexClassFinset p n k,
          ‖ZMod.stdAddChar (∑ i, a i * v i)‖ = (1 : ℝ) :=
        fun v _ => norm_stdAddChar_eq_one _
      rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h3 : (0 : ℝ) ≤ (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) := Real.rpow_nonneg hp0.le _
    have h4 : (2 : ℝ) ^ ((n + 1) ^ 4) * (n : ℝ) ^ θ
        ≤ max (CE * (2 : ℝ) ^ ((n + 1) ^ 4))
          ((2 : ℝ) ^ ((n + 1) ^ 4) * (n : ℝ) ^ θ) := le_max_right _ _
    have hpr : (p : ℝ) ^ θ ≤ (n : ℝ) ^ θ :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hple) hθ.le
    calc ‖indexFourierCoeff p n k a‖ ≤ ((indexClassFinset p n k).card : ℝ) := hnorm
      _ ≤ (2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ (n - k) := hcardR
      _ = (2 : ℝ) ^ ((n + 1) ^ 4)
            * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) * (p : ℝ) ^ θ) := by
            rw [rpow_split p n k hp0 hk θ]
      _ ≤ (2 : ℝ) ^ ((n + 1) ^ 4)
            * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) * (n : ℝ) ^ θ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpr h3) h2p
      _ = ((2 : ℝ) ^ ((n + 1) ^ 4) * (n : ℝ) ^ θ)
            * (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) := by ring
      _ ≤ max (CE * (2 : ℝ) ^ ((n + 1) ^ 4))
            ((2 : ℝ) ^ ((n + 1) ^ 4) * (n : ℝ) ^ θ)
            * (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) :=
            mul_le_mul_of_nonneg_right h4 h3

/-- **The Weil bound implies the single-prime §4 input `MIndexBound`** (the
`θ = 1/2` case of `mIndexSaving_of_expSumBound`). -/
theorem mIndexBound_of_weilPolyBound (n : ℕ) (hn : 1 ≤ n) (hW : WeilPolyBound n) :
    MIndexBound n := by
  obtain ⟨C, hC, hb⟩ := mIndexSaving_of_expSumBound n (1 / 2) (by norm_num)
    (expSumBound_half_of_weilPolyBound n hW)
  refine ⟨C, hC, ?_⟩
  intro p _inst k hk a ha
  simpa using hb p k hk a ha

end
end Submission.Vdw
