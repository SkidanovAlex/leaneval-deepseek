import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Commons.FieldTheory.Minpoly.ConjRoots.trace_rat_poly

open Polynomial
open scoped BigOperators

namespace Commons.Polynomial.Prod

noncomputable section

/-- Membership in the complex root multiset of the minimal polynomial of an
algebraic `z` is equivalent to vanishing of the minimal polynomial at `w`. -/
private lemma mem_aroots_minpoly_iff_aeval {z : ℂ} (hz : IsIntegral ℚ z) (w : ℂ) :
    w ∈ (minpoly ℚ z).aroots ℂ ↔ aeval w (minpoly ℚ z) = 0 := by
  rw [Polynomial.aroots_def]
  rw [Polynomial.mem_roots]
  · rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def]
  · exact Polynomial.map_ne_zero (minpoly.ne_zero hz)

/-- The unweighted power sum over the conjugate class of `k0` (the indices
whose `b`-values are roots of `minpoly ℚ (b k0)`) is rational.  It is the
trace of `X^e` in `ℚ(b k0)/ℚ`, and the class is the full root set of the
minimal polynomial (closure `hclosed`, distinctness `hinj`). -/
private lemma conjClass_powerSum_rat {n : ℕ} (I : Finset (Fin n)) (b : Fin n → ℂ)
    (k0 : Fin n) (hk0 : k0 ∈ I)
    (hbI : ∀ k ∈ I, IsIntegral ℤ (b k))
    (hinjI : ∀ {k t : Fin n}, k ∈ I → t ∈ I → b k = b t → k = t)
    (hclosed : ∀ k ∈ I, ∀ w : ℂ, aeval w (minpoly ℚ (b k)) = 0 → ∃ t ∈ I, b t = w)
    (e : ℕ) :
    ∃ q : ℚ,
      (∑ t ∈ I.filter (fun t => aeval (b t) (minpoly ℚ (b k0)) = 0), (b t) ^ e) = (q : ℂ) := by
  classical
  let C : Finset (Fin n) := I.filter (fun t => aeval (b t) (minpoly ℚ (b k0)) = 0)
  have hzI : IsIntegral ℚ (b k0) := IsIntegral.tower_top (R := ℤ) (A := ℚ) (B := ℂ) (hbI k0 hk0)
  have hz : IsAlgebraic ℚ (b k0) := (isAlgebraic_iff_isIntegral).mpr hzI
  have hnoduproots : ((minpoly ℚ (b k0)).aroots ℂ).Nodup := by
    rw [Polynomial.aroots_def]
    apply Polynomial.nodup_roots
    exact Polynomial.Separable.map (minpoly.irreducible hzI).separable
  have hsum_img : (∑ t ∈ C, (b t) ^ e) = ∑ w ∈ C.image b, w ^ e := by
    dsimp [C]
    rw [Finset.sum_image]
    intro t ht t' ht' h
    exact hinjI (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht').1 h
  have himg : C.image b = ((minpoly ℚ (b k0)).aroots ℂ).toFinset := by
    dsimp [C]
    ext w
    constructor
    · intro hw
      rcases (Finset.mem_image.mp hw) with ⟨t, htC, hbt⟩
      have hbroot : aeval (b t) (minpoly ℚ (b k0)) = 0 := (Finset.mem_filter.mp htC).2
      have hwrootw : aeval w (minpoly ℚ (b k0)) = 0 := by
        rw [← hbt]
        exact hbroot
      exact Multiset.mem_toFinset.2 ((mem_aroots_minpoly_iff_aeval hzI w).mpr hwrootw)
    · intro hw
      have hwmem : w ∈ (minpoly ℚ (b k0)).aroots ℂ := Multiset.mem_toFinset.1 hw
      have hwroot : aeval w (minpoly ℚ (b k0)) = 0 :=
        (mem_aroots_minpoly_iff_aeval hzI w).mp hwmem
      rcases hclosed k0 hk0 w hwroot with ⟨t, htI, hbt⟩
      refine Finset.mem_image.mpr ⟨t, ?_, hbt⟩
      exact Finset.mem_filter.mpr ⟨htI, by rwa [hbt]⟩
  obtain ⟨q, hq⟩ :=
    Commons.FieldTheory.Minpoly.ConjRoots.trace_rat_poly hz (X ^ e)
  have hms : (((minpoly ℚ (b k0)).aroots ℂ).map (fun w : ℂ => w ^ e)).sum = (q : ℂ) := by
    simpa [Polynomial.eval_map, Polynomial.eval_pow] using hq
  have hnodup_sub : (∑ w : {y : ℂ // y ∈ (minpoly ℚ (b k0)).aroots ℂ}, w.1 ^ e) =
      (((minpoly ℚ (b k0)).aroots ℂ).map (fun w : ℂ => w ^ e)).sum := by
    exact Commons.FieldTheory.Minpoly.ConjRoots.multiset_nodup_sum_subtype
      ((minpoly ℚ (b k0)).aroots ℂ) hnoduproots (fun w : ℂ => w ^ e)
  have hsum_toFinset : (∑ w ∈ ((minpoly ℚ (b k0)).aroots ℂ).toFinset, w ^ e) = (q : ℂ) := by
    calc
      (∑ w ∈ ((minpoly ℚ (b k0)).aroots ℂ).toFinset, w ^ e)
          = ∑ w : {y : ℂ // y ∈ (minpoly ℚ (b k0)).aroots ℂ}, w.1 ^ e := by
              rw [Finset.sum_mem_multiset ((minpoly ℚ (b k0)).aroots ℂ)
                (fun w : {y : ℂ // y ∈ (minpoly ℚ (b k0)).aroots ℂ} => w.1 ^ e)
                (fun w : ℂ => w ^ e) (by intro x; rfl)]
      _ = (((minpoly ℚ (b k0)).aroots ℂ).map (fun w : ℂ => w ^ e)).sum := hnodup_sub
      _ = (q : ℂ) := hms
  have hmain : (∑ t ∈ C, (b t) ^ e) = (q : ℂ) := by
    rw [hsum_img, himg]
    exact hsum_toFinset
  exact ⟨q, hmain⟩

/-- The `β`-weighted power sum over the conjugate class of `k0` is rational:
on the class `β` is constantly `β k0`, and the unweighted class power sum is
rational. -/
private lemma conjClass_weighted_sum_rat {n : ℕ} (I : Finset (Fin n)) (b : Fin n → ℂ)
    (β : Fin n → ℤ) (k0 : Fin n) (hk0 : k0 ∈ I)
    (hbI : ∀ k ∈ I, IsIntegral ℤ (b k))
    (hinjI : ∀ {k t : Fin n}, k ∈ I → t ∈ I → b k = b t → k = t)
    (hclosed : ∀ k ∈ I, ∀ w : ℂ, aeval w (minpoly ℚ (b k)) = 0 → ∃ t ∈ I, b t = w)
    (hβc : ∀ k ∈ I, ∀ t ∈ I, aeval (b t) (minpoly ℚ (b k)) = 0 → β k = β t)
    (e : ℕ) :
    ∃ q : ℚ,
      (∑ t ∈ I.filter (fun t => aeval (b t) (minpoly ℚ (b k0)) = 0),
        ((β t : ℤ) : ℂ) * (b t) ^ e) = (q : ℂ) := by
  classical
  obtain ⟨q1, hq1⟩ := conjClass_powerSum_rat I b k0 hk0 hbI hinjI hclosed e
  have hβeq : ∀ t : Fin n, t ∈ I → aeval (b t) (minpoly ℚ (b k0)) = 0 → β t = β k0 := by
    intro t htI hroot
    exact (hβc k0 hk0 t htI hroot).symm
  refine ⟨(((β k0 : ℤ) : ℚ) * q1), ?_⟩
  calc
    (∑ t ∈ I.filter (fun t => aeval (b t) (minpoly ℚ (b k0)) = 0),
        ((β t : ℤ) : ℂ) * (b t) ^ e)
        = (∑ t ∈ I.filter (fun t => aeval (b t) (minpoly ℚ (b k0)) = 0),
            (((β k0 : ℤ) : ℂ)) * (b t) ^ e) := by
            apply Finset.sum_congr rfl
            intro t ht
            have hβ : β t = β k0 := hβeq t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2
            simp [hβ]
    _ = ((β k0 : ℤ) : ℂ) *
          (∑ t ∈ I.filter (fun t => aeval (b t) (minpoly ℚ (b k0)) = 0), (b t) ^ e) := by
          rw [Finset.mul_sum]
    _ = ((β k0 : ℤ) : ℂ) * (q1 : ℂ) := by rw [hq1]
    _ = ((((β k0 : ℤ) : ℚ) * q1 : ℚ) : ℂ) := by norm_cast

/-- Finset-level `WeightedPowerSumsConjClosed`: over any finite family of
indices whose `b`-values are pairwise distinct, conjugate-closed algebraic
integers, with integer weights `β` constant on each conjugate class, the
weighted power sum `∑ βₖ·bₖ^e` is rational.  Proved by peeling off one
conjugate class at a time (strong induction on the cardinality of the index
set). -/
private lemma WeightedPowerSumsConjClosed_finset {n : ℕ} (I : Finset (Fin n))
    (b : Fin n → ℂ) (β : Fin n → ℤ)
    (hbI : ∀ k ∈ I, IsIntegral ℤ (b k))
    (hinjI : ∀ {k t : Fin n}, k ∈ I → t ∈ I → b k = b t → k = t)
    (hclosed : ∀ k ∈ I, ∀ w : ℂ, aeval w (minpoly ℚ (b k)) = 0 → ∃ t ∈ I, b t = w)
    (hβc : ∀ k ∈ I, ∀ t ∈ I, aeval (b t) (minpoly ℚ (b k)) = 0 → β k = β t)
    (e : ℕ) : ∃ q : ℚ, (∑ k ∈ I, ((β k : ℤ) : ℂ) * (b k) ^ e) = (q : ℂ) := by
  classical
  let P : ℕ → Prop := fun m => ∀ (I : Finset (Fin n)), I.card = m →
      (∀ k ∈ I, IsIntegral ℤ (b k)) →
      (∀ {k t : Fin n}, k ∈ I → t ∈ I → b k = b t → k = t) →
      (∀ k ∈ I, ∀ w : ℂ, aeval w (minpoly ℚ (b k)) = 0 → ∃ t ∈ I, b t = w) →
      (∀ k ∈ I, ∀ t ∈ I, aeval (b t) (minpoly ℚ (b k)) = 0 → β k = β t) →
      ∃ q : ℚ, (∑ k ∈ I, ((β k : ℤ) : ℂ) * (b k) ^ e) = (q : ℂ)
  have hP : ∀ m : ℕ, P m := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih I hcard hbI hinjI hclosed hβc
    by_cases hIempty : I = ∅
    · subst I
      refine ⟨0, ?_⟩
      simp
    · rcases Finset.nonempty_iff_ne_empty.mpr hIempty with ⟨k0, hk0I⟩
      let p : Fin n → Prop := fun t => aeval (b t) (minpoly ℚ (b k0)) = 0
      let C : Finset (Fin n) := I.filter p
      let R : Finset (Fin n) := I.filter (fun t => ¬ p t)
      have hk0C : k0 ∈ C := by
        dsimp [C, p]
        exact Finset.mem_filter.mpr ⟨hk0I, minpoly.aeval ℚ (b k0)⟩
      have hCpos : 0 < C.card := Finset.card_pos.mpr ⟨k0, hk0C⟩
      have hRcard_lt_I : R.card < I.card := by
        have hsum : C.card + R.card = I.card := by
          dsimp [C, R]
          rw [Finset.card_filter_add_card_filter_not]
        omega
      have hRcard_lt_m : R.card < m := by omega
      have hrec := ih R.card hRcard_lt_m R rfl
        (fun k hk => hbI k (Finset.mem_filter.mp hk).1)
        (fun {k t} hk ht h => hinjI (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp ht).1 h)
        (fun k hk w hw => by
          have hkI : k ∈ I := (Finset.mem_filter.mp hk).1
          have hknp : ¬ p k := (Finset.mem_filter.mp hk).2
          rcases hclosed k hkI w hw with ⟨t, htI, hbt⟩
          refine ⟨t, ?_, hbt⟩
          refine Finset.mem_filter.mpr ⟨htI, ?_⟩
          intro hpt
          have hQk0 : IsIntegral ℚ (b k0) :=
            IsIntegral.tower_top (R := ℤ) (A := ℚ) (B := ℂ) (hbI k0 hk0I)
          have hQk : IsIntegral ℚ (b k) :=
            IsIntegral.tower_top (R := ℤ) (A := ℚ) (B := ℂ) (hbI k hkI)
          have hroot_bt : aeval (b t) (minpoly ℚ (b k)) = 0 := by rwa [hbt]
          have hmin_k0_t : minpoly ℚ (b k0) = minpoly ℚ (b t) :=
            (minpoly.eq_iff_aeval_minpoly_eq_zero (A := ℚ) (B := ℂ) (C := ℂ)
              (b := b k0) hQk0 (c := b t)).mpr hpt
          have hmin_k_t : minpoly ℚ (b k) = minpoly ℚ (b t) :=
            (minpoly.eq_iff_aeval_minpoly_eq_zero (A := ℚ) (B := ℂ) (C := ℂ)
              (b := b k) hQk (c := b t)).mpr hroot_bt
          have hmin_k_k0 : minpoly ℚ (b k0) = minpoly ℚ (b k) := hmin_k0_t.trans hmin_k_t.symm
          have hpk : aeval (b k) (minpoly ℚ (b k0)) = 0 :=
            (minpoly.eq_iff_aeval_minpoly_eq_zero (A := ℚ) (B := ℂ) (C := ℂ)
              (b := b k0) hQk0 (c := b k)).mp hmin_k_k0
          exact hknp (by dsimp [p]; exact hpk))
        (fun k hk t ht h => hβc k (Finset.mem_filter.mp hk).1 t (Finset.mem_filter.mp ht).1 h)
      -- class part rational
      obtain ⟨qC, hqC⟩ := conjClass_weighted_sum_rat I b β k0 hk0I hbI hinjI hclosed hβc e
      -- rest part rational
      obtain ⟨qR, hqR⟩ := hrec
      refine ⟨qC + qR, ?_⟩
      calc
        (∑ k ∈ I, ((β k : ℤ) : ℂ) * (b k) ^ e)
            = (∑ k ∈ I.filter p, ((β k : ℤ) : ℂ) * (b k) ^ e) +
                (∑ k ∈ I.filter (fun k => ¬ p k), ((β k : ℤ) : ℂ) * (b k) ^ e) := by
                exact (Finset.sum_filter_add_sum_filter_not I p
                  (f := fun k => ((β k : ℤ) : ℂ) * (b k) ^ e)).symm
        _ = (qC : ℂ) + (qR : ℂ) := by
            dsimp [p, C, R]
            rw [hqC, hqR]
        _ = ((qC + qR : ℚ) : ℂ) := by norm_cast
  exact hP I.card I rfl hbI hinjI hclosed hβc

/-- `WeightedPowerSumsConjClosed`: if `b` is an injective family of algebraic
integers closed under `ℚ`-conjugation and `β` is constant on each conjugate
class, then every weighted power sum `∑ₖ βₖ·bₖᵉ` is rational. -/
lemma WeightedPowerSumsConjClosed {n : ℕ} (b : Fin n → ℂ) (β : Fin n → ℤ)
    (hb : ∀ k : Fin n, IsIntegral ℤ (b k))
    (hinj : Function.Injective b)
    (hclosed : ∀ k : Fin n, ∀ w : ℂ, aeval w (minpoly ℚ (b k)) = 0 → ∃ t : Fin n, b t = w)
    (hβc : ∀ k t : Fin n, aeval (b t) (minpoly ℚ (b k)) = 0 → β k = β t)
    (e : ℕ) :
    ∃ q : ℚ, (∑ k : Fin n, ((β k : ℤ) : ℂ) * (b k) ^ e) = (q : ℂ) := by
  classical
  obtain ⟨q, hq⟩ := WeightedPowerSumsConjClosed_finset (Finset.univ : Finset (Fin n)) b β
    (fun k hk => hb k)
    (fun {k t} hk ht h => hinj h)
    (fun k hk w hw => by
      rcases hclosed k w hw with ⟨t, ht⟩
      exact ⟨t, Finset.mem_univ t, ht⟩)
    (fun k hk t ht h => hβc k t h)
    e
  refine ⟨q, ?_⟩
  simpa using hq

end

end Commons.Polynomial.Prod