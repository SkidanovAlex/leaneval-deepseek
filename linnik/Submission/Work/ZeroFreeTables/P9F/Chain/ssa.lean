import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.DdBits
import Submission.Work.LinnikBurgess.local_corr6_nonContent_sharp
import Submission.Work.LinnikBurgess.corr6_norm_le_prod_local
import Submission.Work.LinnikBurgess.menuW_univ
import Submission.Work.LinnikBurgess.local_prime_sqrtWeight
import Submission.Work.LinnikBurgess.DLd_prod_of_DLp
import Submission.Work.LinnikBurgess.local_prime_powOne_bound
import Submission.Work.LinnikBurgess.localFactor_bound_ge5
import Submission.Work.ZeroFreeTables.P9F.localFactor_bound_small_aux
import Submission.Work.ZeroFreeTables.P9F.Chain.frame_stub
import Submission.Work.LinnikBurgess.sqrtGcdW_prod_le_sqfreePart
import Submission.Work.LinnikBurgess.sqrt_mul_sum_le
import Submission.Work.LinnikBurgess.divisors_card_pow_le
import Submission.Work.LinnikBurgess.sqrt_prod_factorization
import Submission.Work.LinnikBurgess.sqfreePart_frame_hyp
import Submission.Work.LinnikBurgess.divisor_bounds_high
import Submission.Work.LinnikBurgess.singleton_ssa_defs
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

set_option maxRecDepth 8000

open scoped BigOperators
open Classical

namespace Work.P9Chain

open Work.LinnikBurgess

/-! ## Elementary facts about the prime factorisation of `q` -/

lemma factorization_pos_of_mem {q p : ℕ} (hp : p ∈ q.primeFactors) : 1 ≤ q.factorization p := by
  have hne : q.factorization p ≠ 0 := by
    have : p ∈ q.factorization.support := by rwa [Nat.support_factorization]
    exact Finsupp.mem_support_iff.mp this
  omega

lemma mem_low_iff {q p : ℕ} (hp : p ∈ q.primeFactors) :
    p ∈ lowPrimeSet q ↔ q.factorization p = 1 := by
  rw [lowPrimeSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩

lemma mem_high_iff {q p : ℕ} (hp : p ∈ q.primeFactors) :
    p ∈ highPrimeSet q ↔ 2 ≤ q.factorization p := by
  rw [highPrimeSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩

lemma low_disjoint_high (q : ℕ) : Disjoint (lowPrimeSet q) (highPrimeSet q) := by
  refine Finset.disjoint_iff_ne.mpr (fun a ha b hb hab => ?_)
  rw [lowPrimeSet, Finset.mem_filter] at ha
  rw [highPrimeSet, Finset.mem_filter] at hb
  subst hab
  omega

lemma low_union_high (q : ℕ) : lowPrimeSet q ∪ highPrimeSet q = q.primeFactors := by
  ext p
  simp only [Finset.mem_union, lowPrimeSet, highPrimeSet, Finset.mem_filter]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro hp
    have h1 := factorization_pos_of_mem hp
    rcases eq_or_lt_of_le h1 with h2 | h2
    · exact Or.inl ⟨hp, h2.symm⟩
    · exact Or.inr ⟨hp, by omega⟩

/-- The primes of `q` split into the exponent-`1` and the exponent-`≥ 2` ones. -/
lemma prod_low_mul_prod_high (q : ℕ) (F : ℕ → ℝ) :
    (∏ p ∈ lowPrimeSet q, F p) * (∏ p ∈ highPrimeSet q, F p)
      = ∏ p ∈ q.primeFactors, F p := by
  rw [← low_union_high q, Finset.prod_union (low_disjoint_high q)]

/-! ## Stage 1: the pointwise local bound -/

/-- `shift6` is `shift` of the shifted triples `aOf`, `bOf`. -/
lemma shift6_eq_shift {H : ℕ} (q : (Fin 3 → Fin H) × (Fin 3 → Fin H)) :
    shift6 q = shift (aOf q) (bOf q) := by
  funext i
  fin_cases i <;> simp [shift6, shift, aOf, bOf]

/-- `corr6` in the notation of `corr6_norm_le_prod_local`. -/
lemma corr6_eq_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {H : ℕ}
    (f g : Fin 3 → Fin H) :
    corr6 q χ f g
      = ∑ x : ZMod q, χ (∏ l : Fin 3, (x + ((aOf (f, g) l : ℕ) : ZMod q)))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + ((bOf (f, g) l : ℕ) : ZMod q)))) := rfl

lemma localFactor_nonneg (p e : ℕ) (a b : Fin 3 → ℕ) : 0 ≤ localFactor p e a b := by
  rw [localFactor]
  refine Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun j _ => ?_
  refine mul_nonneg (menuW_nonneg p e s j) ?_
  split_ifs <;> norm_num

lemma sqrtGcdW_nonneg (m : ℕ) (i : Fin 6) (v : Fin 6 → ℕ) : 0 ≤ sqrtGcdW m i v := by
  rw [sqrtGcdW]
  exact Finset.prod_nonneg fun l _ => Real.sqrt_nonneg _

lemma localB_nonneg (i : Fin 6) (a b : Fin 3 → ℕ) (p e : ℕ) : 0 ≤ localB i a b p e := by
  rw [localB]
  split_ifs with h
  · exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (sqrtGcdW_nonneg p i (shift a b))
  · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (localFactor_nonneg p e a b)

lemma localB_low {q p : ℕ} (a b : Fin 3 → ℕ) (i : Fin 6) (hp : p ∈ lowPrimeSet q) :
    localB i a b p (q.factorization p) = 6 * Real.sqrt (p : ℝ) * sqrtGcdW p i (shift a b) := by
  have hmem : p ∈ q.primeFactors := by
    rw [lowPrimeSet, Finset.mem_filter] at hp; exact hp.1
  rw [localB, if_pos ((mem_low_iff hmem).mp hp)]

lemma localB_high {q p : ℕ} (a b : Fin 3 → ℕ) (i : Fin 6) (hp : p ∈ highPrimeSet q) :
    localB i a b p (q.factorization p)
      = (p : ℝ) ^ ((q.factorization p : ℝ) / 2) * localFactor p (q.factorization p) a b := by
  have hmem : p ∈ q.primeFactors := by
    rw [highPrimeSet, Finset.mem_filter] at hp; exact hp.1
  rw [localB, if_neg (by have := (mem_high_iff hmem).mp hp; omega)]

lemma prod_low_localB (q : ℕ) (a b : Fin 3 → ℕ) (i : Fin 6) :
    (∏ p ∈ lowPrimeSet q, localB i a b p (q.factorization p))
      = (6 : ℝ) ^ (lowPrimeSet q).card * (∏ p ∈ lowPrimeSet q, Real.sqrt (p : ℝ))
        * ∏ p ∈ lowPrimeSet q, sqrtGcdW p i (shift a b) := by
  classical
  rw [Finset.prod_congr rfl (fun p hp => localB_low a b i hp)]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const]

lemma prod_high_localB (q : ℕ) (a b : Fin 3 → ℕ) (i : Fin 6) :
    (∏ p ∈ highPrimeSet q, localB i a b p (q.factorization p))
      = (∏ p ∈ highPrimeSet q, (p : ℝ) ^ ((q.factorization p : ℝ) / 2))
        * ∏ p ∈ highPrimeSet q, localFactor p (q.factorization p) a b := by
  classical
  rw [Finset.prod_congr rfl (fun p hp => localB_high a b i hp)]
  rw [Finset.prod_mul_distrib]

/-- The locally-checked bound `‖S_{p^e}‖ ≤ localB i a b p e` at every prime power, assembled from
the `e = 1` Weil bound `hOne` and the prime-power bounds `h5`, `h3`. -/
lemma localB_spec (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j)
    (hOne : ∀ (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ (p ^ 1)), χ.IsPrimitive →
      ‖∑ x : ZMod (p ^ 1), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ 1))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ 1)))))‖
        ≤ 6 * Real.sqrt (p : ℝ) * sqrtGcdW p i (shift a b))
    (h5 : ∀ {p e : ℕ} [Fact p.Prime], 5 ≤ p → 2 ≤ e → ∀ (χ : DirichletCharacter ℂ (p ^ e)),
      χ.IsPrimitive →
      ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
        ≤ (p : ℝ) ^ ((e : ℝ) / 2) * localFactor p e a b)
    (h3 : ∀ {p e : ℕ} [Fact p.Prime], p ≤ 3 → 2 ≤ e → ∀ (χ : DirichletCharacter ℂ (p ^ e)),
      χ.IsPrimitive →
      ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
        ≤ (p : ℝ) ^ ((e : ℝ) / 2) * localFactor p e a b) :
    ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 1 ≤ e → ∀ (χ : DirichletCharacter ℂ (p ^ e)),
      χ.IsPrimitive →
      ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
        ≤ localB i a b p e := by
  intro p hpF e he χ hχ
  have hp : p.Prime := Fact.out
  rcases eq_or_lt_of_le he with h1 | h2
  · subst h1
    rw [localB, if_pos rfl]
    exact hOne p χ hχ
  · rw [localB, if_neg (by omega)]
    by_cases h5' : 5 ≤ p
    · exact h5 h5' h2 χ hχ
    · have hp3 : p ≤ 3 := by
        by_contra hc
        have hlt : 3 < p := not_le.mp hc
        have hp4 : p = 4 := by omega
        subst hp4
        exact absurd hp (by norm_num)
      exact h3 hp3 h2 χ hχ

/-- **The pointwise CRT bound**: for a primitive `χ` mod `q` and a pair `(f, g)` whose `i`-th shift
is unique, `‖corr6 q χ f g‖` is bounded by the square-root weight times the product of the
`localFactor`s over the primes of `q` with exponent `≥ 2`. -/
lemma corr6_le_prod_local {q : ℕ} [NeZero q] (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {H : ℕ} (f g : Fin 3 → Fin H) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i →
      shift (aOf (f, g)) (bOf (f, g)) i ≠ shift (aOf (f, g)) (bOf (f, g)) j)
    (hloc : ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 1 ≤ e → ∀ (χp : DirichletCharacter ℂ (p ^ e)),
      χp.IsPrimitive →
      ‖∑ x : ZMod (p ^ e), χp (∏ l : Fin 3, (x + (aOf (f, g) l : ZMod (p ^ e))))
          * (starRingEnd ℂ) (χp (∏ l : Fin 3, (x + (bOf (f, g) l : ZMod (p ^ e)))))‖
        ≤ localB i (aOf (f, g)) (bOf (f, g)) p e)
    (hSq : (∏ p ∈ lowPrimeSet q, sqrtGcdW p i (shift (aOf (f, g)) (bOf (f, g))))
        ≤ sqrtGcdW (sqfreePart q) i (shift (aOf (f, g)) (bOf (f, g))))
    (hFac : (∏ p ∈ lowPrimeSet q, Real.sqrt (p : ℝ))
        * (∏ p ∈ highPrimeSet q, (p : ℝ) ^ ((q.factorization p : ℝ) / 2)) = Real.sqrt (q : ℝ)) :
    ‖corr6 q χ f g‖ ≤ 6 ^ (lowPrimeSet q).card * Real.sqrt (q : ℝ)
      * sqrtGcdW (sqfreePart q) i (shift6 (f, g))
      * ∏ p ∈ highPrimeSet q, localFactor p (q.factorization p) (aOf (f, g)) (bOf (f, g)) := by
  classical
  rw [corr6_eq_sum]
  refine (corr6_norm_le_prod_local (aOf (f, g)) (bOf (f, g))
      (localB i (aOf (f, g)) (bOf (f, g))) (localB_nonneg i (aOf (f, g)) (bOf (f, g)))
      hloc χ hχ).trans ?_
  rw [shift6_eq_shift (f, g)]
  rw [← prod_low_mul_prod_high q
        (fun p => localB i (aOf (f, g)) (bOf (f, g)) p (q.factorization p))]
  rw [prod_low_localB, prod_high_localB]
  have hA0 : (0 : ℝ) ≤ ∏ p ∈ lowPrimeSet q, Real.sqrt (p : ℝ) :=
    Finset.prod_nonneg fun p _ => Real.sqrt_nonneg _
  have hB0 : (0 : ℝ) ≤ ∏ p ∈ highPrimeSet q, (p : ℝ) ^ ((q.factorization p : ℝ) / 2) :=
    Finset.prod_nonneg fun p _ => Real.rpow_nonneg (by positivity) _
  have hW0 : (0 : ℝ) ≤ ∏ p ∈ lowPrimeSet q, sqrtGcdW p i (shift (aOf (f, g)) (bOf (f, g))) :=
    Finset.prod_nonneg fun p _ => sqrtGcdW_nonneg _ _ _
  have hW'0 : (0 : ℝ) ≤ sqrtGcdW (sqfreePart q) i
      (shift (aOf (f, g)) (bOf (f, g))) := sqrtGcdW_nonneg _ _ _
  have hL0 : (0 : ℝ) ≤ ∏ p ∈ highPrimeSet q,
      localFactor p (q.factorization p) (aOf (f, g)) (bOf (f, g)) :=
    Finset.prod_nonneg fun p _ => localFactor_nonneg _ _ _ _
  have hc0 : (0 : ℝ) ≤ (6 : ℝ) ^ (lowPrimeSet q).card := by positivity
  have hs0 : (0 : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  calc (6 : ℝ) ^ (lowPrimeSet q).card
        * (∏ p ∈ lowPrimeSet q, Real.sqrt (p : ℝ))
        * (∏ p ∈ lowPrimeSet q, sqrtGcdW p i (shift (aOf (f, g)) (bOf (f, g))))
        * ((∏ p ∈ highPrimeSet q, (p : ℝ) ^ ((q.factorization p : ℝ) / 2))
            * ∏ p ∈ highPrimeSet q,
                localFactor p (q.factorization p) (aOf (f, g)) (bOf (f, g)))
      = (6 : ℝ) ^ (lowPrimeSet q).card * Real.sqrt (q : ℝ)
        * ((∏ p ∈ lowPrimeSet q, sqrtGcdW p i (shift (aOf (f, g)) (bOf (f, g))))
            * ∏ p ∈ highPrimeSet q,
                localFactor p (q.factorization p) (aOf (f, g)) (bOf (f, g))) := by
        rw [← hFac]; ring
    _ ≤ (6 : ℝ) ^ (lowPrimeSet q).card * Real.sqrt (q : ℝ)
        * (sqrtGcdW (sqfreePart q) i (shift (aOf (f, g)) (bOf (f, g)))
            * ∏ p ∈ highPrimeSet q,
                localFactor p (q.factorization p) (aOf (f, g)) (bOf (f, g))) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hc0 hs0)
        exact mul_le_mul_of_nonneg_right hSq hL0
    _ = (6 : ℝ) ^ (lowPrimeSet q).card * Real.sqrt (q : ℝ)
        * sqrtGcdW (sqfreePart q) i (shift (aOf (f, g)) (bOf (f, g)))
        * ∏ p ∈ highPrimeSet q, localFactor p (q.factorization p) (aOf (f, g)) (bOf (f, g)) := by
        ring

/-! ## The index set of the content/level expansion -/

/-- The set of pairs `(s, j)` available at the prime power `p^{e_p}`. -/
noncomputable def Tset (q p : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (q.factorization p + 2)).product (Finset.range (q.factorization p + 1))

/-- The choice of a pair `(s, j)` at every prime of `q` with exponent `≥ 2`. -/
abbrev Sig (q : ℕ) : Type := ↥(highPrimeSet q) → ℕ × ℕ

/-- The finitely many choices available. -/
noncomputable def Pset (q : ℕ) : Finset (Sig q) :=
  Fintype.piFinset (fun p : ↥(highPrimeSet q) => Tset q p.val)

/-- `∏_{p ∈ high} p^{s_p}`. -/
noncomputable def dOf (q : ℕ) (σ : Sig q) : ℕ :=
  ∏ p : ↥(highPrimeSet q), p.val ^ (σ p).1

/-- `∏_{p ∈ high} p^{j_p}`. -/
noncomputable def gOf (q : ℕ) (σ : Sig q) : ℕ :=
  ∏ p : ↥(highPrimeSet q), p.val ^ (σ p).2

/-- `∏_{p ∈ high} menuW p e_p s_p j_p`. -/
noncomputable def wOf (q : ℕ) (σ : Sig q) : ℝ :=
  ∏ p : ↥(highPrimeSet q), menuW p.val (q.factorization p.val) (σ p).1 (σ p).2

/-- The indicator of `DLp p s_p ∧ p^{j_p} ∣ contAB` over the primes of `highPrimeSet q`. -/
noncomputable def indOf (q : ℕ) (a b : Fin 3 → ℕ) (σ : Sig q) : ℝ :=
  ∏ p : ↥(highPrimeSet q),
    (if DLp p.val (σ p).1 a b ∧ p.val ^ (σ p).2 ∣ contAB a b then 1 else 0)

/-- The exponent of `p` in `dOf q σ`, as a function of `p : ℕ`. -/
noncomputable def sig1 (q : ℕ) (σ : Sig q) (p : ℕ) : ℕ :=
  if h : p ∈ highPrimeSet q then (σ ⟨p, h⟩).1 else 0

/-- The exponent of `p` in `gOf q σ`, as a function of `p : ℕ`. -/
noncomputable def sig2 (q : ℕ) (σ : Sig q) (p : ℕ) : ℕ :=
  if h : p ∈ highPrimeSet q then (σ ⟨p, h⟩).2 else 0

/-- The set of pairs of triples whose `i`-th shift is unique. -/
noncomputable def uniqSet (H : ℕ) (i : Fin 6) :
    Finset ((Fin 3 → Fin H) × (Fin 3 → Fin H)) :=
  (Finset.univ : Finset ((Fin 3 → Fin H) × (Fin 3 → Fin H))).filter
    (fun fg => ∀ i', i' ≠ i → shift6 fg i ≠ shift6 fg i')

lemma mem_uniqSet {H : ℕ} {i : Fin 6} {fg : (Fin 3 → Fin H) × (Fin 3 → Fin H)} :
    fg ∈ uniqSet H i ↔ ∀ i', i' ≠ i → shift6 fg i ≠ shift6 fg i' := by
  rw [uniqSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- `dOf` agrees with the Finset product form, so that `DLd_prod_of_DLp` applies. -/
lemma dOf_eq_prod (q : ℕ) (σ : Sig q) :
    dOf q σ = ∏ p ∈ highPrimeSet q, p ^ sig1 q σ p := by
  rw [dOf, ← Finset.prod_attach (highPrimeSet q) (fun p : ℕ => p ^ sig1 q σ p),
    Finset.attach_eq_univ]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [sig1, dif_pos p.2]

lemma gOf_eq_prod (q : ℕ) (σ : Sig q) :
    gOf q σ = ∏ p ∈ highPrimeSet q, p ^ sig2 q σ p := by
  rw [gOf, ← Finset.prod_attach (highPrimeSet q) (fun p : ℕ => p ^ sig2 q σ p),
    Finset.attach_eq_univ]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [sig2, dif_pos p.2]

lemma mem_Pset {q : ℕ} {σ : Sig q} : σ ∈ Pset q ↔ ∀ p, σ p ∈ Tset q p.val := by
  rw [Pset]
  exact Fintype.mem_piFinset

/-- `localFactor` as a sum over the pair `(s, j)`. -/
lemma localFactor_eq_sum_Tset (q p : ℕ) (a b : Fin 3 → ℕ) :
    localFactor p (q.factorization p) a b
      = ∑ x ∈ Tset q p, menuW p (q.factorization p) x.1 x.2
          * (if DLp p x.1 a b ∧ p ^ x.2 ∣ contAB a b then 1 else 0) := by
  rw [localFactor, Tset]
  exact (Finset.sum_product (Finset.range (q.factorization p + 2))
    (Finset.range (q.factorization p + 1))
    (fun x : ℕ × ℕ => menuW p (q.factorization p) x.1 x.2
      * (if DLp p x.1 a b ∧ p ^ x.2 ∣ contAB a b then 1 else 0))).symm

/-- The content/level expansion of `∏_{p ∈ high} localFactor p e_p`. -/
lemma locProd_eq_sum (q : ℕ) (a b : Fin 3 → ℕ) :
    (∏ p ∈ highPrimeSet q, localFactor p (q.factorization p) a b)
      = ∑ σ ∈ Pset q, wOf q σ * indOf q a b σ := by
  classical
  rw [← Finset.prod_attach (highPrimeSet q)
        (fun p => localFactor p (q.factorization p) a b), Finset.attach_eq_univ]
  rw [Finset.prod_congr rfl (fun p _ => localFactor_eq_sum_Tset q p.val a b)]
  rw [Finset.prod_univ_sum, Pset]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [wOf, indOf, Finset.prod_mul_distrib]

lemma prod_primePow_dvd {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (s : ℕ → ℕ) {z : ℕ}
    (h : ∀ p ∈ P, p ^ s p ∣ z) : (∏ p ∈ P, p ^ s p) ∣ z := by
  classical
  revert hP h
  induction P using Finset.induction_on with
  | empty => intro _ _; simpa using one_dvd z
  | insert a P ha ih =>
    intro hP h
    rw [Finset.prod_insert ha]
    have hcop : Nat.Coprime (a ^ s a) (∏ p ∈ P, p ^ s p) := by
      refine Nat.Coprime.pow_left _ ?_
      refine Nat.Coprime.prod_right (fun p hp => ?_)
      refine Nat.Coprime.pow_right _ ?_
      have hpne : a ≠ p := fun hh => ha (hh ▸ hp)
      exact (Nat.coprime_primes (hP a (Finset.mem_insert_self a P))
        (hP p (Finset.mem_insert_of_mem hp))).mpr hpne
    exact hcop.mul_dvd_of_dvd_of_dvd (h a (Finset.mem_insert_self a P))
      (ih (fun p hp => hP p (Finset.mem_insert_of_mem hp))
          (fun p hp => h p (Finset.mem_insert_of_mem hp)))

lemma two_pow_card_primeFactors_le_tau {q : ℕ} (hq : 0 < q) :
    ((2 : ℝ) ^ (q.primeFactors.card : ℕ)) ≤ (q.divisors.card : ℝ) := by
  have hn0 : q ≠ 0 := ne_of_gt hq
  have hnat : (2 : ℕ) ^ q.primeFactors.card ≤ q.divisors.card := by
    rw [Nat.card_divisors hn0]
    calc (2 : ℕ) ^ q.primeFactors.card = ∏ p ∈ q.primeFactors, 2 := by
          rw [Finset.prod_const]
      _ ≤ ∏ p ∈ q.primeFactors, (q.factorization p + 1) := by
          refine Finset.prod_le_prod₀ (fun p _ => by norm_num) (fun p hp => ?_)
          have h1 := factorization_pos_of_mem hp
          omega
  calc ((2 : ℝ) ^ (q.primeFactors.card : ℕ)) = (((2 : ℕ) ^ q.primeFactors.card : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ (q.divisors.card : ℝ) := by exact_mod_cast hnat

lemma six_pow_low_le_tau {q : ℕ} (hq : 0 < q) :
    ((6 : ℝ) ^ (lowPrimeSet q).card) ≤ ((q.divisors.card : ℝ)) ^ 3 := by
  have hle : (lowPrimeSet q).card ≤ q.primeFactors.card := by
    rw [lowPrimeSet]
    exact Finset.card_filter_le _ _
  have h2 := two_pow_card_primeFactors_le_tau hq
  calc ((6 : ℝ) ^ (lowPrimeSet q).card) ≤ ((8 : ℝ) ^ (lowPrimeSet q).card) :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = (((2 : ℝ) ^ (lowPrimeSet q).card) ^ 3) := by
        rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, ← pow_mul, ← pow_mul]
        congr 1
        omega
    _ ≤ (((2 : ℝ) ^ (q.primeFactors.card)) ^ 3) :=
        pow_le_pow_left₀ (by positivity)
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hle) 3
    _ ≤ (((q.divisors.card : ℝ)) ^ 3) := by
        refine pow_le_pow_left₀ (by positivity) ?_ 3
        calc ((2 : ℝ) ^ (q.primeFactors.card)) = ((2 : ℝ) ^ (q.primeFactors.card : ℕ)) := rfl
          _ ≤ (q.divisors.card : ℝ) := h2

lemma sum_Tset_eq (q p : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ x ∈ Tset q p, F x.1 x.2)
      = ∑ s ∈ Finset.range (q.factorization p + 2),
          ∑ j ∈ Finset.range (q.factorization p + 1), F s j := by
  rw [Tset]
  exact Finset.sum_product _ _ _



/-- **U13 assembly, with all external local/counting inputs as hypotheses.**

`hOne` is the `e = 1` local Weil bound (in the `ZMod (p^1)` presentation), `h5`/`h3` are Theorems
L/L' (the local bounds at prime powers with `e ≥ 2`), `hframe` is Theorem F, `hSq`, `hFac`, `hDiv`,
`hFrameHyp`, `hDvd` are the elementary arithmetic inputs, and `hFin` is the final real inequality.
-/
theorem singleton_sum_all_aux
    (hOne : ∀ (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ (p ^ 1)), χ.IsPrimitive →
      ∀ (a b : Fin 3 → ℕ) (i : Fin 6),
        ‖∑ x : ZMod (p ^ 1), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ 1))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ 1)))))‖
          ≤ 6 * Real.sqrt (p : ℝ) * sqrtGcdW p i (shift a b))
    (h5 : ∀ {p e : ℕ} [Fact p.Prime], 5 ≤ p → 2 ≤ e → ∀ (χ : DirichletCharacter ℂ (p ^ e)),
      χ.IsPrimitive → ∀ (a b : Fin 3 → ℕ) (i : Fin 6),
        (∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j) →
        ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
          ≤ (p : ℝ) ^ ((e : ℝ) / 2) * localFactor p e a b)
    (h3 : ∀ {p e : ℕ} [Fact p.Prime], p ≤ 3 → 2 ≤ e → ∀ (χ : DirichletCharacter ℂ (p ^ e)),
      χ.IsPrimitive → ∀ (a b : Fin 3 → ℕ) (i : Fin 6),
        (∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j) →
        ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
          ≤ (p : ℝ) ^ ((e : ℝ) / 2) * localFactor p e a b)
    (hframe : ∀ {H : ℕ} (i : Fin 6) {m d g : ℕ}, Squarefree m → Nat.Coprime m d →
      Nat.Coprime m g → 0 < d → 0 < g →
      ∑ fg ∈ uniqSet H i, sqrtGcdW m i (shift6 fg) * frameW d g fg
        ≤ 10 ^ 5 * (3 : ℝ) ^ d.primeFactors.card * ((m * d * g).divisors.card : ℝ) ^ 8
            * ((H : ℝ) ^ 6 / ((d : ℝ) * g) + (H : ℝ) ^ 5 / g))
    (hSq : ∀ (q : ℕ) (i : Fin 6) (v : Fin 6 → ℕ),
      (∏ p ∈ lowPrimeSet q, sqrtGcdW p i v) ≤ sqrtGcdW (sqfreePart q) i v)
    (hFac : ∀ {q : ℕ}, 0 < q → (∏ p ∈ lowPrimeSet q, Real.sqrt (p : ℝ))
        * (∏ p ∈ highPrimeSet q, (p : ℝ) ^ ((q.factorization p : ℝ) / 2)) = Real.sqrt (q : ℝ))
    (hDiv : ∀ {q d g : ℕ}, 0 < q → sqfreePart q * d * g ∣ q ^ 3 →
        (((sqfreePart q * d * g).divisors.card : ℝ)) ^ 8 ≤ ((q.divisors.card : ℝ)) ^ 24)
    (hFrameHyp : ∀ {q : ℕ}, 0 < q → ∀ (σ : Sig q),(∀ p, σ p ∈ Tset q p.val) →
        Squarefree (sqfreePart q)
          ∧ Nat.Coprime (sqfreePart q) (dOf q σ)
          ∧ Nat.Coprime (sqfreePart q) (gOf q σ)
          ∧ 0 < dOf q σ ∧ 0 < gOf q σ
          ∧ sqfreePart q * dOf q σ * gOf q σ ∣ q ^ 3
          ∧ (dOf q σ).primeFactors.card ≤ (highPrimeSet q).card)
    (hDvd : ∀ {q : ℕ}, 0 < q → ∀ {d : ℕ}, d.primeFactors.card ≤ (highPrimeSet q).card →
        (2 : ℝ) ^ (highPrimeSet q).card ≤ (q.divisors.card : ℝ)
          ∧ (∏ p : ↥(highPrimeSet q), ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2)
              ≤ (q.divisors.card : ℝ) ^ 2
          ∧ (∏ p : ↥(highPrimeSet q), (p.val : ℝ) ^ ((q.factorization p.val : ℝ) / 6))
              ≤ (q : ℝ) ^ ((1 : ℝ) / 6)
          ∧ (3 : ℝ) ^ d.primeFactors.card ≤ (q.divisors.card : ℝ) ^ 2)
    (hFin : ∀ {q H : ℕ}, Real.sqrt (q : ℝ)
        * ((H : ℝ) ^ 6 + (H : ℝ) ^ 5 * (q : ℝ) ^ ((1 : ℝ) / 6))
        ≤ 2 * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      χ ≠ 1 → ∀ H : ℕ,
        ∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
          (if IsSingleton6 (f, g) then ‖corr6 q χ f g‖ else 0)
        ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ)) := by
  classical
  obtain ⟨Cτ, hCτpos, hCτ⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (ε / 200) (by positivity)
  refine ⟨max 1 (12 * (10 : ℝ) ^ 5 * (max Cτ 1) ^ 110),
    lt_max_iff.mpr (Or.inl one_pos), ?_⟩
  intro q _ χ hχ hχ1 H
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq0' : q ≠ 0 := NeZero.ne q
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq0'
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hqe : (0 : ℝ) ≤ (q : ℝ) ^ ε := Real.rpow_nonneg hqnn _
  have hτ1 : (1 : ℝ) ≤ (q.divisors.card : ℝ) := by
    have : 0 < q.divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd q, hq0'⟩⟩
    exact_mod_cast this
  have hτnn : (0 : ℝ) ≤ (q.divisors.card : ℝ) := Nat.cast_nonneg _
  set Y : ℝ := (H : ℝ) ^ 6 + (H : ℝ) ^ 5 * (q : ℝ) ^ ((1 : ℝ) / 6) with hY
  have hY0 : (0 : ℝ) ≤ Y := by rw [hY]; positivity
  have hper : ∀ i : Fin 6, ∑ fg ∈ uniqSet H i, ‖corr6 q χ fg.1 fg.2‖
      ≤ 6 ^ (lowPrimeSet q).card * Real.sqrt (q : ℝ) * (10 : ℝ) ^ 5
          * ((q.divisors.card : ℝ)) ^ 58 * Y := by
    intro i
    have hd0 : (∏ p ∈ highPrimeSet q, p).primeFactors.card ≤ (highPrimeSet q).card :=
      le_of_eq (congrArg Finset.card (Nat.primeFactors_prod (fun p hp =>
        (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1)))
    have hs1 : ∑ fg ∈ uniqSet H i, ‖corr6 q χ fg.1 fg.2‖
        ≤ 6 ^ (lowPrimeSet q).card * Real.sqrt (q : ℝ)
            * ∑ fg ∈ uniqSet H i, sqrtGcdW (sqfreePart q) i (shift6 fg)
                * ∏ p ∈ highPrimeSet q, localFactor p (q.factorization p) (aOf fg) (bOf fg) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun fg hfg => ?_)
      have hmem := mem_uniqSet.mp hfg
      have hi : ∀ j : Fin 6, j ≠ i →
          shift (aOf fg) (bOf fg) i ≠ shift (aOf fg) (bOf fg) j := by
        intro j hj
        have h := hmem j hj
        rwa [shift6_eq_shift fg] at h
      have hp := corr6_le_prod_local hq0 χ hχ fg.1 fg.2 i hi
        (localB_spec (aOf fg) (bOf fg) i hi
          (fun p _ χ hχ => hOne p χ hχ (aOf fg) (bOf fg) i)
          (fun {p e} _ hp he χ hχ => h5 hp he χ hχ (aOf fg) (bOf fg) i hi)
          (fun {p e} _ hp he χ hχ => h3 hp he χ hχ (aOf fg) (bOf fg) i hi))
        (hSq q i (shift (aOf fg) (bOf fg))) (hFac hq0)
      calc ‖corr6 q χ fg.1 fg.2‖
          ≤ 6 ^ (lowPrimeSet q).card * Real.sqrt (q : ℝ)
              * sqrtGcdW (sqfreePart q) i (shift6 fg)
              * ∏ p ∈ highPrimeSet q,
                  localFactor p (q.factorization p) (aOf fg) (bOf fg) := hp
        _ = (6 ^ (lowPrimeSet q).card * Real.sqrt (q : ℝ))
              * (sqrtGcdW (sqfreePart q) i (shift6 fg)
                  * ∏ p ∈ highPrimeSet q,
                      localFactor p (q.factorization p) (aOf fg) (bOf fg)) := by ring
    have hs2 : ∑ fg ∈ uniqSet H i, (sqrtGcdW (sqfreePart q) i (shift6 fg)
          * ∏ p ∈ highPrimeSet q, localFactor p (q.factorization p) (aOf fg) (bOf fg))
        = ∑ σ ∈ Pset q, ∑ fg ∈ uniqSet H i,
            sqrtGcdW (sqfreePart q) i (shift6 fg)
              * (wOf q σ * indOf q (aOf fg) (bOf fg) σ) := by
      calc ∑ fg ∈ uniqSet H i, (sqrtGcdW (sqfreePart q) i (shift6 fg)
            * ∏ p ∈ highPrimeSet q, localFactor p (q.factorization p) (aOf fg) (bOf fg))
          = ∑ fg ∈ uniqSet H i, ∑ σ ∈ Pset q, sqrtGcdW (sqfreePart q) i (shift6 fg)
              * (wOf q σ * indOf q (aOf fg) (bOf fg) σ) := by
            refine Finset.sum_congr rfl (fun fg _ => ?_)
            rw [locProd_eq_sum, Finset.mul_sum]
        _ = ∑ σ ∈ Pset q, ∑ fg ∈ uniqSet H i, sqrtGcdW (sqfreePart q) i (shift6 fg)
              * (wOf q σ * indOf q (aOf fg) (bOf fg) σ) := Finset.sum_comm
    have hs3 : ∀ σ ∈ Pset q,
        ∑ fg ∈ uniqSet H i, sqrtGcdW (sqfreePart q) i (shift6 fg)
            * (wOf q σ * indOf q (aOf fg) (bOf fg) σ)
          ≤ wOf q σ * ((10 : ℝ) ^ 5 * (3 : ℝ) ^ (dOf q σ).primeFactors.card
              * ((sqfreePart q * dOf q σ * gOf q σ).divisors.card : ℝ) ^ 8
              * ((H : ℝ) ^ 6 / ((dOf q σ : ℝ) * gOf q σ)
                  + (H : ℝ) ^ 5 / (gOf q σ : ℝ))) := by
      intro σ hσ
      have hσmem : ∀ p, σ p ∈ Tset q p.val := mem_Pset.mp hσ
      obtain ⟨hm_sq, hm_d, hm_g, hd_pos, hg_pos, hdg_dvd, hω⟩ := hFrameHyp hq0 σ hσmem
      have hfc := hframe (H := H) i (m := sqfreePart q) (d := dOf q σ) (g := gOf q σ)
        hm_sq hm_d hm_g hd_pos hg_pos
      have hind : ∀ fg : (Fin 3 → Fin H) × (Fin 3 → Fin H),
          indOf q (aOf fg) (bOf fg) σ ≤ frameW (dOf q σ) (gOf q σ) fg := by
        intro fg
        by_cases hP : ∀ p : ↥(highPrimeSet q),
            (DLp p.val (σ p).1 (aOf fg) (bOf fg) ∧ p.val ^ (σ p).2 ∣ contAB (aOf fg) (bOf fg))
        · have hind1 : indOf q (aOf fg) (bOf fg) σ = 1 := by
            rw [indOf]
            exact Finset.prod_eq_one (fun p _ => if_pos (hP p))
          have hDLd : DLd (dOf q σ) (aOf fg) (bOf fg) := by
            rw [dOf_eq_prod]
            exact DLd_prod_of_DLp (highPrimeSet q)
              (fun p hp => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1)
              (sig1 q σ) (aOf fg) (bOf fg)
              (fun p hp => by rw [sig1, dif_pos hp]; exact (hP ⟨p, hp⟩).1)
          have hcont : gOf q σ ∣ contAB (aOf fg) (bOf fg) := by
            rw [gOf_eq_prod]
            refine prod_primePow_dvd (P := highPrimeSet q)
              (fun p hp => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1)
              (sig2 q σ) ?_
            intro p hp
            rw [sig2, dif_pos hp]
            exact (hP ⟨p, hp⟩).2
          rw [hind1, frameW, if_pos ⟨hDLd, hcont⟩]
        · have hind0 : indOf q (aOf fg) (bOf fg) σ = 0 := by
            push_neg at hP
            obtain ⟨p0, hp0⟩ := hP
            rw [indOf]
            exact Finset.prod_eq_zero (Finset.mem_univ p0) (if_neg (fun h => hp0 h.1 h.2))
          rw [hind0, frameW]
          split_ifs <;> norm_num
      have hstep : ∑ fg ∈ uniqSet H i, sqrtGcdW (sqfreePart q) i (shift6 fg)
            * (wOf q σ * indOf q (aOf fg) (bOf fg) σ)
          = wOf q σ * ∑ fg ∈ uniqSet H i, sqrtGcdW (sqfreePart q) i (shift6 fg)
              * indOf q (aOf fg) (bOf fg) σ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun fg _ => ?_)
        ring
      have hw0 : 0 ≤ wOf q σ := by
        rw [wOf]
        exact Finset.prod_nonneg (fun p _ => menuW_nonneg _ _ _ _)
      have hub : ∑ fg ∈ uniqSet H i, sqrtGcdW (sqfreePart q) i (shift6 fg)
            * indOf q (aOf fg) (bOf fg) σ
          ≤ ∑ fg ∈ uniqSet H i, sqrtGcdW (sqfreePart q) i (shift6 fg)
              * frameW (dOf q σ) (gOf q σ) fg := by
        refine Finset.sum_le_sum (fun fg _ => ?_)
        exact mul_le_mul_of_nonneg_left (hind fg) (sqrtGcdW_nonneg _ _ _)
      rw [hstep]
      refine mul_le_mul_of_nonneg_left (hub.trans hfc) hw0
    have h4a : ∀ σ ∈ Pset q,
        (10 : ℝ) ^ 5 * (3 : ℝ) ^ (dOf q σ).primeFactors.card
            * ((sqfreePart q * dOf q σ * gOf q σ).divisors.card : ℝ) ^ 8
          ≤ (10 : ℝ) ^ 5 * ((q.divisors.card : ℝ)) ^ 26 := by
      intro σ hσ
      have hσmem : ∀ p, σ p ∈ Tset q p.val := mem_Pset.mp hσ
      obtain ⟨hm_sq, hm_d, hm_g, hd_pos, hg_pos, hdg_dvd, hω⟩ := hFrameHyp hq0 σ hσmem
      obtain ⟨h2ω, hge, hpf, h3ω⟩ := hDvd hq0 hω
      have hdiv := hDiv hq0 hdg_dvd
      calc (10 : ℝ) ^ 5 * (3 : ℝ) ^ (dOf q σ).primeFactors.card
            * ((sqfreePart q * dOf q σ * gOf q σ).divisors.card : ℝ) ^ 8
          ≤ (10 : ℝ) ^ 5 * (((q.divisors.card : ℝ)) ^ 2)
              * (((q.divisors.card : ℝ)) ^ 24) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h3ω (by positivity)) hdiv
              (by positivity) (by positivity)
        _ = (10 : ℝ) ^ 5 * ((q.divisors.card : ℝ)) ^ 26 := by ring
    have hA1 : ∑ σ ∈ Pset q, wOf q σ * ((H : ℝ) ^ 6 / ((dOf q σ : ℝ) * gOf q σ))
        = (H : ℝ) ^ 6 * ∏ p : ↥(highPrimeSet q), (∑ x ∈ Tset q p.val,
            menuW p.val (q.factorization p.val) x.1 x.2
              / (p.val : ℝ) ^ (x.1 + x.2)) := by
      rw [Finset.sum_congr rfl (fun σ _ => ?_), ← Finset.mul_sum, Pset,
        ← Finset.prod_univ_sum]
      have hdg : (dOf q σ : ℝ) * (gOf q σ : ℝ)
          = ∏ p : ↥(highPrimeSet q), (p.val : ℝ) ^ ((σ p).1 + (σ p).2) := by
        rw [dOf, gOf, Nat.cast_prod, Nat.cast_prod]
        simp only [Nat.cast_pow]
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun p _ => ?_)
        rw [← pow_add]
      rw [wOf, hdg, Finset.prod_div_distrib]
      ring
    have hA2 : ∑ σ ∈ Pset q, wOf q σ * ((H : ℝ) ^ 5 / (gOf q σ : ℝ))
        = (H : ℝ) ^ 5 * ∏ p : ↥(highPrimeSet q), (∑ x ∈ Tset q p.val,
            menuW p.val (q.factorization p.val) x.1 x.2 / (p.val : ℝ) ^ (x.2)) := by
      rw [Finset.sum_congr rfl (fun σ _ => ?_), ← Finset.mul_sum, Pset,
        ← Finset.prod_univ_sum]
      have hdg2 : (gOf q σ : ℝ)
          = ∏ p : ↥(highPrimeSet q), (p.val : ℝ) ^ (σ p).2 := by
        rw [gOf, Nat.cast_prod]
        simp only [Nat.cast_pow]
      rw [wOf, hdg2, Finset.prod_div_distrib]
      ring
    have hb1 : ∏ p : ↥(highPrimeSet q), (∑ x ∈ Tset q p.val,
          menuW p.val (q.factorization p.val) x.1 x.2 / (p.val : ℝ) ^ (x.1 + x.2))
        ≤ (10 : ℝ) ^ (8 * (highPrimeSet q).card)
            * ∏ p : ↥(highPrimeSet q), ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2 := by
      calc ∏ p : ↥(highPrimeSet q), (∑ x ∈ Tset q p.val,
            menuW p.val (q.factorization p.val) x.1 x.2 / (p.val : ℝ) ^ (x.1 + x.2))
          ≤ ∏ p : ↥(highPrimeSet q),
              ((10 : ℝ) ^ 8 * ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2) := by
            refine Finset.prod_le_prod₀ (fun p _ => ?_) (fun p _ => ?_)
            · exact Finset.sum_nonneg (fun x _ => div_nonneg (menuW_nonneg _ _ _ _)
                (pow_nonneg (Nat.cast_nonneg p.val) (x.1 + x.2)))
            · rw [sum_Tset_eq q p.val (fun a b => menuW p.val (q.factorization p.val) a b
                / (p.val : ℝ) ^ (a + b))]
              have hp := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp p.2).1).1
              have he := (Finset.mem_filter.mp p.2).2
              simpa only [Nat.cast_add, Nat.cast_one] using (menuW_univ hp he).2.1
        _ = (10 : ℝ) ^ (8 * (highPrimeSet q).card)
              * ∏ p : ↥(highPrimeSet q), ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2 := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
              ← pow_mul]
    have hb2 : ∏ p : ↥(highPrimeSet q), (∑ x ∈ Tset q p.val,
          menuW p.val (q.factorization p.val) x.1 x.2 / (p.val : ℝ) ^ (x.2))
        ≤ (10 : ℝ) ^ (8 * (highPrimeSet q).card)
            * ((∏ p : ↥(highPrimeSet q), ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2)
                * ∏ p : ↥(highPrimeSet q),
                    (p.val : ℝ) ^ ((q.factorization p.val : ℝ) / 6)) := by
      calc ∏ p : ↥(highPrimeSet q), (∑ x ∈ Tset q p.val,
            menuW p.val (q.factorization p.val) x.1 x.2 / (p.val : ℝ) ^ (x.2))
          ≤ ∏ p : ↥(highPrimeSet q),
              ((10 : ℝ) ^ 8 * ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2
                * (p.val : ℝ) ^ ((q.factorization p.val : ℝ) / 6)) := by
            refine Finset.prod_le_prod₀ (fun p _ => ?_) (fun p _ => ?_)
            · exact Finset.sum_nonneg (fun x _ => div_nonneg (menuW_nonneg _ _ _ _)
                (pow_nonneg (Nat.cast_nonneg p.val) (x.2)))
            · rw [sum_Tset_eq q p.val (fun a b => menuW p.val (q.factorization p.val) a b
                / (p.val : ℝ) ^ b)]
              have hp := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp p.2).1).1
              have he := (Finset.mem_filter.mp p.2).2
              simpa only [Nat.cast_add, Nat.cast_one] using (menuW_univ hp he).2.2.1
        _ = (10 : ℝ) ^ (8 * (highPrimeSet q).card)
              * ((∏ p : ↥(highPrimeSet q), ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2)
                  * ∏ p : ↥(highPrimeSet q),
                      (p.val : ℝ) ^ ((q.factorization p.val : ℝ) / 6)) := by
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
              Finset.card_univ, Fintype.card_coe, ← pow_mul]
            ring
    have h4b : ∑ σ ∈ Pset q, wOf q σ
          * ((H : ℝ) ^ 6 / ((dOf q σ : ℝ) * gOf q σ) + (H : ℝ) ^ 5 / (gOf q σ : ℝ))
        ≤ (10 : ℝ) ^ (8 * (highPrimeSet q).card)
            * (∏ p : ↥(highPrimeSet q), ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2)
            * Y := by
      have hsplit : ∑ σ ∈ Pset q, wOf q σ
            * ((H : ℝ) ^ 6 / ((dOf q σ : ℝ) * gOf q σ) + (H : ℝ) ^ 5 / (gOf q σ : ℝ))
          = ∑ σ ∈ Pset q, (wOf q σ * ((H : ℝ) ^ 6 / ((dOf q σ : ℝ) * gOf q σ))
              + wOf q σ * ((H : ℝ) ^ 5 / (gOf q σ : ℝ))) := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        ring
      rw [hsplit, Finset.sum_add_distrib, hA1, hA2]
      obtain ⟨-, hge', hpf', -⟩ := hDvd hq0 hd0
      calc (H : ℝ) ^ 6 * (∏ p : ↥(highPrimeSet q), (∑ x ∈ Tset q p.val,
              menuW p.val (q.factorization p.val) x.1 x.2 / (p.val : ℝ) ^ (x.1 + x.2)))
            + (H : ℝ) ^ 5 * (∏ p : ↥(highPrimeSet q), (∑ x ∈ Tset q p.val,
              menuW p.val (q.factorization p.val) x.1 x.2 / (p.val : ℝ) ^ (x.2)))
          ≤ (H : ℝ) ^ 6 * ((10 : ℝ) ^ (8 * (highPrimeSet q).card)
                * ∏ p : ↥(highPrimeSet q), ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2)
              + (H : ℝ) ^ 5 * ((10 : ℝ) ^ (8 * (highPrimeSet q).card)
                * ((∏ p : ↥(highPrimeSet q), ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2)
                    * ∏ p : ↥(highPrimeSet q),
                        (p.val : ℝ) ^ ((q.factorization p.val : ℝ) / 6))) := by
            refine add_le_add (mul_le_mul_of_nonneg_left hb1 (by positivity))
              (mul_le_mul_of_nonneg_left hb2 (by positivity))
        _ ≤ (H : ℝ) ^ 6 * ((10 : ℝ) ^ (8 * (highPrimeSet q).card)
                * (∏ p : ↥(highPrimeSet q), ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2))
              + (H : ℝ) ^ 5 * ((10 : ℝ) ^ (8 * (highPrimeSet q).card)
                * ((∏ p : ↥(highPrimeSet q), ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2)
                    * (q : ℝ) ^ ((1 : ℝ) / 6))) := by
            refine add_le_add le_rfl ?_
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hpf' (by positivity)) (by positivity)) (by positivity)
        _ = (10 : ℝ) ^ (8 * (highPrimeSet q).card)
              * (∏ p : ↥(highPrimeSet q), ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2) * Y := by
            rw [hY]; ring
    have hA0 : ∀ σ ∈ Pset q, 0 ≤ (H : ℝ) ^ 6 / ((dOf q σ : ℝ) * gOf q σ)
        + (H : ℝ) ^ 5 / (gOf q σ : ℝ) := by
      intro σ hσ
      obtain ⟨-, -, -, hd_pos, hg_pos, -, -⟩ := hFrameHyp hq0 σ (mem_Pset.mp hσ)
      have h1 : (0 : ℝ) < (dOf q σ : ℝ) := by exact_mod_cast hd_pos
      have h2 : (0 : ℝ) < (gOf q σ : ℝ) := by exact_mod_cast hg_pos
      positivity
    have hw0 : ∀ σ ∈ Pset q, 0 ≤ wOf q σ := by
      intro σ _
      rw [wOf]
      exact Finset.prod_nonneg (fun p _ => menuW_nonneg _ _ _ _)
    have hsumstep : ∑ σ ∈ Pset q, wOf q σ * ((10 : ℝ) ^ 5
            * (3 : ℝ) ^ (dOf q σ).primeFactors.card
            * ((sqfreePart q * dOf q σ * gOf q σ).divisors.card : ℝ) ^ 8
            * ((H : ℝ) ^ 6 / ((dOf q σ : ℝ) * gOf q σ)
                + (H : ℝ) ^ 5 / (gOf q σ : ℝ)))
        ≤ ((10 : ℝ) ^ 5 * ((q.divisors.card : ℝ)) ^ 26)
            * ∑ σ ∈ Pset q, wOf q σ * ((H : ℝ) ^ 6 / ((dOf q σ : ℝ) * gOf q σ)
                + (H : ℝ) ^ 5 / (gOf q σ : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun σ hσ => ?_)
      have hB : (10 : ℝ) ^ 5 * (3 : ℝ) ^ (dOf q σ).primeFactors.card
            * ((sqfreePart q * dOf q σ * gOf q σ).divisors.card : ℝ) ^ 8
          ≤ (10 : ℝ) ^ 5 * ((q.divisors.card : ℝ)) ^ 26 := h4a σ hσ
      have hA : 0 ≤ (H : ℝ) ^ 6 / ((dOf q σ : ℝ) * gOf q σ)
          + (H : ℝ) ^ 5 / (gOf q σ : ℝ) := hA0 σ hσ
      calc wOf q σ * (((10 : ℝ) ^ 5 * (3 : ℝ) ^ (dOf q σ).primeFactors.card
              * ((sqfreePart q * dOf q σ * gOf q σ).divisors.card : ℝ) ^ 8)
              * ((H : ℝ) ^ 6 / ((dOf q σ : ℝ) * gOf q σ)
                  + (H : ℝ) ^ 5 / (gOf q σ : ℝ)))
          = (wOf q σ * ((10 : ℝ) ^ 5 * (3 : ℝ) ^ (dOf q σ).primeFactors.card
                * ((sqfreePart q * dOf q σ * gOf q σ).divisors.card : ℝ) ^ 8))
              * ((H : ℝ) ^ 6 / ((dOf q σ : ℝ) * gOf q σ)
                  + (H : ℝ) ^ 5 / (gOf q σ : ℝ)) := by ring
        _ ≤ (wOf q σ * ((10 : ℝ) ^ 5 * ((q.divisors.card : ℝ)) ^ 26))
              * ((H : ℝ) ^ 6 / ((dOf q σ : ℝ) * gOf q σ)
                  + (H : ℝ) ^ 5 / (gOf q σ : ℝ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB (hw0 σ hσ)) hA
        _ = ((10 : ℝ) ^ 5 * ((q.divisors.card : ℝ)) ^ 26)
              * (wOf q σ * ((H : ℝ) ^ 6 / ((dOf q σ : ℝ) * gOf q σ)
                  + (H : ℝ) ^ 5 / (gOf q σ : ℝ))) := by ring
    have h10 : (10 : ℝ) ^ (8 * (highPrimeSet q).card)
        ≤ ((q.divisors.card : ℝ)) ^ 27 := by
      have h2ω := (hDvd hq0 hd0).1
      have h108 : ((10 : ℝ) ^ 8) ≤ ((2 : ℝ) ^ 27) := by norm_num
      calc (10 : ℝ) ^ (8 * (highPrimeSet q).card)
          = (((10 : ℝ) ^ 8) ^ (highPrimeSet q).card) := by rw [← pow_mul]
        _ ≤ (((2 : ℝ) ^ 27) ^ (highPrimeSet q).card) :=
            pow_le_pow_left₀ (by positivity) h108 _
        _ = (((2 : ℝ) ^ (highPrimeSet q).card) ^ 27) := by
            rw [← pow_mul, ← pow_mul]; congr 1; omega
        _ ≤ ((q.divisors.card : ℝ)) ^ 27 :=
            pow_le_pow_left₀ (by positivity) h2ω 27
    have hge := (hDvd hq0 hd0).2.1
    have hτ55 : ((q.divisors.card : ℝ)) ^ 55 ≤ ((q.divisors.card : ℝ)) ^ 58 :=
      pow_le_pow_right₀ hτ1 (by norm_num)
    have hstep2 : ((10 : ℝ) ^ 5 * ((q.divisors.card : ℝ)) ^ 26)
          * ((10 : ℝ) ^ (8 * (highPrimeSet q).card)
              * (∏ p : ↥(highPrimeSet q), ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2) * Y)
        ≤ (10 : ℝ) ^ 5 * ((q.divisors.card : ℝ)) ^ 58 * Y := by
      have h1 : (10 : ℝ) ^ (8 * (highPrimeSet q).card) * ((q.divisors.card : ℝ)) ^ 26
          ≤ ((q.divisors.card : ℝ)) ^ 27 * ((q.divisors.card : ℝ)) ^ 26 :=
        mul_le_mul_of_nonneg_right h10 (by positivity)
      calc ((10 : ℝ) ^ 5 * ((q.divisors.card : ℝ)) ^ 26)
            * ((10 : ℝ) ^ (8 * (highPrimeSet q).card)
                * (∏ p : ↥(highPrimeSet q), ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2) * Y)
          ≤ ((10 : ℝ) ^ 5 * ((q.divisors.card : ℝ)) ^ 26)
              * (((q.divisors.card : ℝ)) ^ 27 * ((q.divisors.card : ℝ)) ^ 2 * Y) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine mul_le_mul_of_nonneg_right ?_ hY0
            exact mul_le_mul h10 hge (by positivity) (by positivity)
        _ = (10 : ℝ) ^ 5 * ((q.divisors.card : ℝ)) ^ 55 * Y := by ring
        _ ≤ (10 : ℝ) ^ 5 * ((q.divisors.card : ℝ)) ^ 58 * Y :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ55 (by positivity)) hY0
    calc ∑ fg ∈ uniqSet H i, ‖corr6 q χ fg.1 fg.2‖
        ≤ 6 ^ (lowPrimeSet q).card * Real.sqrt (q : ℝ)
            * ∑ fg ∈ uniqSet H i, sqrtGcdW (sqfreePart q) i (shift6 fg)
                * ∏ p ∈ highPrimeSet q, localFactor p (q.factorization p) (aOf fg) (bOf fg) := hs1
      _ = 6 ^ (lowPrimeSet q).card * Real.sqrt (q : ℝ)
            * (∑ σ ∈ Pset q, ∑ fg ∈ uniqSet H i, sqrtGcdW (sqfreePart q) i (shift6 fg)
                * (wOf q σ * indOf q (aOf fg) (bOf fg) σ)) := by rw [hs2]
      _ ≤ 6 ^ (lowPrimeSet q).card * Real.sqrt (q : ℝ)
            * ∑ σ ∈ Pset q, wOf q σ * ((10 : ℝ) ^ 5
                * (3 : ℝ) ^ (dOf q σ).primeFactors.card
                * ((sqfreePart q * dOf q σ * gOf q σ).divisors.card : ℝ) ^ 8
                * ((H : ℝ) ^ 6 / ((dOf q σ : ℝ) * gOf q σ)
                    + (H : ℝ) ^ 5 / (gOf q σ : ℝ))) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun σ hσ => hs3 σ hσ)) ?_
            positivity
      _ ≤ 6 ^ (lowPrimeSet q).card * Real.sqrt (q : ℝ)
            * (((10 : ℝ) ^ 5 * ((q.divisors.card : ℝ)) ^ 26)
                * ∑ σ ∈ Pset q, wOf q σ * ((H : ℝ) ^ 6 / ((dOf q σ : ℝ) * gOf q σ)
                    + (H : ℝ) ^ 5 / (gOf q σ : ℝ))) := by
            refine mul_le_mul_of_nonneg_left hsumstep (by positivity)
      _ ≤ 6 ^ (lowPrimeSet q).card * Real.sqrt (q : ℝ)
            * (((10 : ℝ) ^ 5 * ((q.divisors.card : ℝ)) ^ 26)
                * ((10 : ℝ) ^ (8 * (highPrimeSet q).card)
                    * (∏ p : ↥(highPrimeSet q), ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2)
                    * Y)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left h4b (by positivity)
      _ ≤ 6 ^ (lowPrimeSet q).card * Real.sqrt (q : ℝ)
            * ((10 : ℝ) ^ 5 * ((q.divisors.card : ℝ)) ^ 58 * Y) := by
            refine mul_le_mul_of_nonneg_left hstep2 (by positivity)
      _ = 6 ^ (lowPrimeSet q).card * Real.sqrt (q : ℝ) * (10 : ℝ) ^ 5
            * ((q.divisors.card : ℝ)) ^ 58 * Y := by ring
  have hsum_eq : (∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
        (if IsSingleton6 (f, g) then ‖corr6 q χ f g‖ else 0))
      = ∑ fg : (Fin 3 → Fin H) × (Fin 3 → Fin H),
          (if IsSingleton6 fg then ‖corr6 q χ fg.1 fg.2‖ else 0) := by
    rw [← Finset.sum_product (s := (Finset.univ : Finset (Fin 3 → Fin H)))
          (t := (Finset.univ : Finset (Fin 3 → Fin H)))
          (f := fun fg : (Fin 3 → Fin H) × (Fin 3 → Fin H) =>
            if IsSingleton6 fg then ‖corr6 q χ fg.1 fg.2‖ else 0)]
    rw [Finset.univ_product_univ]
  rw [hsum_eq]
  have hpt : ∀ fg : (Fin 3 → Fin H) × (Fin 3 → Fin H),
      (if IsSingleton6 fg then ‖corr6 q χ fg.1 fg.2‖ else 0)
        ≤ ∑ i : Fin 6, (if (∀ i', i' ≠ i → shift6 fg i ≠ shift6 fg i')
            then ‖corr6 q χ fg.1 fg.2‖ else 0) := by
    intro fg
    by_cases h : IsSingleton6 fg
    · rw [if_pos h]
      obtain ⟨i0, hi0⟩ := h
      have h1 : ‖corr6 q χ fg.1 fg.2‖
          ≤ (if (∀ i', i' ≠ i0 → shift6 fg i0 ≠ shift6 fg i')
              then ‖corr6 q χ fg.1 fg.2‖ else 0) := by rw [if_pos hi0]
      exact h1.trans
        (Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin 6 => if (∀ i', i' ≠ j → shift6 fg j ≠ shift6 fg i')
            then ‖corr6 q χ fg.1 fg.2‖ else 0)
          (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ i0))
    · rw [if_neg h]
      exact Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
  refine (Finset.sum_le_sum (fun fg _ => hpt fg)).trans ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_le_sum
      (f := fun i : Fin 6 => ∑ fg : (Fin 3 → Fin H) × (Fin 3 → Fin H),
        (if (∀ i', i' ≠ i → shift6 fg i ≠ shift6 fg i')
          then ‖corr6 q χ fg.1 fg.2‖ else 0))
      (g := fun _i : Fin 6 => 6 ^ (lowPrimeSet q).card * Real.sqrt (q : ℝ) * (10 : ℝ) ^ 5
          * ((q.divisors.card : ℝ)) ^ 58 * Y)
      (fun i _ => ?_)).trans ?_
  · have hconv : (∑ fg ∈ uniqSet H i, ‖corr6 q χ fg.1 fg.2‖)
        = ∑ fg : (Fin 3 → Fin H) × (Fin 3 → Fin H),
            (if (∀ i', i' ≠ i → shift6 fg i ≠ shift6 fg i')
              then ‖corr6 q χ fg.1 fg.2‖ else 0) := by
      rw [show uniqSet H i = (Finset.univ.filter
        (fun fg : (Fin 3 → Fin H) × (Fin 3 → Fin H) =>
          ∀ i', i' ≠ i → shift6 fg i ≠ shift6 fg i')) from rfl, Finset.sum_filter]
    rw [← hconv]
    exact hper i
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h6tau : ((6 : ℝ) ^ (lowPrimeSet q).card) * ((q.divisors.card : ℝ)) ^ 58
        ≤ (max Cτ 1) ^ 110 * (q : ℝ) ^ ε := by
      have hCmax : (1 : ℝ) ≤ max Cτ 1 := le_max_right _ _
      have hstep : ((q.divisors.card : ℝ)) ^ 61 ≤ (max Cτ 1) ^ 110 * (q : ℝ) ^ ε := by
        have hle1 : (q.divisors.card : ℝ) ≤ (max Cτ 1) * (q : ℝ) ^ (ε / 200) := by
          calc (q.divisors.card : ℝ) ≤ Cτ * (q : ℝ) ^ (ε / 200) := hCτ q
            _ ≤ (max Cτ 1) * (q : ℝ) ^ (ε / 200) :=
                mul_le_mul_of_nonneg_right (le_max_left Cτ 1) (Real.rpow_nonneg hqnn _)
        have hsl : ((q.divisors.card : ℝ)) ^ 61
            ≤ ((max Cτ 1) * (q : ℝ) ^ (ε / 200)) ^ 61 :=
          pow_le_pow_left₀ (by positivity) hle1 61
        have hfac : ((max Cτ 1) * (q : ℝ) ^ (ε / 200)) ^ 61
            = (max Cτ 1) ^ 61 * ((q : ℝ) ^ (ε / 200)) ^ 61 := by rw [mul_pow]
        have hrpow : ((q : ℝ) ^ (ε / 200)) ^ 61 ≤ (q : ℝ) ^ ε := by
          rw [← Real.rpow_natCast ((q : ℝ) ^ (ε / 200)) 61, ← Real.rpow_mul hqnn]
          exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
        have hCp : (max Cτ 1) ^ 61 ≤ (max Cτ 1) ^ 110 :=
          pow_le_pow_right₀ hCmax (by norm_num)
        calc ((q.divisors.card : ℝ)) ^ 61
            ≤ ((max Cτ 1) * (q : ℝ) ^ (ε / 200)) ^ 61 := hsl
          _ = (max Cτ 1) ^ 61 * ((q : ℝ) ^ (ε / 200)) ^ 61 := hfac
          _ ≤ (max Cτ 1) ^ 110 * (q : ℝ) ^ ε :=
              mul_le_mul hCp hrpow (by positivity) (by positivity)
      calc ((6 : ℝ) ^ (lowPrimeSet q).card) * ((q.divisors.card : ℝ)) ^ 58
          ≤ ((q.divisors.card : ℝ)) ^ 3 * ((q.divisors.card : ℝ)) ^ 58 :=
            mul_le_mul_of_nonneg_right (six_pow_low_le_tau hq0) (by positivity)
        _ = ((q.divisors.card : ℝ)) ^ 61 := by ring
        _ ≤ (max Cτ 1) ^ 110 * (q : ℝ) ^ ε := hstep
    have hsqrtY : Real.sqrt (q : ℝ) * Y
        ≤ 2 * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ)) := by
      rw [hY]; exact hFin (q := q) (H := H)
    calc 6 * (6 ^ (lowPrimeSet q).card * Real.sqrt (q : ℝ) * (10 : ℝ) ^ 5
          * ((q.divisors.card : ℝ)) ^ 58 * Y)
        = (6 * (10 : ℝ) ^ 5)
            * (((6 : ℝ) ^ (lowPrimeSet q).card * ((q.divisors.card : ℝ)) ^ 58)
                * (Real.sqrt (q : ℝ) * Y)) := by ring
      _ ≤ (6 * (10 : ℝ) ^ 5) * (((max Cτ 1) ^ 110 * (q : ℝ) ^ ε)
            * (2 * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul h6tau hsqrtY (by positivity) (by positivity)
      _ = 12 * (10 : ℝ) ^ 5 * (max Cτ 1) ^ 110 * (q : ℝ) ^ ε
            * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ)) := by ring
      _ ≤ max 1 (12 * (10 : ℝ) ^ 5 * (max Cτ 1) ^ 110) * (q : ℝ) ^ ε
            * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hqe


/-- **U13 of `BURGESS_ROUTE_LEAD.md`: the sixth-moment singleton-pair bound.**

Assembly of (1) the CRT factorisation of the correlation over the prime powers of `q`
(`corr6_norm_le_prod_local`), with the local inputs `local_prime_powWeight` (`e = 1`), Theorem L
(`localFactor_bound_ge5`) and Theorem L' (`localFactor_bound_small`) at `e ≥ 2`; (2) the expansion
of `∏_p localFactor` into the choices `σ = (s_p, j_p)`; (3) the counting Theorem F (`frame_count`)
with `m = sqfreePart q`, `d = d_σ = ∏ p^{s_p}`, `g = g_σ = ∏ p^{j_p}`; (4) the per-prime sums
`menuW_univ`; and (5) the divisor bound `card_divisors_le_rpow` together with the final real split
`√q (H^6 + H^5 q^{1/6}) ≤ 2 (q H^3 + H^6 √q)`. -/
theorem singleton_sum_all {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      χ ≠ 1 → ∀ H : ℕ,
        ∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
          (if IsSingleton6 (f, g) then ‖corr6 q χ f g‖ else 0)
        ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ)) :=
  singleton_sum_all_aux
    (fun p _ χ hχ a b i => local_prime_powOne_bound χ hχ a b i)
    (fun {p e} _ hp5 he χ hχ a b i hi => localFactor_bound_ge5 hp5 he χ hχ a b i hi)
    (fun {p e} _ hp3 he χ hχ a b i hi =>
      Work.ZeroFreeTables.P9F.localFactor_bound_small_aux hp3 he χ hχ a b i hi)
    (fun {H} i {m d g} hm hmd hmg hd hg =>
      Work.ZeroFreeTables.P9F.frame_stub_aux (H := H) i hm hmd hmg hd hg)
    (fun q i v => sqrtGcdW_prod_le_sqfreePart q i v)
    (fun {q} hq => sqrt_prod_factorization hq)
    (fun {q d g} hq h => divisors_card_pow_le hq h)
    (fun {q} hq σ hσ => sqfreePart_frame_hyp hq σ hσ)
    (fun {q} hq {d} hd => divisor_bounds_high hq hd)
    (fun {q H} => sqrt_mul_sum_le (q := q) (H := H))
    hε

end Work.P9Chain
