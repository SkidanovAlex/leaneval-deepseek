import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators
open Finset

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

noncomputable section

namespace Commons.NumberTheory.Nat

/-! ## Generic real-analysis helpers -/

/-- `Real.rpow` factors over Finset products (nonnegative bases). -/
lemma rpow_prod_finset {ι : Type*} (s : Finset ι) (x : ι → ℝ) (r : ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    Real.rpow (∏ i ∈ s, x i) r = ∏ i ∈ s, Real.rpow (x i) r := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro a s has ih
    rw [Finset.prod_insert has, Finset.prod_insert has]
    have hxpos : 0 ≤ ∏ x_1 ∈ s, x x_1 := Finset.prod_nonneg (fun i _ => hx i)
    have hm : Real.rpow (x a * (∏ x_1 ∈ s, x x_1)) r
        = Real.rpow (x a) r * Real.rpow (∏ x_1 ∈ s, x x_1) r := by
      exact Real.mul_rpow (x := x a) (y := ∏ x_1 ∈ s, x x_1) (z := r) (hx a) hxpos
    rw [hm]
    rw [ih]

/-- `Real.rpow` factors over whole-type products (nonnegative bases). -/
lemma rpow_prod_univ {ι : Type*} [Fintype ι] (x : ι → ℝ) (r : ℝ) (hx : ∀ i, 0 ≤ x i) :
    Real.rpow (∏ i, x i) r = ∏ i, Real.rpow (x i) r := by
  simpa using (rpow_prod_finset (Finset.univ : Finset ι) x r hx)

/-- cast of a `Fin c`-indexed natural product equals the product of the casts -/
lemma cast_prod_coord (c : ℕ) (t : Fin c → ℕ) :
    (((∏ i : Fin c, t i : ℕ) : ℕ) : ℝ) = ∏ i : Fin c, (t i : ℝ) := by
  simp

/-- weight of a product of coordinates factors into the product of coordinate weights -/
lemma rpow_coord_prod (s : ℝ) (c : ℕ) (t : Fin c → ℕ) :
    Real.rpow (((∏ i : Fin c, t i) : ℕ) : ℝ) (-s) =
      ∏ i : Fin c, Real.rpow ((t i : ℕ) : ℝ) (-s) := by
  rw [cast_prod_coord]
  exact rpow_prod_univ (fun i : Fin c => (t i : ℝ)) (-s) (fun i => by positivity)

/-- Sum over a set of an injectively-mapped nonnegative function is at most the
sum over the codomain set. -/
lemma sum_le_sum_of_injective_nonneg {α β : Type*} (s : Finset α) (t : Finset β)
    (φ : α → β) (v : β → ℝ) (hinj : Set.InjOn φ (↑s : Set α))
    (hφ : ∀ x ∈ s, φ x ∈ t) (hv : ∀ y ∈ t, 0 ≤ v y) :
    (∑ x ∈ s, v (φ x)) ≤ ∑ y ∈ t, v y := by
  classical
  calc
    (∑ x ∈ s, v (φ x)) = ∑ y ∈ s.image φ, v y := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ y ∈ t, v y := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (s := s.image φ) (t := t)
        · intro y hy
          rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
          exact hφ x hx
        · intro y hy hy2
          exact hv y hy

/-- Expansion of the `c`-th power of a sum as the sum over `c`-tuples of products. -/
lemma sum_pow_eq_piFinset (c : ℕ) (S : Finset ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ S, f k) ^ c = ∑ t ∈ Fintype.piFinset (fun _ : Fin c => S), ∏ i : Fin c, f (t i) := by
  calc
    (∑ k ∈ S, f k) ^ c = ∏ i : Fin c, (∑ k ∈ S, f k) := by
        symm
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = ∑ t ∈ Fintype.piFinset (fun _ : Fin c => S), ∏ i : Fin c, f (t i) := by
        rw [Finset.prod_univ_sum]

/-! ## The box of `c`-tuples and its fibers -/

/-- box `{1,…,A}^c` of `c`-tuples of positive integers -/
def colorBox (c A : ℕ) : Finset (Fin c → ℕ) :=
  Fintype.piFinset (fun _ : Fin c => Finset.Icc 1 A)

/-- tuples in the box whose product equals `a` -/
def colorFiber (c A a : ℕ) : Finset (Fin c → ℕ) :=
  (colorBox c A).filter (fun t => (∏ i : Fin c, t i) = a)

lemma mem_colorFiber_iff (c A a : ℕ) (t : Fin c → ℕ) :
    t ∈ colorFiber c A a ↔ (∀ i, t i ∈ Finset.Icc 1 A) ∧ (∏ i, t i) = a := by
  simp [colorFiber, colorBox, Fintype.mem_piFinset]

/-- the sum over the box of products equals the `c`-th power of the coordinate sum -/
lemma box_sum_pow (c A : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 A, f k) ^ c = ∑ t ∈ colorBox c A, ∏ i : Fin c, f (t i) := by
  unfold colorBox
  exact sum_pow_eq_piFinset (c := c) (S := Finset.Icc 1 A) (f := f)

/-- collapse of the double sum over fibers into a single indicator sum over the box -/
lemma doubleSum_eq_filterSum (c A : ℕ) (S : Finset ℕ) (v : (Fin c → ℕ) → ℝ) :
    (∑ a ∈ S, ∑ t ∈ colorFiber c A a, v t) =
      ∑ t ∈ colorBox c A, (if (∏ i : Fin c, t i) ∈ S then v t else 0) := by
  classical
  calc
    (∑ a ∈ S, ∑ t ∈ colorFiber c A a, v t)
        = ∑ a ∈ S, ∑ t ∈ colorBox c A,
            (if (∏ i : Fin c, t i) = a then v t else 0) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [← Finset.sum_filter]
            rfl
    _ = ∑ t ∈ colorBox c A, ∑ a ∈ S,
            (if (∏ i : Fin c, t i) = a then v t else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ t ∈ colorBox c A, (if (∏ i : Fin c, t i) ∈ S then v t else 0) := by
            apply Finset.sum_congr rfl
            intro t ht
            calc
              (∑ a ∈ S, (if (∏ i : Fin c, t i) = a then v t else 0))
                  = ∑ a ∈ S, (if a = (∏ i : Fin c, t i) then v t else 0) := by
                      apply Finset.sum_congr rfl
                      intro a ha
                      by_cases h : (∏ i : Fin c, t i) = a
                      · simp [h]
                      · have ha' : ¬ a = (∏ i : Fin c, t i) := by
                          intro hh
                          exact h hh.symm
                        simp [h, ha']
              _ = if (∏ i : Fin c, t i) ∈ S then v t else 0 := by
                      exact Finset.sum_ite_eq' (s := S) (a := (∏ i : Fin c, t i))
                        (b := fun _ : ℕ => v t)

/-! ## Colorings of the prime factors and their induced tuples -/

/-- the `c`-tuple associated to a coloring of the prime factors of `a` -/
def colorTuple (a c : ℕ) (f : a.primeFactors → Fin c) : Fin c → ℕ :=
  fun j => ∏ p ∈ a.primeFactors.attach with f p = j, (p : ℕ) ^ a.factorization (p : ℕ)

/-- product of the `c` entries equals `a` -/
lemma prod_colorTuple (a c : ℕ) (ha : a ≠ 0) (f : a.primeFactors → Fin c) :
    (∏ j : Fin c, colorTuple a c f j) = a := by
  calc
    (∏ j : Fin c, colorTuple a c f j)
        = ∏ p ∈ a.primeFactors.attach, (p : ℕ) ^ a.factorization (p : ℕ) := by
            simpa [colorTuple] using
              (Finset.prod_fiberwise (s := a.primeFactors.attach) (g := f)
                (f := fun p : ↥(a.primeFactors) => (p : ℕ) ^ a.factorization (p : ℕ)))
    _ = ∏ p ∈ a.primeFactors, p ^ a.factorization p := by
            simpa using (Finset.prod_attach (s := a.primeFactors)
              (f := fun p : ℕ => p ^ a.factorization p))
    _ = a := by
            calc
              (∏ p ∈ a.primeFactors, p ^ a.factorization p)
                  = a.factorization.prod (fun p e => p ^ e) := by
                      simp [Finsupp.prod, Nat.support_factorization]
              _ = a := by exact Nat.prod_factorization_pow_eq_self (n := a) ha

/-- each entry divides `a` -/
lemma colorTuple_dvd (a c : ℕ) (ha : a ≠ 0) (f : a.primeFactors → Fin c) (j : Fin c) :
    colorTuple a c f j ∣ a := by
  have h := Finset.dvd_prod_of_mem (s := (Finset.univ : Finset (Fin c)))
      (f := fun j' => colorTuple a c f j') (Finset.mem_univ j)
  simpa [prod_colorTuple a c ha f] using h

/-- the exponent of a prime factor of `a` is positive -/
lemma factorization_ne_zero_of_mem_primeFactors (a : ℕ) {p : ℕ} (hp : p ∈ a.primeFactors) :
    a.factorization p ≠ 0 := by
  have hsp : p ∈ a.factorization.support := by
    rw [Nat.support_factorization]
    exact hp
  exact Finsupp.mem_support_iff.mp hsp

/-- each entry is at least `1` -/
lemma colorTuple_ge_one (a c : ℕ) (f : a.primeFactors → Fin c) (j : Fin c) :
    1 ≤ colorTuple a c f j := by
  unfold colorTuple
  apply Finset.one_le_prod₀
  intro p hp
  have hpp : Nat.Prime (p : ℕ) := (Nat.mem_primeFactors.mp p.2).1
  have hp1 : 1 ≤ (p : ℕ) := le_of_lt (Nat.Prime.one_lt hpp)
  exact pow_le_pow_right₀ (a := (p : ℕ)) (m := 0) (n := a.factorization (p : ℕ)) hp1 (by omega)

/-- each entry is at most `a` -/
lemma colorTuple_le_a (a c : ℕ) (ha : a ≠ 0) (f : a.primeFactors → Fin c) (j : Fin c) :
    colorTuple a c f j ≤ a := by
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero ha) (colorTuple_dvd a c ha f j)

/-- coordinates lie in the box `{1,…,A}` when `a ≤ A` -/
lemma colorTuple_mem_Icc (c A a : ℕ) (haA : a ≤ A) (ha : a ≠ 0)
    (f : a.primeFactors → Fin c) (j : Fin c) :
    colorTuple a c f j ∈ Finset.Icc 1 A := by
  exact Finset.mem_Icc.mpr
    ⟨colorTuple_ge_one a c f j, le_trans (colorTuple_le_a a c ha f j) haA⟩

/-- the tuple induced by a coloring lies in the fiber over `a` -/
lemma colorTuple_mem_colorFiber (c A a : ℕ) (haA : a ≤ A) (ha : a ≠ 0)
    (f : a.primeFactors → Fin c) :
    colorTuple a c f ∈ colorFiber c A a := by
  rw [mem_colorFiber_iff]
  constructor
  · intro i
    exact colorTuple_mem_Icc c A a haA ha f i
  · exact prod_colorTuple a c ha f

/-- the prime `p` divides the box assigned its color -/
lemma colorTuple_prime_dvd (a c : ℕ) (f : a.primeFactors → Fin c) (p : ↥(a.primeFactors)) :
    (p : ℕ) ∣ colorTuple a c f (f p) := by
  unfold colorTuple
  have hmem : p ∈ (a.primeFactors.attach).filter (fun x => f x = f p) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_attach a.primeFactors p, rfl⟩
  have hdv := Finset.dvd_prod_of_mem
    (s := (a.primeFactors.attach).filter (fun x => f x = f p))
    (f := fun x : ↥(a.primeFactors) => (x : ℕ) ^ a.factorization (x : ℕ)) hmem
  have hne : a.factorization (p : ℕ) ≠ 0 := factorization_ne_zero_of_mem_primeFactors a p.2
  have he : 1 ≤ a.factorization (p : ℕ) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
  have hp_div_pow : (p : ℕ) ∣ (p : ℕ) ^ a.factorization (p : ℕ) := by
    simpa using (pow_dvd_pow (p : ℕ) (m := 1) (n := a.factorization (p : ℕ)) he)
  exact dvd_trans hp_div_pow hdv

/-- distinct colorings induce distinct tuples -/
lemma colorTuple_injective (a c : ℕ) : Function.Injective (colorTuple a c) := by
  intro f g hfg
  funext p
  by_contra hne
  let j : Fin c := f p
  have hjg : g p ≠ j := by
    intro h
    exact hne (by simpa [j] using h.symm)
  have hfgj : colorTuple a c f j = colorTuple a c g j := congrFun hfg j
  have hpf : (p : ℕ) ∣ colorTuple a c f j := by
    simpa [j] using (colorTuple_prime_dvd a c f p)
  have hpg : ¬ (p : ℕ) ∣ colorTuple a c g j := by
    intro hpd
    let G : Finset (↥(a.primeFactors)) := (a.primeFactors.attach).filter (fun x => g x = j)
    have hdvdG : (p : ℕ) ∣ ∏ x ∈ G, (x : ℕ) ^ a.factorization (x : ℕ) := by
      unfold colorTuple at hpd
      simpa [G] using hpd
    have hpp : Nat.Prime (p : ℕ) := (Nat.mem_primeFactors.mp p.2).1
    have hiff := Prime.dvd_finsetProd_iff (S := G) (Nat.Prime.prime hpp)
      (g := fun x : ↥(a.primeFactors) => (x : ℕ) ^ a.factorization (x : ℕ))
    rcases hiff.mp hdvdG with ⟨x, hxG, hxpd⟩
    have hxne : x ≠ p := by
      intro hxeq
      have hgx : g x = j := (Finset.mem_filter.mp hxG).2
      exact hjg (by simpa [hxeq] using hgx)
    have hvalne : (x : ℕ) ≠ (p : ℕ) := by
      intro hv
      exact hxne (Subtype.ext hv)
    have hxprime : Nat.Prime (x : ℕ) := (Nat.mem_primeFactors.mp x.2).1
    have hiff2 := Nat.prime_dvd_prime_iff_eq hpp hxprime
    have hnpdx : ¬ (p : ℕ) ∣ (x : ℕ) := by
      intro hd
      exact hvalne ((hiff2.mp hd).symm)
    have hxpd_m : (p : ℕ) ∣ (x : ℕ) := hpp.dvd_of_dvd_pow hxpd
    exact hnpdx hxpd_m
  rw [hfgj] at hpf
  exact hpg hpf

/-- injectivity into the fiber -/
lemma colorTuple_inj_fiber (c A a : ℕ) (haA : a ≤ A) (ha : a ≠ 0) :
    Function.Injective
      (fun f : a.primeFactors → Fin c =>
        (⟨colorTuple a c f, colorTuple_mem_colorFiber c A a haA ha f⟩ : colorFiber c A a)) := by
  intro f g hfg
  have htu : colorTuple a c f = colorTuple a c g := congrArg Subtype.val hfg
  exact colorTuple_injective a c htu

/-- `c ^ ω(a)` colorings fit into the ordered factorizations of `a` in the box -/
lemma coloring_card_le_fiber (c A a : ℕ) (hc : 1 ≤ c) (ha : a ∈ Finset.Icc 1 A) :
    c ^ (a.primeFactors).card ≤ (colorFiber c A a).card := by
  classical
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  have haA : a ≤ A := (Finset.mem_Icc.mp ha).2
  have ha0 : a ≠ 0 := by omega
  have hcard : (Fintype.card (a.primeFactors → Fin c)) = c ^ (a.primeFactors).card := by
    rw [Fintype.card_fun, Fintype.card_fin]
    congr 1
    exact Fintype.card_coe a.primeFactors
  have hinj := colorTuple_inj_fiber c A a haA ha0
  have hle := Fintype.card_le_of_injective (fun f : a.primeFactors → Fin c =>
    (⟨colorTuple a c f, colorTuple_mem_colorFiber c A a haA ha0 f⟩ : colorFiber c A a)) hinj
  rw [hcard, Fintype.card_coe] at hle
  exact hle

/-- Power-weighted double-counting bound for the `ω`-coloring sum -/
theorem omega_color_sum_weighted_le (c A : ℕ) (hc : 1 ≤ c) (s : ℝ) (hs : 0 ≤ s) :
    (∑ a ∈ Finset.Icc 1 A, (c : ℝ) ^ (a.primeFactors).card * Real.rpow (a : ℝ) (-s)) ≤
      (∑ k ∈ Finset.Icc 1 A, Real.rpow (k : ℝ) (-s)) ^ c := by
  classical
  let S : Finset ℕ := Finset.Icc 1 A
  let w : ℕ → ℝ := fun k => Real.rpow (k : ℝ) (-s)
  let v : (Fin c → ℕ) → ℝ := fun t => ∏ i : Fin c, Real.rpow ((t i : ℕ) : ℝ) (-s)
  have hw0 : ∀ k : ℕ, 0 ≤ w k := by
    intro k
    unfold w
    exact Real.rpow_nonneg (by positivity) (-s)
  have hv0 : ∀ t : Fin c → ℕ, 0 ≤ v t := by
    intro t
    unfold v
    exact Finset.prod_nonneg (fun i hi => Real.rpow_nonneg (by positivity) (-s))
  calc
    (∑ a ∈ Finset.Icc 1 A, (c : ℝ) ^ (a.primeFactors).card * Real.rpow (a : ℝ) (-s))
        = ∑ a ∈ S, (c : ℝ) ^ (a.primeFactors).card * w a := by
            simp [S, w]
    _ ≤ ∑ a ∈ S, ((colorFiber c A a).card : ℝ) * w a := by
            apply Finset.sum_le_sum
            intro a ha
            have hcc : (c : ℝ) ^ (a.primeFactors).card ≤ (colorFiber c A a).card := by
              exact_mod_cast coloring_card_le_fiber c A a hc ha
            exact mul_le_mul_of_nonneg_right hcc (hw0 a)
    _ = ∑ a ∈ S, ∑ t ∈ colorFiber c A a, w a := by
            apply Finset.sum_congr rfl
            intro a ha
            calc
              ((colorFiber c A a).card : ℝ) * w a
                  = ∑ _t ∈ colorFiber c A a, w a := by
                      rw [Finset.sum_const, nsmul_eq_mul]
              _ = ∑ t ∈ colorFiber c A a, w a := by
                      rfl
    _ = ∑ a ∈ S, ∑ t ∈ colorFiber c A a, v t := by
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro t ht
            have hpx : (∏ i : Fin c, t i) = a := (mem_colorFiber_iff c A a t).1 ht |>.2
            unfold w v
            calc
              Real.rpow (a : ℝ) (-s) = Real.rpow (((∏ i : Fin c, t i) : ℕ) : ℝ) (-s) := by rw [hpx]
              _ = ∏ i : Fin c, Real.rpow ((t i : ℕ) : ℝ) (-s) := by
                    rw [rpow_coord_prod]
    _ = ∑ t ∈ colorBox c A, (if (∏ i : Fin c, t i) ∈ S then v t else 0) := by
            exact doubleSum_eq_filterSum c A S v
    _ ≤ ∑ t ∈ colorBox c A, v t := by
            apply Finset.sum_le_sum
            intro t ht
            by_cases h : (∏ i : Fin c, t i) ∈ S
            · simp [h]
            · simp [h, hv0 t]
    _ = (∑ k ∈ Finset.Icc 1 A, Real.rpow (k : ℝ) (-s)) ^ c := by
            calc
              (∑ t ∈ colorBox c A, v t)
                  = ∑ t ∈ colorBox c A, ∏ i : Fin c, Real.rpow ((t i : ℕ) : ℝ) (-s) := by
                      rfl
              _ = (∑ k ∈ Finset.Icc 1 A, Real.rpow (k : ℝ) (-s)) ^ c := by
                      rw [box_sum_pow (c := c) (A := A) (f := fun k : ℕ => Real.rpow (k : ℝ) (-s))]

end Commons.NumberTheory.Nat