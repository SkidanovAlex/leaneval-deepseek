import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Series
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Foundations for the degree induction of Milne's Lemma 2.11

This file sets up the vocabulary for the proof of `existsUnique_lubinTate_solution`
(Milne, *Classical Field Theory*, Lemma I.2.11): the series `D φ = f ∘ φ - φ ∘ g`,
the predicate `OrderGe k f` ("all coefficients of total degree `< k` vanish") and its
calculus (closure under sums, products, powers), the "top-degree" lemmas for products and
powers of series of positive order, the finitary coefficient formula for substitutions,
and the resulting "gain" lemma for substitutions.
-/

open MvPowerSeries

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

variable {A : Type u} [CommRing A]

/-- The family of series `X i ↦ g(X i)` (in `n` variables), used to substitute `g` into
each variable of an `n`-variable series. -/
noncomputable def gSub (n : ℕ) (g : MvPowerSeries (Fin 1) A) : Fin n → MvPowerSeries (Fin n) A :=
  fun i => MvPowerSeries.subst ![MvPowerSeries.X i] g

/-- **The discrepancy** `D φ = f ∘ φ - φ ∘ g` of Milne's Lemma 2.11.  The theorem
`existsUnique_lubinTate_solution` asserts that `D φ = 0` has a unique solution with
prescribed terms of degree `≤ 1`. -/
noncomputable def Dsub (n : ℕ) (f g : MvPowerSeries (Fin 1) A) (φ : MvPowerSeries (Fin n) A) :
    MvPowerSeries (Fin n) A :=
  MvPowerSeries.subst ![φ] f - MvPowerSeries.subst (gSub n g) φ

variable {σ : Type*} {τ : Type*}

/-- `OrderGe k f` means: every coefficient of `f` whose total degree is `< k` vanishes. -/
def OrderGe (k : ℕ) (f : MvPowerSeries σ A) : Prop :=
  ∀ s : σ →₀ ℕ, s.degree < k → MvPowerSeries.coeff s f = 0

theorem orderGe_zero (k : ℕ) : OrderGe (A := A) k (0 : MvPowerSeries σ A) := fun _ _ => rfl

theorem orderGe_sub_iff {k : ℕ} {f g : MvPowerSeries σ A} :
    OrderGe k (f - g) ↔ (∀ s : σ →₀ ℕ, s.degree < k →
      MvPowerSeries.coeff s f = MvPowerSeries.coeff s g) := by
  constructor
  · intro h s hs
    have h' := h s hs
    rw [map_sub, sub_eq_zero] at h'
    exact h'
  · intro h s hs
    rw [map_sub, h s hs, sub_self]

theorem OrderGe.mono {k l : ℕ} {f : MvPowerSeries σ A} (h : OrderGe k f) (hkl : l ≤ k) :
    OrderGe l f := fun s hs => h s (lt_of_lt_of_le hs hkl)

theorem OrderGe.add {k : ℕ} {f g : MvPowerSeries σ A} (hf : OrderGe k f) (hg : OrderGe k g) :
    OrderGe k (f + g) := by
  intro s hs
  simp only [map_add, hf s hs, hg s hs, add_zero]

theorem OrderGe.neg {k : ℕ} {f : MvPowerSeries σ A} (hf : OrderGe k f) : OrderGe k (-f) := by
  intro s hs
  simpa using hf s hs

theorem OrderGe.sub {k : ℕ} {f g : MvPowerSeries σ A} (hf : OrderGe k f) (hg : OrderGe k g) :
    OrderGe k (f - g) := by
  intro s hs
  simp only [map_sub, hf s hs, hg s hs, sub_zero]

theorem OrderGe.smul {k : ℕ} {f : MvPowerSeries σ A} (hf : OrderGe k f) (a : A) :
    OrderGe k (a • f) := by
  intro s hs
  simp only [map_smul, hf s hs, smul_zero]

theorem OrderGe.sum {ι : Type*} {k : ℕ} {s : Finset ι} {F : ι → MvPowerSeries σ A}
    (h : ∀ i ∈ s, OrderGe k (F i)) : OrderGe k (∑ i ∈ s, F i) := by
  classical
  intro c hc
  rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => h i hi c hc

theorem OrderGe.mul {k l : ℕ} {f g : MvPowerSeries σ A} (hf : OrderGe k f) (hg : OrderGe l g) :
    OrderGe (k + l) (f * g) := by
  classical
  intro s hs
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' : p.1 + p.2 = s := (Finset.HasAntidiagonal.mem_antidiagonal.mp hp)
  by_cases h1 : p.1.degree < k
  · rw [hf p.1 h1, zero_mul]
  · have h2 : p.2.degree < l := by
      have : p.1.degree + p.2.degree = s.degree := by rw [← hp', map_add]
      omega
    rw [hg p.2 h2, mul_zero]

theorem OrderGe.pow {k : ℕ} {f : MvPowerSeries σ A} (hf : OrderGe k f) (m : ℕ) :
    OrderGe (k * m) (f ^ m) := by
  induction m with
  | zero => intro s hs; simp at hs
  | succ m ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul hf

theorem OrderGe.pow_one {f : MvPowerSeries σ A} (hf : OrderGe 1 f) (m : ℕ) :
    OrderGe m (f ^ m) := by
  simpa using OrderGe.pow hf m

theorem OrderGe.prod {ι : Type*} {s : Finset ι} {F : ι → MvPowerSeries σ A} {k : ι → ℕ}
    (h : ∀ i ∈ s, OrderGe (k i) (F i)) : OrderGe (∑ i ∈ s, k i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => exact fun t ht => absurd ht (by simp)
  | cons a s ha ih =>
    rw [Finset.sum_cons ha, Finset.prod_cons ha]
    exact (h a (Finset.mem_cons_self a s)).mul (ih fun i hi => h i (Finset.mem_cons.mpr (Or.inr hi)))


/-- Substituting `π X i` for each variable is the rescaling by the constant family `π`. -/
theorem subst_C_mul_X_eq_rescale (a : τ → A) (f : MvPowerSeries τ A) :
    MvPowerSeries.subst (fun i => MvPowerSeries.C (a i) * MvPowerSeries.X i) f
      = MvPowerSeries.rescale a f := by
  rw [MvPowerSeries.rescale_eq_subst]
  congr 1
  ext i
  rw [Pi.smul_apply', MvPowerSeries.smul_eq_C_mul]

/-- A series of positive order has zero constant coefficient. -/
theorem OrderGe.constantCoeff {f : MvPowerSeries σ A} (hf : OrderGe 1 f) : f.constantCoeff = 0 := by
  have := hf 0 (by simp)
  simpa using this

/-- A series with zero constant coefficient has positive order. -/
theorem OrderGe.of_constantCoeff {f : MvPowerSeries σ A} (hf : f.constantCoeff = 0) :
    OrderGe 1 f := by
  intro s hs
  have hs0 : s.degree = 0 := by omega
  rw [show s = 0 from by
    ext i
    exact Nat.eq_zero_of_le_zero (hs0 ▸ Finsupp.le_degree i s)]
  simpa using hf

/-- The telescoping identity: `u^m - v^m = (u - v) * ∑_{i<m} u^i v^{m-1-i}`. -/
theorem geom_sum_factor (u v : MvPowerSeries σ A) (m : ℕ) :
    (u - v) * (∑ i ∈ Finset.range m, u ^ i * v ^ (m - 1 - i)) = u ^ m - v ^ m :=
  (Commute.all u v).mul_geom_sum₂ m

/-- **Top-degree behaviour of powers**: if `u ≡ v` modulo terms of degree `≥ m` and both have
zero constant coefficient, then `u^n ≡ v^n` modulo terms of degree `≥ (m-1) + n`. -/
theorem OrderGe.pow_sub_pow {u v : MvPowerSeries σ A} {m : ℕ} (hm : 1 ≤ m)
    (h : OrderGe m (u - v)) (hu : OrderGe 1 u) (hv : OrderGe 1 v) (n : ℕ) :
    OrderGe (m - 1 + n) (u ^ n - v ^ n) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simpa using orderGe_zero (A := A) (m - 1) (σ := σ)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have key : OrderGe (m + k) ((u - v) * ∑ i ∈ Finset.range (k + 1), u ^ i * v ^ (k + 1 - 1 - i)) := by
    refine OrderGe.mul h (OrderGe.sum fun i hi => ?_)
    have hi' : i ≤ k := by simpa [Nat.lt_succ_iff] using hi
    have hsum : i + (k + 1 - 1 - i) = k := by omega
    have := (OrderGe.pow_one hu i).mul (OrderGe.pow_one hv (k + 1 - 1 - i))
    rwa [hsum] at this
  rw [← geom_sum_factor u v (k + 1)]
  exact key.mono (by omega)

/-- **Top-degree behaviour of products of powers**: if `u i ≡ v i` modulo terms of degree `≥ m`
and `u i`, `v i` have positive order, then `∏ (u i)^{d i} ≡ ∏ (v i)^{d i}` modulo terms of
degree `≥ (m-1) + ∑ d i`. -/
theorem OrderGe.prod_pow_sub_prod_pow {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ι → ℕ)
    {u v : ι → MvPowerSeries σ A} {m : ℕ} (hm : 1 ≤ m) (hu : ∀ i ∈ s, OrderGe 1 (u i))
    (hv : ∀ i ∈ s, OrderGe 1 (v i)) (huv : ∀ i ∈ s, OrderGe m (u i - v i)) :
    OrderGe (m - 1 + ∑ i ∈ s, d i) (∏ i ∈ s, u i ^ d i - ∏ i ∈ s, v i ^ d i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using orderGe_zero (A := A) (m - 1) (σ := σ)
  | cons a s ha ih =>
    have hua : OrderGe 1 (u a) := hu a (Finset.mem_cons_self a s)
    have hva : OrderGe 1 (v a) := hv a (Finset.mem_cons_self a s)
    have huva : OrderGe m (u a - v a) := huv a (Finset.mem_cons_self a s)
    have hu' : ∀ i ∈ s, OrderGe 1 (u i) := fun i hi => hu i (Finset.mem_cons.mpr (Or.inr hi))
    have hv' : ∀ i ∈ s, OrderGe 1 (v i) := fun i hi => hv i (Finset.mem_cons.mpr (Or.inr hi))
    have huv' : ∀ i ∈ s, OrderGe m (u i - v i) :=
      fun i hi => huv i (Finset.mem_cons.mpr (Or.inr hi))
    have hPu : OrderGe (∑ i ∈ s, d i) (∏ i ∈ s, u i ^ d i) :=
      OrderGe.prod fun i hi => OrderGe.pow_one (hu' i hi) (d i)
    have h1 : OrderGe ((m - 1 + d a) + ∑ i ∈ s, d i)
        ((u a ^ d a - v a ^ d a) * ∏ i ∈ s, u i ^ d i) :=
      (OrderGe.pow_sub_pow hm huva hua hva (d a)).mul hPu
    have h2 : OrderGe (d a + (m - 1 + ∑ i ∈ s, d i))
        (v a ^ d a * (∏ i ∈ s, u i ^ d i - ∏ i ∈ s, v i ^ d i)) :=
      (OrderGe.pow_one hva (d a)).mul (ih hu' hv' huv')
    have h3 : OrderGe (m - 1 + ∑ i ∈ Finset.cons a s ha, d i)
        ((u a ^ d a - v a ^ d a) * ∏ i ∈ s, u i ^ d i
          + v a ^ d a * (∏ i ∈ s, u i ^ d i - ∏ i ∈ s, v i ^ d i)) := by
      have e1 : OrderGe (m - 1 + (d a + ∑ i ∈ s, d i))
          ((u a ^ d a - v a ^ d a) * ∏ i ∈ s, u i ^ d i) := h1.mono (by omega)
      have e2 : OrderGe (m - 1 + (d a + ∑ i ∈ s, d i))
          (v a ^ d a * (∏ i ∈ s, u i ^ d i - ∏ i ∈ s, v i ^ d i)) := h2.mono (by omega)
      rw [Finset.sum_cons ha]
      exact e1.add e2
    convert h3 using 2
    rw [Finset.prod_cons ha, Finset.prod_cons ha]
    ring

/-- A product `∏ (a i)^{d i}` has order at least `∑ d i`. -/
theorem coeff_finsupp_prod_pow_eq_zero {ι : Type*} {a : ι → MvPowerSeries τ A}
    (ha : ∀ i, (a i).constantCoeff = 0) {d : ι →₀ ℕ} {e : τ →₀ ℕ} (h : e.degree < d.degree) :
    MvPowerSeries.coeff e (d.prod fun i n => (a i) ^ n) = 0 := by
  classical
  rw [Finsupp.prod]
  have hge : OrderGe d.degree (∏ i ∈ d.support, (a i) ^ d i) := by
    have := OrderGe.prod (s := d.support) (F := fun i => (a i) ^ d i) (k := fun i => d i)
      (fun i _ => OrderGe.pow_one (OrderGe.of_constantCoeff (ha i)) (d i))
    simpa [Finsupp.degree_apply] using this
  exact hge e h

/-- **Finitary coefficient formula for a substitution**: the coefficient of `X^e` in
`q(a₁,…,aₙ)` is the finite sum over the monomials `d` of total degree `≤ degree e` of
`coeff d q` times the coefficient of `X^e` in `∏ (a i)^{d i}`. -/
theorem coeff_subst_degree {ι : Type*} [Finite ι] {a : ι → MvPowerSeries τ A}
    (ha : ∀ i, (a i).constantCoeff = 0) (q : MvPowerSeries ι A) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.subst a q) =
      ∑ d ∈ (Finsupp.finite_of_degree_lt (σ := ι) (e.degree + 1)).toFinset,
        MvPowerSeries.coeff d q • MvPowerSeries.coeff e (d.prod fun i n => (a i) ^ n) := by
  classical
  have hsub : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hfin : (Function.support fun d : ι →₀ ℕ => MvPowerSeries.coeff d q •
      MvPowerSeries.coeff e (d.prod fun i n => (a i) ^ n)).Finite :=
    MvPowerSeries.coeff_subst_finite hsub q e
  rw [MvPowerSeries.coeff_subst hsub, finsum_eq_sum _ hfin]
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hd
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    by_contra hcon
    push_neg at hcon
    have hzero := coeff_finsupp_prod_pow_eq_zero (d := d) (e := e) ha (by omega)
    exact hd (by simp only [hzero, smul_zero])
  · intro d _ hd'
    rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hd'
    exact hd'

/-- **Gain lemma for substitutions**: if `a i ≡ b i` modulo terms of degree `≥ k`, if `q` vanishes
below degree `κ`, and if all `a i`, `b i` have zero constant coefficient, then
`q(a) - q(b)` vanishes below degree `k + κ - 1`. -/
theorem OrderGe.subst_sub {ι : Type*} [Finite ι] {a b : ι → MvPowerSeries τ A}
    {q : MvPowerSeries ι A} {k κ : ℕ} (hk : 1 ≤ k) (hκ : 1 ≤ κ)
    (ha : ∀ i, OrderGe 1 (a i)) (hb : ∀ i, OrderGe 1 (b i))
    (hab : ∀ i, OrderGe k (a i - b i)) (hq : OrderGe κ q) :
    OrderGe (k + κ - 1) (MvPowerSeries.subst a q - MvPowerSeries.subst b q) := by
  classical
  have ha' : ∀ i, (a i).constantCoeff = 0 := fun i => by
    have := ha i 0 (by simp); simpa using this
  have hb' : ∀ i, (b i).constantCoeff = 0 := fun i => by
    have := hb i 0 (by simp); simpa using this
  intro e he
  rw [map_sub, coeff_subst_degree ha' q e, coeff_subst_degree hb' q e]
  rw [Finset.sum_congr rfl (fun d hd => ?_), sub_self]
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hd
  by_cases hdq : d.degree < κ
  · rw [hq d hdq, zero_smul, zero_smul]
  · push_neg at hdq
    have hzero : MvPowerSeries.coeff e (∏ i ∈ d.support, (a i) ^ d i)
        = MvPowerSeries.coeff e (∏ i ∈ d.support, (b i) ^ d i) := by
      have hkey := OrderGe.prod_pow_sub_prod_pow (σ := τ) (A := A) d.support d hk
        (fun i _ => ha i) (fun i _ => hb i) (fun i _ => hab i)
      have hlt : e.degree < k - 1 + ∑ i ∈ d.support, d i := by
        have hdq' : κ ≤ ∑ i ∈ d.support, d i := by
          rw [← Finsupp.degree_apply]; exact hdq
        omega
      have := hkey e hlt
      rwa [map_sub, sub_eq_zero] at this
    rw [Finsupp.prod, Finsupp.prod, hzero]

end NK.LocalReciprocityLubinTate.LubinTate
