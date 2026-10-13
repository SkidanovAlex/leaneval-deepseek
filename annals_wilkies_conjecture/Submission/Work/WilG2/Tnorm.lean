/-
  WilG2 : the jet ("T") norm of BNZ, Lemma 4.2.

  `tnorm r f x = Σ_{k ≤ r} ‖D^k f(x)‖ / k!` with operator norms on the iterated
  derivatives (`iteratedFDeriv`, i.e. `k`-multilinear maps `E [×k]→L ℝ`).
  It is the `r`-jet norm `‖f‖_{T,r}` of Binyamini–Novikov–Zak evaluated at a point.

  This file: basic API for `tnorm`, and the submultiplicativity `G2_tnorm_mul`.
-/
import Submission.Work.Wilkies.CG.Spec
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
noncomputable section
open Classical Finset
namespace WilkiesDesign.CG
open WilkiesConjecture WilkiesDesign FirstOrder Language

/-! ### Basic API for the jet norm -/

/-- The `k`-th Taylor coefficient norm `‖D^k F(x)‖/k!`; `tnorm` is the sum of these for
scalar-valued `F`.  Stated for an arbitrary normed target space so that it also applies to
vector-valued maps such as `F : E → (Fin m → ℝ)`. -/
def jetCoeff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ) (F : E → V) (x : E) : ℝ :=
  ‖iteratedFDeriv ℝ k F x‖ / (k.factorial : ℝ)

theorem jetCoeff_nonneg {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ) (F : E → V) (x : E) :
    0 ≤ jetCoeff k F x :=
  div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)

theorem tnorm_eq_sum_jetCoeff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ)
    (f : E → ℝ) (x : E) : tnorm r f x = ∑ k ∈ Finset.range (r + 1), jetCoeff k f x := rfl

theorem tnorm_nonneg {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ)
    (f : E → ℝ) (x : E) : 0 ≤ tnorm r f x :=
  Finset.sum_nonneg fun k _ => jetCoeff_nonneg k f x

/-- `tnorm` is monotone in the order. -/
theorem tnorm_mono {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {r r' : ℕ} (h : r ≤ r')
    (f : E → ℝ) (x : E) : tnorm r f x ≤ tnorm r' f x :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.succ_le_succ h))
    fun k _ _ => jetCoeff_nonneg k f x

/-- The `k = 0` term is the norm of the value. -/
theorem jetCoeff_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : E → V) (x : E) :
    jetCoeff 0 F x = ‖F x‖ := by
  simp [jetCoeff]

/-! ### Local smoothness from `ContDiffAt` -/

/-- `ContDiffAt` gives an open neighbourhood on which the function is `C^r`. -/
theorem exists_isOpen_contDiffOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} {r : ℕ} (hf : ContDiffAt ℝ r f x) :
    ∃ u : Set E, IsOpen u ∧ x ∈ u ∧ ContDiffOn ℝ (r : WithTop ℕ∞) f u := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (fun h => absurd h (by simp))
  obtain ⟨v, hvu, hvopen, hxv⟩ := mem_nhds_iff.mp hu
  exact ⟨v, hvopen, hxv, hfu.mono hvu⟩

/-- The iterated derivative within an open set agrees with the global iterated derivative. -/
theorem iteratedFDerivWithin_open {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : Set E} (hu : IsOpen u) {f : E → ℝ} {x : E} (hx : x ∈ u) (k : ℕ) :
    iteratedFDerivWithin ℝ k f u x = iteratedFDeriv ℝ k f x :=
  iteratedFDerivWithin_of_isOpen k hu hx

/-! ### The product rule for the jet norm (BNZ Lemma 4.2(i)) -/

/-- Pointwise multilinear Leibniz bound for `iteratedFDeriv` of a product, at a point,
from `ContDiffAt` hypotheses. -/
theorem norm_iteratedFDeriv_mul_le_at {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r n : ℕ) (hn : n ≤ r) (f g : E → ℝ) (x : E) (hf : ContDiffAt ℝ r f x)
    (hg : ContDiffAt ℝ r g x) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  obtain ⟨uf, hufo, hxuf, hfc⟩ := exists_isOpen_contDiffOn hf
  obtain ⟨ug, hugo, hxug, hgc⟩ := exists_isOpen_contDiffOn hg
  have hu : IsOpen (uf ∩ ug) := hufo.inter hugo
  have hx : x ∈ uf ∩ ug := ⟨hxuf, hxug⟩
  have hf' : ContDiffOn ℝ (r : WithTop ℕ∞) f (uf ∩ ug) := hfc.mono (Set.inter_subset_left)
  have hg' : ContDiffOn ℝ (r : WithTop ℕ∞) g (uf ∩ ug) := hgc.mono (Set.inter_subset_right)
  have hn' : (n : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by exact_mod_cast hn
  have key := norm_iteratedFDerivWithin_mul_le hf' hg' hu.uniqueDiffOn hx hn'
  simpa only [iteratedFDerivWithin_open hu hx] using key

/-- `Nat.cast` of a binomial coefficient, as a ratio of factorials. -/
theorem choose_cast_eq (n i : ℕ) (hi : i ≤ n) :
    (n.choose i : ℝ) = (n.factorial : ℝ) / ((i.factorial : ℝ) * ((n - i).factorial : ℝ)) :=
  Nat.cast_choose ℝ hi

/-- Triangular (Cauchy-product) bound: a double sum over `i + j = n ≤ r` is at most the
product of the two partial sums. -/
theorem sum_range_sum_range_le (r : ℕ) (a b : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) :
    (∑ n ∈ Finset.range (r + 1), ∑ i ∈ Finset.range (n + 1), a i * b (n - i)) ≤
      (∑ i ∈ Finset.range (r + 1), a i) * (∑ j ∈ Finset.range (r + 1), b j) := by
  classical
  set T : Finset (ℕ × ℕ) := (Finset.range (r + 1)) ×ˢ (Finset.range (r + 1)) with hT
  set S : Finset (Σ _ : ℕ, ℕ) := (Finset.range (r + 1)).sigma fun n => Finset.range (n + 1)
    with hS
  let φ : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun x => (x.2, x.1 - x.2)
  let G : ℕ × ℕ → ℝ := fun p => a p.1 * b p.2
  have hL : (∑ n ∈ Finset.range (r + 1), ∑ i ∈ Finset.range (n + 1), a i * b (n - i))
      = ∑ x ∈ S, G (φ x) := by
    rw [hS, Finset.sum_sigma]
  have hsub : S.image φ ⊆ T := by
    intro y hy
    simp only [Finset.mem_image, hS, Finset.mem_sigma, Finset.mem_range, hT,
      Finset.mem_product] at hy ⊢
    obtain ⟨x, ⟨hx1, hx2⟩, rfl⟩ := hy
    refine ⟨?_, ?_⟩ <;> simp only [φ] <;> omega
  have hinj : Set.InjOn φ ↑S := by
    intro x hx y hy hxy
    simp only [hS, Finset.mem_coe, Finset.mem_sigma, Finset.mem_range] at hx hy
    simp only [φ, Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have hxle : x.2 ≤ x.1 := by omega
    have hyle : y.2 ≤ y.1 := by omega
    have h3 : x.1 = y.1 := by omega
    exact Sigma.ext h3 (by simp [h1])
  have hstep1 : (∑ x ∈ S, G (φ x)) = ∑ y ∈ S.image φ, G y :=
    (Finset.sum_image hinj).symm
  have hstep2 : (∑ y ∈ S.image φ, G y) ≤ ∑ y ∈ T, G y :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun y _ _ => mul_nonneg (ha _) (hb _)
  have hstep3 : (∑ y ∈ T, G y) = (∑ i ∈ Finset.range (r + 1), a i) *
      (∑ j ∈ Finset.range (r + 1), b j) := by
    rw [hT, Finset.sum_product, Finset.sum_mul_sum]
  rw [hL]
  exact hstep1.trans_le (hstep2.trans_eq hstep3)

/-- **G2, submultiplicativity of the jet norm** (BNZ Lemma 4.2(i)). -/
theorem G2_tnorm_mul_proved {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ)
    (f g : E → ℝ) (x : E) (hf : ContDiffAt ℝ r f x) (hg : ContDiffAt ℝ r g x) :
    tnorm r (f * g) x ≤ tnorm r f x * tnorm r g x := by
  rw [tnorm_eq_sum_jetCoeff, tnorm_eq_sum_jetCoeff, tnorm_eq_sum_jetCoeff,
    Finset.sum_mul_sum]
  have key : ∀ n ∈ Finset.range (r + 1),
      jetCoeff n (f * g) x ≤
        ∑ i ∈ Finset.range (n + 1), jetCoeff i f x * jetCoeff (n - i) g x := by
    intro n hn
    have hnle : n ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hb := norm_iteratedFDeriv_mul_le_at r n hnle f g x hf hg
    have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    rw [jetCoeff, div_le_iff₀ hfac]
    calc ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖
        ≤ ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := hb
      _ = ∑ i ∈ Finset.range (n + 1),
            (jetCoeff i f x * jetCoeff (n - i) g x) * (n.factorial : ℝ) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rw [choose_cast_eq n i hi', jetCoeff, jetCoeff]
          field_simp
      _ = (∑ i ∈ Finset.range (n + 1), jetCoeff i f x * jetCoeff (n - i) g x) *
            (n.factorial : ℝ) := (Finset.sum_mul ..).symm
  calc (∑ n ∈ Finset.range (r + 1), jetCoeff n (f * g) x)
      ≤ ∑ n ∈ Finset.range (r + 1),
          ∑ i ∈ Finset.range (n + 1), jetCoeff i f x * jetCoeff (n - i) g x :=
        Finset.sum_le_sum key
    _ ≤ (∑ i ∈ Finset.range (r + 1), jetCoeff i f x) *
          (∑ j ∈ Finset.range (r + 1), jetCoeff j g x) :=
        sum_range_sum_range_le r (jetCoeff · f x) (jetCoeff · g x)
          (fun i => jetCoeff_nonneg i f x) (fun j => jetCoeff_nonneg j g x)
    _ = ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1),
          jetCoeff i f x * jetCoeff j g x := Finset.sum_mul_sum ..

/-- Subadditivity of the jet norm. -/
theorem tnorm_add_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ) (f g : E → ℝ)
    (x : E) (hf : ContDiffAt ℝ r f x) (hg : ContDiffAt ℝ r g x) :
    tnorm r (f + g) x ≤ tnorm r f x + tnorm r g x := by
  rw [tnorm_eq_sum_jetCoeff, tnorm_eq_sum_jetCoeff, tnorm_eq_sum_jetCoeff,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : (k : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by
    exact_mod_cast (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have h := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := k) (f := f) (g := g) (x := x)
    (hf.of_le hk') (hg.of_le hk')
  simp only [jetCoeff]
  rw [h, ← add_div]
  exact div_le_div_of_nonneg_right (norm_add_le _ _) (Nat.cast_nonneg _)

/-- The jet norm of a constant function is the norm of the constant. -/
theorem tnorm_const {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ) (c : ℝ)
    (x : E) : tnorm r (fun _ : E => c) x = ‖c‖ := by
  rw [tnorm_eq_sum_jetCoeff, Finset.sum_range_succ']
  have hzero : ∀ k : ℕ, jetCoeff (k + 1) (fun _ : E => c) x = 0 := by
    intro k
    have h := congr_fun (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (Nat.succ_ne_zero k) c) x
    simp [jetCoeff, h]
  simp only [hzero, Finset.sum_const_zero, zero_add, jetCoeff_zero]

/-- The value is dominated by the jet norm. -/
theorem norm_le_tnorm {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ) (f : E → ℝ)
    (x : E) : ‖f x‖ ≤ tnorm r f x := by
  rw [tnorm_eq_sum_jetCoeff]
  have h := Finset.single_le_sum (fun k (_ : k ∈ Finset.range (r + 1)) => jetCoeff_nonneg k f x)
    (Finset.mem_range.mpr (Nat.succ_pos r))
  rwa [jetCoeff_zero] at h

/-- The jet norm is invariant under negation. -/
theorem tnorm_neg {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ) (f : E → ℝ)
    (x : E) : tnorm r (-f) x = tnorm r f x := by
  rw [tnorm_eq_sum_jetCoeff, tnorm_eq_sum_jetCoeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [jetCoeff, iteratedFDeriv_neg, Pi.neg_apply, norm_neg]

end WilkiesDesign.CG
