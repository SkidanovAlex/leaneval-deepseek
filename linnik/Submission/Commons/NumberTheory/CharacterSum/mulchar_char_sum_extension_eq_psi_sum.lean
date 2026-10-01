import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.NumberTheory.MulChar.Basic
import Submission.Commons.Algebra.Polynomial.resultant_eq_norm_adjoinRoot
import Submission.Commons.FieldTheory.Minpoly.conjRootClass_card_carrier
import Submission.Commons.FieldTheory.Minpoly.sum_eq_sum_conjRootClass_commmonoid
import Submission.Commons.FieldTheory.Finite.exists_root_of_irreducible_natDegree_dvd
import Submission.Commons.FieldTheory.Finite.minpoly_map_eq_prod_pow_card
import Submission.Commons.FieldTheory.Finite.minpoly_pow_card_pow_eq_self

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.CharacterSum

open Polynomial

noncomputable section

/-! ## Auxiliary lemmas about finite field extensions -/

/-- Raising `eval a f` to the power `|F| ^ i` is evaluating `f` at `a ^ (|F| ^ i)`
(this is the Frobenius twist). -/
theorem eval_pow_card_pow {F E : Type*} [Field F] [Field E] [Fintype F] [Fintype E]
    [Algebra F E] (f : Polynomial F) (a : E) (i : ℕ) :
    ((f.map (algebraMap F E)).eval a) ^ (Fintype.card F ^ i)
      = (f.map (algebraMap F E)).eval (a ^ (Fintype.card F ^ i)) := by
  set σ : Gal(E/F) := FiniteField.frobeniusAlgEquivOfAlgebraic F E with hσdef
  have hσi : ∀ x : E, (σ ^ i) x = x ^ (Fintype.card F ^ i) := by
    intro x
    rw [AlgEquiv.coe_pow, hσdef, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  have hσφ : (σ ^ i).toRingHom.comp (algebraMap F E) = algebraMap F E := by
    ext c
    exact (σ ^ i).commutes c
  have h2 : (σ ^ i).toRingHom ((f.map (algebraMap F E)).eval a)
      = (f.map (algebraMap F E)).eval ((σ ^ i).toRingHom a) := by
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, hσφ, ← Polynomial.eval_map]
  rw [← hσi ((f.map (algebraMap F E)).eval a), ← hσi a]
  exact h2

/-- The roots in `E` of the minimal polynomial of `a : E` are the Frobenius orbit
`a, a^q, ..., a^(q^(m-1))` (as a multiset). -/
theorem roots_minpoly_map {F E : Type*} [Field F] [Field E] [Fintype F] [Fintype E]
    [DecidableEq F] [DecidableEq E] [Algebra F E] (a : E) :
    ((minpoly F a).map (algebraMap F E)).roots
      = (Finset.univ.val.map (fun i : Fin (minpoly F a).natDegree =>
          a ^ (Fintype.card F ^ (i : ℕ)))) := by
  rw [Commons.FieldTheory.Finite.minpoly_map_eq_prod_pow_card a]
  rw [Finset.prod_eq_multiset_prod]
  have h := Polynomial.roots_multiset_prod_X_sub_C
    (Finset.univ.val.map (fun i : Fin (minpoly F a).natDegree =>
      a ^ (Fintype.card F ^ (i : ℕ))) : Multiset E)
  simp only [Multiset.map_map, Function.comp] at h
  rw [h]

/-- The product of `f` over the Frobenius orbit of `a` equals the resultant
`Res(minpoly a, f)` (embedded into `E`). -/
theorem prod_eval_eq_algebraMap_resultant {F E : Type*} [Field F] [Field E] [Fintype F] [Fintype E]
    [DecidableEq F] [DecidableEq E] [Algebra F E] [Module.Finite F E] [Module.Free F E]
    (f : Polynomial F) (a : E) :
    (∏ i : Fin (minpoly F a).natDegree,
        (f.map (algebraMap F E)).eval (a ^ (Fintype.card F ^ (i : ℕ))))
      = algebraMap F E (Polynomial.resultant (minpoly F a) f) := by
  classical
  set φ := algebraMap F E with hφ
  set P : Polynomial F := minpoly F a with hP
  have h1 : Polynomial.resultant (P.map φ) (f.map φ) = φ (Polynomial.resultant P f) := by
    rw [Polynomial.resultant_map_map]
    congr 1
    rw [Polynomial.natDegree_map_eq_of_injective φ.injective P,
        Polynomial.natDegree_map_eq_of_injective φ.injective f]
  have hmonic : (P.map φ).Monic := (minpoly.monic (IsIntegral.of_finite F a)).map φ
  have hsplits : (P.map φ).Splits := (inferInstance : Normal F E).splits a
  have h2 := Polynomial.resultant_eq_prod_eval (P.map φ) (f.map φ) ((f.map φ).natDegree)
    le_rfl hsplits
  rw [hmonic.leadingCoeff, one_pow, one_mul] at h2
  rw [← h1, h2]
  rw [roots_minpoly_map a]
  rw [Multiset.map_map]
  rw [Finset.prod_eq_multiset_prod]
  rfl

/-- A periodic sequence satisfies `f (m * k + i) = f i`. -/
theorem shift_mul {M : Type*} (f : ℕ → M) {m : ℕ} (hf : ∀ i, f (i + m) = f i) :
    ∀ k i, f (m * k + i) = f i := by
  intro k
  induction k with
  | zero => intro i; simp
  | succ k ihk =>
    intro i
    have h1 : m * (k + 1) + i = (m * k + i) + m := by ring
    rw [h1, hf, ihk]

/-- The product of the first `m * k` terms of an `m`-periodic sequence is the `k`-th power
of the product of the first `m` terms. -/
theorem prod_range_eq_pow_of_period {M : Type*} [CommMonoid M] (f : ℕ → M) {m : ℕ} (_hm : 0 < m)
    (hf : ∀ i, f (i + m) = f i) :
    ∀ k, ∏ i ∈ Finset.range (m * k), f i = (∏ i ∈ Finset.range m, f i) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hshift := shift_mul f hf
    rw [Nat.mul_succ]
    rw [← Finset.prod_range_mul_prod_Ico f (Nat.le_add_right (m * k) m)]
    rw [Finset.prod_Ico_eq_prod_range f (m * k) (m * k + m)]
    simp only [Nat.add_sub_cancel_left]
    rw [show (∏ k_1 ∈ Finset.range m, f (m * k + k_1)) = ∏ k_1 ∈ Finset.range m, f k_1 from
      Finset.prod_congr rfl (fun i _ => hshift k i)]
    rw [ih, pow_succ]

/-- **Key computation.** For a finite field extension `E/F` of degree `n`, `f ∈ F[X]` and `a : E`
with minimal polynomial of degree `m`, the norm of `f(a)` is `Res(minpoly a, f) ^ (n/m)`. -/
theorem norm_eval_eq_resultant_pow {F E : Type*} [Field F] [Field E] [Fintype F] [Fintype E]
    [DecidableEq F] [DecidableEq E] [Algebra F E] [Module.Finite F E] [Module.Free F E]
    (f : Polynomial F) (a : E) :
    Algebra.norm F ((f.map (algebraMap F E)).eval a)
      = (Polynomial.resultant (minpoly F a) f) ^ (Module.finrank F E / (minpoly F a).natDegree) := by
  classical
  set n := Module.finrank F E with hn
  set m := (minpoly F a).natDegree with hm
  set q := Fintype.card F with hq
  set g : E → E := fun x => (f.map (algebraMap F E)).eval x with hg
  have hmdvd : m ∣ n := by
    have h1 : m = Module.finrank F ↥(IntermediateField.adjoin F {a}) := by
      rw [hm]; exact (IntermediateField.adjoin.finrank (IsIntegral.of_finite F a)).symm
    have h2 : Module.finrank F ↥(IntermediateField.adjoin F {a})
        ∣ Module.finrank F ↥(⊤ : IntermediateField F E) :=
      IntermediateField.finrank_dvd_of_le_right
        (le_top : (IntermediateField.adjoin F {a}) ≤ (⊤ : IntermediateField F E))
    have h3 : Module.finrank F ↥(⊤ : IntermediateField F E) = n := by
      rw [IntermediateField.finrank_top', ← hn]
    rw [← h1, h3] at h2
    exact h2
  have hnpos : 0 < n := by rw [hn]; exact Module.finrank_pos
  have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hmdvd hnpos
  have hL : algebraMap F E (Algebra.norm F ((f.map (algebraMap F E)).eval a))
      = ∏ i ∈ Finset.range n, g (a ^ (q ^ i)) := by
    rw [FiniteField.algebraMap_norm_eq_prod_pow]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Nat.card_eq_fintype_card]
    simp only [hg, hq]
    exact eval_pow_card_pow f a i
  have hfix : a ^ (q ^ m) = a := by
    rw [hm, hq]
    exact Commons.FieldTheory.Finite.minpoly_pow_card_pow_eq_self a
  have hper : ∀ i, g (a ^ (q ^ (i + m))) = g (a ^ (q ^ i)) := by
    intro i
    congr 1
    rw [show q ^ (i + m) = q ^ m * q ^ i by rw [pow_add, mul_comm], pow_mul, hfix]
  have hn_eq : m * (n / m) = n := Nat.mul_div_cancel' hmdvd
  have hstep2 : ∏ i ∈ Finset.range n, g (a ^ (q ^ i))
      = (∏ i ∈ Finset.range m, g (a ^ (q ^ i))) ^ (n / m) := by
    have h := prod_range_eq_pow_of_period (fun i => g (a ^ (q ^ i))) hmpos hper (n / m)
    rwa [hn_eq] at h
  have hstep3 : ∏ i ∈ Finset.range m, g (a ^ (q ^ i))
      = algebraMap F E (Polynomial.resultant (minpoly F a) f) := by
    rw [hm, ← Fin.prod_univ_eq_prod_range]
    simp only [hg, hq]
    exact prod_eval_eq_algebraMap_resultant f a
  apply (algebraMap F E).injective
  rw [hL, hstep2, hstep3, map_pow]

/-! ## Irreducible polynomials of degree `m` vs. conjugate root classes -/

private lemma sum_ite_eq_sum_subtype {α M : Type*} [Fintype α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] (f : α → M) :
    (∑ a : α, if p a then f a else 0) = ∑ a : {a // p a}, f a := by
  rw [← Fintype.sum_subtype_add_sum_subtype p (fun a => if p a then f a else 0)]
  have h1 : (∑ a : {a // p a}, (if p ↑a then f ↑a else 0)) = ∑ a : {a // p a}, f ↑a := by
    refine Finset.sum_congr rfl fun a _ => by rw [if_pos a.2]
  have h2 : (∑ a : {a // ¬p a}, (if p ↑a then f ↑a else 0)) = 0 := by
    refine Finset.sum_eq_zero fun a _ => by rw [if_neg a.2]
  rw [h1, h2, add_zero]

variable {F : Type*} [Field F]

/-- The monic polynomial of degree `m` with lower coefficients given by `c`. -/
private noncomputable def coeffPoly (m : ℕ) (c : Fin m → F) : Polynomial F :=
  X ^ m + ∑ j : Fin m, C (c j) * X ^ (j : ℕ)

private lemma coeff_coeffPoly (m : ℕ) (c : Fin m → F) (i : Fin m) :
    (coeffPoly m c).coeff (i : ℕ) = c i := by
  rw [coeffPoly, coeff_add, coeff_X_pow]
  have hne : (i : ℕ) ≠ m := by have := i.isLt; omega
  rw [if_neg hne, zero_add]
  rw [Polynomial.finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    exact if_neg (fun h => hb (Fin.ext h.symm))
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma coeff_coeffPoly_top (m : ℕ) (c : Fin m → F) :
    (coeffPoly m c).coeff m = 1 := by
  rw [coeffPoly, coeff_add, coeff_X_pow, if_pos rfl]
  have hS : (∑ j : Fin m, C (c j) * X ^ (j : ℕ)).coeff m = 0 := by
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [coeff_C_mul_X_pow]
    exact if_neg (fun h => absurd h.symm (Nat.ne_of_lt j.isLt))
  rw [hS, add_zero]

private lemma natDegree_coeffPoly (m : ℕ) (c : Fin m → F) :
    (coeffPoly m c).natDegree = m := by
  rw [coeffPoly]
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · refine (Polynomial.natDegree_add_le _ _).trans ?_
    rw [Polynomial.natDegree_X_pow]
    refine max_le le_rfl ?_
    refine Polynomial.natDegree_sum_le_of_forall_le (n := m) Finset.univ
      (fun j : Fin m => C (c j) * X ^ (j : ℕ)) (fun j _ => ?_)
    exact (Polynomial.natDegree_C_mul_X_pow_le (c j) (j : ℕ)).trans (Nat.le_of_lt j.isLt)
  · rw [← coeffPoly, coeff_coeffPoly_top]; exact one_ne_zero

private lemma monic_coeffPoly (m : ℕ) (c : Fin m → F) :
    (coeffPoly m c).Monic := by
  show (coeffPoly m c).coeff (coeffPoly m c).natDegree = 1
  rw [natDegree_coeffPoly, coeff_coeffPoly_top]

private lemma coeffPoly_inj (m : ℕ) : Function.Injective (coeffPoly (F := F) m) := by
  intro c d hcd
  funext i
  have := congrArg (fun p : Polynomial F => p.coeff (i : ℕ)) hcd
  rwa [coeff_coeffPoly, coeff_coeffPoly] at this

private lemma coeffPoly_surj (m : ℕ) (P : Polynomial F) (hmonic : P.Monic)
    (hdeg : P.natDegree = m) : ∃ c : Fin m → F, coeffPoly m c = P := by
  have hcm : P.coeff m = 1 := by rw [← hdeg]; exact hmonic.coeff_natDegree
  have hP : P = (∑ i ∈ Finset.range m, C (P.coeff i) * X ^ i) + C (P.coeff m) * X ^ m := by
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow' P (by rw [hdeg]; exact Nat.lt_succ_self m)]
    rw [Finset.sum_range_succ]
  refine ⟨fun i => P.coeff i, ?_⟩
  rw [coeffPoly]
  have hsum : (∑ j : Fin m, C ((fun i => P.coeff i) j) * X ^ (j : ℕ))
      = ∑ i ∈ Finset.range m, C (P.coeff i) * X ^ i :=
    Fin.sum_univ_eq_sum_range (fun i => C (P.coeff i) * X ^ i) m
  calc X ^ m + ∑ j : Fin m, C ((fun i => P.coeff i) j) * X ^ (j : ℕ)
      = (∑ i ∈ Finset.range m, C (P.coeff i) * X ^ i) + X ^ m := by rw [hsum, add_comm]
    _ = (∑ i ∈ Finset.range m, C (P.coeff i) * X ^ i) + C (P.coeff m) * X ^ m := by
          rw [hcm, Polynomial.C_1, one_mul]
    _ = P := hP.symm

open Classical in
/-- The monic irreducible polynomials of degree `m` over a finite field `F`, weighted by any
function `Ψ`, sum to the same thing as the conjugate-root classes of that degree in a
degree-`n` extension `E` (`m ∣ n`). -/
theorem sum_fin_irreducible_eq_sum_conjRootClass_monoid {F E M : Type*} [Field F] [Field E]
    [Fintype F] [Fintype E] [DecidableEq F] [DecidableEq E] [Algebra F E]
    [Fintype (ConjRootClass F E)] [AddCommMonoid M]
    (n : ℕ) (hn : Module.finrank F E = n) (m : ℕ) (hm : m ∈ n.divisors) (Ψ : Polynomial F → M) :
    (∑ c : Fin m → F,
        if Irreducible (Polynomial.X ^ m + ∑ i : Fin m, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))
        then Ψ (Polynomial.X ^ m + ∑ i : Fin m, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)) else 0)
      = ∑ c : {c : ConjRootClass F E // c.minpoly.natDegree = m}, Ψ c.1.minpoly := by
  classical
  have hAlg : Algebra.IsAlgebraic F E := inferInstance
  have hmdvd : m ∣ n := (Nat.mem_divisors.mp hm).1
  change (∑ c : Fin m → F, if Irreducible (coeffPoly m c) then Ψ (coeffPoly m c) else 0)
      = ∑ c : {c : ConjRootClass F E // c.minpoly.natDegree = m}, Ψ c.1.minpoly
  have h1 : (∑ c : Fin m → F, if Irreducible (coeffPoly m c) then Ψ (coeffPoly m c) else 0)
      = ∑ c : {c : Fin m → F // Irreducible (coeffPoly m c)}, Ψ (coeffPoly m c.1) :=
    sum_ite_eq_sum_subtype (fun c : Fin m → F => Irreducible (coeffPoly m c))
      (fun c => Ψ (coeffPoly m c))
  have hroot : ∀ c : {c : Fin m → F // Irreducible (coeffPoly m c)},
      ∃ x : E, aeval x (coeffPoly m c.1) = 0 := by
    intro c
    have hd : (coeffPoly m c.1).natDegree ∣ n := by
      rw [natDegree_coeffPoly]; exact hmdvd
    obtain ⟨x, hx⟩ :=
      Commons.FieldTheory.Finite.exists_root_of_irreducible_natDegree_dvd n hn (coeffPoly m c.1) c.2 hd
    exact ⟨x, by rwa [Polynomial.aeval_def]⟩
  let χ : {c : Fin m → F // Irreducible (coeffPoly m c)} → E := fun c => Classical.choose (hroot c)
  have hχ : ∀ c, aeval (χ c) (coeffPoly m c.1) = 0 := fun c => Classical.choose_spec (hroot c)
  have hχmin : ∀ c, minpoly F (χ c) = coeffPoly m c.1 := by
    intro c
    exact (minpoly.eq_of_irreducible_of_monic c.2 (hχ c) (monic_coeffPoly m c.1)).symm
  let g : {c : Fin m → F // Irreducible (coeffPoly m c)} →
      {c : ConjRootClass F E // c.minpoly.natDegree = m} :=
    fun c => ⟨ConjRootClass.mk F (χ c),
      by rw [ConjRootClass.minpoly_mk, hχmin c, natDegree_coeffPoly]⟩
  have g_minpoly : ∀ c, (g c).1.minpoly = coeffPoly m c.1 := by
    intro c; exact hχmin c
  have g_inj : Function.Injective g := by
    intro c d hcd
    refine Subtype.ext (coeffPoly_inj m ?_)
    have h : (g c).1 = (g d).1 := congrArg Subtype.val hcd
    rw [← g_minpoly c, ← g_minpoly d, h]
  have g_surj : Function.Surjective g := by
    intro d
    obtain ⟨c0, hc0⟩ := coeffPoly_surj m d.1.minpoly d.1.monic_minpoly d.2
    have hirr : Irreducible (coeffPoly m c0) := hc0 ▸ d.1.irreducible_minpoly
    refine ⟨⟨c0, hirr⟩, ?_⟩
    refine Subtype.ext (ConjRootClass.minpoly_inj.mp ?_)
    rw [g_minpoly, hc0]
  let eg := Equiv.ofBijective g ⟨g_inj, g_surj⟩
  have h2 : (∑ c : {c : Fin m → F // Irreducible (coeffPoly m c)}, Ψ (coeffPoly m c.1))
      = ∑ c : {c : ConjRootClass F E // c.minpoly.natDegree = m}, Ψ c.1.minpoly := by
    rw [← Equiv.sum_comp eg
      (fun d : {c : ConjRootClass F E // c.minpoly.natDegree = m} => Ψ d.1.minpoly)]
    refine Finset.sum_congr rfl fun c _ => ?_
    change Ψ (coeffPoly m c.1) = Ψ (g c).1.minpoly
    rw [g_minpoly]
  rw [h1, h2]


/-! ## The "L-function value" and the pointwise identity -/

/-- The `L`-function value attached to a monic polynomial `P`: the product
`χ(-1)^(deg f · deg P) · χ(N_{F[X]/f}(P))`, raised to the power `n / deg P`. -/
noncomputable def Psi {F : Type*} [Field F] (χ : MulChar F ℂ) (f : Polynomial F) (n : ℕ)
    (P : Polynomial F) : ℂ :=
  (χ ((-1 : F) ^ (f.natDegree * P.natDegree)) *
    χ (Algebra.norm F (AdjoinRoot.mk f P))) ^ (n / P.natDegree)

/-- Pointwise identity underlying the character sum decomposition: for `a : E` with minimal
polynomial `P` of degree `m`, `χ(N_{E/F}(f(a))) = Psi χ f n P`. -/
theorem chi_norm_eval_eq_Psi {F E : Type*} [Field F] [Field E] [Fintype F] [Fintype E]
    [DecidableEq F] [DecidableEq E] [Algebra F E] [Module.Finite F E] [Module.Free F E]
    (χ : MulChar F ℂ) (f : Polynomial F) (hf : f.Monic) (n : ℕ) (hn : Module.finrank F E = n)
    (a : E) :
    χ (Algebra.norm F ((f.map (algebraMap F E)).eval a)) = Psi χ f n (minpoly F a) := by
  set P : Polynomial F := minpoly F a with hP
  have hk := norm_eval_eq_resultant_pow f a
  rw [hk, hn]
  rw [map_pow]
  rw [Psi]
  congr 1
  -- show χ (Res P f) = χ ((-1)^(deg f * deg P)) * χ (N (mk f P))
  rw [← Commons.Algebra.Polynomial.resultant_eq_norm_adjoinRoot f hf P]
  rw [← map_mul]
  congr 1
  -- (-1)^(deg f * deg P) * Res f P = Res P f
  have hcomm : Polynomial.resultant f P
      = (-1 : F) ^ (f.natDegree * P.natDegree) * Polynomial.resultant P f :=
    Polynomial.resultant_comm f P f.natDegree P.natDegree
  have hsq : (-1 : F) ^ (f.natDegree * P.natDegree) * (-1 : F) ^ (f.natDegree * P.natDegree)
      = 1 := by
    rw [← pow_add,
      show f.natDegree * P.natDegree + f.natDegree * P.natDegree
        = 2 * (f.natDegree * P.natDegree) by ring, pow_mul]
    norm_num
  rw [hcomm, ← mul_assoc, hsq, one_mul]


open Classical in
/-- For a finite field extension `E/F` of degree `n`, a multiplicative character
`χ : MulChar F ℂ` and a monic `f ∈ F[X]`, the character sum `∑_{a : E} χ (N_{E/F} (f a))`
equals the "L-function power sum" `∑_{m | n} m · ∑_{P monic irreducible, deg P = m} Ψ(P)^{n/m}`,
where `Ψ(P) = χ (-1)^{deg f · m} · χ (N_{F[X]/f} (P mod f))`.  (For monic `A`,
`Ψ(A) = χ (Polynomial.resultant A f)`.) -/
theorem mulchar_char_sum_extension_eq_psi_sum {F E : Type*} [Field F] [Field E] [Fintype F]
    [Fintype E] [DecidableEq F] [DecidableEq E] [Algebra F E] [Module.Finite F E] [Module.Free F E]
    (χ : MulChar F ℂ) (f : Polynomial F) (hf : f.Monic) (n : ℕ) (hn : Module.finrank F E = n) :
    ∑ a : E, χ (Algebra.norm F ((f.map (algebraMap F E)).eval a))
      = ∑ m ∈ n.divisors, (m : ℂ) * ∑ c : Fin m → F,
          if Irreducible (Polynomial.X ^ m + ∑ i : Fin m, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))
          then (χ ((-1 : F) ^ (f.natDegree * m)) *
                  χ (Algebra.norm F (AdjoinRoot.mk f
                    (Polynomial.X ^ m + ∑ i : Fin m, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)))))
                ^ (n / m)
          else 0 := by
  classical
  haveI : Fintype (ConjRootClass F E) :=
    Fintype.ofSurjective (ConjRootClass.mk F)
      (fun c => Quotient.inductionOn c (fun x => ⟨x, rfl⟩))
  have hnpos : 0 < n := by rw [← hn]; exact Module.finrank_pos
  have hnne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hnpos
  haveI : Normal F E := inferInstance
  have deg_dvd : ∀ c : ConjRootClass F E, c.minpoly.natDegree ∣ n := by
    intro c
    induction c using ConjRootClass.ind with
    | h x =>
      rw [ConjRootClass.minpoly_mk]
      have h1 : (minpoly F x).natDegree = Module.finrank F ↥(IntermediateField.adjoin F {x}) :=
        (IntermediateField.adjoin.finrank (IsIntegral.of_finite F x)).symm
      have h2 : Module.finrank F ↥(IntermediateField.adjoin F {x})
          ∣ Module.finrank F ↥(⊤ : IntermediateField F E) :=
        IntermediateField.finrank_dvd_of_le_right
          (le_top : (IntermediateField.adjoin F {x}) ≤ (⊤ : IntermediateField F E))
      rw [IntermediateField.finrank_top'] at h2
      rw [h1, ← hn]
      exact h2
  have hgroup : (∑ a : E, χ (Algebra.norm F ((f.map (algebraMap F E)).eval a)))
      = ∑ c : ConjRootClass F E, (c.minpoly.natDegree : ℂ) * Psi χ f n c.minpoly := by
    rw [Commons.FieldTheory.Minpoly.sum_eq_sum_conjRootClass_commmonoid (K := F) (L := E)
          (fun a : E => χ (Algebra.norm F ((f.map (algebraMap F E)).eval a)))]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hconst : (∑ a ∈ c.carrier.toFinset,
          χ (Algebra.norm F ((f.map (algebraMap F E)).eval a)))
        = ∑ _a ∈ c.carrier.toFinset, Psi χ f n c.minpoly := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [chi_norm_eval_eq_Psi χ f hf n hn a]
      congr 1
      have hca : ConjRootClass.mk F a = c :=
        ConjRootClass.mem_carrier.mp ((Set.mem_toFinset).mp ha)
      rw [← ConjRootClass.minpoly_mk, hca]
    rw [hconst, Finset.sum_const, Commons.FieldTheory.Minpoly.conjRootClass_card_carrier c,
      nsmul_eq_mul]
  have hstep5 : (∑ c : ConjRootClass F E, (c.minpoly.natDegree : ℂ) * Psi χ f n c.minpoly)
      = ∑ m ∈ n.divisors, (m : ℂ)
          * ∑ c : {c : ConjRootClass F E // c.minpoly.natDegree = m}, Psi χ f n c.1.minpoly := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := n.divisors)
          (g := fun c : ConjRootClass F E => c.minpoly.natDegree)
          (f := fun c => (c.minpoly.natDegree : ℂ) * Psi χ f n c.minpoly)
          (h := fun c _ => by rw [Nat.mem_divisors]; exact ⟨deg_dvd c, hnne⟩)]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h1 : (∑ c ∈ Finset.univ.filter (fun c : ConjRootClass F E => c.minpoly.natDegree = m),
                (c.minpoly.natDegree : ℂ) * Psi χ f n c.minpoly)
        = ∑ c ∈ Finset.univ.filter (fun c : ConjRootClass F E => c.minpoly.natDegree = m),
                (m : ℂ) * Psi χ f n c.minpoly := by
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [Finset.mem_filter] at hc
      rw [hc.2]
    rw [h1, Finset.mul_sum]
    exact Finset.sum_subtype
      (Finset.univ.filter (fun c : ConjRootClass F E => c.minpoly.natDegree = m))
      (fun c => by simp [Finset.mem_filter]) (fun c => (m : ℂ) * Psi χ f n c.minpoly)
  rw [hgroup, hstep5]
  refine Finset.sum_congr rfl fun m hm => ?_
  congr 1
  rw [← sum_fin_irreducible_eq_sum_conjRootClass_monoid n hn m hm (Psi χ f n)]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : Irreducible
    (Polynomial.X ^ m + ∑ i : Fin m, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))
  · rw [if_pos hc, if_pos hc]
    show Psi χ f n (Polynomial.X ^ m + ∑ i : Fin m, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))
      = (χ ((-1 : F) ^ (f.natDegree * m)) *
          χ (Algebra.norm F (AdjoinRoot.mk f
            (Polynomial.X ^ m + ∑ i : Fin m, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))))) ^ (n / m)
    rw [Psi]
    rw [show (Polynomial.X ^ m + ∑ i : Fin m, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))
        = coeffPoly m c from rfl, natDegree_coeffPoly]
  · rw [if_neg hc, if_neg hc]

end

end Commons.NumberTheory.CharacterSum