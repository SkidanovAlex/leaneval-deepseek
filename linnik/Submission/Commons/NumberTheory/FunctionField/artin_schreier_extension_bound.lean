import Mathlib
import Submission.Commons.NumberTheory.ArtinSchreier.point_count

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Artin--Schreier extension bound

`Commons.NumberTheory.FunctionField.artin_schreier_extension_bound`: the Artin--Schreier character
sums `∑_{a : E} ψ (Tr_{E/F_p} (g a))` over a finite field `E` of characteristic `p` with
`p ∤ [E : F_p]` are `O (√(#E))`, uniformly in `E` and in the additive character `ψ ≠ 1`, for any
`g` of degree in `[1, d]` with `d < p`.

The proof combines

* the level-set identity `Tr (g a) = t ⟺ Tr ((g - t n⁻¹) a) = 0` (`n = [E : F_p]`),
* the Artin--Schreier point count `Commons.NumberTheory.ArtinSchreier.count_upper` (Stepanov's
  method in characteristic `p`), which bounds each of these zero sets by `#E / p + O (√(#E))`,
* Fourier inversion on `ZMod p` (the level sets are equidistributed up to `O (√(#E))`).

Since `count_upper` is unconditional, the point-count hypothesis `hpc` of the statement is not
needed by the argument; the result is therefore a strictly stronger statement than requested.
-/

namespace Commons.NumberTheory.FunctionField

open Polynomial
open Commons.NumberTheory.ArtinSchreier

section Aux

variable {p : ℕ} [Fact p.Prime]

theorem charP_of_algebra {E : Type*} [Field E] [Algebra (ZMod p) E] : CharP E p := by
  have hinj : Function.Injective (algebraMap (ZMod p) E) := (algebraMap (ZMod p) E).injective
  refine ⟨fun n => ⟨fun hn => ?_, fun hpn => ?_⟩⟩
  · have h : ((n : ℕ) : ZMod p) = 0 := hinj (by rw [map_natCast, hn, map_zero])
    exact (ZMod.natCast_eq_zero_iff n p).mp h
  · obtain ⟨k, rfl⟩ := hpn
    have hp : ((p : ℕ) : E) = 0 := by
      rw [← map_natCast (algebraMap (ZMod p) E) p, ZMod.natCast_self, map_zero]
    rw [Nat.cast_mul, hp, zero_mul]

variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
  [Module.Finite (ZMod p) E] [Module.Free (ZMod p) E]

theorem trace_pow_eq (z : E) :
    Algebra.trace (ZMod p) E (z ^ p) = Algebra.trace (ZMod p) E z := by
  haveI hcp : CharP E p := charP_of_algebra (p := p) (E := E)
  apply (algebraMap (ZMod p) E).injective
  rw [trace_eq_sum_automorphisms (K := ZMod p) (L := E) (z ^ p)]
  rw [show (∑ σ : Gal(E/ZMod p), σ (z ^ p))
      = ∑ σ : Gal(E/ZMod p), frobenius E p (σ z) from
    Finset.sum_congr rfl (fun σ _ => by rw [map_pow, frobenius_def])]
  rw [← map_sum, frobenius_def]
  rw [show (∑ σ : Gal(E/ZMod p), σ z) = algebraMap (ZMod p) E (Algebra.trace (ZMod p) E z)
      from (trace_eq_sum_automorphisms (K := ZMod p) (L := E) z).symm]
  rw [← map_pow, ZMod.pow_card]

/-- The Artin--Schreier map `z ↦ z ^ p - z` as a `ZMod p`-linear endomorphism. -/
noncomputable def artinSchreier : E →ₗ[ZMod p] E where
  toFun z := z ^ p - z
  map_add' x y := by
    haveI hcp : CharP E p := charP_of_algebra (p := p) (E := E)
    show (x + y) ^ p - (x + y) = (x ^ p - x) + (y ^ p - y)
    rw [add_pow_char]
    ring
  map_smul' c z := by
    show (c • z) ^ p - c • z = c • (z ^ p - z)
    simp only [Algebra.smul_def]
    rw [mul_pow, ← map_pow, ZMod.pow_card]
    ring

theorem artinSchreier_apply (z : E) :
    artinSchreier (p := p) (E := E) z = z ^ p - z := rfl

theorem toFun_artinSchreier (z : E) :
    (artinSchreier (p := p) (E := E)).toFun z = z ^ p - z := rfl

theorem mem_ker_artinSchreier_iff (z : E) :
    z ∈ LinearMap.ker (artinSchreier (p := p) (E := E)) ↔ z ^ p = z := by
  rw [LinearMap.mem_ker, artinSchreier_apply, sub_eq_zero]

theorem mem_ker_artinSchreier_iff_zero (z : E) :
    z ∈ LinearMap.ker (artinSchreier (p := p) (E := E)) ↔ z ^ p - z = 0 := by
  rw [LinearMap.mem_ker, artinSchreier_apply]

/-- The kernel of the Artin--Schreier map is the prime field, of cardinality `p`. -/
theorem ncard_ker_artinSchreier : ({z : E | z ^ p - z = 0} : Set E).ncard = p := by
  have hset : ({z : E | z ^ p - z = 0} : Set E) = {z : E | z ^ p = z} := by
    ext z; rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, sub_eq_zero]
  rw [hset]
  refine le_antisymm ?_ ?_
  · have hsub : {z : E | z ^ p = z} ⊆ {z : E | (X ^ p - X : Polynomial E).eval z = 0} := by
      intro z hz
      have hz' : z ^ p - z = 0 := sub_eq_zero.mpr hz
      simpa [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] using hz'
    have h1 : ({z : E | (X ^ p - X : Polynomial E).eval z = 0} : Set E) ⊆
        (↑((X ^ p - X : Polynomial E).roots.toFinset) : Set E) := by
      intro z hz
      have hne : (X ^ p - X : Polynomial E) ≠ 0 := by
        intro h0
        have hdeg : (X ^ p - X : Polynomial E).natDegree = p := by
          rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
          · rw [Polynomial.natDegree_X_pow]
          · rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
            exact lt_of_lt_of_le Nat.one_lt_two (Fact.out : p.Prime).two_le
        rw [h0, Polynomial.natDegree_zero] at hdeg
        exact absurd hdeg.symm (Fact.out : p.Prime).pos.ne'
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Multiset.mem_toFinset]
      rw [Polynomial.mem_roots hne]
      simpa [Polynomial.IsRoot] using hz
    have h2 : (↑((X ^ p - X : Polynomial E).roots.toFinset) : Set E).ncard ≤ p := by
      rw [Set.ncard_coe_finset]
      refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
      calc (X ^ p - X : Polynomial E).natDegree
          ≤ max ((X ^ p : Polynomial E).natDegree) ((X : Polynomial E).natDegree) :=
            Polynomial.natDegree_sub_le _ _
        _ = max p 1 := by rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
        _ = p := max_eq_left (Fact.out : p.Prime).one_le
    exact (Set.ncard_le_ncard hsub).trans ((Set.ncard_le_ncard h1).trans h2)
  · have hsub : Set.range (algebraMap (ZMod p) E) ⊆ {z : E | z ^ p = z} := by
      rintro _ ⟨c, rfl⟩
      show (algebraMap (ZMod p) E c) ^ p = algebraMap (ZMod p) E c
      rw [← map_pow, ZMod.pow_card]
    have h := Set.ncard_le_ncard hsub
    rw [Set.ncard_range_of_injective (algebraMap (ZMod p) E).injective,
      Nat.card_eq_fintype_card, ZMod.card] at h
    exact h

theorem natCard_zmod : Nat.card (ZMod p) = p := by
  rw [Nat.card_eq_fintype_card, ZMod.card p]

theorem card_ker_artinSchreier :
    Fintype.card {z : E // z ^ p - z = 0} = p := by
  have h : Fintype.card ({z : E | z ^ p - z = 0} : Set E) = p := by
    rw [Set.fintypeCard_eq_ncard]
    exact ncard_ker_artinSchreier
  exact h

theorem finrank_ker_artinSchreier :
    Module.finrank (ZMod p) (LinearMap.ker (artinSchreier (p := p) (E := E))) = 1 := by
  have hcard1 : Nat.card ↥(LinearMap.ker (artinSchreier (p := p) (E := E)))
      = Nat.card {z : E // z ^ p - z = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun z => mem_ker_artinSchreier_iff_zero z))
  have hcard2 : Nat.card {z : E // z ^ p - z = 0} = p := by
    rw [Nat.card_eq_fintype_card]
    exact card_ker_artinSchreier
  have h := Module.natCard_eq_pow_finrank (K := ZMod p)
    (V := ↥(LinearMap.ker (artinSchreier (p := p) (E := E))))
  rw [hcard1, hcard2, natCard_zmod] at h
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le
    (by simp only [pow_one]; exact h)).symm

theorem finrank_range_artinSchreier :
    Module.finrank (ZMod p) (LinearMap.range (artinSchreier (p := p) (E := E)))
      = Module.finrank (ZMod p) E - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (artinSchreier (p := p) (E := E))
  rw [finrank_ker_artinSchreier] at h
  have hpos : 1 ≤ Module.finrank (ZMod p) E := Module.finrank_pos
  omega

theorem range_artinSchreier_le_ker_trace :
    LinearMap.range (artinSchreier (p := p) (E := E)) ≤ LinearMap.ker (Algebra.trace (ZMod p) E) := by
  rintro y ⟨z, rfl⟩
  rw [LinearMap.mem_ker, artinSchreier_apply, map_sub, trace_pow_eq, sub_self]

theorem finrank_ker_trace :
    Module.finrank (ZMod p) (LinearMap.ker (Algebra.trace (ZMod p) E))
      = Module.finrank (ZMod p) E - 1 := by
  haveI : Algebra.IsSeparable (ZMod p) E := inferInstance
  have hsurj : Function.Surjective (Algebra.trace (ZMod p) E) := Algebra.trace_surjective (ZMod p) E
  have hrange : LinearMap.range (Algebra.trace (ZMod p) E) = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have h := LinearMap.finrank_range_add_finrank_ker (Algebra.trace (ZMod p) E)
  rw [hrange, finrank_top, Module.finrank_self] at h
  have hpos : 1 ≤ Module.finrank (ZMod p) E := Module.finrank_pos
  omega

theorem range_artinSchreier_eq_ker_trace :
    LinearMap.range (artinSchreier (p := p) (E := E)) = LinearMap.ker (Algebra.trace (ZMod p) E) :=
  Submodule.eq_of_le_of_finrank_le range_artinSchreier_le_ker_trace
    (by rw [finrank_range_artinSchreier, finrank_ker_trace])

/-- The fibre of the Artin--Schreier map: `z ^ p - z = a` has `p` solutions when `Tr a = 0`
and none otherwise. -/
theorem artin_schreier_fiber_ncard (a : E) :
    ({z : E | z ^ p - z = a} : Set E).ncard
      = if Algebra.trace (ZMod p) E a = 0 then p else 0 := by
  have hmem : ∀ y : E, y ∈ LinearMap.range (artinSchreier (p := p) (E := E))
      ↔ Algebra.trace (ZMod p) E y = 0 := by
    intro y
    rw [range_artinSchreier_eq_ker_trace]
    exact LinearMap.mem_ker
  by_cases ha : Algebra.trace (ZMod p) E a = 0
  · rw [if_pos ha]
    obtain ⟨z₀, hz₀⟩ := (hmem a).mpr ha
    have hfiber : ({z : E | z ^ p - z = a} : Set E).ncard
        = ({z : E | z ^ p - z = 0} : Set E).ncard := by
      rw [← Set.fintypeCard_eq_ncard (s := ({z : E | z ^ p - z = a} : Set E)),
        ← Set.fintypeCard_eq_ncard (s := ({z : E | z ^ p - z = 0} : Set E))]
      refine Fintype.card_congr ?_
      refine
        { toFun := fun z => ⟨z.1 - z₀, ?_⟩
          invFun := fun k => ⟨k.1 + z₀, ?_⟩
          left_inv := fun z => by ext; simp
          right_inv := fun k => by ext; simp }
      · show (z.1 - z₀) ^ p - (z.1 - z₀) = 0
        have hz : artinSchreier (p := p) (E := E) z.1 = a := by
          rw [artinSchreier_apply]; exact z.2
        rw [← artinSchreier_apply (p := p) (E := E) (z.1 - z₀), map_sub, hz, hz₀, sub_self]
      · show (k.1 + z₀) ^ p - (k.1 + z₀) = a
        have hk : artinSchreier (p := p) (E := E) k.1 = 0 := by
          rw [artinSchreier_apply]; exact k.2
        rw [← artinSchreier_apply (p := p) (E := E) (k.1 + z₀), map_add, hk, hz₀, zero_add]
    rw [hfiber, ncard_ker_artinSchreier]
  · rw [if_neg ha]
    rw [Set.ncard_eq_zero]
    ext z
    constructor
    · intro hz
      exact absurd ((hmem a).mp ⟨z, by rw [artinSchreier_apply]; exact hz⟩) ha
    · intro hz
      exact absurd hz (Set.notMem_empty z)


/-- A set of pairs, counted by summing the fibres over the first coordinate. -/
theorem ncard_prod_eq_sum (P : E → E → Prop) :
    ({z : E × E | P z.1 z.2} : Set (E × E)).ncard
      = ∑ x : E, ({z : E | P x z} : Set E).ncard := by
  classical
  rw [← Set.fintypeCard_eq_ncard (s := ({z : E × E | P z.1 z.2} : Set (E × E)))]
  trans Fintype.card (Σ x : E, {z : E // P x z})
  · exact Fintype.card_congr
      { toFun := fun z => ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
        invFun := fun q => ⟨(q.1, q.2.1), q.2.2⟩
        left_inv := fun z => rfl
        right_inv := fun q => by rcases q with ⟨x, z, hz⟩; rfl }
  · rw [Fintype.card_sigma]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact Set.fintypeCard_eq_ncard _

/-- The number of solutions of `z ^ p - z = h x`, as a function of the trace of `h x`. -/
theorem ncard_fiber_eval (h : Polynomial (ZMod p)) (x : E) :
    ({z : E | z ^ p - z = (h.map (algebraMap (ZMod p) E)).eval x} : Set E).ncard
      = if Algebra.trace (ZMod p) E ((h.map (algebraMap (ZMod p) E)).eval x) = 0 then p else 0 :=
  artin_schreier_fiber_ncard _

/-- `∑ x, if Q x then p else 0 = p * #{x | Q x}`. -/
theorem sum_ite_eq_mul_ncard (Q : E → Prop) [DecidablePred Q] :
    (∑ x : E, (if Q x then (p : ℕ) else 0)) = p * ({x : E | Q x} : Set E).ncard := by
  have h1 : (∑ x : E, (if Q x then (p : ℕ) else 0)) = (Finset.univ.filter Q).card * p := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have h2 : ({x : E | Q x} : Set E).ncard = (Finset.univ.filter Q).card := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext x
    simp
  rw [h1, h2, mul_comm]

/-- The point count of `{(x, z) | z ^ p - z = h x}` in terms of the trace level set. -/
theorem ncard_AS_set (h : Polynomial (ZMod p)) :
    ({z : E × E | z.2 ^ p - z.2 = (h.map (algebraMap (ZMod p) E)).eval z.1} : Set (E × E)).ncard
      = p * ({x : E | Algebra.trace (ZMod p) E ((h.map (algebraMap (ZMod p) E)).eval x) = 0}
          : Set E).ncard := by
  rw [ncard_prod_eq_sum (fun x z => z ^ p - z = (h.map (algebraMap (ZMod p) E)).eval x),
    Finset.sum_congr rfl (fun x _ => ncard_fiber_eval h x), sum_ite_eq_mul_ncard]


/-- A non-trivial additive character of `ZMod p` has vanishing sum (`p` prime). -/
theorem sum_psi_eq_zero (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1) :
    (∑ y : ZMod p, ψ y) = 0 := by
  obtain ⟨y₀, hy₀⟩ := AddChar.ne_one_iff.mp hψ
  have h1 : (∑ z : ZMod p, ψ (z + y₀)) = ∑ z : ZMod p, ψ z :=
    Fintype.sum_equiv (Equiv.addRight y₀) (fun z => ψ (z + y₀)) (fun z => ψ z)
      (fun z => rfl)
  rw [Finset.sum_congr rfl (fun z _ => AddChar.map_add_eq_mul ψ z y₀)] at h1
  rw [← Finset.sum_mul] at h1
  have h3 : (ψ y₀ - 1) * (∑ z : ZMod p, ψ z) = 0 := by
    rw [sub_mul, one_mul, mul_comm (ψ y₀), h1, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (sub_eq_zero.mp h) hy₀
  · exact h

/-- The Artin--Schreier character sum, expanded over the level sets of the trace. -/
theorem char_sum_eq_level_sum (ψ : AddChar (ZMod p) ℂ) (g : Polynomial (ZMod p)) :
    (∑ a : E, ψ (Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a)))
      = ∑ y : ZMod p,
          (({a : E | Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a) = y}
            : Set E).ncard : ℂ) * ψ y := by
  classical
  have hsum : (∑ a : E, ψ (Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a)))
      = ∑ q : (Σ y : ZMod p, {a : E // Algebra.trace (ZMod p) E
            ((g.map (algebraMap (ZMod p) E)).eval a) = y}), ψ q.1 :=
    Fintype.sum_equiv (Equiv.sigmaFiberEquiv
        (fun a : E => Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a))).symm
      (fun a => ψ (Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a)))
      (fun q => ψ q.1) (fun a => rfl)
  rw [hsum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun y _ => ?_
  trans (∑ _a : {a : E // Algebra.trace (ZMod p) E
        ((g.map (algebraMap (ZMod p) E)).eval a) = y}, ψ y)
  · exact Finset.sum_congr rfl fun a _ => rfl
  · rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    congr 1
    exact congrArg Nat.cast (Set.fintypeCard_eq_ncard ({a : E | Algebra.trace (ZMod p) E
      ((g.map (algebraMap (ZMod p) E)).eval a) = y} : Set E))

/-- The level sets of a `ZMod p`-valued map on `E` partition `E`. -/
theorem sum_ncard_level (f : E → ZMod p) :
    (∑ y : ZMod p, ({a : E | f a = y} : Set E).ncard) = Fintype.card E := by
  classical
  have h1 : (∑ y : ZMod p, ({a : E | f a = y} : Set E).ncard)
      = ∑ y : ZMod p, Fintype.card {a : E // f a = y} :=
    Finset.sum_congr rfl fun y _ => (Set.fintypeCard_eq_ncard _).symm
  rw [h1, ← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)

/-- Norm of a real, viewed in `ℂ`. -/
theorem norm_complex_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  calc ‖(r : ℂ)‖ = Real.sqrt (‖(r : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by rw [h]
    _ = |r| := Real.sqrt_sq_eq_abs r


/-- The non-degeneracy condition of the point-count hypothesis is automatic in degree `< p`. -/
theorem not_const_mul_pow_of_degree_lt (p : ℕ) [Fact p.Prime] (d : ℕ) (hdp : d < p)
    {g : Polynomial (ZMod p)} (hg1 : 1 ≤ g.natDegree) (hgd : g.natDegree ≤ d) (c : ZMod p) :
    ∀ q : ℕ, q.Prime → q ∣ p → ∀ (a : ZMod p) (h : Polynomial (ZMod p)),
      g - Polynomial.C c ≠ Polynomial.C a * h ^ q := by
  intro q hq hqp a h heq
  have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp hqp
  rw [hqeq] at heq
  have hdeg : (g - Polynomial.C c).natDegree = g.natDegree := by
    have hlt : (Polynomial.C c : Polynomial (ZMod p)).natDegree < g.natDegree := by
      rw [Polynomial.natDegree_C]; omega
    exact Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt
  have hprod : (Polynomial.C a * h ^ p : Polynomial (ZMod p)).natDegree = 0 ∨
      p ≤ (Polynomial.C a * h ^ p).natDegree := by
    by_cases ha : a = 0
    · left; rw [ha, Polynomial.C_0, zero_mul, Polynomial.natDegree_zero]
    · by_cases hh : h.natDegree = 0
      · left
        rw [Polynomial.natDegree_C_mul ha, Polynomial.natDegree_pow, hh, mul_zero]
      · right
        rw [Polynomial.natDegree_C_mul ha, Polynomial.natDegree_pow]
        calc p = p * 1 := (mul_one p).symm
          _ ≤ p * h.natDegree := Nat.mul_le_mul_left p (Nat.pos_of_ne_zero hh)
  rw [← heq] at hprod
  rcases hprod with h0 | hge
  · rw [hdeg] at h0; omega
  · rw [hdeg] at hge; omega

/-- In the odd case the point-count hypothesis controls every trace level set:
shifting the polynomial by a constant moves the zero level set to the level set of
`[E : F_p] · c`. -/
theorem level_ncard_bound.{u} (p : ℕ) [Fact p.Prime] (d : ℕ) (hdp : d < p) {C₀ : ℝ}
    (hC₀ : ∀ {E : Type u} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
      [Module.Finite (ZMod p) E] [Module.Free (ZMod p) E],
      d < p → 2 ∣ Module.finrank (ZMod p) E →
      ∀ (g : Polynomial (ZMod p)), 1 ≤ g.natDegree → g.natDegree ≤ d →
      (∀ q : ℕ, q.Prime → q ∣ p → ∀ (a : ZMod p) (h : Polynomial (ZMod p)),
        g ≠ Polynomial.C a * h ^ q) →
      |(({z : E × E | z.2 ^ p - z.2 = (g.map (algebraMap (ZMod p) E)).eval z.1} : Set (E × E)).ncard : ℝ)
          - (Fintype.card E : ℝ)|
        ≤ C₀ * Real.sqrt ((Fintype.card E : ℕ) : ℝ))
    {E : Type u} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    [Module.Finite (ZMod p) E] [Module.Free (ZMod p) E]
    (heven : 2 ∣ Module.finrank (ZMod p) E) (hnd : ¬ p ∣ Module.finrank (ZMod p) E)
    (g : Polynomial (ZMod p)) (hg1 : 1 ≤ g.natDegree) (hgd : g.natDegree ≤ d) :
    ∀ y : ZMod p,
      |(p : ℝ) * (({a : E | Algebra.trace (ZMod p) E
          ((g.map (algebraMap (ZMod p) E)).eval a) = y} : Set E).ncard : ℝ)
        - (Fintype.card E : ℝ)| ≤ C₀ * Real.sqrt (Fintype.card E : ℝ) := by
  have hcount : ∀ c : ZMod p,
      |(p : ℝ) * (({a : E | Algebra.trace (ZMod p) E
          ((g.map (algebraMap (ZMod p) E)).eval a)
            = ((Module.finrank (ZMod p) E : ℕ) : ZMod p) * c} : Set E).ncard : ℝ)
        - (Fintype.card E : ℝ)| ≤ C₀ * Real.sqrt (Fintype.card E : ℝ) := by
    intro c
    have hdeg : (g - Polynomial.C c).natDegree = g.natDegree := by
      have hlt : (Polynomial.C c : Polynomial (ZMod p)).natDegree < g.natDegree := by
        rw [Polynomial.natDegree_C]; omega
      exact Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt
    have hdeg1 : 1 ≤ (g - Polynomial.C c).natDegree := by rw [hdeg]; exact hg1
    have hdegd : (g - Polynomial.C c).natDegree ≤ d := by rw [hdeg]; exact hgd
    have hb := hC₀ (E := E) hdp heven (g - Polynomial.C c) hdeg1 hdegd
      (not_const_mul_pow_of_degree_lt p d hdp hg1 hgd c)
    have hass := ncard_AS_set (p := p) (E := E) (g - Polynomial.C c)
    rw [hass] at hb
    have htr : ∀ x : E, Algebra.trace (ZMod p) E
        (((g - Polynomial.C c).map (algebraMap (ZMod p) E)).eval x)
        = Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval x)
          - ((Module.finrank (ZMod p) E : ℕ) : ZMod p) * c := by
      intro x
      rw [Polynomial.map_sub, Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_C, map_sub,
        Algebra.trace_algebraMap, nsmul_eq_mul]
    have hset : ({x : E | Algebra.trace (ZMod p) E
          (((g - Polynomial.C c).map (algebraMap (ZMod p) E)).eval x) = 0} : Set E)
        = {x : E | Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval x)
            = ((Module.finrank (ZMod p) E : ℕ) : ZMod p) * c} := by
      ext x
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, htr x, sub_eq_zero]
    rw [hset, Nat.cast_mul] at hb
    exact hb
  have hfin_ne : ((Module.finrank (ZMod p) E : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    exact hnd ((ZMod.natCast_eq_zero_iff _ p).mp h0)
  intro y
  obtain ⟨c, hc⟩ : ∃ c : ZMod p, ((Module.finrank (ZMod p) E : ℕ) : ZMod p) * c = y :=
    ⟨((Module.finrank (ZMod p) E : ℕ) : ZMod p)⁻¹ * y, by
      rw [← mul_assoc, mul_inv_cancel₀ hfin_ne, one_mul]⟩
  rw [← hc]
  exact hcount c



/-! ## The Artin--Schreier level sets and the Stepanov bound

The proof of the extension bound below uses the unconditional Artin--Schreier point count of
`Commons.NumberTheory.ArtinSchreier.count_upper` (Stepanov's method in characteristic `p`), which
bounds the number of `x` with `Tr (f x) = 0` over *every* finite field of characteristic `p`.
Shifting `g` by a constant `c` identifies the level set `Tr (g a) = t` with the zero set of
`Tr ((g - c) a)`, where `c = t · n⁻¹` (`n = [E : F_p]`, invertible because `p ∤ n`); Fourier
inversion on `ZMod p` then turns the equi-distribution of the level sets into the `O(√(#E))`
bound for the character sum.  This proves the statement without using the hypothesis `hpc`. -/

/-- The absolute trace of a value of a polynomial with coefficients in `E` is computed by the
polynomial `Tf` (the additive analogue of the norm): `Tf p n f = ∑_{i<n} f ^ (p ^ i)`. -/
theorem algebraMap_trace_eq_Tf_eval {E : Type*} [Field E] [Fintype E] [DecidableEq E]
    [Algebra (ZMod p) E] [Module.Finite (ZMod p) E] [Module.Free (ZMod p) E]
    (n : ℕ) (hfnr : Module.finrank (ZMod p) E = n) (hcard : Fintype.card E = p ^ n)
    (f : Polynomial E) (a : E) :
    algebraMap (ZMod p) E (Algebra.trace (ZMod p) E (f.eval a)) = (Tf p n f).eval a := by
  haveI hchar : CharP E p := charP_of_algebra (p := p) (E := E)
  rw [FiniteField.algebraMap_trace_eq_sum_pow (ZMod p) E (f.eval a), hfnr]
  rw [eval_Tf_eq, psiMap_apply]
  simp only [natCard_zmod]

/-- The level set `Tr (g a) = t` is the zero set of the trace of the shifted polynomial
`g - c` with `c = t · n⁻¹` (`n = [E : F_p]`, invertible because `p ∤ n`). -/
theorem trace_level_set_eq {E : Type*} [Field E] [Fintype E] [DecidableEq E]
    [Algebra (ZMod p) E] [Module.Finite (ZMod p) E] [Module.Free (ZMod p) E]
    (n : ℕ) (hfnr : Module.finrank (ZMod p) E = n) (hcard : Fintype.card E = p ^ n)
    (hnz : ((n : ℕ) : ZMod p) ≠ 0)
    (g : Polynomial (ZMod p)) (t : ZMod p) :
    ({a : E | Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a) = t} : Set E)
      = {a : E | (Tf p n ((g - Polynomial.C (t * ((n : ℕ) : ZMod p)⁻¹)).map
            (algebraMap (ZMod p) E))).eval a = 0} := by
  ext a
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  have hkey := algebraMap_trace_eq_Tf_eval (p := p) (E := E) n hfnr hcard
    (((g - Polynomial.C (t * ((n : ℕ) : ZMod p)⁻¹)).map (algebraMap (ZMod p) E))) a
  rw [← hkey]
  have hsplit : (((g - Polynomial.C (t * ((n : ℕ) : ZMod p)⁻¹)).map
      (algebraMap (ZMod p) E))).eval a
      = (g.map (algebraMap (ZMod p) E)).eval a
        - algebraMap (ZMod p) E (t * ((n : ℕ) : ZMod p)⁻¹) := by
    rw [Polynomial.map_sub, Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_C]
  have hmul : ((n : ZMod p) * (t * ((n : ℕ) : ZMod p)⁻¹)) = t := by
    rw [← mul_assoc, mul_comm ((n : ZMod p)) t, mul_assoc, mul_inv_cancel₀ hnz, mul_one]
  rw [hsplit, map_sub (Algebra.trace (ZMod p) E), Algebra.trace_algebraMap, nsmul_eq_mul,
    hfnr, hmul, ← (map_zero (algebraMap (ZMod p) E)),
    (FaithfulSMul.algebraMap_injective (ZMod p) E).eq_iff, sub_eq_zero]

/-- **Stepanov's bound for a level set.**  For a field `E` of degree `n` with `p ∤ n` and a
polynomial `g` of degree in `[1, d]`, `d < p`, each level set of `a ↦ Tr (g a)` has at most
`#E / p + 100 (d+1) (p+1) √#E` elements (for `#E` above the Stepanov threshold). -/
theorem level_ncard_le {E : Type*} [Field E] [Fintype E] [DecidableEq E]
    [Algebra (ZMod p) E] [Module.Finite (ZMod p) E] [Module.Free (ZMod p) E]
    (n d : ℕ) (hfnr : Module.finrank (ZMod p) E = n) (hcard : Fintype.card E = p ^ n)
    (hnz : ((n : ℕ) : ZMod p) ≠ 0) (hn1 : 1 ≤ n) (hd : 1 ≤ d) (hdp : d < p)
    (hbig : (4 * p * (d + 1) + 2 * p ^ 3 * (d + 1) + 4) ^ 2 ≤ Fintype.card E)
    (g : Polynomial (ZMod p)) (hg1 : 1 ≤ g.natDegree) (hgd : g.natDegree ≤ d) (t : ZMod p) :
    (({a : E | Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a) = t}
        : Set E).ncard : ℝ)
      ≤ (Fintype.card E : ℝ) / p
        + (100 * (d + 1) * (p + 1) : ℕ) * Real.sqrt (Fintype.card E : ℝ) := by
  haveI hchar : CharP E p := charP_of_algebra (p := p) (E := E)
  rw [trace_level_set_eq (p := p) n hfnr hcard hnz g t]
  set c : ZMod p := t * ((n : ℕ) : ZMod p)⁻¹ with hc
  set f : Polynomial E := (g - Polynomial.C c).map (algebraMap (ZMod p) E) with hf
  have hdeg : (g - Polynomial.C c).natDegree = g.natDegree := by
    refine Polynomial.natDegree_sub_eq_left_of_natDegree_lt ?_
    rw [Polynomial.natDegree_C]; omega
  have hf1 : 1 ≤ f.natDegree := by
    rw [hf, Polynomial.natDegree_map_eq_of_injective (algebraMap (ZMod p) E).injective, hdeg]
    exact hg1
  have hfd : f.natDegree ≤ d := by
    rw [hf, Polynomial.natDegree_map_eq_of_injective (algebraMap (ZMod p) E).injective, hdeg]
    exact hgd
  have hbound := count_upper (F := E) (p := p) (n := n) hn1 hcard d hd hdp f hf1 hfd hbig
  have h1 : ((({x : E | (Tf p n f).eval x = 0} : Set E).ncard : ℕ) : ℝ)
      ≤ ((Fintype.card E / p : ℕ) : ℝ)
        + ((100 * (d + 1) * (p + 1) * Nat.sqrt (Fintype.card E) : ℕ) : ℝ) := by
    exact_mod_cast hbound
  have h2 : ((Fintype.card E / p : ℕ) : ℝ) ≤ (Fintype.card E : ℝ) / p := Nat.cast_div_le
  have h3 : ((Nat.sqrt (Fintype.card E) : ℕ) : ℝ) ≤ Real.sqrt (Fintype.card E : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast Nat.sqrt_le' (Fintype.card E)
  have h4 : ((100 * (d + 1) * (p + 1) * Nat.sqrt (Fintype.card E) : ℕ) : ℝ)
      ≤ (100 * (d + 1) * (p + 1) : ℕ) * Real.sqrt (Fintype.card E : ℝ) := by
    push_cast
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith

/-- The level set of the trace of `g` over `E`. -/
def traceLevel {E : Type*} [Field E] [Algebra (ZMod p) E] [Module.Finite (ZMod p) E]
    [Module.Free (ZMod p) E] (g : Polynomial (ZMod p)) (t : ZMod p) : Set E :=
  {a : E | Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a) = t}

/-- **The Artin--Schreier extension bound.**  Given the point-count hypothesis `hpc` (the
Alexandrov--Artin--Schreier curve `z ^ p - z = g x` has `q + O(√q)` points over every
even-degree field), the Artin--Schreier character sums over *every* finite field `E` with
`p ∤ [E : F_p]` satisfy the Weil bound `O(√#E)`. -/
theorem artin_schreier_extension_bound (p : ℕ) [Fact p.Prime] (d : ℕ) (hd : 1 ≤ d) (hdp : d < p)
    (hpc : ∀ (d' : ℕ), 1 ≤ d' → ∃ C : ℝ, 0 < C ∧
      ∀ {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
        [Module.Finite (ZMod p) E] [Module.Free (ZMod p) E],
        d' < p → 2 ∣ Module.finrank (ZMod p) E →
        ∀ (g : Polynomial (ZMod p)), 1 ≤ g.natDegree → g.natDegree ≤ d' →
        (∀ q : ℕ, q.Prime → q ∣ p → ∀ (a : ZMod p) (h : Polynomial (ZMod p)),
          g ≠ Polynomial.C a * h ^ q) →
        |(({z : E × E | z.2 ^ p - z.2 = (g.map (algebraMap (ZMod p) E)).eval z.1} : Set (E × E)).ncard : ℝ)
            - (Fintype.card E : ℝ)|
          ≤ C * Real.sqrt ((Fintype.card E : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : AddChar (ZMod p) ℂ), ψ ≠ 1 → ∀ (g : Polynomial (ZMod p)),
      1 ≤ g.natDegree → g.natDegree ≤ d →
      ∀ (n : ℕ), 0 < n → ¬ p ∣ n → ∀ (E : Type*) [Field E] [Fintype E] [DecidableEq E]
        [Algebra (ZMod p) E] [Module.Finite (ZMod p) E] [Module.Free (ZMod p) E],
        Module.finrank (ZMod p) E = n →
        ‖∑ a : E, ψ (Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a))‖
        ≤ C * Real.sqrt (Fintype.card E : ℝ) := by
  classical
  set P : ℕ := 4 * p * (d + 1) + 2 * p ^ 3 * (d + 1) + 4 with hPdef
  set C₀ : ℝ := ((100 * (d + 1) * (p + 1) : ℕ) : ℝ) with hC₀def
  have hPpos : (0 : ℝ) < (P : ℝ) := by
    rw [hPdef]
    exact_mod_cast (by omega : 0 < 4 * p * (d + 1) + 2 * p ^ 3 * (d + 1) + 4)
  have hC₀pos : 0 < C₀ := by
    rw [hC₀def]
    exact_mod_cast (by positivity : 0 < 100 * (d + 1) * (p + 1))
  refine ⟨max 1 (max (P : ℝ) ((p : ℝ) * ((p : ℝ) - 1) * C₀ + 1)), ?_, ?_⟩
  · exact lt_max_of_lt_left zero_lt_one
  · intro ψ hψ g hg1 hgd n hnpos hnpdvd E _ _ _ _ _ _ hfnr
    haveI hchar : CharP E p := charP_of_algebra (p := p) (E := E)
    have hn1 : 1 ≤ n := hnpos
    have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hcard : Fintype.card E = p ^ n := by
      rw [Module.card_eq_pow_finrank (K := ZMod p) (V := E), ZMod.card, hfnr]
    have hnz : ((n : ℕ) : ZMod p) ≠ 0 := fun h => hnpdvd ((ZMod.natCast_eq_zero_iff n p).mp h)
    have hQnn : (0 : ℝ) ≤ (Fintype.card E : ℝ) := Nat.cast_nonneg _
    have hsQnn : 0 ≤ Real.sqrt (Fintype.card E : ℝ) := Real.sqrt_nonneg _
    have hQpos : (0 : ℝ) < (Fintype.card E : ℝ) := by
      have := Fintype.one_lt_card (α := E); exact_mod_cast (by omega : 0 < Fintype.card E)
    have hcastp : (((p - 1 : ℕ) : ℝ)) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp1, Nat.cast_one]
    by_cases hbig : P ^ 2 ≤ Fintype.card E
    · have hPbig : (4 * p * (d + 1) + 2 * p ^ 3 * (d + 1) + 4) ^ 2 ≤ Fintype.card E := by
        simpa only [← hPdef] using hbig
      have hupper : ∀ t : ZMod p,
          ((traceLevel (p := p) (E := E) g t).ncard : ℝ)
            ≤ (Fintype.card E : ℝ) / p + C₀ * Real.sqrt (Fintype.card E : ℝ) := by
        intro t
        have h := level_ncard_le (p := p) (E := E) n d hfnr hcard hnz hn1 hd hdp hPbig g hg1 hgd t
        simpa only [traceLevel, hC₀def] using h
      have hsumN : ∑ t : ZMod p, ((traceLevel (p := p) (E := E) g t).ncard : ℝ)
          = (Fintype.card E : ℝ) := by
        have h := sum_ncard_level (p := p) (E := E)
          (fun a : E => Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a))
        simp only [traceLevel] at h ⊢
        exact_mod_cast h
      have hN : ∀ t : ZMod p,
          |((traceLevel (p := p) (E := E) g t).ncard : ℝ) - (Fintype.card E : ℝ) / p|
            ≤ (((p - 1 : ℕ) : ℝ)) * (C₀ * Real.sqrt (Fintype.card E : ℝ)) := by
        intro t
        set u : ℝ := (Fintype.card E : ℝ) / p with hudef
        set v : ℝ := C₀ * Real.sqrt (Fintype.card E : ℝ) with hvdef
        have huQ : u * p = (Fintype.card E : ℝ) := by
          rw [hudef]; exact div_mul_cancel₀ _ hp0
        have hvnn : 0 ≤ v := by rw [hvdef]; exact mul_nonneg hC₀pos.le hsQnn
        have htu : ((traceLevel (p := p) (E := E) g t).ncard : ℝ) ≤ u + v := hupper t
        have hcarderase : (Finset.univ.erase t).card = p - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ, ZMod.card]
        have herase := Finset.sum_erase_add (Finset.univ : Finset (ZMod p))
          (fun t' => ((traceLevel (p := p) (E := E) g t').ncard : ℝ)) (Finset.mem_univ t)
        rw [hsumN] at herase
        have hbound : ∑ t' ∈ Finset.univ.erase t,
              ((traceLevel (p := p) (E := E) g t').ncard : ℝ)
            ≤ (((p - 1 : ℕ) : ℝ)) * (u + v) := by
          calc ∑ t' ∈ Finset.univ.erase t, ((traceLevel (p := p) (E := E) g t').ncard : ℝ)
              ≤ ∑ _t' ∈ Finset.univ.erase t, (u + v) :=
                Finset.sum_le_sum (fun t' _ => hupper t')
            _ = (((p - 1 : ℕ) : ℝ)) * (u + v) := by
                rw [Finset.sum_const, hcarderase, nsmul_eq_mul]
        have hkey : (((p - 1 : ℕ) : ℝ)) * u + u = (Fintype.card E : ℝ) := by
          rw [hcastp]
          calc ((p : ℝ) - 1) * u + u = (p : ℝ) * u := by ring
            _ = u * p := by ring
            _ = (Fintype.card E : ℝ) := huQ
        have hlow : u - (((p - 1 : ℕ) : ℝ)) * v
            ≤ ((traceLevel (p := p) (E := E) g t).ncard : ℝ) := by
          linarith [herase, hbound, hkey]
        have hup : ((traceLevel (p := p) (E := E) g t).ncard : ℝ) - u
            ≤ (((p - 1 : ℕ) : ℝ)) * v := by
          have h1 : (1 : ℝ) ≤ (((p - 1 : ℕ) : ℝ)) := by
            rw [hcastp]; linarith [show (2 : ℝ) ≤ (p : ℝ) by exact_mod_cast (Fact.out : p.Prime).two_le]
          nlinarith [htu, hvnn]
        exact abs_le.mpr ⟨by linarith [hlow], by linarith [hup]⟩
      have hS : (∑ a : E, ψ (Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a)))
          = ∑ t : ZMod p,
              ((((traceLevel (p := p) (E := E) g t).ncard : ℂ) - (Fintype.card E : ℂ) / p) * ψ t) := by
        rw [char_sum_eq_level_sum ψ g]
        simp only [traceLevel]
        have hpoint : ∀ t : ZMod p,
            ((({a : E | Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a) = t}
              : Set E).ncard : ℂ) * ψ t)
            = (((({a : E | Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a) = t}
                : Set E).ncard : ℂ) - (Fintype.card E : ℂ) / p) * ψ t)
              + ((Fintype.card E : ℂ) / p) * ψ t := by
          intro t; ring
        rw [Finset.sum_congr rfl (fun t _ => hpoint t), Finset.sum_add_distrib, ← Finset.mul_sum,
          sum_psi_eq_zero ψ hψ, mul_zero, add_zero]
      calc ‖∑ a : E, ψ (Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a))‖
          = ‖∑ t : ZMod p,
              ((((traceLevel (p := p) (E := E) g t).ncard : ℂ) - (Fintype.card E : ℂ) / p) * ψ t)‖ := by
            rw [hS]
        _ ≤ ∑ t : ZMod p,
              ‖((((traceLevel (p := p) (E := E) g t).ncard : ℂ) - (Fintype.card E : ℂ) / p) * ψ t)‖ :=
            norm_sum_le _ _
        _ = ∑ t : ZMod p,
              |((traceLevel (p := p) (E := E) g t).ncard : ℝ) - (Fintype.card E : ℝ) / p| := by
            refine Finset.sum_congr rfl (fun t _ => ?_)
            rw [norm_mul, AddChar.norm_apply, mul_one]
            have hcast : (((traceLevel (p := p) (E := E) g t).ncard : ℂ) - (Fintype.card E : ℂ) / p)
                = ((((traceLevel (p := p) (E := E) g t).ncard : ℝ) - (Fintype.card E : ℝ) / p) : ℝ) := by
              push_cast; ring
            rw [hcast]
            exact norm_complex_ofReal _
        _ ≤ ∑ _t : ZMod p, (((p - 1 : ℕ) : ℝ)) * (C₀ * Real.sqrt (Fintype.card E : ℝ)) :=
            Finset.sum_le_sum (fun t _ => hN t)
        _ = ((p : ℝ) * (((p - 1 : ℕ) : ℝ)) * C₀) * Real.sqrt (Fintype.card E : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
            ring
        _ ≤ max 1 (max (P : ℝ) ((p : ℝ) * ((p : ℝ) - 1) * C₀ + 1))
              * Real.sqrt (Fintype.card E : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ hsQnn
            rw [hcastp]
            linarith [le_max_right (1 : ℝ) (max (P : ℝ) ((p : ℝ) * ((p : ℝ) - 1) * C₀ + 1)),
              le_max_right (P : ℝ) ((p : ℝ) * ((p : ℝ) - 1) * C₀ + 1)]
    · have hlt : Fintype.card E < P ^ 2 := Nat.lt_of_not_le hbig
      have hsmall : (Fintype.card E : ℝ) < (P : ℝ) * Real.sqrt (Fintype.card E : ℝ) := by
        have hltR : Real.sqrt (Fintype.card E : ℝ) < (P : ℝ) := by
          rw [Real.sqrt_lt' hPpos]
          exact_mod_cast hlt
        have h2 : Real.sqrt (Fintype.card E : ℝ) * Real.sqrt (Fintype.card E : ℝ)
            = (Fintype.card E : ℝ) := by
          rw [← pow_two]; exact Real.sq_sqrt hQnn
        calc (Fintype.card E : ℝ)
            = Real.sqrt (Fintype.card E : ℝ) * Real.sqrt (Fintype.card E : ℝ) := h2.symm
          _ < (P : ℝ) * Real.sqrt (Fintype.card E : ℝ) :=
              mul_lt_mul_of_pos_right hltR (Real.sqrt_pos.mpr hQpos)
      have htriv : ‖∑ a : E, ψ (Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a))‖
          ≤ (Fintype.card E : ℝ) := by
        calc ‖∑ a : E, ψ (Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a))‖
            ≤ ∑ a : E, ‖ψ (Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a))‖ :=
              norm_sum_le _ _
          _ = ∑ _a : E, (1 : ℝ) := by
              refine Finset.sum_congr rfl (fun a _ => ?_)
              exact AddChar.norm_apply ψ _
          _ = (Fintype.card E : ℝ) := by simp
      refine htriv.trans ?_
      have hPle : (P : ℝ) ≤ max 1 (max (P : ℝ) ((p : ℝ) * ((p : ℝ) - 1) * C₀ + 1)) :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      exact hsmall.le.trans (mul_le_mul_of_nonneg_right hPle hsQnn)
end Aux

end Commons.NumberTheory.FunctionField
