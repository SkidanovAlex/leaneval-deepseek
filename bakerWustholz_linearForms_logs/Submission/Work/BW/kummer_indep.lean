import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.kummer_crux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! ## Multi-quadratic Kummer theory (BW §9/§20)

`Work.BW.kummer_indep`: under `KummerCond η` and `ρ i ^ 2 = φ (η i)`, the `2 ^ r` products
`∏ i, ρ i ^ (ε i : ℕ)` are linearly independent over `φ(K)`.

The heart is `kummer_crux` (separate module): a `φ(K)`-linear combination `x` of the products
with `x ^ 2 = φ a₀` forces `a₀` times some product of the `η`'s to be a square. The induction
below peels off coordinate `0`, applies the crux to `ρ 0`, and contradicts `KummerCond`. -/

namespace Work.BW

open Complex
open scoped Classical
open scoped Pointwise

private lemma pow_mod (ρ : ℂ) (m : ℕ) : ρ ^ m = (ρ ^ 2) ^ (m / 2) * ρ ^ (m % 2) := by
  conv_lhs => rw [← Nat.div_add_mod m 2]
  rw [pow_add, pow_mul]

private lemma div2_mul (a b : Fin 2) : ((a : ℕ) + (b : ℕ)) / 2 = (a : ℕ) * (b : ℕ) := by
  fin_cases a <;> fin_cases b <;> decide

/-- The set of `φ(K)`-linear combinations of the `2^r` products `∏ i, ρ i ^ (ε i : ℕ)`. -/
def ksp {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (ρ : Fin r → ℂ) : Set ℂ :=
  {x | ∃ c : (Fin r → Fin 2) → K, x = ∑ ε, φ (c ε) * ∏ i, ρ i ^ (ε i : ℕ)}

private lemma ksp_eq_span {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (ρ : Fin r → ℂ) :
    letI : Algebra K ℂ := φ.toAlgebra
    ksp φ ρ = (Submodule.span K (Set.range (fun ε : Fin r → Fin 2 => ∏ i, ρ i ^ (ε i : ℕ))) : Set ℂ) := by
  letI : Algebra K ℂ := φ.toAlgebra
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    refine Submodule.sum_mem _ fun ε _ => ?_
    rw [← RingHom.algebraMap_toAlgebra φ, ← Algebra.smul_def]
    exact Submodule.smul_mem _ (c ε) (Submodule.subset_span (Set.mem_range_self ε))
  · intro hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    refine ⟨c, ?_⟩
    rw [← hc]
    apply Finset.sum_congr rfl; intro ε _
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]

/-- Multiplication rule: `(∏ ρ^ε)(∏ ρ^δ) = φ(∏ η^{ε·δ}) · ∏ ρ^{ε+δ}`. -/
private lemma ksp_mul_rule {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (η : Fin r → K)
    (ρ : Fin r → ℂ) (hρ : ∀ i, ρ i ^ 2 = φ (η i)) (ε δ : Fin r → Fin 2) :
    (∏ i, ρ i ^ (ε i : ℕ)) * (∏ i, ρ i ^ (δ i : ℕ)) =
      φ (∏ i, η i ^ ((ε i : ℕ) * (δ i : ℕ))) * (∏ i, ρ i ^ ((ε + δ) i : ℕ)) := by
  rw [map_prod φ, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Pi.add_apply, Fin.val_add]
  rw [← pow_add]
  rw [show ρ i ^ ((ε i : ℕ) + (δ i : ℕ)) =
        (ρ i ^ 2) ^ (((ε i : ℕ) + (δ i : ℕ)) / 2) * ρ i ^ (((ε i : ℕ) + (δ i : ℕ)) % 2)
      from pow_mod (ρ i) ((ε i : ℕ) + (δ i : ℕ)), hρ i, ← map_pow, div2_mul (ε i) (δ i)]

/-- The span of the products is closed under multiplication. -/
lemma ksp_mul {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (η : Fin r → K)
    (ρ : Fin r → ℂ) (hρ : ∀ i, ρ i ^ 2 = φ (η i)) {x y : ℂ}
    (hx : x ∈ ksp φ ρ) (hy : y ∈ ksp φ ρ) : x * y ∈ ksp φ ρ := by
  letI : Algebra K ℂ := φ.toAlgebra
  have hS := ksp_eq_span φ ρ
  rw [hS] at hx hy ⊢
  have hmul : (Set.range (fun ε : Fin r → Fin 2 => ∏ i, ρ i ^ (ε i : ℕ))) *
      (Set.range (fun ε : Fin r → Fin 2 => ∏ i, ρ i ^ (ε i : ℕ))) ⊆
      (Submodule.span K (Set.range (fun ε : Fin r → Fin 2 => ∏ i, ρ i ^ (ε i : ℕ))) : Set ℂ) := by
    rintro z ⟨a, ⟨ε, rfl⟩, b, ⟨δ, rfl⟩, rfl⟩
    show (∏ i, ρ i ^ (ε i : ℕ)) * (∏ i, ρ i ^ (δ i : ℕ)) ∈
      (Submodule.span K (Set.range (fun ε : Fin r → Fin 2 => ∏ i, ρ i ^ (ε i : ℕ))) : Set ℂ)
    rw [ksp_mul_rule φ η ρ hρ, ← RingHom.algebraMap_toAlgebra φ, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (ε + δ)))
  have hSS : (Submodule.span K (Set.range (fun ε : Fin r → Fin 2 => ∏ i, ρ i ^ (ε i : ℕ)))) *
      (Submodule.span K (Set.range (fun ε : Fin r → Fin 2 => ∏ i, ρ i ^ (ε i : ℕ)))) ≤
      (Submodule.span K (Set.range (fun ε : Fin r → Fin 2 => ∏ i, ρ i ^ (ε i : ℕ)))) := by
    rw [Submodule.span_mul_span]
    exact Submodule.span_le.mpr hmul
  exact hSS (Submodule.mul_mem_mul hx hy)

/-- The span of the products is a field: every nonzero element is invertible inside it. -/
lemma ksp_inv {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (η : Fin r → K)
    (ρ : Fin r → ℂ) (hρ : ∀ i, ρ i ^ 2 = φ (η i)) {y : ℂ}
    (hy : y ∈ ksp φ ρ) (hy0 : y ≠ 0) : y⁻¹ ∈ ksp φ ρ := by
  letI : Algebra K ℂ := φ.toAlgebra
  have hkS : ksp φ ρ =
      (Submodule.span K (Set.range (fun ε : Fin r → Fin 2 => ∏ i, ρ i ^ (ε i : ℕ))) : Set ℂ) :=
    ksp_eq_span φ ρ
  set S := Submodule.span K (Set.range (fun ε : Fin r → Fin 2 => ∏ i, ρ i ^ (ε i : ℕ))) with hSdef
  have hyS : y ∈ S := by rw [hkS] at hy; exact hy
  haveI : FiniteDimensional K S :=
    FiniteDimensional.span_of_finite K (Set.finite_range _)
  have hmul : ∀ v ∈ S, ∀ w ∈ S, v * w ∈ S := by
    intro v hv w hw
    have h := ksp_mul φ η ρ hρ (x := v) (y := w) (by rw [hkS]; exact hv) (by rw [hkS]; exact hw)
    rwa [hkS] at h
  have h1mem : (1 : ℂ) ∈ S := by
    have h : (∏ i, ρ i ^ (((0 : Fin r → Fin 2) i) : ℕ)) ∈
        (Submodule.span K (Set.range (fun ε : Fin r → Fin 2 => ∏ i, ρ i ^ (ε i : ℕ)))) :=
      Submodule.subset_span (Set.mem_range_self (0 : Fin r → Fin 2))
    simpa using h
  let m : S →ₗ[K] S :=
    { toFun := fun v => ⟨y * v.1, hmul y hyS v.1 v.2⟩
      map_add' := by intro a b; ext; simp [mul_add]
      map_smul' := by
        intro c a
        apply Subtype.ext
        show y * (c • (a : ℂ)) = c • (y * (a : ℂ))
        rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
        ring }
  have hinj : Function.Injective m := by
    intro a b hab
    have h1 : y * a.1 = y * b.1 := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel₀ hy0 h1)
  have hsurj := LinearMap.surjective_of_injective hinj
  obtain ⟨v, hv⟩ := hsurj ⟨1, h1mem⟩
  have hv1 : y * v.1 = 1 := congrArg Subtype.val hv
  have hv2 : v.1 = y⁻¹ := by
    calc v.1 = 1 * v.1 := by rw [one_mul]
      _ = (y⁻¹ * y) * v.1 := by rw [inv_mul_cancel₀ hy0]
      _ = y⁻¹ * (y * v.1) := by rw [mul_assoc]
      _ = y⁻¹ * 1 := by rw [hv1]
      _ = y⁻¹ := by rw [mul_one]
  rw [hkS, ← hv2]
  exact v.2

/-- The product over `Fin (r+1)` splits according to the `0`-th coordinate. -/
private lemma prod_cons {r : ℕ} (ρ : Fin (r+1) → ℂ) (e : Fin 2) (ε : Fin r → Fin 2) :
    (∏ i : Fin (r+1), ρ i ^ (((Fin.cons e ε : Fin (r+1) → Fin 2) i) : ℕ)) =
      ρ 0 ^ (e : ℕ) * ∏ i : Fin r, ρ i.succ ^ (ε i : ℕ) := by
  rw [Fin.prod_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

/-- Reindexing a sum over `Fin (r+1) → Fin 2` by the first coordinate. -/
private lemma sum_cons {M : Type*} [AddCommMonoid M] {r : ℕ}
    (f : (Fin (r+1) → Fin 2) → M) :
    (∑ γ : Fin (r+1) → Fin 2, f γ) = ∑ p : Fin 2 × (Fin r → Fin 2), f (Fin.cons p.1 p.2) := by
  symm
  refine Fintype.sum_equiv (Fin.consEquiv (fun _ => Fin 2))
    (fun p : Fin 2 × (Fin r → Fin 2) => f (Fin.cons p.1 p.2)) f (fun p => ?_)
  rw [show (Fin.consEquiv (fun _ => Fin 2)) p = Fin.cons p.1 p.2 from
    funext (fun i => by rw [Fin.consEquiv_apply])]

/-- Multi-quadratic Kummer independence (main induction). -/
theorem kummer_indep_aux {K : Type*} [Field K] :
    ∀ (r : ℕ) (φ : K →+* ℂ) (η : Fin r → K) (hη : ∀ i, η i ≠ 0)
      (hK : KummerCond η) (ρ : Fin r → ℂ) (hρ : ∀ i, ρ i ^ 2 = φ (η i))
      (a : (Fin r → Fin 2) → K),
      (∑ ε, φ (a ε) * ∏ i, ρ i ^ (ε i : ℕ)) = 0 → a = 0 := by
  intro r
  induction r with
  | zero =>
    intro φ η hη hK ρ hρ a ha
    funext ε
    have h1 : ∑ ε' : Fin 0 → Fin 2, φ (a ε') * ∏ i, ρ i ^ (ε' i : ℕ) = φ (a ε) := by
      have hc : ∀ x : Fin 0 → Fin 2, φ (a x) * ∏ i, ρ i ^ (x i : ℕ) = φ (a ε) := by
        intro x; rw [Subsingleton.elim x ε]; simp
      rw [Finset.sum_congr rfl (fun x _ => hc x)]; simp
    rw [h1] at ha
    exact RingHom.injective φ (by simpa using ha)
  | succ r ih =>
    intro φ η hη hK ρ hρ a ha
    set ρ' : Fin r → ℂ := fun i => ρ i.succ with hρ'e
    set η' : Fin r → K := fun i => η i.succ with hη'e
    have hρ' : ∀ i, ρ' i ^ 2 = φ (η' i) := fun i => hρ i.succ
    have hη' : ∀ i, η' i ≠ 0 := fun i => hη i.succ
    have hK' : KummerCond η' := by
      intro e he
      have he' : (Fin.cons 0 e : Fin (r+1) → Fin 2) ≠ 0 := by
        intro h0
        apply he
        funext i
        have := congrFun h0 i.succ
        simpa using this
      have h2 := hK (Fin.cons 0 e) he'
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero,
        one_mul] at h2
      exact h2
    have hind : ∀ (b : (Fin r → Fin 2) → K),
        (∑ ε, φ (b ε) * ∏ i, ρ' i ^ (ε i : ℕ)) = 0 → b = 0 :=
      ih φ η' hη' hK' ρ' hρ'
    set a0f : (Fin r → Fin 2) → K := fun ε => a (Fin.cons 0 ε) with ha0f
    set a1f : (Fin r → Fin 2) → K := fun ε => a (Fin.cons 1 ε) with ha1f
    set X : ℂ := ∑ ε, φ (a0f ε) * ∏ i, ρ' i ^ (ε i : ℕ) with hX
    set Y : ℂ := ∑ ε, φ (a1f ε) * ∏ i, ρ' i ^ (ε i : ℕ) with hY
    have hsplit : (∑ γ : Fin (r+1) → Fin 2, φ (a γ) * ∏ i, ρ i ^ (γ i : ℕ))
        = ∑ ε : Fin r → Fin 2, (φ (a0f ε) + φ (a1f ε) * ρ 0) * ∏ i, ρ' i ^ (ε i : ℕ) := by
      rw [sum_cons (fun γ : Fin (r+1) → Fin 2 => φ (a γ) * ∏ i, ρ i ^ (γ i : ℕ)),
        Fintype.sum_prod_type_right]
      apply Finset.sum_congr rfl; intro ε _
      rw [Fin.sum_univ_two]
      simp only [prod_cons ρ 0 ε, prod_cons ρ 1 ε, Fin.val_zero, pow_zero, mul_one,
        Fin.val_one, pow_one]
      have h0 : a (Fin.cons 0 ε) = a0f ε := by rw [ha0f]
      have h1 : a (Fin.cons 1 ε) = a1f ε := by rw [ha1f]
      rw [h0, h1]; ring
    have hrel : X + ρ 0 * Y = 0 := by
      have hXY : X + ρ 0 * Y =
          ∑ ε : Fin r → Fin 2, (φ (a0f ε) + φ (a1f ε) * ρ 0) * ∏ i, ρ' i ^ (ε i : ℕ) := by
        rw [hX, hY, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro ε _
        ring
      rw [hXY, ← hsplit, ha]
    by_cases hY0 : Y = 0
    · have hX0 : X = 0 := by rw [hY0, mul_zero, add_zero] at hrel; exact hrel
      have ha0 : a0f = 0 := hind a0f (by rw [← hX]; exact hX0)
      have ha1 : a1f = 0 := hind a1f (by rw [← hY]; exact hY0)
      funext γ
      rw [← Fin.cons_self_tail γ]
      by_cases h : γ 0 = 0
      · rw [h]; exact congrFun ha0 (Fin.tail γ)
      · rw [Fin.eq_one_of_ne_zero (γ 0) h]; exact congrFun ha1 (Fin.tail γ)
    · exfalso
      have hYmem : Y ∈ ksp φ ρ' := ⟨a1f, hY⟩
      have hXmem : X ∈ ksp φ ρ' := ⟨a0f, hX⟩
      have hYinv : Y⁻¹ ∈ ksp φ ρ' := ksp_inv φ η' ρ' hρ' hYmem hY0
      have hXneg : -X ∈ ksp φ ρ' := by
        refine ⟨fun ε => -a0f ε, ?_⟩
        rw [hX, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro ε _
        rw [map_neg]; ring
      have hXY0 : -X * Y⁻¹ = ρ 0 := by
        have h1 : ρ 0 * Y = -X := eq_neg_of_add_eq_zero_right hrel
        calc -X * Y⁻¹ = (ρ 0 * Y) * Y⁻¹ := by rw [h1]
          _ = ρ 0 := by rw [mul_assoc, mul_inv_cancel₀ hY0, mul_one]
      have hρ0mem : ρ 0 ∈ ksp φ ρ' := by
        have := ksp_mul φ η' ρ' hρ' hXneg hYinv
        rwa [hXY0] at this
      obtain ⟨c, hc⟩ := hρ0mem
      have hx : (∑ ε, φ (c ε) * ∏ i, ρ' i ^ (ε i : ℕ)) ^ 2 = φ (η 0) := by
        rw [← hc, hρ 0]
      obtain ⟨γ, u, hu⟩ := kummer_crux φ η' ρ' hρ' hind c (η 0) hx
      refine (hK (Fin.cons 1 γ) ?_) ?_
      · intro h0
        have := congrFun h0 0
        simpa using this
      · refine ⟨u, ?_⟩
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_one, pow_one]
        rw [show (∏ i : Fin r, η i.succ ^ (γ i : ℕ)) = ∏ i, η' i ^ (γ i : ℕ) from by rw [hη'e]]
        rw [hu, sq]

/-- Multi-quadratic Kummer theory: under `KummerCond η`, for any choice of square roots
`ρᵢ² = φ(ηᵢ)` the `2^r` products `∏ ρᵢ^{εᵢ}` are linearly independent over `φ(K)`. -/
theorem kummer_indep {K : Type*} [Field K] [NumberField K] {r : ℕ} (φ : K →+* ℂ)
    (η : Fin r → K) (hη : ∀ i, η i ≠ 0) (hK : KummerCond η) (ρ : Fin r → ℂ)
    (hρ : ∀ i, ρ i ^ 2 = φ (η i)) (a : (Fin r → Fin 2) → K)
    (ha : ∑ ε, φ (a ε) * ∏ i, ρ i ^ (ε i : ℕ) = 0) :
    a = 0 :=
  kummer_indep_aux r φ η hη hK ρ hρ a ha

end Work.BW
