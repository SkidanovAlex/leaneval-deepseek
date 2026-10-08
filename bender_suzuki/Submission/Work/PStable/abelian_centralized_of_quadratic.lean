/-
Feit--Thompson odd order drive: `Work.PStable.abelian_centralized_of_quadratic`.

Gorenstein, *Finite Groups*, 2.6.6 (quadratic minimal polynomial), in the `p`-stability form
used by `Work.PStable.condition_of_isPSolvable`: let `k` be an algebraically closed field of
characteristic `p ≠ 2`, `ρ : G → GL_k(V)`, `A ⊴ G` abelian with `p ∤ |A|`, and `x ∈ G` with
`x ^ p = 1` and `(ρ x - 1) ^ 2 = 0`.  Then `ρ x` commutes with `ρ a` for every `a ∈ A`, i.e.
`ρ [x,a] = 1`.

The proof is the classical one: since `p ∤ |A|`, the group algebra `k[A]` is semisimple, hence
(being commutative and finite dimensional over the algebraically closed field `k`) isomorphic to
a product of copies of `k`.  Its standard idempotents `e i` give a decomposition
`V = ⨁ i, P i V` with `P i = ρ (e i)`, and conjugation by `M = ρ x` permutes the `e i` (hence the
`P i`) along a permutation `σ` satisfying `σ ^ p = id`.  If `σ` moved `i`, the orbit would have
size `p ≥ 3`, and evaluating `(M - 1)^2 = 0` against the idempotent `P i` would force `P i = 0`;
hence `σ i = i` whenever `P i ≠ 0`.  The character relation `χ_{σ i} (α y) = χ_i y` (where
`α` is conjugation by `x` on `A` and `χ_i` is the `i`-th coordinate of the algebra isomorphism)
then shows `ρ (α a) = ρ a` for all `a ∈ A`, and `ρ [x,a] = ρ (α a) ρ (a)⁻¹ = 1`.
-/
import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PStable

open scoped BigOperators

set_option linter.style.haveILetI false

/-! ## Auxiliary linear algebra / algebra lemmas -/

/-- Pointwise decomposition of `g : ι → k` in the standard idempotents. -/
private lemma pi_decomp {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι] (g : ι → k) :
    g = ∑ i, g i • (Function.update (0 : ι → k) i 1) := by
  ext x
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single x]
  · rw [Pi.smul_apply, Function.update_self, smul_eq_mul, mul_one]
  · intro b _ hb
    rw [Pi.smul_apply, Function.update_of_ne (Ne.symm hb), Pi.zero_apply, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- Every `k`-algebra homomorphism `(ι → k) →ₐ[k] k` is an evaluation. -/
private lemma algHom_pi_eq_eval {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
    (φ : (ι → k) →ₐ[k] k) : ∃ j, φ = Pi.evalAlgHom k (fun _ => k) j := by
  classical
  let f : ι → (ι → k) := fun j => Function.update (0 : ι → k) j 1
  have hf_apply : ∀ j x, f j x = if x = j then (1:k) else 0 := by
    intro j x; simp only [f, Function.update_apply, Pi.zero_apply]
  have hf_self : ∀ j, f j j = 1 := by intro j; rw [hf_apply, if_pos rfl]
  have hf_ne : ∀ i j, i ≠ j → f j i = 0 := by
    intro i j h; rw [hf_apply, if_neg h]
  have hsum : (∑ j, f j) = (1 : ι → k) := by
    ext x
    rw [Finset.sum_apply, Pi.one_apply]
    rw [Finset.sum_eq_single x]
    · exact hf_self x
    · intro b _ hb; rw [hf_ne x b (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_univ x) h
  have h1 : (∑ j, φ (f j)) = 1 := by rw [← map_sum, hsum, map_one]
  have hidem : ∀ j, φ (f j) = 0 ∨ φ (f j) = 1 := by
    intro j
    have hsq : f j * f j = f j := by
      ext x; rw [Pi.mul_apply, hf_apply j x]
      by_cases hx : x = j <;> simp [hx]
    have hthis := congrArg φ hsq
    rw [map_mul] at hthis
    have h : φ (f j) * (φ (f j) - 1) = 0 := by rw [mul_sub, mul_one, hthis, sub_self]
    rcases mul_eq_zero.mp h with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h0)
  have hle : ∀ i j, i ≠ j → φ (f i) * φ (f j) = 0 := by
    intro i j hij
    have h0 : f i * f j = 0 := by
      ext x; rw [Pi.mul_apply, hf_apply i x, hf_apply j x, Pi.zero_apply]
      by_cases hx : x = i
      · simp [hx, hij]
      · simp [hx]
    rw [← map_mul, h0, map_zero]
  obtain ⟨j₀, hj₀⟩ : ∃ j, φ (f j) = 1 := by
    by_contra h
    push Not at h
    have hz : (∑ j, φ (f j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rcases hidem j with h0 | h1
      · exact h0
      · exact absurd h1 (h j)
    rw [hz] at h1
    exact one_ne_zero h1.symm
  refine ⟨j₀, ?_⟩
  ext g
  rw [Pi.evalAlgHom_apply]
  conv_lhs => rw [pi_decomp g]
  rw [map_sum]
  rw [Finset.sum_eq_single j₀]
  · rw [map_smul, hj₀, smul_eq_mul, mul_one]
  · intro b _ hb
    have hb2 := hle j₀ b (Ne.symm hb)
    rw [hj₀, one_mul] at hb2
    rw [map_smul, hb2, smul_eq_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j₀) h

/-- An algebra automorphism of `ι → k` permutes the standard idempotents. -/
private lemma exists_perm_single_of_algEquiv {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
    (ψ : (ι → k) ≃ₐ[k] (ι → k)) :
    ∃ σ : ι ≃ ι, ∀ i, ψ (Function.update (0 : ι → k) i 1)
      = Function.update (0 : ι → k) (σ i) 1 := by
  classical
  have hcomp : ∀ j : ι, ∃ j', (Pi.evalAlgHom k (fun _ => k) j).comp ψ.toAlgHom
      = Pi.evalAlgHom k (fun _ => k) j' := fun j => algHom_pi_eq_eval _
  choose g hg using hcomp
  have hg_eval : ∀ j x, (ψ x) j = x (g j) := by
    intro j x
    have h1 := congrArg (fun (φ : (ι → k) →ₐ[k] k) => φ x) (hg j)
    simpa [AlgHom.comp_apply, Pi.evalAlgHom_apply] using h1
  have hinj : Function.Injective g := by
    intro i j hij
    have h1 : (Pi.evalAlgHom k (fun _ => k) i).comp ψ.toAlgHom
        = (Pi.evalAlgHom k (fun _ => k) j).comp ψ.toAlgHom := by rw [hg i, hg j, hij]
    have h2 : Pi.evalAlgHom k (fun _ => k) i = Pi.evalAlgHom k (fun _ => k) j := by
      ext y
      obtain ⟨x, rfl⟩ := ψ.surjective y
      exact congrArg (fun (φ : (ι → k) →ₐ[k] k) => φ x) h1
    have h3 := congrArg (fun (φ : (ι → k) →ₐ[k] k) => φ (Function.update (0 : ι → k) i 1)) h2
    simp only [Pi.evalAlgHom_apply] at h3
    rw [Function.update_self, Function.update_apply, Pi.zero_apply] at h3
    by_cases hji : j = i
    · exact hji.symm
    · rw [if_neg hji] at h3
      exact absurd h3.symm zero_ne_one
  set e : ι ≃ ι := Equiv.ofBijective g ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩ with he
  have he_apply : ∀ j, e j = g j := fun j => Equiv.ofBijective_apply g _ j
  refine ⟨e.symm, ?_⟩
  intro i
  ext j
  rw [hg_eval j (Function.update (0 : ι → k) i 1), Function.update_apply,
    Function.update_apply, Pi.zero_apply, Pi.zero_apply]
  have hiff : (g j = i) ↔ (j = e.symm i) := by
    rw [← he_apply j]
    exact Equiv.apply_eq_iff_eq_symm_apply e
  by_cases h : g j = i
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun hj => h (hiff.mpr hj))]

/-- The orbit argument. -/
private lemma orbit_arg {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {p : ℕ} (hodd : Odd p)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Module.End k V} (hM : (M - 1) ^ 2 = 0)
    {P : ι → Module.End k V}
    (hPorth : ∀ i j, P i * P j = if i = j then P i else 0)
    {σ : ι → ι} (hσ : ∀ i, M * P i = P (σ i) * M)
    (hσp : ∀ i, (σ^[p]) i = i) :
    ∀ i, σ i ≠ i → P i = 0 := by
  classical
  have hsq : (M - 1) ^ 2 = M * M - M - M + 1 := by
    rw [pow_two, sub_mul, mul_sub, mul_one, one_mul]; abel
  intro i hne
  have hσ2 : σ (σ i) ≠ i := by
    intro h2
    have hσ2' : (σ^[2]) i = i := by simpa [Function.iterate_succ, Function.comp_apply] using h2
    have hcyc : ∀ n : ℕ, (σ^[2 * n + 1]) i = σ i := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [show 2 * (n+1) + 1 = (2*n+1) + 2 by ring]
        rw [Function.iterate_add_apply, hσ2']
        exact ih
    obtain ⟨k, hk⟩ := hodd
    have hp_eq : p = 2 * k + 1 := by omega
    have := hσp i
    rw [hp_eq, hcyc k] at this
    exact hne this
  have hPidem : P i * P i = P i := by rw [hPorth i i, if_pos rfl]
  have hM2P : M * M * P i = P (σ (σ i)) * (M * M) := by
    calc M * M * P i = M * (M * P i) := by rw [mul_assoc]
      _ = M * (P (σ i) * M) := by rw [hσ i]
      _ = (M * P (σ i)) * M := by rw [← mul_assoc]
      _ = (P (σ (σ i)) * M) * M := by rw [hσ (σ i)]
      _ = P (σ (σ i)) * (M * M) := by rw [mul_assoc]
  have e1 : (P i) * (M * M) * (P i) = 0 := by
    rw [mul_assoc (P i) (M*M) (P i), hM2P, ← mul_assoc (P i) (P (σ (σ i))) (M*M),
      hPorth i (σ (σ i)), if_neg (Ne.symm hσ2), zero_mul]
  have e2 : (P i) * M * (P i) = 0 := by
    rw [mul_assoc (P i) M (P i), hσ i, ← mul_assoc (P i) (P (σ i)) M,
      hPorth i (σ i), if_neg (Ne.symm hne), zero_mul]
  have hfinal : (P i) * (M - 1) ^ 2 * (P i) = P i := by
    rw [hsq]
    have expand : (P i) * (M * M - M - M + 1) * (P i)
        = (P i) * (M*M) * (P i) - (P i) * M * (P i) - (P i) * M * (P i)
          + (P i) * 1 * (P i) := by noncomm_ring
    rw [expand, e1, e2, mul_one, hPidem]
    abel
  rw [hM, mul_zero, zero_mul] at hfinal
  exact hfinal.symm

/-! ## The main result -/

theorem abelian_centralized_of_quadratic {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {k V : Type*} [Field k] [CharP k p] [IsAlgClosed k]
    {G : Type*} [Group G] [Finite G] [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (A : Subgroup G) [A.Normal] (hAab : IsMulCommutative ↥A) (hcop : ¬ p ∣ Nat.card A)
    {x : G} (hxp : x ^ p = 1) (hquad : (ρ x - 1) ^ 2 = 0) :
    ∀ a ∈ A, ρ (commutatorElement.bracket x a) = 1 := by
  classical
  letI : CommMonoid ↥A := { (inferInstance : Monoid ↥A) with
    mul_comm := fun a b => hAab.is_comm.comm a b }
  haveI hAne : NeZero (Nat.card ↥A : k) :=
    ⟨fun h => hcop ((CharP.cast_eq_zero_iff k p (Nat.card ↥A)).mp h)⟩
  let ρA : Representation k ↥A V := ρ.comp A.subtype
  let F : MonoidAlgebra k ↥A →ₐ[k] Module.End k V := ρA.asAlgebraHom
  haveI : FiniteDimensional k (MonoidAlgebra k ↥A) := inferInstance
  haveI : IsSemisimpleRing (MonoidAlgebra k ↥A) := inferInstance
  have hpi : Nonempty (MonoidAlgebra k ↥A ≃ₐ[k] ((MaximalSpectrum (MonoidAlgebra k ↥A)) → k)) := by
    haveI : IsReduced (MonoidAlgebra k ↥A) := inferInstance
    haveI : IsArtinianRing (MonoidAlgebra k ↥A) := IsArtinianRing.of_finite k _
    have hres : ∀ I : MaximalSpectrum (MonoidAlgebra k ↥A),
        Nonempty (k ≃ₐ[k] (MonoidAlgebra k ↥A ⧸ I.asIdeal)) := by
      intro I
      haveI : Field (MonoidAlgebra k ↥A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
      haveI : Algebra.IsIntegral k (MonoidAlgebra k ↥A ⧸ I.asIdeal) :=
        Algebra.IsIntegral.of_finite k _
      exact ⟨AlgEquiv.ofBijective (Algebra.ofId k _)
        IsAlgClosed.algebraMap_bijective_of_isIntegral⟩
    refine ⟨(AlgEquiv.restrictScalars k (IsArtinianRing.equivPi (MonoidAlgebra k ↥A))).trans
      (AlgEquiv.piCongrRight (fun I => (Classical.choice (hres I)).symm))⟩
  obtain ⟨Φ⟩ := hpi
  let ι := MaximalSpectrum (MonoidAlgebra k ↥A)
  haveI : Fintype ι := Fintype.ofFinite ι
  let f : ι → (ι → k) := fun i => Function.update (0 : ι → k) i 1
  let e : ι → MonoidAlgebra k ↥A := fun i => Φ.symm (f i)
  have hf_apply : ∀ i j, f i j = if j = i then (1:k) else 0 := fun i j => by
    simp only [f, Function.update_apply, Pi.zero_apply]
  have hdecomp : ∀ y : MonoidAlgebra k ↥A, y = ∑ i, (Φ y) i • e i := by
    intro y
    calc y = Φ.symm (Φ y) := (AlgEquiv.symm_apply_apply Φ y).symm
      _ = Φ.symm (∑ i, (Φ y) i • f i) := congrArg Φ.symm (pi_decomp (Φ y))
      _ = ∑ i, (Φ y) i • Φ.symm (f i) := by simp only [map_sum, map_smul]
      _ = ∑ i, (Φ y) i • e i := rfl
  have he_apply : ∀ i, Φ (e i) = f i := fun i => AlgEquiv.apply_symm_apply Φ (f i)
  let ω : MulAut ↥A :=
    { toFun := fun a => ⟨x * (a:G) * x⁻¹,
        Subgroup.Normal.conj_mem (H := A) inferInstance (a:G) a.2 x⟩
      invFun := fun a => ⟨x⁻¹ * (a:G) * x,
        Subgroup.Normal.conj_mem' (H := A) inferInstance (a:G) a.2 x⟩
      left_inv := fun a => by ext; group
      right_inv := fun a => by ext; group
      map_mul' := fun a b => by ext; simp only [Subgroup.coe_mul]; group }
  have hωval : ∀ (k : ℕ) (a : ↥A), ((ω^k) a : G) = x^k * (a:G) * (x^k)⁻¹ := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [pow_succ, MulAut.mul_apply, ih (ω a)]
      change x ^ k * (x * (a:G) * x⁻¹) * (x ^ k)⁻¹
        = x ^ (k+1) * (a:G) * (x ^ (k+1))⁻¹
      rw [pow_succ]
      group
  have hωp : ω ^ p = 1 := by
    ext a
    rw [hωval p a, hxp, one_mul, inv_one, mul_one, MulAut.one_apply]
  let αR : MonoidAlgebra k ↥A ≃ₐ[k] MonoidAlgebra k ↥A := MonoidAlgebra.domCongr k k ω
  have hαRp : αR ^ p = 1 := by
    have h : αR = MonoidAlgebra.domCongrAut (A := k) ω :=
      (MonoidAlgebra.domCongrAut_apply (R := k) (A := k) ω).symm
    rw [h, ← map_pow, hωp, map_one]
  have hαR_of : ∀ a : ↥A, αR (MonoidAlgebra.of k ↥A a) = MonoidAlgebra.of k ↥A (ω a) := by
    intro a
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.domCongr_single, MonoidAlgebra.of_apply]
  let ψ : (ι → k) ≃ₐ[k] (ι → k) := (Φ.symm.trans αR).trans Φ
  obtain ⟨σ, hσ⟩ := exists_perm_single_of_algEquiv ψ
  have hψpow : ∀ n : ℕ, ∀ g : ι → k, (ψ^n) g = Φ ((αR^n) (Φ.symm g)) := by
    intro n
    induction n with
    | zero => intro g; simp only [pow_zero, AlgEquiv.one_apply, AlgEquiv.apply_symm_apply]
    | succ n ih =>
      intro g
      rw [pow_succ, AlgEquiv.mul_apply, ih (ψ g)]
      have h1 : Φ.symm (ψ g) = αR (Φ.symm g) := by
        simp only [ψ, AlgEquiv.trans_apply]; exact Φ.symm_apply_apply _
      rw [h1, pow_succ, AlgEquiv.mul_apply]
  have hψp : ψ ^ p = 1 := by
    ext g
    rw [hψpow p g, hαRp, AlgEquiv.one_apply, AlgEquiv.apply_symm_apply, AlgEquiv.one_apply]
  have heα : ∀ i, αR (e i) = e (σ i) := by
    intro i
    apply Φ.injective
    calc Φ (αR (e i)) = ψ (f i) := rfl
      _ = f (σ i) := hσ i
      _ = Φ (e (σ i)) := (he_apply (σ i)).symm
  have hχ : ∀ i y, (Φ (αR y)) (σ i) = (Φ y) i := by
    intro i y
    have h1 : Φ (αR y) = ψ (Φ y) := by
      simp only [ψ, AlgEquiv.trans_apply]; exact congrArg Φ (congrArg αR (Φ.symm_apply_apply y).symm)
    have hψ : ∀ g : ι → k, ψ g = ∑ j, g j • f (σ j) := by
      intro g
      conv_lhs => rw [pi_decomp g]
      rw [map_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [map_smul, hσ])
    rw [h1, hψ, Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · rw [Pi.smul_apply, hf_apply, if_pos rfl, smul_eq_mul, mul_one]
    · intro j _ hj
      rw [Pi.smul_apply, hf_apply]
      rw [if_neg (fun hh => hj (σ.injective hh).symm), smul_eq_mul, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hsm : ∀ (c : k) (X : Module.End k V),
      ρ x * (c • X) * ρ (x⁻¹) = c • (ρ x * X * ρ (x⁻¹)) := by
    intro c X; rw [mul_smul_comm, smul_mul_assoc]
  have hkey : ∀ y : MonoidAlgebra k ↥A, ρ x * F y * ρ (x⁻¹) = F (αR y) := by
    intro y
    refine MonoidAlgebra.induction_on
      (motive := fun z => ρ x * F z * ρ (x⁻¹) = F (αR z)) y ?_ ?_ ?_
    · intro a
      rw [hαR_of, Representation.asAlgebraHom_of, Representation.asAlgebraHom_of]
      show ρ x * ρ (a : G) * ρ (x⁻¹) = ρ (x * (a : G) * x⁻¹)
      rw [← map_mul, ← map_mul]
    · intro z w hz hw
      rw [map_add F z w, map_add αR z w, map_add F (αR z) (αR w), mul_add, add_mul, hz, hw]
    · intro c z hz
      rw [map_smul F c z, map_smul αR c z, map_smul F c (αR z), hsm c (F z), hz]
  let P : ι → Module.End k V := fun i => F (e i)
  have hexpand : ∀ y : MonoidAlgebra k ↥A, F y = ∑ i, (Φ y) i • P i := by
    intro y
    conv_lhs => rw [hdecomp y]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])
  have hPsum : ∑ i, P i = 1 := by
    have h := hexpand 1
    rw [map_one] at h
    rw [show (∑ i, (Φ (1 : MonoidAlgebra k ↥A)) i • P i) = ∑ i, P i from
      Finset.sum_congr rfl (fun i _ => by rw [map_one, Pi.one_apply, one_smul])] at h
    exact h.symm
  have he_orth : ∀ i j, e i * e j = if i = j then e i else 0 := by
    intro i j
    have hfmul : f i * f j = if i = j then f i else 0 := by
      by_cases h : i = j
      · subst h; rw [if_pos rfl]
        ext x; rw [Pi.mul_apply, hf_apply i x]
        by_cases hx : x = i <;> simp [hx]
      · rw [if_neg h]
        ext x; rw [Pi.mul_apply, hf_apply i x, hf_apply j x, Pi.zero_apply]
        by_cases hx : x = i
        · rw [if_pos hx, if_neg (fun hh => h (hx.symm.trans hh)), mul_zero]
        · rw [if_neg hx, zero_mul]
    apply Φ.injective
    rw [map_mul, he_apply i, he_apply j, hfmul]
    split_ifs with h
    · exact (he_apply i).symm
    · rw [map_zero]
  have hPorth : ∀ i j, P i * P j = if i = j then P i else 0 := by
    intro i j
    have h1 : F (e i * e j) = if i = j then F (e i) else 0 := by
      rw [he_orth i j]
      by_cases h : i = j
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, map_zero]
    rw [map_mul] at h1
    exact h1
  have hMP : ∀ i, ρ x * P i = P (σ i) * ρ x := by
    intro i
    have hk := hkey (e i)
    rw [heα i] at hk
    have hxinv : ρ (x⁻¹) * ρ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have h2 := congrArg (fun Z : Module.End k V => Z * ρ x) hk
    simp only [mul_assoc, hxinv, mul_one] at h2
    simpa [P] using h2
  have hσp : ∀ i : ι, (σ^[p]) i = i := by
    intro i
    have hiter : ∀ k : ℕ, ∀ j : ι, (ψ^k) (f j) = f ((σ^k) j) := by
      intro k
      induction k with
      | zero => intro j; simp
      | succ k ih =>
        intro j
        rw [pow_succ, AlgEquiv.mul_apply, hσ j, ih (σ j)]
        rw [pow_succ, Equiv.Perm.mul_apply]
    have h1 : (ψ^p) (f i) = f i := by rw [hψp, AlgEquiv.one_apply]
    rw [hiter p i, Equiv.Perm.coe_pow σ p] at h1
    have h2 := congrFun h1 i
    rw [hf_apply ((σ^[p]) i) i, hf_apply i i, if_pos rfl] at h2
    by_cases h : i = (σ^[p]) i
    · exact h.symm
    · rw [if_neg h] at h2
      exact absurd h2 zero_ne_one
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hzero : ∀ i, σ i ≠ i → P i = 0 := orbit_arg hodd hquad hPorth hMP hσp
  intro a ha
  set a' : ↥A := ⟨a, ha⟩ with ha'
  have h1 : F (αR (MonoidAlgebra.of k ↥A a')) = F (MonoidAlgebra.of k ↥A a') := by
    rw [hexpand (αR (MonoidAlgebra.of k ↥A a')), hexpand (MonoidAlgebra.of k ↥A a')]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : σ i = i
    · have h2 : Φ (αR (MonoidAlgebra.of k ↥A a')) i
          = Φ (MonoidAlgebra.of k ↥A a') i := by
        conv_lhs => rw [← hi]
        exact hχ i (MonoidAlgebra.of k ↥A a')
      rw [h2]
    · rw [hzero i hi]; simp
  have h2 : ρ x * ρ a * ρ (x⁻¹) = ρ a := by
    have hk := hkey (MonoidAlgebra.of k ↥A a')
    rw [h1] at hk
    rw [Representation.asAlgebraHom_of] at hk
    simpa [ρA, ha'] using hk
  rw [commutatorElement_def, map_mul, map_mul, map_mul, h2]
  rw [← map_mul, mul_inv_cancel, map_one]

end Work.PStable
