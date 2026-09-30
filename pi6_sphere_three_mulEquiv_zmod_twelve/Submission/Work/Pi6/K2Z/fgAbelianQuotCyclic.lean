import Mathlib
import Submission.Work.Pi6.EMZ.Defs
import Submission.Work.Pi6.K2Z.fgAbelianCyclic
import Submission.Work.Pi6.K2Z.finrank_zmodTensor_prod
import Submission.Work.Pi6.K2Z.tensorZModQuot
import Submission.Work.Pi6.K2Z.fgAbelianVanishesZmod
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false

/-!
# `A ⧸ pA ≅ ℤ/p` for every prime `p` forces `A ≅ ℤ`

Let `A` be a finitely generated abelian group.  If for every prime `p` the quotient of `A` by the
subgroup `p·A` of `p`-multiples is cyclic of order `p`, i.e. `A ⧸ p·A ≅ ℤ/p`, then `A ≅ ℤ`.

## Route

Write `A ≅ ℤ^n × T` with `T` a finite direct sum of cyclic torsion groups
(`Module.equiv_free_prod_directSum`).  Tensoring with `ℤ/p` gives
`ℤ/p ⊗[ℤ] A ≅ (ℤ/p)^n × (ℤ/p ⊗[ℤ] T) = A ⧸ p·A`, so the hypothesis says

`n + dim_{𝔽_p} (ℤ/p ⊗[ℤ] T) = 1` for every prime `p`.

Hence `n ≤ 1`.  If `n = 0` then `A ≅ T` is a finite direct sum of cyclic groups, so it has a
bounded exponent `N` with `N · A = 0`; taking a prime `q > N`, Bézout shows that multiplication by
`q` is surjective on `A`, i.e. `A ⧸ q·A = 0`, contradicting `A ⧸ q·A ≅ ℤ/q`.  So `n = 1`, and the
dimension formula forces `dim_{𝔽_p}(ℤ/p ⊗[ℤ] T) = 0` for every prime `p`; by
`Work.Pi6.K2Z.fgAbelianVanishesZmod` this forces `T = 0`, and `A ≅ ℤ¹ = ℤ`.

The four ingredients are `Work.Pi6.K2Z.tensorZModQuot` (the identification
`ℤ/p ⊗[ℤ] A ≅ A ⧸ p·A`), `Work.Pi6.K2Z.fgAbelianVanishesZmod` (a f.g. abelian group whose `ℤ/p`
base change vanishes for all primes is trivial), and the two elementary facts proved below
(a direct sum of cyclic torsion groups has bounded exponent; a bounded-exponent group is
`q`-divisible for every prime `q` exceeding the exponent).
-/

namespace Work.Pi6.K2Z

open scoped TensorProduct
open CategoryTheory

noncomputable section

/-- A finite direct sum of cyclic torsion groups `ℤ ⧸ (q i)` (with `q i ≠ 0`) has a *bounded*
exponent: some `N > 0` kills every element.  Take `N = ∏ i, |q i|`. -/
theorem exponentDirectSumQuot_aux {ι : Type} [Fintype ι] (q : ι → ℤ) (hq : ∀ i, q i ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : DirectSum ι (fun i => ℤ ⧸ Ideal.span ({q i} : Set ℤ)), N • x = 0 := by
  classical
  refine ⟨∏ i, (q i).natAbs, Finset.prod_pos (fun i _ => Int.natAbs_pos.mpr (hq i)), ?_⟩
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i m =>
      have hmem : ((q i).natAbs : ℤ) ∈ Ideal.span ({(q i)} : Set ℤ) :=
        Ideal.mem_span_singleton.mpr (Int.dvd_natAbs.mpr dvd_rfl)
      have hzero : (q i).natAbs • m = 0 := by
        rw [← Nat.cast_smul_eq_nsmul ℤ ((q i).natAbs) m]
        exact zsmul_eq_zero_of_mem_span hmem m
      have hdvd : (q i).natAbs ∣ ∏ j, (q j).natAbs :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      have hm0 : (∏ j, (q j).natAbs) • m = 0 := by
        calc (∏ j, (q j).natAbs) • m
            = ((∏ j, (q j).natAbs) / (q i).natAbs * (q i).natAbs) • m := by
              rw [Nat.div_mul_cancel hdvd]
          _ = ((∏ j, (q j).natAbs) / (q i).natAbs) • ((q i).natAbs • m) := by rw [mul_smul]
          _ = 0 := by rw [hzero, smul_zero]
      rw [← map_nsmul (DirectSum.of (fun i => ℤ ⧸ Ideal.span ({(q i)} : Set ℤ)) i)
        (∏ j, (q j).natAbs) m, hm0, map_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/-- If `N · A = 0` and `q` is a prime with `N < q`, then `q` is coprime to `N`, so Bézout's
identity exhibits every element of `A` as a `q`-multiple: multiplication by `q` is surjective. -/
theorem nsmul_surjective_of_exponent_aux (B : Type) [AddCommGroup B] (N q : ℕ) (hN : 0 < N)
    (hq : q.Prime) (hNq : N < q) (hexp : ∀ x : B, N • x = 0) :
    ∀ x : B, ∃ y, q • y = x := by
  intro x
  have hcop : Nat.Coprime q N := (Nat.Prime.coprime_iff_not_dvd hq).mpr fun hdvd =>
    absurd (Nat.le_of_dvd hN hdvd) (by omega)
  have hbez : (1 : ℤ) = (q : ℤ) * q.gcdA N + (N : ℤ) * q.gcdB N := by
    have h := Nat.gcd_eq_gcd_ab q N
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at h
    simpa using h
  have hNz : (N : ℤ) • x = 0 := by
    rw [Nat.cast_smul_eq_nsmul ℤ N x]
    exact hexp x
  refine ⟨q.gcdA N • x, ?_⟩
  have hmul : (q : ℤ) * q.gcdA N = 1 - (N : ℤ) * q.gcdB N := by linarith
  rw [← Nat.cast_smul_eq_nsmul ℤ q (q.gcdA N • x)]
  calc (q : ℤ) • (q.gcdA N • x)
      = ((q : ℤ) * q.gcdA N) • x := smul_smul _ _ _
    _ = (1 - (N : ℤ) * q.gcdB N) • x := by rw [hmul]
    _ = x - ((N : ℤ) * q.gcdB N) • x := by rw [sub_smul, one_smul]
    _ = x - (N : ℤ) • (q.gcdB N • x) := by rw [← smul_smul]
    _ = x - q.gcdB N • ((N : ℤ) • x) := by rw [smul_comm]
    _ = x := by rw [hNz, smul_zero, sub_zero]

/-- Auxiliary form of `fgAbelianQuotCyclic` with the four ingredient lemmas as hypotheses, so that
the assembly is independent of how they are proved. -/
theorem fgAbelianQuotCyclic_aux (A : Type) [AddCommGroup A] [Module.Finite ℤ A]
    (h : ∀ p : ℕ, p.Prime → Nonempty ((A ⧸ Work.Pi6.EMZ.pH p A) ≃+ ZMod p))
    (hTQ : ∀ (B : Type) [AddCommGroup B] (p : ℕ),
      Nonempty (TensorProduct ℤ (ZMod p) B ≃+ (B ⧸ Work.Pi6.EMZ.pH p B)))
    (hExp : ∀ (ι' : Type) [Fintype ι'] (q : ι' → ℤ), (∀ i, q i ≠ 0) →
      ∃ N : ℕ, 0 < N ∧ ∀ x : DirectSum ι' (fun i => ℤ ⧸ Ideal.span ({q i} : Set ℤ)), N • x = 0)
    (hNsmul : ∀ (B : Type) [AddCommGroup B] (N q : ℕ), 0 < N → q.Prime → N < q →
      (∀ x : B, N • x = 0) → ∀ x : B, ∃ y, q • y = x)
    (hVan : ∀ (B : Type) [AddCommGroup B] [Module.Finite ℤ B],
      (∀ p : ℕ, p.Prime → Module.finrank (ZMod p)
        ↥((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of ℤ B)) = 0) →
      Subsingleton B) :
    Nonempty (A ≃+ ℤ) := by
  classical
  -- Step 1: `ZMod p ⊗[ℤ] A` is one-dimensional over `ZMod p` for every prime `p`.
  have hfin : ∀ p : ℕ, p.Prime → Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) A) = 1 := by
    intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    have hcardA : Nat.card (TensorProduct ℤ (ZMod p) A) = p := by
      obtain ⟨e⟩ := h p hp
      rw [Nat.card_congr (hTQ A p).some.toEquiv, Nat.card_congr e.toEquiv,
        Nat.card_eq_fintype_card, ZMod.card]
    have hcardZ : Nat.card (TensorProduct ℤ (ZMod p) A) = Nat.card (ZMod p) := by
      rw [hcardA, Nat.card_eq_fintype_card, ZMod.card]
    have h1 := finrank_zmod_eq_of_natCard_eq p hp (TensorProduct ℤ (ZMod p) A) (ZMod p) hcardZ
    rwa [Module.finrank_self] at h1
  -- Step 2: the structure theorem for the finitely generated `ℤ`-module `A`.
  obtain ⟨n, ι, instι, P, hP, E, ⟨Φ⟩⟩ := Module.equiv_free_prod_directSum (R := ℤ) (M := A)
  letI : Fintype ι := instι
  let T : Type := DirectSum ι fun i => ℤ ⧸ Ideal.span ({(P i) ^ (E i)} : Set ℤ)
  have hΦ : A ≃ₗ[ℤ] (Fin n →₀ ℤ) × T := Φ
  haveI hTfin : Module.Finite ℤ T :=
    Module.Finite.of_surjective ((LinearMap.snd ℤ (Fin n →₀ ℤ) T).comp hΦ.toLinearMap) (by
      intro y
      obtain ⟨z, hz⟩ := hΦ.surjective (0, y)
      exact ⟨z, by simp [hz]⟩)
  haveI hprod_fin : Module.Finite ℤ ((Fin n →₀ ℤ) × T) :=
    Module.Finite.of_surjective (σ := RingHom.id ℤ) hΦ.toLinearMap hΦ.surjective
  -- Step 3: transfer of the finrank through `hΦ`, and additivity over the product.
  have hformula : ∀ p : ℕ, p.Prime → Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) A)
      = n + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) T) := by
    intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Module.Finite (ZMod p) (TensorProduct ℤ (ZMod p) ((Fin n →₀ ℤ) × T)) :=
      Module.Finite.base_change ℤ (ZMod p) ((Fin n →₀ ℤ) × T)
    haveI : Module.Finite (ZMod p) (TensorProduct ℤ (ZMod p) A) :=
      Module.Finite.base_change ℤ (ZMod p) A
    have hcard' : Nat.card (TensorProduct ℤ (ZMod p) A)
        = Nat.card (TensorProduct ℤ (ZMod p) ((Fin n →₀ ℤ) × T)) :=
      Nat.card_congr (hΦ.lTensor (ZMod p)).toEquiv
    have h1 : Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) A)
        = Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) ((Fin n →₀ ℤ) × T)) :=
      finrank_zmod_eq_of_natCard_eq p hp _ _ hcard'
    rw [h1, finrank_zmodTensor_prod p hp (Fin n →₀ ℤ) T, Module.finrank_baseChange,
      Module.finrank_finsupp_self ℤ, Fintype.card_fin]
  -- Step 4: `n ≤ 1`.
  have hn_le : n ≤ 1 := by
    have h2 := hformula 2 Nat.prime_two
    rw [hfin 2 Nat.prime_two] at h2
    omega
  -- Step 5: `n ≠ 0` (else `A` is a bounded-torsion group and multiplication by a large prime
  -- cannot be surjective).
  have hn_ne : n ≠ 0 := by
    intro hn0
    rw [hn0] at hΦ
    haveI : Subsingleton (Fin 0 →₀ ℤ) := ⟨fun a b => Finsupp.ext fun i => i.elim0⟩
    have hqne : ∀ i, (fun i => (P i) ^ (E i)) i ≠ 0 := fun i => pow_ne_zero _ (hP i).ne_zero
    obtain ⟨N, hNpos, hNexp⟩ := hExp ι (fun i => (P i) ^ (E i)) hqne
    have hexpA : ∀ x : A, N • x = 0 := by
      intro x
      apply hΦ.injective
      rw [map_nsmul, map_zero]
      refine Prod.ext ?_ ?_
      · rw [Prod.smul_fst]; exact Subsingleton.elim _ _
      · rw [Prod.smul_snd]; exact hNexp (hΦ x).2
    obtain ⟨q, hqge, hqprime⟩ := Nat.exists_infinite_primes (N + 1)
    have hNq : N < q := by omega
    have hsub : Subsingleton (A ⧸ Work.Pi6.EMZ.pH q A) := by
      rw [Work.Pi6.EMZ.subsingleton_quot_pH_iff]
      exact hNsmul A N q hNpos hqprime hNq hexpA
    obtain ⟨e⟩ := h q hqprime
    haveI : Fact (1 < q) := ⟨hqprime.one_lt⟩
    exact (not_subsingleton_iff_nontrivial.mpr inferInstance)
      ⟨fun a b => e.symm.injective (hsub.elim (e.symm a) (e.symm b))⟩
  have hn : n = 1 := by omega
  -- Step 6: the torsion summand `T` is trivial.
  have hT0 : ∀ p : ℕ, p.Prime → Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) T) = 0 := by
    intro p hp
    have h2 := hformula p hp
    rw [hfin p hp, hn] at h2
    omega
  have hTsub : Subsingleton T := by
    refine hVan T ?_
    intro p hp
    rw [finrankExtendScalarsZMod_aux T p hp]
    exact hT0 p hp
  -- Step 7: `A ≅ ℤ`.
  rw [hn] at hΦ
  haveI : Unique T := ⟨⟨0⟩, fun a => hTsub.elim a 0⟩
  exact ⟨(hΦ.trans (LinearEquiv.prodUnique (R := ℤ) (M := Fin 1 →₀ ℤ) (M₂ := T))).trans
    ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin 1)).trans
      (LinearEquiv.funUnique (Fin 1) ℤ ℤ)) |>.toAddEquiv⟩

theorem fgAbelianQuotCyclic (A : Type) [AddCommGroup A] [Module.Finite ℤ A]
    (h : ∀ p : ℕ, p.Prime → Nonempty ((A ⧸ Work.Pi6.EMZ.pH p A) ≃+ ZMod p)) :
    Nonempty (A ≃+ ℤ) :=
  fgAbelianQuotCyclic_aux A h (fun B _ p => tensorZModQuot B p)
    (fun _ι' _ q hq => exponentDirectSumQuot_aux q hq)
    (fun B _ N q hN hq hNq hexp => nsmul_surjective_of_exponent_aux B N q hN hq hNq hexp)
    (fun B _ _ hp => fgAbelianVanishesZmod B hp)

end

end Work.Pi6.K2Z
