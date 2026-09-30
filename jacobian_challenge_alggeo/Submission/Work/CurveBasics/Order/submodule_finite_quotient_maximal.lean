import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

/-!
# Finiteness of `M ⧸ pM` over `A ⧸ p`

Let `A` be a principal ideal domain with fraction field `K`, `L` a finite extension of `K`
(as a field), and `M ⊆ L` an `A`-submodule.  For a maximal ideal `p` of `A`, the quotient
`M ⧸ pM` is finite (in fact finite dimensional, of dimension at most `[L : K]`) over the
residue field `A ⧸ p`.

The proof is the classical "descending denominator" argument: if lifts of `n+1` elements of
`M ⧸ pM` were `A ⧸ p`-linearly independent, then (since `[L : K] = n`) their images in `L`
satisfy a nontrivial `K`-linear relation; clearing denominators and cancelling the gcd of the
coefficients gives a relation whose coefficients generate the unit ideal in `A`, which, reduced
mod `p`, contradicts linear independence.

We avoid the (instance-level) field structure on `A ⧸ p` in the final step by converting the
rank bound on `M ⧸ pM` into finite generation via a maximal independent set, using only that
nonzero elements of `A ⧸ p` are invertible.
-/

namespace Work.CurveBasics.Order

/-- Given a `K`-linear relation among elements of `L`, with not all coefficients zero, we may
clear denominators and obtain an `A`-linear relation with not all coefficients zero. -/
private lemma clear_denom {A K L : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    {ι : Type*} [Fintype ι] (g : ι → L) (c : ι → K)
    (hc : ∑ i, c i • g i = 0) (hcne : ∃ i, c i ≠ 0) :
    ∃ a : ι → A, (∑ i, a i • g i = 0 ∧ ∃ i, a i ≠ 0) := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) c
  have hb' : ∀ i, ∃ a : A, algebraMap A K a = (b : A) • c i := fun i =>
    RingHom.mem_rangeS.mp (hb i)
  choose a ha using hb'
  refine ⟨a, ?_, ?_⟩
  · have hbmul : (b : A) • (∑ i, c i • g i) = ∑ i, (a i) • g i := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← smul_assoc (α := L) (M := A) (N := K) (b : A) (c i) (g i), ← ha i]
      simp only [IsScalarTower.algebraMap_apply A K L, Algebra.smul_def]
    rw [← hbmul, hc, smul_zero]
  · rcases hcne with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    intro hai
    have hb0 : algebraMap A K (b : A) ≠ 0 := by
      rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]
      intro h
      exact one_ne_zero ((mem_nonZeroDivisors_iff.mp b.2).1 1 (by rw [h, zero_mul]))
    have key : algebraMap A K (b : A) * c i = 0 := by
      rw [← Algebra.smul_def, ← ha i, hai, map_zero]
    exact hi ((mul_eq_zero.mp key).resolve_left hb0)

/-- Given an `A`-linear relation among elements of `L` (`L` a field containing `A`), with not all
coefficients zero, and a domain `A` in which every ideal is principal, we may factor out the gcd
of the coefficients and obtain a relation whose coefficients generate the unit ideal. -/
private lemma pid_primitive_relation {A L : Type*} [CommRing A] [IsDomain A]
    [IsPrincipalIdealRing A] [Field L] [Algebra A L]
    (hinj : Function.Injective (algebraMap A L))
    {ι : Type*} [Fintype ι] (g : ι → L) (a : ι → A)
    (hrel : ∑ i, a i • g i = 0) (hne : ∃ i, a i ≠ 0) :
    ∃ e : ι → A, Ideal.span (Set.range e) = ⊤ ∧ ∑ i, e i • g i = 0 := by
  set I := Ideal.span (Set.range a) with hI
  have hIne : I ≠ ⊥ := by
    intro h
    obtain ⟨i, hi⟩ := hne
    have : a i ∈ (⊥ : Ideal A) := by rw [← h, hI]; exact Ideal.subset_span ⟨i, rfl⟩
    exact hi (by simpa using this)
  haveI : I.IsPrincipal := inferInstance
  set d := Submodule.IsPrincipal.generator I with hd
  have hspand : Ideal.span {d} = I := Ideal.span_singleton_generator I
  have hd0 : d ≠ 0 := by
    intro h
    apply hIne
    rw [← hspand, h]; simp
  have hdvd : ∀ i, d ∣ a i := fun i =>
    (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp (hI ▸ Ideal.subset_span ⟨i, rfl⟩)
  choose e he using hdvd
  have hde : ∀ i, a i = d * e i := he
  refine ⟨e, ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    have hdmem : d ∈ Ideal.span (Set.range a) := by
      rw [← hI, ← hspand]; exact Ideal.subset_span (Set.mem_singleton d)
    rw [Ideal.mem_span_range_iff_exists_fun] at hdmem
    obtain ⟨c, hc⟩ := hdmem
    refine ⟨c, ?_⟩
    have key : (∑ i, d * (c i * e i)) = d := by
      have key1 : (∑ i, d * (c i * e i)) = ∑ i, c i * a i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hde i]; ring
      rw [key1]; exact hc
    have hkey : d * (∑ i, c i * e i) = d * 1 := by
      rw [mul_one, Finset.mul_sum]
      exact key
    exact mul_left_cancel₀ hd0 hkey
  · have hsum : d • (∑ i, e i • g i) = 0 := by
      rw [Finset.smul_sum, ← hrel]
      apply Finset.sum_congr rfl
      intro i _
      rw [hde i]; simp only [mul_smul]
    have : algebraMap A L d * (∑ i, e i • g i) = 0 := by
      rw [← Algebra.smul_def]; exact hsum
    have halg : algebraMap A L d ≠ 0 := fun h => hd0 (hinj (by rw [h, map_zero]))
    exact (mul_eq_zero.mp this).resolve_left halg

/-- The images in `M ⧸ pM` of any `ι`-indexed family in `M` with `Fintype.card ι > [L : K]` are
`A ⧸ p`-linearly dependent. -/
private lemma not_linearIndependent_quotient_family {A K L : Type*}
    [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (p : Ideal A) [p.IsMaximal] (M : Submodule A L)
    {ι : Type*} [Fintype ι] (hcard : Module.finrank K L < Fintype.card ι) (f : ι → M) :
    ¬ LinearIndependent (A ⧸ p)
      (fun i => (Submodule.Quotient.mk (f i) : M ⧸ (p • ⊤ : Submodule A M))) := by
  intro hli
  have hinj : Function.Injective (algebraMap A L) := by
    intro x y h
    have h' : algebraMap K L (algebraMap A K x) = algebraMap K L (algebraMap A K y) := by
      rw [← IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply A K L]
      exact h
    exact IsFractionRing.injective A K ((algebraMap K L).injective h')
  have hdep : ¬ LinearIndependent K (fun i => (f i : L)) := by
    intro hK
    have := hK.fintype_card_le_finrank
    omega
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨c, hc, hcne⟩ := hdep
  obtain ⟨a, ha, hane⟩ := clear_denom (A := A) (K := K) (L := L) (fun i => (f i : L)) c hc hcne
  obtain ⟨e, hespan, herel⟩ := pid_primitive_relation hinj (fun i => (f i : L)) a ha hane
  have hM : (∑ i, e i • f i : M) = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, SetLike.val_smul, Submodule.coe_zero]
    exact herel
  have hsum : (∑ i, (Ideal.Quotient.mk p (e i)) •
      (Submodule.Quotient.mk (f i) : M ⧸ (p • ⊤ : Submodule A M))) = 0 := by
    rw [show (0 : M ⧸ (p • ⊤ : Submodule A M)) = Submodule.mkQ (p • ⊤) (∑ i, e i • f i) by
      rw [hM]; rfl]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    rfl
  have hep : ∀ i, e i ∈ p := fun i => by
    have := (Fintype.linearIndependent_iff.mp hli) (fun i => Ideal.Quotient.mk p (e i)) hsum i
    exact (Ideal.Quotient.eq_zero_iff_mem).mp this
  have htop : (⊤ : Ideal A) ≤ p := by
    rw [← hespan]
    exact Ideal.span_le.mpr (by rintro x ⟨i, rfl⟩; exact hep i)
  exact (Ideal.IsMaximal.ne_top ‹p.IsMaximal›) (top_le_iff.mp htop)

/-- A module `V` over a commutative ring `R`, in which nonzero elements of `R` are invertible and
in which there is no `R`-linearly independent family of length `> n`, is finite over `R`. -/
private lemma module_finite_of_forall_not_linearIndependent {R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V]
    (hinv : ∀ r : R, r ≠ 0 → ∃ s : R, s * r = 1) {n : ℕ}
    (h : ∀ {m : ℕ}, n < m → ∀ v : Fin m → V, ¬ LinearIndependent R v) :
    Module.Finite R V := by
  classical
  have hcard : ∀ S : Finset V, LinearIndepOn R id (S : Set V) → S.card ≤ n := by
    intro S hS
    by_contra hle
    rw [not_le] at hle
    set e := (Finset.equivFin S).symm with he
    have hind : LinearIndependent R (fun i : Fin S.card => (e i : V)) := hS.comp e e.injective
    exact h hle (fun i => (e i : V)) hind
  let P : ℕ → Prop := fun k => ∃ S : Finset V, S.card = k ∧ LinearIndepOn R id (S : Set V)
  have hP0 : P 0 := ⟨∅, rfl, by simp [linearIndepOn_empty]⟩
  set m := Nat.findGreatest P n with hm
  have hmP : P m := Nat.findGreatest_spec (Nat.zero_le n) hP0
  obtain ⟨S, hScard, hSind⟩ := hmP
  have hspan : Submodule.span R (S : Set V) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    by_contra hxs
    have hins : LinearIndepOn R id (insert x (S : Set V)) :=
      LinearIndepOn.id_insert' hSind (fun r hr => by
        by_contra hr0
        obtain ⟨s, hs⟩ := hinv r hr0
        refine hxs ?_
        have h1 : s • (r • x) ∈ Submodule.span R (S : Set V) := Submodule.smul_mem _ s hr
        rwa [← mul_smul, hs, one_smul] at h1)
    have hins' : LinearIndepOn R id ((insert x S : Finset V) : Set V) := by
      rw [Finset.coe_insert]; exact hins
    have hxS : x ∉ S := fun hx => hxs (Submodule.subset_span hx)
    have hc : (insert x S).card = m + 1 := by
      rw [Finset.card_insert_of_notMem hxS, hScard]
    have hPm1 : P (m + 1) := ⟨insert x S, hc, hins'⟩
    have hle' : (insert x S).card ≤ n := hcard (insert x S) hins'
    rw [hc] at hle'
    exact (Nat.findGreatest_eq_iff.mp hm.symm).2.2 (Nat.lt_succ_self m) hle' hPm1
  rw [Module.finite_def]
  rw [← hspan]
  exact Submodule.fg_span S.finite_toSet

theorem submodule_finite_quotient_maximal {A K L : Type*}
    [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (p : Ideal A) [p.IsMaximal] (M : Submodule A L) :
    Module.Finite (A ⧸ p) (M ⧸ (p • ⊤ : Submodule A M)) := by
  refine module_finite_of_forall_not_linearIndependent
    (R := A ⧸ p) (V := M ⧸ (p • ⊤ : Submodule A M)) ?_ (n := Module.finrank K L) ?_
  · intro r hr
    obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (I := p) (a := r) hr
    exact ⟨b, by rw [mul_comm]; exact hb⟩
  · intro m hm v hv
    choose f hf using fun i => Submodule.Quotient.mk_surjective (p • ⊤) (v i)
    have hv' : LinearIndependent (A ⧸ p)
        (fun i => (Submodule.Quotient.mk (f i) : M ⧸ (p • ⊤ : Submodule A M))) := by
      rw [show (fun i => (Submodule.Quotient.mk (f i) : M ⧸ (p • ⊤ : Submodule A M))) = v
        from funext hf]
      exact hv
    exact not_linearIndependent_quotient_family p M (by simpa using hm) f hv'

end Work.CurveBasics.Order
