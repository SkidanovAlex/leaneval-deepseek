import Mathlib

set_option linter.unusedVariables false -- v435-speed

namespace Work.MotAS.ASRulV2M

open MvPolynomial

/-- The fraction field of a domain is algebraic over the domain. -/
lemma isAlgebraic_fractionRing_self (S : Type*) [CommRing S] [IsDomain S] :
    Algebra.IsAlgebraic S (FractionRing S) := by
  rw [← IsFractionRing.isAlgebraic_iff' S S (FractionRing S)]
  infer_instance

theorem trdeg_span_prime_eq_two {K : Type*} [Field K] (p : MvPolynomial (Fin 3) K)
    (hp : Prime p) :
    Algebra.trdeg K (FractionRing (MvPolynomial (Fin 3) K ⧸ Ideal.span {p})) = 2 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  haveI hIprime : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp0).mpr hp
  haveI hRdomain : IsDomain (MvPolynomial (Fin 3) K ⧸ Ideal.span {p}) := inferInstance
  -- The fraction field is algebraic over the quotient, so the transcendence degree is unchanged.
  have htr : Algebra.trdeg K (FractionRing (MvPolynomial (Fin 3) K ⧸ Ideal.span {p}))
      = Algebra.trdeg K (MvPolynomial (Fin 3) K ⧸ Ideal.span {p}) := by
    haveI : Algebra.IsAlgebraic (MvPolynomial (Fin 3) K ⧸ Ideal.span {p})
        (FractionRing (MvPolynomial (Fin 3) K ⧸ Ideal.span {p})) :=
      isAlgebraic_fractionRing_self _
    have h := trdeg_add_eq K (MvPolynomial (Fin 3) K ⧸ Ideal.span {p})
      (A := FractionRing (MvPolynomial (Fin 3) K ⧸ Ideal.span {p}))
    have h2 : Algebra.trdeg (MvPolynomial (Fin 3) K ⧸ Ideal.span {p})
        (FractionRing (MvPolynomial (Fin 3) K ⧸ Ideal.span {p})) = 0 := trdeg_eq_zero
    rw [h2, add_zero] at h
    exact h.symm
  rw [htr]
  refine le_antisymm ?_ ?_
  · -- upper bound : `trdeg ≤ 2`, because `p ≠ 0` is a nontrivial relation among the
    -- three generators `X₀, X₁, X₂`.
    by_contra hcon
    rw [not_le] at hcon
    have h3 : (3 : Cardinal) ≤ Algebra.trdeg K (MvPolynomial (Fin 3) K ⧸ Ideal.span {p}) := by
      have hh : ((2 : Cardinal) + 1 : Cardinal) ≤
          Algebra.trdeg K (MvPolynomial (Fin 3) K ⧸ Ideal.span {p}) :=
        (Cardinal.natCast_add_one_le_iff (n := 2) (c := _)).mpr hcon
      convert hh using 1
      norm_cast
    let v : Fin 3 → (MvPolynomial (Fin 3) K ⧸ Ideal.span {p}) :=
      fun i => Ideal.Quotient.mk (Ideal.span {p}) (MvPolynomial.X i)
    have hgen : Algebra.adjoin K (Set.range v) = ⊤ := by
      have hrange : Set.range v
          = (Ideal.Quotient.mkₐ K (Ideal.span {p})) '' Set.range MvPolynomial.X := by
        ext a
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨MvPolynomial.X i, ⟨i, rfl⟩, rfl⟩
        · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, rfl⟩
      rw [hrange, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top]
      exact (AlgHom.range_eq_top (Ideal.Quotient.mkₐ K (Ideal.span {p}))).mpr
        (Ideal.Quotient.mkₐ_surjective K (Ideal.span {p}))
    haveI hinst : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range v))
        (MvPolynomial (Fin 3) K ⧸ Ideal.span {p}) := by
      rw [hgen]
      exact ⟨fun a => ⟨Polynomial.X - Polynomial.C ⟨a, by simp⟩,
        by simp [Polynomial.X_sub_C_ne_zero], by simp⟩⟩
    have hbasis : IsTranscendenceBasis K v :=
      Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite K v (by
        simpa using h3)
    have hinj : Function.Injective (MvPolynomial.aeval v) :=
      algebraicIndependent_iff_injective_aeval.mp hbasis.1
    have haeval : (MvPolynomial.aeval v : MvPolynomial (Fin 3) K →ₐ[K] _)
        = Ideal.Quotient.mkₐ K (Ideal.span {p}) := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [MvPolynomial.aeval_X]
      rw [Ideal.Quotient.mkₐ_eq_mk]
    have h0 : (MvPolynomial.aeval v) p = 0 := by
      rw [haeval, Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton p))
    exact hp0 (hinj (by rw [h0, map_zero]))
  · -- lower bound : `2 ≤ trdeg`, because `p` involves some variable, whence the two
    -- remaining variables are algebraically independent in the quotient.
    obtain ⟨i0, hi0⟩ : ∃ i : Fin 3, p.degreeOf i ≠ 0 := by
      by_contra hcon
      have hall : ∀ i : Fin 3, p.degreeOf i = 0 := by
        intro i
        by_contra hi
        exact hcon ⟨i, hi⟩
      have hvars : p.vars = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro i hi
        exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) (hall i)
      rw [MvPolynomial.vars_eq_empty_iff_eq_C] at hvars
      have hc : p.coeff 0 ≠ 0 := fun hc => hp0 (by rw [hvars, hc, map_zero])
      exact hp.not_isUnit (by
        rw [hvars]
        exact (isUnit_iff_ne_zero.mpr hc).map (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K))
    let σ := {j : Fin 3 // j ≠ i0}
    let emb : σ → Fin 3 := fun j => j.1
    have hemb : Function.Injective emb := fun a b h => Subtype.ext h
    let ψ : MvPolynomial σ K →ₐ[K] (MvPolynomial (Fin 3) K ⧸ Ideal.span {p}) :=
      (Ideal.Quotient.mkₐ K (Ideal.span {p})).comp (MvPolynomial.rename emb)
    have hker : ∀ f : MvPolynomial σ K, ψ f = 0 → f = 0 := by
      intro f hf
      have hmem : MvPolynomial.rename emb f ∈ Ideal.span {p} := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        simpa [ψ, Ideal.Quotient.mkₐ_eq_mk] using hf
      rw [Ideal.mem_span_singleton] at hmem
      obtain ⟨h, hh⟩ := hmem
      -- `rename emb f` does not involve `X_{i0}`, while `p` does.
      have hdeg : MvPolynomial.degreeOf i0 (MvPolynomial.rename emb f) = 0 := by
        by_contra hne
        have hmem2 : i0 ∈ (MvPolynomial.rename emb f).vars :=
          (MvPolynomial.mem_vars_iff_degreeOf_ne_zero).mpr hne
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ((MvPolynomial.vars_rename emb f) hmem2)
        exact i.2 hi
      by_cases hh0 : h = 0
      · have : MvPolynomial.rename emb f = 0 := by rw [hh, hh0, mul_zero]
        exact (MvPolynomial.rename_eq_zero_iff_of_injective f hemb).mp this
      · exfalso
        have hmul := MvPolynomial.degreeOf_mul_eq (n := i0) hp0 hh0
        rw [← hh, hdeg] at hmul
        omega
    have hψ : Function.Injective ψ := by
      intro f g hfg
      have : f - g = 0 := hker (f - g) (by rw [map_sub, hfg, sub_self])
      exact sub_eq_zero.mp this
    have hcardF : Fintype.card σ = 2 := by
      have h := Fintype.card_subtype_compl (α := Fin 3) (p := fun j : Fin 3 => j = i0)
      rw [Fintype.card_subtype_eq, Fintype.card_fin] at h
      change Fintype.card {j : Fin 3 // j ≠ i0} = 2
      exact h
    have hcard : Cardinal.mk σ = 2 := by
      rw [Cardinal.mk_fintype, hcardF]
      norm_num
    have htrσ : Algebra.trdeg K (MvPolynomial σ K) = 2 := by
      rw [MvPolynomial.trdeg_of_isDomain, hcard]
      simp
    have hle := trdeg_le_of_injective ψ hψ
    rw [htrσ] at hle
    exact hle

end Work.MotAS.ASRulV2M
