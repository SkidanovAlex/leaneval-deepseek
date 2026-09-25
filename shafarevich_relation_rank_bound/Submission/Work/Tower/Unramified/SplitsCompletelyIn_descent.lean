import Mathlib
import Submission.Work.Tower.Unramified.Basic
import Submission.Work.Tower.Unramified.SplitsCompletelyIn_ncard
import Submission.Work.Tower.Unramified.SplitsCompletelyNF
import Submission.Work.Tower.Glue.exists_galois_closure_split

/-!
# Complete splitting descends to intermediate fields

If the prime `𝔭` of `𝓞 F` splits completely in the finite extension `L/F`, then it splits
completely in every intermediate field `F ⊆ K ⊆ L`.

The proof is the standard one.  From `SplitsCompletelyIn F L 𝔭` we get that the primes of `𝓞 L`
above `𝔭` are exactly `[L : F]` in number with ramification index and inertia degree `1`
(`Work.Tower.Unramified.SplitsCompletelyIn_ncard` plus the fundamental identity
`Ideal.sum_ramification_inertia_eq_finrank`).  Since `e` and `f` are multiplicative in towers and
divisibility in a tower forces `e(𝔮/𝔭) ∣ e(P/𝔭)` and `f(𝔮/𝔭) ∣ f(P/𝔭)` for any prime `P` of
`𝓞 L` above `𝔮`, every prime of `𝓞 K` above `𝔭` has `e = f = 1`; the fundamental identity in
`K/F` then shows that there are exactly `[K : F]` of them.  Residue fields are identified with
`(𝓞 F) ⧸ 𝔭` by `nonempty_quot_equiv_of_inertiaDeg_eq_one`.

The completely split case `𝔭 = ⊥` is degenerate: it forces `[L : F] = 1` (hence `[K : F] = 1`),
so that `K = F` as `F`-algebras and the ring of integers of `K` is isomorphic to `𝓞 F` via
`AlgEquiv.mapIntegralClosure`.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.Tower.Unramified

/-- The `𝓞 F`-rank of the ring of integers of `L` equals the degree `[L : F]`. -/
theorem finrank_ringOfIntegers_self {F L : Type*} [Field F] [Field L] [NumberField F]
    [NumberField L] [Algebra F L] [FiniteDimensional F L] :
    Module.finrank (𝓞 F) (𝓞 L) = Module.finrank F L :=
  (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 L) L).symm

/-- The `𝓞 F`-rank of the ring of integers of an intermediate field `K` equals `[K : F]`. -/
theorem finrank_ringOfIntegers_intermediate {F L : Type*} [Field F] [Field L] [NumberField F]
    [NumberField L] [Algebra F L] [FiniteDimensional F L] (K : IntermediateField F L)
    [FiniteDimensional F K] :
    Module.finrank (𝓞 F) (𝓞 ↥K) = Module.finrank F ↥K :=
  (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 ↥K) ↥K).symm

/-- If `𝔭 ≠ ⊥` splits completely in `L/F`, then every prime of `𝓞 L` above `𝔭` has ramification
index `1` and inertia degree `1` over `𝓞 F`.

Indeed the primes above `𝔭` number exactly `[L : F]` and each contributes at least `1` to the
fundamental identity `∑_{P | 𝔭} e(P) f(P) = [L : F]`. -/
theorem ef_eq_one_of_splitsCompletelyIn {F L : Type*} [Field F] [Field L] [NumberField F]
    [NumberField L] [Algebra F L] [FiniteDimensional F L] {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭 ≠ ⊥) (h : Work.Tower.SplitsCompletelyIn F L 𝔭) :
    ∀ P : 𝔭.primesOver (𝓞 L),
      P.1.ramificationIdx (𝓞 F) = 1 ∧ P.1.inertiaDeg (𝓞 F) = 1 := by
  classical
  haveI : Fintype (𝔭.primesOver (𝓞 L)) := (Algebra.QuasiFinite.finite_primesOver 𝔭).fintype
  have hcard : (Finset.univ : Finset (𝔭.primesOver (𝓞 L))).card = Module.finrank F L := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact SplitsCompletelyIn_ncard h
  obtain ⟨𝔔, hprime, hlies, -, -⟩ := h
  haveI : 𝔭.IsPrime := Ideal.isPrime_of_liesOver (𝔔 ⟨0, Module.finrank_pos⟩) 𝔭
  haveI : 𝔭.IsMaximal := ‹𝔭.IsPrime›.isMaximal h𝔭
  have hsum : ∑ P : 𝔭.primesOver (𝓞 L),
      P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F) = Module.finrank F L := by
    rw [Ideal.sum_ramification_inertia_eq_finrank (R := 𝓞 F) 𝔭 (𝓞 L), finrank_ringOfIntegers_self]
  have hone : ∀ x ∈ (Finset.univ : Finset (𝔭.primesOver (𝓞 L))),
      1 ≤ x.1.ramificationIdx (𝓞 F) * x.1.inertiaDeg (𝓞 F) := fun x _ =>
    Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (Ideal.ramificationIdx_pos x.1 (𝓞 F)).ne'
      (Ideal.inertiaDeg_pos x.1 (𝓞 F)).ne')
  have hsum' : ∑ x ∈ (Finset.univ : Finset (𝔭.primesOver (𝓞 L))),
      x.1.ramificationIdx (𝓞 F) * x.1.inertiaDeg (𝓞 F)
        = (Finset.univ : Finset (𝔭.primesOver (𝓞 L))).card := by
    rw [hcard, ← hsum]
  intro P
  exact (mul_eq_one_iff_of_one_le
      (Nat.one_le_iff_ne_zero.mpr (Ideal.ramificationIdx_pos P.1 (𝓞 F)).ne')
      (Nat.one_le_iff_ne_zero.mpr (Ideal.inertiaDeg_pos P.1 (𝓞 F)).ne')).mp
    (Work.Tower.Glue.sum_eq_card_imp_eq_one _ _
      (fun x _ => hone x (Finset.mem_univ x)) hsum' P (Finset.mem_univ P))

theorem SplitsCompletelyIn_descent {F L : Type*} [Field F] [Field L] [NumberField F]
    [NumberField L] [Algebra F L] [FiniteDimensional F L] {K : IntermediateField F L}
    [FiniteDimensional F K] {𝔭 : Ideal (NumberField.RingOfIntegers F)}
    (h : Work.Tower.SplitsCompletelyIn F L 𝔭) :
    Work.Tower.SplitsCompletelyIn F ↥K 𝔭 := by
  classical
  rcases eq_or_ne 𝔭 ⊥ with hbot | h𝔭
  · -- Degenerate case `𝔭 = ⊥`: complete splitting forces `[L : F] = 1`, hence `K = F`.
    subst hbot
    have hL1 : Module.finrank F L = 1 := by
      have h1 := SplitsCompletelyIn_ncard h
      rw [Ideal.primesOver_bot, Set.ncard_singleton] at h1
      exact h1.symm
    have hK1 : Module.finrank F ↥K = 1 := by
      have hmul : Module.finrank F ↥K * Module.finrank ↥K L = 1 := by
        rw [Module.finrank_mul_finrank F ↥K L, hL1]
      exact ((mul_eq_one_iff_of_one_le
        (Nat.one_le_iff_ne_zero.mpr (Module.finrank_pos (R := F) (M := ↥K)).ne')
        (Nat.one_le_iff_ne_zero.mpr (Module.finrank_pos (R := ↥K) (M := L)).ne')).mp
          hmul).1
    have hK : K = ⊥ := IntermediateField.finrank_eq_one_iff.mp hK1
    have σ : ↥K ≃ₐ[F] F :=
      (IntermediateField.equivOfEq hK).trans (IntermediateField.botEquiv F L)
    have σZ : ↥K ≃ₐ[ℤ] F := σ.restrictScalars ℤ
    have e : 𝓞 ↥K ≃+* 𝓞 F := (σZ.mapIntegralClosure).toRingEquiv
    refine ⟨fun _ => (⊥ : Ideal (𝓞 ↥K)), ?_, ?_, ?_, ?_⟩
    · intro i; exact Ideal.isPrime_bot
    · intro i; exact ⟨(Ideal.under_bot (𝓞 F) (𝓞 ↥K)).symm⟩
    · intro i j _
      haveI : Subsingleton (Fin (Module.finrank F ↥K)) := by rw [hK1]; infer_instance
      exact Subsingleton.elim i j
    · intro i
      exact ⟨Ideal.quotientEquiv ⊥ ⊥ e Ideal.map_bot.symm⟩
  · -- Main case `𝔭 ≠ ⊥`.
    have hefL := ef_eq_one_of_splitsCompletelyIn h𝔭 h
    obtain ⟨𝔔, hprime, hlies, -, -⟩ := h
    haveI : 𝔭.IsPrime := Ideal.isPrime_of_liesOver (𝔔 ⟨0, Module.finrank_pos⟩) 𝔭
    haveI : 𝔭.IsMaximal := ‹𝔭.IsPrime›.isMaximal h𝔭
    -- Every prime of `𝓞 K` above `𝔭` has `e = f = 1`, by multiplicativity in the tower `F ⊆ K ⊆ L`.
    have hefK : ∀ Q : 𝔭.primesOver (𝓞 ↥K),
        Q.1.ramificationIdx (𝓞 F) = 1 ∧ Q.1.inertiaDeg (𝓞 F) = 1 := by
      intro Q
      obtain ⟨P, hPmax, hPlie⟩ :=
        Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := 𝓞 ↥K) (S := 𝓞 L) Q.1
      haveI : P.LiesOver Q.1 := hPlie
      haveI : P.IsPrime := hPmax.isPrime
      have hPp : P ∈ 𝔭.primesOver (𝓞 L) :=
        ⟨hPmax.isPrime, Ideal.LiesOver.trans P Q.1 𝔭⟩
      obtain ⟨he1, hf1⟩ := hefL ⟨P, hPp⟩
      refine ⟨?_, ?_⟩
      · refine Nat.dvd_one.mp ?_
        rw [← he1]
        exact Ideal.ramificationIdx_below_dvd (R := 𝓞 F) Q.1 P
      · refine Nat.dvd_one.mp ?_
        rw [← hf1]
        exact Ideal.inertiaDeg_below_dvd (R := 𝓞 F) Q.1 P
    -- The fundamental identity in `K/F` now shows that there are exactly `[K : F]` such primes.
    have hcardK : Fintype.card (𝔭.primesOver (𝓞 ↥K)) = Module.finrank F ↥K := by
      have hsum : ∑ Q : 𝔭.primesOver (𝓞 ↥K),
          Q.1.ramificationIdx (𝓞 F) * Q.1.inertiaDeg (𝓞 F) = Module.finrank F ↥K := by
        rw [Ideal.sum_ramification_inertia_eq_finrank (R := 𝓞 F) 𝔭 (𝓞 ↥K),
          finrank_ringOfIntegers_intermediate K]
      have h1 : ∑ _Q : 𝔭.primesOver (𝓞 ↥K), (1 : ℕ)
          = Fintype.card (𝔭.primesOver (𝓞 ↥K)) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
      rw [← h1, ← hsum]
      exact Finset.sum_congr rfl (fun Q _ => by rw [(hefK Q).1, (hefK Q).2, mul_one])
    let e : 𝔭.primesOver (𝓞 ↥K) ≃ Fin (Module.finrank F ↥K) := Fintype.equivFinOfCardEq hcardK
    refine ⟨fun i => (e.symm i).1, fun i => (e.symm i).2.1, fun i => (e.symm i).2.2, ?_, ?_⟩
    · intro i j hij
      exact e.symm.injective (Subtype.ext hij)
    · intro i
      exact nonempty_quot_equiv_of_inertiaDeg_eq_one (F := F) (L := ↥K) (P := (e.symm i).1)
        (hf := (hefK (e.symm i)).2)

end Work.Tower.Unramified
