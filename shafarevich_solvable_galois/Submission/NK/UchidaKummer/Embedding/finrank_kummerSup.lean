import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.NK.UchidaKummer.Embedding.KummerSup
import Submission.NK.UchidaKummer.Embedding.localDeg_eq_one_of_kummerSup
import Submission.NK.UchidaKummer.Embedding.transfer_ellPow_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.UchidaKummer.Embedding

/-- The compositum of the Kummer fields `L(b_P^{1/ℓ})` over the primes of `T` has degree `ℓ ^ T.card`
over `L`, when the local `ℓ`-power classes of the `b_P` are independent in the strong sense that
`b_P` is a non-`ℓ`-th power at `P` and an `ℓ`-th power at every other prime of `T`.

Suggested proof: induction on `T` (`Finset.induction_on`). Write `T = insert P₀ T'`,
`M' := kummerSup ℓ T' b`, `N := kummerField ℓ (b P₀)`, `M := kummerSup ℓ T b`, so that
`M = N ⊔ M'` (`Finset.sup_insert`). Then `N/L` is Galois of degree `ℓ` (use
`NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank`; `b P₀ ∉ powSubgroup ℓ L` because a
global `ℓ`-th power is a local one at `P₀`, contradicting `hnot`), and the induction hypothesis gives
`finrank L ↥M' = ℓ ^ T'.card`.

The key point is `N ⊓ M' = ⊥`. For this it suffices to know `¬ N ≤ M'`: if `N ≤ M'`, take a root
`β : K'` of `X ^ ℓ - b P₀` with `β ∈ N` (`NK.UchidaKummer.Kummer.exists_pow_eq_algebraMap_of_isSepClosure`
with `hζ`), so `b P₀` is an `ℓ`-th power in `↥M'`. `M'` splits completely at `P₀`: apply
`NK.UchidaKummer.Embedding.localDeg_eq_one_of_kummerSup` to `T'` and `𝔮 := P₀` (the hypothesis
`hpow` there is `htriv` at `Q := P₀`). Pick a prime `𝔭` of `↥M'` over `P₀`
(`Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver`) and apply
`NK.UchidaKummer.Embedding.transfer_ellPow_adicCompletion` (with `L := L`, `N := ↥M'`), which
contradicts `hnot` at `P₀`.

From `¬ N ≤ M'` deduce `N ⊓ M' = ⊥` via the simple-order argument: `IntermediateField.restrict`
gives `(N ⊓ M').restrict` as an element of `IntermediateField L ↥N`, whose order is simple because
`Module.finrank L ↥N = ℓ` is prime (`IntermediateField.isSimpleOrder_of_finrank_prime`); use
`IntermediateField.lift_restrict`, `IntermediateField.lift_top`, `IntermediateField.lift_bot`.

Finally `IntermediateField.LinearDisjoint.of_inf_eq_bot` (needs `[IsGalois L ↥N]`,
`[FiniteDimensional L ↥N]`, `[FiniteDimensional L ↥M']`) and
`IntermediateField.LinearDisjoint.finrank_sup` give
`finrank L ↥M = finrank L ↥N * finrank L ↥M' = ℓ * ℓ ^ T'.card`, and `T.card = T'.card + 1`.
Instances for `M'` and `N` come from the induction hypothesis and the Kummer degree results
(`FiniteDimensional.of_finrank_pos`, `Commons.NumberTheory.NumberField.numberField_of_intermediateField`). -/
theorem finrank_kummerSup {L K' : Type*} [Field L] [NumberField L] [Field K'] [Algebra L K']
    [IsSepClosure L K'] (ℓ : ℕ) (hℓ : ℓ.Prime) {ζ : L} (hζ : IsPrimitiveRoot ζ ℓ)
    (T : Finset (NK.Chebotarev.PrimeIdeal L)) (b : NK.Chebotarev.PrimeIdeal L → Lˣ)
    (hnot : ∀ P ∈ T, ¬ ∃ c : (P.adicCompletion L)ˣ,
      algebraMap L (P.adicCompletion L) (b P : L) = (c : P.adicCompletion L) ^ ℓ)
    (htriv : ∀ P ∈ T, ∀ Q ∈ T, Q ≠ P → ∃ c : (Q.adicCompletion L)ˣ,
      algebraMap L (Q.adicCompletion L) (b P : L) = (c : Q.adicCompletion L) ^ ℓ) :
    Module.finrank L ↥(NK.UchidaKummer.Embedding.kummerSup (K' := K') ℓ T b) = ℓ ^ T.card := by
  classical
  have key : ∀ (T : Finset (NK.Chebotarev.PrimeIdeal L))
      (b : NK.Chebotarev.PrimeIdeal L → Lˣ),
      (∀ P ∈ T, ¬ ∃ c : (P.adicCompletion L)ˣ,
        algebraMap L (P.adicCompletion L) (b P : L) = (c : P.adicCompletion L) ^ ℓ) →
      (∀ P ∈ T, ∀ Q ∈ T, Q ≠ P → ∃ c : (Q.adicCompletion L)ˣ,
        algebraMap L (Q.adicCompletion L) (b P : L) = (c : Q.adicCompletion L) ^ ℓ) →
      Module.finrank L ↥(NK.UchidaKummer.Embedding.kummerSup (K' := K') ℓ T b) =
        ℓ ^ T.card := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro b hnot htriv
      rw [NK.UchidaKummer.Embedding.kummerSup, Finset.sup_empty, Finset.card_empty, pow_zero]
      exact IntermediateField.finrank_bot
    | insert P₀ T' hP₀ ih =>
      intro b hnot htriv
      have hnot' : ∀ P ∈ T', ¬ ∃ c : (P.adicCompletion L)ˣ,
          algebraMap L (P.adicCompletion L) (b P : L) = (c : P.adicCompletion L) ^ ℓ :=
        fun P hP => hnot P (Finset.mem_insert_of_mem hP)
      have htriv' : ∀ P ∈ T', ∀ Q ∈ T', Q ≠ P → ∃ c : (Q.adicCompletion L)ˣ,
          algebraMap L (Q.adicCompletion L) (b P : L) = (c : Q.adicCompletion L) ^ ℓ :=
        fun P hP Q hQ hne =>
          htriv P (Finset.mem_insert_of_mem hP) Q (Finset.mem_insert_of_mem hQ) hne
      let M' : IntermediateField L K' := NK.UchidaKummer.Embedding.kummerSup (K' := K') ℓ T' b
      let N : IntermediateField L K' := NK.LocalAnabelian.kummerField (K' := K') ℓ (b P₀)
      let M : IntermediateField L K' :=
        NK.UchidaKummer.Embedding.kummerSup (K' := K') ℓ (insert P₀ T') b
      have hM : M = N ⊔ M' := by
        simp only [M, N, M', NK.UchidaKummer.Embedding.kummerSup, Finset.sup_insert]
      have hfinM' : Module.finrank L ↥M' = ℓ ^ T'.card := ih b hnot' htriv'
      haveI : FiniteDimensional L ↥M' :=
        FiniteDimensional.of_finrank_pos (by rw [hfinM']; exact pow_pos hℓ.pos T'.card)
      haveI : NumberField ↥M' :=
        Commons.NumberTheory.NumberField.numberField_of_intermediateField M'
      -- `N = kummerField ℓ (b P₀)` is Galois of degree `ℓ` over `L`
      have hnotmem : b P₀ ∉ NK.LocalAnabelian.powSubgroup ℓ L := by
        intro hmem
        obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
        rw [powMonoidHom_apply] at hc
        have hc' : (c : L) ^ ℓ = (b P₀ : L) := by
          simpa using congrArg (fun u : Lˣ => (u : L)) hc
        refine hnot P₀ (Finset.mem_insert_self P₀ T')
          ⟨Units.mk0 (algebraMap L (P₀.adicCompletion L) (c : L))
            ((map_ne_zero _).mpr (Units.ne_zero c)), ?_⟩
        rw [Units.val_mk0, ← map_pow, hc']
      obtain ⟨hgalN, hfinN⟩ :=
        NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (k := L) (K' := K')
          ℓ hℓ hζ (b P₀) hnotmem
      haveI : IsGalois L ↥N := hgalN
      have hfinN' : Module.finrank L ↥N = ℓ := hfinN
      haveI : FiniteDimensional L ↥N :=
        FiniteDimensional.of_finrank_pos (by rw [hfinN']; exact hℓ.pos)
      haveI : NumberField ↥N :=
        Commons.NumberTheory.NumberField.numberField_of_intermediateField N
      -- `N ⊄ M'`
      have hnotle : ¬ N ≤ M' := by
        intro hle
        obtain ⟨β, hβ⟩ := NK.UchidaKummer.Kummer.exists_pow_eq_algebraMap_of_isSepClosure
          (k := L) (K' := K') ℓ hℓ hζ (b P₀)
        have hβN : β ∈ N := NK.LocalAnabelian.mem_kummerField_of_pow_eq hβ
        have hβM' : β ∈ M' := hle hβN
        obtain ⟨𝔭, h𝔭lies⟩ :=
          Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
            (K := L) (L := ↥M') P₀
        have hpow : ∀ P ∈ T', ∃ c : (P₀.adicCompletion L)ˣ,
            algebraMap L (P₀.adicCompletion L) (b P : L) = (c : P₀.adicCompletion L) ^ ℓ :=
          fun P hP => htriv P (Finset.mem_insert_of_mem hP) P₀ (Finset.mem_insert_self P₀ T')
            (fun h => hP₀ (h ▸ hP))
        have hldeg : NK.UchidaKummer.localDeg 𝔭 P₀ = 1 :=
          NK.UchidaKummer.Embedding.localDeg_eq_one_of_kummerSup ℓ hℓ hζ T' b P₀ hpow 𝔭 h𝔭lies
        -- `b P₀` is an `ℓ`-th power in the completion of `↥M'` at `𝔭`
        have hb : ∃ c : (𝔭.adicCompletion ↥M')ˣ,
            algebraMap ↥M' (𝔭.adicCompletion ↥M') (algebraMap L ↥M' (b P₀ : L)) =
              (c : 𝔭.adicCompletion ↥M') ^ ℓ := by
          let x : ↥M' := ⟨β, hβM'⟩
          have hxpow : x ^ ℓ = algebraMap L ↥M' (b P₀ : L) := by
            apply Subtype.ext
            simp only [IntermediateField.coe_pow]
            rw [show ((x : ↥M') : K') = β from rfl]
            rw [← IntermediateField.algebraMap_apply M' (algebraMap L ↥M' (b P₀ : L)),
              ← IsScalarTower.algebraMap_apply L ↥M' K' (b P₀ : L)]
            exact hβ
          have hxne : x ≠ 0 := by
            intro h0
            have hw : algebraMap L ↥M' (b P₀ : L) = 0 := by
              rw [← hxpow, h0, zero_pow hℓ.ne_zero]
            exact Units.ne_zero (b P₀) ((map_eq_zero (algebraMap L ↥M')).mp hw)
          refine ⟨Units.mk0 (algebraMap ↥M' (𝔭.adicCompletion ↥M') x)
            ((map_ne_zero _).mpr hxne), ?_⟩
          rw [Units.val_mk0, ← map_pow, hxpow]
        exact hnot P₀ (Finset.mem_insert_self P₀ T')
          (NK.UchidaKummer.Embedding.transfer_ellPow_adicCompletion ℓ P₀ 𝔭 h𝔭lies hldeg
            (b P₀) hb)
      -- `N ⊓ M' = ⊥` by the simple-order argument
      have hinf : N ⊓ M' = ⊥ := by
        haveI : IsSimpleOrder (IntermediateField L ↥N) :=
          IntermediateField.isSimpleOrder_of_finrank_prime L ↥N (by rw [hfinN']; exact hℓ)
        rcases IsSimpleOrder.eq_bot_or_eq_top ((N ⊓ M').restrict inf_le_left) with h | h
        · rw [← IntermediateField.lift_restrict (F := N ⊓ M') (E := N) inf_le_left, h]
          exact IntermediateField.lift_bot L N
        · exfalso
          have h2 : N ⊓ M' = N := by
            rw [← IntermediateField.lift_restrict (F := N ⊓ M') (E := N) inf_le_left, h]
            exact IntermediateField.lift_top L N
          exact hnotle (h2 ▸ inf_le_right)
      have hLD : N.LinearDisjoint ↥M' := IntermediateField.LinearDisjoint.of_inf_eq_bot hinf
      have hsuprank : Module.finrank L ↥(N ⊔ M') = ℓ * ℓ ^ T'.card := by
        rw [IntermediateField.LinearDisjoint.finrank_sup hLD, hfinN', hfinM']
      show Module.finrank L ↥M = ℓ ^ (insert P₀ T').card
      rw [hM, hsuprank, Finset.card_insert_of_notMem hP₀, pow_succ]
      exact Nat.mul_comm ℓ (ℓ ^ T'.card)
  exact key T b hnot htriv


end NK.UchidaKummer.Embedding
