import Mathlib
import Submission.Work.BG.centralIntegral
import Submission.Work.BG.CharBridge
import Submission.Work.BG.S02
import Submission.Work.BG.s02_abstractCoherence

namespace Work.BG

open OddOrder.RepresentationTheory Work.BG

/-! ### Two auxiliary lemmas (independent of the ambient character theory)

The main theorem `Work.BG.c3deChiEven` is assembled from

* a **Sylow/index** statement: if a subgroup `L` of a Sylow `2`-subgroup `S` has `[S : L] ≤ 2`
  and is contained in `C`, then `4 ∤ [G : C]` — so the class size of a `u` centralized by `L`
  has `2`-part at most two;
* an **arithmetic** statement: if `y` is an algebraic integer and `n · y / 4` is an algebraic
  integer for a natural number `n` not divisible by `4`, then `y / 2` is an algebraic integer.

Both are stated for arbitrary groups/natural numbers; they are the only inputs besides
Gorenstein 4.2.10 (`Work.BG.centralIntegral`) and the integrality of character values
(`OddOrder.RepresentationTheory.character_isIntegral`). -/

/-- **Sylow/index arithmetic.** If `S` is a Sylow `2`-subgroup of a finite group `G`, `L ≤ S`
with `[S : L] ≤ 2` and `L ≤ C`, then `4 ∤ [G : C]`.

Indeed `[G : L] = [G : S] · [S : L]` with `[G : S]` odd (Sylow) and `[S : L] ≤ 2`, so the
`2`-part of `[G : L]` is at most `2`; and `[G : C] ∣ [G : L]` since `L ≤ C`. -/
theorem c3deSylowIndexAux {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (L C : Subgroup G) (hLS : L ≤ (S : Subgroup G)) (hLC : L ≤ C)
    (hL2 : L.relIndex (S : Subgroup G) ≤ 2) : ¬ 4 ∣ C.index := by
  classical
  set T : Subgroup G := (S : Subgroup G) ⊓ C with hT
  have hLT : L ≤ T := le_inf hLS hLC
  have hTS : T ≤ (S : Subgroup G) := inf_le_left
  have hTC : T ≤ C := inf_le_right
  -- `[G : C]` divides `[G : T]`
  have hdvd : C.index ∣ T.index := Subgroup.index_dvd_of_le hTC
  -- `[G : T] = [S : T] · [G : S]`
  have hTidx : T.index = T.relIndex (S : Subgroup G) * (S : Subgroup G).index :=
    (Subgroup.relIndex_mul_index hTS).symm
  have hLne : L.relIndex (S : Subgroup G) ≠ 0 := by
    rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite
  have hTne : T.relIndex (S : Subgroup G) ≠ 0 := by
    rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite
  -- `[S : T] ≤ [S : L] ≤ 2` since `L ≤ T ≤ S`
  have hle : T.relIndex (S : Subgroup G) ≤ L.relIndex (S : Subgroup G) :=
    Subgroup.relIndex_le_of_le_left hLT hLne
  have hle2 : T.relIndex (S : Subgroup G) ≤ 2 := le_trans hle hL2
  -- the index of a Sylow `2`-subgroup is odd
  have hSodd : Odd (S : Subgroup G).index := by
    have h := @Sylow.not_dvd_index 2 G _ _ S _
    exact Nat.not_even_iff_odd.mp (by simpa [Nat.even_iff] using h)
  intro h4dvd
  have h4T : 4 ∣ T.index := dvd_trans h4dvd hdvd
  have hcop : Nat.Coprime 4 (S : Subgroup G).index := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl]
    exact (Nat.coprime_two_left.mpr hSodd).pow_left 2
  have h4r : 4 ∣ T.relIndex (S : Subgroup G) := by
    have : 4 ∣ T.relIndex (S : Subgroup G) * (S : Subgroup G).index := by rwa [← hTidx]
    exact hcop.dvd_of_dvd_mul_right this
  obtain ⟨k, hk⟩ := h4r
  omega

/-- **Arithmetic parity step.** If `y` is an algebraic integer, `n ∈ ℕ` is not divisible by
`4`, and `n · y / 4` is an algebraic integer, then `y / 2` is an algebraic integer.

(Case `n` odd: `n · y / 2 = 2 · (n · y / 4)` and `y / 2 = n·y/2 - ((n-1)/2)·y`.  Case
`n ≡ 2 mod 4`: `n = 2m` with `m` odd, `n·y/4 = m·y/2` and `y/2 = m·y/2 - ((m-1)/2)·y`.) -/
theorem c3deIntegralDivTwoAux {y : ℂ} (n : ℕ) (hy : IsIntegral ℤ y)
    (h : IsIntegral ℤ ((n : ℂ) * y / 4)) (hn : ¬ 4 ∣ n) : IsIntegral ℤ (y / 2) := by
  have key : ∀ m : ℕ, Odd m → IsIntegral ℤ ((m : ℂ) * y / 2) → IsIntegral ℤ (y / 2) := by
    intro m hm hint
    obtain ⟨j, hj⟩ := hm
    have hyj : IsIntegral ℤ (y * (j : ℂ)) := hy.mul (isIntegral_natCast j)
    have hsub : IsIntegral ℤ ((m : ℂ) * y / 2 - y * (j : ℂ)) := hint.sub hyj
    convert hsub using 1
    push_cast [hj]
    ring
  have hmod : n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
    have hne : n % 4 ≠ 0 := fun h0 => hn (Nat.dvd_of_mod_eq_zero h0)
    omega
  rcases hmod with h1 | h1 | h1
  · -- `n` odd
    have hm : Odd n := by
      obtain ⟨t, ht⟩ : ∃ t, n = 4 * t + 1 := ⟨n / 4, by omega⟩
      exact ⟨2 * t, by omega⟩
    refine key n hm ?_
    have h2n : IsIntegral ℤ (((n : ℂ) * y / 4) * 2) := h.mul (isIntegral_intCast 2)
    convert h2n using 1
    ring
  · -- `n = 2m` with `m` odd
    obtain ⟨t, ht⟩ : ∃ t, n = 4 * t + 2 := ⟨n / 4, by omega⟩
    have hm : Odd (2 * t + 1) := ⟨t, rfl⟩
    have hmul : n = 2 * (2 * t + 1) := by omega
    refine key (2 * t + 1) hm ?_
    convert h using 1
    push_cast [hmul]
    ring
  · -- `n` odd
    have hm : Odd n := by
      obtain ⟨t, ht⟩ : ∃ t, n = 4 * t + 3 := ⟨n / 4, by omega⟩
      exact ⟨2 * t + 1, by omega⟩
    refine key n hm ?_
    have h2n : IsIntegral ℤ (((n : ℂ) * y / 4) * 2) := h.mul (isIntegral_intCast 2)
    convert h2n using 1
    ring

open OddOrder.RepresentationTheory Work.BG in
/-- Gorenstein 4.2.10 (`Work.BG.centralIntegral`): if `χ ∈ ±Irr(G)` has `4 ∣ χ(1)` and `u` is
centralized by a subgroup `L · S` of index at most `2` in a Sylow `2`-subgroup `S`, then `χ(u)`
is `0` modulo `2` (as an algebraic integer). -/
theorem c3deChiEven {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (S : Sylow 2 G) {χ : ClassFunction G ℂ} (hχ : Work.BG.IsPmIrr χ)
    (h4 : ∃ k : ℤ, χ 1 = (4 : ℂ) * (k : ℂ)) {u : G}
    (hL : ∃ L : Subgroup G, L ≤ (S : Subgroup G) ∧ L.relIndex (S : Subgroup G) ≤ 2 ∧
      (∀ l ∈ L, l * u = u * l)) :
    Work.BG.AlgIntModTwo (χ u) 0 := by
  obtain ⟨L, hLle, hLrel, hcomm⟩ := hL
  obtain ⟨k, hk⟩ := h4
  -- `L` centralizes `u`
  have hLC : L ≤ Subgroup.centralizer ({u} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm l hl)
  -- hence the class size of `u` has `2`-part at most `2`
  have hnot4 : ¬ 4 ∣ (Subgroup.centralizer ({u} : Set G)).index :=
    c3deSylowIndexAux S L (Subgroup.centralizer ({u} : Set G)) hLle hLC hLrel
  -- character values are algebraic integers
  have hψint : ∀ ψ : ClassFunction G ℂ, IsIrreducibleCharacter ψ → IsIntegral ℤ (ψ u) := by
    intro ψ hψ
    obtain ⟨V, hV1, hV2, hV3, ρ, _hρ, hψρ⟩ := hψ
    letI := hV1
    letI := hV2
    letI := hV3
    have hval : ψ u = ρ.character u := by simpa using congrFun hψρ u
    rw [hval]
    exact character_isIntegral ρ u
  have hχint : IsIntegral ℤ (χ u) := by
    rcases hχ with h | h
    · exact hψint χ h
    · have hneg := hψint (-χ) h
      rw [ClassFunction.neg_apply] at hneg
      simpa using hneg.neg
  -- Gorenstein 4.2.10: `|G : C_G(u)| · χ(u) / χ(1)` is an algebraic integer
  have hCI : IsIntegral ℤ
      (((Subgroup.centralizer ({u} : Set G)).index : ℂ) * χ u / χ 1) := by
    rcases hχ with h | h
    · exact centralIntegral (K := G) χ h u
    · have hneg := centralIntegral (K := G) (-χ) h u
      simpa using hneg
  -- multiply by `χ(1)/4 = k`, giving integrality of `|G : C_G(u)| · χ(u) / 4`
  have hχ1ne : χ 1 ≠ 0 := hχ.apply_one_ne_zero
  have hkne : (k : ℂ) ≠ 0 := by
    intro h0
    exact hχ1ne (by rw [hk, h0, mul_zero])
  have hMint : IsIntegral ℤ (((Subgroup.centralizer ({u} : Set G)).index : ℂ) * χ u / 4) := by
    have hmul : IsIntegral ℤ
        (((Subgroup.centralizer ({u} : Set G)).index : ℂ) * χ u / χ 1 * (k : ℂ)) :=
      hCI.mul (isIntegral_intCast k)
    have heq : ((Subgroup.centralizer ({u} : Set G)).index : ℂ) * χ u / χ 1 * (k : ℂ)
        = ((Subgroup.centralizer ({u} : Set G)).index : ℂ) * χ u / 4 := by
      rw [hk]
      field_simp
    rwa [heq] at hmul
  -- conclude
  have h2 : IsIntegral ℤ (χ u / 2) :=
    c3deIntegralDivTwoAux (Subgroup.centralizer ({u} : Set G)).index hχint hMint hnot4
  exact ⟨χ u / 2, h2, by ring⟩

end Work.BG
