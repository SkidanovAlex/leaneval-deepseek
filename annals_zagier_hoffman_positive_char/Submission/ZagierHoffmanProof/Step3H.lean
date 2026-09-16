import Submission.ZagierHoffmanProof.Step3General
import Submission.ZagierHoffmanProof.BridgeP2
import Submission.ZagierHoffmanProof.HDatum
import Submission.ZagierHoffmanProof.TpTrans
import Submission.Commons.Combinatorics.TupleCount.tail_shape

/-!
# Dac §5.3 Step 3 (a) for the Anderson–Thakur datum `Q_j = H_{s_j}`

`Step3General.lean` runs Dac's §5.3 Step 3 for a datum whose `Q`-entries are all `1` (`MZVD`).
For Dac's Theorem 6.2 (`𝒯'_w`, entries not divisible by `q`) the datum is
`Q_j = H_{s_j} = ambH F s_j` (the Anderson–Thakur polynomials), so the bridge used on the dropped
tail is `BridgeP2.bridgeP_mul` rather than `ATBridge2.bridge_mul`, and it carries the extra factor
`∏_j ambGammaF F (s_j) ∈ ambK^×`.

This module provides

* the datum structure `MZVDH` (positions `q ∤ s_i`, entries `≤ 2q-2`, `Q = H_s`, common weight `w`);
* `dvd_pred_weight_H`, the divisibility **(q-1) ∣ (w - w(𝔱))** of Dac §5.3 Step 3 for such a datum,
  the key input of the `𝒯'`-induction (`TupleIndP`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
open Polynomial PowerSeries Finset
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

/-- A `Finset` of exponent tuples of the Anderson–Thakur type: entries with no position divisible
by `q`, exponents `≥ 1` and `≤ 2q-2`, `Q`-entry `H_s = ambH F s`, all of the same weight `w`. -/
structure MZVDH (F : Type*) [Field F] [Finite F] (w : ℕ) where
  /-- the tuples -/
  S : Finset (List (ℕ × Polynomial (Ambient F)))
  /-- the `Q`'s are the Anderson–Thakur polynomials `H_s` -/
  entry : ∀ s ∈ S, ∀ x ∈ s, x.2 = ambH F x.1
  /-- all exponents are `≥ 1` -/
  pos : ∀ s ∈ S, ∀ x ∈ s, 1 ≤ x.1
  /-- all exponents are `≤ 2q-2` -/
  le : ∀ s ∈ S, ∀ x ∈ s, x.1 ≤ 2 * Nat.card F - 2
  /-- no exponent is divisible by `q` -/
  nd : ∀ s ∈ S, ∀ x ∈ s, ¬ Nat.card F ∣ x.1
  /-- all tuples have weight `w` -/
  weight : ∀ s ∈ S, tmWeight s = w

section General

variable {F : Type*} [Field F] [Finite F] [DecidableEq (RatFunc F)]

attribute [local instance 100] Classical.decEq

lemma MZVDH.drop_entry {w : ℕ} (D : MZVDH F w) {s : List (ℕ × Polynomial (Ambient F))}
    (hs : s ∈ D.S) (k : ℕ) : ∀ x ∈ s.drop k, x.2 = ambH F x.1 := by
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (List.mem_of_mem_drop hx)
  exact D.entry s hs _ (List.get_mem s j)

lemma MZVDH.drop_pos {w : ℕ} (D : MZVDH F w) {s : List (ℕ × Polynomial (Ambient F))}
    (hs : s ∈ D.S) (k : ℕ) : ∀ x ∈ s.drop k, 1 ≤ x.1 := by
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (List.mem_of_mem_drop hx)
  exact D.pos s hs _ (List.get_mem s j)

lemma MZVDH.drop_le {w : ℕ} (D : MZVDH F w) {s : List (ℕ × Polynomial (Ambient F))}
    (hs : s ∈ D.S) (k : ℕ) : ∀ x ∈ s.drop k, x.1 ≤ 2 * Nat.card F - 2 := by
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (List.mem_of_mem_drop hx)
  exact D.le s hs _ (List.get_mem s j)

lemma MZVDH.drop_weight {w : ℕ} (D : MZVDH F w) {s : List (ℕ × Polynomial (Ambient F))}
    (hs : s ∈ D.S) (k : ℕ) : tmWeight (s.drop k) + tmWeight (s.take k) = w := by
  have h1 := tmWeight_take_add_drop s k
  have h2 := D.weight s hs
  omega

/-- `suffixList` of a tuple whose `Q`-entries are `H_s` has `Q`-entries `↑(H_s)`. -/
lemma suffixList_mem_ambH {L : List (ℕ × Polynomial (Ambient F))}
    (hL : ∀ x ∈ L, x.2 = ambH F x.1) :
    ∀ x ∈ suffixList F L, x.2 = ((ambH F x.1 : Polynomial (Ambient F)) : PowerSeries (Ambient F)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_suffixList F).mp hx
  rw [hL y hy]

/-- `suffixList` of a tuple with exponents `≤ 2q-2` has exponents `≤ 2q-2`. -/
lemma suffixList_mem_le_two {L : List (ℕ × Polynomial (Ambient F))}
    (hL : ∀ x ∈ L, x.1 ≤ 2 * Nat.card F - 2) :
    ∀ x ∈ suffixList F L, x.1 ≤ 2 * Nat.card F - 2 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_suffixList F).mp hx
  exact hL y hy

/-- `GSuperEntire` of the `L`-series of the dropped tail, for the Anderson–Thakur datum. -/
lemma gSuperEntire_tmL_dropH {w : ℕ} (D : MZVDH F w) {s : List (ℕ × Polynomial (Ambient F))}
    (hs : s ∈ D.S) (k : ℕ) :
    GSuperEntire ambGamma (tmL (Nat.card F) (ambOmega F) (s.drop k)) := by
  have hsm : ∀ s' ∈ D.S, ∀ y ∈ s',
      GIsSmall ambGamma ((ambOmega F) ^ y.1 * (y.2 : PowerSeries (Ambient F))) := by
    intro s' hs' y hy
    rw [D.entry s' hs' y hy]
    exact gIsSmall_ambOmega_pow_mul_ambH F (D.pos s' hs' y hy)
  have hSse : ∀ s' ∈ D.S, ∀ y ∈ s', GSuperEntire ambGamma ((y.2 : PowerSeries (Ambient F))) := by
    intro s' hs' y hy
    rw [D.entry s' hs' y hy]
    exact gSuperEntire_ambH F _
  exact gSuperEntire_tmL_of_mem (F := F) (γ := ambGamma) (ω := ambOmega F) (S := D.S)
    (u := s.drop k) ambGamma_lt_one gammaArchimedean_rat (two_le_ambCard F)
    (gIsSmall_ambOmega F) (gSuperEntire_ambOmega F) hsm hSse
    (fun y hy => ⟨s, hs, List.mem_of_mem_drop hy⟩)

/-- **Step 3's divisibility `(q-1) ∣ w - w(𝔱)` for the Anderson–Thakur datum** (Dac §5.3 Step 3,
the form used in the `𝒯'`-induction). -/
theorem dvd_pred_weight_H {w : ℕ} (_hw : 1 ≤ w) (D : MZVDH F w)
    {s₀ : List (ℕ × Polynomial (Ambient F))} (hs₀ : s₀ ∈ D.S) {k : ℕ}
    (hkl : k < s₀.length)
    (huniq : ∀ s ∈ D.S, s.take k = s₀.take k → s = s₀)
    {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}
    {b : Polynomial (Ambient F)} (hcf : cf s₀ = b)
    (hbmem : ∀ j, b.coeff j ∈ ambA F 0) (hb0 : b.eval (ambTheta F) ≠ 0)
    (hζ : ζ_A F (suffixExp F (s₀.drop k) (D.drop_pos hs₀ k)) ≠ 0)
    (hfK : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S cf (s₀.take k)) (ambTheta F)
      ∈ ambK F)
    (hf0 : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S cf (s₀.take k)) (ambTheta F)
      ≠ 0) :
    (Nat.card F - 1) ∣ (w - tmWeight (K := Ambient F) (s₀.take k)) := by
  have hq2 : 2 ≤ Nat.card F := two_le_ambCard F
  have hII := evalSeriesGen_tmF_gen (F := F) (w := w) (S := D.S) (cf := cf) hs₀
    (le_of_lt hkl) huniq hcf (gSuperEntire_tmL_dropH (F := F) D hs₀ k)
  have hbridge := bridgeP_mul F (suffixList F (s₀.drop k))
    (suffixList_ne_nil F (drop_ne_nil_of_lt_length hkl))
    (fun j => suffixList_mem_ambH (F := F) (D.drop_entry hs₀ k)
      _ (List.get_mem (suffixList F (s₀.drop k)) j))
    (fun j => suffixList_mem_pos F (D.drop_pos hs₀ k)
      _ (List.get_mem (suffixList F (s₀.drop k)) j))
    (fun j => suffixList_mem_le_two (F := F) (D.drop_le hs₀ k)
      _ (List.get_mem (suffixList F (s₀.drop k)) j))
    (suffixExp F (s₀.drop k) (D.drop_pos hs₀ k))
    (fun j => rfl)
    (fun j => by
      simp only [suffixExp_apply]
      exact suffixList_mem_le_two (F := F) (D.drop_le hs₀ k) _
        (List.get_mem (suffixList F (s₀.drop k)) (Fin.rev j)))
    b
  have hstep : (ambPiTilde F) ^ (∑ j : Fin (suffixList F (s₀.drop k)).length,
        (suffixExp F (s₀.drop k) (D.drop_pos hs₀ k) j : ℕ))
      * evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S cf (s₀.take k)) (ambTheta F)
      = (∏ j : Fin (suffixList F (s₀.drop k)).length,
            ambGammaF F ((suffixExp F (s₀.drop k) (D.drop_pos hs₀ k) j : ℕ)))
        * (b.eval (ambTheta F) * ambInfHom F (ζ_A F
          (suffixExp F (s₀.drop k) (D.drop_pos hs₀ k)))) := by
    rw [hII]
    exact hbridge
  have hwt : tmWeight (K := Ambient F) s₀ = w := D.weight s₀ hs₀
  have h1 : (∑ j : Fin (suffixList F (s₀.drop k)).length,
      (suffixExp F (s₀.drop k) (D.drop_pos hs₀ k) j : ℕ))
      = tmWeight (K := Ambient F) (s₀.drop k) := by
    have h := suffixList_weight F (s₀.drop k)
    simp only [suffixExp_apply]
    exact h
  have hfinal : (ambPiTilde F) ^ (tmWeight (K := Ambient F) (s₀.drop k))
      * evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S cf (s₀.take k)) (ambTheta F)
      = (∏ j : Fin (suffixList F (s₀.drop k)).length,
            ambGammaF F ((suffixExp F (s₀.drop k) (D.drop_pos hs₀ k) j : ℕ)))
        * (b.eval (ambTheta F) * ambInfHom F (ζ_A F
          (suffixExp F (s₀.drop k) (D.drop_pos hs₀ k)))) := by
    rw [← h1]; exact hstep
  have h2 : w - tmWeight (K := Ambient F) (s₀.take k)
      = tmWeight (K := Ambient F) (s₀.drop k) := by
    have h3 := tmWeight_take_add_drop (K := Ambient F) s₀ k
    omega
  rw [h2]
  set 𝔰 := suffixExp F (s₀.drop k) (D.drop_pos hs₀ k) with h𝔰def
  have hΓmem : (∏ j : Fin (suffixList F (s₀.drop k)).length, ambGammaF F (𝔰 j : ℕ))
      ∈ ambK F := (ambK F).prod_mem (fun j _ => ambGammaF_mem_ambK F _)
  have hΓ0 : (∏ j : Fin (suffixList F (s₀.drop k)).length, ambGammaF F (𝔰 j : ℕ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => ambGammaF_ne_zero F _)
  refine dvd_pred_of_v_eq_exp_mul
    (m := tmWeight (K := Ambient F) (s₀.drop k))
    (y := (ambPiTilde F) ^ (tmWeight (K := Ambient F) (s₀.drop k)))
    (u := (∏ j : Fin (suffixList F (s₀.drop k)).length, ambGammaF F (𝔰 j : ℕ))
      * (b.eval (ambTheta F) * ambInfHom F (ζ_A F 𝔰)))
    (v := evalSeriesGen (tmF (Nat.card F) (ambOmega F) w D.S cf (s₀.take k)) (ambTheta F))
    (hy := ?_) (hu := ?_) (hv := ?_) (hv0 := hf0) (h := hfinal)
  · exact v_ambPiTilde_pow F _
  · obtain ⟨k₁, hk₁⟩ := v_mem_ambK F hΓmem hΓ0
    obtain ⟨k₂, hk₂⟩ := v_mem_ambK F (eval_mem_ambK F b hbmem) hb0
    obtain ⟨k₃, hk₃⟩ := v_ambInfHom_mem_pred F _ hζ
    refine ⟨k₁ + k₂ + k₃, ?_⟩
    rw [map_mul, map_mul, hk₁, hk₂, hk₃, ← WithZero.exp_add, ← WithZero.exp_add]
    congr 1
    push_cast
    ring
  · exact v_mem_ambK F hfK hf0


/-- **Step 3(b) for the Anderson–Thakur datum (Dac §6, Theorem 6.2): the SHAPE conclusion.**
Given the divisibility `(q-1) ∣ w - w(𝔱)` for every prefix `𝔱` of every tuple of the datum (the
output of `dvd_pred_weight_H`), and `w ≤ 2q-2`, every tuple of the datum is either the single-entry
tuple `(w)` or the two-entry tuple `(w-(q-1), q-1)`. -/
theorem shape_of_dvd_H {w : ℕ} (hq : 3 ≤ Nat.card F) (hw1 : 1 ≤ w)
    (hw2 : w ≤ 2 * Nat.card F - 2) (D : MZVDH F w)
    (hdiv : ∀ s ∈ D.S, ∀ k : ℕ, 1 ≤ k → k ≤ s.length →
      (Nat.card F - 1) ∣ tmWeight (K := Ambient F) (s.drop k)) :
    ∀ s ∈ D.S,
      s.map Prod.fst = [w] ∨ s.map Prod.fst = [w - (Nat.card F - 1), Nat.card F - 1] := by
  intro s hs
  have hsne : s ≠ [] := by
    intro hnil
    have h1 : tmWeight (K := Ambient F) s = w := D.weight s hs
    rw [hnil, tmWeight_nil] at h1
    omega
  have hℓne : s.map Prod.fst ≠ [] := fun h => hsne (List.map_eq_nil_iff.mp h)
  have hpos : ∀ x ∈ s.map Prod.fst, 1 ≤ x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact D.pos s hs y hy
  have hnd : ∀ x ∈ s.map Prod.fst, ¬ Nat.card F ∣ x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact D.nd s hs y hy
  have hsum : (s.map Prod.fst).sum = w := D.weight s hs
  have hdiv' : ∀ k : ℕ, 1 ≤ k → k ≤ (s.map Prod.fst).length →
      (Nat.card F - 1) ∣ ((s.map Prod.fst).drop k).sum := by
    intro k h1 h2
    have h2' : k ≤ s.length := by simpa using h2
    have h3 := hdiv s hs k h1 h2'
    have h4 : ((s.map Prod.fst).drop k).sum = tmWeight (K := Ambient F) (s.drop k) := by
      rw [← List.map_drop]
      rfl
    rw [h4]
    exact h3
  rcases Commons.Combinatorics.TupleCount.tail_shape (q := Nat.card F) (w := w) hq hw2 hℓne hpos
    hnd hsum hdiv' with ⟨-, h⟩ | h
  · exact Or.inl h
  · exact Or.inr h

end General

end ZagierHoffmanPositiveChar
