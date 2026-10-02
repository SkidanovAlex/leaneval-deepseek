import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.EmbedAux
import Submission.Work.Deep.Nibble.EmbedDes
import Submission.Work.Deep.Nibble.EmbedStar

/-!
# The vertex count of `𝓖` (condition (E3))
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

variable {N r : ℕ} {𝓗 : MultiHypergraph N}

/-- **Double counting.**  `2 · #E(𝓗) ≤ ∑_v d^E_𝓗(v)`. -/
theorem two_mul_ncard_le_sum_hdeg (h2 : ∀ e ∈ 𝓗.edges, 2 ≤ edgeSize e) :
    2 * 𝓗.edges.ncard ≤ ∑ v : Fin N, MultiHypergraph.hdeg 𝓗.edges v := by
  classical
  haveI : Fintype ↥𝓗.edges := Fintype.ofFinite _
  have hcard : (Fintype.card ↥𝓗.edges : ℕ) = 𝓗.edges.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hsum : (∑ e : ↥𝓗.edges, edgeSize (e : Set (Fin N)))
      = ∑ v : Fin N, MultiHypergraph.hdeg 𝓗.edges v := by
    rw [Work.Deep.Kahn.sum_edgeSize_eq_sum_degree]
    exact Finset.sum_congr rfl fun v _ => (hypergraphDegree_eq_ncard 𝓗.edges v).trans rfl
  have h2' : (∑ _ : ↥𝓗.edges, (2:ℕ)) ≤ ∑ e : ↥𝓗.edges, edgeSize (e : Set (Fin N)) :=
    Finset.sum_le_sum fun e _ => h2 (e : Set (Fin N)) e.2
  have hc : (∑ _ : ↥𝓗.edges, (2:ℕ)) = 2 * 𝓗.edges.ncard := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, hcard, Nat.mul_comm]
  calc 2 * 𝓗.edges.ncard = ∑ _ : ↥𝓗.edges, (2:ℕ) := hc.symm
    _ ≤ ∑ e : ↥𝓗.edges, edgeSize (e : Set (Fin N)) := h2'
    _ = ∑ v : Fin N, MultiHypergraph.hdeg 𝓗.edges v := hsum

/-- `⌈D - C⌉₊ ≤ D` when `C ≥ 1` and `D > 0`. -/
theorem natCeil_sub_le {C D : ℝ} (hC : 1 ≤ C) (hD : 0 < D) : (⌈D - C⌉₊ : ℝ) ≤ D := by
  have h1 : D - C < (⌊D⌋₊ : ℝ) := by
    have := Nat.sub_one_lt_floor D
    linarith
  have h2 : ⌈D - C⌉₊ ≤ ⌊D⌋₊ := Nat.ceil_le.mpr (le_of_lt h1)
  calc (⌈D - C⌉₊ : ℝ) ≤ (⌊D⌋₊ : ℝ) := by exact_mod_cast h2
    _ ≤ D := Nat.floor_le (le_of_lt hD)

/-- The degree sum is at most `N · D`. -/
theorem sum_deg_le {D : ℝ} (hdegD : ∀ v : Fin N, (𝓗.deg v : ℝ) ≤ D) :
    (∑ v : Fin N, (𝓗.deg v : ℝ)) ≤ (N : ℝ) * D := by
  calc (∑ v : Fin N, (𝓗.deg v : ℝ)) ≤ ∑ _v : Fin N, D :=
        Finset.sum_le_sum fun v _ => hdegD v
    _ = (N : ℝ) * D := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The vertex count of `𝓗*`**: `|V(𝓗*)| ≤ N (1 + (r-1) D)`. -/
theorem card_Vstar_le (U : UnifData N r 𝓗) (hr : 2 ≤ r)
    (hlin : 𝓗.IsLinear) {D : ℝ} (hdegD : ∀ v : Fin N, (𝓗.deg v : ℝ) ≤ D) :
    (Nat.card (Vstar 𝓗 r U.M) : ℝ) ≤ (N : ℝ) * (1 + ((r : ℝ) - 1) * D) := by
  classical
  set E : ℝ := (𝓗.edges.ncard : ℝ) with hE
  set A : ℝ := ∑ v : Fin N, (MultiHypergraph.hdeg 𝓗.edges v : ℝ) with hAdef
  set S : ℝ := ∑ v : Fin N, (𝓗.singles v : ℝ) with hSdef
  have hkeys : (Nat.card (SC 𝓗) : ℝ) = S := by rw [SC.card, Nat.cast_sum, hSdef]
  have hdegsum : A + S ≤ (N : ℝ) * D := by
    have h1 : A + S = ∑ v : Fin N, (𝓗.deg v : ℝ) := by
      rw [hAdef, hSdef, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => by
        rw [MultiHypergraph.deg_def]; push_cast; ring
    rw [h1]; exact sum_deg_le hdegD
  have hA : 2 * E ≤ A := by
    rw [hE, hAdef]
    exact_mod_cast two_mul_ncard_le_sum_hdeg (𝓗 := 𝓗) hlin.1
  have hA' : E ≤ A / 2 := by linarith
  have hAh : 0 ≤ A := by rw [hAdef]; exact Finset.sum_nonneg fun v _ => Nat.cast_nonneg _
  have hS0 : 0 ≤ S := by rw [hSdef]; exact Finset.sum_nonneg fun v _ => Nat.cast_nonneg _
  have hrm1 : 0 ≤ (r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
    linarith
  have hV : (Nat.card (Vstar 𝓗 r U.M) : ℝ) = (U.M : ℝ) + S * ((r : ℝ) - 1) := by
    rw [Vstar.card, Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one,
      hkeys]
  rw [hV]
  have hbound : (U.M : ℝ) ≤ (N : ℝ) + (r : ℝ) * E := by rw [hE]; exact U.bound
  have hrm2 : (r : ℝ) / 2 ≤ (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have key : E * (r : ℝ) + S * ((r : ℝ) - 1) ≤ (N : ℝ) * D * ((r : ℝ) - 1) := by
    have h1 : (r : ℝ) * E ≤ ((r : ℝ) - 1) * A := by
      calc (r : ℝ) * E ≤ (r : ℝ) * (A / 2) := mul_le_mul_of_nonneg_left hA' (by linarith)
        _ = (r : ℝ) / 2 * A := by ring
        _ ≤ ((r : ℝ) - 1) * A := mul_le_mul_of_nonneg_right hrm2 hAh
    have h2 : ((r : ℝ) - 1) * (A + S) ≤ ((r : ℝ) - 1) * ((N : ℝ) * D) :=
      mul_le_mul_of_nonneg_left hdegsum hrm1
    nlinarith [h1, h2, hAh, hS0]
  calc (U.M : ℝ) + S * ((r : ℝ) - 1)
      ≤ ((N : ℝ) + (r : ℝ) * E) + S * ((r : ℝ) - 1) := by linarith
    _ ≤ (N : ℝ) + (N : ℝ) * D * ((r : ℝ) - 1) := by linarith
    _ = (N : ℝ) * (1 + ((r : ℝ) - 1) * D) := by ring


/-- `dprime D C U u ≤ ⌈D - C⌉₊` for every `u`. -/
theorem dprime_le_ceil (D C : ℝ) (U : UnifData N r 𝓗) (u : Vstar 𝓗 r U.M) :
    dprime D C U u ≤ ⌈D - C⌉₊ := by
  rw [dprime, mdeg, Nat.sub_le_iff_le_add]
  exact max_le (by omega) (by omega)

/-- If some design is needed then `C < D`. -/
theorem lt_of_dmax_ne_zero (U : UnifData N r 𝓗) {C D : ℝ} (hd : dmax D C U ≠ 0) : C < D := by
  obtain ⟨u, hu⟩ : ∃ u, dprime D C U u ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hd ((dmax_eq_zero_iff D C U).mpr hcon)
  have h1 : 1 ≤ dprime D C U u := by omega
  have h2 : 1 ≤ ⌈D - C⌉₊ := le_trans h1 (dprime_le_ceil D C U u)
  by_contra hcon
  push_neg at hcon
  have h3 : ⌈D - C⌉₊ ≤ 0 := Nat.ceil_le.mpr (show D - C ≤ ((0 : ℕ) : ℝ) from by linarith)
  omega

/-- **Condition (E3)**: `|V(𝓖)| = T · |V(𝓗*)| ≤ r (r-1)² D³ N`. -/
theorem card_G_le (U : UnifData N r 𝓗) (hr : 3 ≤ r) (hlin : 𝓗.IsLinear)
    {C D : ℝ} (hrC : (r : ℝ) ≤ C) (hD1 : 1 ≤ D)
    (hdegD : ∀ v : Fin N, (𝓗.deg v : ℝ) ≤ D) :
    ((T hr D C U : ℕ) : ℝ) * (Nat.card (Vstar 𝓗 r U.M) : ℝ)
      ≤ (r : ℝ) * ((r : ℝ) - 1) ^ 2 * D ^ 3 * (N : ℝ) := by
  classical
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
  have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr2 : 2 ≤ r := by omega
  have hC1 : 1 ≤ C := le_trans (by linarith : (1 : ℝ) ≤ (r : ℝ)) hrC
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hV := card_Vstar_le U hr2 hlin hdegD
  have hD2 : (1 : ℝ) ≤ D ^ 2 := by nlinarith [sq_nonneg (D - 1), hD1]
  have hrm2 : (1 : ℝ) ≤ ((r : ℝ) - 1) ^ 2 := by nlinarith [sq_nonneg ((r : ℝ) - 1), hr3]
  have hsq : (1 : ℝ) ≤ ((r : ℝ) - 1) ^ 2 * D ^ 2 := by nlinarith [hD2, hrm2]
  have h1rD : 1 + ((r : ℝ) - 1) * D ≤ (r : ℝ) * D := by nlinarith
  have hstep : (r : ℝ) * D ≤ ((r : ℝ) - 1) ^ 2 * D ^ 3 * (r : ℝ) := by
    have h1 : D ≤ ((r : ℝ) - 1) ^ 2 * D ^ 3 := by nlinarith [hsq, hD1]
    nlinarith [h1, hr1]
  have hV' : (Nat.card (Vstar 𝓗 r U.M) : ℝ) ≤ (N : ℝ) * ((r : ℝ) * D) :=
    le_trans hV (mul_le_mul_of_nonneg_left h1rD hN)
  have hdmaxD : (dmax D C U : ℝ) ≤ D := by
    have h2 : (dmax D C U : ℝ) ≤ (⌈D - C⌉₊ : ℝ) := by
      exact_mod_cast Finset.sup_le fun u _ => dprime_le_ceil D C U u
    exact le_trans h2 (natCeil_sub_le hC1 (by linarith))
  by_cases hd : dmax D C U = 0
  · rw [T, if_pos hd, Nat.cast_one, one_mul]
    calc (Nat.card (Vstar 𝓗 r U.M) : ℝ) ≤ (N : ℝ) * ((r : ℝ) * D) := hV'
      _ ≤ (N : ℝ) * (((r : ℝ) - 1) ^ 2 * D ^ 3 * (r : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep hN
      _ = (r : ℝ) * ((r : ℝ) - 1) ^ 2 * D ^ 3 * (N : ℝ) := by ring
  · have hCD : C < D := lt_of_dmax_ne_zero U hd
    have hrD : (r : ℝ) < D := lt_of_le_of_lt hrC hCD
    have hTmax : ((max r (dmax D C U) : ℕ) : ℝ) ≤ D := by
      rw [Nat.cast_max]
      exact max_le (le_of_lt hrD) hdmaxD
    have hT : ((T hr D C U : ℕ) : ℝ) ≤ 2 * (r : ℝ) * D := by
      rw [T_eq_of_ne hr D C U hd, Nat.cast_mul]
      have hp : (designPrime hr D C U : ℝ) ≤ 2 * ((max r (dmax D C U) : ℕ) : ℝ) := by
        exact_mod_cast designPrime_le hr D C U
      nlinarith [hp, hTmax, hr1]
    calc ((T hr D C U : ℕ) : ℝ) * (Nat.card (Vstar 𝓗 r U.M) : ℝ)
        ≤ (2 * (r : ℝ) * D) * ((N : ℝ) * ((r : ℝ) * D)) :=
          mul_le_mul hT hV' (Nat.cast_nonneg _) (by positivity)
      _ = 2 * (r : ℝ) ^ 2 * D ^ 2 * (N : ℝ) := by ring
      _ ≤ (r : ℝ) * ((r : ℝ) - 1) ^ 2 * D ^ 3 * (N : ℝ) := by
          have h4 : (4 : ℝ) ≤ ((r : ℝ) - 1) ^ 2 := by nlinarith [hr3]
          have hquad : 2 * (r : ℝ) ≤ ((r : ℝ) - 1) ^ 2 * D := by
            have h5 : (4 : ℝ) * (r : ℝ) ≤ ((r : ℝ) - 1) ^ 2 * (r : ℝ) :=
              mul_le_mul_of_nonneg_right h4 (by linarith)
            have h6 : ((r : ℝ) - 1) ^ 2 * (r : ℝ) ≤ ((r : ℝ) - 1) ^ 2 * D :=
              mul_le_mul_of_nonneg_left (le_of_lt hrD) (by linarith)
            linarith
          have h7 : 2 * (r : ℝ) * ((r : ℝ) * D ^ 2 * (N : ℝ))
              ≤ ((r : ℝ) - 1) ^ 2 * D * ((r : ℝ) * D ^ 2 * (N : ℝ)) :=
            mul_le_mul_of_nonneg_right hquad (by positivity)
          linarith [h7]


end

end Work.Deep.Nibble
