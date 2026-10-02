import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.KahnPartition
import Submission.Work.Deep.Nibble.partDegCount
import Submission.Work.Deep.Nibble.partBalCount
import Submission.Work.Deep.Nibble.sum_classVert_ncard_eq
import Submission.Work.Deep.Nibble.pi_uniform_exp_sum
import Submission.Work.Deep.Nibble.prod_uniform_lower_tail
import Submission.Work.Deep.Nibble.relcoverMargins

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Deep.Nibble

open scoped BigOperators

/-! ## Elementary arithmetic helpers -/

/-- `log y < X` gives `exp (-X) < 1/y` for `y > 0`. -/
lemma exp_neg_lt_inv {y X : ℝ} (hy : 0 < y) (h : Real.log y < X) : Real.exp (-X) < 1 / y := by
  have h1 : Real.exp (-X) < Real.exp (-(Real.log y)) := Real.exp_lt_exp.mpr (by linarith)
  have h2 : Real.exp (-(Real.log y)) = 1 / y := by
    rw [Real.exp_neg, Real.exp_log hy, one_div]
  rwa [h2] at h1

/-- The Chernoff exponent comparison of the partition step. -/
lemma chernoff_exp_le {A μ ε' : ℝ} (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1) (hμ0 : 0 < μ)
    (hAμ : A ≤ μ) :
    3 * ε' ^ 2 * A / 8 ≤ (ε' * μ) ^ 2 / (2 * (1 * μ + ε' * μ / 3)) := by
  have hden : 0 < 2 * (1 * μ + ε' * μ / 3) := by nlinarith
  have hstep : 3 * ε' ^ 2 * A / 8 ≤ 3 * ε' ^ 2 * μ / 8 := by nlinarith
  refine hstep.trans ?_
  rw [le_div_iff₀ hden]
  have hmono : 2 * (1 * μ + ε' * μ / 3) ≤ 2 * (1 * μ + 1 * μ / 3) := by nlinarith
  have hfac : (0:ℝ) ≤ 3 * ε' ^ 2 * μ / 8 := by positivity
  have hkey : 3 * ε' ^ 2 * μ / 8 * (2 * (1 * μ + 1 * μ / 3)) = (ε' * μ) ^ 2 := by ring
  have := mul_le_mul_of_nonneg_left hmono hfac
  rw [hkey] at this
  exact this

/-- The balance exponent comparison of the partition step. -/
lemma bal_exp_le {c t : ℝ} (hc0 : 0 < c) (hct : c ≤ t) :
    3 * c / 8 ≤ t ^ 2 / (2 * (c + t / 3)) := by
  have hden : 0 < 2 * (c + t / 3) := by linarith
  rw [le_div_iff₀ hden]
  nlinarith [mul_nonneg (le_of_lt hc0) (by linarith : (0:ℝ) ≤ t - c), sq_nonneg (t - c)]

/-! ## The induced maximum degree of a part -/

/-- The maximum induced degree of a part is at most `(1+ε')(1+κ)D/p^{r-1}`. -/
lemma partMaxDegree_le {n p r : ℕ} {𝓗 : HG n} {π : Fin n → Fin p} {κ ε' D : ℝ}
    {𝓕 : Set (Set (Fin n))} (hπ : GoodPartition 𝓗 r ε' D 𝓕 π)
    (hdeg : ∀ v : Fin n, |((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ) - D| ≤ κ * D)
    (hκ0 : 0 < κ) (hε'0 : 0 < ε') (hD0 : 0 < D) :
    ∀ i : Fin p, ((ErdosFaberLovaszConjecture.hypergraphMaxDegree (partHyp 𝓗 π i) : ℕ) : ℝ)
        ≤ (1 + ε') * (1 + κ) * (D / (p : ℝ) ^ (r - 1)) := by
  intro i
  have hc'0 : (0:ℝ) ≤ (1 + ε') * (1 + κ) * (D / (p : ℝ) ^ (r - 1)) := by positivity
  have hv : ∀ v : Fin n, ((ErdosFaberLovaszConjecture.hypergraphDegree (partHyp 𝓗 π i) v : ℕ) : ℝ)
      ≤ (1 + ε') * (1 + κ) * (D / (p : ℝ) ^ (r - 1)) := by
    intro v
    by_cases hmem : v ∈ partSet π i
    · have h1 := hπ.1 i v hmem
      rw [abs_le] at h1
      have h2 := hdeg v
      rw [abs_le] at h2
      have h3 : ((ErdosFaberLovaszConjecture.hypergraphDegree (partHyp 𝓗 π i) v : ℕ) : ℝ)
          ≤ (1 + ε') * (((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ)
              / (p : ℝ) ^ (r - 1)) := by
        rw [degInPart] at h1
        linarith [h1.2]
      have h4 : ((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ) ≤ (1 + κ) * D := by
        linarith [h2.2]
      calc ((ErdosFaberLovaszConjecture.hypergraphDegree (partHyp 𝓗 π i) v : ℕ) : ℝ)
          ≤ (1 + ε') * (((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ)
              / (p : ℝ) ^ (r - 1)) := h3
        _ ≤ (1 + ε') * ((1 + κ) * D / (p : ℝ) ^ (r - 1)) := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            exact div_le_div_of_nonneg_right h4 (by positivity)
        _ = (1 + ε') * (1 + κ) * (D / (p : ℝ) ^ (r - 1)) := by ring
    · have h0 : ErdosFaberLovaszConjecture.hypergraphDegree (partHyp 𝓗 π i) v = 0 := by
        haveI : IsEmpty {e : partHyp 𝓗 π i // v ∈ (e : Set (Fin n))} :=
          ⟨fun e => hmem (e.1.2.2 e.2)⟩
        simp [ErdosFaberLovaszConjecture.hypergraphDegree]
      rw [h0]
      simpa using hc'0
  have hsup : ((Finset.univ : Finset (Fin n)).sup
      (fun v => ErdosFaberLovaszConjecture.hypergraphDegree (partHyp 𝓗 π i) v)) ≤ ⌊(1 + ε') * (1 + κ) * (D / (p : ℝ) ^ (r - 1))⌋₊ :=
    Finset.sup_le (fun v _ => Nat.le_floor (hv v))
  calc ((ErdosFaberLovaszConjecture.hypergraphMaxDegree (partHyp 𝓗 π i) : ℕ) : ℝ)
      = (((Finset.univ : Finset (Fin n)).sup
          (fun v => ErdosFaberLovaszConjecture.hypergraphDegree (partHyp 𝓗 π i) v) : ℕ) : ℝ) := rfl
    _ ≤ ((⌊(1 + ε') * (1 + κ) * (D / (p : ℝ) ^ (r - 1))⌋₊ : ℕ) : ℝ) := by exact_mod_cast hsup
    _ ≤ (1 + ε') * (1 + κ) * (D / (p : ℝ) ^ (r - 1)) := Nat.floor_le hc'0

/-! ## The two counting estimates of the partition step -/

/-- The number of partitions `π` with `π v = i` for which the induced degree of `v` in
part `i` deviates from its mean `d_𝓗(v)/p^{r-1}` is at most `p^{n-1}/(2np)`. -/
lemma badDegCard_le {n p r : ℕ} {𝓗 : HG n} {κ ε' D : ℝ} (v : Fin n) (i : Fin p)
    (hr : 2 ≤ r) (hp : 2 ≤ p) (hn1 : 1 ≤ n)
    (hlin : ErdosFaberLovaszConjecture.Hypergraph.IsLinear 𝓗)
    (hrs : ∀ e ∈ 𝓗, v ∈ e → e.ncard = r)
    (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1) (hκ1 : κ < 1) (hD0 : 0 < D)
    (hdegv : |((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ) - D| ≤ κ * D)
    (hcher : Real.log (4 * (n : ℝ) * (p : ℝ))
      < 3 * ε' ^ 2 * ((1 - κ) * D / (p : ℝ) ^ (r - 1)) / 8) :
    ((Finset.univ.filter (fun π : Fin n → Fin p =>
        π v = i ∧ ε' * (((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ)
              / (p : ℝ) ^ (r - 1))
          ≤ |((degInPart 𝓗 π v i : ℕ) : ℝ)
              - ((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ)
                  / (p : ℝ) ^ (r - 1)|)).card : ℝ)
      ≤ (p : ℝ) ^ (n - 1) * (1 / (2 * (n : ℝ) * (p : ℝ))) := by
  have hpow : (0:ℝ) < (p : ℝ) ^ (r - 1) := by positivity
  have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hd0 : (0:ℝ) < ((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ) := by
    have h := hdegv
    rw [abs_le] at h
    have hDp : (0:ℝ) < (1 - κ) * D := by
      have : (0:ℝ) < 1 - κ := by linarith
      positivity
    linarith [h.1]
  have hτ : (0:ℝ) ≤ ε' * (((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ)
      / (p : ℝ) ^ (r - 1)) := by
    apply mul_nonneg (le_of_lt hε'0)
    positivity
  have hpc := partDegCount (𝓗 := 𝓗) v hr hp hlin hrs i (τ := ε' *
    (((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ) / (p : ℝ) ^ (r - 1))) hτ
  refine hpc.trans ?_
  set m : ℝ := ((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ) / (p : ℝ) ^ (r - 1)
    with hm
  have hmpos : 0 < m := by rw [hm]; positivity
  have hμlb : (1 - κ) * D / (p : ℝ) ^ (r - 1) ≤ m := by
    rw [hm]
    have h := hdegv
    rw [abs_le] at h
    have hd : (1 - κ) * D ≤ ((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ) := by
      linarith [h.1]
    exact div_le_div_of_nonneg_right hd (le_of_lt hpow)
  have hcmp := chernoff_exp_le (A := (1 - κ) * D / (p : ℝ) ^ (r - 1)) (μ := m) (ε' := ε')
    hε'0 hε'1 hmpos hμlb
  have hlt : Real.log (4 * (n : ℝ) * (p : ℝ))
      < (ε' * m) ^ 2 / (2 * (1 * m + ε' * m / 3)) := lt_of_lt_of_le hcher hcmp
  have hpos4 : (0:ℝ) < 4 * (n : ℝ) * (p : ℝ) := by positivity
  have hexp : Real.exp (-(ε' * m) ^ 2 / (2 * (1 * m + ε' * m / 3)))
      < 1 / (4 * (n : ℝ) * (p : ℝ)) := by
    simpa only [neg_div] using
      exp_neg_lt_inv (X := (ε' * m) ^ 2 / (2 * (1 * m + ε' * m / 3))) hpos4 hlt
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h2 : 2 * Real.exp (-(ε' * m) ^ 2 / (2 * (1 * m + ε' * m / 3)))
      < 2 * (1 / (4 * (n : ℝ) * (p : ℝ))) := mul_lt_mul_of_pos_left hexp (by norm_num)
  have hid : 2 * (1 / (4 * (n : ℝ) * (p : ℝ))) = 1 / (2 * (n : ℝ) * (p : ℝ)) := by
    field_simp
    ring
  linarith [h2, hid]

/-- The number of partitions `π` for which `S` meets part `i` in at least `⌈2|S|/p⌉`
vertices is at most `p^n/(2Np)`, where `N` is a lower bound for the number of prescribed
sets of the family. -/
lemma badBalCard_le {n p : ℕ} {D N : ℝ} (hp : 2 ≤ p) (S : Set (Fin n)) (i : Fin p)
    (hm : 0 < (S.ncard : ℝ)) (hN : 0 < N) (hD0 : 0 < D) (hD1 : 1 ≤ D)
    (hbal : (8 / 3) * Real.log (4 * N * (p : ℝ)) < (S.ncard : ℝ) / (p : ℝ)) :
    ((Finset.univ.filter (fun π : Fin n → Fin p =>
        ⌈2 * (S.ncard : ℝ) / (p : ℝ)⌉₊ ≤ (S ∩ partSet π i).ncard)).card : ℝ)
      ≤ (p : ℝ) ^ n * (1 / (2 * N * (p : ℝ))) := by
  have hppos : (0:ℝ) < (p : ℝ) := by positivity
  have hnn : (0:ℝ) ≤ (S.ncard : ℝ) := Nat.cast_nonneg _
  have hk : (S.ncard : ℝ) / (p : ℝ) ≤ ((⌈2 * (S.ncard : ℝ) / (p : ℝ)⌉₊ : ℕ) : ℝ) := by
    have h2 : (S.ncard : ℝ) / (p : ℝ) ≤ 2 * (S.ncard : ℝ) / (p : ℝ) := by
      rw [mul_div_assoc]
      have h3 := div_nonneg hnn (le_of_lt hppos)
      linarith
    exact h2.trans (Nat.le_ceil _)
  have hpc := partBalCount hp S i hk
  refine hpc.trans ?_
  set m : ℝ := (S.ncard : ℝ) with hmS
  set k : ℝ := ((⌈2 * (S.ncard : ℝ) / (p : ℝ)⌉₊ : ℕ) : ℝ) with hkS
  have hmpos : 0 < m := by rw [hmS]; exact hm
  have h2m : 2 * (m / (p : ℝ)) ≤ k := by
    have h0 : 2 * (m / (p : ℝ)) = 2 * m / (p : ℝ) := by ring
    rw [h0, hmS, hkS]
    exact Nat.le_ceil (2 * (S.ncard : ℝ) / (p : ℝ))
  have hτ : m / (p : ℝ) ≤ k - m / (p : ℝ) := by linarith [h2m]
  have hcmp := bal_exp_le (c := m / (p : ℝ)) (t := k - m / (p : ℝ))
    (by positivity) hτ
  have hlt : Real.log (4 * N * (p : ℝ))
      < (k - m / (p : ℝ)) ^ 2 / (2 * (m / (p : ℝ) + (k - m / (p : ℝ)) / 3)) := by
    have h3 : Real.log (4 * N * (p : ℝ)) < 3 / 8 * (m / (p : ℝ)) := by
      have h4 := hbal
      rw [hmS] at h4
      nlinarith
    have h5 : 3 * (m / (p : ℝ)) / 8 = 3 / 8 * (m / (p : ℝ)) := by ring
    linarith [h3, hcmp, h5.le, h5.ge]
  have hpos4 : (0:ℝ) < 4 * N * (p : ℝ) := by positivity
  have hexp : Real.exp (-(k - m / (p : ℝ)) ^ 2 / (2 * (m / (p : ℝ) + (k - m / (p : ℝ)) / 3)))
      < 1 / (4 * N * (p : ℝ)) := by
    simpa only [neg_div] using
      exp_neg_lt_inv (X := (k - m / (p : ℝ)) ^ 2 / (2 * (m / (p : ℝ) + (k - m / (p : ℝ)) / 3)))
        hpos4 hlt
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h2 : 2 * Real.exp (-(k - m / (p : ℝ)) ^ 2 / (2 * (m / (p : ℝ) + (k - m / (p : ℝ)) / 3)))
      < 2 * (1 / (4 * N * (p : ℝ))) := mul_lt_mul_of_pos_left hexp (by norm_num)
  have hid : 2 * (1 / (4 * N * (p : ℝ))) = 1 / (2 * N * (p : ℝ)) := by
    field_simp
    ring
  linarith [h2, hid]

/-! ## Existence of a good random partition (the probabilistic method) -/

theorem exists_goodPartition {n : ℕ} {𝓗 : HG n} {r p : ℕ} (hr : 2 ≤ r) (hp : 2 ≤ p)
    {κ ε' D : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1)
    (hD0 : 0 < D) (hD1 : 1 ≤ D) (hn1 : 1 ≤ n)
    (hlin : ErdosFaberLovaszConjecture.Hypergraph.IsLinear 𝓗)
    (hrsize : ∀ e ∈ 𝓗, e.ncard = r)
    (hdeg : ∀ v : Fin n, |((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ) - D| ≤ κ * D)
    {𝓕 : Set (Set (Fin n))}
    (hcher : Real.log (4 * (n : ℝ) * (p : ℝ))
      < 3 * ε' ^ 2 * ((1 - κ) * D / (p : ℝ) ^ (r - 1)) / 8)
    (hbal : ∀ S ∈ 𝓕, D ^ ((1 : ℝ) / 20) ≤ (S.ncard : ℝ) →
      (8 / 3) * Real.log (4 * (𝓕.ncard : ℝ) * (p : ℝ)) < (S.ncard : ℝ) / (p : ℝ)) :
    ∃ π : Fin n → Fin p, GoodPartition 𝓗 r ε' D 𝓕 π := by
  classical
  have hppos : (0:ℝ) < (p:ℝ) := by positivity
  have hpgt1 : (1:ℝ) < (p:ℝ) := by
    have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    linarith
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  -- (1) the bad-degree partitions
  set BadD : Fin n × Fin p → Finset (Fin n → Fin p) := fun q => Finset.univ.filter (fun π =>
      π q.1 = q.2 ∧ ε' * (((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 q.1 : ℕ) : ℝ)
            / (p : ℝ) ^ (r - 1))
        ≤ |((degInPart 𝓗 π q.1 q.2 : ℕ) : ℝ)
            - ((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 q.1 : ℕ) : ℝ)
                / (p : ℝ) ^ (r - 1)|) with hBadD
  have hbnD : ∀ q : Fin n × Fin p, ((BadD q).card : ℝ)
      ≤ (p : ℝ) ^ (n - 1) * (1 / (2 * (n : ℝ) * (p : ℝ))) := by
    rintro ⟨v, i⟩
    have h := badDegCard_le (𝓗 := 𝓗) v i hr hp hn1 hlin (fun e he _ => hrsize e he)
      hε'0 hε'1 hκ1 hD0 (hdeg v) hcher
    simpa only [hBadD] using h
  have hsumD : (∑ q : Fin n × Fin p, ((BadD q).card : ℝ)) ≤ (p : ℝ) ^ (n - 1) / 2 := by
    calc ∑ q : Fin n × Fin p, ((BadD q).card : ℝ)
        ≤ ∑ _q : Fin n × Fin p, ((p : ℝ) ^ (n - 1) * (1 / (2 * (n : ℝ) * (p : ℝ)))) :=
          Finset.sum_le_sum (fun q _ => hbnD q)
      _ = (p : ℝ) ^ (n - 1) / 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast
          field_simp
  have hcardD : (((Finset.univ : Finset (Fin n × Fin p)).biUnion BadD).card : ℝ)
      ≤ ∑ q : Fin n × Fin p, ((BadD q).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin n × Fin p)))
      (t := BadD))
  -- (2) the balance-bad partitions
  set U : Finset (Set (Fin n)) := Finset.univ.filter (fun S : Set (Fin n) =>
      S ∈ 𝓕 ∧ D ^ ((1:ℝ)/20) ≤ (S.ncard : ℝ)) with hU
  have hUmem : ∀ S, S ∈ U → S ∈ 𝓕 ∧ D ^ ((1:ℝ)/20) ≤ (S.ncard : ℝ) := by
    intro S hS
    rw [hU, Finset.mem_filter] at hS
    exact hS.2
  have hUcard : U.card ≤ 𝓕.ncard := by
    have h1 : (U : Set (Set (Fin n))) ⊆ 𝓕 := by
      intro S hS
      exact (hUmem S (by simpa using hS)).1
    have h2 := Set.ncard_mono h1
    rwa [show ((U : Set (Set (Fin n)))).ncard = U.card by simp] at h2
  set BadB : Set (Fin n) → Fin p → Finset (Fin n → Fin p) := fun S i => Finset.univ.filter (fun π =>
      ⌈2 * (S.ncard : ℝ) / (p : ℝ)⌉₊ ≤ (S ∩ partSet π i).ncard) with hBadB
  have hbnB : ∀ S ∈ U, ∀ i : Fin p, ((BadB S i).card : ℝ)
      ≤ (p:ℝ)^n * (1/(2 * (𝓕.ncard:ℝ) * (p:ℝ))) := by
    intro S hS i
    obtain ⟨hS𝓕, hSsz⟩ := hUmem S hS
    have hNpos : 0 < (𝓕.ncard : ℝ) := by
      have h0 : 0 < 𝓕.ncard := (Set.ncard_pos (Set.toFinite 𝓕)).mpr ⟨S, hS𝓕⟩
      exact_mod_cast h0
    have hmpos : 0 < (S.ncard : ℝ) := by
      have h1 : (1:ℝ) ≤ D ^ ((1:ℝ)/20) := Real.one_le_rpow hD1 (by norm_num)
      linarith [hSsz, h1]
    have h := badBalCard_le (N := (𝓕.ncard : ℝ)) hp S i hmpos hNpos hD0 hD1 (hbal S hS𝓕 hSsz)
    simpa only [hBadB] using h
  have hcardB : ((U.biUnion fun S => (Finset.univ : Finset (Fin p)).biUnion (fun i => BadB S i)).card : ℝ)
      ≤ (p:ℝ)^n / 2 := by
    have hstep : ∀ S ∈ U, (((Finset.univ : Finset (Fin p)).biUnion (fun i => BadB S i)).card : ℝ)
        ≤ (p:ℝ) * ((p:ℝ)^n * (1/(2 * (𝓕.ncard:ℝ) * (p:ℝ)))) := by
      intro S hS
      have h1 : (((Finset.univ : Finset (Fin p)).biUnion (fun i => BadB S i)).card : ℝ)
          ≤ ∑ i : Fin p, ((BadB S i).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin p)))
          (t := fun i => BadB S i))
      refine h1.trans ?_
      calc ∑ i : Fin p, ((BadB S i).card : ℝ)
          ≤ ∑ _i : Fin p, ((p:ℝ)^n * (1/(2 * (𝓕.ncard:ℝ) * (p:ℝ)))) :=
            Finset.sum_le_sum (fun i _ => hbnB S hS i)
        _ = (p:ℝ) * ((p:ℝ)^n * (1/(2 * (𝓕.ncard:ℝ) * (p:ℝ)))) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hstep2 : ((U.biUnion fun S => (Finset.univ : Finset (Fin p)).biUnion (fun i => BadB S i)).card : ℝ)
        ≤ ∑ S ∈ U, (((Finset.univ : Finset (Fin p)).biUnion (fun i => BadB S i)).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := U)
        (t := fun S => (Finset.univ : Finset (Fin p)).biUnion (fun i => BadB S i)))
    by_cases hU0 : U = ∅
    · rw [hU0]
      simp only [Finset.biUnion_empty, Finset.card_empty, Nat.cast_zero]
      positivity
    · obtain ⟨S0, hS0⟩ := Finset.nonempty_iff_ne_empty.mpr hU0
      have hNpos : 0 < (𝓕.ncard : ℝ) := by
        have h0 : 0 < 𝓕.ncard := (Set.ncard_pos (Set.toFinite 𝓕)).mpr ⟨S0, (hUmem S0 hS0).1⟩
        exact_mod_cast h0
      have hfin : (∑ S ∈ U, (((Finset.univ : Finset (Fin p)).biUnion (fun i => BadB S i)).card : ℝ))
          ≤ (𝓕.ncard : ℝ) * ((p:ℝ) * ((p:ℝ)^n * (1/(2 * (𝓕.ncard:ℝ) * (p:ℝ))))) := by
        calc (∑ S ∈ U, (((Finset.univ : Finset (Fin p)).biUnion (fun i => BadB S i)).card : ℝ))
            ≤ ∑ _S ∈ U, ((p:ℝ) * ((p:ℝ)^n * (1/(2 * (𝓕.ncard:ℝ) * (p:ℝ))))) :=
              Finset.sum_le_sum (fun S hS => hstep S hS)
          _ = (U.card : ℝ) * ((p:ℝ) * ((p:ℝ)^n * (1/(2 * (𝓕.ncard:ℝ) * (p:ℝ))))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (𝓕.ncard : ℝ) * ((p:ℝ) * ((p:ℝ)^n * (1/(2 * (𝓕.ncard:ℝ) * (p:ℝ))))) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact_mod_cast hUcard
      have hval : (𝓕.ncard : ℝ) * ((p:ℝ) * ((p:ℝ)^n * (1/(2 * (𝓕.ncard:ℝ) * (p:ℝ)))))
          = (p:ℝ)^n / 2 := by
        field_simp
      linarith [hstep2, hfin, hval.le, hval.ge]
  -- (3) the union of the bad sets is not everything
  set BadT : Finset (Fin n → Fin p) :=
    (Finset.univ : Finset (Fin n × Fin p)).biUnion BadD ∪
      (U.biUnion fun S => (Finset.univ : Finset (Fin p)).biUnion (fun i => BadB S i)) with hBadT
  have hcardT : (BadT.card : ℝ) < (p:ℝ)^n := by
    have h1 : (BadT.card : ℝ)
        ≤ (((Finset.univ : Finset (Fin n × Fin p)).biUnion BadD).card : ℝ)
          + ((U.biUnion fun S => (Finset.univ : Finset (Fin p)).biUnion (fun i => BadB S i)).card : ℝ) := by
      rw [hBadT]
      exact_mod_cast Finset.card_union_le _ _
    have h4 : (p:ℝ)^(n-1)/2 + (p:ℝ)^n/2 < (p:ℝ)^n := by
      have h5 : (p:ℝ)^n = (p:ℝ)^(n-1) * (p:ℝ) := by
        rw [← pow_succ, Nat.sub_add_cancel hn1]
      have h6 : (0:ℝ) < (p:ℝ)^(n-1) := pow_pos hppos _
      nlinarith [h5, h6, hpgt1]
    have hcardD' : (((Finset.univ : Finset (Fin n × Fin p)).biUnion BadD).card : ℝ)
        ≤ (p:ℝ)^(n-1)/2 := hcardD.trans hsumD
    linarith [h1, hcardD', hcardB, h4]
  have hex : ∃ π : Fin n → Fin p, π ∉ BadT := by
    by_contra h
    push_neg at h
    have hfull : BadT = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    have : (BadT.card : ℝ) = (p:ℝ)^n := by
      rw [hfull, Finset.card_univ, Fintype.card_fun]
      simp
    linarith [hcardT, this]
  obtain ⟨π, hπ⟩ := hex
  refine ⟨π, ?_, ?_⟩
  · intro i v hv
    have hq : π ∉ BadD (v, i) := by
      intro hc
      exact hπ (by
        rw [hBadT]
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(v, i), Finset.mem_univ _, hc⟩))
    have hcond : ¬ (π v = i ∧ ε' * (((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ)
            / (p : ℝ) ^ (r - 1))
        ≤ |((degInPart 𝓗 π v i : ℕ) : ℝ)
            - ((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ) / (p : ℝ) ^ (r - 1)|) := by
      intro hc
      exact hq (by rw [hBadD]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    have hlt := not_le.mp (fun hc => hcond ⟨hv, hc⟩)
    linarith [hlt]
  · intro S hS hSsz i
    have hSU : S ∈ U := by
      rw [hU, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hS, hSsz⟩
    have hq : π ∉ BadB S i := by
      intro hc
      exact hπ (by
        rw [hBadT]
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨S, hSU,
          Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hc⟩⟩))
    have hcond : ¬ (⌈2 * (S.ncard : ℝ) / (p : ℝ)⌉₊ ≤ (S ∩ partSet π i).ncard) := by
      intro hc
      exact hq (by rw [hBadB]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    have h2 : (S ∩ partSet π i).ncard < ⌈2 * (S.ncard : ℝ) / (p : ℝ)⌉₊ := not_le.mp hcond
    have h3 : ((S ∩ partSet π i).ncard : ℝ) ≤ 2 * (S.ncard : ℝ) / (p : ℝ) := by
      have h4 : (S ∩ partSet π i).ncard + 1 ≤ ⌈2 * (S.ncard : ℝ) / (p : ℝ)⌉₊ :=
        Nat.succ_le_of_lt h2
      have h4' : (((S ∩ partSet π i).ncard : ℕ) : ℝ) + 1
          ≤ ((⌈2 * (S.ncard : ℝ) / (p : ℝ)⌉₊ : ℕ) : ℝ) := by exact_mod_cast h4
      have h5 : ((⌈2 * (S.ncard : ℝ) / (p : ℝ)⌉₊ : ℕ) : ℝ)
          < 2 * (S.ncard : ℝ) / (p : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
      linarith [h4', h5]
    rw [show 2 * ((S.ncard : ℝ) / (p : ℝ)) = 2 * (S.ncard : ℝ) / (p : ℝ) by ring]
    exact h3


/-- The `ncard` of a disjoint finite union. -/
lemma ncard_iUnion_disj {n : ℕ} {ι : Type*} [Fintype ι] (f : ι → Set (Fin n))
    (h : ∀ i j, i ≠ j → Disjoint (f i) (f j)) :
    (⋃ i, f i).ncard = ∑ i, (f i).ncard := by
  classical
  rw [Set.ncard_iUnion_of_finite (fun i => Set.toFinite (f i)) (fun i j hij => h i j hij)]
  exact finsum_eq_sum_of_fintype _

/-- `ncard` as a sum of indicators. -/
lemma ncard_eq_sum_indicator {n : ℕ} (T : Set (Fin n)) :
    (T.ncard : ℝ) = ∑ v : Fin n, T.indicator (fun _ => (1:ℝ)) v := by
  classical
  have h1 : T.ncard = (Finset.univ.filter (fun v : Fin n => v ∈ T)).card := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext v
    simp [Set.mem_toFinset]
  rw [h1, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro v _
  rw [Set.indicator_apply]

/-- A sum of a constant over a set, written with indicators. -/
lemma sum_indicator_const {n : ℕ} (T : Set (Fin n)) (a : ℝ) :
    (∑ v : Fin n, T.indicator (fun _ => a) v) = a * (T.ncard : ℝ) := by
  classical
  rw [ncard_eq_sum_indicator T, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases hv : v ∈ T <;> simp [hv]

end Work.Deep.Nibble

namespace Work.Deep.Nibble

theorem cover_of_good {n : ℕ} {𝓗 : HG n} {r p : ℕ} {κ ε' D : ℝ}
    {𝓕 : Set (Set (Fin n))} {π : Fin n → Fin p}
    (hr : 2 ≤ r) (hp : 2 ≤ p) (hπ : GoodPartition 𝓗 r ε' D 𝓕 π)
    (hκ0 : 0 < κ) (hκ4 : κ < 1 / 4) (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1) (hD0 : 0 < D)
    (hdeg : ∀ v : Fin n, |((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ) - D| ≤ κ * D)
    {c : Fin p → ℕ} (hc1 : ∀ i, 1 ≤ c i)
    (φ : ∀ i : Fin p, (partHyp 𝓗 π i).Coloring (Fin (c i)))
    (hcub : ∀ i : Fin p, (c i : ℝ) ≤ (1 + κ/4) * ((1 + ε') * (1 + κ) * (D / (p:ℝ)^(r-1))) + 1)
    (hmarg : (1 - 2.5 * κ) * ((1 + κ/4) * ((1 + ε') * (1 + κ) * (D / (p:ℝ)^(r-1))) + 1)
        ≤ (1 - ε') * (1 - κ) * (D / (p:ℝ)^(r-1)))
    (hunion : 2 * (𝓕.ncard : ℝ) * Real.exp (-(κ^2 * (p:ℝ)/4)) < 1) :
    ∃ M₀ : Set 𝓗, ErdosFaberLovaszConjecture.IsMatching 𝓗 M₀ ∧
      ∀ S ∈ 𝓕, D ^ ((1:ℝ)/20) ≤ (S.ncard : ℝ) →
        (1 - 3 * κ) * (S.ncard : ℝ) ≤
          ((S ∩ ErdosFaberLovaszConjecture.matchVert M₀).ncard : ℝ) := by
  classical
  have hci : ∀ i : Fin p, (0:ℝ) < (c i : ℝ) := by
    intro i
    have h := hc1 i
    exact_mod_cast (by omega : 0 < c i)
  -- (1) the per-vertex mean bound
  have hvert : ∀ (i : Fin p) (v : Fin n), v ∈ partSet π i →
      (1 - 2.5 * κ) * (c i : ℝ) ≤ ((degInPart 𝓗 π v i : ℕ) : ℝ) := by
    intro i v hv
    have h1 := hπ.1 i v hv
    rw [abs_le] at h1
    have h2 := hdeg v
    rw [abs_le] at h2
    have hpow : (0:ℝ) < (p:ℝ)^(r-1) := by positivity
    have hm : (1 - κ) * D / (p:ℝ)^(r-1)
        ≤ ((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ) / (p:ℝ)^(r-1) :=
      div_le_div_of_nonneg_right (by linarith [h2.1]) (le_of_lt hpow)
    have hm2 : (1 - ε') * (((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ)
        / (p:ℝ)^(r-1)) ≤ ((degInPart 𝓗 π v i : ℕ) : ℝ) := by
      linarith [h1.1]
    have hL : (1 - ε') * ((1 - κ) * D / (p:ℝ)^(r-1)) ≤ ((degInPart 𝓗 π v i : ℕ) : ℝ) :=
      (mul_le_mul_of_nonneg_left hm (by linarith)).trans hm2
    have hM := hcub i
    have h3 : (1 - 2.5 * κ) * (c i : ℝ) ≤ (1 - ε') * ((1 - κ) * D / (p:ℝ)^(r-1)) := by
      have heq : (1 - ε') * ((1 - κ) * D / (p:ℝ)^(r-1))
          = (1 - ε') * (1 - κ) * (D / (p:ℝ)^(r-1)) := by
        rw [mul_div_assoc]
        ring
      rw [heq]
      have h4 : (0:ℝ) < 1 - 2.5 * κ := by linarith
      have h5 := mul_le_mul_of_nonneg_left hM (le_of_lt h4)
      linarith [h5, hmarg]
    linarith [h3, hL]
  -- (0) the colour classes are inside their part
  have hclass_sub : ∀ (i : Fin p) (x : Fin (c i)), classVert (φ i) x ⊆ partSet π i := by
    intro i x v hv
    rw [classVert, Set.mem_sUnion] at hv
    obtain ⟨e, he, hve⟩ := hv
    rw [classEdges, Set.mem_image] at he
    obtain ⟨e', he', rfl⟩ := he
    exact e'.2.2 hve
  have hclass_mem_H : ∀ (i : Fin p) (x : Fin (c i)) {e : Set (Fin n)},
      e ∈ classEdges (φ i) x → e ∈ 𝓗 := by
    intro i x e he
    rw [classEdges, Set.mem_image] at he
    obtain ⟨e', he', rfl⟩ := he
    exact e'.2.1
  have hclass_subset : ∀ (i : Fin p) (x : Fin (c i)) {e : Set (Fin n)},
      e ∈ classEdges (φ i) x → e ⊆ partSet π i := by
    intro i x e he
    rw [classEdges, Set.mem_image] at he
    obtain ⟨e', he', rfl⟩ := he
    exact e'.2.2
  -- (2) the mean of the covered count in one part
  have hmean_part : ∀ (S : Set (Fin n)) (i : Fin p),
      (1 - 2.5 * κ) * ((S ∩ partSet π i).ncard : ℝ)
        ≤ (∑ x : Fin (c i), ((S ∩ classVert (φ i) x).ncard : ℝ)) / (c i : ℝ) := by
    intro S i
    have hdc := sum_classVert_ncard_eq (n := n) (𝓖 := partHyp 𝓗 π i) (c := c i) (hc1 i) (φ i) S
    have hlow : ((1 - 2.5 * κ) * (c i : ℝ)) * ((S ∩ partSet π i).ncard : ℝ)
        ≤ ∑ x : Fin (c i), ((S ∩ classVert (φ i) x).ncard : ℝ) := by
      have hpoint : ∀ v : Fin n,
          (S ∩ partSet π i).indicator (fun _ => (1 - 2.5 * κ) * (c i : ℝ)) v
            ≤ (S ∩ partSet π i).indicator
                (fun v => ((ErdosFaberLovaszConjecture.hypergraphDegree (partHyp 𝓗 π i) v : ℕ) : ℝ)) v := by
        intro v
        by_cases hv : v ∈ S ∩ partSet π i
        · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
          exact hvert i v hv.2
        · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]
      have h2 : (∑ v : Fin n,
            (S ∩ partSet π i).indicator
              (fun v => ((ErdosFaberLovaszConjecture.hypergraphDegree (partHyp 𝓗 π i) v : ℕ) : ℝ)) v)
          ≤ ∑ v : Fin n, S.indicator
              (fun v => ((ErdosFaberLovaszConjecture.hypergraphDegree (partHyp 𝓗 π i) v : ℕ) : ℝ)) v := by
        apply Finset.sum_le_sum
        intro v _
        by_cases hv : v ∈ S ∩ partSet π i
        · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv.1]
        · rw [Set.indicator_of_notMem hv]
          by_cases hv2 : v ∈ S
          · rw [Set.indicator_of_mem hv2]
            exact Nat.cast_nonneg _
          · rw [Set.indicator_of_notMem hv2]
      rw [← sum_indicator_const (S ∩ partSet π i) ((1 - 2.5 * κ) * (c i : ℝ))]
      rw [hdc]
      exact (Finset.sum_le_sum (fun v _ => hpoint v)).trans h2
    rw [le_div_iff₀ (hci i)]
    rw [show (1 - 2.5 * κ) * ((S ∩ partSet π i).ncard : ℝ) * (c i : ℝ)
        = ((1 - 2.5 * κ) * (c i : ℝ)) * ((S ∩ partSet π i).ncard : ℝ) by ring]
    exact hlow
  -- (3) the per-part sizes form a partition of `S`
  have hsumS : ∀ S ∈ 𝓕, (∑ i : Fin p, ((S ∩ partSet π i).ncard : ℝ)) = (S.ncard : ℝ) := by
    intro S _
    have hdisj' : ∀ i i' : Fin p, i ≠ i' → Disjoint (S ∩ partSet π i) (S ∩ partSet π i') := by
      intro i i' hii
      rw [Set.disjoint_left]
      intro v hv hv'
      exact hii (hv.2.symm.trans hv'.2)
    have h := ncard_iUnion_disj (fun i : Fin p => S ∩ partSet π i) hdisj'
    have h2 : (⋃ i : Fin p, S ∩ partSet π i) = S := by
      ext v
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨i, hv, _⟩; exact hv
      · intro hv; exact ⟨π v, hv, rfl⟩
    rw [h2] at h
    exact_mod_cast h.symm
  have hparts_disj : ∀ i i' : Fin p, i ≠ i' → Disjoint (partSet π i) (partSet π i') := by
    intro i i' hii
    rw [Set.disjoint_left]
    intro v hv hv'
    exact hii (hv.symm.trans hv')
  have hbsq : ∀ S ∈ 𝓕, D ^ ((1:ℝ)/20) ≤ (S.ncard : ℝ) →
      (∑ i : Fin p, (((S ∩ partSet π i).ncard : ℝ)) ^ 2)
        ≤ 2 * (∑ i : Fin p, ((S ∩ partSet π i).ncard : ℝ)) ^ 2 / (p:ℝ) := by
    intro S hS hSsz
    have hb : ∀ i : Fin p, ((S ∩ partSet π i).ncard : ℝ) ≤ 2 * ((S.ncard : ℝ) / (p:ℝ)) :=
      fun i => hπ.2 S hS hSsz i
    have hsum := hsumS S hS
    calc ∑ i : Fin p, (((S ∩ partSet π i).ncard : ℝ)) ^ 2
        ≤ ∑ i : Fin p, (2 * ((S.ncard : ℝ) / (p:ℝ))) * ((S ∩ partSet π i).ncard : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          rw [sq]
          exact mul_le_mul_of_nonneg_right (hb i) (Nat.cast_nonneg _)
      _ = (2 * ((S.ncard : ℝ) / (p:ℝ))) * ∑ i : Fin p, ((S ∩ partSet π i).ncard : ℝ) := by
          rw [Finset.mul_sum]
      _ = 2 * (∑ i : Fin p, ((S ∩ partSet π i).ncard : ℝ)) ^ 2 / (p:ℝ) := by
          rw [hsum]
          ring
  -- (4) the large sets and the union bound over the random choices
  haveI : ∀ i : Fin p, NeZero (c i) := fun i => ⟨by have := hc1 i; omega⟩
  set U : Finset (Set (Fin n)) := Finset.univ.filter (fun S : Set (Fin n) =>
      S ∈ 𝓕 ∧ D ^ ((1:ℝ)/20) ≤ (S.ncard : ℝ)) with hU
  have hUmem : ∀ S, S ∈ U → S ∈ 𝓕 ∧ D ^ ((1:ℝ)/20) ≤ (S.ncard : ℝ) := by
    intro S hS
    rw [hU, Finset.mem_filter] at hS
    exact hS.2
  have hUcard : U.card ≤ 𝓕.ncard := by
    have h1 : (U : Set (Set (Fin n))) ⊆ 𝓕 := by
      intro S hS
      exact (hUmem S (by simpa using hS)).1
    have h2 := Set.ncard_mono h1
    rwa [show ((U : Set (Set (Fin n)))).ncard = U.card by simp] at h2
  set Bad : Set (Fin n) → Set (∀ i : Fin p, Fin (c i)) := fun S =>
      {q | (1 - 3 * κ) * (S.ncard : ℝ) > ∑ i, ((S ∩ classVert (φ i) (q i)).ncard : ℝ)} with hBad
  have hprob : ∀ S ∈ U, (Work.Deep.Reed.FinProb.pi
      (fun i => Work.Deep.Reed.FinProb.uniform (Fin (c i)))).prob (Bad S)
      ≤ 2 * Real.exp (-(κ^2 * (p:ℝ)/4)) := by
    intro S hS
    obtain ⟨hS𝓕, hSsz⟩ := hUmem S hS
    have hpt := prod_uniform_lower_tail (c := c) hκ0
      (b := fun i : Fin p => ((S ∩ partSet π i).ncard : ℝ)) (fun i => Nat.cast_nonneg _)
      (Y := fun i (x : Fin (c i)) => ((S ∩ classVert (φ i) x).ncard : ℝ))
      (fun i x => Nat.cast_nonneg _)
      (fun i x => by
        exact_mod_cast Set.ncard_mono (Set.inter_subset_inter_right S (hclass_sub i x)))
      (hmean_part S) (hbsq S hS𝓕 hSsz)
    rw [hsumS S hS𝓕] at hpt
    rw [hBad]
    exact hpt
  have hlim : (Work.Deep.Reed.FinProb.pi
      (fun i => Work.Deep.Reed.FinProb.uniform (Fin (c i)))).prob (⋃ S ∈ U, Bad S) < 1 := by
    set ν := Work.Deep.Reed.FinProb.pi (fun i => Work.Deep.Reed.FinProb.uniform (Fin (c i))) with hν
    have h1 : ν.prob (⋃ S ∈ U, Bad S) ≤ ∑ S ∈ U, ν.prob (Bad S) :=
      Work.Deep.Reed.FinProb.prob_iUnion_le ν U Bad
    have h2 : (∑ S ∈ U, ν.prob (Bad S)) ≤ ∑ _S ∈ U, (2 * Real.exp (-(κ^2 * (p:ℝ)/4))) :=
      Finset.sum_le_sum (fun S hS => by
        have hh := hprob S hS
        rwa [hν] at hh)
    have h3 : (∑ _S ∈ U, (2 * Real.exp (-(κ^2 * (p:ℝ)/4))))
        = (U.card : ℝ) * (2 * Real.exp (-(κ^2 * (p:ℝ)/4))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h4 : (U.card : ℝ) ≤ (𝓕.ncard : ℝ) := by exact_mod_cast hUcard
    have h5 : (𝓕.ncard : ℝ) * (2 * Real.exp (-(κ^2 * (p:ℝ)/4))) < 1 := by
      nlinarith [hunion]
    have h7 : (U.card : ℝ) * (2 * Real.exp (-(κ^2 * (p:ℝ)/4))) < 1 := by
      have h8 : (0:ℝ) ≤ 2 * Real.exp (-(κ^2 * (p:ℝ)/4)) := by positivity
      nlinarith [h4, h5, h8]
    linarith [h1, h2, h3.le, h7]
  have hex : ∃ q : (∀ i : Fin p, Fin (c i)), q ∉ (⋃ S ∈ U, Bad S) := by
    by_contra h
    push_neg at h
    have hfull : (⋃ S ∈ U, Bad S) = Set.univ := Set.eq_univ_of_forall h
    rw [hfull, Work.Deep.Reed.FinProb.prob_univ] at hlim
    linarith
  obtain ⟨q, hq⟩ := hex
  have hqgood : ∀ S ∈ U, ¬ ((1 - 3 * κ) * (S.ncard : ℝ)
      > ∑ i : Fin p, ((S ∩ classVert (φ i) (q i)).ncard : ℝ)) := by
    intro S hS hgt
    exact hq (Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨hS, hgt⟩⟩)
  -- (5) the matching
  set M : Set 𝓗 := {e : 𝓗 | ∃ i : Fin p, (e : Set (Fin n)) ∈ classEdges (φ i) (q i)} with hM
  have hMmem : ∀ e : 𝓗, e ∈ M ↔ ∃ i : Fin p, (e : Set (Fin n)) ∈ classEdges (φ i) (q i) := by
    intro e
    rw [hM]
    exact Iff.rfl
  refine ⟨M, ?_, ?_⟩
  · intro e₁ he₁ e₂ he₂ hne
    obtain ⟨i₁, hi₁⟩ := (hMmem e₁).mp he₁
    obtain ⟨i₂, hi₂⟩ := (hMmem e₂).mp he₂
    have hi₁' := hi₁
    have hi₂' := hi₂
    rw [classEdges, Set.mem_image] at hi₁ hi₂
    obtain ⟨e₁', he₁', hv₁⟩ := hi₁
    obtain ⟨e₂', he₂', hv₂⟩ := hi₂
    by_cases hii : i₁ = i₂
    · subst hii
      have hmatch := ErdosFaberLovaszConjecture.Hypergraph.Coloring.colorClass_isMatching
        (φ i₁) (q i₁)
      have hdis : Disjoint (e₁' : Set (Fin n)) (e₂' : Set (Fin n)) :=
        hmatch he₁' he₂' (fun hcon => hne (Subtype.ext (by rw [← hv₁, ← hv₂, hcon])))
      rw [← hv₁, ← hv₂]
      exact hdis
    · exact Disjoint.mono (hclass_subset i₁ (q i₁) hi₁') (hclass_subset i₂ (q i₂) hi₂')
        (hparts_disj i₁ i₂ hii)
  · intro S hS hSsz
    have hSU : S ∈ U := by
      rw [hU, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hS, hSsz⟩
    have hle := le_of_not_gt (hqgood S hSU)
    have hsub : S ∩ (⋃ i : Fin p, classVert (φ i) (q i)) ⊆ S ∩ ErdosFaberLovaszConjecture.matchVert M := by
      intro v hv
      obtain ⟨hvS, hvi⟩ := hv
      obtain ⟨i, hvi'⟩ := Set.mem_iUnion.mp hvi
      obtain ⟨e', he', hve'⟩ := Set.mem_sUnion.mp hvi'
      refine ⟨hvS, ?_⟩
      rw [ErdosFaberLovaszConjecture.matchVert]
      exact Set.mem_iUnion.mpr ⟨⟨e', hclass_mem_H i (q i) he'⟩,
        Set.mem_iUnion.mpr ⟨(hMmem _).mpr ⟨i, he'⟩, hve'⟩⟩
    have hUnion : S ∩ (⋃ i : Fin p, classVert (φ i) (q i))
        = ⋃ i : Fin p, (S ∩ classVert (φ i) (q i)) := by
      ext v
      simp only [Set.mem_inter_iff, Set.mem_iUnion]
      constructor
      · rintro ⟨hvS, i, hvi⟩
        exact ⟨i, hvS, hvi⟩
      · rintro ⟨i, hvS, hvi⟩
        exact ⟨hvS, i, hvi⟩
    have hdisj' : ∀ i i' : Fin p, i ≠ i' →
        Disjoint (S ∩ classVert (φ i) (q i)) (S ∩ classVert (φ i') (q i')) := by
      intro i i' hii
      exact Disjoint.mono (Set.inter_subset_right.trans (hclass_sub i (q i)))
        (Set.inter_subset_right.trans (hclass_sub i' (q i'))) (hparts_disj i i' hii)
    calc (1 - 3 * κ) * (S.ncard : ℝ)
        ≤ ∑ i : Fin p, ((S ∩ classVert (φ i) (q i)).ncard : ℝ) := hle
      _ = ((S ∩ (⋃ i : Fin p, classVert (φ i) (q i))).ncard : ℝ) := by
          rw [hUnion, ncard_iUnion_disj _ hdisj']
          push_cast
          ring
      _ ≤ ((S ∩ ErdosFaberLovaszConjecture.matchVert M).ncard : ℝ) := by
          exact_mod_cast Set.ncard_mono hsub


/-- `Work.Deep.Nibble.RelCoverStatement` follows from Kahn's result (proved in `Work.Deep.Kahn`) by the paper's own route -- `cor:sparse_egj` from `thm:egj` -- with the soft Kahn colouring in place of Molloy-Reed, since the target covering `(1-3κ)|S|` needs no `Δ^{-ε}` precision.  Recipe: fix `α := κ/4`, take `D₀` from `ErdosFaberLovaszConjecture.kahn_colorable`, pick `p := ⌈C (log n)²/κ²⌉` and split `V` randomly into `p` parts; each induced part has degrees within `(1±ε')` of `d(v)/p^{r-1}` (probabilistic method, Chernoff), hence maximum degree `D_i ≥ D₀`, so Kahn colours it with `c_i := ⌈(1+α)D_i⌉` colours whose classes are matchings; a uniformly random class of part `i` gives a matching `M_i` with `E|S ∩ V(M_i)| = (Σ_{v∈S_i} d_i(v))/c_i ≥ (1-2.5κ)|S_i|` exactly; the `p` independent choices concentrate (Hoeffding, with `Σ_i|S_i|² ≤ 2|S|²/p` and `|𝓕| ≤ n^{2 log n}`), so some choice has `|S ∩ V(M)| ≥ (1-3κ)|S|` for all `S ∈ 𝓕`. -/
theorem relCoverStatement_of_Kahn (hK : ErdosFaberLovaszConjecture.KahnStatement) :
    Work.Deep.Nibble.RelCoverStatement := by
  intro r hr κ hκ0 hκ4
  have hα : (0:ℝ) < κ / 4 := by linarith
  obtain ⟨D₀, hD₀pos, hKahn⟩ := ErdosFaberLovaszConjecture.kahn_colorable hK hα hr
  obtain ⟨n₀, _hn₀pos, hn₀⟩ := relcoverMargins (r := r) hr hκ0 hκ4 hD₀pos
  refine ⟨max n₀ 100, lt_max_of_lt_right (by norm_num), ?_⟩
  intro n hn D hD 𝓗 hlin hrsizeE hdeg 𝓕 h𝓕
  have hn₁ : n₀ ≤ (n:ℝ) := le_trans (le_max_left _ _) hn
  have hn₂ : (100:ℝ) ≤ (n:ℝ) := le_trans (le_max_right _ _) hn
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1:ℝ) ≤ (n:ℝ) by linarith)
  have hn1' : (1:ℝ) ≤ (n:ℝ) := by linarith
  have hκ1 : κ < 1 := by linarith
  have hε'0 : (0:ℝ) < κ/100 := by linarith
  have hε'1 : κ/100 ≤ 1 := by linarith
  have hD0 : 0 < D := lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hD
  have hD1 : 1 ≤ D := le_trans (Real.one_le_rpow hn1' (by norm_num)) hD
  -- the number of parts
  set p : ℕ := ⌈32 * (Real.log (n:ℝ))^2 / κ^2⌉₊ + 2 with hp
  have hp2 : 2 ≤ p := by omega
  set Y : ℝ := (Real.log (n:ℝ))^2 / κ^2 with hY
  have hY0 : (0:ℝ) ≤ Y := by rw [hY]; positivity
  have hy : (32 * (Real.log (n:ℝ))^2 / κ^2) = 32 * Y := by rw [hY]; ring
  have hpv : (p:ℝ) = ((⌈32 * Y⌉₊ : ℕ) : ℝ) + 2 := by
    rw [hp, hy]
    push_cast
    ring
  have hplow : 32 * (Real.log (n:ℝ))^2 / κ^2 ≤ (p:ℝ) := by
    rw [hy, hpv]
    have hc := Nat.le_ceil (32 * Y)
    linarith
  have hphigh : (p:ℝ) ≤ 33 * ((Real.log (n:ℝ))^2 / κ^2 + 1) := by
    rw [hpv, hY]
    have hc : ((⌈32 * ((Real.log (n:ℝ))^2 / κ^2)⌉₊ : ℕ) : ℝ)
        < 32 * ((Real.log (n:ℝ))^2 / κ^2) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hY0' : (0:ℝ) ≤ (Real.log (n:ℝ))^2 / κ^2 := by positivity
    linarith [hc, hY0']
  -- the threshold arithmetic
  obtain ⟨hm1, hm2, hm3, hm4, hm5, _hm6⟩ := hn₀ n hn₁ p hp2 hplow hphigh D hD 𝓕 h𝓕
  -- the size hypothesis in `ncard` form
  have hrsize : ∀ e ∈ 𝓗, e.ncard = r := by
    intro e he
    rw [← ErdosFaberLovaszConjecture.edgeSize_eq_ncard]
    exact hrsizeE e he
  -- the good random partition
  obtain ⟨π, hπ⟩ := exists_goodPartition (𝓗 := 𝓗) (𝓕 := 𝓕) (r := r) (p := p)
    hr hp2 hκ0 hκ1 hε'0 hε'1 hD0 hD1 hn1 hlin hrsize hdeg hm1 hm2
  -- the number of colours of each part and Kahn's colourings
  set c : Fin p → ℕ := fun i => max 1
    ⌈(1 + κ/4) * ((ErdosFaberLovaszConjecture.hypergraphMaxDegree (partHyp 𝓗 π i) : ℕ) : ℝ)⌉₊
    with hc
  have hc1 : ∀ i, 1 ≤ c i := by intro i; rw [hc]; exact le_max_left _ _
  have hcol : ∀ i : Fin p, Nonempty ((partHyp 𝓗 π i).Coloring (Fin (c i))) := by
    intro i
    by_cases hne : (partSet π i).Nonempty
    · obtain ⟨v, hv⟩ := hne
      have hDmax : D₀ ≤ ((ErdosFaberLovaszConjecture.hypergraphMaxDegree (partHyp 𝓗 π i) : ℕ) : ℝ) := by
        have h1 := hπ.1 i v hv
        rw [abs_le] at h1
        have h2 := hdeg v
        rw [abs_le] at h2
        have hpow : (0:ℝ) < (p:ℝ)^(r-1) := by positivity
        have h4 : (1 - κ) * D / (p:ℝ)^(r-1)
            ≤ ((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ) / (p:ℝ)^(r-1) :=
          div_le_div_of_nonneg_right (by linarith [h2.1]) (le_of_lt hpow)
        have h5 : (1 - κ/100) * (((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ)
            / (p:ℝ)^(r-1)) ≤ ((degInPart 𝓗 π v i : ℕ) : ℝ) := by
          linarith [h1.1]
        have h3 : (1 - κ/100) * ((1 - κ) * D / (p:ℝ)^(r-1))
            ≤ ((degInPart 𝓗 π v i : ℕ) : ℝ) := by
          calc (1 - κ/100) * ((1 - κ) * D / (p:ℝ)^(r-1))
              ≤ (1 - κ/100) * (((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ)
                  / (p:ℝ)^(r-1)) := by
                apply mul_le_mul_of_nonneg_left h4 (by linarith)
            _ ≤ ((degInPart 𝓗 π v i : ℕ) : ℝ) := h5
        have h6 := ErdosFaberLovaszConjecture.hypergraphDegree_le_maxDegree (partHyp 𝓗 π i) v
        have h7 : D₀ + 1 ≤ (1 - κ/100) * ((1 - κ) * D / (p:ℝ)^(r-1)) := by
          have heq : (1 - κ/100) * ((1 - κ) * D / (p:ℝ)^(r-1))
              = (1 - κ/100) * (1 - κ) * (D / (p:ℝ)^(r-1)) := by
            rw [mul_div_assoc]
            ring
          rw [heq]
          exact hm5
        calc D₀ ≤ D₀ + 1 := by linarith
          _ ≤ (1 - κ/100) * ((1 - κ) * D / (p:ℝ)^(r-1)) := h7
          _ ≤ ((degInPart 𝓗 π v i : ℕ) : ℝ) := h3
          _ = ((ErdosFaberLovaszConjecture.hypergraphDegree (partHyp 𝓗 π i) v : ℕ) : ℝ) := by
              rw [degInPart]
          _ ≤ ((ErdosFaberLovaszConjecture.hypergraphMaxDegree (partHyp 𝓗 π i) : ℕ) : ℝ) := by
              exact_mod_cast h6
      have hlin_i : ErdosFaberLovaszConjecture.Hypergraph.IsLinear (partHyp 𝓗 π i) :=
        Set.Pairwise.mono (fun e he => he.1) hlin
      have hmax_i : ((ErdosFaberLovaszConjecture.hypergraphMaxDegree (partHyp 𝓗 π i) : ℕ) : ℝ)
          ≤ ((ErdosFaberLovaszConjecture.hypergraphMaxDegree (partHyp 𝓗 π i) : ℕ) : ℝ) := le_refl _
      have hsize_i : ∀ e : partHyp 𝓗 π i,
          (ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) : ℝ) ≤ (r:ℝ) := by
        intro e
        rw [ErdosFaberLovaszConjecture.edgeSize_eq_ncard, hrsize (e : Set (Fin n)) e.2.1]
      have hcub_i : (1 + κ/4) * ((ErdosFaberLovaszConjecture.hypergraphMaxDegree
          (partHyp 𝓗 π i) : ℕ) : ℝ) ≤ (c i : ℝ) := by
        rw [hc]
        calc (1 + κ/4) * ((ErdosFaberLovaszConjecture.hypergraphMaxDegree (partHyp 𝓗 π i) : ℕ) : ℝ)
            ≤ ((⌈(1 + κ/4) * ((ErdosFaberLovaszConjecture.hypergraphMaxDegree
                (partHyp 𝓗 π i) : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
          _ ≤ ((max 1 ⌈(1 + κ/4) * ((ErdosFaberLovaszConjecture.hypergraphMaxDegree
                (partHyp 𝓗 π i) : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
      exact hKahn _ hDmax n (partHyp 𝓗 π i) hlin_i hmax_i hsize_i (c i) hcub_i
    · have h0 : partSet π i = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hempty : ∀ e, e ∉ partHyp 𝓗 π i := by
        intro e he
        have hsub : e ⊆ partSet π i := he.2
        have hee : e = ∅ := Set.subset_empty_iff.mp (by rwa [h0] at hsub)
        have h1 := hrsize e he.1
        rw [hee] at h1
        simp at h1
        omega
      exact ⟨⟨fun e => ⟨0, hc1 i⟩, fun e _ _ _ => (hempty e e.2).elim⟩⟩
  let φ : ∀ i : Fin p, (partHyp 𝓗 π i).Coloring (Fin (c i)) := fun i => Classical.choice (hcol i)
  -- the upper bound on the number of colours
  have hcub : ∀ i : Fin p, (c i : ℝ)
      ≤ (1 + κ/4) * ((1 + κ/100) * (1 + κ) * (D / (p:ℝ)^(r-1))) + 1 := by
    intro i
    have hmax := partMaxDegree_le hπ hdeg hκ0 hε'0 hD0 i
    have h1 : ((max 1 ⌈(1 + κ/4) * ((ErdosFaberLovaszConjecture.hypergraphMaxDegree
        (partHyp 𝓗 π i) : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)
        ≤ (1 + κ/4) * ((ErdosFaberLovaszConjecture.hypergraphMaxDegree (partHyp 𝓗 π i) : ℕ) : ℝ) + 1 := by
      push_cast
      have hM0 : (0:ℝ) ≤ ((ErdosFaberLovaszConjecture.hypergraphMaxDegree (partHyp 𝓗 π i) : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      apply max_le
      · nlinarith [hM0, hκ0]
      · have hc := Nat.ceil_lt_add_one (show (0:ℝ) ≤ (1 + κ/4) *
            ((ErdosFaberLovaszConjecture.hypergraphMaxDegree (partHyp 𝓗 π i) : ℕ) : ℝ) by positivity)
        linarith
    have h2 : (1 + κ/4) * ((ErdosFaberLovaszConjecture.hypergraphMaxDegree
        (partHyp 𝓗 π i) : ℕ) : ℝ) + 1
        ≤ (1 + κ/4) * ((1 + κ/100) * (1 + κ) * (D / (p:ℝ)^(r-1))) + 1 := by
      have h3 := mul_le_mul_of_nonneg_left hmax (by linarith : (0:ℝ) ≤ 1 + κ/4)
      linarith
    calc (c i : ℝ) = ((max 1 ⌈(1 + κ/4) * ((ErdosFaberLovaszConjecture.hypergraphMaxDegree
          (partHyp 𝓗 π i) : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := rfl
      _ ≤ (1 + κ/4) * ((ErdosFaberLovaszConjecture.hypergraphMaxDegree
            (partHyp 𝓗 π i) : ℕ) : ℝ) + 1 := h1
      _ ≤ (1 + κ/4) * ((1 + κ/100) * (1 + κ) * (D / (p:ℝ)^(r-1))) + 1 := h2
  -- the mean inequality
  have hmarg : (1 - 2.5 * κ) * ((1 + κ / 4) * ((1 + κ/100) * (1 + κ) * (D / (p : ℝ) ^ (r - 1))) + 1)
      ≤ (1 - κ/100) * (1 - κ) * (D / (p : ℝ) ^ (r - 1)) := by
    nlinarith [hm4]
  -- the union bound
  have hunion : 2 * (𝓕.ncard : ℝ) * Real.exp (-(κ ^ 2 * (p : ℝ) / 4)) < 1 := by
    by_cases h𝓕0 : 𝓕.ncard = 0
    · rw [h𝓕0]
      simp
    have h2Npos : (0:ℝ) < 2 * (𝓕.ncard : ℝ) := by
      have h1 : (0:ℝ) < (𝓕.ncard : ℝ) := by
        exact_mod_cast (Nat.pos_of_ne_zero h𝓕0)
      linarith
    have hexppos : (0:ℝ) < Real.exp (κ ^ 2 * (p : ℝ) / 4) := Real.exp_pos _
    have h2N : 2 * (𝓕.ncard : ℝ) < Real.exp (κ ^ 2 * (p : ℝ) / 4) := by
      have h := Real.exp_lt_exp.mpr hm3
      rwa [Real.exp_log h2Npos] at h
    have hexp : Real.exp (-(κ ^ 2 * (p : ℝ) / 4)) = 1 / Real.exp (κ ^ 2 * (p : ℝ) / 4) := by
      rw [Real.exp_neg]; ring
    rw [hexp]
    calc 2 * (𝓕.ncard : ℝ) * (1 / Real.exp (κ ^ 2 * (p : ℝ) / 4))
        < Real.exp (κ ^ 2 * (p : ℝ) / 4) * (1 / Real.exp (κ ^ 2 * (p : ℝ) / 4)) := by
          apply mul_lt_mul_of_pos_right h2N
          positivity
      _ = 1 := by field_simp
  -- the covering matching
  obtain ⟨M₀, hM₀, hcov⟩ := cover_of_good hr hp2 hπ hκ0 hκ4 hε'0 hε'1 hD0 hdeg hc1 φ
    hcub hmarg hunion
  exact ⟨M₀, hM₀, fun S hS hSbig => hcov S hS hSbig⟩

end Work.Deep.Nibble
