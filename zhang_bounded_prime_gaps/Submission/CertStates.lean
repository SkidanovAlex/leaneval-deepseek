import Mathlib
import Submission.CertIndex

set_option maxRecDepth 1000000
open scoped BigOperators
open Finset

/-!
# The state space of the certificate's packed computation

`Submission/CertIndex.lean` enumerates the 272 multiplicity vectors `m : Fin 12 → ℕ` of weighted
degree `≤ 24` as `certStates = certSigs.map mvec` and equips each degree class with the linear
functional `muVal` (`mu_inj_class`).  The packed DP of the certificate computation needs two
*state-space* facts about `certStates`:

* **completeness**: every multiplicity vector of weighted degree `≤ 24` is in `certStates`
  (`mem_certStates_of_deg`) — equivalently the 272 states are exactly the vectors of degree `≤ 24`;
* **closure**: `certStates` is closed under `m ↦ m - e_v` (`certStates_sub_evec`), so that the
  shift `m ↦ m + e_v` of class `j` lands inside class `j + v + 1`.

Both come from the canonical (decreasing) signature `sigOf m = [24]^{m 11} ++ … ++ [2]^{m 0}`:
`sigAux` generates every decreasing multiset of weighted degree `≤ rem` (`sigOfAux_mem`), and
`mvec (sigOf m) = m` (`mvec_sigOfAux`).

The last ingredient is the **no-interference** lemma `no_interference`: for a state `m` of class
`i = j + v + 1` with `m v = 0`, either `muVal m < mu v` (so the shift never reaches the block) or
no state of class `j` sits at position `muVal m - mu v`.  It uses `muVal_inj_class`, the
injectivity of `muVal` inside a class, extracted from the `decide`-checked `mu_inj_class` via the
generic `nodup_map_injective`.
-/

namespace Commons.NumberTheory.MaynardSieve


def sigOfAux : (i : ℕ) → (hi : i ≤ 12) → MV → List ℕ
  | 0, _, _ => []
  | (i+1), hi, m =>
      List.replicate (m ⟨i, Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi⟩) (2 * (i + 1))
        ++ sigOfAux i (Nat.le_of_succ_le hi) m

def sigOf (m : MV) : List ℕ := sigOfAux 12 le_rfl m

theorem sigOfAux_succ (i : ℕ) (hi : i + 1 ≤ 12) (m : MV) :
    sigOfAux (i+1) hi m
      = List.replicate (m ⟨i, Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi⟩) (2 * (i + 1))
        ++ sigOfAux i (Nat.le_of_succ_le hi) m := rfl

theorem sigAux_mono : ∀ (k : ℕ) {rem rem' : ℕ}, rem ≤ rem' →
    ∀ σ ∈ sigAux k rem, σ ∈ sigAux k rem'
  | 0, rem, rem', h, σ, hσ => by simpa [sigAux] using hσ
  | (k+1), rem, rem', h, σ, hσ => by
      rw [sigAux] at hσ ⊢
      simp only [List.mem_flatMap, List.mem_map] at hσ ⊢
      obtain ⟨c, hc, t, ht, rfl⟩ := hσ
      refine ⟨c, ?_, t, ?_, rfl⟩
      · rw [List.mem_range] at hc ⊢
        have h1 : c * (2 * (k+1)) ≤ rem := by
          have := (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * (k+1))).mp
            (by omega : c ≤ rem / (2*(k+1)))
          linarith
        have h2 : c * (2 * (k+1)) ≤ rem' := by omega
        have := (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * (k+1))).mpr h2
        omega
      · exact sigAux_mono k (by omega) t ht

def Sf (i : ℕ) (m : MV) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin 12 => (j:ℕ) < i), 2 * ((j:ℕ)+1) * m j

theorem Sf_succ (i : ℕ) (hi : i < 12) (m : MV) :
    Sf (i+1) m = Sf i m + 2 * (i+1) * m ⟨i, hi⟩ := by
  unfold Sf
  have h : Finset.univ.filter (fun j : Fin 12 => (j:ℕ) < i+1)
      = insert ⟨i, hi⟩ (Finset.univ.filter (fun j : Fin 12 => (j:ℕ) < i)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | h)
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt h
  rw [h, Finset.sum_insert]
  · ring
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.lt_irrefl i

theorem Sf_twelve (m : MV) : Sf 12 m = degV m := by
  unfold Sf degV
  refine Finset.sum_congr ?_ (fun j _ => rfl)
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun _ => trivial, fun _ => j.isLt⟩

theorem sigOfAux_mem : ∀ (i : ℕ) (hi : i ≤ 12) (m : MV) (rem : ℕ),
    Sf i m ≤ rem → sigOfAux i hi m ∈ sigAux i rem
  | 0, hi, m, rem, h => by
      simp only [sigOfAux, sigAux]
      exact List.mem_singleton.mpr rfl
  | (i+1), hi, m, rem, h => by
      have hi' : i < 12 := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi
      rw [sigOfAux_succ, sigAux]
      simp only [List.mem_flatMap, List.mem_map]
      refine ⟨m ⟨i, hi'⟩, ?_, sigOfAux i (Nat.le_of_succ_le hi) m, ?_, ?_⟩
      · rw [List.mem_range]
        have h1 : Sf i m + 2 * (i+1) * m ⟨i, hi'⟩ ≤ rem := by rw [← Sf_succ i hi' m]; exact h
        have h2 : m ⟨i, hi'⟩ * (2 * (i+1)) ≤ rem := by linarith
        have := (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * (i+1))).mpr h2
        omega
      · apply sigOfAux_mem i (Nat.le_of_succ_le hi) m
        have h1 : Sf i m + 2 * (i+1) * m ⟨i, hi'⟩ ≤ rem := by rw [← Sf_succ i hi' m]; exact h
        omega
      · rfl

theorem count_replicate_eq (a b : ℕ) (n : ℕ) :
    List.count a (List.replicate n b) = if b = a then n else 0 := by
  rw [List.count_replicate]
  by_cases h : b = a <;> simp [h, beq_iff_eq]

theorem mvec_sigOfAux (i : ℕ) (hi : i ≤ 12) (m : MV) :
    mvec (sigOfAux i hi m) = fun j : Fin 12 => if (j:ℕ) < i then m j else 0 := by
  induction i with
  | zero =>
      funext j
      simp only [sigOfAux, mvec, List.count_nil, Nat.not_lt_zero, if_false]
  | succ i ih =>
      have hi' : i < 12 := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi
      rw [sigOfAux_succ]
      funext j
      rw [mvec, List.count_append, count_replicate_eq]
      have h2 : List.count (2 * ((j:ℕ)+1)) (sigOfAux i (Nat.le_of_succ_le hi) m)
          = (if (j:ℕ) < i then m j else 0) := by
        rw [← congrFun (ih (Nat.le_of_succ_le hi)) j]; rfl
      rw [h2]
      by_cases hij : 2 * (i+1) = 2 * ((j:ℕ)+1)
      · rw [if_pos hij, if_neg (by omega : ¬ (j:ℕ) < i), add_zero,
          if_pos (by omega : (j:ℕ) < i + 1)]
        have hfin : (⟨i, Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi⟩ : Fin 12) = j := by
          apply Fin.ext
          show i = (j:ℕ)
          omega
        exact congrArg m hfin
      · rw [if_neg hij]
        by_cases hlt : (j:ℕ) < i
        · rw [if_pos hlt, zero_add, if_pos (Nat.lt_succ_of_lt hlt)]
        · rw [if_neg hlt, if_neg (by omega)]

theorem mem_certStates_of_deg (m : MV) (h : degV m ≤ 24) : m ∈ certStates := by
  have hmem : sigOf m ∈ certSigs := by
    unfold sigOf certSigs
    apply sigOfAux_mem 12 le_rfl m 24
    rw [Sf_twelve]; exact h
  refine List.mem_map.mpr ⟨sigOf m, hmem, ?_⟩
  show mvec (sigOfAux 12 le_rfl m) = m
  rw [mvec_sigOfAux 12 le_rfl m]
  funext j
  rw [if_pos j.isLt]

theorem certStates_deg_le : certStates.all (fun m => decide (degV m ≤ 24)) = true := by decide

theorem degV_le_of_mem_certStates (m : MV) (hm : m ∈ certStates) : degV m ≤ 24 :=
  of_decide_eq_true ((List.all_eq_true.mp certStates_deg_le) m hm)

theorem degV_sub_evec_add (m : MV) (q : Fin 12) (hq : 1 ≤ m q) :
    degV (m - evec q) + 2 * ((q:ℕ)+1) = degV m := by
  have h1 : ∀ i : Fin 12, i ≠ q → (m - evec q) i = m i := by
    intro i hi
    rw [Pi.sub_apply, evec, Pi.single_eq_of_ne hi 1, tsub_zero]
  have h2 : (m - evec q) q = m q - 1 := by
    rw [Pi.sub_apply, evec, Pi.single_eq_same]
  have hA : degV (m - evec q) = ∑ i ∈ Finset.univ.erase q, 2 * ((i:ℕ)+1) * (m - evec q) i
      + 2 * ((q:ℕ)+1) * (m q - 1) := by
    unfold degV
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ q), h2]
  have hB : degV m = ∑ i ∈ Finset.univ.erase q, 2 * ((i:ℕ)+1) * m i
      + 2 * ((q:ℕ)+1) * m q := by
    unfold degV
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ q)]
  have hC : ∑ i ∈ Finset.univ.erase q, 2 * ((i:ℕ)+1) * (m - evec q) i
      = ∑ i ∈ Finset.univ.erase q, 2 * ((i:ℕ)+1) * m i :=
    Finset.sum_congr rfl (fun i hi => by rw [h1 i (Finset.mem_erase.mp hi).1])
  rw [hA, hB, hC]
  have h3 : 2 * ((q:ℕ)+1) * (m q - 1) + 2 * ((q:ℕ)+1) = 2 * ((q:ℕ)+1) * m q := by
    have h4 : 2 * ((q:ℕ)+1) * (m q - 1) + 2 * ((q:ℕ)+1) * 1 = 2 * ((q:ℕ)+1) * m q := by
      rw [← Nat.mul_add]
      congr 1
      omega
    simpa using h4
  omega

theorem certStates_sub_evec (m : MV) (hm : m ∈ certStates) (v : Fin 12) (hv : 1 ≤ m v) :
    m - evec v ∈ certStates := by
  apply mem_certStates_of_deg
  have h1 := degV_sub_evec_add m v hv
  have h2 := degV_le_of_mem_certStates m hm
  omega

theorem nodup_map_injective {α β : Type*} {l : List α} {f : α → β}
    (h : (l.map f).Nodup) : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b := by
  intro a ha b hb hab
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hb
  have hi' : i < (l.map f).length := by simpa using hi
  have hj' : j < (l.map f).length := by simpa using hj
  have h1 : (l.map f)[i] = (l.map f)[j] := by
    rw [List.getElem_map, List.getElem_map, hia, hjb, hab]
  have h2 : i = j := (h.getElem_inj_iff).mp h1
  subst h2
  exact hia.symm.trans hjb

theorem muVal_inj_class (j : ℕ) (hj : j < 13) {a b : MV} (ha : a ∈ classJ j) (hb : b ∈ classJ j)
    (h : muVal a = muVal b) : a = b :=
  nodup_map_injective (mu_inj_class j hj) a ha b hb h

theorem classJ_deg (j : ℕ) {m : MV} (hm : m ∈ classJ j) : degV m = 2 * j :=
  of_decide_eq_true (List.mem_filter.mp hm).2

theorem classJ_subset (j : ℕ) : ∀ m ∈ classJ j, m ∈ certStates := by
  intro m hm
  exact (List.mem_filter.mp hm).1

theorem degV_even (m : MV) : 2 * (degV m / 2) = degV m := by
  have h : degV m = 2 * (∑ i : Fin 12, ((i:ℕ)+1) * m i) := by
    unfold degV
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [h]
  omega

theorem no_interference (m : MV) (i : ℕ) (hm : m ∈ classJ i) (hi : i < 13)
    (v : Fin 12) (j : ℕ) (hij : i = j + (v:ℕ) + 1) (hv : m v = 0) :
    muVal m < mu v ∨ ∀ m' ∈ classJ j, muVal m' ≠ muVal m - mu v := by
  rcases lt_or_ge (muVal m) (mu v) with hlt | hge
  · exact Or.inl hlt
  right
  intro m' hm' hEq
  have hm'deg : degV m' = 2 * j := classJ_deg j hm'
  have hmdeg : degV m = 2 * i := classJ_deg i hm
  set m'' := m' + evec v with hm''
  have hd'' : degV m'' = degV m := by
    rw [hm'', degV_add_single, hm'deg, hmdeg, hij]
    ring
  have hv_le : mu v ≤ muVal m := hge
  have hmu'' : muVal m'' = muVal m := by
    rw [hm'', muVal_add_single]
    omega
  have hm''cert : m'' ∈ certStates := by
    apply mem_certStates_of_deg
    rw [hd'']
    have := degV_le_of_mem_certStates m (classJ_subset i m hm)
    omega
  have hm''class : m'' ∈ classJ i := by
    simp only [classJ, List.mem_filter]
    refine ⟨hm''cert, ?_⟩
    rw [hd'', hmdeg]
    simp only [decide_eq_true_eq]
  have heq : m'' = m := muVal_inj_class i hi hm''class hm (by rw [hmu''])
  have hv0 : m'' v = m v := by rw [heq]
  rw [hm'', Pi.add_apply] at hv0
  have : (evec v : Fin 12 → ℕ) v = 1 := by simp [evec]
  rw [this, hv] at hv0
  omega

theorem certStates_muVal_le : certStates.all (fun m => decide (muVal m ≤ 204)) = true := by decide

/-- Every state lives at a packed position `≤ 204` (the largest `muVal` of a state). -/
theorem muVal_le_of_mem_certStates (m : MV) (hm : m ∈ certStates) : muVal m ≤ 204 :=
  of_decide_eq_true ((List.all_eq_true.mp certStates_muVal_le) m hm)

theorem mu_pos : (List.finRange 12).all (fun i : Fin 12 => decide (0 < mu i)) = true := by decide

/-- `muVal` vanishes only at the origin. -/
theorem muVal_eq_zero (m : MV) (h : muVal m = 0) : m = 0 := by
  funext i
  have hpos : 0 < mu i := of_decide_eq_true ((List.all_eq_true.mp mu_pos) i (List.mem_finRange i))
  have hsum : (∑ j : Fin 12, mu j * m j) = 0 := by simpa only [muVal] using h
  have hterm : mu i * m i = 0 := (Finset.sum_eq_zero_iff.mp hsum) i (Finset.mem_univ i)
  rcases Nat.mul_eq_zero.mp hterm with h1 | h1
  · exact absurd h1 (Nat.pos_iff_ne_zero.mp hpos)
  · exact h1

end Commons.NumberTheory.MaynardSieve
