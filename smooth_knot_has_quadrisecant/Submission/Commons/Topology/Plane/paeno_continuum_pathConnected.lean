import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Connected.PathConnected

/-
# Peano continua are path connected

A compact, connected, locally connected metric space is path connected.  This is the
classical *Peano continuum* theorem; the proof here is the elementary chain/refinement
construction: approximate the space from `x` to `y` by chains of connected open sets of
meshes tending to `0`, refine uniformly at each step, and read off the limit map
`[0,1] → X` from the nested families of closures.

Main result: `Commons.Topology.Plane.paeno_continuum_pathConnected`.
-/
open Set Metric Filter
open scoped Topology
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Commons.Topology.Peano

variable {X : Type*} [MetricSpace X] [LocallyConnectedSpace X]

lemma exists_isConnected_isOpen_subset {W : Set X} (hW : IsOpen W) {a : X} (ha : a ∈ W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set X, IsOpen U ∧ IsConnected U ∧ a ∈ U ∧ U ⊆ W ∧ Metric.diam U < ε := by
  have hmem : W ∩ Metric.ball a (ε/4) ∈ 𝓝 a :=
    Filter.inter_mem (hW.mem_nhds ha) (Metric.ball_mem_nhds a (by linarith))
  obtain ⟨V, hVsub, hVopen, haV, hVconn⟩ :=
    (locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance a
      (W ∩ Metric.ball a (ε/4)) hmem)
  refine ⟨V, hVopen, hVconn, haV, hVsub.trans (inter_subset_left ..), ?_⟩
  have hbdd : Bornology.IsBounded (Metric.ball a (ε/4)) := Metric.isBounded_ball
  have h1 : Metric.diam V ≤ Metric.diam (Metric.ball a (ε/4)) :=
    Metric.diam_mono (hVsub.trans (inter_subset_right ..)) hbdd
  have h2 : Metric.diam (Metric.ball a (ε/4)) ≤ 2 * (ε/4) := Metric.diam_ball (by linarith)
  linarith

/-- Data of a finite chain of connected open subsets of `W`, all of diameter `< ε`,
with consecutive links meeting, going from `a` to `b`. -/
structure ChainData (W : Set X) (ε : ℝ) (a b : X) where
  k : ℕ
  hk : 0 < k
  U : ℕ → Set X
  isOpen_U : ∀ i, i < k → IsOpen (U i)
  isConn_U : ∀ i, i < k → IsConnected (U i)
  sub_U : ∀ i, i < k → U i ⊆ W
  diam_U : ∀ i, i < k → Metric.diam (U i) < ε
  chain_U : ∀ i, i + 1 < k → (U i ∩ U (i + 1)).Nonempty
  a_mem : a ∈ U 0
  b_mem : b ∈ U (k - 1)

namespace ChainData

variable {W : Set X} {ε : ℝ} {a b c : X}

lemma mem (C : ChainData W ε a b) : b ∈ W := C.sub_U (C.k - 1) (by have := C.hk; omega) C.b_mem

/-- Reflexivity: a chain from `a` to `a` (a single connected open neighbourhood). -/
noncomputable def refl (hW : IsOpen W) (ha : a ∈ W) (hε : 0 < ε) : ChainData W ε a a :=
  let V := Classical.choose (exists_isConnected_isOpen_subset hW ha hε)
  let hV := Classical.choose_spec (exists_isConnected_isOpen_subset hW ha hε)
  { k := 1, hk := one_pos, U := fun _ => V,
    isOpen_U := fun i hi => hV.1,
    isConn_U := fun i hi => hV.2.1,
    sub_U := fun i hi => hV.2.2.2.1,
    diam_U := fun i hi => hV.2.2.2.2,
    chain_U := fun i hi => (not_lt_of_ge (Nat.succ_pos i) hi).elim,
    a_mem := hV.2.2.1,
    b_mem := by simpa using hV.2.2.1 }

/-- Concatenation of chains. -/
def trans (C₁ : ChainData W ε a b) (C₂ : ChainData W ε b c) : ChainData W ε a c :=
  have hk1 : 0 < C₁.k := C₁.hk
  have hk2 : 0 < C₂.k := C₂.hk
  let V : ℕ → Set X := fun i => if i < C₁.k then C₁.U i else C₂.U (i - C₁.k)
  have hV1 : ∀ i, i < C₁.k → V i = C₁.U i := by intro i hi; simp [V, hi]
  have hV2 : ∀ i, ¬ (i < C₁.k) → V i = C₂.U (i - C₁.k) := by intro i hi; simp [V, hi]
  { k := C₁.k + C₂.k
    hk := by omega
    U := V
    isOpen_U := by
      intro i hi
      by_cases h : i < C₁.k
      · rw [hV1 i h]; exact C₁.isOpen_U i h
      · rw [hV2 i h]; exact C₂.isOpen_U (i - C₁.k) (by omega)
    isConn_U := by
      intro i hi
      by_cases h : i < C₁.k
      · rw [hV1 i h]; exact C₁.isConn_U i h
      · rw [hV2 i h]; exact C₂.isConn_U (i - C₁.k) (by omega)
    sub_U := by
      intro i hi
      by_cases h : i < C₁.k
      · rw [hV1 i h]; exact C₁.sub_U i h
      · rw [hV2 i h]; exact C₂.sub_U (i - C₁.k) (by omega)
    diam_U := by
      intro i hi
      by_cases h : i < C₁.k
      · rw [hV1 i h]; exact C₁.diam_U i h
      · rw [hV2 i h]; exact C₂.diam_U (i - C₁.k) (by omega)
    chain_U := by
      intro i hi
      by_cases h : i + 1 < C₁.k
      · rw [hV1 i (by omega), hV1 (i + 1) h]; exact C₁.chain_U i h
      · by_cases h' : i < C₁.k
        · have hi' : i = C₁.k - 1 := by omega
          rw [hV1 i h', hV2 (i + 1) (by omega)]
          have hik : i + 1 - C₁.k = 0 := by omega
          rw [hik]
          exact ⟨b, by rw [hi']; exact C₁.b_mem, C₂.a_mem⟩
        · rw [hV2 i h', hV2 (i + 1) (by omega)]
          have hidx : i + 1 - C₁.k = i - C₁.k + 1 := by omega
          rw [hidx]
          exact C₂.chain_U (i - C₁.k) (by omega)
    a_mem := by rw [hV1 0 C₁.hk]; exact C₁.a_mem
    b_mem := by
      rw [hV2 (C₁.k + C₂.k - 1) (by omega)]
      have : C₁.k + C₂.k - 1 - C₁.k = C₂.k - 1 := by omega
      rw [this]; exact C₂.b_mem }

/-- Extension of a chain ending at `b` by a connected open set `V ∋ z`. -/
def extend (C : ChainData W ε a b) {V : Set X} (hV : IsOpen V) (hVc : IsConnected V)
    (hbV : b ∈ V) (hVW : V ⊆ W) (hVd : Metric.diam V < ε) {z : X} (hzV : z ∈ V) :
    ChainData W ε a z :=
  have hk : 0 < C.k := C.hk
  let V' : ℕ → Set X := fun i => if i < C.k then C.U i else V
  have hV'1 : ∀ i, i < C.k → V' i = C.U i := by intro i hi; simp [V', hi]
  have hV'2 : ∀ i, ¬ (i < C.k) → V' i = V := by intro i hi; simp [V', hi]
  { k := C.k + 1
    hk := by omega
    U := V'
    isOpen_U := by
      intro i hi
      by_cases h : i < C.k
      · rw [hV'1 i h]; exact C.isOpen_U i h
      · rw [hV'2 i h]; exact hV
    isConn_U := by
      intro i hi
      by_cases h : i < C.k
      · rw [hV'1 i h]; exact C.isConn_U i h
      · rw [hV'2 i h]; exact hVc
    sub_U := by
      intro i hi
      by_cases h : i < C.k
      · rw [hV'1 i h]; exact C.sub_U i h
      · rw [hV'2 i h]; exact hVW
    diam_U := by
      intro i hi
      by_cases h : i < C.k
      · rw [hV'1 i h]; exact C.diam_U i h
      · rw [hV'2 i h]; exact hVd
    chain_U := by
      intro i hi
      by_cases h : i + 1 < C.k
      · rw [hV'1 i (by omega), hV'1 (i + 1) h]; exact C.chain_U i h
      · have hik : i = C.k - 1 := by omega
        rw [hV'1 i (by omega), hV'2 (i + 1) h]
        exact ⟨b, by rw [hik]; exact C.b_mem, hbV⟩
    a_mem := by rw [hV'1 0 C.hk]; exact C.a_mem
    b_mem := by rw [hV'2 (C.k + 1 - 1) (by omega)]; simpa using hzV }


/-- Pad a chain to a prescribed length by repeating its last link. -/
noncomputable def pad (C : ChainData W ε a b) (m : ℕ) (hm : C.k ≤ m) : ChainData W ε a b where
  k := m
  hk := lt_of_lt_of_le C.hk hm
  U := fun l => C.U (min l (C.k - 1))
  isOpen_U := fun l hl => C.isOpen_U _ (by have := C.hk; omega)
  isConn_U := fun l hl => C.isConn_U _ (by have := C.hk; omega)
  sub_U := fun l hl => C.sub_U _ (by have := C.hk; omega)
  diam_U := fun l hl => C.diam_U _ (by have := C.hk; omega)
  chain_U := fun l hl => by
    rcases Nat.lt_or_ge (C.k - 1) (l + 1) with h | h
    · rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
      obtain ⟨z, hz⟩ := (C.isConn_U (C.k - 1) (by have := C.hk; omega)).1
      exact ⟨z, hz, hz⟩
    · rw [Nat.min_eq_left (by omega), Nat.min_eq_left h]
      exact C.chain_U l (by omega)
  a_mem := by rw [Nat.min_eq_left (by have := C.hk; omega)]; exact C.a_mem
  b_mem := by rw [Nat.min_eq_right (by omega)]; exact C.b_mem

@[simp] lemma pad_k (C : ChainData W ε a b) (m : ℕ) (hm : C.k ≤ m) : (C.pad m hm).k = m := rfl

end ChainData

lemma isChain_of_isOpen_isPreconnected {W : Set X} (hW : IsOpen W) (hWc : IsPreconnected W)
    {a b : X} (ha : a ∈ W) (hb : b ∈ W) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (ChainData W ε a b) := by
  classical
  suffices h : ∀ b ∈ W, Nonempty (ChainData W ε a b) from h b hb
  intro b hb
  set S : Set X := {b | Nonempty (ChainData W ε a b)} with hS
  have haS : a ∈ S := by
    show Nonempty (ChainData W ε a a)
    exact ⟨ChainData.refl hW ha hε⟩
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro u huS
    obtain ⟨C⟩ := huS
    have huW : u ∈ W := C.mem
    obtain ⟨V, hVopen, hVconn, huV, hVsub, hVdiam⟩ := exists_isConnected_isOpen_subset hW huW hε
    refine mem_of_superset (hVopen.mem_nhds huV) ?_
    intro z hzV
    exact ⟨C.extend hVopen hVconn huV hVsub hVdiam hzV⟩
  have hScopen : IsOpen (W \ S) := by
    rw [isOpen_iff_mem_nhds]
    intro u huS
    obtain ⟨huW, huS'⟩ := huS
    obtain ⟨V, hVopen, hVconn, huV, hVsub, hVdiam⟩ := exists_isConnected_isOpen_subset hW huW hε
    refine mem_of_superset (hVopen.mem_nhds huV) ?_
    intro z hzV
    refine ⟨hVsub hzV, ?_⟩
    rintro ⟨C⟩
    exact huS' ⟨C.extend hVopen hVconn hzV hVsub hVdiam huV⟩
  have hcl : closure S ∩ W ⊆ S := by
    intro x hx
    obtain ⟨hxcl, hxW⟩ := hx
    by_contra hxS
    obtain ⟨y, hy⟩ := mem_closure_iff.1 hxcl (W \ S) hScopen ⟨hxW, hxS⟩
    exact hy.1.2 hy.2
  exact hWc.subset_of_closure_inter_subset hSopen ⟨a, ha, haS⟩ hcl hb



/-- For `K > 0`, the index `j` of the grid interval `(j/K, (j+1)/K]` of the real line
containing `t`, i.e. the least `j` with `t ≤ (j+1)/K`. -/
noncomputable def gridIdx (K : ℕ) (t : ℝ) : ℕ :=
  if h : ∃ j : ℕ, t ≤ ((j : ℝ) + 1) / (K : ℝ) then Nat.find h else 0

lemma gridIdx_last_spec (K : ℕ) (hK : 0 < K) {t : ℝ} (ht : t ≤ 1) :
    t ≤ (((K - 1 : ℕ) : ℝ) + 1) / (K : ℝ) := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hK)
  have hcast : (((K - 1 : ℕ) : ℝ) + 1) = (K : ℝ) := by
    have h : K - 1 + 1 = K := by omega
    rw [← h]; push_cast; ring
  rw [hcast, div_self hK']
  exact ht

lemma gridIdx_exists (K : ℕ) (hK : 0 < K) {t : ℝ} (ht : t ≤ 1) :
    ∃ j : ℕ, t ≤ ((j : ℝ) + 1) / (K : ℝ) :=
  ⟨K - 1, gridIdx_last_spec K hK ht⟩

lemma gridIdx_eq (K : ℕ) (hK : 0 < K) {t : ℝ} (ht : t ≤ 1) :
    gridIdx K t = Nat.find (gridIdx_exists K hK ht) := by
  rw [gridIdx, dif_pos (gridIdx_exists K hK ht)]

lemma gridIdx_spec (K : ℕ) (hK : 0 < K) {t : ℝ} (ht : t ≤ 1) :
    t ≤ ((gridIdx K t : ℝ) + 1) / (K : ℝ) := by
  rw [gridIdx_eq K hK ht]; exact Nat.find_spec (gridIdx_exists K hK ht)

lemma gridIdx_le (K : ℕ) (hK : 0 < K) {t : ℝ} (ht : t ≤ 1) : gridIdx K t ≤ K - 1 := by
  rw [gridIdx_eq K hK ht]
  exact Nat.find_min' (gridIdx_exists K hK ht) (gridIdx_last_spec K hK ht)

lemma gridIdx_min (K : ℕ) (hK : 0 < K) {t : ℝ} (ht : t ≤ 1) {j : ℕ}
    (hj : j < gridIdx K t) : ((j : ℝ) + 1) / (K : ℝ) < t := by
  rw [gridIdx_eq K hK ht] at hj
  exact not_le.mp (Nat.find_min (gridIdx_exists K hK ht) hj)

lemma gridIdx_zero_or_lt (K : ℕ) (hK : 0 < K) {t : ℝ} (ht : t ≤ 1) :
    gridIdx K t = 0 ∨ (gridIdx K t : ℝ) / (K : ℝ) < t := by
  rcases Nat.eq_zero_or_pos (gridIdx K t) with h | h
  · exact Or.inl h
  · right
    have h1 : gridIdx K t - 1 < gridIdx K t := by omega
    have h2 := gridIdx_min K hK ht h1
    have hcast : (((gridIdx K t - 1 : ℕ) : ℝ) + 1) = (gridIdx K t : ℝ) := by
      have h : gridIdx K t - 1 + 1 = gridIdx K t := by omega
      rw [← h]; push_cast; ring
    rwa [hcast] at h2



lemma gridIdx_div (K m : ℕ) (hK : 0 < K) (hm : 0 < m) {t : ℝ} (ht : t ≤ 1) :
    gridIdx (K * m) t / m = gridIdx K t := by
  have hKm : 0 < K * m := Nat.mul_pos hK hm
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hK)
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hm)
  set i := gridIdx K t with hi
  set j := gridIdx (K * m) t with hj
  have hspec_i : t ≤ ((i : ℝ) + 1) / (K : ℝ) := gridIdx_spec K hK ht
  have hlo : i * m ≤ j := by
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · rw [hi0]; simp
    · by_contra hcon
      have hjlt : j < i * m := by omega
      have hstrict : (i : ℝ) / (K : ℝ) < t := by
        rcases gridIdx_zero_or_lt K hK ht with h0 | h0
        · omega
        · exact h0
      have hle : ((j : ℝ) + 1) / ((K * m : ℕ) : ℝ) ≤ (i : ℝ) / (K : ℝ) := by
        have h1 : ((j : ℝ) + 1) / ((K * m : ℕ) : ℝ) ≤ ((i * m : ℕ) : ℝ) / ((K * m : ℕ) : ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          have hle' : j + 1 ≤ i * m := by omega
          exact_mod_cast hle'
        have h2 : ((i * m : ℕ) : ℝ) / ((K * m : ℕ) : ℝ) = (i : ℝ) / (K : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_mul]; field_simp
        rw [h2] at h1; exact h1
      exact (not_le.mpr (lt_of_le_of_lt hle hstrict)) (gridIdx_spec (K * m) hKm ht)
  have hup' : j < (i + 1) * m := by
    rw [hj, gridIdx_eq (K * m) hKm ht]
    have hp : t ≤ (((i * m + m - 1 : ℕ) : ℝ) + 1) / ((K * m : ℕ) : ℝ) := by
      have hcast : (((i * m + m - 1 : ℕ) : ℝ) + 1) = ((i : ℝ) + 1) * (m : ℝ) := by
        calc (((i * m + m - 1 : ℕ) : ℝ) + 1)
            = ((((i * m + m - 1 : ℕ) + 1) : ℕ) : ℝ) := by push_cast; ring
          _ = ((i * m + m : ℕ) : ℝ) := by
                congr 1; omega
          _ = ((i : ℝ) + 1) * (m : ℝ) := by push_cast; ring
      rw [hcast]
      have heq : (((i : ℝ) + 1) * (m : ℝ)) / ((K * m : ℕ) : ℝ) = ((i : ℝ) + 1) / (K : ℝ) := by
        rw [Nat.cast_mul]; field_simp
      rw [heq]; exact hspec_i
    have hle := Nat.find_min' (gridIdx_exists (K * m) hKm ht) hp
    have h2 : (i + 1) * m = i * m + m := by ring
    omega
  exact Nat.div_eq_of_lt_le hlo hup'

lemma gridIdx_adj {K : ℕ} {s t : ℝ} (hK : 0 < K) (hs : s ≤ 1) (ht : t ≤ 1)
    (hst : s ≤ t + 1 / (K : ℝ)) : gridIdx K s ≤ gridIdx K t + 1 := by
  rw [gridIdx_eq K hK hs]
  apply Nat.find_min' (gridIdx_exists K hK hs)
  have hspec := gridIdx_spec K hK ht
  have hcast : (((gridIdx K t + 1 : ℕ) : ℝ) + 1) = ((gridIdx K t : ℝ) + 1) + 1 := by
    push_cast; ring
  rw [hcast, add_div]
  linarith


lemma div_add_one_of_mod_add_one_lt {j m : ℕ} (hm : 0 < m) (h : j % m + 1 < m) :
    (j + 1) / m = j / m := by
  conv_lhs => rw [← Nat.div_add_mod j m]
  rw [show m * (j / m) + j % m + 1 = m * (j / m) + (j % m + 1) from by ring]
  rw [Nat.mul_add_div hm, Nat.div_eq_of_lt h, add_zero]

lemma mod_add_one_of_mod_add_one_lt {j m : ℕ} (hm : 0 < m) (h : j % m + 1 < m) :
    (j + 1) % m = j % m + 1 := by
  conv_lhs => rw [← Nat.div_add_mod j m]
  rw [show m * (j / m) + j % m + 1 = m * (j / m) + (j % m + 1) from by ring]
  rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt h]

lemma div_add_one_of_mod_add_one_eq {j m : ℕ} (hm : 0 < m) (h : j % m + 1 = m) :
    (j + 1) / m = j / m + 1 := by
  conv_lhs => rw [← Nat.div_add_mod j m]
  rw [show m * (j / m) + j % m + 1 = m * (j / m) + (j % m + 1) from by ring]
  rw [h, Nat.mul_add_div hm, Nat.div_self hm]

lemma mod_add_one_of_mod_add_one_eq {j m : ℕ} (hm : 0 < m) (h : j % m + 1 = m) :
    (j + 1) % m = 0 := by
  conv_lhs => rw [← Nat.div_add_mod j m]
  rw [show m * (j / m) + j % m + 1 = m * (j / m) + (j % m + 1) from by ring]
  rw [h, Nat.mul_add_mod_self_left, Nat.mod_self]

lemma mul_sub_one_eq {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    k * m - 1 = (k - 1) * m + (m - 1) := by
  have hk' : k - 1 + 1 = k := by omega
  rw [← hk', Nat.add_mul, Nat.one_mul]
  exact Nat.add_sub_assoc hm _

lemma div_mul_sub_one {k m : ℕ} (hk : 0 < k) (hm : 0 < m) : (k * m - 1) / m = k - 1 := by
  rw [mul_sub_one_eq hk hm, Nat.mul_comm (k - 1) m, Nat.mul_add_div hm]
  rw [Nat.div_eq_of_lt (by omega : m - 1 < m), add_zero]

lemma mod_mul_sub_one {k m : ℕ} (hk : 0 < k) (hm : 0 < m) : (k * m - 1) % m = m - 1 := by
  rw [mul_sub_one_eq hk hm, Nat.mul_comm (k - 1) m, Nat.mul_add_mod_self_left]
  rw [Nat.mod_eq_of_lt (by omega : m - 1 < m)]



/-! ## The refinement stages -/

/-- A `Stage` collects the data of one approximation level: a finite chain `U 0, …, U (k-1)`
of connected open sets of diameter `< ε`, consecutive ones meeting, from `x` to `y`. -/
structure Stage (X : Type*) [MetricSpace X] (ε : ℝ) where
  x : X
  y : X
  k : ℕ
  hk : 0 < k
  U : ℕ → Set X
  isOpen_U : ∀ i, i < k → IsOpen (U i)
  isConn_U : ∀ i, i < k → IsConnected (U i)
  chain_U : ∀ i, i + 1 < k → (U i ∩ U (i + 1)).Nonempty
  x_mem : x ∈ U 0
  y_mem : y ∈ U (k - 1)
  diam_U : ∀ i, i < k → Metric.diam (U i) < ε

namespace Stage

variable {ε : ℝ} {D : Stage X ε}

/-- The `i`-th junction point: `x`, a point of `U (i-1) ∩ U i`, or `y`. -/
noncomputable def junc (D : Stage X ε) (i : ℕ) : X :=
  if h : i = 0 then D.x
  else if h2 : i < D.k then (D.chain_U (i - 1) (by have := D.hk; omega)).some
  else D.y

lemma junc_zero (D : Stage X ε) : D.junc 0 = D.x := by
  rw [junc, dif_pos rfl]

lemma junc_last (D : Stage X ε) : D.junc D.k = D.y := by
  rw [junc, dif_neg (by have := D.hk; omega), dif_neg (by omega)]

lemma junc_mem (D : Stage X ε) {i : ℕ} (hi0 : 0 < i) (hik : i < D.k) :
    D.junc i ∈ D.U (i - 1) ∩ D.U i := by
  rw [junc, dif_neg (by omega), dif_pos hik]
  have h := (D.chain_U (i - 1) (by have := D.hk; omega)).some_mem
  have hc : (i - 1) + 1 = i := by omega
  simpa [hc] using h

lemma junc_mem_U (D : Stage X ε) {i : ℕ} (hik : i < D.k) : D.junc i ∈ D.U i := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · rw [h0, junc_zero]; exact D.x_mem
  · exact (D.junc_mem hpos hik).2

lemma junc_succ_mem_U (D : Stage X ε) {i : ℕ} (hik : i < D.k) :
    D.junc (i + 1) ∈ D.U i := by
  by_cases h : i + 1 < D.k
  · exact (D.junc_mem (Nat.succ_pos i) h).1
  · have hk : i + 1 = D.k := by omega
    have hi : i = D.k - 1 := by omega
    rw [hk, junc_last, hi]
    exact D.y_mem

lemma div_lt_of_lt_mul' {j m k : ℕ} (h : j < k * m) : j / m < k :=
  Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])

/-- The chain in block `i`, connecting the junction points `D.junc i` and `D.junc (i+1)`. -/
noncomputable def blockChain (D : Stage X ε) (ε' : ℝ) (hε' : 0 < ε') (i : Fin D.k) :
    ChainData (D.U i.1) ε' (D.junc i.1) (D.junc (i.1 + 1)) :=
  Classical.choice (isChain_of_isOpen_isPreconnected (D.isOpen_U i.1 i.2)
    (D.isConn_U i.1 i.2).2 (D.junc_mem_U i.2) (D.junc_succ_mem_U i.2) hε')

/-- The uniform block length of the refinement: the maximal length of the block chains. -/
noncomputable def blockLen (D : Stage X ε) (ε' : ℝ) (hε' : 0 < ε') : ℕ :=
  (Finset.univ : Finset (Fin D.k)).sup (fun i => (D.blockChain ε' hε' i).k)

lemma blockChain_k_le (D : Stage X ε) (ε' : ℝ) (hε' : 0 < ε') (i : Fin D.k) :
    (D.blockChain ε' hε' i).k ≤ D.blockLen ε' hε' :=
  Finset.le_sup (f := fun t : Fin D.k => (D.blockChain ε' hε' t).k) (Finset.mem_univ i)

lemma one_le_blockLen (D : Stage X ε) (ε' : ℝ) (hε' : 0 < ε') : 1 ≤ D.blockLen ε' hε' := by
  have h := Finset.le_sup (f := fun t : Fin D.k => (D.blockChain ε' hε' t).k)
    (Finset.mem_univ (⟨0, D.hk⟩ : Fin D.k))
  exact le_trans (D.blockChain ε' hε' ⟨0, D.hk⟩).hk h

lemma blockLen_pos (D : Stage X ε) (ε' : ℝ) (hε' : 0 < ε') : 0 < D.blockLen ε' hε' :=
  lt_of_lt_of_le Nat.zero_lt_one (D.one_le_blockLen ε' hε')

/-- The block chain padded to the uniform block length. -/
noncomputable def padBlock (D : Stage X ε) (ε' : ℝ) (hε' : 0 < ε') (i : Fin D.k) :
    ChainData (D.U i.1) ε' (D.junc i.1) (D.junc (i.1 + 1)) :=
  (D.blockChain ε' hε' i).pad (D.blockLen ε' hε') (D.blockChain_k_le ε' hε' i)

@[simp] lemma padBlock_k (D : Stage X ε) (ε' : ℝ) (hε' : 0 < ε') (i : Fin D.k) :
    (D.padBlock ε' hε' i).k = D.blockLen ε' hε' := rfl

/-- The `j`-th set of the refined stage: the `(j % m)`-th set of the padded chain of
block `j / m`. -/
noncomputable def refineU (D : Stage X ε) (ε' : ℝ) (hε' : 0 < ε') (j : ℕ) : Set X :=
  if h : j < D.k * D.blockLen ε' hε' then
    (D.padBlock ε' hε' ⟨j / D.blockLen ε' hε', div_lt_of_lt_mul' h⟩).U
      (j % D.blockLen ε' hε')
  else univ

lemma refineU_eq (D : Stage X ε) (ε' : ℝ) (hε' : 0 < ε') {j : ℕ}
    (hj : j < D.k * D.blockLen ε' hε') (h : j / D.blockLen ε' hε' < D.k) :
    D.refineU ε' hε' j =
      (D.padBlock ε' hε' ⟨j / D.blockLen ε' hε', h⟩).U (j % D.blockLen ε' hε') := by
  rw [refineU, dif_pos hj]

/-- Membership in the refined stage through explicit block index, sub-index and proofs. -/
lemma refineU_eq' (D : Stage X ε) (ε' : ℝ) (hε' : 0 < ε') {j i l : ℕ}
    (hj : j < D.k * D.blockLen ε' hε') (hdiv : j / D.blockLen ε' hε' = i)
    (hi : i < D.k) (hmod : j % D.blockLen ε' hε' = l) :
    D.refineU ε' hε' j = (D.padBlock ε' hε' ⟨i, hi⟩).U l := by
  rw [D.refineU_eq ε' hε' hj (hdiv ▸ hi)]
  have hfin : (⟨j / D.blockLen ε' hε', hdiv ▸ hi⟩ : Fin D.k) = ⟨i, hi⟩ := Fin.ext hdiv
  rw [hfin, hmod]

lemma sub_refineU (D : Stage X ε) (ε' : ℝ) (hε' : 0 < ε') {j : ℕ}
    (hj : j < D.k * D.blockLen ε' hε') :
    D.refineU ε' hε' j ⊆ D.U (j / D.blockLen ε' hε') := by
  rw [refineU, dif_pos hj]
  exact (D.padBlock ε' hε' ⟨j / D.blockLen ε' hε', div_lt_of_lt_mul' hj⟩).sub_U _
    (Nat.mod_lt _ (D.blockLen_pos ε' hε'))

lemma isOpen_refineU (D : Stage X ε) (ε' : ℝ) (hε' : 0 < ε') {j : ℕ}
    (hj : j < D.k * D.blockLen ε' hε') : IsOpen (D.refineU ε' hε' j) := by
  rw [refineU, dif_pos hj]
  exact (D.padBlock ε' hε' ⟨j / D.blockLen ε' hε', div_lt_of_lt_mul' hj⟩).isOpen_U _
    (Nat.mod_lt _ (D.blockLen_pos ε' hε'))

lemma isConn_refineU (D : Stage X ε) (ε' : ℝ) (hε' : 0 < ε') {j : ℕ}
    (hj : j < D.k * D.blockLen ε' hε') : IsConnected (D.refineU ε' hε' j) := by
  rw [refineU, dif_pos hj]
  exact (D.padBlock ε' hε' ⟨j / D.blockLen ε' hε', div_lt_of_lt_mul' hj⟩).isConn_U _
    (Nat.mod_lt _ (D.blockLen_pos ε' hε'))

lemma diam_refineU (D : Stage X ε) (ε' : ℝ) (hε' : 0 < ε') {j : ℕ}
    (hj : j < D.k * D.blockLen ε' hε') : Metric.diam (D.refineU ε' hε' j) < ε' := by
  rw [refineU, dif_pos hj]
  exact (D.padBlock ε' hε' ⟨j / D.blockLen ε' hε', div_lt_of_lt_mul' hj⟩).diam_U _
    (Nat.mod_lt _ (D.blockLen_pos ε' hε'))

/-- The `j = i * m`-th set of the refined stage contains the junction point `D.junc i`. -/
lemma junc_mem_refineU_left (D : Stage X ε) (ε' : ℝ) (hε' : 0 < ε') (i : Fin D.k) :
    D.junc i.1 ∈ D.refineU ε' hε' (i.1 * D.blockLen ε' hε') := by
  have hm : 0 < D.blockLen ε' hε' := D.blockLen_pos ε' hε'
  have hdiv : i.1 * D.blockLen ε' hε' / D.blockLen ε' hε' = i.1 := Nat.mul_div_cancel _ hm
  have hmod : i.1 * D.blockLen ε' hε' % D.blockLen ε' hε' = 0 := by
    rw [Nat.mul_comm]; exact Nat.mul_mod_right _ _
  rw [D.refineU_eq' ε' hε' (j := i.1 * D.blockLen ε' hε')
      (Nat.mul_lt_mul_of_pos_right i.2 hm) hdiv i.2 hmod]
  exact (D.padBlock ε' hε' i).a_mem

/-- The `j = i * m + (m-1)`-th set of the refined stage contains `D.junc (i+1)`. -/
lemma junc_mem_refineU_right (D : Stage X ε) (ε' : ℝ) (hε' : 0 < ε') (i : Fin D.k) :
    D.junc (i.1 + 1) ∈
      D.refineU ε' hε' (i.1 * D.blockLen ε' hε' + (D.blockLen ε' hε' - 1)) := by
  have hm : 0 < D.blockLen ε' hε' := D.blockLen_pos ε' hε'
  have hlt : i.1 * D.blockLen ε' hε' + (D.blockLen ε' hε' - 1) < D.k * D.blockLen ε' hε' := by
    have h1 : i.1 * D.blockLen ε' hε' + (D.blockLen ε' hε' - 1) <
        i.1 * D.blockLen ε' hε' + D.blockLen ε' hε' := by omega
    have h2 : i.1 * D.blockLen ε' hε' + D.blockLen ε' hε' =
        (i.1 + 1) * D.blockLen ε' hε' := by ring
    have h3 : (i.1 + 1) * D.blockLen ε' hε' ≤ D.k * D.blockLen ε' hε' :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt i.2)
    omega
  have hdiv : (i.1 * D.blockLen ε' hε' + (D.blockLen ε' hε' - 1)) / D.blockLen ε' hε' = i.1 := by
    have h : i.1 * D.blockLen ε' hε' + (D.blockLen ε' hε' - 1) =
        D.blockLen ε' hε' * i.1 + (D.blockLen ε' hε' - 1) := by rw [Nat.mul_comm]
    rw [h, Nat.mul_add_div hm, Nat.div_eq_of_lt (by omega : _ - 1 < _), add_zero]
  have hmod : (i.1 * D.blockLen ε' hε' + (D.blockLen ε' hε' - 1)) %
      D.blockLen ε' hε' = D.blockLen ε' hε' - 1 := by
    have h : i.1 * D.blockLen ε' hε' + (D.blockLen ε' hε' - 1) =
        D.blockLen ε' hε' * i.1 + (D.blockLen ε' hε' - 1) := by rw [Nat.mul_comm]
    rw [h, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega : _ - 1 < _)]
  rw [D.refineU_eq' ε' hε' (j := i.1 * D.blockLen ε' hε' + (D.blockLen ε' hε' - 1)) hlt hdiv i.2 hmod]
  exact (D.padBlock ε' hε' i).b_mem

/-- The refined stage. -/
noncomputable def refine (D : Stage X ε) (ε' : ℝ) (hε' : 0 < ε') : Stage X ε' where
  x := D.x
  y := D.y
  k := D.k * D.blockLen ε' hε'
  hk := Nat.mul_pos D.hk (D.blockLen_pos ε' hε')
  U := D.refineU ε' hε'
  isOpen_U := fun i hi => D.isOpen_refineU ε' hε' hi
  isConn_U := fun i hi => D.isConn_refineU ε' hε' hi
  chain_U := by
    intro j hj
    have hm : 0 < D.blockLen ε' hε' := D.blockLen_pos ε' hε'
    have hj1 : j < D.k * D.blockLen ε' hε' := by omega
    by_cases hcase : j % D.blockLen ε' hε' + 1 < D.blockLen ε' hε'
    · have hdiv1 : (j + 1) / D.blockLen ε' hε' = j / D.blockLen ε' hε' :=
        div_add_one_of_mod_add_one_lt hm hcase
      have hmod1 : (j + 1) % D.blockLen ε' hε' = j % D.blockLen ε' hε' + 1 :=
        mod_add_one_of_mod_add_one_lt hm hcase
      rw [D.refineU_eq' ε' hε' (j := j) (i := j / D.blockLen ε' hε') hj1 rfl
            (div_lt_of_lt_mul' hj1) (l := j % D.blockLen ε' hε') rfl,
          D.refineU_eq' ε' hε' (j := j + 1) (i := j / D.blockLen ε' hε') hj hdiv1
            (div_lt_of_lt_mul' hj1) (l := j % D.blockLen ε' hε' + 1) hmod1]
      exact (D.padBlock ε' hε' ⟨j / D.blockLen ε' hε', div_lt_of_lt_mul' hj1⟩).chain_U
        (j % D.blockLen ε' hε') hcase
    · have hmod : j % D.blockLen ε' hε' + 1 = D.blockLen ε' hε' := by
        have := Nat.mod_lt j hm; omega
      have hdiv1 : (j + 1) / D.blockLen ε' hε' = j / D.blockLen ε' hε' + 1 :=
        div_add_one_of_mod_add_one_eq hm hmod
      have hmod1 : (j + 1) % D.blockLen ε' hε' = 0 := mod_add_one_of_mod_add_one_eq hm hmod
      have hnext : j / D.blockLen ε' hε' + 1 < D.k := by
        have h1 : j = D.blockLen ε' hε' * (j / D.blockLen ε' hε') + j % D.blockLen ε' hε' :=
          (Nat.div_add_mod j (D.blockLen ε' hε')).symm
        have h3 : j + 1 = D.blockLen ε' hε' * (j / D.blockLen ε' hε') + D.blockLen ε' hε' := by
          conv_lhs => rw [h1]
          rw [Nat.add_assoc, hmod]
        have h4 : (j / D.blockLen ε' hε' + 1) * D.blockLen ε' hε' =
            D.blockLen ε' hε' * (j / D.blockLen ε' hε') + D.blockLen ε' hε' := by ring
        exact Nat.lt_of_mul_lt_mul_right (by rw [h4, ← h3]; exact hj)
      rw [D.refineU_eq' ε' hε' (j := j) (i := j / D.blockLen ε' hε') hj1 rfl
            (div_lt_of_lt_mul' hj1) (l := j % D.blockLen ε' hε') rfl,
          D.refineU_eq' ε' hε' (j := j + 1) (i := j / D.blockLen ε' hε' + 1) hj hdiv1 hnext
            (l := 0) hmod1]
      have hjmod : j % D.blockLen ε' hε' = D.blockLen ε' hε' - 1 := by omega
      rw [hjmod]
      exact ⟨D.junc (j / D.blockLen ε' hε' + 1),
        (D.padBlock ε' hε' ⟨j / D.blockLen ε' hε', div_lt_of_lt_mul' hj1⟩).b_mem,
        (D.padBlock ε' hε' ⟨j / D.blockLen ε' hε' + 1, hnext⟩).a_mem⟩
  x_mem := by
    have h : D.junc 0 ∈ D.refineU ε' hε' 0 := by
      rw [D.refineU_eq' ε' hε' (j := 0) (i := 0)
        (by exact Nat.mul_pos D.hk (D.blockLen_pos ε' hε')) (Nat.zero_div _) D.hk (l := 0)
        (Nat.zero_mod _)]
      exact (D.padBlock ε' hε' ⟨0, D.hk⟩).a_mem
    simpa only [D.junc_zero] using h
  y_mem := by
    have hm : 0 < D.blockLen ε' hε' := D.blockLen_pos ε' hε'
    have h : D.junc D.k ∈ D.refineU ε' hε' (D.k * D.blockLen ε' hε' - 1) := by
      rw [D.refineU_eq' ε' hε' (j := D.k * D.blockLen ε' hε' - 1) (i := D.k - 1)
        (Nat.sub_one_lt (Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp D.hk) (Nat.pos_iff_ne_zero.mp hm)))
        (div_mul_sub_one D.hk hm) (Nat.sub_one_lt_of_lt D.hk)
        (l := D.blockLen ε' hε' - 1) (mod_mul_sub_one D.hk hm)]
      have hb := (D.padBlock ε' hε' ⟨D.k - 1, Nat.sub_one_lt_of_lt D.hk⟩).b_mem
      have hk1 : D.k - 1 + 1 = D.k := by have := D.hk; omega
      simpa only [Fin.val_mk, hk1, D.junc_last, Stage.padBlock_k] using hb
    simpa only [D.junc_last] using h
  diam_U := fun i hi => D.diam_refineU ε' hε' hi

end Stage



section Main

variable [CompactSpace X] [ConnectedSpace X]

/-- Nested nonempty closed sets of diameter tending to `0` in a compact metric space
have a unique common point. -/
lemma unique_mem_iInter_nested (C : ℕ → Set X) (hclosed : ∀ n, IsClosed (C n))
    (hanti : ∀ i j, i ≤ j → C j ⊆ C i) (hne : ∀ n, (C n).Nonempty)
    (hdiam : ∀ ε : ℝ, 0 < ε → ∃ n, Metric.diam (C n) < ε) :
    ∃! x : X, x ∈ ⋂ n, C n := by
  classical
  have hbdd : Bornology.IsBounded (⋂ n, C n) :=
    isCompact_univ.isBounded.subset (subset_univ _)
  have hnonempty : (⋂ n, C n).Nonempty := by
    have h := isCompact_univ.inter_iInter_nonempty C hclosed (fun u => ?_)
    · simpa using h
    · have hsub : C (u.sup id) ⊆ ⋂ i ∈ u, C i := by
        intro z hz
        rw [Set.mem_iInter]
        intro i
        rw [Set.mem_iInter]
        intro hi
        exact hanti i (u.sup id) (Finset.le_sup (f := id) hi) hz
      obtain ⟨z, hz⟩ := hne (u.sup id)
      exact ⟨z, mem_univ z, hsub hz⟩
  have hdiam0 : Metric.diam (⋂ n, C n) = 0 := by
    refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) Metric.diam_nonneg
    obtain ⟨N, hN⟩ := hdiam ε hε
    have h1 : Metric.diam (⋂ n, C n) ≤ Metric.diam (C N) :=
      Metric.diam_mono (Set.iInter_subset C N)
        (isCompact_univ.isBounded.subset (subset_univ _))
    linarith
  obtain ⟨x, hx⟩ := hnonempty
  refine ⟨x, hx, fun y hy => ?_⟩
  have h1 : dist y x ≤ Metric.diam (⋂ n, C n) := Metric.dist_le_diam_of_mem hbdd hy hx
  rw [hdiam0] at h1
  exact dist_eq_zero.mp (le_antisymm h1 dist_nonneg)

end Main


section Stages

variable [CompactSpace X] [ConnectedSpace X]

noncomputable def eps (n : ℕ) : ℝ := (Metric.diam (univ : Set X) + 1) * (1/2) ^ n

lemma eps_pos (n : ℕ) : 0 < eps (X := X) n := by
  have h : (0:ℝ) < Metric.diam (univ : Set X) + 1 := by
    have := Metric.diam_nonneg (s := (univ : Set X)); linarith
  exact mul_pos h (pow_pos (by norm_num) n)

lemma eps_zero : eps (X := X) 0 = Metric.diam (univ : Set X) + 1 := by simp [eps]

lemma eps_succ (n : ℕ) : eps (X := X) (n+1) = eps (X := X) n * (1/2) := by
  simp only [eps, pow_succ]; ring

lemma eps_tendsto_zero : Tendsto (fun n : ℕ => eps (X := X) n) atTop (nhds 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (1:ℝ)/2 < 1 by norm_num)
  simpa only [eps, mul_zero] using h.const_mul (Metric.diam (univ : Set X) + 1)

noncomputable def stage0 (x y : X) : Stage X (eps (X := X) 0) where
  x := x
  y := y
  k := 1
  hk := one_pos
  U := fun _ => univ
  isOpen_U := fun i hi => isOpen_univ
  isConn_U := fun i hi => isConnected_univ
  chain_U := fun i hi => absurd hi (by omega)
  x_mem := mem_univ x
  y_mem := mem_univ y
  diam_U := fun i hi => by
    rw [eps_zero]
    exact lt_add_one _

noncomputable def stages (x y : X) : (n : ℕ) → Stage X (eps (X := X) n)
  | 0 => stage0 x y
  | n + 1 => (stages x y n).refine (eps (n+1)) (eps_pos (n+1))

lemma stages_succ (x y : X) (n : ℕ) :
    stages x y (n+1) = (stages x y n).refine (eps (X := X) (n+1)) (eps_pos (n+1)) := by
  rw [stages]

lemma stages_k_succ (x y : X) (n : ℕ) :
    (stages x y (n+1)).k = (stages x y n).k * (stages x y n).blockLen (eps (X := X) (n+1))
      (eps_pos (n+1)) := by
  rw [stages_succ x y]; rfl

end Stages


section Limit

variable [CompactSpace X] [ConnectedSpace X] (x y : X)

lemma gridIdx_zero (K : ℕ) : gridIdx K 0 = 0 := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp [gridIdx]
  · rw [gridIdx_eq K hK (by norm_num : (0:ℝ) ≤ 1)]
    exact Nat.eq_zero_of_le_zero (Nat.find_min' _
      (show (0:ℝ) ≤ (((0:ℕ):ℝ) + 1) / (K:ℝ) by positivity))

lemma gridIdx_one (K : ℕ) (hK : 0 < K) : gridIdx K 1 = K - 1 := by
  have h := gridIdx_le K hK (le_refl (1:ℝ))
  refine le_antisymm h ?_
  rw [gridIdx_eq K hK (le_refl (1:ℝ)), Nat.le_find_iff]
  intro m hm
  rw [not_le, div_lt_one (by exact_mod_cast hK)]
  have : m + 1 < K := by omega
  exact_mod_cast this

lemma stages_x (x y : X) (n : ℕ) : (stages x y n).x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stages_succ x y]; exact ih

lemma stages_y (x y : X) (n : ℕ) : (stages x y n).y = y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stages_succ x y]; exact ih

noncomputable def cell (n : ℕ) (t : ℝ) : ℕ := gridIdx (stages x y n).k t

lemma cell_lt (n : ℕ) {t : ℝ} (ht : t ≤ 1) : cell x y n t < (stages x y n).k :=
  lt_of_le_of_lt (gridIdx_le (stages x y n).k (stages x y n).hk ht)
    (Nat.sub_one_lt_of_lt (stages x y n).hk)

lemma cell_zero (n : ℕ) : cell x y n 0 = 0 := gridIdx_zero _

lemma cell_one (n : ℕ) : cell x y n 1 = (stages x y n).k - 1 := gridIdx_one _ (stages x y n).hk

noncomputable def cellSet (n : ℕ) (t : ℝ) : Set X := (stages x y n).U (cell x y n t)
noncomputable def cellCl (n : ℕ) (t : ℝ) : Set X := closure (cellSet x y n t)

lemma cellSet_nonempty (n : ℕ) {t : ℝ} (ht : t ≤ 1) : (cellSet x y n t).Nonempty :=
  ((stages x y n).isConn_U _ (cell_lt x y n ht)).1

lemma cellCl_nonempty (n : ℕ) {t : ℝ} (ht : t ≤ 1) : (cellCl x y n t).Nonempty :=
  (cellSet_nonempty x y n ht).mono subset_closure

lemma cellSet_succ_subset (n : ℕ) {t : ℝ} (ht : t ≤ 1) :
    cellSet x y (n+1) t ⊆ cellSet x y n t := by
  have hcell : cell x y (n+1) t < (stages x y (n+1)).k := cell_lt x y (n+1) ht
  rw [stages_k_succ x y] at hcell
  have hdiv : cell x y (n+1) t / (stages x y n).blockLen (eps (X := X) (n+1))
        (eps_pos (X := X) (n+1)) = cell x y n t := by
    show gridIdx (stages x y (n+1)).k t / (stages x y n).blockLen (eps (X := X) (n+1))
        (eps_pos (X := X) (n+1)) = gridIdx (stages x y n).k t
    rw [stages_k_succ x y]
    exact gridIdx_div _ _ (stages x y n).hk
      ((stages x y n).blockLen_pos (eps (X := X) (n+1)) (eps_pos (X := X) (n+1))) ht
  intro z hz
  rw [cellSet] at hz ⊢
  rw [stages_succ x y] at hz
  have h2 := (stages x y n).sub_refineU (eps (X := X) (n+1)) (eps_pos (X := X) (n+1)) hcell hz
  rwa [hdiv] at h2

lemma cellSet_anti {i j : ℕ} (hij : i ≤ j) {t : ℝ} (ht : t ≤ 1) :
    cellSet x y j t ⊆ cellSet x y i t := by
  induction hij with
  | refl => exact Subset.rfl
  | step h ih => exact (cellSet_succ_subset x y _ ht).trans ih

lemma cellCl_anti {i j : ℕ} (hij : i ≤ j) {t : ℝ} (ht : t ≤ 1) :
    cellCl x y j t ⊆ cellCl x y i t :=
  closure_mono (cellSet_anti x y hij ht)

lemma diam_cellCl (n : ℕ) {t : ℝ} (ht : t ≤ 1) : Metric.diam (cellCl x y n t) < eps (X := X) n := by
  rw [cellCl, Metric.diam_closure]
  exact (stages x y n).diam_U _ (cell_lt x y n ht)

lemma cellCl_unique (t : ℝ) (ht : t ≤ 1) : ∃! z : X, z ∈ ⋂ n, cellCl x y n t := by
  refine unique_mem_iInter_nested _ (fun n => isClosed_closure) (fun i j hij => cellCl_anti x y hij ht)
    (fun n => cellCl_nonempty x y n ht) ?_
  intro ε hε
  have hev : ∀ᶠ n in Filter.atTop, eps (X := X) n < ε :=
    (eps_tendsto_zero (X := X)).eventually (isOpen_Iio.mem_nhds hε)
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨n, lt_trans (diam_cellCl x y n ht) hn⟩

noncomputable def fAt (t : ℝ) (ht : t ≤ 1) : X := (cellCl_unique x y t ht).choose

lemma fAt_mem (t : ℝ) (ht : t ≤ 1) (n : ℕ) : fAt x y t ht ∈ cellCl x y n t :=
  Set.mem_iInter.mp (cellCl_unique x y t ht).choose_spec.1 n

lemma cellSet_inter (n : ℕ) {s t : ℝ} (hs : s ≤ 1) (ht : t ≤ 1)
    (h : cell x y n s ≤ cell x y n t + 1) (h' : cell x y n t ≤ cell x y n s + 1) :
    (cellSet x y n s ∩ cellSet x y n t).Nonempty := by
  rcases Nat.lt_or_ge (cell x y n s) (cell x y n t) with hlt | hge
  · have hlt' : cell x y n s + 1 = cell x y n t := by omega
    have hk : cell x y n s + 1 < (stages x y n).k := by rw [hlt']; exact cell_lt x y n ht
    obtain ⟨z, hz1, hz2⟩ := (stages x y n).chain_U (cell x y n s) hk
    exact ⟨z, by rw [cellSet]; exact hz1, by rw [cellSet, ← hlt']; exact hz2⟩
  · rcases Nat.lt_or_ge (cell x y n t) (cell x y n s) with hlt | hge'
    · have hlt' : cell x y n t + 1 = cell x y n s := by omega
      have hk : cell x y n t + 1 < (stages x y n).k := by rw [hlt']; exact cell_lt x y n hs
      obtain ⟨z, hz1, hz2⟩ := (stages x y n).chain_U (cell x y n t) hk
      exact ⟨z, by rw [cellSet, ← hlt']; exact hz2, by rw [cellSet]; exact hz1⟩
    · have heq : cell x y n s = cell x y n t := le_antisymm hge' hge
      obtain ⟨z, hz⟩ := cellSet_nonempty x y n hs
      refine ⟨z, hz, ?_⟩
      rw [cellSet, ← heq, ← cellSet]
      exact hz

lemma dist_fAt_le (n : ℕ) {s t : ℝ} (hs : s ≤ 1) (ht : t ≤ 1)
    (hst : |s - t| ≤ 1 / ((stages x y n).k : ℝ)) :
    dist (fAt x y s hs) (fAt x y t ht) ≤ 2 * eps (X := X) n := by
  obtain ⟨h1, h2⟩ := abs_le.mp hst
  have ha : cell x y n s ≤ cell x y n t + 1 :=
    gridIdx_adj (stages x y n).hk hs ht (by linarith)
  have hb : cell x y n t ≤ cell x y n s + 1 :=
    gridIdx_adj (stages x y n).hk ht hs (by linarith)
  obtain ⟨z, hz1, hz2⟩ := cellSet_inter x y n hs ht ha hb
  have hmem1 : fAt x y s hs ∈ cellCl x y n s := fAt_mem x y s hs n
  have hmem2 : fAt x y t ht ∈ cellCl x y n t := fAt_mem x y t ht n
  have hbdd : Bornology.IsBounded (cellCl x y n s ∪ cellCl x y n t) :=
    isCompact_univ.isBounded.subset (subset_univ _)
  have hdist : dist (fAt x y s hs) (fAt x y t ht) ≤
      Metric.diam (cellCl x y n s ∪ cellCl x y n t) :=
    Metric.dist_le_diam_of_mem hbdd (Or.inl hmem1) (Or.inr hmem2)
  have hdiam : Metric.diam (cellCl x y n s ∪ cellCl x y n t) ≤ 2 * eps (X := X) n := by
    have hu := Metric.diam_union (subset_closure hz1) (subset_closure hz2)
    simp only [dist_self, add_zero] at hu
    rw [← cellCl, ← cellCl] at hu
    linarith [hu, diam_cellCl x y n hs, diam_cellCl x y n ht]
  linarith

end Limit



section Final

variable [CompactSpace X] [ConnectedSpace X] (x y : X)

noncomputable def fI (t : unitInterval) : X := fAt x y t.val t.property.2

lemma fAt_proof_irrel (t : ℝ) (h1 h2 : t ≤ 1) : fAt x y t h1 = fAt x y t h2 := by
  have h : cellCl_unique x y t h1 = cellCl_unique x y t h2 := Subsingleton.elim _ _
  unfold fAt
  rw [h]

lemma fAt_zero : fAt x y 0 (by norm_num : (0:ℝ) ≤ 1) = x := by
  apply dist_eq_zero.mp
  refine le_antisymm (le_of_forall_pos_lt_add fun δ hδ => ?_) dist_nonneg
  have hev : ∀ᶠ n in Filter.atTop, eps (X := X) n < δ :=
    (eps_tendsto_zero (X := X)).eventually (isOpen_Iio.mem_nhds hδ)
  obtain ⟨n, hn⟩ := hev.exists
  have h1 : fAt x y 0 (by norm_num : (0:ℝ) ≤ 1) ∈ cellCl x y n 0 :=
    fAt_mem x y 0 (by norm_num : (0:ℝ) ≤ 1) n
  have h2 : x ∈ cellCl x y n 0 := by
    rw [cellCl, cellSet, cell_zero x y n]
    refine subset_closure ?_
    have hm : (stages x y n).x ∈ (stages x y n).U 0 := (stages x y n).x_mem
    rwa [stages_x x y n] at hm
  have hbdd : Bornology.IsBounded (cellCl x y n 0) :=
    isCompact_univ.isBounded.subset (subset_univ _)
  have hd := Metric.dist_le_diam_of_mem hbdd h1 h2
  have hd2 := diam_cellCl x y n (by norm_num : (0:ℝ) ≤ 1)
  linarith

lemma fAt_one : fAt x y 1 (by norm_num : (1:ℝ) ≤ 1) = y := by
  apply dist_eq_zero.mp
  refine le_antisymm (le_of_forall_pos_lt_add fun δ hδ => ?_) dist_nonneg
  have hev : ∀ᶠ n in Filter.atTop, eps (X := X) n < δ :=
    (eps_tendsto_zero (X := X)).eventually (isOpen_Iio.mem_nhds hδ)
  obtain ⟨n, hn⟩ := hev.exists
  have h1 : fAt x y 1 (by norm_num : (1:ℝ) ≤ 1) ∈ cellCl x y n 1 :=
    fAt_mem x y 1 (by norm_num : (1:ℝ) ≤ 1) n
  have h2 : y ∈ cellCl x y n 1 := by
    rw [cellCl, cellSet, cell_one x y n]
    refine subset_closure ?_
    have hm : (stages x y n).y ∈ (stages x y n).U ((stages x y n).k - 1) := (stages x y n).y_mem
    rwa [stages_y x y n] at hm
  have hbdd : Bornology.IsBounded (cellCl x y n 1) :=
    isCompact_univ.isBounded.subset (subset_univ _)
  have hd := Metric.dist_le_diam_of_mem hbdd h1 h2
  have hd2 := diam_cellCl x y n (by norm_num : (1:ℝ) ≤ 1)
  linarith

lemma continuous_fI : Continuous (fI x y) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  have hev : ∀ᶠ n in Filter.atTop, 2 * eps (X := X) n < ε := by
    have h2 : Filter.Tendsto (fun n : ℕ => 2 * eps (X := X) n) Filter.atTop (nhds (2 * 0)) :=
      Filter.Tendsto.const_mul 2 (eps_tendsto_zero (X := X))
    simpa using h2.eventually (isOpen_Iio.mem_nhds (by linarith : (2:ℝ) * 0 < ε))
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨1 / ((stages x y n).k : ℝ),
    div_pos one_pos (by exact_mod_cast (stages x y n).hk), fun a ha => ?_⟩
  have ha' : |a.val - b.val| ≤ 1 / ((stages x y n).k : ℝ) := by
    rw [Subtype.dist_eq, Real.dist_eq] at ha
    exact le_of_lt ha
  have h := dist_fAt_le x y n a.property.2 b.property.2 ha'
  show dist (fAt x y a.val a.property.2) (fAt x y b.val b.property.2) < ε
  linarith

lemma fI_zero : fI x y 0 = x := by
  rw [fI]
  exact fAt_zero x y

lemma fI_one : fI x y 1 = y := by
  rw [fI]
  exact fAt_one x y

end Final


/-- A compact, connected, locally connected metric space is path connected
(the Peano continuum theorem). -/
theorem pathConnectedSpace_of_compact_connected_locallyConnected (X : Type*) [MetricSpace X]
    [CompactSpace X] [ConnectedSpace X] [LocallyConnectedSpace X] : PathConnectedSpace X :=
  ⟨inferInstance, fun x y => ⟨⟨fI x y, continuous_fI x y⟩, fI_zero x y, fI_one x y⟩⟩

end Commons.Topology.Peano

namespace Commons.Topology.Plane

theorem paeno_continuum_pathConnected {K : Set ℂ}
    (hK : IsCompact K) (hKc : IsConnected K) (hlc : LocallyConnectedSpace ↥K) :
    PathConnectedSpace ↥K := by
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  haveI : ConnectedSpace ↥K := isConnected_iff_connectedSpace.mp hKc
  exact Commons.Topology.Peano.pathConnectedSpace_of_compact_connected_locallyConnected ↥K

end Commons.Topology.Plane