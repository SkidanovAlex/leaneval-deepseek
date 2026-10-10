import Mathlib.GroupTheory.Nilpotent
import Submission.Work.SSGRoute.prop5.Basic
import Submission.Work.SSGRoute.prop5.commutator_lowerCentralSeries_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.prop5

open scoped commutatorElement

set_option maxHeartbeats 1600000

/-! ## Centrality modulo a normal subgroup

If every commutator of `M` with the whole group lies in a normal subgroup `N`, then every
element of `M` is central modulo `N`. -/

lemma mk_commute_of_commutator_le {P : Type*} [Group P] {N M : Subgroup P} [N.Normal]
    (h : ⁅(⊤ : Subgroup P), M⁆ ≤ N) {x : P} (hx : x ∈ M) (y : P) :
    (QuotientGroup.mk' N x) * (QuotientGroup.mk' N y) =
      (QuotientGroup.mk' N y) * (QuotientGroup.mk' N x) := by
  have hmem : ⁅x, y⁆ ∈ N := by
    have h' := h
    rw [Subgroup.commutator_comm] at h'
    exact h' (Subgroup.commutator_mem_commutator hx (Subgroup.mem_top y))
  have h1 : ⁅(QuotientGroup.mk' N) x, (QuotientGroup.mk' N) y⁆ = 1 := by
    rw [← map_commutatorElement (QuotientGroup.mk' N), QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

/-- Conjugation by any element fixes the class modulo `N` of an element of `M`. -/
lemma mk_conj_eq_of_commutator_le {P : Type*} [Group P] {N M : Subgroup P} [N.Normal]
    (h : ⁅(⊤ : Subgroup P), M⁆ ≤ N) {y : P} (hy : y ∈ M) (g : P) :
    (QuotientGroup.mk' N) (g * y * g⁻¹) = (QuotientGroup.mk' N) y := by
  rw [map_mul, map_mul, map_inv, ← mk_commute_of_commutator_le h hy g]
  group

/-- Two abstract conjugation-triviality lemmas for a central element. -/
lemma center_conj_left {G : Type*} [Group G] {E : G} (hE : ∀ z, E * z = z * E) (W : G) :
    E * W * E⁻¹ = W := by
  rw [hE W]; group

lemma center_conj_right {G : Type*} [Group G] {E : G} (hE : ∀ z, E * z = z * E) (W : G) :
    W * E * W⁻¹ = E := by
  rw [← hE W]; group

/-! ## Two-variable multiplicativity of the commutator modulo `γ_{n+2}`

For `u ∈ γ_n`, the map `a ↦ ⁅a, u⁆` is a homomorphism into `γ_{n+1}/γ_{n+2}`, and for
`u, v ∈ γ_n` the map `x ↦ ⁅x, ·⁆` is a homomorphism on `γ_n` modulo `γ_{n+2}`. -/

lemma commutator_mul_left_sub_mem {P : Type*} [Group P] (n : ℕ) (u a b : P)
    (hu : u ∈ (⊤ : Subgroup P).lowerCentralSeries n) :
    ⁅a * b, u⁆ * (⁅a, u⁆ * ⁅b, u⁆)⁻¹ ∈ (⊤ : Subgroup P).lowerCentralSeries (n + 2) := by
  set N : Subgroup P := (⊤ : Subgroup P).lowerCentralSeries (n + 2) with hN
  haveI hNn : N.Normal := by rw [hN]; infer_instance
  have hb1 : ⁅b, u⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries (n + 1) := by
    have := commutator_lowerCentralSeries_le P 0 n
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top b) hu)
    simpa using this
  have ha1 : ⁅a, u⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries (n + 1) := by
    have := commutator_lowerCentralSeries_le P 0 n
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) hu)
    simpa using this
  have hcen : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P).lowerCentralSeries (n + 1)⁆ ≤ N := by
    rw [hN]; exact commutator_top_lowerCentralSeries_le P (n + 1)
  have key : (QuotientGroup.mk' N) ⁅a * b, u⁆ =
      (QuotientGroup.mk' N) ⁅b, u⁆ * (QuotientGroup.mk' N) ⁅a, u⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul a b u, map_mul,
      mk_conj_eq_of_commutator_le hcen hb1 a]
  have hgoal : (QuotientGroup.mk' N) (⁅a * b, u⁆ * (⁅a, u⁆ * ⁅b, u⁆)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, key]
    rw [← mk_commute_of_commutator_le hcen ha1 ⁅b, u⁆]
    group
  rw [← QuotientGroup.eq_one_iff]
  exact hgoal

lemma commutator_mul_right_sub_mem {P : Type*} [Group P] (n : ℕ) (x u v : P)
    (hu : u ∈ (⊤ : Subgroup P).lowerCentralSeries n)
    (hv : v ∈ (⊤ : Subgroup P).lowerCentralSeries n) :
    ⁅x, u * v⁆ * (⁅x, u⁆ * ⁅x, v⁆)⁻¹ ∈ (⊤ : Subgroup P).lowerCentralSeries (n + 2) := by
  set N : Subgroup P := (⊤ : Subgroup P).lowerCentralSeries (n + 2) with hN
  haveI hNn : N.Normal := by rw [hN]; infer_instance
  have hu1 : ⁅x, u⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries (n + 1) := by
    have := commutator_lowerCentralSeries_le P 0 n
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) hu)
    simpa using this
  have hv1 : ⁅x, v⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries (n + 1) := by
    have := commutator_lowerCentralSeries_le P 0 n
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) hv)
    simpa using this
  have hcen : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P).lowerCentralSeries (n + 1)⁆ ≤ N := by
    rw [hN]; exact commutator_top_lowerCentralSeries_le P (n + 1)
  have hid : ⁅x, u * v⁆ = ⁅x, u⁆ * (u * ⁅x, v⁆ * u⁻¹) := by
    rw [commutatorElement_mul_right_eq_mul_conj x u v]; group
  have key : (QuotientGroup.mk' N) ⁅x, u * v⁆ =
      (QuotientGroup.mk' N) ⁅x, u⁆ * (QuotientGroup.mk' N) ⁅x, v⁆ := by
    rw [hid, map_mul, mk_conj_eq_of_commutator_le hcen hv1 u]
  have hgoal : (QuotientGroup.mk' N) (⁅x, u * v⁆ * (⁅x, u⁆ * ⁅x, v⁆)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, key]
    group
  rw [← QuotientGroup.eq_one_iff]
  exact hgoal

/-! ## The main lemma -/

theorem commWord_update_mul_mem {P : Type*} [Group P] (j : ℕ) (hj : 1 ≤ j)
    (x : Fin j → P) (k : Fin j) (a b : P) :
    commWord j (Function.update x k (a * b)) *
        (commWord j (Function.update x k a) * commWord j (Function.update x k b))⁻¹
      ∈ (⊤ : Subgroup P).lowerCentralSeries j := by
  revert hj x k a b
  induction j with
  | zero => intro hj; omega
  | succ i ih =>
    intro hj x k a b
    rcases i with _ | m
    · -- j = 1
      have hk : k = 0 := Fin.ext (by omega)
      rw [hk]
      simp [commWord, Function.update_self]
    · -- j = m + 2
      by_cases hk0 : k = 0
      · -- the updated slot is the outermost variable
        rw [hk0]
        have htail0 : ∀ c : P, (fun t : Fin (m + 1) => Function.update x 0 c t.succ)
            = (fun t : Fin (m + 1) => x t.succ) := by
          intro c
          funext t
          exact Function.update_of_ne (Fin.succ_ne_zero t) c x
        have hcwu : ∀ c : P, commWord (m + 2) (Function.update x 0 c)
            = ⁅c, commWord (m + 1) (fun t : Fin (m + 1) => x t.succ)⁆ := by
          intro c
          rw [commWord_succ_succ, Function.update_self, htail0 c]
        rw [hcwu (a * b), hcwu a, hcwu b]
        refine commutator_mul_left_sub_mem m _ a b ?_
        have h := commWord_mem_lowerCentralSeries (m + 1) (fun t : Fin (m + 1) => x t.succ)
        simpa using h
      · -- the updated slot is inside the iterated commutator
        obtain ⟨k', hk'⟩ : ∃ k' : Fin (m + 1), k'.succ = k := ⟨k.pred hk0, Fin.succ_pred k hk0⟩
        have htail : ∀ c : P, (fun t : Fin (m + 1) => Function.update x k c t.succ)
            = Function.update (fun t : Fin (m + 1) => x t.succ) k' c := by
          intro c
          funext t
          rw [Function.update_apply, Function.update_apply, ← hk']
          simp [Fin.succ_inj]
        have hcw : ∀ c : P, commWord (m + 2) (Function.update x k c)
            = ⁅x 0, commWord (m + 1)
                (Function.update (fun t : Fin (m + 1) => x t.succ) k' c)⁆ := by
          intro c
          rw [commWord_succ_succ, Function.update_of_ne (Ne.symm hk0), htail c]
        rw [hcw (a * b), hcw a, hcw b]
        set A : P := commWord (m + 1) (Function.update (fun t : Fin (m + 1) => x t.succ) k' a)
          with hA_def
        set B : P := commWord (m + 1) (Function.update (fun t : Fin (m + 1) => x t.succ) k' b)
          with hB_def
        set C : P := commWord (m + 1)
            (Function.update (fun t : Fin (m + 1) => x t.succ) k' (a * b)) with hC_def
        obtain ⟨η, hη_def⟩ : ∃ η : P, η = C * (A * B)⁻¹ := ⟨_, rfl⟩
        have hAm : A ∈ (⊤ : Subgroup P).lowerCentralSeries m := by
          rw [hA_def]
          have h := commWord_mem_lowerCentralSeries (m + 1)
            (Function.update (fun t : Fin (m + 1) => x t.succ) k' a)
          simpa using h
        have hBm : B ∈ (⊤ : Subgroup P).lowerCentralSeries m := by
          rw [hB_def]
          have h := commWord_mem_lowerCentralSeries (m + 1)
            (Function.update (fun t : Fin (m + 1) => x t.succ) k' b)
          simpa using h
        have hηmem : η ∈ (⊤ : Subgroup P).lowerCentralSeries (m + 1) := by
          rw [hη_def, hA_def, hB_def, hC_def]
          exact ih (by omega) (fun t : Fin (m + 1) => x t.succ) k' a b
        have hηm : η ∈ (⊤ : Subgroup P).lowerCentralSeries m :=
          (⊤ : Subgroup P).lowerCentralSeries_antitone (by omega) hηmem
        have hkey : ⁅x 0, C⁆ * (⁅x 0, A⁆ * ⁅x 0, B⁆)⁻¹ =
            (⁅x 0, η * A * B⁆ * (⁅x 0, η * A⁆ * ⁅x 0, B⁆)⁻¹)
              * (⁅x 0, η * A⁆ * (⁅x 0, η⁆ * ⁅x 0, A⁆)⁻¹)
              * ⁅x 0, η⁆ := by
          have hCeq : C = η * A * B := by rw [hη_def]; group
          rw [hCeq]; group
        have hD1 : ⁅x 0, η * A * B⁆ * (⁅x 0, η * A⁆ * ⁅x 0, B⁆)⁻¹
            ∈ (⊤ : Subgroup P).lowerCentralSeries (m + 2) :=
          commutator_mul_right_sub_mem m (x 0) (η * A) B (mul_mem hηm hAm) hBm
        have hD2 : ⁅x 0, η * A⁆ * (⁅x 0, η⁆ * ⁅x 0, A⁆)⁻¹
            ∈ (⊤ : Subgroup P).lowerCentralSeries (m + 2) :=
          commutator_mul_right_sub_mem m (x 0) η A hηm hAm
        have hxη : ⁅x 0, η⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries (m + 2) := by
          have h := commutator_lowerCentralSeries_le P 0 (m + 1)
            (Subgroup.commutator_mem_commutator (Subgroup.mem_top (x 0)) hηmem)
          simpa using h
        rw [hkey]
        exact mul_mem (mul_mem hD1 hD2) hxη

end Work.SSGRoute.prop5
