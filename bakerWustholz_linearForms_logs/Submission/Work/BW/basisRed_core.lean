import Mathlib
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.basisRed_succMinL_mono

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Core of the basis reduction (BW Lemma 4)

This file proves the abstract form of Lemma 4 of Baker–Wüstholz: for a "lattice norm" `F` on `ℝⁿ`
(see `Work.BW.IsLatticeNorm`) and lattice vectors `u 0, …, u (n-1)` that are `ℝ`-linearly
independent with `F (u k) ≤ λ_{k+1}` (the successive minima of `ℤⁿ` w.r.t. `F`), there is a
`ℤ`-basis `w` of `ℤⁿ` with

`∏ j, F (w j) ≤ n!/2^{n-1} * ∏ j, succMinL F (j+1)`.

The construction follows BW p. 28: `w_j` is chosen in `L_j ∖ L_{j-1}` (where `L_j` is spanned by
`u_0,…,u_j`) minimising the `u_j`-coordinate, and then reduced modulo the previous `u`'s by nearest
integers. The minimising property forces `w_0, …, w_{n-1}` to be a basis of `ℤⁿ`.

Everything is phrased for the lattice `ℤⁿ ⊆ ℝⁿ`; the linear isomorphism given by `A` transports it
to the lattice `A ℤⁿ`.
-/

namespace Work.BW

open Matrix Finset

variable {n : ℕ}

/-- The real vector underlying an integer vector (the inclusion `ℤⁿ ↪ ℝⁿ`). -/
def toR (v : Fin n → ℤ) : Fin n → ℝ := fun i => (v i : ℝ)

lemma toR_injective : Function.Injective (toR (n := n)) := by
  intro a b h
  funext i
  have h' := congrFun h i
  simp only [toR] at h'
  exact_mod_cast h'

lemma toR_zero : toR (0 : Fin n → ℤ) = 0 := by ext i; simp [toR]

lemma toR_sub (a b : Fin n → ℤ) : toR (a - b) = toR a - toR b := by
  ext i; simp [toR]

lemma toR_add (a b : Fin n → ℤ) : toR (a + b) = toR a + toR b := by
  ext i; simp [toR]

lemma toR_smul (m : ℤ) (a : Fin n → ℤ) : toR (m • a) = (m : ℝ) • toR a := by
  ext i; simp [toR]

lemma toR_neg (a : Fin n → ℤ) : toR (-a) = -toR a := by
  ext i; simp [toR]

lemma toR_sum {ι : Type*} (s : Finset ι) (c : ι → ℤ) (v : ι → Fin n → ℤ) :
    toR (∑ k ∈ s, c k • v k) = ∑ k ∈ s, (c k : ℝ) • toR (v k) := by
  ext i; simp [toR, Finset.sum_apply]

/-- An integer nearest to a real number. -/
lemma exists_int_near (a : ℝ) : ∃ m : ℤ, |a - (m : ℝ)| ≤ 1 / 2 := by
  refine ⟨⌊a + 1 / 2⌋, ?_⟩
  have h1 : ((⌊a + 1 / 2⌋ : ℤ) : ℝ) ≤ a + 1 / 2 := Int.floor_le _
  have h2 : a + 1 / 2 < ((⌊a + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  constructor <;> linarith

/-- For `β ≠ 0` every real `θ` has an integer multiple of `β` strictly closer than `|β|`. -/
lemma exists_int_mul_near {β θ : ℝ} (hβ : β ≠ 0) :
    ∃ m : ℤ, |θ - (m : ℝ) * β| < |β| := by
  obtain ⟨m, hm⟩ := exists_int_near (θ / β)
  refine ⟨m, ?_⟩
  have h1 : θ - (m : ℝ) * β = β * (θ / β - (m : ℝ)) := by field_simp
  rw [h1, abs_mul]
  have h2 : |θ / β - (m : ℝ)| ≤ 1 / 2 := hm
  nlinarith [abs_pos.mpr hβ]

/-- An additive subgroup of `ℝ` containing `1` has its least positive element equal to `1` or
`≤ 1/2`. -/
lemma gamma_cases {γ : ℝ} {G : Set ℝ} (h0 : (0 : ℝ) ∈ G)
    (hsub : ∀ x ∈ G, ∀ y ∈ G, x - y ∈ G) (h1 : (1 : ℝ) ∈ G)
    (hpos : 0 < γ) (hγG : γ ∈ G) (hmin : ∀ x ∈ G, x ≠ 0 → γ ≤ |x|) :
    γ = 1 ∨ γ ≤ 1 / 2 := by
  by_cases hγ1 : γ = 1
  · exact Or.inl hγ1
  · right
    rcases lt_or_gt_of_ne hγ1 with hlt | hgt
    · have hneg : -γ ∈ G := by simpa using hsub 0 h0 γ hγG
      have hmult : ∀ m : ℕ, (m : ℝ) * γ ∈ G := by
        intro m
        induction m with
        | zero => simpa using h0
        | succ m ih =>
            have : ((m + 1 : ℕ) : ℝ) * γ = (m : ℝ) * γ - (-γ) := by push_cast; ring
            rw [this]
            exact hsub _ ih _ hneg
      have hex : ∃ k : ℕ, 1 < (k : ℝ) * γ := by
        obtain ⟨k, hk⟩ := exists_nat_gt (1 / γ)
        exact ⟨k, (div_lt_iff₀ hpos).mp hk⟩
      obtain ⟨k, hkprop, hkmin⟩ : ∃ k : ℕ, 1 < (k : ℝ) * γ ∧ ∀ m : ℕ, 1 < (m : ℝ) * γ → k ≤ m :=
        ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min' hex hm⟩
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h] at hkprop; push_cast at hkprop; linarith
        · exact h
      have hprev : ((k - 1 : ℕ) : ℝ) * γ ≤ 1 := by
        by_contra hcon
        have hcon' : 1 < ((k - 1 : ℕ) : ℝ) * γ := not_le.mp hcon
        have hcontra := hkmin (k - 1) hcon'
        have hlt2 : k - 1 < k := Nat.sub_lt hkpos (by norm_num)
        omega
      have hkcast : ((k : ℕ) : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
        have : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_pos hkpos).symm
        rw [this]; push_cast; ring
      have hkγ : (k : ℝ) * γ = ((k - 1 : ℕ) : ℝ) * γ + γ := by rw [hkcast]; ring
      have hkprop' : 1 < ((k - 1 : ℕ) : ℝ) * γ + γ := by rw [← hkγ]; exact hkprop
      rcases lt_or_eq_of_le hprev with hlt' | heq
      · exfalso
        have hmem : (k : ℝ) * γ - 1 ∈ G := hsub _ (hmult k) 1 h1
        have hpos' : 0 < (k : ℝ) * γ - 1 := by linarith
        have hne : (k : ℝ) * γ - 1 ≠ 0 := ne_of_gt hpos'
        have hbound := hmin _ hmem hne
        rw [abs_of_pos hpos'] at hbound
        have hlt2 : (k : ℝ) * γ - 1 < γ := by linarith
        linarith
      · have hk1n : (k - 1 : ℕ) ≠ 0 := by
          intro h
          rw [h] at heq
          simp at heq
        have hcast : ((k - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hk1n
        have hγeq : γ = 1 / ((k - 1 : ℕ) : ℝ) := by
          rw [eq_div_iff hcast]
          linarith
        have h2 : 2 ≤ k - 1 := by
          have hge1 : 1 ≤ k - 1 := Nat.one_le_iff_ne_zero.mpr hk1n
          rcases eq_or_lt_of_le hge1 with h | h
          · exfalso
            rw [← h] at heq
            simp only [Nat.cast_one, one_mul] at heq
            linarith
          · omega
        have hle : (2 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast h2
        have hposc : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 0 < k - 1)
        rw [hγeq, div_le_iff₀ hposc]
        nlinarith [hle]
    · exfalso
      have hmem : γ - 1 ∈ G := hsub γ hγG 1 h1
      have hne : γ - 1 ≠ 0 := by linarith
      have hbound := hmin (γ - 1) hmem hne
      rw [abs_of_pos (by linarith : (0 : ℝ) < γ - 1)] at hbound
      linarith


/-- Data for the basis reduction: a lattice norm `F` on `ℤⁿ` and a `ℝ`-independent family `u` of
lattice vectors with `F (u k) ≤ λ_{k+1}`. -/
structure RedData (n : ℕ) where
  hn : 0 < n
  F : (Fin n → ℝ) → ℝ
  hF : IsLatticeNorm F
  u : Fin n → (Fin n → ℤ)
  hind : LinearIndependent ℝ (fun k : Fin n => toR (u k))
  hbd : ∀ k : Fin n, F (toR (u k)) ≤ succMinL F (k.1 + 1)

namespace RedData

variable {n : ℕ} (D : RedData n)

lemma hspanU : ⊤ ≤ Submodule.span ℝ (Set.range (fun k : Fin n => toR (D.u k))) := by
  have hne : Nonempty (Fin n) := ⟨⟨0, D.hn⟩⟩
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (Fin n → ℝ) := by
    rw [Fintype.card_fin, Module.finrank_fin_fun]
  exact le_of_eq (LinearIndependent.span_eq_top_of_card_eq_finrank D.hind hcard).symm

/-- The basis of `ℝⁿ` given by the independent family `u`. -/
noncomputable def bU : Module.Basis (Fin n) ℝ (Fin n → ℝ) :=
  Module.Basis.mk D.hind D.hspanU

lemma bU_apply (k : Fin n) : D.bU k = toR (D.u k) :=
  Module.Basis.mk_apply D.hind D.hspanU k

/-- The `j`-th coordinate functional in the basis `u`. -/
noncomputable def cf (j : Fin n) : (Fin n → ℝ) →ₗ[ℝ] ℝ := D.bU.coord j

lemma cf_apply (j : Fin n) (x : Fin n → ℝ) : D.cf j x = D.bU.repr x j :=
  Module.Basis.coord_apply _ _ _

lemma cf_self (j : Fin n) : D.cf j (toR (D.u j)) = 1 := by
  rw [cf_apply, ← bU_apply]
  rw [Module.Basis.repr_self_apply D.bU j j]
  simp

lemma cf_other {j k : Fin n} (h : k ≠ j) : D.cf j (toR (D.u k)) = 0 := by
  rw [cf_apply, ← bU_apply]
  rw [Module.Basis.repr_self_apply D.bU k j]
  simp [h]

lemma sum_cf (x : Fin n → ℝ) : ∑ k : Fin n, D.cf k x • toR (D.u k) = x := by
  have h := Module.Basis.sum_repr D.bU x
  simpa [cf_apply, bU_apply] using h

/-- `Lsp j` is spanned by `u 0, …, u j` (points whose coordinates vanish above `j`). -/
noncomputable def Lsp (j : ℕ) : Submodule ℝ (Fin n → ℝ) :=
  ⨅ k : {k : Fin n // j < k.1}, (D.cf k.1).ker

/-- `Msp j` is spanned by `u 0, …, u (j-1)` (points whose coordinates vanish from `j` on). -/
noncomputable def Msp (j : ℕ) : Submodule ℝ (Fin n → ℝ) :=
  ⨅ k : {k : Fin n // j ≤ k.1}, (D.cf k.1).ker

lemma mem_Lsp {j : ℕ} {x : Fin n → ℝ} :
    x ∈ D.Lsp j ↔ ∀ k : Fin n, j < k.1 → D.cf k x = 0 := by
  simp only [Lsp, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h k hk; exact h ⟨k, hk⟩
  · intro h k; exact h k.1 k.2

lemma mem_Msp {j : ℕ} {x : Fin n → ℝ} :
    x ∈ D.Msp j ↔ ∀ k : Fin n, j ≤ k.1 → D.cf k x = 0 := by
  simp only [Msp, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h k hk; exact h ⟨k, hk⟩
  · intro h k; exact h k.1 k.2

lemma Lsp_eq_Msp_succ (j : Fin n) : D.Lsp j.1 = D.Msp (j.1 + 1) := by
  ext x
  rw [mem_Lsp, mem_Msp]
  constructor
  · intro h k hk; exact h k (by omega)
  · intro h k hk; exact h k (by omega)

lemma Msp_le_Lsp (j : ℕ) : D.Msp j ≤ D.Lsp j := by
  intro x hx
  rw [mem_Lsp]
  intro k hk
  exact (mem_Msp D).mp hx k (le_of_lt hk)

lemma Msp_le_Msp {i j : ℕ} (h : i ≤ j) : D.Msp i ≤ D.Msp j := by
  intro x hx
  rw [mem_Msp] at hx ⊢
  exact fun k hk => hx k (le_trans h hk)

lemma Lsp_le_Lsp {i j : ℕ} (h : i ≤ j) : D.Lsp i ≤ D.Lsp j := by
  intro x hx
  rw [mem_Lsp] at hx ⊢
  exact fun k hk => hx k (lt_of_le_of_lt h hk)

lemma u_mem_Lsp (j : ℕ) (k : Fin n) : toR (D.u k) ∈ D.Lsp j ↔ k.1 ≤ j := by
  rw [mem_Lsp]
  constructor
  · intro h
    by_contra hc
    have hkj : j < k.1 := not_le.mp hc
    have h1 := h k hkj
    rw [cf_self] at h1
    norm_num at h1
  · intro hk l hl
    exact cf_other D (by omega)

lemma u_mem_Msp (j : ℕ) (k : Fin n) : toR (D.u k) ∈ D.Msp j ↔ k.1 < j := by
  rw [mem_Msp]
  constructor
  · intro h
    by_contra hc
    have hkj : j ≤ k.1 := not_lt.mp hc
    have h1 := h k hkj
    rw [cf_self] at h1
    norm_num at h1
  · intro hk l hl
    exact cf_other D (by omega)

lemma cf_eq_zero_of_mem_Lsp {j : ℕ} {x : Fin n → ℝ} (hx : x ∈ D.Lsp j)
    {k : Fin n} (hk : j < k.1) : D.cf k x = 0 :=
  (mem_Lsp D).mp hx k hk

lemma eq_sum_of_mem_Lsp {j : ℕ} {x : Fin n → ℝ} (hx : x ∈ D.Lsp j) :
    x = ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.1 ≤ j), D.cf k x • toR (D.u k) := by
  conv_lhs => rw [← sum_cf D x]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin n => k.1 ≤ j)
      (fun k => D.cf k x • toR (D.u k))]
  have hzero : ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ (k.1 ≤ j)),
      D.cf k x • toR (D.u k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [cf_eq_zero_of_mem_Lsp D hx (not_le.mp hk), zero_smul]
  rw [hzero, add_zero]

/-- `cf j` does not vanish on a point of `Lsp j` outside `Msp j`. -/
lemma cf_j_ne_zero_of_mem {j : ℕ} (hj : j < n) {x : Fin n → ℝ} (hL : x ∈ D.Lsp j)
    (hM : x ∉ D.Msp j) : D.cf ⟨j, hj⟩ x ≠ 0 := by
  by_contra h0
  refine hM ((mem_Msp D).mpr (fun k hk => ?_))
  rcases eq_or_lt_of_le hk with h | h
  · subst h; exact h0
  · exact cf_eq_zero_of_mem_Lsp D hL h

/-- The norm bound for linear combinations of the `u k` with real coefficients. -/
lemma F_sum_smul_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → Fin n → ℝ) :
    D.F (∑ k ∈ s, c k • v k) ≤ ∑ k ∈ s, |c k| * D.F (v k) := by
  classical
  induction s using Finset.induction with
  | empty => simp [(D.hF.eq_zero 0).mpr rfl]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have h1 : D.F (c a • v a + ∑ k ∈ s, c k • v k) ≤ D.F (c a • v a) + D.F (∑ k ∈ s, c k • v k) :=
        D.hF.add_le _ _
      rw [D.hF.smul] at h1
      linarith

lemma F_finset_sum_u_le (s : Finset (Fin n)) (c : Fin n → ℝ) :
    D.F (∑ k ∈ s, c k • toR (D.u k)) ≤ ∑ k ∈ s, |c k| * D.F (toR (D.u k)) :=
  F_sum_smul_le D s c (fun k => toR (D.u k))

/-- Normalisation of a lattice vector modulo `u 0, …, u (j-1)` by nearest integers. -/
noncomputable def nrm (j : Fin n) (v : Fin n → ℤ) : Fin n → ℤ :=
  v - ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.1 < j.1),
      ⌊D.cf k (toR v) + 1 / 2⌋ • D.u k

lemma abs_sub_floor_half (a : ℝ) : |a - (⌊a + 1 / 2⌋ : ℝ)| ≤ 1 / 2 := by
  have h1 : ((⌊a + 1 / 2⌋ : ℤ) : ℝ) ≤ a + 1 / 2 := Int.floor_le _
  have h2 : a + 1 / 2 < ((⌊a + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  constructor <;> linarith

lemma toR_nrm (j : Fin n) (v : Fin n → ℤ) :
    toR (D.nrm j v) = toR v - ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.1 < j.1),
        ((⌊D.cf k (toR v) + 1 / 2⌋ : ℤ) : ℝ) • toR (D.u k) := by
  rw [nrm, toR_sub, toR_sum]

lemma cf_nrm_eq_of_lt {j : Fin n} {v : Fin n → ℤ} {k : Fin n} (hk : k.1 < j.1) :
    D.cf k (toR (D.nrm j v)) = D.cf k (toR v) - ⌊D.cf k (toR v) + 1 / 2⌋ := by
  have hmem : k ∈ Finset.univ.filter (fun k : Fin n => k.1 < j.1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hk
  rw [toR_nrm, map_sub, map_sum]
  rw [Finset.sum_eq_single k
    (fun l _ hl => by
      rw [map_smul, cf_other D hl]
      simp)
    (fun hknot => absurd hmem hknot)]
  rw [map_smul, cf_self]
  simp

lemma cf_nrm_eq_of_ge {j : Fin n} {v : Fin n → ℤ} {k : Fin n} (hk : j.1 ≤ k.1) :
    D.cf k (toR (D.nrm j v)) = D.cf k (toR v) := by
  rw [toR_nrm, map_sub, map_sum]
  have hzero : ∑ l ∈ Finset.univ.filter (fun l : Fin n => l.1 < j.1),
      D.cf k (((⌊D.cf l (toR v) + 1 / 2⌋ : ℤ) : ℝ) • toR (D.u l)) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rw [map_smul, cf_other D (by omega : l ≠ k)]
    simp
  rw [hzero, sub_zero]

lemma cf_nrm_bound {j : Fin n} {v : Fin n → ℤ} {k : Fin n} (hk : k.1 < j.1) :
    |D.cf k (toR (D.nrm j v))| ≤ 1 / 2 := by
  rw [cf_nrm_eq_of_lt D hk]
  exact abs_sub_floor_half _

/-- The bound cutting off the finite candidate set. -/
noncomputable def Ebound (j : Fin n) : ℝ :=
  D.F (toR (D.u j)) + (1 / 2) * ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.1 < j.1),
    D.F (toR (D.u k))

/-- The finite set of lattice vectors of `F`-norm `≤ Ebound j` lying in `Lsp j ∖ Msp j`. -/
noncomputable def cand (j : Fin n) : Finset (Fin n → ℤ) := by
  classical
  exact ((D.hF.finite (D.Ebound j)).toFinset).filter
    (fun v => toR v ∈ D.Lsp j.1 ∧ toR v ∉ D.Msp j.1)

lemma mem_cand {j : Fin n} {v : Fin n → ℤ} :
    v ∈ D.cand j ↔ D.F (toR v) ≤ D.Ebound j ∧ toR v ∈ D.Lsp j.1 ∧ toR v ∉ D.Msp j.1 := by
  simp only [cand, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact Iff.rfl

lemma u_mem_cand (j : Fin n) : D.u j ∈ D.cand j := by
  rw [mem_cand]
  refine ⟨?_, (u_mem_Lsp D j.1 j).mpr le_rfl, ?_⟩
  · rw [Ebound]
    have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.1 < j.1),
        D.F (toR (D.u k)) := Finset.sum_nonneg (fun k _ => D.hF.nonneg _)
    nlinarith
  · rw [u_mem_Msp]
    exact lt_irrefl _

lemma cand_nonempty (j : Fin n) : (D.cand j).Nonempty := ⟨D.u j, u_mem_cand D j⟩

/-- The element of `cand j` minimising the `j`-th coordinate. -/
noncomputable def wRaw (j : Fin n) : Fin n → ℤ :=
  Classical.choose (Finset.exists_min_image (D.cand j) (fun v => |D.cf j (toR v)|)
    (cand_nonempty D j))

lemma wRaw_mem (j : Fin n) : D.wRaw j ∈ D.cand j :=
  (Classical.choose_spec (Finset.exists_min_image (D.cand j)
    (fun v => |D.cf j (toR v)|) (cand_nonempty D j))).1

lemma wRaw_min (j : Fin n) {v : Fin n → ℤ} (hv : v ∈ D.cand j) :
    |D.cf j (toR (D.wRaw j))| ≤ |D.cf j (toR v)| :=
  (Classical.choose_spec (Finset.exists_min_image (D.cand j)
    (fun v => |D.cf j (toR v)|) (cand_nonempty D j))).2 v hv

lemma wRaw_Lsp (j : Fin n) : toR (D.wRaw j) ∈ D.Lsp j.1 :=
  ((mem_cand D).mp (wRaw_mem D j)).2.1

lemma wRaw_not_Msp (j : Fin n) : toR (D.wRaw j) ∉ D.Msp j.1 :=
  ((mem_cand D).mp (wRaw_mem D j)).2.2

/-- The minimal positive value of the `j`-th coordinate on `Lsp j ∖ Msp j`. -/
noncomputable def gam (j : Fin n) : ℝ := |D.cf j (toR (D.wRaw j))|

lemma gam_pos (j : Fin n) : 0 < D.gam j := by
  have hL := wRaw_Lsp D j
  have hM := wRaw_not_Msp D j
  refine abs_pos.mpr (fun h0 => hM ?_)
  rw [mem_Msp]
  intro k hk
  rcases eq_or_lt_of_le hk with h | h
  · have hkj : k = j := Fin.ext h.symm
    rw [hkj]
    exact h0
  · exact cf_eq_zero_of_mem_Lsp D hL h

lemma gam_le_one (j : Fin n) : D.gam j ≤ 1 := by
  have h := wRaw_min D j (u_mem_cand D j)
  rw [cf_self] at h
  simpa [gam] using h

/-- The key minimality property of `wRaw j`. -/
lemma gam_global_min {j : Fin n} {v : Fin n → ℤ} (hL : toR v ∈ D.Lsp j.1)
    (hM : toR v ∉ D.Msp j.1) : D.gam j ≤ |D.cf j (toR v)| := by
  by_contra hcon
  have hlt : |D.cf j (toR v)| < |D.cf j (toR (D.wRaw j))| := not_le.mp hcon
  -- the normalised vector is again a candidate
  have hL' : toR (D.nrm j v) ∈ D.Lsp j.1 := by
    rw [mem_Lsp]
    intro k hk
    rw [cf_nrm_eq_of_ge D (le_of_lt hk)]
    exact cf_eq_zero_of_mem_Lsp D hL hk
  have hM' : toR (D.nrm j v) ∉ D.Msp j.1 := by
    intro hcontra
    exact hM ((mem_Msp D).mpr (fun k hk =>
      by rw [← cf_nrm_eq_of_ge D hk]; exact (mem_Msp D).mp hcontra k hk))
  have hF' : D.F (toR (D.nrm j v)) ≤ D.Ebound j := by
    have hbond : D.F (toR (D.nrm j v))
        ≤ (1 / 2) * ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.1 < j.1), D.F (toR (D.u k))
          + |D.cf j (toR v)| * D.F (toR (D.u j)) := by
      conv_lhs => rw [← sum_cf D (toR (D.nrm j v))]
      refine le_trans (F_finset_sum_u_le D Finset.univ (fun k => D.cf k (toR (D.nrm j v)))) ?_
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin n => k.1 < j.1)
            (fun k => |D.cf k (toR (D.nrm j v))| * D.F (toR (D.u k)))]
      have h1 : ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.1 < j.1),
            |D.cf k (toR (D.nrm j v))| * D.F (toR (D.u k))
          ≤ (1 / 2) * ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.1 < j.1),
              D.F (toR (D.u k)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        have hb := cf_nrm_bound (D := D) (v := v) hk
        have hFnn : 0 ≤ D.F (toR (D.u k)) := D.hF.nonneg _
        nlinarith
      have h2 : ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ (k.1 < j.1)),
            |D.cf k (toR (D.nrm j v))| * D.F (toR (D.u k))
          = |D.cf j (toR v)| * D.F (toR (D.u j)) := by
        rw [Finset.sum_eq_single j
          (fun k hk hkj => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            rcases lt_or_eq_of_le (not_lt.mp hk) with h | h
            · rw [cf_nrm_eq_of_ge D (le_of_lt h), cf_eq_zero_of_mem_Lsp D hL h, abs_zero, zero_mul]
            · exact absurd (Fin.ext h).symm hkj)
          (fun hjnot => absurd (by simp) hjnot)]
        rw [cf_nrm_eq_of_ge D le_rfl]
      linarith
    rw [Ebound]
    have hjpos : 0 < D.F (toR (D.u j)) := by
      have hne : toR (D.u j) ≠ 0 := D.hind.ne_zero j
      have hz : D.F (toR (D.u j)) ≠ 0 := fun h => hne ((D.hF.eq_zero _).mp h)
      exact lt_of_le_of_ne (D.hF.nonneg _) (Ne.symm hz)
    have hlt1 : |D.cf j (toR v)| < 1 := lt_of_lt_of_le hlt (gam_le_one D j)
    have : |D.cf j (toR v)| * D.F (toR (D.u j)) < D.F (toR (D.u j)) := by
      nlinarith [abs_nonneg (D.cf j (toR v))]
    linarith
  have hmem : D.nrm j v ∈ D.cand j := (mem_cand D).mpr ⟨hF', hL', hM'⟩
  have hmin := wRaw_min D j hmem
  rw [cf_nrm_eq_of_ge D (le_refl _)] at hmin
  linarith

/-- The set of values of the `j`-th coordinate on `Lsp j`. -/
noncomputable def Gam (j : Fin n) : Set ℝ :=
  {x : ℝ | ∃ v : Fin n → ℤ, toR v ∈ D.Lsp j.1 ∧ D.cf j (toR v) = x}

/-- The minimal positive value `gam j` is `1` or at most `1/2`. -/
lemma gam_eq_one_or_le_half (j : Fin n) : D.gam j = 1 ∨ D.gam j ≤ 1 / 2 := by
  refine gamma_cases (γ := D.gam j) (G := D.Gam j) ?_ ?_ ?_ (gam_pos D j) ?_ ?_
  · exact ⟨0, by rw [toR_zero]; exact Submodule.zero_mem _, by rw [toR_zero, map_zero]⟩
  · rintro x ⟨v, hv, rfl⟩ y ⟨w, hw, rfl⟩
    exact ⟨v - w, by rw [toR_sub]; exact Submodule.sub_mem _ hv hw,
      by rw [toR_sub, map_sub]⟩
  · exact ⟨D.u j, (u_mem_Lsp D j.1 j).mpr le_rfl, cf_self D j⟩
  · by_cases h : 0 ≤ D.cf j (toR (D.wRaw j))
    · exact ⟨D.wRaw j, wRaw_Lsp D j, by rw [gam, abs_of_nonneg h]⟩
    · exact ⟨-D.wRaw j, by rw [toR_neg]; exact Submodule.neg_mem _ (wRaw_Lsp D j),
        by rw [toR_neg, map_neg, gam, abs_of_neg (not_le.mp h)]⟩
  · rintro x ⟨v, hv, rfl⟩ hx0
    have hM : toR v ∉ D.Msp j.1 := fun hmem =>
      hx0 (by rw [← (mem_Msp D).mp hmem j le_rfl])
    exact gam_global_min D hv hM

/-- The basis vector attached to `j`: the minimiser of the `j`-th coordinate, normalised by
nearest integers (or `u j` in the case `gam j = 1`). -/
noncomputable def w (j : Fin n) : Fin n → ℤ :=
  if D.gam j = 1 then D.u j else D.nrm j (D.wRaw j)

lemma gam_w_eq (j : Fin n) : |D.cf j (toR (D.w j))| = D.gam j := by
  by_cases h : D.gam j = 1
  · rw [w, if_pos h, cf_self, abs_one, h]
  · rw [w, if_neg h, cf_nrm_eq_of_ge D le_rfl]
    rfl

lemma w_mem_Lsp (j : Fin n) : toR (D.w j) ∈ D.Lsp j.1 := by
  by_cases h : D.gam j = 1
  · rw [w, if_pos h]
    exact (u_mem_Lsp D j.1 j).mpr le_rfl
  · rw [w, if_neg h, mem_Lsp]
    intro k hk
    rw [cf_nrm_eq_of_ge D (le_of_lt hk)]
    exact cf_eq_zero_of_mem_Lsp D (wRaw_Lsp D j) hk

lemma w_not_mem_Msp (j : Fin n) : toR (D.w j) ∉ D.Msp j.1 := by
  intro hcontra
  have hzero : D.cf j (toR (D.w j)) = 0 := (mem_Msp D).mp hcontra j le_rfl
  have hg : D.gam j = 0 := by rw [← gam_w_eq D j, hzero, abs_zero]
  exact (ne_of_gt (gam_pos D j)) hg

lemma w_min (j : Fin n) {v : Fin n → ℤ} (hL : toR v ∈ D.Lsp j.1)
    (hM : toR v ∉ D.Msp j.1) : |D.cf j (toR (D.w j))| ≤ |D.cf j (toR v)| := by
  rw [gam_w_eq D j]
  exact gam_global_min D hL hM

lemma succMinL_nonneg (j : ℕ) (hj : j ≤ n) : 0 ≤ succMinL D.F j := by
  rcases Nat.eq_zero_or_pos j with h | h
  · rw [h, basisRed_succMinL_zero D.F]
  · rw [basisRed_succMinL_eq_sInf]
    exact le_csInf (basisRed_succSetL_nonempty D.hF hj)
      (fun t ht => basisRed_succSetL_nonneg D.hF h ht)

/-- The norm bound for `w j`. -/
lemma w_norm_le (j : Fin n) : D.F (toR (D.w j)) ≤
    max (D.F (toR (D.u j)))
      ((1 / 2) * ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.1 ≤ j.1), D.F (toR (D.u k))) := by
  by_cases h : D.gam j = 1
  · rw [w, if_pos h]; exact le_max_left _ _
  · have hhalf : D.gam j ≤ 1 / 2 := (gam_eq_one_or_le_half D j).resolve_left h
    rw [w, if_neg h]
    have hmain : D.F (toR (D.nrm j (D.wRaw j))) ≤
        (1 / 2) * ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.1 ≤ j.1), D.F (toR (D.u k)) := by
      conv_lhs => rw [← sum_cf D (toR (D.nrm j (D.wRaw j)))]
      refine le_trans (F_finset_sum_u_le D Finset.univ
        (fun k => D.cf k (toR (D.nrm j (D.wRaw j))))) ?_
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin n => k.1 ≤ j.1)
            (fun k => |D.cf k (toR (D.nrm j (D.wRaw j)))| * D.F (toR (D.u k)))]
      have h2 : ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ (k.1 ≤ j.1)),
            |D.cf k (toR (D.nrm j (D.wRaw j)))| * D.F (toR (D.u k)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rw [cf_nrm_eq_of_ge D (le_of_lt (not_le.mp hk)),
          cf_eq_zero_of_mem_Lsp D (wRaw_Lsp D j) (not_le.mp hk), abs_zero, zero_mul]
      rw [h2, add_zero, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have hb : |D.cf k (toR (D.nrm j (D.wRaw j)))| ≤ 1 / 2 := by
        rcases lt_or_eq_of_le hk with hlt | heq
        · exact cf_nrm_bound D hlt
        · have hkj : k = j := Fin.ext heq
          rw [hkj, cf_nrm_eq_of_ge D le_rfl]
          exact hhalf
      have hFnn : 0 ≤ D.F (toR (D.u k)) := D.hF.nonneg _
      nlinarith [abs_nonneg (D.cf k (toR (D.nrm j (D.wRaw j))))]
    exact le_trans hmain (le_max_right _ _)

lemma card_filter_le (j : Fin n) :
    (Finset.univ.filter (fun k : Fin n => k.1 ≤ j.1)).card = j.1 + 1 := by
  rw [← Finset.card_range (j.1 + 1)]
  refine Finset.card_bij (fun k _ => k.1) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact Finset.mem_range.mpr (by omega)
  · intro a ha b hb hab
    exact Fin.ext hab
  · intro b hb
    refine ⟨⟨b, by have := Finset.mem_range.mp hb; omega⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := Finset.mem_range.mp hb
    omega

/-- The pointwise bound on the basis vectors in terms of the successive minima. -/
lemma w_bound (j : Fin n) : D.F (toR (D.w j)) ≤
    (if j.1 = 0 then succMinL D.F 1 else ((j.1 : ℝ) + 1) / 2 * succMinL D.F (j.1 + 1)) := by
  refine le_trans (w_norm_le D j) ?_
  rcases Nat.eq_zero_or_pos j.1 with h0 | hpos
  · rw [if_pos h0]
    have hset : Finset.univ.filter (fun k : Fin n => k.1 ≤ j.1) = {j} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hk; exact Fin.ext (by omega)
      · intro hk; rw [hk]
    rw [hset, Finset.sum_singleton]
    have hmax : max (D.F (toR (D.u j))) ((1 / 2) * D.F (toR (D.u j))) = D.F (toR (D.u j)) := by
      rw [max_eq_left]; nlinarith [D.hF.nonneg (toR (D.u j))]
    rw [hmax]
    have := D.hbd j
    rwa [h0] at this
  · rw [if_neg (by omega : ¬ j.1 = 0)]
    refine max_le ?_ ?_
    · have h1 := D.hbd j
      have hmono := basisRed_succMinL_mono D.hF (Nat.le_refl (j.1 + 1)) (by omega : j.1 + 1 ≤ n)
      have hnn : 0 ≤ succMinL D.F (j.1 + 1) := succMinL_nonneg D _ (by omega)
      have hge1 : (1 : ℝ) ≤ ((j.1 : ℝ) + 1) / 2 := by
        have hj1 : (1 : ℝ) ≤ (j.1 : ℝ) := by exact_mod_cast hpos
        linarith
      nlinarith [h1, hnn]
    · have hsum : ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.1 ≤ j.1), D.F (toR (D.u k))
          ≤ ((j.1 : ℝ) + 1) * succMinL D.F (j.1 + 1) := by
        have hpt : ∀ k ∈ Finset.univ.filter (fun k : Fin n => k.1 ≤ j.1),
            D.F (toR (D.u k)) ≤ succMinL D.F (j.1 + 1) := by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          exact le_trans (D.hbd k)
            (basisRed_succMinL_mono D.hF (by omega) (by omega : j.1 + 1 ≤ n))
        calc ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.1 ≤ j.1), D.F (toR (D.u k))
            ≤ ∑ _k ∈ Finset.univ.filter (fun k : Fin n => k.1 ≤ j.1),
                succMinL D.F (j.1 + 1) := Finset.sum_le_sum hpt
          _ = ((Finset.univ.filter (fun k : Fin n => k.1 ≤ j.1)).card : ℝ)
                * succMinL D.F (j.1 + 1) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ = ((j.1 : ℝ) + 1) * succMinL D.F (j.1 + 1) := by
              rw [card_filter_le j]; push_cast; ring
      have hnn : 0 ≤ succMinL D.F (j.1 + 1) := succMinL_nonneg D _ (by omega)
      linarith

/-- The `w k` generate the whole lattice. -/
lemma exists_coeffs_of_mem_Msp : ∀ (j : ℕ), j ≤ n → ∀ x : Fin n → ℤ, toR x ∈ D.Msp j →
    ∃ c : Fin n → ℤ, ∑ k : Fin n, c k • D.w k = x := by
  intro j
  induction j with
  | zero =>
    intro _ x hx
    have hx0 : x = 0 := by
      have h := (mem_Msp D).mp hx
      have hz : toR x = 0 := by
        conv_lhs => rw [← sum_cf D (toR x)]
        apply Finset.sum_eq_zero
        intro k _
        rw [h k (Nat.zero_le _), zero_smul]
      exact toR_injective (by rw [hz, toR_zero])
    refine ⟨fun _ => 0, ?_⟩
    rw [hx0]
    simp
  | succ j ih =>
    intro hj x hx
    have hjlt : j < n := by omega
    set j' : Fin n := ⟨j, hjlt⟩ with hj'def
    have hxM : toR x ∈ D.Msp (j'.1 + 1) := by
      simpa [hj'def] using hx
    by_cases hcf : D.cf j' (toR x) = 0
    · have hprev : toR x ∈ D.Msp j := by
        rw [mem_Msp] at hx ⊢
        intro k hk
        rcases eq_or_lt_of_le hk with h | h
        · have hkj : k = j' := Fin.ext (by rw [hj'def]; exact h.symm)
          rw [hkj]; exact hcf
        · exact hx k (by omega)
      exact ih (by omega) x hprev
    · have hL : toR x ∈ D.Lsp j'.1 := by
        rw [Lsp_eq_Msp_succ D j']
        exact hxM
      have hM : toR x ∉ D.Msp j'.1 := fun hcontra =>
        hcf ((mem_Msp D).mp hcontra j' le_rfl)
      obtain ⟨m, hm⟩ := exists_int_mul_near (β := D.cf j' (toR (D.w j')))
        (θ := D.cf j' (toR x)) (fun h0 => D.w_not_mem_Msp j' ((mem_Msp D).mpr
          (fun k hk => by
            rcases eq_or_lt_of_le hk with h | h
            · have hkj : k = j' := Fin.ext h.symm
              rw [hkj]; exact h0
            · exact cf_eq_zero_of_mem_Lsp D (w_mem_Lsp D j') h)))
      set x' : Fin n → ℤ := x - m • D.w j' with hx'def
      have hx'L : toR x' ∈ D.Lsp j'.1 := by
        rw [hx'def, toR_sub, toR_smul]
        exact Submodule.sub_mem _ hL (Submodule.smul_mem _ _ (w_mem_Lsp D j'))
      have hcoord : D.cf j' (toR x') = D.cf j' (toR x) - (m : ℝ) * D.cf j' (toR (D.w j')) := by
        rw [hx'def, toR_sub, toR_smul, map_sub, map_smul]
        ring
      have hcontr : D.cf j' (toR x') = 0 := by
        by_contra h0
        have hM' : toR x' ∉ D.Msp j'.1 := fun hcontra =>
          h0 ((mem_Msp D).mp hcontra j' le_rfl)
        have h1 := w_min D j' hx'L hM'
        rw [hcoord] at h1
        have h2 : |D.cf j' (toR x) - (m : ℝ) * D.cf j' (toR (D.w j'))|
            < |D.cf j' (toR (D.w j'))| := hm
        linarith
      have hx'M : toR x' ∈ D.Msp j'.1 := by
        rw [mem_Msp]
        intro k hk
        rcases eq_or_lt_of_le hk with h | h
        · have hkj : k = j' := Fin.ext h.symm
          rw [hkj]; exact hcontr
        · have h1 := cf_eq_zero_of_mem_Lsp D hxM (by omega : j'.1 + 1 ≤ k.1)
          have h2 := cf_eq_zero_of_mem_Lsp D (w_mem_Lsp D j') h
          rw [hx'def, toR_sub, toR_smul, map_sub, map_smul, h1, h2]
          simp
      obtain ⟨c, hc⟩ := ih (by omega) x' hx'M
      refine ⟨fun k => c k + (if k = j' then m else 0), ?_⟩
      have hxeq : x = m • D.w j' + x' := by rw [hx'def]; abel
      rw [hxeq, ← hc]
      have hsum : ∑ k : Fin n, (c k + (if k = j' then m else 0)) • D.w k
          = (∑ k : Fin n, c k • D.w k) + ∑ k : Fin n, (if k = j' then m else 0) • D.w k := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun k _ => by rw [add_smul])
      have hsingle : ∑ k : Fin n, (if k = j' then m else 0) • D.w k = m • D.w j' := by
        rw [Finset.sum_eq_single j'
          (fun k _ hk => by simp [hk])
          (fun hnot => absurd (Finset.mem_univ j') hnot)]
        simp
      rw [hsum, hsingle, add_comm]

lemma exists_coeffs (x : Fin n → ℤ) : ∃ c : Fin n → ℤ, ∑ k : Fin n, c k • D.w k = x := by
  refine exists_coeffs_of_mem_Msp D n le_rfl x ?_
  rw [mem_Msp]
  intro k hk
  exact absurd k.2 (by omega)

/-- The matrix whose columns are the `w k`. -/
noncomputable def Wmat : Matrix (Fin n) (Fin n) ℤ := Matrix.of (fun i k => D.w k i)

/-- A right inverse of `Wmat`. -/
noncomputable def Vmat : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of (fun k i => Classical.choose (exists_coeffs D (Pi.single i (1 : ℤ))) k)

lemma Wmat_mul_Vmat : D.Wmat * D.Vmat = 1 := by
  ext i l
  have h := congrFun (Classical.choose_spec (exists_coeffs D (Pi.single l (1 : ℤ)))) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [Matrix.mul_apply]
  simp only [Wmat, Vmat, Matrix.of_apply]
  have h1 : ∑ k : Fin n, D.w k i * (Classical.choose (exists_coeffs D (Pi.single l (1 : ℤ)))) k
      = ((Pi.single l (1 : ℤ) : Fin n → ℤ)) i := by
    rw [← h]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [h1]
  by_cases hil : i = l <;> simp [Pi.single_apply, Matrix.one_apply, hil]

lemma isUnit_det_Wmat : IsUnit D.Wmat.det := by
  have hmul : D.Wmat.det * D.Vmat.det = 1 := by
    rw [← Matrix.det_mul, Wmat_mul_Vmat D, Matrix.det_one]
  exact (IsUnit.mul_iff.mp (by rw [hmul]; exact isUnit_one)).1

end RedData

end Work.BW

namespace Work.BW

lemma prod_range_cast (m : ℕ) :
    ∏ i ∈ Finset.range m, ((i : ℝ) + 1) = (m.factorial : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
      push_cast
      ring

lemma Finset.prod_le_prod_nonneg {ι : Type*} [DecidableEq ι] {s : Finset ι} {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hfs : 0 ≤ ∏ i ∈ s, f i :=
        Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have h1 : f a ≤ g a := h a (Finset.mem_insert_self a s)
      have h2 : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => h i (Finset.mem_insert_of_mem hi))
      nlinarith [h1, h2, hfa, hfs]

lemma prod_g_univ (n : ℕ) :
    ∏ j : Fin n, ((j.1 : ℝ) + 1) / 2 = (n.factorial : ℝ) / (2 : ℝ) ^ n := by
  rw [Fin.prod_univ_eq_prod_range (fun k => ((k : ℝ) + 1) / 2) n, Finset.prod_div_distrib]
  congr 1
  · exact prod_range_cast n
  · simp

lemma prod_g_erase {n : ℕ} [NeZero n] (hn : 0 < n) :
    ∏ j ∈ Finset.univ.erase (0 : Fin n), ((j.1 : ℝ) + 1) / 2
      = (n.factorial : ℝ) / (2 : ℝ) ^ (n - 1) := by
  have huniv := prod_g_univ n
  have h0 : (((0 : Fin n).1 : ℝ) + 1) / 2 = 1 / 2 := by simp
  have hsplit := (Finset.prod_erase_mul Finset.univ
    (fun j : Fin n => ((j.1 : ℝ) + 1) / 2) (Finset.mem_univ (0 : Fin n))).symm
  rw [hsplit, h0] at huniv
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have h2 : (n.factorial : ℝ) / (2 : ℝ) ^ n = ((n.factorial : ℝ) / (2 : ℝ) ^ (n - 1)) / 2 := by
    rw [hpow]; ring
  rw [h2] at huniv
  linarith

end Work.BW

namespace Work.BW

namespace RedData

variable {n : ℕ} (D : RedData n)

lemma prod_bound : ∏ j : Fin n, D.F (toR (D.w j)) ≤ (n.factorial : ℝ) / (2 : ℝ) ^ (n - 1) *
    ∏ j : Fin n, succMinL D.F (j.1 + 1) := by
  haveI : NeZero n := ⟨D.hn.ne'⟩
  have hpt : ∀ j : Fin n, D.F (toR (D.w j)) ≤
      (if j.1 = 0 then succMinL D.F 1 else ((j.1 : ℝ) + 1) / 2 * succMinL D.F (j.1 + 1)) :=
    fun j => w_bound D j
  refine le_trans (Finset.prod_le_prod_nonneg (fun j _ => D.hF.nonneg _) (fun j _ => hpt j)) ?_
  set A : ℝ := succMinL D.F 1 with hA
  set G : ℝ := ∏ j ∈ Finset.univ.erase (0 : Fin n), ((j.1 : ℝ) + 1) / 2 with hG
  set Lp : ℝ := ∏ j ∈ Finset.univ.erase (0 : Fin n), succMinL D.F (j.1 + 1) with hLp
  set f : Fin n → ℝ := fun j =>
    (if j.1 = 0 then A else ((j.1 : ℝ) + 1) / 2 * succMinL D.F (j.1 + 1)) with hf
  have hf0 : f 0 = A := by simp [hf]
  have hsplit : ∏ j : Fin n, f j = f 0 * ∏ j ∈ Finset.univ.erase (0 : Fin n), f j := by
    rw [eq_comm, mul_comm]
    exact Finset.prod_erase_mul Finset.univ f (Finset.mem_univ (0 : Fin n))
  have hinner : ∏ j ∈ Finset.univ.erase (0 : Fin n), f j
      = ∏ j ∈ Finset.univ.erase (0 : Fin n),
          (((j.1 : ℝ) + 1) / 2 * succMinL D.F (j.1 + 1)) := by
    refine Finset.prod_congr rfl (fun j hj => ?_)
    have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
    have hj1 : ¬ (j.1 = 0) := fun h => hj0 (Fin.ext h)
    simp only [hf]
    rw [if_neg hj1]
  have hLprod : A * Lp = ∏ j : Fin n, succMinL D.F (j.1 + 1) := by
    have h0 : succMinL D.F (((0 : Fin n).1) + 1) = A := by simp [hA]
    rw [hLp, ← h0, mul_comm]
    exact Finset.prod_erase_mul Finset.univ (fun j : Fin n => succMinL D.F (j.1 + 1))
      (Finset.mem_univ (0 : Fin n))
  have hgprod : ∏ j ∈ Finset.univ.erase (0 : Fin n), ((j.1 : ℝ) + 1) / 2
      = (n.factorial : ℝ) / (2 : ℝ) ^ (n - 1) := prod_g_erase D.hn
  rw [hsplit, hf0, hinner, Finset.prod_mul_distrib]
  refine le_of_eq ?_
  rw [← hG, ← hLp]
  rw [show A * (G * Lp) = G * (A * Lp) by ring, hLprod, ← hgprod]

end RedData

/-- **BW Lemma 4** (abstract form): given a lattice norm `F` on `ℤⁿ` and `ℝ`-independent lattice
vectors `u 0, …, u (n-1)` with `F (u k) ≤ λ_{k+1}`, there is a `ℤ`-basis `w` of `ℤⁿ` with
`∏ j, F (w j) ≤ n!/2^{n-1} · ∏ j, λ_{j+1}`. -/
theorem exists_basis_of_indep {n : ℕ} (hn : 0 < n) {F : (Fin n → ℝ) → ℝ} (hF : IsLatticeNorm F)
    (u : Fin n → (Fin n → ℤ)) (hind : LinearIndependent ℝ (fun k : Fin n => toR (u k)))
    (hbd : ∀ k : Fin n, F (toR (u k)) ≤ succMinL F (k.1 + 1)) :
    ∃ w : Fin n → (Fin n → ℤ), IsUnit (Matrix.of (fun i j => w j i)).det ∧
      ∏ j : Fin n, F (toR (w j)) ≤ (n.factorial : ℝ) / (2 : ℝ) ^ (n - 1) *
        ∏ j : Fin n, succMinL F (j.1 + 1) := by
  let D : RedData n := ⟨hn, F, hF, u, hind, hbd⟩
  exact ⟨D.w, D.isUnit_det_Wmat, D.prod_bound⟩

end Work.BW
