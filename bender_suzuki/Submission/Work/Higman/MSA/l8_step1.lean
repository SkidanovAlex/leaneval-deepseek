import Mathlib
import Submission.Work.Higman.MSA.l8_local
import Submission.Work.Higman.MSA.l8_triv
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.delta_uv_mem_powSub_four
import Submission.Work.Higman.Fq_structure
import Submission.Work.Higman.xi_pow_triv_omega1_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.MSA.L8

variable {P : Type} [Group P] [Finite P]

theorem mem_pow_xi {h : IsSuzuki2Grp P} {H : Subgroup P}
    (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) (k : ℕ) {y : P} (hy : y ∈ H) :
    (h.xi ^ k) y ∈ H := by
  induction k with
  | zero => simpa using hy
  | succ j ih =>
      have h2 : h.xi ((h.xi ^ j) y) ∈ H := by
        have h3 := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom ih
        rwa [hinv] at h3
      simpa [pow_succ', MulAut.mul_apply] using h2

theorem l8_collapse_mod_four {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) {k : ℕ}
    (hk1 : ∀ a ∈ A, (h.xi ^ k) a * a⁻¹ ∈ powSub A 2)
    (hk2 : ∀ b ∈ powSub A 2, (h.xi ^ k) b * b⁻¹ ∈ powSub A 4)
    {x : P} (hx : x ∈ C) {a : P} (ha : a ∈ A) :
    ((h.xi ^ k) x * x⁻¹) * a * ((h.xi ^ k) x * x⁻¹)⁻¹ * a⁻¹ ∈ powSub A 4 := by
  have hA4le : powSub A 4 ≤ A := powSub_le (by norm_num)
  have hA2le : powSub A 2 ≤ A := powSub_le (by norm_num)
  set X : P := (h.xi ^ k) x with hX
  set u : P := a⁻¹ * ((h.xi ^ k) a) with hu
  set c : P := ⁅x, a⁆ with hc
  set d : P := X * x⁻¹ with hd
  set w : P := a * ⁅X, u⁆ * a⁻¹ with hw
  set Q : P := (d * c * d⁻¹ * c⁻¹)⁻¹ * ((h.xi ^ k) c * c⁻¹) with hQ
  have hXmem : X ∈ C := by rw [hX]; exact mem_pow_xi S.hCinv k hx
  have hδmem : d ∈ C := by rw [hd]; exact C.mul_mem hXmem (C.inv_mem hx)
  have hCA2 : ⁅C, A⁆ = powSub A 2 := by
    rw [Subgroup.commutator_comm]
    show ⁅A, C⁆ = powSub A 2
    simpa [pow_zero, powSub_one_eq] using (commutator_powSub_A_C h S.hA S.hCn S.hC2 S.hCd 0)
  have hcA2 : c ∈ powSub A 2 := by
    rw [hc]
    exact hCA2 ▸ Subgroup.commutator_mem_commutator hx ha
  have hcA : c ∈ A := hA2le hcA2
  have hCAf : ⁅C, powSub A 2⁆ = powSub A 4 := by
    rw [Subgroup.commutator_comm]
    have hh := commutator_powSub_A_C h S.hA S.hCn S.hC2 S.hCd 1
    simpa using hh
  have hdc : d * c * d⁻¹ * c⁻¹ ∈ powSub A 4 := by
    have h1 : ⁅d, c⁆ ∈ powSub A 4 := by
      rw [← hCAf]
      exact Subgroup.commutator_mem_commutator hδmem hcA2
    simpa [commutatorElement_def] using h1
  have hηcc : (h.xi ^ k) c * c⁻¹ ∈ powSub A 4 := hk2 c hcA2
  have hQmem : Q ∈ powSub A 4 := by
    rw [hQ]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hdc) hηcc
  have hηaA : (h.xi ^ k) a ∈ A := mem_pow_xi S.hA.map_eq k ha
  have huA2 : u ∈ powSub A 2 := by
    rw [hu]
    have h1 := hk1 a ha
    exact (S.hA.abelian _ (A.inv_mem ha) _ hηaA) ▸ h1
  have hXu : ⁅X, u⁆ ∈ powSub A 4 := by
    rw [← hCAf]
    exact Subgroup.commutator_mem_commutator hXmem huA2
  have hwmem : w ∈ powSub A 4 := by
    rw [hw]
    exact (powSub_normal S.hA.normal 4).conj_mem ⁅X, u⁆ hXu a
  have hηa : (h.xi ^ k) a = a * u := by rw [hu]; group
  have hdecomp : d * a * d⁻¹ * a⁻¹ = c⁻¹ * Q * c * w⁻¹ := by
    rw [hQ, hw, hd, hc]
    simp only [commutatorElement_def, map_mul, map_inv]
    rw [hηa, ← hX]
    group
  have hcQ : c⁻¹ * Q * c = Q := by
    have hcomm : Q * c = c * Q := S.hA.abelian Q (hA4le hQmem) c hcA
    rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hdecomp, hcQ]
  exact Subgroup.mul_mem _ hQmem (Subgroup.inv_mem _ hwmem)

theorem l8_omega1_le_powSub_two_of_D {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) : omega1 P ≤ powSub A 2 := by
  have he2 : 2 ≤ S.e := S.he2
  rw [← S.htopA]
  exact powSub_le_of_dvd S.hA.abelian ⟨2 ^ (S.e - 2), by rw [mul_comm, ← pow_succ]; congr 1; omega⟩

theorem l8_powSub_two_ne_bot_of_D {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) : powSub A 2 ≠ ⊥ := by
  intro hbot
  have h1 : omega1 P ≤ (⊥ : Subgroup P) := (l8_omega1_le_powSub_two_of_D S).trans (le_of_eq hbot)
  have h2 : Nat.card ↥(omega1 P) = 1 := by rw [le_bot_iff.mp h1, Subgroup.card_bot]
  have h4 := h.omega1_card_ge_four
  rw [h2] at h4
  omega

theorem l8_xi_pow_card_sub_one_triv_mod_A2 {h : IsSuzuki2Grp P} {A C : Subgroup P}
    [hAn : A.Normal] (S : D h A C) :
    ∀ a ∈ A, (h.xi ^ (Nat.card ↥(omega1 P) - 1)) a * a⁻¹ ∈ powSub A 2 := by
  set k : ℕ := Nat.card ↥(omega1 P) - 1 with hk
  have hηΩ : ∀ w ∈ omega1 P, (h.xi ^ k) w = w := by
    intro w hw
    rw [hk]
    exact (xi_pow_triv_omega1_iff h (Nat.card ↥(omega1 P) - 1)).mpr dvd_rfl w hw
  intro a ha
  have hηaA : (h.xi ^ k) a ∈ A := mem_pow_xi S.hA.map_eq k ha
  have hbA : (h.xi ^ k) a * a⁻¹ ∈ A := A.mul_mem hηaA (A.inv_mem ha)
  refine (S.hkey _ hbA).mpr ?_
  have hcomm : Commute ((h.xi ^ k) a) a⁻¹ := S.hA.abelian _ hηaA _ (A.inv_mem ha)
  rw [hcomm.mul_pow, inv_pow]
  have hpow : ((h.xi ^ k) a) ^ 2 ^ (S.e - 1) = (h.xi ^ k) (a ^ 2 ^ (S.e - 1)) :=
    (map_pow (h.xi ^ k) a (2 ^ (S.e - 1))).symm
  rw [hpow, hηΩ _ (by rw [← S.htopA]; exact pow_mem_powSub (A := A) (n := 2 ^ (S.e - 1)) ha)]
  exact mul_inv_cancel _

theorem l8_xi_pow_card_sub_one_triv_mod_A4 {h : IsSuzuki2Grp P} {A C : Subgroup P}
    [hAn : A.Normal] (S : D h A C) :
    ∀ b ∈ powSub A 2, (h.xi ^ (Nat.card ↥(omega1 P) - 1)) b * b⁻¹ ∈ powSub A 4 := by
  set k : ℕ := Nat.card ↥(omega1 P) - 1 with hk
  have hηΩ : ∀ w ∈ omega1 P, (h.xi ^ k) w = w := by
    intro w hw
    rw [hk]
    exact (xi_pow_triv_omega1_iff h (Nat.card ↥(omega1 P) - 1)).mpr dvd_rfl w hw
  intro b hb
  have hbA : b ∈ A := powSub_le (by norm_num) hb
  have hηbA : (h.xi ^ k) b ∈ A := mem_pow_xi S.hA.map_eq k hbA
  have hηb2 : (h.xi ^ k) b ∈ powSub A 2 :=
    mem_pow_xi (map_powSub (h.xi : MulAut P) S.hA.map_eq 2) k hb
  have hβ2 : (h.xi ^ k) b * b⁻¹ ∈ powSub A 2 :=
    Subgroup.mul_mem _ hηb2 (Subgroup.inv_mem _ hb)
  refine (powSub_four_ker h S.hA S.he1 S.hkey hβ2).mpr ?_
  have hcomm : Commute ((h.xi ^ k) b) b⁻¹ := S.hA.abelian _ hηbA _ (A.inv_mem hbA)
  rw [hcomm.mul_pow, inv_pow]
  have hpow : ((h.xi ^ k) b) ^ 2 ^ (S.e - 2) = (h.xi ^ k) (b ^ 2 ^ (S.e - 2)) :=
    (map_pow (h.xi ^ k) b (2 ^ (S.e - 2))).symm
  rw [hpow]
  have hbOm : b ^ 2 ^ (S.e - 2) ∈ omega1 P := by
    have he2 : 2 ≤ S.e := S.he2
    have h1 : b ^ 2 ^ (S.e - 2) ∈ powSub A (2 * 2 ^ (S.e - 2)) := by
      have h2 := pow_mem_powSub (A := powSub A 2) (n := 2 ^ (S.e - 2)) hb
      rwa [powSub_powSub S.hA.abelian] at h2
    have h3 : 2 * 2 ^ (S.e - 2) = 2 ^ (S.e - 1) := by
      rw [mul_comm, ← pow_succ, show S.e - 2 + 1 = S.e - 1 from by omega]
    rw [h3, S.htopA] at h1
    exact h1
  rw [hηΩ _ hbOm]
  exact mul_inv_cancel _

theorem l8_xi_pow_card_sub_one_triv_quot {h : IsSuzuki2Grp P} {A C : Subgroup P}
    [hAn : A.Normal] (S : D h A C) :
    ∀ x ∈ C, (h.xi ^ (Nat.card ↥(omega1 P) - 1)) x * x⁻¹ ∈ A := by
  set k : ℕ := Nat.card ↥(omega1 P) - 1 with hk
  have hk1 := l8_xi_pow_card_sub_one_triv_mod_A2 (h := h) S
  have hk2 := l8_xi_pow_card_sub_one_triv_mod_A4 (h := h) S
  have hPC : ⁅(⊤ : Subgroup P), C⁆ ≤ A :=
    commutator_top_C_le h S.hA S.hCn S.hCinv S.hAC S.hCA S.hcover S.hC2 S.hCd S.hAne
  set Gs : Set P := (A : Set P) ∪ {e | ∃ y ∈ C, e = (h.xi ^ k) y * y⁻¹} with hGs
  set E : Subgroup P := Subgroup.closure Gs with hE
  have hAE : A ≤ E := fun a ha => Subgroup.subset_closure (Or.inl ha)
  have hEC : E ≤ C := by
    rw [hE, Subgroup.closure_le]
    rintro d (hd | ⟨y, hy, rfl⟩)
    · exact S.hAC hd
    · exact C.mul_mem (mem_pow_xi S.hCinv k hy) (C.inv_mem hy)
  have hξC : ∀ y ∈ C, h.xi y ∈ C := by
    intro y hy
    have h1 : h.xi y ∈ Subgroup.map (h.xi : MulAut P).toMonoidHom C := Subgroup.mem_map_of_mem _ hy
    rwa [S.hCinv] at h1
  have hgen : ∀ y ∈ C, h.xi ((h.xi ^ k) y * y⁻¹) = (h.xi ^ k) (h.xi y) * (h.xi y)⁻¹ := by
    intro y _
    have h1 : h.xi ((h.xi ^ k) y) = (h.xi ^ (k + 1)) y := by
      rw [← MulAut.mul_apply, ← pow_succ']
    have h2 : (h.xi ^ k) (h.xi y) = (h.xi ^ (k + 1)) y := by
      rw [← MulAut.mul_apply, ← pow_succ]
    simp only [map_mul, map_inv]
    rw [h1, h2]
  have hgen' : ∀ y ∈ C, (h.xi : MulAut P).symm ((h.xi ^ k) y * y⁻¹)
      = (h.xi ^ k) ((h.xi : MulAut P).symm y) * ((h.xi : MulAut P).symm y)⁻¹ := by
    intro y hy
    have h1 : h.xi ((h.xi ^ k) ((h.xi : MulAut P).symm y) * ((h.xi : MulAut P).symm y)⁻¹)
        = (h.xi : MulAut P) ((h.xi : MulAut P).symm ((h.xi ^ k) y * y⁻¹)) := by
      rw [hgen ((h.xi : MulAut P).symm y) (symm_mem_of_map_eq (h.xi : MulAut P) S.hCinv hy),
        MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    have h2 : (h.xi : MulAut P) ((h.xi : MulAut P).symm ((h.xi ^ k) y * y⁻¹))
        = (h.xi ^ k) y * y⁻¹ := MulEquiv.apply_symm_apply _ _
    exact h.xi.injective (by rw [h1, h2])
  have hEinv : Subgroup.map (h.xi : MulAut P).toMonoidHom E = E := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, hE, Subgroup.closure_le]
      rintro d (hd | ⟨y, hy, rfl⟩)
      · have h1 : h.xi d ∈ Subgroup.map (h.xi : MulAut P).toMonoidHom A :=
          Subgroup.mem_map_of_mem _ hd
        rw [S.hA.map_eq] at h1
        exact hAE h1
      · exact Subgroup.subset_closure (Or.inr ⟨h.xi y, hξC y hy, hgen y hy⟩)
    · rw [hE, Subgroup.closure_le]
      rintro d (hd | ⟨y, hy, rfl⟩)
      · refine Subgroup.mem_map.mpr ⟨(h.xi : MulAut P).symm d,
          hAE (symm_mem_of_map_eq (h.xi : MulAut P) S.hA.map_eq hd), ?_⟩
        exact MulEquiv.apply_symm_apply h.xi d
      · have hy' : (h.xi : MulAut P).symm y ∈ C :=
          symm_mem_of_map_eq (h.xi : MulAut P) S.hCinv hy
        refine Subgroup.mem_map.mpr ⟨(h.xi ^ k) ((h.xi : MulAut P).symm y)
          * ((h.xi : MulAut P).symm y)⁻¹,
          Subgroup.subset_closure (Or.inr ⟨(h.xi : MulAut P).symm y, hy', rfl⟩), ?_⟩
        show (h.xi : MulAut P)
            ((h.xi ^ k) ((h.xi : MulAut P).symm y) * ((h.xi : MulAut P).symm y)⁻¹)
          = (h.xi ^ k) y * y⁻¹
        rw [hgen ((h.xi : MulAut P).symm y) hy']
        simp
  have hEn : E.Normal := normal_of_le_of_contains hPC hAE hEC
  rcases S.hcover E hEn hEinv hAE hEC with hEA | hEC'
  · intro x hx
    have hmem : (h.xi ^ k) x * x⁻¹ ∈ E := Subgroup.subset_closure (Or.inr ⟨x, hx, rfl⟩)
    rw [hEA] at hmem
    exact hmem
  · exfalso
    have hA2ne := l8_powSub_two_ne_bot_of_D (h := h) S
    -- `[C,A] ≤ A⁴`
    have hCA2 : ⁅C, A⁆ = powSub A 2 := by
      rw [Subgroup.commutator_comm]
      show ⁅A, C⁆ = powSub A 2
      simpa [pow_zero, powSub_one_eq] using (commutator_powSub_A_C h S.hA S.hCn S.hC2 S.hCd 0)
    have hCA4 : ⁅C, A⁆ ≤ powSub A 4 := by
      rw [Subgroup.commutator_le]
      intro c hc a ha
      have hcE : c ∈ E := by rw [hEC']; exact hc
      have hcl : c * a * c⁻¹ * a⁻¹ ∈ powSub A 4 := by
        rw [hE] at hcE
        refine Subgroup.closure_induction (k := Gs)
          (p := fun z (_ : z ∈ Subgroup.closure Gs) => z * a * z⁻¹ * a⁻¹ ∈ powSub A 4)
          ?_ ?_ ?_ ?_ hcE
        · rintro z (hzA | ⟨y, hy, rfl⟩)
          · have hz : z * a * z⁻¹ * a⁻¹ = 1 := by rw [S.hA.abelian z hzA a ha]; group
            rw [hz]
            exact (powSub A 4).one_mem
          · exact l8_collapse_mod_four S hk1 hk2 hy ha
        · simp
        · intro x y hx hy ihx ihy
          have h1 : (x * y) * a * (x * y)⁻¹ * a⁻¹
              = (x * (y * a * y⁻¹ * a⁻¹) * x⁻¹) * (x * a * x⁻¹ * a⁻¹) := by group
          rw [h1]
          exact Subgroup.mul_mem _ ((powSub_normal S.hA.normal 4).conj_mem _ ihy x) ihx
        · intro x hx ihx
          have h1 : x⁻¹ * a * x⁻¹⁻¹ * a⁻¹ = x⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * x := by group
          rw [h1]
          simpa using (powSub_normal S.hA.normal 4).conj_mem _ (Subgroup.inv_mem _ ihx) x⁻¹
      simpa [commutatorElement_def] using hcl
    have hA2le4 : powSub A 2 ≤ powSub A 4 := by
      rw [← hCA2]; exact hCA4
    have hA2eq4 : powSub A 2 = powSub A 4 :=
      le_antisymm hA2le4 (powSub_le_of_dvd S.hA.abelian (by norm_num : 2 ∣ 4))
    -- iterate to reach exponent `2 ^ e`
    have hiter : ∀ j : ℕ, 1 ≤ j → powSub A 2 = powSub A (2 ^ j) := by
      intro j hj
      induction j with
      | zero => omega
      | succ m ih =>
          rcases Nat.eq_zero_or_pos m with hm | hm
          · subst hm; rw [pow_one]
          · have hstep : powSub A (2 ^ (m + 1)) = powSub (powSub A (2 ^ m)) 2 := by
              rw [pow_succ, powSub_powSub S.hA.abelian]
            rw [hstep, ← ih (by omega), powSub_powSub S.hA.abelian]
            norm_num
            exact hA2eq4
    have hbot : powSub A 2 = ⊥ := by
      rw [hiter S.e S.he]
      exact powSub_eq_bot_of_exp S.hA.abelian le_rfl S.he1
    exact hA2ne hbot

end Work.Higman.MSA.L8
