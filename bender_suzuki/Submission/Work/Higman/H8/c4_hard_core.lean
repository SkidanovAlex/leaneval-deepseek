import Mathlib
import Submission.Work.Higman.higman9_case_deriv_le_sq
import Submission.Work.Higman.no_cent_elt_outside_maximal
import Submission.Work.Higman.H8.alt_pairing_false
import Submission.Work.Higman.no_square_derived
import Submission.Work.Higman.MSA.higman_lemma7_msa
import Submission.Work.Higman.H8.cw_cube_bound
import Submission.Work.Higman.H8.card_sub_one_dvd_xi
import Submission.Work.Higman.H8.c4_card_le
import Submission.Work.Higman.Q3.pow_sub_one_dvd_pow_sub_one_iff
import Submission.Work.Higman.homogeneous_structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.H8

open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

/-- **The `C₄` shape with `[P,D] ⊆ A²` is impossible.**

If `[D,D] = A²`, `A⁴ = 1`, `D ≤ P` and `[P,D] ⊆ A² = Ω₁(P)` (so that every commutator
`⁅u,d⁆` is an involution), then for every `u : P` and `d ∈ D` the identity
`⁅u ^ 2, d⁆ = ⁅u, ⁅u,d⁆⁆ ⁅u,d⁆ ^ 2` collapses to `⁅u ^ 2, d⁆ = 1`: both factors on the right are
`1` because `⁅u,d⁆ ∈ A² = Ω₁(P)` is central and an involution.  Hence `P ^ (2) ⊆ C_P(D)`, and
since `A = P ^ (2)` (as `[P,P] = A ⊆ P ^ (2) ⊆ A`) this gives `A ⊆ C_P(D)`, i.e.
`⁅A,D⁆ = ⊥`, against `⁅A,D⁆ = ⁅D,A⁆ = A² ≠ ⊥`. -/
theorem false_of_comm_le_powSub_two (h : IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : IsXiAbelNormal h A) (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥) (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hDd : ⁅D, D⁆ = Work.Higman.powSub A 2) (hAD : A ≤ D)
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hnZ : ¬(∀ e ∈ D, ∀ a ∈ A, e * a = a * e))
    (hcase : ⁅(⊤ : Subgroup P), D⁆ ≤ Work.Higman.powSub A 2) :
    False := by
  classical
  -- `A² = Ω₁(P)` is central and elementary abelian
  have hA2Z : Work.Higman.powSub A 2 ≤ Subgroup.center P := by
    rw [htop]; exact h.omega1_le_center
  have hA2inv : ∀ x ∈ Work.Higman.powSub A 2, x ^ 2 = 1 := by
    intro x hx
    exact h.mem_omega1.mp (htop ▸ hx)
  -- `[D,A] = A²`, hence `[A,D] = A²`
  have hDAeq : ⁅D, A⁆ = Work.Higman.powSub A 2 := by
    have hle : ⁅D, A⁆ ≤ Work.Higman.powSub A 2 :=
      (Subgroup.commutator_mono le_rfl hAD).trans (hDd ▸ le_rfl)
    have hinv : (⁅D, A⁆).map (h.xi : MulAut P).toMonoidHom = ⁅D, A⁆ := by
      rw [Subgroup.map_commutator, hDinv, IsXiAbelNormal.map_eq hA]
    have hne : ⁅D, A⁆ ≠ ⊥ := by
      intro hbot
      apply hnZ
      intro e he a ha
      have h1 : ⁅e, a⁆ ∈ (⊥ : Subgroup P) := by
        rw [← hbot]
        exact Subgroup.commutator_mem_commutator he ha
      exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)
    rcases Work.Higman.nsd_omega1_eq_bot_or_top_of_invariant h
      (htop ▸ hle) hinv with hb | hT
    · exact absurd hb hne
    · rw [hT]; exact htop.symm
  have hADeq : ⁅A, D⁆ = Work.Higman.powSub A 2 := by
    rw [Subgroup.commutator_comm]; exact hDAeq
  -- every square commutes with `D`
  have hsq_comm : ∀ u : P, ∀ v : P, v ∈ D → u ^ 2 * v = v * u ^ 2 := by
    intro u v hv
    have h1 : ⁅u, v⁆ ∈ Work.Higman.powSub A 2 :=
      hcase (Subgroup.commutator_mem_commutator (Subgroup.mem_top u) hv)
    have hmem : ⁅u, v⁆ ∈ Subgroup.center P := hA2Z h1
    have h2 : ⁅u, ⁅u, v⁆⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hmem u)
    have h3 : ⁅u, v⁆ ^ 2 = 1 := hA2inv _ h1
    have h4 : ⁅u ^ 2, v⁆ = 1 := by
      rw [Work.Higman.commutatorElement_sq_self u v, h2, h3, one_mul]
    have h5 : u ^ 2 * v * (u ^ 2)⁻¹ * v⁻¹ = 1 := by
      simpa [commutatorElement_def] using h4
    have h6 : u ^ 2 * v * (u ^ 2)⁻¹ = v := by
      calc u ^ 2 * v * (u ^ 2)⁻¹ = (u ^ 2 * v * (u ^ 2)⁻¹ * v⁻¹) * v := by group
        _ = 1 * v := by rw [h5]
        _ = v := one_mul v
    calc u ^ 2 * v = u ^ 2 * v * (u ^ 2)⁻¹ * u ^ 2 := by group
      _ = v * u ^ 2 := by rw [h6]
  -- `P ^ (2) = A`
  have hP2 : Work.Higman.powSub (⊤ : Subgroup P) 2 = A := by
    refine le_antisymm ?_ ?_
    · rw [Work.Higman.powSub, Subgroup.closure_le]
      rintro y ⟨x, -, rfl⟩
      exact hsq x
    · rw [← hGs, Subgroup.commutator_le]
      intro x _ y _
      exact Work.Higman.commutator_mem_powSub_top x y
  -- `P ^ (2) ≤ C_P(D)`, hence `A ≤ C_P(D)`
  have hP2C : Work.Higman.powSub (⊤ : Subgroup P) 2 ≤ Subgroup.centralizer (D : Set P) := by
    rw [Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    exact fun v hv => (hsq_comm x v hv).symm
  have hAC : A ≤ Subgroup.centralizer (D : Set P) := hP2 ▸ hP2C
  -- contradiction with `⁅A,D⁆ = A² ≠ ⊥`
  have hbot : ⁅A, D⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hAC
  have hA2ne : Work.Higman.powSub A 2 ≠ ⊥ := by
    intro hb
    have h1 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by rw [← htop, hb]; simp
    have h2 := h.omega1_card_ge_four
    omega
  exact hA2ne (hADeq ▸ hbot)

/-- **The hard core of `c4_exclusion_sq`.**  The `C₄` setting with `[D,D] = A²`,
`Φ(D) = D² ⊔ [D,D] = A²` and `D` not centralising `A`.  Then contradiction. -/
theorem c4_hard_core (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A ≤ D) (hADne : D ≠ A)
    (hDd : ⁅D, D⁆ = Work.Higman.powSub A 2)
    (hcover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ D → E = A ∨ E = D)
    (hPhi : Work.Higman.powSub D 2 ⊔ ⁅D, D⁆ = Work.Higman.powSub A 2)
    (hnZ : ¬(∀ e ∈ D, ∀ a ∈ A, e * a = a * e)) :
    False := by
  classical
  -- Case analysis on `[P,D]`
  by_cases hcase : ⁅(⊤ : Subgroup P), D⁆ ≤ Work.Higman.powSub A 2
  · exact false_of_comm_le_powSub_two h hA hGs hsq hA4 htop hDd hAD hDinv hnZ hcase
  · -- Case II: `[P,D] = A`
    have hA2ne : Work.Higman.powSub A 2 ≠ ⊥ := by
      intro hb
      have h1 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by rw [← htop, hb]; simp
      have h2 := h.omega1_card_ge_four
      omega
    -- `[P,D] = A`
    have hDP : ⁅(⊤ : Subgroup P), D⁆ = A := by
      have hle : ⁅(⊤ : Subgroup P), D⁆ ≤ A :=
        (Subgroup.commutator_mono (le_refl (⊤ : Subgroup P)) le_top).trans (le_of_eq hGs)
      have hge : Work.Higman.powSub A 2 ≤ ⁅(⊤ : Subgroup P), D⁆ := by
        rw [← hDd]; exact Subgroup.commutator_mono le_top le_rfl
      have hinv : (⁅(⊤ : Subgroup P), D⁆).map (h.xi : MulAut P).toMonoidHom
          = ⁅(⊤ : Subgroup P), D⁆ := by
        rw [Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective, hDinv]
      rcases Work.Higman.xi_invariant_eq_powSub_two_or_self h hA hle hge hinv with h1 | h2
      · exact absurd (le_of_eq h1) hcase
      · exact h2
    -- `[D,A] = A²`
    have hDAeq : ⁅D, A⁆ = Work.Higman.powSub A 2 := by
      have hle : ⁅D, A⁆ ≤ Work.Higman.powSub A 2 :=
        (Subgroup.commutator_mono le_rfl hAD).trans (hDd ▸ le_rfl)
      have hinv : (⁅D, A⁆).map (h.xi : MulAut P).toMonoidHom = ⁅D, A⁆ := by
        rw [Subgroup.map_commutator, hDinv, IsXiAbelNormal.map_eq hA]
      have hne : ⁅D, A⁆ ≠ ⊥ := by
        intro hbot
        apply hnZ
        intro e he a ha
        have h1 : ⁅e, a⁆ ∈ (⊥ : Subgroup P) := by
          rw [← hbot]
          exact Subgroup.commutator_mem_commutator he ha
        exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)
      rcases Work.Higman.nsd_omega1_eq_bot_or_top_of_invariant h
        (hle.trans (htop ▸ le_rfl)) hinv with hb | hT
      · exact absurd hb hne
      · rw [hT]; exact htop.symm
    -- `[A,P] = A²`
    have hAP : ⁅A, (⊤ : Subgroup P)⁆ = Work.Higman.powSub A 2 := by
      have hle : ⁅A, (⊤ : Subgroup P)⁆ ≤ Work.Higman.powSub A 2 :=
        Work.Higman.nsd_comm_le h (IsXiAbelNormal.map_eq hA) (IsXiAbelNormal.abelian hA) hGs
      have hge : Work.Higman.powSub A 2 ≤ ⁅A, (⊤ : Subgroup P)⁆ := by
        rw [← hDAeq, Subgroup.commutator_comm]
        exact Subgroup.commutator_mono le_rfl le_top
      exact le_antisymm hle hge
    -- `Z(P) = A²`
    have hZP : Subgroup.center P = Work.Higman.powSub A 2 := by
      have hZleA : Subgroup.center P ≤ A := Work.Higman.center_le_of_maximal h hA hmax
      have hA2leZ : Work.Higman.powSub A 2 ≤ Subgroup.center P := by
        rw [htop]; exact h.omega1_le_center
      have hZinv : (Subgroup.center P).map (h.xi : MulAut P).toMonoidHom
          = Subgroup.center P := by
        refine le_antisymm ?_ ?_
        · rintro x ⟨z, hz, rfl⟩
          exact Work.Higman.aut_mem_center (h.xi : MulAut P) hz
        · intro x hx
          exact ⟨(h.xi : MulAut P).symm x,
            Work.Higman.aut_mem_center (h.xi : MulAut P).symm hx, by simp⟩
      rcases Work.Higman.xi_invariant_eq_powSub_two_or_self h hA hZleA hA2leZ hZinv with h1 | h2
      · exact h1
      · exfalso
        have hbot : ⁅A, (⊤ : Subgroup P)⁆ = ⊥ := by
          refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
          intro a ha
          rw [Subgroup.mem_centralizer_iff]
          intro y _
          exact Subgroup.mem_center_iff.mp (h2 ▸ ha) y
        exact hA2ne (hAP ▸ hbot)
    -- `P² = A`
    have hP2 : Work.Higman.powSub (⊤ : Subgroup P) 2 = A := by
      refine le_antisymm ?_ ?_
      · rw [Work.Higman.powSub, Subgroup.closure_le]
        rintro y ⟨x, -, rfl⟩
        exact hsq x
      · rw [← hGs, Subgroup.commutator_le]
        intro x _ y _
        exact Work.Higman.commutator_mem_powSub_top x y
    -- `Z(D) = A²`
    have hZD : D ⊓ Subgroup.centralizer (D : Set P) = Work.Higman.powSub A 2 := by
      have hcomm : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ A := by
        intro x y
        rw [← hGs]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      have hleA : D ⊓ Subgroup.centralizer (D : Set P) ≤ A := by
        intro z hz
        by_contra hzA
        exact Work.Higman.no_cent_elt_outside_maximal h hA hmax hDn hDinv hAD hcomm hz.1
          (fun y hy => Subgroup.mem_centralizer_iff.mp hz.2 y hy) hzA
      have hA2leD : Work.Higman.powSub A 2 ≤ D ⊓ Subgroup.centralizer (D : Set P) := by
        intro z hz
        refine Subgroup.mem_inf.mpr
          ⟨hAD ((Work.Higman.powSub_le (A := A) (n := 2) (by norm_num)) hz), ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact Subgroup.mem_center_iff.mp (h.omega1_le_center (htop ▸ hz)) y
      have hinv : (D ⊓ Subgroup.centralizer (D : Set P)).map (h.xi : MulAut P).toMonoidHom
          = D ⊓ Subgroup.centralizer (D : Set P) :=
        Work.Higman.map_inf_centralizer_eq (h.xi : MulAut P) hDinv
      rcases Work.Higman.xi_invariant_eq_powSub_two_or_self h hA hleA hA2leD hinv with h1 | h2
      · exact h1
      · exfalso
        apply hnZ
        intro e he a ha
        have hmem : a ∈ D ⊓ Subgroup.centralizer (D : Set P) := h2 ▸ ha
        exact Subgroup.mem_centralizer_iff.mp hmem.2 e he
    -- `|D| = |Ω₁(P)|³`
    have hDcard : Nat.card ↥D = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := by
      obtain ⟨n, hn⟩ := h.exists_card_omega1_eq_two_pow
      obtain ⟨e, he⟩ := (h.isPGroup.to_subgroup D).exists_card_eq
      have hq4 : 4 ≤ 2 ^ n := by rw [← hn]; exact h.omega1_card_ge_four
      have hnpos : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0; norm_num at hq4
        · exact hpos
      -- the orbit count `2 ^ n - 1 ∣ |D| - 1`
      have hdiv : 2 ^ n - 1 ∣ 2 ^ e - 1 := by
        rw [← hn, ← he]
        exact Work.Higman.H8.card_sub_one_dvd_xi h hDinv
      -- hence `n ∣ e`
      have hned : n ∣ e :=
        (Work.Higman.Q3.pow_sub_one_dvd_pow_sub_one_iff (x := 2) (m := n) (k := e)
          (by norm_num) hnpos).mp hdiv
      -- Chevalley--Warning for `D`: `|D| ≤ (2 ^ n) ^ 3`
      have hDle : Nat.card ↥D ≤ (2 ^ n) ^ 3 := by
        rw [← hn]
        refine Work.Higman.H8.card_le_cube_of_sq_le_omega1 h ?_ ?_ ?_
        · rw [← htop]
          exact (Work.Higman.powSub_le (A := A) (n := 2) (by norm_num)).trans hAD
        · rw [← htop]
          exact le_sup_left.trans_eq hPhi
        · rw [← htop, hDd]
      -- `|A| < |D|`
      have hlt : Nat.card ↥A < Nat.card ↥D := by
        have hne : A.subgroupOf D ≠ ⊤ := by
          intro hc
          exact hADne (le_antisymm (Subgroup.subgroupOf_eq_top.mp hc) hAD)
        have hcard : Nat.card ↥(A.subgroupOf D) = Nat.card ↥A :=
          Nat.card_congr
            { toFun := fun x => (⟨((x : ↥D) : P), x.2⟩ : ↥A)
              invFun := fun a => (⟨⟨(a : P), hAD a.2⟩, a.2⟩ : ↥(A.subgroupOf D))
              left_inv := fun x => Subtype.ext rfl
              right_inv := fun a => Subtype.ext rfl }
        have h1 : Nat.card ↥(A.subgroupOf D) < Nat.card ↥D := by
          have h2 : (A.subgroupOf D : Set ↥D) ≠ Set.univ := fun h' =>
            hne (SetLike.coe_set_eq.mp h')
          have h3 := Set.ncard_lt_card (α := ↥D) h2
          rwa [← Nat.card_coe_set_eq ((A.subgroupOf D) : Set ↥D)] at h3
        rwa [hcard] at h1
      -- `|D| > |A| = (2 ^ n) ^ 2`, so `2 * n < e`
      have hgt : 2 ^ (2 * n) < 2 ^ e := by
        have hAcard : Nat.card ↥A = (2 ^ n) ^ 2 := by rw [hcard, hn]
        calc 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
          _ = Nat.card ↥A := hAcard.symm
          _ < Nat.card ↥D := hlt
          _ = 2 ^ e := he
      have he2n : 2 * n < e := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hgt
      -- `e ≤ 3 * n`
      have hele : e ≤ 3 * n := by
        have h1 : 2 ^ e ≤ 2 ^ (3 * n) := by
          calc 2 ^ e = Nat.card ↥D := he.symm
            _ ≤ (2 ^ n) ^ 3 := hDle
            _ = 2 ^ (3 * n) := by rw [← pow_mul, Nat.mul_comm]
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
      -- hence `e = 3 * n`
      have he3 : e = 3 * n := by
        rcases hned with ⟨c, hc⟩
        have hc3 : c = 3 := by
          have hcle : c ≤ 3 := by
            have hle' : n * c ≤ n * 3 := by
              rw [← hc]
              exact hele.trans (le_of_eq (Nat.mul_comm 3 n))
            exact Nat.le_of_mul_le_mul_left hle' hnpos
          have hcge : 3 ≤ c := by
            by_contra hcon
            push_neg at hcon
            interval_cases c <;> (rw [hc] at he2n <;> omega)
          omega
        rw [hc, hc3, Nat.mul_comm]
      rw [he, he3, hn, ← pow_mul, Nat.mul_comm]
    -- `|P| = |D|`, so `D = ⊤`
    have hPle : Nat.card P ≤ (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 :=
      Work.Higman.H8.c4_card_le h
    have hDPle : Nat.card ↥D ≤ Nat.card P :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card D)
    have hPeq : Nat.card P = Nat.card ↥D := le_antisymm (by rw [hDcard]; exact hPle) hDPle
    have hDtop : D = ⊤ := Subgroup.eq_top_of_card_eq D hPeq.symm
    -- `A = A²`, contradiction
    have hAeq : A = Work.Higman.powSub A 2 :=
      calc A = ⁅(⊤ : Subgroup P), ⊤⁆ := hGs.symm
        _ = ⁅D, D⁆ := by rw [hDtop]
        _ = Work.Higman.powSub A 2 := hDd
    have hAne2 : A ≠ Work.Higman.powSub A 2 := by
      intro hEq
      have h1 : Nat.card ↥A = Nat.card ↥(Work.Higman.powSub A 2) :=
        congrArg (fun s : Subgroup P => Nat.card ↥s) hEq
      rw [htop] at h1
      have hkey : Nat.card ↥(Work.Higman.omega1 P) = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 :=
        calc Nat.card ↥(Work.Higman.omega1 P) = Nat.card ↥A := h1.symm
          _ = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 := hcard
      have h4 := h.omega1_card_ge_four
      have hq2 : Nat.card ↥(Work.Higman.omega1 P)
          * (Nat.card ↥(Work.Higman.omega1 P) - 1) = 0 := by nlinarith [hkey]
      have hpos : 0 < Nat.card ↥(Work.Higman.omega1 P)
          * (Nat.card ↥(Work.Higman.omega1 P) - 1) :=
        Nat.mul_pos Nat.card_pos (by omega)
      omega
    exact hAne2 hAeq

end Work.Higman.H8
