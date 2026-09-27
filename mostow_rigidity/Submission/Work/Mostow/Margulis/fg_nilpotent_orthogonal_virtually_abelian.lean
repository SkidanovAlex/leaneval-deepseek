import Mathlib
import Submission.Work.Mostow.Margulis.engel_frobenius_orthogonal
import Submission.Work.Mostow.Margulis.exists_pow_near_one
import Submission.Work.Mostow.Margulis.fg_nilpotent_finiteIndex_torsionFree

namespace Work.Mostow.Margulis

open scoped commutatorElement

set_option linter.style.haveILetI false

theorem commutator_pow_pow {G : Type*} [Group G] (u h : G) (k m : ℕ)
    (huc : u * (u * h * u⁻¹ * h⁻¹) = (u * h * u⁻¹ * h⁻¹) * u)
    (hhc : h * (u * h * u⁻¹ * h⁻¹) = (u * h * u⁻¹ * h⁻¹) * h) :
    u ^ k * h ^ m * (u ^ k)⁻¹ * (h ^ m)⁻¹ = (u * h * u⁻¹ * h⁻¹) ^ (k * m) := by
  have h1 : u ^ k * h * (u ^ k)⁻¹ = (u * h * u⁻¹ * h⁻¹) ^ k * h :=
    pow_conj_commutator u h (u * h * u⁻¹ * h⁻¹) rfl huc k
  have hCh : Commute ((u * h * u⁻¹ * h⁻¹) ^ k) h :=
    (show Commute h (u * h * u⁻¹ * h⁻¹) from hhc).symm.pow_left k
  have h2 : u ^ k * h ^ m * (u ^ k)⁻¹ = (u * h * u⁻¹ * h⁻¹) ^ (k * m) * h ^ m := by
    rw [← conj_pow, h1, hCh.mul_pow m, ← pow_mul]
  rw [h2, mul_assoc, mul_inv_cancel, mul_one]

theorem central_commutator_isOfFinOrder {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (A B : V ≃ₗᵢ[ℝ] V)
    (hAB : A * (A * B * A⁻¹ * B⁻¹) = (A * B * A⁻¹ * B⁻¹) * A)
    (hBA : B * (A * B * A⁻¹ * B⁻¹) = (A * B * A⁻¹ * B⁻¹) * B) :
    IsOfFinOrder (A * B * A⁻¹ * B⁻¹) := by
  obtain ⟨k, hk1, hk⟩ := exists_pow_near_one A (1 / 2) (by norm_num)
  obtain ⟨m, hm1, hm⟩ := exists_pow_near_one B (1 / 2) (by norm_num)
  have hpow := commutator_pow_pow A B k m hAB hBA
  have hABc : Commute A (A * B * A⁻¹ * B⁻¹) := hAB
  have hcomm : A ^ k * (A ^ k * B ^ m * (A ^ k)⁻¹ * (B ^ m)⁻¹)
      = (A ^ k * B ^ m * (A ^ k)⁻¹ * (B ^ m)⁻¹) * A ^ k := by
    rw [hpow]
    exact (hABc.pow_left k).pow_right (k * m)
  have heq : A ^ k * B ^ m = B ^ m * A ^ k :=
    engel_frobenius_orthogonal (A ^ k) (B ^ m) hk hm hcomm
  have h1 : (A * B * A⁻¹ * B⁻¹) ^ (k * m) = 1 := by
    rw [← hpow, heq]
    group
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨k * m, Nat.mul_pos hk1 hm1, h1⟩

theorem torsionFree_nilpotent_orthogonal_abelian {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {G : Type*} [Group G]
    (φ : G →* (V ≃ₗᵢ[ℝ] V)) (hφ : Function.Injective φ)
    (hnil : Group.IsNilpotent G) (htf : ∀ x : G, IsOfFinOrder x → x = 1) :
    ∀ a b : G, a * b = b * a := by
  have key : ∀ c : ℕ, (⊤ : Subgroup G).lowerCentralSeries (c + 1) = ⊥ →
      ∀ a b : G, a * b = b * a := by
    intro c
    induction c with
    | zero =>
        intro hbot a b
        have hle : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ ⊥ := le_of_eq hbot
        have hcab : ⁅a, b⁆ = 1 :=
          Subgroup.mem_bot.mp ((Subgroup.commutator_le.mp hle) a (Subgroup.mem_top a) b
            (Subgroup.mem_top b))
        exact commutatorElement_eq_one_iff_mul_comm.mp hcab
    | succ c ih =>
        intro hbot
        have hcomm0 : ⁅(⊤ : Subgroup G).lowerCentralSeries (c + 1), (⊤ : Subgroup G)⁆ = ⊥ := by
          rw [← Subgroup.lowerCentralSeries_succ]; exact hbot
        have hcen : (⊤ : Subgroup G).lowerCentralSeries (c + 1) ≤ Subgroup.center G := by
          intro x hx
          rw [Subgroup.mem_center_iff]
          intro y
          have h1 : ⁅x, y⁆ = 1 :=
            Subgroup.mem_bot.mp ((Subgroup.commutator_le.mp (le_of_eq hcomm0)) x hx y
              (Subgroup.mem_top y))
          exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
        have hEq : (⊤ : Subgroup G).lowerCentralSeries (c + 1) =
            Subgroup.closure {x | ∃ p ∈ (⊤ : Subgroup G).lowerCentralSeries c,
              ∃ q ∈ (⊤ : Subgroup G), ⁅p, q⁆ = x} := by
          ext x; exact Subgroup.mem_lowerCentralSeries_succ_iff (⊤ : Subgroup G) c x
        have hstep : (⊤ : Subgroup G).lowerCentralSeries (c + 1) = ⊥ := by
          rw [hEq]
          refine le_antisymm ?_ bot_le
          rw [Subgroup.closure_le]
          rintro x ⟨p, hp, q, hq, rfl⟩
          have hmem : ⁅p, q⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (c + 1) := by
            rw [hEq]; exact Subgroup.subset_closure ⟨p, hp, q, hq, rfl⟩
          have hcp := Subgroup.mem_center_iff.mp (hcen hmem) p
          have hcq := Subgroup.mem_center_iff.mp (hcen hmem) q
          have hfin : IsOfFinOrder (φ ⁅p, q⁆) := by
            have h := central_commutator_isOfFinOrder (φ p) (φ q) ?_ ?_
            · simpa [map_commutatorElement, commutatorElement_def] using h
            · have h' := congrArg φ hcp
              rw [map_mul, map_mul, map_commutatorElement] at h'
              simpa [commutatorElement_def] using h'
            · have h' := congrArg φ hcq
              rw [map_mul, map_mul, map_commutatorElement] at h'
              simpa [commutatorElement_def] using h'
          have hfin' : IsOfFinOrder ⁅p, q⁆ := (hφ.isOfFinOrder_iff).mp hfin
          exact Subgroup.mem_bot.mpr (htf _ hfin')
        exact ih hstep
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries (⊤ : Subgroup G)).mp
    (Group.isNilpotent_top.mpr hnil)
  rcases n with _ | m
  · intro a b
    have hbot : (⊤ : Subgroup G) = ⊥ := hn
    have ha : a = 1 := Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top a)
    have hb : b = 1 := Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top b)
    rw [ha, hb]
  · exact key m hn

theorem fg_nilpotent_orthogonal_virtually_abelian {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (P : Subgroup (V ≃ₗᵢ[ℝ] V))
    (hnil : Group.IsNilpotent P) (hfg : P.FG) :
    ∃ A : Subgroup P, A.FiniteIndex ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  haveI : Group.IsNilpotent P := hnil
  haveI : Group.FG P := (Group.fg_iff_subgroup_fg P).mpr hfg
  obtain ⟨A, hAfin, hAtf⟩ := fg_nilpotent_finiteIndex_torsionFree (G := P)
  have htf' : ∀ x : A, IsOfFinOrder x → x = 1 := by
    intro x hx
    have hx' : IsOfFinOrder (x : P) := by
      rw [isOfFinOrder_iff_pow_eq_one] at hx ⊢
      obtain ⟨n, hn, hxn⟩ := hx
      exact ⟨n, hn, by simpa using (Subtype.ext_iff.mp hxn)⟩
    exact Subtype.ext (hAtf (x : P) x.2 hx')
  have hinj : Function.Injective ((Subgroup.subtype P).comp (Subgroup.subtype A)) := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)
  have hcomm := torsionFree_nilpotent_orthogonal_abelian
    ((Subgroup.subtype P).comp (Subgroup.subtype A)) hinj inferInstance htf'
  refine ⟨A, hAfin, ?_⟩
  intro a ha b hb
  have h2 := hcomm ⟨a, ha⟩ ⟨b, hb⟩
  exact Subtype.ext_iff.mp h2


end Work.Mostow.Margulis
