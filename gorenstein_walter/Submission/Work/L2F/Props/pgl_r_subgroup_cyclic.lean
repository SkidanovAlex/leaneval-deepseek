import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs
import Submission.Work.L2F.Torus.centralizer_pslMap_eq
import Submission.Work.L2F.Torus.centralizer_equiv_hypTorus
import Submission.Work.L2F.Torus.disc_ne_zero
import Submission.Work.L2F.Conic.hypTorus_cyclic
import Submission.Work.DSTR.D16.pgl2_psl_index_two

namespace Work.L2F.Props

open Subgroup (centralizer)
open Matrix Polynomial

/-- A finite `r`-group is cyclic as soon as the centralizer of each of its order-`r` elements
is cyclic. -/
theorem isCyclic_of_isPGroup_centralizer {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    {P : Subgroup G} (hP : IsPGroup r P)
    (h : ∀ t : G, t ∈ P → orderOf t = r → IsCyclic (Subgroup.centralizer ({t} : Set G))) :
    IsCyclic P := by
  rcases eq_or_ne P ⊥ with hbot | hbot
  · rw [hbot]; infer_instance
  · haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hbot
    haveI : Nontrivial ↥(Subgroup.center ↥P) := IsPGroup.center_nontrivial hP
    obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(Subgroup.center ↥P))
    have hzcen : (c : ↥P) ∈ Subgroup.center ↥P := c.2
    have hzne : (c : ↥P) ≠ 1 := fun he => hc1 (Subtype.ext he)
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hP) (c : ↥P)
    have hjpos : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0, pow_zero] at hj
        exact absurd (orderOf_eq_one_iff.mp hj) hzne
      · exact h0
    obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [hi] at hj
    set tc : ↥P := (c : ↥P) ^ (r ^ i) with htcdef
    have htcmem : tc ∈ Subgroup.center ↥P := Subgroup.pow_mem _ hzcen _
    have ht_r : tc ^ r = 1 := by
      rw [htcdef, ← pow_mul, ← pow_succ r i, ← hj, pow_orderOf_eq_one]
    have ht_ne : tc ≠ 1 := by
      rw [htcdef]
      intro h1
      have hdvd : orderOf (c : ↥P) ∣ r ^ i := orderOf_dvd_iff_pow_eq_one.mpr h1
      rw [hj, pow_succ r i] at hdvd
      have hpos : 0 < r ^ i := pow_pos (Fact.out : Nat.Prime r).pos i
      have hrdvd : r ∣ 1 := (Nat.mul_dvd_mul_iff_left hpos).mp (by simpa using hdvd)
      exact (Fact.out : Nat.Prime r).not_dvd_one hrdvd
    have htord : orderOf tc = r := orderOf_eq_prime ht_r ht_ne
    have hle : P ≤ Subgroup.centralizer ({(tc : G)} : Set G) := by
      intro p hp
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm : (⟨p, hp⟩ : ↥P) * tc = tc * ⟨p, hp⟩ := (Subgroup.mem_center_iff.mp htcmem) ⟨p, hp⟩
      exact congrArg (fun w : ↥P => (w : G)) hcomm
    haveI : IsCyclic ↥(Subgroup.centralizer ({(tc : G)} : Set G)) :=
      h (tc : G) tc.2 (by rw [Subgroup.orderOf_coe]; exact htord)
    exact Subgroup.isCyclic_of_le hle

/-- In odd characteristic, the centralizer of an element of order `r ≠ 2` of `PSL(2,F)` is
cyclic (it is the image of a torus of `SL(2,F)`). -/
theorem psl_centralizer_cyclic (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (r : ℕ)
    [Fact r.Prime] (hr : (r : F) ≠ 0) (hr2 : r ≠ 2)
    (t : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (ht : orderOf t = r) :
    IsCyclic (Subgroup.centralizer ({t} :
      Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))) := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) t
  have hx' : Work.PSL2.pslMap F x = t := hx
  have hxord : orderOf (Work.PSL2.pslMap F x) = r := by rw [hx', ht]
  haveI : Fact (Nat.Prime (ringChar F)) := ⟨CharP.prime_ringChar F⟩
  have hrc2 : ringChar F ≠ 2 := by
    intro hc
    exact h2 ((CharP.cast_eq_zero_iff F (ringChar F) 2).mpr (by rw [hc]))
  have hodd : Odd (ringChar F) := (CharP.prime_ringChar F).odd_of_ne_two hrc2
  have hrp : r ≠ ringChar F := by
    intro h
    rw [h] at hr
    exact hr (CharP.cast_eq_zero F (ringChar F))
  have hD : Work.L2F.Torus.disc F x ≠ 0 :=
    Work.L2F.Torus.disc_ne_zero F (ringChar F) r hodd x (Fact.out) hrp hxord
  haveI hcyc : IsCyclic (Work.L2F.Torus.cent F x) :=
    (MulEquiv.isCyclic (Classical.choice
      (Work.L2F.Torus.centralizer_equiv_hypTorus F h2 x hD))).mpr
      (Work.L2F.Conic.hypTorus_cyclic F h2 (Work.L2F.Torus.disc F x) hD)
  have hcyc2 : IsCyclic ↥((Work.L2F.Torus.cent F x).map (Work.PSL2.pslMap F)) := by
    have hrange : ((Work.PSL2.pslMap F).comp (Work.L2F.Torus.cent F x).subtype).range
        = (Work.L2F.Torus.cent F x).map (Work.PSL2.pslMap F) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    haveI : IsCyclic ↥(((Work.PSL2.pslMap F).comp
        (Work.L2F.Torus.cent F x).subtype).range) :=
      isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    exact hrange ▸ this
  rw [← hx', Work.L2F.Torus.centralizer_pslMap_eq F h2 x r (Fact.out) hr2 hxord]
  exact hcyc2

/-- Reduction to `PSL(2,F)` for odd characteristic: an odd `r`-subgroup of `PGL(2,F)` lies in
the image of `SL(2,F)` (a subgroup of index two). -/
theorem le_toPGL_range (F : Type*) [Field F] [Fintype F] (hchar : ringChar F ≠ 2)
    (r : ℕ) [Fact r.Prime] (hr2 : r ≠ 2) (P : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F))
    (hP : IsPGroup r P) :
    P ≤ (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 2) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hidx : (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.index = 2 :=
    Work.DSTR.D16.index_range_toPGL hchar
  haveI : (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.Normal :=
    Subgroup.normal_of_index_eq_two hidx
  have hmap : Nat.card (P.map (QuotientGroup.mk'
      (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)) ∣ 2 := by
    have h1 : Nat.card (P.map (QuotientGroup.mk'
        (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)) ∣
        Nat.card (Matrix.ProjGenLinGroup (Fin 2) F ⧸
          (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) :=
      Subgroup.card_subgroup_dvd_card _
    rw [← Subgroup.index_eq_card (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range,
      hidx] at h1
    exact h1
  have hk : ∃ k, Nat.card (P.map (QuotientGroup.mk'
      (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)) = r ^ k :=
    IsPGroup.iff_card.mp (IsPGroup.map hP (QuotientGroup.mk'
      (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range))
  obtain ⟨k, hk⟩ := hk
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact h0
    · exfalso
      have hrk : r ^ k ∣ 2 := hk ▸ hmap
      have hle : r ^ k ≤ 2 := Nat.le_of_dvd (by norm_num) hrk
      have hr3 : 3 ≤ r := by
        have := (Fact.out : Nat.Prime r).two_le
        omega
      have hge : r ≤ r ^ k := Nat.le_self_pow (Nat.pos_iff_ne_zero.mp h0) r
      omega
  have hcard1 : Nat.card (P.map (QuotientGroup.mk'
      (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)) = 1 := by
    rw [hk, hk0, pow_zero]
  have hbot : P.map (QuotientGroup.mk'
      (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) = ⊥ :=
    Subgroup.card_eq_one.mp hcard1
  rw [Subgroup.map_eq_bot_iff] at hbot
  rwa [QuotientGroup.ker_mk'] at hbot

/-- Every `r`-subgroup of `PSL(2,F)` (`r` odd, `r ≠ ringChar F`, `F` finite) is cyclic. -/
theorem isCyclic_subgroup_psl (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (r : ℕ)
    [Fact r.Prime] (hr : (r : F) ≠ 0) (hr2 : r ≠ 2)
    (P : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) (hP : IsPGroup r P) :
    IsCyclic P :=
  isCyclic_of_isPGroup_centralizer hP
    (fun t _ ht => psl_centralizer_cyclic F h2 r hr hr2 t ht)

/-- Every `r`-subgroup of `PGL(2,F)` (`F` finite, `r` odd, `r ≠ ringChar F`) is cyclic;
odd characteristic case, by reduction to `PSL(2,F)`. -/
theorem isCyclic_subgroup_pgl_odd (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (r : ℕ) [Fact r.Prime] (hr : (r : F) ≠ 0) (hr2 : r ≠ 2)
    (P : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)) (hP : IsPGroup r P) : IsCyclic P := by
  have hchar : ringChar F ≠ 2 := by
    intro hc
    haveI : CharP F 2 := by rw [← hc]; exact ringChar.charP F
    exact h2 (CharP.cast_eq_zero F 2)
  have hPL : P ≤ (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    le_toPGL_range F hchar r hr2 P hP
  obtain ⟨e⟩ := Work.DSTR.D16.range_toPGL_mulEquiv_PSL (F := F)
  let L : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F) :=
    (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
  have hQ : IsPGroup r ↥(P.subgroupOf L) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm
  have hP' : IsPGroup r ↥((P.subgroupOf L).map e.toMonoidHom) := hQ.map e.toMonoidHom
  have hcyc' : IsCyclic ↥((P.subgroupOf L).map e.toMonoidHom) :=
    isCyclic_subgroup_psl F h2 r hr hr2 _ hP'
  exact (MulEquiv.isCyclic
    ((Subgroup.equivMapOfInjective (P.subgroupOf L) e.toMonoidHom e.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hPL))).mp hcyc'

section CharTwoAux

variable {F : Type*} [Field F]

theorem mul_self_eq_trace_smul_sub_det_smul_one (M : Matrix (Fin 2) (Fin 2) F) :
    M * M = M.trace • M - M.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem trace_smul_one_add (h2 : (2 : F) = 0) (M : Matrix (Fin 2) (Fin 2) F) (A B : F) :
    (A • (1 : Matrix (Fin 2) (Fin 2) F) + B • M).trace = B * M.trace := by
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul, smul_eq_mul]
  rw [show ((2 : ℕ) : F) = 0 from by simpa using h2, mul_zero, zero_add]

theorem apply00_smul_one_add (M : Matrix (Fin 2) (Fin 2) F) (A B : F) :
    (A • (1 : Matrix (Fin 2) (Fin 2) F) + B • M) 0 0 = A + B * M 0 0 := by
  simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem det_smul_one_add_smul (M : Matrix (Fin 2) (Fin 2) F) (A B : F) :
    (A • (1 : Matrix (Fin 2) (Fin 2) F) + B • M).det =
      A ^ 2 + A * B * M.trace + B ^ 2 * M.det := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

/-- **The centralizer of a non-scalar `2 × 2` matrix is the algebra it generates.** -/
theorem eq_smul_one_add_smul_of_mul_comm
    (X Y : Matrix (Fin 2) (Fin 2) F) (hX : ∀ c : F, X ≠ c • 1) (hcomm : Y * X = X * Y) :
    ∃ a b : F, Y = a • 1 + b • X := by
  have e00 : Y 0 1 * X 1 0 = X 0 1 * Y 1 0 := by
    have h := congrFun (congrFun hcomm 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  have e01 : Y 0 0 * X 0 1 + Y 0 1 * X 1 1 = X 0 0 * Y 0 1 + X 0 1 * Y 1 1 := by
    have h := congrFun (congrFun hcomm 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
    exact h
  have e10 : Y 1 1 * X 1 0 = X 1 0 * Y 0 0 + X 1 1 * Y 1 0 - Y 1 0 * X 0 0 := by
    have h := congrFun (congrFun hcomm 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  have e11 : Y 1 0 * X 0 1 = X 1 0 * Y 0 1 := by
    have h := congrFun (congrFun hcomm 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  rcases eq_or_ne (X 1 0) 0 with h10 | h10
  · rcases eq_or_ne (X 0 1) 0 with h01 | h01
    · have hne : X 0 0 ≠ X 1 1 := by
        intro hd
        exact hX (X 0 0) (by ext i j; fin_cases i <;> fin_cases j <;> simp [h10, h01, hd])
      have hy01 : Y 0 1 = 0 := by
        have h := e01
        rw [h01, mul_zero, zero_mul, add_zero, zero_add] at h
        rw [mul_comm (X 0 0) (Y 0 1)] at h
        have h2 : Y 0 1 * (X 1 1 - X 0 0) = 0 := by rw [mul_sub, h, sub_self]
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact h3
        · exact absurd (sub_eq_zero.mp h3) (Ne.symm hne)
      have hy10 : Y 1 0 = 0 := by
        have h := e10
        rw [h10, mul_zero, zero_mul, zero_add] at h
        rw [mul_comm (X 1 1) (Y 1 0)] at h
        have h2 : Y 1 0 * (X 1 1 - X 0 0) = 0 := by rw [mul_sub, ← h]
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact h3
        · exact absurd (sub_eq_zero.mp h3) (Ne.symm hne)
      refine ⟨Y 0 0 - (Y 0 0 - Y 1 1) / (X 0 0 - X 1 1) * X 0 0,
        (Y 0 0 - Y 1 1) / (X 0 0 - X 1 1), ?_⟩
      have hsub : X 0 0 - X 1 1 ≠ 0 := sub_ne_zero.mpr hne
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
          hy01, hy10, h01, h10] <;> field_simp <;> ring
    · have hy10 : Y 1 0 = 0 := by
        have h := e11
        rw [h10, zero_mul] at h
        rcases mul_eq_zero.mp h with h2 | h2
        · exact h2
        · exact absurd h2 h01
      have hy11 : Y 1 1 = Y 0 0 - Y 0 1 / X 0 1 * X 0 0 + Y 0 1 / X 0 1 * X 1 1 := by
        field_simp
        linear_combination -e01
      refine ⟨Y 0 0 - Y 0 1 / X 0 1 * X 0 0, Y 0 1 / X 0 1, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
          hy10, hy11, h10] <;> field_simp <;> ring
  · have hy01 : Y 0 1 = Y 1 0 / X 1 0 * X 0 1 := by
      field_simp
      linear_combination e00
    have hy11 : Y 1 1 = Y 0 0 - Y 1 0 / X 1 0 * X 0 0 + Y 1 0 / X 1 0 * X 1 1 := by
      field_simp
      linear_combination e10
    refine ⟨Y 0 0 - Y 1 0 / X 1 0 * X 0 0, Y 1 0 / X 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        hy01, hy11] <;> field_simp <;> ring


theorem sl_centralizer_cyclic_char_two (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) = 0)
    (r : ℕ) [Fact r.Prime] (hr2 : r ≠ 2) (t : Matrix.SpecialLinearGroup (Fin 2) F)
    (ht : orderOf t = r) :
    IsCyclic (Subgroup.centralizer ({t} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) := by
  set G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Subgroup.centralizer ({t} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) with hGdef
  haveI : Finite ↥G := Subtype.finite
  have htwo : ∀ x : F, x + x = 0 := by
    intro x
    have hx : (2 : F) * x = 0 := by rw [h2, zero_mul]
    rwa [two_mul] at hx
  have hneg1 : (-1 : F) = 1 := by rw [neg_eq_iff_add_eq_zero]; exact htwo 1
  have haddM : ∀ x : Matrix (Fin 2) (Fin 2) F, x + x = 0 := by
    intro x
    rw [← one_smul F x, ← one_smul F x, ← add_smul,
      show (1 : F) + 1 = 0 from by rw [one_add_one_eq_two]; exact h2, zero_smul]
  have hneg1M : (-(1 : Matrix (Fin 2) (Fin 2) F)) = 1 := by
    rw [neg_eq_iff_add_eq_zero]; exact haddM 1
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht
    exact (Fact.out : Nat.Prime r).ne_one ht.symm
  have htns : ∀ c : F, ((t : Matrix (Fin 2) (Fin 2) F)) ≠ c • 1 := by
    intro c hc
    have hcc : c * c = 1 := by
      have h := congrArg Matrix.det hc
      simp only [Matrix.det_smul, Matrix.det_one, Matrix.SpecialLinearGroup.det_coe,
        Fintype.card_fin] at h
      simpa [pow_two] using h.symm
    have hz : (c + 1) * (c + 1) = 0 := by
      rw [show (c + 1) * (c + 1) = c * c + (c + c) + 1 from by ring, hcc, htwo c, add_zero]
      exact htwo 1
    have hc1 : c = 1 := by
      have h := mul_self_eq_zero.mp hz
      rw [add_eq_zero_iff_eq_neg] at h
      rw [h, hneg1]
    refine ht1 (Subtype.ext ?_)
    rw [hc, hc1, one_smul, Matrix.SpecialLinearGroup.coe_one]
  set s : F := ((t : Matrix (Fin 2) (Fin 2) F)).trace with hsdef
  have hs0 : s ≠ 0 := by
    intro h0
    have hT : ((t : Matrix (Fin 2) (Fin 2) F)) * ((t : Matrix (Fin 2) (Fin 2) F)) = 1 := by
      have h := mul_self_eq_trace_smul_sub_det_smul_one ((t : Matrix (Fin 2) (Fin 2) F))
      rw [Matrix.SpecialLinearGroup.det_coe, one_smul, ← hsdef, h0, zero_smul, zero_sub,
        hneg1M] at h
      exact h
    have hdvd : orderOf t ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_pow, pow_two]
      exact hT
    rw [ht] at hdvd
    have hle : r ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    exact hr2 (le_antisymm hle (Fact.out : Nat.Prime r).two_le)
  have hT2 : ((t : Matrix (Fin 2) (Fin 2) F)) * ((t : Matrix (Fin 2) (Fin 2) F)) =
      s • ((t : Matrix (Fin 2) (Fin 2) F)) + 1 := by
    have h := mul_self_eq_trace_smul_sub_det_smul_one ((t : Matrix (Fin 2) (Fin 2) F))
    rw [Matrix.SpecialLinearGroup.det_coe, one_smul, ← hsdef, sub_eq_add_neg, hneg1M] at h
    exact h
  have hrep : ∀ y : ↥G, ∃ a b : F, ((y : ↥G) : Matrix (Fin 2) (Fin 2) F) =
      a • 1 + b • ((t : Matrix (Fin 2) (Fin 2) F)) := by
    intro y
    have hcomm : ((y : ↥G) : Matrix (Fin 2) (Fin 2) F) * ((t : Matrix (Fin 2) (Fin 2) F)) =
        ((t : Matrix (Fin 2) (Fin 2) F)) * ((y : ↥G) : Matrix (Fin 2) (Fin 2) F) := by
      have h1 : (y : ↥G) * t = t * (y : ↥G) := Subgroup.mem_centralizer_singleton_iff.mp y.2
      have h2' := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F =>
        (z : Matrix (Fin 2) (Fin 2) F)) h1
      rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h2'
    exact eq_smul_one_add_smul_of_mul_comm _ _ htns hcomm
  set qC : ↥G → F := fun y => ((y : ↥G) : Matrix (Fin 2) (Fin 2) F).trace / s with hqC
  set pC : ↥G → F := fun y => ((y : ↥G) : Matrix (Fin 2) (Fin 2) F) 0 0
      - qC y * ((t : Matrix (Fin 2) (Fin 2) F)) 0 0 with hpC
  have hcoeff : ∀ y : ↥G, ((y : ↥G) : Matrix (Fin 2) (Fin 2) F) =
      pC y • 1 + qC y • ((t : Matrix (Fin 2) (Fin 2) F)) := by
    intro y
    obtain ⟨a, b, hab⟩ := hrep y
    have hq : qC y = b := by
      rw [hqC]
      change ((y : ↥G) : Matrix (Fin 2) (Fin 2) F).trace / s = b
      rw [hab, trace_smul_one_add h2, ← hsdef]
      exact mul_div_cancel_right₀ b hs0
    have hp : pC y = a := by
      rw [hpC]
      change ((y : ↥G) : Matrix (Fin 2) (Fin 2) F) 0 0
        - qC y * ((t : Matrix (Fin 2) (Fin 2) F)) 0 0 = a
      rw [hq, hab, apply00_smul_one_add]
      ring
    rw [hp, hq, hab]
  have hmul : ∀ y y' : ↥G, ((y * y' : ↥G) : Matrix (Fin 2) (Fin 2) F) =
      (pC y * pC y' + qC y * qC y') • 1 +
        (pC y * qC y' + qC y * pC y' + qC y * qC y' * s) •
          ((t : Matrix (Fin 2) (Fin 2) F)) := by
    intro y y'
    rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hcoeff y, hcoeff y']
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_smul, smul_add, add_smul, hT2, mul_one]
    module
  have hqCmul : ∀ y y' : ↥G,
      qC (y * y') = pC y * qC y' + qC y * pC y' + qC y * qC y' * s := by
    intro y y'
    rw [hqC]
    change ((y * y' : ↥G) : Matrix (Fin 2) (Fin 2) F).trace / s = _
    rw [hmul y y', trace_smul_one_add h2, ← hsdef]
    exact mul_div_cancel_right₀ _ hs0
  have hpCmul : ∀ y y' : ↥G, pC (y * y') = pC y * pC y' + qC y * qC y' := by
    intro y y'
    rw [hpC]
    change ((y * y' : ↥G) : Matrix (Fin 2) (Fin 2) F) 0 0
      - qC (y * y') * ((t : Matrix (Fin 2) (Fin 2) F)) 0 0 = _
    rw [hqCmul y y', hmul y y', apply00_smul_one_add]
    ring
  set mP : Polynomial F := X ^ 2 + C s * X + 1 with hmP
  have h2A : (2 : AdjoinRoot mP) = 0 := by
    rw [show (2 : AdjoinRoot mP) = AdjoinRoot.of mP 2 from
      (map_ofNat (AdjoinRoot.of mP) 2).symm]
    rw [show ((2 : F)) = 0 from h2, map_zero]
  have hnegA : ∀ x : AdjoinRoot mP, -x = x := by
    intro x
    rw [neg_eq_iff_add_eq_zero, ← two_mul, h2A, zero_mul]
  have hroot0 : AdjoinRoot.root mP * AdjoinRoot.root mP
      + AdjoinRoot.of mP s * AdjoinRoot.root mP + 1 = 0 := by
    have h := AdjoinRoot.mk_self (f := mP)
    rw [hmP] at h
    simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
      map_one, pow_two] at h
    exact h
  have hroot : AdjoinRoot.root mP ^ 2 = AdjoinRoot.of mP s * AdjoinRoot.root mP + 1 := by
    rw [add_assoc] at hroot0
    have h := add_eq_zero_iff_eq_neg.mp hroot0
    rw [hnegA] at h
    rwa [pow_two]
  let Ψ : ↥G →* AdjoinRoot mP :=
    { toFun := fun y => AdjoinRoot.mk mP (C (pC y) + C (qC y) * X)
      map_one' := by
        have hq1 : qC 1 = 0 := by
          rw [hqC]
          change (((1 : ↥G)) : Matrix (Fin 2) (Fin 2) F).trace / s = 0
          rw [show (((1 : ↥G)) : Matrix (Fin 2) (Fin 2) F) = 1 from by
            rw [Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one], Matrix.trace_one,
            Fintype.card_fin]
          rw [show ((2 : ℕ) : F) = 0 from by simpa using h2, zero_div]
        have hp1 : pC 1 = 1 := by
          rw [hpC]
          change (((1 : ↥G)) : Matrix (Fin 2) (Fin 2) F) 0 0
            - qC 1 * ((t : Matrix (Fin 2) (Fin 2) F)) 0 0 = 1
          rw [show (((1 : ↥G)) : Matrix (Fin 2) (Fin 2) F) = 1 from by
            rw [Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one],
            hq1, zero_mul, sub_zero]
          simp
        rw [hp1, hq1]
        simp
      map_mul' := by
        intro y y'
        have hmk : ∀ c d : F, AdjoinRoot.mk mP (C c + C d * X) =
            AdjoinRoot.of mP c + AdjoinRoot.of mP d * AdjoinRoot.root mP := by
          intro c d
          simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
        show AdjoinRoot.mk mP (C (pC (y * y')) + C (qC (y * y')) * X) = _
        rw [hmk (pC y) (qC y), hmk (pC y') (qC y'), hmk (pC (y * y')) (qC (y * y')),
          hpCmul y y', hqCmul y y']
        simp only [map_add, map_mul]
        ring_nf
        rw [hroot]
        ring_nf }
  have hΨinj : Function.Injective Ψ := by
    intro y y' hyy
    have h : AdjoinRoot.mk mP (C (pC y) + C (qC y) * X) =
        AdjoinRoot.mk mP (C (pC y') + C (qC y') * X) := hyy
    rw [AdjoinRoot.mk_eq_mk] at h
    have hb1 : (C (pC y) + C (qC y) * X : Polynomial F).natDegree ≤ 1 := by
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · rw [Polynomial.natDegree_C]; norm_num
      · by_cases hb : qC y = 0
        · rw [hb, Polynomial.C_0, zero_mul, Polynomial.natDegree_zero]; norm_num
        · rw [Polynomial.natDegree_C_mul_X _ hb]
    have hb2 : (C (pC y') + C (qC y') * X : Polynomial F).natDegree ≤ 1 := by
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · rw [Polynomial.natDegree_C]; norm_num
      · by_cases hb : qC y' = 0
        · rw [hb, Polynomial.C_0, zero_mul, Polynomial.natDegree_zero]; norm_num
        · rw [Polynomial.natDegree_C_mul_X _ hb]
    have hdeg : ((C (pC y) + C (qC y) * X) - (C (pC y') + C (qC y') * X)).natDegree
        < mP.natDegree := by
      rw [hmP]
      have hsub := Polynomial.natDegree_sub_le (C (pC y) + C (qC y) * X)
        (C (pC y') + C (qC y') * X)
      have h2' : (X ^ 2 + C s * X + 1 : Polynomial F).natDegree = 2 := by compute_degree!
      omega
    have hzero : (C (pC y) + C (qC y) * X) - (C (pC y') + C (qC y') * X) = 0 :=
      Polynomial.eq_zero_of_dvd_of_natDegree_lt h hdeg
    rw [sub_eq_zero] at hzero
    have hp : pC y = pC y' := by
      have := congrArg (fun p : Polynomial F => p.coeff 0) hzero
      simpa using this
    have hq : qC y = qC y' := by
      have := congrArg (fun p : Polynomial F => p.coeff 1) hzero
      simpa using this
    have hval : ((y : ↥G) : Matrix (Fin 2) (Fin 2) F) = ((y' : ↥G) : Matrix (Fin 2) (Fin 2) F) := by
      rw [hcoeff y, hcoeff y', hp, hq]
    exact Subtype.ext (Subtype.ext hval)
  by_cases hex : ∃ a : F, a ^ 2 + s * a + 1 = 0
  · obtain ⟨a, ha⟩ := hex
    have h2a : a + a = 0 := htwo a
    have haa : a * a + s * a = 1 := by
      have h := ha
      rw [pow_two, ← hneg1] at h
      simpa using add_eq_zero_iff_eq_neg.mp h
    have haa2 : a * (s + a) = 1 := by
      have h : a * (s + a) = a * a + s * a := by ring
      rw [h]; exact haa
    have hasum : a + (s + a) = s := by
      rw [← add_assoc, add_comm a s, add_assoc, h2a, add_zero]
    have hasum' : (s + a) + a = s := by rw [add_comm (s + a) a]; exact hasum
    have hηzero : eval₂ (RingHom.id F) a mP = 0 := by
      rw [hmP]
      simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eval₂_one,
        RingHom.id_apply]
      exact ha
    let η : AdjoinRoot mP →+* F := AdjoinRoot.lift (RingHom.id F) a hηzero
    have hηof : ∀ c : F, η (AdjoinRoot.of mP c) = c :=
      fun c => AdjoinRoot.lift_of (h := hηzero)
    have hηroot : η (AdjoinRoot.root mP) = a := AdjoinRoot.lift_root hηzero
    have hηΨ : ∀ y : ↥G, (η.toMonoidHom.comp Ψ) y = pC y + qC y * a := by
      intro y
      show η (AdjoinRoot.mk mP (C (pC y) + C (qC y) * X)) = _
      simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
      rw [hηof (pC y), hηof (qC y), hηroot]
    have hinj : Function.Injective (η.toMonoidHom.comp Ψ) := by
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro y hy
      rw [MonoidHom.mem_ker] at hy
      rw [hηΨ y] at hy
      have hdet : (pC y) ^ 2 + pC y * qC y * s + (qC y) ^ 2 = 1 := by
        have h1 : (((y : ↥G) : Matrix (Fin 2) (Fin 2) F)).det = 1 :=
          Matrix.SpecialLinearGroup.det_coe _
        rw [hcoeff y, det_smul_one_add_smul, Matrix.SpecialLinearGroup.det_coe, mul_one,
          ← hsdef] at h1
        exact h1
      have hfac : (pC y + qC y * a) * (pC y + qC y * (s + a)) = 1 := by
        rw [← hdet]
        have e : (pC y + qC y * a) * (pC y + qC y * (s + a))
            = (pC y) ^ 2 + pC y * qC y * s + (qC y) ^ 2 := by
          calc (pC y + qC y * a) * (pC y + qC y * (s + a))
              = (pC y) ^ 2 + pC y * qC y * (s + a) + pC y * qC y * a
                  + (qC y) ^ 2 * (a * (s + a)) := by ring
            _ = (pC y) ^ 2 + pC y * qC y * ((s + a) + a)
                  + (qC y) ^ 2 * (a * (s + a)) := by ring
            _ = (pC y) ^ 2 + pC y * qC y * s + (qC y) ^ 2 := by
                  rw [hasum', haa2, mul_one]
        exact e
      have hpq : pC y + qC y * (s + a) = 1 := by rw [← hfac, hy, one_mul]
      have hq0 : qC y = 0 := by
        have h1 : pC y + qC y * a = pC y + qC y * (s + a) := by rw [hy, hpq]
        have h2'' : qC y * a = qC y * (s + a) := add_left_cancel h1
        have h3 : qC y * ((s + a) - a) = 0 := by rw [mul_sub, h2'', sub_self]
        rw [add_sub_cancel_right] at h3
        exact (mul_eq_zero.mp h3).resolve_right hs0
      have hp1 : pC y = 1 := by
        rw [hq0, zero_mul, add_zero] at hy
        exact hy
      apply Subtype.ext
      apply Subtype.ext
      rw [hcoeff y, hp1, hq0, one_smul, zero_smul, add_zero]
      rw [Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one]
    exact isCyclic_of_injective_ringHom (η.toMonoidHom.comp Ψ) hinj
  · have hirr : Irreducible mP := by
      refine irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
      · rw [hmP]
        have : (X ^ 2 + C s * X + 1 : Polynomial F).natDegree = 2 := by compute_degree!
        rw [this]; norm_num
      · intro x hx
        exact hex ⟨x, by
          simpa only [hmP, Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
            pow_two] using hx⟩
    haveI : IsDomain (AdjoinRoot mP) :=
      AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)
    exact isCyclic_of_injective_ringHom Ψ hΨinj



end CharTwoAux

theorem sl_pgroup_cyclic_char_two (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) = 0)
    (r : ℕ) [Fact r.Prime] (hr2 : r ≠ 2)
    (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) (hP : IsPGroup r P) :
    IsCyclic P :=
  isCyclic_of_isPGroup_centralizer hP
    (fun t _ ht => sl_centralizer_cyclic_char_two F h2 r hr2 t ht)

theorem pgl_isCyclic_char_two (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) = 0) (r : ℕ)
    [Fact r.Prime] (hr2 : r ≠ 2) (P : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F))
    (hP : IsPGroup r P) : IsCyclic P := by
  have htwo : ∀ x : F, x + x = 0 := by
    intro x
    have hx : (2 : F) * x = 0 := by rw [h2, zero_mul]
    rwa [two_mul] at hx
  have h2u : ∀ u : Fˣ, u ^ 2 = 1 → u = 1 := by
    intro u hu
    have hu' : (u : F) * (u : F) = 1 := by
      have := congrArg (fun w : Fˣ => (w : F)) hu
      simpa [pow_two] using this
    apply Units.ext
    have h : ((u : F) - 1) * ((u : F) - 1) = 0 := by
      rw [show ((u : F) - 1) * ((u : F) - 1) = (u : F) * (u : F) - ((u : F) + (u : F)) + 1
        from by ring, hu', htwo (u : F), sub_zero]
      rw [show (1 : F) + 1 = 0 from by rw [one_add_one_eq_two]; exact h2]
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h)
  have hker : (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).ker = ⊥ := by
    rw [Matrix.SpecialLinearGroup.toPGL_ker, Subgroup.eq_bot_iff_forall]
    intro z hz
    have hz' : (⟨z, hz⟩ : ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) = 1 := by
      set u : Fˣ := ((Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 2) (R := F))
        ⟨z, hz⟩).1 with hudef
      have hu : u ^ 2 = 1 := by
        have h : u ^ (max (Fintype.card (Fin 2)) 1) = 1 := by
          rw [hudef]
          exact ((Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 2) (R := F))
            ⟨z, hz⟩).2
        rwa [show max (Fintype.card (Fin 2)) 1 = 2 from by simp] at h
      have h1 : u = 1 := h2u u hu
      apply (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 2) (R := F)).injective
      rw [map_one]
      apply Subtype.ext
      rw [← hudef]
      exact h1
    exact congrArg (fun w : ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) =>
      (w : Matrix.SpecialLinearGroup (Fin 2) F)) hz'
  have hinj : Function.Injective ⇑(Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have hcard : Nat.card (Matrix.ProjGenLinGroup (Fin 2) F) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Work.CORE2A.card_PGL2_eq_card_SL2 F
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 2) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hrange : (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [← Subgroup.map_top (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)),
      Subgroup.card_map_of_injective (K := ⊤) hinj,
      Nat.card_congr (Subgroup.topEquiv (G := Matrix.SpecialLinearGroup (Fin 2) F)).toEquiv,
      hcard]
  have hsurj : Function.Surjective ⇑(Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)) := by
    intro y
    exact MonoidHom.mem_range.mp (hrange ▸ Subgroup.mem_top y)
  obtain ⟨e⟩ : Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃*
      Matrix.ProjGenLinGroup (Fin 2) F) :=
    ⟨MulEquiv.ofBijective _ ⟨hinj, hsurj⟩⟩
  let P' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) := P.comap e.toMonoidHom
  have hmap : P'.map e.toMonoidHom = P :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective P
  have hiso : ↥P' ≃* ↥P := hmap ▸ Subgroup.equivMapOfInjective P' e.toMonoidHom e.injective
  have hP' : IsPGroup r ↥P' := hP.of_equiv hiso.symm
  rw [← hmap]
  exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective P' e.toMonoidHom e.injective)).mp
    (sl_pgroup_cyclic_char_two F h2 r hr2 P' hP')


theorem pgl_r_subgroup_cyclic (F : Type*) [Field F] [Fintype F] (r : ℕ) [Fact r.Prime]
    (hr : (r : F) ≠ 0) (hr2 : r ≠ 2) (P : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F))
    (hP : IsPGroup r P) : IsCyclic P := by
  by_cases h2 : (2 : F) = 0
  · exact pgl_isCyclic_char_two F h2 r hr2 P hP
  · exact isCyclic_subgroup_pgl_odd F h2 r hr hr2 P hP

end Work.L2F.Props