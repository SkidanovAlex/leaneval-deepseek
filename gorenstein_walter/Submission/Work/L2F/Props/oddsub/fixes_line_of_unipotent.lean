import Mathlib
import Submission.Work.L2F.Props.OddSubDefs
import Submission.OddOrder.FeitThompson
import Submission.Work.L2F.Props.oddsub.charP_odd_of_unipotent
import Submission.Work.L2F.Props.oddsub.charP_odd_of_unipotent_in_pgl
import Submission.Work.L2F.Props.oddsub.normal_elementaryAbelian_of_solvable
import Submission.Work.L2F.Props.oddsub.oddPart_of_central_involution
import Submission.Work.L2F.Props.oddsub.no_unipotent_of_normal_abelian_irreducible
import Submission.Work.L2F.Props.oddsub.common_fixed_vector_of_isPGroup
import Submission.Work.L2F.Props.oddsub.fixes_line_of_normal_abelian_with_invariant_line

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props.oddsub

/-!
# `fixes_line_of_unipotent`

An odd-order subgroup of `PGL(2,F)` which contains the image of a unipotent element of `SL(2,F)`
fixes a common line, i.e. lies in a Borel subgroup.

The proof goes through the preimage in `SL(2,F)`, its (odd) part, and the structure of solvable
odd-order subgroups of `SL(2,F)`; the auxiliary facts used here are proved in the sibling files
of this directory.
-/

/-! ## Elementary helpers -/

/-- Negating a unipotent matrix keeps it unipotent. -/
lemma unipotent_neg {F : Type*} [Field F] {g : Matrix (Fin 2) (Fin 2) F}
    (h : UnipotentMatrix g) : UnipotentMatrix (-g) := by
  obtain ⟨a, hne, hsq⟩ := h
  refine ⟨-a, ?_, ?_⟩
  · intro h0
    apply hne
    have := congrArg Neg.neg h0
    simpa [sub_eq_add_neg, add_comm] using this
  · have h0 : -g - (-a) • (1 : Matrix (Fin 2) (Fin 2) F) = -(g - a • 1) := by
      rw [neg_smul, neg_sub]
      abel
    rw [h0, neg_mul_neg, hsq]

/-- If `v ≠ 0` and `w ∉ F v` in the two-dimensional space `F²`, then `{v, w}` spans. -/
lemma span_pair_eq_top_of_notMem_span {F : Type*} [Field F] {v w : Fin 2 → F}
    (hv : v ≠ 0) (hw : w ∉ Submodule.span F ({v} : Set (Fin 2 → F))) :
    Submodule.span F ({v, w} : Set (Fin 2 → F)) = ⊤ := by
  have hstep : Submodule.span F ({v} : Set (Fin 2 → F))
      < Submodule.span F ({v, w} : Set (Fin 2 → F)) := by
    refine lt_of_le_of_ne (Submodule.span_mono ?_) ?_
    · intro x hx
      simp only [Set.mem_singleton_iff] at hx
      rw [hx]
      simp
    · intro heq
      apply hw
      rw [heq]
      exact Submodule.subset_span (by simp)
  have hlt := Submodule.finrank_lt_finrank_of_lt hstep
  rw [show Module.finrank F ↥(Submodule.span F ({v} : Set (Fin 2 → F))) = 1 from
    finrank_span_singleton hv] at hlt
  have hle : Module.finrank F ↥(Submodule.span F ({v, w} : Set (Fin 2 → F))) ≤ 2 := by
    have h := Submodule.finrank_mono
      (show Submodule.span F ({v, w} : Set (Fin 2 → F)) ≤ ⊤ from le_top)
    have htop : Module.finrank F ↥(⊤ : Submodule F (Fin 2 → F)) = 2 := by
      rw [LinearEquiv.finrank_eq (Submodule.topEquiv (R := F) (M := Fin 2 → F)),
        Module.finrank_fintype_fun_eq_card F, Fintype.card_fin]
    omega
  have hfin : Module.finrank F ↥(Submodule.span F ({v, w} : Set (Fin 2 → F))) = 2 := by omega
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [hfin, Module.finrank_fintype_fun_eq_card F, Fintype.card_fin]

/-- A `2 × 2` matrix fixing a spanning pair of vectors is the identity. -/
lemma eq_one_of_mulVec_eq_on_span {F : Type*} [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (v w : Fin 2 → F) (hspan : Submodule.span F ({v, w} : Set (Fin 2 → F)) = ⊤)
    (hv : M.mulVec v = v) (hw : M.mulVec w = w) : M = 1 := by
  have hfix : ∀ u : Fin 2 → F, M.mulVec u = u := by
    intro u
    have hmem : u ∈ Submodule.span F ({v, w} : Set (Fin 2 → F)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
    rw [← hab, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hv, hw]
  ext i j
  have h := congrFun (hfix (Pi.single j (1 : F))) i
  rw [Matrix.mulVec_single] at h
  simp only [Pi.smul_apply, Matrix.col_apply, Matrix.one_apply, Pi.single_apply,
    MulOpposite.op_one, one_smul] at h
  exact h

/-- `-1 ≠ 1` in `SL(2,F)` when `2 ≠ 0` in `F`. -/
lemma negOne_ne_one (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) : Work.L2F.negOne F ≠ 1 := by
  intro h
  have h' := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
    (x : Matrix (Fin 2) (Fin 2) F)) h
  simp only [Matrix.SpecialLinearGroup.coe_one] at h'
  have h00 := congrFun (congrFun h' 0) 0
  have hmat : ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = -1 := rfl
  rw [hmat] at h00
  have h00' : (-1 : F) = 1 := by simpa using h00
  exact h2 (by linear_combination -h00')

/-- An element of the center of `SL(2,F)` is `±1`. -/
lemma center_eq_one_or_negOne (F : Type*) [Field F] (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) :
    x = 1 ∨ x = Work.L2F.negOne F := by
  set u : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    with hu
  set w : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    with hw
  have hcu : u * x = x * u := Subgroup.mem_center_iff.mp hx u
  have hcw : w * x = x * w := Subgroup.mem_center_iff.mp hx w
  have hcu' : (u : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F)
      = (x : Matrix (Fin 2) (Fin 2) F) * (u : Matrix (Fin 2) (Fin 2) F) := by
    simpa [Matrix.SpecialLinearGroup.coe_mul] using congrArg
      (fun y : Matrix.SpecialLinearGroup (Fin 2) F => (y : Matrix (Fin 2) (Fin 2) F)) hcu
  have hcw' : (w : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F)
      = (x : Matrix (Fin 2) (Fin 2) F) * (w : Matrix (Fin 2) (Fin 2) F) := by
    simpa [Matrix.SpecialLinearGroup.coe_mul] using congrArg
      (fun y : Matrix.SpecialLinearGroup (Fin 2) F => (y : Matrix (Fin 2) (Fin 2) F)) hcw
  have hu00 : (u : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by simp [hu]
  have hu01 : (u : Matrix (Fin 2) (Fin 2) F) 0 1 = 1 := by simp [hu]
  have hu10 : (u : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simp [hu]
  have hu11 : (u : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by simp [hu]
  have hw00 : (w : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by simp [hw]
  have hw01 : (w : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by simp [hw]
  have hw10 : (w : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by simp [hw]
  have h10 : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have h := congrFun (congrFun hcu' 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hu00, hu01, hu10, hu11] at h
    simp only [one_mul, mul_one, mul_zero, zero_mul, add_zero] at h
    linear_combination h
  have h11 : (x : Matrix (Fin 2) (Fin 2) F) 1 1 = (x : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    have h := congrFun (congrFun hcu' 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hu00, hu01, hu10, hu11] at h
    simp only [one_mul, mul_one, mul_zero, zero_mul, add_zero] at h
    linear_combination h
  have h01 : (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have h := congrFun (congrFun hcw' 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hw00, hw01, hw10] at h
    simp only [one_mul, mul_one, mul_zero, zero_mul, add_zero] at h
    linear_combination -h
  have hxscal : (x : Matrix (Fin 2) (Fin 2) F)
      = (x : Matrix (Fin 2) (Fin 2) F) 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, Matrix.one_apply, h10, h11, h01]
  have hdet : ((x : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe x
    rw [hxscal, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at h
    exact h
  have ha : (x : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∨
      (x : Matrix (Fin 2) (Fin 2) F) 0 0 = -1 := by
    have h : ((x : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) *
        ((x : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) = 0 := by
      linear_combination hdet
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases ha with h | h
  · left
    apply Subtype.ext
    rw [hxscal, h, one_smul, Matrix.SpecialLinearGroup.coe_one]
  · right
    apply Subtype.ext
    rw [hxscal, h]
    rw [show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
    rw [neg_smul, one_smul]

/-! ## The main structure theorem -/

/-- **An odd-order subgroup of `SL(2,F)` containing a unipotent element fixes a line.** -/
theorem oddOrder_unipotent_fixes_line (F : Type*) [Field F]
    (L : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) (hodd : Odd (Nat.card L))
    (hu : ∃ g ∈ L, UnipotentMatrix ((g : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)) :
    HasCommonEigenvectorSL L := by
  classical
  haveI hfinL : Finite ↥L := Finite.of_not_infinite fun hinf => by
    have h0 : Nat.card ↥L = 0 := @Nat.card_eq_zero_of_infinite _ hinf
    rw [h0] at hodd
    exact absurd hodd (by simp [Nat.odd_iff])
  obtain ⟨p, hpp, hCharP, hp2⟩ := charP_odd_of_unipotent F L hodd hu
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨g₀, hg₀L, hg₀uni⟩ := hu
  have hg₀ne : g₀ ≠ 1 := by
    intro hone
    obtain ⟨a, hane, hsq⟩ := hg₀uni
    rw [hone, Matrix.SpecialLinearGroup.coe_one] at hane hsq
    have hsub : (1 : Matrix (Fin 2) (Fin 2) F) - a • 1 = (1 - a) • 1 := by
      rw [sub_smul, one_smul]
    rw [hsub] at hane hsq
    have h2 : (1 - a) * (1 - a) = 0 := by
      have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hsq
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply] using h
    have h3 : (1 - a) = 0 := mul_self_eq_zero.mp h2
    rw [h3, zero_smul] at hane
    exact hane rfl
  have hLne : L ≠ ⊥ := by
    intro hbot
    apply hg₀ne
    have : g₀ ∈ (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) := hbot ▸ hg₀L
    simpa using this
  haveI hntL : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hLne
  have hsolv : Group.IsSolvable ↥L := OddOrder.feitThompson hodd
  obtain ⟨q, hqfact, Q, hQnorm, hQne, hQp, hQexp, hQab⟩ :=
    normal_elementaryAbelian_of_solvable ↥L hntL hsolv
  haveI : Fact q.Prime := hqfact
  set Q' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) := Q.map L.subtype with hQ'def
  have hQ'L : Q' ≤ L := Subgroup.map_subtype_le Q
  have hQ'ne : Q' ≠ ⊥ := by
    rw [hQ'def]
    intro hmap
    exact hQne (Subgroup.map_injective (Subgroup.subtype_injective L)
      (by rw [hmap, Subgroup.map_bot]))
  have hQ'ab : ∀ x ∈ Q', ∀ y ∈ Q', x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
    have h := congrArg (fun z : ↥L => (z : Matrix.SpecialLinearGroup (Fin 2) F))
      (hQab x₀ hx₀ y₀ hy₀)
    simpa [Subgroup.coe_mul] using h
  have hQ'p : IsPGroup q ↥Q' :=
    hQp.of_equiv (Subgroup.equivMapOfInjective Q L.subtype (Subgroup.subtype_injective L))
  have hQ'norm : (Q'.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQ'L]
    intro h k hh hk
    obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.mp hh
    have hmem := hQnorm.conj_mem h₀ hh₀ (⟨k, hk⟩ : ↥L)
    refine Subgroup.mem_map.mpr ⟨_, hmem, ?_⟩
    show L.subtype (⟨k, hk⟩ * h₀ * (⟨k, hk⟩ : ↥L)⁻¹) = k * L.subtype h₀ * k⁻¹
    rw [map_mul, map_mul, map_inv]
    rfl
  have hrc : ringChar F = p := ringChar.eq F p
  have hoddL : ∀ l ∈ L, Odd (orderOf l) := fun l hl =>
    hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard L hl)
  by_cases hqp : q = p
  · have hCharPq : CharP F q := hqp ▸ hCharP
    haveI hfinQ' : Finite ↥Q' := Finite.of_injective
      (fun x : ↥Q' => (⟨(x : Matrix.SpecialLinearGroup (Fin 2) F), hQ'L x.2⟩ : ↥L))
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
    obtain ⟨v, hvne, hvfix⟩ := common_fixed_vector_of_isPGroup F q hCharPq Q' hQ'p hQ'ne
    by_cases hgoal : ∀ l ∈ L, ∃ c : F,
        Matrix.mulVec ((l : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) v
          = c • v
    · exact ⟨v, hvne, hgoal⟩
    · exfalso
      push_neg at hgoal
      obtain ⟨l, hlL, hlno⟩ := hgoal
      set w : Fin 2 → F := Matrix.mulVec ((l : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) v with hwdef
      have hwnot : w ∉ Submodule.span F ({v} : Set (Fin 2 → F)) := by
        rw [hwdef]
        intro hmem
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
        exact hlno c hc.symm
      have hspan := span_pair_eq_top_of_notMem_span hvne hwnot
      have hQbot : Q' = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        have hxv : Matrix.mulVec ((x : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) v = v := hvfix x hx
        have hxw : Matrix.mulVec ((x : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) w = w := by
          have hconjAll : ∀ (y : Matrix.SpecialLinearGroup (Fin 2) F)
              (k : Matrix.SpecialLinearGroup (Fin 2) F), y ∈ Q' → k ∈ L → k * y * k⁻¹ ∈ Q' :=
            (Subgroup.normal_subgroupOf_iff hQ'L).mp hQ'norm
          have hconj : l⁻¹ * x * l ∈ Q' := by
            simpa using hconjAll x l⁻¹ hx (L.inv_mem hlL)
          have hfix := hvfix (l⁻¹ * x * l) hconj
          have hsl : x * l = l * (l⁻¹ * x * l) := by group
          have hmat : ((x : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F)
              * ((l : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
              = ((l : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
              * (((l⁻¹ * x * l) : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F) := by
            simpa [Matrix.SpecialLinearGroup.coe_mul] using congrArg
              (fun y : Matrix.SpecialLinearGroup (Fin 2) F =>
                (y : Matrix (Fin 2) (Fin 2) F)) hsl
          rw [hwdef]
          calc ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
                *ᵥ (((l : Matrix.SpecialLinearGroup (Fin 2) F) :
                  Matrix (Fin 2) (Fin 2) F) *ᵥ v)
              = (((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
                * ((l : Matrix.SpecialLinearGroup (Fin 2) F) :
                  Matrix (Fin 2) (Fin 2) F)) *ᵥ v := by
                  rw [Matrix.mulVec_mulVec]
            _ = (((l : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
                * (((l⁻¹ * x * l) : Matrix.SpecialLinearGroup (Fin 2) F) :
                  Matrix (Fin 2) (Fin 2) F)) *ᵥ v := by rw [hmat]
            _ = Matrix.mulVec ((l : Matrix.SpecialLinearGroup (Fin 2) F) :
                  Matrix (Fin 2) (Fin 2) F)
                (Matrix.mulVec (((l⁻¹ * x * l) : Matrix.SpecialLinearGroup (Fin 2) F) :
                  Matrix (Fin 2) (Fin 2) F) v) := by
                  rw [Matrix.mulVec_mulVec]
            _ = ((l : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
                *ᵥ v := by rw [hfix]
        have hx1 : ((x : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) = 1 :=
          eq_one_of_mulVec_eq_on_span _ v w hspan hxv hxw
        exact Subtype.ext hx1
      exact hQ'ne hQbot
  · have hQ'cop : ∀ x ∈ Q', ¬ ringChar F ∣ orderOf x := by
      intro x hx hdvd
      obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
      rw [orderOf_injective L.subtype (Subgroup.subtype_injective L) x₀] at hdvd
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
      have hdvd' : orderOf x₀ ∣ q ^ k := by
        rw [← hk]; exact Subgroup.orderOf_dvd_natCard Q hx₀
      have hpdvd : p ∣ q ^ k := by
        rw [← hrc]; exact hdvd.trans hdvd'
      have hpq : p ∣ q := hpp.dvd_of_dvd_pow hpdvd
      have h1 : p = q := (Nat.prime_dvd_prime_iff_eq hpp hqfact.out).mp hpq
      exact hqp h1.symm
    by_cases hline : ∃ v : Fin 2 → F, v ≠ 0 ∧ ∀ x ∈ Q',
        ∃ c : F, Matrix.mulVec ((x : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) v = c • v
    · exact fixes_line_of_normal_abelian_with_invariant_line F L Q' hQ'L hQ'norm hQ'ab
        hQ'ne hQ'cop hoddL hline
    · exact absurd ⟨g₀, hg₀L, hg₀uni⟩
        (no_unipotent_of_normal_abelian_irreducible F L Q' hQ'L hQ'norm hQ'ab
          hQ'ne hline hoddL)

/-! ## The requested lemma -/

theorem fixes_line_of_unipotent (F : Type*) [Field F]
    (K : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)) (hodd : Odd (Nat.card K))
    (hK : K ≤ Matrix.SpecialLinearGroup.toPGL.range)
    (hu : ∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
        Matrix.SpecialLinearGroup.toPGL g ∈ K ∧
          Work.L2F.Props.UnipotentMatrix (g : Matrix (Fin 2) (Fin 2) F)) :
    Work.L2F.Props.HasCommonEigenvectorSL (Subgroup.comap Matrix.SpecialLinearGroup.toPGL K) := by
  classical
  obtain ⟨p, hpp, hCharP, hp2⟩ := charP_odd_of_unipotent_in_pgl F K hodd hu
  haveI : Fact p.Prime := ⟨hpp⟩
  have hchar2 : (2 : F) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp h0
    exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hpp.two_le)
  haveI hfinK : Finite ↥K := Finite.of_not_infinite fun hinf => by
    have h0 : Nat.card ↥K = 0 := @Nat.card_eq_zero_of_infinite _ hinf
    rw [h0] at hodd
    exact absurd hodd (by simp [Nat.odd_iff])
  set H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Subgroup.comap Matrix.SpecialLinearGroup.toPGL K with hHdef
  set f : ↥H →* Matrix.ProjGenLinGroup (Fin 2) F :=
    Matrix.SpecialLinearGroup.toPGL.comp H.subtype with hfdef
  have hneg1 : Matrix.SpecialLinearGroup.toPGL (Work.L2F.negOne F) = 1 := by
    rw [← MonoidHom.mem_ker, Matrix.SpecialLinearGroup.toPGL_ker, Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
    rw [mul_neg, neg_mul, mul_one, one_mul]
  have hzmem : (Work.L2F.negOne F) ∈ H := by
    rw [hHdef, Subgroup.mem_comap, hneg1]
    exact K.one_mem
  set z : ↥H := ⟨Work.L2F.negOne F, hzmem⟩ with hzdef
  have hzz : z * z = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [Subgroup.coe_mul, hzdef]
    rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
    rw [Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one, neg_mul_neg, one_mul]
  have hzord : orderOf z = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]; exact hzz
    · intro h
      apply negOne_ne_one F hchar2
      have := congrArg (fun y : ↥H => ((y : ↥H) : Matrix.SpecialLinearGroup (Fin 2) F)) h
      rw [hzdef] at this
      simpa using this
  have hzc : ∀ y : ↥H, y * z = z * y := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    rw [hzdef]
    rw [show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
    rw [mul_neg, neg_mul, mul_one, one_mul]
  have hker : f.ker = Subgroup.zpowers z := by
    apply le_antisymm
    · intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hxcenter : ((x : ↥H) : Matrix.SpecialLinearGroup (Fin 2) F) ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
        rw [← Matrix.SpecialLinearGroup.toPGL_ker, MonoidHom.mem_ker]
        exact hx
      rcases center_eq_one_or_negOne F _ hxcenter with h1 | h1
      · rw [Subgroup.mem_zpowers_iff]
        exact ⟨0, by rw [zpow_zero]; exact Subtype.ext h1.symm⟩
      · rw [Subgroup.mem_zpowers_iff]
        refine ⟨1, ?_⟩
        rw [zpow_one]
        apply Subtype.ext
        rw [hzdef]
        exact h1.symm
    · rw [Subgroup.zpowers_le]
      rw [hfdef]
      show Matrix.SpecialLinearGroup.toPGL ((z : ↥H) :
        Matrix.SpecialLinearGroup (Fin 2) F) = 1
      rw [hzdef]
      exact hneg1
  have hrange : f.range = K := by
    rw [hfdef, MonoidHom.range_comp, Subgroup.range_subtype, hHdef]
    exact Subgroup.map_comap_eq_self hK
  have hoddquot : Odd (Nat.card (↥H ⧸ Subgroup.zpowers z)) := by
    rw [← hker]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange]
    exact hodd
  have hHcard : Nat.card ↥H = Nat.card ↥K * 2 := by
    have h : Nat.card ↥H = Nat.card (↥H ⧸ Subgroup.zpowers z) * Nat.card ↥(Subgroup.zpowers z) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers z)
    rw [show Nat.card ↥(Subgroup.zpowers z) = 2 from by rw [Nat.card_zpowers, hzord]] at h
    rw [← hker] at h
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange] at h
    exact h
  haveI hfinH : Finite ↥H := Finite.of_not_infinite fun hinf => by
    have h0 : Nat.card ↥H = 0 := @Nat.card_eq_zero_of_infinite _ hinf
    rw [hHcard] at h0
    haveI : Nonempty ↥K := ⟨⟨1, K.one_mem⟩⟩
    have hpos : 0 < Nat.card ↥K := Nat.card_pos
    omega
  obtain ⟨O, hOnorm, hOodd, hOoddElts, hOmem, hOcover⟩ :=
    oddPart_of_central_involution ↥H z hzord hzc hoddquot
  set O' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) := O.map H.subtype with hO'def
  have hO'odd : Odd (Nat.card ↥O') := by
    rw [hO'def]
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective O H.subtype
      (Subgroup.subtype_injective H)).toEquiv]
    exact hOodd
  obtain ⟨g, hgK, hguni⟩ := hu
  have hgH : g ∈ H := by rw [hHdef, Subgroup.mem_comap]; exact hgK
  have hO'uni : ∃ y ∈ O', UnipotentMatrix ((y : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) := by
    rcases hOcover (⟨g, hgH⟩ : ↥H) with h | h
    · refine ⟨H.subtype ⟨g, hgH⟩, ?_, ?_⟩
      · rw [hO'def]; exact Subgroup.mem_map.mpr ⟨⟨g, hgH⟩, h, rfl⟩
      · exact hguni
    · refine ⟨H.subtype (⟨g, hgH⟩ * z), ?_, ?_⟩
      · rw [hO'def]; exact Subgroup.mem_map.mpr ⟨⟨g, hgH⟩ * z, h, rfl⟩
      · have hcoe : ((H.subtype (⟨g, hgH⟩ * z) : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) = -(g : Matrix (Fin 2) (Fin 2) F) := by
          rw [map_mul]
          show ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
              * ((z : ↥H) : Matrix (Fin 2) (Fin 2) F) = -(g : Matrix (Fin 2) (Fin 2) F)
          rw [show ((z : ↥H) : Matrix (Fin 2) (Fin 2) F) = -1 from by rw [hzdef]; rfl,
            mul_neg, mul_one]
        rw [hcoe]
        exact unipotent_neg hguni
  obtain ⟨v, hvne, hvfix⟩ := oddOrder_unipotent_fixes_line F O' hO'odd hO'uni
  refine ⟨v, hvne, fun g hg => ?_⟩
  rcases hOcover (⟨g, hg⟩ : ↥H) with hin | hin
  · have hmem : g ∈ O' := Subgroup.mem_map.mpr ⟨⟨g, hg⟩, hin, rfl⟩
    exact hvfix g hmem
  · have hmem : (H.subtype (⟨g, hg⟩ * z) : Matrix.SpecialLinearGroup (Fin 2) F) ∈ O' :=
      Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * z, hin, rfl⟩
    obtain ⟨c, hc⟩ := hvfix _ hmem
    refine ⟨-c, ?_⟩
    have hmat : (g : Matrix (Fin 2) (Fin 2) F)
        = -(H.subtype (⟨g, hg⟩ * z) : Matrix (Fin 2) (Fin 2) F) := by
      have h1 : H.subtype (⟨g, hg⟩ * z) = H.subtype z * H.subtype ⟨g, hg⟩ := by
        rw [hzc]
        rfl
      rw [h1]
      show (g : Matrix (Fin 2) (Fin 2) F)
          = -(((H.subtype z : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F))
      rw [show (H.subtype z : Matrix.SpecialLinearGroup (Fin 2) F) = Work.L2F.negOne F
          from rfl,
        show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
      rw [neg_mul, one_mul, neg_neg]
    rw [hmat, Matrix.neg_mulVec, hc, neg_smul]

end Work.L2F.Props.oddsub
