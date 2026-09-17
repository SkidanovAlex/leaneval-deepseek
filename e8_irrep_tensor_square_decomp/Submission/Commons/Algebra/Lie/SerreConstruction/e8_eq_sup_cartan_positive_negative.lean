import Mathlib.Data.Complex.Basic
import Submission.Commons.Algebra.Lie.SerreConstruction.eq_top_of_lieSubalgebra_of_generators

open CartanMatrix

namespace Commons.Algebra.Lie.SerreConstruction

private noncomputable abbrev L8 : Type := LieAlgebra.e₈ ℂ
private noncomputable abbrev FL8 : Type := FreeLieAlgebra ℂ (CartanMatrix.Generators (Fin 8))
private noncomputable abbrev J8 : LieIdeal ℂ FL8 := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈

private noncomputable def q : FL8 →ₗ⁅ℂ⁆ L8 :=
  { toLinearMap := (LieSubmodule.Quotient.mk' J8).toLinearMap
    map_lie' := fun {x y} => LieSubmodule.Quotient.mk_bracket J8 x y }

private noncomputable def genH (i : Fin 8) : L8 :=
  LieSubmodule.Quotient.mk (N := J8) (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i))
private noncomputable def genE (i : Fin 8) : L8 :=
  LieSubmodule.Quotient.mk (N := J8) (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i))
private noncomputable def genF (i : Fin 8) : L8 :=
  LieSubmodule.Quotient.mk (N := J8) (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i))

private noncomputable def SE : LieSubalgebra ℂ L8 := LieSubalgebra.lieSpan ℂ L8 (Set.range genE)
private noncomputable def H0 : Submodule ℂ L8 := Submodule.span ℂ (Set.range genH)
private noncomputable def SF : LieSubalgebra ℂ L8 := LieSubalgebra.lieSpan ℂ L8 (Set.range genF)
private noncomputable def W8 : Submodule ℂ L8 := (SE : Submodule ℂ L8) ⊔ H0 ⊔ (SF : Submodule ℂ L8)

private lemma HH_mem (i j : Fin 8) :
    CartanMatrix.Relations.HH ℂ (i, j) ∈ (J8 : Submodule ℂ FL8) :=
  LieSubmodule.subset_lieSpan (by simp [CartanMatrix.Relations.toSet] : _ ∈ _)
private lemma HE_mem (i j : Fin 8) :
    CartanMatrix.Relations.HE ℂ CartanMatrix.E₈ (i, j) ∈ (J8 : Submodule ℂ FL8) :=
  LieSubmodule.subset_lieSpan (by simp [CartanMatrix.Relations.toSet] : _ ∈ _)
private lemma HF_mem (i j : Fin 8) :
    CartanMatrix.Relations.HF ℂ CartanMatrix.E₈ (i, j) ∈ (J8 : Submodule ℂ FL8) :=
  LieSubmodule.subset_lieSpan (by simp [CartanMatrix.Relations.toSet] : _ ∈ _)
private lemma EF_mem (i j : Fin 8) :
    CartanMatrix.Relations.EF ℂ (i, j) ∈ (J8 : Submodule ℂ FL8) :=
  LieSubmodule.subset_lieSpan (by simp [CartanMatrix.Relations.toSet] : _ ∈ _)

private lemma qHH (i j : Fin 8) : q (CartanMatrix.Relations.HH ℂ (i, j)) = 0 := by
  change LieSubmodule.Quotient.mk (N := J8) (CartanMatrix.Relations.HH ℂ (i, j)) = 0
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact HH_mem i j
private lemma qHE (i j : Fin 8) : q (CartanMatrix.Relations.HE ℂ CartanMatrix.E₈ (i, j)) = 0 := by
  change LieSubmodule.Quotient.mk (N := J8) (CartanMatrix.Relations.HE ℂ CartanMatrix.E₈ (i, j)) = 0
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact HE_mem i j
private lemma qHF (i j : Fin 8) : q (CartanMatrix.Relations.HF ℂ CartanMatrix.E₈ (i, j)) = 0 := by
  change LieSubmodule.Quotient.mk (N := J8) (CartanMatrix.Relations.HF ℂ CartanMatrix.E₈ (i, j)) = 0
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact HF_mem i j
private lemma qEF (i j : Fin 8) : q (CartanMatrix.Relations.EF ℂ (i, j)) = 0 := by
  change LieSubmodule.Quotient.mk (N := J8) (CartanMatrix.Relations.EF ℂ (i, j)) = 0
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact EF_mem i j

private lemma rHH (i j : Fin 8) : ⁅genH i, genH j⁆ = 0 := by
  rw [show genH i = q (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i)) from rfl,
      show genH j = q (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H j)) from rfl,
      ← LieHom.map_lie]
  rw [show ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i),
        FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H j)⁆
      = CartanMatrix.Relations.HH ℂ (i, j) from rfl, qHH]

private lemma rHE (i j : Fin 8) : ⁅genH i, genE j⁆ = (CartanMatrix.E₈ i j) • genE j := by
  rw [show genH i = q (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i)) from rfl,
      show genE j = q (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j)) from rfl,
      ← LieHom.map_lie]
  have hdeq : ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i),
        FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j)⁆
      = CartanMatrix.Relations.HE ℂ CartanMatrix.E₈ (i, j)
        + (CartanMatrix.E₈ i j) • FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j) := by
    rw [show CartanMatrix.Relations.HE ℂ CartanMatrix.E₈ (i, j)
        = ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j)⁆
          - (CartanMatrix.E₈ i j) • FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j) from rfl]
    abel
  rw [hdeq, map_add, map_zsmul, qHE, zero_add]

private lemma rHF (i j : Fin 8) : ⁅genH i, genF j⁆ = (-(CartanMatrix.E₈ i j)) • genF j := by
  rw [show genH i = q (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i)) from rfl,
      show genF j = q (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)) from rfl,
      ← LieHom.map_lie]
  have hdeq : ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i),
        FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)⁆
      = CartanMatrix.Relations.HF ℂ CartanMatrix.E₈ (i, j)
        + (-(CartanMatrix.E₈ i j)) • FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j) := by
    rw [show CartanMatrix.Relations.HF ℂ CartanMatrix.E₈ (i, j)
        = ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)⁆
          + (CartanMatrix.E₈ i j) • FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j) from rfl]
    simp only [neg_smul, add_assoc, add_neg_cancel, add_zero]
  rw [hdeq, map_add, map_zsmul, qHF, zero_add]

private lemma rEF (i j : Fin 8) : ⁅genE i, genF j⁆ = if i = j then genH i else 0 := by
  have hE : genE i = q (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i)) := rfl
  have hF : genF j = q (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)) := rfl
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, hE, hF, ← LieHom.map_lie]
    have hdeq : ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i),
          FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i)⁆
        = CartanMatrix.Relations.EF ℂ (i, i) + FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i) := by
      rw [show CartanMatrix.Relations.EF ℂ (i, i)
          = ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i)⁆
            - FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i) from by
        simp [CartanMatrix.Relations.EF]]
      abel
    rw [hdeq, map_add, qEF, zero_add]
    exact rfl
  · rw [if_neg h, hE, hF, ← LieHom.map_lie]
    have hdeq : ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i),
          FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)⁆
        = CartanMatrix.Relations.EF ℂ (i, j) := by
      rw [show CartanMatrix.Relations.EF ℂ (i, j)
          = ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)⁆ from by
        simp [CartanMatrix.Relations.EF, h]]
    rw [hdeq, qEF]

private lemma ad_mem_of_mem_lieSpan_of {R : Type*} [CommRing R] {L : Type*} [LieRing L] [LieAlgebra R L]
    {s : Set L} {W : Submodule R L} {u : L}
    (hW : ∀ ⦃a b : L⦄, a ∈ W → b ∈ W → ⁅a, b⁆ ∈ W)
    (hSW : (LieSubalgebra.lieSpan R L s : Submodule R L) ≤ W)
    (hgen : ∀ p ∈ s, ⁅u, p⁆ ∈ W) :
    ∀ y ∈ LieSubalgebra.lieSpan R L s, ⁅u, y⁆ ∈ W := by
  let S : LieSubalgebra R L := LieSubalgebra.lieSpan R L s
  let Nsub : Submodule R L :=
    { carrier := {y | y ∈ S ∧ ⁅u, y⁆ ∈ W}
      zero_mem' := ⟨S.zero_mem, by rw [lie_zero]; exact W.zero_mem⟩
      add_mem' := fun ha hb => ⟨S.add_mem ha.1 hb.1, by rw [lie_add]; exact W.add_mem ha.2 hb.2⟩
      smul_mem' := fun c y hy => ⟨S.smul_mem c hy.1, by rw [lie_smul]; exact W.smul_mem c hy.2⟩ }
  let N : LieSubalgebra R L :=
    { Nsub with lie_mem' := fun {a b} ha hb =>
        ⟨S.lie_mem ha.1 hb.1, by
          rw [leibniz_lie]
          exact W.add_mem (hW ha.2 (hSW hb.1)) (hW (hSW ha.1) hb.2)⟩ }
  have hle : S ≤ N :=
    LieSubalgebra.lieSpan_le.mpr fun p hp => ⟨LieSubalgebra.subset_lieSpan hp, hgen p hp⟩
  intro y hy
  exact (hle hy).2

end Commons.Algebra.Lie.SerreConstruction

namespace Commons.Algebra.Lie.SerreConstruction

theorem e8_eq_sup_cartan_positive_negative :
    (LieSubalgebra.lieSpan ℂ (LieAlgebra.e₈ ℂ) (Set.range (fun i : Fin 8 =>
        (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
          (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i)) : LieAlgebra.e₈ ℂ))) :
        Submodule ℂ (LieAlgebra.e₈ ℂ)) ⊔
      Submodule.span ℂ (Set.range (fun i : Fin 8 =>
        (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
          (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i)) : LieAlgebra.e₈ ℂ))) ⊔
      (LieSubalgebra.lieSpan ℂ (LieAlgebra.e₈ ℂ) (Set.range (fun i : Fin 8 =>
        (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
          (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i)) : LieAlgebra.e₈ ℂ))) :
        Submodule ℂ (LieAlgebra.e₈ ℂ)) = ⊤ := by
  change W8 = ⊤
  have hSE_le : (SE : Submodule ℂ L8) ≤ W8 :=
    fun x hx => Submodule.mem_sup_left (Submodule.mem_sup_left hx)
  have hH0_le : H0 ≤ W8 := fun x hx => Submodule.mem_sup_left (Submodule.mem_sup_right hx)
  have hSF_le : (SF : Submodule ℂ L8) ≤ W8 := fun x hx => Submodule.mem_sup_right hx
  have hW1_le : H0 ⊔ (SF : Submodule ℂ L8) ≤ W8 := sup_le hH0_le hSF_le
  -- (1) [genH i, SE] ⊆ SE
  have hH_SE : ∀ i, ∀ y ∈ SE, ⁅genH i, y⁆ ∈ SE := by
    intro i
    refine ad_mem_of_mem_lieSpan_of (W := (SE : Submodule ℂ L8)) ?_ ?_ ?_
    · intro a b ha hb; exact SE.lie_mem ha hb
    · exact le_rfl
    · intro p hp
      obtain ⟨j, rfl⟩ := hp
      rw [rHE i j]
      exact zsmul_mem (LieSubalgebra.subset_lieSpan (Set.mem_range_self j)) (CartanMatrix.E₈ i j)
  -- (2) [genH i, SF] ⊆ SF
  have hH_SF : ∀ i, ∀ y ∈ SF, ⁅genH i, y⁆ ∈ SF := by
    intro i
    refine ad_mem_of_mem_lieSpan_of (W := (SF : Submodule ℂ L8)) ?_ ?_ ?_
    · intro a b ha hb; exact SF.lie_mem ha hb
    · exact le_rfl
    · intro p hp
      obtain ⟨j, rfl⟩ := hp
      rw [rHF i j]
      exact zsmul_mem (LieSubalgebra.subset_lieSpan (Set.mem_range_self j)) (-(CartanMatrix.E₈ i j))
  -- (3) [SE, H0] ⊆ SE
  have hSE_H0 : ∀ y ∈ SE, ∀ h ∈ H0, ⁅y, h⁆ ∈ SE := by
    intro y hy h hh
    refine Submodule.span_induction (p := fun x _ => ⁅y, x⁆ ∈ SE) ?_ ?_ ?_ ?_ hh
    · intro z hz; obtain ⟨i, rfl⟩ := hz
      rw [← lie_skew]
      exact SE.neg_mem (hH_SE i y hy)
    · rw [lie_zero]; exact SE.zero_mem
    · intro a b _ _ ha hb; rw [lie_add]; exact SE.add_mem ha hb
    · intro c a _ ha; rw [lie_smul]; exact SE.smul_mem c ha
  -- (4) [H0, SF] ⊆ SF
  have hH0_SF : ∀ h ∈ H0, ∀ y ∈ SF, ⁅h, y⁆ ∈ SF := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => ∀ z ∈ (SF : Submodule ℂ L8),
      ⁅x, z⁆ ∈ (SF : Submodule ℂ L8)) ?_ ?_ ?_ ?_ hx
    · intro p hp z hz; obtain ⟨i, rfl⟩ := hp; exact hH_SF i z hz
    · intro z hz; rw [zero_lie]; exact SF.zero_mem
    · intro a b _ _ ha hb z hz; rw [add_lie]; exact SF.add_mem (ha z hz) (hb z hz)
    · intro c a _ ha z hz; rw [smul_lie]; exact SF.smul_mem c (ha z hz)
  -- (5) [H0, H0] ⊆ H0
  have hH0_H0 : ∀ h1 ∈ H0, ∀ h2 ∈ H0, ⁅h1, h2⁆ ∈ H0 := by
    have hgen : ∀ i, ∀ z ∈ H0, ⁅genH i, z⁆ ∈ H0 := by
      intro i z hz
      refine Submodule.span_induction (p := fun z _ => ⁅genH i, z⁆ ∈ H0) ?_ ?_ ?_ ?_ hz
      · intro w hw; obtain ⟨j, rfl⟩ := hw; rw [rHH i j]; exact H0.zero_mem
      · rw [lie_zero]; exact H0.zero_mem
      · intro a b _ _ ha hb; rw [lie_add]; exact H0.add_mem ha hb
      · intro c a _ ha; rw [lie_smul]; exact H0.smul_mem c ha
    intro h1 hh1
    refine Submodule.span_induction (p := fun z _ => ∀ h2 ∈ H0, ⁅z, h2⁆ ∈ H0) ?_ ?_ ?_ ?_ hh1
    · intro w hw h2 hh2; obtain ⟨i, rfl⟩ := hw; exact hgen i h2 hh2
    · intro h2 _; rw [zero_lie]; exact H0.zero_mem
    · intro a b _ _ ha hb h2 hh2; rw [add_lie]; exact H0.add_mem (ha h2 hh2) (hb h2 hh2)
    · intro c a _ ha h2 hh2; rw [smul_lie]; exact H0.smul_mem c (ha h2 hh2)
  -- (6) W1 = H0 ⊔ SF closed under bracket
  have hW1closed : ∀ ⦃a b : L8⦄, a ∈ H0 ⊔ (SF : Submodule ℂ L8) → b ∈ H0 ⊔ (SF : Submodule ℂ L8) →
      ⁅a, b⁆ ∈ H0 ⊔ (SF : Submodule ℂ L8) := by
    intro a b ha hb
    obtain ⟨h1, hh1, m1, hm1, haeq⟩ := Submodule.mem_sup.mp ha
    obtain ⟨h2, hh2, m2, hm2, hbeq⟩ := Submodule.mem_sup.mp hb
    have h11 : ⁅h1, h2⁆ ∈ H0 ⊔ (SF : Submodule ℂ L8) := Submodule.mem_sup_left (hH0_H0 h1 hh1 h2 hh2)
    have h12 : ⁅h1, m2⁆ ∈ H0 ⊔ (SF : Submodule ℂ L8) := Submodule.mem_sup_right (hH0_SF h1 hh1 m2 hm2)
    have h21 : ⁅m1, h2⁆ ∈ H0 ⊔ (SF : Submodule ℂ L8) := Submodule.mem_sup_right (by
      rw [← lie_skew]; exact SF.neg_mem (hH0_SF h2 hh2 m1 hm1))
    have h22 : ⁅m1, m2⁆ ∈ H0 ⊔ (SF : Submodule ℂ L8) := Submodule.mem_sup_right (SF.lie_mem hm1 hm2)
    rw [← haeq, ← hbeq]
    simp only [add_lie, lie_add]
    repeat' first
      | exact h11 | exact h12 | exact h21 | exact h22
      | apply Submodule.add_mem
  -- (7) [genE i, SF] ⊆ W1
  have hE_SF : ∀ i, ∀ y ∈ SF, ⁅genE i, y⁆ ∈ H0 ⊔ (SF : Submodule ℂ L8) := by
    intro i
    refine ad_mem_of_mem_lieSpan_of (W := H0 ⊔ (SF : Submodule ℂ L8)) hW1closed ?_ ?_
    · exact le_sup_right
    · intro p hp
      obtain ⟨j, rfl⟩ := hp
      rw [rEF i j]
      by_cases hij : i = j
      · rw [if_pos hij]
        exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_range_self i))
      · rw [if_neg hij]; exact (H0 ⊔ (SF : Submodule ℂ L8)).zero_mem
  -- (8) [genE i, W8] ⊆ W8
  have hgenE_W8 : ∀ i, ∀ w ∈ W8, ⁅genE i, w⁆ ∈ W8 := by
    intro i w hw
    obtain ⟨u, hu, m, hm, hweq⟩ := Submodule.mem_sup.mp hw
    obtain ⟨s, hs, h, hh, hueq⟩ := Submodule.mem_sup.mp hu
    have h1 : ⁅genE i, s⁆ ∈ W8 :=
      hSE_le (SE.lie_mem (LieSubalgebra.subset_lieSpan (Set.mem_range_self i)) hs)
    have h2 : ⁅genE i, h⁆ ∈ W8 :=
      hSE_le (hSE_H0 (genE i) (LieSubalgebra.subset_lieSpan (Set.mem_range_self i)) h hh)
    have h3 : ⁅genE i, m⁆ ∈ W8 := hW1_le (hE_SF i m hm)
    rw [← hweq, ← hueq]
    simp only [lie_add]
    repeat' first | exact h1 | exact h2 | exact h3 | apply Submodule.add_mem
  -- (9) [SE, W8] ⊆ W8
  have hSE_W8 : ∀ y ∈ SE, ∀ w ∈ W8, ⁅y, w⁆ ∈ W8 := by
    let Qsub : Submodule ℂ L8 :=
      { carrier := {y | y ∈ SE ∧ ∀ w ∈ W8, ⁅y, w⁆ ∈ W8}
        zero_mem' := ⟨SE.zero_mem, fun w _ => by rw [zero_lie]; exact W8.zero_mem⟩
        add_mem' := fun ha hb => ⟨SE.add_mem ha.1 hb.1, fun w hw => by
          rw [add_lie]; exact W8.add_mem (ha.2 w hw) (hb.2 w hw)⟩
        smul_mem' := fun c y hy => ⟨SE.smul_mem c hy.1, fun w hw => by
          rw [smul_lie]; exact W8.smul_mem c (hy.2 w hw)⟩ }
    let Q : LieSubalgebra ℂ L8 :=
      { Qsub with lie_mem' := fun {a b} ha hb =>
          ⟨SE.lie_mem ha.1 hb.1, fun w hw => by
            have h1 : ⁅b, w⁆ ∈ W8 := hb.2 w hw
            have h2 : ⁅a, w⁆ ∈ W8 := ha.2 w hw
            have hJ : ⁅⁅a, b⁆, w⁆ = ⁅a, ⁅b, w⁆⁆ - ⁅b, ⁅a, w⁆⁆ := by
              rw [leibniz_lie]; abel
            rw [hJ]
            exact W8.sub_mem (ha.2 _ h1) (hb.2 _ h2)⟩ }
    have hle : SE ≤ Q :=
      LieSubalgebra.lieSpan_le.mpr fun p hp => by
        obtain ⟨i, rfl⟩ := hp
        exact ⟨LieSubalgebra.subset_lieSpan (Set.mem_range_self i), hgenE_W8 i⟩
    intro y hy w hw
    exact (hle hy).2 w hw
  -- (10) W8 closed under bracket
  have hW8closed : ∀ ⦃a b : L8⦄, a ∈ W8 → b ∈ W8 → ⁅a, b⁆ ∈ W8 := by
    intro a b ha hb
    obtain ⟨u, hu, m, hm, haeq⟩ := Submodule.mem_sup.mp ha
    obtain ⟨s, hs, h, hh, hueq⟩ := Submodule.mem_sup.mp hu
    obtain ⟨u', hu', m', hm', hbeq⟩ := Submodule.mem_sup.mp hb
    obtain ⟨s', hs', h', hh', hu'eq⟩ := Submodule.mem_sup.mp hu'
    have h1 : ⁅s, s'⁆ ∈ W8 := hSE_le (SE.lie_mem hs hs')
    have h2 : ⁅s, h'⁆ ∈ W8 := hSE_le (hSE_H0 s hs h' hh')
    have h3 : ⁅s, m'⁆ ∈ W8 := hSE_W8 s hs m' (hSF_le hm')
    have h4 : ⁅h, s'⁆ ∈ W8 := hSE_le (by rw [← lie_skew]; exact SE.neg_mem (hSE_H0 s' hs' h hh))
    have h5 : ⁅h, h'⁆ ∈ W8 := hH0_le (hH0_H0 h hh h' hh')
    have h6 : ⁅h, m'⁆ ∈ W8 := hSF_le (hH0_SF h hh m' hm')
    have h7 : ⁅m, s'⁆ ∈ W8 := by
      rw [← lie_skew]; exact W8.neg_mem (hSE_W8 s' hs' m (hSF_le hm))
    have h8 : ⁅m, h'⁆ ∈ W8 := by
      rw [← lie_skew]; exact W8.neg_mem (hSF_le (hH0_SF h' hh' m hm))
    have h9 : ⁅m, m'⁆ ∈ W8 := hSF_le (SF.lie_mem hm hm')
    rw [← haeq, ← hueq, ← hbeq, ← hu'eq]
    simp only [add_lie, lie_add]
    repeat' first
      | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6 | exact h7 | exact h8 | exact h9
      | apply Submodule.add_mem
  -- (11) conclude
  let N : LieSubalgebra ℂ L8 := { W8 with lie_mem' := fun ha hb => hW8closed ha hb }
  have hgen : ∀ g : CartanMatrix.Generators (Fin 8),
      LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
        (FreeLieAlgebra.of ℂ g) ∈ N := by
    intro g
    cases g with
    | H i => exact hH0_le (Submodule.subset_span (Set.mem_range_self i))
    | E i => exact hSE_le (LieSubalgebra.subset_lieSpan (Set.mem_range_self i))
    | F i => exact hSF_le (LieSubalgebra.subset_lieSpan (Set.mem_range_self i))
  have hNtop : N = ⊤ := eq_top_of_lieSubalgebra_of_generators CartanMatrix.E₈ N hgen
  rw [← show ((N : LieSubalgebra ℂ L8) : Submodule ℂ L8) = W8 from rfl, hNtop]
  rfl

end Commons.Algebra.Lie.SerreConstruction