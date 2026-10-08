import Mathlib
import Submission.Work.AUTA7.Defs
import Submission.Work.AUTA7.Dihedral.AutOrderThree
import Submission.Work.A7.Defs
import Submission.Work.AUTA7.A7.SylowTwoSubgroup
import Submission.Work.AUTA7.A7.CentralizerInvolution
import Submission.Work.AUTA7.A7.CentralizerOrderThree

/-!
# `A₇`: the Sylow `2`-subgroup is self-normalizing and the centralizers of its involutions
generate `A₇`

This file proves `Work.GW2.A7SylowFactsProp`:

* `N_{A₇}(D) = D` for every Sylow `2`-subgroup `D` of `A₇` (here `D ≅ DihedralGroup 4`) and
* the join of the centralizers `C_{A₇}(z)`, over the involutions `z ∈ D`, is all of `A₇`.

The second statement is proved by reducing to the concrete Sylow
`D₀ = ⟨(0 1 2 3)(4 5), (0 2)(4 5)⟩`: the join over `D₀` contains a 3-cycle and acts transitively
on `Fin 7`, hence (Jordan's theorem, `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`)
contains `A₇`.
-/

open Equiv
open scoped Pointwise

namespace Work.AUTA7.A7

abbrev Alt7 := alternatingGroup (Fin 7)

theorem card_range_dihToA7 : Nat.card ↥dihToA7.range = 2 ^ 3 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective dihToA7_injective).toEquiv,
    DihedralGroup.nat_card]
  norm_num

theorem index_range_dihToA7 : dihToA7.range.index = 315 := by
  have h := Subgroup.card_mul_index dihToA7.range
  rw [card_range_dihToA7, Work.A7.card_alternatingGroup_seven] at h
  omega

theorem not_two_dvd_index_range : ¬ 2 ∣ dihToA7.range.index := by
  rw [index_range_dihToA7]
  decide

noncomputable def sylowD0 : Sylow 2 Alt7 :=
  (IsPGroup.of_card card_range_dihToA7).toSylow not_two_dvd_index_range

theorem sylowD0_coe : (sylowD0 : Subgroup Alt7) = dihToA7.range :=
  IsPGroup.toSylow_coe (IsPGroup.of_card card_range_dihToA7) not_two_dvd_index_range

theorem mem_sylowD0_sr_one : (a7S * a7R : Alt7) ∈ (sylowD0 : Subgroup Alt7) := by
  rw [sylowD0_coe]
  exact ⟨DihedralGroup.sr 1, by decide⟩

theorem orderOf_a7S_mul_a7R : orderOf (a7S * a7R : Alt7) = 2 :=
  orderOf_eq_prime (by decide) (by decide)

theorem orderOf_a7R_sq : orderOf ((a7R : Alt7) ^ 2) = 2 :=
  orderOf_eq_prime (by decide) (by decide)

theorem mem_sylowD0_R_sq : ((a7R : Alt7) ^ 2) ∈ (sylowD0 : Subgroup Alt7) := by
  rw [sylowD0_coe]
  exact ⟨DihedralGroup.r 2, by decide⟩

theorem mem_sylowD0_a7S : (a7S : Alt7) ∈ (sylowD0 : Subgroup Alt7) := by
  rw [sylowD0_coe]
  exact ⟨DihedralGroup.sr 0, by decide⟩

theorem orderOf_a7S : orderOf (a7S : Alt7) = 2 :=
  orderOf_eq_prime (by decide) (by decide)

/-- `X = (0 4)(2 5)` -/
def bigX : Alt7 := ⟨Equiv.swap 0 4 * Equiv.swap 2 5, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem commute_XY_a7S : bigX * (a7S : Alt7) = (a7S : Alt7) * bigX := by decide
theorem bigX_smul_zero : bigX • (0 : Fin 7) = 4 := by decide
theorem R_smul_zero : (a7R : Alt7) • (0 : Fin 7) = 1 := by decide
theorem Rsq_smul_zero : ((a7R : Alt7)^2) • (0 : Fin 7) = 2 := by decide
theorem Rcub_smul_zero : ((a7R : Alt7)^3) • (0 : Fin 7) = 3 := by decide
theorem c1_smul_four : (Work.A7.a7ThreeCycle : Alt7) • (4 : Fin 7) = 5 := by decide
theorem c1sq_smul_four : (Work.A7.a7ThreeCycle : Alt7)^2 • (4 : Fin 7) = 6 := by decide

theorem isThreeCycle_a7ThreeCycle : (Work.A7.a7ThreeCycle : Perm (Fin 7)).IsThreeCycle := by
  have h := Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := (5:Fin 7)) (b := 4) (c := 6)
    (by decide) (by decide) (by decide)
  simpa [Work.A7.coe_a7ThreeCycle, Work.A7.a7ThreeCyclePerm, Equiv.swap_comm] using h


open MulAction

/-- The join of the centralizers of the involutions of a subgroup. -/
def joinOf (D : Subgroup Alt7) : Subgroup Alt7 :=
  ⨆ (z : Alt7) (_ : z ∈ D) (_ : orderOf z = 2), Subgroup.centralizer ({z} : Set Alt7)

theorem mem_joinOf {D : Subgroup Alt7} {w x : Alt7} (hw : w ∈ D) (ho : orderOf w = 2)
    (h : x * w = w * x) : x ∈ joinOf D := by
  have hx : x ∈ Subgroup.centralizer ({w} : Set Alt7) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h
  have h1 := le_iSup (fun _ : orderOf w = 2 => Subgroup.centralizer ({w} : Set Alt7)) ho hx
  have h2 := le_iSup (fun _ : w ∈ D => ⨆ (_ : orderOf w = 2),
    Subgroup.centralizer ({w} : Set Alt7)) hw h1
  exact le_iSup (fun z : Alt7 => ⨆ (_ : z ∈ D), ⨆ (_ : orderOf z = 2),
    Subgroup.centralizer ({z} : Set Alt7)) w h2

theorem mem_joinD0_bigX : bigX ∈ joinOf (sylowD0 : Subgroup Alt7) :=
  mem_joinOf mem_sylowD0_a7S orderOf_a7S commute_XY_a7S

theorem mem_joinD0_R : (a7R : Alt7) ∈ joinOf (sylowD0 : Subgroup Alt7) :=
  mem_joinOf mem_sylowD0_R_sq orderOf_a7R_sq (by decide)

theorem mem_joinD0_c1 : (Work.A7.a7ThreeCycle : Alt7) ∈ joinOf (sylowD0 : Subgroup Alt7) :=
  mem_joinOf mem_sylowD0_R_sq orderOf_a7R_sq
    (by decide : (Work.A7.a7ThreeCycle : Alt7) * ((a7R : Alt7)^2) = ((a7R : Alt7)^2) * _)

theorem exists_smul_zero_eq (y : Fin 7) :
    ∃ g : joinOf (sylowD0 : Subgroup Alt7), g • (0 : Fin 7) = y := by
  fin_cases y
  · exact ⟨1, by simp⟩
  · exact ⟨⟨a7R, mem_joinD0_R⟩, R_smul_zero⟩
  · exact ⟨⟨(a7R : Alt7)^2, pow_mem mem_joinD0_R 2⟩, Rsq_smul_zero⟩
  · exact ⟨⟨(a7R : Alt7)^3, pow_mem mem_joinD0_R 3⟩, Rcub_smul_zero⟩
  · exact ⟨⟨bigX, mem_joinD0_bigX⟩, bigX_smul_zero⟩
  · refine ⟨⟨(Work.A7.a7ThreeCycle : Alt7) * bigX, mul_mem mem_joinD0_c1 mem_joinD0_bigX⟩, ?_⟩
    show ((Work.A7.a7ThreeCycle : Alt7) * bigX) • (0 : Fin 7) = (5 : Fin 7)
    rw [mul_smul, bigX_smul_zero, c1_smul_four]
  · refine ⟨⟨(Work.A7.a7ThreeCycle : Alt7)^2 * bigX, mul_mem (pow_mem mem_joinD0_c1 2) mem_joinD0_bigX⟩, ?_⟩
    show ((Work.A7.a7ThreeCycle : Alt7)^2 * bigX) • (0 : Fin 7) = (6 : Fin 7)
    rw [mul_smul, bigX_smul_zero, c1sq_smul_four]

theorem pretransitive_joinD0 : MulAction.IsPretransitive (joinOf (sylowD0 : Subgroup Alt7)) (Fin 7) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨g, hg⟩ := exists_smul_zero_eq a
  obtain ⟨h, hh⟩ := exists_smul_zero_eq b
  refine ⟨h * g⁻¹, ?_⟩
  rw [mul_smul]
  have h1 : g⁻¹ • a = (0 : Fin 7) := by
    rw [← hg]
    rw [← mul_smul, inv_mul_cancel, one_smul]
  rw [h1, hh]

theorem preprimitive_joinD0 : MulAction.IsPreprimitive (joinOf (sylowD0 : Subgroup Alt7)) (Fin 7) := by
  haveI := pretransitive_joinD0
  refine MulAction.IsPreprimitive.of_prime_card ?_
  rw [Nat.card_fin]
  norm_num

/-- The image of `joinOf D₀` in `Perm (Fin 7)`. -/
noncomputable def Jperm : Subgroup (Perm (Fin 7)) :=
  (joinOf (sylowD0 : Subgroup Alt7)).map (Subgroup.subtype Alt7)

theorem exists_smul_zero_eq_perm (y : Fin 7) : ∃ g : Jperm, g • (0 : Fin 7) = y := by
  obtain ⟨g, hg⟩ := exists_smul_zero_eq y
  exact ⟨⟨(g : Perm (Fin 7)), Subgroup.mem_map.mpr ⟨g, g.2, rfl⟩⟩, hg⟩

theorem pretransitive_Jperm : MulAction.IsPretransitive Jperm (Fin 7) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨g, hg⟩ := exists_smul_zero_eq_perm a
  obtain ⟨h, hh⟩ := exists_smul_zero_eq_perm b
  refine ⟨h * g⁻¹, ?_⟩
  rw [mul_smul]
  have h1 : g⁻¹ • a = (0 : Fin 7) := by
    rw [← hg]
    rw [← mul_smul, inv_mul_cancel, one_smul]
  rw [h1, hh]

theorem preprimitive_Jperm : MulAction.IsPreprimitive Jperm (Fin 7) := by
  haveI := pretransitive_Jperm
  refine MulAction.IsPreprimitive.of_prime_card ?_
  rw [Nat.card_fin]
  norm_num

theorem alternatingGroup_le_Jperm : alternatingGroup (Fin 7) ≤ Jperm :=
  Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem preprimitive_Jperm
    isThreeCycle_a7ThreeCycle (Subgroup.mem_map.mpr ⟨_, mem_joinD0_c1, rfl⟩)

theorem map_top_subtype : (⊤ : Subgroup Alt7).map (Subgroup.subtype Alt7) = alternatingGroup (Fin 7) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, trivial, rfl⟩

theorem joinOf_sylowD0_eq_top : joinOf (sylowD0 : Subgroup Alt7) = ⊤ := by
  have hmap : Jperm = alternatingGroup (Fin 7) :=
    le_antisymm (Subgroup.map_subtype_le _) alternatingGroup_le_Jperm
  refine Subgroup.map_injective (f := Subgroup.subtype Alt7) Subtype.val_injective ?_
  rw [show (joinOf (sylowD0 : Subgroup Alt7)).map (Subgroup.subtype Alt7) = Jperm from rfl,
    hmap, map_top_subtype]



/-! ## Conjugation transport of the join of centralizers -/

theorem map_centralizer_conj (g z : Alt7) :
    (Subgroup.centralizer ({z} : Set Alt7)).map (MulAut.conj g).toMonoidHom
      = Subgroup.centralizer ({(MulAut.conj g) z} : Set Alt7) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    change (MulEquiv.toMonoidHom (MulAut.conj g)) x *
        (MulEquiv.toMonoidHom (MulAut.conj g)) z =
      (MulEquiv.toMonoidHom (MulAut.conj g)) z *
        (MulEquiv.toMonoidHom (MulAut.conj g)) x
    rw [← map_mul, ← map_mul, hx]
  · intro y hy
    rw [Subgroup.mem_map]
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      rw [Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply] at hy
      calc (g⁻¹ * y * g) * z = g⁻¹ * (y * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * y) * g := by rw [hy]
        _ = z * (g⁻¹ * y * g) := by group
    · change g * (g⁻¹ * y * g) * g⁻¹ = y
      group

theorem map_conj_le_joinOf {D : Subgroup Alt7} {g : Alt7} :
    (joinOf D).map (MulAut.conj g).toMonoidHom
      ≤ joinOf (D.map (MulAut.conj g).toMonoidHom) := by
  rw [joinOf, Subgroup.map_iSup]
  refine iSup_le fun z => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hz => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun ho => ?_
  rw [map_centralizer_conj]
  have hmem : (MulAut.conj g) z ∈ D.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have hord : orderOf ((MulAut.conj g) z) = 2 := by
    have h2 : orderOf ((MulAut.conj g) z) = orderOf z :=
      orderOf_injective (MulEquiv.toMonoidHom (MulAut.conj g))
        (MulEquiv.injective (MulAut.conj g)) z
    rw [h2, ho]
  intro x hx
  exact le_iSup (fun z' : Alt7 => ⨆ (_ : z' ∈ D.map (MulAut.conj g).toMonoidHom),
      ⨆ (_ : orderOf z' = 2), Subgroup.centralizer ({z'} : Set Alt7)) ((MulAut.conj g) z)
    (le_iSup (fun _ : (MulAut.conj g) z ∈ D.map (MulAut.conj g).toMonoidHom =>
        ⨆ (_ : orderOf ((MulAut.conj g) z) = 2),
          Subgroup.centralizer ({(MulAut.conj g) z} : Set Alt7)) hmem
      (le_iSup (fun _ : orderOf ((MulAut.conj g) z) = 2 =>
          Subgroup.centralizer ({(MulAut.conj g) z} : Set Alt7)) hord hx))

theorem joinOf_sylow_eq_top (D : Sylow 2 Alt7) : joinOf (D : Subgroup Alt7) = ⊤ := by
  haveI : MulAction.IsPretransitive Alt7 (Sylow 2 Alt7) :=
    Sylow.isPretransitive_of_finite (p := 2) (G := Alt7)
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Alt7)
    (α := Sylow 2 Alt7) (sylowD0) D
  -- the set equality `g D₀ g⁻¹ = D`
  have hset : (MulAut.conj g) • ((sylowD0 : Subgroup Alt7) : Set Alt7)
      = ((D : Subgroup Alt7) : Set Alt7) := by
    rw [← congrArg (fun P : Sylow 2 Alt7 => ((P : Subgroup Alt7) : Set Alt7)) hg]
    exact Sylow.coe_smul
  have hmemD : ∀ z ∈ (sylowD0 : Subgroup Alt7), (MulAut.conj g) z ∈ (D : Subgroup Alt7) := by
    intro z hz
    have h1 : (MulAut.conj g) z ∈ (MulAut.conj g) • ((sylowD0 : Subgroup Alt7) : Set Alt7) :=
      Set.smul_mem_smul_set hz
    rwa [hset] at h1
  have hle : (joinOf (sylowD0 : Subgroup Alt7)).map (MulAut.conj g).toMonoidHom
      ≤ joinOf (D : Subgroup Alt7) := by
    rw [joinOf, Subgroup.map_iSup]
    refine iSup_le fun z => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hz => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ho => ?_
    rw [map_centralizer_conj]
    have hmem := hmemD z hz
    have hord : orderOf ((MulAut.conj g) z) = 2 := by
      have h2 : orderOf ((MulAut.conj g) z) = orderOf z :=
        orderOf_injective (MulEquiv.toMonoidHom (MulAut.conj g))
          (MulEquiv.injective (MulAut.conj g)) z
      rw [h2, ho]
    intro x hx
    exact le_iSup (fun z' : Alt7 => ⨆ (_ : z' ∈ (D : Subgroup Alt7)),
        ⨆ (_ : orderOf z' = 2),
          Subgroup.centralizer ({z'} : Set Alt7)) ((MulAut.conj g) z)
      (le_iSup (fun _ : (MulAut.conj g) z ∈ (D : Subgroup Alt7) =>
          ⨆ (_ : orderOf ((MulAut.conj g) z) = 2),
            Subgroup.centralizer ({(MulAut.conj g) z} : Set Alt7)) hmem
        (le_iSup (fun _ : orderOf ((MulAut.conj g) z) = 2 =>
            Subgroup.centralizer ({(MulAut.conj g) z} : Set Alt7)) hord hx))
  have htop : (joinOf (sylowD0 : Subgroup Alt7)).map (MulAut.conj g).toMonoidHom = ⊤ := by
    rw [joinOf_sylowD0_eq_top, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]
  rw [htop] at hle
  exact le_antisymm le_top hle

/-! ## Part 1: `N(D) = D` -/

namespace Part1

open DihedralGroup

theorem mulAut_dihedral_four_pow_eight (σ : MulAut (DihedralGroup 4)) : σ ^ 8 = 1 := by
  -- Step 1: σ (r 1) is r 1 or r 3
  have hordr1 : orderOf (DihedralGroup.r 1 : DihedralGroup 4) = 4 := by
    rw [DihedralGroup.orderOf_r]
    decide
  have hord : orderOf (σ (DihedralGroup.r 1)) = 4 := by
    have h : orderOf (σ (DihedralGroup.r 1)) =
        orderOf (DihedralGroup.r 1 : DihedralGroup 4) :=
      orderOf_injective (MulEquiv.toMonoidHom σ) (MulEquiv.injective σ) (DihedralGroup.r 1)
    rw [h, hordr1]
  have hσr : σ (DihedralGroup.r 1) = DihedralGroup.r 1 ∨
      σ (DihedralGroup.r 1) = DihedralGroup.r 3 := by
    have key : ∀ i : ZMod 4, 4 / Nat.gcd 4 i.val = 4 → i = 1 ∨ i = 3 := by decide
    rcases hx : σ (DihedralGroup.r 1) with i | i
    · have hi : orderOf (DihedralGroup.r i : DihedralGroup 4) = 4 := by rw [← hx]; exact hord
      rw [DihedralGroup.orderOf_r] at hi
      rcases key i hi with h | h
      · left; rw [h]
      · right; rw [h]
    · have : orderOf (DihedralGroup.sr i : DihedralGroup 4) = 4 := by rw [← hx]; exact hord
      rw [DihedralGroup.orderOf_sr] at this
      norm_num at this
  -- Step 2: σ² fixes the rotations
  have hσ2r1 : σ (σ (DihedralGroup.r 1)) = DihedralGroup.r 1 := by
    rcases hσr with h | h
    · simp only [h]
    · have h3 : (DihedralGroup.r 3 : DihedralGroup 4) = (DihedralGroup.r 1) ^ 3 := by
        rw [DihedralGroup.r_one_pow]
        norm_num
      rw [h, h3, map_pow, h]
      decide
  have hσ2r : ∀ i : ZMod 4, σ (σ (DihedralGroup.r i)) = DihedralGroup.r i := by
    intro i
    have hi : (DihedralGroup.r i : DihedralGroup 4) = (DihedralGroup.r 1) ^ i.val := by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    calc σ (σ (DihedralGroup.r i)) = σ (σ ((DihedralGroup.r 1) ^ i.val)) := by rw [hi]
      _ = σ ((σ (DihedralGroup.r 1)) ^ i.val) := by rw [map_pow]
      _ = (σ (σ (DihedralGroup.r 1))) ^ i.val := by rw [map_pow]
      _ = (DihedralGroup.r 1) ^ i.val := by rw [hσ2r1]
      _ = DihedralGroup.r i := by rw [← hi]
  -- Step 3: σ² (sr 0) is a reflection
  have hσ2sr : ∃ a : ZMod 4, σ (σ (DihedralGroup.sr 0)) = DihedralGroup.sr a := by
    rcases hx : σ (σ (DihedralGroup.sr 0)) with i | i
    · exfalso
      have hA : σ (σ (σ (σ (DihedralGroup.sr 0)))) = DihedralGroup.r i := by
        rw [hx]; exact hσ2r i
      have hB : σ (σ (σ (σ (DihedralGroup.sr 0)))) = σ (σ (DihedralGroup.sr 0)) := by
        rw [hA, ← hx]
      have hC : σ (σ (DihedralGroup.sr 0)) = DihedralGroup.sr 0 := (σ * σ).injective hB
      rw [hx] at hC
      exact absurd hC (by intro h; cases h)
    · exact ⟨i, rfl⟩
  obtain ⟨a, ha⟩ := hσ2sr
  -- Step 4: the orbit formula for reflections
  have hstep : ∀ i : ZMod 4, σ (σ (DihedralGroup.sr i)) = DihedralGroup.sr (a + i) := by
    intro i
    have hsr : (DihedralGroup.sr i : DihedralGroup 4) =
        DihedralGroup.r (-i) * DihedralGroup.sr 0 := by
      rw [DihedralGroup.r_mul_sr]; simp
    calc σ (σ (DihedralGroup.sr i)) = σ (σ (DihedralGroup.r (-i) * DihedralGroup.sr 0)) := by
          rw [hsr]
      _ = σ (σ (DihedralGroup.r (-i)) * σ (DihedralGroup.sr 0)) := by rw [map_mul]
      _ = σ (σ (DihedralGroup.r (-i))) * σ (σ (DihedralGroup.sr 0)) := by rw [map_mul]
      _ = DihedralGroup.r (-i) * DihedralGroup.sr a := by rw [hσ2r (-i), ha]
      _ = DihedralGroup.sr (a + i) := by rw [DihedralGroup.r_mul_sr]; congr 1; ring
  have hpow : ∀ (m : ℕ) (i : ZMod 4), ((σ ^ 2) ^ m) (DihedralGroup.sr i) =
      DihedralGroup.sr ((m : ZMod 4) * a + i) := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih =>
      intro i
      rw [pow_succ', show (σ ^ 2 * (σ ^ 2) ^ m) (DihedralGroup.sr i) =
          (σ ^ 2) (((σ ^ 2) ^ m) (DihedralGroup.sr i)) from rfl, ih,
        show (σ ^ 2) (DihedralGroup.sr ((m : ZMod 4) * a + i)) =
          DihedralGroup.sr (a + ((m : ZMod 4) * a + i)) from hstep _]
      congr 1
      push_cast
      ring
  have hpowr : ∀ (m : ℕ) (i : ZMod 4), ((σ ^ 2) ^ m) (DihedralGroup.r i) = DihedralGroup.r i := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih =>
      intro i
      rw [pow_succ', show (σ ^ 2 * (σ ^ 2) ^ m) (DihedralGroup.r i) =
          (σ ^ 2) (((σ ^ 2) ^ m) (DihedralGroup.r i)) from rfl, ih,
        show (σ ^ 2) (DihedralGroup.r i) = DihedralGroup.r i from hσ2r i]
  -- Step 5: conclude
  have h8 : σ ^ 8 = (σ ^ 2) ^ 4 := by rw [← pow_mul]
  apply MulEquiv.ext
  intro x
  show (σ ^ 8) x = x
  rw [h8]
  rcases x with i | i
  · exact hpowr 4 i
  · rw [hpow 4 i]
    have h4a : ((4 : ℕ) : ZMod 4) * a = 0 := by
      have h4 : ((4 : ℕ) : ZMod 4) = 0 := by decide
      rw [h4, zero_mul]
    rw [h4a, zero_add]


theorem mulAut_pow_eight_of_iso {D : Subgroup Alt7} (ψ : D ≃* DihedralGroup 4)
    (σ : MulAut ↥D) : σ ^ 8 = 1 := by
  set e : MulAut (DihedralGroup 4) := ψ.symm.trans (σ.trans ψ) with he
  have he_apply : ∀ y : DihedralGroup 4, e y = ψ (σ (ψ.symm y)) := by
    intro y; rw [he]; rfl
  have hpow : ∀ (n : ℕ) (x : ↥D), (e ^ n) (ψ x) = ψ ((σ ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', show (e * e ^ n) (ψ x) = e ((e ^ n) (ψ x)) from rfl, ih, he_apply]
      simp only [MulEquiv.symm_apply_apply]
      congr 1
      rw [pow_succ']
      rfl
  have h8 : e ^ 8 = 1 := mulAut_dihedral_four_pow_eight e
  apply MulEquiv.ext
  intro x
  apply ψ.injective
  have h := congrArg (fun f : MulAut (DihedralGroup 4) => f (ψ x)) h8
  rw [hpow 8 x] at h
  simpa using h


open Subgroup in
theorem normalizer_eq_of_iso {D : Subgroup Alt7} (ψ : D ≃* DihedralGroup 4) :
    Subgroup.normalizer (D : Set Alt7) = D := by
  set N := Subgroup.normalizer (D : Set Alt7) with hNdef
  set C := Subgroup.centralizer (D : Set Alt7) with hCdef
  have hcardD : Nat.card ↥D = 8 := by
    rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
  -- the conjugation map
  let conjAut (g : ↥N) : MulAut ↥D :=
    { toFun := fun x => ⟨(g : Alt7) * x * (g : Alt7)⁻¹,
        (Subgroup.mem_normalizer_iff.mp g.2 x).mp x.2⟩
      invFun := fun x => ⟨(g : Alt7)⁻¹ * x * (g : Alt7),
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem N g.2) x).mp x.2⟩
      left_inv := by intro x; apply Subtype.ext; group
      right_inv := by intro x; apply Subtype.ext; group
      map_mul' := by intro x y; apply Subtype.ext; simp only [Subgroup.coe_mul]; group }
  have hmul : ∀ (f₁ f₂ : MulAut ↥D) (y : ↥D), (f₁ * f₂) y = f₁ (f₂ y) := fun _ _ _ => rfl
  have hcoe_conjAut : ∀ (g : ↥N) (x : ↥D),
      (conjAut g x : Alt7) = (g : Alt7) * (x : Alt7) * (g : Alt7)⁻¹ := fun _ _ => rfl
  have conjAut_one : conjAut 1 = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [hcoe_conjAut]
    simp
  have conjAut_mul : ∀ g h : ↥N, conjAut (g * h) = conjAut g * conjAut h := by
    intro g h
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp only [hcoe_conjAut, hmul, Subgroup.coe_mul]
    group
  let conjAutHom : ↥N →* MulAut ↥D :=
    { toFun := conjAut, map_one' := conjAut_one, map_mul' := conjAut_mul }
  have hCAH : ∀ g : ↥N, conjAutHom g = conjAut g := fun _ => rfl
  have hker : ∀ g : ↥N, conjAutHom g = 1 → (g : Alt7) ∈ C := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h2 : conjAut g ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [← hCAH g, hg]; rfl
    have h3 : (g : Alt7) * x * (g : Alt7)⁻¹ = x := by
      have := congrArg (fun z : ↥D => (z : Alt7)) h2
      rwa [hcoe_conjAut] at this
    have key : ((g : Alt7) * x * (g : Alt7)⁻¹) * (g : Alt7) = x * (g : Alt7) := by rw [h3]
    have key2 : (g : Alt7) * x = x * (g : Alt7) := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using key
    exact key2.symm
  -- Step A
  have hstep : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card ↥N → p ∣ Nat.card ↥C := by
    intro p hp hp2 hdvd
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hdvd
    have hgp : g ^ p = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hg]
    have hp8 : (conjAutHom g) ^ p = 1 := by
      rw [← map_pow, hgp, map_one]
    have h8 : (conjAutHom g) ^ 8 = 1 := mulAut_pow_eight_of_iso ψ (conjAutHom g)
    have hp8' : ¬ p ∣ 8 := by
      intro h
      have h2 : p ∣ 2 := by
        have := hp.dvd_of_dvd_pow (by simpa using h : p ∣ 2 ^ 3)
        simpa using this
      have hle := Nat.le_of_dvd (by norm_num) h2
      have hge := hp.two_le
      omega
    have hgcd : Nat.gcd 8 p = 1 := by
      have h1 : p.Coprime 8 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hp8'
      rw [Nat.coprime_iff_gcd_eq_one] at h1
      rwa [Nat.gcd_comm] at h1
    have hconj1 : conjAutHom g = 1 := by
      have h1 : orderOf (conjAutHom g) ∣ 8 := orderOf_dvd_iff_pow_eq_one.mpr h8
      have h2 : orderOf (conjAutHom g) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hp8
      have h3 : orderOf (conjAutHom g) ∣ 1 := by
        have := Nat.dvd_gcd h1 h2
        rwa [hgcd] at this
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
    have hmemC : (g : Alt7) ∈ C := hker g hconj1
    have hord1 : orderOf (⟨(g : Alt7), hmemC⟩ : ↥C) = orderOf (g : Alt7) := by
      have h := orderOf_injective (Subgroup.subtype C) Subtype.val_injective
        (⟨(g : Alt7), hmemC⟩ : ↥C)
      simpa using h.symm
    have hord2 : orderOf (g : Alt7) = orderOf (g : ↥N) :=
      orderOf_injective (Subgroup.subtype N) Subtype.val_injective g
    have hordC : p = orderOf (⟨(g : Alt7), hmemC⟩ : ↥C) := by
      rw [hord1, hord2, ← hg]
    rw [hordC, ← Nat.card_zpowers]
    exact Subgroup.card_subgroup_dvd_card _
  -- Step B
  have hCdvd : Nat.card ↥C ∣ 24 := by
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 2 (by rw [hcardD]; norm_num)
    have hword : orderOf (w : Alt7) = 2 :=
      (orderOf_injective (Subgroup.subtype D) Subtype.val_injective w).trans hw
    have hwne : (w : Alt7) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hword
      exact absurd hword (by norm_num)
    have hww : (w : Alt7) * (w : Alt7) = 1 := by
      rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, hword]
    have h24 := CentralizerInvolution hww hwne
    have hle : C ≤ Subgroup.centralizer ({(w : Alt7)} : Set Alt7) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp hx) (w : Alt7) w.2).symm
    have h1 := Subgroup.relIndex_mul_card C (Subgroup.centralizer ({(w : Alt7)} : Set Alt7))
    rw [inf_of_le_left hle, h24] at h1
    exact ⟨C.relIndex _, by rw [mul_comm]; exact h1.symm⟩
  -- Step C: no odd prime divides |N|
  have hNoOdd : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card ↥N := by
    intro p hp hp2 hdvd
    haveI : Fact p.Prime := ⟨hp⟩
    have hCdiv := hstep p hp hp2 hdvd
    have hp24 : p ∣ 24 := hCdiv.trans hCdvd
    have hp3 : p = 3 := by
      have h24' : p ∣ 2 ^ 3 * 3 := by norm_num; exact hp24
      rcases (Nat.Prime.dvd_mul hp).mp h24' with h | h
      · have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
        have hle := Nat.le_of_dvd (by norm_num) h2
        have hge := hp.two_le
        omega
      · have hle3 := Nat.le_of_dvd (by norm_num) h
        have hge := hp.two_le
        omega
    obtain ⟨c, hcord⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) p hCdiv
    have hcC : (c : Alt7) ∈ C := c.2
    have h3 : orderOf (c : Alt7) = 3 := by
      have h1 : orderOf (c : Alt7) = orderOf (c : ↥C) :=
        orderOf_injective (Subgroup.subtype C) Subtype.val_injective c
      rw [h1, hcord, hp3]
    set Cc := Subgroup.centralizer ({(c : Alt7)} : Set Alt7) with hCc
    have hDle : D ≤ Cc := by
      intro x hx
      rw [hCc, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hcC) x hx
    have h8dvd : 8 ∣ Nat.card ↥Cc := by
      have h1 := Subgroup.relIndex_mul_card D Cc
      rw [inf_of_le_left hDle, hcardD] at h1
      exact ⟨D.relIndex Cc, by rw [mul_comm]; exact h1.symm⟩
    rcases CentralizerOrderThree h3 with h | h
    · rw [hCc] at h8dvd; rw [h] at h8dvd; norm_num at h8dvd
    · rw [hCc] at h8dvd; rw [h] at h8dvd; norm_num at h8dvd
  -- conclusion
  have hindexD : D.index = 315 := by
    have h := Subgroup.card_mul_index D
    rw [hcardD, Work.A7.card_alternatingGroup_seven] at h
    omega
  have hrelidx : D.relIndex N = 1 := by
    have hidx : D.relIndex N * N.index = 315 := by
      rw [Subgroup.relIndex_mul_index (Subgroup.le_normalizer), hindexD]
    have hdvd : D.relIndex N ∣ 315 := ⟨N.index, hidx.symm⟩
    by_contra hne1
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne1
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : 2 ∣ 315 := hpdvd.trans hdvd
      norm_num at this
    refine hNoOdd p hp hp2 (hpdvd.trans ?_)
    have hcardN : Nat.card ↥N = D.relIndex N * 8 := by
      have h1 := Subgroup.relIndex_mul_card D N
      rw [inf_of_le_left (Subgroup.le_normalizer), hcardD] at h1
      exact h1.symm
    exact ⟨8, hcardN⟩
  have hle : N ≤ D := Subgroup.relIndex_eq_one.mp hrelidx
  exact le_antisymm hle (Subgroup.le_normalizer)


end Part1

/-! ## The isomorphism `D₀ ≃* DihedralGroup 4` and the main theorem -/

noncomputable def equivSylowD0 : ↥(sylowD0 : Subgroup Alt7) ≃* DihedralGroup 4 :=
  (MulEquiv.ofBijective (dihToA7.codRestrict (sylowD0 : Subgroup Alt7) (by
      intro k
      rw [sylowD0_coe]
      exact ⟨k, rfl⟩))
    ⟨fun a b h => dihToA7_injective (by
        have := congrArg (fun z : ↥(sylowD0 : Subgroup Alt7) => (z : Alt7)) h
        simpa using this), fun y => by
        have hy : (y : Alt7) ∈ dihToA7.range := by
          rw [← sylowD0_coe]; exact y.2
        obtain ⟨k, hk⟩ := hy
        exact ⟨k, Subtype.ext hk⟩⟩).symm

/-- **`A₇`: the Sylow `2`-subgroups are self-normalizing and the centralizers of their
involutions generate `A₇`.** -/
theorem SylowFacts : Work.GW2.A7SylowFactsProp := by
  intro D
  constructor
  · have hiso : ↥(D : Subgroup Alt7) ≃* DihedralGroup 4 :=
      (Sylow.equiv D sylowD0).trans equivSylowD0
    exact Part1.normalizer_eq_of_iso (D := (D : Subgroup Alt7)) hiso
  · exact joinOf_sylow_eq_top D

end Work.AUTA7.A7
