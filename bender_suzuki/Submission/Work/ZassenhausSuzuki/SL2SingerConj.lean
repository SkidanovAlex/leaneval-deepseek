import Mathlib
import Submission.Work.ZassenhausSuzuki.SL2ModelClass
import Submission.Work.Models.PSL2.D_facts
import Submission.Work.ZassenhausSuzuki.SingerModelCycle.singer_cycle_model
import Submission.Work.Models.Port.Commons.LinearAlgebra.Matrix.card_SL2_field

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Singer cycles of `SL(2,F)` form a single conjugacy class

`F` is a finite field of characteristic two.  A *Singer cycle* of `SL(2,F)` is a cyclic
subgroup of order `|F| + 1`; equivalently the centraliser `C(x)` of an element `x ≠ 1` with
`x ^ (|F| + 1) = 1` (there are no other such elements, by `pow_qp1_iff`).  Distinct Singer
cycles intersect trivially, and they are pairwise conjugate
(`sl2_cyclic_conj_card_add_one`), the Singer-cycle companion of `sl2_cyclic_conj_card_sub_one`
in `SL2ModelClass`.

The proof of conjugacy is by counting: the Singer cycles partition the non-identity elements
`x` with `x ^ (|F|+1) = 1` into blocks of size `|F|`, so their number is `|F| (|F| - 1) / 2`
(`two_mul_card_T`), which is also the size of the conjugacy class of one Singer cycle
(`|SL(2,F)| / |N(V)|`, from `card_SL2_field` and `card_normalizer_singer`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Matrix

namespace Work.ZassenhausSuzuki

open Work.Hering.AppVIII

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

section Elements

/-- Conjugating the centraliser of `a` gives the centraliser of the conjugate of `a`. -/
private lemma map_conj_centralizer {G : Type*} [Group G] (c a : G) :
    (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj c).toMonoidHom
      = Subgroup.centralizer ({(MulAut.conj c) a} : Set G) := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨y, hy, rfl⟩ := hg
    rw [Subgroup.mem_centralizer_iff] at hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have h1 : a * y = y * a := hy a rfl
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e1 : c * a * c⁻¹ * (c * y * c⁻¹) = c * (a * y) * c⁻¹ := by group
    have e2 : c * y * c⁻¹ * (c * a * c⁻¹) = c * (y * a) * c⁻¹ := by group
    rw [e1, e2, h1]
  · intro g hg
    refine ⟨(MulAut.conj c).symm g, ?_, ?_⟩
    · change (MulAut.conj c).symm g ∈ Subgroup.centralizer ({a} : Set G)
      rw [Subgroup.mem_centralizer_iff] at hg
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      have h1 : (MulAut.conj c) a * g = g * (MulAut.conj c) a := hg _ rfl
      rw [MulAut.conj_apply] at h1
      rw [MulAut.conj_symm_apply]
      have e1 : a * (c⁻¹ * g * c) = c⁻¹ * (c * a * c⁻¹ * g) * c := by group
      have e2 : c⁻¹ * g * c * a = c⁻¹ * (g * (c * a * c⁻¹)) * c := by group
      rw [e1, e2, h1]
    · exact MulEquiv.apply_symm_apply _ _

/-- `x` lies in its own centraliser. -/
private lemma mem_centralizer_self (x : Work.Models.SL2 F) :
    x ∈ Subgroup.centralizer ({x} : Set (Work.Models.SL2 F)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  rw [hv]

/-- If `x ≠ 1` and `x ^ (q + 1) = 1` (with `q = |F|`) then `C(x)` is a Singer cycle: cyclic of
order `q + 1`. -/
private lemma centralizer_isSinger {x : Work.Models.SL2 F} (hx1 : x ≠ 1)
    (hx : x ^ (Nat.card F + 1) = 1) :
    IsCyclic ↥(Subgroup.centralizer ({x} : Set (Work.Models.SL2 F))) ∧
      Nat.card ↥(Subgroup.centralizer ({x} : Set (Work.Models.SL2 F))) = Nat.card F + 1 := by
  have hanis : Anisotropic F ((x : Matrix (Fin 2) (Fin 2) F).trace) :=
    (pow_qp1_iff x).mp hx |>.resolve_left hx1
  have hb0 : (x : Matrix (Fin 2) (Fin 2) F).trace ≠ 0 := eps_ne_zero F hanis
  have htr : ((SingerModelCycle.alphaSL ((x : Matrix (Fin 2) (Fin 2) F).trace) :
        Work.Models.SL2 F) : Matrix (Fin 2) (Fin 2) F).trace
      = (x : Matrix (Fin 2) (Fin 2) F).trace := by
    rw [SingerModelCycle.alphaSL_coe, qalphaMat_trace]
  obtain ⟨h, hh⟩ := sl2_conj_of_trace_eq (A := SingerModelCycle.alphaSL _) (B := x) htr
    (by rw [htr]; exact hb0)
  have hC : (Subgroup.centralizer (singleton (SingerModelCycle.alphaSL
        ((x : Matrix (Fin 2) (Fin 2) F).trace)) : Set (Work.Models.SL2 F))).map
        (MulAut.conj h).toMonoidHom
      = Subgroup.centralizer ({x} : Set (Work.Models.SL2 F)) := by
    rw [map_conj_centralizer,
      show (MulAut.conj h) (SingerModelCycle.alphaSL ((x : Matrix (Fin 2) (Fin 2) F).trace)) = x
        from by rw [MulAut.conj_apply]; exact hh]
  have hCeq : Subgroup.centralizer (singleton (SingerModelCycle.alphaSL
        ((x : Matrix (Fin 2) (Fin 2) F).trace)) : Set (Work.Models.SL2 F))
      = singerSubgroup ((x : Matrix (Fin 2) (Fin 2) F).trace) :=
    centralizer_alphaSL hanis
  constructor
  · have hcyc : IsCyclic ↥(Subgroup.centralizer (singleton (SingerModelCycle.alphaSL
          ((x : Matrix (Fin 2) (Fin 2) F).trace)) : Set (Work.Models.SL2 F))) := by
      rw [hCeq]
      exact SingerModelCycle.isCyclic_singerSubgroup hanis
    have hmap : IsCyclic ↥((Subgroup.centralizer (singleton (SingerModelCycle.alphaSL
          ((x : Matrix (Fin 2) (Fin 2) F).trace)) : Set (Work.Models.SL2 F))).map
          (MulAut.conj h).toMonoidHom) :=
      (MulEquiv.isCyclic (Subgroup.equivMapOfInjective (Subgroup.centralizer
        ({SingerModelCycle.alphaSL ((x : Matrix (Fin 2) (Fin 2) F).trace)} :
          Set (Work.Models.SL2 F))) (MulAut.conj h).toMonoidHom
        (MulAut.conj h).injective)).mp hcyc
    rwa [hC] at hmap
  · have hcard : Nat.card ↥(Subgroup.centralizer (singleton (SingerModelCycle.alphaSL
          ((x : Matrix (Fin 2) (Fin 2) F).trace)) : Set (Work.Models.SL2 F)))
        = Nat.card F + 1 := by
      rw [hCeq]
      exact SingerModelCycle.card_singerSubgroup hanis
    rw [← hC, Subgroup.card_map_of_injective (MulAut.conj h).injective]
    exact hcard

/-- A finite subgroup `W` of cardinality `q + 1` containing `x` is exactly `C(x)`, provided
`x ≠ 1` and `x ^ (q + 1) = 1`: `W` is abelian hence contained in `C(x)`, and both have the same
order. -/
private lemma eq_centralizer_of_mem {x : Work.Models.SL2 F} {W : Subgroup (Work.Models.SL2 F)}
    (hx1 : x ≠ 1) (hx : x ^ (Nat.card F + 1) = 1)
    (hWcyc : IsCyclic ↥W) (hWcard : Nat.card ↥W = Nat.card F + 1) (hxW : x ∈ W) :
    W = Subgroup.centralizer ({x} : Set (Work.Models.SL2 F)) := by
  have hle : W ≤ Subgroup.centralizer ({x} : Set (Work.Models.SL2 F)) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    rw [hv]
    haveI : IsMulCommutative ↥W := IsCyclic.isMulCommutative
    have hcomm := congrArg (fun z : ↥W => (z : Work.Models.SL2 F))
      (IsMulCommutative.is_comm.comm (⟨x, hxW⟩ : ↥W) ⟨w, hw⟩)
    simpa using hcomm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [(centralizer_isSinger hx1 hx).2, hWcard]

/-- Every element `≠ 1` of a subgroup of order `q + 1` satisfies `x ^ (q + 1) = 1`. -/
private lemma pow_card_of_mem {x : Work.Models.SL2 F} {W : Subgroup (Work.Models.SL2 F)}
    (hWcard : Nat.card ↥W = Nat.card F + 1) (hxW : x ∈ W) :
    x ^ (Nat.card F + 1) = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (by
    rw [← hWcard]
    exact Subgroup.orderOf_dvd_natCard W hxW)

end Elements

section Counting

/-- `(K.map (conj b)).map (conj a) = K.map (conj (a * b))`. -/
private lemma map_conj_map_conj {G : Type*} [Group G] (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom
      = K.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

/-- `K.map (conj 1) = K`. -/
private lemma map_conj_one {G : Type*} [Group G] (K : Subgroup G) :
    K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [show (MulEquiv.toMonoidHom (MulAut.conj (1 : G))) y = y from by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group] at hyx
    exact hyx ▸ hy
  · intro hx
    exact Subgroup.mem_map.mpr ⟨x, hx, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group⟩

/-- The elements `x ≠ 1` with `x ^ (|F| + 1) = 1` number `(|F| / 2) · |F| (|F| - 1)`: they are
counted by their (anisotropic) trace. -/
private lemma card_SF [DecidableEq F]
    [DecidablePred (fun x : Work.Models.SL2 F => x ≠ 1 ∧ x ^ (Nat.card F + 1) = 1)]
    [DecidablePred (fun b : F => Anisotropic F b)] :
    (Finset.univ.filter (fun x : Work.Models.SL2 F => x ≠ 1 ∧ x ^ (Nat.card F + 1) = 1)).card
      = (Finset.univ.filter (fun b : F => Anisotropic F b)).card
        * (Nat.card F * (Nat.card F - 1)) := by
  classical
  have hiff : ∀ x : Work.Models.SL2 F,
      (x ≠ 1 ∧ x ^ (Nat.card F + 1) = 1) ↔
        Anisotropic F ((x : Matrix (Fin 2) (Fin 2) F).trace) := by
    intro x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ((pow_qp1_iff x).mp hx2).resolve_left hx1
    · intro h
      refine ⟨?_, (pow_qp1_iff x).mpr (Or.inr h)⟩
      intro hx1
      rw [hx1] at h
      refine (eps_ne_zero F h) ?_
      rw [Matrix.trace_fin_two]
      simp [CharTwo.add_self_eq_zero]
  have h1 : (Finset.univ.filter (fun x : Work.Models.SL2 F =>
        x ≠ 1 ∧ x ^ (Nat.card F + 1) = 1))
      = Finset.univ.filter (fun x : Work.Models.SL2 F =>
          Anisotropic F ((x : Matrix (Fin 2) (Fin 2) F).trace)) :=
    Finset.filter_congr (s := Finset.univ) (fun x _ => hiff x)
  rw [h1]
  have hMapsTo : Set.MapsTo
      (fun x : Work.Models.SL2 F => (x : Matrix (Fin 2) (Fin 2) F).trace)
      ↑(Finset.univ.filter (fun x : Work.Models.SL2 F =>
          Anisotropic F ((x : Matrix (Fin 2) (Fin 2) F).trace)))
      ↑(Finset.univ.filter (fun b : F => Anisotropic F b)) := by
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx
  rw [Finset.card_eq_sum_card_fiberwise hMapsTo]
  have hconst : ∀ b ∈ Finset.univ.filter (fun b : F => Anisotropic F b),
      ((Finset.univ.filter (fun x : Work.Models.SL2 F =>
            Anisotropic F ((x : Matrix (Fin 2) (Fin 2) F).trace))).filter
          (fun a : Work.Models.SL2 F =>
            ((a : Matrix (Fin 2) (Fin 2) F).trace = b))).card
        = Nat.card F * (Nat.card F - 1) := by
    intro b hb
    rw [Finset.mem_filter] at hb
    have h2 : ((Finset.univ.filter (fun x : Work.Models.SL2 F =>
            Anisotropic F ((x : Matrix (Fin 2) (Fin 2) F).trace))).filter
          (fun a : Work.Models.SL2 F =>
            ((a : Matrix (Fin 2) (Fin 2) F).trace = b))).card
        = (Finset.univ.filter (fun x : Work.Models.SL2 F =>
            (x : Matrix (Fin 2) (Fin 2) F).trace = b)).card := by
      rw [Finset.filter_filter]
      exact congrArg Finset.card (Finset.filter_congr (s := Finset.univ) (fun x _ =>
        ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hb.2, h⟩⟩))
    rw [h2]
    have h3 : (Finset.univ.filter (fun x : Work.Models.SL2 F =>
          (x : Matrix (Fin 2) (Fin 2) F).trace = b)).card
        = Nat.card {x : Work.Models.SL2 F //
            (x : Matrix (Fin 2) (Fin 2) F).trace = b} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h3]
    exact card_trace_class hb.2
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  simp

/-- The Singer cycles of `SL(2,F)` number `|F| (|F| - 1) / 2`: they partition the non-identity
elements `x` with `x ^ (|F| + 1) = 1` into blocks of size `|F|`. -/
private lemma two_mul_card_T [DecidableEq F]
    [DecidablePred (fun W : Subgroup (Work.Models.SL2 F) =>
      IsCyclic ↥W ∧ Nat.card ↥W = Nat.card F + 1)] :
    2 * (Finset.univ.filter (fun W : Subgroup (Work.Models.SL2 F) =>
        IsCyclic ↥W ∧ Nat.card ↥W = Nat.card F + 1)).card
      = Nat.card F * (Nat.card F - 1) := by
  classical
  have hqpos : 0 < Nat.card F := Nat.card_pos
  -- the disjoint union of the Singer cycles' non-identity elements
  have hUnion : (Finset.univ.filter (fun x : Work.Models.SL2 F =>
        x ≠ 1 ∧ x ^ (Nat.card F + 1) = 1))
      = (Finset.univ.filter (fun W : Subgroup (Work.Models.SL2 F) =>
            IsCyclic ↥W ∧ Nat.card ↥W = Nat.card F + 1)).biUnion
          (fun W => Finset.univ.filter (fun x : Work.Models.SL2 F => x ∈ W ∧ x ≠ 1)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro hx
      refine ⟨Subgroup.centralizer ({x} : Set (Work.Models.SL2 F)),
        centralizer_isSinger hx.1 hx.2, mem_centralizer_self x, hx.1⟩
    · rintro ⟨W, hemp, hxW, hx1⟩
      exact ⟨hx1, pow_card_of_mem hemp.2 hxW⟩
  have hdisj : (↑(Finset.univ.filter (fun W : Subgroup (Work.Models.SL2 F) =>
        IsCyclic ↥W ∧ Nat.card ↥W = Nat.card F + 1)) :
      Set (Subgroup (Work.Models.SL2 F))).PairwiseDisjoint
      (fun W => Finset.univ.filter (fun x : Work.Models.SL2 F => x ∈ W ∧ x ≠ 1)) := by
    intro W hW W' hW' hne
    change Disjoint (Finset.univ.filter (fun x : Work.Models.SL2 F => x ∈ W ∧ x ≠ 1))
      (Finset.univ.filter (fun x : Work.Models.SL2 F => x ∈ W' ∧ x ≠ 1))
    rw [Finset.disjoint_iff_ne]
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hW hW'
    intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have h1 : W = Subgroup.centralizer ({a} : Set (Work.Models.SL2 F)) :=
      eq_centralizer_of_mem ha.2 (pow_card_of_mem hW.2 ha.1) hW.1 hW.2 ha.1
    have h2 : W' = Subgroup.centralizer ({a} : Set (Work.Models.SL2 F)) := by
      rw [← hab] at hb
      exact eq_centralizer_of_mem hb.2 (pow_card_of_mem hW'.2 hb.1) hW'.1 hW'.2 hb.1
    exact hne (h1.trans h2.symm)
  have hcardFiber : ∀ W ∈ Finset.univ.filter (fun W : Subgroup (Work.Models.SL2 F) =>
      IsCyclic ↥W ∧ Nat.card ↥W = Nat.card F + 1),
      (Finset.univ.filter (fun x : Work.Models.SL2 F => x ∈ W ∧ x ≠ 1)).card = Nat.card F := by
    intro W hW
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW
    have h3 : (Finset.univ.filter (fun x : Work.Models.SL2 F => x ∈ W ∧ x ≠ 1))
        = (Finset.univ.filter (fun x : Work.Models.SL2 F => x ∈ W)).erase 1 := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      tauto
    rw [h3, Finset.card_erase_of_mem (by simp : (1 : Work.Models.SL2 F) ∈
      Finset.univ.filter (fun x : Work.Models.SL2 F => x ∈ W))]
    have h4 : (Finset.univ.filter (fun x : Work.Models.SL2 F => x ∈ W)).card
        = Nat.card ↥W := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h4, hW.2]
    omega
  have hstep1 : (Finset.univ.filter (fun W : Subgroup (Work.Models.SL2 F) =>
        IsCyclic ↥W ∧ Nat.card ↥W = Nat.card F + 1)).card * Nat.card F
      = (Finset.univ.filter (fun x : Work.Models.SL2 F =>
          x ≠ 1 ∧ x ^ (Nat.card F + 1) = 1)).card := by
    rw [hUnion, Finset.card_biUnion hdisj,
      Finset.sum_congr rfl hcardFiber, Finset.sum_const, nsmul_eq_mul]
    simp
  have hkey : (Finset.univ.filter (fun W : Subgroup (Work.Models.SL2 F) =>
        IsCyclic ↥W ∧ Nat.card ↥W = Nat.card F + 1)).card * Nat.card F
      = (Finset.univ.filter (fun b : F => Anisotropic F b)).card
        * (Nat.card F * (Nat.card F - 1)) := hstep1.trans card_SF
  have hTFc : (Finset.univ.filter (fun W : Subgroup (Work.Models.SL2 F) =>
        IsCyclic ↥W ∧ Nat.card ↥W = Nat.card F + 1)).card
      = (Finset.univ.filter (fun b : F => Anisotropic F b)).card * (Nat.card F - 1) := by
    refine Nat.mul_right_cancel hqpos ?_
    rw [hkey]
    ring
  rw [hTFc]
  have h2A : 2 * (Finset.univ.filter (fun b : F => Anisotropic F b)).card = Nat.card F :=
    two_mul_card_anisotropic
  rw [show 2 * ((Finset.univ.filter (fun b : F => Anisotropic F b)).card * (Nat.card F - 1))
      = 2 * (Finset.univ.filter (fun b : F => Anisotropic F b)).card * (Nat.card F - 1)
      from by ring, h2A]

/-- `Nat.card = Fintype.card`, with the type as an explicit argument. -/
private lemma natCard_eq_fintypeCard (α : Type*) [Fintype α] :
    Nat.card α = Fintype.card α :=
  Nat.card_eq_fintype_card

/-- `|SL(2,F)| = q (q - 1) (q + 1)`, `q = |F|`. -/
private lemma natCard_sl2 {F : Type*} [Field F] [Fintype F] :
    Nat.card (Work.Models.SL2 F) = Nat.card F * (Nat.card F - 1) * (Nat.card F + 1) := by
  rw [Commons.LinearAlgebra.Matrix.card_SL2_field]
  rw [(natCard_eq_fintypeCard F).symm]
  have h2 : (Nat.card F) ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    have h3 : (Nat.card F) ^ 2 - (1 : ℕ) ^ 2 = (Nat.card F - 1) * (Nat.card F + 1) := by
      rw [Nat.sq_sub_sq]
      ring
    simpa using h3
  rw [h2]
  ring

end Counting


/-! ## The conjugacy class of a Singer cycle -/

/-- **Any two cyclic subgroups of `SL(2,F)` of order `|F| + 1` are conjugate.**  For `F` a
finite field of characteristic two with `4 ≤ |F|`, the cyclic subgroups of order `|F| + 1` are
the Singer cycles, and they form a single conjugacy class. -/
theorem sl2_cyclic_conj_card_add_one {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 4 ≤ Nat.card F)
    {W₁ W₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (h₁ : IsCyclic ↥W₁) (hc₁ : Nat.card ↥W₁ = Nat.card F + 1)
    (h₂ : IsCyclic ↥W₂) (hc₂ : Nat.card ↥W₂ = Nat.card F + 1) :
    ∃ h : Matrix.SpecialLinearGroup (Fin 2) F,
      W₁.map (MulAut.conj h).toMonoidHom = W₂ := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨ε₀, hε₀⟩ := SingerModelCycle.exists_anisotropic F
  let T₀ : Subgroup (Work.Models.SL2 F) := singerSubgroup ε₀
  have hT₀cyc : IsCyclic ↥T₀ := SingerModelCycle.isCyclic_singerSubgroup hε₀
  have hT₀card : Nat.card ↥T₀ = Nat.card F + 1 := SingerModelCycle.card_singerSubgroup hε₀
  have hN₀ : Nat.card ↥(Subgroup.normalizer (T₀ : Set (Work.Models.SL2 F)))
      = 2 * (Nat.card F + 1) := card_normalizer_singer hε₀
  -- every Singer cycle is conjugate to `T₀`
  have horb : ∀ W : Subgroup (Work.Models.SL2 F), IsCyclic ↥W →
      Nat.card ↥W = Nat.card F + 1 →
      ∃ g : Work.Models.SL2 F, W = T₀.map (MulAut.conj g).toMonoidHom := by
    intro W hWcyc hWcard
    have hfib_iff : ∀ g g₀ : Work.Models.SL2 F,
        (T₀.map (MulAut.conj g).toMonoidHom = T₀.map (MulAut.conj g₀).toMonoidHom) ↔
          g₀⁻¹ * g ∈ Subgroup.normalizer (T₀ : Set (Work.Models.SL2 F)) := by
      intro g g₀
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      constructor
      · intro h
        have h1 : (T₀.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g₀⁻¹).toMonoidHom
            = (T₀.map (MulAut.conj g₀).toMonoidHom).map (MulAut.conj g₀⁻¹).toMonoidHom := by
          rw [h]
        rw [map_conj_map_conj T₀ g₀⁻¹ g, map_conj_map_conj T₀ g₀⁻¹ g₀] at h1
        rw [show g₀⁻¹ * g₀ = (1 : Work.Models.SL2 F) from inv_mul_cancel g₀] at h1
        rwa [map_conj_one] at h1
      · intro h
        calc T₀.map (MulAut.conj g).toMonoidHom
            = T₀.map (MulAut.conj (g₀ * (g₀⁻¹ * g))).toMonoidHom := by
              rw [show g₀ * (g₀⁻¹ * g) = g by group]
          _ = (T₀.map (MulAut.conj (g₀⁻¹ * g)).toMonoidHom).map
                (MulAut.conj g₀).toMonoidHom := (map_conj_map_conj T₀ g₀ (g₀⁻¹ * g)).symm
          _ = T₀.map (MulAut.conj g₀).toMonoidHom :=
              congrArg (fun X : Subgroup (Work.Models.SL2 F) =>
                X.map (MulAut.conj g₀).toMonoidHom) h
    have hfib : ∀ g₀ : Work.Models.SL2 F,
        (Finset.univ.filter (fun g : Work.Models.SL2 F =>
          T₀.map (MulAut.conj g).toMonoidHom
            = T₀.map (MulAut.conj g₀).toMonoidHom)).card = 2 * (Nat.card F + 1) := by
      intro g₀
      have hset : (Finset.univ.filter (fun g : Work.Models.SL2 F =>
            T₀.map (MulAut.conj g).toMonoidHom
              = T₀.map (MulAut.conj g₀).toMonoidHom))
          = (Finset.univ.filter (fun n : Work.Models.SL2 F =>
              n ∈ Subgroup.normalizer (T₀ : Set (Work.Models.SL2 F)))).image
              (fun n => g₀ * n) := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hg
          exact ⟨g₀⁻¹ * g, (hfib_iff g g₀).mp hg, by group⟩
        · rintro ⟨n, hn, rfl⟩
          exact (hfib_iff (g₀ * n) g₀).mpr (by
            rwa [show g₀⁻¹ * (g₀ * n) = n by group])
      rw [hset, Finset.card_image_of_injective _ (fun a b hab => by
        simpa using congrArg (fun z : Work.Models.SL2 F => g₀⁻¹ * z) hab)]
      have h4 : (Finset.univ.filter (fun n : Work.Models.SL2 F =>
            n ∈ Subgroup.normalizer (T₀ : Set (Work.Models.SL2 F)))).card
          = Nat.card ↥(Subgroup.normalizer (T₀ : Set (Work.Models.SL2 F))) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [h4, hN₀]
    have hOrbcard : (Finset.univ.image (fun g : Work.Models.SL2 F =>
          T₀.map (MulAut.conj g).toMonoidHom)).card * 2 = Nat.card F * (Nat.card F - 1) := by
      have hMapsTo : Set.MapsTo (fun g : Work.Models.SL2 F =>
            T₀.map (MulAut.conj g).toMonoidHom)
          ↑(Finset.univ : Finset (Work.Models.SL2 F))
          ↑(Finset.univ.image (fun g : Work.Models.SL2 F =>
            T₀.map (MulAut.conj g).toMonoidHom)) := by
        intro g _
        exact Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩
      have h1 : (Finset.univ : Finset (Work.Models.SL2 F)).card
          = (Finset.univ.image (fun g : Work.Models.SL2 F =>
              T₀.map (MulAut.conj g).toMonoidHom)).card * (2 * (Nat.card F + 1)) := by
        rw [Finset.card_eq_sum_card_fiberwise hMapsTo]
        have hfib' : ∀ W' ∈ Finset.univ.image (fun g : Work.Models.SL2 F =>
              T₀.map (MulAut.conj g).toMonoidHom),
            (Finset.univ.filter (fun g : Work.Models.SL2 F =>
              T₀.map (MulAut.conj g).toMonoidHom = W')).card = 2 * (Nat.card F + 1) := by
          intro W' hW'
          obtain ⟨g₀, -, hg₀⟩ := Finset.mem_image.mp hW'
          rw [← hg₀]
          exact hfib g₀
        rw [Finset.sum_congr rfl hfib', Finset.sum_const, nsmul_eq_mul]
        simp
      have h2 : (Finset.univ : Finset (Work.Models.SL2 F)).card
          = Nat.card (Work.Models.SL2 F) := by
        rw [Finset.card_univ, natCard_eq_fintypeCard]
      have h1' : (Finset.univ.image (fun g : Work.Models.SL2 F =>
            T₀.map (MulAut.conj g).toMonoidHom)).card * (2 * (Nat.card F + 1))
          = Nat.card (Work.Models.SL2 F) := h1.symm.trans h2
      rw [natCard_sl2] at h1'
      have h3 : ((Finset.univ.image (fun g : Work.Models.SL2 F =>
            T₀.map (MulAut.conj g).toMonoidHom)).card * 2) * (Nat.card F + 1)
          = (Nat.card F * (Nat.card F - 1)) * (Nat.card F + 1) := by
        rw [← h1']
        ring
      exact Nat.mul_right_cancel (by omega : 0 < Nat.card F + 1) h3
    have hsub : (Finset.univ.image (fun g : Work.Models.SL2 F =>
          T₀.map (MulAut.conj g).toMonoidHom)) ⊆
        Finset.univ.filter (fun W' : Subgroup (Work.Models.SL2 F) =>
          IsCyclic ↥W' ∧ Nat.card ↥W' = Nat.card F + 1) := by
      intro W' hW'
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hW'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(MulEquiv.isCyclic (Subgroup.equivMapOfInjective T₀
            (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)).mp hT₀cyc,
        (Subgroup.card_map_of_injective (MulAut.conj g).injective).trans hT₀card⟩
    have hcard_eq : (Finset.univ.image (fun g : Work.Models.SL2 F =>
          T₀.map (MulAut.conj g).toMonoidHom)).card
        = (Finset.univ.filter (fun W' : Subgroup (Work.Models.SL2 F) =>
            IsCyclic ↥W' ∧ Nat.card ↥W' = Nat.card F + 1)).card := by
      apply Nat.mul_left_cancel (show 0 < 2 by norm_num)
      rw [two_mul_card_T, ← hOrbcard]
      ring
    have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_eq.symm)
    have hW' : W ∈ Finset.univ.image (fun g : Work.Models.SL2 F =>
        T₀.map (MulAut.conj g).toMonoidHom) := by
      rw [heq]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hWcyc, hWcard⟩
    obtain ⟨g, -, hg⟩ := Finset.mem_image.mp hW'
    exact ⟨g, hg.symm⟩
  obtain ⟨g₁, hg₁⟩ := horb W₁ h₁ hc₁
  obtain ⟨g₂, hg₂⟩ := horb W₂ h₂ hc₂
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  rw [hg₁, hg₂, map_conj_map_conj T₀ (g₂ * g₁⁻¹) g₁,
    show (g₂ * g₁⁻¹) * g₁ = g₂ by group]

end Work.ZassenhausSuzuki
