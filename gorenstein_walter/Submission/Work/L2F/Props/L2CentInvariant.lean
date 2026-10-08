import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.PSL.centralizer_psl_dihedral
import Submission.Work.L2F.Conic.circle_card
import Submission.Work.L2F.Involution.lift_sq_neg_one
import Submission.Work.L2F.PSL.trace_lift_ne_zero_and_sq_ne_four
import Submission.Work.L2F.Mat2.centralizer_sl2_structure
import Submission.Work.L2F.PSL.card_normalizer_pSubgroup_dvd

namespace Work.L2F.Props

set_option maxHeartbeats 1000000

open scoped MatrixGroups
open Matrix
open Subgroup (centralizer normalizer)

/-! ## Elementary lemmas -/

/-- For odd `q ≥ 5` neither `q - 1` nor `q + 1` divides `q * (q - 1) / 2`. -/
theorem not_dvd_of_odd {q : ℕ} (hodd : Odd q) (h5 : 5 ≤ q) :
    ¬ (q - 1 ∣ q * (q - 1) / 2) ∧ ¬ (q + 1 ∣ q * (q - 1) / 2) := by
  have hq1 : 1 ≤ q := by omega
  have heven : 2 ∣ q - 1 := by
    obtain ⟨m, hm⟩ := hodd
    exact ⟨m, by omega⟩
  have hprod : q * (q - 1) / 2 = q * ((q - 1) / 2) := by
    have h : q - 1 = ((q - 1) / 2) * 2 := (Nat.div_mul_cancel heven).symm
    conv_lhs => rw [h]
    rw [← mul_assoc, Nat.mul_div_left _ (by norm_num : 0 < 2)]
  have hcop1 : Nat.Coprime (q - 1) q := by
    have h := (Nat.coprime_self_sub_right (m := 1) hq1).mpr (Nat.coprime_one_right q)
    exact h.symm
  have hcop2 : Nat.Coprime (q + 1) q := by
    have h := (Nat.coprime_self_add_right (m := q) (n := 1)).mpr (Nat.coprime_one_right q)
    exact h.symm
  constructor
  · intro hdiv
    rw [hprod] at hdiv
    have hdiv' : q - 1 ∣ (q - 1) / 2 := hcop1.dvd_of_dvd_mul_left hdiv
    rcases Nat.eq_zero_or_pos ((q - 1) / 2) with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hdiv'
      omega
  · intro hdiv
    rw [hprod] at hdiv
    have hdiv' : q + 1 ∣ (q - 1) / 2 := hcop2.dvd_of_dvd_mul_left hdiv
    rcases Nat.eq_zero_or_pos ((q - 1) / 2) with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hdiv'
      omega

/-- The normalizer of `P` is contained in the normalizer of the centralizer of `P`. -/
theorem normalizer_le_normalizer_centralizer {G : Type*} [Group G] (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (P : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx p hp
    have hp' : g⁻¹ * p * g ∈ P := (hg (g⁻¹ * p * g)).mpr (by
      have : g * (g⁻¹ * p * g) * g⁻¹ = p := by group
      rw [this]; exact hp)
    have h1 : (g⁻¹ * p * g) * x = x * (g⁻¹ * p * g) := hx _ hp'
    calc p * (g * x * g⁻¹) = g * ((g⁻¹ * p * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * p * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * p := by group
  · intro hx p hp
    have hp' : g * p * g⁻¹ ∈ P := (hg p).mp hp
    have h1 : (g * p * g⁻¹) * (g * x * g⁻¹) = (g * x * g⁻¹) * (g * p * g⁻¹) := hx _ hp'
    have h2 : g * (p * x) * g⁻¹ = g * (x * p) * g⁻¹ := by
      rwa [show (g * p * g⁻¹) * (g * x * g⁻¹) = g * (p * x) * g⁻¹ by group,
        show (g * x * g⁻¹) * (g * p * g⁻¹) = g * (x * p) * g⁻¹ by group] at h1
    calc p * x = g⁻¹ * (g * (p * x) * g⁻¹) * g := by group
      _ = g⁻¹ * (g * (x * p) * g⁻¹) * g := by rw [h2]
      _ = x * p := by group

/-- `2 ≠ 0` in `GF(p,k)` for an odd prime `p`. -/
private theorem two_ne_zero_gf {p k : ℕ} [Fact p.Prime] (hp : Odd p) :
    (2 : GaloisField p k) ≠ 0 := by
  intro h
  have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p k) p 2).mp h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
  have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp2 : p = 2 := le_antisymm hle hge
  rw [hp2] at hp
  exact (by decide : ¬ Odd 2) hp

/-- `-1 ≠ 1` in `SL(2,F)` for `(2 : F) ≠ 0`. -/
private theorem negOne_ne_one (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    Work.L2F.negOne F ≠ (1 : Matrix.SpecialLinearGroup (Fin 2) F) := by
  intro h
  have hmat : (((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F)) :
      Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [h]; rfl
  have h00 : (-1 : F) = 1 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hmat
    simpa [Work.L2F.negOne] using this
  have h' : (1 : F) + 1 = 0 := by
    have : (1 : F) - (-1) = 0 := sub_eq_zero.mpr h00.symm
    simpa using this
  rw [one_add_one_eq_two] at h'
  exact h2 h'

/-- **Structure of the centralizer of an odd order element of `PSL(2,GF(p,k))`**: it is cyclic of
order `(q ∓ 1)/2` and its normalizer has order at most twice that.

Proof: lift `y` to `x ∈ SL(2,GF(p,k))`.  Since `y` has odd order coprime to `p`, the element `x`
is semisimple with `tr x ≠ 0` and `(tr x)^2 ≠ 4`, so `C_{SL}(x)` is cyclic of order `q ∓ 1` with
`|N_{SL}(C_{SL}(x))| ≤ 2 |C_{SL}(x)|` (delegated `centralizer_sl2_structure`); and `tr x ≠ 0`
rules out `x ~ -x`, which gives `C_{PSL}(y) = π(C_{SL}(x))`: its order is half, it is cyclic, and
`N_{PSL}(C_{PSL}(y)) ≤ π(N_{SL}(C_{SL}(x)))`, again of half the order. -/
private theorem torus_structure {p k : ℕ} [Fact p.Prime] (hp : Odd p) (h5 : 5 ≤ p ^ k)
    (y : PSL(2, GaloisField p k)) (hy1 : y ≠ 1) (hodd : Odd (orderOf y)) (hcop : ¬ p ∣ orderOf y) :
    IsCyclic (Subgroup.centralizer ({y} : Set (PSL(2, GaloisField p k)))) ∧
    (2 * Nat.card (Subgroup.centralizer ({y} : Set (PSL(2, GaloisField p k)))) = p ^ k - 1 ∨
     2 * Nat.card (Subgroup.centralizer ({y} : Set (PSL(2, GaloisField p k)))) = p ^ k + 1) ∧
    Nat.card (Subgroup.normalizer (Subgroup.centralizer ({y} : Set (PSL(2, GaloisField p k))) : Set (PSL(2, GaloisField p k))))
      ≤ 2 * Nat.card (Subgroup.centralizer ({y} : Set (PSL(2, GaloisField p k)))) := by
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have h2 : (2 : GaloisField p k) ≠ 0 := two_ne_zero_gf hp
  obtain ⟨x, hx⟩ : ∃ x : SL(2, GaloisField p k), Work.PSL2.pslMap (GaloisField p k) x = y :=
    QuotientGroup.mk'_surjective (Subgroup.center (SL(2, GaloisField p k))) y
  obtain ⟨htr0, htr2⟩ :=
    Work.L2F.PSL.trace_lift_ne_zero_and_sq_ne_four hp y hy1 hodd hcop x hx
  obtain ⟨hcyc, hcard, hnormbd⟩ :=
    Work.L2F.Mat2.centralizer_sl2_structure (GaloisField p k) h2 x htr2
  set C : Subgroup (SL(2, GaloisField p k)) :=
    Subgroup.centralizer ({x} : Set (SL(2, GaloisField p k))) with hCdef
  set T : Subgroup (PSL(2, GaloisField p k)) :=
    Subgroup.centralizer ({y} : Set (PSL(2, GaloisField p k))) with hTdef
  set N : Subgroup (SL(2, GaloisField p k)) :=
    Subgroup.normalizer (C : Set (SL(2, GaloisField p k))) with hNdef
  have hmemneg : Work.L2F.negOne (GaloisField p k) ∈ C := by
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    exact Work.L2F.Involution.negOne_mul_comm (GaloisField p k) x
  have hmemnegN : Work.L2F.negOne (GaloisField p k) ∈ N := by
    rw [hNdef]; exact Subgroup.le_normalizer hmemneg
  -- ## `T` is the image of `C`
  have hT_eq : T = C.map (Work.PSL2.pslMap (GaloisField p k)) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨u, hu0⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SL(2, GaloisField p k))) g
      have hu' : Work.PSL2.pslMap (GaloisField p k) u = g := hu0
      have hgy : g * y = y * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      have hker : Work.PSL2.pslMap (GaloisField p k) (u * x * u⁻¹ * x⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hu', hx]
        rw [hgy]; group
      rcases (Work.L2F.Mat2.pslMap_eq_one_iff (GaloisField p k) h2
        (u * x * u⁻¹ * x⁻¹)).mp hker with h1 | h1
      · refine Subgroup.mem_map.mpr ⟨u, ?_, hu'⟩
        change u ∈ Subgroup.centralizer ({x} : Set (SL(2, GaloisField p k)))
        have h1' : (u * x) * (x * u)⁻¹ = 1 := by
          have h : (u * x) * (x * u)⁻¹ = u * x * u⁻¹ * x⁻¹ := by group
          rw [h, h1]
        exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_one.mp h1')
      · exfalso
        have hux : u * x * u⁻¹ = Work.L2F.negOne (GaloisField p k) * x := by
          rw [← h1]; group
        have hcoe : (((u * x * u⁻¹ : SL(2, GaloisField p k))) :
            Matrix (Fin 2) (Fin 2) (GaloisField p k))
            = (↑u : Matrix (Fin 2) (Fin 2) (GaloisField p k))
              * (↑x : Matrix (Fin 2) (Fin 2) (GaloisField p k))
              * (↑u : Matrix (Fin 2) (Fin 2) (GaloisField p k)).adjugate := by
          rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
            Matrix.SpecialLinearGroup.coe_inv]
        have hmat : (((u * x * u⁻¹ : SL(2, GaloisField p k))) :
            Matrix (Fin 2) (Fin 2) (GaloisField p k))
            = -(((x : SL(2, GaloisField p k)) : Matrix (Fin 2) (Fin 2) (GaloisField p k))) := by
          have hc := congrArg (fun t : SL(2, GaloisField p k) =>
            ((t : SL(2, GaloisField p k)) : Matrix (Fin 2) (Fin 2) (GaloisField p k))) hux
          rw [hcoe, Matrix.SpecialLinearGroup.coe_mul] at hc
          rw [show (((Work.L2F.negOne (GaloisField p k) : SL(2, GaloisField p k))) :
              Matrix (Fin 2) (Fin 2) (GaloisField p k)) = -1 from rfl, neg_mul, one_mul] at hc
          exact hc
        have htr : ((↑u : Matrix (Fin 2) (Fin 2) (GaloisField p k))
              * (↑x : Matrix (Fin 2) (Fin 2) (GaloisField p k))
              * (↑u : Matrix (Fin 2) (Fin 2) (GaloisField p k)).adjugate).trace
            = (((x : SL(2, GaloisField p k))) : Matrix (Fin 2) (Fin 2) (GaloisField p k)).trace := by
          rw [Matrix.trace_mul_cycle, Matrix.adjugate_mul,
            Matrix.SpecialLinearGroup.det_coe (A := u), Matrix.smul_mul, Matrix.one_mul,
            one_smul]
        have hzero : (((x : SL(2, GaloisField p k))) :
            Matrix (Fin 2) (Fin 2) (GaloisField p k)).trace = 0 := by
          have hneg : -(((x : SL(2, GaloisField p k))) :
              Matrix (Fin 2) (Fin 2) (GaloisField p k)).trace
              = (((x : SL(2, GaloisField p k))) : Matrix (Fin 2) (Fin 2) (GaloisField p k)).trace := by
            rw [← hcoe, hmat, Matrix.trace_neg] at htr
            exact htr
          have hsum : (((x : SL(2, GaloisField p k))) :
              Matrix (Fin 2) (Fin 2) (GaloisField p k)).trace
              + (((x : SL(2, GaloisField p k))) : Matrix (Fin 2) (Fin 2) (GaloisField p k)).trace = 0 :=
            add_eq_zero_iff_eq_neg.mpr hneg.symm
          have h2t : (2 : GaloisField p k) * (((x : SL(2, GaloisField p k))) :
              Matrix (Fin 2) (Fin 2) (GaloisField p k)).trace = 0 := by
            rw [two_mul]; exact hsum
          exact (mul_eq_zero.mp h2t).resolve_left h2
        exact htr0 hzero
    · rintro g ⟨u, hu, rfl⟩
      have hux : u * x = x * u := by
        have h : u ∈ Subgroup.centralizer ({x} : Set (SL(2, GaloisField p k))) := hu
        exact Subgroup.mem_centralizer_singleton_iff.mp h
      change Work.PSL2.pslMap (GaloisField p k) u ∈
        Subgroup.centralizer ({y} : Set (PSL(2, GaloisField p k)))
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← hx]
      calc Work.PSL2.pslMap (GaloisField p k) u * Work.PSL2.pslMap (GaloisField p k) x
          = Work.PSL2.pslMap (GaloisField p k) (u * x) := (map_mul _ u x).symm
        _ = Work.PSL2.pslMap (GaloisField p k) (x * u) := by rw [hux]
        _ = Work.PSL2.pslMap (GaloisField p k) x * Work.PSL2.pslMap (GaloisField p k) u :=
              map_mul _ x u
  -- ## `|C| = 2 * |T|`
  have hcardCT : Nat.card ↥C = 2 * Nat.card ↥T := by
    let g : ↥C := ⟨Work.L2F.negOne (GaloisField p k), hmemneg⟩
    have hker : ((Work.PSL2.pslMap (GaloisField p k)).comp C.subtype).ker
        = Subgroup.zpowers g := by
      apply le_antisymm
      · intro z hz
        rw [MonoidHom.mem_ker] at hz
        change Work.PSL2.pslMap (GaloisField p k) (z : SL(2, GaloisField p k)) = 1 at hz
        rcases (Work.L2F.Mat2.pslMap_eq_one_iff (GaloisField p k) h2
          (z : SL(2, GaloisField p k))).mp hz with h | h
        · rw [show z = 1 from Subtype.ext h]; exact Subgroup.one_mem _
        · rw [show z = g from Subtype.ext h]; exact Subgroup.mem_zpowers g
      · rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
        change Work.PSL2.pslMap (GaloisField p k)
          ((g : ↥C) : SL(2, GaloisField p k)) = 1
        exact (Work.L2F.Mat2.pslMap_eq_one_iff (GaloisField p k) h2 _).mpr (Or.inr rfl)
    have hcard2 : Nat.card ↥(((Work.PSL2.pslMap (GaloisField p k)).comp C.subtype).ker) = 2 := by
      rw [hker, Nat.card_zpowers]
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two]
        apply Subtype.ext
        show Work.L2F.negOne (GaloisField p k) * Work.L2F.negOne (GaloisField p k) = 1
        exact Work.L2F.Involution.negOne_mul_self (GaloisField p k)
      · intro h
        exact negOne_ne_one (GaloisField p k) h2
          (congrArg (fun z : ↥C => (z : SL(2, GaloisField p k))) h)
    have hrange : ((Work.PSL2.pslMap (GaloisField p k)).comp C.subtype).range
        = C.map (Work.PSL2.pslMap (GaloisField p k)) := by
      change ((Work.PSL2.pslMap (GaloisField p k)).comp C.subtype).range
        = Subgroup.map (Work.PSL2.pslMap (GaloisField p k)) C
      rw [← MonoidHom.map_range (Work.PSL2.pslMap (GaloisField p k)) C.subtype,
        Subgroup.range_subtype]
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((Work.PSL2.pslMap (GaloisField p k)).comp C.subtype).ker
    have heq : Nat.card (↥C ⧸ ((Work.PSL2.pslMap (GaloisField p k)).comp C.subtype).ker)
        = Nat.card ((Work.PSL2.pslMap (GaloisField p k)).comp C.subtype).range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
    rw [heq, hcard2, hrange, ← hT_eq] at hq
    rw [mul_comm] at hq
    exact hq
  -- ## `T` is cyclic
  have hcyclT : IsCyclic ↥T := by
    haveI : IsCyclic ↥C := hcyc
    have h1 : IsCyclic ↥(C.map (Work.PSL2.pslMap (GaloisField p k))) := by
      let ψ : ↥C →* ↥(C.map (Work.PSL2.pslMap (GaloisField p k))) :=
        { toFun := fun z => ⟨Work.PSL2.pslMap (GaloisField p k) z,
            Subgroup.mem_map.mpr ⟨z, z.2, rfl⟩⟩
          map_one' := by
            apply Subtype.ext
            exact map_one (Work.PSL2.pslMap (GaloisField p k))
          map_mul' := by
            intro a b
            apply Subtype.ext
            exact map_mul (Work.PSL2.pslMap (GaloisField p k))
              (a : SL(2, GaloisField p k)) (b : SL(2, GaloisField p k)) }
      exact isCyclic_of_surjective ψ (fun c => by
        obtain ⟨z, hz, hzc⟩ := Subgroup.mem_map.mp c.2
        exact ⟨⟨z, hz⟩, Subtype.ext hzc⟩)
    rw [hT_eq]; exact h1
  -- ## the order of `T`
  have hcardT : 2 * Nat.card ↥T = p ^ k - 1 ∨ 2 * Nat.card ↥T = p ^ k + 1 := by
    have hcardF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k (by
      rintro rfl
      simp at h5)
    rcases hcard with h | h
    · left; rw [← hcardCT, h, hcardF]
    · right; rw [← hcardCT, h, hcardF]
  -- ## the normalizer bound
  have hnormT : Nat.card
      (Subgroup.normalizer (Subgroup.centralizer ({y} : Set (PSL(2, GaloisField p k))) :
        Set (PSL(2, GaloisField p k))))
      ≤ 2 * Nat.card (Subgroup.centralizer ({y} : Set (PSL(2, GaloisField p k)))) := by
    have hkerN : ((Work.PSL2.pslMap (GaloisField p k)).comp N.subtype).ker
        = Subgroup.zpowers (⟨Work.L2F.negOne (GaloisField p k), hmemnegN⟩ : ↥N) := by
      apply le_antisymm
      · intro z hz
        rw [MonoidHom.mem_ker] at hz
        change Work.PSL2.pslMap (GaloisField p k) (z : SL(2, GaloisField p k)) = 1 at hz
        rcases (Work.L2F.Mat2.pslMap_eq_one_iff (GaloisField p k) h2
          (z : SL(2, GaloisField p k))).mp hz with h | h
        · rw [show z = 1 from Subtype.ext h]; exact Subgroup.one_mem _
        · rw [show z = ⟨Work.L2F.negOne (GaloisField p k), hmemnegN⟩ from Subtype.ext h]
          exact Subgroup.mem_zpowers _
      · rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
        change Work.PSL2.pslMap (GaloisField p k)
          (((⟨Work.L2F.negOne (GaloisField p k), hmemnegN⟩ : ↥N)) :
            SL(2, GaloisField p k)) = 1
        exact (Work.L2F.Mat2.pslMap_eq_one_iff (GaloisField p k) h2 _).mpr (Or.inr rfl)
    have hcard2N : Nat.card ↥(((Work.PSL2.pslMap (GaloisField p k)).comp N.subtype).ker) = 2 := by
      rw [hkerN, Nat.card_zpowers]
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two]
        apply Subtype.ext
        show Work.L2F.negOne (GaloisField p k) * Work.L2F.negOne (GaloisField p k) = 1
        exact Work.L2F.Involution.negOne_mul_self (GaloisField p k)
      · intro h
        exact negOne_ne_one (GaloisField p k) h2
          (congrArg (fun z : ↥N => (z : SL(2, GaloisField p k))) h)
    have hrangeN : ((Work.PSL2.pslMap (GaloisField p k)).comp N.subtype).range
        = N.map (Work.PSL2.pslMap (GaloisField p k)) := by
      change ((Work.PSL2.pslMap (GaloisField p k)).comp N.subtype).range
        = Subgroup.map (Work.PSL2.pslMap (GaloisField p k)) N
      rw [← MonoidHom.map_range (Work.PSL2.pslMap (GaloisField p k)) N.subtype,
        Subgroup.range_subtype]
    have hcardN : Nat.card ↥N = 2 * Nat.card ↥(N.map (Work.PSL2.pslMap (GaloisField p k))) := by
      have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup
        ((Work.PSL2.pslMap (GaloisField p k)).comp N.subtype).ker
      have heq : Nat.card (↥N ⧸ ((Work.PSL2.pslMap (GaloisField p k)).comp N.subtype).ker)
          = Nat.card ((Work.PSL2.pslMap (GaloisField p k)).comp N.subtype).range :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
      rw [heq, hcard2N, hrangeN] at hq
      rw [mul_comm] at hq
      exact hq
    have hcomap : Subgroup.comap (Work.PSL2.pslMap (GaloisField p k)) T = C := by
      rw [hT_eq, Subgroup.comap_map_eq, sup_eq_left]
      intro z hz
      rw [MonoidHom.mem_ker] at hz
      rcases (Work.L2F.Mat2.pslMap_eq_one_iff (GaloisField p k) h2 z).mp hz with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [show z = Work.L2F.negOne (GaloisField p k) from h]; exact hmemneg
    have hle : Subgroup.normalizer (T : Set (PSL(2, GaloisField p k)))
        ≤ N.map (Work.PSL2.pslMap (GaloisField p k)) := by
      intro g hg
      obtain ⟨u, hu0⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SL(2, GaloisField p k))) g
      have hu : Work.PSL2.pslMap (GaloisField p k) u = g := hu0
      rw [← hu] at hg
      refine Subgroup.mem_map.mpr ⟨u, ?_, hu⟩
      rw [hNdef, Subgroup.mem_normalizer_iff]
      intro w
      have h1 : w ∈ C ↔ Work.PSL2.pslMap (GaloisField p k) w ∈ T := by
        rw [← hcomap]; exact Subgroup.mem_comap
      have h2 : Work.PSL2.pslMap (GaloisField p k) (u * w * u⁻¹) ∈ T ↔ u * w * u⁻¹ ∈ C := by
        rw [← hcomap]; exact Subgroup.mem_comap.symm
      have h3 : Work.PSL2.pslMap (GaloisField p k) w ∈ T ↔
          Work.PSL2.pslMap (GaloisField p k) (u * w * u⁻¹) ∈ T := by
        have h4 : Work.PSL2.pslMap (GaloisField p k) u * Work.PSL2.pslMap (GaloisField p k) w
            * (Work.PSL2.pslMap (GaloisField p k) u)⁻¹
            = Work.PSL2.pslMap (GaloisField p k) (u * w * u⁻¹) := by
          rw [map_mul, map_mul, map_inv]
        have h5 := (Subgroup.mem_normalizer_iff.mp hg) (Work.PSL2.pslMap (GaloisField p k) w)
        rw [h4] at h5
        exact h5
      exact h1.trans (h3.trans h2)
    have hb : Nat.card (Subgroup.normalizer (T : Set (PSL(2, GaloisField p k))))
        ≤ Nat.card ↥(N.map (Work.PSL2.pslMap (GaloisField p k))) := by
      haveI : Nonempty ↥(N.map (Work.PSL2.pslMap (GaloisField p k))) :=
        ⟨1, Subgroup.one_mem _⟩
      haveI : Finite ↥(N.map (Work.PSL2.pslMap (GaloisField p k))) :=
        Finite.of_injective (Subgroup.subtype _) Subtype.coe_injective
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hle)
    have hgoal : Nat.card (Subgroup.normalizer (T : Set (PSL(2, GaloisField p k))))
        ≤ 2 * Nat.card ↥T := by
      omega
    rw [hTdef] at hgoal
    exact hgoal
  exact ⟨hcyclT, hcardT, hnormT⟩
/-- The centralizer in `PSL(2,GF(p,k))` of an involution has order `q - 1` or `q + 1`. -/
theorem card_centralizer_involution {p k : ℕ} [Fact p.Prime] (hp : Odd p) (h5 : 5 ≤ p ^ k)
    (t : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set (Matrix.ProjectiveSpecialLinearGroup
      (Fin 2) (GaloisField p k)))) = p ^ k - 1 ∨
    Nat.card (Subgroup.centralizer ({t} : Set (Matrix.ProjectiveSpecialLinearGroup
      (Fin 2) (GaloisField p k)))) = p ^ k + 1 := by
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have h2 : (2 : GaloisField p k) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p k) p 2).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hp2 : p = 2 := le_antisymm hle hge
    rw [hp2] at hp
    exact (by decide : ¬ Odd 2) hp
  obtain ⟨x, hx_eq, hx_sq⟩ := Work.L2F.Involution.lift_sq_neg_one (GaloisField p k) h2 t ht
  obtain ⟨n, hn, ⟨e0⟩⟩ := @Work.L2F.PSL.centralizer_psl_dihedral (GaloisField p k) _
    (Fintype.ofFinite _) h2 x hx_sq
  have hcardC : Nat.card (Subgroup.centralizer ({t} :
      Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)))) = 2 * n := by
    have hset : ({t} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) =
        {Work.PSL2.pslMap (GaloisField p k) x} := by rw [hx_eq]
    rw [hset, Nat.card_congr e0.toEquiv, DihedralGroup.nat_card]
  have hq := Work.L2F.Conic.circle_card (GaloisField p k) h2
  have hcardF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k (by
    rintro rfl
    simp at h5)
  rcases hq with h | h
  · left; rw [hcardC, hn, h, hcardF]
  · right; rw [hcardC, hn, h, hcardF]

/-- `L2CentInvariantProp` (Bender 1.10(i)): an odd-prime `r`-subgroup `P` (`r ≠ 2`) normalized by
the centralizer of an involution lies in that centralizer.
Proof: `C(t)` is dihedral and `P` is an `r`-group with `r` odd; when `r = p` the normalizer of a
unipotent subgroup is a Borel of order `q(q-1)/2`, which cannot contain a dihedral group of order
`q∓1` (`q∓1 ∤ q(q-1)/2`), so that case is void; when `r ≠ p` every `r`-subgroup is cyclic and lies
in a maximal torus `T` of order `q±1` in `SL` (or `(q±1)/2` in `PSL`), `N(P) = N(T)` (a `T`-unique
order-`r` subgroup is characteristic in `T`, and normalizing `P` normalizes `C(P) = T`), so
`C(t) ≤ N(T)` forces `|C(t)| = q∓1 | |N(T)| = 2(q±1)`, hence `q ∓ 1 | 2(q ± 1)`, i.e. `q ≤ 5` unless
the tori agree, in which case `P ≤ T ≤ C(t)`; the small cases `q = 5` (`A₅`) are settled by the same
order comparison. -/
theorem L2CentInvariant : Work.L2F.L2CentInvariantProp := by
  intro p k _ hp h5 t ht r hrprime hr2 P hPgrp hnorm
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  by_cases hPbot : P = ⊥
  · rw [hPbot]; exact bot_le
  by_cases hrp : r = p
  · -- ## the case `r = p`
    have hPg : IsPGroup p P := by rwa [hrp] at hPgrp
    have hdvd : Nat.card (Subgroup.normalizer (P : Set (PSL(2, GaloisField p k))))
        ∣ p ^ k * (p ^ k - 1) / 2 :=
      Work.L2F.PSL.card_normalizer_pSubgroup_dvd hp h5 P hPg hPbot
    have hdvd2 : Nat.card (Subgroup.centralizer ({t} : Set (PSL(2, GaloisField p k))))
        ∣ p ^ k * (p ^ k - 1) / 2 :=
      dvd_trans (Subgroup.card_dvd_of_le hnorm) hdvd
    have hCt := card_centralizer_involution hp h5 t ht
    rcases hCt with h | h
    · rw [h] at hdvd2
      exact absurd hdvd2 (not_dvd_of_odd (hp.pow) h5).1
    · rw [h] at hdvd2
      exact absurd hdvd2 (not_dvd_of_odd (hp.pow) h5).2
  · -- ## the case `r ≠ p`
    haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPbot
    haveI : Finite ↥P := Finite.of_injective (Subgroup.subtype P) Subtype.coe_injective
    -- a nonidentity central element `z` of `P`
    obtain ⟨z, hz⟩ : ∃ z : ↥(Subgroup.center ↥P), z ≠ 1 := by
      have hnt : Nontrivial ↥(Subgroup.center ↥P) := IsPGroup.center_nontrivial hPgrp
      exact exists_ne 1
    obtain ⟨m, hm⟩ : ∃ m : ℕ, orderOf (z : ↥P) = r ^ m := by
      obtain ⟨n, hn⟩ := hPgrp (z : ↥P)
      have hdvd : orderOf (z : ↥P) ∣ r ^ n := orderOf_dvd_of_pow_eq_one hn
      rcases (Nat.dvd_prime_pow hrprime.out).mp hdvd with ⟨j, -, hj⟩
      exact ⟨j, hj⟩
    have hyord : orderOf ((z : ↥P) : PSL(2, GaloisField p k)) = r ^ m :=
      (Subgroup.orderOf_coe (z : ↥P)).trans hm
    have hy1 : ((z : ↥P) : PSL(2, GaloisField p k)) ≠ 1 := by
      intro h
      exact hz (Subtype.ext (Subtype.ext h))
    have hodd_y : Odd (orderOf ((z : ↥P) : PSL(2, GaloisField p k))) := by
      rw [hyord]
      exact (hrprime.out.odd_of_ne_two hr2).pow
    have hcop_y : ¬ p ∣ orderOf ((z : ↥P) : PSL(2, GaloisField p k)) := by
      rw [hyord]
      intro hdvd
      have hpr : p ∣ r := (Fact.out : p.Prime).dvd_of_dvd_pow hdvd
      have h1 : r = p := (hrprime.out.dvd_iff_eq (Fact.out : p.Prime).ne_one).mp hpr
      exact hrp h1
    obtain ⟨hcyclT, hcardT, hnormT⟩ :=
      torus_structure hp h5 ((z : ↥P) : PSL(2, GaloisField p k)) hy1 hodd_y hcop_y
    set T : Subgroup (PSL(2, GaloisField p k)) :=
      Subgroup.centralizer ({((z : ↥P) : PSL(2, GaloisField p k))} :
        Set (PSL(2, GaloisField p k))) with hTdef
    haveI : IsCyclic ↥T := hcyclT
    haveI : CommGroup ↥T := IsCyclic.commGroup
    -- `P ≤ T`
    have hPleT : P ≤ T := by
      intro u hu
      change u ∈ Subgroup.centralizer ({((z : ↥P) : PSL(2, GaloisField p k))} :
        Set (PSL(2, GaloisField p k)))
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have h1 : (⟨u, hu⟩ : ↥P) * (z : ↥P) = (z : ↥P) * ⟨u, hu⟩ :=
        (Subgroup.mem_center_iff.mp z.2) ⟨u, hu⟩
      simpa using congrArg (fun w : ↥P => (w : PSL(2, GaloisField p k))) h1
    -- `C_G(P) = T`
    have hCT : Subgroup.centralizer (P : Set (PSL(2, GaloisField p k))) = T := by
      apply le_antisymm
      · intro u hu
        change u ∈ Subgroup.centralizer ({((z : ↥P) : PSL(2, GaloisField p k))} :
          Set (PSL(2, GaloisField p k)))
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        have h1 : ((z : ↥P) : PSL(2, GaloisField p k)) * u
            = u * ((z : ↥P) : PSL(2, GaloisField p k)) :=
          (Subgroup.mem_centralizer_iff.mp hu) _ (z : ↥P).2
        exact h1.symm
      · intro u hu
        change u ∈ Subgroup.centralizer (P : Set (PSL(2, GaloisField p k)))
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro w hw
        have h1 : (⟨u, hu⟩ : ↥T) * ⟨w, hPleT hw⟩ = ⟨w, hPleT hw⟩ * ⟨u, hu⟩ :=
          (IsCyclic.commGroup (α := ↥T)).mul_comm _ _
        simpa using (congrArg (fun v : ↥T => (v : PSL(2, GaloisField p k))) h1).symm
    have hNle : Subgroup.normalizer (P : Set (PSL(2, GaloisField p k)))
        ≤ Subgroup.normalizer (T : Set (PSL(2, GaloisField p k))) := by
      have h := normalizer_le_normalizer_centralizer P
      rwa [hCT] at h
    -- `|C(t)|` divides `|N(T)|`
    have hdvd : Nat.card (Subgroup.centralizer ({t} : Set (PSL(2, GaloisField p k))))
        ∣ Nat.card (Subgroup.normalizer (T : Set (PSL(2, GaloisField p k)))) :=
      Subgroup.card_dvd_of_le (le_trans hnorm hNle)
    -- the two possible orders agree
    have hkey : Nat.card (Subgroup.centralizer ({t} : Set (PSL(2, GaloisField p k))))
        = Nat.card (Subgroup.normalizer (T : Set (PSL(2, GaloisField p k)))) := by
      have htpos : 0 < Nat.card (Subgroup.normalizer (T : Set (PSL(2, GaloisField p k)))) := by
        haveI : Nonempty ↥(Subgroup.normalizer (T : Set (PSL(2, GaloisField p k)))) :=
          ⟨1, Subgroup.one_mem _⟩
        haveI : Finite ↥(Subgroup.normalizer (T : Set (PSL(2, GaloisField p k)))) :=
          Finite.of_injective (Subgroup.subtype _) Subtype.coe_injective
        exact Nat.card_pos
      have hab : Nat.card (Subgroup.centralizer ({t} : Set (PSL(2, GaloisField p k))))
          ≤ Nat.card (Subgroup.normalizer (T : Set (PSL(2, GaloisField p k)))) :=
        Nat.le_of_dvd htpos hdvd
      have hCt := card_centralizer_involution hp h5 t ht
      rcases hCt with h1 | h1 <;> rcases hcardT with h2 | h2
      · omega
      · have hdvd1 : p ^ k - 1 ∣
            Nat.card (Subgroup.normalizer (T : Set (PSL(2, GaloisField p k)))) := by
          rw [← h1]; exact hdvd
        have hbge : p ^ k - 1 ≤
            Nat.card (Subgroup.normalizer (T : Set (PSL(2, GaloisField p k)))) := by omega
        have hd : p ^ k - 1 ∣ Nat.card (Subgroup.normalizer (T : Set (PSL(2, GaloisField p k))))
            - (p ^ k - 1) := Nat.dvd_sub hdvd1 (dvd_refl _)
        have hlt : Nat.card (Subgroup.normalizer (T : Set (PSL(2, GaloisField p k))))
            - (p ^ k - 1) < p ^ k - 1 := by omega
        have h0 := Nat.eq_zero_of_dvd_of_lt hd hlt
        omega
      · omega
      · omega
    have hTeq : Subgroup.centralizer ({t} : Set (PSL(2, GaloisField p k)))
        = Subgroup.normalizer (T : Set (PSL(2, GaloisField p k))) :=
      Subgroup.eq_of_le_of_card_ge (le_trans hnorm hNle) (by rw [hkey])
    calc P ≤ T := hPleT
      _ ≤ Subgroup.normalizer (T : Set (PSL(2, GaloisField p k))) := Subgroup.le_normalizer
      _ = Subgroup.centralizer ({t} : Set (PSL(2, GaloisField p k))) := hTeq.symm

end Work.L2F.Props
