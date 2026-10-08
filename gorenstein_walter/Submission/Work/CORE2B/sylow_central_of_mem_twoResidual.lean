import Mathlib
import Submission.Work.CORE2B.Defs
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.Dihedral.Defs
import Submission.Work.FUS.thompson_transfer
import Submission.Work.FUS.DihedralSylow.subgroup_cyclic_or_dihedral

/-!
# `Work.CORE2B.sylow_central_of_mem_twoResidual`

Bender 1981, Lemma 2.7, first step, case `t ∈ O²(M)`:

Let `G` be a finite group with a dihedral Sylow `2`-subgroup `S` (`S ≃* DihedralGroup n`) and let
`t` be an involution centralizing `S` which lies in a subgroup `M ≤ G` all of whose Sylow
`2`-subgroups are non-cyclic.  If moreover `t ∈ O²(M)` (the `2`-residual of `M`, realized in `G`
as `Work.GW2.twoResidualIn M`), then `t` is *`2`-central* in `M`: some Sylow `2`-subgroup `P` of
`M` centralizes `t`.

Since every Sylow `2`-subgroup of `M` is a `2`-subgroup of `G`, it is cyclic or dihedral
(`Work.FUS.DihedralSylow.subgroup_cyclic_or_dihedral`), and the hypothesis "non-cyclic" makes it
dihedral: `P ≅ DihedralGroup m` with `m ≥ 2`.  Writing `t' = ⟨t, ·⟩ ∈ P` and
`σ = dihedralSign ∘ e : P →* Multiplicative (ZMod 2)` (the "reflection sign", whose kernel is the
rotation part `⟨r⟩` of `P`):

* if an `M`-conjugate of `t'` lies in `⟨r⟩`, then it is an involution of the cyclic group `⟨r⟩`,
  i.e. the central involution `r (m/2)` of `DihedralGroup m`; centrality of the rotations whose
  square is `1` then shows that a conjugate of `t` is central in a conjugate of `P` (a Sylow
  `2`-subgroup of `M`), which is the claim;
* if no `M`-conjugate of `t'` lies in `⟨r⟩`, then Thompson's transfer lemma
  (`Work.FUS.thompson_transfer`) produces a normal subgroup of index two of `M` not containing
  `t`; hence `t ∉ O²(M)`, contradicting the hypothesis.

The second alternative is therefore impossible, and the first gives the required Sylow subgroup.
-/

namespace Work.CORE2B

open Subgroup

open scoped Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-! ## Auxiliary group-theoretic facts -/

/-- A group of order at most two is cyclic. -/
theorem isCyclic_of_card_le_two {X : Type} [Group X] [Finite X] (h : Nat.card X ≤ 2) :
    IsCyclic X := by
  haveI : Nonempty X := ⟨1⟩
  have hpos : 0 < Nat.card X := Nat.card_pos
  rcases Nat.lt_or_ge (Nat.card X) 2 with h2 | h2
  · have h1 : Nat.card X = 1 := by omega
    refine isCyclic_iff_exists_orderOf_eq_natCard.mpr ⟨1, ?_⟩
    rw [orderOf_one, h1]
  · have h2' : Nat.card X = 2 := le_antisymm h h2
    obtain ⟨g, hg⟩ : ∃ g : X, g ≠ 1 := by
      by_contra hcon
      have hall : ∀ g : X, g = 1 := fun g => by
        by_contra hg
        exact hcon ⟨g, hg⟩
      haveI : Subsingleton X := ⟨fun a b => by rw [hall a, hall b]⟩
      have hcard : Nat.card X = 1 := Nat.card_eq_one_iff_unique.mpr ⟨‹Subsingleton X›, ⟨1⟩⟩
      omega
    refine isCyclic_iff_exists_orderOf_eq_natCard.mpr ⟨g, ?_⟩
    have hdvd : orderOf g ∣ 2 := by rw [← h2']; exact orderOf_dvd_natCard g
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hg
    · exact h1.trans h2'.symm

/-- In `DihedralGroup m`, an element of the rotation subgroup `⟨r⟩` whose square is `1` is
central.  (For `x = r i` the hypothesis `x ^ 2 = 1` is equivalent to `2 * i = 0`, which is exactly
the condition for `r i` to commute with the reflections.) -/
theorem rot_sq_one_mem_center (m : ℕ) {x : DihedralGroup m} (hx : x ∈ Work.Dihedral.rot m)
    (hx2 : x ^ 2 = 1) : x ∈ Subgroup.center (DihedralGroup m) := by
  obtain ⟨i, rfl⟩ := Work.Dihedral.mem_rot.mp hx
  have hsum : i + i = 0 := by
    have h : (DihedralGroup.r i : DihedralGroup m) * DihedralGroup.r i = DihedralGroup.r 0 := by
      rw [← pow_two, hx2, DihedralGroup.r_zero]
    rw [DihedralGroup.r_mul_r, DihedralGroup.r_zero] at h
    exact DihedralGroup.r.inj h
  have hneg : -i = i := (neg_eq_iff_add_eq_zero (a := i) (b := i)).mpr hsum
  refine Subgroup.mem_center_iff.mpr fun y => ?_
  rcases Work.Dihedral.eq_r_or_sr y with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r]
    congr 1
    ring
  · rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr]
    congr 1
    rw [sub_eq_add_neg, hneg]

/-- Transport of `rot_sq_one_mem_center` along a multiplicative equivalence: if `e u` is a rotation
of `DihedralGroup m` and `u ^ 2 = 1`, then `u` is central. -/
theorem mem_center_of_map_mem_rot {X : Type} [Group X] (m : ℕ) (e : X ≃* DihedralGroup m)
    (u : X) (hu : e u ∈ Work.Dihedral.rot m) (hu2 : u ^ 2 = 1) : u ∈ Subgroup.center X := by
  have hcenter : e u ∈ Subgroup.center (DihedralGroup m) :=
    rot_sq_one_mem_center m hu (by rw [← map_pow, hu2, map_one])
  refine Subgroup.mem_center_iff.mpr fun y => ?_
  refine e.injective ?_
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.mp hcenter (e y)

/-- Centrality transfers to conjugates: if `u ∈ P` is central in `P` and `g ∈ M`, then
`g⁻¹ * u * g` commutes with every element of the conjugate subgroup `g⁻¹ P g`. -/
theorem conj_mem_center_conj {M : Type} [Group M] (P : Subgroup M) (g u : M) (hu : u ∈ P)
    (hZ : (⟨u, hu⟩ : ↥P) ∈ Subgroup.center ↥P) :
    ∀ x ∈ (MulAut.conj g⁻¹) • P, x * (g⁻¹ * u * g) = (g⁻¹ * u * g) * x := by
  intro x hx
  have hxP : g * x * g⁻¹ ∈ P := by
    have h1 : (MulAut.conj g⁻¹)⁻¹ • x ∈ P :=
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hx
    have h2 : (MulAut.conj g⁻¹)⁻¹ • x = g * x * g⁻¹ := by
      show ((MulAut.conj g⁻¹)⁻¹ : MulAut M) x = g * x * g⁻¹
      rw [MulAut.inv_apply, MulAut.conj_symm_apply, inv_inv]
    rwa [h2] at h1
  have hcomm : (g * x * g⁻¹) * u = u * (g * x * g⁻¹) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hZ (⟨g * x * g⁻¹, hxP⟩ : ↥P))
  calc x * (g⁻¹ * u * g) = g⁻¹ * ((g * x * g⁻¹) * u) * g := by group
    _ = g⁻¹ * (u * (g * x * g⁻¹)) * g := by rw [hcomm]
    _ = (g⁻¹ * u * g) * x := by group

/-- A normal subgroup of index two contains the `2`-residual `O²` (it contains every odd-order
element, and `O²` is generated by those). -/
theorem twoResidual_le_of_index_two {M : Type} [Group M] [Finite M] (N : Subgroup M)
    (hN : N.Normal) (hidx : N.index = 2) : Work.GW2.twoResidual M ≤ N := by
  haveI := hN
  rw [Work.GW2.twoResidual, Subgroup.closure_le]
  intro g hg
  have hcard : Nat.card (M ⧸ N) = 2 := by
    rw [← Subgroup.index_eq_card N, hidx]
  have h2 : (QuotientGroup.mk' N g) ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := QuotientGroup.mk' N g)
    rwa [hcard] at h
  have hodd : Odd (orderOf (QuotientGroup.mk' N g)) :=
    Odd.of_dvd_nat hg (orderOf_map_dvd (QuotientGroup.mk' N) g)
  have hdvd2 : orderOf (QuotientGroup.mk' N g) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr h2
  have h1 : (QuotientGroup.mk' N g) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · rw [h1] at hodd
      exact absurd hodd (by decide)
  exact (QuotientGroup.eq_one_iff g).mp ((QuotientGroup.mk'_apply N g).symm.trans h1)

/-- Thompson's transfer lemma in the form used below: for a Sylow `2`-subgroup `P` of a finite
group `M` identified with `DihedralGroup m` through `e`, an involution `s ∈ P` none of whose
`M`-conjugates inside `P` is a rotation cannot lie in `O²(M)`. -/
theorem not_mem_twoResidual_of_conj_sign_ne_one {M : Type} [Group M] [Finite M]
    (P : Sylow 2 M) (m : ℕ) (e : ↥(P : Subgroup M) ≃* DihedralGroup m)
    (s : ↥(P : Subgroup M)) (hs : orderOf s = 2)
    (hfus : ∀ (g : M) (hh : g * (s : M) * g⁻¹ ∈ (P : Subgroup M)),
      ((Work.RED.dihedralSign m).comp e.toMonoidHom) ⟨g * (s : M) * g⁻¹, hh⟩ ≠ 1) :
    (s : M) ∉ Work.GW2.twoResidual M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (P : Subgroup M).index := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact P.not_dvd_index
  have hσs : ((Work.RED.dihedralSign m).comp e.toMonoidHom) s ≠ 1 := by
    have hh : (1 : M) * (s : M) * (1 : M)⁻¹ ∈ (P : Subgroup M) := by simpa using s.2
    simpa using hfus 1 hh
  obtain ⟨N, hNnorm, hidx, hsN⟩ :=
    Work.FUS.thompson_transfer (S := (P : Subgroup M)) hodd
      ((Work.RED.dihedralSign m).comp e.toMonoidHom) s hs hσs hfus
  intro hcon
  exact hsN (twoResidual_le_of_index_two N hNnorm hidx hcon)

/-- A non-cyclic `2`-subgroup `P` of a finite group `G` whose Sylow `2`-subgroups are dihedral
(`≅ DihedralGroup n`) is dihedral: `2 ≤ n` and `P ≅ DihedralGroup m` for some `m ≥ 2`. -/
theorem noncyclic_two_subgroup_dihedral_aux {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (n : ℕ) (hS : Nonempty ((S : Subgroup G) ≃* DihedralGroup n)) (P : Subgroup G)
    (hP : IsPGroup 2 P) (hnc : ¬ IsCyclic ↥P) :
    2 ≤ n ∧ ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥P ≃* DihedralGroup m) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `|P| ≤ |S| = 2 * n`
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  have hcardS : Nat.card (S : Subgroup G) = 2 * n := by
    obtain ⟨eS⟩ := hS
    rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card]
  have hcardP : Nat.card ↥P ≤ 2 * n := by
    have h1 : Nat.card ↥P ≤ Nat.card (Q : Subgroup G) := Subgroup.card_le_of_le hQ
    have h2 : Nat.card (Q : Subgroup G) = Nat.card (S : Subgroup G) :=
      Nat.card_congr (Sylow.equiv Q S).toEquiv
    omega
  -- `4 ≤ |P|`: a non-cyclic `2`-group has order at least `4`
  have hP4 : 4 ≤ Nat.card ↥P := by
    by_contra hcon
    have hcon' : Nat.card ↥P < 4 := not_le.mp hcon
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hk2 : k ≤ 1 := by
      by_contra h
      have h4 : 4 ≤ 2 ^ k := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_le.mp h)
      omega
    interval_cases k
    · exact hnc (isCyclic_of_card_le_two (X := ↥P) (by rw [hk]; norm_num))
    · exact hnc (isCyclic_of_card_le_two (X := ↥P) (by rw [hk]; norm_num))
  have hn2 : 2 ≤ n := by omega
  rcases Work.FUS.DihedralSylow.subgroup_cyclic_or_dihedral S n hn2 hS P hP with hcyc | hdih
  · exact absurd hcyc hnc
  · exact ⟨hn2, hdih⟩

/-! ## The main result -/

theorem sylow_central_of_mem_twoResidual {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (n : ℕ) (hS : Nonempty ((S : Subgroup G) ≃* DihedralGroup n)) (t : G)
    (ht : orderOf t = 2) (htc : ∀ x ∈ (S : Subgroup G), x * t = t * x) (M : Subgroup G)
    (htM : t ∈ M) (hnc : ∀ P : Sylow 2 M, ¬ IsCyclic P)
    (hres : t ∈ Work.GW2.twoResidualIn M) :
    ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M), (x : G) * t = t * (x : G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite M := inferInstance
  -- (1) a Sylow `2`-subgroup `P` of `M` containing `t`
  have htM2 : orderOf (⟨t, htM⟩ : M) = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have hgen : IsPGroup 2 (Subgroup.zpowers (⟨t, htM⟩ : M)) :=
    IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, htM2, pow_one]⟩
  obtain ⟨P, hPle⟩ := hgen.exists_le_sylow
  have htP : (⟨t, htM⟩ : M) ∈ (P : Subgroup M) := hPle (Subgroup.mem_zpowers _)
  have hncP : ¬ IsCyclic ↥(P : Subgroup M) := hnc P
  -- (2) `P` is dihedral: `P ≅ DihedralGroup m` with `m ≥ 2`
  obtain ⟨hn2, m, hm2, ⟨e₀⟩⟩ :=
    noncyclic_two_subgroup_dihedral_aux S n hS ((P : Subgroup M).map M.subtype)
      (P.isPGroup'.map M.subtype)
      (fun hcyc => hncP ((MulEquiv.isCyclic
        (Subgroup.equivMapOfInjective (P : Subgroup M) M.subtype M.subtype_injective)).mpr hcyc))
  let e : ↥(P : Subgroup M) ≃* DihedralGroup m :=
    (Subgroup.equivMapOfInjective (P : Subgroup M) M.subtype M.subtype_injective).trans e₀
  -- (3) `t` as an element of `P`, and the reflection sign on `P`
  let T : ↥(P : Subgroup M) := ⟨⟨t, htM⟩, htP⟩
  have hT2 : orderOf T = 2 := by
    rw [show T = ⟨⟨t, htM⟩, htP⟩ from rfl, Subgroup.orderOf_mk, htM2]
  by_cases hex : ∃ (g : M) (hh : g * (T : M) * g⁻¹ ∈ (P : Subgroup M)),
      ((Work.RED.dihedralSign m).comp e.toMonoidHom) ⟨g * (T : M) * g⁻¹, hh⟩ = 1
  · -- a conjugate of `t` is a rotation of `P`: it is the central involution of a Sylow of `M`
    obtain ⟨g, hh, hσ⟩ := hex
    set u : ↥(P : Subgroup M) := ⟨g * (T : M) * g⁻¹, hh⟩ with hu
    have hu2 : u ^ 2 = 1 := by
      have hord : orderOf u = 2 := by
        rw [hu, Subgroup.orderOf_mk]
        have hconj : orderOf (g * (T : M) * g⁻¹) = orderOf (T : M) := by
          have h := MulEquiv.orderOf_eq (MulAut.conj g) (T : M)
          simpa [MulAut.conj_apply] using h
        rw [hconj, Subgroup.orderOf_coe, hT2]
      simpa [hord] using pow_orderOf_eq_one u
    have huZ : u ∈ Subgroup.center ↥(P : Subgroup M) := by
      refine mem_center_of_map_mem_rot m e u ?_ hu2
      have hmem : ((Work.RED.dihedralSign m).comp e.toMonoidHom) u = 1 := by
        rw [hu]
        exact hσ
      rwa [MonoidHom.comp_apply, Work.RED.dihedralSign_eq_one_iff] at hmem
    refine ⟨(MulAut.conj g⁻¹) • P, ?_⟩
    have hkey := conj_mem_center_conj (P : Subgroup M) g (g * (T : M) * g⁻¹) hh huZ
    intro x hx
    have hxM : x ∈ (MulAut.conj g⁻¹) • (P : Subgroup M) := by
      rw [← Sylow.coe_subgroup_smul]
      exact hx
    have hcomm : x * (T : M) = (T : M) * x := by
      have h := hkey x hxM
      simpa [mul_assoc] using h
    have hTG : ((T : M) : G) = t := rfl
    simpa [hTG] using congrArg (fun z : M => (z : G)) hcomm
  · -- otherwise Thompson's transfer contradicts `t ∈ O²(M)`
    exfalso
    have hfus : ∀ (g : M) (hh : g * (T : M) * g⁻¹ ∈ (P : Subgroup M)),
        ((Work.RED.dihedralSign m).comp e.toMonoidHom) ⟨g * (T : M) * g⁻¹, hh⟩ ≠ 1 := by
      intro g hh h1
      exact hex ⟨g, hh, h1⟩
    have htres : (T : M) ∈ Work.GW2.twoResidual M := by
      have hbase : (⟨t, htM⟩ : M) ∈ Work.GW2.twoResidual M := by
        obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hres
        have hy' : y = (⟨t, htM⟩ : M) := Subtype.ext (by
          show (y : G) = t
          exact hyeq)
        rwa [hy'] at hy
      exact hbase
    exact not_mem_twoResidual_of_conj_sign_ne_one P m e T hT2 hfus htres

end Work.CORE2B
