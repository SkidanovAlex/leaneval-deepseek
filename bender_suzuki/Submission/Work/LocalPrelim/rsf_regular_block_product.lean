import Mathlib
import Submission.Work.SmallRank.Regular.Defs
import Submission.Work.SmallRank.Regular.commutator_pow_eq_one_of_regular
import Submission.Work.SmallRank.Regular.commutator_le_of_mem
import Submission.Work.SmallRank.Regular.mul_pow_of_commutator_pow_eq_one
import Submission.Work.SmallRank.Regular.isRegular_quotient
import Submission.Work.SmallRank.Regular.isRegular_subgroup
import Submission.Work.SmallRank.Regular.pow_mul_eq_one_of_isRegular

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Classical Pointwise commutatorElement
open Subgroup

namespace Work.LocalPrelim

lemma rsf_aux_smul_npow_orbit {G α : Type*} [Group G] [MulAction G α] {p : ℕ}
    (y : G) (c : ZMod p → α) (hyc : ∀ i, y • c i = c (i + 1)) :
    ∀ k : ℕ, y ^ k • c 0 = c (k : ZMod p) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_smul, ih, hyc]
      congr 1
      push_cast
      ring

lemma rsf_aux_smul_npow_mk {G : Type*} [Group G] (N : Subgroup G) (y u : G) (k : ℕ) :
    ((y ^ k * u : G) : G ⧸ N) = y ^ k • (u : G ⧸ N) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_assoc]
      rw [show ((y * (y ^ k * u) : G) : G ⧸ N) = y • ((y ^ k * u : G) : G ⧸ N) from rfl,
        ih, mul_smul]

lemma rsf_aux_conj_pow {G : Type*} [Group G] (g a : G) (k : ℕ) :
    (g⁻¹ * a * g) ^ k = g⁻¹ * a ^ k * g := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, pow_succ]; group

lemma rsf_aux_map_list_prod_range {A : Type*} [CommMonoid A] (g : ℕ → A) (n : ℕ) :
    ((List.range n).map g).prod = ∏ k ∈ Finset.range n, g k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, ih, Finset.prod_range_succ]

lemma rsf_aux_telescoping_list {G : Type*} [Group G] (b w : G) (n : ℕ) :
    (b * w) ^ n = ((List.range n).map (fun k => w ^ k * b * (w ^ k)⁻¹)).prod * w ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, pow_succ, ih]
      group

lemma rsf_aux_prod_univ_zmod_val {p : ℕ} [NeZero p] {A : Type*} [CommMonoid A] (F : ZMod p → A) :
    ∏ i : ZMod p, F i = ∏ k ∈ Finset.range p, F (k : ZMod p) := by
  have h : (Finset.univ : Finset (ZMod p)) = (Finset.range p).image (fun k : ℕ => (k : ZMod p)) := by
    ext i
    constructor
    · intro _
      exact Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr (ZMod.val_lt i),
        ZMod.natCast_zmod_val i⟩
    · intro _
      exact Finset.mem_univ i
  rw [h]
  rw [Finset.prod_image (s := Finset.range p) (g := fun k : ℕ => (k : ZMod p))]
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_range] at hx hy
  rw [← ZMod.val_natCast_of_lt hx, ← ZMod.val_natCast_of_lt hy]
  exact congrArg ZMod.val hxy

lemma rsf_aux_conj_telescoping_apply {G A : Type*} [Group G] [CommMonoid A]
    {N : Subgroup G} (φ : N →* A) (b w : G) (p : ℕ)
    (hbmem : ∀ k : ℕ, (w ^ k * b * (w ^ k)⁻¹) ∈ N)
    (hwmem : w ^ p ∈ N) (hprodmem : (b * w) ^ p ∈ N) :
    φ ⟨(b * w) ^ p, hprodmem⟩ =
      (∏ k ∈ Finset.range p, φ ⟨w ^ k * b * (w ^ k)⁻¹, hbmem k⟩) * φ ⟨w ^ p, hwmem⟩ := by
  set L : List N := (List.range p).map (fun k => (⟨w ^ k * b * (w ^ k)⁻¹, hbmem k⟩ : N)) with hL
  set PN : N := L.prod with hPN
  have hPNval : (PN : G) = ((List.range p).map (fun k => w ^ k * b * (w ^ k)⁻¹)).prod := by
    rw [hPN, hL, SubmonoidClass.coe_list_prod, List.map_map]
    rfl
  have h1 : (⟨(b * w) ^ p, hprodmem⟩ : N) = PN * ⟨w ^ p, hwmem⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subtype.coe_mk, rsf_aux_telescoping_list b w p, hPNval]
  calc φ ⟨(b * w) ^ p, hprodmem⟩
      = φ (PN * ⟨w ^ p, hwmem⟩) := by rw [h1]
    _ = φ PN * φ ⟨w ^ p, hwmem⟩ := by rw [map_mul]
    _ = (∏ k ∈ Finset.range p, φ ⟨w ^ k * b * (w ^ k)⁻¹, hbmem k⟩) * φ ⟨w ^ p, hwmem⟩ := by
        rw [hPN, map_list_prod]
        congr 1
        rw [hL, List.map_map]
        exact rsf_aux_map_list_prod_range (fun k => φ ⟨w ^ k * b * (w ^ k)⁻¹, hbmem k⟩) p

lemma rsf_aux_lift_indep {G A : Type*} [Group G] [CommMonoid A] {N : Subgroup G}
    (φ : N →* A) (x : G) {g₁ g₂ : G} (h : (g₁ : G ⧸ N) = (g₂ : G ⧸ N))
    (h₁ : g₁⁻¹ * x * g₁ ∈ N) (h₂ : g₂⁻¹ * x * g₂ ∈ N) :
    φ ⟨g₁⁻¹ * x * g₁, h₁⟩ = φ ⟨g₂⁻¹ * x * g₂, h₂⟩ := by
  have hrel : g₁⁻¹ * g₂ ∈ N := by
    have hh := Quotient.exact' h
    rwa [QuotientGroup.leftRel_apply] at hh
  have hsub : (⟨g₂⁻¹ * x * g₂, h₂⟩ : N) =
      (⟨g₁⁻¹ * g₂, hrel⟩ : N)⁻¹ * ⟨g₁⁻¹ * x * g₁, h₁⟩ * ⟨g₁⁻¹ * g₂, hrel⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
    rw [show g₂ = g₁ * (g₁⁻¹ * g₂) from by group]
    group
  have hconj : ∀ (n u : N), φ (n⁻¹ * u * n) = φ u := by
    intro n u
    rw [map_mul, map_mul, mul_assoc, mul_left_comm, ← map_mul, inv_mul_cancel, map_one, mul_one]
  rw [hsub]
  exact (hconj ⟨g₁⁻¹ * g₂, hrel⟩ ⟨g₁⁻¹ * x * g₁, h₁⟩).symm

lemma rsf_aux_translation_of_closure {G α : Type*} [Group G] [MulAction G α] {p : ℕ}
    (c : ZMod p → α) (u v : G) (ku kv : ZMod p)
    (hu : ∀ i, u • c i = c (i + ku)) (hv : ∀ i, v • c i = c (i + kv)) :
    ∀ g ∈ Subgroup.closure ({u, v} : Set G), ∃ k : ZMod p, ∀ i, g • c i = c (i + k) := by
  let S : Subgroup G :=
    { carrier := {g | ∃ k : ZMod p, ∀ i, g • c i = c (i + k)}
      mul_mem' := by
        rintro a b ⟨ka, ha⟩ ⟨kb, hb⟩
        refine ⟨ka + kb, fun i => ?_⟩
        rw [mul_smul, hb i, ha (i + kb)]
        congr 1
        ring
      one_mem' := ⟨0, fun i => by simp⟩
      inv_mem' := by
        rintro a ⟨k, ha⟩
        refine ⟨-k, fun i => ?_⟩
        rw [inv_smul_eq_iff]
        rw [ha (i + (-k))]
        congr 1
        ring }
  have huS : u ∈ S := ⟨ku, hu⟩
  have hvS : v ∈ S := ⟨kv, hv⟩
  intro g hg
  have hle : Subgroup.closure ({u, v} : Set G) ≤ S := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl) <;> assumption
  exact hle hg

lemma rsf_aux_isRegular_of_mulEquiv {p : ℕ} {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (h : Work.SmallRank.IsRegular p X) : Work.SmallRank.IsRegular p Y := by
  intro a b
  obtain ⟨d, hdmem, hdeq⟩ := h (e.symm a) (e.symm b)
  refine ⟨e d, ?_, ?_⟩
  · have hset : (e : X →* Y) '' ({(e.symm a), (e.symm b)} : Set X) = ({a, b} : Set Y) := by
      ext u; simp
    have h2 : Work.PGroup.agemo p 1 (⁅Subgroup.closure ({(a : Y), b} : Set Y),
        Subgroup.closure ({(a : Y), b} : Set Y)⁆)
        = (Work.PGroup.agemo p 1 (⁅Subgroup.closure ({(e.symm a), (e.symm b)} : Set X),
          Subgroup.closure ({(e.symm a), (e.symm b)} : Set X)⁆)).map (e : X →* Y) := by
      simp only [Work.SmallRank.Regular.map_agemo, Subgroup.map_commutator,
        MonoidHom.map_closure, hset]
    rw [h2]; exact ⟨d, hdmem, rfl⟩
  · simpa using congrArg e hdeq

lemma rsf_aux_conj_mem_phi {G A : Type*} [Group G] [CommMonoid A] {N : Subgroup G}
    (φ : N →* A) {a b n : G} (ha : a ∈ N) (hb : b ∈ N) (hn : n ∈ N)
    (h : a = n⁻¹ * b * n) : φ ⟨a, ha⟩ = φ ⟨b, hb⟩ := by
  rw [show (⟨a, ha⟩ : N) = ⟨n, hn⟩⁻¹ * ⟨b, hb⟩ * ⟨n, hn⟩ from Subtype.ext h]
  have hconj : ∀ (n b : N), φ (n⁻¹ * b * n) = φ b := by
    intro n b
    rw [map_mul, map_mul, mul_assoc, mul_left_comm, ← map_mul, inv_mul_cancel, map_one, mul_one]
  exact hconj ⟨n, hn⟩ ⟨b, hb⟩

theorem rsf_regular_block_product {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hreg : Work.SmallRank.IsRegular p ↥(P : Subgroup G))
    (N : Subgroup G) {A : Type*} [CommGroup A] (φ : ↥N →* A)
    (x y : G) (hxP : x ∈ (P : Subgroup G)) (hyP : y ∈ (P : Subgroup G)) (hxN : x ∈ N)
    (c : ZMod p → G ⧸ N) (r : ZMod p → G)
    (hc : Function.Injective c)
    (hr : ∀ i, (r i : G ⧸ N) = c i)
    (hxfix : ∀ i, x • c i = c i) (hycyc : ∀ i, y • c i = c (i + 1))
    (hxmem : ∀ i, (r i)⁻¹ * x * (r i) ∈ N)
    (hb : ∀ i, (φ ⟨(r i)⁻¹ * x * (r i), hxmem i⟩) ^ p = (φ ⟨x, hxN⟩) ^ p) :
    ∏ i : ZMod p, φ ⟨(r i)⁻¹ * x * (r i), hxmem i⟩ = (φ ⟨x, hxN⟩) ^ p := by
  classical
  haveI hpnz : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  have hyinv : ∀ i : ZMod p, y⁻¹ • c i = c (i + (-1)) := by
    intro i
    rw [inv_smul_eq_iff, hycyc (i + (-1))]
    congr 1; ring
  have hxyinv : ∀ i : ZMod p, (x * y⁻¹) • c i = c (i + (-1)) := by
    intro i
    rw [mul_smul, hyinv i, hxfix (i + (-1))]
  set r0 : G := r 0 with hr0def
  have hc0 : (r0 : G ⧸ N) = c 0 := by rw [hr0def]; exact hr 0
  have horbit : ∀ k : ℕ, y ^ k • c 0 = c (k : ZMod p) := rsf_aux_smul_npow_orbit y c hycyc
  have hlift : ∀ k : ℕ, ((y ^ k * r0 : G) : G ⧸ N) = c (k : ZMod p) := by
    intro k
    rw [rsf_aux_smul_npow_mk N y r0 k, hc0, horbit k]
  have hconjm : ∀ k : ℕ, (y ^ k * r0)⁻¹ * x * (y ^ k * r0) ∈ N := by
    intro k
    have hA : (x * (y ^ k * r0) : G ⧸ N) = (y ^ k * r0 : G ⧸ N) := by
      rw [show (x * (y ^ k * r0) : G ⧸ N) = x • ((y ^ k * r0 : G) : G ⧸ N) from rfl,
        hlift k, hxfix (k : ZMod p), ← hlift k]
    have hB := Quotient.exact' hA.symm
    rw [QuotientGroup.leftRel_apply] at hB
    simpa only [mul_assoc] using hB
  have hfixN : ∀ g : G, g • c 0 = c 0 → r0⁻¹ * g * r0 ∈ N := by
    intro g hg
    have hA : (g * r0 : G ⧸ N) = (r0 : G ⧸ N) := by
      rw [show (g * r0 : G ⧸ N) = g • (r0 : G ⧸ N) from rfl, hc0, hg]
    have hB := Quotient.exact' hA.symm
    rw [QuotientGroup.leftRel_apply] at hB
    simpa only [mul_assoc] using hB
  -- memberships
  have hyinvm : (y⁻¹) ^ p • c 0 = c 0 := by
    have h1 : y ^ p • c 0 = c 0 := by
      have := rsf_aux_smul_npow_orbit y c hycyc p
      simpa using this
    rw [inv_pow, inv_smul_eq_iff]
    exact h1.symm
  have hxy0 : (x * y⁻¹) ^ p • c 0 = c 0 := by
    have hxyk : ∀ k : ℕ, (x * y⁻¹) ^ k • c 0 = c (-(k : ZMod p)) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ', mul_smul, ih, hxyinv]
          congr 1; push_cast; ring
    have := hxyk p
    simpa using this
  have hxpk : ∀ k : ℕ, x ^ k • c 0 = c 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_smul, ih, hxfix 0]
  have hxp0 : x ^ p • c 0 = c 0 := hxpk p
  have hB0 : (x ^ p * (y⁻¹) ^ p) • c 0 = c 0 := by
    rw [mul_smul, hyinvm, hxp0]
  -- define b, w
  set w : G := r0⁻¹ * y⁻¹ * r0 with hwdef
  set b : G := r0⁻¹ * x * r0 with hbdef
  have hwb : ∀ k : ℕ, w ^ k * b * (w ^ k)⁻¹ = (y ^ k * r0)⁻¹ * x * (y ^ k * r0) := by
    intro k
    rw [hwdef, hbdef, rsf_aux_conj_pow r0 y⁻¹ k, inv_pow]
    group
  have hbmem : ∀ k : ℕ, (w ^ k * b * (w ^ k)⁻¹) ∈ N := by
    intro k
    rw [hwb k]; exact hconjm k
  have hwp : w ^ p = r0⁻¹ * (y⁻¹) ^ p * r0 := by
    rw [hwdef, rsf_aux_conj_pow r0 y⁻¹ p]
  have hwm : w ^ p ∈ N := by rw [hwp]; exact hfixN _ hyinvm
  have hbw : b * w = r0⁻¹ * (x * y⁻¹) * r0 := by rw [hbdef, hwdef]; group
  have hbwp : (b * w) ^ p = r0⁻¹ * (x * y⁻¹) ^ p * r0 := by
    rw [hbw]; exact rsf_aux_conj_pow r0 (x * y⁻¹) p
  have hA : r0⁻¹ * (x * y⁻¹) ^ p * r0 ∈ N := hfixN _ hxy0
  have hC : r0⁻¹ * (y⁻¹) ^ p * r0 ∈ N := hfixN _ hyinvm
  have hB : r0⁻¹ * (x ^ p * (y⁻¹) ^ p) * r0 ∈ N := hfixN _ hB0
  have hD : r0⁻¹ * x ^ p * r0 ∈ N := hfixN _ hxp0
  -- product equality (reindex)
  have hprod_eq : (∏ i : ZMod p, φ ⟨(r i)⁻¹ * x * (r i), hxmem i⟩)
      = ∏ k ∈ Finset.range p, φ ⟨(y ^ k * r0)⁻¹ * x * (y ^ k * r0), hconjm k⟩ := by
    rw [rsf_aux_prod_univ_zmod_val (fun i => φ ⟨(r i)⁻¹ * x * (r i), hxmem i⟩)]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    exact (rsf_aux_lift_indep φ x (by rw [hlift k, hr (k : ZMod p)]) (hconjm k)
      (hxmem (k : ZMod p))).symm
  -- telescoping in r0-conjugate form
  have hTel'' : (∏ k ∈ Finset.range p, φ ⟨(y ^ k * r0)⁻¹ * x * (y ^ k * r0), hconjm k⟩)
      = φ ⟨r0⁻¹ * (x * y⁻¹) ^ p * r0, hA⟩ * (φ ⟨r0⁻¹ * (y⁻¹) ^ p * r0, hC⟩)⁻¹ := by
    have ht := rsf_aux_conj_telescoping_apply φ b w p hbmem hwm (by rw [hbwp]; exact hA)
    rw [show (⟨(b * w) ^ p, _⟩ : N) = ⟨r0⁻¹ * (x * y⁻¹) ^ p * r0, hA⟩ from Subtype.ext hbwp] at ht
    rw [show (⟨w ^ p, hwm⟩ : N) = ⟨r0⁻¹ * (y⁻¹) ^ p * r0, hC⟩ from Subtype.ext hwp] at ht
    rw [show (∏ k ∈ Finset.range p, φ ⟨w ^ k * b * (w ^ k)⁻¹, hbmem k⟩)
        = ∏ k ∈ Finset.range p, φ ⟨(y ^ k * r0)⁻¹ * x * (y ^ k * r0), hconjm k⟩ from
      Finset.prod_congr rfl (fun k _ => congrArg φ (Subtype.ext (hwb k)))] at ht
    rw [ht]; group
  have hsplit : φ ⟨r0⁻¹ * (x ^ p * (y⁻¹) ^ p) * r0, hB⟩
      = φ ⟨r0⁻¹ * x ^ p * r0, hD⟩ * φ ⟨r0⁻¹ * (y⁻¹) ^ p * r0, hC⟩ := by
    rw [show (⟨r0⁻¹ * (x ^ p * (y⁻¹) ^ p) * r0, hB⟩ : N)
        = ⟨r0⁻¹ * x ^ p * r0, hD⟩ * ⟨r0⁻¹ * (y⁻¹) ^ p * r0, hC⟩ from
      Subtype.ext (by simp only [Subgroup.coe_mul, Subtype.coe_mk]; group), map_mul]
  have hxppow : φ ⟨r0⁻¹ * x ^ p * r0, hD⟩ = (φ ⟨x, hxN⟩) ^ p := by
    have h1 : (⟨r0⁻¹ * x ^ p * r0, hD⟩ : N) = (⟨r0⁻¹ * x * r0, hfixN x (hxfix 0)⟩ : N) ^ p := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact (rsf_aux_conj_pow r0 x p).symm
    have h1' : (φ ⟨r0⁻¹ * x ^ p * r0, hD⟩ : A)
        = (φ ⟨r0⁻¹ * x * r0, hfixN x (hxfix 0)⟩ : A) ^ p :=
      (congrArg φ h1).trans (by rw [map_pow])
    rw [h1']
    have h2' : (φ ⟨r0⁻¹ * x * r0, hfixN x (hxfix 0)⟩ : A)
        = φ ⟨(r 0)⁻¹ * x * (r 0), hxmem 0⟩ :=
      rsf_aux_lift_indep φ x (hc0.trans (hr 0).symm) (hfixN x (hxfix 0)) (hxmem 0)
    exact (congrArg (· ^ p) h2').trans (hb 0)
  have hclaim2 : φ ⟨r0⁻¹ * (x * y⁻¹) ^ p * r0, hA⟩ = φ ⟨r0⁻¹ * (x ^ p * (y⁻¹) ^ p) * r0, hB⟩ := by
    let H : Subgroup G := Subgroup.closure ({x, y⁻¹} : Set G)
    let K : Subgroup G := MulAction.stabilizer G (c 0)
    let xH : H := ⟨x, Subgroup.subset_closure (by simp)⟩
    let yH : H := ⟨y⁻¹, Subgroup.subset_closure (by simp)⟩
    have hHleP : H ≤ (P : Subgroup G) := by
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact hxP
      · exact (P : Subgroup G).inv_mem hyP
    have hHreg : Work.SmallRank.IsRegular p ↥H :=
      rsf_aux_isRegular_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHleP)
        (Work.SmallRank.Regular.isRegular_subgroup hreg (H.subgroupOf (P : Subgroup G)))
    have hKiff : ∀ g : G, g ∈ K ↔ g • c 0 = c 0 := fun g => MulAction.mem_stabilizer_iff
    have hKmem : ∀ g : G, g ∈ K → r0⁻¹ * g * r0 ∈ N := fun g hg => hfixN g ((hKiff g).mp hg)
    let psi : K →* A :=
      { toFun := fun g => φ ⟨r0⁻¹ * ((g : K) : G) * r0, hKmem (g : K) g.2⟩
        map_one' := by
          rw [show (⟨r0⁻¹ * (((1 : K) : K) : G) * r0, hKmem ((1:K):K) (1:K).2⟩ : N) = 1 from
            Subtype.ext (by simp), map_one]
        map_mul' := by
          intro g h
          rw [show (⟨r0⁻¹ * (((g * h : K) : K) : G) * r0, hKmem ((g*h:K):K) ((g*h:K):K).2⟩ : N)
              = ⟨r0⁻¹ * ((g:K):G) * r0, hKmem (g:K) (g:K).2⟩
                * ⟨r0⁻¹ * ((h:K):G) * r0, hKmem (h:K) (h:K).2⟩ from
            Subtype.ext (by simp only [Subgroup.coe_mul]; group), map_mul] }
    have hxyfix : ∀ i : ZMod p, ⁅x, y⁻¹⁆ • c i = c i := by
      intro i
      rw [commutatorElement_def]
      simp only [mul_smul, inv_inv]
      rw [hycyc i, show x⁻¹ • c (i + 1) = c (i + 1) from by rw [inv_smul_eq_iff, hxfix],
        show y⁻¹ • c (i + 1) = c i from by rw [inv_smul_eq_iff, hycyc i]]
      exact hxfix i
    have hH'K : ⁅H, H⁆ ≤ K := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨ka, hka⟩ := (rsf_aux_translation_of_closure c x y⁻¹ 0 (-1)
        (fun i => by rw [hxfix i, add_zero]) hyinv) a ha
      obtain ⟨kb, hkb⟩ := (rsf_aux_translation_of_closure c x y⁻¹ 0 (-1)
        (fun i => by rw [hxfix i, add_zero]) hyinv) b hb
      have hka' : ∀ i : ZMod p, a⁻¹ • c i = c (i - ka) := by
        intro i
        rw [inv_smul_eq_iff, hka (i - ka)]
        congr 1; ring
      have hkb' : ∀ i : ZMod p, b⁻¹ • c i = c (i - kb) := by
        intro i
        rw [inv_smul_eq_iff, hkb (i - kb)]
        congr 1; ring
      exact (hKiff ⁅a, b⁆).mpr (by
        rw [commutatorElement_def]
        simp only [mul_smul]
        rw [hkb' 0, hka' (0 - kb), hkb ((0 - kb) - ka), hka (((0 - kb) - ka) + kb)]
        congr 1; ring)
    have hxyH : ((⁅xH, yH⁆ : H) : G) = ⁅x, y⁻¹⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    have hPc : ∀ w : H, ∀ (hk : ((w * ⁅xH, yH⁆ * w⁻¹ : H) : G) ∈ K),
        (psi ⟨((w * ⁅xH, yH⁆ * w⁻¹ : H) : G), hk⟩) ^ p = 1 := by
      intro w hk
      obtain ⟨kz, hkz⟩ := (rsf_aux_translation_of_closure c x y⁻¹ 0 (-1)
        (fun i => by rw [hxfix i, add_zero]) hyinv) (w⁻¹) (H.inv_mem w.2)
      have hzc0 : ((w⁻¹ : H) : G) • c 0 = c kz := by
        rw [show ((w⁻¹:H):G) • c 0 = c (0 + kz) from hkz 0]; congr 1; ring
      have hcoe : ((w * ⁅xH, yH⁆ * w⁻¹ : H) : G) = (((w⁻¹ : H) : G))⁻¹ * ⁅x, y⁻¹⁆ * ((w⁻¹ : H) : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxyH]
        group
      set rh : G := ((w⁻¹ : H) : G) * r0 with hrh
      have hrhc : (rh : G ⧸ N) = c kz := by
        rw [hrh, show (((w⁻¹:H):G) * r0 : G ⧸ N) = ((w⁻¹:H):G) • (r0 : G ⧸ N) from rfl,
          hc0, hzc0]
      have hxm : rh⁻¹ * x * rh ∈ N := by
        have h1 : (x * rh : G ⧸ N) = (rh : G ⧸ N) := by
          rw [show (x * rh : G ⧸ N) = x • (rh : G ⧸ N) from rfl, hrhc, hxfix kz, ← hrhc]
        have h2 := Quotient.exact' h1.symm
        rw [QuotientGroup.leftRel_apply] at h2
        simpa only [mul_assoc] using h2
      have hrmem : rh⁻¹ * ⁅x, y⁻¹⁆ * rh ∈ N := by
        have h1 : (⁅x, y⁻¹⁆ * rh : G ⧸ N) = (rh : G ⧸ N) := by
          rw [show (⁅x,y⁻¹⁆ * rh : G ⧸ N) = ⁅x,y⁻¹⁆ • (rh : G ⧸ N) from rfl, hrhc, hxyfix kz,
            ← hrhc]
        have h2 := Quotient.exact' h1.symm
        rw [QuotientGroup.leftRel_apply] at h2
        simpa only [mul_assoc] using h2
      have hval : (psi ⟨((w * ⁅xH, yH⁆ * w⁻¹ : H) : G), hk⟩ : A)
          = φ ⟨rh⁻¹ * ⁅x, y⁻¹⁆ * rh, hrmem⟩ := by
        have heq : r0⁻¹ * (((w * ⁅xH, yH⁆ * w⁻¹ : H) : G)) * r0 = rh⁻¹ * ⁅x, y⁻¹⁆ * rh := by
          rw [hcoe, hrh]; group
        exact congrArg φ (Subtype.ext heq)
      rw [hval]
      have hyr : (y * rh)⁻¹ * x * (y * rh) ∈ N := by
        have hyrhc : ((y * rh : G) : G ⧸ N) = c (kz + 1) := by
          rw [show ((y * rh : G) : G ⧸ N) = y • (rh : G ⧸ N) from rfl, hrhc, hycyc kz]
        have h1 : (x * (y * rh) : G ⧸ N) = (y * rh : G ⧸ N) := by
          rw [show (x * (y * rh) : G ⧸ N) = x • ((y * rh : G) : G ⧸ N) from rfl, hyrhc,
            hxfix (kz + 1), ← hyrhc]
        have h2 := Quotient.exact' h1.symm
        rw [QuotientGroup.leftRel_apply] at h2
        simpa only [mul_assoc] using h2
      have hsplit : φ ⟨rh⁻¹ * ⁅x, y⁻¹⁆ * rh, hrmem⟩
          = φ ⟨rh⁻¹ * x * rh, hxm⟩ * (φ ⟨(y * rh)⁻¹ * x * (y * rh), hyr⟩)⁻¹ := by
        have heq : (⟨rh⁻¹ * ⁅x, y⁻¹⁆ * rh, hrmem⟩ : N)
            = ⟨rh⁻¹ * x * rh, hxm⟩ * (⟨(y * rh)⁻¹ * x * (y * rh), hyr⟩)⁻¹ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
          rw [commutatorElement_def]
          group
        rw [heq, map_mul, map_inv]
      rw [hsplit]
      have hl1 : φ ⟨rh⁻¹ * x * rh, hxm⟩
          = φ ⟨(r kz)⁻¹ * x * (r kz), hxmem kz⟩ :=
        rsf_aux_lift_indep φ x (by rw [hrhc, hr kz]) hxm (hxmem kz)
      have hl2 : φ ⟨(y * rh)⁻¹ * x * (y * rh), hyr⟩
          = φ ⟨(r (kz + 1))⁻¹ * x * (r (kz + 1)), hxmem (kz + 1)⟩ :=
        rsf_aux_lift_indep φ x (by
          rw [show ((y * rh : G) : G ⧸ N) = y • (rh : G ⧸ N) from rfl, hrhc, hycyc kz,
            ← hr (kz + 1)]) hyr (hxmem (kz + 1))
      rw [hl1, hl2, mul_pow, inv_pow, hb kz, hb (kz + 1), mul_inv_cancel]
    let T : Subgroup A :=
      { carrier := {u : A | u ^ p = 1}
        mul_mem' := by
          intro a b ha hb
          show (a * b) ^ p = 1
          rw [mul_pow, ha, hb, one_mul]
        one_mem' := by
          show (1 : A) ^ p = 1
          rw [one_pow]
        inv_mem' := by
          intro a ha
          show (a⁻¹) ^ p = 1
          rw [inv_pow, ha, inv_one] }
    let S : Subgroup G := (Subgroup.comap psi T).map K.subtype
    have hSleK : S ≤ K := Subgroup.map_le_iff_le_comap.mpr (fun x _ => x.2)
    have hSchar : ∀ c ∈ S, c ∈ K ∧ ∀ (hc : c ∈ K), (psi ⟨c, hc⟩) ^ p = 1 := by
      intro c hc
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hc
      exact ⟨k.2, fun _ => Subgroup.mem_comap.mp hk⟩
    have hconjS : ∀ w : H, ((w * ⁅xH, yH⁆ * w⁻¹ : H) : G) ∈ S := by
      intro w
      have hK : ((w * ⁅xH, yH⁆ * w⁻¹ : H) : G) ∈ K := by
        rw [hKiff]
        set v : G := ((w⁻¹ : H) : G) with hv
        have hcoe : ((w * ⁅xH, yH⁆ * w⁻¹ : H) : G) = v⁻¹ * ⁅x, y⁻¹⁆ * v := by
          rw [hv]; simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxyH]; group
        obtain ⟨kw, hkw⟩ := (rsf_aux_translation_of_closure c x y⁻¹ 0 (-1)
          (fun i => by rw [hxfix i, add_zero]) hyinv) (w⁻¹) (H.inv_mem w.2)
        have hvc : v • c 0 = c kw := by
          rw [hv]
          exact (by rw [show ((w⁻¹:H):G)•c 0 = c (0+kw) from hkw 0]; congr 1; ring)
        rw [hcoe, show (v⁻¹ * ⁅x,y⁻¹⁆ * v) • c 0 = v⁻¹ • (⁅x,y⁻¹⁆ • (v • c 0)) from by
            rw [mul_smul, mul_smul], hvc, hxyfix kw,
          show v⁻¹ • c kw = c 0 from by rw [inv_smul_eq_iff]; exact hvc.symm]
      refine Subgroup.mem_map.mpr ⟨⟨_, hK⟩, ?_, rfl⟩
      exact Subgroup.mem_comap.mpr (hPc w hK)
    have hNnS : Subgroup.normalClosure ({⁅xH, yH⁆} : Set H) ≤ S.comap H.subtype := by
      rw [show Subgroup.normalClosure ({⁅xH, yH⁆} : Set H)
          = Subgroup.closure (Group.conjugatesOfSet ({⁅xH, yH⁆} : Set H)) from rfl]
      rw [Subgroup.closure_le]
      intro z hz
      rw [Group.mem_conjugatesOfSet_iff] at hz
      obtain ⟨a, ha, hac⟩ := hz
      obtain rfl : a = ⁅xH, yH⁆ := by simpa using ha
      obtain ⟨w, hw⟩ := isConj_iff.mp hac
      rw [← hw]
      exact hconjS w
    have hgen : Subgroup.closure ({xH, yH} : Set H) = ⊤ := by
      rw [eq_top_iff]
      intro z _
      suffices h : (z : G) ∈ (Subgroup.closure ({xH, yH} : Set H)).map H.subtype by
        obtain ⟨w, hw, hwz⟩ := h
        rwa [← Subtype.ext hwz]
      have hmap : (Subgroup.closure ({xH, yH} : Set H)).map H.subtype = H := by
        rw [MonoidHom.map_closure]
        rw [show H.subtype '' ({xH, yH} : Set H) = ({x, y⁻¹} : Set G) from by
          ext u; constructor
          · rintro ⟨v, (rfl | rfl), rfl⟩
            · exact Or.inl rfl
            · exact Or.inr rfl
          · rintro (rfl | rfl)
            · exact ⟨xH, Or.inl rfl, rfl⟩
            · exact ⟨yH, Or.inr rfl, rfl⟩]
      rw [hmap]; exact z.2
    have hmemNn : xH * yH * xH⁻¹ * yH⁻¹ ∈ Subgroup.normalClosure ({⁅xH, yH⁆} : Set H) :=
      Subgroup.subset_normalClosure (by rw [commutatorElement_def]; exact Set.mem_singleton _)
    have hcommle : Work.SmallRank.commutator ↥H ≤ Subgroup.normalClosure ({⁅xH, yH⁆} : Set H) :=
      Work.SmallRank.Regular.commutator_le_of_mem hgen _ hmemNn
    have hH'le : ⁅H, H⁆ ≤ S := by
      have h1 : (Work.SmallRank.commutator ↥H).map H.subtype
          ≤ (Subgroup.normalClosure ({⁅xH, yH⁆} : Set H)).map H.subtype :=
        Subgroup.map_mono hcommle
      rw [Work.SmallRank.commutator, Subgroup.map_commutator, Subgroup.map_top, H.range_subtype] at h1
      exact h1.trans ((Subgroup.map_mono hNnS).trans (Subgroup.map_comap_le H.subtype S))
    have hpsiH' : ∀ c ∈ ⁅H, H⁆, ∀ (hc : c ∈ K), (psi ⟨c, hc⟩) ^ p = 1 := by
      intro c hc0 hc
      have hSc := hSchar c (hH'le hc0)
      rw [show (⟨c, hc⟩ : K) = ⟨c, hSleK (hH'le hc0)⟩ from Subtype.ext rfl]
      exact hSc.2 _
    obtain ⟨d, hdmem, hdeq⟩ := hHreg xH yH
    have hd' : ((d : H) : G) ∈ Work.PGroup.agemo p 1 ⁅H, H⁆ := by
      rw [hgen] at hdmem
      have h1 : (d : G) ∈ (Work.PGroup.agemo p 1 (Work.SmallRank.commutator ↥H)).map H.subtype :=
        ⟨d, hdmem, rfl⟩
      rw [Work.SmallRank.Regular.map_agemo, Work.SmallRank.commutator, Subgroup.map_commutator,
        Subgroup.map_top, H.range_subtype] at h1
      exact h1
    have hdeq' : x ^ p * (y⁻¹) ^ p = (x * y⁻¹) ^ p * ((d : H) : G) := by
      have h := congrArg (fun u : H => (u : G)) hdeq
      simpa only [Subgroup.coe_mul, Subgroup.coe_pow] using h
    have hdK : ((d : H) : G) ∈ K := by
      have hdd : ((d : H) : G) = ((x * y⁻¹) ^ p)⁻¹ * (x ^ p * (y⁻¹) ^ p) := by
        rw [show ((d:H):G) = ((x*y⁻¹)^p)⁻¹ * ((x*y⁻¹)^p * ((d:H):G)) from by group, ← hdeq']
      rw [hKiff, hdd, show (((x*y⁻¹)^p)⁻¹ * (x^p*(y⁻¹)^p)) • c 0
          = ((x*y⁻¹)^p)⁻¹ • ((x^p*(y⁻¹)^p) • c 0) from by rw [mul_smul], hB0,
        show ((x*y⁻¹)^p)⁻¹ • c 0 = c 0 from by rw [inv_smul_eq_iff]; exact hxy0.symm]
    have heK : ((d : H) : G)⁻¹ ∈ K := K.inv_mem hdK
    have he : ((d : H) : G)⁻¹ ∈ Work.PGroup.agemo p 1 ⁅H, H⁆ :=
      (Work.PGroup.agemo p 1 ⁅H,H⁆).inv_mem hd'
    have hAgemo : ∀ (g : G) (hg : g ∈ Work.PGroup.agemo p 1 ⁅H, H⁆) (hk : g ∈ K),
        (psi ⟨g, hk⟩ : A) = 1 := by
      intro g hg hk
      have hle : Work.PGroup.agemo p 1 ⁅H, H⁆ ≤ (psi.ker).map K.subtype := by
        rw [Work.PGroup.agemo, Subgroup.closure_le]
        rintro y ⟨x, hx, rfl⟩
        refine Subgroup.mem_map.mpr ⟨⟨x ^ p ^ 1, K.pow_mem (hH'K hx) (p ^ 1)⟩, ?_, ?_⟩
        · rw [MonoidHom.mem_ker]
          have h1 : (⟨x ^ p ^ 1, K.pow_mem (hH'K hx) (p ^ 1)⟩ : K) = (⟨x, hH'K hx⟩ : K) ^ p := by
            apply Subtype.ext
            simp only [Subgroup.coe_pow]
            rw [pow_one]
          have h2 : psi (⟨x ^ p ^ 1, K.pow_mem (hH'K hx) (p ^ 1)⟩ : K)
              = (psi (⟨x, hH'K hx⟩ : K)) ^ p :=
            (congrArg psi h1).trans (by rw [map_pow])
          rw [h2]
          exact hpsiH' x hx (hH'K hx)
        · rfl
      obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp (hle hg)
      exact (congrArg psi (Subtype.ext hkg.symm)).trans (MonoidHom.mem_ker.mp hk)
    have hkill : φ ⟨r0⁻¹ * ((d : H) : G)⁻¹ * r0, hKmem _ heK⟩ = 1 := by
      have h1 : psi ⟨((d : H) : G)⁻¹, heK⟩ = φ ⟨r0⁻¹ * ((d : H) : G)⁻¹ * r0, hKmem _ heK⟩ := rfl
      rw [← h1]
      exact hAgemo _ he heK
    have heq : (⟨r0⁻¹ * (x * y⁻¹) ^ p * r0, hA⟩ : N)
        = ⟨r0⁻¹ * (x ^ p * (y⁻¹) ^ p) * r0, hB⟩
          * ⟨r0⁻¹ * ((d : H) : G)⁻¹ * r0, hKmem _ heK⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subtype.coe_mk]
      rw [hdeq']; group
    rw [show φ ⟨r0⁻¹ * (x * y⁻¹) ^ p * r0, hA⟩
        = φ ⟨r0⁻¹ * (x ^ p * (y⁻¹) ^ p) * r0, hB⟩ * φ ⟨r0⁻¹ * ((d : H) : G)⁻¹ * r0, hKmem _ heK⟩
        from by rw [heq, map_mul]]
    rw [hkill, mul_one]
  calc ∏ i : ZMod p, φ ⟨(r i)⁻¹ * x * (r i), hxmem i⟩
      = ∏ k ∈ Finset.range p, φ ⟨(y ^ k * r0)⁻¹ * x * (y ^ k * r0), hconjm k⟩ := hprod_eq
    _ = φ ⟨r0⁻¹ * (x * y⁻¹) ^ p * r0, hA⟩ * (φ ⟨r0⁻¹ * (y⁻¹) ^ p * r0, hC⟩)⁻¹ := hTel''
    _ = φ ⟨r0⁻¹ * (x ^ p * (y⁻¹) ^ p) * r0, hB⟩ * (φ ⟨r0⁻¹ * (y⁻¹) ^ p * r0, hC⟩)⁻¹ := by
        rw [hclaim2]
    _ = (φ ⟨r0⁻¹ * x ^ p * r0, hD⟩ * φ ⟨r0⁻¹ * (y⁻¹) ^ p * r0, hC⟩)
          * (φ ⟨r0⁻¹ * (y⁻¹) ^ p * r0, hC⟩)⁻¹ := by rw [hsplit]
    _ = φ ⟨r0⁻¹ * x ^ p * r0, hD⟩ := by group
    _ = (φ ⟨x, hxN⟩) ^ p := hxppow

end Work.LocalPrelim
