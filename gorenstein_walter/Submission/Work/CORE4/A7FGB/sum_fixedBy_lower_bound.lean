import Mathlib
import Submission.Work.CORE4.A7FGB.involution_support_injective
import Submission.Work.CORE4.A7FGB.sum_fixedBy_pretransitive

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Work.CORE4.A7FGB

open scoped Pointwise

/-!
# A lower bound for `|R|` in terms of the number of conjugates of a four-group

Let `V ≤ R ≤ A₇` with `V` a four-group all of whose non-identity elements have support a
`4`-element set `T`, let `x ∈ R` be a `3`-cycle whose support is the complement of `T`, and
suppose that `R` acts transitively on `Fin 7`.  Then

  `17 * [R : N_R(V)] + 7 ≤ |R|`.

The proof counts fixed points.  Since `R` is transitive, `∑_{g ∈ R} |Fix g| = |R|`.  The
conjugates of `V` number `[R : N_R(V)]` and contribute `3` involutions of support of size `4`
each (three fixed points apiece), while each conjugate of `V` also determines the two `3`-cycles
supported on the complement of its support (four fixed points apiece).  This gives
`|R| ≥ 7 + 9[R : N_R(V)] + 8[R : N_R(V)]`.

The only structural input is that among the involutions of `A₇` with a prescribed support there
are at most three, whence the conjugates of `V` are exactly the four-groups with that support.
-/

/-- The coercion of a product of two elements of a subgroup. -/
lemma sfb_coe_mul_self {u : alternatingGroup (Fin 7)} (h : u * u = 1) :
    (u : Equiv.Perm (Fin 7)) * (u : Equiv.Perm (Fin 7)) = 1 := by
  have h' := congrArg (fun z : alternatingGroup (Fin 7) => (z : Equiv.Perm (Fin 7))) h
  simpa only [Subgroup.coe_mul, Subgroup.coe_one] using h'

/-- Cancellation of a conjugate. -/
lemma sfb_conj_cancel {a b c : Equiv.Perm (Fin 7)} (h : a * b * a⁻¹ = a * c * a⁻¹) :
    b = c := by
  calc b = (a⁻¹ * a) * b * (a⁻¹ * a) := by simp
    _ = a⁻¹ * (a * b * a⁻¹) * a := by group
    _ = a⁻¹ * (a * c * a⁻¹) * a := by rw [h]
    _ = c := by group

/-- **At most three involutions of `A₇` have a prescribed support.**  An involution of a
`4`-element support is determined by its value at a fixed point of the support. -/
lemma sfb_card_involWithSupp_le_three (S : Finset (Fin 7)) (hS : S.card = 4) :
    (Finset.univ.filter (fun u : alternatingGroup (Fin 7) =>
      u * u = 1 ∧ u ≠ 1 ∧ (u : Equiv.Perm (Fin 7)).support = S)).card ≤ 3 := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hmain : (Finset.univ.filter (fun u : alternatingGroup (Fin 7) =>
      u * u = 1 ∧ u ≠ 1 ∧ (u : Equiv.Perm (Fin 7)).support = S)).card ≤ (S.erase a).card := by
    refine Finset.card_le_card_of_injOn
      (fun u : alternatingGroup (Fin 7) => (u : Equiv.Perm (Fin 7)) a) ?_ ?_
    · intro u hu
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      obtain ⟨-, _, huS⟩ := hu
      have hmem : a ∈ ((u : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support := by
        rw [huS]; exact ha
      rw [Finset.mem_coe, Finset.mem_erase]
      exact ⟨fun hcon => (Equiv.Perm.mem_support.mp hmem) hcon,
        by rw [← huS]; exact Equiv.Perm.apply_mem_support.mpr (by rw [huS]; exact ha)⟩
    · intro u hu v hv huv
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      exact Subtype.ext
        (involution_support_injective S hS a ha _ _ (sfb_coe_mul_self hu.1)
          (sfb_coe_mul_self hv.1) hu.2.2 hv.2.2 huv)
  simpa [Finset.card_erase_of_mem ha, hS] using hmain

/-- **Fixed points versus support.**  An element of a subgroup of `A₇` fixes `7` minus the
cardinality of its support points of `Fin 7`. -/
lemma sfb_card_fixedBy_eq (R : Subgroup (alternatingGroup (Fin 7))) (g : ↥R) :
    Fintype.card (MulAction.fixedBy (Fin 7) g)
      = 7 - ((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support.card := by
  classical
  set σ : Equiv.Perm (Fin 7) := ((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) with hσ
  have hfix : Fintype.card (MulAction.fixedBy (Fin 7) g) =
      Fintype.card {x : Fin 7 // σ x = x} := by
    refine Fintype.card_congr (Equiv.subtypeEquivRight ?_)
    intro x
    simp only [MulAction.mem_fixedBy, Subgroup.smul_def, Equiv.Perm.smul_def, hσ]
  have hcard : Fintype.card {x : Fin 7 // σ x = x}
      = (Finset.univ.filter (fun x : Fin 7 => σ x = x)).card := Fintype.card_subtype _
  have hsup : σ.support = Finset.univ.filter (fun x : Fin 7 => σ x ≠ x) := rfl
  have hpart : (Finset.univ.filter (fun x : Fin 7 => σ x = x)).card +
      (Finset.univ.filter (fun x : Fin 7 => σ x ≠ x)).card = 7 := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 7)))
      (p := fun x => σ x = x)
    simpa using h
  rw [hfix, hcard, hsup]
  omega

/-- The pointwise action of an element of a subgroup on a `Finset` is the image under the
underlying permutation. -/
lemma sfb_smul_finset_eq_map {R : Subgroup (alternatingGroup (Fin 7))} (g : ↥R)
    (S : Finset (Fin 7)) :
    (g • S : Finset (Fin 7)) =
      S.map ((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).toEmbedding := by
  ext x
  rw [Finset.mem_smul_finset, Finset.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, hy, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hyx⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, hy, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hyx⟩

/-- A permutation preserving a `Finset` is also preserved by its inverse. -/
lemma sfb_map_inv_eq_of_map_eq (σ : Equiv.Perm (Fin 7)) (S : Finset (Fin 7))
    (h : S.map σ.toEmbedding = S) : S.map (σ⁻¹).toEmbedding = S := by
  have hset : (σ : Equiv.Perm (Fin 7)) '' (S : Set (Fin 7)) = (S : Set (Fin 7)) := by
    simpa [Finset.coe_map] using
      congrArg (fun t : Finset (Fin 7) => (t : Set (Fin 7))) h
  apply Finset.coe_injective
  rw [Finset.coe_map]
  conv_lhs => rw [← hset]
  rw [Set.image_image]
  simp

/-- A permutation maps the complement of a `Finset` onto the complement of its image. -/
lemma sfb_map_sdiff_univ (σ : Equiv.Perm (Fin 7)) (S : Finset (Fin 7)) :
    (Finset.univ \ S).map σ.toEmbedding = Finset.univ \ S.map σ.toEmbedding := by
  rw [Finset.map_sdiff, Finset.map_univ_equiv σ]

/-- The support of a conjugate. -/
lemma sfb_conj_support (g h : alternatingGroup (Fin 7)) :
    ((g * h * g⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support =
      ((h : Equiv.Perm (Fin 7)).support).map (g : Equiv.Perm (Fin 7)).toEmbedding := by
  rw [show ((g * h * g⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
      (g : Equiv.Perm (Fin 7)) * (h : Equiv.Perm (Fin 7)) * ((g : Equiv.Perm (Fin 7)))⁻¹
      from by simp only [Subgroup.coe_mul, Subgroup.coe_inv],
    Equiv.Perm.support_conj]

/-- **The four-group of a given support is determined by its support.**  If `g` maps the
`4`-element set `T` onto itself, then conjugation by `g` preserves any four-group `V ≤ A₇` whose
non-identity elements all have support `T`. -/
lemma sfb_conj_mem_iff_of_map_eq (V : Subgroup (alternatingGroup (Fin 7))) (T : Finset (Fin 7))
    (hT : T.card = 4) (hVcard : Nat.card V = 4) (h2 : ∀ v ∈ V, v * v = 1)
    (hsupp : ∀ v ∈ V, v ≠ 1 → (v : Equiv.Perm (Fin 7)).support = T)
    (g : alternatingGroup (Fin 7)) (hg : T.map (g : Equiv.Perm (Fin 7)).toEmbedding = T) :
    ∀ h : alternatingGroup (Fin 7), h ∈ V ↔ g * h * g⁻¹ ∈ V := by
  classical
  -- The involutions of support `T` are exactly the non-identity elements of `V`.
  set Inv : Finset (alternatingGroup (Fin 7)) :=
    Finset.univ.filter (fun u => u * u = 1 ∧ u ≠ 1 ∧
      (u : Equiv.Perm (Fin 7)).support = T) with hInv
  have hInv_le : Inv.card ≤ 3 := sfb_card_involWithSupp_le_three T hT
  have hVsub : (V : Set (alternatingGroup (Fin 7))).toFinset.erase 1 ⊆ Inv := by
    intro u hu
    rw [Finset.mem_erase] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have huV : u ∈ V := by rwa [Set.mem_toFinset] at hu2
    rw [hInv]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h2 u huV, hu1, hsupp u huV hu1⟩
  have herase_card : ((V : Set (alternatingGroup (Fin 7))).toFinset.erase 1).card = 3 := by
    rw [Finset.card_erase_of_mem (by rw [Set.mem_toFinset]; exact V.one_mem), Set.toFinset_card]
    have hcardV : Fintype.card ↥(V : Set (alternatingGroup (Fin 7))) = 4 := by
      rw [← Nat.card_eq_fintype_card]; exact hVcard
    omega
  have hInv_eq : Inv = (V : Set (alternatingGroup (Fin 7))).toFinset.erase 1 :=
    (Finset.eq_of_subset_of_card_le hVsub (by rw [herase_card]; exact hInv_le)).symm
  have hkey : ∀ u : alternatingGroup (Fin 7), u ≠ 1 → (u ∈ V ↔ u ∈ Inv) := by
    intro u hu
    rw [hInv_eq, Finset.mem_erase]
    exact ⟨fun huv => ⟨hu, by rwa [Set.mem_toFinset]⟩,
      fun h => by obtain ⟨-, huV⟩ := h; rwa [Set.mem_toFinset] at huV⟩
  -- Conjugation by an element preserving `T` maps `V` into `V`.
  have hmain : ∀ a : alternatingGroup (Fin 7),
      T.map (a : Equiv.Perm (Fin 7)).toEmbedding = T →
      ∀ u : alternatingGroup (Fin 7), u ∈ V → a * u * a⁻¹ ∈ V := by
    intro a ha u huV
    by_cases hu1 : u = 1
    · subst hu1; simp
    · have huInv : u ∈ Inv := (hkey u hu1).mp huV
      have hconjInv : a * u * a⁻¹ ∈ Inv := by
        rw [hInv] at huInv ⊢
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at huInv ⊢
        obtain ⟨hu2, hu1', huS⟩ := huInv
        refine ⟨?_, ?_, ?_⟩
        · have hmul : (a * u * a⁻¹) * (a * u * a⁻¹) = a * (u * u) * a⁻¹ := by group
          rw [hmul, hu2, mul_one]
          exact mul_inv_cancel a
        · intro hcon
          exact hu1' (by
            have hu' : u = a⁻¹ * (a * u * a⁻¹) * a := by group
            rw [hu', hcon]
            simp)
        · rw [sfb_conj_support, huS, ha]
      have hne : a * u * a⁻¹ ≠ 1 := by
        intro hcon
        exact hu1 (by
          have hu' : u = a⁻¹ * (a * u * a⁻¹) * a := by group
          rw [hu', hcon]
          simp)
      exact (hkey (a * u * a⁻¹) hne).mpr hconjInv
  intro h
  by_cases h1 : h = 1
  · subst h1; simp
  constructor
  · intro hV; exact hmain g hg h hV
  · intro hV
    have hginv : T.map ((g⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).toEmbedding = T := by
      have hmap := sfb_map_inv_eq_of_map_eq (g : Equiv.Perm (Fin 7)) T hg
      simpa only [Subgroup.coe_inv] using hmap
    have h' : h = g⁻¹ * (g * h * g⁻¹) * g := by group
    rw [h']
    simpa using hmain g⁻¹ hginv (g * h * g⁻¹) hV

/-- **The number of conjugates of `V` is the index of its normalizer.** -/
lemma sfb_orbit_card_eq_relIndex (R V : Subgroup (alternatingGroup (Fin 7)))
    (T : Finset (Fin 7)) (hT : T.card = 4) (hVcard : Nat.card V = 4)
    (h2 : ∀ v ∈ V, v * v = 1)
    (hsupp : ∀ v ∈ V, v ≠ 1 → (v : Equiv.Perm (Fin 7)).support = T) :
    Nat.card (MulAction.orbit ↥R T) =
      (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R := by
  classical
  set M : Subgroup (alternatingGroup (Fin 7)) := R ⊓ Subgroup.normalizer (V : Set _) with hM
  have hstab : MulAction.stabilizer ↥R T = M.subgroupOf R := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hgT
      refine ⟨g.2, ?_⟩
      have hgmap : T.map ((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).toEmbedding = T := by
        rw [← sfb_smul_finset_eq_map (g := g) T, hgT]
      exact Subgroup.mem_normalizer_iff.mpr
        (sfb_conj_mem_iff_of_map_eq V T hT hVcard h2 hsupp g hgmap)
    · rintro ⟨-, hgN⟩
      obtain ⟨v, hv⟩ := Fintype.exists_ne_of_one_lt_card (α := ↥V)
        (by rw [← Nat.card_eq_fintype_card]; omega) (1 : ↥V)
      have hvV : (v : alternatingGroup (Fin 7)) ∈ V := v.2
      have hv1 : (v : alternatingGroup (Fin 7)) ≠ 1 := fun h => hv (Subtype.ext h)
      have hmem : (g : alternatingGroup (Fin 7)) * (v : alternatingGroup (Fin 7)) *
          (g : alternatingGroup (Fin 7))⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp hgN (v : alternatingGroup (Fin 7))).mp hvV
      have hne1 : (g : alternatingGroup (Fin 7)) * (v : alternatingGroup (Fin 7)) *
          (g : alternatingGroup (Fin 7))⁻¹ ≠ 1 := by
        intro hcon
        exact hv1 (by
          have hv' : (v : alternatingGroup (Fin 7)) = (g : alternatingGroup (Fin 7))⁻¹ *
              ((g : alternatingGroup (Fin 7)) * (v : alternatingGroup (Fin 7)) *
                (g : alternatingGroup (Fin 7))⁻¹) * (g : alternatingGroup (Fin 7)) := by group
          rw [hv', hcon]
          simp)
      have hsupp' := hsupp _ hmem hne1
      rw [sfb_conj_support, hsupp v hvV hv1] at hsupp'
      rw [sfb_smul_finset_eq_map (g := g) T]
      exact hsupp'
  have hcardstab : Nat.card ↥(M.subgroupOf R) = Nat.card ↥M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show M ≤ R from inf_le_left)).toEquiv
  calc Nat.card (MulAction.orbit ↥R T)
      = (MulAction.stabilizer ↥R T).index := by
        rw [Subgroup.index_eq_card]
        exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥R T)
    _ = (M.subgroupOf R).index := by rw [hstab]
    _ = Nat.card ↥R / Nat.card ↥(M.subgroupOf R) := Subgroup.index_eq_card_div _
    _ = Nat.card ↥R / Nat.card ↥M := by rw [hcardstab]
    _ = M.relIndex R := by
        rw [show M.relIndex R = (M.subgroupOf R).index from rfl,
          Subgroup.index_eq_card_div (M.subgroupOf R), hcardstab]

/-- `3 * [R : N_R(V)]` involutions of support of size `4` lie in `R`. -/
lemma sfb_three_mul_relIndex_le_involutions (R V : Subgroup (alternatingGroup (Fin 7)))
    [Fintype ↥R] (T : Finset (Fin 7)) (hT : T.card = 4) (hVR : V ≤ R)
    (hVcard : Nat.card V = 4) (h2 : ∀ v ∈ V, v * v = 1)
    (hsupp : ∀ v ∈ V, v ≠ 1 → (v : Equiv.Perm (Fin 7)).support = T) :
    3 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R ≤
      (Finset.univ.filter (fun t : ↥R => t * t = 1 ∧ t ≠ 1 ∧
        ((t : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support.card = 4)).card := by
  classical
  have horbit := sfb_orbit_card_eq_relIndex R V T hT hVcard h2 hsupp
  have hex : ∀ S : Finset (Fin 7), ∃ g : ↥R, (∃ h : ↥R, h • T = S) → g • T = S := by
    intro S
    by_cases h : ∃ g : ↥R, g • T = S
    · exact ⟨Classical.choose h, fun _ => Classical.choose_spec h⟩
    · exact ⟨1, fun hh => absurd hh h⟩
  let pick : Finset (Fin 7) → ↥R := fun S => Classical.choose (hex S)
  have hpick : ∀ S : Finset (Fin 7), (∃ g : ↥R, g • T = S) → pick S • T = S := by
    intro S hS
    exact Classical.choose_spec (hex S) hS
  -- abbreviations to keep coercions under control
  let gG : Finset (Fin 7) → alternatingGroup (Fin 7) := fun S => (pick S : alternatingGroup (Fin 7))
  let X := {v : ↥V // (v : alternatingGroup (Fin 7)) ≠ 1}
  let vG : X → alternatingGroup (Fin 7) := fun v => (v.1 : alternatingGroup (Fin 7))
  let valP : (MulAction.orbit ↥R T) × X → Equiv.Perm (Fin 7) := fun p =>
    ((gG (p.1 : Finset (Fin 7)) : Equiv.Perm (Fin 7))) *
      ((vG p.2 : Equiv.Perm (Fin 7))) *
      (((gG (p.1 : Finset (Fin 7))) : Equiv.Perm (Fin 7)))⁻¹
  let elem : (MulAction.orbit ↥R T) × X → ↥R := fun p =>
    ⟨gG (p.1 : Finset (Fin 7)) * vG p.2 * (gG (p.1 : Finset (Fin 7)))⁻¹,
      R.mul_mem (R.mul_mem (by simpa only [gG] using (pick (p.1 : Finset (Fin 7))).2)
        (hVR (by simpa only [vG] using (p.2.1).2)))
        (R.inv_mem (by simpa only [gG] using (pick (p.1 : Finset (Fin 7))).2))⟩
  have hcoe : ∀ p : (MulAction.orbit ↥R T) × X,
      ((elem p : ↥R) : Equiv.Perm (Fin 7)) = valP p := by
    intro p
    simp only [elem, valP, gG, vG, Subgroup.coe_mul, Subgroup.coe_inv]
  have hvP_supp : ∀ v : X, ((vG v : Equiv.Perm (Fin 7))).support = T := by
    intro v
    exact hsupp (v.1 : alternatingGroup (Fin 7)) v.1.2 v.2
  have hvalP_supp : ∀ p : (MulAction.orbit ↥R T) × X,
      (valP p).support = (p.1 : Finset (Fin 7)) := by
    rintro ⟨⟨S, hS⟩, ⟨v, hv⟩⟩
    have hp := hpick S (MulAction.mem_orbit_iff.mp hS)
    have hv' := hvP_supp ⟨v, hv⟩
    rw [show valP (⟨⟨S, hS⟩, ⟨v, hv⟩⟩ : (MulAction.orbit ↥R T) × X) =
        ((gG S : Equiv.Perm (Fin 7))) * ((vG ⟨v, hv⟩ : Equiv.Perm (Fin 7))) *
          (((gG S) : Equiv.Perm (Fin 7)))⁻¹ from rfl,
      Equiv.Perm.support_conj, hv']
    rw [← sfb_smul_finset_eq_map (g := pick S) T, hp]
  have hconj_inv : ∀ (a b : Equiv.Perm (Fin 7)), b * b = 1 →
      (a * b * a⁻¹) * (a * b * a⁻¹) = 1 := by
    intro a b hb
    have hmul : (a * b * a⁻¹) * (a * b * a⁻¹) = a * (b * b) * a⁻¹ := by group
    rw [hmul, hb, mul_one]
    exact mul_inv_cancel a
  have hvalP_inv : ∀ p : (MulAction.orbit ↥R T) × X, valP p * valP p = 1 := by
    rintro ⟨⟨S, hS⟩, ⟨v, hv⟩⟩
    have hv2 : ((vG ⟨v, hv⟩ : Equiv.Perm (Fin 7))) * ((vG ⟨v, hv⟩ : Equiv.Perm (Fin 7))) = 1 := by
      have h := h2 ((v : ↥V) : alternatingGroup (Fin 7)) v.2
      simp only [vG]
      exact congrArg (fun z : alternatingGroup (Fin 7) => (z : Equiv.Perm (Fin 7))) h
    rw [show valP (⟨⟨S, hS⟩, ⟨v, hv⟩⟩ : (MulAction.orbit ↥R T) × X) =
        ((gG S : Equiv.Perm (Fin 7))) * ((vG ⟨v, hv⟩ : Equiv.Perm (Fin 7))) *
          (((gG S) : Equiv.Perm (Fin 7)))⁻¹ from rfl]
    exact hconj_inv _ _ hv2
  have hvalP_ne : ∀ p : (MulAction.orbit ↥R T) × X, valP p ≠ 1 := by
    rintro ⟨⟨S, hS⟩, ⟨v, hv⟩⟩ hcon
    rw [show valP (⟨⟨S, hS⟩, ⟨v, hv⟩⟩ : (MulAction.orbit ↥R T) × X) =
        ((gG S : Equiv.Perm (Fin 7))) * ((vG ⟨v, hv⟩ : Equiv.Perm (Fin 7))) *
          (((gG S) : Equiv.Perm (Fin 7)))⁻¹ from rfl] at hcon
    have hvP_ne : (vG ⟨v, hv⟩ : Equiv.Perm (Fin 7)) ≠ 1 := fun h => hv (Subtype.ext h)
    apply hvP_ne
    have hv' : (vG ⟨v, hv⟩ : Equiv.Perm (Fin 7)) =
        ((gG S : Equiv.Perm (Fin 7)))⁻¹ *
          ((gG S : Equiv.Perm (Fin 7)) * (vG ⟨v, hv⟩ : Equiv.Perm (Fin 7)) *
            ((gG S : Equiv.Perm (Fin 7)))⁻¹) * (gG S : Equiv.Perm (Fin 7)) := by group
    rw [hv', hcon]
    simp
  have elem_inv : ∀ p : (MulAction.orbit ↥R T) × X, elem p * elem p = 1 := by
    intro p
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, hcoe p]
    exact hvalP_inv p
  have elem_ne : ∀ p : (MulAction.orbit ↥R T) × X, elem p ≠ 1 := by
    intro p hcon
    apply hvalP_ne p
    have h := congrArg (fun z : ↥R => ((z : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) hcon
    simpa only [Subgroup.coe_one, hcoe p] using h
  have elem_card : ∀ p : (MulAction.orbit ↥R T) × X,
      (((elem p : ↥R) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support.card = 4 := by
    intro p
    have hsupp_i : (valP p).support = (p.1 : Finset (Fin 7)) := hvalP_supp p
    rw [hcoe p, hsupp_i]
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp p.1.2
    rw [← hg, Finset.card_smul_finset]
    exact hT
  let θ : (MulAction.orbit ↥R T) × X →
      ↥(Finset.univ.filter (fun t : ↥R => t * t = 1 ∧ t ≠ 1 ∧
        ((t : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support.card = 4)) := fun p =>
    ⟨elem p, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, elem_inv p, elem_ne p, elem_card p⟩⟩
  have hinj : Function.Injective θ := by
    rintro ⟨⟨S, hS⟩, ⟨v, hv⟩⟩ ⟨⟨S', hS'⟩, ⟨v', hv'⟩⟩ heq
    have h1 : elem (⟨⟨S, hS⟩, ⟨v, hv⟩⟩ : (MulAction.orbit ↥R T) × X) =
        elem (⟨⟨S', hS'⟩, ⟨v', hv'⟩⟩ : (MulAction.orbit ↥R T) × X) := by
      have h2' : (θ (⟨⟨S, hS⟩, ⟨v, hv⟩⟩ : (MulAction.orbit ↥R T) × X)).val =
          (θ (⟨⟨S', hS'⟩, ⟨v', hv'⟩⟩ : (MulAction.orbit ↥R T) × X)).val :=
        congrArg Subtype.val heq
      simpa [θ] using h2'
    have h2elem : valP (⟨⟨S, hS⟩, ⟨v, hv⟩⟩ : (MulAction.orbit ↥R T) × X) =
        valP (⟨⟨S', hS'⟩, ⟨v', hv'⟩⟩ : (MulAction.orbit ↥R T) × X) := by
      rw [← hcoe, ← hcoe, h1]
    have hS_eq : S = S' := by
      have h3 : (valP (⟨⟨S, hS⟩, ⟨v, hv⟩⟩ : (MulAction.orbit ↥R T) × X)).support = S := by
        simpa using hvalP_supp (⟨⟨S, hS⟩, ⟨v, hv⟩⟩ : (MulAction.orbit ↥R T) × X)
      have h4 : (valP (⟨⟨S', hS'⟩, ⟨v', hv'⟩⟩ : (MulAction.orbit ↥R T) × X)).support = S' := by
        simpa using hvalP_supp (⟨⟨S', hS'⟩, ⟨v', hv'⟩⟩ : (MulAction.orbit ↥R T) × X)
      rw [← h3, ← h4, h2elem]
    subst hS_eq
    have hv_eq : (v : ↥V) = (v' : ↥V) := by
      have h3 : (vG ⟨v, hv⟩ : Equiv.Perm (Fin 7)) = (vG ⟨v', hv'⟩ : Equiv.Perm (Fin 7)) := by
        have h4 := h2elem
        simp only [valP, gG] at h4
        exact sfb_conj_cancel h4
      have h3' : ((v : ↥V) : alternatingGroup (Fin 7)) =
          ((v' : ↥V) : alternatingGroup (Fin 7)) := by
        apply Subtype.ext
        simpa only [vG] using h3
      exact Subtype.ext h3'
    exact Prod.ext (Subtype.ext rfl) (Subtype.ext hv_eq)
  have hXcard : Nat.card X = 3 := by
    have hiff : ∀ v : ↥V, (v : alternatingGroup (Fin 7)) ≠ 1 ↔ v ≠ 1 := by
      intro v
      exact ⟨fun h hv => h (by rw [hv]; rfl), fun hv h => hv (Subtype.ext h)⟩
    have hsub : Nat.card {v : ↥V // v ≠ 1} = Nat.card ↥V - 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have hfilter : (Finset.univ.filter (fun x : ↥V => x ≠ 1)) =
          (Finset.univ : Finset ↥V).erase 1 := by
        ext x; simp [Finset.mem_erase]
      rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ (1 : ↥V)), Finset.card_univ,
        Nat.card_eq_fintype_card]
    rw [show Nat.card X = Nat.card {v : ↥V // v ≠ 1} from
      Nat.card_congr (Equiv.subtypeEquivRight hiff), hsub, hVcard]
  have hkey : Nat.card ((MulAction.orbit ↥R T) × X) ≤
      (Finset.univ.filter (fun t : ↥R => t * t = 1 ∧ t ≠ 1 ∧
        ((t : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support.card = 4)).card := by
    have h := Nat.card_le_card_of_injective θ hinj
    have h2 : Nat.card ↥(Finset.univ.filter (fun t : ↥R => t * t = 1 ∧ t ≠ 1 ∧
        ((t : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support.card = 4)) =
        (Finset.univ.filter (fun t : ↥R => t * t = 1 ∧ t ≠ 1 ∧
        ((t : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support.card = 4)).card := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_coe _
    rwa [h2] at h
  calc 3 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R
      = Nat.card ((MulAction.orbit ↥R T) × X) := by
        rw [Nat.card_prod, hXcard, horbit]; ring
    _ ≤ _ := hkey

/-- `2 * [R : N_R(V)]` three-cycles lie in `R`. -/
lemma sfb_two_mul_relIndex_le_threecycles (R V : Subgroup (alternatingGroup (Fin 7)))
    [Fintype ↥R] (T : Finset (Fin 7)) (x : alternatingGroup (Fin 7)) (hT : T.card = 4)
    (hVcard : Nat.card V = 4) (h2 : ∀ v ∈ V, v * v = 1)
    (hsupp : ∀ v ∈ V, v ≠ 1 → (v : Equiv.Perm (Fin 7)).support = T)
    (hxR : x ∈ R) (hx3 : orderOf x = 3)
    (hxsupp : (x : Equiv.Perm (Fin 7)).support = Finset.univ \ T) :
    2 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R ≤
      (Finset.univ.filter (fun y : ↥R => orderOf y = 3 ∧
        ((y : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support.card = 3)).card := by
  classical
  have horbit := sfb_orbit_card_eq_relIndex R V T hT hVcard h2 hsupp
  have hex : ∀ S : Finset (Fin 7), ∃ g : ↥R, (∃ h : ↥R, h • T = S) → g • T = S := by
    intro S
    by_cases h : ∃ g : ↥R, g • T = S
    · exact ⟨Classical.choose h, fun _ => Classical.choose_spec h⟩
    · exact ⟨1, fun hh => absurd hh h⟩
  let pick : Finset (Fin 7) → ↥R := fun S => Classical.choose (hex S)
  have hpick : ∀ S : Finset (Fin 7), (∃ g : ↥R, g • T = S) → pick S • T = S := by
    intro S hS
    exact Classical.choose_spec (hex S) hS
  let cyc : Bool → alternatingGroup (Fin 7) := fun b => if b then x ^ 2 else x
  have hcycf : cyc false = x := by simp [cyc]
  have hcyct : cyc true = x ^ 2 := by simp [cyc]
  have hxne1 : x ≠ 1 := by
    intro hcon
    rw [hcon] at hx3
    simp at hx3
  have hxne_x2 : x ≠ x ^ 2 := by
    intro hcon
    exact hxne1 (by
      have h1 : x⁻¹ * x = x⁻¹ * x ^ 2 := congrArg (fun z => x⁻¹ * z) hcon
      rw [inv_mul_cancel] at h1
      have h2 : x⁻¹ * x ^ 2 = x := by rw [pow_two, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [h2] at h1
      exact h1.symm)
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hx2inv : (x ^ 2 : alternatingGroup (Fin 7)) = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hx3']
  have hx3P : ((x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hx3', Subgroup.coe_one]
  have hx2P : (((x ^ 2 : alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) ^ 3 = 1 := by
    rw [hx2inv, Subgroup.coe_inv, inv_pow, hx3P, inv_one]
  have hcycsupp : ∀ b : Bool,
      ((cyc b : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support = Finset.univ \ T := by
    intro b
    cases b
    · rw [hcycf]; exact hxsupp
    · rw [hcyct, hx2inv, Subgroup.coe_inv, Equiv.Perm.support_inv, hxsupp]
  have hcyc3P : ∀ b : Bool,
      ((cyc b : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ^ 3 = 1 := by
    intro b
    cases b
    · rw [hcycf]; exact hx3P
    · rw [hcyct]; exact hx2P
  have hcycne1 : ∀ b : Bool, cyc b ≠ 1 := by
    intro b
    cases b
    · rw [hcycf]; exact hxne1
    · rw [hcyct]
      intro hcon
      apply hxne1
      calc x = x * 1 := (mul_one x).symm
        _ = x * x ^ 2 := by rw [hcon]
        _ = x ^ 3 := by rw [← pow_succ']
        _ = 1 := hx3'
  have hcycne1P : ∀ b : Bool, ((cyc b : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ≠ 1 :=
    fun b hcon => hcycne1 b (Subtype.ext hcon)
  have hcyc_inj : Function.Injective cyc := by
    intro a b hab
    cases a <;> cases b <;> try rfl
    · exact absurd (by rw [← hcyct, ← hcycf]; exact hab) hxne_x2
    · exact absurd (by rw [← hcyct, ← hcycf]; exact hab.symm) hxne_x2
  have hcycR : ∀ b : Bool, cyc b ∈ R := by
    intro b
    cases b
    · rw [hcycf]; exact hxR
    · rw [hcyct]; exact R.mul_mem hxR hxR
  let gG : Finset (Fin 7) → alternatingGroup (Fin 7) := fun S => (pick S : alternatingGroup (Fin 7))
  let valP : (MulAction.orbit ↥R T) × Bool → Equiv.Perm (Fin 7) := fun p =>
    ((gG (p.1 : Finset (Fin 7)) : Equiv.Perm (Fin 7))) *
      ((cyc p.2 : Equiv.Perm (Fin 7))) *
      (((gG (p.1 : Finset (Fin 7))) : Equiv.Perm (Fin 7)))⁻¹
  let elem : (MulAction.orbit ↥R T) × Bool → ↥R := fun p =>
    ⟨gG (p.1 : Finset (Fin 7)) * cyc p.2 * (gG (p.1 : Finset (Fin 7)))⁻¹,
      R.mul_mem (R.mul_mem (by simpa only [gG] using (pick (p.1 : Finset (Fin 7))).2)
        (hcycR p.2))
        (R.inv_mem (by simpa only [gG] using (pick (p.1 : Finset (Fin 7))).2))⟩
  have hcoe : ∀ p : (MulAction.orbit ↥R T) × Bool,
      ((elem p : ↥R) : Equiv.Perm (Fin 7)) = valP p := by
    intro p
    simp only [elem, valP, gG, Subgroup.coe_mul, Subgroup.coe_inv]
  have hvalP_supp : ∀ p : (MulAction.orbit ↥R T) × Bool,
      (valP p).support = Finset.univ \ (p.1 : Finset (Fin 7)) := by
    rintro ⟨⟨S, hS⟩, b⟩
    have hp := hpick S (MulAction.mem_orbit_iff.mp hS)
    have hc := hcycsupp b
    rw [show valP (⟨⟨S, hS⟩, b⟩ : (MulAction.orbit ↥R T) × Bool) =
        ((gG S : Equiv.Perm (Fin 7))) * ((cyc b : Equiv.Perm (Fin 7))) *
          (((gG S) : Equiv.Perm (Fin 7)))⁻¹ from rfl,
      Equiv.Perm.support_conj, hc, sfb_map_sdiff_univ,
      ← sfb_smul_finset_eq_map (g := pick S) T, hp]
  have hval3 : ∀ p : (MulAction.orbit ↥R T) × Bool, (valP p) ^ 3 = 1 := by
    rintro ⟨⟨S, hS⟩, b⟩
    rw [show valP (⟨⟨S, hS⟩, b⟩ : (MulAction.orbit ↥R T) × Bool) =
        ((gG S : Equiv.Perm (Fin 7))) * ((cyc b : Equiv.Perm (Fin 7))) *
          (((gG S) : Equiv.Perm (Fin 7)))⁻¹ from rfl]
    have h3' : (((gG S : Equiv.Perm (Fin 7))) * ((cyc b : Equiv.Perm (Fin 7))) *
        (((gG S) : Equiv.Perm (Fin 7)))⁻¹) ^ 3 =
        (gG S : Equiv.Perm (Fin 7)) * ((cyc b : Equiv.Perm (Fin 7))) ^ 3 *
          ((gG S : Equiv.Perm (Fin 7)))⁻¹ := by
      rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]
    rw [h3', hcyc3P b, mul_one]
    exact mul_inv_cancel _
  have hval_ne : ∀ p : (MulAction.orbit ↥R T) × Bool, valP p ≠ 1 := by
    rintro ⟨⟨S, hS⟩, b⟩ hcon
    rw [show valP (⟨⟨S, hS⟩, b⟩ : (MulAction.orbit ↥R T) × Bool) =
        ((gG S : Equiv.Perm (Fin 7))) * ((cyc b : Equiv.Perm (Fin 7))) *
          (((gG S) : Equiv.Perm (Fin 7)))⁻¹ from rfl] at hcon
    apply hcycne1P b
    have hc' : (cyc b : Equiv.Perm (Fin 7)) = ((gG S : Equiv.Perm (Fin 7)))⁻¹ *
        ((gG S : Equiv.Perm (Fin 7)) * (cyc b : Equiv.Perm (Fin 7)) *
          ((gG S : Equiv.Perm (Fin 7)))⁻¹) * (gG S : Equiv.Perm (Fin 7)) := by group
    rw [hc', hcon]
    simp
  have hval_order : ∀ p : (MulAction.orbit ↥R T) × Bool, orderOf (valP p) = 3 := by
    intro p
    have hdvd : orderOf (valP p) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr (hval3 p)
    rcases Nat.dvd_prime (by norm_num : Nat.Prime 3) |>.mp hdvd with h' | h'
    · exact absurd (orderOf_eq_one_iff.mp h') (hval_ne p)
    · exact h'
  have hval_card : ∀ p : (MulAction.orbit ↥R T) × Bool, (valP p).support.card = 3 := by
    rintro ⟨⟨S, hS⟩, b⟩
    have hsupp_i : (valP (⟨⟨S, hS⟩, b⟩ : (MulAction.orbit ↥R T) × Bool)).support =
        Finset.univ \ S := by
      simpa using hvalP_supp (⟨⟨S, hS⟩, b⟩ : (MulAction.orbit ↥R T) × Bool)
    rw [hsupp_i]
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hS
    have hScard : S.card = 4 := by rw [← hg, Finset.card_smul_finset]; exact hT
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hScard]
  have elem_order : ∀ p : (MulAction.orbit ↥R T) × Bool, orderOf (elem p) = 3 := by
    intro p
    rw [← Subgroup.orderOf_coe (elem p), ← Subgroup.orderOf_coe ((elem p : ↥R) :
      alternatingGroup (Fin 7)), hcoe p]
    exact hval_order p
  have elem_card : ∀ p : (MulAction.orbit ↥R T) × Bool,
      (((elem p : ↥R) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support.card = 3 := by
    intro p
    have hsupp_i : (valP p).support.card = 3 := hval_card p
    rw [hcoe p, hsupp_i]
  let θ : (MulAction.orbit ↥R T) × Bool →
      ↥(Finset.univ.filter (fun y : ↥R => orderOf y = 3 ∧
        ((y : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support.card = 3)) := fun p =>
    ⟨elem p, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, elem_order p, elem_card p⟩⟩
  have hinj : Function.Injective θ := by
    rintro ⟨⟨S, hS⟩, b⟩ ⟨⟨S', hS'⟩, b'⟩ heq
    have h1 : elem (⟨⟨S, hS⟩, b⟩ : (MulAction.orbit ↥R T) × Bool) =
        elem (⟨⟨S', hS'⟩, b'⟩ : (MulAction.orbit ↥R T) × Bool) := by
      have h2' : (θ (⟨⟨S, hS⟩, b⟩ : (MulAction.orbit ↥R T) × Bool)).val =
          (θ (⟨⟨S', hS'⟩, b'⟩ : (MulAction.orbit ↥R T) × Bool)).val :=
        congrArg Subtype.val heq
      simpa [θ] using h2'
    have h2elem : valP (⟨⟨S, hS⟩, b⟩ : (MulAction.orbit ↥R T) × Bool) =
        valP (⟨⟨S', hS'⟩, b'⟩ : (MulAction.orbit ↥R T) × Bool) := by
      rw [← hcoe, ← hcoe, h1]
    have hS_eq : S = S' := by
      have h3 : (valP (⟨⟨S, hS⟩, b⟩ : (MulAction.orbit ↥R T) × Bool)).support = Finset.univ \ S := by
        simpa using hvalP_supp (⟨⟨S, hS⟩, b⟩ : (MulAction.orbit ↥R T) × Bool)
      have h4 : (valP (⟨⟨S', hS'⟩, b'⟩ : (MulAction.orbit ↥R T) × Bool)).support =
          Finset.univ \ S' := by
        simpa using hvalP_supp (⟨⟨S', hS'⟩, b'⟩ : (MulAction.orbit ↥R T) × Bool)
      have hs : Finset.univ \ S = Finset.univ \ S' := by rw [← h3, ← h4, h2elem]
      have := (Finset.sdiff_eq_sdiff_iff_inter_eq_inter (s := Finset.univ)).mp hs
      simpa using this
    subst hS_eq
    have hcyc_eq : cyc b = cyc b' := by
      apply Subtype.ext
      have h3 : ((gG S : Equiv.Perm (Fin 7))) * ((cyc b : Equiv.Perm (Fin 7))) *
          (((gG S) : Equiv.Perm (Fin 7)))⁻¹ =
          ((gG S : Equiv.Perm (Fin 7))) * ((cyc b' : Equiv.Perm (Fin 7))) *
            (((gG S) : Equiv.Perm (Fin 7)))⁻¹ := by
        have h4 := h2elem
        simp only [valP, gG] at h4
        exact h4
      exact sfb_conj_cancel h3
    have hii : b = b' := hcyc_inj hcyc_eq
    subst hii
    exact Prod.ext (Subtype.ext rfl) rfl
  have hkey : Nat.card ((MulAction.orbit ↥R T) × Bool) ≤
      (Finset.univ.filter (fun y : ↥R => orderOf y = 3 ∧
        ((y : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support.card = 3)).card := by
    have h := Nat.card_le_card_of_injective θ hinj
    have h2 : Nat.card ↥(Finset.univ.filter (fun y : ↥R => orderOf y = 3 ∧
        ((y : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support.card = 3)) =
        (Finset.univ.filter (fun y : ↥R => orderOf y = 3 ∧
        ((y : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support.card = 3)).card := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_coe _
    rwa [h2] at h
  calc 2 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R
      = Nat.card ((MulAction.orbit ↥R T) × Bool) := by
        rw [Nat.card_prod, show Nat.card Bool = 2 from by simp, horbit]; ring
    _ ≤ _ := hkey

/-- **The fixed-point count.**  If `W` is a set of involutions of `R` with support of size `4`
and `C` a disjoint set of `3`-cycles, then `|R| ≥ 7 + 3|W| + 4|C|`. -/
lemma sfb_card_le_seven_add (R : Subgroup (alternatingGroup (Fin 7))) [Fintype ↥R]
    (htrans : MulAction.IsPretransitive ↥R (Fin 7)) (W C : Finset ↥R)
    (hW : ∀ t ∈ W, ((t : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support.card = 4)
    (hC : ∀ y ∈ C, orderOf y = 3 ∧
      ((y : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support.card = 3)
    (hd : Disjoint W C) :
    7 + 3 * W.card + 4 * C.card ≤ Nat.card ↥R := by
  classical
  have hsum : (∑ g : ↥R, Fintype.card (MulAction.fixedBy (Fin 7) g)) = Fintype.card ↥R :=
    sum_fixedBy_pretransitive ↥R (Fin 7)
  have hWsum : (∑ t ∈ W, Fintype.card (MulAction.fixedBy (Fin 7) t)) = W.card * 3 := by
    rw [Finset.sum_congr rfl (fun t ht => by rw [sfb_card_fixedBy_eq R t, hW t ht]),
      Finset.sum_const]
    rfl
  have hCsum : (∑ y ∈ C, Fintype.card (MulAction.fixedBy (Fin 7) y)) = C.card * 4 := by
    rw [Finset.sum_congr rfl (fun y hy => by rw [sfb_card_fixedBy_eq R y, (hC y hy).2]),
      Finset.sum_const]
    rfl
  have hfix1 : Fintype.card (MulAction.fixedBy (Fin 7) (1 : ↥R)) = 7 := by
    rw [sfb_card_fixedBy_eq R 1]
    simp
  have hnotW : (1 : ↥R) ∉ W := fun hcon => by
    have := hW 1 hcon
    simp at this
  rw [← Finset.insert_erase (Finset.mem_univ (1 : ↥R)),
    Finset.sum_insert (Finset.notMem_erase _ _)] at hsum
  have hsubset : W ∪ C ⊆ (Finset.univ : Finset ↥R).erase 1 := by
    intro t ht
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [Finset.mem_union] at ht
    rintro rfl
    rcases ht with ht | ht
    · exact hnotW ht
    · exact absurd (hC 1 ht).1 (by simp)
  have hmono : (∑ g ∈ W ∪ C, Fintype.card (MulAction.fixedBy (Fin 7) g)) ≤
      ∑ g ∈ (Finset.univ : Finset ↥R).erase 1,
        Fintype.card (MulAction.fixedBy (Fin 7) g) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Nat.zero_le _)
  have hunion : (∑ g ∈ W ∪ C, Fintype.card (MulAction.fixedBy (Fin 7) g)) =
      (∑ g ∈ W, Fintype.card (MulAction.fixedBy (Fin 7) g)) +
        ∑ g ∈ C, Fintype.card (MulAction.fixedBy (Fin 7) g) :=
    Finset.sum_union hd
  have hfinal : 7 + 3 * W.card + 4 * C.card ≤ Fintype.card ↥R := by
    have h1 : 3 * W.card + 4 * C.card ≤
        ∑ g ∈ (Finset.univ : Finset ↥R).erase 1,
          Fintype.card (MulAction.fixedBy (Fin 7) g) := by
      have h2 : (∑ g ∈ W ∪ C, Fintype.card (MulAction.fixedBy (Fin 7) g)) =
          W.card * 3 + C.card * 4 := by
        rw [hunion, hWsum, hCsum]
      rw [h2] at hmono
      omega
    rw [hfix1] at hsum
    omega
  rw [Nat.card_eq_fintype_card]
  exact hfinal

theorem sum_fixedBy_lower_bound (R V : Subgroup (alternatingGroup (Fin 7))) (T : Finset (Fin 7))
    (hT : T.card = 4) (hVR : V ≤ R) (hVcard : Nat.card V = 4) (h2 : ∀ v ∈ V, v * v = 1)
    (hsupp : ∀ v ∈ V, v ≠ 1 → (v : Equiv.Perm (Fin 7)).support = T)
    (hx : ∃ x : alternatingGroup (Fin 7), x ∈ R ∧ orderOf x = 3 ∧
      (x : Equiv.Perm (Fin 7)).support = Finset.univ \ T)
    (htrans : MulAction.IsPretransitive ↥R (Fin 7)) :
    17 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R + 7 ≤
      Nat.card ↥R := by
  classical
  haveI : Fintype ↥R := Fintype.ofFinite ↥R
  obtain ⟨x, hxR, hx3, hxsupp⟩ := hx
  have h3n := sfb_three_mul_relIndex_le_involutions R V T hT hVR hVcard h2 hsupp
  have h2n := sfb_two_mul_relIndex_le_threecycles R V T x hT hVcard h2 hsupp hxR hx3 hxsupp
  set W : Finset ↥R := Finset.univ.filter (fun t : ↥R => t * t = 1 ∧ t ≠ 1 ∧
    ((t : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support.card = 4) with hW
  set C : Finset ↥R := Finset.univ.filter (fun y : ↥R => orderOf y = 3 ∧
    ((y : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support.card = 3) with hC
  have hWcard : 3 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R
      ≤ W.card := by rw [hW]; exact h3n
  have hCcard : 2 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R
      ≤ C.card := by rw [hC]; exact h2n
  have hd : Disjoint W C := by
    rw [Finset.disjoint_left]
    intro t htW htC
    rw [hW, Finset.mem_filter] at htW
    rw [hC, Finset.mem_filter] at htC
    omega
  have hsum := sfb_card_le_seven_add R htrans W C
    (fun t ht => by rw [hW, Finset.mem_filter] at ht; exact ht.2.2.2)
    (fun y hy => by rw [hC, Finset.mem_filter] at hy; exact hy.2) hd
  have hstep : 7 + 3 * (3 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R) +
      4 * (2 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R)
      ≤ 7 + 3 * W.card + 4 * C.card := by
    have h1 : 3 * (3 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R)
        ≤ 3 * W.card := Nat.mul_le_mul_left 3 hWcard
    have h2'' : 4 * (2 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R)
        ≤ 4 * C.card := Nat.mul_le_mul_left 4 hCcard
    omega
  have hfinal : 7 + 3 * (3 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R) +
      4 * (2 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R)
      ≤ Nat.card ↥R := le_trans hstep hsum
  have harith : 17 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R + 7
      = 7 + 3 * (3 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R) +
        4 * (2 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R) := by
    ring
  rwa [harith]

end Work.CORE4.A7FGB
