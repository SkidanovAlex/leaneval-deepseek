import Mathlib
import Submission.Work.CORE4.A7FGB.involution_support_mem

open scoped Pointwise

set_option linter.style.haveILetI false

/-!
# `three_cycles_ge`

Let `R ≤ A₇`, let `V ≤ R` be a four-group all of whose non-identity elements are involutions
with support the four-element set `T`, and let `x ∈ R` be an element of order `3` with support
exactly `univ \ T` (a three-cycle on the complement of `T`).

The number of `R`-conjugates of `V` is the index `[R : R ∩ N(V)]`.  Each conjugate of `V` is
the (unique) four-group whose non-identity elements are the three double transpositions of a
four-element set `T'` in the `↥R`-orbit of `T`; distinct conjugates correspond to distinct
four-sets.  For each such `T'` the two three-cycles supported on the complement of `T'` are
exactly the two `R`-conjugates of `x` by an element mapping `T` to `T'`, so the `R`-elements
of order `3` whose support has cardinality `3` contain two elements for each conjugate of `V`.
This gives the inequality

`2 * [R : R ∩ N(V)] ≤ #{y ∈ R : orderOf y = 3, support.card = 3}`.

The identification of `MulAction.stabilizer ↥R T` with `R ∩ N(V)` is the content of
`stabilizer_orbit_eq_normalizer`; the doubling count is `two_mul_orbit_le`.
-/

namespace Work.CORE4.A7FGB

open Equiv

/-! ## Auxiliary lemmas -/

/-- The pointwise action of a permutation on a `Finset` is `Finset.map` along the permutation. -/
private lemma map_toEmbedding_eq_smul (e : Equiv.Perm (Fin 7)) (T : Finset (Fin 7)) :
    Finset.map e.toEmbedding T = e • T := by
  ext x
  rw [Finset.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Finset.smul_mem_smul_finset_iff e).mpr hy
  · intro hx
    refine ⟨e.symm x, ?_, ?_⟩
    · exact (Finset.smul_mem_smul_finset_iff e).mp (by simpa using hx)
    · simp

/-- The image of the complement of `T` under a permutation is the complement of the image. -/
private lemma map_toEmbedding_sdiff_univ (e : Equiv.Perm (Fin 7)) (T : Finset (Fin 7)) :
    Finset.map e.toEmbedding (Finset.univ \ T) = Finset.univ \ (e • T) := by
  rw [Finset.map_sdiff, Finset.map_univ_equiv, map_toEmbedding_eq_smul]

/-- Conjugation of an element of `A₇` acts on its support by applying the conjugating
permutation. -/
private lemma support_conj_coe (a w : alternatingGroup (Fin 7)) :
    ((a * w * a⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support =
      Finset.map (Equiv.toEmbedding (a : Equiv.Perm (Fin 7)))
        (w : Equiv.Perm (Fin 7)).support := by
  have hcoe : ((a * w * a⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
      = (a : Equiv.Perm (Fin 7)) * (w : Equiv.Perm (Fin 7)) *
        ((a : Equiv.Perm (Fin 7)))⁻¹ := rfl
  rw [hcoe, Equiv.Perm.support_conj]

/-- If `g ∈ A₇` fixes the four-element set `T` setwise, then it normalizes any subgroup `V` of
order four whose non-identity elements all have support exactly `T`: conjugation by `g` carries
each such involution to an involution with the same support, hence into `V`. -/
private lemma mem_normalizer_of_smul_eq
    (V : Subgroup (alternatingGroup (Fin 7))) (T : Finset (Fin 7))
    (hT : T.card = 4) (hVcard : Nat.card V = 4) (h2 : ∀ v ∈ V, v * v = 1)
    (hsupp : ∀ v ∈ V, v ≠ 1 → (v : Equiv.Perm (Fin 7)).support = T)
    (g : alternatingGroup (Fin 7)) (hg : g • T = T) :
    g ∈ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7))) := by
  have key : ∀ a : alternatingGroup (Fin 7), a • T = T → ∀ y ∈ V, a * y * a⁻¹ ∈ V := by
    intro a ha y hy
    rcases eq_or_ne y 1 with rfl | hy1
    · simp
    · have hyy : y * y = 1 := h2 y hy
      have hys : (y : Equiv.Perm (Fin 7)).support = T := hsupp y hy hy1
      have hcs : ((a * y * a⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).support = T := by
        rw [support_conj_coe, hys, map_toEmbedding_eq_smul]
        exact ha
      have hcc : (a * y * a⁻¹) * (a * y * a⁻¹) = 1 := by
        rw [show (a * y * a⁻¹) * (a * y * a⁻¹) = a * (y * y) * a⁻¹ from by group, hyy]
        group
      have hc1 : (a * y * a⁻¹ : alternatingGroup (Fin 7)) ≠ 1 := by
        intro h0
        refine hy1 ?_
        have h1 : a⁻¹ * (a * y * a⁻¹) * a = y := by group
        rw [h0] at h1
        simpa using h1.symm
      exact involution_support_mem V T hT hVcard h2 hsupp (a * y * a⁻¹) hcc hc1 hcs
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    exact key g hg w hw
  · intro hw
    have hg' : g⁻¹ • T = T := by
      have h : g⁻¹ • (g • T) = g⁻¹ • T := congrArg (fun s => g⁻¹ • s) hg
      rw [← mul_smul, inv_mul_cancel, one_smul] at h
      exact h.symm
    have h : g⁻¹ * (g * w * g⁻¹) * (g⁻¹)⁻¹ ∈ V := key g⁻¹ hg' (g * w * g⁻¹) hw
    have heq : g⁻¹ * (g * w * g⁻¹) * (g⁻¹)⁻¹ = w := by group
    rwa [heq] at h

/-- Conversely, an element of `A₇` normalizing `V` fixes the common support `T` of the
non-identity elements of `V` setwise. -/
private lemma smul_eq_of_mem_normalizer
    (V : Subgroup (alternatingGroup (Fin 7))) (T : Finset (Fin 7))
    (hVcard : Nat.card V = 4)
    (hsupp : ∀ v ∈ V, v ≠ 1 → (v : Equiv.Perm (Fin 7)).support = T)
    (g : alternatingGroup (Fin 7))
    (hg : g ∈ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))) :
    g • T = T := by
  have hVne : V ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hVcard
    exact absurd hVcard (by norm_num)
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
  have hwV : (w : alternatingGroup (Fin 7)) ∈ V := w.2
  have hw1 : (w : alternatingGroup (Fin 7)) ≠ 1 := fun h => hw (Subtype.ext (by simpa using h))
  have hmem : g * (w : alternatingGroup (Fin 7)) * g⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp hg (w : alternatingGroup (Fin 7))).mp hwV
  have hc1 : (g * (w : alternatingGroup (Fin 7)) * g⁻¹ : alternatingGroup (Fin 7)) ≠ 1 := by
    intro h0
    refine hw1 ?_
    have h1 : g⁻¹ * (g * (w : alternatingGroup (Fin 7)) * g⁻¹) * g
        = (w : alternatingGroup (Fin 7)) := by group
    rw [h0] at h1
    simpa using h1.symm
  have hcs : ((g * (w : alternatingGroup (Fin 7)) * g⁻¹ : alternatingGroup (Fin 7))
      : Equiv.Perm (Fin 7)).support = T :=
    hsupp (g * (w : alternatingGroup (Fin 7)) * g⁻¹) hmem hc1
  rw [support_conj_coe, hsupp (w : alternatingGroup (Fin 7)) hwV hw1,
    map_toEmbedding_eq_smul] at hcs
  exact hcs

/-- The stabilizer of the four-set `T` in the action of `↥R` on `Finset (Fin 7)` is exactly
`R ∩ N(V)`. -/
private lemma stabilizer_orbit_eq_normalizer
    (R V : Subgroup (alternatingGroup (Fin 7))) (T : Finset (Fin 7))
    (hT : T.card = 4) (hVcard : Nat.card V = 4) (h2 : ∀ v ∈ V, v * v = 1)
    (hsupp : ∀ v ∈ V, v ≠ 1 → (v : Equiv.Perm (Fin 7)).support = T) :
    MulAction.stabilizer ↥R T =
      (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).subgroupOf R := by
  refine le_antisymm ?_ ?_
  · intro r hr
    rw [MulAction.mem_stabilizer_iff] at hr
    rw [Subgroup.mem_subgroupOf]
    exact ⟨r.2, mem_normalizer_of_smul_eq V T hT hVcard h2 hsupp
      (r : alternatingGroup (Fin 7)) hr⟩
  · intro r hr
    rw [Subgroup.mem_subgroupOf] at hr
    rw [MulAction.mem_stabilizer_iff]
    exact smul_eq_of_mem_normalizer V T hVcard hsupp
      (r : alternatingGroup (Fin 7)) hr.2

/-- The number of `R`-conjugates of `V` (the index of `R ∩ N(V)` in `R`) is the size of the
orbit of the four-set `T` under `↥R`. -/
private lemma relIndex_eq_card_orbit
    (R V : Subgroup (alternatingGroup (Fin 7))) (T : Finset (Fin 7))
    (hT : T.card = 4) (hVcard : Nat.card V = 4) (h2 : ∀ v ∈ V, v * v = 1)
    (hsupp : ∀ v ∈ V, v ≠ 1 → (v : Equiv.Perm (Fin 7)).support = T) :
    (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R =
      Nat.card (MulAction.orbit ↥R T) := by
  have hstab := stabilizer_orbit_eq_normalizer R V T hT hVcard h2 hsupp
  change ((R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).subgroupOf R).index
      = Nat.card (MulAction.orbit ↥R T)
  rw [← hstab, Subgroup.index_eq_card]
  exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (G := ↥R) T).symm

/-- The doubling step: for every `R`-conjugate `V ^ r` of `V` the two three-cycles supported on
the complement of the four-set `T ^ r` lie in `R`. -/
private lemma two_mul_orbit_le_local
    (R : Subgroup (alternatingGroup (Fin 7))) (x : alternatingGroup (Fin 7))
    (T : Finset (Fin 7)) (hT : T.card = 4) (hxR : x ∈ R) (hx3 : orderOf x = 3)
    (hxsupp : (x : Equiv.Perm (Fin 7)).support = Finset.univ \ T) :
    2 * Nat.card (MulAction.orbit ↥R T) ≤
      Nat.card {y : ↥R // orderOf y = 3 ∧ (y : Equiv.Perm (Fin 7)).support.card = 3} := by
  classical
  haveI : Fintype ↥(MulAction.orbit ↥R T) := Fintype.ofFinite _
  -- the element `x` as an element of `R`
  let xR : ↥R := ⟨x, hxR⟩
  -- a choice, for each element `T'` of the orbit, of `r` with `r • T = T'`
  let rp : ↥(MulAction.orbit ↥R T) → ↥R :=
    fun p => Classical.choose (MulAction.mem_orbit_iff.mp p.2)
  have hrp : ∀ p : ↥(MulAction.orbit ↥R T), rp p • T = p.1 :=
    fun p => Classical.choose_spec (MulAction.mem_orbit_iff.mp p.2)
  -- the conjugate of `x` by the chosen representative
  let g : ↥(MulAction.orbit ↥R T) → alternatingGroup (Fin 7) :=
    fun p => (rp p : alternatingGroup (Fin 7)) * (xR : alternatingGroup (Fin 7)) *
      (rp p : alternatingGroup (Fin 7))⁻¹
  have hgmem : ∀ p, g p ∈ R := fun p =>
    R.mul_mem (R.mul_mem (rp p).2 xR.2) (R.inv_mem (rp p).2)
  let cR : ↥(MulAction.orbit ↥R T) → ↥R := fun p => ⟨g p, hgmem p⟩
  have hcoeeq : ∀ p, (((cR p)⁻¹ : ↥R) : Equiv.Perm (Fin 7))
      = (((cR p : ↥R) : Equiv.Perm (Fin 7)))⁻¹ := by
    intro p; rfl
  -- `T'` has cardinality `4` for every `T'` in the orbit
  have hpcard : ∀ p : ↥(MulAction.orbit ↥R T), p.1.card = 4 := by
    intro p
    have h1 : (rp p • T).card = p.1.card := by rw [hrp p]
    have h2 : (rp p • T).card = 4 := by
      show (((rp p : ↥R) : Equiv.Perm (Fin 7)) • T).card = 4
      rw [← map_toEmbedding_eq_smul ((rp p : ↥R) : Equiv.Perm (Fin 7)) T, Finset.card_map, hT]
    omega
  -- the support of the conjugate is the complement of `T'`
  have hsuppc : ∀ p, ((cR p : ↥R) : Equiv.Perm (Fin 7)).support = Finset.univ \ p.1 := by
    intro p
    have hcoe : ((cR p : ↥R) : Equiv.Perm (Fin 7)) =
        ((rp p : alternatingGroup (Fin 7)) * (xR : alternatingGroup (Fin 7)) *
          (rp p : alternatingGroup (Fin 7))⁻¹ : alternatingGroup (Fin 7)) := rfl
    rw [hcoe, support_conj_coe (rp p : alternatingGroup (Fin 7)) (xR : alternatingGroup (Fin 7)),
      hxsupp, map_toEmbedding_sdiff_univ]
    exact congrArg (fun s => Finset.univ \ s)
      (show (((rp p : ↥R) : Equiv.Perm (Fin 7)) • T) = p.1 from hrp p)
  have hcardc : ∀ p, ((cR p : ↥R) : Equiv.Perm (Fin 7)).support.card = 3 := by
    intro p
    rw [hsuppc p, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      hpcard p]
  -- the conjugates have order `3`
  have hordan : ∀ p, orderOf (g p) = 3 := by
    intro p
    have hsem : SemiconjBy (rp p : alternatingGroup (Fin 7))
        (xR : alternatingGroup (Fin 7)) (g p) := by
      rw [SemiconjBy]
      show (rp p : alternatingGroup (Fin 7)) * (xR : alternatingGroup (Fin 7)) =
        ((rp p : alternatingGroup (Fin 7)) * (xR : alternatingGroup (Fin 7)) *
          (rp p : alternatingGroup (Fin 7))⁻¹) * (rp p : alternatingGroup (Fin 7))
      group
    rw [← SemiconjBy.orderOf_eq (rp p : alternatingGroup (Fin 7)) hsem]
    exact hx3
  have hordc : ∀ p, orderOf (cR p) = 3 := by
    intro p
    rw [← Subgroup.orderOf_coe (cR p)]
    exact hordan p
  -- different orbit elements give conjugates with different supports
  have hcRinj : Function.Injective cR := by
    intro p q h
    have h1 : ((cR p : ↥R) : Equiv.Perm (Fin 7)).support
        = ((cR q : ↥R) : Equiv.Perm (Fin 7)).support := by rw [h]
    rw [hsuppc p, hsuppc q] at h1
    apply Subtype.ext
    apply Finset.ext
    intro y
    have h2 := congrArg (fun s : Finset (Fin 7) => y ∈ s) h1
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at h2
    exact not_iff_not.mp (iff_of_eq h2)
  have hinv : Function.Injective (fun p : ↥(MulAction.orbit ↥R T) => (cR p)⁻¹) :=
    fun p q h => hcRinj (inv_injective h)
  set Or : Finset ↥R := Finset.univ.image cR with hOrDef
  set Or2 : Finset ↥R := Finset.univ.image (fun p : ↥(MulAction.orbit ↥R T) => (cR p)⁻¹)
    with hOr2Def
  have hOr : Or.card = Nat.card ↥(MulAction.orbit ↥R T) := by
    rw [hOrDef, Finset.card_image_of_injective _ hcRinj, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
  have hOr2 : Or2.card = Nat.card ↥(MulAction.orbit ↥R T) := by
    rw [hOr2Def, Finset.card_image_of_injective _ hinv, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
  -- a conjugate and its inverse cannot have the same support for the same orbit element
  have hdisj : Disjoint Or Or2 := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    rw [hOrDef, Finset.mem_image] at ha
    rw [hOr2Def, Finset.mem_image] at hb
    obtain ⟨p, -, rfl⟩ := ha
    obtain ⟨q, -, rfl⟩ := hb
    have hsup : ((cR p : ↥R) : Equiv.Perm (Fin 7)).support
        = ((cR q : ↥R) : Equiv.Perm (Fin 7)).support := by
      rw [hab, hcoeeq q, Equiv.Perm.support_inv]
    rw [hsuppc p, hsuppc q] at hsup
    have hpq : p = q := by
      apply Subtype.ext
      apply Finset.ext
      intro y
      have h2 := congrArg (fun s : Finset (Fin 7) => y ∈ s) hsup
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at h2
      exact not_iff_not.mp (iff_of_eq h2)
    rw [← hpq] at hab
    have h2 : (cR p) * (cR p) = 1 := by
      nth_rewrite 2 [hab]
      exact mul_inv_cancel (cR p)
    have h3 : orderOf (cR p) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact h2)
    rw [hordc p] at h3
    exact absurd h3 (by norm_num)
  set Av : Finset ↥R := Finset.univ.filter
    (fun y : ↥R => orderOf y = 3 ∧ (y : Equiv.Perm (Fin 7)).support.card = 3) with hAvDef
  have hsub : Or ∪ Or2 ⊆ Av := by
    intro y hy
    rw [Finset.mem_union] at hy
    rcases hy with hy | hy
    · rw [hOrDef, Finset.mem_image] at hy
      obtain ⟨p, -, rfl⟩ := hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hordc p, hcardc p⟩
    · rw [hOr2Def, Finset.mem_image] at hy
      obtain ⟨p, -, rfl⟩ := hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [orderOf_inv]; exact hordc p,
        by rw [hcoeeq p, Equiv.Perm.support_inv]; exact hcardc p⟩
  have hAvcard : Av.card = Nat.card
      {y : ↥R // orderOf y = 3 ∧ (y : Equiv.Perm (Fin 7)).support.card = 3} := by
    rw [hAvDef, Finset.card_filter]
    rw [Nat.card_eq_fintype_card, Finset.sum_boole]
    exact (Fintype.card_subtype _).symm
  have hle : (Or ∪ Or2).card ≤ Av.card := Finset.card_le_card hsub
  have hunion : (Or ∪ Or2).card = Or.card + Or2.card := Finset.card_union_of_disjoint hdisj
  rw [← hAvcard]
  calc 2 * Nat.card ↥(MulAction.orbit ↥R T) = Or.card + Or2.card := by rw [hOr, hOr2]; ring
    _ = (Or ∪ Or2).card := hunion.symm
    _ ≤ Av.card := hle

set_option linter.unusedVariables false in
theorem three_cycles_ge (R V : Subgroup (alternatingGroup (Fin 7))) (x : alternatingGroup (Fin 7))
    (T : Finset (Fin 7)) (hT : T.card = 4) (hVR : V ≤ R) (hVcard : Nat.card V = 4)
    (h2 : ∀ v ∈ V, v * v = 1)
    (hsupp : ∀ v ∈ V, v ≠ 1 → (v : Equiv.Perm (Fin 7)).support = T)
    (hxR : x ∈ R) (hx3 : orderOf x = 3)
    (hxsupp : (x : Equiv.Perm (Fin 7)).support = Finset.univ \ T) :
    2 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R ≤
      Nat.card {y : ↥R // orderOf y = 3 ∧ (y : Equiv.Perm (Fin 7)).support.card = 3} := by
  have hA := relIndex_eq_card_orbit R V T hT hVcard h2 hsupp
  have hB := two_mul_orbit_le_local R x T hT hxR hx3 hxsupp
  calc 2 * (R ⊓ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7)))).relIndex R
      = 2 * Nat.card (MulAction.orbit ↥R T) := by rw [hA]
    _ ≤ Nat.card {y : ↥R // orderOf y = 3 ∧ (y : Equiv.Perm (Fin 7)).support.card = 3} := hB

end Work.CORE4.A7FGB
