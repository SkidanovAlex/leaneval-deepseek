import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.Basic` — general API for the Bender–Suzuki vocabulary

Elementary, model-independent lemmas about the vocabulary of
`Submission.Blueprint.Interfaces` that the whole `Models` area uses:

* `conj` (the challenge's conjugation `g H g⁻¹`),
* `involutions S`,
* `twoPoint H t = H ⊓ H^t`,
* `invertedBy X t = {x ∈ X | t x t⁻¹ = x⁻¹}`,
* `IsStronglyEmbedded`, `HasFourGroup`, `IsSplitRankOne`.
-/

namespace Work.Models

open LeanEval.GroupTheory.Defs

section Conj

variable {G : Type*} [Group G]

lemma mem_conj_iff {H : Subgroup G} {g x : G} :
    x ∈ Submission.Blueprint.conj g H ↔ g⁻¹ * x * g ∈ H := by
  rw [Submission.Blueprint.conj, Subgroup.mem_map]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨h, hh, rfl⟩
    have : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    rwa [this]
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by group⟩

lemma mem_conj_inv_iff {H : Subgroup G} {g x : G} :
    x ∈ Submission.Blueprint.conj g⁻¹ H ↔ g * x * g⁻¹ ∈ H := by
  rw [mem_conj_iff, inv_inv]

lemma conj_one (H : Subgroup G) : Submission.Blueprint.conj (1 : G) H = H := by
  ext x; rw [mem_conj_iff]; simp

lemma conj_top (g : G) : Submission.Blueprint.conj g (⊤ : Subgroup G) = ⊤ :=
  Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

lemma conj_mul (g h : G) (H : Subgroup G) :
    Submission.Blueprint.conj (g * h) H
      = Submission.Blueprint.conj g (Submission.Blueprint.conj h H) := by
  ext x
  rw [mem_conj_iff, mem_conj_iff, mem_conj_iff]
  constructor
  · intro hx
    have hr : (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h := by group
    rwa [hr] at hx
  · intro hx
    have hr : h⁻¹ * (g⁻¹ * x * g) * h = (g * h)⁻¹ * x * (g * h) := by group
    rwa [← hr]

lemma conj_inv_conj (g : G) (H : Subgroup G) :
    Submission.Blueprint.conj g⁻¹ (Submission.Blueprint.conj g H) = H := by
  rw [← conj_mul, inv_mul_cancel, conj_one]

lemma conj_conj_inv (g : G) (H : Subgroup G) :
    Submission.Blueprint.conj g (Submission.Blueprint.conj g⁻¹ H) = H := by
  rw [← conj_mul, mul_inv_cancel, conj_one]

lemma conj_le_conj_iff {H K : Subgroup G} {g : G} :
    Submission.Blueprint.conj g H ≤ Submission.Blueprint.conj g K ↔ H ≤ K := by
  constructor
  · intro h x hx
    have hy : g * x * g⁻¹ ∈ Submission.Blueprint.conj g H := by
      refine mem_conj_iff.mpr ?_
      have hr : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rwa [hr]
    have hz : g * x * g⁻¹ ∈ Submission.Blueprint.conj g K := h hy
    have hz' : g⁻¹ * (g * x * g⁻¹) * g ∈ K := mem_conj_iff.mp hz
    have hr : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [hr] at hz'
  · intro h x hx
    have hx' : g⁻¹ * x * g ∈ H := mem_conj_iff.mp hx
    exact mem_conj_iff.mpr (h hx')

lemma conj_eq_conj_iff {H K : Subgroup G} {g : G} :
    Submission.Blueprint.conj g H = Submission.Blueprint.conj g K ↔ H = K := by
  constructor
  · intro h
    rw [← conj_inv_conj g H, h, conj_inv_conj]
  · intro h; rw [h]

lemma card_conj (g : G) (H : Subgroup G) :
    Nat.card (Submission.Blueprint.conj g H) = Nat.card H := by
  rw [Submission.Blueprint.conj]
  exact Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective

@[simp] lemma conj_eq_top_iff {g : G} {H : Subgroup G} :
    Submission.Blueprint.conj g H = ⊤ ↔ H = ⊤ := by
  constructor
  · intro h
    rw [← conj_inv_conj g H, h, conj_top]
  · intro h; rw [h, conj_top]

@[simp] lemma conj_bot (g : G) : Submission.Blueprint.conj g (⊥ : Subgroup G) = ⊥ := by
  rw [Submission.Blueprint.conj, Subgroup.map_bot]

lemma conj_self_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    Submission.Blueprint.conj g H = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp hg

lemma mem_normalizer_of_conj_eq {H : Subgroup G} {g : G}
    (h : Submission.Blueprint.conj g H = H) :
    g ∈ Subgroup.normalizer (H : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

end Conj

section Involutions

variable {G : Type*} [Group G]

@[simp] lemma mem_involutions_iff {S : Set G} {x : G} :
    x ∈ Submission.Blueprint.involutions S ↔ x ∈ S ∧ orderOf x = 2 := Iff.rfl

lemma involutions_subset (S : Set G) : Submission.Blueprint.involutions S ⊆ S :=
  fun _ h => h.1

@[simp] lemma one_notMem_involutions (S : Set G) :
    (1 : G) ∉ Submission.Blueprint.involutions S := by
  intro h; rw [mem_involutions_iff] at h; exact absurd h.2 (by simp)

lemma involutions_mono {S T : Set G} (h : S ⊆ T) :
    Submission.Blueprint.involutions S ⊆ Submission.Blueprint.involutions T :=
  fun _ hx => ⟨h hx.1, hx.2⟩

lemma inv_mem_involutions {S : Set G} (hS : ∀ x ∈ S, x⁻¹ ∈ S) {x : G}
    (hx : x ∈ Submission.Blueprint.involutions S) :
    x⁻¹ ∈ Submission.Blueprint.involutions S :=
  ⟨hS x hx.1, by rw [orderOf_inv, hx.2]⟩

lemma involutions_commute_of_abelian {S : Set G} (h : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    {a b : G} (ha : a ∈ Submission.Blueprint.involutions S)
    (hb : b ∈ Submission.Blueprint.involutions S) : a * b = b * a :=
  h a ha.1 b hb.1

/-- In an abelian group a four-group is two distinct involutions. -/
lemma HasFourGroup.of_commute {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a ≠ b) (hc : a * b = b * a) : Submission.Blueprint.HasFourGroup G :=
  ⟨a, b, ha, hb, hab, hc⟩

end Involutions

section TransportSet

variable {G : Type*} [Group G]

/-- Image of `involutions H` under the conjugation map `x ↦ g x g⁻¹`. -/
lemma involutions_conj (g : G) (H : Subgroup G) :
    Submission.Blueprint.involutions ((Submission.Blueprint.conj g H : Subgroup G) : Set G)
      = (fun x => g * x * g⁻¹) '' Submission.Blueprint.involutions (H : Set G) := by
  ext x
  constructor
  · rintro ⟨hx, hord⟩
    have hxg : g⁻¹ * x * g ∈ H := mem_conj_iff.mp hx
    refine ⟨g⁻¹ * x * g, ⟨hxg, ?_⟩, by group⟩
    have h1 : orderOf (g⁻¹ * x * g) = orderOf x := by
      have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) x
      simpa [mul_assoc] using this
    rw [h1, hord]
  · rintro ⟨y, ⟨hy, hord⟩, hxy⟩
    simp only at hxy
    rw [← hxy]
    refine ⟨?_, ?_⟩
    · refine mem_conj_iff.mpr ?_
      show g⁻¹ * (g * y * g⁻¹) * g ∈ H
      have hr : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rwa [hr]
    · have h1 : orderOf (g * y * g⁻¹) = orderOf y := by
        have := MulEquiv.orderOf_eq (MulAut.conj g) y
        simpa [mul_assoc] using this
      rw [h1, hord]

end TransportSet

section TwoPoint

variable {G : Type*} [Group G]

theorem twoPoint_def (H : Subgroup G) (t : G) :
    Submission.Blueprint.twoPoint H t = H ⊓ Submission.Blueprint.conj t H := rfl

@[simp] lemma mem_twoPoint_iff {H : Subgroup G} {t x : G} :
    x ∈ Submission.Blueprint.twoPoint H t ↔ x ∈ H ∧ t⁻¹ * x * t ∈ H := by
  rw [twoPoint_def, Subgroup.mem_inf, mem_conj_iff]

lemma twoPoint_le_left (H : Subgroup G) (t : G) :
    Submission.Blueprint.twoPoint H t ≤ H := inf_le_left

lemma twoPoint_one (H : Subgroup G) : Submission.Blueprint.twoPoint H 1 = H := by
  rw [twoPoint_def, conj_one, inf_idem]

lemma twoPoint_self_of_mem {H : Subgroup G} {t : G} (ht : t ∈ H) :
    Submission.Blueprint.twoPoint H t = H := by
  have hconj : Submission.Blueprint.conj t H = H :=
    conj_self_of_mem_normalizer (Subgroup.le_normalizer ht)
  rw [twoPoint_def, hconj, inf_idem]

lemma twoPoint_le_conj_iff {H : Subgroup G} {t : G} {D : Subgroup G} :
    D ≤ Submission.Blueprint.twoPoint H t ↔ D ≤ H ∧ D ≤ Submission.Blueprint.conj t H :=
  le_inf_iff

lemma twoPoint_conj_conj {H : Subgroup G} {t g : G} :
    Submission.Blueprint.twoPoint (Submission.Blueprint.conj g H) t
      = Submission.Blueprint.conj g (Submission.Blueprint.twoPoint H (g⁻¹ * t * g)) := by
  rw [twoPoint_def, twoPoint_def]
  change Submission.Blueprint.conj g H ⊓ Submission.Blueprint.conj t
      (Submission.Blueprint.conj g H)
    = (H ⊓ Submission.Blueprint.conj (g⁻¹ * t * g) H).map
        (MulAut.conj g).toMonoidHom
  rw [Subgroup.map_inf H (Submission.Blueprint.conj (g⁻¹ * t * g) H)
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective]
  change Submission.Blueprint.conj g H ⊓ Submission.Blueprint.conj t
      (Submission.Blueprint.conj g H)
    = Submission.Blueprint.conj g H
      ⊓ Submission.Blueprint.conj g (Submission.Blueprint.conj (g⁻¹ * t * g) H)
  rw [← conj_mul]
  rw [← conj_mul]
  rw [show g * (g⁻¹ * t * g) = t * g from by group]

end TwoPoint

section InvertedBy

variable {G : Type*} [Group G]

@[simp] lemma mem_invertedBy_iff {X : Subgroup G} {t x : G} :
    x ∈ Submission.Blueprint.invertedBy X t ↔ x ∈ X ∧ t * x * t⁻¹ = x⁻¹ := Iff.rfl

lemma invertedBy_subset (X : Subgroup G) (t : G) :
    Submission.Blueprint.invertedBy X t ⊆ X := fun _ h => h.1

@[simp] lemma one_mem_invertedBy (X : Subgroup G) (t : G) :
    (1 : G) ∈ Submission.Blueprint.invertedBy X t := ⟨X.one_mem, by simp⟩

lemma inv_mem_invertedBy {X : Subgroup G} {t x : G}
    (hx : x ∈ Submission.Blueprint.invertedBy X t) :
    x⁻¹ ∈ Submission.Blueprint.invertedBy X t := by
  rw [mem_invertedBy_iff] at hx ⊢
  refine ⟨X.inv_mem hx.1, ?_⟩
  have h := congrArg (fun y => y⁻¹) hx.2
  simp only [mul_inv_rev, inv_inv] at h
  simpa [mul_assoc] using h

/-- Conjugation transports `J(X,t)`. -/
lemma invertedBy_conj {X : Subgroup G} {t g : G} :
    Submission.Blueprint.invertedBy (Submission.Blueprint.conj g X) (g * t * g⁻¹)
      = (fun x => g * x * g⁻¹) '' Submission.Blueprint.invertedBy X t := by
  ext x
  constructor
  · intro hx
    rw [mem_invertedBy_iff] at hx
    obtain ⟨hxX, hxinv⟩ := hx
    have hxX' : g⁻¹ * x * g ∈ X := mem_conj_iff.mp hxX
    refine ⟨g⁻¹ * x * g, ⟨hxX', ?_⟩, by group⟩
    have h2 := congrArg (fun y => g⁻¹ * y * g) hxinv
    simpa [mul_assoc] using h2
  · rintro ⟨y, ⟨hyX, hyinv⟩, hxy⟩
    simp only at hxy
    rw [← hxy]
    rw [mem_invertedBy_iff]
    refine ⟨?_, ?_⟩
    · refine mem_conj_iff.mpr ?_
      show g⁻¹ * (g * y * g⁻¹) * g ∈ X
      have hr : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rwa [hr]
    · have := congrArg (fun y => g * y * g⁻¹) hyinv
      simpa [mul_assoc] using this

end InvertedBy

section StronglyEmbedded

variable {G : Type*} [Group G]

lemma IsStronglyEmbedded.ne_top {H : Subgroup G} (h : IsStronglyEmbedded H) : H ≠ ⊤ :=
  h.1

lemma IsStronglyEmbedded.even {H : Subgroup G} (h : IsStronglyEmbedded H) :
    Even (Nat.card H) := h.2.1

lemma IsStronglyEmbedded.odd_twoPoint {H : Subgroup G} (h : IsStronglyEmbedded H)
    {g : G} (hg : g ∉ H) : Odd (Nat.card (Submission.Blueprint.twoPoint H g)) :=
  h.2.2 g hg

/-- A strongly embedded subgroup is self-normalising. -/
lemma IsStronglyEmbedded.normalizer_le {H : Subgroup G} (h : IsStronglyEmbedded H) :
    Subgroup.normalizer (H : Set G) ≤ H := by
  intro g hg
  by_contra hgH
  have hodd : Odd (Nat.card (Submission.Blueprint.twoPoint H g)) := h.2.2 g hgH
  have hconj : Submission.Blueprint.conj g H = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have h2 : Submission.Blueprint.twoPoint H g = H := by
    rw [twoPoint_def, hconj, inf_idem]
  rw [h2] at hodd
  exact Nat.not_even_iff_odd.mpr hodd h.2.1

lemma IsStronglyEmbedded.normalizer_eq {H : Subgroup G} (h : IsStronglyEmbedded H) :
    Subgroup.normalizer (H : Set G) = H :=
  le_antisymm (IsStronglyEmbedded.normalizer_le h) Subgroup.le_normalizer

/-- The normaliser of an even-order subgroup of a strongly embedded `H` is contained in `H`. -/
lemma IsStronglyEmbedded.normalizer_le_of_le {H X : Subgroup G} (h : IsStronglyEmbedded H)
    (hX : X ≤ H) (heven : Even (Nat.card X)) :
    Subgroup.normalizer (X : Set G) ≤ H := by
  intro g hg
  by_contra hgH
  have hodd : Odd (Nat.card (Submission.Blueprint.twoPoint H g)) := h.2.2 g hgH
  have hsub : X ≤ Submission.Blueprint.twoPoint H g := by
    rw [twoPoint_le_conj_iff]
    refine ⟨hX, ?_⟩
    have hXg : Submission.Blueprint.conj g X ≤ Submission.Blueprint.conj g H :=
      Subgroup.map_mono hX
    rwa [conj_self_of_mem_normalizer hg] at hXg
  have hdvd : Nat.card X ∣ Nat.card (Submission.Blueprint.twoPoint H g) :=
    Subgroup.card_dvd_of_le hsub
  exact Nat.not_even_iff_odd.mpr hodd
    (even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp heven) hdvd))

lemma IsStronglyEmbedded.conj {H : Subgroup G} (h : IsStronglyEmbedded H) (g : G) :
    IsStronglyEmbedded (Submission.Blueprint.conj g H) := by
  refine ⟨(conj_eq_top_iff.not).mpr h.1, ?_, ?_⟩
  · rw [card_conj]; exact h.2.1
  · intro x hx
    show Odd (Nat.card (Submission.Blueprint.twoPoint (Submission.Blueprint.conj g H) x))
    rw [twoPoint_conj_conj, card_conj]
    exact h.2.2 _ fun hg => hx (mem_conj_iff.mpr hg)

end StronglyEmbedded

section SplitRankOne

variable {G : Type*} [Group G]

lemma IsSplitRankOne.Q_le {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) : Q ≤ H :=
  h.le

lemma IsSplitRankOne.Q_normal {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    H ≤ Subgroup.normalizer (Q : Set G) := h.normal

lemma IsSplitRankOne.sup {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    Q ⊔ Submission.Blueprint.twoPoint H t = H := h.sup_eq

lemma IsSplitRankOne.inf {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    Q ⊓ Submission.Blueprint.twoPoint H t = ⊥ := h.inf_eq

lemma IsSplitRankOne.isStronglyEmbedded {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) : IsStronglyEmbedded H :=
  h.stronglyEmbedded

lemma IsSplitRankOne.twoTransitive {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    Submission.Blueprint.IsTwoTransitiveOn H := h.twoTransitive

lemma IsSplitRankOne.invol {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) : orderOf t = 2 := h.invol

lemma IsSplitRankOne.not_mem {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) : t ∉ H := h.not_mem

end SplitRankOne

end Work.Models
