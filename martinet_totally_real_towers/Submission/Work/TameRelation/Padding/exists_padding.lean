import Mathlib

/-!
# Padding a pro-`p` presentation by trivial generators

A presentation of a group `G` by `d` generators `gen : Fin d → G` and a finite relator set
`rel ⊆ FreeGroup (Fin d)`, encoded as the equality
`ker (FreeGroup.lift gen) = normalClosure rel`, can be *padded*: for every `n ≥ d` there is a
presentation by `n` generators `gen' : Fin n → G` (with `gen'` extending `gen` along
`Fin.castLE hdn` and with `gen' i = 1` for `i ≥ d`) whose relator set has at most
`rel.card + (n - d)` elements.

The `n - d` extra relators are the images of the padding generators `x_i` (`d ≤ i < n`) in the
free group on `n` letters, and the images of the old relators under the inclusion of the first
`d` letters.  The proof compares the quotients

* `FreeGroup (Fin d) ⧸ normalClosure rel ≅ im (lift gen)` (first isomorphism theorem), and
* `FreeGroup (Fin n) ⧸ normalClosure rel'`,

via the natural maps induced by `FreeGroup.lift gen'` and by the projection
`FreeGroup (Fin n) →* FreeGroup (Fin d)` which kills the padding generators.

This is the bookkeeping step which decouples the number of generators from the number of
relators in the Shafarevich--Koch relation count (see `Work.TameRelation.Deficiency`).
-/

namespace Work.TameRelation.Padding

/-- The number of indices `i : Fin n` with `d ≤ i` is `n - d`. -/
private lemma card_filter_univ_fin (d n : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => d ≤ (i : ℕ))).card = n - d := by
  rcases lt_or_ge d n with h | h
  · have : (Finset.univ.filter (fun i : Fin n => d ≤ (i : ℕ))) = Finset.Ici (⟨d, h⟩ : Fin n) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici, Fin.le_def]
    rw [this, Fin.card_Ici]
  · have : (Finset.univ.filter (fun i : Fin n => d ≤ (i : ℕ))) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i _
      have := i.2
      omega
    rw [this, Finset.card_empty]
    omega

theorem exists_padding {G : Type*} [Group G] {d n : ℕ} (hdn : d ≤ n) (gen : Fin d → G)
    (rel : Finset (FreeGroup (Fin d)))
    (hker : MonoidHom.ker (FreeGroup.lift gen) =
      Subgroup.normalClosure (rel : Set (FreeGroup (Fin d)))) :
    ∃ (gen' : Fin n → G) (rel' : Finset (FreeGroup (Fin n))),
      rel'.card ≤ rel.card + (n - d) ∧ gen' ∘ Fin.castLE hdn = gen ∧
      MonoidHom.ker (FreeGroup.lift gen') =
        Subgroup.normalClosure (rel' : Set (FreeGroup (Fin n))) := by
  -- the padded generators: the old ones on the first `d` indices, `1` afterwards
  let gen' : Fin n → G := fun i => if h : (i : ℕ) < d then gen ⟨i, h⟩ else 1
  have hgen'_lt : ∀ (i : Fin n) (h : (i : ℕ) < d), gen' i = gen ⟨i, h⟩ := by
    intro i h
    simp only [gen']
    rw [dite_eq_left h]
  have hgen'_ge : ∀ (i : Fin n), ¬ ((i : ℕ) < d) → gen' i = 1 := by
    intro i h
    simp only [gen']
    rw [dite_eq_right h]
  -- the inclusion of the first `d` free generators
  let A : FreeGroup (Fin d) →* FreeGroup (Fin n) :=
    FreeGroup.lift (fun i : Fin d => FreeGroup.of (Fin.castLE hdn i))
  have hAi : ∀ (i : Fin d), A (FreeGroup.of i) = FreeGroup.of (Fin.castLE hdn i) :=
    fun i => FreeGroup.lift_apply_of
  have hφA : ∀ x : FreeGroup (Fin d), FreeGroup.lift gen' (A x) = FreeGroup.lift gen x := by
    intro x
    refine FreeGroup.lift_unique (f := gen) ((FreeGroup.lift gen').comp A) ?_
    intro i
    simp only [MonoidHom.comp_apply, hAi, FreeGroup.lift_apply_of]
    exact hgen'_lt (Fin.castLE hdn i) i.isLt
  -- the padding relators `x_d, …, x_{n-1}`
  let tail : Finset (FreeGroup (Fin n)) :=
    (Finset.univ.filter (fun i : Fin n => d ≤ (i : ℕ))).image FreeGroup.of
  let rel' : Finset (FreeGroup (Fin n)) := rel.image (fun r => A r) ∪ tail
  have hrel'sub : (rel' : Set (FreeGroup (Fin n))) ⊆
      (MonoidHom.ker (FreeGroup.lift gen') : Set (FreeGroup (Fin n))) := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hw
      refine MonoidHom.mem_ker.mpr ?_
      have hψ : FreeGroup.lift gen r = 1 := by
        have : r ∈ MonoidHom.ker (FreeGroup.lift gen) := by
          rw [hker]; exact Subgroup.subset_normalClosure hr
        exact MonoidHom.mem_ker.mp this
      rw [hφA r, hψ]
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      refine MonoidHom.mem_ker.mpr ?_
      rw [FreeGroup.lift_apply_of]
      exact hgen'_ge i (by have hh := (Finset.mem_filter.mp hi).2; omega)
  let N : Subgroup (FreeGroup (Fin n)) := Subgroup.normalClosure (rel' : Set (FreeGroup (Fin n)))
  let K : Subgroup (FreeGroup (Fin d)) := Subgroup.normalClosure (rel : Set (FreeGroup (Fin d)))
  have hNle : N ≤ MonoidHom.ker (FreeGroup.lift gen') := Subgroup.normalClosure_le_normal hrel'sub
  have hKle : K ≤ MonoidHom.ker (FreeGroup.lift gen) := hker.ge
  have hAK : K ≤ Subgroup.comap A N := by
    refine (Subgroup.comap_normalClosure_image_ge (rel : Set (FreeGroup (Fin d))) A).trans
      (Subgroup.comap_mono ?_)
    apply Subgroup.normalClosure_le_normal
    rintro y ⟨r, hr, rfl⟩
    exact Subgroup.subset_normalClosure
      (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩)))
  let q : FreeGroup (Fin n) →* FreeGroup (Fin n) ⧸ N := QuotientGroup.mk' N
  let γ : FreeGroup (Fin d) ⧸ K →* FreeGroup (Fin n) ⧸ N := QuotientGroup.map K N A hAK
  let β : FreeGroup (Fin n) ⧸ N →* G := QuotientGroup.lift N (FreeGroup.lift gen') hNle
  let ψb : FreeGroup (Fin d) ⧸ K →* G := QuotientGroup.lift K (FreeGroup.lift gen) hKle
  -- the two composite maps `FreeGroup (Fin d) ⧸ K →* G` agree
  have hcomp : ∀ x : FreeGroup (Fin d) ⧸ K, β (γ x) = ψb x := by
    intro x
    induction x using QuotientGroup.induction_on with
    | _ y =>
      simp only [γ, β, ψb, QuotientGroup.map_mk, QuotientGroup.lift_mk]
      exact hφA y
  -- `FreeGroup (Fin d) ⧸ K →* G` is injective, because its kernel is `K`
  have hψbinj : Function.Injective ψb := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with
    | _ a =>
      induction y using QuotientGroup.induction_on with
      | _ b =>
        simp only [ψb, QuotientGroup.lift_mk] at hxy
        have hab : a⁻¹ * b ∈ K := by
          have h2 : a⁻¹ * b ∈ MonoidHom.ker (FreeGroup.lift gen) := by
            rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
          rwa [hker] at h2
        exact QuotientGroup.eq.mpr hab
  -- `q` maps the generators of `FreeGroup (Fin n)` onto generators of the quotient
  have htop : Subgroup.closure (Set.range (fun i : Fin n => q (FreeGroup.of i))) = ⊤ := by
    have h1 : (fun i : Fin n => q (FreeGroup.of i)) = q ∘ FreeGroup.of := rfl
    rw [h1, Set.range_comp, ← MonoidHom.map_closure, FreeGroup.closure_range_of, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
  -- `γ` is surjective: the padding generators die in the target
  have hγsurj : Function.Surjective γ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← htop, Subgroup.closure_le]
    rintro z ⟨i, rfl⟩
    rcases lt_or_ge (i : ℕ) d with hi | hi
    · have hAi' : A (FreeGroup.of (⟨i, hi⟩ : Fin d)) = FreeGroup.of (i : Fin n) := by
        rw [hAi]
        congr 1
      refine ⟨QuotientGroup.mk' K (FreeGroup.of ⟨i, hi⟩), ?_⟩
      simp only [γ, q, QuotientGroup.map_mk, QuotientGroup.mk'_apply, hAi']
    · refine ⟨1, ?_⟩
      rw [map_one]
      exact ((QuotientGroup.eq_one_iff (N := N) (FreeGroup.of i)).mpr
        (Subgroup.subset_normalClosure (Finset.mem_coe.mpr (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩))))).symm
  -- hence `β` has trivial kernel
  have hβinj : Function.Injective β := by
    intro x y hxy
    obtain ⟨x', rfl⟩ := hγsurj x
    obtain ⟨y', rfl⟩ := hγsurj y
    have h1 : ψb x' = ψb y' := by rw [← hcomp x', ← hcomp y']; exact hxy
    rw [hψbinj h1]
  refine ⟨gen', rel', ?_, ?_, ?_⟩
  · -- the cardinality bound
    have h1 : (rel.image fun r => A r).card ≤ rel.card := Finset.card_image_le
    have h2 : tail.card ≤ n - d := by
      have := Finset.card_image_le
        (s := (Finset.univ.filter (fun i : Fin n => d ≤ (i:ℕ)))) (f := FreeGroup.of)
      rw [card_filter_univ_fin d n] at this
      exact this
    calc rel'.card ≤ (rel.image (fun r => A r)).card + tail.card := Finset.card_union_le _ _
      _ ≤ rel.card + (n - d) := Nat.add_le_add h1 h2
  · -- `gen'` extends `gen`
    funext i
    rw [Function.comp_apply, hgen'_lt (Fin.castLE hdn i) i.isLt]
    congr 1
  · -- the kernel equality
    refine le_antisymm ?_ hNle
    intro w hw
    have hw1 : β (QuotientGroup.mk' N w) = 1 := by
      simp only [β, QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
      exact MonoidHom.mem_ker.mp hw
    have h2 : QuotientGroup.mk' N w = 1 := hβinj (by rw [hw1, map_one])
    exact (QuotientGroup.eq_one_iff (N := N) w).mp h2

end Work.TameRelation.Padding
