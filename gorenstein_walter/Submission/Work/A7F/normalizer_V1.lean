/-
The normalizer in `A₇` of the Klein four group `V₁ = {1, (01)(23), (02)(13), (03)(12)}` has order
`72`, and it coincides with the normalizer of `K = ⟨(4 5 6)⟩`.

Both normalizers are the setwise stabilizer `H` of the four point set `{0,1,2,3}`:

* the image of `V₁` under conjugation is the set of double transpositions of `{0,1,2,3}`, so
  `g` normalizes `V₁` exactly when `g` maps `{0,1,2,3}` to itself;
* `K` is the pointwise stabilizer of `{0,1,2,3}`, and it is the full subgroup of `A₇` supported on
  `{4,5,6}`, from which the same equivalence follows.

Finally `|H| = 72` because `A₇` has `2520` elements and the orbit of `{0,1,2,3}` consists of the
`35 = C(7,4)` four element subsets.
-/
import Mathlib
import Submission.Work.A7F.Defs

open scoped MatrixGroups Pointwise

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Work.A7F

open Work.A7 Subgroup Equiv

/-! ### The Klein four group `V₁` and its image in `Equiv.Perm (Fin 7)` -/

/-- The image of `V₁ = {1, (01)(23), (02)(13), (03)(12)}` in `Equiv.Perm (Fin 7)`, as a finset. -/
private def Vperm : Finset (Perm (Fin 7)) :=
  {1, dswapPerm 0 1 2 3, dswapPerm 0 2 1 3, dswapPerm 0 3 1 2}

/-- The four elements of `V₁`, written inside `A₇`. -/
private def V1f : Finset (alternatingGroup (Fin 7)) :=
  {1, a7Invol, a7Dswap 0 2 1 3 (by decide) (by decide), a7Dswap 0 3 1 2 (by decide) (by decide)}

private lemma V1f_mem_of (x : alternatingGroup (Fin 7)) (hx : x ∈ V1f) :
    x = 1 ∨ x = a7Invol ∨ x = a7Dswap 0 2 1 3 (by decide) (by decide)
      ∨ x = a7Dswap 0 3 1 2 (by decide) (by decide) := by
  simpa [V1f] using hx

set_option linter.unusedSimpArgs false in
/-- `V₁` is the Klein four group `{1, (01)(23), (02)(13), (03)(12)}`. -/
private def V1sub : Subgroup (alternatingGroup (Fin 7)) where
  carrier := ↑V1f
  mul_mem' := by
    intro x y hx hy
    rcases V1f_mem_of x hx with rfl | rfl | rfl | rfl <;>
      rcases V1f_mem_of y hy with rfl | rfl | rfl | rfl <;>
      simp only [V1f, Finset.mem_insert, Finset.mem_singleton] <;> decide
  one_mem' := by simp [V1f]
  inv_mem' := by
    intro x hx
    rcases V1f_mem_of x hx with rfl | rfl | rfl | rfl <;>
      simp only [V1f, Finset.mem_insert, Finset.mem_singleton] <;> decide

private lemma a7V1_eq_V1sub : a7V1 = V1sub := by
  apply le_antisymm
  · rw [show a7V1 = Subgroup.closure
        ({a7Invol, a7Dswap 0 2 1 3 (by decide) (by decide)}
          : Set (alternatingGroup (Fin 7))) from rfl]
    refine (closure_le (K := V1sub)).mpr ?_
    rintro x (hx : x = a7Invol ∨ x = a7Dswap 0 2 1 3 (by decide) (by decide))
    rcases hx with rfl | rfl
    · show (a7Invol : alternatingGroup (Fin 7)) ∈ V1f
      simp [V1f]
    · show (a7Dswap 0 2 1 3 (by decide) (by decide) : alternatingGroup (Fin 7)) ∈ V1f
      simp [V1f]
  · intro x hx
    rcases V1f_mem_of x hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · have hw : a7Dswap 0 3 1 2 (by decide) (by decide) =
          a7Invol * a7Dswap 0 2 1 3 (by decide) (by decide) := by decide
      rw [hw]
      exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

private lemma V1f_iff_Vperm : ∀ x : alternatingGroup (Fin 7), x ∈ V1f ↔ (x : Perm (Fin 7)) ∈ Vperm := by
  decide

/-- The elements of `V₁` are exactly the identity and the three double transpositions of
`{0,1,2,3}`. -/
private lemma a7V1_mem_iff_perm (x : alternatingGroup (Fin 7)) :
    x ∈ a7V1 ↔ (x : Perm (Fin 7)) ∈ Vperm := by
  rw [a7V1_eq_V1sub]
  exact V1f_iff_Vperm x

/-- Any double transposition `(a b)(c d)` whose four points are exactly `{0,1,2,3}` is one of the
three non-identity double transpositions of `{0,1,2,3}` (namely an element of `V₁`). -/
private lemma dswap_mem_Vperm : ∀ a b c d : Fin 7, a ≠ b → c ≠ d →
    ({a,b,c,d} : Finset (Fin 7)) = {0,1,2,3} → dswapPerm a b c d ∈ Vperm := by
  decide

/-- Conjugation of a double transposition `(a b)(c d)` sends it to `(f a f b)(f c f d)`. -/
private lemma conj_dswap (f : Perm (Fin 7)) (a b c d : Fin 7) :
    f * dswapPerm a b c d * f⁻¹ = dswapPerm (f a) (f b) (f c) (f d) := by
  calc f * dswapPerm a b c d * f⁻¹
      = (f * Equiv.swap a b * f⁻¹) * (f * Equiv.swap c d * f⁻¹) := by
        simp only [dswapPerm]; group
    _ = Equiv.swap (f a) (f b) * Equiv.swap (f c) (f d) := by
        rw [Equiv.swap_apply_apply, Equiv.swap_apply_apply]
    _ = dswapPerm (f a) (f b) (f c) (f d) := rfl

/-! ### The point sets `{0,1,2,3}` and `{4,5,6}` -/

/-- The four points moved by `V₁`. -/
private def SS : Set (Fin 7) := {0,1,2,3}

/-- The three points moved by `K = ⟨(4 5 6)⟩`. -/
private def TT : Set (Fin 7) := {4,5,6}

/-- The setwise stabilizer in `A₇` of `{0,1,2,3}`. -/
private def HH : Subgroup (alternatingGroup (Fin 7)) :=
  MulAction.stabilizer (alternatingGroup (Fin 7)) SS

private lemma mem_SS_or_TT (p : Fin 7) : p ∈ SS ∨ p ∈ TT := by fin_cases p <;> simp [SS, TT]

private lemma SS_eq_compl_TT : SS = TTᶜ := by ext p; fin_cases p <;> simp [SS, TT]

/-- A bijection mapping a set to itself also maps its complement to itself. -/
private lemma image_compl_eq (e : Perm (Fin 7)) (t : Set (Fin 7)) (h : e '' t = t) :
    e '' tᶜ = tᶜ := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩ hp
    have hmem : e q ∈ e '' t := by rw [h]; exact hp
    obtain ⟨q', hq', hqq⟩ := hmem
    exact hq (e.injective hqq ▸ hq')
  · intro hp
    refine ⟨e⁻¹ p, ?_, by simp⟩
    intro hq
    apply hp
    have hmem : p ∈ e '' t := by
      have : e (e⁻¹ p) ∈ e '' t := ⟨e⁻¹ p, hq, rfl⟩
      simpa using this
    rwa [h] at hmem

private lemma mem_supp_t (p : Fin 7) : p ∈ a7InvolPerm.support ↔ p ∈ SS := by
  rw [show SS = ({0,1,2,3} : Set (Fin 7)) from rfl]
  rw [show ({0,1,2,3} : Set (Fin 7)) = (({0,1,2,3} : Finset (Fin 7)) : Set (Fin 7)) from by simp]
  rw [← Finset.mem_coe, show a7InvolPerm.support = ({0,1,2,3} : Finset (Fin 7)) from by decide]

private lemma mem_supp_c (p : Fin 7) : p ∈ a7ThreeCyclePerm.support ↔ p ∈ TT := by
  rw [show TT = ({4,5,6} : Set (Fin 7)) from rfl]
  rw [show ({4,5,6} : Set (Fin 7)) = (({4,5,6} : Finset (Fin 7)) : Set (Fin 7)) from by simp]
  rw [← Finset.mem_coe, show a7ThreeCyclePerm.support = ({4,5,6} : Finset (Fin 7)) from by decide]

/-- `V₁` fixes the three points `4,5,6`. -/
private lemma a7V1_le_fixingT : a7V1 ≤ fixingSubgroup (alternatingGroup (Fin 7)) TT := by
  rw [show a7V1 = Subgroup.closure
      ({a7Invol, a7Dswap 0 2 1 3 (by decide) (by decide)}
        : Set (alternatingGroup (Fin 7))) from rfl]
  refine (closure_le (K := fixingSubgroup (alternatingGroup (Fin 7)) TT)).mpr ?_
  rintro x (hx : x = a7Invol ∨ x = a7Dswap 0 2 1 3 (by decide) (by decide))
  rcases hx with rfl | rfl
  · exact (mem_fixingSubgroup_iff (alternatingGroup (Fin 7))).mpr (by
      show ∀ y ∈ ({4,5,6} : Set (Fin 7)), a7Invol • y = y
      decide)
  · exact (mem_fixingSubgroup_iff (alternatingGroup (Fin 7))).mpr (by
      show ∀ y ∈ ({4,5,6} : Set (Fin 7)),
        a7Dswap 0 2 1 3 (by decide) (by decide) • y = y
      decide)

/-- `K = ⟨(4 5 6)⟩` fixes the four points `0,1,2,3`. -/
private lemma a7K_le_fixingS : a7K ≤ fixingSubgroup (alternatingGroup (Fin 7)) SS := by
  rw [show a7K = Subgroup.zpowers a7ThreeCycle from rfl, Subgroup.zpowers_le,
    mem_fixingSubgroup_iff]
  show ∀ y ∈ ({0,1,2,3} : Set (Fin 7)), a7ThreeCycle • y = y
  decide

/-- The pointwise stabilizer in `A₇` of `{0,1,2,3}` is exactly `K`. -/
private lemma fixing_eq_a7K : fixingSubgroup (alternatingGroup (Fin 7)) SS = a7K := by
  have h := Subgroup.card_mul_index (fixingSubgroup (alternatingGroup (Fin 7)) SS)
  have hidx : (fixingSubgroup (alternatingGroup (Fin 7)) SS).index = 840 := by
    have hMk : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 7)) (Fin 7) SS.ncard := by
      rw [show SS.ncard = 4 from by simp [SS]]
      haveI : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 7)) (Fin 7)
          (Nat.card (Fin 7) - 2) := alternatingGroup.isMultiplyPretransitive (Fin 7)
      refine MulAction.isMultiplyPretransitive_of_le (m := 4) (n := Nat.card (Fin 7) - 2) ?_ ?_
      · rw [Nat.card_fin]; norm_num
      · exact Nat.sub_le _ _
    have h := MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq (s := SS) hMk
    rw [show SS.ncard = 4 from by simp [SS], Nat.card_fin] at h
    rw [h]; decide
  rw [hidx, Work.A7.card_alternatingGroup_seven] at h
  refine (Subgroup.eq_of_le_of_card_ge a7K_le_fixingS ?_).symm
  rw [Work.A7.card_a7K]
  omega

/-! ### The subgroup `H` is the common normalizer -/

private lemma image_finset_eq (g : alternatingGroup (Fin 7)) (hg : g ∈ HH) :
    ({((g : Perm (Fin 7)) 0), ((g : Perm (Fin 7)) 1), ((g : Perm (Fin 7)) 2),
        ((g : Perm (Fin 7)) 3)} : Finset (Fin 7)) = {0,1,2,3} := by
  rw [← Finset.coe_inj]
  have h : (g : Perm (Fin 7)) '' SS = SS := MulAction.mem_stabilizer_iff.mp hg
  have hst : ((({0,1,2,3} : Finset (Fin 7))) : Set (Fin 7)) = SS := by
    show ((({0,1,2,3} : Finset (Fin 7))) : Set (Fin 7)) = ({0,1,2,3} : Set (Fin 7))
    simp
  rw [hst, ← h]
  rw [show SS = ({0,1,2,3} : Set (Fin 7)) from rfl]
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]

/-- Reordering the second and third entries of a four element finset of points. -/
private lemma finset_reorder (f : Fin 7 → Fin 7) :
    ({f 0, f 2, f 1, f 3} : Finset (Fin 7)) = {f 0, f 1, f 2, f 3} := by
  ext p
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- Conjugation by an element of `H` preserves `V₁`. -/
private lemma conj_mem_V1 (g : alternatingGroup (Fin 7)) (hg : g ∈ HH) (h : alternatingGroup (Fin 7))
    (hh : h ∈ a7V1) : g * h * g⁻¹ ∈ a7V1 := by
  have ht : (MulAut.conj g) a7Invol ∈ a7V1 := by
    rw [MulAut.conj_apply, a7V1_mem_iff_perm]
    have hcoe : (((g * a7Invol * g⁻¹ : alternatingGroup (Fin 7))) : Perm (Fin 7))
        = (g : Perm (Fin 7)) * a7InvolPerm * (g : Perm (Fin 7))⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Work.A7.coe_a7Invol]
    rw [hcoe, show a7InvolPerm = dswapPerm 0 1 2 3 from rfl, conj_dswap]
    refine dswap_mem_Vperm _ _ _ _ ?_ ?_ (image_finset_eq g hg)
    · exact fun hc => (by decide : (0 : Fin 7) ≠ 1) ((g : Perm (Fin 7)).injective hc)
    · exact fun hc => (by decide : (2 : Fin 7) ≠ 3) ((g : Perm (Fin 7)).injective hc)
  have hu : (MulAut.conj g) (a7Dswap 0 2 1 3 (by decide) (by decide)) ∈ a7V1 := by
    rw [MulAut.conj_apply, a7V1_mem_iff_perm]
    have hcoe : (((g * (a7Dswap 0 2 1 3 (by decide) (by decide)) * g⁻¹
            : alternatingGroup (Fin 7))) : Perm (Fin 7))
        = (g : Perm (Fin 7)) * dswapPerm 0 2 1 3 * (g : Perm (Fin 7))⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Work.A7.coe_a7Dswap]
    rw [hcoe, conj_dswap]
    refine dswap_mem_Vperm _ _ _ _ ?_ ?_ ?_
    · exact fun hc => (by decide : (0 : Fin 7) ≠ 2) ((g : Perm (Fin 7)).injective hc)
    · exact fun hc => (by decide : (1 : Fin 7) ≠ 3) ((g : Perm (Fin 7)).injective hc)
    · have h := image_finset_eq g hg
      rw [show ({((g : Perm (Fin 7)) 0), ((g : Perm (Fin 7)) 2), ((g : Perm (Fin 7)) 1),
            ((g : Perm (Fin 7)) 3)} : Finset (Fin 7))
          = ({((g : Perm (Fin 7)) 0), ((g : Perm (Fin 7)) 1), ((g : Perm (Fin 7)) 2),
              ((g : Perm (Fin 7)) 3)} : Finset (Fin 7)) from
        finset_reorder (fun i => (g : Perm (Fin 7)) i)]
      exact h
  have hmap : Subgroup.map (MulAut.conj g).toMonoidHom a7V1 ≤ a7V1 := by
    rw [show a7V1 = Subgroup.closure
        ({a7Invol, a7Dswap 0 2 1 3 (by decide) (by decide)}
          : Set (alternatingGroup (Fin 7))) from rfl, MonoidHom.map_closure]
    refine (closure_le (K := a7V1)).mpr ?_
    rintro y hy
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    obtain ⟨x, rfl | rfl, hxy⟩ := hy
    · rw [← hxy]; exact ht
    · rw [← hxy]; exact hu
  have hz : (MulAut.conj g) h ∈ Subgroup.map (MulAut.conj g).toMonoidHom a7V1 :=
    ⟨h, hh, rfl⟩
  have := hmap hz
  rwa [MulAut.conj_apply] at this

/-- Conjugation by an element of `H` preserves `K`. -/
private lemma conj_mem_a7K (g : alternatingGroup (Fin 7)) (hg : g ∈ HH) (h : alternatingGroup (Fin 7))
    (hh : h ∈ a7K) : g * h * g⁻¹ ∈ a7K := by
  have hmem : (MulAut.conj g) a7ThreeCycle ∈ a7K := by
    rw [MulAut.conj_apply, ← fixing_eq_a7K, mem_fixingSubgroup_iff]
    intro y hy
    have hgy : (g : Perm (Fin 7))⁻¹ y ∈ SS := by
      have hg' : (g⁻¹ : alternatingGroup (Fin 7)) ∈ HH := HH.inv_mem hg
      have h2 : ((g⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7)) '' SS = SS :=
        MulAction.mem_stabilizer_iff.mp hg'
      have himg : ((g⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7)) y ∈ SS :=
        h2 ▸ (Set.mem_image_of_mem _ hy)
      simpa using himg
    have hcfix : ((a7ThreeCycle : alternatingGroup (Fin 7)) : Perm (Fin 7))
        ((g : Perm (Fin 7))⁻¹ y) = (g : Perm (Fin 7))⁻¹ y :=
      (mem_fixingSubgroup_iff (alternatingGroup (Fin 7))).mp
        (a7K_le_fixingS (Subgroup.mem_zpowers a7ThreeCycle)) ((g : Perm (Fin 7))⁻¹ y) hgy
    show ((g * a7ThreeCycle * g⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7)) y = y
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
    rw [show ((a7ThreeCycle : alternatingGroup (Fin 7)) : Perm (Fin 7)) ((g : Perm (Fin 7))⁻¹ y)
        = (g : Perm (Fin 7))⁻¹ y from hcfix]
    simp
  have hmap : Subgroup.map (MulAut.conj g).toMonoidHom a7K ≤ a7K := by
    rw [show a7K = Subgroup.zpowers a7ThreeCycle from rfl, MonoidHom.map_zpowers,
      Subgroup.zpowers_le]
    exact hmem
  have hz : (MulAut.conj g) h ∈ Subgroup.map (MulAut.conj g).toMonoidHom a7K :=
    ⟨h, hh, rfl⟩
  have := hmap hz
  rwa [MulAut.conj_apply] at this

/-- The normalizer of `V₁` is contained in `H`. -/
private lemma normalizer_a7V1_le :
    Subgroup.normalizer (a7V1 : Set (alternatingGroup (Fin 7))) ≤ HH := by
  intro g hg
  have hmem : g * a7Invol * g⁻¹ ∈ a7V1 :=
    (Subgroup.mem_normalizer_iff.mp hg a7Invol).mp (Subgroup.subset_closure (by simp))
  have hfix : g * a7Invol * g⁻¹ ∈ fixingSubgroup (alternatingGroup (Fin 7)) TT :=
    a7V1_le_fixingT hmem
  change g ∈ MulAction.stabilizer (alternatingGroup (Fin 7)) SS
  rw [MulAction.mem_stabilizer_iff]
  show (g : Perm (Fin 7)) '' SS = SS
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite SS)
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hpt : p ∈ a7InvolPerm.support := (mem_supp_t p).mpr hp
    have hne : a7InvolPerm p ≠ p := Equiv.Perm.mem_support.mp hpt
    have hyne : ((g * a7Invol * g⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7))
        ((g : Perm (Fin 7)) p) ≠ (g : Perm (Fin 7)) p := by
      rw [show ((g * a7Invol * g⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7))
          = (g : Perm (Fin 7)) * a7InvolPerm * (g : Perm (Fin 7))⁻¹ from by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Work.A7.coe_a7Invol]]
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      intro hcon
      exact hne (by simpa using ((g : Perm (Fin 7)).injective hcon))
    have hsupp : (g : Perm (Fin 7)) p ∈
        ((g * a7Invol * g⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7)).support :=
      Equiv.Perm.mem_support.mpr hyne
    by_contra hnot
    have hT : (g : Perm (Fin 7)) p ∈ TT := (mem_SS_or_TT _).resolve_left hnot
    have hfixp : ((g * a7Invol * g⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7))
        ((g : Perm (Fin 7)) p) = (g : Perm (Fin 7)) p :=
      (mem_fixingSubgroup_iff (alternatingGroup (Fin 7))).mp hfix ((g : Perm (Fin 7)) p) hT
    exact (Equiv.Perm.mem_support.mp hsupp) hfixp
  · exact ge_of_eq (Set.ncard_image_of_injective SS (g : Perm (Fin 7)).injective)

/-- `H` is contained in the normalizer of `V₁`. -/
private lemma normalizer_a7V1_ge :
    HH ≤ Subgroup.normalizer (a7V1 : Set (alternatingGroup (Fin 7))) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conj_mem_V1 g hg h
  · intro hh
    have hg' : (g⁻¹ : alternatingGroup (Fin 7)) ∈ HH := HH.inv_mem hg
    have hh' := conj_mem_V1 g⁻¹ hg' (g * h * g⁻¹) hh
    rwa [show (g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ : alternatingGroup (Fin 7)) = h from by
      group] at hh'

/-- The normalizer of `K` is contained in `H`. -/
private lemma normalizer_a7K_le :
    Subgroup.normalizer (a7K : Set (alternatingGroup (Fin 7))) ≤ HH := by
  intro g hg
  have hmem : g * a7ThreeCycle * g⁻¹ ∈ a7K :=
    (Subgroup.mem_normalizer_iff.mp hg a7ThreeCycle).mp (Subgroup.mem_zpowers a7ThreeCycle)
  have hfix : g * a7ThreeCycle * g⁻¹ ∈ fixingSubgroup (alternatingGroup (Fin 7)) SS :=
    a7K_le_fixingS hmem
  change g ∈ MulAction.stabilizer (alternatingGroup (Fin 7)) SS
  rw [MulAction.mem_stabilizer_iff]
  show (g : Perm (Fin 7)) '' SS = SS
  have himgT : (g : Perm (Fin 7)) '' TT ⊆ TT := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hpt : p ∈ a7ThreeCyclePerm.support := (mem_supp_c p).mpr hp
    have hne : a7ThreeCyclePerm p ≠ p := Equiv.Perm.mem_support.mp hpt
    have hyne : ((g * a7ThreeCycle * g⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7))
        ((g : Perm (Fin 7)) p) ≠ (g : Perm (Fin 7)) p := by
      rw [show ((g * a7ThreeCycle * g⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7))
          = (g : Perm (Fin 7)) * a7ThreeCyclePerm * (g : Perm (Fin 7))⁻¹ from by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Work.A7.coe_a7ThreeCycle]]
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      intro hcon
      exact hne (by simpa using ((g : Perm (Fin 7)).injective hcon))
    have hsupp : (g : Perm (Fin 7)) p ∈
        ((g * a7ThreeCycle * g⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7)).support :=
      Equiv.Perm.mem_support.mpr hyne
    by_contra hnot
    have hS : (g : Perm (Fin 7)) p ∈ SS := (mem_SS_or_TT _).resolve_right hnot
    have hfixp : ((g * a7ThreeCycle * g⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7))
        ((g : Perm (Fin 7)) p) = (g : Perm (Fin 7)) p :=
      (mem_fixingSubgroup_iff (alternatingGroup (Fin 7))).mp hfix ((g : Perm (Fin 7)) p) hS
    exact (Equiv.Perm.mem_support.mp hsupp) hfixp
  have himgTeq : (g : Perm (Fin 7)) '' TT = TT :=
    Set.eq_of_subset_of_ncard_le himgT
      (ge_of_eq (Set.ncard_image_of_injective TT (g : Perm (Fin 7)).injective))
      (Set.toFinite TT)
  rw [SS_eq_compl_TT]
  exact image_compl_eq (g : Perm (Fin 7)) TT himgTeq

/-- `H` is contained in the normalizer of `K`. -/
private lemma normalizer_a7K_ge :
    HH ≤ Subgroup.normalizer (a7K : Set (alternatingGroup (Fin 7))) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conj_mem_a7K g hg h
  · intro hh
    have hg' : (g⁻¹ : alternatingGroup (Fin 7)) ∈ HH := HH.inv_mem hg
    have hh' := conj_mem_a7K g⁻¹ hg' (g * h * g⁻¹) hh
    rwa [show (g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ : alternatingGroup (Fin 7)) = h from by
      group] at hh'

/-! ### The order of `H` -/

/-- The number of four element subsets of `Fin 7` is `35`. -/
private lemma ncard_four_sets : ({s : Set (Fin 7) | s.ncard = 4}).ncard = 35 := by
  rw [show ({s : Set (Fin 7) | s.ncard = 4})
      = {t : Set (Fin 7) | t ⊆ Set.univ ∧ t.ncard = 4} from by ext t; simp]
  rw [Set.ncard_powerset_ncard (Set.finite_univ) 4, Set.ncard_univ, Nat.card_fin]
  decide

/-- Every four element set of `Fin 7` is the range of an embedding `Fin 4 ↪ Fin 7`. -/
private lemma exists_embedding_range (s : Set (Fin 7)) (hs : s.ncard = 4) :
    ∃ a : Fin 4 ↪ Fin 7, Set.range (a : Fin 4 → Fin 7) = s := by
  haveI : Fintype ↥s := (Set.toFinite s).fintype
  have hcard : Fintype.card ↥s = 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hs]
  let e : Fin 4 ≃ ↥s := Fintype.equivOfCardEq (by rw [Fintype.card_fin, hcard])
  refine ⟨e.toEmbedding.trans (Function.Embedding.subtype (· ∈ s)), ?_⟩
  ext p
  simp only [Set.mem_range, Function.Embedding.trans_apply, Function.Embedding.coe_subtype,
    Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨i, hi⟩
    exact hi ▸ (e i).2
  · intro hp
    obtain ⟨i, hi⟩ := e.surjective ⟨p, hp⟩
    exact ⟨i, by rw [hi]⟩

/-- The range of an embedding is carried to the range of its image under a permutation. -/
private lemma range_smul_embedding (g : alternatingGroup (Fin 7)) (b : Fin 4 ↪ Fin 7) :
    Set.range ((g • b : Fin 4 ↪ Fin 7) : Fin 4 → Fin 7)
      = (g : Perm (Fin 7)) '' Set.range (b : Fin 4 → Fin 7) := by
  ext p
  simp only [Set.mem_range, Set.mem_image, Function.Embedding.smul_apply]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨b i, ⟨i, rfl⟩, hi⟩
  · rintro ⟨q, ⟨i, rfl⟩, hq⟩
    exact ⟨i, hq⟩

private lemma orbit_eq : MulAction.orbit (alternatingGroup (Fin 7)) SS
    = {s : Set (Fin 7) | s.ncard = 4} := by
  have hSS : SS = ({0,1,2,3} : Set (Fin 7)) := rfl
  rw [hSS]
  apply Set.Subset.antisymm
  · rintro s ⟨g, rfl⟩
    show ((g : Perm (Fin 7)) '' ({0,1,2,3} : Set (Fin 7))).ncard = 4
    rw [Set.ncard_image_of_injective ({0,1,2,3} : Set (Fin 7)) (g : Perm (Fin 7)).injective]
    simp
  · intro s hs
    rw [MulAction.mem_orbit_iff]
    obtain ⟨b, hb⟩ := exists_embedding_range ({0,1,2,3} : Set (Fin 7)) (by simp)
    obtain ⟨a, ha⟩ := exists_embedding_range s hs
    have hpre : MulAction.IsPretransitive (alternatingGroup (Fin 7)) (Fin 4 ↪ Fin 7) := by
      haveI : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 7)) (Fin 7)
          (Nat.card (Fin 7) - 2) := alternatingGroup.isMultiplyPretransitive (Fin 7)
      refine MulAction.isMultiplyPretransitive_of_le (m := 4) (n := Nat.card (Fin 7) - 2) ?_ ?_
      · rw [Nat.card_fin]; norm_num
      · exact Nat.sub_le _ _
    obtain ⟨g, hg⟩ := hpre.exists_smul_eq b a
    refine ⟨g, ?_⟩
    show (g : Perm (Fin 7)) '' ({0,1,2,3} : Set (Fin 7)) = s
    rw [← hb, ← range_smul_embedding g b, hg, ha]

theorem normalizer_V1 :
    Nat.card (Subgroup.normalizer (a7V1 : Set (alternatingGroup (Fin 7)))) = 72 ∧
    Subgroup.normalizer (a7V1 : Set (alternatingGroup (Fin 7))) =
      Subgroup.normalizer (a7K : Set (alternatingGroup (Fin 7))) := by
  have hV1 : Subgroup.normalizer (a7V1 : Set (alternatingGroup (Fin 7))) = HH :=
    le_antisymm normalizer_a7V1_le normalizer_a7V1_ge
  have hK : Subgroup.normalizer (a7K : Set (alternatingGroup (Fin 7))) = HH :=
    le_antisymm normalizer_a7K_le normalizer_a7K_ge
  have hcard : Nat.card HH = 72 := by
    have hidx : (MulAction.stabilizer (alternatingGroup (Fin 7)) SS).index = 35 := by
      rw [MulAction.index_stabilizer, orbit_eq, ncard_four_sets]
    have h := Subgroup.card_mul_index (MulAction.stabilizer (alternatingGroup (Fin 7)) SS)
    rw [hidx, Work.A7.card_alternatingGroup_seven] at h
    have : Nat.card (MulAction.stabilizer (alternatingGroup (Fin 7)) SS) = 72 := by omega
    simpa [HH] using this
  refine ⟨?_, ?_⟩
  · rw [hV1]; exact hcard
  · rw [hV1, hK]

end Work.A7F
