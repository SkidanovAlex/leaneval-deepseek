import Submission.Work.Hering.Wagner.Basic
import Submission.Work.Hering.Wagner.exists_smul_eq_of_smul_eq_of_coprime
import Submission.Work.Hering.Wagner.card_grass_two_above
import Submission.Work.Hering.Wagner.card_fixPts_eq_card_fixHyp
import Submission.Work.Hering.Wagner.card_hyp_notMem
import Submission.Work.Hering.Wagner.card_hyp_above
import Submission.Work.Hering.Wagner.closure_transvections_eq_top
import Submission.Work.Hering.Wagner.eq_transvection_of_fixes_coatom
import Submission.Work.Hering.Wagner.card_fixed_hyp_above_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Wagner's proposition: the orbit-counting steps

This file runs the proof of Wagner's proposition (Peterfalvi I §1, p.188) in the linear
setting: `V` is a finite-dimensional `𝔽₂`-space, `G ≤ GL(V)` is doubly transitive on the
nonzero vectors, and the goal is to show that the setwise stabiliser of a 3-dimensional
subspace `U` induces all of `GL(U)` on `U`.

The argument is the one of Wagner, as transcribed in `REFS/peterfalvi_I_ch3_4.md` §1:
the duality between points and hyperplanes (Burnside + the incidence-matrix identity) gives
control over the orbits of point stabilisers, which yields that `G_{a,b}` is transitive on the
`2`-dimensional subspaces `Y` with `X ⊂ Y ⊂ U` (`X = ⟨a,b⟩`), which in turn produces enough
transvections.
-/

set_option autoImplicit false

namespace Work.Hering.Wagner

open Module Submodule

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- `Gm` acts doubly transitively on the nonzero vectors of `V`. -/
def IsTwoTrans (Gm : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∀ a b c d : V, a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 → a ≠ b → c ≠ d →
    ∃ g ∈ Gm, g a = c ∧ g b = d

theorem IsTwoTrans.trans {Gm : Subgroup (V ≃ₗ[ZMod 2] V)} (h2 : IsTwoTrans Gm)
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : ∃ g ∈ Gm, g x = y := by
  by_cases h : ∃ b : V, b ≠ 0 ∧ b ≠ x
  · obtain ⟨b, hb0, hbx⟩ := h
    by_cases h' : ∃ d : V, d ≠ 0 ∧ d ≠ y
    · obtain ⟨d, hd0, hdy⟩ := h'
      obtain ⟨g, hg, hgx, -⟩ := h2 x b y d hx hb0 hy hd0 hbx.symm hdy.symm
      exact ⟨g, hg, hgx⟩
    · push Not at h'
      have hxy : x = y := h' x hx
      subst hxy
      exact ⟨1, Gm.one_mem, by simp⟩
  · push Not at h
    have hyx : y = x := h y hy
    subst hyx
    exact ⟨1, Gm.one_mem, by simp⟩

/-- The two-point stabiliser in `Gm` is transitive on the remaining nonzero vectors. -/
theorem IsTwoTrans.stabPt_trans {Gm : Subgroup (V ≃ₗ[ZMod 2] V)} (h2 : IsTwoTrans Gm)
    {a x y : V} (ha : a ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) (hxa : x ≠ a) (hya : y ≠ a) :
    ∃ g ∈ stabPt Gm a, g x = y := by
  obtain ⟨g, hg, hga, hgx⟩ := h2 a x a y ha hx ha hy hxa.symm hya.symm
  exact ⟨g, ⟨hg, MulAction.mem_stabilizer_iff.mpr (by simpa using hga)⟩, hgx⟩

/-! ## Counting helpers -/

theorem Nat.card_zmod_two : Nat.card (ZMod 2) = 2 := by simp

/-- In a space of dimension at least `2` there is a nonzero vector different from any given
nonzero vector. -/
theorem exists_ne_zero_ne_of_finrank (hV : 2 ≤ Module.finrank (ZMod 2) V) {a : V} (ha : a ≠ 0) :
    ∃ b : V, b ≠ 0 ∧ b ≠ a := by
  classical
  by_contra h
  push Not at h
  have hcard : Nat.card V ≤ 2 := by
    have hsurj : Function.Surjective (fun i : Fin 2 => if (i : ℕ) = 0 then (0 : V) else a) := by
      intro x
      rcases eq_or_ne x 0 with hx | hx
      · exact ⟨0, by simp [hx]⟩
      · exact ⟨1, by simp [h x hx]⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    simpa using this
  have hge : 4 ≤ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod_two]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Module.finrank (ZMod 2) V := Nat.pow_le_pow_right (by norm_num) hV
  omega

/-! ## The duality between points and hyperplanes -/

/-- The number of `H`-orbits on nonzero vectors equals the number of `H`-orbits on hyperplanes.
This is Lemma 2 of Peterfalvi I §1 (p.189): the incidence matrix shows that the permutation
characters agree, so Burnside's lemma gives equality of orbit counts. -/
theorem orbCount_pts_eq_orbCount_hyp (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hV : 0 < Module.finrank (ZMod 2) V) :
    orbCount H (Pts V) Set.univ = orbCount H (Hyp V) Set.univ := by
  classical
  have hP := orbCount_mul_card H (S := (Set.univ : Set (Pts V))) (fun _ _ _ _ => Set.mem_univ _)
  have hH := orbCount_mul_card H (S := (Set.univ : Set (Hyp V))) (fun _ _ _ _ => Set.mem_univ _)
  have h1 : ∀ g : H, Nat.card (fixedSubtype H (Set.univ : Set (Pts V)) g) =
      Nat.card {x : V // x ≠ 0 ∧ (g : V ≃ₗ[ZMod 2] V) x = x} := fun g =>
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, by
          show (g : V ≃ₗ[ZMod 2] V) x.1.1 = x.1.1
          exact congrArg Subtype.val x.2.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, ⟨Set.mem_univ _, by
          refine Subtype.ext ?_
          show (g : V ≃ₗ[ZMod 2] V) x.1 = x.1
          exact x.2.2⟩⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun x => Subtype.ext rfl }
  have h2 : ∀ g : H, Nat.card (fixedSubtype H (Set.univ : Set (Hyp V)) g) =
      Nat.card {L : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) V - 1 ∧
          L.map (g : V →ₗ[ZMod 2] V) = L} := fun g =>
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, by
          show x.1.1.map (g : V →ₗ[ZMod 2] V) = x.1.1
          exact congrArg Subtype.val x.2.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, ⟨Set.mem_univ _, Subtype.ext (by
          show x.1.map (g : V →ₗ[ZMod 2] V) = x.1
          exact x.2.2)⟩⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun x => Subtype.ext rfl }
  have hsum : (∑ g : H, Nat.card (fixedSubtype H (Set.univ : Set (Pts V)) g)) =
      ∑ g : H, Nat.card (fixedSubtype H (Set.univ : Set (Hyp V)) g) := by
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [h1 g, h2 g]
    exact card_fixPts_eq_card_fixHyp hV (g : V ≃ₗ[ZMod 2] V)
  rw [hP, hH] at hsum
  exact Nat.mul_right_cancel (natCard_pos_of_fintype H) hsum

/-! ## Step 1: the point stabiliser has two orbits on the hyperplanes -/

theorem hyp_smul_val (g : V ≃ₗ[ZMod 2] V) (H : Hyp V) :
    (g • H).1 = H.1.map (g : V →ₗ[ZMod 2] V) := Grass.smul_val g H

/-- The hyperplanes containing `a`. -/
def hypMem (a : V) : Set (Hyp V) := {H | a ∈ H.1}

/-- The hyperplanes not containing `a`. -/
def hypNotMem (a : V) : Set (Hyp V) := {H | a ∉ H.1}

theorem mem_hypMem {a : V} {H : Hyp V} : H ∈ hypMem a ↔ a ∈ H.1 := Iff.rfl

theorem mem_hypNotMem {a : V} {H : Hyp V} : H ∈ hypNotMem a ↔ a ∉ H.1 := Iff.rfl

theorem card_hypNotMem' {a : V} (ha : a ≠ 0) :
    Nat.card {H : Hyp V // H ∈ hypNotMem a} = 2 ^ (Module.finrank (ZMod 2) V - 1) := by
  rw [← card_hyp_notMem a ha]
  refine Nat.card_congr
    { toFun := fun H => ⟨H.1.1, H.1.2, H.2⟩
      invFun := fun H => ⟨⟨H.1, H.2.1⟩, H.2.2⟩
      left_inv := fun H => Subtype.ext rfl
      right_inv := fun H => Subtype.ext rfl }

theorem card_hypMem' {a : V} (ha : a ≠ 0) (hV : 0 < Module.finrank (ZMod 2) V) :
    Nat.card {H : Hyp V // H ∈ hypMem a} = 2 ^ (Module.finrank (ZMod 2) V - 1) - 1 := by
  have hspan : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({a} : Set V)) = 1 :=
    finrank_span_singleton ha
  have hcard := card_hyp_above (Submodule.span (ZMod 2) ({a} : Set V))
  rw [hspan] at hcard
  rw [← hcard]
  refine Nat.card_congr
    { toFun := fun H => ⟨H.1.1,
        Submodule.span_le.mpr (Set.singleton_subset_iff.mpr H.2), by
          have := H.1.2; omega⟩
      invFun := fun P => ⟨⟨P.1, by have := P.2.2; omega⟩,
        show a ∈ P.1 from Set.singleton_subset_iff.mp (Submodule.span_le.mp P.2.1)⟩
      left_inv := fun H => Subtype.ext rfl
      right_inv := fun P => Subtype.ext rfl }

/-- The point stabiliser of a nonzero vector is transitive on the remaining nonzero vectors,
hence has exactly two orbits on them. -/
theorem orbCount_stabPt_pts (Gm : Subgroup (V ≃ₗ[ZMod 2] V)) (h2 : IsTwoTrans Gm) {a : V}
    (ha : a ≠ 0) (hV : 2 ≤ Module.finrank (ZMod 2) V) :
    orbCount (stabPt Gm a) (Pts V) Set.univ = 2 := by
  classical
  obtain ⟨b, hb0, hba⟩ := exists_ne_zero_ne_of_finrank (V := V) hV ha
  have hfix : ∀ g ∈ stabPt Gm a, g • (⟨a, ha⟩ : Pts V) = ⟨a, ha⟩ := by
    intro g hg
    refine Subtype.ext ?_
    show (g : V ≃ₗ[ZMod 2] V) a = a
    exact (mem_stabPt.mp hg).2
  have hne : ({x : Pts V | x ≠ (⟨a, ha⟩ : Pts V)} : Set (Pts V)).Nonempty := by
    refine ⟨⟨b, hb0⟩, ?_⟩
    show (⟨b, hb0⟩ : Pts V) ≠ ⟨a, ha⟩
    intro h
    exact hba (congrArg Subtype.val h)
  have hcomp : orbCount (stabPt Gm a) (Pts V) {x : Pts V | x ≠ (⟨a, ha⟩ : Pts V)} = 1 := by
    refine orbCount_eq_one_of_transitive (stabPt Gm a) hne ?_
    intro x hx y hy
    have hxa : x.1 ≠ a := fun h => hx (Subtype.ext h)
    have hya : y.1 ≠ a := fun h => hy (Subtype.ext h)
    obtain ⟨g, hg, hgxy⟩ := IsTwoTrans.stabPt_trans h2 ha x.2 y.2 hxa hya
    exact ⟨g, hg, Subtype.ext hgxy⟩
  have huniv : (Set.univ : Set (Pts V)) = {x : Pts V | x ≠ (⟨a, ha⟩ : Pts V)} ∪ {⟨a, ha⟩} := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
    tauto
  have hU : ∀ g ∈ stabPt Gm a, ∀ y ∈ {x : Pts V | x ≠ (⟨a, ha⟩ : Pts V)} ∪ {⟨a, ha⟩},
      g • y ∈ {x : Pts V | x ≠ (⟨a, ha⟩ : Pts V)} ∪ {⟨a, ha⟩} := by
    intro g hg y hy
    exact huniv ▸ Set.mem_univ (g • y)
  have hS : ∀ g ∈ stabPt Gm a, ∀ y ∈ {x : Pts V | x ≠ (⟨a, ha⟩ : Pts V)},
      g • y ∈ {x : Pts V | x ≠ (⟨a, ha⟩ : Pts V)} := by
    intro g hg y hy
    exact fun h => hy (Subtype.ext (g.injective (by
      have h' : g y.1 = a := by
        have h2 := congrArg Subtype.val h
        rwa [Pts.smul_val] at h2
      rw [h', (mem_stabPt.mp hg).2])))
  rw [huniv, orbCount_eq_succ_of_union_singleton _ (by simp) hfix hS hU, hcomp]

/-- The point stabiliser has exactly two orbits on the hyperplanes (Lemma 2 of Peterfalvi I §1,
applied to `G_a`). -/
theorem orbCount_stabPt_hyp (Gm : Subgroup (V ≃ₗ[ZMod 2] V)) (h2 : IsTwoTrans Gm) {a : V}
    (ha : a ≠ 0) (hV : 2 ≤ Module.finrank (ZMod 2) V) :
    orbCount (stabPt Gm a) (Hyp V) Set.univ = 2 := by
  rw [← orbCount_pts_eq_orbCount_hyp (stabPt Gm a) (by omega)]
  exact orbCount_stabPt_pts Gm h2 ha hV

/-- **Step 1.** The point stabiliser of a nonzero vector is transitive on the hyperplanes not
containing it. -/
theorem stabPt_trans_hypNotMem (Gm : Subgroup (V ≃ₗ[ZMod 2] V)) (h2 : IsTwoTrans Gm) {a : V}
    (ha : a ≠ 0) (hV : 2 ≤ Module.finrank (ZMod 2) V) :
    ∀ H₁ ∈ hypNotMem a, ∀ H₂ ∈ hypNotMem a, ∃ g ∈ stabPt Gm a, g • H₁ = H₂ := by
  classical
  have htwo := orbCount_stabPt_hyp Gm h2 ha hV
  have hSin_inv : ∀ g ∈ stabPt Gm a, ∀ H ∈ hypMem a, g • H ∈ hypMem a := by
    intro g hg H hH
    rw [mem_hypMem] at hH ⊢
    have hga : (g : V ≃ₗ[ZMod 2] V) a = a := (mem_stabPt.mp hg).2
    rw [hyp_smul_val g H, Submodule.mem_map]
    exact ⟨a, hH, hga⟩
  have hSout_inv : ∀ g ∈ stabPt Gm a, ∀ H ∈ hypNotMem a, g • H ∈ hypNotMem a := by
    intro g hg H hH
    rw [mem_hypNotMem] at hH ⊢
    have hga : (g : V ≃ₗ[ZMod 2] V) a = a := (mem_stabPt.mp hg).2
    intro hmem
    rw [hyp_smul_val g H, Submodule.mem_map] at hmem
    obtain ⟨x, hx, hxg⟩ := hmem
    refine hH ?_
    have hxa : x = a := g.injective (by simpa [hxg, hga])
    rw [← hxa]
    exact hx
  have huniv : (Set.univ : Set (Hyp V)) = hypMem a ∪ hypNotMem a := by
    ext H
    constructor
    · intro _
      rw [Set.mem_union, mem_hypMem, mem_hypNotMem]
      by_cases h : a ∈ H.1
      · exact Or.inl h
      · exact Or.inr h
    · intro _
      exact Set.mem_univ H
  have hdisj : Disjoint (hypMem a) (hypNotMem a) := by
    rw [Set.disjoint_left]
    intro H h1 h2
    rw [mem_hypMem] at h1
    rw [mem_hypNotMem] at h2
    exact h2 h1
  have hU : ∀ g ∈ stabPt Gm a, ∀ H ∈ hypMem a ∪ hypNotMem a,
      g • H ∈ hypMem a ∪ hypNotMem a := by
    intro g hg H hH
    have hUu : hypMem a ∪ hypNotMem a = (Set.univ : Set (Hyp V)) := huniv.symm
    rw [hUu]
    exact Set.mem_univ _
  have hsum : orbCount (stabPt Gm a) (Hyp V) (hypNotMem a) +
      orbCount (stabPt Gm a) (Hyp V) (hypMem a) = 2 := by
    rw [add_comm, ← orbCount_union _ hdisj hSin_inv hSout_inv hU, ← huniv, htwo]
  have hSin_ne : (hypMem a).Nonempty := by
    have hc := card_hypMem' (V := V) (a := a) ha (by omega)
    have hpos : 0 < Nat.card {H : Hyp V // H ∈ hypMem a} := by
      rw [hc]
      have h1 : 1 ≤ Module.finrank (ZMod 2) V - 1 := by omega
      have h2' : 2 ≤ 2 ^ (Module.finrank (ZMod 2) V - 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (Module.finrank (ZMod 2) V - 1) := Nat.pow_le_pow_right (by norm_num) h1
      omega
    obtain ⟨hne, _⟩ := Nat.card_pos_iff.mp hpos
    obtain ⟨H⟩ := hne
    exact ⟨H.1, H.2⟩
  have hSout_ne : (hypNotMem a).Nonempty := by
    have hc := card_hypNotMem' (V := V) (a := a) ha
    have hpos : 0 < Nat.card {H : Hyp V // H ∈ hypNotMem a} := by
      rw [hc]; positivity
    obtain ⟨hne, _⟩ := Nat.card_pos_iff.mp hpos
    obtain ⟨H⟩ := hne
    exact ⟨H.1, H.2⟩
  have h1 := one_le_orbCount_of_nonempty (stabPt Gm a) hSout_ne
  have h2' := one_le_orbCount_of_nonempty (stabPt Gm a) hSin_ne
  have hout : orbCount (stabPt Gm a) (Hyp V) (hypNotMem a) = 1 := by omega
  exact transitive_of_orbCount_eq_one _ hout

/-! ## Step 2: coprime orbit counts

`G_a` is transitive on the 2-spaces through `a` and on the hyperplanes avoiding `a`; the
corresponding orbit sizes `2^{n-1}-1` and `2^{n-1}` are coprime, so by the standard
coprime-orbit lemma the stabiliser of a 2-space `X` is still transitive on the hyperplanes
avoiding `a` (Peterfalvi I §1, step 2).
-/

theorem coprime_two_pow_sub_one (m : ℕ) : Nat.Coprime (2 ^ m - 1) (2 ^ m) := by
  have h : 2 ^ m - 1 + 1 = 2 ^ m := Nat.sub_add_cancel (Nat.one_le_two_pow)
  rw [← h]
  exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)

/-- The 2-dimensional subspaces containing a fixed nonzero vector, as a subset of `Grass V 2`. -/
def grassTwoMem (a : V) : Set (Grass V 2) := {Y | Submodule.span (ZMod 2) ({a} : Set V) ≤ Y.1}

theorem mem_grassTwoMem {a : V} {Y : Grass V 2} :
    Y ∈ grassTwoMem a ↔ Submodule.span (ZMod 2) ({a} : Set V) ≤ Y.1 := Iff.rfl

theorem card_grassTwoMem' {a : V} (ha : a ≠ 0) :
    Nat.card {Y : Grass V 2 // Y ∈ grassTwoMem a} = 2 ^ (Module.finrank (ZMod 2) V - 1) - 1 := by
  rw [← card_grass_two_above a ha]
  refine Nat.card_congr
    { toFun := fun Y => ⟨Y.1.1, Y.2, Y.1.2⟩
      invFun := fun Y => ⟨⟨Y.1, Y.2.2⟩, Y.2.1⟩
      left_inv := fun Y => Subtype.ext rfl
      right_inv := fun Y => Subtype.ext rfl }

/-- Every 2-dimensional subspace containing a nonzero vector `a` is `⟨a⟩ ⊔ ⟨b⟩` for some
`b ∉ ⟨a⟩`. -/
theorem exists_sup_span_eq_of_finrank_two {a : V} {Y : Submodule (ZMod 2) V}
    (ha : a ≠ 0) (hle : (Submodule.span (ZMod 2) ({a} : Set V)) ≤ Y)
    (hf : Module.finrank (ZMod 2) Y = 2) :
    ∃ b : V, b ∉ Submodule.span (ZMod 2) ({a} : Set V) ∧
      (Submodule.span (ZMod 2) ({a} : Set V)) ⊔ (Submodule.span (ZMod 2) ({b} : Set V)) = Y := by
  classical
  have hfa : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({a} : Set V)) = 1 :=
    finrank_span_singleton ha
  have hlt : (Submodule.span (ZMod 2) ({a} : Set V)) < Y := by
    rw [lt_iff_le_and_ne]
    refine ⟨hle, fun h => ?_⟩
    rw [← h, hfa] at hf
    omega
  obtain ⟨b, hbY, hbs⟩ := SetLike.exists_of_lt hlt
  refine ⟨b, hbs, ?_⟩
  let A : Submodule (ZMod 2) V := Submodule.span (ZMod 2) ({a} : Set V)
  let B : Submodule (ZMod 2) V := Submodule.span (ZMod 2) ({b} : Set V)
  let Z : Submodule (ZMod 2) V := A ⊔ B
  have hAeq : A = Submodule.span (ZMod 2) ({a} : Set V) := rfl
  have hBeq : B = Submodule.span (ZMod 2) ({b} : Set V) := rfl
  have hZdef : Z = A ⊔ B := rfl
  have hab : a ≠ b := fun h => hbs (by rw [← h]; exact Submodule.mem_span_singleton_self a)
  have hb0 : b ≠ 0 := fun h => hbs (by rw [h]; exact Submodule.zero_mem _)
  have hfA : Module.finrank (ZMod 2) A = 1 := by rw [hAeq]; exact hfa
  have hfB : Module.finrank (ZMod 2) B = 1 := by rw [hBeq]; exact finrank_span_singleton hb0
  have hdisj : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [hAeq] at hx1
    rw [hBeq] at hx2
    change x ∈ Submodule.span (ZMod 2) ({a} : Set V) at hx1
    change x ∈ Submodule.span (ZMod 2) ({b} : Set V) at hx2
    rw [Submodule.mem_span_singleton] at hx1 hx2
    obtain ⟨c, hc⟩ := hx1
    obtain ⟨d, hd⟩ := hx2
    rcases eq_or_ne c 0 with hc0 | hc0
    · rw [hc0, zero_smul] at hc
      exact hc.symm
    · have hc1 : c = 1 := by
        have hv : c.val = 1 := by
          have hlt2 : c.val < 2 := ZMod.val_lt c
          rcases Nat.eq_zero_or_pos c.val with h0 | hpos
          · exact absurd ((ZMod.val_eq_zero c).mp h0) hc0
          · omega
        exact (ZMod.val_eq_one (by norm_num : 1 < 2) c).mp hv
      rw [hc1, one_smul] at hc
      rcases eq_or_ne d 0 with hd0 | hd0
      · rw [hd0, zero_smul] at hd
        exact hd.symm
      · have hd1 : d = 1 := by
          have hv : d.val = 1 := by
            have hlt2 : d.val < 2 := ZMod.val_lt d
            rcases Nat.eq_zero_or_pos d.val with h0 | hpos
            · exact absurd ((ZMod.val_eq_zero d).mp h0) hd0
            · omega
          exact (ZMod.val_eq_one (by norm_num : 1 < 2) d).mp hv
        rw [hd1, one_smul] at hd
        exact absurd (hc.trans hd.symm) hab
  have hfinZ : Module.finrank (ZMod 2) Z = 2 := by
    rw [hZdef]
    have h := Submodule.finrank_sup_add_finrank_inf_eq A B
    rw [hfA, hfB, hdisj, finrank_bot] at h
    omega
  have hZle : Z ≤ Y := by
    rw [hZdef]
    refine sup_le ?_ ?_
    · rw [hAeq]; exact hle
    · rw [hBeq]; exact (Submodule.span_singleton_le_iff_mem b Y).mpr hbY
  rw [← hZdef]
  exact Submodule.eq_of_le_of_finrank_eq hZle (by rw [hfinZ, hf])

theorem grassTwoMem_inv (Gm : Subgroup (V ≃ₗ[ZMod 2] V)) {a : V} (ha : a ≠ 0) :
    ∀ g ∈ stabPt Gm a, ∀ Y ∈ grassTwoMem a, g • Y ∈ grassTwoMem a := by
  intro g hg Y hY
  rw [mem_grassTwoMem] at hY ⊢
  have hga : (g : V ≃ₗ[ZMod 2] V) a = a := (mem_stabPt.mp hg).2
  have hspan : Submodule.span (ZMod 2) ({a} : Set V) =
      (Submodule.span (ZMod 2) ({a} : Set V)).map (g : V →ₗ[ZMod 2] V) := by
    rw [Submodule.map_span, Set.image_singleton]
    exact Submodule.span_singleton_eq_span_singleton.mpr ⟨1, by simpa using hga.symm⟩
  rw [Grass.smul_val, hspan]
  exact Submodule.map_mono hY

theorem hypNotMem_inv (Gm : Subgroup (V ≃ₗ[ZMod 2] V)) {a : V} (ha : a ≠ 0) :
    ∀ g ∈ stabPt Gm a, ∀ H ∈ hypNotMem a, g • H ∈ hypNotMem a := by
  intro g hg H hH
  rw [mem_hypNotMem] at hH ⊢
  have hga : (g : V ≃ₗ[ZMod 2] V) a = a := (mem_stabPt.mp hg).2
  rw [hyp_smul_val g H]
  rintro ⟨x, hx, hxg⟩
  refine hH ?_
  have hxa : x = a := g.injective (by simpa [hxg, hga])
  rw [← hxa]
  exact hx

/-- `G_a` is transitive on the 2-dimensional subspaces containing `a`. -/
theorem stabPt_trans_grassTwoMem (Gm : Subgroup (V ≃ₗ[ZMod 2] V)) (h2 : IsTwoTrans Gm) {a : V}
    (ha : a ≠ 0) :
    ∀ Y ∈ grassTwoMem a, ∀ Y' ∈ grassTwoMem a, ∃ g ∈ stabPt Gm a, g • Y = Y' := by
  intro Y hY Y' hY'
  rw [mem_grassTwoMem] at hY hY'
  obtain ⟨b, hbs, hbY⟩ := exists_sup_span_eq_of_finrank_two ha hY Y.2
  obtain ⟨b', hb's, hb'Y⟩ := exists_sup_span_eq_of_finrank_two ha hY' Y'.2
  have hb0 : b ≠ 0 := fun h => hbs (by rw [h]; exact Submodule.zero_mem _)
  have hb'0 : b' ≠ 0 := fun h => hb's (by rw [h]; exact Submodule.zero_mem _)
  have hab : a ≠ b := fun h => hbs (by rw [← h]; exact Submodule.mem_span_singleton_self a)
  have hab' : a ≠ b' := fun h => hb's (by rw [← h]; exact Submodule.mem_span_singleton_self a)
  obtain ⟨g, hgG, hga, hgb⟩ := h2 a b a b' ha hb0 ha hb'0 hab hab'
  refine ⟨g, ⟨hgG, MulAction.mem_stabilizer_iff.mpr (by simpa using hga)⟩, ?_⟩
  refine Subtype.ext ?_
  show Submodule.map (g : V →ₗ[ZMod 2] V) Y.1 = Y'.1
  rw [← hbY, ← hb'Y, Submodule.map_sup]
  congr 1
  · rw [Submodule.map_span, Set.image_singleton]
    exact Submodule.span_singleton_eq_span_singleton.mpr ⟨1, by simpa using hga⟩
  · rw [Submodule.map_span, Set.image_singleton]
    exact Submodule.span_singleton_eq_span_singleton.mpr ⟨1, by simpa using hgb⟩

/-- **Step 2.** The stabiliser of a 2-dimensional subspace `X` containing `a` (inside `G_a`) is
still transitive on the hyperplanes not containing `a`. -/
theorem stabPt_inf_stabSub_trans_hypNotMem (Gm : Subgroup (V ≃ₗ[ZMod 2] V)) (h2 : IsTwoTrans Gm)
    {a : V} (ha : a ≠ 0) (hV : 2 ≤ Module.finrank (ZMod 2) V)
    (X : Submodule (ZMod 2) V) (hXle : Submodule.span (ZMod 2) ({a} : Set V) ≤ X)
    (hXf : Module.finrank (ZMod 2) X = 2) :
    ∀ H₁ ∈ hypNotMem a, ∀ H₂ ∈ hypNotMem a,
      ∃ g ∈ stabPt Gm a ⊓ stabSub X, g • H₁ = H₂ := by
  classical
  intro H₁ hH₁ H₂ hH₂
  letI : MulAction (stabPt Gm a) ↥(grassTwoMem a) :=
    mulActionSubtype _ _ (grassTwoMem_inv Gm ha)
  letI : MulAction (stabPt Gm a) ↥(hypNotMem a) :=
    mulActionSubtype _ _ (hypNotMem_inv Gm ha)
  have hA : ∀ Y Y' : ↥(grassTwoMem a), ∃ g : stabPt Gm a, g • Y = Y' := by
    intro Y Y'
    obtain ⟨g, hg, hgY⟩ := stabPt_trans_grassTwoMem Gm h2 ha Y.1 Y.2 Y'.1 Y'.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgY⟩
  have hB : ∀ H H' : ↥(hypNotMem a), ∃ g : stabPt Gm a, g • H = H' := by
    intro H H'
    obtain ⟨g, hg, hgH⟩ := stabPt_trans_hypNotMem Gm h2 ha hV H.1 H.2 H'.1 H'.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgH⟩
  have hcop : Nat.Coprime (Nat.card ↥(grassTwoMem a)) (Nat.card ↥(hypNotMem a)) := by
    rw [card_grassTwoMem' ha, card_hypNotMem' ha]
    exact coprime_two_pow_sub_one _
  obtain ⟨g, hgX, hgH⟩ :=
    exists_smul_eq_of_smul_eq_of_coprime hA hB (⟨⟨X, hXf⟩, hXle⟩ : ↥(grassTwoMem a)) hcop
      ⟨H₁, hH₁⟩ ⟨H₂, hH₂⟩
  refine ⟨(g : V ≃ₗ[ZMod 2] V), ⟨g.2, ?_⟩, ?_⟩
  · have h1 : (g • (⟨X, hXf⟩ : Grass V 2)).1 = X :=
      congrArg Subtype.val (congrArg Subtype.val hgX)
    show X.map (g : V →ₗ[ZMod 2] V) = X
    exact h1
  · show (g : V ≃ₗ[ZMod 2] V) • H₁ = H₂
    exact congrArg Subtype.val hgH

/-! ## Step 3: transitivity on the hyperplanes containing `a` but not `b` -/

/-- A hyperplane containing `a` and not `b` meets `⟨a⟩ ⊔ ⟨b⟩` in `⟨a⟩` (elementwise form). -/
theorem mem_span_singleton_of_mem_sup_span {a b : V} (ha : a ≠ 0) {H : Submodule (ZMod 2) V}
    (haH : a ∈ H) (hbH : b ∉ H) {x : V} (hxH : x ∈ H)
    (hxX : x ∈ (Submodule.span (ZMod 2) ({a} : Set V)) ⊔ (Submodule.span (ZMod 2) ({b} : Set V))) :
    x ∈ Submodule.span (ZMod 2) ({a} : Set V) := by
  classical
  rw [Submodule.mem_sup] at hxX
  obtain ⟨p, hpA, q, hqB, hpq⟩ := hxX
  rw [Submodule.mem_span_singleton] at hpA hqB
  obtain ⟨α, hα⟩ := hpA
  obtain ⟨β, hβ⟩ := hqB
  rcases eq_or_ne β 0 with hβ0 | hβ0
  · rw [hβ0, zero_smul] at hβ
    rw [Submodule.mem_span_singleton]
    exact ⟨α, by rw [hα, ← hpq, ← hβ, add_zero]⟩
  · exfalso
    have hβ1 : β = 1 := by
      have hv : β.val = 1 := by
        have hlt2 : β.val < 2 := ZMod.val_lt β
        rcases Nat.eq_zero_or_pos β.val with h0 | hpos
        · exact absurd ((ZMod.val_eq_zero β).mp h0) hβ0
        · omega
      exact (ZMod.val_eq_one (by norm_num : 1 < 2) β).mp hv
    rw [hβ1, one_smul] at hβ
    have hpH : p ∈ H := by rw [← hα]; exact Submodule.smul_mem _ α haH
    have hqH : q ∈ H := by
      have hq_eq : q = x - p := by rw [← hpq]; simp
      rw [hq_eq]; exact H.sub_mem hxH hpH
    exact hbH (by rw [hβ]; exact hqH)

/-- **Step 3.** `G_{a,b}` is transitive on the hyperplanes containing `a` but not `b`. -/
theorem stabPt_stabPt_trans_hypMem (Gm : Subgroup (V ≃ₗ[ZMod 2] V)) (h2 : IsTwoTrans Gm)
    {a b : V} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hV : 2 ≤ Module.finrank (ZMod 2) V) :
    ∀ H₁ ∈ {H : Hyp V | a ∈ H.1 ∧ b ∉ H.1}, ∀ H₂ ∈ {H : Hyp V | a ∈ H.1 ∧ b ∉ H.1},
      ∃ g ∈ stabPt (stabPt Gm a) b, g • H₁ = H₂ := by
  classical
  intro H₁ hH₁ H₂ hH₂
  obtain ⟨ha₁, hb₁⟩ := hH₁
  obtain ⟨ha₂, hb₂⟩ := hH₂
  let A : Submodule (ZMod 2) V := Submodule.span (ZMod 2) ({a} : Set V)
  let B : Submodule (ZMod 2) V := Submodule.span (ZMod 2) ({b} : Set V)
  let X : Submodule (ZMod 2) V := A ⊔ B
  have hAeq : A = Submodule.span (ZMod 2) ({a} : Set V) := rfl
  have hBeq : B = Submodule.span (ZMod 2) ({b} : Set V) := rfl
  have hXdef : X = A ⊔ B := rfl
  have hfA : Module.finrank (ZMod 2) A = 1 := by rw [hAeq]; exact finrank_span_singleton ha
  have hfB : Module.finrank (ZMod 2) B = 1 := by rw [hBeq]; exact finrank_span_singleton hb
  have hdisj : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [hAeq] at hx1
    rw [hBeq] at hx2
    change x ∈ Submodule.span (ZMod 2) ({a} : Set V) at hx1
    change x ∈ Submodule.span (ZMod 2) ({b} : Set V) at hx2
    rw [Submodule.mem_span_singleton] at hx1 hx2
    obtain ⟨c, hc⟩ := hx1
    obtain ⟨d, hd⟩ := hx2
    rcases eq_or_ne c 0 with hc0 | hc0
    · rw [hc0, zero_smul] at hc
      exact hc.symm
    · have hc1 : c = 1 := by
        have hv : c.val = 1 := by
          have hlt2 : c.val < 2 := ZMod.val_lt c
          rcases Nat.eq_zero_or_pos c.val with h0 | hpos
          · exact absurd ((ZMod.val_eq_zero c).mp h0) hc0
          · omega
        exact (ZMod.val_eq_one (by norm_num : 1 < 2) c).mp hv
      rw [hc1, one_smul] at hc
      rcases eq_or_ne d 0 with hd0 | hd0
      · rw [hd0, zero_smul] at hd
        exact hd.symm
      · have hd1 : d = 1 := by
          have hv : d.val = 1 := by
            have hlt2 : d.val < 2 := ZMod.val_lt d
            rcases Nat.eq_zero_or_pos d.val with h0 | hpos
            · exact absurd ((ZMod.val_eq_zero d).mp h0) hd0
            · omega
          exact (ZMod.val_eq_one (by norm_num : 1 < 2) d).mp hv
        rw [hd1, one_smul] at hd
        exact absurd (hc.trans hd.symm) hab
  have hfX : Module.finrank (ZMod 2) X = 2 := by
    rw [hXdef]
    have h := Submodule.finrank_sup_add_finrank_inf_eq A B
    rw [hfA, hfB, hdisj, finrank_bot] at h
    omega
  have hBle : B ≤ X := by rw [hXdef]; exact le_sup_right
  obtain ⟨g, hg, hgH⟩ := stabPt_inf_stabSub_trans_hypNotMem Gm h2 hb hV X hBle hfX H₁ hb₁ H₂ hb₂
  obtain ⟨hgb, hgX⟩ := hg
  have hgb' : (g : V ≃ₗ[ZMod 2] V) b = b := (mem_stabPt.mp hgb).2
  -- `g a = a`
  have hga_mem_H₂ : (g : V ≃ₗ[ZMod 2] V) a ∈ H₂.1 := by
    have : g • H₁ = H₂ := hgH
    rw [← this, hyp_smul_val]
    exact Submodule.mem_map_of_mem ha₁
  have hga_mem_X : (g : V ≃ₗ[ZMod 2] V) a ∈ X := by
    have hmem : a ∈ X := by rw [hXdef]; exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self a)
    have hmap : (g : V ≃ₗ[ZMod 2] V) a ∈ X.map (g : V →ₗ[ZMod 2] V) :=
      Submodule.mem_map_of_mem hmem
    rwa [show X.map (g : V →ₗ[ZMod 2] V) = X from hgX] at hmap
  have hga_in_A : (g : V ≃ₗ[ZMod 2] V) a ∈ A :=
    mem_span_singleton_of_mem_sup_span ha ha₂ hb₂ hga_mem_H₂ (by
      rw [← hXdef]; exact hga_mem_X)
  have hga : (g : V ≃ₗ[ZMod 2] V) a = a := by
    rw [hAeq, Submodule.mem_span_singleton] at hga_in_A
    obtain ⟨α, hα⟩ := hga_in_A
    have hg0 : (g : V ≃ₗ[ZMod 2] V) a ≠ 0 := by
      intro h
      exact ha (g.injective (by rw [h]; simp))
    rcases eq_or_ne α 0 with hα0 | hα0
    · rw [hα0, zero_smul] at hα
      exact absurd hα.symm hg0
    · have hα1 : α = 1 := by
        have hv : α.val = 1 := by
          have hlt2 : α.val < 2 := ZMod.val_lt α
          rcases Nat.eq_zero_or_pos α.val with h0 | hpos
          · exact absurd ((ZMod.val_eq_zero α).mp h0) hα0
          · omega
        exact (ZMod.val_eq_one (by norm_num : 1 < 2) α).mp hv
      rw [hα1, one_smul] at hα
      exact hα.symm
  exact ⟨g, ⟨⟨hgb.1, MulAction.mem_stabilizer_iff.mpr (by simpa using hga)⟩,
    MulAction.mem_stabilizer_iff.mpr (by simpa using hgb')⟩, hgH⟩

/-! ## The subgroup of `GL(U)` induced by `Gm` -/

def inducedSub (Gm : Subgroup (V ≃ₗ[ZMod 2] V)) (U : Submodule (ZMod 2) V) :
    Subgroup (U ≃ₗ[ZMod 2] U) where
  carrier := {τ | ∃ g ∈ Gm, ∀ u : U, g (u : V) = (τ u : V)}
  one_mem' := ⟨1, Gm.one_mem, by intro u; simp⟩
  mul_mem' := by
    intro σ τ hσ hτ
    obtain ⟨g, hg, hgσ⟩ := hσ
    obtain ⟨h, hh, hhτ⟩ := hτ
    refine ⟨g * h, Gm.mul_mem hg hh, fun u => ?_⟩
    calc (g * h) (u : V) = g (h (u : V)) := LinearEquiv.mul_apply g h (u : V)
      _ = g (((τ u : U)) : V) := by rw [hhτ u]
      _ = ((σ * τ) u : V) := by rw [LinearEquiv.mul_apply, hgσ (τ u)]
  inv_mem' := by
    intro σ hσ
    obtain ⟨g, hg, hgσ⟩ := hσ
    refine ⟨g⁻¹, Gm.inv_mem hg, fun u => ?_⟩
    have h1 : g (((σ⁻¹) u : U) : V) = (u : V) := by
      have h2 := hgσ (σ⁻¹ u)
      simpa using h2
    calc g⁻¹ (u : V) = g⁻¹ (g (((σ⁻¹) u : U) : V)) := by rw [← h1]
      _ = ((σ⁻¹) u : V) := LinearEquiv.symm_apply_apply g (((σ⁻¹) u : U) : V)

theorem mem_inducedSub {Gm : Subgroup (V ≃ₗ[ZMod 2] V)} {U : Submodule (ZMod 2) V}
    {τ : U ≃ₗ[ZMod 2] U} :
    τ ∈ inducedSub Gm U ↔ ∃ g ∈ Gm, ∀ u : U, g (u : V) = (τ u : V) := Iff.rfl

end Work.Hering.Wagner
