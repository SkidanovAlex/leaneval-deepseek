import Mathlib
import Submission.Work.SSGRoute.wordBarDefs
import Submission.Work.SSGRoute.dswClashFree
import Submission.Work.SSGRoute.lieSpanNested
import Submission.Work.SSGRoute.wordInvolution_ker_eq_im
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The degree-`j` part of the free `𝔽₂`-Lie algebra is `σ`-regular for odd `j`
-/

noncomputable section

open Work.SSGRoute.prop5

namespace Work.SSGRoute

variable {X : Type*}

/-! ## The left-normed map, over `ℤ` and over `𝔽₂` -/

/-- The coefficient map `ℤ⟨X⟩ → (FreeMonoid X →₀ ℤ)` as a `ℤ`-linear map. -/
def coeffLin (X : Type*) : FreeAssoc X →ₗ[ℤ] (FreeMonoid X →₀ ℤ) where
  toFun := MonoidAlgebra.coeff
  map_add' a b := MonoidAlgebra.coeff_add a b
  map_smul' c a := by
    ext w
    rw [MonoidAlgebra.coeff_smul_apply]
    rfl

@[simp] theorem coeffLin_apply (X : Type*) (a : FreeAssoc X) :
    coeffLin X a = a.coeff := rfl

/-- The `ℤ`-linear left-normed bracket map on `ℤ⟨X⟩`: on a word, `w ↦ lnMon w`. -/
def lnMonLin (X : Type*) : FreeAssoc X →ₗ[ℤ] FreeAssoc X :=
  (Finsupp.linearCombination ℤ (fun w : FreeMonoid X => lnMon (FreeMonoid.toList w))).comp
    (coeffLin X)

/-- The `𝔽₂`-linear left-normed bracket map on `𝔽₂⟨X⟩`. -/
def LamBar (X : Type*) : WordBar X →ₗ[ZMod 2] WordBar X :=
  Finsupp.linearCombination (ZMod 2) (fun w : FreeMonoid X =>
    redZ X (lnMon (FreeMonoid.toList w)))

@[simp] theorem redZ_single (w : FreeMonoid X) (c : ℤ) :
    redZ X (MonoidAlgebra.single w c) = Finsupp.single w ((c : ZMod 2)) := by
  ext k
  rw [redZ_apply, MonoidAlgebra.coeff_mapRingHom]
  by_cases h : k = w
  · subst h; simp [MonoidAlgebra.coeff_single]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne h]
    simp

@[simp] theorem lnMonLin_wordEl (w : List X) : lnMonLin X (wordEl w) = lnMon w := by
  show Finsupp.linearCombination ℤ (fun v : FreeMonoid X => lnMon (FreeMonoid.toList v))
      (coeffLin X (wordEl w)) = lnMon w
  rw [coeffLin_apply,
    show (wordEl (X := X) w).coeff
      = Finsupp.single (FreeMonoid.ofList w) (1 : ℤ) from MonoidAlgebra.coeff_single _ _,
    Finsupp.linearCombination_single, one_smul, FreeMonoid.toList_ofList]

@[simp] theorem LamBar_single (w : FreeMonoid X) (c : ZMod 2) :
    LamBar X (Finsupp.single w c) = c • redZ X (lnMon (FreeMonoid.toList w)) := by
  show Finsupp.linearCombination (ZMod 2) (fun v : FreeMonoid X =>
      redZ X (lnMon (FreeMonoid.toList v))) (Finsupp.single w c) = _
  rw [Finsupp.linearCombination_single]

/-- The Dynkin/Specht–Wever identity mod `2`: on the Lie part of degree `j`, the left-normed map
acts by `j`. -/
theorem lnMonLin_lieSpan (j : ℕ) {x : FreeAssoc X} (hx : x ∈ lieSpan X j) :
    lnMonLin X x = (j : ℤ) • x :=
  nestedBracket_dswC X j (lnMonLin X) (fun w => lnMonLin_wordEl w) hx

/-- Reduction commutes with the left-normed map. -/
theorem LamBar_redZ (a : FreeAssoc X) : LamBar X (redZ X a) = redZ X (lnMonLin X a) := by
  induction a using MonoidAlgebra.induction_on with
  | of m =>
      rw [MonoidAlgebra.of_apply ℤ (FreeMonoid X) m, redZ_single, LamBar_single, Int.cast_one,
        one_smul]
      rw [show lnMonLin X (MonoidAlgebra.single m (1 : ℤ)) = lnMon (FreeMonoid.toList m) from by
        show Finsupp.linearCombination ℤ (fun v : FreeMonoid X => lnMon (FreeMonoid.toList v))
          (coeffLin X (MonoidAlgebra.single m (1:ℤ))) = _
        rw [coeffLin_apply, MonoidAlgebra.coeff_single, Finsupp.linearCombination_single,
          one_smul]]
  | add a b iha ihb =>
      rw [map_add, map_add, iha, ihb, map_add, map_add]
  | smul c a iha =>
      rw [map_zsmul (redZ X) c a, map_zsmul (LamBar X) c (redZ X a), iha,
        ← map_zsmul (redZ X) c (lnMonLin X a), ← map_zsmul (lnMonLin X) c a]

/-! ## The relabelling algebra automorphism of `ℤ⟨X⟩` -/

/-- The algebra automorphism of `ℤ⟨X⟩` induced by a permutation `σ` of `X`. -/
def freeAssocPerm (X : Type*) (σ : X ≃ X) : FreeAssoc X →ₐ[ℤ] FreeAssoc X :=
  MonoidAlgebra.lift ℤ (FreeAssoc X) (FreeMonoid X)
    ((MonoidAlgebra.of ℤ (FreeMonoid X)).comp (FreeMonoid.map (σ : X → X)))

theorem freeAssocPerm_single (σ : X ≃ X) (m : FreeMonoid X) (c : ℤ) :
    freeAssocPerm X σ (MonoidAlgebra.single m c)
      = MonoidAlgebra.single (FreeMonoid.map (σ : X → X) m) c := by
  rw [freeAssocPerm, MonoidAlgebra.lift_single, MonoidHom.comp_apply,
    MonoidAlgebra.of_apply, MonoidAlgebra.smul_single']
  simp

theorem freeAssocPerm_wordEl (σ : X ≃ X) (y : X) :
    freeAssocPerm X σ (wordEl [y]) = wordEl [σ y] := by
  rw [show wordEl (X := X) [y] = MonoidAlgebra.single (FreeMonoid.of y) (1:ℤ) from rfl,
    freeAssocPerm_single]
  rfl

/-- Coefficient reduction commutes with the relabelling. -/
theorem redZ_freeAssocPerm (σ : X ≃ X) (a : FreeAssoc X) :
    redZ X (freeAssocPerm X σ a) = wordBarσ X σ (redZ X a) := by
  induction a using MonoidAlgebra.induction_on with
  | of m =>
      rw [MonoidAlgebra.of_apply ℤ (FreeMonoid X) m, freeAssocPerm_single, redZ_single,
        redZ_single, wordBarσ_single]
  | add a b iha ihb =>
      rw [map_add (freeAssocPerm X σ) a b, map_add (redZ X) _ _, map_add (redZ X) a b,
        map_add (wordBarσ X σ) (redZ X a) (redZ X b), iha, ihb]
  | smul c a iha =>
      rw [map_zsmul (freeAssocPerm X σ) c a, map_zsmul (redZ X) c (freeAssocPerm X σ a),
        iha, map_zsmul (redZ X) c a, ← map_zsmul (wordBarσ X σ) c (redZ X a)]

theorem freeAssocPerm_lnMon_foldl (σ : X ≃ X) :
    ∀ (u : List X) (init : FreeAssoc X),
      freeAssocPerm X σ (u.foldl (fun acc y => acc * wordEl [y] - wordEl [y] * acc) init)
        = (u.map (σ : X → X)).foldl
            (fun acc y => acc * wordEl [y] - wordEl [y] * acc) (freeAssocPerm X σ init) := by
  intro u
  induction u with
  | nil => intro init; rfl
  | cons y rest ih =>
      intro init
      rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih]
      rw [show freeAssocPerm X σ (init * wordEl [y] - wordEl [y] * init)
          = freeAssocPerm X σ init * wordEl [σ y] - wordEl [σ y] * freeAssocPerm X σ init from by
        rw [map_sub, map_mul, map_mul, freeAssocPerm_wordEl]]

theorem freeAssocPerm_lnMon (σ : X ≃ X) (w : List X) :
    freeAssocPerm X σ (lnMon w) = lnMon (w.map (σ : X → X)) := by
  cases w with
  | nil => rfl
  | cons x rest =>
      show freeAssocPerm X σ
          (rest.foldl (fun acc y => acc * wordEl [y] - wordEl [y] * acc) (wordEl [x]))
        = (rest.map (σ : X → X)).foldl
            (fun acc y => acc * wordEl [y] - wordEl [y] * acc) (wordEl [σ x])
      rw [freeAssocPerm_lnMon_foldl, freeAssocPerm_wordEl]

/-- The left-normed map is `σ`-equivariant. -/
theorem LamBar_wordBarσ (σ : X ≃ X) (v : WordBar X) :
    LamBar X (wordBarσ X σ v) = wordBarσ X σ (LamBar X v) := by
  induction v using Finsupp.induction_linear with
  | zero => rw [map_zero (wordBarσ X σ), map_zero (LamBar X), map_zero (wordBarσ X σ)]
  | add f g hf hg =>
      rw [map_add (wordBarσ X σ) f g, map_add (LamBar X) (wordBarσ X σ f) (wordBarσ X σ g),
        map_add (LamBar X) f g, hf, hg, map_add (wordBarσ X σ) (LamBar X f) (LamBar X g)]
  | single w c =>
      rw [wordBarσ_single, LamBar_single, LamBar_single, map_smul, ← redZ_freeAssocPerm,
        freeAssocPerm_lnMon, FreeMonoid.toList_map]

/-! ## Degree bookkeeping -/

theorem natCast_zmodTwo_eq_one {j : ℕ} (hj : Odd j) : (j : ZMod 2) = 1 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  rcases hj with ⟨k, rfl⟩
  push_cast
  rw [h2]
  ring

/-- The bracket monomial of a tree of size `j` is a `ℤ`-combination of words of length `j`. -/
theorem brkMon_mem_wordSpan (c : Magma X) :
    brkMon X c ∈ wordSpan (X := X) (Magma.size c) := by
  induction c with
  | gen x => exact Submodule.subset_span ⟨[x], rfl, rfl⟩
  | mul a b iha ihb =>
      rw [brkMon_mul, Magma.size_mul]
      exact Submodule.sub_mem _
        (wordSpan_mul_mem (p := Magma.size a) (q := Magma.size b) iha ihb)
        (by rw [Nat.add_comm]
            exact wordSpan_mul_mem (p := Magma.size b) (q := Magma.size a) ihb iha)

/-- Every element of `barLie X j` is supported in words of length `j`. -/
theorem barLie_degree {j : ℕ} {v : WordBar X} (hv : v ∈ barLie X j) :
    ∀ w : FreeMonoid X, w.length ≠ j → v w = 0 := by
  refine Submodule.span_induction (p := fun v _ => ∀ w, w.length ≠ j → v w = 0) ?_ ?_ ?_ ?_ hv
  · rintro v ⟨c, rfl⟩ w hw
    change (redZ X (brkMon X c.1)) w = 0
    rw [redZ_apply, MonoidAlgebra.coeff_mapRingHom]
    have h0 : (brkMon X c.1).coeff w = 0 :=
      (mem_wordSpan_iff (Magma.size c.1) (brkMon X c.1)).mp (brkMon_mem_wordSpan c.1) w
        (by intro h; exact hw (by rw [← c.2]; exact h))
    rw [h0]; simp
  · intro w _; simp
  · intro v₁ v₂ _ _ h₁ h₂ w hw
    rw [Finsupp.add_apply, h₁ w hw, h₂ w hw, add_zero]
  · intro t v _ h w hw
    rw [Finsupp.smul_apply, h w hw, smul_zero]

/-- The reduction of an element of the Lie span lies in the mod-`2` Lie part. -/
theorem redZ_lieSpan_mem_barLie {j : ℕ} {a : FreeAssoc X} (ha : a ∈ lieSpan X j) :
    redZ X a ∈ barLie X j := by
  refine Submodule.span_induction (p := fun a _ => redZ X a ∈ barLie X j) ?_ ?_ ?_ ?_ ha
  · rintro a ⟨c, hc, rfl⟩
    rw [← hc]
    exact Submodule.subset_span ⟨⟨c, rfl⟩, rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro t a _ ha
    rw [map_zsmul,
      show t • (redZ X a) = ((t : ZMod 2)) • (redZ X a) from
        (Int.cast_smul_eq_zsmul (ZMod 2) t (redZ X a)).symm]
    exact Submodule.smul_mem (barLie X j) ((t : ZMod 2)) ha

/-- The left-normed map sends the degree-`j` part of `ℤ⟨X⟩` into the Lie span. -/
theorem lnMonLin_mem_lieSpan {j : ℕ} {a : FreeAssoc X} (ha : a ∈ wordSpan (X := X) j) :
    lnMonLin X a ∈ lieSpan X j := by
  refine Submodule.span_induction (p := fun a _ => lnMonLin X a ∈ lieSpan X j) ?_ ?_ ?_ ?_ ha
  · rintro a ⟨w, hw, rfl⟩
    rw [lnMonLin_wordEl]
    exact lnMon_mem_lieSpan X w j hw
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro t a _ ha; rw [map_zsmul]; exact Submodule.smul_mem _ t ha

/-- The left-normed map sends the degree-`j` part of `𝔽₂⟨X⟩` into `barLie X j`. -/
theorem LamBar_mem_barLie (j : ℕ) (v : WordBar X)
    (hv : ∀ w : FreeMonoid X, v w ≠ 0 → w.length = j) : LamBar X v ∈ barLie X j := by
  classical
  revert hv
  refine Finsupp.induction v ?_ ?_
  · intro _; rw [map_zero]; exact Submodule.zero_mem _
  · intro a b f ha hb ih hv
    have hv' : ∀ w : FreeMonoid X, f w ≠ 0 → w.length = j := by
      intro w hw
      refine hv w ?_
      have hfa : f a = 0 := by
        by_contra h
        exact ha (Finsupp.mem_support_iff.mpr h)
      by_cases hwa : w = a
      · subst hwa
        rw [Finsupp.add_apply, Finsupp.single_eq_same, hfa, add_zero]
        exact hb
      · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hwa, zero_add]
        exact hw
    have ha_len : a.length = j := by
      have hfa : f a = 0 := by
        by_contra h
        exact ha (Finsupp.mem_support_iff.mpr h)
      refine hv a ?_
      rw [Finsupp.add_apply, Finsupp.single_eq_same, hfa, add_zero]
      exact hb
    rw [map_add, LamBar_single]
    refine Submodule.add_mem _ ?_ (ih hv')
    exact Submodule.smul_mem _ b
      (redZ_lieSpan_mem_barLie
        (lnMon_mem_lieSpan X (FreeMonoid.toList a) j ha_len))

/-- The left-normed map is the identity on `barLie X j` for odd `j`. -/
theorem LamBar_eq_self_of_mem_barLie {j : ℕ} (hj : Odd j) {v : WordBar X}
    (hv : v ∈ barLie X j) : LamBar X v = v := by
  refine Submodule.span_induction (p := fun v _ => LamBar X v = v) ?_ ?_ ?_ ?_ hv
  · rintro v ⟨c, rfl⟩
    change LamBar X (redZ X (brkMon X c.1)) = redZ X (brkMon X c.1)
    rw [LamBar_redZ, lnMonLin_lieSpan j (Submodule.subset_span ⟨c.1, c.2, rfl⟩), map_zsmul,
      ← Int.cast_smul_eq_zsmul (ZMod 2) (j : ℤ) (redZ X (brkMon X c.1)),
      show ((j : ℤ) : ZMod 2) = 1 from by rw [Int.cast_natCast]; exact natCast_zmodTwo_eq_one hj,
      one_smul]
  · rw [map_zero]
  · intro a b _ _ ha hb; rw [map_add, ha, hb]
  · intro t a _ ha; rw [map_smul, ha]

/-! ## The main statement -/

/-- **The degree-`j` part of the free `𝔽₂`-Lie algebra is `σ`-regular for odd `j`.** -/
theorem freeLie_regular_odd (X : Type*) (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
    (hfree : ∀ x, σ x ≠ x) (j : ℕ) (hj : Odd j) (hj1 : 1 ≤ j) :
    ∀ v ∈ barLie X j, v + wordBarσ X σ v = 0 →
      ∃ w ∈ barLie X j, v = w + wordBarσ X σ w := by
  intro v hv hfix
  have hdeg : ∀ w : FreeMonoid X, v w ≠ 0 → w.length = j := by
    intro w hw
    by_contra hne
    exact hw (barLie_degree hv w hne)
  have hfix' : v + Finsupp.mapDomain (FreeMonoid.map (σ : X → X)) v = 0 := by
    rw [← wordBarσ_apply X σ v]
    exact hfix
  obtain ⟨t, htdeg, ht⟩ := wordInvolution_ker_eq_im X σ hσ hfree j hj1 v hdeg hfix'
  have ht' : v = t + wordBarσ X σ t := by
    rw [wordBarσ_apply, ← ht]
  refine ⟨LamBar X t, LamBar_mem_barLie j t htdeg, ?_⟩
  calc v = LamBar X v := (LamBar_eq_self_of_mem_barLie hj hv).symm
    _ = LamBar X (t + wordBarσ X σ t) := by rw [← ht']
    _ = LamBar X t + wordBarσ X σ (LamBar X t) := by rw [map_add, LamBar_wordBarσ]

/-! ## The relabelled tree, and `σ`-invariance of `barLie` -/

/-- Relabelling a binary tree by a map of the alphabet. -/
def magmaMap (f : X → X) : Magma X → Magma X
  | .gen x => .gen (f x)
  | .mul a b => .mul (magmaMap f a) (magmaMap f b)

@[simp] theorem magmaMap_size (f : X → X) (c : Magma X) :
    Magma.size (magmaMap f c) = Magma.size c := by
  induction c with
  | gen x => rfl
  | mul a b iha ihb => rw [magmaMap, Magma.size_mul, Magma.size_mul, iha, ihb]

theorem brkMon_magmaMap (σ : X ≃ X) (c : Magma X) :
    brkMon X (magmaMap (σ : X → X) c) = freeAssocPerm X σ (brkMon X c) := by
  induction c with
  | gen x => exact (freeAssocPerm_wordEl σ x).symm
  | mul a b iha ihb =>
      rw [magmaMap, brkMon_mul, brkMon_mul, iha, ihb, map_sub, map_mul, map_mul]

/-- `barLie X j` is invariant under the relabelling action of `σ`. -/
theorem barLie_wordBarσ_mem (σ : X ≃ X) {j : ℕ} {v : WordBar X} (hv : v ∈ barLie X j) :
    wordBarσ X σ v ∈ barLie X j := by
  refine Submodule.span_induction (p := fun v _ => wordBarσ X σ v ∈ barLie X j) ?_ ?_ ?_ ?_ hv
  · rintro v ⟨c, rfl⟩
    change wordBarσ X σ (redZ X (brkMon X c.1)) ∈ barLie X j
    rw [← redZ_freeAssocPerm, ← brkMon_magmaMap]
    exact Submodule.subset_span ⟨⟨magmaMap (σ : X → X) c.1, by rw [magmaMap_size, c.2]⟩, rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro t a _ ha; rw [map_smul]; exact Submodule.smul_mem _ t ha

end Work.SSGRoute
