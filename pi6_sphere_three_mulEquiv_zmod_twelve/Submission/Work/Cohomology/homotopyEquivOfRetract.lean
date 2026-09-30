import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cohomology

open CategoryTheory

/-!
# A retract of a chain complex is a homotopy equivalence

Let `i : A ⟶ B` be a chain map of `ℕ`-indexed chain complexes of `ℤ`-modules which is a
degreewise split mono, with chosen retraction `r` (`i.f n ≫ r n = 𝟙`).  Assume given morphisms
`κ n : B.X n ⟶ B.X (n+1)` such that

* `θ n := r n ≫ i.f n` kills `κ n` (`h1`),
* `κ n` lands in `ker θ (n+1)` (`h2`),
* `E n := κ (n+1) ≫ B.d (n+2) (n+1) + B.d (n+1) n ≫ κ n - 𝟙` kills the complementary
  idempotent `π (n+1) = 𝟙 - θ (n+1)` (`h3`, and `h3zero` in degree `0`).

Then `i` is a homotopy equivalence, with homotopy inverse given degreewise by
`v n = r n - (κ n ≫ B.d (n+1) n) ≫ r n` and homotopy `v ≫ i ~ 𝟙 B` with components `-κ n`.

The proof is the usual computation: writing `θ = r ≫ i` and `π = 𝟙 - θ` one has
`v ≫ i = θ - κ d θ`, and `h2`/`h3` rewrite `κ d θ = κ d - κ d π` and
`d κ = π - κ d π`, giving `(v ≫ i).f n - 𝟙 = -(κ n ≫ B.d (n+1) n) - B.d n (n-1) ≫ κ (n-1)`.
Likewise `i ≫ v = 𝟙` uses `h1` in the form `i.f n ≫ κ n = 0`.
-/

/-- `i.f n ≫ κ n = 0`: the image of `i` is contained in `im θ`, and `κ` kills `im θ`. -/
private theorem retract_i_comp_kappa {A B : ChainComplex (ModuleCat ℤ) ℕ} (i : A ⟶ B)
    (r : ∀ n, B.X n ⟶ A.X n) (hr : ∀ n, i.f n ≫ r n = 𝟙 (A.X n))
    (κ : ∀ n, B.X n ⟶ B.X (n + 1))
    (h1 : ∀ n, (r n ≫ i.f n) ≫ κ n = 0) (n : ℕ) : i.f n ≫ κ n = 0 := by
  have hθ : i.f n ≫ (r n ≫ i.f n) = i.f n := by
    rw [← Category.assoc, hr n, Category.id_comp]
  rw [← hθ, Category.assoc, h1 n, Limits.comp_zero]

/-- The key identity in degree `n+1`: `(v ≫ i).f (n+1) = 𝟙 - dκ - κd`. -/
private theorem retract_keySucc {A B : ChainComplex (ModuleCat ℤ) ℕ} (i : A ⟶ B)
    (r : ∀ n, B.X n ⟶ A.X n)
    (κ : ∀ n, B.X n ⟶ B.X (n + 1))
    (h2 : ∀ n, κ n ≫ (r (n + 1) ≫ i.f (n + 1)) = 0)
    (h3 : ∀ n, (κ (n + 1) ≫ B.d (n + 2) (n + 1) + B.d (n + 1) n ≫ κ n - 𝟙 (B.X (n + 1))) ≫
      (𝟙 (B.X (n + 1)) - r (n + 1) ≫ i.f (n + 1)) = 0) (n : ℕ) :
    (r (n + 1) - (κ (n + 1) ≫ B.d (n + 2) (n + 1)) ≫ r (n + 1)) ≫ i.f (n + 1)
      = 𝟙 (B.X (n + 1)) - B.d (n + 1) n ≫ κ n - κ (n + 1) ≫ B.d (n + 2) (n + 1) := by
  have hBπ : (B.d (n + 1) n ≫ κ n) ≫ (𝟙 (B.X (n + 1)) - r (n + 1) ≫ i.f (n + 1))
      = B.d (n + 1) n ≫ κ n := by
    rw [Category.assoc, Preadditive.comp_sub, Category.comp_id, h2 n, sub_zero]
  have hAπ : (κ (n + 1) ≫ B.d (n + 2) (n + 1)) ≫ (𝟙 (B.X (n + 1)) - r (n + 1) ≫ i.f (n + 1))
      = (𝟙 (B.X (n + 1)) - r (n + 1) ≫ i.f (n + 1)) - B.d (n + 1) n ≫ κ n := by
    have h := h3 n
    rw [Preadditive.sub_comp, Preadditive.add_comp, Category.id_comp] at h
    rw [hBπ] at h
    exact eq_sub_iff_add_eq.mpr (sub_eq_zero.mp h)
  have key : (r (n + 1) - (κ (n + 1) ≫ B.d (n + 2) (n + 1)) ≫ r (n + 1)) ≫ i.f (n + 1)
      - 𝟙 (B.X (n + 1)) = -(B.d (n + 1) n ≫ κ n) - κ (n + 1) ≫ B.d (n + 2) (n + 1) := by
    rw [Preadditive.sub_comp, Category.assoc]
    rw [(sub_sub_cancel (𝟙 (B.X (n + 1))) (r (n + 1) ≫ i.f (n + 1))).symm]
    rw [Preadditive.comp_sub, Category.comp_id]
    rw [hAπ]
    abel
  rw [sub_eq_iff_eq_add.mp key]
  abel

/-- The key identity in degree `0` (there is no `κ (-1)` term). -/
private theorem retract_keyZero {A B : ChainComplex (ModuleCat ℤ) ℕ} (i : A ⟶ B)
    (r : ∀ n, B.X n ⟶ A.X n)
    (κ : ∀ n, B.X n ⟶ B.X (n + 1))
    (h3zero : (κ 0 ≫ B.d 1 0 - 𝟙 (B.X 0)) ≫ (𝟙 (B.X 0) - r 0 ≫ i.f 0) = 0) :
    (r 0 - (κ 0 ≫ B.d 1 0) ≫ r 0) ≫ i.f 0 = 𝟙 (B.X 0) - κ 0 ≫ B.d 1 0 := by
  have hAπ : (κ 0 ≫ B.d 1 0) ≫ (𝟙 (B.X 0) - r 0 ≫ i.f 0)
      = 𝟙 (B.X 0) - r 0 ≫ i.f 0 := by
    have h := h3zero
    rw [Preadditive.sub_comp, Category.id_comp] at h
    exact sub_eq_zero.mp h
  have key : (r 0 - (κ 0 ≫ B.d 1 0) ≫ r 0) ≫ i.f 0 - 𝟙 (B.X 0) = -(κ 0 ≫ B.d 1 0) := by
    rw [Preadditive.sub_comp, Category.assoc]
    rw [(sub_sub_cancel (𝟙 (B.X 0)) (r 0 ≫ i.f 0)).symm]
    rw [Preadditive.comp_sub, Category.comp_id]
    rw [hAπ]
    abel
  rw [sub_eq_iff_eq_add.mp key]
  abel

/-- `v n = r n - (κ n ≫ B.d (n+1) n) ≫ r n` is a chain map.  It suffices to test the
commutation relation after postcomposing with the split mono `i.f n`. -/
private theorem retract_v_comm {A B : ChainComplex (ModuleCat ℤ) ℕ} (i : A ⟶ B)
    (r : ∀ n, B.X n ⟶ A.X n) (hr : ∀ n, i.f n ≫ r n = 𝟙 (A.X n))
    (κ : ∀ n, B.X n ⟶ B.X (n + 1))
    (h2 : ∀ n, κ n ≫ (r (n + 1) ≫ i.f (n + 1)) = 0)
    (h3zero : (κ 0 ≫ B.d 1 0 - 𝟙 (B.X 0)) ≫ (𝟙 (B.X 0) - r 0 ≫ i.f 0) = 0)
    (h3 : ∀ n, (κ (n + 1) ≫ B.d (n + 2) (n + 1) + B.d (n + 1) n ≫ κ n - 𝟙 (B.X (n + 1))) ≫
      (𝟙 (B.X (n + 1)) - r (n + 1) ≫ i.f (n + 1)) = 0) (n : ℕ) :
    (r (n + 1) - (κ (n + 1) ≫ B.d (n + 2) (n + 1)) ≫ r (n + 1)) ≫ A.d (n + 1) n
      = B.d (n + 1) n ≫ (r n - (κ n ≫ B.d (n + 1) n) ≫ r n) := by
  have keyS := retract_keySucc i r κ h2 h3
  have keyZ := retract_keyZero i r κ h3zero
  rw [← sub_eq_zero]
  have cancel : ∀ X : B.X (n + 1) ⟶ A.X n, X ≫ i.f n = 0 → X = 0 := by
    intro X h
    rw [← Category.comp_id X, ← hr n, ← Category.assoc, h]
    simp
  apply cancel
  rw [Preadditive.sub_comp]
  rcases n with _ | m
  · rw [Category.assoc, ← HomologicalComplex.Hom.comm i 1 0, ← Category.assoc, keyS 0]
    rw [Category.assoc, keyZ]
    rw [Preadditive.sub_comp, Preadditive.sub_comp, Category.id_comp]
    rw [Preadditive.comp_sub, Category.comp_id]
    simp only [Category.assoc]
    try simp only [Nat.reduceAdd]
    simp only [HomologicalComplex.d_comp_d, Limits.comp_zero]
    abel
  · rw [Category.assoc, ← HomologicalComplex.Hom.comm i (m + 2) (m + 1), ← Category.assoc, keyS (m+1)]
    rw [Category.assoc, keyS m]
    rw [Preadditive.sub_comp, Preadditive.sub_comp, Category.id_comp]
    rw [Preadditive.comp_sub, Preadditive.comp_sub, Category.comp_id]
    simp only [Category.assoc]
    try simp only [Nat.reduceAdd]
    simp only [HomologicalComplex.d_comp_d, HomologicalComplex.d_comp_d_assoc, Limits.comp_zero,
      Limits.zero_comp]
    abel

/-- If `i : A ⟶ B` is a chain map which is a degreewise split mono with retraction `r`, and if
`κ` contracts the complement of `im i` (hypotheses `h1`, `h2`, `h3zero`, `h3` below), then `i`
is a homotopy equivalence, with forward map exactly `i`. -/
theorem homotopyEquivOfRetract {A B : ChainComplex (ModuleCat ℤ) ℕ} (i : A ⟶ B)
    (r : ∀ n, B.X n ⟶ A.X n) (hr : ∀ n, i.f n ≫ r n = 𝟙 (A.X n))
    (κ : ∀ n, B.X n ⟶ B.X (n + 1))
    (h1 : ∀ n, (r n ≫ i.f n) ≫ κ n = 0)
    (h2 : ∀ n, κ n ≫ (r (n + 1) ≫ i.f (n + 1)) = 0)
    (h3zero : (κ 0 ≫ B.d 1 0 - 𝟙 (B.X 0)) ≫ (𝟙 (B.X 0) - r 0 ≫ i.f 0) = 0)
    (h3 : ∀ n, (κ (n + 1) ≫ B.d (n + 2) (n + 1) + B.d (n + 1) n ≫ κ n - 𝟙 (B.X (n + 1))) ≫
      (𝟙 (B.X (n + 1)) - r (n + 1) ≫ i.f (n + 1)) = 0) :
    ∃ e : HomotopyEquiv A B, e.hom = i := by
  have hiκ : ∀ n, i.f n ≫ κ n = 0 := retract_i_comp_kappa i r hr κ h1
  -- the homotopy inverse, which we first show to be a chain map
  let v : B ⟶ A :=
    { f := fun n => r n - (κ n ≫ B.d (n + 1) n) ≫ r n
      comm' := by
        intro p q hpq
        rw [← hpq]
        exact retract_v_comm i r hr κ h2 h3zero h3 q }
  have keyS : ∀ n, v.f (n + 1) ≫ i.f (n + 1)
      = 𝟙 (B.X (n + 1)) - B.d (n + 1) n ≫ κ n - κ (n + 1) ≫ B.d (n + 2) (n + 1) :=
    fun n => retract_keySucc i r κ h2 h3 n
  have keyZ : v.f 0 ≫ i.f 0 = 𝟙 (B.X 0) - κ 0 ≫ B.d 1 0 :=
    retract_keyZero i r κ h3zero
  have hiv : i ≫ v = 𝟙 A := by
    rw [HomologicalComplex.Hom.ext_iff]
    funext p
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
    show i.f p ≫ (r p - (κ p ≫ B.d (p + 1) p) ≫ r p) = 𝟙 (A.X p)
    rw [Preadditive.comp_sub, hr p]
    have hz : i.f p ≫ ((κ p ≫ B.d (p + 1) p) ≫ r p) = 0 := by
      rw [Category.assoc, ← Category.assoc (i.f p) (κ p), hiκ p, Limits.zero_comp]
    rw [hz, sub_zero]
  -- the homotopy `v ≫ i ~ 𝟙 B` with components `-κ n`
  let hom : ∀ p q : ℕ, B.X p ⟶ B.X q :=
    fun p q => if h : p + 1 = q then -κ p ≫ eqToHom (congrArg B.X h) else 0
  have hhom_eq : ∀ p, hom p (p + 1) = -κ p := fun p => by simp [hom]
  have hhom : Homotopy ((v ≫ i) - 𝟙 B) 0 := by
    refine { hom := hom, zero := fun p q h => dif_neg h, comm := ?_ }
    intro p
    rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, HomologicalComplex.zero_f_apply,
      add_zero]
    cases p with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, hhom_eq 0]
      rw [HomologicalComplex.comp_f, keyZ]
      simp
    | succ m =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, hhom_eq m, hhom_eq (m + 1)]
      rw [HomologicalComplex.comp_f, keyS m, Preadditive.comp_neg, Preadditive.neg_comp]
      abel
  let e : HomotopyEquiv A B :=
    { hom := i
      inv := v
      homotopyHomInvId := Homotopy.ofEq hiv
      homotopyInvHomId := (Homotopy.equivSubZero).symm hhom }
  exact ⟨e, rfl⟩

end Work.Cohomology
