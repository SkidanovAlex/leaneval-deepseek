import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- Every element of `ZMod 2` is `0` or `1`. -/
lemma zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  exact h a

/-- Given a free involution-like permutation `σ` of a finite type `X`, together with a
retraction `r` onto a transversal of the `⟨σ⟩`-orbits, the type `X` splits as the product of
the fixed-point set of `r` and `ZMod 2`, and `σ` acts by translating the `ZMod 2`-coordinate. -/
theorem exists_equiv_transversal_mul_zmodTwo {X : Type*} [Finite X] (σ : X ≃ X)
    (hσ : ∀ x, σ (σ x) = x) (hfree : ∀ x, σ x ≠ x) (r : X → X)
    (hidem : ∀ x, r (r x) = r x) (hmem : ∀ x, r x = x ∨ r x = σ x)
    (hcomm : ∀ x, r (σ x) = r x) :
    ∃ e : X ≃ ({x : X // r x = x} × Multiplicative (ZMod 2)),
      ∀ x : X, (e (σ x)).1 = (e x).1 ∧
        (e (σ x)).2 = Multiplicative.ofAdd (1 : ZMod 2) * (e x).2 := by
  classical
  -- `b` records, for each `x`, whether `x` is on the chosen transversal (`0`) or is the
  -- other element of its `⟨σ⟩`-orbit (`1`).
  let b : X → ZMod 2 := fun x => if r x = x then 0 else 1
  have hb_fixed : ∀ x, r x = x → b x = 0 := by
    intro x hx; dsimp only [b]; rw [if_pos hx]
  have hb_nonfixed : ∀ x, r x ≠ x → b x = 1 := by
    intro x hx; dsimp only [b]; rw [if_neg hx]
  -- `b` toggles when `σ` is applied.
  have hb_toggle : ∀ x, b (σ x) = 1 + b x := by
    intro x
    rcases hmem x with hx | hx
    · have h1 : b x = 0 := hb_fixed x hx
      have hneq : r (σ x) ≠ σ x := by
        rw [hcomm x, hx]; exact fun h => hfree x h.symm
      have h2 : b (σ x) = 1 := hb_nonfixed (σ x) hneq
      rw [h1, h2]; decide
    · have hxne : r x ≠ x := by rw [hx]; exact hfree x
      have h1 : b x = 1 := hb_nonfixed x hxne
      have h2 : b (σ x) = 0 := hb_fixed (σ x) (by rw [hcomm x, hx])
      rw [h1, h2]; decide
  -- The candidate equivalence `x ↦ (r x, b x)`.
  let f : X → ({x : X // r x = x} × Multiplicative (ZMod 2)) :=
    fun x => (⟨r x, hidem x⟩, Multiplicative.ofAdd (b x))
  have hinj : Function.Injective f := by
    intro x y h
    have h1 : r x = r y := by
      have h' := congrArg (fun z : {x : X // r x = x} × Multiplicative (ZMod 2) =>
        z.1.1) h
      dsimp only [f] at h'
      exact h'
    have h2 : b x = b y := by
      have h' := congrArg (fun z : {x : X // r x = x} × Multiplicative (ZMod 2) =>
        Multiplicative.toAdd z.2) h
      dsimp only [f] at h'
      exact h'
    rcases hmem x with hx | hx
    · have hbx : b x = 0 := hb_fixed x hx
      have hby : b y = 0 := by rw [← h2]; exact hbx
      have hy : r y = y := by
        by_contra hyne
        have hb1 : b y = 1 := hb_nonfixed y hyne
        rw [hb1] at hby
        exact one_ne_zero hby
      calc x = r x := hx.symm
        _ = r y := h1
        _ = y := hy
    · have hxne : r x ≠ x := by rw [hx]; exact hfree x
      have hbx : b x = 1 := hb_nonfixed x hxne
      have hby : b y = 1 := by rw [← h2]; exact hbx
      have hyne : r y ≠ y := by
        intro hy
        have hb0 : b y = 0 := hb_fixed y hy
        rw [hb0] at hby
        exact zero_ne_one hby
      have hy : r y = σ y := by
        rcases hmem y with h | h
        · exact absurd h hyne
        · exact h
      have hs : σ x = σ y := by rw [← hx, h1, hy]
      have hs2 := congrArg σ hs
      rwa [hσ x, hσ y] at hs2
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨y, hy⟩, m⟩
    rcases zmod_two_eq_zero_or_one (Multiplicative.toAdd m) with ha | ha
    · refine ⟨y, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        dsimp only [f]
        exact hy
      · dsimp only [f]
        rw [hb_fixed y hy, ← ha]
        rfl
    · refine ⟨σ y, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        dsimp only [f]
        rw [hcomm y, hy]
      · dsimp only [f]
        have hb1 : b (σ y) = 1 := by
          have hne : r (σ y) ≠ σ y := by
            rw [hcomm y, hy]; exact fun h => hfree y h.symm
          exact hb_nonfixed (σ y) hne
        rw [hb1, ← ha]
        rfl
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  intro x
  constructor
  · change (⟨r (σ x), hidem (σ x)⟩ : {x : X // r x = x}) = ⟨r x, hidem x⟩
    apply Subtype.ext
    exact hcomm x
  · change Multiplicative.ofAdd (b (σ x)) =
      Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (b x)
    rw [hb_toggle x]
    rfl

end Work.SSGRoute
