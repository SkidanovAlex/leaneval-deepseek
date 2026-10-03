import Mathlib
import Submission.Work.OROneRel.tlWinCherryDefs

/-!
# The cherry lemma, the case `m+1-p = m+1-q`

`cherry_unit_mem_eq` is the *degenerate* case `m + 1 - p = m + 1 - q` (equivalently `p = q`) of the
"cherry" bookkeeping behind `tlWin_succ_le_cherry`: the two attachment levels of the cherry
coincide, so the `χ`-weight of the two-letter excursion `[x, y]` vanishes and the excursion does not
move the level at all.  Consequently the connection element is the same on both sides and the
statement reduces to elementary group identities:

* `x = a`, `y = a⁻¹` (resp. `x = b⁻¹`, `y = b`): the excursion is trivial, the expression is `1`;
* `x = a`, `y = b`: the expression is `δ · (pβ · pα⁻¹)` with `δ = pα · a · b · pβ⁻¹` the cherry loop
  and `pβ · pα⁻¹ ∈ tlWin p q m` the given connection;
* `x = b⁻¹`, `y = a⁻¹`: the expression is `(pα · pβ⁻¹) · δ⁻¹`.

The weight computation uses `p = q` (from the hypothesis `heq`) via `lsig_pair_eq_zero` below.
-/
namespace Work.OROneRel

/-- The head of a `FreeGroup.mk` word: a positive letter. -/
private theorem mk_cons_true_pair {β : Type*} (a : β) (M : List (β × Bool)) :
    FreeGroup.mk ((a, true) :: M) = FreeGroup.of a * FreeGroup.mk M := by
  rw [FreeGroup.of, FreeGroup.mul_mk]; rfl

/-- The head of a `FreeGroup.mk` word: a negative letter. -/
private theorem mk_cons_false_pair {β : Type*} (a : β) (M : List (β × Bool)) :
    FreeGroup.mk ((a, false) :: M) = (FreeGroup.of a)⁻¹ * FreeGroup.mk M := by
  rw [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.mul_mk]; rfl

/-- The class of the empty word. -/
private theorem mk_nil_pair : FreeGroup.mk ([] : List (Fin 2 × Bool)) = 1 :=
  FreeGroup.one_eq_mk.symm

/-- **The weight of the cherry excursion vanishes when `p = q`.**  The two admissible choices of the
first letter (`a`, coming up from the lower attachment level, or `b⁻¹`, coming down from the top)
each have weight `q`, resp. `-(-p) = p`, and the second letter (`a⁻¹`, `b`) contributes `-q`,
resp. `-p`; with `p = q` both cancel. -/
private lemma lsig_pair_eq_zero (p q : ℕ) (hpq : p = q) :
    ∀ x y : Fin 2 × Bool,
      (x = ((0 : Fin 2), true) ∨ x = ((1 : Fin 2), false)) →
      (y = ((0 : Fin 2), false) ∨ y = ((1 : Fin 2), true)) →
      lsig (tlW p q) [x, y] = 0 := by
  intro x y hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp [lsig, tlW, hpq]

theorem cherry_unit_mem_eq (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (m : ℤ)
    (heq : m + 1 - (p : ℤ) = m + 1 - (q : ℤ))
    {pα pβ : FreeGroup (Fin 2)} (hαβ : pβ * pα⁻¹ ∈ tlWin p q m)
    {s : ℤ} (x y : Fin 2 × Bool)
    (hx : (s = m + 1 - (q : ℤ) ∧ x = ((0 : Fin 2), true)) ∨
      (s = m + 1 - (p : ℤ) ∧ x = ((1 : Fin 2), false)))
    (hy : y = ((0 : Fin 2), false) ∨ y = ((1 : Fin 2), true)) :
    cherryConn p q m pα pβ s * FreeGroup.mk [x, y] *
        (cherryConn p q m pα pβ (s + lsig (tlW p q) [x, y]))⁻¹ ∈
      tlWin p q m ⊔ Subgroup.closure
        ({pα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * pβ⁻¹} :
          Set (FreeGroup (Fin 2))) ∧
    cherryOuter p q m (s + lsig (tlW p q) [x, y]) := by
  -- the equation forces `p = q`
  have hpq : p = q := by
    have h : (p : ℤ) = (q : ℤ) := by omega
    exact_mod_cast h
  -- the level of the first letter is `m + 1 - q`
  have hsq : s = m + 1 - (q : ℤ) := by
    rcases hx with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · rw [h]; exact heq
  -- the excursion has vanishing weight
  have hlsig : lsig (tlW p q) [x, y] = 0 :=
    lsig_pair_eq_zero p q hpq x y
      (by rcases hx with ⟨_, h0⟩ | ⟨_, h1⟩
          · exact Or.inl h0
          · exact Or.inr h1) hy
  -- the connection elements at the two ends of the excursion
  have hconn : cherryConn p q m pα pβ s = pα := by
    rw [hsq, cherryConn_self_q]
  have hconn2 : cherryConn p q m pα pβ (s + lsig (tlW p q) [x, y]) = pα := by
    rw [hlsig, add_zero, hconn]
  -- the cherry loop and the memberships of the pieces
  have hδ_mem : pα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * pβ⁻¹ ∈
      Subgroup.closure ({pα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * pβ⁻¹} :
        Set (FreeGroup (Fin 2))) :=
    Subgroup.subset_closure (by simp)
  have hδT : pα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * pβ⁻¹ ∈
      tlWin p q m ⊔ Subgroup.closure
        ({pα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * pβ⁻¹} :
          Set (FreeGroup (Fin 2))) :=
    Subgroup.mem_sup_right (S := tlWin p q m) hδ_mem
  have hδTinv : (pα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * pβ⁻¹)⁻¹ ∈
      tlWin p q m ⊔ Subgroup.closure
        ({pα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * pβ⁻¹} :
          Set (FreeGroup (Fin 2))) :=
    Subgroup.inv_mem _ hδT
  have hAT : pβ * pα⁻¹ ∈
      tlWin p q m ⊔ Subgroup.closure
        ({pα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * pβ⁻¹} :
          Set (FreeGroup (Fin 2))) :=
    Subgroup.mem_sup_left (T := Subgroup.closure
      ({pα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * pβ⁻¹} :
        Set (FreeGroup (Fin 2)))) hαβ
  have hAinvT : pα * pβ⁻¹ ∈
      tlWin p q m ⊔ Subgroup.closure
        ({pα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * pβ⁻¹} :
          Set (FreeGroup (Fin 2))) := by
    have h := Subgroup.inv_mem _ hAT
    simpa only [mul_inv_rev, inv_inv] using h
  refine ⟨?_, ?_⟩
  · rw [hconn, hconn2]
    rcases hx with ⟨_, hx0⟩ | ⟨_, hx1⟩
    · subst hx0
      rcases hy with hy0 | hy1
      · -- `x = a`, `y = a⁻¹`: the excursion is trivial
        subst hy0
        have h1 : pα * FreeGroup.mk [((0 : Fin 2), true), ((0 : Fin 2), false)] * pα⁻¹ = 1 := by
          rw [mk_cons_true_pair, mk_cons_false_pair, mk_nil_pair]; group
        rw [h1]
        exact Subgroup.one_mem _
      · -- `x = a`, `y = b`: the excursion is the cherry `a·b`
        subst hy1
        have hmk : FreeGroup.mk [((0 : Fin 2), true), ((1 : Fin 2), true)] =
            FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) := by
          rw [mk_cons_true_pair, mk_cons_true_pair, mk_nil_pair]; group
        rw [hmk]
        have heq2 : pα * (FreeGroup.of 0 * FreeGroup.of 1) * pα⁻¹ =
            (pα * FreeGroup.of 0 * FreeGroup.of 1 * pβ⁻¹) * (pβ * pα⁻¹) := by group
        rw [heq2]
        exact Subgroup.mul_mem _ hδT hAT
    · subst hx1
      rcases hy with hy0 | hy1
      · -- `x = b⁻¹`, `y = a⁻¹`: the excursion is the inverse cherry
        subst hy0
        have hmk : FreeGroup.mk [((1 : Fin 2), false), ((0 : Fin 2), false)] =
            (FreeGroup.of (1 : Fin 2))⁻¹ * (FreeGroup.of (0 : Fin 2))⁻¹ := by
          rw [mk_cons_false_pair, mk_cons_false_pair, mk_nil_pair]; group
        rw [hmk]
        have heq3 : pα * ((FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹) * pα⁻¹ =
            (pα * pβ⁻¹) * (pα * FreeGroup.of 0 * FreeGroup.of 1 * pβ⁻¹)⁻¹ := by group
        rw [heq3]
        exact Subgroup.mul_mem _ hAinvT hδTinv
      · -- `x = b⁻¹`, `y = b`: the excursion is trivial
        subst hy1
        have h1 : pα * FreeGroup.mk [((1 : Fin 2), false), ((1 : Fin 2), true)] * pα⁻¹ = 1 := by
          rw [mk_cons_false_pair, mk_cons_true_pair, mk_nil_pair]; group
        rw [h1]
        exact Subgroup.one_mem _
  · rw [hlsig, add_zero]
    simp only [cherryOuter]
    exact Or.inr (Or.inl hsq)

end Work.OROneRel
