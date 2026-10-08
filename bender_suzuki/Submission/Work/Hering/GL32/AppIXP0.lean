import Mathlib
import Submission.Work.Hering.GL32.AppIXPair

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix IX: the fixed pair `p₀ = {e₀, e₁}` and its stabiliser

Concrete points and pairs of `PG(2,2)`, used for the Frobenius step: `GL(3,2)` is transitive on the
`21` pairs, and the stabiliser of the pair `{e₀,e₁}` is a Sylow `2`-subgroup (of order `8`).
-/

set_option autoImplicit false

namespace Work.Hering.GL32

/-- A point of `PG(2,2)` from a nonzero vector. -/
def ptOf (v : F2v) (hv : v ≠ 0) : Pt := ⟨v, hv⟩

/-- The unordered pair of two distinct points. -/
def mkPair (a b : Pt) (h : a ≠ b) : Pair :=
  ⟨Sym2.mk a b, by rw [Sym2.mk_isDiag_iff]; exact h⟩

@[simp] lemma ptOf_val (v : F2v) (hv : v ≠ 0) : (ptOf v hv : F2v) = v := rfl

@[simp] lemma mkPair_val (a b : Pt) (h : a ≠ b) : (mkPair a b h).1 = Sym2.mk a b := rfl

/-- The standard point `e₀`. -/
def p₀pt : Pt := ptOf e₀ (by decide)

/-- The standard point `e₁`. -/
def p₁pt : Pt := ptOf e₁ (by decide)

lemma p₀pt_val : (p₀pt : F2v) = e₀ := rfl
lemma p₁pt_val : (p₁pt : F2v) = e₁ := rfl
lemma p₀pt_ne_zero : (p₀pt : F2v) ≠ 0 := (by decide : e₀ ≠ 0)
lemma p₁pt_ne_zero : (p₁pt : F2v) ≠ 0 := (by decide : e₁ ≠ 0)
lemma p₀pt_ne_p₁pt : p₀pt ≠ p₁pt := by
  intro h
  have := congrArg Subtype.val h
  simp only [p₀pt_val, p₁pt_val] at this
  exact absurd this (by decide : e₀ ≠ e₁)

/-- **The standard pair** `p₀ = {e₀, e₁}` of `PG(2,2)`. -/
def p₀ : Pair := mkPair p₀pt p₁pt p₀pt_ne_p₁pt

lemma p₀_val : (p₀).1 = Sym2.mk p₀pt p₁pt := rfl

@[simp] lemma psum_p₀ : psum p₀ = e₀ + e₁ := by
  show Sym2.lift _ (Sym2.mk p₀pt p₁pt) = _
  rw [Sym2.lift_mk]
  rfl

/-- The line spanned by the two points of `p₀` (the set `{0, e₀, e₁, e₀+e₁}`). -/
lemma mem_p₀_iff (x : Pt) : x ∈ (p₀).1 ↔ x = p₀pt ∨ x = p₁pt := by
  rw [p₀_val, Sym2.mem_iff]

/-! ## The `GL(3,2)`-action on pairs -/

lemma ptPerm_one_apply (v : Pt) : ptPerm (1 : GL32) v = v := by
  apply Subtype.ext
  rfl

lemma ptPerm_mul_apply (g h : GL32) (v : Pt) : ptPerm (g * h) v = ptPerm g (ptPerm h v) := by
  apply Subtype.ext
  rfl

lemma pairPerm_one_apply (p : Pair) : pairPerm (1 : GL32) p = p := by
  apply Subtype.ext
  show Sym2.map (ptPerm (1 : GL32)) p.1 = p.1
  rw [show (ptPerm (1 : GL32) : Pt → Pt) = id from funext ptPerm_one_apply, Sym2.map_id]
  rfl

lemma pairPerm_mul_apply (g h : GL32) (p : Pair) :
    pairPerm (g * h) p = pairPerm g (pairPerm h p) := by
  apply Subtype.ext
  show Sym2.map (ptPerm (g * h)) p.1 = Sym2.map (ptPerm g) (Sym2.map (ptPerm h) p.1)
  rw [show (ptPerm (g * h) : Pt → Pt) = (ptPerm g : Pt → Pt) ∘ (ptPerm h : Pt → Pt) from
        funext fun v => ptPerm_mul_apply g h v, Sym2.map_comp]
  rfl

/-- The natural action of `GL(3,2)` on the set `Ω` of pairs. -/
instance instMulActionPair : MulAction GL32 Pair where
  smul g p := pairPerm g p
  one_smul p := pairPerm_one_apply p
  mul_smul g h p := pairPerm_mul_apply g h p

/-- The stabiliser of the standard pair, a Sylow `2`-subgroup of `GL(3,2)` of order `8`. -/
noncomputable def pairStab : Subgroup GL32 := MulAction.stabilizer GL32 p₀

lemma mem_pairStab_iff (g : GL32) : g ∈ pairStab ↔ pairPerm g p₀ = p₀ := Iff.rfl

end Work.Hering.GL32
