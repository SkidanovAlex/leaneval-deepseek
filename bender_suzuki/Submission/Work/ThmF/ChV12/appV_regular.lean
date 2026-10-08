import Mathlib
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# App. V (a), regular form (Peterfalvi I, p. 211)

An abelian group `K` acting on a finite abelian group `E` by additive automorphisms,
regularly (= sharply transitively) on `E \ {0}`, turns `E` into a field `F` with `K ≃* Fˣ`
acting by multiplication and a fixed nonzero `s` mapping to `1`.

The construction is elementary and avoids any structure theory of `F_pK`-modules: fixing
`s ≠ 0`, denote by `ι x` the unique `k : K` with `k • s = x` (for `x ≠ 0`) and set
`x * y = ι x • y` for `x ≠ 0`, `0 * y = 0`.  Left distributivity is the action axiom; `ι` is a
group isomorphism `(E\{0}, *) ≅ K` (so `*` is associative, commutative whenever `K` is), which
supplies `1 = s`, inverses, and — via commutativity — right distributivity.  Hence `E` is a
field (`Field.ofMinimalAxioms`), `s = 1`, and `κ k := k • s` is the required isomorphism
`K ≃* Eˣ` with `ι` as inverse.
-/

set_option autoImplicit false

open Classical

namespace Work.ThmF.ChV12

section Helpers

variable {E K : Type} [AddCommGroup E] [CommGroup K] [DistribMulAction K E]

/-- For `x ≠ 0`, the unique `k : K` with `k • s = x`; junk value `1` at `x = 0`. -/
noncomputable def iota (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) (x : E) : K :=
  if hx : x = 0 then 1 else Classical.choose (hreg s x hs hx)

/-- An element of `K` (a group) never sends a nonzero vector to `0`. -/
theorem smul_ne_zero_of_ne_zero {k : K} {y : E} (hy : y ≠ 0) : k • y ≠ 0 := by
  intro h
  have : y = 0 := by
    calc y = (1 : K) • y := (one_smul K y).symm
    _ = (k⁻¹ * k) • y := by rw [inv_mul_cancel]
    _ = k⁻¹ • (k • y) := by rw [mul_smul]
    _ = k⁻¹ • 0 := by rw [h]
    _ = 0 := smul_zero k⁻¹
  exact hy this

theorem iota_smul (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) {x : E} (hx : x ≠ 0) :
    iota s hs hreg x • s = x := by
  simp only [iota, dite_eq_right hx]
  exact (Classical.choose_spec (hreg s x hs hx)).1

theorem iota_s_eq_one (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) :
    iota s hs hreg s = 1 :=
  (hreg s s hs hs).unique (iota_smul s hs hreg hs) (one_smul K s)

theorem eq_iota_of_smul_eq (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) {k : K} {x : E}
    (hx : x ≠ 0) (h : k • s = x) : k = iota s hs hreg x :=
  (hreg s x hs hx).unique h (iota_smul s hs hreg hx)

theorem iota_smul_smul (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) (k : K) :
    iota s hs hreg (k • s) = k :=
  (eq_iota_of_smul_eq s hs hreg (x := k • s) (k := k) (smul_ne_zero_of_ne_zero hs) rfl).symm

/-- The multiplication on `E`: `x * y = ι x • y`, zero if `x = 0`. -/
noncomputable def mulE (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) (x y : E) : E :=
  if x = 0 then 0 else iota s hs hreg x • y

/-- The inverse for the multiplication `mulE`: `x⁻¹ = (ι x)⁻¹ • s`, zero if `x = 0`. -/
noncomputable def invE (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) (x : E) : E :=
  if x = 0 then 0 else (iota s hs hreg x)⁻¹ • s

theorem mulE_eq_smul (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) {x : E} (hx : x ≠ 0) (y : E) :
    mulE s hs hreg x y = iota s hs hreg x • y := by
  simp only [mulE, ite_eq_right hx]

theorem mulE_zero_left (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) (y : E) :
    mulE s hs hreg 0 y = 0 := by
  simp only [mulE, ↓reduceIte]

theorem mulE_zero_right (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) (x : E) :
    mulE s hs hreg x 0 = 0 := by
  by_cases hx : x = 0
  · simp only [hx, mulE, ↓reduceIte]
  · rw [mulE_eq_smul s hs hreg hx, smul_zero]

theorem mulE_ne_zero (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) {x y : E}
    (hx : x ≠ 0) (hy : y ≠ 0) : mulE s hs hreg x y ≠ 0 := by
  rw [mulE_eq_smul s hs hreg hx]
  exact smul_ne_zero_of_ne_zero hy

theorem iota_mul (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) {x y : E}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    iota s hs hreg (mulE s hs hreg x y) = iota s hs hreg x * iota s hs hreg y := by
  have hnm := mulE_ne_zero s hs hreg hx hy
  have h2 : (iota s hs hreg x * iota s hs hreg y) • s = mulE s hs hreg x y := by
    rw [mul_smul, iota_smul s hs hreg hy, ← mulE_eq_smul s hs hreg hx y]
  exact (hreg s (mulE s hs hreg x y) hs hnm).unique (iota_smul s hs hreg hnm) h2

theorem mulE_comm (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) (x y : E) :
    mulE s hs hreg x y = mulE s hs hreg y x := by
  by_cases hx : x = 0
  · rw [hx, mulE_zero_left, mulE_zero_right]
  · by_cases hy : y = 0
    · rw [hy, mulE_zero_left, mulE_zero_right]
    · calc mulE s hs hreg x y = iota s hs hreg x • y := mulE_eq_smul s hs hreg hx y
        _ = iota s hs hreg x • (iota s hs hreg y • s) := by rw [iota_smul s hs hreg hy]
        _ = (iota s hs hreg x * iota s hs hreg y) • s := by rw [← mul_smul]
        _ = (iota s hs hreg y * iota s hs hreg x) • s := by rw [mul_comm]
        _ = iota s hs hreg y • (iota s hs hreg x • s) := by rw [mul_smul]
        _ = iota s hs hreg y • x := by rw [iota_smul s hs hreg hx]
        _ = mulE s hs hreg y x := (mulE_eq_smul s hs hreg hy x).symm

theorem mulE_assoc (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) (x y z : E) :
    mulE s hs hreg (mulE s hs hreg x y) z = mulE s hs hreg x (mulE s hs hreg y z) := by
  by_cases hx : x = 0
  · subst hx; simp only [mulE_zero_left]
  · by_cases hy : y = 0
    · subst hy; simp only [mulE_zero_right, mulE_zero_left]
    · by_cases hz : z = 0
      · subst hz; simp only [mulE_zero_right]
      · calc mulE s hs hreg (mulE s hs hreg x y) z
            = iota s hs hreg (mulE s hs hreg x y) • z :=
              mulE_eq_smul s hs hreg (mulE_ne_zero s hs hreg hx hy) z
          _ = (iota s hs hreg x * iota s hs hreg y) • z := by rw [iota_mul s hs hreg hx hy]
          _ = iota s hs hreg x • (iota s hs hreg y • z) := by rw [mul_smul]
          _ = iota s hs hreg x • (mulE s hs hreg y z) := by rw [← mulE_eq_smul s hs hreg hy z]
          _ = mulE s hs hreg x (mulE s hs hreg y z) :=
              (mulE_eq_smul s hs hreg hx (mulE s hs hreg y z)).symm

theorem mulE_one_left (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) (y : E) :
    mulE s hs hreg s y = y := by
  rw [mulE_eq_smul s hs hreg hs, iota_s_eq_one s hs hreg, one_smul]

theorem invE_eq (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) {x : E} (hx : x ≠ 0) :
    invE s hs hreg x = (iota s hs hreg x)⁻¹ • s := by
  simp only [invE, ite_eq_right hx]

theorem mulE_mul_inv (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) {x : E} (hx : x ≠ 0) :
    mulE s hs hreg x (invE s hs hreg x) = s := by
  rw [mulE_eq_smul s hs hreg hx, invE_eq s hs hreg hx, ← mul_smul, mul_inv_cancel, one_smul]

theorem invE_zero (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) :
    invE s hs hreg 0 = 0 := by
  simp only [invE, ↓reduceIte]

theorem mulE_left_distrib (s : E) (hs : s ≠ 0)
    (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) (x y z : E) :
    mulE s hs hreg x (y + z) = mulE s hs hreg x y + mulE s hs hreg x z := by
  by_cases hx : x = 0
  · subst hx; simp only [mulE_zero_left, zero_add]
  · rw [mulE_eq_smul s hs hreg hx, smul_add, mulE_eq_smul s hs hreg hx,
      mulE_eq_smul s hs hreg hx]

end Helpers

open Classical in theorem appV_regular {E K : Type} [AddCommGroup E] [Fintype E] [CommGroup K] [Fintype K] [DistribMulAction K E] {p : ℕ} (hp : p.Prime) (hpE : ∀ x : E, p • x = 0) (hreg : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) (s : E) (hs : s ≠ 0) : ∃ (F : Type) (_ : Field F) (_ : Fintype F) (e : E ≃+ F) (κ : K ≃* Fˣ), e s = 1 ∧ ∀ (k : K) (x : E), e (k • x) = (κ k : F) * e x := by
  letI hMul : Mul E := ⟨mulE s hs hreg⟩
  letI hOne : One E := ⟨s⟩
  letI hInv : Inv E := ⟨invE s hs hreg⟩
  let fieldE : Field E := Field.ofMinimalAxioms E
    (fun a b c => add_assoc a b c)
    (fun a => zero_add a)
    (fun a => neg_add_cancel a)
    (fun a b c => mulE_assoc s hs hreg a b c)
    (fun a b => mulE_comm s hs hreg a b)
    (fun a => mulE_one_left s hs hreg a)
    (fun a ha => mulE_mul_inv s hs hreg ha)
    (invE_zero s hs hreg)
    (fun a b c => mulE_left_distrib s hs hreg a b c)
    ⟨0, s, Ne.symm hs⟩
  letI : Field E := fieldE
  let f : K → Eˣ := fun k => Units.mk0 (k • s) (smul_ne_zero_of_ne_zero hs)
  have hfmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    ext
    simp only [f, Units.val_mk0, Units.val_mul]
    change (a * b) • s = mulE s hs hreg (a • s) (b • s)
    rw [mulE_eq_smul s hs hreg (smul_ne_zero_of_ne_zero hs), iota_smul_smul s hs hreg,
      ← mul_smul]
  let hκ : K ≃* Eˣ :=
    { toFun := f
      invFun := fun u => iota s hs hreg (u : E)
      left_inv := fun k => iota_smul_smul s hs hreg k
      right_inv := fun u => by
        apply Units.ext
        exact iota_smul s hs hreg (Units.ne_zero u)
      map_mul' := hfmul }
  refine ⟨E, fieldE, inferInstance, AddEquiv.refl E, hκ, ?_⟩
  constructor
  · rfl
  · intro k x
    show k • x = (hκ k : E) * x
    have hk : (hκ k : E) = k • s := by
      change (↑(f k) : E) = k • s
      exact Units.val_mk0 _
    rw [hk]
    change k • x = mulE s hs hreg (k • s) x
    rw [mulE_eq_smul s hs hreg (smul_ne_zero_of_ne_zero hs), iota_smul_smul s hs hreg]

end Work.ThmF.ChV12
