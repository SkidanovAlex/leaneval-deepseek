import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Conic.mem_circle
import Submission.Work.L2F.Conic.ncard_conic_plus

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Conic

/-! ## Counting the conic `a² + b² = 1`

The conic is parametrised from the point `(0,1)` by the lines through it: the point of the conic
on the line of slope `t` is `(2t/(t²+1), (t²-1)/(t²+1))`, and `t = ∞` (i.e. `none : Option F`)
gives back `(0,1)`.  When `t² + 1 ≠ 0` for every `t` (which is what `-1` not being a square
says, `2 ≠ 0` being available in the odd-characteristic case), the two maps are mutually inverse
and the conic has `q + 1` points, and an elementary calculation gives `q - 1` points when `-1`
is a square (`ncard_conic_plus`). -/

/-- The parametrisation of the conic from `(0,1)`: `none ↦ (0,1)` and
`some t ↦ (2t/(t²+1), (t²-1)/(t²+1))`. -/
private def conicParam (F : Type*) [Field F] (m : Option F) : F × F :=
  match m with
  | none => (0, 1)
  | some t => (2 * t / (t ^ 2 + 1), (t ^ 2 - 1) / (t ^ 2 + 1))

/-- The slope of the line joining `p` to `(0,1)`; `none` when `p = (0,1)`. -/
private noncomputable def conicSlope (F : Type*) [Field F] (p : F × F) : Option F := by
  classical
  exact if p.2 = 1 then none else some (p.1 / (1 - p.2))

/-- The parametrisation lands on the conic. -/
private lemma conicParam_mem (F : Type*) [Field F] (h : ∀ i : F, i * i ≠ -1) (m : Option F) :
    (conicParam F m).1 ^ 2 + (conicParam F m).2 ^ 2 = 1 := by
  cases m with
  | none => simp [conicParam]
  | some t =>
    have ht : t ^ 2 + 1 ≠ 0 := by intro hc; exact h t (by linear_combination hc)
    simp only [conicParam]
    field_simp
    ring

/-- `conicSlope` is a left inverse of the parametrisation. -/
private lemma conicSlope_conicParam (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (h : ∀ i : F, i * i ≠ -1) (m : Option F) : conicSlope F (conicParam F m) = m := by
  cases m with
  | none => simp [conicParam, conicSlope]
  | some t =>
    have ht : t ^ 2 + 1 ≠ 0 := by intro hc; exact h t (by linear_combination hc)
    have hne : (t ^ 2 - 1) / (t ^ 2 + 1) ≠ 1 := by
      intro hc
      have heq : t ^ 2 - 1 = t ^ 2 + 1 := (div_eq_one_iff_eq ht).mp hc
      exact h2 (by linear_combination -heq)
    rw [conicSlope]
    split_ifs with hc
    · exact absurd (by simpa only [conicParam] using hc) hne
    · congr 1
      simp only [conicParam]
      have hden : 1 - (t ^ 2 - 1) / (t ^ 2 + 1) = 2 / (t ^ 2 + 1) := by
        field_simp
        ring
      rw [hden, div_div_eq_mul_div]
      rw [div_mul_eq_mul_div₀]
      rw [mul_div_cancel_right₀ _ ht]
      rw [mul_comm 2 t, mul_div_cancel_right₀ _ h2]

/-- The parametrisation is injective (it has the left inverse `conicSlope`). -/
private lemma conicParam_inj (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (h : ∀ i : F, i * i ≠ -1) : Function.Injective (conicParam F) := by
  intro m m' hmm
  have h1 : conicSlope F (conicParam F m) = conicSlope F (conicParam F m') := by rw [hmm]
  rwa [conicSlope_conicParam F h2 h m, conicSlope_conicParam F h2 h m'] at h1

/-- The parametrisation is surjective onto the conic (its explicit right inverse). -/
private lemma conicParam_surj (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) {p : F × F}
    (hp : p.1 ^ 2 + p.2 ^ 2 = 1) : ∃ m : Option F, conicParam F m = p := by
  by_cases hb : p.2 = 1
  · have hp1 : p.1 = 0 := by
      have h : p.1 ^ 2 = 0 := by
        have hhp := hp
        rw [hb] at hhp
        linear_combination hhp
      exact sq_eq_zero_iff.mp h
    refine ⟨none, ?_⟩
    simp only [conicParam]
    ext <;> simp [hp1, hb]
  · have hd : 1 - p.2 ≠ 0 := by intro h; exact hb (by linear_combination -h)
    have ht2 : (p.1 / (1 - p.2)) ^ 2 = (1 + p.2) / (1 - p.2) := by
      field_simp
      linear_combination hp
    have ht2p1 : (p.1 / (1 - p.2)) ^ 2 + 1 = 2 / (1 - p.2) := by
      rw [ht2]
      field_simp
      ring
    have hc1 : 2 * (p.1 / (1 - p.2)) / ((p.1 / (1 - p.2)) ^ 2 + 1) = p.1 := by
      rw [ht2p1, div_div_eq_mul_div]
      rw [mul_assoc, div_mul_cancel₀ _ hd]
      rw [mul_comm 2 p.1, mul_div_cancel_right₀ _ h2]
    have hc2 : ((p.1 / (1 - p.2)) ^ 2 - 1) / ((p.1 / (1 - p.2)) ^ 2 + 1) = p.2 := by
      rw [ht2p1, ht2]
      field_simp
      ring
    exact ⟨some (p.1 / (1 - p.2)), by simp only [conicParam]; exact Prod.ext hc1 hc2⟩

/-- If `-1` is not a square in a finite field of odd characteristic, the conic `a² + b² = 1`
has `q + 1` points. -/
private lemma ncard_conic_not (F : Type*) [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (h : ∀ i : F, i * i ≠ -1) :
    {p : F × F | p.1 ^ 2 + p.2 ^ 2 = 1}.ncard = Nat.card F + 1 := by
  have key : (Set.univ : Set (Option F)).ncard = {p : F × F | p.1 ^ 2 + p.2 ^ 2 = 1}.ncard :=
    Set.ncard_congr (s := (Set.univ : Set (Option F))) (f := fun m _ => conicParam F m)
      (fun m _ => conicParam_mem F h m)
      (fun a b _ _ hab => conicParam_inj F h2 h hab)
      (fun p hp => by
        obtain ⟨m, hm⟩ := conicParam_surj F h2 hp
        exact ⟨m, Set.mem_univ m, hm⟩)
  rw [← key, Set.ncard_univ, Finite.card_option]

/-! ## The centralizer of `z` -/

/-- The matrix `!![a, b; -b, a]` attached to a point of the conic, as an element of `SL(2,F)`.
Its determinant is `a² + b² = 1`. -/
private def conicToSL (F : Type*) [Field F] (p : F × F) (hp : p.1 ^ 2 + p.2 ^ 2 = 1) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![p.1, p.2; -p.2, p.1], by
    rw [Matrix.det_fin_two_of]
    linear_combination hp⟩

/-- `Nat.card (circle F)` equals the number of points of the conic: `mem_circle` identifies
`circle F` with the image of `(a,b) ↦ !![a,b;-b,a]`, which is injective. -/
private theorem card_circle_eq_ncard_conic (F : Type*) [Field F] :
    Nat.card (Work.L2F.circle F) = {p : F × F | p.1 ^ 2 + p.2 ^ 2 = 1}.ncard := by
  rw [← SetLike.coe_sort_coe]
  rw [Nat.card_coe_set_eq]
  refine (Set.ncard_congr (s := {p : F × F | p.1 ^ 2 + p.2 ^ 2 = 1})
    (t := (Work.L2F.circle F : Set (Matrix.SpecialLinearGroup (Fin 2) F)))
    (fun p hp => conicToSL F p hp) ?_ ?_ ?_).symm
  · -- the image lies in `circle F`
    intro p hp
    exact (mem_circle F _).mpr ⟨p.1, p.2, hp, rfl⟩
  · -- injectivity: the matrix determines `(a,b)`
    intro p q hp hq heq
    have hmat := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
      (x : Matrix (Fin 2) (Fin 2) F)) heq
    have h0 := congrFun (congrFun hmat 0) 0
    have h1 := congrFun (congrFun hmat 0) 1
    simp only [conicToSL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val_one] at h0 h1
    exact Prod.ext h0 h1
  · -- surjectivity: `mem_circle` produces the preimage
    intro x hx
    obtain ⟨a, b, hab, hxeq⟩ := (mem_circle F x).mp hx
    refine ⟨(a, b), hab, ?_⟩
    apply Subtype.ext
    rw [hxeq]
    rfl

/-- `|C_{SL(2,F)}(z)| = q - 1` if `-1` is a square and `q + 1` otherwise.  Proof: `mem_circle`
identifies `circle F` with the image of the conic `a² + b² = 1` under the injective map
`(a,b) ↦ !![a,b;-b,a]`; the conic has `q - 1` points when `-1` is a square (`ncard_conic_plus`)
and `q + 1` otherwise (`ncard_conic_not`). -/
theorem circle_card (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) :
    Nat.card (Work.L2F.circle F) = Nat.card F - 1 ∨
      Nat.card (Work.L2F.circle F) = Nat.card F + 1 := by
  rcases Classical.em (∃ i : F, i * i = -1) with ⟨i, hi⟩ | h
  · exact Or.inl (by rw [card_circle_eq_ncard_conic F, ncard_conic_plus F h2 ⟨i, hi⟩])
  · exact Or.inr (by
      rw [card_circle_eq_ncard_conic F, ncard_conic_not F h2 (fun i hii => h ⟨i, hii⟩)])

end Work.L2F.Conic
