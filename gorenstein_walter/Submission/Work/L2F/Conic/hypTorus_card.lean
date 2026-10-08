import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Conic.mem_hypTorus
import Submission.Work.L2F.Conic.ParamMinus

set_option autoImplicit false

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Conic

variable {F : Type*} [Field F]

/-! ## The conic `a² - d·b² = 1` has `q + 1` points

For a finite field `F` of odd characteristic and `d ≠ 0` not a square, the conic
`C = {(a,b) | a² - d·b² = 1}` has exactly `q + 1` points: the map
`t ↦ conicMinusParam d t = ((1 + d t²)/(1 - d t²), 2 t/(1 - d t²))` is a bijection from `F`
onto `C \ {(-1,0)}` (its denominator `1 - d t²` never vanishes because `d t² = 1` would make
`d = (t⁻¹)²` a square), and `(-1,0)` is the one remaining point of `C`. -/

/-- The slope of the line through `(-1,0)` and `p`, namely `p.2 / (1 + p.1)`. -/
private noncomputable def conicMinusSlope (p : F × F) : F := p.2 / (1 + p.1)

/-- `1 - d t² ≠ 0` when `d` is not a square (in particular `d t² ≠ 1` for every `t`). -/
private lemma one_sub_mul_sq_ne_zero (d : F) (h : ∀ a : F, a * a ≠ d) (t : F) :
    1 - d * t ^ 2 ≠ 0 := by
  intro ht
  have hdt : d * t ^ 2 = 1 := by linear_combination -ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at hdt
  have hd' : d = (t⁻¹) ^ 2 := by
    field_simp
    exact hdt
  exact h t⁻¹ (by rw [← sq]; exact hd'.symm)

/-- The parametrised point `conicMinusParam d t` lies on the conic `a² - d·b² = 1`. -/
private lemma conicMinusParam_mem (d : F) (h : ∀ a : F, a * a ≠ d) (t : F) :
    (conicMinusParam d t).1 ^ 2 - d * (conicMinusParam d t).2 ^ 2 = 1 := by
  have hden := one_sub_mul_sq_ne_zero d h t
  simp only [conicMinusParam]
  field_simp
  ring

/-- The slope attached to the parametrised point is the parameter. -/
private lemma conicMinusSlope_conicMinusParam (h2 : (2 : F) ≠ 0) (d : F)
    (h : ∀ a : F, a * a ≠ d) (t : F) : conicMinusSlope (conicMinusParam d t) = t := by
  have hden : 1 - d * t ^ 2 ≠ 0 := one_sub_mul_sq_ne_zero d h t
  have hden' : 1 - t ^ 2 * d ≠ 0 := by rwa [mul_comm (t ^ 2) d]
  have h1 : 1 + (1 + d * t ^ 2) / (1 - d * t ^ 2) = 2 / (1 - d * t ^ 2) := by
    field_simp
    ring
  simp only [conicMinusSlope, conicMinusParam, h1]
  field_simp

/-- The parametrisation is injective. -/
private lemma conicMinusParam_injective (h2 : (2 : F) ≠ 0) (d : F)
    (h : ∀ a : F, a * a ≠ d) : Function.Injective (conicMinusParam d) := by
  intro s t hst
  have h1 := conicMinusSlope_conicMinusParam h2 d h s
  have h2' := conicMinusSlope_conicMinusParam h2 d h t
  rw [hst] at h1
  rw [h1] at h2'
  exact h2'

/-- No parametrised point is `(-1,0)`. -/
private lemma conicMinusParam_ne (h2 : (2 : F) ≠ 0) (d : F) (h : ∀ a : F, a * a ≠ d)
    (t : F) : conicMinusParam d t ≠ (-1, 0) := by
  intro heq
  have hden : 1 - d * t ^ 2 ≠ 0 := one_sub_mul_sq_ne_zero d h t
  have h2c : 2 * t / (1 - d * t ^ 2) = (0 : F) := by
    have h := congrArg Prod.snd heq
    simpa only [conicMinusParam] using h
  have h1c : (1 + d * t ^ 2) / (1 - d * t ^ 2) = (-1 : F) := by
    have h := congrArg Prod.fst heq
    simpa only [conicMinusParam] using h
  have ht : t = 0 := by
    have h0 : 2 * t = 0 := by
      rcases div_eq_zero_iff.mp h2c with hc | hc
      · exact hc
      · exact absurd hc hden
    exact (mul_eq_zero.mp h0).resolve_left h2
  rw [div_eq_iff hden] at h1c
  rw [ht] at h1c
  simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero, sub_zero, mul_one] at h1c
  exact h2 (by linear_combination h1c)

/-- Every point of the conic other than `(-1,0)` is a parametrised point. -/
private lemma conicMinusParam_surj (h2 : (2 : F) ≠ 0) (d : F) (hd : d ≠ 0)
    {p : F × F} (hp : p.1 ^ 2 - d * p.2 ^ 2 = 1)
    (hpne : p ≠ (-1, 0)) : ∃ t : F, conicMinusParam d t = p := by
  have hp1 : p.1 ≠ -1 := by
    intro h1
    have h0 : d * p.2 ^ 2 = 0 := by
      rw [h1] at hp
      linear_combination -hp
    have hb : p.2 = 0 := by
      have h2' : p.2 ^ 2 = 0 := (mul_eq_zero.mp h0).resolve_left hd
      exact (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp h2'
    exact hpne (Prod.ext h1 hb)
  have hne : 1 + p.1 ≠ 0 := by
    intro hc
    exact hp1 (by linear_combination hc)
  have hA : 1 - d * (p.2 / (1 + p.1)) ^ 2 = 2 / (1 + p.1) := by
    field_simp
    linear_combination hp
  have hB : 1 + d * (p.2 / (1 + p.1)) ^ 2 = 2 * p.1 / (1 + p.1) := by
    field_simp
    linear_combination -hp
  refine ⟨p.2 / (1 + p.1), ?_⟩
  ext
  · simp only [conicMinusParam]
    rw [hB, hA]
    field_simp
  · simp only [conicMinusParam]
    rw [hA]
    field_simp

/-- The conic `a² - d·b² = 1` has `q + 1` points when `d ≠ 0` is a nonsquare in a finite field
of odd characteristic. -/
private theorem ncard_conicMinus [Fintype F] (h2 : (2 : F) ≠ 0) (d : F) (hd : d ≠ 0)
    (h : ∀ a : F, a * a ≠ d) :
    {p : F × F | p.1 ^ 2 - d * p.2 ^ 2 = 1}.ncard = Nat.card F + 1 := by
  have hmemi : ∀ t : F, conicMinusParam d t ∈ {p : F × F | p.1 ^ 2 - d * p.2 ^ 2 = 1} :=
    fun t => conicMinusParam_mem d h t
  have hinj : Function.Injective (conicMinusParam d) := conicMinusParam_injective h2 d h
  have hsurj : ∀ p ∈ {p : F × F | p.1 ^ 2 - d * p.2 ^ 2 = 1}, p ≠ (-1, 0) →
      ∃ t : F, conicMinusParam d t = p :=
    fun p hp hpne => conicMinusParam_surj h2 d hd hp hpne
  have hne : (-1, 0) ∉ conicMinusParam d '' (Set.univ : Set F) := by
    rintro ⟨t, -, ht⟩
    exact conicMinusParam_ne h2 d h t ht
  have himg : conicMinusParam d '' (Set.univ : Set F) =
      {p : F × F | p.1 ^ 2 - d * p.2 ^ 2 = 1} \ {(-1, 0)} := by
    ext p
    constructor
    · rintro ⟨t, -, rfl⟩
      exact ⟨hmemi t, fun hp' => hne ⟨t, Set.mem_univ t, hp'⟩⟩
    · rintro ⟨hp, hpne⟩
      obtain ⟨t, ht⟩ := hsurj p hp (by simpa using hpne)
      exact ⟨t, Set.mem_univ t, ht⟩
  have hCeq : {p : F × F | p.1 ^ 2 - d * p.2 ^ 2 = 1} =
      insert (-1, 0) (conicMinusParam d '' (Set.univ : Set F)) := by
    rw [himg]
    ext p
    simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · intro hp
      by_cases h1 : p = (-1, 0)
      · exact Or.inl h1
      · exact Or.inr ⟨hp, h1⟩
    · rintro (rfl | ⟨hp, -⟩)
      · simp
      · exact hp
  have hfin : (conicMinusParam d '' (Set.univ : Set F)).Finite :=
    Set.Finite.image (conicMinusParam d) (Set.finite_univ (α := F))
  calc {p : F × F | p.1 ^ 2 - d * p.2 ^ 2 = 1}.ncard
      = (insert (-1, 0) (conicMinusParam d '' (Set.univ : Set F))).ncard := by rw [hCeq]
    _ = (conicMinusParam d '' (Set.univ : Set F)).ncard + 1 :=
          Set.ncard_insert_of_notMem hne hfin
    _ = (Set.univ : Set F).ncard + 1 := by rw [Set.ncard_image_of_injective _ hinj]
    _ = Nat.card F + 1 := by rw [Set.ncard_univ]

/-! ## The bijection between the conic and `hypTorus F d` -/

/-- The matrix `!![a, d*b; b, a]`, as an element of `SL(2,F)` when `a² - d b² = 1`. -/
private def matOfConic (d : F) (p : F × F) (hp : p.1 ^ 2 - d * p.2 ^ 2 = 1) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![p.1, d * p.2; p.2, p.1], by
    rw [Matrix.det_fin_two_of]
    linear_combination hp⟩

private lemma matOfConic_mem (d : F) (p : F × F) (hp : p.1 ^ 2 - d * p.2 ^ 2 = 1) :
    matOfConic d p hp ∈ Work.L2F.hypTorusSet F d :=
  ⟨p.1, p.2, hp, rfl⟩

private lemma matOfConic_inj (d : F) (p q : F × F) (hp : p.1 ^ 2 - d * p.2 ^ 2 = 1)
    (hq : q.1 ^ 2 - d * q.2 ^ 2 = 1) (heq : matOfConic d p hp = matOfConic d q hq) :
    p = q := by
  have hmat := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
    (x : Matrix (Fin 2) (Fin 2) F)) heq
  have h0 := congrFun (congrFun hmat 0) 0
  have h1 := congrFun (congrFun hmat 1) 0
  simp only [matOfConic, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one] at h0 h1
  exact Prod.ext h0 h1

private lemma matOfConic_surj (d : F) (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : x ∈ Work.L2F.hypTorus F d) :
    ∃ p : F × F, ∃ hp : p.1 ^ 2 - d * p.2 ^ 2 = 1, matOfConic d p hp = x := by
  obtain ⟨a, b, hab, hx'⟩ := (mem_hypTorus F d x).mp hx
  refine ⟨(a, b), hab, ?_⟩
  apply Subtype.ext
  simp only [matOfConic]
  exact hx'.symm

/-- `hypTorus F d` and the conic `a² - d·b² = 1` have the same number of elements, via
`p ↦ !![p.1, d * p.2; p.2, p.1]`. -/
private theorem ncard_hypTorus_eq_conic (d : F) :
    (Work.L2F.hypTorus F d : Set (Matrix.SpecialLinearGroup (Fin 2) F)).ncard =
      {p : F × F | p.1 ^ 2 - d * p.2 ^ 2 = 1}.ncard :=
  (Set.ncard_congr (s := {p : F × F | p.1 ^ 2 - d * p.2 ^ 2 = 1})
    (t := (Work.L2F.hypTorus F d : Set (Matrix.SpecialLinearGroup (Fin 2) F)))
    (fun p hp => matOfConic d p hp)
    (fun p hp => Subgroup.subset_closure (matOfConic_mem d p hp))
    (fun p q hp hq heq => matOfConic_inj d p q hp hq heq)
    (fun x hx => matOfConic_surj d x hx)).symm

end Work.L2F.Conic

namespace Work.L2F.Conic

/-- A nonsquare `d ≠ 0` in a finite field of odd characteristic gives `|hypTorus F d| = q + 1`.
Proof: `mem_hypTorus` describes `hypTorus F d` as the image of
`{p : F × F | p.1² - d * p.2² = 1}` under the injective map `p ↦ !![p.1, d * p.2; p.2, p.1]`, and
`ncard_conic_minus` says that set has `q + 1` elements.  (That counting fact — the same statement
as `ncard_conic_minus` — is proved inline below as `ncard_conicMinus` by the rational
parametrisation `conicMinusParam` of the conic from the point `(-1,0)`, so that this file is
self-contained.) -/
theorem hypTorus_card (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (d : F) (hd : d ≠ 0)
    (h : ∀ a : F, a * a ≠ d) :
    Nat.card (Work.L2F.hypTorus F d) = Nat.card F + 1 := by
  show (Work.L2F.hypTorus F d : Set (Matrix.SpecialLinearGroup (Fin 2) F)).ncard = Nat.card F + 1
  rw [ncard_hypTorus_eq_conic d]
  exact ncard_conicMinus h2 d hd h

end Work.L2F.Conic
