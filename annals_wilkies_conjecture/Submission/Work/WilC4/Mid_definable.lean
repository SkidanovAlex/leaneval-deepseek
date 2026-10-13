/-
  WilC4/Mid_definable : `Mid E` is `∅`-definable when `E ⊆ ℝ` is.

  `Mid E` (see `ULPMDev`) is the set of *geometric midpoints* of consecutive positive elements
  of `E ⊆ ℝ`:

      x ∈ Mid E ↔ ∃ ρ₁ ∈ E, ∃ ρ₂ ∈ E, 0 < ρ₁ ∧ ρ₁ < ρ₂ ∧
                     (∀ ρ ∈ E, 0 < ρ → ρ ≤ ρ₁ ∨ ρ₂ ≤ ρ) ∧ x * x = ρ₁ * ρ₂ ∧ 0 < x

  so it is a first-order definition over `ℝ` in the single parameter `E`.  As `E` is `∅`-definable
  in `LRc`, so is `Mid E`: the whole proof is quantifier bookkeeping, built from the arithmetic
  toolkit of `ClusterTool` (ring terms are comparable definable functions) and the projection
  lemmas `Set.Definable.exists_of_finite` / `forall_of_finite`.

  The chain of sets (contexts are nested right blocks, so quantifiers are eliminated from the
  right):

  * `MidCx = x`,
  * `MidC1 = (x, ρ₁)`,
  * `MidC2 = (x, ρ₁, ρ₂)`,
  * `MidC3 = (x, ρ₁, ρ₂, ρ)`   — the universally quantified element of `E`.

  `MidBadD` is the bad set of the one-variable universal clause `∀ ρ ∈ E, 0 < ρ → ρ ≤ ρ₁ ∨ ρ₂ ≤ ρ`
  in the context `MidC3`; eliminating `ρ` gives `MidBadSet` in `MidC2`, whose complement is
  `MidGood`.  `MidBody` is the body of the definition in the context `MidC2`, and `MidSet` is
  obtained from it by eliminating `ρ₂` and then `ρ₁`.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ClusterTool

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The contexts and their slots -/

/-- The context `x`. -/
abbrev MidCx : Type := Fin 1

/-- The context `(x, ρ₁)`. -/
abbrev MidC1 : Type := MidCx ⊕ Fin 1

/-- The context `(x, ρ₁, ρ₂)`. -/
abbrev MidC2 : Type := MidC1 ⊕ Fin 1

/-- The context `(x, ρ₁, ρ₂, ρ)`. -/
abbrev MidC3 : Type := MidC2 ⊕ Fin 1

/-- `x` in `MidCx`. -/
def mid_sx : MidCx := 0

/-- `x` in `MidC1`. -/
def mid_x1 : MidC1 := Sum.inl mid_sx

/-- `ρ₁` in `MidC1`. -/
def mid_q1 : MidC1 := Sum.inr (0 : Fin 1)

/-- `x` in `MidC2`. -/
def mid_x2 : MidC2 := Sum.inl mid_x1

/-- `ρ₁` in `MidC2`. -/
def mid_a2 : MidC2 := Sum.inl mid_q1

/-- `ρ₂` in `MidC2`. -/
def mid_b2 : MidC2 := Sum.inr (0 : Fin 1)

/-- `x` in `MidC3`. -/
def mid_x3 : MidC3 := Sum.inl mid_x2

/-- `ρ₁` in `MidC3`. -/
def mid_a3 : MidC3 := Sum.inl mid_a2

/-- `ρ₂` in `MidC3`. -/
def mid_b3 : MidC3 := Sum.inl mid_b2

/-- `ρ` in `MidC3`. -/
def mid_r3 : MidC3 := Sum.inr (0 : Fin 1)

@[simp] theorem mid_elim_r3 (w : MidC2 → ℝ) (ρ : Fin 1 → ℝ) :
    (Sum.elim w ρ) mid_r3 = ρ 0 := rfl
@[simp] theorem mid_elim_a3 (w : MidC2 → ℝ) (ρ : Fin 1 → ℝ) :
    (Sum.elim w ρ) mid_a3 = w mid_a2 := rfl
@[simp] theorem mid_elim_b3 (w : MidC2 → ℝ) (ρ : Fin 1 → ℝ) :
    (Sum.elim w ρ) mid_b3 = w mid_b2 := rfl
@[simp] theorem mid_elim_x2 (v ρ₁ ρ₂ : Fin 1 → ℝ) :
    (Sum.elim (Sum.elim v ρ₁) ρ₂) mid_x2 = v 0 := rfl
@[simp] theorem mid_elim_a2 (v ρ₁ ρ₂ : Fin 1 → ℝ) :
    (Sum.elim (Sum.elim v ρ₁) ρ₂) mid_a2 = ρ₁ 0 := rfl
@[simp] theorem mid_elim_b2 (v ρ₁ ρ₂ : Fin 1 → ℝ) :
    (Sum.elim (Sum.elim v ρ₁) ρ₂) mid_b2 = ρ₂ 0 := rfl

/-! ## 2. Membership in a definable set, read off a coordinate -/

/-- If `E ⊆ ℝ` is `∅`-definable, so is `{u : ρ → ℝ | u s ∈ E}` for any slot `s`. -/
theorem memE_definable {E : Set ℝ} (hE : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc E)
    {ρ : Type} (s : ρ) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc {u : ρ → ℝ | u s ∈ E} := by
  have h := hE.preimage_comp (fun _ : Fin 1 => s)
  have hset : {u : ρ → ℝ | u s ∈ E} =
      (fun g : ρ → ℝ => g ∘ (fun _ : Fin 1 => s)) ⁻¹'
        {x : Fin 1 → ℝ | x 0 ∈ E} := by
    ext u; rfl
  rw [hset]; exact h

/-! ## 3. The pieces of the definition -/

/-- `ρ₁ ∈ E`. -/
def MidE1 (E : Set ℝ) : Set (MidC2 → ℝ) := {w | w mid_a2 ∈ E}

/-- `ρ₂ ∈ E`. -/
def MidE2 (E : Set ℝ) : Set (MidC2 → ℝ) := {w | w mid_b2 ∈ E}

/-- `0 < ρ₁`. -/
def MidPos1 : Set (MidC2 → ℝ) := {w | 0 < w mid_a2}

/-- `ρ₁ < ρ₂`. -/
def MidLt : Set (MidC2 → ℝ) := {w | w mid_a2 < w mid_b2}

/-- `x * x = ρ₁ * ρ₂`. -/
def MidSq : Set (MidC2 → ℝ) := {w | w mid_x2 * w mid_x2 = w mid_a2 * w mid_b2}

/-- `0 < x`. -/
def MidPosX : Set (MidC2 → ℝ) := {w | 0 < w mid_x2}

/-- The bad set of the universal clause `∀ ρ ∈ E, 0 < ρ → ρ ≤ ρ₁ ∨ ρ₂ ≤ ρ`, in the context
`(x, ρ₁, ρ₂, ρ)`: the element `ρ` is in `E`, positive, and fails both inequalities
(`ρ₁ < ρ` and `ρ < ρ₂`, the strict-inequality form of the failure). -/
def MidBadD (E : Set ℝ) : Set (MidC3 → ℝ) :=
  {w | w mid_r3 ∈ E ∧ 0 < w mid_r3 ∧ w mid_a3 < w mid_r3 ∧ w mid_r3 < w mid_b3}

/-- The projection of `MidBadD` over `ρ`. -/
def MidBadSet (E : Set ℝ) : Set (MidC2 → ℝ) :=
  {w | ∃ ρ : Fin 1 → ℝ, Sum.elim w ρ ∈ MidBadD E}

/-- The complement of `MidBadSet`: the universal clause holds. -/
def MidGood (E : Set ℝ) : Set (MidC2 → ℝ) := (MidBadSet E)ᶜ

/-- The body of the definition of `Mid E`, in the context `(x, ρ₁, ρ₂)`. -/
def MidBody (E : Set ℝ) : Set (MidC2 → ℝ) :=
  (((((MidE1 E ∩ MidE2 E) ∩ MidPos1) ∩ MidLt) ∩ MidGood E) ∩ MidSq) ∩ MidPosX

/-- The set of `x` admitting `ρ₁, ρ₂` making `MidBody` hold; equal to `{x | x ∈ Mid E}`. -/
def MidSet (E : Set ℝ) : Set (MidCx → ℝ) :=
  {v | ∃ ρ₁ : Fin 1 → ℝ, ∃ ρ₂ : Fin 1 → ℝ, Sum.elim (Sum.elim v ρ₁) ρ₂ ∈ MidBody E}

/-! ## 4. Definability of the pieces -/

theorem MidE1_definable {E : Set ℝ} (hE : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc E) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (MidE1 E) := memE_definable hE mid_a2

theorem MidE2_definable {E : Set ℝ} (hE : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc E) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (MidE2 E) := memE_definable hE mid_b2

theorem MidPos1_definable : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc MidPos1 := by
  have h := definable_lt_fun (ρ := MidC2) (defFun_const (ρ := MidC2) 0)
    (Set.DefinableFun.proj (L := WilkiesDesign.CG.LRc) (A := (∅ : Set ℝ)) (i := mid_a2))
  simpa [MidPos1] using h

theorem MidLt_definable : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc MidLt := by
  have h := definable_lt_fun (ρ := MidC2)
    (Set.DefinableFun.proj (L := WilkiesDesign.CG.LRc) (A := (∅ : Set ℝ)) (i := mid_a2))
    (Set.DefinableFun.proj (L := WilkiesDesign.CG.LRc) (A := (∅ : Set ℝ)) (i := mid_b2))
  simpa [MidLt] using h

theorem MidSq_definable : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc MidSq := by
  have h := definable_eq_fun (ρ := MidC2)
    (defFun_mul (ρ := MidC2) mid_x2 mid_x2) (defFun_mul (ρ := MidC2) mid_a2 mid_b2)
  simpa [MidSq] using h

theorem MidPosX_definable : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc MidPosX := by
  have h := definable_lt_fun (ρ := MidC2) (defFun_const (ρ := MidC2) 0)
    (Set.DefinableFun.proj (L := WilkiesDesign.CG.LRc) (A := (∅ : Set ℝ)) (i := mid_x2))
  simpa [MidPosX] using h

theorem MidBadD_definable {E : Set ℝ} (hE : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc E) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (MidBadD E) := by
  have h1 : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc {w : MidC3 → ℝ | w mid_r3 ∈ E} :=
    memE_definable hE mid_r3
  have h2 : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc {w : MidC3 → ℝ | 0 < w mid_r3} := by
    have h := definable_lt_fun (ρ := MidC3) (defFun_const (ρ := MidC3) 0)
      (Set.DefinableFun.proj (L := WilkiesDesign.CG.LRc) (A := (∅ : Set ℝ)) (i := mid_r3))
    simpa using h
  have h3 : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {w : MidC3 → ℝ | w mid_a3 < w mid_r3 ∧ w mid_r3 < w mid_b3} := by
    have hA := definable_lt_fun (ρ := MidC3)
      (Set.DefinableFun.proj (L := WilkiesDesign.CG.LRc) (A := (∅ : Set ℝ)) (i := mid_a3))
      (Set.DefinableFun.proj (L := WilkiesDesign.CG.LRc) (A := (∅ : Set ℝ)) (i := mid_r3))
    have hB := definable_lt_fun (ρ := MidC3)
      (Set.DefinableFun.proj (L := WilkiesDesign.CG.LRc) (A := (∅ : Set ℝ)) (i := mid_r3))
      (Set.DefinableFun.proj (L := WilkiesDesign.CG.LRc) (A := (∅ : Set ℝ)) (i := mid_b3))
    convert hA.inter hB using 1
    ext w; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  convert ((h1.inter h2).inter h3) using 1
  ext w
  simp only [MidBadD, Set.mem_setOf_eq, Set.mem_inter_iff]
  tauto

theorem MidBadSet_definable {E : Set ℝ} (hE : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc E) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (MidBadSet E) :=
  (MidBadD_definable hE).exists_of_finite (α := MidC2) (β := Fin 1)

theorem MidGood_definable {E : Set ℝ} (hE : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc E) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (MidGood E) :=
  (MidBadSet_definable hE).compl

theorem MidBody_definable {E : Set ℝ} (hE : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc E) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (MidBody E) :=
  ((((((MidE1_definable hE).inter (MidE2_definable hE)).inter MidPos1_definable).inter
    MidLt_definable).inter (MidGood_definable hE)).inter MidSq_definable).inter MidPosX_definable

theorem MidSet_definable {E : Set ℝ} (hE : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc E) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (MidSet E) :=
  ((MidBody_definable hE).exists_of_finite (α := MidC1) (β := Fin 1)).exists_of_finite
    (α := MidCx) (β := Fin 1)

/-! ## 5. Reading the definition semantically -/

/-- `MidGood E` is exactly the universal clause `∀ ρ ∈ E, 0 < ρ → ρ ≤ ρ₁ ∨ ρ₂ ≤ ρ`. -/
theorem mid_good_mem (E : Set ℝ) (w : MidC2 → ℝ) :
    w ∈ MidGood E ↔ ∀ r : ℝ, r ∈ E → 0 < r → (r ≤ w mid_a2 ∨ w mid_b2 ≤ r) := by
  simp only [MidGood, MidBadSet, Set.mem_compl_iff, Set.mem_setOf_eq, MidBadD]
  constructor
  · intro h r hr h0
    by_contra hcon
    rw [not_or, not_le, not_le] at hcon
    exact h ⟨fun _ : Fin 1 => r, by
      simp only [mid_elim_r3, mid_elim_a3, mid_elim_b3]
      exact ⟨hr, h0, hcon.1, hcon.2⟩⟩
  · rintro h ⟨ρ, hρ⟩
    simp only [mid_elim_r3, mid_elim_a3, mid_elim_b3] at hρ
    obtain ⟨h1, h2, h3, h4⟩ := hρ
    rcases h (ρ 0) h1 h2 with hle | hle <;> linarith

/-- Membership in `MidBody`, read off the coordinates. -/
theorem mid_body_mem (E : Set ℝ) (w : MidC2 → ℝ) :
    w ∈ MidBody E ↔ w mid_a2 ∈ E ∧ w mid_b2 ∈ E ∧ 0 < w mid_a2 ∧ w mid_a2 < w mid_b2 ∧
      (∀ r : ℝ, r ∈ E → 0 < r → (r ≤ w mid_a2 ∨ w mid_b2 ≤ r)) ∧
      w mid_x2 * w mid_x2 = w mid_a2 * w mid_b2 ∧ 0 < w mid_x2 := by
  simp only [MidBody, MidE1, MidE2, MidPos1, MidLt, MidSq, MidPosX, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  rw [mid_good_mem]
  tauto

/-- `MidSet E` is the `Definable₁`-read of `Mid E`. -/
theorem mid_set_mem (E : Set ℝ) (v : Fin 1 → ℝ) :
    v ∈ MidSet E ↔ v 0 ∈ Mid E := by
  simp only [MidSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ρ₁, ρ₂, hw⟩
    rw [mid_body_mem] at hw
    simp only [mid_elim_a2, mid_elim_b2, mid_elim_x2] at hw
    simp only [Mid, Set.mem_setOf_eq]
    exact ⟨ρ₁ 0, hw.1, ρ₂ 0, hw.2.1, hw.2.2⟩
  · rintro hv
    simp only [Mid, Set.mem_setOf_eq] at hv
    rcases hv with ⟨a, ha, b, hb, hrest⟩
    refine ⟨fun _ => a, fun _ => b, ?_⟩
    rw [mid_body_mem]
    simp only [mid_elim_a2, mid_elim_b2, mid_elim_x2]
    exact ⟨ha, hb, hrest⟩

/-! ## 6. The theorem -/

theorem Mid_definable (E : Set ℝ) (hEdef : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc E) :
    (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc (Work.WilC4.Mid E) := by
  rw [Set.Definable₁]
  convert MidSet_definable hEdef using 1
  ext v
  simp only [Set.mem_setOf_eq]
  exact (mid_set_mem E v).symm

end Work.WilC4
