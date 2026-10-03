import Mathlib
import Submission.Work.Peluse.Prop36SW.encDefs
import Submission.Work.Peluse.ladderBaseDefs
import Submission.Work.Peluse.Prop36SW.LStateAbs

/-!
# The vocabulary of the §5 chain in the flat world (`pFlat`, `Abox`, the regrouped multiplicity,
# `LStateBox`)

See `NOTES_prop36SW_of_ladderA_SESSION7.md`.  The chain's state at **slot level `m`** is

* slot type `D.S (m + 1)` (with `Slot ι (fun _ => 1) ≃ ι`);
* parameter type `Fin (nD D (m + 1)) → ℤ` (`= D.Idx (m+1)` flattened), holding the levels `≤ m`;
* box `paramBox (k := fun _ : D.S (m + 1) => 1) M₂`, holding the level-`(m+1)` coordinates;
* coefficient `pFlat D d c m Λ` — the ladder's `p`, the *signed* slot coefficient
  `Λ · (d - m) · dir d c m (par m s) (pad (m+1) a)` of `Work.Peluse.slotCoeff`;
* family `pDirFamG (pFlat D d c m Λ) M₁ a b`, i.e. the level-`(m+1)` direction family.

The round `m → m-1` consumes the level-`(m+1)` coordinates as the new box and regroups the slots by
`D.par m`; the new coefficient is `pFlat D d c (m-1) (Λ * (d - m))`, and the new parameter set is
`Abox D m H` (the levels `≤ m-1` of the closed box), with the box `paramBox (k := fun _ : D.S m => 1) M₂`.

`LStateBox` is `LStateAbs` with the non-vanishing conjunct **removed** (the full product box
`Abox D (m+1) H` is needed for the round's regrouping, while the ladder is applied only on the good
subset — see the session note §2).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-- **The chain's coefficient function at slot level `m`** (flat parameter): the signed slot
coefficient `Λ · slotCoeff D d c m s` read at the flat parameter `x`, i.e.
`Λ · (d - m) · D.dir d c m (D.par m s) (D.pad (m+1) (decD D (m+1) x))`.

For `Λ = 1` this is *definitionally* `Work.Peluse.slotCoeff D d c m s (D.pad (m+1) (decD D (m+1) x))`. -/
def pFlat (D : IdxDatum) (d : ℕ) (c : ℤ) (m : ℕ) (Λ : ℕ) (s : D.S (m + 1))
    (x : Fin (nD D (m + 1)) → ℤ) : ℤ :=
  (Λ : ℤ) * ((d : ℤ) - (m : ℤ)) *
    D.dir d c m (D.par m s) (D.pad (m + 1) (decD D (m + 1) x))

/-- `pFlat` at `Λ = 1` is the (flattened) `slotCoeff` of the node's base definitions. -/
theorem pFlat_one (D : IdxDatum) (d : ℕ) (c : ℤ) (m : ℕ) (s : D.S (m + 1))
    (x : Fin (nD D (m + 1)) → ℤ) :
    pFlat D d c m 1 s x = Work.Peluse.slotCoeff D d c m s (D.pad (m + 1) (decD D (m + 1) x)) := by
  simp only [pFlat, Work.Peluse.slotCoeff]
  ring

/-- **The closed parameter box at level `l`, in the flat parameter type.** -/
def Abox (D : IdxDatum) (l H : ℕ) : Finset (Fin (nD D l) → ℤ) :=
  (D.parBox l H).image (encD D l)

/-- The flat box has the same cardinality as the `D.Idx`-box. -/
theorem card_Abox (D : IdxDatum) (l H : ℕ) : (Abox D l H).card = (D.parBox l H).card :=
  Finset.card_image_of_injective _ (encD_injective D l)

/-- Membership in the flat box: the decoded parameter lies in `D.parBox l H`.  (The converse
fails: `decD` is only a left inverse of `encD`, so a junk parameter outside the image of `encD` can
decode into the box.) -/
theorem decD_mem_parBox_of_mem_Abox {D : IdxDatum} {l H : ℕ} {x : Fin (nD D l) → ℤ}
    (hx : x ∈ Abox D l H) : decD D l x ∈ D.parBox l H := by
  rw [Abox, Finset.mem_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  rwa [decD_encD]

/-- Membership in the flat box, in terms of the encoding. -/
theorem mem_Abox_iff {D : IdxDatum} {l H : ℕ} {x : Fin (nD D l) → ℤ} :
    x ∈ Abox D l H ↔ ∃ a ∈ D.parBox l H, encD D l a = x := by
  rw [Abox, Finset.mem_image]

/-- **The multiplicity function of the state after the round.**  The slots `s : D.S (m+1)` are
grouped by their parent `D.par m s ∈ D.I m` (a nonempty subset of `D.S m`), and the multiplicities
add: `kω' ω = Σ_{s : par m s = ω} t s`.  The slot type `Slot (D.S m) (fun _ => 1) = D.S m × Fin 1` is
identified with `D.S m` through its first component. -/
def regroupKω (D : IdxDatum) (m : ℕ) (t : D.S (m + 1) → ℕ) :
    SlotSet (D.S m) (fun _ => 1) → ℕ :=
  fun ω => ∑ s ∈ Finset.univ.filter (fun s : D.S (m + 1) =>
      D.par m s = ⟨ω.1.image (fun x => x.1), Finset.image_nonempty.mpr ω.2⟩), t s

/-- **The chain state without the non-vanishing conjunct.**  `LStateAbs` with
`(∀ i a, a ∈ A → p i a ≠ 0)` removed: the parameter set is a full *product* box, on which the natural
signed coefficient of the chain does vanish.  The ladder is applied on the good subset only (see the
session note §2), so the state itself must not require non-vanishing. -/
def LStateBox {ι : Type} [Fintype ι] [DecidableEq ι] (kω : SlotSet ι (fun _ => 1) → ℕ)
    {P : Type} [DecidableEq P] (p : ι → P → ℤ) (M₁ M₂ N Dc : ℕ)
    (A : Finset P) (g : P → ℤ → ℂ) (γ : ℝ) : Prop :=
  0 < γ ∧ γ ≤ 1 ∧ 1 ≤ M₂ ∧ M₂ ≤ M₁ ∧ 1 ≤ N ∧ ((M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ)) ∧
  (∀ i a, a ∈ A → |p i a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ)) ∧
  (∀ i a, a ∈ A → |p i a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (Dc : ℤ) * (N : ℤ)) ∧
  (∀ a ∈ A, ∀ x, ‖g a x‖ ≤ 1) ∧ (∀ a ∈ A, SupportIn (g a) N) ∧
  γ ≤ ((A.card : ℝ))⁻¹ * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
      ∑ a ∈ A, ∑ a' ∈ paramBox (k := fun _ : ι => 1) M₂,
        boxNorm (Fintype.card (FamIdx kω))
          (fun j : Fin (Fintype.card (FamIdx kω)) =>
            pDirFamG p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc N) (g a)

/-- An `LStateAbs` is an `LStateBox` (the non-vanishing conjunct is simply dropped). -/
theorem LStateAbs.toBox {ι : Type} [Fintype ι] [DecidableEq ι]
    {kω : SlotSet ι (fun _ => 1) → ℕ} {P : Type} [DecidableEq P] {p : ι → P → ℤ}
    {M₁ M₂ N Dc : ℕ} {A : Finset P} {g : P → ℤ → ℂ} {γ : ℝ}
    (h : LStateAbs kω p M₁ M₂ N Dc A g γ) : LStateBox kω p M₁ M₂ N Dc A g γ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, -, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11⟩

end

end Work.Peluse.Prop36SW
