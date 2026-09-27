import Mathlib
import Submission.Work.EKLC6Core.InjRadius
import Submission.Work.EKLC6Core.entrybox_cover_V
import Submission.Work.EKLC6Core.mul_inv_mem_V_of_floor_eq
import Submission.Work.EKLC6Core.floorTuple_rel_card_bound

/-!
# `Work.EKLC6Core.vball_packing_uniform` — packing balls are finite *uniformly* in the scale

For a fixed constant `c > 0` there is a single constant `M > 0` bounding the cardinality of every
family `S ⊆ V (c · sep) • z` (`Work.EKLComp.Vball`) which is `sep`-separated "on the left" (no two
distinct points of `S` are related by a displacement in `V sep`), *for all* scales `sep > 0`, all
centres `z ∈ X₃` and all `S`, subject only to the scale hypothesis `c · sep ≤ injCap z / 2`.

This is the cusp-free form of `Work.EKLC6Core.vball_packing_bound`.  That lemma counts the
entrywise floor tuples of the lifts `lift x ∈ V (c · sep)` of the points of `S` at the mesh
`η = sep/48`: two points whose lifts have equal floors differ by less than `η` entrywise, hence
their quotient lies in `V sep` and the separation hypothesis forbids that.  The count obtained
there is `(2 (⌈(1 + c sep)/η⌉₊ + 1) + 1)^9`, which blows up like `sep^{-9}` as `sep → 0`,
because it grids the *absolute* entry box of size `1 + c sep`.

The uniform statement needs the *relative* count: the entries of a lift lie in an interval of
width `2 c sep` (each entry is within `c sep` of the corresponding entry of the identity), so the
number of admissible floors is bounded by the width of that window divided by the mesh, i.e. by
`2 c sep / (sep/48) = 96 c`, which is independent of `sep`.  This is exactly
`Work.EKLC6Core.floorTuple_rel_card_bound`, applied with centre `c₀ = 1` (the identity matrix),
width `R = c sep ≤ ⌈48 c⌉₊ · η` and `N = ⌈48 c⌉₊`, giving the uniform bound
`M = max 1 ((2 ⌈48 c⌉₊ + 2)^9)`.

The hypothesis `c · sep ≤ injCap z / 2` enters only through `injCap z ≤ 1/2`
(`Work.EKLC6Core.injCap_le_half`), which gives `c sep ≤ 1/4`; at that scale `lift x` lies in the
closed unit entry-box, which is what makes the entrywise estimates on `SL₃(ℝ)` available
(`Work.EKLC6Core.mul_inv_mem_V_of_floor_eq`).
-/

set_option linter.unusedVariables false

namespace Work.EKLC6Core

/-- **Packing bound for `V`-balls, uniform in the scale.**  For `c > 0` there is `M > 0` such
that for every `sep > 0`, every `z ∈ X₃` and every finite `S ⊆ V (c sep) • z` with no two distinct
points of `S` related by a displacement in `V sep`, subject to `c sep ≤ injCap z / 2`, one has
`|S| ≤ M`. -/
theorem vball_packing_uniform {c : ℝ} (hc : 0 < c) :
    ∃ M : ℝ, 0 < M ∧ ∀ (sep : ℝ) (hsep : 0 < sep) (z : Work.EKLContract.X3)
      (S : Finset Work.EKLContract.X3),
      (c * sep ≤ Work.EKLC6Core.injCap z / 2) →
      (∀ x ∈ S, x ∈ Work.EKLComp.Vball (c * sep) z) →
      (∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → ∀ w : Work.EKLContract.SL3,
        w ∈ Work.EKLContract.V sep → w • x ≠ x') →
      (S.card : ℝ) ≤ M := by
  classical
  -- the uniform bound: `(2 ⌈48 c⌉₊ + 2)^9` (the mesh `η = sep/48` and the relative width
  -- `c sep` give at most `2 ⌈48 c⌉₊ + 2` admissible floors per entry)
  refine ⟨max 1 (((2 * ⌈48 * c⌉₊ + 2) ^ 9 : ℕ) : ℝ), lt_max_of_lt_left one_pos, ?_⟩
  intro sep hsep z S hcap hball hpack
  -- the mesh of the floor grid, chosen so that `24 η < sep`
  set η : ℝ := sep / 48 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; linarith
  have h24 : 24 * η < sep := by rw [hηdef]; linarith
  -- the hypothesis puts `c sep` below `1/4`, where the entrywise estimates hold
  have hu4 : c * sep ≤ 1 / 4 := le_trans hcap (by have h := injCap_le_half z; linarith)
  -- the lift of a point of `S` to an element of `V (c sep)`
  set lift : Work.EKLContract.X3 → Work.EKLContract.SL3 := fun x =>
    if h : ∃ u : Work.EKLContract.SL3,
        u ∈ Work.EKLContract.V (c * sep) ∧ u • z = x then Classical.choose h else 1
    with hliftdef
  have hlift : ∀ x ∈ S, lift x ∈ Work.EKLContract.V (c * sep) ∧ (lift x) • z = x := by
    intro x hx
    have hex : ∃ u : Work.EKLContract.SL3,
        u ∈ Work.EKLContract.V (c * sep) ∧ u • z = x :=
      Work.EKLComp.mem_Vball.mp (hball x hx)
    have h1 : lift x = Classical.choose hex := by rw [hliftdef]; exact dif_pos hex
    rw [h1]; exact Classical.choose_spec hex
  -- the nine entry functions of the lifts
  set f : Work.EKLContract.X3 → (Fin 3 × Fin 3 → ℝ) := fun x p =>
    ((lift x : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2 with hfdef
  -- every entry of a lift lies in the window of width `2 c sep` around the identity
  have hrange : ∀ x ∈ S, ∀ p : Fin 3 × Fin 3,
      |f x p - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2| ≤ c * sep := by
    intro x hx p
    exact le_of_lt ((hlift x hx).1 p.1 p.2)
  -- distinct points of `S` have distinct floor tuples: equal floors would put the quotient of
  -- the two lifts in `V sep` and exhibit `x' = w • x` with `w ∈ V sep`
  have hfloorinj : ∀ x ∈ S, ∀ x' ∈ S,
      (∀ p : Fin 3 × Fin 3, ⌊f x p / η⌋ = ⌊f x' p / η⌋) → x = x' := by
    intro x hx x' hx' hfl
    by_contra hne
    have h1 := hlift x hx
    have h2 := hlift x' hx'
    have hfl' : ∀ i j : Fin 3,
        ⌊((lift x : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j / η⌋
          = ⌊((lift x' : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j / η⌋ := by
      intro i j
      have h := hfl (i, j)
      simpa only [hfdef] using h
    have hmem : (lift x') * (lift x)⁻¹ ∈ Work.EKLContract.V sep :=
      mul_inv_mem_V_of_floor_eq hu4 hηpos h24 h1.1 hfl'
    have heq : ((lift x') * (lift x)⁻¹) • x = x' := by
      have step1 : ((lift x') * (lift x)⁻¹) • x
          = ((lift x') * (lift x)⁻¹) • ((lift x) • z) := by rw [h1.2]
      rw [step1, ← mul_smul]
      have hcc : (lift x' * (lift x)⁻¹) * lift x = lift x' := by group
      rw [hcc, h2.2]
    exact (hpack x hx x' hx' hne _ hmem) heq
  -- the relative width `c sep` is at most `⌈48 c⌉₊` mesh steps
  have hR : c * sep ≤ ((⌈48 * c⌉₊ : ℕ) : ℝ) * η := by
    have h48 : 48 * c ≤ ((⌈48 * c⌉₊ : ℕ) : ℝ) := Nat.le_ceil (48 * c)
    have h1 : c * sep = 48 * c * η := by rw [hηdef]; ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right h48 (le_of_lt hηpos)
  have hcard := floorTuple_rel_card_bound (S := S) (f := f) (η := η) (R := c * sep)
    (c₀ := fun p : Fin 3 × Fin 3 => (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2)
    (N := ⌈48 * c⌉₊) hηpos hR hrange hfloorinj
  have h9 : Fintype.card (Fin 3 × Fin 3) = 9 := by simp
  rw [h9] at hcard
  calc (S.card : ℝ) ≤ (((2 * ⌈48 * c⌉₊ + 2) ^ 9 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ max 1 (((2 * ⌈48 * c⌉₊ + 2) ^ 9 : ℕ) : ℝ) := le_max_right _ _

end Work.EKLC6Core
