import Mathlib
import Submission.Work.OROneRel.tlWindowHalvesDefs
import Submission.Work.OROneRel.hnnConjSplit
import Submission.Work.OROneRel.upBlockDefs

/-!
# The pinch dictionary of the two-letter band (shared vocabulary)

Writing `τ = tlLowTau p q hp hq hcop`, `A = hnnEdgeA tlH τ = tlH ⊓ τ⁻¹tlHτ` and
`B = hnnEdgeB tlH τ = τAτ⁻¹ = tlH ⊓ τtlHτ⁻¹`, the *two-way* dictionary between the guards of the
up-block lemma `Work.OROneRel.bandUpBlock` and the no-pinch conditions of the HNN word
`h 0 * τ^{ε 1} * h 1 * ⋯ * h (n-1)` is:

* `y ∈ tlAk k  ⟺  τ^(-k)·y·τ^k ∈ B` (`mem_tlAk_iff_conj_mem_hnnEdgeB`);
* at a **peak**, `y i ∉ tlAk (t i - 1)  ⟺  h i ∉ A` (`not_mem_hnnEdgeA_of_not_mem_tlAk_sub_one`);
* at a **valley**, `y i ∉ tlAk (t i)  ⟺  h i ∉ B` (`not_mem_hnnEdgeB_of_not_mem_tlAk`),
  where `h i = τ^(-t i)·y i·τ^(t i)`.

This file collects those lemmas (plus the membership dictionary `mem_tlHk_iff_bandUpBlock` for the
translated band vertices) so that both `Submission/Work/OROneRel/bandUpBlock.lean` and the files
assembled *on top of* `bandUpBlock` (in particular
`Submission/Work/OROneRel/bandUpBlockHk_of_hnnConjMap_injective.lean`) can import them without the
latter having to import `bandUpBlock` itself.

`mem_tlHk_iff_bandUpBlock` is a local copy of `Work.OROneRel.mem_tlHk_iff` (whose home module
`band_hnnConjMap_injective` brings in `bandLoopsDefs`, whose `mk_lpow` clashes with the one of
`tlHalves_inter`).
-/

namespace Work.OROneRel

universe u

/-- **The membership dictionary for the translated band vertices** (a local copy of
`Work.OROneRel.mem_tlHk_iff`: the module `band_hnnConjMap_injective` that holds it clashes with
`tlHalves_inter` in this workspace). -/
theorem mem_tlHk_iff_bandUpBlock (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (k : ℤ) (x : FreeGroup (Fin 2)) :
    x ∈ tlHk p q hp hq hcop Wt k ↔
      (tlLowTau p q hp hq hcop) ^ (-k) * x * (tlLowTau p q hp hq hcop) ^ k ∈ tlH p q Wt := by
  rw [tlHk, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hxy : x = (tlLowTau p q hp hq hcop) ^ k * y * ((tlLowTau p q hp hq hcop) ^ k)⁻¹ := by
      rw [← hyx]
      show MulAut.conj ((tlLowTau p q hp hq hcop) ^ k) y = _
      rw [MulAut.conj_apply]
    rw [hxy]
    have hcancel : (tlLowTau p q hp hq hcop) ^ (-k) *
        ((tlLowTau p q hp hq hcop) ^ k * y * ((tlLowTau p q hp hq hcop) ^ k)⁻¹) *
        (tlLowTau p q hp hq hcop) ^ k = y := by group
    rw [hcancel]
    exact hy
  · intro hx
    refine ⟨(tlLowTau p q hp hq hcop) ^ (-k) * x * (tlLowTau p q hp hq hcop) ^ k, hx, ?_⟩
    show (MulAut.conj ((tlLowTau p q hp hq hcop) ^ k))
        ((tlLowTau p q hp hq hcop) ^ (-k) * x * (tlLowTau p q hp hq hcop) ^ k) = x
    rw [MulAut.conj_apply]
    group

/-- **The upper gate `B` in elements**: `g ∈ B = τAτ⁻¹ = tlH ⊓ τtlHτ⁻¹` iff `g ∈ tlH` and
`τ⁻¹ g τ ∈ tlH`. -/
theorem mem_hnnEdgeB_iff_bandUpBlock (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) (Wt : ℤ → FreeGroup (Fin 2)) (g : FreeGroup (Fin 2)) :
    g ∈ hnnEdgeB (tlH p q Wt) (tlLowTau p q hp hq hcop) ↔
      g ∈ tlH p q Wt ∧
        (tlLowTau p q hp hq hcop)⁻¹ * g * (tlLowTau p q hp hq hcop) ∈ tlH p q Wt := by
  rw [hnnEdgeB, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, hag⟩
    rw [hnnEdgeA, Subgroup.mem_inf] at ha
    obtain ⟨h, hh, hha⟩ := Subgroup.mem_map.mp ha.2
    have hha' : MulAut.conj (tlLowTau p q hp hq hcop)⁻¹ h = a := hha
    have hag' : MulAut.conj (tlLowTau p q hp hq hcop) a = g := hag
    rw [MulAut.conj_apply] at hha'
    refine ⟨?_, ?_⟩
    · rw [← hag']
      have h2 : MulAut.conj (tlLowTau p q hp hq hcop) a = h := by
        rw [MulAut.conj_apply, ← hha']
        group
      rw [h2]
      exact hh
    · rw [← hag']
      have h3 : (tlLowTau p q hp hq hcop)⁻¹ *
          MulAut.conj (tlLowTau p q hp hq hcop) a * (tlLowTau p q hp hq hcop) = a := by
        rw [MulAut.conj_apply]
        group
      rw [h3]
      exact ha.1
  · rintro ⟨hg, hτ⟩
    refine ⟨(tlLowTau p q hp hq hcop)⁻¹ * g * (tlLowTau p q hp hq hcop), ?_, ?_⟩
    · rw [hnnEdgeA, Subgroup.mem_inf]
      refine ⟨hτ, ?_⟩
      refine Subgroup.mem_map.mpr ⟨g, hg, ?_⟩
      show MulAut.conj (tlLowTau p q hp hq hcop)⁻¹ g =
        (tlLowTau p q hp hq hcop)⁻¹ * g * (tlLowTau p q hp hq hcop)
      rw [MulAut.conj_apply]
      group
    · show MulAut.conj (tlLowTau p q hp hq hcop)
        ((tlLowTau p q hp hq hcop)⁻¹ * g * (tlLowTau p q hp hq hcop)) = g
      rw [MulAut.conj_apply]
      group

/-- **The gate dictionary**: `y ∈ tlAk k` iff the `τ^(-k)`-conjugate of `y` lies in the *upper*
gate `B` of the pair `(tlH, τ)`. -/
theorem mem_tlAk_iff_conj_mem_hnnEdgeB (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) (Wt : ℤ → FreeGroup (Fin 2)) (k : ℤ) (y : FreeGroup (Fin 2)) :
    y ∈ tlAk p q hp hq hcop Wt k ↔
      (tlLowTau p q hp hq hcop) ^ (-k) * y * (tlLowTau p q hp hq hcop) ^ k ∈
        hnnEdgeB (tlH p q Wt) (tlLowTau p q hp hq hcop) := by
  rw [tlAk, Subgroup.mem_inf, mem_tlHk_iff_bandUpBlock, mem_tlHk_iff_bandUpBlock,
    mem_hnnEdgeB_iff_bandUpBlock]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have h : (tlLowTau p q hp hq hcop)⁻¹ *
        ((tlLowTau p q hp hq hcop) ^ (-k) * y * (tlLowTau p q hp hq hcop) ^ k) *
        (tlLowTau p q hp hq hcop) =
        (tlLowTau p q hp hq hcop) ^ (-(k + 1)) * y *
          (tlLowTau p q hp hq hcop) ^ (k + 1) := by group
    rw [h]
    exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have h : (tlLowTau p q hp hq hcop) ^ (-(k + 1)) * y *
        (tlLowTau p q hp hq hcop) ^ (k + 1) =
        (tlLowTau p q hp hq hcop)⁻¹ *
          ((tlLowTau p q hp hq hcop) ^ (-k) * y * (tlLowTau p q hp hq hcop) ^ k) *
          (tlLowTau p q hp hq hcop) := by group
    rw [h]
    exact h2

/-- **The peak guard is the no-pinch condition against the lower gate `A`**: if
`h = τ^(-t) y τ^t ∈ tlH` and `y ∉ tlAk (t - 1)` then `h ∉ A = hnnEdgeA tlH τ`. -/
theorem not_mem_hnnEdgeA_of_not_mem_tlAk_sub_one (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) (Wt : ℤ → FreeGroup (Fin 2)) {t : ℤ} {y h : FreeGroup (Fin 2)}
    (hh : h = (tlLowTau p q hp hq hcop) ^ (-t) * y * (tlLowTau p q hp hq hcop) ^ t)
    (hguard : y ∉ tlAk p q hp hq hcop Wt (t - 1)) :
    h ∉ hnnEdgeA (tlH p q Wt) (tlLowTau p q hp hq hcop) := by
  intro hmem
  apply hguard
  rw [mem_tlAk_iff_conj_mem_hnnEdgeB]
  have hconj : (tlLowTau p q hp hq hcop) ^ (-(t - 1)) * y *
      (tlLowTau p q hp hq hcop) ^ (t - 1) =
      (tlLowTau p q hp hq hcop) * h * (tlLowTau p q hp hq hcop)⁻¹ := by
    rw [hh]
    group
  rw [hconj]
  refine Subgroup.mem_map.mpr ⟨h, hmem, ?_⟩
  show MulAut.conj (tlLowTau p q hp hq hcop) h =
    (tlLowTau p q hp hq hcop) * h * (tlLowTau p q hp hq hcop)⁻¹
  rw [MulAut.conj_apply]

/-- **The valley guard is the no-pinch condition against the upper gate `B`**: if
`h = τ^(-t) y τ^t ∈ tlH` and `y ∉ tlAk t` then `h ∉ B = hnnEdgeB tlH τ`. -/
theorem not_mem_hnnEdgeB_of_not_mem_tlAk (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) (Wt : ℤ → FreeGroup (Fin 2)) {t : ℤ} {y h : FreeGroup (Fin 2)}
    (hh : h = (tlLowTau p q hp hq hcop) ^ (-t) * y * (tlLowTau p q hp hq hcop) ^ t)
    (hguard : y ∉ tlAk p q hp hq hcop Wt t) :
    h ∉ hnnEdgeB (tlH p q Wt) (tlLowTau p q hp hq hcop) := by
  intro hmem
  apply hguard
  rw [mem_tlAk_iff_conj_mem_hnnEdgeB]
  have : (tlLowTau p q hp hq hcop) ^ (-t) * y * (tlLowTau p q hp hq hcop) ^ t = h := hh.symm
  rw [this]
  exact hmem

end Work.OROneRel
