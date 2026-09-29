import Mathlib
import Submission.Work.TMC16Core.Core.uni_nonres3_support
import Submission.Work.TMC16Core.Core.uni_nonres3_blkG
import Submission.Work.TMC16Core.Core.uni_nonres3_blkGmem
import Submission.Work.TMC16Core.Core.sum_Dnr_blocks
import Submission.Work.TMC16Core.NrFinal.sepB_bound
import Submission.Work.Basic.UniNonres.Defs

/-!
# `nruDenom`: a self-contained copy of the denominator estimate `NrFinal.denom`

This file is a verbatim copy of `Submission/Work/TMC16Core/NrFinal/denom.lean` (the complete,
complete proof of the AJ §9 denominator bound written by the `NrFinal` team), with the
statement renamed `nru_denom`, so that `nr_uniform` can depend on a module that is not being
edited concurrently.
-/
namespace Work.TMC16Core.NrFinal

open Work.TMC16Core
open Work.TMC16Core.Core

noncomputable section

/-! ## Local helper machinery for `denom`

The block with base point `p` and length `L`, the choice of an argmin of `|sin (π (ξ + i α))|`
over a block, and its basic properties, together with the two-interval block decomposition used
to bound the two sums of `denom`. -/

/-- The summand `-log |sin (π (ξ + i α))|`. -/
private noncomputable def dsum (α ξ : ℝ) (i : ℤ) : ℝ :=
  -Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|

/-- The integer block `[A, A+L-1]`. -/
private def dblk (A L : ℤ) : Finset ℤ := Finset.Icc A (A + L - 1)

private lemma dblk_nonempty {A L : ℤ} (hL : 1 ≤ L) : (dblk A L).Nonempty := by
  refine ⟨A, ?_⟩
  rw [dblk, Finset.mem_Icc]
  constructor <;> omega

/-- A point of the block `dblk p L` minimising `|sin (π (ξ + i α))|`. -/
private noncomputable def dargmin (α ξ : ℝ) (p L : ℤ) : ℤ :=
  if h : (dblk p L).Nonempty then
    Classical.choose (Finset.exists_min_image (dblk p L)
      (fun k : ℤ => |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|) h)
  else 0

private lemma dargmin_mem {α ξ : ℝ} {p L : ℤ} (hL : 1 ≤ L) :
    dargmin α ξ p L ∈ dblk p L := by
  have h := dblk_nonempty (A := p) (L := L) hL
  rw [dargmin, dif_pos h]
  exact (Classical.choose_spec (Finset.exists_min_image (dblk p L)
    (fun k : ℤ => |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|) h)).1

private lemma dargmin_min {α ξ : ℝ} {p L : ℤ} (hL : 1 ≤ L) {k : ℤ} (hk : k ∈ dblk p L) :
    |Real.sin (Real.pi * (ξ + (dargmin α ξ p L : ℝ) * α))|
      ≤ |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| := by
  have h := dblk_nonempty (A := p) (L := L) hL
  rw [dargmin, dif_pos h]
  exact (Classical.choose_spec (Finset.exists_min_image (dblk p L)
    (fun k : ℤ => |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|) h)).2 k hk

/-- Two blocks with different bases among the blocks `dblk (A + tL) L` are disjoint, hence the
chosen argmins over a range of `t` are distinct. -/
private lemma dargmin_injOn {A L : ℤ} (hL : 1 ≤ L) (α ξ : ℝ) (N : ℕ) :
    Set.InjOn (fun t : ℕ => dargmin α ξ (A + (t : ℤ) * L) L) ↑(Finset.range N) := by
  intro t ht t' ht' heq
  simp only [Finset.mem_coe, Finset.mem_range] at ht ht'
  have heq' : dargmin α ξ (A + (t : ℤ) * L) L = dargmin α ξ (A + (t' : ℤ) * L) L := heq
  have h1 := dargmin_mem (α := α) (ξ := ξ) (p := A + (t : ℤ) * L) (L := L) hL
  have h2 := dargmin_mem (α := α) (ξ := ξ) (p := A + (t' : ℤ) * L) (L := L) hL
  rw [dblk, Finset.mem_Icc] at h1 h2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hle : dargmin α ξ (A + (t' : ℤ) * L) L ≤ A + (t : ℤ) * L + L - 1 := heq' ▸ h1.2
    have hge : A + (t' : ℤ) * L ≤ dargmin α ξ (A + (t' : ℤ) * L) L := h2.1
    have hstep : A + ((t : ℤ) + 1) * L ≤ A + (t' : ℤ) * L := by
      have hcast : (t : ℤ) + 1 ≤ (t' : ℤ) := by
        have : t + 1 ≤ t' := by omega
        exact_mod_cast this
      nlinarith
    have h4 : A + ((t : ℤ) + 1) * L = A + (t : ℤ) * L + L := by ring
    omega
  · have hle : dargmin α ξ (A + (t : ℤ) * L) L ≤ A + (t' : ℤ) * L + L - 1 := heq' ▸ h2.2
    have hge : A + (t : ℤ) * L ≤ dargmin α ξ (A + (t : ℤ) * L) L := h1.1
    have hstep : A + ((t' : ℤ) + 1) * L ≤ A + (t : ℤ) * L := by
      have hcast : (t' : ℤ) + 1 ≤ (t : ℤ) := by
        have : t' + 1 ≤ t := by omega
        exact_mod_cast this
      nlinarith
    have h4 : A + ((t' : ℤ) + 1) * L = A + (t' : ℤ) * L + L := by ring
    omega

/-- **Block bound, full block.**  `uni_nonres3_blkG` with the block's chosen argmin. -/
private lemma dblkG_le {L : ℕ} (hL : 1 ≤ L) {α ξ : ℝ} {p : ℤ}
    (hblk : ∀ (p : ℤ) (k₀ : ℤ), k₀ ∈ Finset.Icc p (p + (L : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((L : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (L : ℝ)) :
    ∑ i ∈ dblk p (L : ℤ), dsum α ξ i
      ≤ ((L : ℝ) - 1) * Real.log 2 + 32 * Real.log (L : ℝ)
        + dsum α ξ (dargmin α ξ p (L : ℤ)) := by
  have hLZ : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
  have h := uni_nonres3_blkG (L := L) (ξ := ξ) (p := p) (k₀ := dargmin α ξ p (L : ℤ)) hL
    (fun p k₀ hk₀ hmin => hblk p k₀ hk₀ hmin) (dargmin_mem (α := α) (ξ := ξ) hLZ)
    (fun k hk => dargmin_min (α := α) (ξ := ξ) hLZ hk)
  simpa only [dblk, dsum, add_comm, sub_eq_add_neg, neg_neg]
    using h

/-- **Block bound, erased block (with an `L∞` lower bound).**  `uni_nonres3_blkGmem`. -/
private lemma dblkGmem_le {L : ℕ} (hL : 1 ≤ L) {α ξ c : ℝ} {p d : ℤ}
    (hblk : ∀ (p : ℤ) (k₀ : ℤ), k₀ ∈ Finset.Icc p (p + (L : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((L : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (L : ℝ))
    (hd : d ∈ dblk p (L : ℤ)) (hc : 0 < c) (hc1 : c ≤ 1 / 2)
    (hlo : ∀ k ∈ dblk p (L : ℤ), 2 * c ≤ |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|) :
    ∑ k ∈ (dblk p (L : ℤ)).erase d, dsum α ξ k
      ≤ ((L : ℝ) - 1) * Real.log 2 + 32 * Real.log (L : ℝ) - Real.log (2 * c) := by
  have h := uni_nonres3_blkGmem (L := L) (ξ := ξ) (p := p) (d := d) hL
    (fun p k₀ hk₀ hmin => hblk p k₀ hk₀ hmin) hd hc hc1 (fun k hk => hlo k hk)
  simpa only [dblk, dsum] using h

/-- **Two-interval block bound with one erased point.**

`[A₁, A₁+N₁L-1]` is split into the `N₁` blocks of length `L`; the point `x` lies in the block
`t₀` of that family and in no other block of that family.  The block `t₀` contributes the given
bound with additive constant `C`, every other block contributes its `blkG` bound with its own
argmin.  The second interval `[A₂, A₂+N₂L-1]` (disjoint from the first, and not containing `x`)
is treated in the same way with all blocks "full".  The result is the sum over the union with `x`
erased, bounded by `(N₁+N₂)·base + C` plus the sum over the chosen argmin points of the two
families outside the special block. -/
private lemma dpair_le {L : ℕ} (hL : 1 ≤ L) {N₁ N₂ : ℕ} {t₀ : ℕ} {A₁ A₂ x : ℤ} {α ξ C : ℝ}
    (hblk : ∀ (p : ℤ) (k₀ : ℤ), k₀ ∈ Finset.Icc p (p + (L : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((L : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (L : ℝ))
    (ht₀ : t₀ ∈ Finset.range N₁)
    (hxmem : x ∈ dblk (A₁ + (t₀ : ℤ) * (L : ℤ)) (L : ℤ))
    (hout : ∀ t ∈ Finset.range N₁, t ≠ t₀ → x ∉ dblk (A₁ + (t : ℤ) * (L : ℤ)) (L : ℤ))
    (hxnot : x ∉ Finset.Icc A₂ (A₂ + (N₂ : ℤ) * (L : ℤ) - 1))
    (hdisj : Disjoint (Finset.Icc A₁ (A₁ + (N₁ : ℤ) * (L : ℤ) - 1))
      (Finset.Icc A₂ (A₂ + (N₂ : ℤ) * (L : ℤ) - 1)))
    (htblock : ∑ i ∈ (dblk (A₁ + (t₀ : ℤ) * (L : ℤ)) (L : ℤ)).erase x, dsum α ξ i
        ≤ ((L : ℝ) - 1) * Real.log 2 + 32 * Real.log (L : ℝ) + C) :
    ∑ i ∈ ((Finset.Icc A₁ (A₁ + (N₁ : ℤ) * (L : ℤ) - 1)) ∪
        (Finset.Icc A₂ (A₂ + (N₂ : ℤ) * (L : ℤ) - 1))).erase x, dsum α ξ i
      ≤ ((N₁ : ℝ) + N₂) * (((L : ℝ) - 1) * Real.log 2 + 32 * Real.log (L : ℝ)) + C
        + ∑ p ∈ (((Finset.range N₁).erase t₀).image
              (fun t : ℕ => dargmin α ξ (A₁ + (t : ℤ) * (L : ℤ)) (L : ℤ)))
            ∪ ((Finset.range N₂).image
              (fun t : ℕ => dargmin α ξ (A₂ + (t : ℤ) * (L : ℤ)) (L : ℤ))),
            dsum α ξ p := by
  classical
  have hm : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
  have hLZ : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
  have hN₁ : 1 ≤ N₁ := by have := Finset.mem_range.mp ht₀; omega
  set base : ℝ := ((L : ℝ) - 1) * Real.log 2 + 32 * Real.log (L : ℝ) with hbase
  set g₁ : ℕ → ℤ := fun t : ℕ => dargmin α ξ (A₁ + (t : ℤ) * (L : ℤ)) (L : ℤ) with hg₁
  set g₂ : ℕ → ℤ := fun t : ℕ => dargmin α ξ (A₂ + (t : ℤ) * (L : ℤ)) (L : ℤ) with hg₂
  have hkey₁ : (∑ i ∈ (Finset.Icc A₁ (A₁ + (N₁ : ℤ) * (L : ℤ) - 1)).erase x, dsum α ξ i)
      = ∑ t ∈ Finset.range N₁,
          ∑ i ∈ (dblk (A₁ + (t : ℤ) * (L : ℤ)) (L : ℤ)).erase x, dsum α ξ i := by
    have h := sum_blocks A₁ (L : ℤ) hm N₁ x (dsum α ξ)
    simpa only [dblk] using h
  have hkey₂ : (∑ i ∈ (Finset.Icc A₂ (A₂ + (N₂ : ℤ) * (L : ℤ) - 1)).erase x, dsum α ξ i)
      = ∑ t ∈ Finset.range N₂,
          ∑ i ∈ (dblk (A₂ + (t : ℤ) * (L : ℤ)) (L : ℤ)).erase x, dsum α ξ i := by
    have h := sum_blocks A₂ (L : ℤ) hm N₂ x (dsum α ξ)
    simpa only [dblk] using h
  have hblock₀ : (∑ i ∈ (dblk (A₁ + (t₀ : ℤ) * (L : ℤ)) (L : ℤ)).erase x, dsum α ξ i)
      ≤ base + C := by rw [hbase]; exact htblock
  have hblocks₁ : ∀ t ∈ (Finset.range N₁).erase t₀,
      (∑ i ∈ (dblk (A₁ + (t : ℤ) * (L : ℤ)) (L : ℤ)).erase x, dsum α ξ i)
        ≤ base + dsum α ξ (g₁ t) := by
    intro t ht
    rw [Finset.mem_erase, Finset.mem_range] at ht
    obtain ⟨htne, htlt⟩ := ht
    have hxnotblk : x ∉ dblk (A₁ + (t : ℤ) * (L : ℤ)) (L : ℤ) :=
      hout t (Finset.mem_range.mpr htlt) htne
    rw [Finset.erase_eq_of_notMem hxnotblk]
    have h := dblkG_le (L := L) hL (α := α) (ξ := ξ) (p := A₁ + (t : ℤ) * (L : ℤ)) hblk
    rw [hbase, hg₁]
    exact h
  have hblocks₂ : ∀ t ∈ Finset.range N₂,
      (∑ i ∈ (dblk (A₂ + (t : ℤ) * (L : ℤ)) (L : ℤ)).erase x, dsum α ξ i)
        ≤ base + dsum α ξ (g₂ t) := by
    intro t ht
    have hxnotblk : x ∉ dblk (A₂ + (t : ℤ) * (L : ℤ)) (L : ℤ) := by
      intro hcon
      rw [dblk, Finset.mem_Icc] at hcon
      apply hxnot
      rw [Finset.mem_Icc]
      obtain ⟨hc1, hc2⟩ := hcon
      have hcast : (t : ℤ) + 1 ≤ (N₂ : ℤ) := by
        have : t + 1 ≤ N₂ := by
          have := Finset.mem_range.mp ht
          omega
        exact_mod_cast this
      constructor <;> nlinarith [hc1, hc2, hcast]
    rw [Finset.erase_eq_of_notMem hxnotblk]
    have h := dblkG_le (L := L) hL (α := α) (ξ := ξ) (p := A₂ + (t : ℤ) * (L : ℤ)) hblk
    rw [hbase, hg₂]
    exact h
  have hinj₁ : Set.InjOn g₁ ↑((Finset.range N₁).erase t₀) := by
    rw [hg₁]
    exact fun a ha b hb hab => dargmin_injOn (A := A₁) (L := L) hLZ α ξ N₁
      (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab
  have hinj₂ : Set.InjOn g₂ ↑(Finset.range N₂) := by
    rw [hg₂]; exact dargmin_injOn (A := A₂) (L := L) hLZ α ξ N₂
  have himg₁ := Finset.sum_image (f := dsum α ξ) hinj₁
  have himg₂ := Finset.sum_image (f := dsum α ξ) hinj₂
  have hcard₁ : ((Finset.range N₁).erase t₀).card = N₁ - 1 := by
    rw [Finset.card_erase_of_mem ht₀, Finset.card_range]
  have hcard₂ : (Finset.range N₂).card = N₂ := Finset.card_range N₂
  have hsplit₁ := Finset.add_sum_erase (Finset.range N₁)
    (fun t => ∑ i ∈ (dblk (A₁ + (t : ℤ) * (L : ℤ)) (L : ℤ)).erase x, dsum α ξ i) ht₀
  have h₁ : (∑ t ∈ Finset.range N₁,
      ∑ i ∈ (dblk (A₁ + (t : ℤ) * (L : ℤ)) (L : ℤ)).erase x, dsum α ξ i)
      ≤ base + C + (((N₁ - 1 : ℕ) : ℝ) * base
          + ∑ t ∈ (Finset.range N₁).erase t₀, dsum α ξ (g₁ t)) := by
    rw [← hsplit₁]
    have h2 := Finset.sum_le_sum hblocks₁
    have h3 : (∑ t ∈ (Finset.range N₁).erase t₀, (base + dsum α ξ (g₁ t)))
        = (((N₁ - 1 : ℕ) : ℝ) * base
          + ∑ t ∈ (Finset.range N₁).erase t₀, dsum α ξ (g₁ t)) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, hcard₁, nsmul_eq_mul]
    linarith [hblock₀, h2, h3]
  have h₂ : (∑ t ∈ Finset.range N₂,
      ∑ i ∈ (dblk (A₂ + (t : ℤ) * (L : ℤ)) (L : ℤ)).erase x, dsum α ξ i)
      ≤ (N₂ : ℝ) * base + ∑ t ∈ Finset.range N₂, dsum α ξ (g₂ t) := by
    have h2 := Finset.sum_le_sum hblocks₂
    have h3 : (∑ t ∈ Finset.range N₂, (base + dsum α ξ (g₂ t)))
        = (N₂ : ℝ) * base + ∑ t ∈ Finset.range N₂, dsum α ξ (g₂ t) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, hcard₂, nsmul_eq_mul]
    linarith [h2, h3]
  have hI₁ : (∑ i ∈ (Finset.Icc A₁ (A₁ + (N₁ : ℤ) * (L : ℤ) - 1)).erase x, dsum α ξ i)
      ≤ base + C + (((N₁ - 1 : ℕ) : ℝ) * base
          + ∑ p ∈ ((Finset.range N₁).erase t₀).image g₁, dsum α ξ p) := by
    rw [hkey₁, himg₁]
    exact h₁
  have hI₂ : (∑ i ∈ (Finset.Icc A₂ (A₂ + (N₂ : ℤ) * (L : ℤ) - 1)).erase x, dsum α ξ i)
      ≤ (N₂ : ℝ) * base + ∑ p ∈ (Finset.range N₂).image g₂, dsum α ξ p := by
    rw [hkey₂, himg₂]
    exact h₂
  have hsub₁ : ∀ p ∈ ((Finset.range N₁).erase t₀).image g₁,
      p ∈ Finset.Icc A₁ (A₁ + (N₁ : ℤ) * (L : ℤ) - 1) := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    have htlt : t < N₁ := Finset.mem_range.mp (Finset.mem_of_mem_erase ht)
    have hmem : g₁ t ∈ dblk (A₁ + (t : ℤ) * (L : ℤ)) (L : ℤ) := by
      rw [hg₁]
      exact dargmin_mem (α := α) (ξ := ξ) (p := A₁ + (t : ℤ) * (L : ℤ)) (L := L) hLZ
    rw [dblk, Finset.mem_Icc] at hmem
    rw [Finset.mem_Icc]
    constructor
    · nlinarith [hmem.1]
    · have hcast : (t : ℤ) + 1 ≤ (N₁ : ℤ) := by
        have : t + 1 ≤ N₁ := by omega
        exact_mod_cast this
      nlinarith [hmem.2, hcast]
  have hsub₂ : ∀ p ∈ (Finset.range N₂).image g₂,
      p ∈ Finset.Icc A₂ (A₂ + (N₂ : ℤ) * (L : ℤ) - 1) := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    have htlt : t < N₂ := Finset.mem_range.mp ht
    have hmem : g₂ t ∈ dblk (A₂ + (t : ℤ) * (L : ℤ)) (L : ℤ) := by
      rw [hg₂]
      exact dargmin_mem (α := α) (ξ := ξ) (p := A₂ + (t : ℤ) * (L : ℤ)) (L := L) hLZ
    rw [dblk, Finset.mem_Icc] at hmem
    rw [Finset.mem_Icc]
    constructor
    · nlinarith [hmem.1]
    · have hcast : (t : ℤ) + 1 ≤ (N₂ : ℤ) := by
        have : t + 1 ≤ N₂ := by omega
        exact_mod_cast this
      nlinarith [hmem.2, hcast]
  have hdisj' : Disjoint (((Finset.range N₁).erase t₀).image g₁)
      ((Finset.range N₂).image g₂) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    exact (Finset.disjoint_left.mp hdisj) (hsub₁ p hp) (hsub₂ p hq)
  have hdisjE : Disjoint ((Finset.Icc A₁ (A₁ + (N₁ : ℤ) * (L : ℤ) - 1)).erase x)
      ((Finset.Icc A₂ (A₂ + (N₂ : ℤ) * (L : ℤ) - 1)).erase x) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    exact (Finset.disjoint_left.mp hdisj) (Finset.mem_of_mem_erase hp)
      (Finset.mem_of_mem_erase hq)
  rw [erase_union (A := Finset.Icc A₁ (A₁ + (N₁ : ℤ) * (L : ℤ) - 1))
      (B := Finset.Icc A₂ (A₂ + (N₂ : ℤ) * (L : ℤ) - 1)) (d := x), Finset.sum_union hdisjE]
  have hunion : (∑ p ∈ ((Finset.range N₁).erase t₀).image g₁ ∪ (Finset.range N₂).image g₂,
        dsum α ξ p)
      = (∑ p ∈ ((Finset.range N₁).erase t₀).image g₁, dsum α ξ p)
        + ∑ p ∈ (Finset.range N₂).image g₂, dsum α ξ p := Finset.sum_union hdisj'
  have hcastN₁ : (((N₁ - 1 : ℕ) : ℝ)) + 1 = (N₁ : ℝ) := by
    have h1 : (1 : ℕ) ≤ N₁ := hN₁
    push_cast [Nat.cast_sub h1]
    ring
  have hprod : ((N₁ - 1 : ℕ) : ℝ) * base + base = (N₁ : ℝ) * base := by
    rw [← hcastN₁]; ring
  linarith [hI₁, hI₂, hunion, hprod]

/-- The blocks `dblk (A + tL) L`, `t < N`, tile the interval `[A, A+NL-1]`. -/
private lemma dblk_union {A L : ℤ} (hL : 1 ≤ L) (N : ℕ) :
    Finset.Icc A (A + (N : ℤ) * L - 1)
      = (Finset.range N).biUnion (fun t : ℕ => dblk (A + (t : ℤ) * L) L) := by
  induction N with
  | zero =>
    have h0 : A + ((0 : ℕ) : ℤ) * L - 1 = A - 1 := by ring
    rw [h0, Finset.Icc_eq_empty_of_lt (by omega), Finset.range_zero, Finset.biUnion_empty]
  | succ N ih =>
    rw [Finset.range_add_one, Finset.biUnion_insert, ← ih]
    have h1 : A ≤ (A + (N : ℤ) * L - 1) + 1 := by
      have : (0 : ℤ) ≤ (N : ℤ) * L := by
        have : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg _
        nlinarith
      omega
    have h2 : (A + (N : ℤ) * L - 1) + 1 ≤ A + ((N : ℤ) + 1) * L - 1 := by
      nlinarith
    have h3 := Icc_union_Icc_succ (a := A) (b := A + (N : ℤ) * L - 1)
      (c := A + ((N : ℤ) + 1) * L - 1) h1 h2
    rw [show (A + (N : ℤ) * L - 1) + 1 = A + (N : ℤ) * L by ring] at h3
    have h4 : A + (((N + 1 : ℕ)) : ℤ) * L - 1 = A + ((N : ℤ) + 1) * L - 1 := by
      push_cast; ring
    have h5 : dblk (A + (N : ℤ) * L) L
        = Finset.Icc (A + (N : ℤ) * L) (A + ((N : ℤ) + 1) * L - 1) := by
      rw [dblk]; congr 1; ring
    rw [h4, h5, ← h3]
    exact Finset.union_comm _ _

private lemma dblk_exists {A L : ℤ} (hL : 1 ≤ L) {N : ℕ} (hN : 0 < N) {x : ℤ}
    (h1 : A ≤ x) (h2 : x ≤ A + (N : ℤ) * L - 1) :
    ∃ t : ℕ, t < N ∧ x ∈ dblk (A + (t : ℤ) * L) L := by
  have hxu : x ∈ Finset.Icc A (A + (N : ℤ) * L - 1) := Finset.mem_Icc.mpr ⟨h1, h2⟩
  rw [dblk_union hL N, Finset.mem_biUnion] at hxu
  obtain ⟨t, ht, hxt⟩ := hxu
  exact ⟨t, Finset.mem_range.mp ht, hxt⟩

/-- The blocks of a fixed family are pairwise disjoint, so the block index of a point is unique. -/
private lemma dblk_unique {A L : ℤ} (hL : 1 ≤ L) {x : ℤ} {t t' : ℕ}
    (hx : x ∈ dblk (A + (t : ℤ) * L) L) (hx' : x ∈ dblk (A + (t' : ℤ) * L) L) : t = t' := by
  by_contra hne
  rw [dblk, Finset.mem_Icc] at hx hx'
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hx3, hx4⟩ := hx'
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hstep : A + ((t : ℤ) + 1) * L ≤ A + (t' : ℤ) * L := by
      have hcast : (t : ℤ) + 1 ≤ (t' : ℤ) := by
        have : t + 1 ≤ t' := by omega
        exact_mod_cast this
      nlinarith
    have h4 : A + ((t : ℤ) + 1) * L = A + (t : ℤ) * L + L := by ring
    omega
  · have hstep : A + ((t' : ℤ) + 1) * L ≤ A + (t : ℤ) * L := by
      have hcast : (t' : ℤ) + 1 ≤ (t : ℤ) := by
        have : t' + 1 ≤ t := by omega
        exact_mod_cast this
      nlinarith
    have h4 : A + ((t' : ℤ) + 1) * L = A + (t' : ℤ) * L + L := by ring
    omega

private lemma dunique {A L : ℤ} (hL : 1 ≤ L) {N : ℕ} (hN : 0 < N) {x : ℤ}
    (h1 : A ≤ x) (h2 : x ≤ A + (N : ℤ) * L - 1) :
    ∃! t : ℕ, t < N ∧ A + (t : ℤ) * L ≤ x ∧ x ≤ A + (t : ℤ) * L + L - 1 := by
  obtain ⟨t₀, ht₀, hx₀⟩ := dblk_exists hL hN h1 h2
  have hx₀' := Finset.mem_Icc.mp hx₀
  refine ⟨t₀, ⟨ht₀, hx₀'.1, hx₀'.2⟩, ?_⟩
  intro t ht
  exact dblk_unique hL (Finset.mem_Icc.mpr ⟨ht.2.1, ht.2.2⟩) hx₀

/-- **The separation/Stirling bound, `Finset ℤ` form.**  Wrapper around
`Work.TMC16Core.NrFinal.sepB_bound`. -/
private lemma dsepB {α ξ c δ : ℝ} {S : Finset ℤ}
    (hc : 0 < c) (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (hlow : ∀ i ∈ S, c ≤ Work.TMC16Core.fracDist (ξ + (i : ℝ) * α))
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      δ ≤ Work.TMC16Core.fracDist (((i - j : ℤ) : ℝ) * α)) :
    ∑ i ∈ S, dsum α ξ i ≤ Work.Basic.UniNonres.sepB c δ S.card := by
  classical
  have h := sepB_bound (ι := ↥S) (k := fun i : ↥S => (i : ℤ)) (α := α) (ξ := ξ)
    (c := c) (δ := δ) hc hδ hδh
    (fun i => hlow i i.2)
    (fun i j hij => hsep i i.2 j j.2 (fun hc' => hij (Subtype.ext hc')))
  have hcard : Fintype.card ↥S = S.card := Fintype.card_coe S
  have hsum : (∑ i : ↥S, -Real.log |Real.sin (Real.pi * (ξ + ((i : ℤ) : ℝ) * α))|)
      = ∑ i ∈ S, -Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))| := by
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach S
      (fun i : ℤ => -Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|)
  rw [hcard, hsum] at h
  simpa only [dsum] using h

/-- **The bound for one of the two sums of `denom`.**

`[A₁, A₁+N₁L-1]` is the interval containing the erased point `x`, `[A₂, A₂+N₂L-1]` the other
one; the special block is handled with the constant `C` (hypothesis `hspec`), all remaining
blocks via their argmins, and the resulting set of argmin points — which is `c₀`-separated from
`0` and `δ`-separated — is controlled by the separation/Stirling bound. -/
private lemma dDnr_bound {L : ℕ} (hL : 1 ≤ L) {N₁ N₂ : ℕ} {A₁ A₂ x : ℤ} {α ξ c₀ δ C : ℝ}
    (hblk : ∀ (p : ℤ) (k₀ : ℤ), k₀ ∈ Finset.Icc p (p + (L : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((L : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (L : ℝ))
    (hN₁ : 0 < N₁)
    (hex : x ∈ Finset.Icc A₁ (A₁ + (N₁ : ℤ) * (L : ℤ) - 1))
    (hxnot : x ∉ Finset.Icc A₂ (A₂ + (N₂ : ℤ) * (L : ℤ) - 1))
    (hdisj : Disjoint (Finset.Icc A₁ (A₁ + (N₁ : ℤ) * (L : ℤ) - 1))
      (Finset.Icc A₂ (A₂ + (N₂ : ℤ) * (L : ℤ) - 1)))
    (hspec : ∀ t ∈ Finset.range N₁, x ∈ dblk (A₁ + (t : ℤ) * (L : ℤ)) (L : ℤ) →
        ∑ i ∈ (dblk (A₁ + (t : ℤ) * (L : ℤ)) (L : ℤ)).erase x, dsum α ξ i
          ≤ ((L : ℝ) - 1) * Real.log 2 + 32 * Real.log (L : ℝ) + C)
    (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (hlow : ∀ p ∈ Finset.Icc A₁ (A₁ + (N₁ : ℤ) * (L : ℤ) - 1)
        ∪ Finset.Icc A₂ (A₂ + (N₂ : ℤ) * (L : ℤ) - 1),
        p ≠ x → c₀ ≤ Work.TMC16Core.fracDist (ξ + (p : ℝ) * α))
    (hsepS : ∀ p ∈ Finset.Icc A₁ (A₁ + (N₁ : ℤ) * (L : ℤ) - 1)
        ∪ Finset.Icc A₂ (A₂ + (N₂ : ℤ) * (L : ℤ) - 1),
        ∀ p' ∈ Finset.Icc A₁ (A₁ + (N₁ : ℤ) * (L : ℤ) - 1)
        ∪ Finset.Icc A₂ (A₂ + (N₂ : ℤ) * (L : ℤ) - 1),
        p ≠ p' → δ ≤ Work.TMC16Core.fracDist (((p - p' : ℤ) : ℝ) * α)) :
    ∑ i ∈ (Finset.Icc A₁ (A₁ + (N₁ : ℤ) * (L : ℤ) - 1) ∪
        Finset.Icc A₂ (A₂ + (N₂ : ℤ) * (L : ℤ) - 1)).erase x, dsum α ξ i
      ≤ ((N₁ : ℝ) + N₂) * (((L : ℝ) - 1) * Real.log 2 + 32 * Real.log (L : ℝ)) + C
        + Work.Basic.UniNonres.sepB c₀ δ (N₁ + N₂ - 1) := by
  classical
  have hLZ : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
  set base : ℝ := ((L : ℝ) - 1) * Real.log 2 + 32 * Real.log (L : ℝ) with hbase
  set I₁ : Finset ℤ := Finset.Icc A₁ (A₁ + (N₁ : ℤ) * (L : ℤ) - 1) with hI₁
  set I₂ : Finset ℤ := Finset.Icc A₂ (A₂ + (N₂ : ℤ) * (L : ℤ) - 1) with hI₂
  -- the block of `x`
  obtain ⟨t₀, ht₀', huniq⟩ := dunique (A := A₁) (L := (L : ℤ)) hLZ hN₁
    (Finset.mem_Icc.mp hex).1 (Finset.mem_Icc.mp hex).2
  have ht₀ : t₀ ∈ Finset.range N₁ := Finset.mem_range.mpr ht₀'.1
  have hxmem : x ∈ dblk (A₁ + (t₀ : ℤ) * (L : ℤ)) (L : ℤ) :=
    Finset.mem_Icc.mpr ⟨ht₀'.2.1, ht₀'.2.2⟩
  have hout : ∀ t ∈ Finset.range N₁, t ≠ t₀ → x ∉ dblk (A₁ + (t : ℤ) * (L : ℤ)) (L : ℤ) := by
    intro t ht hne hmem
    rw [dblk, Finset.mem_Icc] at hmem
    exact hne (huniq t ⟨Finset.mem_range.mp ht, hmem.1, hmem.2⟩)
  have hdp := dpair_le (L := L) hL hblk ht₀ hxmem hout hxnot hdisj (hspec t₀ ht₀ hxmem)
  set g₁ : ℕ → ℤ := fun t : ℕ => dargmin α ξ (A₁ + (t : ℤ) * (L : ℤ)) (L : ℤ) with hg₁
  set g₂ : ℕ → ℤ := fun t : ℕ => dargmin α ξ (A₂ + (t : ℤ) * (L : ℤ)) (L : ℤ) with hg₂
  set S : Finset ℤ := ((Finset.range N₁).erase t₀).image g₁ ∪ (Finset.range N₂).image g₂ with hS
  have hdp' : (∑ i ∈ (I₁ ∪ I₂).erase x, dsum α ξ i)
      ≤ ((N₁ : ℝ) + N₂) * (((L : ℝ) - 1) * Real.log 2 + 32 * Real.log (L : ℝ)) + C
        + ∑ p ∈ S, dsum α ξ p := by
    rw [hI₁, hI₂, hS, hg₁, hg₂]
    exact hdp
  -- cardinality of the leftover set
  have hinj₁ : Set.InjOn g₁ ↑((Finset.range N₁).erase t₀) := by
    rw [hg₁]
    exact fun a ha b hb hab => dargmin_injOn (A := A₁) (L := L) hLZ α ξ N₁
      (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab
  have hinj₂ : Set.InjOn g₂ ↑(Finset.range N₂) := by
    rw [hg₂]; exact dargmin_injOn (A := A₂) (L := L) hLZ α ξ N₂
  have hcard₁ : (((Finset.range N₁).erase t₀).image g₁).card = N₁ - 1 := by
    rw [Finset.card_image_of_injOn hinj₁, Finset.card_erase_of_mem ht₀, Finset.card_range]
  have hcard₂ : ((Finset.range N₂).image g₂).card = N₂ := by
    rw [Finset.card_image_of_injOn hinj₂, Finset.card_range]
  have hsub₁ : ∀ p ∈ ((Finset.range N₁).erase t₀).image g₁, p ∈ I₁ := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    have htlt : t < N₁ := Finset.mem_range.mp (Finset.mem_of_mem_erase ht)
    have hmem : g₁ t ∈ dblk (A₁ + (t : ℤ) * (L : ℤ)) (L : ℤ) := by
      rw [hg₁]
      exact dargmin_mem (α := α) (ξ := ξ) (p := A₁ + (t : ℤ) * (L : ℤ)) (L := L) hLZ
    rw [dblk, Finset.mem_Icc] at hmem
    rw [hI₁, Finset.mem_Icc]
    have hprod : (0 : ℤ) ≤ (t : ℤ) * (L : ℤ) :=
      mul_nonneg (Int.natCast_nonneg _) (by omega)
    constructor
    · linarith [hmem.1, hprod]
    · have hcast : ((t : ℤ) + 1) ≤ (N₁ : ℤ) := by
        have : t + 1 ≤ N₁ := by omega
        exact_mod_cast this
      have h3 : ((t : ℤ) + 1) * (L : ℤ) ≤ (N₁ : ℤ) * (L : ℤ) :=
        mul_le_mul_of_nonneg_right hcast (by omega)
      have h4 : ((t : ℤ) + 1) * (L : ℤ) = (t : ℤ) * (L : ℤ) + (L : ℤ) := by ring
      omega
  have hsub₂ : ∀ p ∈ (Finset.range N₂).image g₂, p ∈ I₂ := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    have htlt : t < N₂ := Finset.mem_range.mp ht
    have hmem : g₂ t ∈ dblk (A₂ + (t : ℤ) * (L : ℤ)) (L : ℤ) := by
      rw [hg₂]
      exact dargmin_mem (α := α) (ξ := ξ) (p := A₂ + (t : ℤ) * (L : ℤ)) (L := L) hLZ
    rw [dblk, Finset.mem_Icc] at hmem
    rw [hI₂, Finset.mem_Icc]
    have hprod : (0 : ℤ) ≤ (t : ℤ) * (L : ℤ) :=
      mul_nonneg (Int.natCast_nonneg _) (by omega)
    constructor
    · linarith [hmem.1, hprod]
    · have hcast : ((t : ℤ) + 1) ≤ (N₂ : ℤ) := by
        have : t + 1 ≤ N₂ := by omega
        exact_mod_cast this
      have h3 : ((t : ℤ) + 1) * (L : ℤ) ≤ (N₂ : ℤ) * (L : ℤ) :=
        mul_le_mul_of_nonneg_right hcast (by omega)
      have h4 : ((t : ℤ) + 1) * (L : ℤ) = (t : ℤ) * (L : ℤ) + (L : ℤ) := by ring
      omega
  have hdisjS : Disjoint (((Finset.range N₁).erase t₀).image g₁) ((Finset.range N₂).image g₂) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    exact (Finset.disjoint_left.mp hdisj) (hsub₁ p hp) (hsub₂ p hq)
  have hcardS : S.card = N₁ + N₂ - 1 := by
    rw [hS, Finset.card_union_of_disjoint hdisjS, hcard₁, hcard₂]
    omega
  -- membership of the leftover points in the union and distinctness from `x`
  have hSsub : ∀ p ∈ S, p ∈ I₁ ∪ I₂ := by
    intro p hp
    rw [hS, Finset.mem_union] at hp
    rcases hp with hp | hp
    · exact Finset.mem_union_left _ (hsub₁ p hp)
    · exact Finset.mem_union_right _ (hsub₂ p hp)
  have hSne : ∀ p ∈ S, p ≠ x := by
    intro p hp hpx
    rw [hS, Finset.mem_union] at hp
    rcases hp with hp | hp
    · obtain ⟨t, ht, hgt⟩ := Finset.mem_image.mp hp
      have htlt : t < N₁ := Finset.mem_range.mp (Finset.mem_of_mem_erase ht)
      have htne : t ≠ t₀ := Finset.mem_erase.mp ht |>.1
      have hmem : g₁ t ∈ dblk (A₁ + (t : ℤ) * (L : ℤ)) (L : ℤ) := by
        rw [hg₁]
        exact dargmin_mem (α := α) (ξ := ξ) (p := A₁ + (t : ℤ) * (L : ℤ)) (L := L) hLZ
      rw [hgt] at hmem
      rw [hpx] at hmem
      exact hout t (Finset.mem_range.mpr htlt) htne hmem
    · obtain ⟨t, ht, hgt⟩ := Finset.mem_image.mp hp
      have hmem : g₂ t ∈ I₂ := hsub₂ (g₂ t) (Finset.mem_image.mpr ⟨t, ht, rfl⟩)
      rw [hgt] at hmem
      rw [hpx] at hmem
      exact hxnot hmem
  -- the sum over the leftover set
  have hsepB := dsepB (α := α) (ξ := ξ) hc₀ hδ hδh
    (fun p hp => hlow p (hSsub p hp) (hSne p hp))
    (fun p hp p' hp' hne => hsepS p (hSsub p hp) p' (hSsub p' hp') hne)
  rw [hcardS] at hsepB
  -- assemble
  have hbase' : ((N₁ : ℝ) + N₂) * base + C + Work.Basic.UniNonres.sepB c₀ δ (N₁ + N₂ - 1)
      = ((N₁ : ℝ) + N₂) * (((L : ℝ) - 1) * Real.log 2 + 32 * Real.log (L : ℝ)) + C
        + Work.Basic.UniNonres.sepB c₀ δ (N₁ + N₂ - 1) := by rw [hbase]
  linarith [hdp', hsepB, hbase']

/-- **Assembly of one of the two sums of `denom`.**

The union `[B₁, B₁+M₁L-1] ∪ [B₂, B₂+M₂L-1]` is a translate-free model of `Dnr = I₁ ∪ I₂`: the
first interval contains the erased point `x`, the special block is bounded with the additive
constant `C`, all other blocks with their argmins, and the `M₁+M₂-1` argmin points are
`c₀`-separated from `0` and `δ`-separated. -/
private lemma ddenom_pair {L : ℕ} (hL : 1 ≤ L) {T : Finset ℤ} {x : ℤ} {α ξ c₀ δ C : ℝ}
    {B₁ B₂ : ℤ} {M₁ M₂ N : ℕ}
    (hblk : ∀ (p : ℤ) (k₀ : ℤ), k₀ ∈ Finset.Icc p (p + (L : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((L : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (L : ℝ))
    (hspec : ∀ t ∈ Finset.range M₁, x ∈ dblk (B₁ + (t : ℤ) * (L : ℤ)) (L : ℤ) →
        ∑ i ∈ (dblk (B₁ + (t : ℤ) * (L : ℤ)) (L : ℤ)).erase x, dsum α ξ i
          ≤ ((L : ℝ) - 1) * Real.log 2 + 32 * Real.log (L : ℝ) + C)
    (hM : 0 < M₁)
    (hmem : x ∈ Finset.Icc B₁ (B₁ + (M₁ : ℤ) * (L : ℤ) - 1))
    (hnot : x ∉ Finset.Icc B₂ (B₂ + (M₂ : ℤ) * (L : ℤ) - 1))
    (hdj : Disjoint (Finset.Icc B₁ (B₁ + (M₁ : ℤ) * (L : ℤ) - 1))
      (Finset.Icc B₂ (B₂ + (M₂ : ℤ) * (L : ℤ) - 1)))
    (hsub : ∀ p ∈ Finset.Icc B₁ (B₁ + (M₁ : ℤ) * (L : ℤ) - 1)
        ∪ Finset.Icc B₂ (B₂ + (M₂ : ℤ) * (L : ℤ) - 1), p ∈ T)
    (hsepT : ∀ p ∈ T, ∀ p' ∈ T, p ≠ p' →
      δ ≤ Work.TMC16Core.fracDist (((p - p' : ℤ) : ℝ) * α))
    (hN : M₁ + M₂ = N)
    (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (hlow : ∀ p ∈ Finset.Icc B₁ (B₁ + (M₁ : ℤ) * (L : ℤ) - 1)
        ∪ Finset.Icc B₂ (B₂ + (M₂ : ℤ) * (L : ℤ) - 1),
        p ≠ x → c₀ ≤ Work.TMC16Core.fracDist (ξ + (p : ℝ) * α)) :
    ∑ i ∈ (Finset.Icc B₁ (B₁ + (M₁ : ℤ) * (L : ℤ) - 1) ∪
        Finset.Icc B₂ (B₂ + (M₂ : ℤ) * (L : ℤ) - 1)).erase x, dsum α ξ i
      ≤ ((M₁ : ℝ) + M₂) * (((L : ℝ) - 1) * Real.log 2 + 32 * Real.log (L : ℝ)) + C
        + Work.Basic.UniNonres.sepB c₀ δ (N - 1) := by
  have h := dDnr_bound (L := L) hL hblk hM hmem hnot hdj hspec hc₀ hδ hδh hlow
    (fun p hp p' hp' hne => hsepT p (hsub p hp) p' (hsub p' hp') hne)
  have hidx : M₁ + M₂ - 1 = N - 1 := by omega
  rw [hidx] at h
  exact h

/-- A block of a partition of `[A, A+ML-1]` is contained in that interval. -/
private lemma dblk_sub_interval {L : ℤ} (hL : 1 ≤ L) {A : ℤ} {M t : ℕ} (ht : t < M) :
    ∀ i ∈ dblk (A + (t : ℤ) * L) L, i ∈ Finset.Icc A (A + (M : ℤ) * L - 1) := by
  intro i hi
  rw [dblk, Finset.mem_Icc] at hi
  obtain ⟨hi1, hi2⟩ := hi
  rw [Finset.mem_Icc]
  have hL0 : (0 : ℤ) ≤ L := by omega
  have ht0 : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg _
  have hprod : (0 : ℤ) ≤ (t : ℤ) * L := mul_nonneg ht0 hL0
  constructor
  · linarith [hi1, hprod]
  · have hcast : ((t : ℤ) + 1) ≤ (M : ℤ) := by
      have : t + 1 ≤ M := by omega
      exact_mod_cast this
    have h3 : ((t : ℤ) + 1) * L ≤ (M : ℤ) * L := mul_le_mul_of_nonneg_right hcast hL0
    have h4 : ((t : ℤ) + 1) * L = (t : ℤ) * L + L := by ring
    linarith [hi2, h3, h4]

end

theorem nru_denom {α θ c : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n s a' b' m : ℕ} {y k : ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hn : 2 ≤ n) (hL : 1 ≤ q (n - 1)) (hs : 1 ≤ s) (hab : a' + b' = s)
    (hy1 : 1 ≤ y)
    (hyΔ : (y : ℝ) * Δ n ≤ 3 / 4)
    (hym : (m : ℤ) * (q n : ℤ) ≤ y) (hym' : y < ((m : ℤ) + 1) * (q n : ℤ))
    (hnres : ∀ ℓ : ℤ, (s : ℤ) * (q (n - 1) : ℤ) ≤ |y - (ℓ : ℤ) * (q n : ℤ)|)
    (hsL : (2 * (s : ℤ)) * (q (n - 1) : ℤ) < (q n : ℤ))
    (hblk : ∀ (p : ℤ) (ξ : ℝ) (k₀ : ℤ),
      k₀ ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (q (n - 1) : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((q (n - 1) : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (q (n - 1) : ℝ))
    (hk : k ∈ Work.TMC16Core.Core.Dnr q n s a' b' y)
    (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (hθ : ∀ j : ℤ, |j| ≤ 2 * |y| + 6 * (s : ℤ) * (q (n - 1) : ℤ) + 4 →
      c ≤ Work.TMC16Core.fracDist (2 * θ + (j : ℝ) * α))
    {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (hsep : ∀ d ∈ Work.TMC16Core.Core.Dnr q n s a' b' y,
      ∀ d' ∈ Work.TMC16Core.Core.Dnr q n s a' b' y,
      d ≠ d' → δ ≤ Work.TMC16Core.fracDist (((d - d' : ℤ) : ℝ) * α)) :
    (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase k,
        Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))|)
      + (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase k,
        Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|)
    ≥ -((4 * (s : ℝ) * (q (n - 1) : ℝ) - 4 * (s : ℝ)) * Real.log 2)
      - 128 * (s : ℝ) * Real.log (q (n - 1) : ℝ)
      + Real.log (2 * c)
      - Work.Basic.UniNonres.sepB c δ (2 * s - 1)
      - Work.Basic.UniNonres.sepB δ δ (2 * s - 1)  := by
  classical
  have hy0 : (0 : ℤ) < y := by omega
  have habZ : ((a' : ℤ) + (b' : ℤ)) = (s : ℤ) := by exact_mod_cast hab
  have hdisjT : (s : ℤ) * (q (n - 1) : ℤ) ≤ y := by
    have h := hnres 0
    have h2 : |y - (0 : ℤ) * (q n : ℤ)| = y := by
      rw [zero_mul, sub_zero, abs_of_pos hy0]
    rwa [h2] at h
  -- the two intervals of `Dnr`, in block-compatible form
  set I₁ : Finset ℤ := Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ)))
      ((-((a' : ℤ) * (q (n - 1) : ℤ))) + ((2 * a' : ℕ) : ℤ) * (q (n - 1) : ℤ) - 1) with hI₁
  set I₂ : Finset ℤ := Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ))
      ((y - (b' : ℤ) * (q (n - 1) : ℤ)) + ((2 * b' : ℕ) : ℤ) * (q (n - 1) : ℤ) - 1) with hI₂
  have e1 : (-((a' : ℤ) * (q (n - 1) : ℤ))) + ((2 * a' : ℕ) : ℤ) * (q (n - 1) : ℤ) - 1
      = (a' : ℤ) * (q (n - 1) : ℤ) - 1 := by push_cast; ring
  have e2 : (y - (b' : ℤ) * (q (n - 1) : ℤ)) + ((2 * b' : ℕ) : ℤ) * (q (n - 1) : ℤ) - 1
      = y + (b' : ℤ) * (q (n - 1) : ℤ) - 1 := by push_cast; ring
  have hDnr : Work.TMC16Core.Core.Dnr q n s a' b' y = I₁ ∪ I₂ := by
    rw [hI₁, hI₂, e1, e2]
    rfl
  have hdisjI : Disjoint I₁ I₂ := by
    rw [hI₁, hI₂, Finset.disjoint_left]
    intro z hz hz'
    rw [Finset.mem_Icc] at hz hz'
    obtain ⟨h1, h2⟩ := hz
    obtain ⟨h3, h4⟩ := hz'
    rw [e1] at h2
    rw [e2] at h4
    have hkey : (s : ℤ) * (q (n - 1) : ℤ)
        = (a' : ℤ) * (q (n - 1) : ℤ) + (b' : ℤ) * (q (n - 1) : ℤ) := by
      rw [← add_mul, habZ]
    rw [hkey] at hdisjT
    have h5 : y - (b' : ℤ) * (q (n - 1) : ℤ) ≤ (a' : ℤ) * (q (n - 1) : ℤ) - 1 :=
      le_trans h3 h2
    have h6 : y ≤ (a' : ℤ) * (q (n - 1) : ℤ) + (b' : ℤ) * (q (n - 1) : ℤ) - 1 := by
      linarith
    linarith [h6, hdisjT]
  have hkI : k ∈ I₁ ∨ k ∈ I₂ := by
    rw [hDnr] at hk
    exact Finset.mem_union.mp hk
  have hsubD : ∀ p ∈ I₁ ∪ I₂, p ∈ Work.TMC16Core.Core.Dnr q n s a' b' y := by
    intro p hp
    rw [hDnr]
    exact hp
  have hsubD' : ∀ p ∈ I₂ ∪ I₁, p ∈ Work.TMC16Core.Core.Dnr q n s a' b' y := by
    intro p hp
    rw [Finset.union_comm] at hp
    rw [hDnr]
    exact hp
  -- the two phases
  set ξ₁ : ℝ := 2 * θ + (k : ℝ) * α with hξ₁
  set ξ₂ : ℝ := -((k : ℝ) * α) with hξ₂
  have hphase₁ : ∀ i : ℤ, (2 * θ + (((i + k : ℤ)) : ℝ) * α) = ξ₁ + (i : ℝ) * α := by
    intro i; rw [hξ₁]; push_cast; ring
  have hphase₂ : ∀ i : ℤ, Real.pi * (((i - k : ℤ)) : ℝ) * α
      = Real.pi * (ξ₂ + (i : ℝ) * α) := by
    intro i; rw [hξ₂]; push_cast; ring
  have hneg₁ : (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase k,
        Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))|)
      = -∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase k, dsum α ξ₁ i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [dsum, hphase₁ i]; ring)
  have hneg₂ : (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase k,
        Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|)
      = -∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase k, dsum α ξ₂ i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [dsum, hphase₂ i]; ring)
  have hS1 : (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase k, dsum α ξ₁ i)
      ≤ 2 * (s : ℝ) * (((q (n - 1) : ℝ) - 1) * Real.log 2 + 32 * Real.log (q (n - 1) : ℝ))
        - Real.log (2 * c) + Work.Basic.UniNonres.sepB c δ (2 * s - 1) := by
    rw [hDnr]
    have hcastab : ((2 * a' : ℕ) : ℝ) + ((2 * b' : ℕ) : ℝ) = 2 * (s : ℝ) := by
      rw [← hab]; push_cast; ring
    have hcastba : ((2 * b' : ℕ) : ℝ) + ((2 * a' : ℕ) : ℝ) = 2 * (s : ℝ) := by
      rw [← hab]; push_cast; ring
    have hNsum : 2 * a' + 2 * b' = 2 * s := by omega
    have hNsum' : 2 * b' + 2 * a' = 2 * s := by omega
    rcases hkI with hk1 | hk2
    · rw [hI₁, Finset.mem_Icc] at hk1
      have hk1I : k ∈ I₁ := by rw [hI₁]; exact Finset.mem_Icc.mpr ⟨hk1.1, hk1.2⟩
      have hM : 0 < 2 * a' := by
        by_contra h0
        have h0' : 2 * a' = 0 := by omega
        have hh := hk1.2
        rw [h0'] at hh
        simp only [Nat.cast_zero, zero_mul, add_zero] at hh
        linarith [hk1.1, hh]
      have h := ddenom_pair (L := q (n - 1)) (T := Work.TMC16Core.Core.Dnr q n s a' b' y)
        (x := k) (α := α) (ξ := ξ₁) (c₀ := c) (δ := δ) (C := -Real.log (2 * c))
        (B₁ := -((a' : ℤ) * (q (n - 1) : ℤ))) (M₁ := 2 * a')
        (B₂ := y - (b' : ℤ) * (q (n - 1) : ℤ)) (M₂ := 2 * b') (N := 2 * s)
        hL (fun p k₀ hk₀ hmin => hblk p ξ₁ k₀ hk₀ hmin) (fun t ht hmem => by
          have htlt : t < 2 * a' := Finset.mem_range.mp ht
          refine dblkGmem_le (L := q (n - 1)) hL
            (fun p k₀ hk₀ hmin => hblk p ξ₁ k₀ hk₀ hmin) hmem hc hc2 (fun i hi => ?_)
          have hiI₁ : i ∈ I₁ := by
            rw [hI₁]
            exact dblk_sub_interval (by exact_mod_cast hL)
              (A := -((a' : ℤ) * (q (n - 1) : ℤ))) (M := 2 * a') htlt i hi
          have hiD : i ∈ Work.TMC16Core.Core.Dnr q n s a' b' y := by
            rw [hDnr]; exact Finset.mem_union_left _ hiI₁
          have hidx := Dnr_add_abs_le hab hiD hk
          have h3 : c ≤ Work.TMC16Core.fracDist (2 * θ + ((i + k : ℤ) : ℝ) * α) := hθ (i + k) hidx
          have h2 := two_mul_fracDist_le_abs_sin (2 * θ + ((i + k : ℤ) : ℝ) * α)
          have h4 : ξ₁ + (i : ℝ) * α = 2 * θ + ((i + k : ℤ) : ℝ) * α := by
            rw [hξ₁]; push_cast; ring
          rw [h4]
          linarith)
        hM hk1I
        (fun hcon => by
          have hcon' : k ∈ I₂ := by
            rw [hI₂, Finset.mem_Icc]
            rw [Finset.mem_Icc] at hcon
            exact hcon
          exact (Finset.disjoint_left.mp hdisjI) hk1I hcon')
        hdisjI
        (fun p hp => hsubD p hp)
        (fun p hp p' hp' hne => hsep p hp p' hp' hne)
        hNsum hc hδ hδh
        (fun p hp hne => by
          have hpD := hsubD p hp
          have hidx := Dnr_add_abs_le hab hpD hk
          have h3 := hθ (p + k) hidx
          have h4 : ξ₁ + (p : ℝ) * α = 2 * θ + ((p + k : ℤ) : ℝ) * α := by
            rw [hξ₁]; push_cast; ring
          rw [h4]
          exact h3)
      refine le_trans h ?_
      rw [hcastab]
      linarith
    · rw [hI₂, Finset.mem_Icc] at hk2
      have hk2I : k ∈ I₂ := by rw [hI₂]; exact Finset.mem_Icc.mpr ⟨hk2.1, hk2.2⟩
      have hM : 0 < 2 * b' := by
        by_contra h0
        have h0' : 2 * b' = 0 := by omega
        have hh := hk2.2
        rw [h0'] at hh
        simp only [Nat.cast_zero, zero_mul, add_zero] at hh
        linarith [hk2.1, hh]
      have h := ddenom_pair (L := q (n - 1)) (T := Work.TMC16Core.Core.Dnr q n s a' b' y)
        (x := k) (α := α) (ξ := ξ₁) (c₀ := c) (δ := δ) (C := -Real.log (2 * c))
        (B₁ := y - (b' : ℤ) * (q (n - 1) : ℤ)) (M₁ := 2 * b')
        (B₂ := -((a' : ℤ) * (q (n - 1) : ℤ))) (M₂ := 2 * a') (N := 2 * s)
        hL (fun p k₀ hk₀ hmin => hblk p ξ₁ k₀ hk₀ hmin) (fun t ht hmem => by
          have htlt : t < 2 * b' := Finset.mem_range.mp ht
          refine dblkGmem_le (L := q (n - 1)) hL
            (fun p k₀ hk₀ hmin => hblk p ξ₁ k₀ hk₀ hmin) hmem hc hc2 (fun i hi => ?_)
          have hiI₂ : i ∈ I₂ := by
            rw [hI₂]
            exact dblk_sub_interval (by exact_mod_cast hL)
              (A := y - (b' : ℤ) * (q (n - 1) : ℤ)) (M := 2 * b') htlt i hi
          have hiD : i ∈ Work.TMC16Core.Core.Dnr q n s a' b' y := by
            rw [hDnr]; exact Finset.mem_union_right _ hiI₂
          have hidx := Dnr_add_abs_le hab hiD hk
          have h3 : c ≤ Work.TMC16Core.fracDist (2 * θ + ((i + k : ℤ) : ℝ) * α) := hθ (i + k) hidx
          have h2 := two_mul_fracDist_le_abs_sin (2 * θ + ((i + k : ℤ) : ℝ) * α)
          have h4 : ξ₁ + (i : ℝ) * α = 2 * θ + ((i + k : ℤ) : ℝ) * α := by
            rw [hξ₁]; push_cast; ring
          rw [h4]
          linarith)
        hM hk2I
        (fun hcon => by
          have hcon' : k ∈ I₁ := by
            rw [hI₁, Finset.mem_Icc]
            rw [Finset.mem_Icc] at hcon
            exact hcon
          exact (Finset.disjoint_left.mp hdisjI.symm) hk2I hcon')
        hdisjI.symm
        (fun p hp => hsubD' p hp)
        (fun p hp p' hp' hne => hsep p hp p' hp' hne)
        hNsum' hc hδ hδh
        (fun p hp hne => by
          have hpD := hsubD' p hp
          have hidx := Dnr_add_abs_le hab hpD hk
          have h3 := hθ (p + k) hidx
          have h4 : ξ₁ + (p : ℝ) * α = 2 * θ + ((p + k : ℤ) : ℝ) * α := by
            rw [hξ₁]; push_cast; ring
          rw [h4]
          exact h3)
      rw [Finset.union_comm] at h
      refine le_trans h ?_
      rw [hcastba]
      linarith
  have hS2 : (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase k, dsum α ξ₂ i)
      ≤ 2 * (s : ℝ) * (((q (n - 1) : ℝ) - 1) * Real.log 2 + 32 * Real.log (q (n - 1) : ℝ))
        + Work.Basic.UniNonres.sepB δ δ (2 * s - 1) := by
    rw [hDnr]
    have hcastab : ((2 * a' : ℕ) : ℝ) + ((2 * b' : ℕ) : ℝ) = 2 * (s : ℝ) := by
      rw [← hab]; push_cast; ring
    have hcastba : ((2 * b' : ℕ) : ℝ) + ((2 * a' : ℕ) : ℝ) = 2 * (s : ℝ) := by
      rw [← hab]; push_cast; ring
    have hNsum : 2 * a' + 2 * b' = 2 * s := by omega
    have hNsum' : 2 * b' + 2 * a' = 2 * s := by omega
    rcases hkI with hk1 | hk2
    · rw [hI₁, Finset.mem_Icc] at hk1
      have hk1I : k ∈ I₁ := by rw [hI₁]; exact Finset.mem_Icc.mpr ⟨hk1.1, hk1.2⟩
      have hM : 0 < 2 * a' := by
        by_contra h0
        have h0' : 2 * a' = 0 := by omega
        have hh := hk1.2
        rw [h0'] at hh
        simp only [Nat.cast_zero, zero_mul, add_zero] at hh
        linarith [hk1.1, hh]
      have h := ddenom_pair (L := q (n - 1)) (T := Work.TMC16Core.Core.Dnr q n s a' b' y)
        (x := k) (α := α) (ξ := ξ₂) (c₀ := δ) (δ := δ) (C := 0)
        (B₁ := -((a' : ℤ) * (q (n - 1) : ℤ))) (M₁ := 2 * a')
        (B₂ := y - (b' : ℤ) * (q (n - 1) : ℤ)) (M₂ := 2 * b') (N := 2 * s)
        hL (fun p k₀ hk₀ hmin => hblk p ξ₂ k₀ hk₀ hmin) (fun t ht hmem => by
          have hb := hblk (-((a' : ℤ) * (q (n - 1) : ℤ)) + (t : ℤ) * (q (n - 1) : ℤ)) ξ₂ k hmem
            (fun k' hk' => by
              have h0 : ξ₂ + (k : ℝ) * α = 0 := by rw [hξ₂]; ring
              rw [h0, mul_zero, Real.sin_zero, abs_zero]
              exact abs_nonneg _)
          have h1 := (abs_le.mp hb).1
          have hneg : (∑ i ∈ (dblk (-((a' : ℤ) * (q (n - 1) : ℤ))
                + (t : ℤ) * (q (n - 1) : ℤ)) (q (n - 1) : ℤ)).erase k, dsum α ξ₂ i)
              = -(∑ i ∈ (dblk (-((a' : ℤ) * (q (n - 1) : ℤ))
                + (t : ℤ) * (q (n - 1) : ℤ)) (q (n - 1) : ℤ)).erase k,
                  Real.log |Real.sin (Real.pi * (ξ₂ + (i : ℝ) * α))|) := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl (fun i _ => by simp only [dsum])
          rw [hneg]
          simp only [dblk]
          linarith)
        hM hk1I
        (fun hcon => by
          have hcon' : k ∈ I₂ := by
            rw [hI₂, Finset.mem_Icc]
            rw [Finset.mem_Icc] at hcon
            exact hcon
          exact (Finset.disjoint_left.mp hdisjI) hk1I hcon')
        hdisjI
        (fun p hp => hsubD p hp)
        (fun p hp p' hp' hne => hsep p hp p' hp' hne)
        hNsum hδ hδ hδh
        (fun p hp hne => by
          have hpD := hsubD p hp
          have h3 := hsep p hpD k hk hne
          have h4 : ξ₂ + (p : ℝ) * α = ((p - k : ℤ) : ℝ) * α := by rw [hξ₂]; push_cast; ring
          rw [h4]
          exact h3)
      refine le_trans h ?_
      rw [hcastab]
      linarith
    · rw [hI₂, Finset.mem_Icc] at hk2
      have hk2I : k ∈ I₂ := by rw [hI₂]; exact Finset.mem_Icc.mpr ⟨hk2.1, hk2.2⟩
      have hM : 0 < 2 * b' := by
        by_contra h0
        have h0' : 2 * b' = 0 := by omega
        have hh := hk2.2
        rw [h0'] at hh
        simp only [Nat.cast_zero, zero_mul, add_zero] at hh
        linarith [hk2.1, hh]
      have h := ddenom_pair (L := q (n - 1)) (T := Work.TMC16Core.Core.Dnr q n s a' b' y)
        (x := k) (α := α) (ξ := ξ₂) (c₀ := δ) (δ := δ) (C := 0)
        (B₁ := y - (b' : ℤ) * (q (n - 1) : ℤ)) (M₁ := 2 * b')
        (B₂ := -((a' : ℤ) * (q (n - 1) : ℤ))) (M₂ := 2 * a') (N := 2 * s)
        hL (fun p k₀ hk₀ hmin => hblk p ξ₂ k₀ hk₀ hmin) (fun t ht hmem => by
          have hb := hblk (y - (b' : ℤ) * (q (n - 1) : ℤ) + (t : ℤ) * (q (n - 1) : ℤ)) ξ₂ k hmem
            (fun k' hk' => by
              have h0 : ξ₂ + (k : ℝ) * α = 0 := by rw [hξ₂]; ring
              rw [h0, mul_zero, Real.sin_zero, abs_zero]
              exact abs_nonneg _)
          have h1 := (abs_le.mp hb).1
          have hneg : (∑ i ∈ (dblk (y - (b' : ℤ) * (q (n - 1) : ℤ)
                + (t : ℤ) * (q (n - 1) : ℤ)) (q (n - 1) : ℤ)).erase k, dsum α ξ₂ i)
              = -(∑ i ∈ (dblk (y - (b' : ℤ) * (q (n - 1) : ℤ)
                + (t : ℤ) * (q (n - 1) : ℤ)) (q (n - 1) : ℤ)).erase k,
                  Real.log |Real.sin (Real.pi * (ξ₂ + (i : ℝ) * α))|) := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl (fun i _ => by simp only [dsum])
          rw [hneg]
          simp only [dblk]
          linarith)
        hM hk2I
        (fun hcon => by
          have hcon' : k ∈ I₁ := by
            rw [hI₁, Finset.mem_Icc]
            rw [Finset.mem_Icc] at hcon
            exact hcon
          exact (Finset.disjoint_left.mp hdisjI.symm) hk2I hcon')
        hdisjI.symm
        (fun p hp => hsubD' p hp)
        (fun p hp p' hp' hne => hsep p hp p' hp' hne)
        hNsum' hδ hδ hδh
        (fun p hp hne => by
          have hpD := hsubD' p hp
          have h3 := hsep p hpD k hk hne
          have h4 : ξ₂ + (p : ℝ) * α = ((p - k : ℤ) : ℝ) * α := by rw [hξ₂]; push_cast; ring
          rw [h4]
          exact h3)
      rw [Finset.union_comm] at h
      refine le_trans h ?_
      rw [hcastba]
      linarith
  rw [hneg₁, hneg₂]
  linarith [hS1, hS2]


end Work.TMC16Core.NrFinal
