import Mathlib
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.sigmaGroupFacts

/-!
# PTCert — the positive-row group labels are invariant under the stabiliser of the row

For `r ≥ 1` the group label `labE r` of the code `z` (the index of the `Stab(x₀_r)`-orbit
containing `z`) is invariant under every `g ∈ Σ₅` fixing the row code `x0c r`.

The argument uses only the semantic Props `CodeFacts`, `ActSetup`, `RowSem`, `GroupSem`
(no `ESem`, hence no bound on the halves of the codes): the table clause of `ActSetup`
turns the action of *any* element of `Sg` on `EI` into the action of a letter table on codes,
so no half-code bound is ever needed.

* `c` = a valid code of `g`; since `g` fixes `x0_r`, `actCode c (x0c r) = x0c r`, so
  `c ∈ stabL r` (`RowSem`), say `c = (stabL r).getD i 0`; by `RowSem` the table `stabTab r i`
  computes `actCode c`, so `TabOf g (stabTab r i)`; hence `(actE g z).1 = actC (stabTab r i) z.1`.
* `GroupSem` writes `z = actC (stabTab r i') (grepE r (labE r z.1))` for some `i'`, and every
  stabiliser generator maps the representative `grepE r g'` into its own group.
* The two stabiliser elements `codeElt c_i`, `codeElt c_{i'}` multiply (matrix-free, via the
  multiplication clause of `ActSetup`) to an element of the stabiliser, whose valid code `c''`
  gives an index `i''` with `actE (codeElt c_i) (actE (codeElt c_{i'}) gr) = actC (stabTab r i'') gr`,
  and the latter lies in the group of `grepE r (labE r z.1)`.
-/

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D

set_option autoImplicit false
set_option maxRecDepth 10000

/-- The value of `toEI z x` when `z` is a code of `B₂`. -/
private lemma stabInv_toEI_val {z : ℕ} {x : EI} (h : z ∈ eS) : (toEI z x).1 = z := by
  rw [toEI, dif_pos h]

/-- The `getD` of a list at an in-range index is a member. -/
private lemma stabInv_getD_mem {l : List ℕ} {i : ℕ} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem (hn := hi)]
  exact List.getElem_mem hi

/-- Every member of a list is the `getD` of an in-range index. -/
private lemma stabInv_mem_getD {l : List ℕ} {c : ℕ} (h : c ∈ l) :
    ∃ i < l.length, l.getD i 0 = c := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp h
  exact ⟨i.1, i.2, by rw [List.getD_eq_getElem (hn := i.2)]; exact hi⟩

theorem stabInvPos (hCF : CodeFacts) (hA : ActSetup) (hR : RowSem) (hG : GroupSem)
    (r : ℕ) (hr : r < 18) (hr1 : 1 ≤ r) (g : G5) (hg : g ∈ Sg)
    (hfix : actE g (x0E r pt0) = x0E r pt0) (z : EI) :
    labE r (actE g z).1 = labE r z.1 := by
  classical
  have hSg : IsFinSubgroup Sg := (sigmaGroupFacts 5).1
  have hmul := hA.2.2.2.1
  have htab := hA.2.2.2.2.2.2.1
  have hcode := hA.2.2.2.2.2.2.2.1
  have hR7 := hR.2.2.2.2.2.2.1
  have hR8 := hR.2.2.2.2.2.2.2
  have hG3 := hG.2.2 r hr hr1
  have hx0E : (x0E r pt0).1 = x0c r :=
    stabInv_toEI_val (List.mem_toFinset.mpr (hR.2.1 r hr))
  -- a valid code of `g`, which fixes the row code, hence lies in the stabiliser list
  obtain ⟨c, hvc, hcg⟩ := hCF.2.1 g hg
  have hfxc : actCode c (x0c r) = x0c r := by
    have h := congrArg Subtype.val hfix
    rw [← hcg, hcode c hvc (x0E r pt0), hx0E] at h
    exact h
  have hcmem : c ∈ stabL r := ((hR7 r hr hr1 c hvc).1).mp hfxc
  obtain ⟨i, hi, hic⟩ := stabInv_mem_getD hcmem
  have hciSg : codeElt ((stabL r).getD i 0) ∈ Sg := (hCF.1 _ ((hR8 r hr hr1 i hi).1)).1
  -- the letter table `stabTab r i` is a table of `g`
  have hTab_g : TabOf g (stabTab r i) := by
    intro k hk
    rw [← hcg]
    rw [show lk (stabTab r i) k = actL 5 (c / 32) (c % 32) k from by
      rw [← hic]; exact (hR8 r hr hr1 i hi).2 k hk]
    exact ((hCF.1 c hvc).2 k hk).2
  have hlk_lt : ∀ k < 81, lk (stabTab r i) k < 81 := by
    intro k hk
    rw [show lk (stabTab r i) k = actL 5 (c / 32) (c % 32) k from by
      rw [← hic]; exact (hR8 r hr hr1 i hi).2 k hk]
    exact ((hCF.1 c hvc).2 k hk).1
  have hstep : (actE g z).1 = actC cmT (stabTab r i) z.1 :=
    htab g (stabTab r i) hTab_g hlk_lt z
  -- `z` is a stabiliser image of its group representative
  have hzE : z.1 ∈ eAll := List.mem_toFinset.mp z.2
  obtain ⟨hg0lt, i', hi', hi'eq⟩ := hG3.1 z.1 hzE
  have hgrep0mem : grepE r (labE r z.1) ∈ eAll := (hG3.2.1 (labE r z.1) hg0lt).1
  set gr : EI := ⟨grepE r (labE r z.1), List.mem_toFinset.mpr hgrep0mem⟩ with hgrdef
  have hTab_i : TabOf (codeElt ((stabL r).getD i 0)) (stabTab r i) := by
    intro k hk
    rw [(hR8 r hr hr1 i hi).2 k hk]
    exact ((hCF.1 _ ((hR8 r hr hr1 i hi).1)).2 k hk).2
  have hTab_i' : TabOf (codeElt ((stabL r).getD i' 0)) (stabTab r i') := by
    intro k hk
    rw [(hR8 r hr hr1 i' hi').2 k hk]
    exact ((hCF.1 _ ((hR8 r hr hr1 i' hi').1)).2 k hk).2
  have hlk'_lt : ∀ k < 81, lk (stabTab r i') k < 81 := by
    intro k hk
    rw [(hR8 r hr hr1 i' hi').2 k hk]
    exact ((hCF.1 _ ((hR8 r hr hr1 i' hi').1)).2 k hk).1
  have hAz : actE (codeElt ((stabL r).getD i' 0)) gr = z := by
    apply Subtype.ext
    show (actE (codeElt ((stabL r).getD i' 0)) gr).1 = z.1
    rw [htab (codeElt ((stabL r).getD i' 0)) (stabTab r i') hTab_i' hlk'_lt gr]
    show actC cmT (stabTab r i') (grepE r (labE r z.1)) = z.1
    exact hi'eq
  -- the two stabiliser elements multiply
  have hprod : actE (codeElt ((stabL r).getD i 0) * codeElt ((stabL r).getD i' 0)) gr
      = actE (codeElt ((stabL r).getD i 0)) (actE (codeElt ((stabL r).getD i' 0)) gr) :=
    hmul _ hciSg _ (hCF.1 _ ((hR8 r hr hr1 i' hi').1)).1 gr
  have hfix_i : actE (codeElt ((stabL r).getD i 0)) (x0E r pt0) = x0E r pt0 := by
    apply Subtype.ext
    show (actE (codeElt ((stabL r).getD i 0)) (x0E r pt0)).1 = (x0E r pt0).1
    rw [hcode ((stabL r).getD i 0) ((hR8 r hr hr1 i hi).1) (x0E r pt0), hx0E]
    exact ((hR7 r hr hr1 ((stabL r).getD i 0) ((hR8 r hr hr1 i hi).1)).1).mpr
      (stabInv_getD_mem hi)
  have hfix_i' : actE (codeElt ((stabL r).getD i' 0)) (x0E r pt0) = x0E r pt0 := by
    apply Subtype.ext
    show (actE (codeElt ((stabL r).getD i' 0)) (x0E r pt0)).1 = (x0E r pt0).1
    rw [hcode ((stabL r).getD i' 0) ((hR8 r hr hr1 i' hi').1) (x0E r pt0), hx0E]
    exact ((hR7 r hr hr1 ((stabL r).getD i' 0) ((hR8 r hr hr1 i' hi').1)).1).mpr
      (stabInv_getD_mem hi')
  obtain ⟨c'', hvc'', hc''⟩ := hCF.2.1 _ (hSg.2.1 _ hciSg _ (hCF.1 _ ((hR8 r hr hr1 i' hi').1)).1)
  have hfix'' : actE (codeElt c'') (x0E r pt0) = x0E r pt0 := by
    rw [hc'', hmul _ hciSg _ (hCF.1 _ ((hR8 r hr hr1 i' hi').1)).1 (x0E r pt0), hfix_i', hfix_i]
  have hc''mem : c'' ∈ stabL r := ((hR7 r hr hr1 c'' hvc'').1).mp (by
    have h := congrArg Subtype.val hfix''
    rw [hcode c'' hvc'' (x0E r pt0), hx0E] at h
    exact h)
  obtain ⟨i'', hi'', hi''c⟩ := stabInv_mem_getD hc''mem
  have hTab_i'' : TabOf (codeElt c'') (stabTab r i'') := by
    intro k hk
    rw [show lk (stabTab r i'') k = actL 5 (c'' / 32) (c'' % 32) k from by
      rw [← hi''c]; exact (hR8 r hr hr1 i'' hi'').2 k hk]
    exact ((hCF.1 c'' hvc'').2 k hk).2
  have hlk''_lt : ∀ k < 81, lk (stabTab r i'') k < 81 := by
    intro k hk
    rw [show lk (stabTab r i'') k = actL 5 (c'' / 32) (c'' % 32) k from by
      rw [← hi''c]; exact (hR8 r hr hr1 i'' hi'').2 k hk]
    exact ((hCF.1 c'' hvc'').2 k hk).1
  have hA2 : (actE (codeElt c'') gr).1 = actC cmT (stabTab r i'') (grepE r (labE r z.1)) := by
    rw [htab (codeElt c'') (stabTab r i'') hTab_i'' hlk''_lt gr]
  have hA1 : (actE (codeElt ((stabL r).getD i 0))
        (actE (codeElt ((stabL r).getD i' 0)) gr)).1 = actC cmT (stabTab r i) z.1 := by
    rw [htab (codeElt ((stabL r).getD i 0)) (stabTab r i) hTab_i hlk_lt
      (actE (codeElt ((stabL r).getD i' 0)) gr), hAz]
  have hlab'' : labE r (actC cmT (stabTab r i'') (grepE r (labE r z.1))) = labE r z.1 :=
    hG3.2.2.1 i'' hi'' (labE r z.1) hg0lt
  calc labE r (actE g z).1
      = labE r (actC cmT (stabTab r i) z.1) := by rw [hstep]
    _ = labE r (actE (codeElt ((stabL r).getD i 0))
          (actE (codeElt ((stabL r).getD i' 0)) gr)).1 := by rw [hA1]
    _ = labE r (actE (codeElt ((stabL r).getD i 0) * codeElt ((stabL r).getD i' 0)) gr).1 := by
          rw [hprod]
    _ = labE r (actE (codeElt c'') gr).1 := by rw [← hc'']
    _ = labE r (actC cmT (stabTab r i'') (grepE r (labE r z.1))) := by rw [hA2]
    _ = labE r z.1 := hlab''

end Work.PTCert
