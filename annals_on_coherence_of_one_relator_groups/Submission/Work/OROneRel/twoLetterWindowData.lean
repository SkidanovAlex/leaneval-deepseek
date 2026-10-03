/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The window data of the two-letter relator `a ^ p * b ^ q`

Target: `Work.OROneRel.twoLetterWindowData`.  For `p, q ≥ 1` coprime and `l ≥ 1` it produces a
weight `c`, a deck element `τ`, a level window `[lo,hi]` and a gauge `Wt` of the `ℤ`-cover of the
two-letter one-relator complex `⟨a,b | (a^p b^q)^l⟩` such that

* `cohom c (tlU p q) = 1` and `cohom c τ = ofAdd 1`;
* `Wt 0 = 1` and `cohom c (Wt i) = ofAdd i` for every level `i`;
* the walk of `tlU p q` lies in the window and no non-zero translate of it does (the window is the
  band `[0, p q]`, which is *forced*: `Work.OROneRel.window_eq_band_tlW`);
* the gauge words of the window levels traverse only window edges of trivial loop class, and some
  traversed edge of the walk is a tree edge;
* **the Freiheitssatz of the domain**: `winRho x ∈ ⟪tlU p q ^ l⟫ → x ∈ ⟪winRoot ^ l⟫`
  (`Work.OROneRel.twoLetterFreiheitssatz`).

## The construction

Take `c = tlW p q` (`a ↦ q`, `b ↦ -p`) and the band `[0, p q]` as the window.  The deck element `τ`
comes from Bézout's identity (`Work.OROneRel.exists_coh_tau_tlW`), and `Wt` is the tree-path gauge of
the band (`Work.OROneRel.treeGauge` of `Work.OROneRel.exists_treeGauge`), extended off the band by the
powers of `τ` (`bandExtend`); the extension is invisible to the loop classes of the window edges, so
the tree property on the band and the Freiheitssatz transfer verbatim.

The reachability input of `exists_treeGauge` is `Work.OROneRel.bandLevelReach` below: every level of
the band is reached, inside the band, by a word.  It is proved from the arithmetic connectivity of the
`±p, ±q` interval (`Work.OROneRel.interval_connected`, via `steps_of_chain`,
`exists_word_of_confined_steps` and `decor_winE_of_red`) in the generic case `p, q ≥ 2`, and from the
monotone chain `0 ↦ 1 ↦ ⋯ ↦ i` in the unit-weight cases `p = 1` or `q = 1`.
-/
import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winAssembly
import Submission.Work.OROneRel.twoLetterFreiheitssatz
import Submission.Work.OROneRel.exists_treeGauge
import Submission.Work.OROneRel.treeGauge_edge_of_unique_witness
import Submission.Work.OROneRel.interval_connected
import Submission.Work.OROneRel.steps_of_chain
import Submission.Work.OROneRel.exists_word_of_confined_steps
import Submission.Work.OROneRel.decor_winE_of_red

namespace Work.OROneRel

/-! ## The band `[0, p q]` as the window of the walk -/

/-- `wordOf` of a free-group word is its reduction. -/
private theorem wordOf_mk_eq_reduce_fin2 (L : List (Fin 2 × Bool)) :
    wordOf (FreeGroup.mk L) = @FreeGroup.reduce (Fin 2) (Classical.decEq (Fin 2)) L := rfl

/-- **The walk of the two-letter relator lies in the band `[0, p q]`.** -/
theorem tlU_walk_mem_winE (p q : ℕ) :
    ∀ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)) := by
  intro e he
  obtain ⟨h1, h2, h3, h4⟩ := walk_levels_tlW p q e he
  rw [mem_winE]
  exact ⟨h1, h2, h3, h4⟩

/-- **The band is tight for the walk of the two-letter relator**: no non-zero translate of the walk
lies in the band.  The walk attains the bottom level `0` (`walk_src_zero_tlW`) and the top level
`p q` (`walk_tgt_top_tlW`). -/
theorem tlU_walk_tight (p q : ℕ) (hp : 1 ≤ p) :
    ∀ k : ℤ, k ≠ 0 →
      ¬ (∀ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
          0 ≤ e.1.2 + k ∧ 0 ≤ e.1.2 + tlW p q e.1.1 + k ∧
            e.1.2 + k ≤ (p : ℤ) * (q : ℤ) ∧
            e.1.2 + tlW p q e.1.1 + k ≤ (p : ℤ) * (q : ℤ)) := by
  intro k hk h
  obtain ⟨e₀, he₀, hsrc⟩ := walk_src_zero_tlW p q hp
  obtain ⟨e₁, he₁, htgt⟩ := walk_tgt_top_tlW p q hp
  have h0 := h e₀ he₀
  have h1 := h e₁ he₁
  rcases lt_or_gt_of_ne hk with hk' | hk'
  · omega
  · omega

/-! ## Reachability of the levels of the band -/

/-- **The monotone chain of unit steps.**  If `A = 1` or `B = 1` then every level `i` of `[0,N]` is
reached from `0` inside `[0,N]` by a chain of `+1`-steps. -/
private theorem chain_unit {N : ℤ} (A B : ℤ) (h1 : A = 1 ∨ B = 1) :
    ∀ i : ℤ, 0 ≤ i → i ≤ N →
      Relation.ReflTransGen (fun a b : ℤ => 0 ≤ b ∧ b ≤ N ∧
        (b = a + A ∨ b = a - A ∨ b = a + B ∨ b = a - B)) 0 i := by
  intro i h0 hi
  have aux : ∀ n : ℕ, ((n : ℕ) : ℤ) ≤ N →
      Relation.ReflTransGen (fun a b : ℤ => 0 ≤ b ∧ b ≤ N ∧
        (b = a + A ∨ b = a - A ∨ b = a + B ∨ b = a - B)) 0 ((n : ℕ) : ℤ) := by
    intro n
    induction n with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ m ih =>
      intro hm
      refine (ih (by omega)).tail ?_
      rcases h1 with h1 | h1
      · refine ⟨by positivity, by push_cast; omega, Or.inl ?_⟩
        rw [h1]; push_cast; ring
      · refine ⟨by positivity, by push_cast; omega, Or.inr (Or.inr (Or.inl ?_))⟩
        rw [h1]; push_cast; ring
  have hcast : (((i.toNat : ℕ)) : ℤ) = i := Int.toNat_of_nonneg h0
  have := aux i.toNat (by rw [hcast]; exact hi)
  rwa [hcast] at this

/-- **A chain of `±A, ±B`-steps in the band yields a word.**  This is the generic step of the
reachability proof: `steps_of_chain` records the chain as a list of steps,
`exists_word_of_confined_steps` spells it out by letters of the two-generator alphabet, and
`decor_winE_of_red` transports the window property of the spelled word to the reduced word of the
group element it represents. -/
private theorem reach_of_chain {p q : ℕ} {A B : ℤ} (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hAB : A ≠ B)
    (hxA : tlW p q 0 = A ∨ tlW p q 0 = -A)
    (hyB : tlW p q 1 = B ∨ tlW p q 1 = -B) {i : ℤ}
    (hchain : Relation.ReflTransGen (fun a b : ℤ => 0 ≤ b ∧ b ≤ (p : ℤ) * (q : ℤ) ∧
        (b = a + A ∨ b = a - A ∨ b = a + B ∨ b = a - B)) 0 i) :
    ∃ w : FreeGroup (Fin 2), cohom (tlW p q) w = Multiplicative.ofAdd i ∧
      ∀ e ∈ decor (tlW p q) 0 (wordOf w),
        coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)) := by
  classical
  have hpq0 : (0 : ℤ) ≤ (p : ℤ) * (q : ℤ) := by positivity
  obtain ⟨ss, hstep, hsum, hscan⟩ := steps_of_chain hchain ⟨le_rfl, hpq0⟩
  obtain ⟨L, hlsig, hWin⟩ := exists_word_of_confined_steps (tlW p q) 0 1 A B hA0 hB0 hAB
    hxA hyB ss hstep 0 ((p : ℤ) * (q : ℤ)) hscan
  refine ⟨FreeGroup.mk L, ?_, ?_⟩
  · rw [cohom_mk, hlsig, hsum]
    simp
  · rw [wordOf_mk_eq_reduce_fin2]
    exact decor_winE_of_red (tlW p q) 0 ((p : ℤ) * (q : ℤ))
      (@FreeGroup.reduce.red (Fin 2) L (Classical.decEq (Fin 2))) hWin

/-- **Every level of the band is reached by a word confined to the band.** -/
theorem bandLevelReach (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) → ∃ w : FreeGroup (Fin 2),
      cohom (tlW p q) w = Multiplicative.ofAdd i ∧
      ∀ e ∈ decor (tlW p q) 0 (wordOf w),
        coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)) := by
  have hpq0 : (0 : ℤ) ≤ (p : ℤ) * (q : ℤ) := by positivity
  by_cases hq1 : q = 1
  · -- `q = 1`: the generator `0` has weight `1`
    intro i h0 hle
    refine reach_of_chain (p := p) (q := q) (A := (1 : ℤ)) (B := -(p : ℤ))
      (by norm_num) (by omega) (by omega) (Or.inl ?_) (Or.inl ?_)
      (chain_unit (N := (p : ℤ) * (q : ℤ)) (A := (1 : ℤ)) (B := -(p : ℤ)) (Or.inl rfl) i h0 hle)
    · rw [tlW_zero, hq1]; norm_num
    · rw [tlW_one]
  · by_cases hp1 : p = 1
    · -- `p = 1`: the generator `1` has weight `-1`
      intro i h0 hle
      refine reach_of_chain (p := p) (q := q) (A := (q : ℤ)) (B := (1 : ℤ))
        (by omega) (by norm_num) (by omega) (Or.inl ?_) (Or.inr ?_)
        (chain_unit (N := (p : ℤ) * (q : ℤ)) (A := (q : ℤ)) (B := (1 : ℤ)) (Or.inr rfl) i h0 hle)
      · rw [tlW_zero]
      · rw [tlW_one, hp1]; norm_num
    · -- both weights are at least `2`
      have hp2 : 2 ≤ p := by omega
      have hq2 : 2 ≤ q := by omega
      have hA2 : 2 ≤ (q : ℤ) := by exact_mod_cast hq2
      have hB2 : 2 ≤ (p : ℤ) := by exact_mod_cast hp2
      have hpq0' : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp2
      have hqq0' : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq2
      have hbez : ∃ a b : ℤ, a * (q : ℤ) + b * (p : ℤ) = 1 := by
        obtain ⟨x, y, hxy⟩ := (Nat.isCoprime_iff_coprime.mpr hcop : IsCoprime (p : ℤ) (q : ℤ))
        exact ⟨y, x, by linarith⟩
      have hbound : (q : ℤ) + (p : ℤ) - 2 ≤ (p : ℤ) * (q : ℤ) - 0 := by nlinarith
      intro i h0 hle
      refine reach_of_chain (p := p) (q := q) (A := (q : ℤ)) (B := (p : ℤ))
        (by omega) (by omega) ?_ (Or.inl ?_) (Or.inr ?_)
        (interval_connected hA2 hB2 hbez 0 ((p : ℤ) * (q : ℤ)) hbound 0 i le_rfl hpq0 h0 hle)
      · intro h
        have hpq : q = p := by exact_mod_cast h
        have hc : Nat.Coprime p p := by rw [← hpq] at hcop ⊢; exact hcop
        have : p = 1 := (Nat.coprime_self p).mp hc
        omega
      · rw [tlW_zero]
      · rw [tlW_one]

/-! ## The deck element of weight `1` -/

/-- **A deck element of weight `1`** for the weight `tlW p q`, from Bézout's identity: if
`x * p + y * q = 1` then `of 0 ^ y * of 1 ^ (-x)` has weight `y * q + x * p = 1`. -/
theorem exists_coh_tau_tlW (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    ∃ τ : FreeGroup (Fin 2), cohom (tlW p q) τ = Multiplicative.ofAdd 1 := by
  obtain ⟨x, y, hxy⟩ := (Nat.isCoprime_iff_coprime.mpr hcop : IsCoprime (p : ℤ) (q : ℤ))
  refine ⟨FreeGroup.of 0 ^ y * FreeGroup.of 1 ^ (-x), ?_⟩
  rw [map_mul, map_zpow, map_zpow, cohom_of, cohom_of, tlW_zero, tlW_one]
  rw [← ofAdd_zsmul, ← ofAdd_zsmul, ← ofAdd_add]
  congr 1
  simp only [zsmul_eq_mul, Int.cast_id]
  linarith

/-! ## The tree-path gauge of the band -/

/-- **The tree-path gauge of the band is a gauge on the band, with tree paths.**  This is the
conclusion of `Work.OROneRel.exists_treeGauge` for the band, with the witness kept explicit (so that
the statements below can refer to `treeGauge` definitionally). -/
theorem treeGauge_band_facts (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    (treeGauge (tlW p q) 0 ((p : ℤ) * (q : ℤ))) 0 = 1 ∧
    (∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      cohom (tlW p q) (treeGauge (tlW p q) 0 ((p : ℤ) * (q : ℤ)) i) = Multiplicative.ofAdd i) ∧
    (∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ decor (tlW p q) 0 (wordOf (treeGauge (tlW p q) 0 ((p : ℤ) * (q : ℤ)) i)),
        coverEdge e ∈ winTree (treeGauge (tlW p q) 0 ((p : ℤ) * (q : ℤ))) (tlW p q) 0
          ((p : ℤ) * (q : ℤ))) := by
  classical
  have hreach := bandLevelReach p q hp hq hcop
  refine ⟨?_, ?_, ?_⟩
  · have h := (Inv_all (tlW p q) 0 ((p : ℤ) * (q : ℤ))
      (NW (tlW p q) 0 ((p : ℤ) * (q : ℤ))) le_rfl).1
    simp only [treeGauge, h, Option.getD_some]
    exact FreeGroup.one_eq_mk.symm
  · intro i hi1 hi2
    have hass := assigned_of_window (tlW p q) 0 ((p : ℤ) * (q : ℤ)) hreach hi1 hi2
    obtain ⟨L, hL⟩ := Option.ne_none_iff_exists'.mp hass
    have hinv := (Inv_all (tlW p q) 0 ((p : ℤ) * (q : ℤ))
      (NW (tlW p q) 0 ((p : ℤ) * (q : ℤ))) le_rfl).2 i L hL
    rw [treeGauge_of hL le_rfl, cohom_mk, hinv.1]
  · intro i hi1 hi2 e he
    have hass := assigned_of_window (tlW p q) 0 ((p : ℤ) * (q : ℤ)) hreach hi1 hi2
    obtain ⟨L, hL⟩ := Option.ne_none_iff_exists'.mp hass
    have hinv := (Inv_all (tlW p q) 0 ((p : ℤ) * (q : ℤ))
      (NW (tlW p q) 0 ((p : ℤ) * (q : ℤ))) le_rfl).2 i L hL
    obtain ⟨-, hred, hE, -, hcl⟩ := hinv
    rw [treeGauge_of hL le_rfl, wordOf_mk_of_isReduced hred] at he
    exact mem_winTree.mpr ⟨hE e he, hcl e he⟩

/-- **Some traversal of the walk is a tree edge of the band gauge.**  The exploration of
`exists_treeGauge` discovers the level `q` (`= c 0`, the target of the first step of the walk) in its
first round, through a root witness whose edge is either `(0,0)` (`a` read at the level `0`) or
`(1,p)` (`b` read at the level `p`); both are traversed by the walk of `tlU p q`, and the discovering
edge of an assigned level has trivial loop class by the invariant of the exploration. -/
theorem bandTreeEdge_local (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∃ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      coverEdge e ∈ winTree (treeGauge (tlW p q) 0 ((p : ℤ) * (q : ℤ))) (tlW p q) 0
        ((p : ℤ) * (q : ℤ)) := by
  classical
  -- the walk starts at the level `0`, so the weight `c = tlW p q` and the level `q = c 0` are used
  have hq0 : ((q : ℤ)) ≠ 0 := by omega
  -- the root witness: the letter `a` read at the level `0`
  have hE₀ : Bwit.edge (tlW p q) (⟨0, (0 : Fin 2), true, []⟩ : Bwit (Fin 2)) ∈
      winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)) := by
    rw [mem_winE]
    have hedge : Bwit.edge (tlW p q) (⟨0, (0 : Fin 2), true, []⟩ : Bwit (Fin 2)) =
        ((0 : Fin 2), (0 : ℤ)) := rfl
    rw [hedge]
    refine ⟨le_rfl, by positivity, ?_, ?_⟩
    · rw [tlW_zero]; positivity
    · rw [tlW_zero]
      have hp1 : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
      have hq1 : (0 : ℤ) ≤ (q : ℤ) := by positivity
      nlinarith
  have htgt₀ : Bwit.tgt (tlW p q) (⟨0, (0 : Fin 2), true, []⟩ : Bwit (Fin 2)) = (q : ℤ) := by
    show (0 : ℤ) + tlW p q (0 : Fin 2) = (q : ℤ)
    rw [tlW_zero]; ring
  have hb0 : bstate (tlW p q) 0 ((p : ℤ) * (q : ℤ)) 0 (q : ℤ) = none := by
    rw [bstate_zero]
    exact if_neg hq0
  -- the witness discovers the level `q`, hence the level is assigned in the first round
  have hbEx : bExists (tlW p q) 0 ((p : ℤ) * (q : ℤ))
      (bstate (tlW p q) 0 ((p : ℤ) * (q : ℤ)) 0) (q : ℤ) :=
    ⟨⟨0, (0 : Fin 2), true, []⟩, hE₀, by rw [bstate_zero]; simp, htgt₀.symm⟩
  have hstep1 : bstate (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (0 + 1) (q : ℤ) =
      some (Bwit.newWord (Classical.choose hbEx)) := by
    rw [bstate_succ, bstep_eq_some_of_exists hb0 hbEx]
  have hNW : 1 ≤ NW (tlW p q) 0 ((p : ℤ) * (q : ℤ)) := by
    rw [NW]; exact Nat.le_add_left 1 _
  -- the invariant: every decorated letter of the word assigned to the level `q` has trivial class
  have hinv := (Inv_all (tlW p q) 0 ((p : ℤ) * (q : ℤ)) 1 hNW).2 (q : ℤ)
    (Bwit.newWord (Classical.choose hbEx)) hstep1
  -- the chosen witness
  obtain ⟨hE', hst', htg'⟩ := Classical.choose_spec hbEx
  obtain ⟨hlv, hw⟩ := bstate_zero_eq_some_iff hst'
  set p' : Bwit (Fin 2) := Classical.choose hbEx with hp'def
  have hE'' : Bwit.edge (tlW p q) p' ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)) := by
    rw [hp'def]; exact hE'
  have hst'' : bstate (tlW p q) 0 ((p : ℤ) * (q : ℤ)) 0 p'.lv = some p'.word := by
    rw [hp'def]; exact hst'
  have htg'' : (q : ℤ) = Bwit.tgt (tlW p q) p' := by
    rw [hp'def]; exact htg'
  have hinv' := hinv
  rw [hp'def] at hinv'
  set hcl' := hinv'.2.2.2.2 with hcl'def
  -- the traversed edge of the chosen witness is `(0,0)` or `(1,p)`
  have hedge : Bwit.edge (tlW p q) p' = ((0 : Fin 2), (0 : ℤ)) ∨
      Bwit.edge (tlW p q) p' = ((1 : Fin 2), (p : ℤ)) := by
    obtain ⟨lv', gen', dir', word'⟩ := p'
    have hlv' : lv' = 0 := hlv
    have htgt' : (q : ℤ) = (if dir' then lv' + tlW p q gen' else lv' - tlW p q gen') := htg''
    subst hlv'
    rw [zero_add, zero_sub] at htgt'
    have hg : gen' = (0 : Fin 2) ∨ gen' = (1 : Fin 2) := by
      have h : (gen' : ℕ) = 0 ∨ (gen' : ℕ) = 1 := by have := gen'.isLt; omega
      rcases h with h | h
      · exact Or.inl (Fin.ext (by simpa using h))
      · exact Or.inr (Fin.ext (by simpa using h))
    rcases hg with hg | hg
    · subst hg
      rw [tlW_zero] at htgt'
      cases dir' with
      | false =>
        simp only [Bool.false_eq_true, if_false] at htgt'
        exact absurd htgt' (by omega)
      | true =>
        simp only [if_true] at htgt'
        exact Or.inl rfl
    · subst hg
      rw [tlW_one] at htgt'
      cases dir' with
      | false =>
        simp only [Bool.false_eq_true, if_false] at htgt'
        refine Or.inr ?_
        show (((1 : Fin 2), (0 : ℤ) - tlW p q (1 : Fin 2)) : Fin 2 × ℤ) = ((1 : Fin 2), (p : ℤ))
        rw [tlW_one]
        simp
      | true =>
        simp only [if_true] at htgt'
        exact absurd htgt' (by omega)
  rcases hedge with hedge | hedge
  · -- the edge `(0,0)` is traversed by the first letter of the walk
    refine ⟨(((0 : Fin 2), (0 : ℤ)), true), ?_, ?_⟩
    · rw [decor_tlU_tlW]
      exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨⟨0, hp⟩, by simp⟩)
    · rw [mem_winTree]
      refine ⟨?_, ?_⟩
      · show ((0 : Fin 2), (0 : ℤ)) ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ))
        rw [← hedge]; exact hE''
      · have hmem : Bwit.dec (tlW p q) p' ∈
            decor (tlW p q) 0 (Bwit.newWord p') := by
          rw [Bwit.newWord_decor (tlW p q) p' (by rw [hw, hlv]; exact lsig_nil' (tlW p q))]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have hthis := hcl' _ hmem
        rw [Bwit.coverEdge_dec, hedge] at hthis
        show coverClassAt (treeGauge (tlW p q) 0 ((p : ℤ) * (q : ℤ))) (tlW p q)
          (((0 : Fin 2), (0 : ℤ))) = 1
        exact hthis
  · -- the edge `(1,p)` is traversed by the last letter of the walk
    refine ⟨(((1 : Fin 2), (p : ℤ)), true), ?_, ?_⟩
    · rw [decor_tlU_tlW]
      refine List.mem_append_right _ (List.mem_ofFn.mpr ⟨⟨q - 1, by omega⟩, ?_⟩)
      simp only [Prod.mk.injEq, true_and]
      have hcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ q)]; simp
      rw [hcast]; ring_nf; simp
    · rw [mem_winTree]
      refine ⟨?_, ?_⟩
      · show ((1 : Fin 2), (p : ℤ)) ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ))
        rw [← hedge]; exact hE''
      · have hmem : Bwit.dec (tlW p q) p' ∈
            decor (tlW p q) 0 (Bwit.newWord p') := by
          rw [Bwit.newWord_decor (tlW p q) p' (by rw [hw, hlv]; exact lsig_nil' (tlW p q))]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have hthis := hcl' _ hmem
        rw [Bwit.coverEdge_dec, hedge] at hthis
        show coverClassAt (treeGauge (tlW p q) 0 ((p : ℤ) * (q : ℤ))) (tlW p q)
          (((1 : Fin 2), (p : ℤ))) = 1
        exact hthis

/-! ## The gauge of the whole level graph -/

/-- The gauge of the band, extended off the band by the powers of a deck element `τ` of weight `1`.
Only the values on the band matter for the loop classes of the window edges, and outside the band the
weight requirement is met as soon as `cohom c τ = ofAdd 1`. -/
private noncomputable def bandExtend (p q : ℕ) (τ : FreeGroup (Fin 2))
    (Wt : ℤ → FreeGroup (Fin 2)) : ℤ → FreeGroup (Fin 2) :=
  fun i => if 0 ≤ i ∧ i ≤ (p : ℤ) * (q : ℤ) then Wt i else τ ^ i

private theorem bandExtend_of_mem {p q : ℕ} {τ : FreeGroup (Fin 2)}
    {Wt : ℤ → FreeGroup (Fin 2)} {i : ℤ} (h : 0 ≤ i ∧ i ≤ (p : ℤ) * (q : ℤ)) :
    bandExtend p q τ Wt i = Wt i := if_pos h

private theorem bandExtend_of_notMem {p q : ℕ} {τ : FreeGroup (Fin 2)}
    {Wt : ℤ → FreeGroup (Fin 2)} {i : ℤ} (h : ¬ (0 ≤ i ∧ i ≤ (p : ℤ) * (q : ℤ))) :
    bandExtend p q τ Wt i = τ ^ i := if_neg h

/-- **The loop classes of the window edges do not see the extension.** -/
private theorem coverClassAt_bandExtend {p q : ℕ} {τ : FreeGroup (Fin 2)}
    {Wt : ℤ → FreeGroup (Fin 2)} {e : Fin 2 × ℤ}
    (he : e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ))) :
    coverClassAt (bandExtend p q τ Wt) (tlW p q) e = coverClassAt Wt (tlW p q) e := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_winE.mp he
  have hA : bandExtend p q τ Wt e.2 = Wt e.2 := bandExtend_of_mem ⟨h1, h2⟩
  have hB : bandExtend p q τ Wt (e.2 + tlW p q e.1) = Wt (e.2 + tlW p q e.1) :=
    bandExtend_of_mem ⟨h3, h4⟩
  simp only [coverClassAt, gaugeMap_of, hA, hB]

/-! ## The target -/

theorem twoLetterWindowData (p q l : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hl : 1 ≤ l)
    (hcop : Nat.Coprime p q) :
    ∃ (c : Fin 2 → ℤ) (τ : FreeGroup (Fin 2)) (lo hi : ℤ) (Wt : ℤ → FreeGroup (Fin 2)),
      Work.OROneRel.cohom c (Work.OROneRel.tlU p q) = 1 ∧
      Work.OROneRel.cohom c τ = Multiplicative.ofAdd 1 ∧
      Wt 0 = 1 ∧ (∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i) ∧
      (∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
        Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE c lo hi) ∧
      (∀ k : ℤ, k ≠ 0 →
        ¬ (∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
            lo ≤ e.1.2 + k ∧ lo ≤ e.1.2 + c e.1.1 + k ∧
              e.1.2 + k ≤ hi ∧ e.1.2 + c e.1.1 + k ≤ hi)) ∧
      (∀ i : ℤ, lo ≤ i → i ≤ hi →
        ∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
          Work.OROneRel.coverEdge e ∈ Work.OROneRel.winTree Wt c lo hi) ∧
      (∃ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
        Work.OROneRel.coverEdge e ∈ Work.OROneRel.winTree Wt c lo hi) ∧
      (∀ x : FreeGroup (Work.OROneRel.winBeta Wt c lo hi),
        Work.OROneRel.winRho Wt c lo hi x ∈
            Subgroup.normalClosure ({Work.OROneRel.tlU p q ^ l} : Set (FreeGroup (Fin 2))) →
          x ∈ Subgroup.normalClosure
            ({Work.OROneRel.winRoot Wt c lo hi (Work.OROneRel.tlU p q) ^ l} :
              Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))) := by
  classical
  obtain ⟨τ, hτ⟩ := exists_coh_tau_tlW p q hp hq hcop
  set G : ℤ → FreeGroup (Fin 2) := treeGauge (tlW p q) 0 ((p : ℤ) * (q : ℤ)) with hG
  obtain ⟨hG0', hGcoh', hGtree'⟩ := treeGauge_band_facts p q hp hq hcop
  have hG0 : G 0 = 1 := hG0'
  have hGcoh : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      cohom (tlW p q) (G i) = Multiplicative.ofAdd i := hGcoh'
  have hGtree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ decor (tlW p q) 0 (wordOf (G i)),
        coverEdge e ∈ winTree G (tlW p q) 0 ((p : ℤ) * (q : ℤ)) := hGtree'
  -- the gauge of the whole level graph
  have hW0 : bandExtend p q τ G 0 = 1 := by
    rw [bandExtend_of_mem (p := p) (q := q) (τ := τ) (Wt := G) ⟨le_rfl, by positivity⟩]
    exact hG0
  have hWcoh : ∀ i : ℤ, cohom (tlW p q) (bandExtend p q τ G i) = Multiplicative.ofAdd i := by
    intro i
    by_cases hb : 0 ≤ i ∧ i ≤ (p : ℤ) * (q : ℤ)
    · rw [bandExtend_of_mem hb]; exact hGcoh i hb.1 hb.2
    · rw [bandExtend_of_notMem hb, map_zpow, hτ, ← ofAdd_zsmul]
      congr 1
      simp
  have hWtree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ decor (tlW p q) 0 (wordOf (bandExtend p q τ G i)),
        coverEdge e ∈ winTree (bandExtend p q τ G) (tlW p q) 0 ((p : ℤ) * (q : ℤ)) := by
    intro i hi0 hile e he
    have hb : 0 ≤ i ∧ i ≤ (p : ℤ) * (q : ℤ) := ⟨hi0, hile⟩
    rw [bandExtend_of_mem hb] at he
    have h1 := hGtree i hi0 hile e he
    rw [mem_winTree] at h1
    exact mem_winTree.mpr ⟨h1.1, by rw [coverClassAt_bandExtend (Wt := G) h1.1]; exact h1.2⟩
  have hWlast : ∃ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      coverEdge e ∈ winTree (bandExtend p q τ G) (tlW p q) 0 ((p : ℤ) * (q : ℤ)) := by
    obtain ⟨e, he, hte⟩ := bandTreeEdge_local p q hp hq
    refine ⟨e, he, ?_⟩
    rw [mem_winTree] at hte ⊢
    refine ⟨hte.1, ?_⟩
    rw [coverClassAt_bandExtend (Wt := G) hte.1]
    rw [hG]
    exact hte.2
  exact ⟨tlW p q, τ, 0, (p : ℤ) * (q : ℤ), bandExtend p q τ G, cohom_tlW_tlU p q, hτ, hW0,
    hWcoh, tlU_walk_mem_winE p q, tlU_walk_tight p q hp, hWtree, hWlast,
    twoLetterFreiheitssatz p q l hp hq hl hcop hW0 hWcoh (cohom_tlW_tlU p q) hτ
      (tlU_walk_mem_winE p q) (tlU_walk_tight p q hp) hWtree⟩

end Work.OROneRel
