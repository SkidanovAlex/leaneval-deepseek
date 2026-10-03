-- **Namespaced copy** (`Work.OROneRel.NC`) of a colleague's module, made so that the
-- window-data pipeline can be imported *together with* the Freiheitssatz pipeline:
-- `Work.OROneRel.decor_replicate_true` (declared in `Submission.Work.OROneRel.decor_wordOf_zpow_of`)
-- clashes with the declaration of the same name in
-- `Submission.Work.OROneRel.twoLetter_cycle_decor`, so no module can import both
-- `exists_window_support_data_cycred` and `bandFreiheitssatz_of_windowData`.  The copy lives in
-- the namespace `Work.OROneRel.NC`, where `decor_replicate_true` is `Work.OROneRel.NC.decor_replicate_true`
-- and no longer clashes.  Nothing here is new mathematics.
import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.band_one_lift
import Submission.Work.OROneRel.exists_treeGauge
import Submission.Work.OROneRel.levels_ncard_two
import Submission.Work.OROneRel.ne_one_of_not_isProperPower
import Submission.Work.OROneRel.treeGauge_edge_of_unique_witness
import Submission.Work.OROneRel.reach_winWindowData_two_nc
import Submission.Work.OROneRel.decor_wordOf_zpow_of_nc
import Submission.Work.OROneRel.exists_killing_weight_structure

namespace Work.OROneRel.NC
universe u

variable {α : Type u}
set_option linter.unusedVariables false

/-- The level `0` of the walk lies in the window. -/
private theorem zero_mem_band {c : α → ℤ} {u : FreeGroup α} {lo hi : ℤ}
    (hu1 : u ≠ 1)
    (hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi) :
    lo ≤ 0 ∧ 0 ≤ hi := by
  obtain ⟨a, b, L, hL⟩ : ∃ a b L, wordOf u = (a, b) :: L := by
    cases hw : wordOf u with
    | nil =>
      exfalso
      have : FreeGroup.mk (wordOf u) = 1 := by rw [hw]; rfl
      rw [mk_wordOf] at this
      exact hu1 this
    | cons q L => obtain ⟨a, b⟩ := q; exact ⟨a, b, L, rfl⟩
  set e : α × ℤ := (a, if b then 0 else 0 - c a) with he
  set q : (α × ℤ) × Bool := (e, b) with hq
  have hqmem : q ∈ decor c 0 (wordOf u) := by
    rw [hL, hq, he, decor_cons']
    exact List.mem_cons_self ..
  have hE : e ∈ winE c lo hi := hwin q hqmem
  obtain ⟨h1, h2, h3, h4⟩ := mem_winE.mp hE
  have hsrc : coverSrc c q = 0 := by
    rw [hq, he]
    cases b <;> simp only [coverSrc, Bool.false_eq_true, if_false, if_true] <;> ring
  have hcase : coverSrc c q = e.2 ∨ coverSrc c q = e.2 + c e.1 := by
    rw [hq]
    cases b <;> simp [coverSrc]
  rw [hsrc] at hcase
  constructor
  · rcases hcase with h | h <;> omega
  · rcases hcase with h | h <;> omega

/-- The first letter of the walk with non-zero weight: its source is the level `0`. -/
private theorem exists_decor_src_zero (c : α → ℤ) :
    ∀ (L : List (α × Bool)), (∃ p ∈ L, c p.1 ≠ 0) →
      ∃ q ∈ decor c 0 L, coverSrc c q = 0 ∧ c q.1.1 ≠ 0 := by
  intro L
  induction L with
  | nil => intro h; obtain ⟨p, hp, _⟩ := h; simp at hp
  | cons p L ih =>
    intro h
    obtain ⟨a, b⟩ := p
    by_cases hca : c a = 0
    · have hrest : ∃ p ∈ L, c p.1 ≠ 0 := by
        obtain ⟨q, hq, hq'⟩ := h
        rw [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact absurd hca hq'
        · exact ⟨q, hq, hq'⟩
      obtain ⟨q, hq, hsrc, hq'⟩ := ih hrest
      refine ⟨q, ?_, hsrc, hq'⟩
      rw [decor_cons']
      refine List.mem_cons_of_mem _ ?_
      have : (0 : ℤ) + linc c (a, b) = 0 := by
        cases b <;> simp [linc, hca]
      rw [this]
      exact hq
    · refine ⟨((a, if b then 0 else 0 - c a), b), ?_, ?_, ?_⟩
      · rw [decor_cons']; exact List.mem_cons_self ..
      · cases b <;> simp only [coverSrc, Bool.false_eq_true, if_false, if_true] <;> ring
      · simpa using hca

/-- The gauge agreeing with `G` on the window and with the powers of `τ` outside. -/
private noncomputable def extGauge (lo hi : ℤ) (G : ℤ → FreeGroup α) (τ : FreeGroup α) :
    ℤ → FreeGroup α :=
  fun i => if lo ≤ i ∧ i ≤ hi then G i else τ ^ i

private theorem extGauge_of_mem {lo hi : ℤ} {G : ℤ → FreeGroup α} {τ : FreeGroup α} {i : ℤ}
    (h : lo ≤ i ∧ i ≤ hi) : extGauge lo hi G τ i = G i := if_pos h

private theorem extGauge_of_notMem {lo hi : ℤ} {G : ℤ → FreeGroup α} {τ : FreeGroup α} {i : ℤ}
    (h : ¬ (lo ≤ i ∧ i ≤ hi)) : extGauge lo hi G τ i = τ ^ i := if_neg h

private theorem mem_winTree_extGauge {lo hi : ℤ} {G : ℤ → FreeGroup α} {τ : FreeGroup α} {c : α → ℤ}
    {e : α × ℤ} (he : e ∈ winE c lo hi) :
    e ∈ winTree (extGauge lo hi G τ) c lo hi ↔ e ∈ winTree G c lo hi := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_winE.mp he
  have hA : extGauge lo hi G τ e.2 = G e.2 := extGauge_of_mem ⟨h1, h2⟩
  have hB : extGauge lo hi G τ (e.2 + c e.1) = G (e.2 + c e.1) := extGauge_of_mem ⟨h3, h4⟩
  have hcc : coverClassAt (extGauge lo hi G τ) c e = coverClassAt G c e := by
    simp only [coverClassAt, gaugeMap_of, hA, hB]
  simp only [mem_winTree, he, true_and, hcc]

private theorem coverTgt_eq_coverSrc_add (c : α → ℤ) (q : (α × ℤ) × Bool) :
    coverTgt c q = coverSrc c q + (if q.2 then c q.1.1 else -c q.1.1) := by
  obtain ⟨⟨a, i⟩, b⟩ := q
  cases b <;> simp [coverTgt, coverSrc]

private theorem Bwit_tgt_eq (c : α → ℤ) (lv : ℤ) (g : α) (b : Bool) (v : List (α × Bool)) :
    Bwit.tgt c ⟨lv, g, b, v⟩ = lv + (if b then c g else -c g) := by
  cases b <;> rfl

end Work.OROneRel.NC

namespace Work.OROneRel.NC
universe u
variable {α : Type u}
set_option linter.unusedVariables false

/-- **The window data in the case where some letter carries the weight `1`.** -/
private theorem windowData_of_gaugeLetter {α : Type u} [Fintype α] [DecidableEq α]
    (u : FreeGroup α) (c : α → ℤ) (z : α)
    (hz : c z = 1) (hzR : z ∈ relatorLetters u) (hcu : cohom c u = 1)
    (hu1 : u ≠ 1) (hsup : ∀ x : α, x ∉ relatorLetters u → c x = 0) :
    ∃ (lo hi : ℤ) (Wt : ℤ → FreeGroup α),
      lo < hi ∧ Wt 0 = 1 ∧ (∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i) ∧
      (∀ i : ℤ, lo ≤ i → i ≤ hi →
        ∀ q ∈ decor c 0 (wordOf (Wt i)), coverEdge q ∈ winTree Wt c lo hi) ∧
      (∀ x : α, ∃ i : ℤ, (x, i) ∈ winE c lo hi) ∧
      (∃ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winTree Wt c lo hi) ∧
      (∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi) ∧
      (∀ k : ℤ, k ≠ 0 → ¬ (∀ p ∈ decor c 0 (wordOf u),
        lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧ p.1.2 + k ≤ hi ∧
          p.1.2 + c p.1.1 + k ≤ hi)) := by
  classical
  have hnd : ∃ x : α, x ∈ relatorLetters u ∧ c x ≠ 0 := ⟨z, hzR, by rw [hz]; norm_num⟩
  obtain ⟨lo, hi, hlt, hwin0, hone0⟩ := band_one_lift c u hu1 hcu hnd
  have hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hwin0 p hp
    rw [mem_winE]
    exact ⟨h1, h3, h2, h4⟩
  have h0mem : lo ≤ 0 ∧ 0 ≤ hi := zero_mem_band hu1 hwin
  have hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ winE c lo hi := by
    intro x
    by_cases hx : c x = 0
    · refine ⟨lo, ?_⟩
      rw [mem_winE]
      refine ⟨le_refl lo, ?_, ?_, ?_⟩
      · exact le_trans h0mem.1 h0mem.2
      · rw [hx]; simp
      · rw [hx]; simp only [add_zero]; exact le_trans h0mem.1 h0mem.2
    · have hxR : x ∈ relatorLetters u := by
        by_contra h; exact hx (hsup x h)
      obtain ⟨b, hb⟩ : ∃ b : Bool, (x, b) ∈ wordOf u := hxR
      obtain ⟨l, hl⟩ := exists_mem_decor_of_mem c 0 (wordOf u) x b hb
      exact ⟨l, hwin _ hl⟩
  refine ⟨lo, hi, fun i => FreeGroup.of z ^ i, hlt, zpow_zero _, ?_, ?_, hcov, ?_, hwin, hone0⟩
  · intro i
    rw [map_zpow, cohom_of, hz]
    simpa using (Int.ofAdd_mul (1 : ℤ) i).symm
  · intro i hi1 hi2 q hq
    rw [decor_wordOf_zpow_of c z i] at hq
    by_cases h0i : 0 ≤ i
    · rw [if_pos h0i] at hq
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      rw [List.mem_range] at hj
      have hji : (j : ℤ) < i := by
        have hcast : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg h0i
        have := Int.ofNat_lt.mpr hj
        omega
      rw [mem_winTree]
      constructor
      · rw [mem_winE]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [coverEdge] <;> rw [hz] <;> omega
      · simp only [coverEdge, coverClassAt, gaugeMap_of]
        rw [hz]
        have key : (FreeGroup.of z) ^ ((j : ℤ) * 1) * FreeGroup.of z *
            ((FreeGroup.of z) ^ ((j : ℤ) * 1 + 1))⁻¹ = 1 := by
          rw [mul_one]
          group
        exact key
    · rw [if_neg h0i] at hq
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      rw [List.mem_range] at hj
      have hji : (j : ℤ) + 1 ≤ -i := by
        have hcast : (((-i).toNat : ℕ) : ℤ) = -i := Int.toNat_of_nonneg (by omega)
        have := Int.ofNat_lt.mpr hj
        omega
      rw [mem_winTree]
      constructor
      · rw [mem_winE]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [coverEdge] <;> rw [hz] <;> omega
      · simp only [coverEdge, coverClassAt, gaugeMap_of]
        rw [hz]
        have key : (FreeGroup.of z) ^ (-(((j : ℤ) + 1) * 1)) * FreeGroup.of z *
            ((FreeGroup.of z) ^ (-(((j : ℤ) + 1) * 1) + 1))⁻¹ = 1 := by
          rw [mul_one]
          group
        exact key
  · obtain ⟨b, hb⟩ : ∃ b : Bool, (z, b) ∈ wordOf u := hzR
    obtain ⟨l, hl⟩ := exists_mem_decor_of_mem c 0 (wordOf u) z b hb
    refine ⟨((z, l), b), hl, ?_⟩
    rw [mem_winTree]
    refine ⟨hwin _ hl, ?_⟩
    simp only [coverEdge, coverClassAt, gaugeMap_of]
    rw [hz]
    have key : (FreeGroup.of z) ^ l * FreeGroup.of z * ((FreeGroup.of z) ^ (l + 1))⁻¹ = 1 := by
      group
    exact key

end Work.OROneRel.NC

namespace Work.OROneRel.NC
universe u
variable {α : Type u}
set_option linter.unusedVariables false

/-- **The window data in the case where the two weights of the walk are distinct up to sign.** -/
private theorem windowData_of_tree {α : Type u} [Fintype α] [DecidableEq α]
    (u : FreeGroup α) (c : α → ℤ) (τ : FreeGroup α) (x0 y0 : α) (cx cy : ℤ)
    (hcu : cohom c u = 1) (hτ : cohom c τ = Multiplicative.ofAdd 1)
    (hu1 : u ≠ 1) (hbad : ∀ x : α, x ∈ relatorLetters u → eps x u ≠ 0)
    (hsup2 : ∀ z : α, z ≠ x0 → z ≠ y0 → c z = 0)
    (hx0R : x0 ∈ relatorLetters u) (hy0R : y0 ∈ relatorLetters u)
    (hcx0 : c x0 = cx) (hcy0 : c y0 = cy) (hcxne : cx ≠ 0) (hcyne : cy ≠ 0)
    (hne1 : c x0 ≠ c y0) (hne2 : c x0 ≠ - c y0)
    (hbez : ∃ p q : ℤ, p * cx + q * cy = 1) :
    ∃ (lo hi : ℤ) (Wt : ℤ → FreeGroup α),
      lo < hi ∧ Wt 0 = 1 ∧ (∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i) ∧
      (∀ i : ℤ, lo ≤ i → i ≤ hi →
        ∀ q ∈ decor c 0 (wordOf (Wt i)), coverEdge q ∈ winTree Wt c lo hi) ∧
      (∀ x : α, ∃ i : ℤ, (x, i) ∈ winE c lo hi) ∧
      (∃ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winTree Wt c lo hi) ∧
      (∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi) ∧
      (∀ k : ℤ, k ≠ 0 → ¬ (∀ p ∈ decor c 0 (wordOf u),
        lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧ p.1.2 + k ≤ hi ∧
          p.1.2 + c p.1.1 + k ≤ hi)) := by
  classical
  have hnd : ∃ x : α, x ∈ relatorLetters u ∧ c x ≠ 0 := ⟨x0, hx0R, by rw [hcx0]; exact hcxne⟩
  obtain ⟨lo, hi, hlt, hwin0, hone0⟩ := band_one_lift c u hu1 hcu hnd
  have hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hwin0 p hp
    rw [mem_winE]
    exact ⟨h1, h3, h2, h4⟩
  have h0mem : lo ≤ 0 ∧ 0 ≤ hi := zero_mem_band hu1 hwin
  have hmov : ∀ z : α, c z ≠ 0 → z = x0 ∨ z = y0 := by
    intro z hz
    by_contra h
    push Not at h
    exact hz (hsup2 z h.1 h.2)
  have hsup : ∀ x : α, x ∉ relatorLetters u → c x = 0 := by
    intro x hx
    exact hsup2 x (fun h => hx (h ▸ hx0R)) (fun h => hx (h ▸ hy0R))
  have hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ winE c lo hi := by
    intro x
    by_cases hx : c x = 0
    · refine ⟨lo, ?_⟩
      rw [mem_winE]
      refine ⟨le_refl lo, ?_, ?_, ?_⟩
      · exact le_trans h0mem.1 h0mem.2
      · rw [hx]; simp
      · rw [hx]; simp only [add_zero]; exact le_trans h0mem.1 h0mem.2
    · rcases hmov x hx with h | h
      · obtain ⟨b, hb⟩ : ∃ b : Bool, (x, b) ∈ wordOf u := h ▸ hx0R
        obtain ⟨l, hl⟩ := exists_mem_decor_of_mem c 0 (wordOf u) x b hb
        exact ⟨l, hwin _ hl⟩
      · obtain ⟨b, hb⟩ : ∃ b : Bool, (x, b) ∈ wordOf u := h ▸ hy0R
        obtain ⟨l, hl⟩ := exists_mem_decor_of_mem c 0 (wordOf u) x b hb
        exact ⟨l, hwin _ hl⟩
  have hbez' : ∃ p q : ℤ, p * c x0 + q * c y0 = 1 := by
    obtain ⟨p, q, hpq⟩ := hbez
    exact ⟨p, q, by rw [hcx0, hcy0]; exact hpq⟩
  have hreach := reach_winWindowData_two c u x0 y0 lo hi hwin hone0 hbad hsup2 hcu
    (by rw [hcx0]; exact hcxne) (by rw [hcy0]; exact hcyne) hx0R hy0R hbez'
  have hG0 : treeGauge c lo hi 0 = 1 := by
    have h := (Inv_all c lo hi (NW c lo hi) le_rfl).1
    simp only [treeGauge, h, Option.getD_some]
    exact FreeGroup.one_eq_mk.symm
  have hGcoh : ∀ i : ℤ, lo ≤ i → i ≤ hi → cohom c (treeGauge c lo hi i) = Multiplicative.ofAdd i := by
    intro i hi1 hi2
    have hass := assigned_of_window c lo hi hreach hi1 hi2
    obtain ⟨L, hL⟩ := Option.ne_none_iff_exists'.mp hass
    have hinv := (Inv_all c lo hi (NW c lo hi) le_rfl).2 i L hL
    rw [treeGauge_of hL le_rfl, cohom_mk, hinv.1]
  have hGtree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ q ∈ decor c 0 (wordOf (treeGauge c lo hi i)),
        coverEdge q ∈ winTree (treeGauge c lo hi) c lo hi := by
    intro i hi1 hi2 q hq
    have hass := assigned_of_window c lo hi hreach hi1 hi2
    obtain ⟨L, hL⟩ := Option.ne_none_iff_exists'.mp hass
    have hinv := (Inv_all c lo hi (NW c lo hi) le_rfl).2 i L hL
    obtain ⟨hlsig, hred, hE, -, hcl⟩ := hinv
    rw [treeGauge_of hL le_rfl, wordOf_mk_of_isReduced hred] at hq
    exact mem_winTree.mpr ⟨hE q hq, hcl q hq⟩
  have hlast : ∃ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winTree (treeGauge c lo hi) c lo hi := by
    obtain ⟨b0, hb0⟩ : ∃ b : Bool, (x0, b) ∈ wordOf u := hx0R
    have hwalkne : ∃ p ∈ wordOf u, c p.1 ≠ 0 := ⟨(x0, b0), hb0, by rw [hcx0]; exact hcxne⟩
    obtain ⟨q, hq, hsrc, hqne⟩ := exists_decor_src_zero c (wordOf u) hwalkne
    have hedge : Bwit.edge c ⟨0, q.1.1, q.2, []⟩ = coverEdge q := by
      rw [← hsrc]
      exact Bwit.edge_mk_coverSrc c q []
    have hE : Bwit.edge c ⟨0, q.1.1, q.2, []⟩ ∈ winE c lo hi := by
      rw [hedge]; exact hwin q hq
    have htm : Bwit.tgt c ⟨0, q.1.1, q.2, []⟩ = (if q.2 then c q.1.1 else -c q.1.1) := by
      rw [Bwit_tgt_eq]; simp
    have hT : Bwit.tgt c ⟨0, q.1.1, q.2, []⟩ ≠ 0 := by
      rw [htm]
      cases hb : q.2
      · simp only [Bool.false_eq_true, if_false]
        intro h; exact hqne (neg_eq_zero.mp h)
      · simp only [if_true]
        exact hqne
    have hM : (if q.2 then c q.1.1 else -c q.1.1) ≠ 0 := htm ▸ hT
    have hgne : c q.1.1 ≠ 0 := by
      intro h0
      apply hM
      cases hb : q.2 <;> simp [hb, h0]
    have hgmem : q.1.1 = x0 ∨ q.1.1 = y0 := hmov _ hgne
    have hinj : ∀ z z' : α, (z = x0 ∨ z = y0) → (z' = x0 ∨ z' = y0) → c z = c z' → z = z' := by
      rintro z z' (rfl | rfl) (rfl | rfl) h
      · rfl
      · exact absurd h hne1
      · exact absurd h.symm hne1
      · rfl
    have hno : ∀ z z' : α, (z = x0 ∨ z = y0) → (z' = x0 ∨ z' = y0) → c z = -c z' → False := by
      rintro z z' (rfl | rfl) (rfl | rfl) h
      · exact hcxne (by linarith [h, hcx0])
      · exact hne2 h
      · exact hne2 (by linarith [h])
      · exact hcyne (by linarith [h, hcy0])
    have huniq : ∀ p' : Bwit α, Bwit.edge c p' ∈ winE c lo hi → p'.lv = 0 → p'.word = [] →
        Bwit.tgt c p' = Bwit.tgt c ⟨0, q.1.1, q.2, []⟩ → p' = ⟨0, q.1.1, q.2, []⟩ := by
      intro p' _ hlv hw htg
      obtain ⟨lv', g', b', w'⟩ := p'
      simp only at hlv hw
      subst hlv
      subst hw
      simp only [Bwit_tgt_eq, zero_add] at htg
      have hg : (if b' then c g' else -c g') = (if q.2 then c q.1.1 else -c q.1.1) := htg
      have hg'mem : g' = x0 ∨ g' = y0 := by
        have hg'ne : c g' ≠ 0 := by
          intro h0
          apply hM
          rw [← hg, h0]
          cases b' <;> simp
        exact hmov g' hg'ne
      cases hb : q.2 <;> cases hb' : b' <;> simp only [hb, hb', Bool.false_eq_true,
        if_true, if_false, neg_inj] at hg
      · have hgg := hinj g' q.1.1 hg'mem hgmem hg
        simp [hgg]
      · exfalso
        exact hno g' q.1.1 hg'mem hgmem (by linarith [hg])
      · exfalso
        exact hno g' q.1.1 hg'mem hgmem (by linarith [hg])
      · have hgg := hinj g' q.1.1 hg'mem hgmem hg
        simp [hgg]
    have hcl := treeGauge_edge_of_unique_witness c lo hi q.1.1 q.2 hE hT huniq
    exact ⟨q, hq, mem_winTree.mpr ⟨hwin q hq, by rw [← hedge]; exact hcl⟩⟩
  refine ⟨lo, hi, extGauge lo hi (treeGauge c lo hi) τ, hlt, ?_, ?_, ?_, hcov, ?_, hwin, hone0⟩
  · rw [extGauge_of_mem ⟨h0mem.1, h0mem.2⟩, hG0]
  · intro i
    by_cases hmem : lo ≤ i ∧ i ≤ hi
    · rw [extGauge_of_mem hmem]; exact hGcoh i hmem.1 hmem.2
    · rw [extGauge_of_notMem hmem, map_zpow, hτ]
      simpa using (Int.ofAdd_mul (1 : ℤ) i).symm
  · intro i hi1 hi2 q hq
    have hq' : q ∈ decor c 0 (wordOf (treeGauge c lo hi i)) := by
      rw [show extGauge lo hi (treeGauge c lo hi) τ i = treeGauge c lo hi i from
        extGauge_of_mem ⟨hi1, hi2⟩] at hq
      exact hq
    have hG := hGtree i hi1 hi2 q hq'
    exact (mem_winTree_extGauge (G := treeGauge c lo hi) (τ := τ)
      (mem_winTree.mp hG).1).mpr hG
  · obtain ⟨p, hp, hptree⟩ := hlast
    exact ⟨p, hp, (mem_winTree_extGauge (G := treeGauge c lo hi) (τ := τ) (hwin p hp)).mpr hptree⟩

end Work.OROneRel.NC

namespace Work.OROneRel.NC
universe u
variable {α : Type u}
set_option linter.unusedVariables false

theorem exists_winWindowData {α : Type u} [Fintype α] [DecidableEq α] (u : FreeGroup α)
    (hu : ¬ Work.OROneRel.IsProperPower u) (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (hbad : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u → Work.OROneRel.eps x u ≠ 0) :
    ∃ (c : α → ℤ) (τ : FreeGroup α) (lo hi : ℤ) (Wt : ℤ → FreeGroup α),
      Function.Surjective (Work.OROneRel.cohom c) ∧ Work.OROneRel.cohom c u = 1 ∧
      Work.OROneRel.cohom c τ = Multiplicative.ofAdd 1 ∧
      Wt 0 = 1 ∧ (∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i) ∧
      lo < hi ∧
      (∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
        Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi) ∧
      (∀ k : ℤ, k ≠ 0 →
        ¬ (∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
            lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧
              p.1.2 + k ≤ hi ∧ p.1.2 + c p.1.1 + k ≤ hi)) ∧
      (∀ i : ℤ, lo ≤ i → i ≤ hi →
        ∀ q ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
          Work.OROneRel.coverEdge q ∈ Work.OROneRel.winTree Wt c lo hi) ∧
      (∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi) ∧
      (∃ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
        Work.OROneRel.coverEdge p ∈ Work.OROneRel.winTree Wt c lo hi) := by
  classical
  obtain ⟨c, x0, y0, cx, cy, τ, bezp, bezq, hx0R, hy0R, hx0y0, hcxne, hcyne, hsurj, hcu, hτ,
    hcx0, hcy0, hsup2, hsum, hbez, hdisj⟩ :=
    exists_killing_weight_structure u hn hu hbad
  have hu1 : u ≠ 1 := ne_one_of_not_isProperPower hu
  have hsupR : ∀ x : α, x ∉ relatorLetters u → c x = 0 := by
    intro x hx
    exact hsup2 x (fun h => hx (h ▸ hx0R)) (fun h => hx (h ▸ hy0R))
  have hgen : ∃ l : List ({x : α // x ∈ relatorLetters u} × ℤ),
      (l.map (fun p => p.2 * c p.1.1)).sum = 1 :=
    ⟨[(⟨x0, hx0R⟩, bezp), (⟨y0, hy0R⟩, bezq)], by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [hcx0, hcy0]
      exact hbez⟩
  rcases hdisj with ⟨z, hz1⟩ | ⟨hne1, hne2⟩
  · have hzR : z ∈ relatorLetters u := by
      by_contra h
      have h1 : c z = 0 := hsup2 z (fun hx => h (hx ▸ hx0R)) (fun hy => h (hy ▸ hy0R))
      rw [h1] at hz1
      exact one_ne_zero hz1.symm
    obtain ⟨lo, hi, Wt, hlt, hW0, hcoh, htree, hcov, hlast, hwin, hone⟩ :=
      windowData_of_gaugeLetter u c z hz1 hzR hcu hu1 hsupR
    exact ⟨c, τ, lo, hi, Wt, hsurj, hcu, hτ, hW0, hcoh, hlt, hwin, hone, htree, hcov, hlast⟩
  · obtain ⟨lo, hi, Wt, hlt, hW0, hcoh, htree, hcov, hlast, hwin, hone⟩ :=
      windowData_of_tree u c τ x0 y0 cx cy hcu hτ hu1 hbad hsup2 hx0R hy0R hcx0 hcy0 hcxne
        hcyne hne1 hne2 (by exact ⟨bezp, bezq, hbez⟩)
    exact ⟨c, τ, lo, hi, Wt, hsurj, hcu, hτ, hW0, hcoh, hlt, hwin, hone, htree, hcov, hlast⟩

end Work.OROneRel.NC
