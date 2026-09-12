import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false
open Finset

namespace Commons.Combinatorics.Fin

-- ======================================================================
-- Generic "rank" function for a depth-valued map D : Fin n → ℕ.
-- x precedes y when it sits in a deeper level (larger D), ties broken by
-- the natural order.
-- ======================================================================

/-- `fin_before D x y`: x comes strictly before y when elements are ordered by
descending `D`, ties broken by the natural order. -/
private def fin_before {n : ℕ} (D : Fin n → ℕ) (x y : Fin n) : Prop :=
  D y < D x ∨ (D y = D x ∧ y < x)

private noncomputable def fin_beforeSet {n : ℕ} (D : Fin n → ℕ) (x : Fin n) : Finset (Fin n) := by
  classical
  exact (Finset.univ : Finset (Fin n)).filter (fun y : Fin n => fin_before D y x)

/-- number of elements strictly before `x` in the shell order -/
private noncomputable def fin_rank {n : ℕ} (D : Fin n → ℕ) (x : Fin n) : ℕ := (fin_beforeSet D x).card

private lemma fin_before_irrefl {n : ℕ} (D : Fin n → ℕ) (x : Fin n) : ¬ fin_before D x x := by
  intro h
  rcases h with h1 | h2
  · exact (lt_irrefl (D x)) h1
  · exact (lt_irrefl x) h2.2

private lemma fin_before_trans {n : ℕ} (D : Fin n → ℕ) {x y z : Fin n}
    (hxy : fin_before D x y) (hyz : fin_before D y z) : fin_before D x z := by
  rcases hxy with hxy1 | hxy2
  · rcases hyz with hyz1 | hyz2
    · left; omega
    · left; omega
  · rcases hyz with hyz1 | hyz2
    · left; omega
    · right
      constructor
      · omega
      · exact lt_trans hyz2.2 hxy2.2

private lemma fin_before_total {n : ℕ} (D : Fin n → ℕ) {x y : Fin n} (hxy : x ≠ y) :
    fin_before D x y ∨ fin_before D y x := by
  rcases lt_trichotomy (D x) (D y) with hlt | heq | hgt
  · right; left; exact hlt
  · by_cases hxylt : x < y
    · right; right; constructor <;> assumption
    · left; right; constructor
      · exact heq.symm
      · exact lt_of_le_of_ne (le_of_not_gt hxylt) (Ne.symm hxy)
  · left; left; exact hgt

private lemma fin_rank_lt {n : ℕ} (D : Fin n → ℕ) (x : Fin n) : fin_rank D x < n := by
  classical
  have hnot : x ∉ fin_beforeSet D x := by
    intro h
    rw [fin_beforeSet] at h
    exact fin_before_irrefl D x (mem_filter.mp h).2
  have hsub : fin_beforeSet D x ⊂ (Finset.univ : Finset (Fin n)) := by
    rw [ssubset_iff_subset_ne]
    constructor
    · intro y hy
      rw [fin_beforeSet] at hy
      exact mem_univ y
    · intro hEq
      have : x ∈ fin_beforeSet D x := by simpa [hEq]
      exact hnot this
  have hcardlt : (fin_beforeSet D x).card < (Finset.univ : Finset (Fin n)).card := card_lt_card hsub
  rw [card_univ, Fintype.card_fin] at hcardlt
  simpa [fin_rank] using hcardlt

private lemma fin_rank_strictMono {n : ℕ} (D : Fin n → ℕ) {x y : Fin n}
    (hxy : fin_before D x y) : fin_rank D x < fin_rank D y := by
  classical
  have hsub : fin_beforeSet D x ⊆ fin_beforeSet D y := by
    intro z hz
    rw [fin_beforeSet] at hz
    have hzx : fin_before D z x := (mem_filter.mp hz).2
    rw [fin_beforeSet]
    exact mem_filter.mpr ⟨by simp, fin_before_trans D hzx hxy⟩
  have hxBy : x ∈ fin_beforeSet D y := by
    rw [fin_beforeSet]
    exact mem_filter.mpr ⟨by simp, hxy⟩
  have hxBn : x ∉ fin_beforeSet D x := by
    intro h
    rw [fin_beforeSet] at h
    exact fin_before_irrefl D x (mem_filter.mp h).2
  have hsub2 : insert x (fin_beforeSet D x) ⊆ fin_beforeSet D y := by
    intro z hz
    rw [mem_insert] at hz
    rcases hz with rfl | hzA
    · exact hxBy
    · exact hsub hzA
  have hcardle : (insert x (fin_beforeSet D x)).card ≤ (fin_beforeSet D y).card := card_le_card hsub2
  have hinsertcard : (insert x (fin_beforeSet D x)).card = (fin_beforeSet D x).card + 1 :=
    card_insert_of_notMem hxBn
  change (fin_beforeSet D x).card < (fin_beforeSet D y).card
  omega

private lemma fin_rank_injective {n : ℕ} (D : Fin n → ℕ) : Function.Injective (fun x : Fin n => fin_rank D x) := by
  intro x y h
  change fin_rank D x = fin_rank D y at h
  by_contra hxy
  rcases fin_before_total D hxy with hlt | hlt
  · have hltpos : fin_rank D x < fin_rank D y := fin_rank_strictMono D hlt
    omega
  · have hltpos : fin_rank D y < fin_rank D x := fin_rank_strictMono D hlt
    omega

/-- the position map (inverse of the permutation we build) -/
private noncomputable def fin_rankFin {n : ℕ} (D : Fin n → ℕ) : Fin n → Fin n :=
  fun x => ⟨fin_rank D x, fin_rank_lt D x⟩

private lemma fin_rankFin_injective {n : ℕ} (D : Fin n → ℕ) : Function.Injective (fin_rankFin D) := by
  intro x y h
  apply fin_rank_injective D
  have : (fin_rankFin D x : ℕ) = (fin_rankFin D y : ℕ) := congrArg (fun z : Fin n => (z : ℕ)) h
  simpa [fin_rankFin] using this

private lemma fin_rankFin_surjective {n : ℕ} (D : Fin n → ℕ) : Function.Surjective (fin_rankFin D) := by
  exact (Finite.injective_iff_surjective.mp (fin_rankFin_injective D))

-- ======================================================================
-- Depth in a nested chain of subsets of Fin n.
-- ======================================================================

/-- levels (indices in `Fin (n+1)`) containing `x` -/
private noncomputable def chainMem {n : ℕ} (f : Fin (n + 1) → Finset (Fin n)) (x : Fin n) :
    Finset (Fin (n + 1)) :=
  (Finset.univ : Finset (Fin (n + 1))).filter (fun j : Fin (n + 1) => x ∈ f j)

/-- number of chain levels containing `x` -/
private noncomputable def chainDepth {n : ℕ} (f : Fin (n + 1) → Finset (Fin n)) (x : Fin n) : ℕ :=
  (chainMem f x).card

private def belowExcl {n : ℕ} (j : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  (Finset.univ : Finset (Fin (n + 1))).filter (fun k : Fin (n + 1) => (k : ℕ) ≤ (j : ℕ) ∧ k ≠ j)

private lemma belowExcl_card (n : ℕ) (j : Fin (n + 1)) : (belowExcl j).card = j.val := by
  classical
  have hEq : belowExcl j = (Finset.Iic j).erase j := by
    apply Finset.ext
    intro k
    constructor
    · intro hk
      rw [belowExcl] at hk
      rcases (mem_filter.mp hk) with ⟨_, ⟨hk1, hk2⟩⟩
      rw [mem_erase]
      exact ⟨hk2, by simpa using (mem_Iic.mpr hk1)⟩
    · intro hk
      rw [mem_erase] at hk
      rcases hk with ⟨hkne, hkIic⟩
      rw [belowExcl]
      refine (mem_filter.mpr ⟨by simp, ?_⟩)
      exact ⟨by simpa using (mem_Iic.mp hkIic), hkne⟩
  rw [hEq]
  have hcardIic : (Finset.Iic j).card = j.val + 1 := by simp
  rw [card_erase_of_mem, hcardIic]
  · omega
  · exact mem_Iic.mpr (le_refl j)

/-- `x ∈ f j` iff at least `j.val+1` levels contain `x`. -/
private lemma chainDepth_mem_iff {n : ℕ} (f : Fin (n + 1) → Finset (Fin n))
    (hnest : ∀ j k : Fin (n + 1), (j : ℕ) ≤ (k : ℕ) → f k ⊆ f j)
    (x : Fin n) (j : Fin (n + 1)) :
    x ∈ f j ↔ j.val + 1 ≤ chainDepth f x := by
  classical
  constructor
  · intro hx
    have hIicSub : Finset.Iic j ⊆ chainMem f x := by
      intro k hk
      have hkj : (k : ℕ) ≤ (j : ℕ) := by simpa using (mem_Iic.mp hk)
      have hkx : x ∈ f k := (hnest k j hkj) hx
      exact (mem_filter.mpr ⟨by simp, hkx⟩)
    have hle1 : (Finset.Iic j).card ≤ (chainMem f x).card := card_le_card hIicSub
    simpa [chainDepth, chainMem] using hle1
  · intro hd
    by_contra hxj
    have hle : chainDepth f x ≤ j.val := by
      have hsub : chainMem f x ⊆ belowExcl j := by
        intro k hk
        rw [chainMem] at hk
        have hkx : x ∈ f k := (mem_filter.mp hk).2
        have hkjval : ¬ (j : ℕ) < (k : ℕ) := by
          intro hlt
          have : x ∈ f j := (hnest j k (le_of_lt hlt)) hkx
          exact hxj this
        have hkj : (k : ℕ) ≤ (j : ℕ) := le_of_not_gt hkjval
        have hkne : k ≠ j := by
          intro hkeq
          subst k
          exact hxj hkx
        rw [belowExcl]
        exact (mem_filter.mpr ⟨by simp, ⟨hkj, hkne⟩⟩)
      have hcard := belowExcl_card n j
      exact le_trans (card_le_card hsub) (le_of_eq hcard)
    rw [chainDepth] at hd hle
    omega

/-- elements at chain-depth at least `k` -/
private noncomputable def levelGE {n : ℕ} (D : Fin n → ℕ) (k : ℕ) : Finset (Fin n) := by
  classical
  exact (Finset.univ : Finset (Fin n)).filter (fun y : Fin n => k ≤ D y)

-- ======================================================================
-- Main theorem
-- ======================================================================

theorem exists_perm_prefix_chain {n t : ℕ} (ht : t ≤ n)
    (f : Fin (n + 1) → Finset (Fin n))
    (hcard : ∀ j : Fin (n + 1), (f j).card = t / 2 ^ (j : ℕ))
    (hnest : ∀ j k : Fin (n + 1), (j : ℕ) ≤ (k : ℕ) → f k ⊆ f j) :
    ∃ σ : Equiv.Perm (Fin n), ∀ j : Fin (n + 1),
      ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => (i : ℕ) < t / 2 ^ (j : ℕ))).image
        (fun x : Fin n => σ x) = f j := by
  classical
  let c : ℕ → ℕ := fun j => t / 2 ^ j
  let D : Fin n → ℕ := chainDepth f
  have hmemD : ∀ (x : Fin n) (j : Fin (n + 1)), x ∈ f j ↔ j.val + 1 ≤ D x := by
    intro x j
    simpa [D] using chainDepth_mem_iff f hnest x j
  have hmem_le_c : ∀ (x : Fin n) (j : Fin (n + 1)), x ∈ f j → fin_rank D x < c (j.val) := by
    intro x j hx
    have hxB : x ∉ fin_beforeSet D x := by
      intro h
      rw [fin_beforeSet] at h
      exact fin_before_irrefl D x (mem_filter.mp h).2
    have hxG : x ∈ levelGE D (D x) := by
      rw [levelGE]
      exact mem_filter.mpr ⟨by simp, le_rfl⟩
    have hsub : insert x (fin_beforeSet D x) ⊆ levelGE D (D x) := by
      intro z hz
      rw [mem_insert] at hz
      rcases hz with rfl | hzB
      · exact hxG
      · rw [fin_beforeSet] at hzB
        have hbz : fin_before D z x := (mem_filter.mp hzB).2
        rw [levelGE]
        exact mem_filter.mpr ⟨by simp, by
          rcases hbz with hbz1 | hbz2
          · exact le_of_lt hbz1
          · exact le_of_eq hbz2.1⟩
    have hcard1 : (insert x (fin_beforeSet D x)).card ≤ (levelGE D (D x)).card := card_le_card hsub
    have hcard2 : (fin_beforeSet D x).card + 1 ≤ (levelGE D (D x)).card := by
      rw [card_insert_of_notMem hxB] at hcard1
      exact hcard1
    have hsubG : levelGE D (D x) ⊆ f j := by
      intro y hy
      rw [levelGE] at hy
      have hDy : D x ≤ D y := (mem_filter.mp hy).2
      have hDxj : j.val + 1 ≤ D x := (hmemD x j).1 hx
      have hDyj : j.val + 1 ≤ D y := le_trans hDxj hDy
      exact (hmemD y j).2 hDyj
    have hcard3 : (levelGE D (D x)).card ≤ (f j).card := card_le_card hsubG
    have hcard4 : (f j).card = c (j.val) := by
      dsimp [c]
      simpa using hcard j
    have hposle : fin_rank D x + 1 ≤ c (j.val) := by
      calc
        fin_rank D x + 1 = (fin_beforeSet D x).card + 1 := by simp [fin_rank]
        _ ≤ (levelGE D (D x)).card := hcard2
        _ ≤ (f j).card := hcard3
        _ = c (j.val) := hcard4
    omega
  have hc_le_rank : ∀ (x : Fin n) (j : Fin (n + 1)), x ∉ f j → c (j.val) ≤ fin_rank D x := by
    intro x j hx
    have hDxj : D x ≤ j.val := by
      have hnot : ¬ j.val + 1 ≤ D x := by
        intro hh
        exact hx ((hmemD x j).2 hh)
      omega
    have hsub : f j ⊆ fin_beforeSet D x := by
      intro y hy
      have hDy : j.val + 1 ≤ D y := (hmemD y j).1 hy
      rw [fin_beforeSet]
      exact mem_filter.mpr ⟨by simp, Or.inl (by omega)⟩
    calc
      c (j.val) = (f j).card := by
        dsimp [c]
        exact (hcard j).symm
      _ ≤ (fin_beforeSet D x).card := card_le_card hsub
      _ = fin_rank D x := by simp [fin_rank]
  have hposiff : ∀ (x : Fin n) (j : Fin (n + 1)), x ∈ f j ↔ fin_rank D x < c (j.val) := by
    intro x j
    constructor
    · exact hmem_le_c x j
    · intro hp
      by_contra hx
      have hle : c (j.val) ≤ fin_rank D x := hc_le_rank x j hx
      omega
  let posF : Fin n → Fin n := fin_rankFin D
  have hpinj : Function.Injective posF := by
    dsimp [posF]
    exact fin_rankFin_injective D
  have hpsurj : Function.Surjective posF := by
    dsimp [posF]
    exact fin_rankFin_surjective D
  let e : Fin n ≃ Fin n := Equiv.ofBijective posF ⟨hpinj, hpsurj⟩
  let σ : Equiv.Perm (Fin n) := e.symm
  have hpre : ∀ (j : Fin (n + 1)) (y : Fin n),
      y ∈ ((Finset.univ : Finset (Fin n)).filter
          (fun i : Fin n => (i : ℕ) < t / 2 ^ (j : ℕ))).image (fun x : Fin n => σ x)
        ↔ fin_rank D y < c (j.val) := by
    intro j y
    constructor
    · intro hy
      rcases mem_image.mp hy with ⟨i, hi, hσi⟩
      have hic : (i : ℕ) < c (j.val) := by
        rw [mem_filter] at hi
        simpa [c] using hi.2
      have hei : e y = i := by
        have h1 := congrArg e hσi
        rw [Equiv.apply_symm_apply] at h1
        exact h1.symm
      have hposy : fin_rank D y < c (j.val) := by
        -- e y = posF y, whose value is fin_rank D y
        have hyeq : (e y : ℕ) = fin_rank D y := by
          change (posF y : ℕ) = fin_rank D y
          simp [posF, fin_rankFin]
        have hval : (e y : ℕ) = (i : ℕ) := congrArg (fun z : Fin n => (z : ℕ)) hei
        rw [← hyeq, hval]
        exact hic
      exact hposy
    · intro hpy
      let i : Fin n := ⟨fin_rank D y, fin_rank_lt D y⟩
      have hi_mem : i ∈ (Finset.univ : Finset (Fin n)).filter
          (fun i : Fin n => (i : ℕ) < t / 2 ^ (j : ℕ)) := by
        rw [mem_filter]
        refine ⟨by simp, ?_⟩
        dsimp [i]
        simpa [c] using hpy
      have hi_posF : i = posF y := by
        dsimp [i, posF]
        rfl
      have hσ : σ i = y := by
        dsimp [σ]
        rw [hi_posF]
        have hpe : posF y = e y := rfl
        rw [hpe]
        exact Equiv.symm_apply_apply e y
      exact mem_image.mpr ⟨i, hi_mem, hσ⟩
  refine ⟨σ, ?_⟩
  intro j
  ext y
  rw [hpre j y]
  exact (hposiff y j).symm

end Commons.Combinatorics.Fin