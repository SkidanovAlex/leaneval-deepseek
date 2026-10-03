import Mathlib
import Submission.Work.Peluse.UControl.levAssemblyDefs
import Submission.Work.Peluse.UControl.levelCompareDefs

/-!
# The inverse coordinate map of a `LevDInv`-state

A `LevDInv`-state at level `j` carries a bijection
`{1,…,j} × [0,N i) → [0,L)`, `(i,s) ↦ c i s` (the fields `ccover` and `cinj`).  The terminal
comparison of the level chain (`levelCompareGen`) needs this map in the *inverse* direction: a point
of the datum's parameter box is a family `a : (j : Fin d) → Fin (N j) → ℤ`, and the corresponding
point of the window tower is `towerOf H L (fun k ↦ a (level of k) (raw index of k))`.

* `coordLvl h k` / `coordRaw h k` — the level and the raw index of the coordinate `k : Fin L`,
  extracted from `LevDInv.ccover` (a `Classical.choose`, hence computable only classically);
* `coordLvl_le` / `coordRaw_lt` / `coord_val` — the specifications;
* `coord_ptFin` — the crucial compatibility: on the *image* of the coordinate map the extracted
  pair is the original one (`cinj`);
* `levTowerOf h H a` — the tower point attached to the levels `≥ 1` of a box point `a` (the level
  `0` coordinate is not read, cf. `levTowerOf_towerIdx`): this is what the terminal comparison's
  constant term `β` is built from, and it must not depend on the level-`0` part (`hβ0`).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The level of the coordinate `k` (the `i` of the unique pair `(i,s)` with `c i s = k`). -/
def coordLvl {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) (k : Fin L) : ℕ :=
  Classical.choose (h.ccover k.1 k.2)

/-- The raw index of the coordinate `k`. -/
def coordRaw {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) (k : Fin L) : ℕ :=
  Classical.choose ((Classical.choose_spec (h.ccover k.1 k.2)).2.2)

lemma coordLvl_one_le {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) (k : Fin L) : 1 ≤ coordLvl h k :=
  (Classical.choose_spec (h.ccover k.1 k.2)).1

lemma coordLvl_le {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) (k : Fin L) : coordLvl h k ≤ j :=
  (Classical.choose_spec (h.ccover k.1 k.2)).2.1

lemma coordRaw_lt {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) (k : Fin L) : coordRaw h k < N (coordLvl h k) :=
  (Classical.choose_spec ((Classical.choose_spec (h.ccover k.1 k.2)).2.2)).1

lemma coord_val {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) (k : Fin L) :
    c (coordLvl h k) (coordRaw h k) = k.1 :=
  (Classical.choose_spec ((Classical.choose_spec (h.ccover k.1 k.2)).2.2)).2

/-- **The inverse coordinate map is the inverse of the coordinate map** in the sense that on a
coordinate `c i s` of a valid level the extracted pair is `(i, s)`. -/
lemma coord_ptFin {lc : ℤ} {j L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc j L hL N P c X f₀) {i s : ℕ} (hi1 : 1 ≤ i) (hij : i ≤ j)
    (hs : s < N i) :
    coordLvl h (ptFin c L i s hL) = i ∧ coordRaw h (ptFin c L i s hL) = s := by
  have hcb := h.cbound i hi1 hij s hs
  set k : Fin L := ptFin c L i s hL with hk
  have hkval : k.1 = c i s := by rw [hk, ptFin_val_of_lt hL hcb]
  have hspec := Classical.choose_spec (h.ccover k.1 k.2)
  have hcl : coordLvl h k = Classical.choose (h.ccover k.1 k.2) := rfl
  set i' := coordLvl h k with hi'def
  have hi'1 : 1 ≤ i' := hspec.1
  have hi'j : i' ≤ j := hspec.2.1
  have hlt : coordRaw h k < N i' := coordRaw_lt h k
  have hcv : c i' (coordRaw h k) = k.1 := coord_val h k
  have hci : c i' (coordRaw h k) = c i s := by rw [hcv, hkval]
  obtain ⟨hii, hss⟩ := h.cinj i' i (coordRaw h k) s hi'1 hi'j hi1 hij hlt hs hci
  exact ⟨hii, hss⟩

/-- **The tower point attached to the levels `≥ 1` of a box point.**  For a parameter family
`a : (j : Fin d) → Fin (N j) → ℤ` the coordinate `k : Fin L` of the state receives the value
`a (level of k) (raw index of k)`; since `LevDInv.ccover` always produces a level `≥ 1`, this never
reads the level-`0` part of `a`. -/
def levTowerOf {lc : ℤ} {L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc (d - 1) L hL N P c X f₀) (H : ℕ)
    (a : (jj : Fin d) → Fin (N jj.1) → ℤ) : WinTower H L :=
  towerOf H L fun k =>
    a ⟨coordLvl h k, by have := coordLvl_le h k; have := h.hj; omega⟩
      ⟨coordRaw h k, coordRaw_lt h k⟩

/-- The attaching family of `levTowerOf`, as a function of the coordinate: on a box point this is
the value read by `WinTower.param`. -/
lemma levTowerOf_apply {lc : ℤ} {L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc (d - 1) L hL N P c X f₀) (H : ℕ)
    (a : (jj : Fin d) → Fin (N jj.1) → ℤ)
    (ha : ∀ (j : Fin d) (s : Fin (N j.1)), -(H : ℤ) ≤ a j s ∧ a j s ≤ (H : ℤ)) (k : Fin L) :
    WinTower.param H L (levTowerOf h H a) k
      = a ⟨coordLvl h k, by have := coordLvl_le h k; have := h.hj; omega⟩
          ⟨coordRaw h k, coordRaw_lt h k⟩ :=
  congrFun (param_towerOf H L _ (fun k => ha _ _)) k

/-- **The tower point is recovered from the box point it maps to**: with
`a := levTowerIdx h H (k, t)` (whose levels `≥ 1` are `param t ∘ c`), the recovered tower point is
`t`.  This is what makes the terminal comparison's constant term `β` well defined. -/
lemma levTowerOf_towerIdx {lc : ℤ} {L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc (d - 1) L hL N P c X f₀) (H : ℕ)
    (p : Fin (2 * H + 1) × WinTower H L) :
    levTowerOf h H (levTowerIdx h H p) = p.2 := by
  have hfun : (fun k : Fin L => (levTowerIdx h H p) ⟨coordLvl h k, by
      have := coordLvl_le h k; have := h.hj; omega⟩ ⟨coordRaw h k, coordRaw_lt h k⟩)
      = WinTower.param H L p.2 := by
    funext k
    simp only [levTowerIdx]
    rw [dif_neg (by have := coordLvl_one_le h k; omega)]
    congr 1
    refine Fin.ext ?_
    exact coord_val h k
  show towerOf H L _ = p.2
  rw [hfun]
  exact towerOf_param H L p.2

/-- The level-`0` slot type of `levDatumOf` is `Fin (N 0) = Fin 1`. -/
lemma levDatumOf_S_zero {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {hsub : ∀ i, ∀ k, k < N (i + 1) → P i k ⊆ Finset.range (N i)}
    {hne : ∀ i, ∀ k, k < N (i + 1) → (P i k).Nonempty}
    {h : N 0 = 1} : (levDatumOf N P hsub hne).S 0 = Fin 1 := by
  show Fin (N 0) = Fin 1
  rw [h]

/-- **The window tower realises the datum's parameter box:** `levTowerIdx` maps
`Fin (2H+1) × WinTower H L` bijectively onto `D.parBox d H`. -/
theorem levTowerIdxProps {d : ℕ} {lc : ℤ} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {L : ℕ} {hL : 1 ≤ L} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc (d - 1) L hL N P c X f₀)
    (hsub : ∀ i, ∀ k, k < N (i + 1) → P i k ⊆ Finset.range (N i))
    (hne : ∀ i, ∀ k, k < N (i + 1) → (P i k).Nonempty)
    (H : ℕ) :
    (∀ p : Fin (2 * H + 1) × WinTower H L,
        levTowerIdx h H p ∈ (levDatumOf N P hsub hne).parBox d H) ∧
    (∀ a ∈ (levDatumOf N P hsub hne).parBox d H,
        ∃ p : Fin (2 * H + 1) × WinTower H L, levTowerIdx h H p = a) ∧
    Function.Injective (levTowerIdx h H) := by
  have hd0 : 0 < d := by have := h.hj; omega
  have hN0 : N 0 = 1 := h.N0
  have hs0 : (0 : ℕ) < N 0 := by rw [hN0]; norm_num
  constructor
  · -- membership: `boxVal` at level `0`, `WinTower.param` above
    intro p
    have hgoal : (levTowerIdx h H p : (levDatumOf N P hsub hne).Idx d)
        ∈ (levDatumOf N P hsub hne).parBox d H := by
      refine (IdxDatum.mem_parBox).mpr ?_
      intro j s
      by_cases hj : (j : ℕ) = 0
      · have hval : levTowerIdx h H p j s = IdxDatum.boxVal H p.1 := by
          simp only [levTowerIdx, dif_pos hj]
        rw [hval]
        exact IdxDatum.boxVal_mem H p.1
      · have hlt : c j.1 s.1 < L := h.cbound j.1 (by omega) (by have := j.2; omega) s.1 s.2
        have hval : levTowerIdx h H p j s
            = WinTower.param H L p.2 ⟨c j.1 s.1, hlt⟩ := by
          simp only [levTowerIdx, dif_neg hj]
        rw [hval]
        exact abs_le.mp (param_abs_le H L p.2 ⟨c j.1 s.1, hlt⟩)
    exact hgoal
  · constructor
    · -- surjectivity: the recovered tower point
      intro a ha
      have ha' : ∀ (j : Fin d) (s : Fin (N j.1)),
          -(H : ℤ) ≤ a j s ∧ a j s ≤ (H : ℤ) := (IdxDatum.mem_parBox).mp ha
      have ha0 : -(H : ℤ) ≤ a ⟨0, hd0⟩ ⟨0, hs0⟩ ∧ a ⟨0, hd0⟩ ⟨0, hs0⟩ ≤ (H : ℤ) :=
        ha' (⟨0, hd0⟩ : Fin d) ⟨0, hs0⟩
      set k : Fin (2 * H + 1) :=
        ⟨Int.toNat (a ⟨0, hd0⟩ ⟨0, hs0⟩ + (H : ℤ)), by omega⟩ with hk
      have hkval : IdxDatum.boxVal H k = a ⟨0, hd0⟩ ⟨0, hs0⟩ := by
        have hcast : ((k : ℕ) : ℤ) = a ⟨0, hd0⟩ ⟨0, hs0⟩ + (H : ℤ) := by
          rw [hk]
          show ((Int.toNat (a ⟨0, hd0⟩ ⟨0, hs0⟩ + (H : ℤ)) : ℕ) : ℤ) = _
          rw [Int.toNat_of_nonneg (by omega)]
        rw [IdxDatum.boxVal, hcast]
        ring
      refine ⟨(k, levTowerOf h H a), ?_⟩
      funext j s
      by_cases hj : (j : ℕ) = 0
      · have hj0 : j = ⟨0, hd0⟩ := Fin.ext hj
        subst hj0
        have hs : s = (⟨0, hs0⟩ : Fin (N 0)) := by
          refine Fin.ext ?_
          have h2 : s.1 < N 0 := s.2
          omega
        subst hs
        have h1 : levTowerIdx h H (k, levTowerOf h H a) ⟨0, hd0⟩ ⟨0, hs0⟩
            = IdxDatum.boxVal H k :=
          congrFun (levTowerIdx_zero h H (k, levTowerOf h H a) hd0) (⟨0, hs0⟩ : Fin (N 0))
        rw [h1, hkval]
      · have hlt : c j.1 s.1 < L := h.cbound j.1 (by omega) (by have := j.2; omega) s.1 s.2
        have h1 : levTowerIdx h H (k, levTowerOf h H a) j s
            = WinTower.param H L (levTowerOf h H a) ⟨c j.1 s.1, hlt⟩ := by
          simp only [levTowerIdx, dif_neg hj]
        rw [h1]
        refine (levTowerOf_apply h H a ha' ⟨c j.1 s.1, hlt⟩).trans ?_
        obtain ⟨hl, hr⟩ := coord_ptFin h (i := j.1) (s := s.1) (by omega)
          (by have := j.2; omega) s.2
        rw [ptFin_of_lt hL hlt] at hl hr
        have hsig : (⟨⟨coordLvl h ⟨c j.1 s.1, hlt⟩,
            by have := coordLvl_le h ⟨c j.1 s.1, hlt⟩; omega⟩,
            ⟨coordRaw h ⟨c j.1 s.1, hlt⟩, coordRaw_lt h ⟨c j.1 s.1, hlt⟩⟩⟩ :
            Sigma fun jj : Fin d => Fin (N jj.1)) = ⟨j, s⟩ := by
          refine Sigma.ext (Fin.ext hl) ?_
          exact (Fin.heq_ext_iff (k := N (coordLvl h ⟨c j.1 s.1, hlt⟩)) (l := N j.1)
            (by rw [hl])).mpr hr
        exact congrArg (fun p : Sigma fun jj : Fin d => Fin (N jj.1) => a p.1 p.2) hsig
    · -- injectivity: level `0` fixes `p.1`, the coordinates fix `p.2`
      intro p q hpq
      have h1 : p.1 = q.1 := by
        have hpt := congrFun (congrFun hpq (⟨0, hd0⟩ : Fin d)) (⟨0, hs0⟩ : Fin (N 0))
        have hp := congrFun (levTowerIdx_zero h H p hd0) (⟨0, hs0⟩ : Fin (N 0))
        have hq := congrFun (levTowerIdx_zero h H q hd0) (⟨0, hs0⟩ : Fin (N 0))
        have h3 : IdxDatum.boxVal H p.1 = IdxDatum.boxVal H q.1 :=
          hp.symm.trans (hpt.trans hq)
        refine Fin.ext ?_
        simp only [IdxDatum.boxVal] at h3
        omega
      have h2 : p.2 = q.2 := param_injective H L (by
        funext k'
        obtain ⟨i, hi1, hij, s, hs, hcs⟩ := h.ccover k'.1 k'.2
        have hlt : c i s < L := h.cbound i (by omega) (by omega) s hs
        have hpt := congrFun (congrFun hpq (⟨i, by omega⟩ : Fin d)) (⟨s, hs⟩ : Fin (N i))
        have h3 : WinTower.param H L p.2 ⟨c i s, hlt⟩
            = WinTower.param H L q.2 ⟨c i s, hlt⟩ := by
          have h3' := hpt
          simp only [levTowerIdx, dif_neg (by omega : ¬ ((i : ℕ) = 0))] at h3'
          exact h3'
        have hki : (⟨c i s, hlt⟩ : Fin L) = k' := Fin.ext hcs
        rw [← hki]
        exact h3)
      exact Prod.ext h1 h2

end

end Work.Peluse.UControl
