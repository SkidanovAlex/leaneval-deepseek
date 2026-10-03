import Mathlib
import Submission.Work.Peluse.UControl.levAtomDirPoly

/-!
# The level-chain invariant survives one round (assembled proof)

`Work.Peluse.UControl.levDInvStep` is the induction step of the level chain of Peluse's Lemma 4.8:
from a `LevDInv`-state at level `j`, a round (`LevCube` at level `j+1` with the round's steps, frozen
vector and atoms) and the round's attachment data, it produces a `LevDInv`-state at level `j + 1` for
the extended data `stepN`, `stepPAll`, `stepC`.

The proof splits into

* `lvstep_stepDataBasic` — the six *combinatorial* fields (`Psub`, `Pne`, `cbound`, `ccover`,
  `cinj`, `f0false`) of the level-`(j+1)` invariant, all of which are bookkeeping about the extended
  index data;
* `lvstep_lcEqCore` — the identity field: the renamed atom sum of a fresh history is the `dirPoly` at
  level `j+1`, obtained by reindexing the fresh coordinates against `Fin Nnew` and substituting the
  per-attachment identity `∑_{s' ∈ Pround s} rename Fin.val (atoms s') = dirPoly j (stepP s)` (which
  is `lvstep_proundSum`, using `levAtomDirPoly`: the atom of a level-`j` slot is `dirPoly` of its
  singleton index set).

The remaining fields (`hj`, `N0`, `Ntop`, `H_eq`, `deg`) are immediate from the hypotheses.
-/

namespace Work.Peluse.UControl

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-! ## Elementary rewrites for the extended data -/

/-- The composition `Fin.val ∘ Fin.castLE` is `Fin.val`, so the two renamings collapse. -/
lemma lvstep_rename_castLE_val {L Nnew : ℕ} (p : MvPolynomial (Fin L) ℤ) :
    MvPolynomial.rename (Fin.val : Fin (L + Nnew) → ℕ)
      (MvPolynomial.rename (Fin.castLE (Nat.le_add_right L Nnew)) p)
      = MvPolynomial.rename (Fin.val : Fin L → ℕ) p := by
  have hfun : (Fin.val : Fin (L + Nnew) → ℕ) ∘ (Fin.castLE (Nat.le_add_right L Nnew))
      = Fin.val := by
    funext x; rfl
  rw [MvPolynomial.rename_rename, hfun]

/-- `rawOf` is injective on the level-`j` slot set (the coordinate map is injective). -/
lemma lvstep_rawOf_injective {d j L : ℕ} {hL : 1 ≤ L} {lc : ℤ}
    {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ} {c : ℕ → ℕ → ℕ} {X : HistData d L}
    {f0 : Fin L → Bool} (h : LevDInv d lc j L hL N P c X f0) :
    Function.Injective (fun s' : {s // s ∈ lvlSet N c L j hL} => rawOf h s') := by
  intro a b hab
  have h1 : ptFin c L j (rawOf h a) hL = ptFin c L j (rawOf h b) hL := by
    rw [show rawOf h a = rawOf h b from hab]
  rw [rawOf_spec h a, rawOf_spec h b] at h1
  exact Subtype.ext h1

/-- At a level `j ≥ 1`, `dirPoly` is the sum of its values on the singletons. -/
lemma lvstep_dirPoly_eq_sum_singletons {d : ℕ} {lc : ℤ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {j : ℕ} (hj : 1 ≤ j) (v : Finset ℕ) :
    dirPoly d lc P c j v = ∑ x ∈ v, dirPoly d lc P c j {x} := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  exact dirPoly_succ_sum_singleton d lc P c m v

/-- `dirPoly` at level `j` only sees the data at levels `≤ j`, and `stepPAll`/`stepC` agree with
`P`/`c` there. -/
lemma lvstep_dirPoly_stepPAll_stepC {d j L Nnew : ℕ} {hL : 1 ≤ L} {lc : ℤ}
    {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ} {c : ℕ → ℕ → ℕ} {X : HistData d L}
    {f0 : Fin L → Bool} (h : LevDInv d lc j L hL N P c X f0)
    {A' : Finset (Fin (L + Nnew))} (hA' : A' = freshFin L Nnew)
    {Pround : {s // s ∈ A'} → Finset {s' // s' ∈ lvlSet N c L j hL}} (v : Finset ℕ) :
    dirPoly d lc (stepPAll h hA' Pround) (stepC c L j) j v = dirPoly d lc P c j v := by
  refine dirPoly_congr (fun i hi s => ?_) (fun i hi s => ?_) v
  · rw [stepPAll_of_ne h hA' Pround (by omega) s]
  · rw [stepC_of_ne (by omega) s]

/-! ## The per-attachment identity -/

/-- The sum of the renamed level-`j` atoms over one attachment `Pround k` of the round equals
`dirPoly` at level `j` of the raw index set `stepP k`. -/
lemma lvstep_proundSum {d j L Nnew : ℕ} (hL : 1 ≤ L) {lc : ℤ}
    {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ} {c : ℕ → ℕ → ℕ} {X : HistData d L}
    {f0 : Fin L → Bool} (h : LevDInv d lc j L hL N P c X f0)
    {A' : Finset (Fin (L + Nnew))} (hA' : A' = freshFin L Nnew)
    {atoms : {s // s ∈ lvlSet N c L j hL} → MvPolynomial (Fin L) ℤ}
    {Pround : {s // s ∈ A'} → Finset {s' // s' ∈ lvlSet N c L j hL}}
    (hAtoms : ∀ s' : {s // s ∈ lvlSet N c L j hL},
      MvPolynomial.rename (Fin.val : Fin L → ℕ) (atoms s') = dirPoly d lc P c j {(rawOf h s')})
    (k : Fin Nnew) :
    (∑ s' ∈ Pround ⟨freshPt L Nnew k,
        by rw [hA']; exact mem_freshFin.mpr (Nat.le_add_right L k.1)⟩,
      MvPolynomial.rename (Fin.val : Fin L → ℕ) (atoms s'))
      = dirPoly d lc P c j (stepP h hA' Pround k.1) := by
  classical
  set t : Finset {s' // s' ∈ lvlSet N c L j hL} :=
    Pround ⟨freshPt L Nnew k, by rw [hA']; exact mem_freshFin.mpr (Nat.le_add_right L k.1)⟩
    with ht
  have hstep : stepP h hA' Pround k.1 = t.image (fun s' => rawOf h s') := by
    rw [ht, stepP, dif_pos k.2]
    have harg : (⟨⟨L + k.1, by omega⟩,
        by rw [hA']; exact mem_freshFin.mpr (Nat.le_add_right L k.1)⟩ :
        {s : Fin (L + Nnew) // s ∈ A'})
        = ⟨freshPt L Nnew k, by rw [hA']; exact mem_freshFin.mpr (Nat.le_add_right L k.1)⟩ :=
      Subtype.ext (Fin.ext rfl)
    rw [harg]
  rw [hstep]
  rw [show (∑ s' ∈ t, MvPolynomial.rename (Fin.val : Fin L → ℕ) (atoms s'))
      = ∑ s' ∈ t, dirPoly d lc P c j {(rawOf h s')} from
    Finset.sum_congr rfl (fun s' _ => hAtoms s')]
  rw [← Finset.sum_image (f := fun x => dirPoly d lc P c j {x})
    (lvstep_rawOf_injective h).injOn]
  exact (lvstep_dirPoly_eq_sum_singletons h.hj _).symm

/-! ## The identity field -/

/-- The fresh coordinates of `Fin (L + Nnew)` indexed by `Fin Nnew`. -/
def lvstep_freshSubtypeEquiv (L Nnew : ℕ) (A' : Finset (Fin (L + Nnew)))
    (hA' : A' = freshFin L Nnew) : Fin Nnew ≃ {s : Fin (L + Nnew) // s ∈ A'} where
  toFun k := ⟨freshPt L Nnew k, by rw [hA']; exact mem_freshFin.mpr (Nat.le_add_right L k.1)⟩
  invFun s := ⟨s.1.1 - L, by
    have hs : s.1 ∈ freshFin L Nnew := by rw [← hA']; exact s.2
    have h1 : L ≤ s.1.1 := mem_freshFin.mp hs
    have h2 : s.1.1 < L + Nnew := s.1.2
    omega⟩
  left_inv k := by
    apply Fin.ext
    simp [freshPt]
  right_inv s := by
    apply Subtype.ext
    apply Fin.ext
    have hs : s.1 ∈ freshFin L Nnew := by rw [← hA']; exact s.2
    have h1 : L ≤ s.1.1 := mem_freshFin.mp hs
    simp [freshPt]
    omega

/-- **The `lc_eq` field of the level-`(j+1)` invariant**, given the per-attachment identity `hsum`:
the renamed atom sum of a history is the `dirPoly` at level `j + 1` of its fresh index set. -/
lemma lvstep_lcEqCore {d j L Nnew : ℕ} (hL : 1 ≤ L) (hL' : 1 ≤ L + Nnew) {lc : ℤ}
    {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ} {c : ℕ → ℕ → ℕ} {X : HistData d L}
    {f0 : Fin L → Bool} (h : LevDInv d lc j L hL N P c X f0)
    {A' : Finset (Fin (L + Nnew))} (hA' : A' = freshFin L Nnew)
    {atoms : {s // s ∈ lvlSet N c L j hL} → MvPolynomial (Fin L) ℤ}
    {Pround : {s // s ∈ A'} → Finset {s' // s' ∈ lvlSet N c L j hL}}
    {atoms' : {s // s ∈ A'} → MvPolynomial (Fin (L + Nnew)) ℤ}
    (hat : ∀ s, atoms' s = MvPolynomial.C ((d : ℤ) - (j : ℤ)) *
      ((∑ s' ∈ Pround s, MvPolynomial.rename (Fin.castLE (Nat.le_add_right L Nnew))
        (atoms s')) * MvPolynomial.X s.1))
    (hsum : ∀ k : Fin Nnew,
      (∑ s' ∈ Pround ⟨freshPt L Nnew k,
          by rw [hA']; exact mem_freshFin.mpr (Nat.le_add_right L k.1)⟩,
        MvPolynomial.rename (Fin.val : Fin L → ℕ) (atoms s'))
      = dirPoly d lc P c j (stepP h hA' Pround k.1))
    (h' : Fin (L + Nnew) → Bool) :
    MvPolynomial.rename (Fin.val : Fin (L + Nnew) → ℕ) (atomSum A' atoms' h')
      = dirPoly d lc (stepPAll h hA' Pround) (stepC c L j) (j + 1)
          (idxSet (stepN N Nnew j) (stepC c L j) (L + Nnew) (j + 1) hL' h') := by
  rw [idxSet_step hL' h']
  have hLHS : MvPolynomial.rename (Fin.val : Fin (L + Nnew) → ℕ) (atomSum A' atoms' h')
      = ∑ k : Fin Nnew, (if h' (freshPt L Nnew k) then
          MvPolynomial.C ((d : ℤ) - (j : ℤ)) *
            ((∑ s' ∈ Pround ⟨freshPt L Nnew k,
                by rw [hA']; exact mem_freshFin.mpr (Nat.le_add_right L k.1)⟩,
              MvPolynomial.rename (Fin.val : Fin L → ℕ) (atoms s'))
              * MvPolynomial.X (L + k.1)) else 0) := by
    rw [atomSum, map_sum]
    have h1 : (∑ s : {s // s ∈ A'}, MvPolynomial.rename (Fin.val : Fin (L + Nnew) → ℕ)
          (if h' s.1 then atoms' s else 0))
        = ∑ s : {s // s ∈ A'}, (if h' s.1 then
            MvPolynomial.rename (Fin.val : Fin (L + Nnew) → ℕ) (atoms' s) else 0) :=
      Finset.sum_congr rfl (fun s _ => by by_cases hh : h' s.1 <;> simp [hh])
    rw [h1]
    have h2 : (∑ s : {s // s ∈ A'}, (if h' s.1 then
          MvPolynomial.rename (Fin.val : Fin (L + Nnew) → ℕ) (atoms' s) else 0))
        = ∑ s : {s // s ∈ A'}, (if h' s.1 then
            MvPolynomial.C ((d : ℤ) - (j : ℤ)) *
              ((∑ s' ∈ Pround s, MvPolynomial.rename (Fin.val : Fin L → ℕ) (atoms s'))
                * MvPolynomial.X s.1.1) else 0) := by
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [hat s]
      split_ifs with hh
      · rw [map_mul, map_mul, map_sum, MvPolynomial.rename_C, MvPolynomial.rename_X]
        congr 1
        congr 1
        exact Finset.sum_congr rfl (fun s' _ => lvstep_rename_castLE_val (atoms s'))
      · simp
    rw [h2]
    rw [← Equiv.sum_comp (lvstep_freshSubtypeEquiv L Nnew A' hA')
      (fun s : {s // s ∈ A'} => (if h' s.1 then
            MvPolynomial.C ((d : ℤ) - (j : ℤ)) *
              ((∑ s' ∈ Pround s, MvPolynomial.rename (Fin.val : Fin L → ℕ) (atoms s'))
                * MvPolynomial.X s.1.1) else 0))]
    rfl
  have hRHS : dirPoly d lc (stepPAll h hA' Pround) (stepC c L j) (j + 1)
        (freshIdxSet L Nnew h')
      = ∑ k : Fin Nnew, (if h' (freshPt L Nnew k) then
          MvPolynomial.C ((d : ℤ) - (j : ℤ)) *
            (dirPoly d lc P c j (stepP h hA' Pround k.1) * MvPolynomial.X (L + k.1))
          else 0) := by
    rw [dirPoly_succ]
    rw [show (∑ s ∈ freshIdxSet L Nnew h',
        (MvPolynomial.C ((d : ℤ) - (j : ℤ)) *
          dirPoly d lc (stepPAll h hA' Pround) (stepC c L j) j (stepPAll h hA' Pround j s))
            * MvPolynomial.X ((stepC c L j) (j + 1) s))
        = ∑ s ∈ freshIdxSet L Nnew h',
          (MvPolynomial.C ((d : ℤ) - (j : ℤ)) *
            (dirPoly d lc P c j (stepP h hA' Pround s) * MvPolynomial.X (L + s))) from
      Finset.sum_congr rfl (fun s _ => by
        rw [stepPAll_self, stepC_self, lvstep_dirPoly_stepPAll_stepC h hA' _, mul_assoc])]
    rw [freshIdxSet]
    rw [Finset.sum_image (f := fun x : ℕ => MvPolynomial.C ((d : ℤ) - (j : ℤ)) *
          (dirPoly d lc P c j (stepP h hA' Pround x) * MvPolynomial.X (L + x)))
      (fun a _ b _ hab => Fin.val_injective hab)]
    rw [Finset.sum_filter]
  rw [hLHS, hRHS]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  split_ifs with hh
  · rw [hsum k]
  · rfl

/-! ## The combinatorial fields -/

/-- The six combinatorial fields of the level-`(j+1)` invariant for the extended data. -/
lemma lvstep_stepDataBasic {d j L Nnew : ℕ} (hL : 1 ≤ L) (hL' : 1 ≤ L + Nnew) {lc : ℤ}
    {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ} {c : ℕ → ℕ → ℕ} {X : HistData d L}
    {f0 : Fin L → Bool} (h : LevDInv d lc j L hL N P c X f0)
    {A' : Finset (Fin (L + Nnew))} (hA' : A' = freshFin L Nnew)
    {Pround : {s // s ∈ A'} → Finset {s' // s' ∈ lvlSet N c L j hL}}
    (hPne : ∀ s, (Pround s).Nonempty)
    {f0' : Fin (L + Nnew) → Bool} (hf0' : ∀ s ∈ A', f0' s = false) :
    (∀ i, i ≤ j + 1 → ∀ k, k < stepN N Nnew j (i + 1) →
        stepPAll h hA' Pround i k ⊆ Finset.range (stepN N Nnew j i)) ∧
    (∀ i, i ≤ j + 1 → ∀ k, k < stepN N Nnew j (i + 1) →
        (stepPAll h hA' Pround i k).Nonempty) ∧
    (∀ i, 1 ≤ i → i ≤ j + 1 → ∀ s, s < stepN N Nnew j i → stepC c L j i s < L + Nnew) ∧
    (∀ k, k < L + Nnew → ∃ i, 1 ≤ i ∧ i ≤ j + 1 ∧
        ∃ s, s < stepN N Nnew j i ∧ stepC c L j i s = k) ∧
    (∀ i i' s s', 1 ≤ i → i ≤ j + 1 → 1 ≤ i' → i' ≤ j + 1 →
        s < stepN N Nnew j i → s' < stepN N Nnew j i' →
        stepC c L j i s = stepC c L j i' s' → i = i' ∧ s = s') ∧
    (∀ s, s < stepN N Nnew j (j + 1) →
        f0' (ptFin (stepC c L j) (L + Nnew) (j + 1) s hL') = false) := by
  have hNj : stepN N Nnew j j = N j := stepN_of_ne (by omega)
  have hNs : ∀ i, i ≠ j + 1 → stepN N Nnew j i = N i := fun i hi => stepN_of_ne hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi k hk
    by_cases hij : i = j
    · subst hij
      rw [stepN_self] at hk
      rw [stepPAll_self, hNj]
      exact stepP_subset h hA' Pround k
    · by_cases hij' : i = j + 1
      · subst hij'
        exfalso
        rw [hNs (j + 1 + 1) (by omega)] at hk
        rw [h.Ntop (j + 1 + 1) (by omega)] at hk
        omega
      · rw [stepPAll_of_ne h hA' Pround hij, hNs i hij']
        exact h.Psub i (by omega) k (by rwa [hNs (i + 1) (by omega)] at hk)
  · intro i hi k hk
    by_cases hij : i = j
    · subst hij
      rw [stepN_self] at hk
      rw [stepPAll_self]
      exact stepP_nonempty h hA' Pround hPne hk
    · by_cases hij' : i = j + 1
      · subst hij'
        exfalso
        rw [hNs (j + 1 + 1) (by omega)] at hk
        rw [h.Ntop (j + 1 + 1) (by omega)] at hk
        omega
      · rw [stepPAll_of_ne h hA' Pround hij]
        exact h.Pne i (by omega) k (by rwa [hNs (i + 1) (by omega)] at hk)
  · intro i hi1 hi2 s hs
    by_cases hij' : i = j + 1
    · subst hij'
      rw [stepC_self]
      have hs' : s < Nnew := by rwa [stepN_self] at hs
      omega
    · rw [stepC_of_ne hij', hNs i hij'] at *
      exact lt_of_lt_of_le (h.cbound i hi1 (by omega) s hs) (Nat.le_add_right L Nnew)
  · intro k hk
    by_cases hkL : k < L
    · obtain ⟨i, hi1, hi2, s, hs, hcs⟩ := h.ccover k hkL
      refine ⟨i, hi1, by omega, s, ?_, ?_⟩
      · rwa [hNs i (by omega)]
      · rw [stepC_of_ne (by omega)]; exact hcs
    · refine ⟨j + 1, by omega, le_refl _, k - L, ?_, ?_⟩
      · rw [stepN_self]; omega
      · rw [stepC_self]; omega
  · intro i i' s s' hi1 hi2 hi1' hi2' hs hs' heq
    by_cases hij' : i = j + 1
    · subst hij'
      rw [stepC_self] at heq
      by_cases hi'j' : i' = j + 1
      · subst hi'j'
        rw [stepC_self] at heq
        exact ⟨rfl, by omega⟩
      · exfalso
        rw [stepC_of_ne hi'j'] at heq
        have hs'L : s' < N i' := by rwa [hNs i' hi'j'] at hs'
        have hlt := h.cbound i' hi1' (by omega) s' hs'L
        omega
    · rw [stepC_of_ne hij'] at heq
      have hsN : s < N i := by rwa [hNs i hij'] at hs
      by_cases hi'j' : i' = j + 1
      · subst hi'j'
        exfalso
        rw [stepC_self] at heq
        have hlt := h.cbound i hi1 (by omega) s hsN
        omega
      · rw [stepC_of_ne hi'j'] at heq
        have hs'N : s' < N i' := by rwa [hNs i' hi'j'] at hs'
        exact h.cinj i i' s s' hi1 (by omega) hi1' (by omega) hsN hs'N heq
  · intro s hs
    rw [stepN_self] at hs
    rw [ptFin_step hL' hs]
    exact hf0' _ (by rw [hA']; exact mem_freshFin.mpr (Nat.le_add_right L s))

/-! ## The induction step -/

theorem levDInvStep {d j L Nnew : Nat} (hL : 1 ≤ L) (hL' : 1 ≤ L + Nnew) {lc : Int}
    {N : Nat -> Nat} {P : Nat -> Nat -> Finset Nat} {c : Nat -> Nat -> Nat}
    {X : Work.Peluse.UControl.HistData d L} {f0 : Fin L -> Bool}
    (h : Work.Peluse.UControl.LevDInv d lc j L hL N P c X f0)
    {A' : Finset (Fin (L + Nnew))} {f0' : Fin (L + Nnew) -> Bool}
    (hA' : A' = Work.Peluse.UControl.freshFin L Nnew)
    (hf0' : ∀ s ∈ A', f0' s = false)
    {atoms : {s : Fin L // s ∈ Work.Peluse.UControl.lvlSet N c L j hL} ->
      MvPolynomial (Fin L) Int}
    (hLev : Work.Peluse.UControl.LevCube d (d - j) L
      (Work.Peluse.UControl.lvlSet N c L j hL) f0 atoms X)
    {Pround : {s : Fin (L + Nnew) // s ∈ A'} ->
      Finset {s' : Fin L // s' ∈ Work.Peluse.UControl.lvlSet N c L j hL}}
    (hPne : ∀ s, (Pround s).Nonempty)
    {atoms' : {s : Fin (L + Nnew) // s ∈ A'} -> MvPolynomial (Fin (L + Nnew)) Int}
    (hat : ∀ s, atoms' s = MvPolynomial.C ((d : Int) - (j : Int)) *
      ((∑ s' ∈ Pround s, MvPolynomial.rename (Fin.castLE (Nat.le_add_right L Nnew))
        (atoms s')) * MvPolynomial.X s.1))
    {X' : Work.Peluse.UControl.HistData d (L + Nnew)}
    (hcube : Work.Peluse.UControl.LevCube d (d - j - 1) (L + Nnew) A' f0' atoms' X') :
    Work.Peluse.UControl.LevDInv d lc (j + 1) (L + Nnew) hL'
      (Work.Peluse.UControl.stepN N Nnew j)
      (Work.Peluse.UControl.stepPAll h hA' Pround)
      (Work.Peluse.UControl.stepC c L j) X' f0' := by
  obtain ⟨hPsub, hPne', hcb, hcc, hcinj, hf0false⟩ :=
    lvstep_stepDataBasic hL hL' h hA' hPne hf0'
  have hN0 : stepN N Nnew j 0 = N 0 := stepN_of_ne (by omega)
  have hAtoms : ∀ s' : {s // s ∈ lvlSet N c L j hL},
      MvPolynomial.rename (Fin.val : Fin L → ℕ) (atoms s') =
        dirPoly d lc P c j {(rawOf h s')} :=
    fun s' => levAtomDirPoly hL h hLev s'
  have hsum : ∀ k : Fin Nnew,
      (∑ s' ∈ Pround ⟨freshPt L Nnew k,
          by rw [hA']; exact mem_freshFin.mpr (Nat.le_add_right L k.1)⟩,
        MvPolynomial.rename (Fin.val : Fin L → ℕ) (atoms s'))
      = dirPoly d lc P c j (stepP h hA' Pround k.1) :=
    fun k => lvstep_proundSum hL h hA' hAtoms k
  refine ⟨by omega, ?_, ?_, hPsub, hPne', hcb, hcc, hcinj, hf0false, ?_, ?_, ?_⟩
  · rw [hN0, h.N0]
  · intro i hi
    have h1 : stepN N Nnew j i = N i := stepN_of_ne (by omega)
    rw [h1, h.Ntop i (by omega)]
  · rw [lvlSet_step hA' hL']; exact hcube.1
  · intro hg hmem hne
    rw [lvlSet_step hA' hL'] at hmem
    rw [(hcube.2 hg hmem hne).1]
    exact Nat.sub_sub d j 1
  · intro hg hmem hne
    rw [lvlSet_step hA' hL'] at hmem
    rw [(hcube.2 hg hmem hne).2]
    exact lvstep_lcEqCore hL hL' h hA' hat hsum hg

end

end Work.Peluse.UControl
