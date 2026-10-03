import Mathlib
import Submission.Work.Peluse.UControl.levDatumStep

namespace Work.Peluse.UControl

theorem levAtomDirPoly {d j L : Nat} (hL : 1 ≤ L) {lc : Int}
    {N : Nat → Nat} {P : Nat → Nat → Finset Nat} {c : Nat → Nat → Nat}
    {X : Work.Peluse.UControl.HistData d L}
    {f0 : Fin L → Bool} (h : Work.Peluse.UControl.LevDInv d lc j L hL N P c X f0)
    {atoms : {s // s ∈ Work.Peluse.UControl.lvlSet N c L j hL} →
      MvPolynomial (Fin L) Int}
    (hLev : Work.Peluse.UControl.LevCube d (d - j) L
      (Work.Peluse.UControl.lvlSet N c L j hL) f0 atoms X)
    (s' : {s // s ∈ Work.Peluse.UControl.lvlSet N c L j hL}) :
    MvPolynomial.rename (Fin.val : Fin L → Nat) (atoms s') =
      Work.Peluse.UControl.dirPoly d lc P c j {(Work.Peluse.UControl.rawOf h s')} := by
  classical
  -- The history which is `true` exactly at `s'` and takes the value `f₀` off the level set.
  set hT : Fin L → Bool := fun i => if i = s'.1 then true else f0 i with hTdef
  -- `f₀` is `false` on the whole level set (with the raw index as witness).
  have hf0A : ∀ b : {s // s ∈ lvlSet N c L j hL}, f0 b.1 = false := by
    intro b
    have h' := h.f0false (rawOf h b) (rawOf_lt h b)
    rwa [rawOf_spec h b] at h'
  have hf0_s' : f0 s'.1 = false := hf0A s'
  have hT_mem : hT ∈ cubeSet L (lvlSet N c L j hL) f0 := by
    simp only [cubeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi
    have hi' : i ≠ s'.1 := fun he => hi (he ▸ s'.2)
    simp only [hTdef]
    simp [hi']
  have hT_ne : hT ≠ f0 := by
    intro hEq
    have h2 : hT s'.1 = f0 s'.1 := congrFun hEq s'.1
    simp only [hTdef] at h2
    simp [hf0_s'] at h2
  have hT_false : ∀ b : {s // s ∈ lvlSet N c L j hL}, b ≠ s' → hT b.1 = false := by
    intro b hbs
    have hne : (b.1 : Fin L) ≠ s'.1 := fun he => hbs (Subtype.ext he)
    rw [hTdef]
    simp only [hne, if_false]
    exact hf0A b
  have hT_self : hT s'.1 = true := by
    rw [hTdef]
    simp
  -- Restrict the level constraint of `LevCube` to the singleton history `hT`.
  have hlc := (hLev.2 hT hT_mem hT_ne).2
  have hcongr : ∀ b : {s // s ∈ lvlSet N c L j hL},
      (if hT b.1 then atoms b else 0) = if b = s' then atoms s' else 0 := by
    intro b
    by_cases hb : b = s'
    · subst hb
      simp [hT_self]
    · rw [hT_false b hb, if_neg hb]
      simp
  -- The atom sum of the singleton history is the single atom.
  have hatom : atomSum (lvlSet N c L j hL) atoms hT = atoms s' := by
    rw [atomSum]
    rw [Finset.sum_congr rfl (fun b _ => hcongr b)]
    rw [Finset.sum_ite_eq']
    simp
  -- The index set of the singleton history is the singleton of the raw index of `s'`.
  have hidx : idxSet N c L j hL hT = {rawOf h s'} := by
    ext s
    rw [mem_idxSet, Finset.mem_singleton]
    constructor
    · rintro ⟨hs, hh⟩
      have hxmem : ptFin c L j s hL ∈ lvlSet N c L j hL := mem_lvlSet.mpr ⟨s, hs, rfl⟩
      have hx : ptFin c L j s hL = s'.1 := by
        by_contra hne
        have h3 : hT (ptFin c L j s hL) = false :=
          hT_false ⟨ptFin c L j s hL, hxmem⟩ (fun he => hne (congrArg Subtype.val he))
        rw [h3] at hh
        exact Bool.false_ne_true hh
      exact ptFin_injective h hs (rawOf_lt h s') (by rw [hx, rawOf_spec h s'])
    · intro hs
      rw [hs]
      exact ⟨rawOf_lt h s', by rw [rawOf_spec h s']; exact hT_self⟩
  calc MvPolynomial.rename (Fin.val : Fin L → Nat) (atoms s')
      = MvPolynomial.rename (Fin.val : Fin L → Nat)
          (atomSum (lvlSet N c L j hL) atoms hT) := by rw [hatom]
    _ = MvPolynomial.rename (Fin.val : Fin L → Nat)
          ((X.Q (Sum.inr 0 : InitIdx d) hT).leadingCoeff) := by rw [hlc]
    _ = dirPoly d lc P c j (idxSet N c L j hL hT) := h.lc_eq hT hT_mem hT_ne
    _ = dirPoly d lc P c j {(rawOf h s')} := by rw [hidx]

end Work.Peluse.UControl
