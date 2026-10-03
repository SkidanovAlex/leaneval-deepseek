import Mathlib
import Submission.Work.Peluse.UControl.dirPolyEvalDir

/-!
# The data of the terminal comparison: the slot bijection and the evaluation of `coeff 1`

The terminal comparison `levelCompareGen` consumes, for the terminal state `X` of the level chain
(a `LevCube`-state of degree `1` on the level-`(dd-1)` slot set),

* `islot : (X.toSym).S.ι ≃ Fin (Fintype.card (D.I (dd-1)))` — the slot bijection, whose defining
  property is that the `idxSet` of the slot (the raw indices at which the history is `true`) is the
  underlying set of the corresponding `D.I (dd-1)` element (`levSlotEquivExists`); the *frozen*
  vector `f₀` is `false` on the level-`(dd-1)` coordinates (`LevDInv.f0false`), which is what makes
  the index set nonempty for every live slot.
* the identification of the linear coefficient of the slot with the datum's direction
  (`levCoeffOneEval`), which is `LevDInv.lc_eq` evaluated through `dirPolyEvalDir`: the bridge from
  the direction polynomial `dirPoly` (built in `MvPolynomial ℕ ℤ`) to the datum's `dir`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **The slot bijection of the terminal comparison.**  The live slots of the terminal state are
the nonempty subsets of the level-`(dd-1)` coordinates, read through `idxSet`. -/
theorem levSlotEquivExists {dd L : ℕ} {lc : ℤ} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {hL : 1 ≤ L} {X : HistData dd L} {f₀ : Fin L → Bool}
    {A : Finset (Fin L)} {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ}
    (h : LevDInv dd lc (dd - 1) L hL N P c X f₀)
    (hsub : ∀ i, ∀ k, k < N (i + 1) → P i k ⊆ Finset.range (N i))
    (hne : ∀ i, ∀ k, k < N (i + 1) → (P i k).Nonempty)
    (hY : LevCube dd 1 L A f₀ atoms X) (hA : A = lvlSet N c L (dd - 1) hL) :
    ∃ e : (X.toSym).S.ι ≃ Fin (Fintype.card ((levDatumOf N P hsub hne).I (dd - 1))),
      ∀ i : (X.toSym).S.ι,
        (((Fintype.equivFin ((levDatumOf N P hsub hne).I (dd - 1))).symm (e i)).val.image
          (fun s => s.1)) = idxSet N c L (dd - 1) hL i.1.2 := by
  have hsub' : ∀ h' : Fin L → Bool, idxSet N c L (dd - 1) hL h' ⊆ Finset.range (N (dd - 1)) :=
    fun h' => idxSet_subset N c L (dd - 1) hL h'
  have hvalInj : Function.Injective
      ((fun s : (levDatumOf N P hsub hne).S (dd - 1) => s.1)) :=
    fun a b hab => Fin.ext hab
  -- the index set of a live slot is nonempty: `f₀` is `false` on the level-`(dd-1)` slots
  have hneIdx : ∀ i : (X.toSym).S.ι, (idxSet N c L (dd - 1) hL i.1.2).Nonempty := by
    intro i
    have hmemH : i.1 ∈ LevH dd L A f₀ := by rw [← hY.1]; exact i.2
    obtain ⟨-, hicube, hine⟩ := mem_LevH.mp hmemH
    have hoff : ∀ x : Fin L, x ∉ A → i.1.2 x = f₀ x := (Finset.mem_filter.mp hicube).2
    have hex : ∃ s ∈ A, i.1.2 s ≠ f₀ s := by
      by_contra hcon
      push_neg at hcon
      exact hine (funext fun x => by
        by_cases hx : x ∈ A
        · exact hcon x hx
        · exact hoff x hx)
    obtain ⟨s, hsA, hsne⟩ := hex
    rw [hA] at hsA
    obtain ⟨r, hr, hpr⟩ := mem_lvlSet.mp hsA
    rw [← hpr, h.f0false r hr] at hsne
    refine ⟨r, mem_idxSet.mpr ⟨hr, ?_⟩⟩
    cases hh : i.1.2 (ptFin c L (dd - 1) r hL) <;> simp_all
  -- the map from the live slots to the index sets
  set ψ : (X.toSym).S.ι → (levDatumOf N P hsub hne).I (dd - 1) :=
    fun i => ⟨(idxSet N c L (dd - 1) hL i.1.2).attach.image
        (fun r : {r // r ∈ idxSet N c L (dd - 1) hL i.1.2} =>
          (⟨r.1, Finset.mem_range.mp (hsub' i.1.2 r.2)⟩ :
            (levDatumOf N P hsub hne).S (dd - 1))),
      Finset.Nonempty.image (Finset.attach_nonempty_iff.mpr (hneIdx i)) _⟩ with hψ
  have hψval : ∀ i : (X.toSym).S.ι,
      (ψ i).val.image (fun s => s.1) = idxSet N c L (dd - 1) hL i.1.2 := by
    intro i
    simp only [hψ]
    ext s
    constructor
    · intro hs
      rw [Finset.mem_image] at hs
      obtain ⟨a, ha, has⟩ := hs
      rw [Finset.mem_image] at ha
      obtain ⟨r, hr, hra⟩ := ha
      rw [← has, ← hra]
      simpa using r.2
    · intro hs
      refine Finset.mem_image.mpr ⟨(⟨s, Finset.mem_range.mp (hsub' i.1.2 hs)⟩ :
          (levDatumOf N P hsub hne).S (dd - 1)), ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_attach _ _, rfl⟩
      · rfl
  have hψinj : Function.Injective ψ := by
    intro i i' hii
    have hset : idxSet N c L (dd - 1) hL i.1.2 = idxSet N c L (dd - 1) hL i'.1.2 := by
      rw [← hψval i, ← hψval i', hii]
    have hmemH : i.1 ∈ LevH dd L A f₀ := by rw [← hY.1]; exact i.2
    obtain ⟨hi1, hicube, -⟩ := mem_LevH.mp hmemH
    have hmemH' : i'.1 ∈ LevH dd L A f₀ := by rw [← hY.1]; exact i'.2
    obtain ⟨hi1', hicube', -⟩ := mem_LevH.mp hmemH'
    have hval : i.1.2 = i'.1.2 := by
      funext x
      by_cases hx : x ∈ A
      · rw [hA] at hx
        obtain ⟨r, hr, hpr⟩ := mem_lvlSet.mp hx
        rw [← hpr]
        have hiff : (i.1.2 (ptFin c L (dd - 1) r hL) = true) ↔
            (i'.1.2 (ptFin c L (dd - 1) r hL) = true) := by
          have h2 : (r ∈ idxSet N c L (dd - 1) hL i.1.2) ↔
              (r ∈ idxSet N c L (dd - 1) hL i'.1.2) := by rw [hset]
          rw [mem_idxSet, mem_idxSet] at h2
          exact ⟨fun hh => (h2.mp ⟨hr, hh⟩).2, fun hh => (h2.mpr ⟨hr, hh⟩).2⟩
        by_cases hb : i.1.2 (ptFin c L (dd - 1) r hL) = true
        · rw [hb, hiff.mp hb]
        · rw [Bool.eq_false_iff.mpr hb, Bool.eq_false_iff.mpr (fun hc => hb (hiff.mpr hc))]
      · have hoff : ∀ x : Fin L, x ∉ A → i.1.2 x = f₀ x := (Finset.mem_filter.mp hicube).2
        have hoff' : ∀ x : Fin L, x ∉ A → i'.1.2 x = f₀ x := (Finset.mem_filter.mp hicube').2
        rw [hoff x hx, hoff' x hx]
    exact Subtype.ext (Prod.ext (by rw [hi1, hi1']) hval)
  have hψsurj : Function.Surjective ψ := by
    intro w
    set hw : Fin L → Bool :=
      fun x => if ∃ r ∈ w.val, ptFin c L (dd - 1) r.1 hL = x then true else f₀ x with hhw
    have hcube : hw ∈ cubeSet L A f₀ := by
      rw [cubeSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun x hx => ?_⟩
      simp only [hhw]
      by_cases hc : ∃ r ∈ w.val, ptFin c L (dd - 1) r.1 hL = x
      · have hcond : (∃ r ∈ w.val, ptFin c L (dd - 1) r.1 hL = x) := hc
        rw [if_pos hcond]
        obtain ⟨r, -, hpr⟩ := hc
        exact absurd (hpr ▸ (hA ▸ mem_lvlSet.mpr ⟨r.1, r.2, rfl⟩)) hx
      · rw [if_neg hc]
    have hne0 : hw ≠ f₀ := by
      intro hcon
      obtain ⟨r, hr⟩ := w.2
      have hcond : (∃ r' ∈ w.val, ptFin c L (dd - 1) r'.1 hL = ptFin c L (dd - 1) r.1 hL) :=
        ⟨r, hr, rfl⟩
      have htrue : hw (ptFin c L (dd - 1) r.1 hL) = true := by
        simp only [hhw]
        rw [if_pos hcond]
      rw [hcon, h.f0false r.1 r.2] at htrue
      exact Bool.noConfusion htrue
    have hmem : ((Sum.inr 0 : InitIdx dd), hw) ∈ X.H := by
      rw [hY.1, LevH, Finset.mem_image]
      exact ⟨hw, Finset.mem_erase.mpr ⟨hne0, hcube⟩, rfl⟩
    have hselfval : (idxSet N c L (dd - 1) hL hw).attach.image
        (fun r : {r // r ∈ idxSet N c L (dd - 1) hL hw} =>
          (⟨r.1, Finset.mem_range.mp (hsub' hw r.2)⟩ :
            (levDatumOf N P hsub hne).S (dd - 1))) = w.val := by
      ext s
      constructor
      · intro hs
        rw [Finset.mem_image] at hs
        obtain ⟨r, hr, hra⟩ := hs
        have hsr : s.1 = r.1 := by rw [← hra]
        have hh : hw (ptFin c L (dd - 1) s.1 hL) = true := by
          rw [hsr]
          exact (mem_idxSet.mp r.2).2
        simp only [hhw] at hh
        by_cases hc : ∃ r' ∈ w.val, ptFin c L (dd - 1) r'.1 hL = ptFin c L (dd - 1) s.1 hL
        · obtain ⟨r', hr', hpr⟩ := hc
          have hfin : r' = s := Fin.ext (ptFin_injective h r'.2 s.2 hpr)
          rwa [hfin] at hr'
        · rw [if_neg hc] at hh
          exact absurd hh (by rw [h.f0false s.1 s.2]; exact Bool.noConfusion)
      · intro hs
        have hsidx : s.1 ∈ idxSet N c L (dd - 1) hL hw := by
          refine mem_idxSet.mpr ⟨s.2, ?_⟩
          simp only [hhw]
          rw [if_pos (show ∃ r' ∈ w.val,
            ptFin c L (dd - 1) r'.1 hL = ptFin c L (dd - 1) s.1 hL from ⟨s, hs, rfl⟩)]
        refine Finset.mem_image.mpr ⟨⟨s.1, hsidx⟩, Finset.mem_attach _ _, ?_⟩
        exact Fin.ext rfl
    refine ⟨⟨((Sum.inr 0 : InitIdx dd), hw), hmem⟩, ?_⟩
    refine Subtype.ext ?_
    simp only [hψ]
    exact hselfval
  let e₀ : (X.toSym).S.ι ≃ (levDatumOf N P hsub hne).I (dd - 1) :=
    Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  let e : (X.toSym).S.ι ≃ Fin (Fintype.card ((levDatumOf N P hsub hne).I (dd - 1))) :=
    e₀.trans (Fintype.equivFin ((levDatumOf N P hsub hne).I (dd - 1)))
  refine ⟨e, ?_⟩
  intro i
  have he : e i = Fintype.equivFin ((levDatumOf N P hsub hne).I (dd - 1)) (e₀ i) := rfl
  have he₀ : e₀ i = ψ i := Equiv.ofBijective_apply ψ ⟨hψinj, hψsurj⟩ i
  rw [he, he₀, Equiv.symm_apply_apply]
  exact hψval i

/-- **The linear coefficient of a terminal slot is the datum's direction.**  On a `LevDInv`-state at
level `dd-1` whose live slots are a `LevCube`-state of degree `1`, the coefficient of `y` of the slot
`i`, evaluated at the window parameters of `t` (read through the coordinate map `c`), is the
direction `D.dir dd lc (dd-1) w`, where `w` is the `idxSet` of the slot. -/
theorem levCoeffOneEval {dd L H : ℕ} {lc : ℤ} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {hL : 1 ≤ L} {X : HistData dd L} {f₀ : Fin L → Bool}
    {A : Finset (Fin L)} {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ}
    (h : LevDInv dd lc (dd - 1) L hL N P c X f₀)
    (hsub : ∀ i, ∀ k, k < N (i + 1) → P i k ⊆ Finset.range (N i))
    (hne : ∀ i, ∀ k, k < N (i + 1) → (P i k).Nonempty)
    (hY : LevCube dd 1 L A f₀ atoms X) (hA : A = lvlSet N c L (dd - 1) hL)
    (i : (X.toSym).S.ι)
    (w : (levDatumOf N P hsub hne).I (dd - 1))
    (hw : w.val.map ⟨fun s : (levDatumOf N P hsub hne).S (dd - 1) => s.1,
        fun a b hab => Fin.ext hab⟩ = idxSet N c L (dd - 1) hL i.1.2)
    (t : WinTower H L) :
    MvPolynomial.eval (fun k : ℕ => if h : k < L then WinTower.param H L t ⟨k, h⟩ else 0)
        (MvPolynomial.rename Fin.val ((X.Q i.1.1 i.1.2).coeff 1))
      = (levDatumOf N P hsub hne).dir dd lc (dd - 1) w
          (fun j s =>
            (fun k : ℕ => if h : k < L then WinTower.param H L t ⟨k, h⟩ else 0) (c j s.1)) := by
  set φ : ℕ → ℤ := fun k => if h : k < L then WinTower.param H L t ⟨k, h⟩ else 0 with hφdef
  have hmemH : i.1 ∈ LevH dd L A f₀ := by rw [← hY.1]; exact i.2
  obtain ⟨hi1, hicube, hine⟩ := mem_LevH.mp hmemH
  have hmem' : i.1.2 ∈ cubeSet L (lvlSet N c L (dd - 1) hL) f₀ := by rwa [← hA]
  have hQi : X.Q i.1.1 i.1.2 = X.Q (Sum.inr 0 : InitIdx dd) i.1.2 := by rw [hi1]
  have hdeg : (X.Q (Sum.inr 0 : InitIdx dd) i.1.2).natDegree = 1 := (hY.2 i.1.2 hicube hine).1
  have hcoeff : (X.Q (Sum.inr 0 : InitIdx dd) i.1.2).coeff 1
      = (X.Q (Sum.inr 0 : InitIdx dd) i.1.2).leadingCoeff := by
    simpa [hdeg] using Polynomial.coeff_natDegree (p := X.Q (Sum.inr 0 : InitIdx dd) i.1.2)
  have hφΦ : (fun k : Fin L => φ (k : ℕ)) = WinTower.param H L t := by
    funext k
    simp only [hφdef, dif_pos k.2]
  have hstep : MvPolynomial.eval φ
        (MvPolynomial.rename Fin.val ((X.Q (Sum.inr 0 : InitIdx dd) i.1.2).coeff 1))
      = MvPolynomial.eval (WinTower.param H L t) ((X.Q (Sum.inr 0 : InitIdx dd) i.1.2).coeff 1) := by
    rw [MvPolynomial.eval_rename Fin.val]
    rw [show (φ ∘ Fin.val) = WinTower.param H L t from hφΦ]
  have hstep2 : MvPolynomial.eval (WinTower.param H L t)
        ((X.Q (Sum.inr 0 : InitIdx dd) i.1.2).leadingCoeff)
      = MvPolynomial.eval φ
        (MvPolynomial.rename Fin.val ((X.Q (Sum.inr 0 : InitIdx dd) i.1.2).leadingCoeff)) := by
    rw [MvPolynomial.eval_rename Fin.val]
    rw [show (φ ∘ Fin.val) = WinTower.param H L t from hφΦ]
  have hdir := dirPolyEvalDir (d := dd) (lc := lc) (N := N) (P := P) (c := c) (L' := L)
    (hL' := hL) (X := X) (f0 := f₀) h hsub hne (fun i s => φ (c i s)) φ
    (fun i s => rfl) (dd - 1) w
  rw [hQi]
  rw [hstep, hcoeff, hstep2, h.lc_eq i.1.2 hmem' hine, ← hw]
  exact hdir

end

end Work.Peluse.UControl
