import Mathlib
import Submission.Work.Peluse.SwapC.cgenSlotsRefine
import Submission.Work.Peluse.SwapC.cStepDefs
import Submission.Work.Peluse.SwapC.pbox_le_one_translate
import Submission.Work.Peluse.SwapC.pboxPeelBlocks
import Submission.Work.Peluse.SwapC.iterDeltaPSupp
-- import Submission.Work.Peluse.SwapC.cgenSlotsRefine

namespace Work.Peluse.SwapC

open scoped BigOperators
open Work.Peluse
open Work.Peluse.LadderP.Swap
open CC

noncomputable section

/-- **The one-step increment of the iteration of `Work.Peluse.SwapC.concatAll`** (KKL Proposition
6.2).  `cSt I q M N f L` is the average over all index assignments `ι : (Fin s → Bool) → I` of the
box norm of `f` with the slots `L` (coefficients `(q (ι a) j, 0)` for `CC.raw j a` and
`(q (ι a) j, q (ι b) j)` for `CC.dff j a b`); `genuineSlots Λ` is the slot list of the subdivision
`Λ`; `refine Λ l` splits the leaf `l` into its two children.  `hStep` is the statement of KKL Lemma
6.1 (`Work.Peluse.SwapC.CStepHyp`, i.e. `concatStep`), the only analytic input.

The conclusion is the increment inequality with constants uniform over all subdivisions whose slot
list has length `≤ D`.

Route.  (1) Rewrite the state with the list `A ++ [qH] ++ Bc` where `qH = CC.raw jh l.str`
(`jh = s - 1 - l.dep`), `A = (genuineSlots Λ).filter (¬touch l.str)` and
`Bc = ((genuineSlots Λ).filter (touch l.str)).erase qH`, using `cgenSlotsRefine` (the first conjunct
locates `qH`), the generic permutation facts `(L.filter p ++ L.filter (¬p)).Perm L` and
`(M.erase a) ++ [a] ~ M` (`a ∈ M`), and `cStPerm`.  (2) Peel the first `|A|` slots by
`pboxSum_peel_iter`; `pbox_eq_re` (for `f` and for the finitely supported `iterDeltaP`-difference)
turns the average of box *norms* into the average of the real parts of the corresponding box *sums*,
which the peel relates by an equality.  (3) The frozen function `iterDeltaP k sh f` is supported in
a translate of `symIcc N`: its corners are partial sums of the shifts, so the support is
`∩_corner (supp f − corner) ⊆ [-N - min corner, N - max corner]`, giving `hStep`'s support hypothesis
with `x₀ = -(max corner)`; it is `1`-bounded by definition.  (4) Fubini over the value at `l.str`:
`avg` over `ι` is the iterated average over `(ι l.str, ι ∘ (≠ l.str))`
(`Equiv.piEquivPiSubtypeProd` + `avg_prod`).  (5) Apply `hStep` at `s' = |Bc| ≤ D` with
`qH i := q i jh` and the `K`-slots the restrictions of the `Bc`-slots to the varying coordinate: for
each fixed frozen data this gives `C · Y ^ e ≤ avg_p pbox (2|Bc| + 1) (⋯)` with the two copies
`Bc.map (CC.subst l.str l.str)` and `Bc.map (CC.subst l.str a1)` and last slot
`CC.dff jh a1 l.str` (`a1 = Function.update l.str ⟨l.dep, _⟩ true`).  (6) Jensen
(`Work.Peluse.Holds.ExpPET.pow_mean_avg_le` with `p := e`, `y := Y^e`): `(E Y)^e ≤ E (Y^e)`.
(7) Reassemble by the peel identity backwards and `cStPerm`, giving `genuineSlots (refine Λ l)`.
Constants: the minimum of `C(s')` and the maximum of `e(s')` over `s' ≤ D`. -/
theorem cStep (hStep : Work.Peluse.SwapC.CStepHyp) (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ e : ℕ, 1 ≤ e ∧
      ∀ (I : Type) [Fintype I] [Nonempty I] (s : ℕ) (q : I → Fin s → ℤ) (M N : ℕ) (f : ℤ → ℂ)
        (Λ : List (CLeaf s)) (l : CLeaf s) (δ : ℝ),
        IsSubdiv Λ → Λ.Nodup → l ∈ Λ → l.dep < s → (genuineSlots Λ).length ≤ D →
        1 ≤ M → Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) → 0 < δ →
        δ ≤ cSt I q M N f (genuineSlots Λ) →
        C * δ ^ e ≤ cSt I q M N f (genuineSlots (refine Λ l)) := by
  classical
  let Cfun : ℕ → ℝ := fun s' => Classical.choose (hStep s')
  have hCfun : ∀ s' : ℕ, 0 < Cfun s' := fun s' => (Classical.choose_spec (hStep s')).1
  have hstep2 : ∀ s' : ℕ, ∃ e : ℕ, 1 ≤ e ∧
      ∀ (I : Type) [Fintype I] [Nonempty I] (qH : I → ℤ) (q₁ q₂ : I → Fin s' → ℤ)
        (M N : ℕ) (x₀ : ℤ) (δ : ℝ) (f : ℤ → ℂ),
        1 ≤ M → (∀ x : ℤ, (N : ℤ) < |x - x₀| → f x = 0) → (∀ x : ℤ, ‖f x‖ ≤ 1) → 0 < δ →
        δ ≤ avg (fun i : I => pbox (s' + 1) (Fin.cons (qH i) (q₁ i)) (Fin.cons 0 (q₂ i))
                M (symIcc N) f) →
        Cfun s' * δ ^ e ≤ avg (fun p : I × I => pbox (s' + s' + 1)
                (Fin.snoc (Fin.append (q₁ p.1) (q₁ p.2)) (qH p.2))
                (Fin.snoc (Fin.append (q₂ p.1) (q₂ p.2)) (qH p.1)) M (symIcc N) f) :=
    fun s' => (Classical.choose_spec (hStep s')).2
  let efun : ℕ → ℕ := fun s' => Classical.choose (hstep2 s')
  have hefun : ∀ s' : ℕ, 1 ≤ efun s' := fun s' => (Classical.choose_spec (hstep2 s')).1
  have hmain : ∀ (s' : ℕ) (I : Type) [Fintype I] [Nonempty I] (qH : I → ℤ)
      (q₁ q₂ : I → Fin s' → ℤ) (M N : ℕ) (x₀ : ℤ) (δ : ℝ) (f : ℤ → ℂ),
      1 ≤ M → (∀ x : ℤ, (N : ℤ) < |x - x₀| → f x = 0) → (∀ x : ℤ, ‖f x‖ ≤ 1) → 0 < δ →
      δ ≤ avg (fun i : I => pbox (s' + 1) (Fin.cons (qH i) (q₁ i)) (Fin.cons 0 (q₂ i))
              M (symIcc N) f) →
      Cfun s' * δ ^ efun s' ≤ avg (fun p : I × I => pbox (s' + s' + 1)
              (Fin.snoc (Fin.append (q₁ p.1) (q₁ p.2)) (qH p.2))
              (Fin.snoc (Fin.append (q₂ p.1) (q₂ p.2)) (qH p.1)) M (symIcc N) f) :=
    fun s' => (Classical.choose_spec (hstep2 s')).2
  obtain ⟨b₀, -, hb₀eq⟩ :=
    Finset.exists_mem_eq_inf' (s := Finset.range (D + 1)) ⟨0, by simp⟩ Cfun
  obtain ⟨b₁, -, hb₁eq⟩ :=
    Finset.exists_mem_eq_sup' (s := Finset.range (D + 1)) ⟨0, by simp⟩ efun
  refine ⟨(Finset.range (D + 1)).inf' ⟨0, by simp⟩ Cfun, ?_,
    (Finset.range (D + 1)).sup' ⟨0, by simp⟩ efun, ?_, ?_⟩
  · rw [hb₀eq]
    exact hCfun b₀
  · rw [hb₁eq]
    exact hefun b₁
  · intro I _instI _neI s q M N f Λ l δ hsub hnod hl hd hlenD hM hsup hbd hδpos hδle
    -- ## 1. the local slot data
    set a : Fin s → Bool := l.str with ha
    set a1 : Fin s → Bool := Function.update l.str ⟨l.dep, hd⟩ true with ha1
    have ha1ne : a1 ≠ a := by
      rw [ha1, ha]
      intro hcon
      have h1 : (Function.update l.str ⟨l.dep, hd⟩ true) ⟨l.dep, hd⟩ = true := by simp
      rw [hcon] at h1
      rw [l.pad ⟨l.dep, hd⟩ (le_refl l.dep)] at h1
      exact Bool.noConfusion h1
    set jh : Fin s := ⟨s - 1 - l.dep, by omega⟩ with hjh
    set qH : CC s := CC.raw jh a with hqH
    set A : List (CC s) := (genuineSlots Λ).filter (fun sl => !CC.touchesb a sl) with hA
    set Bc : List (CC s) :=
      ((genuineSlots Λ).filter (fun sl => CC.touchesb a sl)).erase qH with hBc
    set new : CC s := CC.dff jh a1 a with hnew
    have hBcm_eq : Bc.map (CC.subst a a) = Bc := by
      induction Bc with
      | nil => rfl
      | cons hd tl ih => simp [CC.subst_self, ih]
    set R : List (CC s) := Bc ++ Bc.map (CC.subst a a1) ++ [new] with hR
    -- ## 2. the decomposition of the refinement (KKL Proposition 6.2, slot bookkeeping)
    have hqHmem : qH ∈ genuineSlots Λ := by
      rw [hqH, ha, genuineSlots, List.mem_append]
      refine Or.inl ?_
      rw [List.mem_flatten]
      refine ⟨CLeaf.raws l, ?_, ?_⟩
      · rw [List.mem_map]; exact ⟨l, hl, rfl⟩
      · rw [CLeaf.raws, List.mem_map]
        refine ⟨jh, ?_, rfl⟩
        rw [List.mem_filter, decide_eq_true_eq]
        refine ⟨List.mem_finRange jh, ?_⟩
        have h3 : jh.val = s - 1 - l.dep := by rw [hjh]
        rw [h3]
        omega
    have hperm : (genuineSlots (refine Λ l)).Perm (A ++ R) := by
      obtain ⟨-, hp⟩ := cgenSlotsRefine (Λ := Λ) (l := l) hsub hnod hl hd
      have hEq : A ++ R = (genuineSlots Λ).filter (fun sl => !CC.touchesb l.str sl)
          ++ (((genuineSlots Λ).filter (fun sl => CC.touchesb l.str sl)).erase
                (CC.raw ⟨s - 1 - l.dep, by omega⟩ l.str)).map (CC.subst l.str l.str)
          ++ (((genuineSlots Λ).filter (fun sl => CC.touchesb l.str sl)).erase
                (CC.raw ⟨s - 1 - l.dep, by omega⟩ l.str)).map
                (CC.subst l.str (Function.update l.str ⟨l.dep, hd⟩ true))
          ++ [CC.dff ⟨s - 1 - l.dep, by omega⟩ (Function.update l.str ⟨l.dep, hd⟩ true) l.str] := by
        have hsubst_id : (fun sl : CC s => CC.subst l.str l.str sl) = id := by
          funext sl; exact CC.subst_self l.str sl
        simp only [hR, hA, hBc, hqH, ha, ha1, hjh, hnew, hsubst_id, List.map_id,
          List.append_assoc]
      rw [hEq]
      exact hp
    have ha1notleaf : ∀ l' ∈ Λ, l'.str ≠ a1 := by
      intro l' hl' hcon
      have hlwit : l ∈ Λ ∧ ∀ i : Fin s, i.val < l.dep → l.str i = a1 i :=
        ⟨hl, fun i hi => by
          have hne : i ≠ ⟨l.dep, hd⟩ := by
            intro he
            have h1 : i.val = l.dep := by
              have := congrArg Fin.val he
              simpa using this
            omega
          rw [ha1, Function.update_of_ne hne]⟩
      have hl'wit : l' ∈ Λ ∧ ∀ i : Fin s, i.val < l'.dep → l'.str i = a1 i :=
        ⟨hl', fun i _ => by rw [hcon]⟩
      have heq : l' = l := ExistsUnique.unique (hsub a1) hl'wit hlwit
      have hfalse : l.str ⟨l.dep, hd⟩ = false := l.pad ⟨l.dep, hd⟩ (le_refl _)
      rw [heq] at hcon
      have htrue : l.str ⟨l.dep, hd⟩ = true := by
        rw [hcon, ha1]
        exact Function.update_self ..
      rw [hfalse] at htrue
      exact Bool.noConfusion htrue
    have hrawlbl : ∀ {j : Fin s} {b : Fin s → Bool},
        CC.raw j b ∈ genuineSlots Λ → ∃ l' ∈ Λ, l'.str = b := by
      intro j b h
      rw [genuineSlots, List.mem_append] at h
      rcases h with h | h
      · rw [List.mem_flatten] at h
        obtain ⟨L, hL, hLb⟩ := h
        rw [List.mem_map] at hL
        obtain ⟨l', hl', rfl⟩ := hL
        rw [CLeaf.raws, List.mem_map] at hLb
        obtain ⟨j', -, hj'⟩ := hLb
        exact ⟨l', hl', (CC.raw.inj hj').2⟩
      · rw [genuineDiffs, List.mem_flatMap] at h
        obtain ⟨p, -, h2⟩ := h
        rw [List.mem_filterMap] at h2
        obtain ⟨j', -, hj'⟩ := h2
        split at hj' <;> simp at hj'
    have hdfflbl : ∀ {j : Fin s} {b c : Fin s → Bool},
        CC.dff j b c ∈ genuineSlots Λ → (∃ l' ∈ Λ, l'.str = b) ∧ (∃ l' ∈ Λ, l'.str = c) := by
      intro j b c h
      rw [genuineSlots, List.mem_append] at h
      rcases h with h | h
      · rw [List.mem_flatten] at h
        obtain ⟨L, hL, hLb⟩ := h
        rw [List.mem_map] at hL
        obtain ⟨l', hl', rfl⟩ := hL
        rw [CLeaf.raws, List.mem_map] at hLb
        obtain ⟨j', -, hj'⟩ := hLb
        exact absurd hj' (by intro hh; cases hh)
      · rw [genuineDiffs, List.mem_flatMap] at h
        obtain ⟨p, hp, h2⟩ := h
        obtain ⟨hp1, hp2⟩ := List.mem_product.mp hp
        rw [List.mem_filterMap] at h2
        obtain ⟨j', -, hj'⟩ := h2
        split at hj'
        · rw [Option.some.injEq, CC.dff.injEq] at hj'
          exact ⟨⟨p.1, hp1, hj'.2.1⟩, ⟨p.2, hp2, hj'.2.2⟩⟩
        · simp at hj'
    have hpermR : (genuineSlots (refine Λ l)).Perm (A ++ R) := hperm
    have havoids : ∀ sl ∈ genuineSlots Λ, avoids a1 sl := by
      intro sl hsl
      cases sl with
      | raw j b =>
          obtain ⟨l', hl', hstr⟩ := hrawlbl hsl
          show b ≠ a1
          rw [← hstr]
          exact ha1notleaf l' hl'
      | dff j b c =>
          obtain ⟨⟨l', hl', hstr⟩, ⟨l'', hl'', hstr'⟩⟩ := hdfflbl hsl
          exact ⟨by rw [← hstr]; exact ha1notleaf l' hl',
                 by rw [← hstr']; exact ha1notleaf l'' hl''⟩
    have hBcsub : ∀ sl ∈ Bc, sl ∈ genuineSlots Λ := by
      intro sl hsl
      rw [hBc] at hsl
      exact (List.mem_filter.mp (List.mem_of_mem_erase hsl)).1
    have hAmem : ∀ sl ∈ A, sl ∈ genuineSlots Λ ∧ CC.touchesb a sl = false := by
      intro sl hsl
      have h2 : (fun sl => !CC.touchesb a sl) sl = true := (List.mem_filter.mp hsl).2
      exact ⟨(List.mem_filter.mp hsl).1, by simpa using h2⟩
    have hasub : ∀ sl ∈ A, sl ∈ genuineSlots Λ := fun sl hsl => (hAmem sl hsl).1
    have havoidsBc : ∀ k : Fin Bc.length, avoids a1 (Bc.get k) :=
      fun k => havoids _ (hBcsub _ (List.get_mem Bc k))
    have havoidsA : ∀ j : Fin A.length, avoids a (A.get j) ∧ avoids a1 (A.get j) := by
      intro j
      refine ⟨?_, havoids _ (hasub _ (List.get_mem A j))⟩
      rw [avoids_iff_touchesb]
      exact (hAmem _ (List.get_mem A j)).2
    have hfin : Work.Peluse.FinSuppZ f := Work.Peluse.FinSuppZ.of_supportIn hsup
    -- ## 3. the frozen data, the peel pair, and the two averages of the step lemma
    let Rest : Type := {x : Fin s → Bool // x ≠ a ∧ x ≠ a1} → I
    let QP : Type := (Fin A.length → Fin M × Fin M) × (Fin A.length → Fin M × Fin M)
    haveI hne_QP : Nonempty QP :=
      ⟨(fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩), fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩))⟩
    let iU : I := Classical.arbitrary I
    let shA : Rest → QP → Fin A.length → ℤ × ℤ := fun rest p j =>
      (pdir (cA q (envOf a a1 rest iU iU) (A.get j))
            (cB q (envOf a a1 rest iU iU) (A.get j)) (p.1 j),
       pdir (cA q (envOf a a1 rest iU iU) (A.get j))
            (cB q (envOf a a1 rest iU iU) (A.get j)) (p.2 j))
    let gF : Rest → QP → ℤ → ℂ := fun rest p => iterDeltaP A.length (shA rest p) f
    let q1F : Rest → I → Fin Bc.length → ℤ :=
      fun rest i k => cA q (envOf a a1 rest i i) (Bc.get k)
    let q2F : Rest → I → Fin Bc.length → ℤ :=
      fun rest i k => cB q (envOf a a1 rest i i) (Bc.get k)
    let HypF : Rest → I → QP → ℝ := fun rest i p =>
      pbox (Bc.length + 1) (Fin.cons (q i jh) (q1F rest i)) (Fin.cons 0 (q2F rest i))
        M (symIcc N) (gF rest p)
    let ConclF : Rest → I × I → QP → ℝ := fun rest ii p =>
      pbox (Bc.length + Bc.length + 1)
        (Fin.snoc (Fin.append (q1F rest ii.1) (q1F rest ii.2)) (q ii.2 jh))
        (Fin.snoc (Fin.append (q2F rest ii.1) (q2F rest ii.2)) (q ii.1 jh))
        M (symIcc N) (gF rest p)
    let PeelC : ((Fin s → Bool) → I) → QP → ℝ := fun η p =>
      pbox (Bc.length + 1) (fun k => cA q η ((qH :: Bc).get k))
        (fun k => cB q η ((qH :: Bc).get k)) M (symIcc N)
        (iterDeltaP A.length (fun j =>
            (pdir (cA q η (A.get j)) (cB q η (A.get j)) (p.1 j),
             pdir (cA q η (A.get j)) (cB q η (A.get j)) (p.2 j))) f)
    let PeelR : ((Fin s → Bool) → I) → QP → ℝ := fun η p =>
      pbox R.length (fun k => cA q η (R.get k)) (fun k => cB q η (R.get k)) M (symIcc N)
        (iterDeltaP A.length (fun j =>
            (pdir (cA q η (A.get j)) (cB q η (A.get j)) (p.1 j),
             pdir (cA q η (A.get j)) (cB q η (A.get j)) (p.2 j))) f)
    -- ## 4. peeling the frozen slots
    have hpeelC : ∀ η : (Fin s → Bool) → I,
        pbox (A ++ (qH :: Bc)).length (fun k => cA q η ((A ++ (qH :: Bc)).get k))
            (fun k => cB q η ((A ++ (qH :: Bc)).get k)) M (symIcc N) f
          = avg (PeelC η) := by
      intro η
      have hlen : (A ++ (qH :: Bc)).length = A.length + (Bc.length + 1) := by
        rw [List.length_append, List.length_cons]
      have hQA : (fun k : Fin (A.length + (Bc.length + 1)) =>
            cA q η ((A ++ (qH :: Bc)).get (Fin.cast hlen.symm k)))
          = Fin.append (fun j : Fin A.length => cA q η (A.get j))
              (fun k : Fin (Bc.length + 1) => cA q η ((qH :: Bc).get k)) := by
        funext k
        refine Fin.addCases ?_ ?_ k
        · intro j
          rw [Fin.append_left]
          show cA q η ((A ++ (qH :: Bc)).get ⟨j.val, _⟩) = cA q η (A.get j)
          rw [get_append_left']
        · intro i
          rw [Fin.append_right]
          show cA q η ((A ++ (qH :: Bc)).get ⟨A.length + i.val, _⟩)
            = cA q η ((qH :: Bc).get i)
          rw [get_append_right']
      have hQB : (fun k : Fin (A.length + (Bc.length + 1)) =>
            cB q η ((A ++ (qH :: Bc)).get (Fin.cast hlen.symm k)))
          = Fin.append (fun j : Fin A.length => cB q η (A.get j))
              (fun k : Fin (Bc.length + 1) => cB q η ((qH :: Bc).get k)) := by
        funext k
        refine Fin.addCases ?_ ?_ k
        · intro j
          rw [Fin.append_left]
          show cB q η ((A ++ (qH :: Bc)).get ⟨j.val, _⟩) = cB q η (A.get j)
          rw [get_append_left']
        · intro i
          rw [Fin.append_right]
          show cB q η ((A ++ (qH :: Bc)).get ⟨A.length + i.val, _⟩)
            = cB q η ((qH :: Bc).get i)
          rw [get_append_right']
      rw [pbox_finCongr hlen, hQA, hQB,
        pboxPeelBlocks (d := A.length) (e := Bc.length + 1) (by omega)
          (fun j : Fin A.length => cA q η (A.get j)) (fun j : Fin A.length => cB q η (A.get j))
          (fun k : Fin (Bc.length + 1) => cA q η ((qH :: Bc).get k))
          (fun k : Fin (Bc.length + 1) => cB q η ((qH :: Bc).get k))
          M (symIcc N) f hfin]
    have hpeelR : ∀ η : (Fin s → Bool) → I,
        pbox (A ++ R).length (fun k => cA q η ((A ++ R).get k))
            (fun k => cB q η ((A ++ R).get k)) M (symIcc N) f
          = avg (PeelR η) := by
      intro η
      have hlen : (A ++ R).length = A.length + R.length := List.length_append
      have hQA : (fun k : Fin (A.length + R.length) =>
            cA q η ((A ++ R).get (Fin.cast hlen.symm k)))
          = Fin.append (fun j : Fin A.length => cA q η (A.get j))
              (fun k : Fin R.length => cA q η (R.get k)) := by
        funext k
        refine Fin.addCases ?_ ?_ k
        · intro j
          rw [Fin.append_left]
          show cA q η ((A ++ R).get ⟨j.val, _⟩) = cA q η (A.get j)
          rw [get_append_left']
        · intro i
          rw [Fin.append_right]
          show cA q η ((A ++ R).get ⟨A.length + i.val, _⟩) = cA q η (R.get i)
          rw [get_append_right']
      have hQB : (fun k : Fin (A.length + R.length) =>
            cB q η ((A ++ R).get (Fin.cast hlen.symm k)))
          = Fin.append (fun j : Fin A.length => cB q η (A.get j))
              (fun k : Fin R.length => cB q η (R.get k)) := by
        funext k
        refine Fin.addCases ?_ ?_ k
        · intro j
          rw [Fin.append_left]
          show cB q η ((A ++ R).get ⟨j.val, _⟩) = cB q η (A.get j)
          rw [get_append_left']
        · intro i
          rw [Fin.append_right]
          show cB q η ((A ++ R).get ⟨A.length + i.val, _⟩) = cB q η (R.get i)
          rw [get_append_right']
      rw [pbox_finCongr hlen, hQA, hQB,
        pboxPeelBlocks (d := A.length) (e := R.length)
          (by rw [hR, List.length_append, List.length_append, List.length_singleton]; omega)
          (fun j : Fin A.length => cA q η (A.get j)) (fun j : Fin A.length => cB q η (A.get j))
          (fun k : Fin R.length => cA q η (R.get k))
          (fun k : Fin R.length => cB q η (R.get k))
          M (symIcc N) f hfin]
    -- ## 5. the identifications of the peeled integrands
    have hshiftC : ∀ (rest : Rest) (i₀ i₁ : I) (p : QP),
        (fun j : Fin A.length =>
            (pdir (cA q (envOf a a1 rest i₀ i₁) (A.get j))
                  (cB q (envOf a a1 rest i₀ i₁) (A.get j)) (p.1 j),
             pdir (cA q (envOf a a1 rest i₀ i₁) (A.get j))
                  (cB q (envOf a a1 rest i₀ i₁) (A.get j)) (p.2 j)))
          = shA rest p := by
      intro rest i₀ i₁ p
      funext j
      have h1 : cA q (envOf a a1 rest i₀ i₁) (A.get j) =
          cA q (envOf a a1 rest iU iU) (A.get j) :=
        cA_envOf_congr_both q (A.get j) (havoidsA j).1 (havoidsA j).2
      have h2 : cB q (envOf a a1 rest i₀ i₁) (A.get j) =
          cB q (envOf a a1 rest iU iU) (A.get j) :=
        cB_envOf_congr_both q (A.get j) (havoidsA j).1 (havoidsA j).2
      rw [h1, h2]
    have hidentC : ∀ (rest : Rest) (i₀ i₁ : I) (p : QP), PeelC (envOf a a1 rest i₀ i₁) p
          = HypF rest i₀ p := by
      intro rest i₀ i₁ p
      show pbox (Bc.length + 1) (fun k => cA q (envOf a a1 rest i₀ i₁) ((qH :: Bc).get k))
            (fun k => cB q (envOf a a1 rest i₀ i₁) ((qH :: Bc).get k)) M (symIcc N)
            (iterDeltaP A.length (fun j =>
              (pdir (cA q (envOf a a1 rest i₀ i₁) (A.get j))
                    (cB q (envOf a a1 rest i₀ i₁) (A.get j)) (p.1 j),
               pdir (cA q (envOf a a1 rest i₀ i₁) (A.get j))
                    (cB q (envOf a a1 rest i₀ i₁) (A.get j)) (p.2 j))) f)
          = pbox (Bc.length + 1) (Fin.cons (q i₀ jh) (q1F rest i₀)) (Fin.cons 0 (q2F rest i₀))
              M (symIcc N) (gF rest p)
      have hC1 : (fun k : Fin (Bc.length + 1) => cA q (envOf a a1 rest i₀ i₁) ((qH :: Bc).get k))
          = Fin.cons (q i₀ jh) (q1F rest i₀) := by
        funext k
        refine Fin.cases ?_ ?_ k
        · show cA q (envOf a a1 rest i₀ i₁) qH = q i₀ jh
          rw [hqH]
          show q ((envOf a a1 rest i₀ i₁) a) jh = q i₀ jh
          rw [envOf_same]
        · intro k'
          show cA q (envOf a a1 rest i₀ i₁) (Bc.get k') = q1F rest i₀ k'
          exact cA_envOf_congr_a1 q (Bc.get k') (havoidsBc k')
      have hC2 : (fun k : Fin (Bc.length + 1) => cB q (envOf a a1 rest i₀ i₁) ((qH :: Bc).get k))
          = Fin.cons 0 (q2F rest i₀) := by
        funext k
        refine Fin.cases ?_ ?_ k
        · show cB q (envOf a a1 rest i₀ i₁) qH = 0
          rw [hqH]
          simp
        · intro k'
          show cB q (envOf a a1 rest i₀ i₁) (Bc.get k') = q2F rest i₀ k'
          exact cB_envOf_congr_a1 q (Bc.get k') (havoidsBc k')
      have hG : (iterDeltaP A.length (fun j =>
            (pdir (cA q (envOf a a1 rest i₀ i₁) (A.get j))
                  (cB q (envOf a a1 rest i₀ i₁) (A.get j)) (p.1 j),
             pdir (cA q (envOf a a1 rest i₀ i₁) (A.get j))
                  (cB q (envOf a a1 rest i₀ i₁) (A.get j)) (p.2 j))) f)
          = gF rest p := by
        rw [hshiftC rest i₀ i₁ p]
      rw [hC1, hC2, hG]
    have hidentR : ∀ (rest : Rest) (i₀ i₁ : I) (p : QP), PeelR (envOf a a1 rest i₀ i₁) p
          = ConclF rest (i₀, i₁) p := by
      intro rest i₀ i₁ p
      have hG : iterDeltaP A.length (fun j =>
            (pdir (cA q (envOf a a1 rest i₀ i₁) (A.get j))
                  (cB q (envOf a a1 rest i₀ i₁) (A.get j)) (p.1 j),
             pdir (cA q (envOf a a1 rest i₀ i₁) (A.get j))
                  (cB q (envOf a a1 rest i₀ i₁) (A.get j)) (p.2 j))) f = gF rest p := by
        rw [hshiftC rest i₀ i₁ p]
      show pbox R.length (fun k => cA q (envOf a a1 rest i₀ i₁) (R.get k))
            (fun k => cB q (envOf a a1 rest i₀ i₁) (R.get k)) M (symIcc N)
            (iterDeltaP A.length (fun j =>
              (pdir (cA q (envOf a a1 rest i₀ i₁) (A.get j))
                    (cB q (envOf a a1 rest i₀ i₁) (A.get j)) (p.1 j),
               pdir (cA q (envOf a a1 rest i₀ i₁) (A.get j))
                    (cB q (envOf a a1 rest i₀ i₁) (A.get j)) (p.2 j))) f)
          = pbox (Bc.length + Bc.length + 1)
              (Fin.snoc (Fin.append (q1F rest i₀) (q1F rest i₁)) (q i₁ jh))
              (Fin.snoc (Fin.append (q2F rest i₀) (q2F rest i₁)) (q i₀ jh))
              M (symIcc N) (gF rest p)
      rw [hG]
      have hlen : R.length = Bc.length + Bc.length + 1 := by
        rw [hR, List.length_append, List.length_append, List.length_singleton,
          List.length_map]
      rw [pbox_finCongr hlen]
      congr 1
      · funext k
        refine Fin.lastCases ?_ ?_ k
        · rw [Fin.snoc_last]
          show cA q (envOf a a1 rest i₀ i₁)
            (R[Bc.length + Bc.length]'(by rw [hlen]; omega)) = q i₁ jh
          rw [getElem_congr_coll hR,
            getElem_congr_idx (show Bc.length + Bc.length
              = Bc.length + (Bc.map (CC.subst a a1)).length from by rw [List.length_map])]
          rw [getElem_append3_last']
          rw [hnew]
          show q ((envOf a a1 rest i₀ i₁) a1) jh = q i₁ jh
          rw [envOf_second ha1ne]
        · intro l
          rw [Fin.snoc_castSucc]
          refine Fin.addCases ?_ ?_ l
          · intro j
            rw [Fin.append_left]
            show cA q (envOf a a1 rest i₀ i₁)
              (R[j.val]'(by rw [hlen]; omega)) = q1F rest i₀ j
            rw [getElem_congr_coll hR,
              getElem_append3_left' Bc (Bc.map (CC.subst a a1)) new j.val j.isLt]
            show cA q (envOf a a1 rest i₀ i₁) (Bc.get j) = q1F rest i₀ j
            exact cA_envOf_congr_a1 q (Bc.get j) (havoidsBc j)
          · intro j
            rw [Fin.append_right]
            show cA q (envOf a a1 rest i₀ i₁)
              (R[Bc.length + j.val]'(by rw [hlen]; omega)) = q1F rest i₁ j
            rw [getElem_congr_coll hR,
              getElem_congr_idx (show Bc.length + j.val
                = Bc.length + j.val from rfl),
              getElem_append3_mid' Bc (Bc.map (CC.subst a a1)) new j.val
                (by rw [List.length_map]; exact j.isLt),
              List.getElem_map]
            show cA q (envOf a a1 rest i₀ i₁) (CC.subst a a1 (Bc.get j)) = q1F rest i₁ j
            exact cA_subst_a1 q (h := ha1ne) (Bc.get j)
      · funext k
        refine Fin.lastCases ?_ ?_ k
        · rw [Fin.snoc_last]
          show cB q (envOf a a1 rest i₀ i₁)
            (R[Bc.length + Bc.length]'(by rw [hlen]; omega)) = q i₀ jh
          rw [getElem_congr_coll hR,
            getElem_congr_idx (show Bc.length + Bc.length
              = Bc.length + (Bc.map (CC.subst a a1)).length from by rw [List.length_map])]
          rw [getElem_append3_last']
          rw [hnew]
          show q ((envOf a a1 rest i₀ i₁) a) jh = q i₀ jh
          rw [envOf_same]
        · intro l
          rw [Fin.snoc_castSucc]
          refine Fin.addCases ?_ ?_ l
          · intro j
            rw [Fin.append_left]
            show cB q (envOf a a1 rest i₀ i₁)
              (R[j.val]'(by rw [hlen]; omega)) = q2F rest i₀ j
            rw [getElem_congr_coll hR,
              getElem_append3_left' Bc (Bc.map (CC.subst a a1)) new j.val j.isLt]
            show cB q (envOf a a1 rest i₀ i₁) (Bc.get j) = q2F rest i₀ j
            exact cB_envOf_congr_a1 q (Bc.get j) (havoidsBc j)
          · intro j
            rw [Fin.append_right]
            show cB q (envOf a a1 rest i₀ i₁)
              (R[Bc.length + j.val]'(by rw [hlen]; omega)) = q2F rest i₁ j
            rw [getElem_congr_coll hR,
              getElem_congr_idx (show Bc.length + j.val
                = Bc.length + j.val from rfl),
              getElem_append3_mid' Bc (Bc.map (CC.subst a a1)) new j.val
                (by rw [List.length_map]; exact j.isLt),
              List.getElem_map]
            show cB q (envOf a a1 rest i₀ i₁) (CC.subst a a1 (Bc.get j)) = q2F rest i₁ j
            exact cB_subst_a1 q (h := ha1ne) (Bc.get j)
    -- ## 6. the two states as iterated averages of the frozen data
    have hpermL : (genuineSlots Λ).Perm (A ++ (qH :: Bc)) := by
      have h1 : (genuineSlots Λ).Perm
          (A ++ (genuineSlots Λ).filter (fun sl => CC.touchesb a sl)) := by
        have h := List.filter_append_perm (fun sl => !CC.touchesb a sl) (genuineSlots Λ)
        simp only [Bool.not_not] at h
        rw [← hA] at h
        exact h.symm
      have h2 : ((genuineSlots Λ).filter (fun sl => CC.touchesb a sl)).Perm (qH :: Bc) := by
        have hmem : qH ∈ (genuineSlots Λ).filter (fun sl => CC.touchesb a sl) := by
          rw [List.mem_filter]
          exact ⟨hqHmem, by rw [hqH, ha]; simp [CC.touchesb, CC.touches]⟩
        have h := List.perm_cons_erase hmem
        rw [hBc]
        exact h
      exact h1.trans (h2.append_left A)
    have hT : cSt I q M N f (genuineSlots Λ)
        = avg (fun z : Rest × QP => avg (fun i : I => HypF z.1 i z.2)) := by
      rw [cStPerm I q M N f hpermL, cSt_def]
      have h1 : (fun η : (Fin s → Bool) → I => pbox (A ++ (qH :: Bc)).length
            (fun k => cA q η ((A ++ (qH :: Bc)).get k))
            (fun k => cB q η ((A ++ (qH :: Bc)).get k)) M (symIcc N) f)
          = fun η => avg (PeelC η) := funext fun η => hpeelC η
      rw [h1, avg_envOf ha1ne (fun η : (Fin s → Bool) → I => avg (PeelC η)),
        ← avg_prod (F := fun z : (Rest × (I × I)) × QP =>
          PeelC (envOf a a1 z.1.1 z.1.2.1 z.1.2.2) z.2)]
      have h2 : (fun z : (Rest × (I × I)) × QP => PeelC (envOf a a1 z.1.1 z.1.2.1 z.1.2.2) z.2)
          = fun z : (Rest × (I × I)) × QP => HypF z.1.1 z.1.2.1 z.2 :=
        funext fun z => hidentC z.1.1 z.1.2.1 z.1.2.2 z.2
      rw [h2, avg_prod (F := fun z : (Rest × (I × I)) × QP => HypF z.1.1 z.1.2.1 z.2),
        avg_prod_drop (F := fun (rest : Rest) (i : I) => avg (fun p : QP => HypF rest i p)),
        avg_swap (F := fun (rest : Rest) (i : I) (p : QP) => HypF rest i p)]
    have hT' : cSt I q M N f (genuineSlots (refine Λ l))
        = avg (fun z : Rest × QP => avg (fun ii : I × I => ConclF z.1 ii z.2)) := by
      rw [cStPerm I q M N f hpermR, cSt_def]
      have h1 : (fun η : (Fin s → Bool) → I => pbox (A ++ R).length
            (fun k => cA q η ((A ++ R).get k)) (fun k => cB q η ((A ++ R).get k))
            M (symIcc N) f) = fun η => avg (PeelR η) := funext fun η => hpeelR η
      rw [h1, avg_envOf ha1ne (fun η : (Fin s → Bool) → I => avg (PeelR η)),
        ← avg_prod (F := fun z : (Rest × (I × I)) × QP =>
          PeelR (envOf a a1 z.1.1 z.1.2.1 z.1.2.2) z.2)]
      have h2 : (fun z : (Rest × (I × I)) × QP => PeelR (envOf a a1 z.1.1 z.1.2.1 z.1.2.2) z.2)
          = fun z : (Rest × (I × I)) × QP => ConclF z.1.1 z.1.2 z.2 :=
        funext fun z => hidentR z.1.1 z.1.2.1 z.1.2.2 z.2
      rw [h2, avg_prod (F := fun z : (Rest × (I × I)) × QP => ConclF z.1.1 z.1.2 z.2),
        avg_swap (F := fun (rest : Rest) (ii : I × I) (p : QP) => ConclF rest ii p)]
    -- ## 7. the pointwise step, for each frozen datum
    set Y : Rest × QP → ℝ := fun z => avg (fun i : I => HypF z.1 i z.2) with hY
    set Z : Rest × QP → ℝ := fun z => avg (fun ii : I × I => ConclF z.1 ii z.2) with hZ
    have hδY : δ ≤ avg Y := by rw [← hT]; exact hδle
    have hYle1 : ∀ z : Rest × QP, Y z ≤ 1 := by
      intro z
      obtain ⟨rest, p⟩ := z
      refine avg_le_of_forall_le fun i => pbox_le_one_translate (Bc.length + 1)
        (Fin.cons (q i jh) (q1F rest i)) (Fin.cons 0 (q2F rest i)) M N
        (-(∑ j : Fin A.length, (shA rest p j).2)) (gF rest p) ?_ ?_
      · intro x
        exact (iterDeltaPSupp (shA rest p) f hsup hbd).1 x
      · intro x
        exact (iterDeltaPSupp (shA rest p) f hsup hbd).2 x
    have hYnn : ∀ z : Rest × QP, 0 ≤ Y z := by
      intro z
      exact avg_nonneg fun i => pbox_nonneg _ _ _ _ _ _
    have hδ1 : δ ≤ 1 := le_trans hδY (avg_le_of_forall_le hYle1)
    have hstep_pt : ∀ z : Rest × QP,
        Cfun (Bc.length) * (Y z) ^ efun (Bc.length) ≤ Z z := by
      intro z
      obtain ⟨rest, p⟩ := z
      show Cfun (Bc.length) * (avg (fun i : I => HypF rest i p)) ^ efun (Bc.length)
        ≤ avg (fun ii : I × I => ConclF rest ii p)
      by_cases hY0 : 0 < avg (fun i : I => HypF rest i p)
      · exact hmain (Bc.length) I (fun i => q i jh) (q1F rest) (q2F rest) M N
          (-(∑ j : Fin A.length, (shA rest p j).2)) (avg (fun i : I => HypF rest i p))
          (gF rest p) hM (fun x => (iterDeltaPSupp (shA rest p) f hsup hbd).1 x)
          (fun x => (iterDeltaPSupp (shA rest p) f hsup hbd).2 x) hY0 (le_refl _)
      · have h0 : avg (fun i : I => HypF rest i p) = 0 :=
          le_antisymm (le_of_not_gt hY0) (avg_nonneg fun i => pbox_nonneg _ _ _ _ _ _)
        have he1 : efun (Bc.length) ≠ 0 := by
          have := hefun (Bc.length); omega
        rw [h0, zero_pow he1, mul_zero]
        exact avg_nonneg fun ii => pbox_nonneg _ _ _ _ _ _
    -- ## 8. the final assembly
    have hBclen : Bc.length ≤ D := by
      have h1 : Bc.length ≤ (genuineSlots Λ).length := by
        rw [hBc]
        exact le_trans List.length_erase_le (List.length_filter_le _ _)
      omega
    have hCmono : (Finset.range (D + 1)).inf' ⟨0, by simp⟩ Cfun ≤ Cfun (Bc.length) :=
      Finset.inf'_le Cfun (Finset.mem_range.mpr (by omega))
    have hemono : efun (Bc.length) ≤ (Finset.range (D + 1)).sup' ⟨0, by simp⟩ efun :=
      Finset.le_sup' efun (Finset.mem_range.mpr (by omega))
    have hδpow : δ ^ ((Finset.range (D + 1)).sup' ⟨0, by simp⟩ efun)
        ≤ δ ^ efun (Bc.length) :=
      pow_le_pow_of_le_one (le_of_lt hδpos) hδ1 hemono
    have hJ : δ ^ efun (Bc.length) ≤ avg (fun z : Rest × QP => (Y z) ^ efun (Bc.length)) :=
      pow_le_avg_pow_of_avg hYnn (hefun (Bc.length)) (le_of_lt hδpos) hδY
    have hpt2 : ∀ z : Rest × QP, (Y z) ^ efun (Bc.length) ≤ Z z / Cfun (Bc.length) := by
      intro z
      rw [le_div_iff₀ (hCfun (Bc.length))]
      calc (Y z) ^ efun (Bc.length) * Cfun (Bc.length)
          = Cfun (Bc.length) * (Y z) ^ efun (Bc.length) := by ring
        _ ≤ Z z := hstep_pt z
    have havgZ : avg (fun z : Rest × QP => Z z / Cfun (Bc.length))
        = avg Z / Cfun (Bc.length) := by
      have h1 : (fun z : Rest × QP => Z z / Cfun (Bc.length))
          = fun z => (Cfun (Bc.length))⁻¹ * Z z := by
        funext z
        rw [div_eq_mul_inv, mul_comm]
      rw [h1, avg_const_mul, div_eq_mul_inv, mul_comm]
    calc (Finset.range (D + 1)).inf' ⟨0, by simp⟩ Cfun * δ ^ ((Finset.range (D + 1)).sup' ⟨0, by simp⟩ efun)
        ≤ Cfun (Bc.length) * δ ^ efun (Bc.length) := by
          exact mul_le_mul hCmono hδpow (by positivity) (le_of_lt (hCfun (Bc.length)))
      _ ≤ Cfun (Bc.length) * (avg Y) ^ efun (Bc.length) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (hCfun (Bc.length)))
          exact pow_le_pow_left₀ (le_of_lt hδpos) hδY _
      _ ≤ Cfun (Bc.length) * avg (fun z : Rest × QP => (Y z) ^ efun (Bc.length)) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (hCfun (Bc.length)))
          exact avg_pow_le_avg_pow Y hYnn (hefun (Bc.length))
      _ ≤ Cfun (Bc.length) * avg (fun z : Rest × QP => Z z / Cfun (Bc.length)) := by
          refine mul_le_mul_of_nonneg_left (avg_le_avg hpt2) (le_of_lt (hCfun (Bc.length)))
      _ = avg Z := by
          rw [havgZ, mul_div_cancel₀]
          exact ne_of_gt (hCfun (Bc.length))
      _ = cSt I q M N f (genuineSlots (refine Λ l)) := hT'.symm

end

end Work.Peluse.SwapC
