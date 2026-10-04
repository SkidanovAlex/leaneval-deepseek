import Mathlib
import Submission.Work.Diff.EXT.reactBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The derivative of the tower array of `∇^a Rm` in a geodesic frame

`Work.Diff.EXT.TowerArr g a D e z i j k l` is the `(i,j,k,l)`-component, in the frame `e`, of the
`a`-th covariant derivative `∇^a Rm` evaluated on the directions `D` (`a` of them) and the four
frame fields `e i, e j, e k, e l`.  Concretely it is the tower level `ckt g a` on the tuple
`Fin.append D W` with `W = ![e i, e j, e k, e l]`.

The recursion of `ckt` (`Work.Diff.EXT.mvfderiv_ckt_T2`) says that the derivative of a tower level
along a field `X` is the next tower level (with `X` prepended) plus one *slot correction* per entry
of the tuple.  For the array `TowerArr g a D e` the tuple is `Fin.append D W`, so the slot
corrections split into

* the `a` corrections of the differentiation directions `D r`, giving
  `∑ r, TowerArr g a (update D r (dirF g (D r) X)) e y i j k l`, and
* the four corrections of the *frame* fields `e i, e j, e k, e l`.

The point of the geodesic-frame hypothesis `hgeo : lcOf g (e i) y = 0` is that the four frame
corrections *vanish*: the tower is a tensor, so its value at `y` only depends on the *values* of
its arguments at `y` (`Work.Diff.EXT.ckt_val_dep_all`), and the correction field
`dirF g (e i) X = ∇_X e_i` vanishes at `y` because `∇e_i|_y = 0`.

Hence no frame-motion terms appear and the identity holds verbatim.

The proof is purely combinatorial: the two `Fin`-index manipulations
(`Fin.append (Fin.cons X D) W = Fin.cons X (Fin.append D W)` and the interaction of
`Function.update` with `Fin.append`) are isolated in the private helper lemmas below, and the four
vanishing frame corrections are dispatched with `Work.Diff.EXT.ckt_zero_slot_T2`.
-/

namespace Work.Diff.EXT.Mono

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! ## Two index lemmas for `Fin.append` -/

/-- Prepending `X` to `D` and then appending `W` is the same as prepending `X` to the appended
tuple `Fin.append D W` (the two sides live in the definitionally equal types `Fin (a+1+4) → α`
and `Fin ((a+4)+1) → α`). -/
private theorem fin_append_cons_eq {a : ℕ} {α : Type*} (X : α) (D : Fin a → α) (W : Fin 4 → α) :
    (Fin.append (Fin.cons X D) W : Fin (a + 1 + 4) → α) = Fin.cons X (Fin.append D W) := by
  funext s
  refine Fin.addCases (m := a + 1) (n := 4) (fun r => ?_) (fun t => ?_) s
  · rw [Fin.append_left]
    refine Fin.cases ?_ (fun i => ?_) r
    · rw [show (Fin.castAdd 4 (0 : Fin (a + 1)) : Fin ((a + 4) + 1)) = 0 from rfl,
        Fin.cons_zero, Fin.cons_zero]
    · rw [show (Fin.castAdd 4 (Fin.succ i) : Fin ((a + 4) + 1))
          = Fin.succ (Fin.castAdd 4 i) from rfl,
        Fin.cons_succ, Fin.cons_succ, Fin.append_left]
  · rw [Fin.append_right]
    rw [show (Fin.natAdd (a + 1) t : Fin ((a + 4) + 1)) = Fin.succ (Fin.natAdd a t) from by
      apply Fin.ext
      simp only [Fin.val_natAdd, Fin.val_succ]
      omega,
      Fin.cons_succ, Fin.append_right]

/-- Updating the `r`-th entry of the first block of an appended tuple is the same as appending the
updated tuple. -/
private theorem fin_update_append {a : ℕ} {α : Type*} (D : Fin a → α) (W : Fin 4 → α)
    (r : Fin a) (Y : α) :
    Function.update (Fin.append D W) (Fin.castAdd 4 r) Y
      = Fin.append (Function.update D r Y) W := by
  funext s
  refine Fin.addCases (m := a) (n := 4) (fun r' => ?_) (fun t => ?_) s
  · rcases eq_or_ne r' r with h | h
    · subst h
      rw [Function.update_self, Fin.append_left, Function.update_self]
    · have h2 : Fin.castAdd 4 r' ≠ Fin.castAdd 4 r :=
        fun hc => h (Fin.castAdd_inj.mp hc)
      rw [Function.update_of_ne h2, Fin.append_left, Fin.append_left,
        Function.update_of_ne h]
  · have h2 : Fin.natAdd a t ≠ Fin.castAdd 4 r := by
      intro hc
      have hv := congrArg Fin.val hc
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      have hr : (r : ℕ) < a := r.isLt
      omega
    rw [Function.update_of_ne h2, Fin.append_right, Fin.append_right]

/-! ## The derivative of the tower array -/

theorem towerArr_mvfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (y : M) (e : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (hgeo : ∀ i, Submission.Diff.lcOf g (e i) y = 0)
    (a : ℕ) (D : Fin a → Work.Diff.EXT.TField (I := I) (M := M))
    (hD : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (D r))
    (X : Work.Diff.EXT.TField (I := I) (M := M))
    (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X) :
    ∀ i j k l, mvfderiv I (fun z => Work.Diff.EXT.TowerArr g a D e z i j k l) y (X y)
      = Work.Diff.EXT.TowerArr g (a + 1) (Fin.cons X D) e y i j k l
        + ∑ r : Fin a, Work.Diff.EXT.TowerArr g a
            (Function.update D r (Work.Diff.EXT.dirF g (D r) X)) e y i j k l := by
  intro i j k l
  -- the tuple of frame fields filling the four curvature slots of the tower
  set W : Fin 4 → Work.Diff.EXT.TField (I := I) (M := M) := ![e i, e j, e k, e l] with hW
  -- unfold `TowerArr` into `ckt` on the appended tuple
  change mvfderiv I (fun z => Work.Diff.EXT.ckt g a (Fin.append D W) z) y (X y)
      = Work.Diff.EXT.ckt g (a + 1) (Fin.append (Fin.cons X D) W) y
        + ∑ r : Fin a, Work.Diff.EXT.ckt g a
            (Fin.append (Function.update D r (Work.Diff.EXT.dirF g (D r) X)) W) y
  -- the recursion of the tower: derivative = next level + slot corrections
  rw [Work.Diff.EXT.mvfderiv_ckt_T2 g a (Fin.append D W) X y]
  rw [fin_append_cons_eq X D W]
  -- smoothness of the entries of the appended tuple
  have hFS : ∀ s : Fin (a + 4), Work.Diff.EXT.SmoothF ((Fin.append D W) s) := by
    intro s
    refine Fin.addCases (m := a) (n := 4) (fun r => ?_) (fun t => ?_) s
    · rw [Fin.append_left]; exact hD r
    · rw [Fin.append_right, hW]
      fin_cases t
      · exact he i
      · exact he j
      · exact he k
      · exact he l
  -- cancel the common next-level term
  rw [add_left_cancel_iff]
  -- split the slot corrections into the `a` direction slots and the four frame slots
  rw [Fin.sum_univ_add]
  have h4 : (∑ t : Fin 4, Work.Diff.EXT.ckt g a
        (Function.update (Fin.append D W) (Fin.natAdd a t)
          (Work.Diff.EXT.dirF g ((Fin.append D W) (Fin.natAdd a t)) X)) y) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    have hWt : (Fin.append D W) (Fin.natAdd a t) = W t := Fin.append_right D W t
    rw [hWt]
    -- the frame correction `∇_X e_t` vanishes at `y` by the geodesic-frame hypothesis
    have hz : (Work.Diff.EXT.dirF g (W t) X) y = 0 := by
      rw [hW, Work.Diff.EXT.dirF]
      fin_cases t <;> simp [hgeo]
    -- and the tower is a tensor: its value only sees the values of its arguments at `y`
    exact Work.Diff.EXT.ckt_zero_slot_T2 hLC g a hFS (Fin.natAdd a t) y
      (Work.Diff.EXT.dirF_smooth hLC g (by rw [← hWt]; exact hFS (Fin.natAdd a t)) hX) hz
  rw [h4, add_zero]
  -- the remaining `a` direction slots match the claimed sum term by term
  apply Finset.sum_congr rfl
  intro r _
  rw [Fin.append_left, fin_update_append]

end Work.Diff.EXT.Mono
