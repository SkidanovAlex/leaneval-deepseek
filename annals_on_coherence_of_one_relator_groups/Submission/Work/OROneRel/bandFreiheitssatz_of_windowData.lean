import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winRho_winRoot
import Submission.Work.OROneRel.tlFreiheitssatz
import Submission.Work.OROneRel.ker_gaugeMap_le_winTree
import Submission.Work.OROneRel.winGateFreiheitssatz
import Submission.Work.OROneRel.unionAmalgam_injective
import Submission.Work.OROneRel.presentedGroup_treeDelete_iso
import Submission.Work.OROneRel.mem_normalClosure_singleton
import Submission.Work.OROneRel.exists_window_of_finite
import Submission.Work.OROneRel.levelChain
import Submission.Work.OROneRel.winGate_inj_counter
import Submission.Work.OROneRel.winTree_forest
import Submission.Work.OROneRel.mk_eq_one_of_walkIn_winTree
import Submission.Work.OROneRel.mem_winRho_range_iff
import Submission.Work.OROneRel.lsig_edgeWordSigned
import Submission.Work.OROneRel.betaCast_spec
import Submission.Work.OROneRel.exists_globalGauge_of_windowData_neg
import Submission.Work.OROneRel.decor_pow_flatMap
import Submission.Work.OROneRel.bandWindow_S1_iso
import Submission.Work.OROneRel.treeKill_walkCell_pow
import Submission.Work.OROneRel.range_winRho_eq_W

namespace Work.OROneRel

universe u

variable {α : Type u}

/-!
## The two-halves decomposition of the target

Write `ρ = winRho Wt c lo hi : F (winBeta) →* F α` and `v = winRoot Wt c lo hi u`, so that
`ρ v = u` (`winRho_winRoot`, for `cohom c u = 1` and `Wt 0 = 1` and the walk of `u` inside the
window).  The target is

  `(T)  ∀ x, ρ x ∈ ⟪u ^ l⟫ → x ∈ ⟪v ^ l⟫`

and it is *equivalent* to the conjunction of

* **(I) the intersection formula**
  `∀ z ∈ ⟪u^l⟫, z ∈ ρ.range → z ∈ ρ.map ⟪v^l⟫`, and
* **(K) the kernel formula** `∀ x, ρ x = 1 → x ∈ ⟪v^l⟫`.

`(T) ⟹ (I) ∧ (K)` is immediate (`(I)` is `(T)` applied to a preimage of `z`, `(K)` is `(T)` with
`ρ x = 1`); the converse is `band_of_intersection_and_kernel` below.  This is the decomposition used
by the route note `NOTES_bandFreiheitssatz_route.md`; both halves are *tree-independent in content*
(`ρ.range` and `ρ.map ⟪v^l⟫` do not depend on the spanning tree), so each may be proved for a
convenient gauge.
-/

/-- **(I) ∧ (K) imply (T).**  Purely group-theoretic: no hypothesis on `ρ`, `u`, `v`, `l`. -/
theorem band_of_intersection_and_kernel {G H : Type*} [Group G] [Group H] (ρ : H →* G)
    (u : G) (v : H) (l : ℕ)
    (hI : ∀ z ∈ Subgroup.normalClosure ({u ^ l} : Set G), z ∈ ρ.range →
      z ∈ Subgroup.map ρ (Subgroup.normalClosure ({v ^ l} : Set H)))
    (hK : ∀ x : H, ρ x = 1 → x ∈ Subgroup.normalClosure ({v ^ l} : Set H)) :
    ∀ x : H, ρ x ∈ Subgroup.normalClosure ({u ^ l} : Set G) →
      x ∈ Subgroup.normalClosure ({v ^ l} : Set H) := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hI (ρ x) hx ⟨x, rfl⟩)
  -- `hyx : ρ y = ρ x`
  have hxy : ρ (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hyx, mul_inv_cancel]
  have h1 : x * y⁻¹ ∈ Subgroup.normalClosure ({v ^ l} : Set H) := hK _ hxy
  have h2 : (x * y⁻¹) * y ∈ Subgroup.normalClosure ({v ^ l} : Set H) :=
    Subgroup.mul_mem _ h1 hy
  simpa using h2

/- **The class map is the gauge map precomposed with the inclusion of the non-tree edges** (already
available for general `α` as `Work.OROneRel.winRho_eq_gaugeMap`, in
`Submission/Work/OROneRel/twoLetterFreiheitssatz.lean`); it is what turns a statement about `winRho`
into a statement about `F (α × ℤ)` (the lift lemma of the chain route). -/

/-- **The forest lemma, with the walk started at an arbitrary level.**  A non-empty reduced word of
vanishing total weight whose walk (from the level `a`) uses only edges of the window's tree is
impossible: it would spell a non-trivial element of `F α` that is trivial by the telescoping
identity.  (`Work.OROneRel.winTree_forest` is the case `a = 0`; the general level is what the
"no closed sub-walk in the tree" argument needs, since the word of `Wt i` is only guaranteed to be a
*tree walk* for `i ∈ [lo,hi]`, while its sub-words are read from shifted levels.) -/
theorem winTree_forest_at {α : Type u} (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi a : ℤ}
    (L : List (α × Bool)) (hne : L ≠ []) (hred : FreeGroup.IsReduced L)
    (hlsig : lsig c L = 0)
    (hL : ∀ p ∈ decor c a L, coverEdge p ∈ winTree Wt c lo hi) : False := by
  classical
  have h1 : FreeGroup.mk L = 1 := mk_eq_one_of_walkIn_winTree Wt c lo hi a L hL hlsig
  exact mk_ne_one_of_isReduced hred hne h1

/-- **The gate inclusion of the `Z`-domain splitting, in kernel form.**

For an edge set `S ⊆ winE c lo hi` (the candidate *gate*, e.g. `winE c (lo+1) hi` or
`winE c lo (hi-1)`), if the vertex relator `winRoot` is cyclically reduced and is *not* supported on
the `β`-generators carried by `S`, then the free group on those generators maps injectively into
`F (β) / ⟪v ^ l⟫`; equivalently, an element of that free group whose image lies in `⟪v ^ l⟫` is
trivial.

This is `winGateFreiheitssatz` (the Magnus Freiheitssatz for the vertex relator) read as a statement
about normal closures.  It is the input that makes the amalgamated-product (van Kampen) route work:
the two amalgamating maps of a van Kampen step over a gate are injectivity statements of exactly
this shape (`unionAmalgam_injective` takes them as hypotheses). -/
theorem winBetaSub_inf_normalClosure {α : Type u} (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l) {S : Set (α × ℤ)}
    (hS : S ⊆ winE c lo hi)
    (hcyc : IsCyclicallyReducedRelator (winRoot Wt c lo hi u))
    (hout : ¬ SupportedOn (winRoot Wt c lo hi u) (Set.range (winBetaSubVal Wt c hS))) :
    ∀ y : FreeGroup (winBetaSub Wt c S),
      winBetaSubIncl Wt c hS y ∈
        Subgroup.normalClosure ({winRoot Wt c lo hi u ^ l} : Set (FreeGroup (winBeta Wt c lo hi))) →
      y = 1 := by
  classical
  intro y hy
  have hinj := winGateFreiheitssatz Wt c u l hl hS hcyc hout
  -- `winBetaSubIncl` is the generating map of the composite appearing in `winGateFreiheitssatz`
  have hmap : (FreeGroup.lift fun e : winBetaSub Wt c S =>
        FreeGroup.of (winBetaSubVal Wt c hS e)) = winBetaSubIncl Wt c hS := by
    refine FreeGroup.ext_hom _ _ fun e => ?_
    rw [FreeGroup.lift_apply_of, winBetaSubIncl_of]
  have hinj2 : Function.Injective (fun z : FreeGroup (winBetaSub Wt c S) =>
      (PresentedGroup.mk ({winRoot Wt c lo hi u ^ l} :
        Set (FreeGroup (winBeta Wt c lo hi)))) (winBetaSubIncl Wt c hS z)) := by
    rw [← hmap]
    exact hinj
  refine hinj2 ?_
  show (PresentedGroup.mk ({winRoot Wt c lo hi u ^ l} : Set (FreeGroup (winBeta Wt c lo hi))))
      (winBetaSubIncl Wt c hS y) =
    (PresentedGroup.mk ({winRoot Wt c lo hi u ^ l} : Set (FreeGroup (winBeta Wt c lo hi))))
      (winBetaSubIncl Wt c hS 1)
  rw [PresentedGroup.mk_eq_one_iff.mpr hy, map_one, map_one]

/-! ## The development of a word along a walk, and the injectivity of the class map

The class map `winRho Wt c lo hi : F (β) →* F α` of the window sends a non-tree edge `e = (x,i)` of
the window to its loop class `Wt i * x * (Wt (i + c x))⁻¹`.  It is *injective*: the development of
the loop word `edgeWord Wt c e` in the window basis `β` is the symbol of `e`
(`winDevAux_edgeWord`), the development is a function of the represented element of `F α`
(`winDevAux_eq_of_mk_eq`) and hence kills every word representing `1`
(`winDevAux_eq_one_of_mk_eq_one`), while the expansion `winExpand` of a word `v ∈ F β`
(`Submission/Work/OROneRel/mem_winRho_range_iff.lean`) satisfies
`FreeGroup.mk (winExpand v) = winRho v` (`winExpand_mk`) and `winDevAux (winExpand v) = v`.  So
`winRho v = 1` forces `v = 1`.

Nothing but the gauge laws (`hcoh`) and the tree condition `htree` are used; the relator hypotheses
of the target are *not* needed for the injectivity. -/

section GenericDev

variable {M : Type*} [Group M]

/-- **The development of a word along a walk**, for a prescribed level-indexed step function `st`:
reading the letter `a` in the direction `b` at running level `i` contributes `st i a b`. -/
noncomputable def devWord (st : ℤ → α → Bool → M) (c : α → ℤ) : ℤ → List (α × Bool) → M
  | _, [] => 1
  | i, (a, true) :: L => st i a true * devWord st c (i + c a) L
  | i, (a, false) :: L => st i a false * devWord st c (i - c a) L

theorem devWord_nil (st : ℤ → α → Bool → M) (c : α → ℤ) (i : ℤ) :
    devWord st c i ([] : List (α × Bool)) = 1 := rfl

theorem devWord_cons_true (st : ℤ → α → Bool → M) (c : α → ℤ) (i : ℤ) (a : α)
    (L : List (α × Bool)) :
    devWord st c i ((a, true) :: L) = st i a true * devWord st c (i + c a) L := rfl

theorem devWord_cons_false (st : ℤ → α → Bool → M) (c : α → ℤ) (i : ℤ) (a : α)
    (L : List (α × Bool)) :
    devWord st c i ((a, false) :: L) = st i a false * devWord st c (i - c a) L := rfl

theorem devWord_append (st : ℤ → α → Bool → M) (c : α → ℤ) (i : ℤ) (L₁ L₂ : List (α × Bool)) :
    devWord st c i (L₁ ++ L₂) = devWord st c i L₁ * devWord st c (i + lsig c L₁) L₂ := by
  induction L₁ generalizing i with
  | nil => simp [lsig, devWord_nil]
  | cons p L₁ ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · rw [List.cons_append, devWord_cons_false, ih (i - c a), lsig_cons_false, devWord_cons_false,
        mul_assoc, show (i - c a) + lsig c L₁ = i + (-c a + lsig c L₁) by ring]
    · rw [List.cons_append, devWord_cons_true, ih (i + c a), lsig_cons_true, devWord_cons_true,
        mul_assoc, add_assoc]

theorem devWord_cancel_true (st : ℤ → α → Bool → M) (c : α → ℤ)
    (h1 : ∀ i a, st i a true * st (i + c a) a false = 1) (i : ℤ) (a : α) (L : List (α × Bool)) :
    devWord st c i ((a, true) :: (a, false) :: L) = devWord st c i L := by
  rw [devWord_cons_true, devWord_cons_false, show (i + c a) - c a = i by ring, ← mul_assoc,
    h1 i a, one_mul]

theorem devWord_cancel_false (st : ℤ → α → Bool → M) (c : α → ℤ)
    (h2 : ∀ i a, st i a false * st (i - c a) a true = 1) (i : ℤ) (a : α) (L : List (α × Bool)) :
    devWord st c i ((a, false) :: (a, true) :: L) = devWord st c i L := by
  rw [devWord_cons_false, devWord_cons_true, show (i - c a) + c a = i by ring, ← mul_assoc,
    h2 i a, one_mul]

theorem devWord_step_not (st : ℤ → α → Bool → M) (c : α → ℤ)
    (h1 : ∀ i a, st i a true * st (i + c a) a false = 1)
    (h2 : ∀ i a, st i a false * st (i - c a) a true = 1)
    (i : ℤ) (L₃ L₄ : List (α × Bool)) (x : α) (b : Bool) :
    devWord st c i (L₃ ++ (x, b) :: (x, !b) :: L₄) = devWord st c i (L₃ ++ L₄) := by
  cases b
  · simp only [Bool.not_false]
    rw [devWord_append, devWord_append]
    exact congrArg (fun z => devWord st c i L₃ * z)
      (devWord_cancel_false st c h2 (i + lsig c L₃) x L₄)
  · simp only [Bool.not_true]
    rw [devWord_append, devWord_append]
    exact congrArg (fun z => devWord st c i L₃ * z)
      (devWord_cancel_true st c h1 (i + lsig c L₃) x L₄)

theorem devWord_step (st : ℤ → α → Bool → M) (c : α → ℤ)
    (h1 : ∀ i a, st i a true * st (i + c a) a false = 1)
    (h2 : ∀ i a, st i a false * st (i - c a) a true = 1)
    (i : ℤ) {L₁ L₂ : List (α × Bool)} (h : FreeGroup.Red.Step L₁ L₂) :
    devWord st c i L₁ = devWord st c i L₂ := by
  cases h
  exact devWord_step_not st c h1 h2 i _ _ _ _

noncomputable def devWordFun (st : ℤ → α → Bool → M) (c : α → ℤ)
    (h1 : ∀ i a, st i a true * st (i + c a) a false = 1)
    (h2 : ∀ i a, st i a false * st (i - c a) a true = 1) (i : ℤ) : FreeGroup α → M :=
  Quot.lift (devWord st c i) fun _L₁ _L₂ h => devWord_step st c h1 h2 i h

theorem devWordFun_mk (st : ℤ → α → Bool → M) (c : α → ℤ)
    (h1 : ∀ i a, st i a true * st (i + c a) a false = 1)
    (h2 : ∀ i a, st i a false * st (i - c a) a true = 1) (i : ℤ) (L : List (α × Bool)) :
    devWordFun st c h1 h2 i (FreeGroup.mk L) = devWord st c i L := rfl

theorem devWord_eq_of_mk_eq (st : ℤ → α → Bool → M) (c : α → ℤ)
    (h1 : ∀ i a, st i a true * st (i + c a) a false = 1)
    (h2 : ∀ i a, st i a false * st (i - c a) a true = 1) (i : ℤ) {L₁ L₂ : List (α × Bool)}
    (h : FreeGroup.mk L₁ = FreeGroup.mk L₂) : devWord st c i L₁ = devWord st c i L₂ := by
  rw [← devWordFun_mk st c h1 h2 i L₁, h, devWordFun_mk st c h1 h2 i L₂]

theorem devWord_eq_one_of_mk_eq_one (st : ℤ → α → Bool → M) (c : α → ℤ)
    (h1 : ∀ i a, st i a true * st (i + c a) a false = 1)
    (h2 : ∀ i a, st i a false * st (i - c a) a true = 1) (i : ℤ) {L : List (α × Bool)}
    (h : FreeGroup.mk L = 1) : devWord st c i L = 1 := by
  have h' : FreeGroup.mk L = FreeGroup.mk ([] : List (α × Bool)) := by rw [h]; rfl
  rw [devWord_eq_of_mk_eq st c h1 h2 i h', devWord_nil]

theorem devWord_map_flatten_of_lsig_eq_zero (st : ℤ → α → Bool → M) (c : α → ℤ)
    {γ : Type*} (l : List γ) (f : γ → List (α × Bool))
    (h : ∀ x ∈ l.map f, lsig c x = 0) (i : ℤ) :
    devWord st c i (l.map f).flatten = (l.map fun x => devWord st c i (f x)).prod := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have hx : lsig c (f x) = 0 := h (f x) (by simp)
    have ht : ∀ y ∈ t.map f, lsig c y = 0 := fun y hy => h y (by simp [hy])
    rw [List.map_cons, List.flatten_cons, devWord_append, hx, add_zero, ih ht, List.map_cons,
      List.prod_cons]

end GenericDev

/-! ## The window step -/

/-- The symbol contributed by the traversal of the edge `e` of the level graph in the direction `b`,
*if* `e` is an edge of the window of non-trivial loop class, and `1` otherwise. -/
noncomputable def winDevEdge (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (e : α × ℤ)
    (b : Bool) : FreeGroup (winBeta Wt c lo hi) := by
  classical
  exact if h : e ∈ winE c lo hi ∧ coverClassAt Wt c e ≠ 1 then
    (bif b then FreeGroup.of (⟨e, h⟩ : winBeta Wt c lo hi)
      else (FreeGroup.of (⟨e, h⟩ : winBeta Wt c lo hi))⁻¹)
  else 1

/-- The step of the window development: reading the letter `a` in the direction `b` at running level
`i` traverses the edge `(a, i)` (for `b = true`) or `(a, i - c a)` (for `b = false`). -/
noncomputable def winDevStep (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (i : ℤ) (a : α)
    (b : Bool) : FreeGroup (winBeta Wt c lo hi) :=
  winDevEdge Wt c lo hi (a, if b then i else i - c a) b

theorem winDevStep_true (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (i : ℤ) (a : α) :
    winDevStep Wt c lo hi i a true = winDevEdge Wt c lo hi (a, i) true := rfl

theorem winDevStep_false (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (i : ℤ) (a : α) :
    winDevStep Wt c lo hi i a false = winDevEdge Wt c lo hi (a, i - c a) false := rfl

theorem winDevEdge_true_of (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (e : α × ℤ)
    (h : e ∈ winE c lo hi ∧ coverClassAt Wt c e ≠ 1) :
    winDevEdge Wt c lo hi e true = FreeGroup.of (⟨e, h⟩ : winBeta Wt c lo hi) := by
  unfold winDevEdge
  rw [dif_pos h]
  simp only [cond_true]
  rfl

theorem winDevEdge_false_of (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (e : α × ℤ)
    (h : e ∈ winE c lo hi ∧ coverClassAt Wt c e ≠ 1) :
    winDevEdge Wt c lo hi e false = (FreeGroup.of (⟨e, h⟩ : winBeta Wt c lo hi))⁻¹ := by
  unfold winDevEdge
  rw [dif_pos h]
  simp only [cond_false]
  rfl

theorem winDevEdge_true_of_not (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (e : α × ℤ)
    (h : ¬ (e ∈ winE c lo hi ∧ coverClassAt Wt c e ≠ 1)) :
    winDevEdge Wt c lo hi e true = 1 := by
  unfold winDevEdge
  rw [dif_neg h]

theorem winDevEdge_false_of_not (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (e : α × ℤ)
    (h : ¬ (e ∈ winE c lo hi ∧ coverClassAt Wt c e ≠ 1)) :
    winDevEdge Wt c lo hi e false = 1 := by
  unfold winDevEdge
  rw [dif_neg h]

theorem winDevEdge_eq_one_of_class (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (e : α × ℤ)
    (h : coverClassAt Wt c e = 1) (b : Bool) : winDevEdge Wt c lo hi e b = 1 := by
  rcases Bool.eq_false_or_eq_true b with rfl | rfl
  · exact winDevEdge_true_of_not Wt c lo hi e (fun hc => hc.2 h)
  · exact winDevEdge_false_of_not Wt c lo hi e (fun hc => hc.2 h)

theorem winDevEdge_mul_inv (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (e : α × ℤ) :
    winDevEdge Wt c lo hi e true * winDevEdge Wt c lo hi e false = 1 := by
  classical
  by_cases h : e ∈ winE c lo hi ∧ coverClassAt Wt c e ≠ 1
  · rw [winDevEdge_true_of Wt c lo hi e h, winDevEdge_false_of Wt c lo hi e h]
    exact mul_inv_cancel _
  · rw [winDevEdge_true_of_not Wt c lo hi e h, winDevEdge_false_of_not Wt c lo hi e h, mul_one]

theorem winDevEdge_inv_mul (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (e : α × ℤ) :
    winDevEdge Wt c lo hi e false * winDevEdge Wt c lo hi e true = 1 :=
  (mul_eq_one_comm).mpr (winDevEdge_mul_inv Wt c lo hi e)

theorem winDevStep_mul (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (i : ℤ) (a : α) :
    winDevStep Wt c lo hi i a true * winDevStep Wt c lo hi (i + c a) a false = 1 := by
  rw [winDevStep_true, winDevStep_false, show i + c a - c a = i by ring]
  exact winDevEdge_mul_inv Wt c lo hi (a, i)

theorem winDevStep_inv_mul (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (i : ℤ) (a : α) :
    winDevStep Wt c lo hi i a false * winDevStep Wt c lo hi (i - c a) a true = 1 := by
  rw [winDevStep_false, winDevStep_true]
  exact winDevEdge_inv_mul Wt c lo hi (a, i - c a)

/-! ## The window development -/

/-- The development of a word in the window basis: the product of the symbols of the traversals of
its walk, with the non-tree edges of the window as alphabet. -/
noncomputable abbrev winDevAux (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    ℤ → List (α × Bool) → FreeGroup (winBeta Wt c lo hi) :=
  devWord (winDevStep Wt c lo hi) c

theorem winDevAux_nil (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (i : ℤ) :
    winDevAux Wt c lo hi i ([] : List (α × Bool)) = 1 := rfl

theorem winDevAux_cons_true (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (i : ℤ) (a : α)
    (L : List (α × Bool)) :
    winDevAux Wt c lo hi i ((a, true) :: L)
      = winDevStep Wt c lo hi i a true * winDevAux Wt c lo hi (i + c a) L := rfl

theorem winDevAux_cons_false (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (i : ℤ) (a : α)
    (L : List (α × Bool)) :
    winDevAux Wt c lo hi i ((a, false) :: L)
      = winDevStep Wt c lo hi i a false * winDevAux Wt c lo hi (i - c a) L := rfl

theorem winDevAux_append (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (i : ℤ)
    (L₁ L₂ : List (α × Bool)) :
    winDevAux Wt c lo hi i (L₁ ++ L₂)
      = winDevAux Wt c lo hi i L₁ * winDevAux Wt c lo hi (i + lsig c L₁) L₂ :=
  devWord_append (winDevStep Wt c lo hi) c i L₁ L₂

theorem winDevAux_eq_of_mk_eq (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (i : ℤ)
    {L₁ L₂ : List (α × Bool)} (h : FreeGroup.mk L₁ = FreeGroup.mk L₂) :
    winDevAux Wt c lo hi i L₁ = winDevAux Wt c lo hi i L₂ :=
  devWord_eq_of_mk_eq (winDevStep Wt c lo hi) c (winDevStep_mul Wt c lo hi)
    (winDevStep_inv_mul Wt c lo hi) i h

theorem winDevAux_eq_one_of_mk_eq_one (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (i : ℤ)
    {L : List (α × Bool)} (h : FreeGroup.mk L = 1) : winDevAux Wt c lo hi i L = 1 :=
  devWord_eq_one_of_mk_eq_one (winDevStep Wt c lo hi) c (winDevStep_mul Wt c lo hi)
    (winDevStep_inv_mul Wt c lo hi) i h

/-- The development of a concatenation of words of vanishing weight, read from one level. -/
theorem winDevAux_map_flatten_of_lsig_eq_zero (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    {γ : Type*} (l : List γ) (f : γ → List (α × Bool))
    (h : ∀ x ∈ l.map f, lsig c x = 0) (i : ℤ) :
    winDevAux Wt c lo hi i (l.map f).flatten = (l.map fun x => winDevAux Wt c lo hi i (f x)).prod :=
  devWord_map_flatten_of_lsig_eq_zero (winDevStep Wt c lo hi) c l f h i

/-- **The development of a walk of trivial loop classes is trivial.** -/
theorem winDevAux_eq_one_of_trivial (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (i : ℤ)
    (L : List (α × Bool))
    (h : ∀ e ∈ decor c i L, coverClassAt Wt c (coverEdge e) = 1) :
    winDevAux Wt c lo hi i L = 1 := by
  induction L generalizing i with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · rw [winDevAux_cons_false]
      have hhead : winDevStep Wt c lo hi i a false = 1 := by
        rw [winDevStep_false]
        exact winDevEdge_eq_one_of_class Wt c lo hi (a, i - c a)
          (h ((a, i - c a), false) (by simp [decor])) false
      have htail : ∀ e ∈ decor c (i - c a) L, coverClassAt Wt c (coverEdge e) = 1 := by
        intro e he
        exact h e (by simp [decor, he])
      rw [hhead, one_mul, ih (i - c a) htail]
    · rw [winDevAux_cons_true]
      have hhead : winDevStep Wt c lo hi i a true = 1 := by
        rw [winDevStep_true]
        exact winDevEdge_eq_one_of_class Wt c lo hi (a, i)
          (h ((a, i), true) (by simp [decor])) true
      have htail : ∀ e ∈ decor c (i + c a) L, coverClassAt Wt c (coverEdge e) = 1 := by
        intro e he
        exact h e (by simp [decor, he])
      rw [hhead, one_mul, ih (i + c a) htail]

/-! ## The development of the loop words of the window -/

/-- The gauge word at a level of the window has trivial development. -/
theorem winDevAux_wordOf_Wt (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (hWt : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ p ∈ decor c 0 (wordOf (Wt i)), coverEdge p ∈ winTree Wt c lo hi)
    (i : ℤ) (h1 : lo ≤ i) (h2 : i ≤ hi) : winDevAux Wt c lo hi 0 (wordOf (Wt i)) = 1 :=
  winDevAux_eq_one_of_trivial Wt c lo hi 0 (wordOf (Wt i))
    (fun p hp => (mem_winTree.mp (hWt i h1 h2 p hp)).2)

/-- The *inverse* gauge word at a level of the window has trivial development (the walk of the
inverse gauge word is the mirror image of the walk of the gauge word). -/
theorem winDevAux_wordOf_inv_Wt (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (hWt : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ p ∈ decor c 0 (wordOf (Wt i)), coverEdge p ∈ winTree Wt c lo hi)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i)
    (i : ℤ) (h1 : lo ≤ i) (h2 : i ≤ hi) : winDevAux Wt c lo hi i (wordOf ((Wt i)⁻¹)) = 1 := by
  have hlsig : lsig c (wordOf (Wt i)) = i := lsig_wordOf_Wt hcoh i
  have hdec : decor c i (FreeGroup.invRev (wordOf (Wt i)))
      = (decor c 0 (wordOf (Wt i))).reverse.map (fun p => (p.1, !p.2)) := by
    have h := decor_invRev c 0 (wordOf (Wt i))
    rwa [hlsig, zero_add] at h
  refine winDevAux_eq_one_of_trivial Wt c lo hi i (wordOf ((Wt i)⁻¹)) fun p hp => ?_
  rw [wordOf_inv, hdec] at hp
  rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
  rw [List.mem_reverse] at hq
  exact (mem_winTree.mp (hWt i h1 h2 q hq)).2

/-- **The development of the loop word of a window edge is the symbol of that edge.** -/
theorem winDevAux_edgeWord (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (hWt : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ p ∈ decor c 0 (wordOf (Wt i)), coverEdge p ∈ winTree Wt c lo hi)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i) (e : winBeta Wt c lo hi) :
    winDevAux Wt c lo hi 0 (edgeWord Wt c e.1) = FreeGroup.of e := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_winE.mp e.2.1
  have hli : lsig c (wordOf (Wt e.1.2)) = e.1.2 := lsig_wordOf_Wt hcoh e.1.2
  have hstep : winDevAux Wt c lo hi (e.1.2 + c e.1.1) (wordOf ((Wt (e.1.2 + c e.1.1))⁻¹)) = 1 :=
    winDevAux_wordOf_inv_Wt Wt c hWt hcoh (e.1.2 + c e.1.1) h3 h4
  have hedge : winDevEdge Wt c lo hi e.1 true = FreeGroup.of (⟨e.1, ⟨e.2.1, e.2.2⟩⟩ :
    winBeta Wt c lo hi) := winDevEdge_true_of Wt c lo hi e.1 ⟨e.2.1, e.2.2⟩
  rw [edgeWord, List.append_assoc, winDevAux_append, winDevAux_append, hli, zero_add,
    winDevAux_wordOf_Wt Wt c hWt e.1.2 h1 h2, one_mul, winDevAux_cons_true, lsig_singleton_true,
    winDevAux_nil, mul_one, hstep, mul_one, winDevStep_true, hedge]
  exact congrArg FreeGroup.of (Subtype.ext rfl)

/-- The loop word of an edge traversed *backwards* (the mirror word of `edgeWord`), which represents
the inverse of the loop class and has the inverse development. -/
noncomputable def edgeWordInv (Wt : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    List (α × Bool) :=
  wordOf (Wt (e.2 + c e.1)) ++ [(e.1, false)] ++ wordOf ((Wt e.2)⁻¹)

/-- **The development of the mirror loop word of a window edge is the inverse symbol.** -/
theorem winDevAux_edgeWordInv (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (hWt : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ p ∈ decor c 0 (wordOf (Wt i)), coverEdge p ∈ winTree Wt c lo hi)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i) (e : winBeta Wt c lo hi) :
    winDevAux Wt c lo hi 0 (edgeWordInv Wt c e.1) = (FreeGroup.of e)⁻¹ := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_winE.mp e.2.1
  have hli : lsig c (wordOf (Wt (e.1.2 + c e.1.1))) = e.1.2 + c e.1.1 :=
    lsig_wordOf_Wt hcoh (e.1.2 + c e.1.1)
  have hstep : winDevAux Wt c lo hi ((e.1.2 + c e.1.1) + -c e.1.1) (wordOf ((Wt e.1.2)⁻¹)) = 1 := by
    rw [show (e.1.2 + c e.1.1) + -c e.1.1 = e.1.2 by ring]
    exact winDevAux_wordOf_inv_Wt Wt c hWt hcoh e.1.2 h1 h2
  have hedge : winDevEdge Wt c lo hi e.1 false
      = (FreeGroup.of (⟨e.1, ⟨e.2.1, e.2.2⟩⟩ : winBeta Wt c lo hi))⁻¹ :=
    winDevEdge_false_of Wt c lo hi e.1 ⟨e.2.1, e.2.2⟩
  have hlev : (e.1).2 + c (e.1).1 - c (e.1).1 = (e.1).2 := by ring
  rw [edgeWordInv, List.append_assoc, winDevAux_append, winDevAux_append, hli, zero_add,
    winDevAux_wordOf_Wt Wt c hWt (e.1.2 + c e.1.1) h3 h4, one_mul, winDevAux_cons_false,
    lsig_singleton_false, winDevAux_nil, mul_one, hstep, mul_one, winDevStep_false, hlev, hedge]
  exact congrArg (fun z => z⁻¹) (congrArg FreeGroup.of (Subtype.ext rfl))

/-- `edgeWordInv` represents the inverse of the loop class of `e`. -/
theorem mk_edgeWordInv (Wt : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    FreeGroup.mk (edgeWordInv Wt c e) = (coverClassAt Wt c e)⁻¹ := by
  have h₁ : FreeGroup.mk (edgeWordInv Wt c e)
      = Wt (e.2 + c e.1) * (FreeGroup.of e.1)⁻¹ * (Wt e.2)⁻¹ := by
    rw [edgeWordInv, mk_append, mk_append, mk_wordOf, mk_singleton_false, mk_wordOf]
  rw [h₁, coverClassAt, gaugeMap_of]
  group

/-- `edgeWordInv` and the reversed `edgeWord` represent the same element. -/
theorem mk_edgeWordInv_eq_mk_invRev (Wt : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    FreeGroup.mk (edgeWordInv Wt c e) = FreeGroup.mk (FreeGroup.invRev (edgeWord Wt c e)) := by
  rw [mk_edgeWordInv, ← FreeGroup.inv_mk, mk_edgeWord]

/-- **The development of the signed loop word of a window edge is the signed symbol.** -/
theorem winDevAux_edgeWordSigned (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (hWt : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ p ∈ decor c 0 (wordOf (Wt i)), coverEdge p ∈ winTree Wt c lo hi)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i) (e : winBeta Wt c lo hi) (b : Bool) :
    winDevAux Wt c lo hi 0 (edgeWordSigned Wt c e.1 b)
      = (if b then FreeGroup.of e else (FreeGroup.of e)⁻¹) := by
  cases b
  · rw [show edgeWordSigned Wt c e.1 false = FreeGroup.invRev (edgeWord Wt c e.1) from by
      simp [edgeWordSigned]]
    rw [winDevAux_eq_of_mk_eq Wt c lo hi 0 (mk_edgeWordInv_eq_mk_invRev Wt c e.1).symm,
      winDevAux_edgeWordInv Wt c hWt hcoh e]
    simp
  · rw [show edgeWordSigned Wt c e.1 true = edgeWord Wt c e.1 from by simp [edgeWordSigned],
      winDevAux_edgeWord Wt c hWt hcoh e]
    simp

/-- **The development of the expansion of a word of the window basis is the word itself.** -/
theorem winDevAux_winExpand (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (hWt : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ p ∈ decor c 0 (wordOf (Wt i)), coverEdge p ∈ winTree Wt c lo hi)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i)
    (v : FreeGroup (winBeta Wt c lo hi)) : winDevAux Wt c lo hi 0 (winExpand Wt c lo hi v) = v := by
  have hpiece : ∀ x ∈ (FreeGroup.toWord v).map
      (fun p : winBeta Wt c lo hi × Bool => edgeWordSigned Wt c p.1.1 p.2), lsig c x = 0 := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨p, -, rfl⟩
    have hmem := winBeta_val_mem (Wt := Wt) (c := c) p.1
    obtain ⟨hp1, hp2, hp3, hp4⟩ := mem_winE.mp hmem
    exact lsig_edgeWordSigned Wt c p.1.1 p.2 (by rw [hcoh p.1.1.2]; rfl)
      (by rw [hcoh (p.1.1.2 + c p.1.1.1)]; rfl)
  have hstep : ((FreeGroup.toWord v).map (fun p : winBeta Wt c lo hi × Bool =>
        winDevAux Wt c lo hi 0 (edgeWordSigned Wt c p.1.1 p.2))).prod
      = ((FreeGroup.toWord v).map (fun p : winBeta Wt c lo hi × Bool =>
        if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹)).prod := by
    refine congrArg List.prod (List.map_congr_left fun p _ => ?_)
    exact winDevAux_edgeWordSigned Wt c hWt hcoh p.1 p.2
  rw [winExpand, winDevAux_map_flatten_of_lsig_eq_zero Wt c lo hi (FreeGroup.toWord v)
    (fun p : winBeta Wt c lo hi × Bool => edgeWordSigned Wt c p.1.1 p.2) hpiece 0, hstep,
    ← mk_eq_prod_map_signed (FreeGroup.toWord v), FreeGroup.mk_toWord]

/-- **The class map of the window is injective.**  Only the gauge laws and the tree condition are
needed. -/
theorem winRho_injective (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (hWt : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ p ∈ decor c 0 (wordOf (Wt i)), coverEdge p ∈ winTree Wt c lo hi)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i) :
    Function.Injective (winRho Wt c lo hi) := by
  intro x y hxy
  have h1 : winRho Wt c lo hi (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have h2 : FreeGroup.mk (winExpand Wt c lo hi (x * y⁻¹)) = 1 := by rw [winExpand_mk, h1]
  have h3 : winDevAux Wt c lo hi 0 (winExpand Wt c lo hi (x * y⁻¹)) = 1 :=
    winDevAux_eq_one_of_mk_eq_one Wt c lo hi 0 h2
  have h4 : winDevAux Wt c lo hi 0 (winExpand Wt c lo hi (x * y⁻¹)) = x * y⁻¹ :=
    winDevAux_winExpand Wt c hWt hcoh (x * y⁻¹)
  exact mul_inv_eq_one.mp (by rw [← h4, h3])

/-- **The kernel formula `(K)`**, which is the whole content of the target once the class map is
known to be injective (the intersection formula `(I)` being the remaining obligation). -/
theorem winRho_ker_le_normalClosure (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (hWt : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ p ∈ decor c 0 (wordOf (Wt i)), coverEdge p ∈ winTree Wt c lo hi)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i) (v : FreeGroup (winBeta Wt c lo hi))
    {x : FreeGroup (winBeta Wt c lo hi)} (hx : winRho Wt c lo hi x = 1) :
    x ∈ Subgroup.normalClosure ({v} : Set (FreeGroup (winBeta Wt c lo hi))) := by
  have hx1 : x = 1 := winRho_injective Wt c hWt hcoh (by rw [hx, map_one])
  rw [hx1]
  exact Subgroup.one_mem _

/-- **The target follows from the intersection formula `(I)`.**  The kernel formula `(K)` is free
once the class map is injective (`winRho_injective`, whose hypotheses are the gauge laws and the tree
condition), so the whole content of the band Freiheitssatz is the *intersection formula*

`(I) : ∀ z ∈ ⟪u ^ l⟫, z ∈ (winRho Wt c lo hi).range → z ∈ (winRho Wt c lo hi).map ⟪winRoot ^ l⟫`,

which is the statement that the band domain `π₁ (D₀) = F (β) / ⟪v ^ l⟫` injects into
`G = ⟨α | u ^ l⟩`.  This lemma is the assembly layer on top of `(I)`. -/
theorem bandFreiheitssatz_of_windowData_of_intersection {α : Type u} (Wt : ℤ → FreeGroup α)
    (c : α → ℤ) {lo hi : ℤ} (u : FreeGroup α) (l : ℕ)
    (hW0 : Wt 0 = 1) (hcu : cohom c u = 1)
    (hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi)
    (hWt : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ p ∈ decor c 0 (wordOf (Wt i)), coverEdge p ∈ winTree Wt c lo hi)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i)
    (hI : ∀ z ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)),
      z ∈ (winRho Wt c lo hi).range →
        z ∈ Subgroup.map (winRho Wt c lo hi)
          (Subgroup.normalClosure ({winRoot Wt c lo hi u ^ l} :
            Set (FreeGroup (winBeta Wt c lo hi))))) :
    ∀ x : FreeGroup (winBeta Wt c lo hi),
      winRho Wt c lo hi x ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure
          ({winRoot Wt c lo hi u ^ l} : Set (FreeGroup (winBeta Wt c lo hi))) :=
  band_of_intersection_and_kernel (winRho Wt c lo hi) u (winRoot Wt c lo hi u) l hI
    (fun x hx => winRho_ker_le_normalClosure Wt c hWt hcoh (winRoot Wt c lo hi u ^ l) hx)

/-- **A weight admitting a gauge is not identically zero.**  If `cohom c (Wt i) = ofAdd i` for all
`i`, then some letter has non-zero weight: otherwise `cohom c` would be the trivial homomorphism and
`cohom c (Wt 1) = 1 ≠ ofAdd 1`. -/
theorem exists_letter_cohom_ne_zero {α : Type*} {c : α → ℤ} {Wt : ℤ → FreeGroup α}
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i) :
    ∃ x : α, c x ≠ 0 := by
  by_contra h
  push_neg at h
  have h1 : cohom c = 1 := by
    refine FreeGroup.ext_hom _ 1 fun x => ?_
    rw [cohom_of, h x]
    rfl
  have h2 := hcoh 1
  rw [h1] at h2
  have : (1 : ℤ) = 0 :=
    Multiplicative.ofAdd.injective (by simpa using h2.symm)
  exact one_ne_zero this

/-- **The walk of a non-trivial word starts at level `0`.**  Hence, if every traversal of the walk of
`u` lies in the window `[lo,hi]`, the window contains the level `0`. -/
theorem window_contains_zero {α : Type*} {c : α → ℤ} {lo hi : ℤ} {u : FreeGroup α} (hu : u ≠ 1)
    (hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi) :
    lo ≤ 0 ∧ 0 ≤ hi := by
  cases hL : wordOf u with
  | nil => exact absurd (by rw [← mk_wordOf u, hL]; rfl) hu
  | cons p ps =>
    obtain ⟨x, b⟩ := p
    cases b
    · have h1 : ((x, 0 - c x), false) ∈ decor c 0 (wordOf u) := by
        rw [hL]
        exact List.mem_cons_self
      have h2 := hwin _ h1
      rw [mem_winE] at h2
      exact ⟨by have := h2.2.2.1; simp only [coverEdge] at this; omega,
        by have := h2.2.2.2; simp only [coverEdge] at this; omega⟩
    · have h1 : ((x, 0), true) ∈ decor c 0 (wordOf u) := by
        rw [hL]
        exact List.mem_cons_self
      have h2 := hwin _ h1
      rw [mem_winE] at h2
      exact ⟨h2.1, h2.2.1⟩

/-- **Gauge transport of the window statement.**  If two gauges have the same loop classes on every
edge of the window, then the window Freiheitssatz for one is *equivalent* to the window
Freiheitssatz for the other: `betaCast_spec` transports the alphabet `β`, the class map `winRho` and
the deleted walk word `winRoot` along the canonical identification of the two `β`'s.

This is what lets the proof of the target be run with a *global* extension gauge (whose trivial edges
outside the window behave well, which is what `ker_gaugeMap_le_winTree` and the transfer
`exists_lift_mem_normalClosure_tree_walk` need) and then transported back to the gauge of the
target. -/
theorem bandFreiheitssatz_of_gauge_agree {α : Type*} {c : α → ℤ} {lo hi : ℤ} {u : FreeGroup α}
    {l : ℕ} {Wt Wt' : ℤ → FreeGroup α}
    (hband : ∀ e ∈ winE c lo hi, coverClassAt Wt' c e = coverClassAt Wt c e)
    (h : ∀ x : FreeGroup (winBeta Wt' c lo hi),
      winRho Wt' c lo hi x ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure ({winRoot Wt' c lo hi u ^ l} :
          Set (FreeGroup (winBeta Wt' c lo hi)))) :
    ∀ x : FreeGroup (winBeta Wt c lo hi),
      winRho Wt c lo hi x ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure ({winRoot Wt c lo hi u ^ l} :
          Set (FreeGroup (winBeta Wt c lo hi))) := by
  classical
  obtain ⟨φ, ψ, hψφ, hρ, hroot⟩ := betaCast_spec hband
  intro x hx
  have hx' : winRho Wt' c lo hi (FreeGroup.map φ x) ∈
      Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) := by
    rw [hρ]; exact hx
  have hmem : FreeGroup.map φ x ∈ Subgroup.normalClosure
      ({winRoot Wt' c lo hi u ^ l} : Set (FreeGroup (winBeta Wt' c lo hi))) := h _ hx'
  have hrootψ : FreeGroup.map ψ (winRoot Wt' c lo hi u ^ l) =
      (winRoot Wt c lo hi u) ^ l := by
    rw [map_pow, ← hroot, hψφ]
  have hle : Subgroup.map (FreeGroup.map ψ) (Subgroup.normalClosure
      ({winRoot Wt' c lo hi u ^ l} : Set (FreeGroup (winBeta Wt' c lo hi))))
      ≤ Subgroup.normalClosure
        ({winRoot Wt c lo hi u ^ l} : Set (FreeGroup (winBeta Wt c lo hi))) := by
    refine le_trans (Subgroup.map_normalClosure_le _ _) ?_
    rw [Set.image_singleton, hrootψ]
  have hfin : FreeGroup.map ψ (FreeGroup.map φ x) ∈ Subgroup.normalClosure
      ({winRoot Wt c lo hi u ^ l} : Set (FreeGroup (winBeta Wt c lo hi))) :=
    hle (Subgroup.mem_map_of_mem _ hmem)
  rwa [hψφ] at hfin

/-- **A sufficient condition for the target: a left inverse of `winRho` on `F (β)`.**  If there is a
homomorphism `π : F α →* F β` with `π (winRho y) = y` for all `y ∈ F β`, then the window
Freiheitssatz holds: `π` carries the normal closure of `u ^ l` into the normal closure of
`π (u ^ l) = winRoot ^ l`, so `x = π (winRho x) ∈ ⟪winRoot ^ l⟫`.

Geometrically this is the case in which `ρ (F β) = π₁ (D₀)` is a *free factor* of `F α`: a retraction
`F α →* F β` of the class map exists exactly then (retracts of free groups are free factors, so this
can only happen when `β` has at most `|α|` elements — e.g. in the five-cycle datum and in the example
of §4 of `NOTES_bandFreiheitssatz_tower_obstruction.md`, where `β` is a singleton and the system
`π (winRho e) = e` reduces to a linear equation in the abelianisation of `F β`).  It is *not*
available in the interesting cases (`β` bigger than `α`), so this lemma is a genuine special case,
but it isolates the algebraic content of the statement when the retraction exists. -/
theorem bandFreiheitssatz_of_retraction {α : Type u} {c : α → ℤ} {lo hi : ℤ} {u : FreeGroup α}
    {l : ℕ} {Wt : ℤ → FreeGroup α}
    (hroot : u = winRho Wt c lo hi (winRoot Wt c lo hi u))
    (hπ : ∃ π : FreeGroup α →* FreeGroup (winBeta Wt c lo hi),
      ∀ y : FreeGroup (winBeta Wt c lo hi), π (winRho Wt c lo hi y) = y) :
    ∀ x : FreeGroup (winBeta Wt c lo hi),
      winRho Wt c lo hi x ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure ({winRoot Wt c lo hi u ^ l} :
          Set (FreeGroup (winBeta Wt c lo hi))) := by
  classical
  obtain ⟨π, hπ⟩ := hπ
  intro x hx
  have hle : Subgroup.map π (Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)))
      ≤ Subgroup.normalClosure
        ({π (u ^ l)} : Set (FreeGroup (winBeta Wt c lo hi))) :=
    le_trans (Subgroup.map_normalClosure_le _ _) (by rw [Set.image_singleton])
  have hmem := hle (Subgroup.mem_map_of_mem π hx)
  rw [hπ x, map_pow, hroot, hπ] at hmem
  exact hmem

/-- **The target reduces to its global-gauge form.**  The window statement for the gauge of the
target follows from the same statement for *any* gauge agreeing with `Wt` on the window (which is
what the target's hypotheses produce, `exists_globalGauge_of_windowData_neg`, and which is the form
in which the splitting/transfer arguments are run: the global gauge's trivial edges are what
`ker_gaugeMap_le_winTree` and `exists_lift_mem_normalClosure_tree_walk` control).

Everything except the uses of `hn` (to know that the walk of `u` is non-empty, so that the window
contains the level `0`), `hcoh` (to find a letter of non-zero weight) and `hcov` (to bound its
weight by the width of the window) is bookkeeping: the extension is applied, and the resulting
statement is transported back along `bandFreiheitssatz_of_gauge_agree`. -/
theorem bandFreiheitssatz_of_globalGauge {α : Type u} [Fintype α] [DecidableEq α]
    (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (hbad : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u → Work.OROneRel.eps x u ≠ 0)
    {c : α → ℤ} (hcu : Work.OROneRel.cohom c u = 1)
    {Wt : ℤ → FreeGroup α} {lo hi : ℤ}
    (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (hone : ∀ k : ℤ, k ≠ 0 →
      ¬ (∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
          lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧
            p.1.2 + k ≤ hi ∧ p.1.2 + c p.1.1 + k ≤ hi))
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ q ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge q ∈ Work.OROneRel.winTree Wt c lo hi)
    (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi)
    (hlast : ∃ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winTree Wt c lo hi)
    (hglobal : ∀ Wt' : ℤ → FreeGroup α,
      (∀ i : ℤ, lo ≤ i → i ≤ hi → Wt' i = Wt i) →
      (∀ i : ℤ, Work.OROneRel.cohom c (Wt' i) = Multiplicative.ofAdd i) →
      (∀ j : ℤ, ∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt' j)),
        Work.OROneRel.coverClassAt Wt' c (Work.OROneRel.coverEdge e) = 1) →
      ∀ x : FreeGroup (Work.OROneRel.winBeta Wt' c lo hi),
        Work.OROneRel.winRho Wt' c lo hi x ∈
            Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
          x ∈ Subgroup.normalClosure
            ({Work.OROneRel.winRoot Wt' c lo hi u ^ l} :
              Set (FreeGroup (Work.OROneRel.winBeta Wt' c lo hi)))) :
    ∀ x : FreeGroup (Work.OROneRel.winBeta Wt c lo hi),
      Work.OROneRel.winRho Wt c lo hi x ∈
          Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure
          ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))) := by
  have hu1 : u ≠ 1 := by
    intro h
    have h0 : relatorNorm u = 0 := by
      rw [h]
      exact (@FreeGroup.norm_eq_zero α (Classical.decEq α) (1 : FreeGroup α)).mpr rfl
    omega
  have h0 := window_contains_zero (c := c) (lo := lo) (hi := hi) hu1 hwin
  obtain ⟨x₀, hx₀⟩ := exists_letter_cohom_ne_zero (Wt := Wt) hcoh
  have hd : |c x₀| ≤ hi - lo := by
    obtain ⟨i, hi_mem⟩ := hcov x₀
    rw [mem_winE] at hi_mem
    obtain ⟨h1, h2, h3, h4⟩ := hi_mem
    simp only [Prod.fst] at h3 h4
    rw [abs_le]
    constructor <;> omega
  obtain ⟨Wt', hagree, hcoh', hwalk'⟩ :=
    exists_globalGauge_of_windowData_neg c Wt lo hi x₀ h0.1 h0.2 hx₀ hd hW0 hcoh htree
  refine bandFreiheitssatz_of_gauge_agree (Wt := Wt) (Wt' := Wt') ?_
    (hglobal Wt' hagree hcoh' hwalk')
  intro e he
  obtain ⟨h1, h2, h3, h4⟩ := he
  simp only [coverClassAt, gaugeMap_of, hagree e.2 h1 h2, hagree (e.2 + c e.1) h3 h4]

/-! ## The two gates of the window, and the minimality hypothesis `hone`

The tower/`ℤ`-domain route to the target decomposes the level complex `Y` into the translates
`D_k = winE c (lo+k) (hi+k)` of the band window and applies Seifert--van Kampen at each step.  The
step `π₁(⋃_{j<k} D_j) ↪ π₁(⋃_{j≤k} D_j)` needs, by the pushout criterion, the injectivity of the
*gate* map `π₁(D_k ∩ ⋃_{j<k} D_j) → π₁(D_k)`; the relevant gate is

  * `winE c (lo+1) hi`  (the window with the *bottom* level removed), and
  * `winE c lo (hi-1)`  (with the top level removed),

i.e. the subgraph on all but one extreme level.  The geometric Freiheitssatz for one-relator
complexes (Linton, *One-relator hierarchies*, Theorem 2.2; Magnus 1930) says that this injection
holds as soon as the attaching cycle is *not supported* on the gate, i.e. as soon as some traversal
of the walk of `u` (hence of `u^l`) leaves the gate.  That "not supported" fact is exactly what
`hone` (the minimality of the window) supplies, and the two lemmas below extract it.  Note that they
are statements about the *edge sets*, hence tree-independent: this is why they are the useful form
of the hypothesis (the `β`-description of the gate, `winBetaSub Wt c S`, is *not* the right object,
see `NOTES_bandFreiheitssatz_gate_obstruction.md`). -/

/-- **The walk of `u` is not supported on the top gate `winE c (lo+1) hi`**: some traversal of the
walk of `u` has an edge that does not lie in the window with the bottom level removed.  Immediate
from `hone` with `k = -1`, since `winE c (lo+1) hi ⊆ winE c (lo+1) (hi+1)`. -/
theorem exists_walk_not_supportedOn_topGate {α : Type u} {c : α → ℤ} {lo hi : ℤ} {u : FreeGroup α}
    (hone : ∀ k : ℤ, k ≠ 0 →
      ¬ (∀ p ∈ decor c 0 (wordOf u),
          lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧
            p.1.2 + k ≤ hi ∧ p.1.2 + c p.1.1 + k ≤ hi)) :
    ∃ p ∈ decor c 0 (wordOf u), coverEdge p ∉ winE c (lo + 1) hi := by
  by_contra h
  have hall : ∀ p, p ∈ decor c 0 (wordOf u) → coverEdge p ∈ winE c (lo + 1) hi := by
    intro p hp
    by_contra hnot
    exact h ⟨p, hp, hnot⟩
  refine hone (-1) (by norm_num) fun p hp => ?_
  have hp' := hall p hp
  simp only [mem_winE, coverEdge] at hp'
  obtain ⟨a1, a2, a3, a4⟩ := hp'
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **The walk of `u` is not supported on the bottom gate `winE c lo (hi-1)`**: some traversal of
the walk of `u` has an edge that does not lie in the window with the top level removed.  Immediate
from `hone` with `k = 1`, since `winE c lo (hi-1) ⊆ winE c (lo-1) (hi-1)`. -/
theorem exists_walk_not_supportedOn_bottomGate {α : Type u} {c : α → ℤ} {lo hi : ℤ}
    {u : FreeGroup α}
    (hone : ∀ k : ℤ, k ≠ 0 →
      ¬ (∀ p ∈ decor c 0 (wordOf u),
          lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧
            p.1.2 + k ≤ hi ∧ p.1.2 + c p.1.1 + k ≤ hi)) :
    ∃ p ∈ decor c 0 (wordOf u), coverEdge p ∉ winE c lo (hi - 1) := by
  by_contra h
  have hall : ∀ p, p ∈ decor c 0 (wordOf u) → coverEdge p ∈ winE c lo (hi - 1) := by
    intro p hp
    by_contra hnot
    exact h ⟨p, hp, hnot⟩
  refine hone 1 (by norm_num) fun p hp => ?_
  have hp' := hall p hp
  simp only [mem_winE, coverEdge] at hp'
  obtain ⟨a1, a2, a3, a4⟩ := hp'
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **The walk of `u` touches the top level `hi`**: some traversal has `hi` among the two levels of
its edge.  A consequence of `hone` with `k = 1` and of the walk lying in the window. -/
theorem exists_walk_edge_touching_top {α : Type u} {c : α → ℤ} {lo hi : ℤ} {u : FreeGroup α}
    (hone : ∀ k : ℤ, k ≠ 0 →
      ¬ (∀ p ∈ decor c 0 (wordOf u),
          lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧
            p.1.2 + k ≤ hi ∧ p.1.2 + c p.1.1 + k ≤ hi))
    (hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi) :
    ∃ p ∈ decor c 0 (wordOf u), p.1.2 = hi ∨ p.1.2 + c p.1.1 = hi := by
  by_contra h
  have hall : ∀ p, p ∈ decor c 0 (wordOf u) → p.1.2 ≠ hi ∧ p.1.2 + c p.1.1 ≠ hi := by
    intro p hp
    constructor
    · intro hc; exact h ⟨p, hp, Or.inl hc⟩
    · intro hc; exact h ⟨p, hp, Or.inr hc⟩
  refine hone 1 (by norm_num) fun p hp => ?_
  have hw := hwin p hp
  simp only [mem_winE, coverEdge] at hw
  obtain ⟨w1, w2, w3, w4⟩ := hw
  obtain ⟨t1, t2⟩ := hall p hp
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **The walk of `u` touches the bottom level `lo`** (from `hone` with `k = -1`). -/
theorem exists_walk_edge_touching_bottom {α : Type u} {c : α → ℤ} {lo hi : ℤ} {u : FreeGroup α}
    (hone : ∀ k : ℤ, k ≠ 0 →
      ¬ (∀ p ∈ decor c 0 (wordOf u),
          lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧
            p.1.2 + k ≤ hi ∧ p.1.2 + c p.1.1 + k ≤ hi))
    (hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi) :
    ∃ p ∈ decor c 0 (wordOf u), p.1.2 = lo ∨ p.1.2 + c p.1.1 = lo := by
  by_contra h
  have hall : ∀ p, p ∈ decor c 0 (wordOf u) → p.1.2 ≠ lo ∧ p.1.2 + c p.1.1 ≠ lo := by
    intro p hp
    constructor
    · intro hc; exact h ⟨p, hp, Or.inl hc⟩
    · intro hc; exact h ⟨p, hp, Or.inr hc⟩
  refine hone (-1) (by norm_num) fun p hp => ?_
  have hw := hwin p hp
  simp only [mem_winE, coverEdge] at hw
  obtain ⟨w1, w2, w3, w4⟩ := hw
  obtain ⟨t1, t2⟩ := hall p hp
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **The gate inclusion of the top gate, from the adapted presentation.**  If a set `S` of
`β`-generators contains the images of the gate loops and the vertex relator is not supported on `S`,
then the free group on `S` meets `⟪winRoot ^ l⟫` trivially (this is
`freiheitssatz_pow_of_not_supportedOn`, the Magnus Freiheitssatz, in the form used by the tower). -/
theorem inf_normalClosure_of_not_supportedOn {α : Type u} (Wt : ℤ → FreeGroup α) (c : α → ℤ)
    {lo hi : ℤ} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l) {S : Set (α × ℤ)}
    (hS : S ⊆ winE c lo hi)
    (hcyc : IsCyclicallyReducedRelator (winRoot Wt c lo hi u))
    (hout : ¬ SupportedOn (winRoot Wt c lo hi u) (Set.range (winBetaSubVal Wt c hS))) :
    ∀ y : FreeGroup (winBetaSub Wt c S),
      winBetaSubIncl Wt c hS y ∈
          Subgroup.normalClosure ({winRoot Wt c lo hi u ^ l} :
            Set (FreeGroup (winBeta Wt c lo hi))) →
        y = 1 :=
  winBetaSub_inf_normalClosure Wt c u l hl hS hcyc hout

/-! ## The chord map of a gate, and the deletion along a spanning forest

The tower/`ℤ`-domain route needs the *honest* gate inclusion: for a set `S` of window edges (the
gate) with a spanning forest `τ` of `S` (given implicitly, see the honest Freiheitssatz below), the
map `π₁(S) = FreeGroup ↥(S ∖ τ) → π₁(D ∪ C) = F(β)/⟪v ^ l⟫` is injective.  The group
`FreeGroup ↥(S ∖ τ)` is the loop group of the gate in the basis "the edges of `S` outside `τ`", and
the map to the vertex alphabet is:

* `1` on the edges of `S ∖ τ` that are *tree edges of the window* (`winTree`), and
* the corresponding `β`-generator on the chords.

This is the map `Φ` of `NOTES_bandFreiheitssatz_honestGate.md` §4bis/4ter.  With `hS : S ⊆ winE` the
proof that such an edge is a `β`-generator is `e ∉ winTree` plus `e ∈ winE` (`mem_winTree`). -/

/-- **The chord map of the gate `S` in the `τ`-basis.**  An edge of `S ∖ τ` which is a tree edge of
the window is sent to `1`; the others (which are chords, hence `β`-generators) are sent to
themselves.  Its domain is the loop group of `S` in the basis `S ∖ τ`. -/
noncomputable def gateChordMap {α : Type u} (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    {S τ : Set (α × ℤ)} [DecidablePred (· ∈ winTree Wt c lo hi)] (hS : S ⊆ winE c lo hi) :
    FreeGroup ↥(S \ τ) →* FreeGroup (winBeta Wt c lo hi) :=
  FreeGroup.lift fun e =>
    if h : (e : α × ℤ) ∈ winTree Wt c lo hi then 1
    else FreeGroup.of (⟨e.1, hS e.2.1,
      fun hcl => h (mem_winTree.mpr ⟨hS e.2.1, hcl⟩)⟩ : winBeta Wt c lo hi)

@[simp] theorem gateChordMap_of {α : Type u} (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    {S τ : Set (α × ℤ)} [DecidablePred (· ∈ winTree Wt c lo hi)] (hS : S ⊆ winE c lo hi)
    (e : ↥(S \ τ)) :
    gateChordMap Wt c (S := S) (τ := τ) hS (FreeGroup.of e) =
      if h : (e : α × ℤ) ∈ winTree Wt c lo hi then 1
      else FreeGroup.of (⟨e.1, hS e.2.1,
        fun hcl => h (mem_winTree.mpr ⟨hS e.2.1, hcl⟩)⟩ : winBeta Wt c lo hi) :=
  FreeGroup.lift_apply_of

/-- **A chord of the gate maps to its own `β`-generator.** -/
theorem gateChordMap_of_chord {α : Type u} (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    {S τ : Set (α × ℤ)} [DecidablePred (· ∈ winTree Wt c lo hi)] (hS : S ⊆ winE c lo hi)
    (e : ↥(S \ τ)) (hcl : (e : α × ℤ) ∉ winTree Wt c lo hi) :
    gateChordMap Wt c (S := S) (τ := τ) hS (FreeGroup.of e) =
      FreeGroup.of (⟨e.1, hS e.2.1,
        fun hc => hcl (mem_winTree.mpr ⟨hS e.2.1, hc⟩)⟩ : winBeta Wt c lo hi) := by
  rw [gateChordMap_of, dif_neg hcl]

/-! ## The band complex of the window

The route to the target (see `NOTES_bandFreiheitssatz_honestGate.md` and the session note
`NOTES_bandFreiheitssatz_bandComplex.md`) runs through the `ℤ`-cover picture: let `Y` be the level
graph of the `ℤ`-cover of the one-relator complex `X = (rose_α, u ^ l)` together with the `2`-cells
attached along the walk of `u ^ l` at every level.  Because `cohom c u = 1` means that `u` has
`c`-weight `0` (`Multiplicative.ofAdd 0 = 1`), the walk of `u` is a *closed* walk of the level graph;
hence `u ^ l ∈ ker c`, the cell of `X` lifts to `Y` once per level, and `π₁ Y = ker (G → ℤ)`.  With
`D = winE c lo hi` the window graph and `C₀` the cell attached along the walk of `u ^ l` at level `0`,
the target is the statement that the band complex `D ∪ C₀` has

  `π₁ (D ∪ C₀) = F (winBeta) / ⟪winRoot ^ l⟫`

injecting into `π₁ Y`.

The lemmas below record the first, purely combinatorial, facts of that picture for the target's own
data: the walk of `u ^ l` *fits into the window* (so that the cell really is a cell of the band), and
hence the band's `2`-cell, read in the window's edge group, kills to the vertex relator. -/

/-- **The walk of `u ^ l` stays in the window.**  If `u` has `c`-weight `0` (`cohom c u = 1`) and its
walk lies in `winE c lo hi`, then the walk of `u ^ l` lies in `winE c lo hi` as well: since the walk
of `u` is closed, the decoration of `u ^ l` is the `l`-fold concatenation of the decoration of `u`
(`Work.OROneRel.decor_pow_flatMap`), each copy read at the same levels. -/
theorem decor_pow_winE_of_windowData {α : Type*} {c : α → ℤ} {lo hi : ℤ} {u : FreeGroup α} (l : ℕ)
    (hcyc : IsCyclicallyReducedRelator u) (hcu : cohom c u = 1)
    (hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi) :
    ∀ p ∈ decor c 0 (wordOf (u ^ l)), coverEdge p ∈ winE c lo hi := by
  intro p hp
  rw [decor_pow_flatMap c u l hcyc hcu] at hp
  obtain ⟨q, hq, hpq⟩ := List.mem_flatten.mp hp
  rw [List.mem_replicate] at hq
  exact hwin p (hq.2 ▸ hpq)

/-- **The band's `2`-cell kills to the vertex relator**, for the target's own data: the walk of
`u ^ l` read in the window's edge group and with the tree edges killed is `winRoot ^ l`.  This is
`Work.OROneRel.treeKill_walkCell_pow` with the window hypothesis supplied by
`decor_pow_winE_of_windowData`. -/
theorem treeKill_walkCell_of_windowData {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (u : FreeGroup α) (l : ℕ) (hcyc : IsCyclicallyReducedRelator u) (hcu : cohom c u = 1)
    (hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi) :
    treeKill Wt c lo hi (walkCell c lo hi 0 (u ^ l) (decor_pow_winE_of_windowData l hcyc hcu hwin))
      = winRoot Wt c lo hi u ^ l :=
  treeKill_walkCell_pow Wt c lo hi u l hcyc hcu (decor_pow_winE_of_windowData l hcyc hcu hwin)

/-- **The presentation of the band's `π₁`.**  The band complex of the window — the window graph
together with the `2`-cell attached along the walk of `u ^ l` at level `0` — has fundamental group
the one-relator group `⟨winBeta | winRoot ^ l⟩` on the window's chords.  This is
`Work.OROneRel.bandWindow_S1_iso` with the window hypothesis supplied by
`decor_pow_winE_of_windowData`. -/
theorem band_presentation_of_windowData {α : Type u} (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (u : FreeGroup α) (l : ℕ) (hcyc : IsCyclicallyReducedRelator u) (hcu : cohom c u = 1)
    (hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi) :
    Nonempty (PresentedGroup (treeRel Wt c lo hi ∪
        {walkCell c lo hi 0 (u ^ l) (decor_pow_winE_of_windowData l hcyc hcu hwin)})
      ≃* PresentedGroup ({winRoot Wt c lo hi u ^ l} : Set (FreeGroup (winBeta Wt c lo hi)))) :=
  bandWindow_S1_iso Wt c lo hi u l hcyc hcu (decor_pow_winE_of_windowData l hcyc hcu hwin)

/-! ## The gate inclusion of the `Z`-domain splitting, with no spanning hypothesis

The `Z`-domain splitting (`Submission/Work/OROneRel/zDomainWindowDefs.lean`,
`Submission/Work/OROneRel/NOTES_bandFreiheitssatz_bandComplex.md`) needs the **gate inclusions**
`π₁ (D ∩ t^{±1} · D) ↪ π₁ (D)` of the window.  In the vocabulary of
`Submission/Work/OROneRel/winChainDefs.lean` the gate is a *subgraph* `S ⊆ winE c lo hi` of the
window, its fundamental group (as a subgroup of `F α`) is `W c S 0`, and the vertex group is
`F (winBeta) / ⟪winRoot ^ l⟫` under the class map `winRho`.  The gate inclusion therefore reads

  `W c S 0 ∩ (winRho).map ⟪winRoot ^ l⟫ = 1`.

The three lemmas below prove it.  **No spanning hypothesis on `S` is needed** — the earlier notes
assumed that the window's tree `T` has to restrict to a spanning tree of `S`, which is not the case:

* `W_le_closure_stbLoop` — the telescoping identity (`Work.pinAux.mul_mem_closure_stbLoop_decor`):
  `W c S 0` is generated by the loop classes `stbLoop Wt c e` of the edges `e ∈ S`;
* `W_le_lift_coverClassAt` — hence `W c S 0` is already carried by the free group on the *chords lying
  in `S`*, i.e. by `FreeGroup (winBetaSub Wt c S) ⊆ F (winBeta)`; this is where the earlier notes'
  spanning hypothesis would have been needed and is **not**: a closed walk in `S` only traverses
  edges of `S`, hence its loop class is a word in the chords of `S`;
* `gate_W_inf_normalClosure` — the Magnus Freiheitssatz `freiheitssatz_at` with the letter set "the
  chords in `S`" then makes the intersection vanish, as soon as some traversal of the walk of `u`
  uses a chord *outside* `S` (the `hout` of `Work.OROneRel.winBetaSub_inf_normalClosure`).

The last hypothesis is not automatic for a given gauge, but the gate inclusion is a statement about
the pair of complexes `(D ∩ t^{±1}D) ↪ D`, hence independent of the spanning tree, so it may be
proved for any gauge for which it does hold and transported back. -/

/-- **`W` of an edge set is generated by the loop classes of its edges.**  This is
`Work.pinAux.mul_mem_closure_stbLoop_decor`: a walk at level `0` with edges in `E` and vanishing
total weight is the product of the loop classes of its decorated edges, conjugated by `Wt 0`; for a
gauge with `Wt 0 = 1` the conjugation disappears. -/
theorem W_le_closure_stbLoop {α : Type u} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (E : Set (α × ℤ))
    (hW0 : Wt 0 = 1) :
    W c E 0 ≤ Subgroup.closure (stbLoop Wt c '' E) := by
  classical
  unfold W
  rw [Subgroup.closure_le]
  rintro x ⟨L, ⟨hwalk, hlsig⟩, rfl⟩
  have h := Work.pinAux.mul_mem_closure_stbLoop_decor Wt c E 0 L hwalk
  rw [hlsig, add_zero, hW0] at h
  simpa using h

/-- **The `π₁` of a subgraph of the window is carried by the chords lying in it.**  A closed walk in
`S` only traverses edges of `S`, so its loop class is a word in the *chords of `S`* (the edges of
`S` outside the tree); hence `W c S 0` lies in the image of the free group on those chords — the
gate alphabet `winBetaSub Wt c S`. -/
theorem W_le_lift_coverClassAt {α : Type u} (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (S : Set (α × ℤ)) (hW0 : Wt 0 = 1) (hS : S ⊆ winE c lo hi) :
    W c S 0 ≤ ((winRho Wt c lo hi).comp
      (FreeGroup.lift (fun g : winBetaSub Wt c S =>
        FreeGroup.of (winBetaSubVal Wt c hS g)))).range := by
  classical
  have hcl : ∀ e : α × ℤ, coverClassAt Wt c e = stbLoop Wt c e := by
    intro e
    rw [coverClassAt, stbLoop, gaugeMap_of]
  refine (W_le_closure_stbLoop Wt c S hW0).trans ?_
  rw [Subgroup.closure_le]
  rintro y ⟨e, he, rfl⟩
  by_cases hc : coverClassAt Wt c e = 1
  · rw [← hcl e, hc]
    exact Subgroup.one_mem _
  · let g : winBetaSub Wt c S := ⟨e, he, hc⟩
    refine ⟨FreeGroup.of g, ?_⟩
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, winRho_of]
    change coverClassAt Wt c e = stbLoop Wt c e
    exact hcl e

/-- **The gate inclusion of the `Z`-domain splitting.**  For a subgraph `S` of the window whose
edges are not enough to carry the vertex relator (`hout`: some traversal of the walk of `u` uses a
chord outside `S`), the fundamental group `W c S 0` of `S` meets the image of `⟪winRoot ^ l⟫` only in
`1`. -/
theorem gate_W_inf_normalClosure {α : Type u} (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l) {S : Set (α × ℤ)} (hW0 : Wt 0 = 1)
    (hS : S ⊆ winE c lo hi)
    (hWt : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ p ∈ decor c 0 (wordOf (Wt i)), coverEdge p ∈ winTree Wt c lo hi)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i)
    (hcycv : IsCyclicallyReducedRelator (winRoot Wt c lo hi u))
    (hout : ¬ SupportedOn (winRoot Wt c lo hi u) (Set.range (winBetaSubVal Wt c hS))) :
    ∀ z : FreeGroup α, z ∈ W c S 0 →
      z ∈ Subgroup.map (winRho Wt c lo hi)
        (Subgroup.normalClosure ({winRoot Wt c lo hi u ^ l} :
          Set (FreeGroup (winBeta Wt c lo hi)))) →
      z = 1 := by
  classical
  intro z hz hz'
  obtain ⟨x, hx⟩ := W_le_lift_coverClassAt Wt c S hW0 hS hz
  obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz'
  -- the two descriptions of the gate alphabet give the same free-group map
  have hmap : (FreeGroup.lift (fun g : winBetaSub Wt c S =>
      FreeGroup.of (winBetaSubVal Wt c hS g))) = winBetaSubIncl Wt c hS := by
    refine FreeGroup.ext_hom _ _ fun g => ?_
    rw [FreeGroup.lift_apply_of, winBetaSubIncl_of]
  have hxm : winRho Wt c lo hi ((FreeGroup.lift (fun g : winBetaSub Wt c S =>
      FreeGroup.of (winBetaSubVal Wt c hS g))) x) = z := hx
  have h1 : (FreeGroup.lift (fun g : winBetaSub Wt c S =>
      FreeGroup.of (winBetaSubVal Wt c hS g))) x = w :=
    winRho_injective Wt c hWt hcoh (by rw [hxm, hwz])
  have hw' : winBetaSubIncl Wt c hS x ∈ Subgroup.normalClosure
      ({winRoot Wt c lo hi u ^ l} : Set (FreeGroup (winBeta Wt c lo hi))) := by
    rw [← hmap, h1]
    exact hw
  have h2 : x = 1 := winBetaSub_inf_normalClosure Wt c u l hl hS hcycv hout x hw'
  rw [h2, map_one, map_one] at hxm
  exact hxm.symm

theorem bandFreiheitssatz_of_windowData {α : Type u} [Fintype α] [DecidableEq α]
    (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (hbad : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u → Work.OROneRel.eps x u ≠ 0)
    {c : α → ℤ} (hcu : Work.OROneRel.cohom c u = 1)
    {Wt : ℤ → FreeGroup α} {lo hi : ℤ}
    (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (hone : ∀ k : ℤ, k ≠ 0 →
      ¬ (∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
          lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧
            p.1.2 + k ≤ hi ∧ p.1.2 + c p.1.1 + k ≤ hi))
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ q ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge q ∈ Work.OROneRel.winTree Wt c lo hi)
    (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi)
    (hlast : ∃ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winTree Wt c lo hi) :
    ∀ x : FreeGroup (Work.OROneRel.winBeta Wt c lo hi),
      Work.OROneRel.winRho Wt c lo hi x ∈
          Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure
          ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))) := by sorry

end Work.OROneRel
