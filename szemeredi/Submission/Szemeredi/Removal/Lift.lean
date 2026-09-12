import Mathlib
import Submission.Szemeredi.Removal.GoodAtomsMain
import Submission.Szemeredi.Removal.Doubling

/-!
# Lifting the good-atom data to hypergraph bundles (Tao, arXiv:math/0503572, §4)

This file derives the abstract counting-lemma hypotheses `GCHyp` for the data obtained by
lifting a family of good atoms along a hypergraph bundle.  The four hypotheses are proved one
at a time:

* (H1) the pointwise decomposition `1_{A_g} = p_g + b_g + c_g` on the lower set,
* (H2) the lower bound `1 / log (R_g) ≤ p_g` (from `LargeOk`),
* (H3) the `L²` bound for `b_g` (from `RegOk`),
* (H4) the discrepancy bound for `c_g` (from the `Pseudorandom` conjunct of `RegOK2`).
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]

/-! ## Elementary facts about the ambient data -/

theorem Hall_card_le {Hd : Finset (Finset ι)} {d : ℕ} (hHd : ∀ e ∈ Hd, e.card = d)
    {f : Finset ι} (hf : f ∈ Hall Hd) : f.card ≤ d := by
  obtain ⟨e, he, hfe⟩ := mem_Hall.mp hf
  rw [← hHd e he]
  exact Finset.card_le_card hfe

theorem algOf_eq_B {d : ℕ} {Bd : Finset ι → SigAlg (Pt V)} {B : ℕ → Finset ι → SigAlg (Pt V)}
    {f : Finset ι} (hf : f.card < d) :
    algOf (V := V) d Bd B f = B f.card f := by
  unfold algOf edgeAlg
  rw [if_neg (ne_of_lt hf)]

/-- Averaging the indicator of a set. -/
theorem avg_indicator (S : Finset (Pt V)) :
    avg (fun x : Pt V => indicator S x) = (S.card : ℝ) / (Fintype.card (Pt V) : ℝ) := by
  unfold avg
  congr 1
  rw [show (∑ x : Pt V, indicator S x)
      = ∑ x : Pt V, (if x ∈ S then (1 : ℝ) else 0) from rfl, Finset.sum_boole]
  have hfil : (Finset.univ.filter (fun x : Pt V => x ∈ S)) = S := by ext x; simp
  rw [hfil]

/-- A sum of indicators over a finset is the cardinality of the intersection. -/
theorem sum_indicator_eq_card (s T : Finset (Pt V)) :
    (∑ x ∈ s, indicator T x) = ((s ∩ T).card : ℝ) := by
  rw [show (∑ x ∈ s, indicator T x) = ∑ x ∈ s, (if x ∈ T then (1 : ℝ) else 0) from rfl,
    Finset.sum_boole, Finset.filter_mem_eq_inter]

/-- The intersection of the boundary atoms of `e`. -/
noncomputable def bdrySet (A : Finset ι → Finset (Pt V)) (e : Finset ι) : Finset (Pt V) :=
  Finset.univ.filter (fun x => ∀ f ∈ del e, x ∈ A f)

theorem mem_bdrySet {A : Finset ι → Finset (Pt V)} {e : Finset ι} {x : Pt V} :
    x ∈ bdrySet A e ↔ ∀ f ∈ del e, x ∈ A f := by
  classical
  simp only [bdrySet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem prod_indicator_bdrySet (A : Finset ι → Finset (Pt V)) (e : Finset ι) (x : Pt V) :
    (∏ f ∈ del e, indicator (A f) x) = indicator (bdrySet A e) x := by
  classical
  rw [show (∏ f ∈ del e, indicator (A f) x)
      = ∏ f ∈ del e, (if x ∈ A f then (1 : ℝ) else 0) from rfl]
  rw [Commons.Data.Finset.prod_ite_one_mem]
  rw [show indicator (bdrySet A e) x = (if x ∈ bdrySet A e then (1 : ℝ) else 0) from rfl]
  by_cases h : x ∈ bdrySet A e
  · rw [if_pos h, if_pos (fun f hf => (mem_bdrySet.mp h) f hf)]
  · rw [if_neg h, if_neg (fun hh => h (mem_bdrySet.mpr hh))]

/-- The lower-order atom intersection is contained in the boundary intersection. -/
theorem interProper_subset_bdrySet (A : Finset ι → Finset (Pt V)) (e : Finset ι) :
    interProper A e ⊆ bdrySet A e := by
  intro x hx
  rw [mem_bdrySet]
  intro f hf
  exact (mem_interProper.mp hx) f (Finset.mem_powerset.mpr (mem_del.mp hf).1)
    (del_subset_proper hf)

/-- The `p_e` numbers: the density of `A_e` inside the boundary intersection. -/
noncomputable def pOf (A : Finset ι → Finset (Pt V)) (e : Finset ι) : ℝ :=
  if h : (bdrySet A e).card = 0 then 1
  else (((bdrySet A e ∩ A e).card : ℕ) : ℝ) / (((bdrySet A e).card : ℕ) : ℝ)

theorem pOf_nonneg (A : Finset ι → Finset (Pt V)) (e : Finset ι) : 0 ≤ pOf A e := by
  unfold pOf
  split
  · norm_num
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem pOf_le_one (A : Finset ι → Finset (Pt V)) (e : Finset ι) : pOf A e ≤ 1 := by
  unfold pOf
  split
  · norm_num
  · rename_i h
    have hpos : (0 : ℝ) < ((bdrySet A e).card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero h
    rw [div_le_one hpos]
    exact_mod_cast Finset.card_le_card Finset.inter_subset_left

/-! ## The ambient decomposition (H1) -/

/-- **The block of the join of the boundary algebras is the boundary intersection.** -/
theorem block_iInf_bdryAlg {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)}
    {B : ℕ → Finset ι → SigAlg (Pt V)} {A : Finset ι → Finset (Pt V)}
    (hHd : ∀ e ∈ Hd, e.card = d) (hAtom : ∀ f ∈ Hall Hd, A f ∈ (algOf (V := V) d Bd B f).atoms)
    {e : Finset ι} (he : e ∈ Hall Hd) {x : Pt V} (hx : x ∈ interProper A e) :
    (SigAlg.iInf (bdryAlg (V := V) B e.card e) Finset.univ).block x = bdrySet A e := by
  classical
  have hcard_le : e.card ≤ d := Hall_card_le hHd he
  rw [SigAlg.iInf_block]
  ext y
  rw [Finset.mem_inf]
  constructor
  · intro h
    rw [mem_bdrySet]
    intro f hf
    have hfe : f ⊆ e := (mem_del.mp hf).1
    have hfcard : f.card + 1 = e.card := (mem_del.mp hf).2
    have hflt : f.card < d := by omega
    have hfHall : f ∈ Hall Hd := Hall_down he hfe
    have hatom : A f ∈ (B f.card f).atoms := by
      rw [← algOf_eq_B (V := V) (Bd := Bd) (B := B) hflt]; exact hAtom f hfHall
    have hxAf : x ∈ A f := (mem_interProper.mp hx) f (Finset.mem_powerset.mpr hfe)
      (del_subset_proper hf)
    have hblock : (B (e.card - 1) f).block x = A f := by
      rw [show e.card - 1 = f.card from by omega]
      exact SigAlg.eq_of_mem_atoms hatom hxAf
    have := h ⟨f, hf⟩ (Finset.mem_univ _)
    rwa [hblock] at this
  · intro h i _
    have hfe : i.val ⊆ e := (mem_del.mp i.2).1
    have hfcard : i.val.card + 1 = e.card := (mem_del.mp i.2).2
    have hflt : i.val.card < d := by omega
    have hfHall : i.val ∈ Hall Hd := Hall_down he hfe
    have hatom : A i.val ∈ (B i.val.card i.val).atoms := by
      rw [← algOf_eq_B (V := V) (Bd := Bd) (B := B) hflt]; exact hAtom i.val hfHall
    have hxAf : x ∈ A i.val := (mem_interProper.mp hx) i.val (Finset.mem_powerset.mpr hfe)
      (del_subset_proper i.2)
    have hblock : (B (e.card - 1) i.val).block x = A i.val := by
      rw [show e.card - 1 = i.val.card from by omega]
      exact SigAlg.eq_of_mem_atoms hatom hxAf
    rw [hblock]
    exact (mem_bdrySet.mp h) i.val i.2

/-- **The `p_e` constant is the conditional expectation of `1_{A_e}` on the lower set.** -/
theorem condExp_iInf_bdryAlg {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)}
    {B : ℕ → Finset ι → SigAlg (Pt V)} {A : Finset ι → Finset (Pt V)}
    (hHd : ∀ e ∈ Hd, e.card = d) (hAtom : ∀ f ∈ Hall Hd, A f ∈ (algOf (V := V) d Bd B f).atoms)
    {e : Finset ι} (he : e ∈ Hall Hd) {x : Pt V} (hx : x ∈ interProper A e) :
    (SigAlg.iInf (bdryAlg (V := V) B e.card e) Finset.univ).condExp (indicator (A e)) x
      = pOf A e := by
  classical
  have hxbdry : x ∈ bdrySet A e := interProper_subset_bdrySet A e hx
  have hcard_ne : (bdrySet A e).card ≠ 0 := fun h => by
    rw [Finset.card_eq_zero] at h
    rw [h] at hxbdry
    exact Finset.notMem_empty x hxbdry
  unfold SigAlg.condExp pOf
  rw [dif_neg hcard_ne]
  rw [block_iInf_bdryAlg (V := V) hHd hAtom he hx]
  rw [sum_indicator_eq_card]

/-! ## The `b` and `c` terms, and the ambient decomposition -/

/-- The error term `b_e` of the decomposition. -/
noncomputable def bOf (B B' : ℕ → Finset ι → SigAlg (Pt V)) (A : Finset ι → Finset (Pt V))
    (e : Finset ι) : Pt V → ℝ :=
  diff (bdryAlg (V := V) B e.card e) (bdryAlg (V := V) B' e.card e) (A e)

/-- The error term `c_e` of the decomposition. -/
noncomputable def cOf (B' : ℕ → Finset ι → SigAlg (Pt V)) (A : Finset ι → Finset (Pt V))
    (e : Finset ι) : Pt V → ℝ :=
  fun x => indicator (A e) x
    - (SigAlg.iInf (bdryAlg (V := V) B' e.card e) Finset.univ).condExp (indicator (A e)) x

/-- **The decomposition** `1_{A_e} = p_e + b_e + c_e` on the lower set. -/
theorem decomp {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)}
    {B B' : ℕ → Finset ι → SigAlg (Pt V)} {A : Finset ι → Finset (Pt V)}
    (hHd : ∀ e ∈ Hd, e.card = d) (hAtom : ∀ f ∈ Hall Hd, A f ∈ (algOf (V := V) d Bd B f).atoms)
    {e : Finset ι} (he : e ∈ Hall Hd) {x : Pt V} (hx : x ∈ interProper A e) :
    indicator (A e) x = pOf A e + bOf (V := V) B B' A e x + cOf (V := V) B' A e x := by
  have hcx := condExp_iInf_bdryAlg (V := V) hHd hAtom he hx
  unfold bOf cOf diff
  rw [hcx]
  ring

/-- The join of the boundary algebras refines the coordinate algebra of `e`. -/
theorem iInf_bdryAlg_refines_coord {B' : ℕ → Finset ι → SigAlg (Pt V)} {e : Finset ι}
    (h : ∀ f ∈ del e, (B' (e.card - 1) f).Refines (coord (V := V) f)) :
    (SigAlg.iInf (bdryAlg (V := V) B' e.card e) Finset.univ).Refines (coord (V := V) e) := by
  intro x y hy
  simp only [coord_block, Finset.mem_filter] at hy
  rw [SigAlg.iInf_block, Finset.mem_inf]
  intro i _
  refine h i.val i.2 x (by
    simp only [coord_block, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun j hj => hy.2 j ((mem_del.mp i.2).1 hj)⟩)

/-- A conditional expectation with respect to a partition refining `coord e` depends only on
the coordinates in `e`. -/
theorem condExp_agree_of_refines {P : SigAlg (Pt V)} {e : Finset ι}
    (h : P.Refines (coord (V := V) e)) (f : Pt V → ℝ) {x y : Pt V}
    (hxy : ∀ i ∈ e, y i = x i) : P.condExp f y = P.condExp f x :=
  SigAlg.condExp_blockConst P f x y
    (h x (by
      rw [coord_block, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hxy⟩))

/-- The `b`-term depends only on the coordinates in `e`. -/
theorem bOf_agree {B B' : ℕ → Finset ι → SigAlg (Pt V)} {A : Finset ι → Finset (Pt V)}
    {e : Finset ι}
    (hB : (SigAlg.iInf (bdryAlg (V := V) B e.card e) Finset.univ).Refines (coord (V := V) e))
    (hB' : (SigAlg.iInf (bdryAlg (V := V) B' e.card e) Finset.univ).Refines (coord (V := V) e))
    {x y : Pt V} (hxy : ∀ i ∈ e, y i = x i) :
    bOf (V := V) B B' A e y = bOf (V := V) B B' A e x := by
  unfold bOf diff
  rw [condExp_agree_of_refines hB' _ hxy, condExp_agree_of_refines hB _ hxy]

/-- The `c`-term depends only on the coordinates in `e`. -/
theorem cOf_agree {B' : ℕ → Finset ι → SigAlg (Pt V)} {A : Finset ι → Finset (Pt V)}
    {e : Finset ι} (hAe : (coord (V := V) e).IsMeas (A e))
    (hB' : (SigAlg.iInf (bdryAlg (V := V) B' e.card e) Finset.univ).Refines (coord (V := V) e))
    {x y : Pt V} (hxy : ∀ i ∈ e, y i = x i) :
    cOf (V := V) B' A e y = cOf (V := V) B' A e x := by
  have hind : indicator (A e) y = indicator (A e) x := by
    have hiff := (coord_isMeas_iff.mp hAe) x y hxy
    unfold indicator
    by_cases hx : x ∈ A e
    · rw [if_pos (hiff.mpr hx), if_pos hx]
    · rw [if_neg (fun h => hx (hiff.mp h)), if_neg hx]
  unfold cOf
  rw [hind, condExp_agree_of_refines hB' _ hxy]

/-- The factorisation of the `b`-term through the restriction to `e`. -/
noncomputable def betaOf (B B' : ℕ → Finset ι → SigAlg (Pt V)) (A : Finset ι → Finset (Pt V))
    (e : Finset ι) : Pd (V := V) e → ℝ :=
  fun w => bOf (V := V) B B' A e (extOfPd (V := V) e w)

/-- The factorisation of the `c`-term through the restriction to `e`. -/
noncomputable def gammaOf (B' : ℕ → Finset ι → SigAlg (Pt V)) (A : Finset ι → Finset (Pt V))
    (e : Finset ι) : Pd (V := V) e → ℝ :=
  fun w => cOf (V := V) B' A e (extOfPd (V := V) e w)

theorem betaOf_restrict {B B' : ℕ → Finset ι → SigAlg (Pt V)} {A : Finset ι → Finset (Pt V)}
    {e : Finset ι}
    (hB : (SigAlg.iInf (bdryAlg (V := V) B e.card e) Finset.univ).Refines (coord (V := V) e))
    (hB' : (SigAlg.iInf (bdryAlg (V := V) B' e.card e) Finset.univ).Refines (coord (V := V) e))
    (x : Pt V) :
    bOf (V := V) B B' A e x = betaOf (V := V) B B' A e (restrict (V := V) x e) :=
  (bOf_agree (V := V) hB hB' (fun i hi => by
    rw [extOfPd_apply (V := V) _ hi]; rfl)).symm

theorem gammaOf_restrict {B' : ℕ → Finset ι → SigAlg (Pt V)} {A : Finset ι → Finset (Pt V)}
    {e : Finset ι} (hAe : (coord (V := V) e).IsMeas (A e))
    (hB' : (SigAlg.iInf (bdryAlg (V := V) B' e.card e) Finset.univ).Refines (coord (V := V) e))
    (x : Pt V) :
    cOf (V := V) B' A e x = gammaOf (V := V) B' A e (restrict (V := V) x e) :=
  (cOf_agree (V := V) hAe hB' (fun i hi => by
    rw [extOfPd_apply (V := V) _ hi]; rfl)).symm

/-! ## Lifting to a hypergraph bundle -/

/-- A face of the hypergraph of full cardinality is an edge. -/
theorem Hall_mem_Hd {Hd : Finset (Finset ι)} {d : ℕ} (hHd : ∀ e ∈ Hd, e.card = d)
    {f : Finset ι} (hf : f ∈ Hall Hd) (hc : f.card = d) : f ∈ Hd := by
  obtain ⟨e, he, hfe⟩ := mem_Hall.mp hf
  have h2 : f = e := Finset.eq_of_subset_of_card_le hfe (by rw [hHd e he, hc])
  rwa [h2]

/-- Every face lies in the level determined by its cardinality. -/
theorem Hall_mem_lev {Hd : Finset (Finset ι)} {d : ℕ} (hHd : ∀ e ∈ Hd, e.card = d)
    {f : Finset ι} (hf : f ∈ Hall Hd) : f ∈ lev Hd (d - f.card) := by
  obtain ⟨e, he, hfe⟩ := mem_Hall.mp hf
  rw [mem_lev_iff]
  refine ⟨e, he, hfe, ?_⟩
  rw [hHd e he]
  exact Nat.add_sub_cancel' (by rw [← hHd e he]; exact Finset.card_le_card hfe)

/-- Every σ-algebra of the hierarchy refines the coordinate algebra of its face. -/
theorem algOf_refines_coord {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)}
    {Md : ℕ} {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    (hHd : ∀ e ∈ Hd, e.card = d) (hBd : ∀ e ∈ Hd, (Bd e).Refines (coord (V := V) e))
    (hR : RegOK2 (V := V) d Hd Bd Md F B B' M)
    {f : Finset ι} (hf : f ∈ Hall Hd) :
    (algOf (V := V) d Bd B f).Refines (coord (V := V) f) := by
  by_cases hc : f.card < d
  · rw [algOf_eq_B (V := V) (Bd := Bd) hc]
    exact hR.2.2.2.1 f.card hc f (Hall_mem_lev hHd hf)
  · have hcd : f.card = d := by have := Hall_card_le hHd hf; omega
    rw [show algOf (V := V) d Bd B f = Bd f from by
      unfold algOf edgeAlg
      rw [if_pos hcd]]
    exact hBd f (Hall_mem_Hd hHd hf hcd)

/-- Atoms of the hierarchy are measurable for the coordinate algebra of their face. -/
theorem coord_isMeas_of_atom {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)}
    {Md : ℕ} {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    {A : Finset ι → Finset (Pt V)}
    (hHd : ∀ e ∈ Hd, e.card = d) (hBd : ∀ e ∈ Hd, (Bd e).Refines (coord (V := V) e))
    (hAtom : ∀ f ∈ Hall Hd, A f ∈ (algOf (V := V) d Bd B f).atoms)
    (hR : RegOK2 (V := V) d Hd Bd Md F B B' M)
    {f : Finset ι} (hf : f ∈ Hall Hd) : (coord (V := V) f).IsMeas (A f) :=
  (IsMeas_of_mem_atoms (hAtom f hf)).of_refines (algOf_refines_coord hHd hBd hR hf)

/-- The lifted data agrees with the subset-lift on subsets of a bundle edge. -/
theorem AgOf_eq_liftSetSub {Hd : Finset (Finset ι)} {A : Finset ι → Finset (Pt V)}
    {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {G : Finset (Finset κ)}
    (hB : IsBundle Hd π G) {g g' : Finset κ} (hg : g ∈ G) (hg' : g' ⊆ g) :
    AgOf (V := V) A π G hB.inj g'
      = liftSetSub (V := V) π g (hB.inj g hg) (A (g'.image π)) g' := by
  rw [AgOf_of_mem (V := V) A π G hB.inj (hB.closed g hg g' hg'),
    liftSetSub_of_subset (V := V) π g (hB.inj g hg) (A (g'.image π)) hg']

theorem lowSetAll_eq_lowSet {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι)
    (Ag : Finset κ → Finset (BPt V π)) (g : Finset κ) :
    lowSetAll π Ag g = lowSet π g.powerset Ag g := by
  ext v
  rw [mem_lowSetAll, mem_lowSet]
  simp only [Finset.mem_powerset]
  exact forall_congr' (fun g' => ⟨fun h _ => h, fun h hlt => h hlt.1 hlt⟩)

/-- The lower set of a bundle edge lies in the lift of the lower-order atom intersection. -/
theorem lowSetAll_AgOf_subset_lowSetLift {Hd : Finset (Finset ι)}
    {A : Finset ι → Finset (Pt V)} {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι}
    {G : Finset (Finset κ)} (hB : IsBundle Hd π G) {g : Finset κ} (hg : g ∈ G)
    (hA : ∀ f, f ⊂ g.image π → (coord (V := V) f).IsMeas (A f)) {v : BPt V π}
    (hv : v ∈ lowSetAll π (AgOf (V := V) A π G hB.inj) g) :
    v ∈ lowSetLift (V := V) π g (hB.inj g hg) A := by
  have hv' : v ∈ lowSet π g.powerset
      (fun g' => liftSetSub (V := V) π g (hB.inj g hg) (A (g'.image π)) g') g := by
    rw [mem_lowSet]
    intro g' hg'pow hlt
    exact (AgOf_eq_liftSetSub (V := V) hB hg (Finset.mem_powerset.mp hg'pow)) ▸
      ((mem_lowSetAll.mp hv) g' hlt)
  exact (lowSet_liftSet_eq (V := V) π g (hB.inj g hg) A hA) ▸ hv'

/-- Membership in a lift is determined by any ambient point agreeing on the edge. -/
theorem mem_liftSet_iff_of_agree {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι)
    (g : Finset κ) (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) {A : Finset (Pt V)}
    (hA : (coord (V := V) (g.image π)).IsMeas A) {v : BPt V π} {x : Pt V}
    (hx : ∀ k ∈ g, x (π k) = v k) :
    v ∈ liftSet (V := V) π g hinj A ↔ x ∈ A := by
  rw [mem_liftSet_iff]
  constructor
  · rintro ⟨y, hyA, hyv⟩
    refine ((coord_isMeas_iff.mp hA) x y (fun i hi => ?_)).mp hyA
    obtain ⟨k, hk, hki⟩ := Finset.mem_image.mp hi
    subst hki
    exact (hyv k hk).trans (hx k hk).symm
  · intro hxA
    exact ⟨x, hxA, fun k hk => hx k hk⟩

/-- The `B`-algebras refine the coordinate algebras on the boundary of a face. -/
theorem bdryAlg_refines_coord {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)}
    {Md : ℕ} {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    (hHd : ∀ e ∈ Hd, e.card = d) (hR : RegOK2 (V := V) d Hd Bd Md F B B' M)
    {e : Finset ι} (he : e ∈ Hall Hd) :
    ∀ f ∈ del e, (B (e.card - 1) f).Refines (coord (V := V) f) := by
  intro f hf
  have hle : e.card ≤ d := Hall_card_le hHd he
  have hcard : f.card + 1 = e.card := (mem_del.mp hf).2
  exact hR.2.2.2.1 (e.card - 1) (by omega) f
    (del_subset_lev' (by omega) hle (Hall_mem_lev hHd he) hf)

/-- The `B'`-algebras refine the coordinate algebras on the boundary of a face. -/
theorem bdryAlg'_refines_coord {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)}
    {Md : ℕ} {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    (hHd : ∀ e ∈ Hd, e.card = d) (hR : RegOK2 (V := V) d Hd Bd Md F B B' M)
    {e : Finset ι} (he : e ∈ Hall Hd) :
    ∀ f ∈ del e, (B' (e.card - 1) f).Refines (coord (V := V) f) := by
  intro f hf
  have hle : e.card ≤ d := Hall_card_le hHd he
  have hcard : f.card + 1 = e.card := (mem_del.mp hf).2
  exact hR.2.2.2.2.2.1 (e.card - 1) (by omega) f
    (del_subset_lev' (by omega) hle (Hall_mem_lev hHd he) hf)

/-! ## The lifted data of a bundle -/

/-- The `p`-component of the lifted data. -/
noncomputable def pgOf (A : Finset ι → Finset (Pt V)) {κ : Type*} (π : κ → ι)
    (g : Finset κ) : ℝ :=
  pOf A (g.image π)

/-- The `b`-component of the lifted data. -/
noncomputable def bgOf (B B' : ℕ → Finset ι → SigAlg (Pt V)) (A : Finset ι → Finset (Pt V))
    {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (G : Finset (Finset κ))
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) (g : Finset κ) : BPt V π → ℝ :=
  if hh : g ∈ G then liftFun (V := V) π g (hinj g hh) (betaOf (V := V) B B' A (g.image π))
  else fun _ => 0

/-- The `c`-component of the lifted data. -/
noncomputable def cgOf (B' : ℕ → Finset ι → SigAlg (Pt V)) (A : Finset ι → Finset (Pt V))
    {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (G : Finset (Finset κ))
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) (g : Finset κ) : BPt V π → ℝ :=
  if hh : g ∈ G then liftFun (V := V) π g (hinj g hh) (gammaOf (V := V) B' A (g.image π))
  else fun _ => 0

/-- The restriction of an ambient point agreeing with a bundle point. -/
theorem restrict_eq_piCongrImage {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι)
    (g : Finset κ) (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) {v : BPt V π} {x : Pt V}
    (h : ∀ k ∈ g, x (π k) = v k) :
    restrict (V := V) x (g.image π)
      = piCongrImage (V := V) π g hinj (restrict (V := fun k => V (π k)) v g) := by
  funext j
  obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp j.2
  have h3 := piCongrImage_symm_apply (V := V) π g hinj
    (piCongrImage (V := V) π g hinj (restrict (V := fun k => V (π k)) v g)) ⟨k, hk⟩
  rw [Equiv.symm_apply_apply] at h3
  rw [show j = (⟨π k, Finset.mem_image.mpr ⟨k, hk, rfl⟩⟩ : {j // j ∈ g.image π})
    from Subtype.ext hkj.symm]
  rw [← h3]
  exact h k hk

/-- **Hypothesis (H1)**: the pointwise decomposition of the lifted data on the lower set. -/
theorem gchyp_h1 {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)} {Md : ℕ}
    {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    {A : Finset ι → Finset (Pt V)}
    (hHd : ∀ e ∈ Hd, e.card = d)
    (hBd : ∀ e ∈ Hd, (Bd e).Refines (coord (V := V) e))
    (hAtom : ∀ f ∈ Hall Hd, A f ∈ (algOf (V := V) d Bd B f).atoms)
    (hGood : ∀ e ∈ Hall Hd, GoodAt (V := V) d Bd B B' M F A e.card e)
    (hR : RegOK2 (V := V) d Hd Bd Md F B B' M)
    {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {G : Finset (Finset κ)}
    (hB : IsBundle Hd π G) {g : Finset κ} (hg : g ∈ G) {v : BPt V π}
    (hv : v ∈ lowSetAll π (AgOf (V := V) A π G hB.inj) g) :
    indicator (AgOf (V := V) A π G hB.inj g) v
      = pgOf A π g + bgOf (V := V) B B' A π G hB.inj g v
        + cgOf (V := V) B' A π G hB.inj g v := by
  classical
  have hHall : g.image π ∈ Hall Hd := hB.img g hg
  have hAe : (coord (V := V) (g.image π)).IsMeas (A (g.image π)) :=
    coord_isMeas_of_atom hHd hBd hAtom hR hHall
  have hBc := iInf_bdryAlg_refines_coord (bdryAlg_refines_coord hHd hR hHall)
  have hB'c := iInf_bdryAlg_refines_coord (bdryAlg'_refines_coord hHd hR hHall)
  -- 1. reduce to the lift of the lower-order intersection
  have hv' : v ∈ lowSetLift (V := V) π g (hB.inj g hg) A :=
    lowSetAll_AgOf_subset_lowSetLift hB hg
      (fun f hf => coord_isMeas_of_atom hHd hBd hAtom hR (Hall_down hHall hf.1)) hv
  simp only [lowSetLift] at hv'
  rw [mem_liftSet_iff] at hv'
  obtain ⟨x, hx, hxv⟩ := hv'
  -- 2. the ambient decomposition at `x`
  have hdec := decomp (V := V) (B' := B') hHd hAtom hHall hx
  -- 3. identify the three lifted terms with the ambient ones
  have h1 : indicator (AgOf (V := V) A π G hB.inj g) v = indicator (A (g.image π)) x :=
    indicator_congr (by
      rw [AgOf_of_mem (V := V) A π G hB.inj hg]
      exact mem_liftSet_iff_of_agree (V := V) π g (hB.inj g hg) hAe hxv)
  have h2 : bgOf (V := V) B B' A π G hB.inj g v = bOf (V := V) B B' A (g.image π) x := by
    rw [bgOf, dif_pos hg, liftFun_apply, betaOf]
    refine bOf_agree (V := V) hBc hB'c (fun i hi => ?_)
    rw [extOfPd_apply (V := V) _ hi]
    exact (congrFun (restrict_eq_piCongrImage (V := V) π g (hB.inj g hg) hxv) ⟨i, hi⟩).symm
  have h3 : cgOf (V := V) B' A π G hB.inj g v = cOf (V := V) B' A (g.image π) x := by
    rw [cgOf, dif_pos hg, liftFun_apply, gammaOf]
    refine cOf_agree (V := V) hAe hB'c (fun i hi => ?_)
    rw [extOfPd_apply (V := V) _ hi]
    exact (congrFun (restrict_eq_piCongrImage (V := V) π g (hB.inj g hg) hxv) ⟨i, hi⟩).symm
  rw [h1, h2, h3, show pgOf A π g = pOf A (g.image π) from rfl]
  exact hdec

/-! ## Hypothesis (H2): the lower bound on `p` -/

/-- The `R`-constants of the lifted data. -/
noncomputable def RgOf (F : ℕ → ℕ) (M : ℕ → ℕ) {κ : Type*} (π : κ → ι) (g : Finset κ) : ℝ :=
  (F (M (g.image π).card) : ℝ)

/-- The average of the boundary product is the density of the boundary intersection. -/
theorem avg_prodT_del (A : Finset ι → Finset (Pt V)) (e : Finset ι) :
    avg (prodT (fun f : {f : Finset ι // f ∈ del e} => A f.val))
      = ((bdrySet A e).card : ℝ) / (Fintype.card (Pt V) : ℝ) := by
  rw [← avg_indicator (V := V) (bdrySet A e)]
  congr 1
  funext x
  rw [prodT, ← prod_indicator_bdrySet A e x,
    ← Finset.prod_attach (s := del e) (f := fun f => indicator (A f) x)]
  exact Finset.prod_congr Finset.attach_eq_univ.symm (fun f _ => rfl)

/-- The average of `1_{A_e}` times the boundary product. -/
theorem avg_prodT_del_mul (A : Finset ι → Finset (Pt V)) (e : Finset ι) (Ae : Finset (Pt V)) :
    avg (fun x => indicator Ae x * prodT (fun f : {f : Finset ι // f ∈ del e} => A f.val) x)
      = ((((bdrySet A e) ∩ Ae).card : ℕ) : ℝ) / (Fintype.card (Pt V) : ℝ) := by
  have hprod : ∀ x : Pt V, prodT (fun f : {f : Finset ι // f ∈ del e} => A f.val) x
      = indicator (bdrySet A e) x := by
    intro x
    rw [prodT, ← prod_indicator_bdrySet A e x,
      ← Finset.prod_attach (s := del e) (f := fun f => indicator (A f) x)]
    exact Finset.prod_congr Finset.attach_eq_univ.symm (fun f _ => rfl)
  rw [show (fun x => indicator Ae x * prodT (fun f : {f : Finset ι // f ∈ del e} => A f.val) x)
      = fun x => indicator Ae x * indicator (bdrySet A e) x from funext (fun x => by rw [hprod x])]
  rw [show (fun x : Pt V => indicator Ae x * indicator (bdrySet A e) x)
      = fun x => indicator (Ae ∩ bdrySet A e) x
    from funext (fun x => indicator_mul Ae (bdrySet A e) x)]
  rw [avg_indicator (V := V), Finset.inter_comm Ae (bdrySet A e)]

/-- **Hypothesis (H2)**: the lower bound on `p` coming from the largeness condition. -/
theorem gchyp_h2 {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)} {Md : ℕ}
    {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    {A : Finset ι → Finset (Pt V)}
    (hGood : ∀ e ∈ Hall Hd, GoodAt (V := V) d Bd B B' M F A e.card e)
    {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {G : Finset (Finset κ)}
    (hB : IsBundle Hd π G) {g : Finset κ} (hg : g ∈ G)
    (hlog : 1 ≤ Real.log (RgOf F M π g)) :
    1 / Real.log (RgOf F M π g) ≤ pgOf A π g := by
  classical
  set e : Finset ι := g.image π with he
  have hHall : e ∈ Hall Hd := hB.img g hg
  have hGO := (hGood e hHall).1
  unfold LargeOk at hGO
  have hp1 := avg_prodT_del (V := V) A e
  have hp2 := avg_prodT_del_mul (V := V) A e (A e)
  rw [hp1, hp2] at hGO
  set L : ℝ := Real.log (F (M e.card)) with hL
  set B : ℝ := (((bdrySet A e).card : ℕ) : ℝ) with hBdef
  set I : ℝ := ((((bdrySet A e) ∩ A e).card : ℕ) : ℝ) with hIdef
  set D : ℝ := (Fintype.card (Pt V) : ℝ) with hDdef
  have hDpos : 0 < D := SigAlg.card_cast_pos
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one (by rw [hL]; exact hlog)
  have hkey : (1 / L) * B ≤ I := by
    have h1 : (1 / L) * (B / D) * D ≤ (I / D) * D :=
      mul_le_mul_of_nonneg_right hGO (le_of_lt hDpos)
    have h2 : (1 / L) * (B / D) * D = (1 / L) * B := by
      rw [mul_assoc, div_mul_cancel₀ B (ne_of_gt hDpos)]
    have h3 : (I / D) * D = I := div_mul_cancel₀ I (ne_of_gt hDpos)
    linarith
  have hpg : pgOf A π g = pOf A e := by rw [pgOf, he]
  have hLrg : Real.log (RgOf F M π g) = L := by rw [RgOf, ← he, ← hL]
  rw [hpg, hLrg]
  by_cases hB0 : (bdrySet A e).card = 0
  · rw [pOf, dif_pos hB0, div_le_one hLpos]
    exact hlog
  · have hBpos : 0 < B := by
      rw [hBdef]
      exact_mod_cast Nat.pos_of_ne_zero hB0
    rw [pOf, dif_neg hB0, div_le_div_iff₀ hLpos hBpos]
    have hBL : B / L ≤ I := by
      rw [show B / L = (1 / L) * B from by ring]
      exact hkey
    have h2 := (div_le_iff₀ hLpos).mp hBL
    simpa using h2

/-! ## Hypothesis (H3): the `L²` bound on the `b`-term -/

/-- Shrinking the bundle edge enlarges the lift. -/
theorem liftSet_subset_of_subset {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι)
    {g' g : Finset κ} (h : g' ⊆ g)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (A : Finset (Pt V)) :
    liftSet (V := V) π g hinj A
      ⊆ liftSet (V := V) π g' (fun a ha b hb hab => hinj a (h ha) b (h hb) hab) A := by
  intro v hv
  rw [mem_liftSet_iff] at hv ⊢
  obtain ⟨x, hxA, hxv⟩ := hv
  exact ⟨x, hxA, fun k hk => hxv k (h hk)⟩

/-- The lower set of a bundle edge is exactly the lift of the lower-order atom intersection. -/
theorem lowSetAll_AgOf_eq_lowSetLift {Hd : Finset (Finset ι)}
    {A : Finset ι → Finset (Pt V)} {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι}
    {G : Finset (Finset κ)} (hB : IsBundle Hd π G) {g : Finset κ} (hg : g ∈ G)
    (hA : ∀ f, f ⊂ g.image π → (coord (V := V) f).IsMeas (A f)) :
    lowSetAll π (AgOf (V := V) A π G hB.inj) g = lowSetLift (V := V) π g (hB.inj g hg) A := by
  apply Finset.Subset.antisymm
  · intro v hv
    exact lowSetAll_AgOf_subset_lowSetLift hB hg hA hv
  · intro v hv
    rw [mem_lowSetAll]
    intro g' hlt
    have hv' : v ∈ liftSet (V := V) π g (hB.inj g hg) (interProper A (g.image π)) := by
      simpa only [lowSetLift] using hv
    rw [mem_liftSet_iff] at hv'
    obtain ⟨x, hx, hxv⟩ := hv'
    rw [AgOf_of_mem (V := V) A π G hB.inj (hB.closed g hg g' hlt.1), mem_liftSet_iff]
    exact ⟨x, (mem_interProper.mp hx) (g'.image π)
      (Finset.mem_powerset.mpr (Finset.image_subset_image hlt.1))
      (image_ssubset_image (hB.inj g hg) hlt.1 (Finset.ssubset_iff_subset_ne.mp hlt).2),
      fun k hk => hxv k (hlt.1 hk)⟩

/-- **Transport of the squared `b`-term**: the bundle average of `(liftFun φ)² · 1_{liftSet A'}`
equals the ambient average of `φ(restrict ·)² · 1_{A'}`. -/
theorem avg_liftFun_sq {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (φ : Pd (V := V) (g.image π) → ℝ)
    {A' : Finset (Pt V)} (hA' : (coord (V := V) (g.image π)).IsMeas A') :
    avg (fun v : BPt V π => (liftFun (V := V) π g hinj φ v) ^ 2
        * indicator (liftSet (V := V) π g hinj A') v)
      = avg (fun x : Pt V => (φ (restrict (V := V) x (g.image π))) ^ 2 * indicator A' x) :=
  lift_avg (V := V) π g hinj (fun w => (φ w) ^ 2) hA'

/-- The product of indicators over the proper subsets of `e`. -/
theorem prodT_interProper (A : Finset ι → Finset (Pt V)) (e : Finset ι) (x : Pt V) :
    prodT (fun f : {f : Finset ι // f ⊂ e} => A f.val) x = indicator (interProper A e) x := by
  by_cases h : ∀ f, f ⊂ e → x ∈ A f
  · rw [indicator, if_pos (mem_interProper.mpr (fun f _ hf => h f hf))]
    refine Finset.prod_eq_one (fun f _ => ?_)
    rw [indicator, if_pos (h f.val f.2)]
  · push_neg at h
    obtain ⟨f₀, hf₀, hx₀⟩ := h
    rw [indicator, if_neg (fun hh => hx₀ ((mem_interProper.mp hh) f₀
      (Finset.mem_powerset.mpr hf₀.1) hf₀))]
    exact Finset.prod_eq_zero (Finset.mem_univ ⟨f₀, hf₀⟩) (by rw [indicator, if_neg hx₀])

/-- **Hypothesis (H3)**: the `L²` bound on the `b`-term, from the regularity condition. -/
theorem gchyp_h3 {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)} {Md : ℕ}
    {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    {A : Finset ι → Finset (Pt V)}
    (hHd : ∀ e ∈ Hd, e.card = d)
    (hBd : ∀ e ∈ Hd, (Bd e).Refines (coord (V := V) e))
    (hAtom : ∀ f ∈ Hall Hd, A f ∈ (algOf (V := V) d Bd B f).atoms)
    (hGood : ∀ e ∈ Hall Hd, GoodAt (V := V) d Bd B B' M F A e.card e)
    (hR : RegOK2 (V := V) d Hd Bd Md F B B' M)
    {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {G : Finset (Finset κ)}
    (hB : IsBundle Hd π G) {g : Finset κ} (hg : g ∈ G) :
    avg (fun v : BPt V π => (bgOf (V := V) B B' A π G hB.inj g v) ^ 2
        * indicator (lowSetAll π (AgOf (V := V) A π G hB.inj) g) v)
      ≤ (1 / RgOf F M π g)
        * avg (indicator (lowSetAll π (AgOf (V := V) A π G hB.inj) g)) := by
  classical
  have hHall : g.image π ∈ Hall Hd := hB.img g hg
  have hAcoord : ∀ f, f ⊂ g.image π → (coord (V := V) f).IsMeas (A f) :=
    fun f hf => coord_isMeas_of_atom hHd hBd hAtom hR (Hall_down hHall hf.1)
  have hAint : (coord (V := V) (g.image π)).IsMeas (interProper A (g.image π)) :=
    interProper_isMeas (V := V) hAcoord
  have hBc := iInf_bdryAlg_refines_coord (bdryAlg_refines_coord hHd hR hHall)
  have hB'c := iInf_bdryAlg_refines_coord (bdryAlg'_refines_coord hHd hR hHall)
  -- the lower set is the lift of the lower-order intersection
  rw [lowSetAll_AgOf_eq_lowSetLift hB hg hAcoord]
  -- unfold the bundle data
  rw [show (fun v : BPt V π => (bgOf (V := V) B B' A π G hB.inj g v) ^ 2
        * indicator (lowSetLift (V := V) π g (hB.inj g hg) A) v)
      = fun v : BPt V π => (liftFun (V := V) π g (hB.inj g hg)
            (betaOf (V := V) B B' A (g.image π)) v) ^ 2
          * indicator (liftSet (V := V) π g (hB.inj g hg) (interProper A (g.image π))) v
      from by
        funext v
        rw [bgOf, dif_pos hg, lowSetLift]]
  rw [avg_liftFun_sq (V := V) π g (hB.inj g hg)
    (betaOf (V := V) B B' A (g.image π)) hAint]
  rw [show (fun x : Pt V => (betaOf (V := V) B B' A (g.image π)
          (restrict (V := V) x (g.image π))) ^ 2 * indicator (interProper A (g.image π)) x)
      = fun x : Pt V => (bOf (V := V) B B' A (g.image π) x) ^ 2
          * prodT (fun f : {f : Finset ι // f ⊂ g.image π} => A f.val) x
      from by
        funext x
        rw [← betaOf_restrict (V := V) hBc hB'c x, ← prodT_interProper (V := V) A (g.image π) x]]
  rw [show avg (indicator (lowSetLift (V := V) π g (hB.inj g hg) A))
      = avg (prodT (fun f : {f : Finset ι // f ⊂ g.image π} => A f.val)) from by
    rw [lowSetLift, liftSet_avg (V := V) π g (hB.inj g hg) hAint]
    congr 1
    funext x
    exact (prodT_interProper (V := V) A (g.image π) x).symm]
  exact (hGood (g.image π) hHall).2

/-! ## Hypothesis (H4): the discrepancy bound on the `c`-term

Step one: the `cg`-factor is independent of the frozen variables, so the average over the bundle
point space splits (Fubini, `avg_split`) into an outer average over the `g`-coordinates and an
inner average over the complement, with the `cg`-factor pulled out of the inner one. -/

/-- The product of the lifted indicators over `G' ∖ {g}`. -/
noncomputable abbrev prodAgOf {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Finset ι → Finset (Pt V))
    (π : κ → ι) (G G' : Finset (Finset κ))
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) (g : Finset κ) :
    BPt V π → ℝ :=
  fun v => ∏ g' ∈ G'.filter (fun g' => g' ≠ g), indicator (AgOf (V := V) A π G hinj g') v

/-- The `cg`-factor is independent of the coordinates outside `g`. -/
theorem cgOf_combine {Hd : Finset (Finset ι)} {A : Finset ι → Finset (Pt V)}
    {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {G : Finset (Finset κ)}
    (B' : ℕ → Finset ι → SigAlg (Pt V)) (hB : IsBundle Hd π G) {g : Finset κ} (hg : g ∈ G)
    (w : (k : {k // k ∈ g}) → V (π k.val))
    (u : (k : {k // k ∉ g}) → V (π k.val)) :
    cgOf (V := V) B' A π G hB.inj g (combine (V := V) π g w u)
      = gammaOf (V := V) B' A (g.image π)
          (piCongrImage (V := V) π g (hB.inj g hg) w) := by
  rw [cgOf, dif_pos hg, liftFun_apply, restrict_combine]

/-- **Step one of (H4)**: the Fubini split of the `c`-term average. -/
theorem avg_cg_prod_split {Hd : Finset (Finset ι)} {A : Finset ι → Finset (Pt V)}
    {B' : ℕ → Finset ι → SigAlg (Pt V)}
    {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {G : Finset (Finset κ)}
    (hB : IsBundle Hd π G) {g : Finset κ} (hg : g ∈ G) (G' : Finset (Finset κ)) :
    avg (fun v : BPt V π => cgOf (V := V) B' A π G hB.inj g v
        * prodAgOf (V := V) A π G G' hB.inj g v)
      = avg (fun w : (k : {k // k ∈ g}) → V (π k.val) =>
          gammaOf (V := V) B' A (g.image π) (piCongrImage (V := V) π g (hB.inj g hg) w)
            * avg (fun u : (k : {k // k ∉ g}) → V (π k.val) =>
                prodAgOf (V := V) A π G G' hB.inj g (combine (V := V) π g w u))) := by
  rw [avg_split (V := V) π g]
  congr 1
  funext w
  rw [show (fun u : (k : {k // k ∉ g}) → V (π k.val) =>
        cgOf (V := V) B' A π G hB.inj g (combine (V := V) π g w u)
          * prodAgOf (V := V) A π G G' hB.inj g (combine (V := V) π g w u))
      = fun u => gammaOf (V := V) B' A (g.image π)
            (piCongrImage (V := V) π g (hB.inj g hg) w)
          * prodAgOf (V := V) A π G G' hB.inj g (combine (V := V) π g w u)
      from funext (fun u => by rw [cgOf_combine (V := V) B' hB hg w u])]
  exact avg_mul_const _ _

/-! ## (H4) step two: the edge grouping -/

/-- The intersection of two distinct edges of the same order is a proper subset of `g`. -/
theorem inter_ssubset_of_ne_card_le {κ : Type*} [DecidableEq κ] {g' g : Finset κ}
    (hne : g' ≠ g) (hc : g'.card ≤ g.card) : g' ∩ g ⊂ g := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, fun heq => hne ?_⟩
  refine (Finset.eq_of_subset_of_card_le (fun x hx => ?_) hc).symm
  have hxg : x ∈ g' ∩ g := by rw [heq]; exact hx
  exact (Finset.mem_inter.mp hxg).1

/-- A proper subset of `e` is contained in a subset of `e` of one lower cardinality. -/
theorem exists_subset_card_pred {ι : Type*} [DecidableEq ι] {A' e : Finset ι} (h : A' ⊂ e) :
    ∃ f, A' ⊆ f ∧ f ⊆ e ∧ f.card + 1 = e.card := by
  obtain ⟨k₀, hk₀e, hk₀A⟩ := Finset.exists_of_ssubset h
  refine ⟨e.erase k₀, fun x hx => Finset.mem_erase.mpr ⟨fun hxk => hk₀A (hxk ▸ hx), h.1 hx⟩,
    Finset.erase_subset _ _, ?_⟩
  rw [Finset.card_erase_of_mem hk₀e]
  have : 1 ≤ e.card := Finset.card_pos.mpr ⟨k₀, hk₀e⟩
  omega

/-- The image of `g' ∩ g` is a proper subset of the image of `g`. -/
theorem inter_image_ssubset_image {κ : Type*} [Fintype κ] [DecidableEq κ]
    {Hd : Finset (Finset ι)} {π : κ → ι} {G : Finset (Finset κ)}
    (hB : IsBundle Hd π G) {g g' : Finset κ} (hg : g ∈ G) (hne : g' ≠ g)
    (hc : g'.card ≤ g.card) : (g' ∩ g).image π ⊂ g.image π :=
  image_ssubset_image (hB.inj g hg) Finset.inter_subset_right
    (Finset.ssubset_iff_subset_ne.mp (inter_ssubset_of_ne_card_le hne hc)).2

/-- **Step two of (H4)**: every bundle edge `g' ≠ g` of no larger order has its intersection
with `g` contained in a codimension-one face of `g.image π`. -/
theorem exists_del_superset {κ : Type*} [Fintype κ] [DecidableEq κ]
    {Hd : Finset (Finset ι)} {π : κ → ι} {G : Finset (Finset κ)} (hB : IsBundle Hd π G)
    {g g' : Finset κ} (hg : g ∈ G) (hne : g' ≠ g) (hc : g'.card ≤ g.card) :
    ∃ f ∈ del (g.image π), (g' ∩ g).image π ⊆ f := by
  obtain ⟨f, h1, h2, h3⟩ := exists_subset_card_pred (inter_image_ssubset_image hB hg hne hc)
  exact ⟨f, mem_del.mpr ⟨h2, h3⟩, h1⟩

/-- **Step two of (H4)**, in the form used for the grouping. -/
theorem exists_del_superset_of_mem {κ : Type*} [Fintype κ] [DecidableEq κ]
    {Hd : Finset (Finset ι)} {π : κ → ι} {G : Finset (Finset κ)}
    (hB : IsBundle Hd π G) {g : Finset κ} (hg : g ∈ G) {G' : Finset (Finset κ)}
    (hc : ∀ g' ∈ G', g'.card ≤ g.card) {g' : Finset κ} (hg' : g' ∈ G') (hne : g' ≠ g) :
    ∃ f ∈ del (g.image π), (g' ∩ g).image π ⊆ f :=
  exists_del_superset hB hg hne (hc g' hg')

/-! ## (H4) step three: the ambient sets `E_f`

For a fixed choice of the frozen coordinates `u` outside `g`, each bundle edge `g' ≠ g` is
read by the ambient point `x` (together with `u`) through the "combined" point `dblPt u x`.
The face `f ∈ del (g.image π)` collects those `g'` whose intersection with `g` maps into `f`,
and the set `E_f` is the conjunction of the corresponding membership conditions — the point
being that it only ever reads the coordinates of `x` inside `f`. -/

/-- Membership in a lift depends only on the coordinates of the edge. -/
theorem mem_liftSet_congr {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) {A' : Finset (Pt V)} {v v' : BPt V π}
    (h : ∀ k ∈ g, v k = v' k) :
    v ∈ liftSet (V := V) π g hinj A' ↔ v' ∈ liftSet (V := V) π g hinj A' := by
  rw [mem_liftSet_iff, mem_liftSet_iff]
  constructor
  · rintro ⟨x, hx, hv⟩
    exact ⟨x, hx, fun k hk => (hv k hk).trans (h k hk)⟩
  · rintro ⟨x, hx, hv⟩
    exact ⟨x, hx, fun k kk => (hv k kk).trans (h k kk).symm⟩

/-- The bundle point obtained from an ambient point `x` (on the coordinates of `g`) together
with the frozen coordinates `u`. -/
noncomputable def dblPt {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b)
    (u : (k : {k // k ∉ g}) → V (π k.val)) (x : Pt V) : BPt V π :=
  combine (V := V) π g
    ((piCongrImage (V := V) π g hinj).symm (restrict (V := V) x (g.image π))) u

theorem dblPt_apply_mem {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b)
    (u : (k : {k // k ∉ g}) → V (π k.val)) (x : Pt V) {k : κ} (hk : k ∈ g) :
    dblPt (V := V) π g hinj u x k = x (π k) := by
  rw [dblPt, combine_apply_mem (V := V) π g _ u hk, piCongrImage_symm_apply, restrict_apply]

theorem dblPt_apply_notMem {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b)
    (u : (k : {k // k ∉ g}) → V (π k.val)) (x : Pt V) {k : κ} (hk : k ∉ g) :
    dblPt (V := V) π g hinj u x k = u ⟨k, hk⟩ := by
  rw [dblPt, combine_apply_notMem (V := V) π g _ u hk]

/-- Two ambient points agreeing on `f` give the same combined bundle point on any edge whose
intersection with `g` maps into `f`. -/
theorem dblPt_agree {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) {g g' : Finset κ}
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b)
    (u : (k : {k // k ∉ g}) → V (π k.val)) {x y : Pt V} {f : Finset ι}
    (hf : (g' ∩ g).image π ⊆ f) (hxy : ∀ i ∈ f, x i = y i) :
    ∀ k ∈ g', dblPt (V := V) π g hinj u x k = dblPt (V := V) π g hinj u y k := by
  intro k hk
  by_cases hkg : k ∈ g
  · rw [dblPt_apply_mem (V := V) π g hinj u x hkg, dblPt_apply_mem (V := V) π g hinj u y hkg]
    exact hxy (π k) (hf (Finset.mem_image.mpr ⟨k, Finset.mem_inter.mpr ⟨hk, hkg⟩, rfl⟩))
  · rw [dblPt_apply_notMem (V := V) π g hinj u x hkg,
      dblPt_apply_notMem (V := V) π g hinj u y hkg]

/-- The ambient set `E_f` attached to a face `f` and a frozen configuration `u`. -/
noncomputable def EfF {κ : Type*} [Fintype κ] [DecidableEq κ] (A : Finset ι → Finset (Pt V))
    (π : κ → ι) (G G' : Finset (Finset κ))
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) {g : Finset κ} (hg : g ∈ G)
    (u : (k : {k // k ∉ g}) → V (π k.val)) (f : Finset ι) : Finset (Pt V) :=
  Finset.univ.filter (fun x => ∀ g' ∈ G'.filter (fun g' => g' ≠ g),
    (g' ∩ g).image π ⊆ f →
      dblPt (V := V) π g (hinj g hg) u x ∈ AgOf (V := V) A π G hinj g')

theorem mem_EfF {κ : Type*} [Fintype κ] [DecidableEq κ] {A : Finset ι → Finset (Pt V)}
    {π : κ → ι} {G G' : Finset (Finset κ)}
    {hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b} {g : Finset κ} {hg : g ∈ G}
    {u : (k : {k // k ∉ g}) → V (π k.val)} {f : Finset ι} {x : Pt V} :
    x ∈ EfF (V := V) A π G G' hinj hg u f ↔
      ∀ g' ∈ G'.filter (fun g' => g' ≠ g), (g' ∩ g).image π ⊆ f →
        dblPt (V := V) π g (hinj g hg) u x ∈ AgOf (V := V) A π G hinj g' := by
  classical
  simp only [EfF, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Membership in `AgOf` is invariant under changing a bundle point on the edge `g'`. -/
theorem AgOf_congr {κ : Type*} [Fintype κ] [DecidableEq κ] {A : Finset ι → Finset (Pt V)}
    {π : κ → ι} {G : Finset (Finset κ)}
    {hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b} {g' : Finset κ}
    {v v' : BPt V π} (h : ∀ k ∈ g', v k = v' k) :
    v ∈ AgOf (V := V) A π G hinj g' ↔ v' ∈ AgOf (V := V) A π G hinj g' := by
  by_cases hG : g' ∈ G
  · rw [AgOf_of_mem (V := V) A π G hinj hG]
    exact mem_liftSet_congr (V := V) π g' (hinj g' hG) h
  · rw [AgOf, dif_neg hG]
    simp

/-- **Step three of (H4)**: each `E_f` is measurable for the coordinate algebra of `f`. -/
theorem EfF_isMeas {κ : Type*} [Fintype κ] [DecidableEq κ] {A : Finset ι → Finset (Pt V)}
    {π : κ → ι} {G G' : Finset (Finset κ)}
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) {g : Finset κ} (hg : g ∈ G)
    (u : (k : {k // k ∉ g}) → V (π k.val)) (f : Finset ι) :
    (coord (V := V) f).IsMeas (EfF (V := V) A π G G' hinj hg u f) := by
  classical
  rw [coord_isMeas_iff]
  intro x y hxy
  rw [mem_EfF, mem_EfF]
  constructor
  · intro h g' hg' hsub
    exact (AgOf_congr (V := V) (A := A) (π := π) (G := G) (hinj := hinj)
      (dblPt_agree (V := V) π (hinj g hg) u hsub (fun i hi => (hxy i hi).symm))).mpr
      (h g' hg' hsub)
  · intro h g' hg' hsub
    exact (AgOf_congr (V := V) (A := A) (π := π) (G := G) (hinj := hinj)
      (dblPt_agree (V := V) π (hinj g hg) u hsub (fun i hi => (hxy i hi).symm))).mp
      (h g' hg' hsub)

end Szemeredi.Removal
