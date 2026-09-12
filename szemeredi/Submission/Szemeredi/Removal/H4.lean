import Mathlib
import Submission.Szemeredi.Removal.Lift

/-!
# Hypothesis (H4) of the counting lemma (Tao, arXiv:math/0503572, §4)

The `c`-term of the counting lemma: the discrepancy conjunct of the corrected full
regularity lemma (`RegOK2`) for the face `e = g.image π` is transported to the bundle
edge `g` by freezing the coordinates outside `g`, averaging over the coordinates
inside `g`, and reading each remaining factor `1_{A_{g'}}` (`g' ≠ g`, `|g'| ≤ |g|`) as a
`coord f`-measurable ambient set `E_f` for a codimension-one face `f ∈ ∂e`.

The main output is `gchyp_h4`, which together with `gchyp_h1`, `gchyp_h2`, `gchyp_h3`
furnishes the abstract hypotheses `GCHyp` for the lifted data.
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]

/-! ## Elementary facts about the averages at the level of `Pt V` -/

/-- The average of a difference is the difference of the averages. -/
theorem avg_sub' (f g : Pt V → ℝ) : avg (fun x => f x - g x) = avg f - avg g := by
  unfold avg
  rw [Finset.sum_sub_distrib]
  ring

/-- Equality of indicators of a `coord e`-measurable set at two points agreeing on `e`. -/
theorem indicator_eq_of_meas_agree {e : Finset ι} {E : Finset (Pt V)}
    (hE : (coord (V := V) e).IsMeas E) {x y : Pt V} (hxy : ∀ i ∈ e, y i = x i) :
    indicator E y = indicator E x := by
  have hiff := (coord_isMeas_iff.mp hE) x y hxy
  unfold indicator
  by_cases hx : x ∈ E
  · rw [if_pos (hiff.mpr hx), if_pos hx]
  · rw [if_neg (fun h => hx (hiff.mp h)), if_neg hx]

/-! ## The bundle point built from an ambient point -/

/-- **The combined bundle point of an ambient point**: if the restriction of `x` to `e` is
the bundle point `w`, then combining `w` with the frozen coordinates `u` is the same as
combining the restriction of `x` with `u`. -/
theorem dblPt_of_restrict_eq {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι)
    {g : Finset κ} (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b)
    {w : (k : {k // k ∈ g}) → V (π k.val)}
    {u : (k : {k // k ∉ g}) → V (π k.val)} {x : Pt V}
    (hx : restrict (V := V) x (g.image π) = piCongrImage (V := V) π g hinj w) :
    dblPt (V := V) π g hinj u x = combine (V := V) π g w u := by
  rw [dblPt, hx, Equiv.symm_apply_apply]

/-! ## The ambient product over the boundary of an edge -/

/-- The product of the ambient sets `E_f` attached to the boundary of `g.image π`. -/
noncomputable abbrev EfProd {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Finset ι → Finset (Pt V)) (π : κ → ι) (G G' : Finset (Finset κ))
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) {g : Finset κ} (hg : g ∈ G)
    (u : (k : {k // k ∉ g}) → V (π k.val)) : Pt V → ℝ :=
  fun x => ∏ f ∈ del (g.image π), indicator (EfF (V := V) A π G G' hinj hg u f) x

/-- The product of the ambient sets is invariant under changing the point on `g.image π`. -/
theorem prod_EfF_congr {κ : Type*} [Fintype κ] [DecidableEq κ] {A : Finset ι → Finset (Pt V)}
    {π : κ → ι} {G G' : Finset (Finset κ)}
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) {g : Finset κ} (hg : g ∈ G)
    (u : (k : {k // k ∉ g}) → V (π k.val)) {x y : Pt V}
    (hxy : ∀ i ∈ g.image π, y i = x i) :
    EfProd (V := V) A π G G' hinj hg u y = EfProd (V := V) A π G G' hinj hg u x :=
  Finset.prod_congr rfl (fun f hf => indicator_eq_of_meas_agree
    (EfF_isMeas (V := V) hinj hg u f) (fun i hi => hxy i ((mem_del.mp hf).1 hi)))

/-! ## The product identity -/

/-- **The product identity for (H4)**: the product of the lifted indicators over the edges
`g' ≠ g` of `G'` of order at most that of `g`, evaluated at the combined point, is the
product of the ambient sets over the boundary of `g.image π`. -/
theorem prodAgOf_dblPt {Hd : Finset (Finset ι)} {A : Finset ι → Finset (Pt V)}
    {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {G : Finset (Finset κ)}
    (hB : IsBundle Hd π G) {g : Finset κ} (hg : g ∈ G) {G' : Finset (Finset κ)}
    (hc : ∀ g' ∈ G', g'.card ≤ g.card)
    (u : (k : {k // k ∉ g}) → V (π k.val)) (x : Pt V) :
    prodAgOf (V := V) A π G G' hB.inj g (dblPt (V := V) π g (hB.inj g hg) u x)
      = EfProd (V := V) A π G G' hB.inj hg u x := by
  classical
  have hfilter : (G'.filter (fun g' => g' ≠ g)).filter (fun g' => True)
      = G'.filter (fun g' => g' ≠ g) := Finset.filter_true_of_mem (fun _ _ => trivial)
  change (∏ g' ∈ G'.filter (fun g' => g' ≠ g),
      indicator (AgOf (V := V) A π G hB.inj g') (dblPt (V := V) π g (hB.inj g hg) u x))
    = ∏ f ∈ del (g.image π), indicator (EfF (V := V) A π G G' hB.inj hg u f) x
  rw [show (∏ g' ∈ G'.filter (fun g' => g' ≠ g),
        indicator (AgOf (V := V) A π G hB.inj g') (dblPt (V := V) π g (hB.inj g hg) u x))
      = ∏ g' ∈ G'.filter (fun g' => g' ≠ g),
          (if dblPt (V := V) π g (hB.inj g hg) u x ∈ AgOf (V := V) A π G hB.inj g'
            then (1 : ℝ) else 0) from rfl]
  rw [Commons.Data.Finset.prod_ite_one_mem]
  rw [show (∏ f ∈ del (g.image π), indicator (EfF (V := V) A π G G' hB.inj hg u f) x)
      = ∏ f ∈ del (g.image π),
          (if x ∈ EfF (V := V) A π G G' hB.inj hg u f then (1 : ℝ) else 0) from rfl]
  rw [Commons.Data.Finset.prod_ite_one_mem]
  by_cases h : ∀ g' ∈ G'.filter (fun g' => g' ≠ g),
      dblPt (V := V) π g (hB.inj g hg) u x ∈ AgOf (V := V) A π G hB.inj g'
  · rw [if_pos h]
    have h2 : ∀ f ∈ del (g.image π), x ∈ EfF (V := V) A π G G' hB.inj hg u f := by
      intro f hf
      rw [mem_EfF]
      exact fun g' hg' _ => h g' hg'
    rw [if_pos h2]
  · rw [if_neg h]
    have h2 : ¬ (∀ f ∈ del (g.image π), x ∈ EfF (V := V) A π G G' hB.inj hg u f) := by
      intro hh
      apply h
      intro g' hg'
      obtain ⟨hg'G', hg'ne⟩ := Finset.mem_filter.mp hg'
      obtain ⟨f, hf, hsub⟩ :=
        exists_del_superset_of_mem hB hg hc hg'G' hg'ne
      exact (mem_EfF.mp (hh f hf)) g' hg' hsub
    rw [if_neg h2]

/-! ## The main transport identity of (H4) -/

/-- **The `u`-level identity of (H4)**: for frozen coordinates `u`, the average over the
`g`-coordinates of the `c`-term times the lifted product equals the ambient average of the
`c`-term times the product of the boundary sets. -/
theorem avg_cg_prod_eq {Hd : Finset (Finset ι)} {A : Finset ι → Finset (Pt V)}
    {B' : ℕ → Finset ι → SigAlg (Pt V)}
    {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {G : Finset (Finset κ)}
    (hB : IsBundle Hd π G) {g : Finset κ} (hg : g ∈ G) (G' : Finset (Finset κ))
    (hc : ∀ g' ∈ G', g'.card ≤ g.card)
    (hAe : (coord (V := V) (g.image π)).IsMeas (A (g.image π)))
    (hB'c : (SigAlg.iInf (bdryAlg (V := V) B' (g.image π).card (g.image π))
        Finset.univ).Refines (coord (V := V) (g.image π)))
    (u : (k : {k // k ∉ g}) → V (π k.val)) :
    avg (fun w : (k : {k // k ∈ g}) → V (π k.val) =>
        gammaOf (V := V) B' A (g.image π) (piCongrImage (V := V) π g (hB.inj g hg) w)
          * prodAgOf (V := V) A π G G' hB.inj g (combine (V := V) π g w u))
      = avg (fun x : Pt V => cOf (V := V) B' A (g.image π) x
          * EfProd (V := V) A π G G' hB.inj hg u x) := by
  classical
  have h1 : avg (fun w : (k : {k // k ∈ g}) → V (π k.val) =>
        gammaOf (V := V) B' A (g.image π) (piCongrImage (V := V) π g (hB.inj g hg) w)
          * prodAgOf (V := V) A π G G' hB.inj g (combine (V := V) π g w u))
      = avg (fun w : (k : {k // k ∈ g}) → V (π k.val) =>
          gammaOf (V := V) B' A (g.image π) (piCongrImage (V := V) π g (hB.inj g hg) w)
            * EfProd (V := V) A π G G' hB.inj hg u
                (extOfPd (V := V) (g.image π)
                  (piCongrImage (V := V) π g (hB.inj g hg) w))) := by
    congr 1
    funext w
    congr 1
    rw [← prodAgOf_dblPt (V := V) hB hg hc u
      (extOfPd (V := V) (g.image π) (piCongrImage (V := V) π g (hB.inj g hg) w)),
      dblPt_of_restrict_eq (V := V) π (hB.inj g hg) (u := u)
        (restrict_extOfPd (V := V) (g.image π)
          (piCongrImage (V := V) π g (hB.inj g hg) w))]
  have h2 : avg (fun w : (k : {k // k ∈ g}) → V (π k.val) =>
          gammaOf (V := V) B' A (g.image π) (piCongrImage (V := V) π g (hB.inj g hg) w)
            * EfProd (V := V) A π G G' hB.inj hg u
                (extOfPd (V := V) (g.image π)
                  (piCongrImage (V := V) π g (hB.inj g hg) w)))
      = avg (fun y : Pd (V := V) (g.image π) =>
          gammaOf (V := V) B' A (g.image π) y
            * EfProd (V := V) A π G G' hB.inj hg u
                (extOfPd (V := V) (g.image π) y)) :=
    avg_equiv' (piCongrImage (V := V) π g (hB.inj g hg))
      (fun y : Pd (V := V) (g.image π) => gammaOf (V := V) B' A (g.image π) y
        * EfProd (V := V) A π G G' hB.inj hg u (extOfPd (V := V) (g.image π) y))
  have h3 : avg (fun x : Pt V => cOf (V := V) B' A (g.image π) x
          * EfProd (V := V) A π G G' hB.inj hg u x)
      = avg (fun y : Pd (V := V) (g.image π) =>
          gammaOf (V := V) B' A (g.image π) y
            * EfProd (V := V) A π G G' hB.inj hg u
                (extOfPd (V := V) (g.image π) y)) := by
    rw [← avg_restrict_eq (V := V) (g.image π)
      (fun y : Pd (V := V) (g.image π) => gammaOf (V := V) B' A (g.image π) y
        * EfProd (V := V) A π G G' hB.inj hg u (extOfPd (V := V) (g.image π) y))]
    congr 1
    funext x
    rw [← gammaOf_restrict (V := V) hAe hB'c x]
    congr 1
    exact (prod_EfF_congr (V := V) hB.inj hg u (fun i hi => by
      rw [extOfPd_apply (V := V) _ hi, restrict_apply])).symm
  rw [h1, h2, h3]

/-! ## The `Pseudorandom` instance -/

/-- The pseudorandomness condition is vacuous for the empty face. -/
theorem pseudorandom_empty (Ee : Finset (Pt V)) (B : SigAlg (Pt V)) {δ : ℝ} (hδ : 0 ≤ δ) :
    Pseudorandom (V := V) (∅ : Finset ι) Ee B δ := by
  intro Ex _
  have hdel : del (∅ : Finset ι) = ∅ := by
    rw [del, Finset.powerset_empty, Finset.filter_eq_empty_iff]
    intro f hf
    rw [Finset.mem_singleton] at hf
    subst hf
    simp
  rw [show (fun x : Pt V => (indicator Ee x - B.condExp (indicator Ee) x)
        * ∏ f ∈ del (∅ : Finset ι), indicator (Ex f) x)
      = fun x : Pt V => indicator Ee x - B.condExp (indicator Ee) x from by
    funext x
    rw [hdel]
    simp]
  rw [show avg (fun x : Pt V => indicator Ee x - B.condExp (indicator Ee) x) = 0 from by
    rw [avg_sub', avg_condExp]
    ring]
  rw [abs_zero]
  exact hδ

/-- **The discrepancy estimate for a face**: the `Pseudorandom` conjunct of `RegOK2`,
extended to the empty face (where it is vacuous). -/
theorem pseudorandom_of_RegOK2 {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)}
    {Md : ℕ} {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    {A : Finset ι → Finset (Pt V)}
    (hHd : ∀ e ∈ Hd, e.card = d)
    (hAtom : ∀ f ∈ Hall Hd, A f ∈ (algOf (V := V) d Bd B f).atoms)
    (hR : RegOK2 (V := V) d Hd Bd Md F B B' M)
    (hδ0 : (0 : ℝ) ≤ 1 / (F (M 0) : ℝ))
    {e : Finset ι} (he : e ∈ Hall Hd) :
    Pseudorandom (V := V) e (A e)
      (SigAlg.iInf (bdryAlg (V := V) B' e.card e) Finset.univ) (1 / (F (M 0) : ℝ)) := by
  classical
  by_cases h0 : e.card = 0
  · rw [Finset.card_eq_zero.mp h0]
    exact pseudorandom_empty (V := V) _ _ hδ0
  · have h1 : 1 ≤ e.card := Nat.one_le_iff_ne_zero.mpr h0
    have h2 : e.card ≤ d := Hall_card_le hHd he
    have hlev : e ∈ lev Hd (d - e.card) := Hall_mem_lev hHd he
    have hmeas : (edgeAlg (V := V) Bd B d e.card e).IsMeas (A e) :=
      IsMeas_of_mem_atoms (hAtom e he)
    have heq : SigAlg.iInf (bdryAlg (V := V) B' e.card e) Finset.univ
        = SigAlg.iInf (B' (e.card - 1)) (del e) :=
      iInf_image_eq (V := V) (del e) (fun f => B' (e.card - 1) f)
    rw [heq]
    exact hR.2.2.2.2.2.2.2.2 e.card h1 h2 e hlev (A e) hmeas

/-! ## Hypothesis (H4) -/

/-- **Hypothesis (H4)**: the discrepancy bound for the `c`-term, transported to a bundle. -/
theorem gchyp_h4 {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)} {Md : ℕ}
    {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    {A : Finset ι → Finset (Pt V)}
    (hHd : ∀ e ∈ Hd, e.card = d)
    (hBd : ∀ e ∈ Hd, (Bd e).Refines (coord (V := V) e))
    (hAtom : ∀ f ∈ Hall Hd, A f ∈ (algOf (V := V) d Bd B f).atoms)
    (hR : RegOK2 (V := V) d Hd Bd Md F B B' M)
    (hF1 : 1 ≤ F (M 0))
    {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {G : Finset (Finset κ)}
    (hB : IsBundle Hd π G) {g : Finset κ} (hg : g ∈ G) {G' : Finset (Finset κ)}
    (hgG' : g ∈ G') (hc : ∀ g' ∈ G', g'.card ≤ g.card) :
    |avg (fun v : BPt V π => cgOf (V := V) B' A π G hB.inj g v
        * prodAgOf (V := V) A π G G' hB.inj g v)| ≤ 1 / (F (M 0) : ℝ) := by
  classical
  have hHall : g.image π ∈ Hall Hd := hB.img g hg
  have hAe : (coord (V := V) (g.image π)).IsMeas (A (g.image π)) :=
    coord_isMeas_of_atom (V := V) hHd hBd hAtom hR hHall
  have hB'c : (SigAlg.iInf (bdryAlg (V := V) B' (g.image π).card (g.image π))
      Finset.univ).Refines (coord (V := V) (g.image π)) :=
    iInf_bdryAlg_refines_coord (V := V) (bdryAlg'_refines_coord hHd hR hHall)
  have hδ0 : (0 : ℝ) ≤ 1 / (F (M 0) : ℝ) := by
    have hpos : (0 : ℝ) < (F (M 0) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hF1)
    positivity
  have hpsd := pseudorandom_of_RegOK2 (V := V) hHd hAtom hR hδ0 hHall
  rw [avg_cg_prod_split (V := V) hB hg G']
  rw [show (fun w : (k : {k // k ∈ g}) → V (π k.val) =>
        gammaOf (V := V) B' A (g.image π) (piCongrImage (V := V) π g (hB.inj g hg) w)
          * avg (fun u : (k : {k // k ∉ g}) → V (π k.val) =>
              prodAgOf (V := V) A π G G' hB.inj g (combine (V := V) π g w u)))
      = fun w : (k : {k // k ∈ g}) → V (π k.val) =>
          avg (fun u : (k : {k // k ∉ g}) → V (π k.val) =>
            gammaOf (V := V) B' A (g.image π) (piCongrImage (V := V) π g (hB.inj g hg) w)
              * prodAgOf (V := V) A π G G' hB.inj g (combine (V := V) π g w u)) from by
    funext w
    rw [avg_mul_const]]
  rw [avg_swap (fun (w : (k : {k // k ∈ g}) → V (π k.val))
      (u : (k : {k // k ∉ g}) → V (π k.val)) =>
    gammaOf (V := V) B' A (g.image π) (piCongrImage (V := V) π g (hB.inj g hg) w)
      * prodAgOf (V := V) A π G G' hB.inj g (combine (V := V) π g w u))]
  refine avg_abs_le_of_le (fun u => ?_)
  rw [avg_cg_prod_eq (V := V) hB hg G' hc hAe hB'c u]
  exact hpsd (fun f => EfF (V := V) A π G G' hB.inj hg u f)
    (fun f _ => EfF_isMeas (V := V) hB.inj hg u f)

/-- **The abstract hypotheses of the counting lemma**: the lifted data of a bundle satisfies
`GCHyp`.  This assembles (H1)–(H4) (`gchyp_h1`, `gchyp_h2`, `gchyp_h3`, `gchyp_h4`). -/
theorem gchyp_of_RegOK2 {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)}
    {Md : ℕ} {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    {A : Finset ι → Finset (Pt V)}
    (hHd : ∀ e ∈ Hd, e.card = d)
    (hBd : ∀ e ∈ Hd, (Bd e).Refines (coord (V := V) e))
    (hAtom : ∀ f ∈ Hall Hd, A f ∈ (algOf (V := V) d Bd B f).atoms)
    (hGood : ∀ e ∈ Hall Hd, GoodAt (V := V) d Bd B B' M F A e.card e)
    (hR : RegOK2 (V := V) d Hd Bd Md F B B' M)
    (hF1 : 1 ≤ F (M 0))
    {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {G : Finset (Finset κ)}
    (hB : IsBundle Hd π G)
    (hlog : ∀ g ∈ G, 1 ≤ Real.log (RgOf F M π g)) :
    GCHyp (V := V) π G (AgOf (V := V) A π G hB.inj) (pgOf A π) (RgOf F M π)
      (bgOf (V := V) B B' A π G hB.inj) (cgOf (V := V) B' A π G hB.inj)
      (1 / (F (M 0) : ℝ)) :=
  ⟨fun g _ => pOf_nonneg A (g.image π),
   fun g _ => pOf_le_one A (g.image π),
   fun g hg v hv => gchyp_h1 (V := V) hHd hBd hAtom hGood hR hB hg hv,
   fun g hg => gchyp_h2 (V := V) (Md := Md) hGood hB hg (hlog g hg),
   fun g hg => gchyp_h3 (V := V) hHd hBd hAtom hGood hR hB hg,
   fun g hg G' hgG' hc => gchyp_h4 (V := V) hHd hBd hAtom hR hF1 hB hg hgG' hc⟩

end Szemeredi.Removal
