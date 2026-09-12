import Mathlib
import Submission.Szemeredi.Removal.Bterm
import Submission.Szemeredi.Removal.GencountConst

/-!
# Tao's generalized counting lemma (`gencount`)

This file completes the proof of the generalized counting lemma: the single induction
step (`gencount_step`), and the double induction on the order `d'` and the number of
edges.
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]

/-! ## Sub-bundles and the partition into lower / top edges -/

theorem isBundle_Glt {Hd : Finset (Finset ι)} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {π : κ → ι} {G : Finset (Finset κ)} {g₀ : Finset κ} (hB : IsBundle Hd π G) :
    IsBundle Hd π (Glt G g₀) where
  closed := fun g hg g' hg' =>
    mem_Glt.mpr ⟨hB.closed g (mem_Glt.mp hg).1 g' hg',
      lt_of_le_of_lt hg' (mem_Glt.mp hg).2⟩
  inj := fun g hg => hB.inj g (mem_Glt.mp hg).1
  img := fun g hg => hB.img g (mem_Glt.mp hg).1

theorem isBundle_dblG {Hd : Finset (Finset ι)} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {π : κ → ι} {G : Finset (Finset κ)} {g₀ : Finset κ} {D : ℕ} (hB : IsBundle Hd π G) :
    IsBundle Hd (dblπ π g₀) (dblG G g₀ D) where
  closed := fun gg hgg gg' hgg' => dblG_closed hB.closed hgg hgg'
  inj := dblInjOn G g₀ D π hB.inj
  img := fun gg hgg => by
    obtain ⟨h, hh, hinl | hinr⟩ := (mem_dblG).mp hgg
    · rw [hinl.2, dblEdge_image]; exact hB.img h hh
    · rcases hinr.2.2 with h1 | h1
      · rw [h1, dblEdge_image]; exact hB.img h hh
      · rw [h1, dblEdge_image]; exact hB.img h hh

/-- The edges of `G` of order exactly `D`. -/
def Top {κ : Type*} (G : Finset (Finset κ)) (D : ℕ) : Finset (Finset κ) :=
  G.filter (fun g => g.card = D)

theorem mem_Top {κ : Type*} {G : Finset (Finset κ)} {D : ℕ} {g : Finset κ} :
    g ∈ Top G D ↔ g ∈ G ∧ g.card = D := Finset.mem_filter

theorem Glt_union_Ggt_eq {κ : Type*} [Fintype κ] [DecidableEq κ]
    {G : Finset (Finset κ)} {g₀ : Finset κ} {D : ℕ}
    (hg₀card : g₀.card = D) (hD : 1 ≤ D) :
    Glt G g₀ ∪ Ggt G g₀ D = G.filter (fun g => g.card ≤ D - 1) := by
  ext g
  rw [Finset.mem_union, mem_Glt, mem_Ggt, Finset.mem_filter]
  constructor
  · rintro (⟨hg, hlt⟩ | ⟨hg, _, hc⟩)
    · exact ⟨hg, by have h := Finset.card_lt_card hlt; omega⟩
    · exact ⟨hg, hc⟩
  · rintro ⟨hg, hc⟩
    by_cases hlt : g ⊂ g₀
    · exact Or.inl ⟨hg, hlt⟩
    · exact Or.inr ⟨hg, hlt, hc⟩

theorem disjoint_Glt_Ggt' {κ : Type*} [Fintype κ] [DecidableEq κ]
    {G : Finset (Finset κ)} {g₀ : Finset κ} {D : ℕ}
    (hg₀card : g₀.card = D) (hD : 1 ≤ D) :
    Disjoint (Glt G g₀ ∪ Ggt G g₀ D) (Top G D) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  rw [Glt_union_Ggt_eq hg₀card hD, Finset.mem_filter] at ha
  rw [mem_Top] at hb
  omega

theorem union_Glt_Ggt_Top {κ : Type*} [Fintype κ] [DecidableEq κ]
    {G : Finset (Finset κ)} {g₀ : Finset κ} {D : ℕ}
    (hg₀ : g₀ ∈ G) (hg₀card : g₀.card = D) (hD : 1 ≤ D) (hord : ∀ g ∈ G, g.card ≤ D) :
    Glt G g₀ ∪ Ggt G g₀ D ∪ Top G D = G := by
  ext g
  rw [Finset.mem_union, Glt_union_Ggt_eq hg₀card hD, Finset.mem_filter, mem_Top]
  constructor
  · rintro (⟨hg, _⟩ | ⟨hg, _⟩) <;> exact hg
  · intro hg
    rcases lt_or_eq_of_le (hord g hg) with h | h
    · exact Or.inl ⟨hg, by omega⟩
    · exact Or.inr ⟨hg, h⟩

/-- The product decomposition `∏_{Glt} · ∏_{Ggt} · ∏_{Top} = ∏_G`. -/
theorem prod_Glt_Ggt_Top {κ : Type*} [Fintype κ] [DecidableEq κ]
    {G : Finset (Finset κ)} {g₀ : Finset κ} {D : ℕ}
    (hg₀ : g₀ ∈ G) (hg₀card : g₀.card = D) (hD : 1 ≤ D) (hord : ∀ g ∈ G, g.card ≤ D)
    (f : Finset κ → ℝ) :
    (∏ g ∈ Glt G g₀, f g) * (∏ g ∈ Ggt G g₀ D, f g) * (∏ g ∈ Top G D, f g)
      = ∏ g ∈ G, f g := by
  rw [← Finset.prod_union (disjoint_Glt_Ggt G g₀ D),
      ← Finset.prod_union (disjoint_Glt_Ggt' (G := G) (g₀ := g₀) (D := D) hg₀card hD),
      union_Glt_Ggt_Top hg₀ hg₀card hD hord]


/-- `#dblG ≤ 2 #G`. -/
theorem dblG_card_le_two {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G : Finset (Finset κ)) (g₀ : Finset κ) (D : ℕ) :
    (dblG G g₀ D).card ≤ 2 * G.card := by
  have h1 : ((Glt G g₀).image (dblEdge g₀ false) ∪ (Ggt G g₀ D).image (dblEdge g₀ false)
      ∪ (Ggt G g₀ D).image (dblEdge g₀ true)).card
      ≤ ((Glt G g₀).image (dblEdge g₀ false)).card
        + ((Ggt G g₀ D).image (dblEdge g₀ false)).card
        + ((Ggt G g₀ D).image (dblEdge g₀ true)).card := by
    have h2 := Finset.card_union_le ((Glt G g₀).image (dblEdge g₀ false)
      ∪ (Ggt G g₀ D).image (dblEdge g₀ false)) ((Ggt G g₀ D).image (dblEdge g₀ true))
    have h3 := Finset.card_union_le ((Glt G g₀).image (dblEdge g₀ false))
      ((Ggt G g₀ D).image (dblEdge g₀ false))
    omega
  have h4 : ((Glt G g₀).image (dblEdge g₀ false)).card ≤ (Glt G g₀).card :=
    Finset.card_image_le
  have h5 : ((Ggt G g₀ D).image (dblEdge g₀ false)).card ≤ (Ggt G g₀ D).card :=
    Finset.card_image_le
  have h6 : ((Ggt G g₀ D).image (dblEdge g₀ true)).card ≤ (Ggt G g₀ D).card :=
    Finset.card_image_le
  have h7 : (Glt G g₀).card + (Ggt G g₀ D).card ≤ G.card := by
    rw [← Finset.card_union_of_disjoint (disjoint_Glt_Ggt G g₀ D)]
    exact Finset.card_le_card (fun a ha => by
      rw [Finset.mem_union] at ha
      exact ha.elim (fun h => (mem_Glt.mp h).1) (fun h => (mem_Ggt.mp h).1))
  rw [dblG]
  omega


/-- The main induction step of the generalized counting lemma. -/
theorem gencount_step
    {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)} {Md : ℕ}
    {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    {A : Finset ι → Finset (Pt V)}
    (hHd : ∀ e ∈ Hd, e.card = d)
    (hBd : ∀ e ∈ Hd, (Bd e).Refines (coord (V := V) e))
    (hAtom : ∀ f ∈ Hall Hd, A f ∈ (algOf (V := V) d Bd B f).atoms)
    (hGood : ∀ e ∈ Hall Hd, GoodAt (V := V) d Bd B B' M F A e.card e)
    (hR : RegOK2 (V := V) d Hd Bd Md F B B' M)
    (hF1 : 1 ≤ F (M 0)) (hFmono : Monotone F) (hFgrow : ∀ n, n + 1 ≤ F n)
    (hlog : ∀ e ∈ Hall Hd, 1 ≤ Real.log ((F (M e.card) : ℕ) : ℝ))
    {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {G : Finset (Finset κ)}
    (hB : IsBundle Hd π G) {g₀ : Finset κ} (hg₀ : g₀ ∈ G) {D : ℕ}
    (hD : 1 ≤ D) (hg₀card : g₀.card = D) (hord : ∀ g ∈ G, g.card ≤ D)
    (hIHerase : |Cnt π (G.erase g₀) (AgOf (V := V) A π G hB.inj)
        - ∏ g ∈ G.erase g₀, pgOf A π g|
        ≤ ThetaC F M D (G.erase g₀).card * (∏ g ∈ G.erase g₀, pgOf A π g)
          + XC F M D (G.erase g₀).card * rhoC F M)
    (hIHglt : |Cnt π (Glt G g₀) (AgOf (V := V) A π G hB.inj)
        - ∏ g ∈ Glt G g₀, pgOf A π g|
        ≤ ThetaC F M (D - 1) (Glt G g₀).card * (∏ g ∈ Glt G g₀, pgOf A π g)
          + XC F M (D - 1) (Glt G g₀).card * rhoC F M)
    (hIHdbl : |Cnt (dblπ π g₀) (dblG G g₀ D) (AgDbl (V := V) A π G g₀ D hB.inj)
        - ∏ g ∈ dblG G g₀ D, pgOf A (dblπ π g₀) g|
        ≤ ThetaC F M (D - 1) (dblG G g₀ D).card * (∏ g ∈ dblG G g₀ D, pgOf A (dblπ π g₀) g)
          + XC F M (D - 1) (dblG G g₀ D).card * rhoC F M) :
    |Cnt π G (AgOf (V := V) A π G hB.inj) - ∏ g ∈ G, pgOf A π g|
      ≤ ThetaC F M D G.card * (∏ g ∈ G, pgOf A π g) + XC F M D G.card * rhoC F M := by
  classical
  have hFpos : ∀ n, 1 ≤ F n := fun n => le_trans (by omega) (hFgrow n)
  have hLuppos : (0 : ℝ) < LupC F M := LupC_pos hFpos
  set m : ℕ := G.card with hm
  have hm1 : 1 ≤ m := by rw [hm]; exact Finset.card_pos.mpr ⟨g₀, hg₀⟩
  have hcard_img : ∀ g ∈ G, (g.image π).card = g.card := fun g hg =>
    Finset.card_image_of_injOn (fun a ha b hb hab => hB.inj g hg a ha b hb hab)
  have hg₀img : (g₀.image π).card = D := by rw [hcard_img g₀ hg₀, hg₀card]
  have hHallg : ∀ g ∈ G, g.image π ∈ Hall Hd := fun g hg => hB.img g hg
  have hHallcard_le : ∀ g ∈ G, (g.image π).card ≤ d := by
    intro g hg
    obtain ⟨e, he, hsub⟩ := mem_Hall.mp (hHallg g hg)
    exact le_trans (Finset.card_le_card hsub) (le_of_eq (hHd e he))
  have hLam1 : 1 ≤ LamC F M D := by
    have h := hlog (g₀.image π) (hHallg g₀ hg₀)
    rw [LamC]
    rwa [hg₀img] at h
  have hLampos : (0 : ℝ) < LamC F M D := lt_of_lt_of_le zero_lt_one hLam1
  have hLup1 : 1 ≤ LupC F M := le_trans (by norm_num) (LupC_ge_two hFpos)
  have hRg_eq : RgOf F M π g₀ = (F (M D) : ℝ) := by rw [RgOf, hg₀img]
  -- the ambient `GCHyp`
  have hGCHG : GCHyp (V := V) π G (AgOf (V := V) A π G hB.inj) (pgOf A π) (RgOf F M π)
      (bgOf (V := V) B B' A π G hB.inj) (cgOf (V := V) B' A π G hB.inj) (rhoC F M) :=
    gchyp_of_RegOK2 (V := V) hHd hBd hAtom hGood hR hF1 hB
      (fun g hg => hlog (g.image π) (hHallg g hg))
  have hpg0 : ∀ g ∈ G, 0 ≤ pgOf A π g := hGCHG.pg_nonneg
  have hpg1 : ∀ g ∈ G, pgOf A π g ≤ 1 := hGCHG.pg_le_one
  -- the product bound `∏_G p ≥ Lup^{-m}`
  have hP : (1 / LupC F M) ^ m ≤ ∏ g ∈ G, pgOf A π g := by
    have h1 : ∀ g ∈ G, (1 / LupC F M) ≤ pgOf A π g := by
      intro g hg
      have h2 := hGCHG.h2 g hg
      have h3 : Real.log (RgOf F M π g) ≤ LupC F M := by
        have hlog_le : Real.log (RgOf F M π g) ≤ Real.log (F (M 0) : ℝ) := by
          rw [RgOf]
          have hMle : M (g.image π).card ≤ M 0 :=
            hR.M_anti hFgrow 0 (g.image π).card (Nat.zero_le _) (hHallcard_le g hg)
          have hFle : F (M (g.image π).card) ≤ F (M 0) := hFmono hMle
          have h4 : (0 : ℝ) < (F (M (g.image π).card) : ℝ) := by
            have := hFgrow (M (g.image π).card)
            exact_mod_cast (by omega : 0 < F (M (g.image π).card))
          exact Real.log_le_log h4 (by exact_mod_cast hFle)
        rw [LupC]; linarith
      have h5 : 0 < Real.log (RgOf F M π g) :=
        lt_of_lt_of_le zero_lt_one (hlog (g.image π) (hHallg g hg))
      exact le_trans (one_div_le_one_div_of_le h5 h3) h2
    calc (1 / LupC F M) ^ m = ∏ g ∈ G, (1 / LupC F M) := by
          rw [Finset.prod_const, hm]
      _ ≤ ∏ g ∈ G, pgOf A π g :=
          Finset.prod_le_prod (fun g _ => by positivity) (fun g hg => h1 g hg)
  -- the product bound `PGlt * PGgt ≤ Λ^m P`
  have hprod : (∏ g ∈ Glt G g₀, pgOf A π g) * (∏ g ∈ Ggt G g₀ D, pgOf A π g)
      ≤ (LamC F M D) ^ m * (∏ g ∈ G, pgOf A π g) := by
    have hpt := prod_Glt_Ggt_Top (f := pgOf A π) hg₀ hg₀card hD hord
    have hTop1 : ∀ g ∈ Top G D, (1 / LamC F M D) ≤ pgOf A π g := by
      intro g hg
      obtain ⟨hgG, hgD⟩ := mem_Top.mp hg
      have h2 := hGCHG.h2 g hgG
      have h3 : Real.log (RgOf F M π g) = LamC F M D := by
        rw [RgOf, LamC, hcard_img g hgG, hgD]
      rwa [h3] at h2
    have hTopge : (1 / LamC F M D) ^ (Top G D).card ≤ ∏ g ∈ Top G D, pgOf A π g := by
      calc (1 / LamC F M D) ^ (Top G D).card = ∏ g ∈ Top G D, (1 / LamC F M D) := by
            rw [Finset.prod_const]
        _ ≤ ∏ g ∈ Top G D, pgOf A π g :=
            Finset.prod_le_prod (fun g _ => by positivity) (fun g hg => hTop1 g hg)
    have hone : (1 : ℝ) ≤ (LamC F M D) ^ (Top G D).card * (∏ g ∈ Top G D, pgOf A π g) := by
      have hpow : (LamC F M D) ^ (Top G D).card
          * (1 / LamC F M D) ^ (Top G D).card = 1 := by
        rw [← mul_pow, mul_one_div, div_self (ne_of_gt hLampos), one_pow]
      calc (1 : ℝ) = (LamC F M D) ^ (Top G D).card
            * (1 / LamC F M D) ^ (Top G D).card := hpow.symm
        _ ≤ (LamC F M D) ^ (Top G D).card * (∏ g ∈ Top G D, pgOf A π g) :=
            mul_le_mul_of_nonneg_left hTopge (by positivity)
    have hrm : (Top G D).card ≤ m := by
      rw [hm]; exact Finset.card_le_card (Finset.filter_subset _ _)
    have hpowle : (LamC F M D) ^ (Top G D).card ≤ (LamC F M D) ^ m :=
      pow_le_pow_right₀ hLam1 hrm
    have hPG0 : 0 ≤ (∏ g ∈ Glt G g₀, pgOf A π g) * (∏ g ∈ Ggt G g₀ D, pgOf A π g) :=
      mul_nonneg (Finset.prod_nonneg (fun g hg => hpg0 g (mem_Glt.mp hg).1))
        (Finset.prod_nonneg (fun g hg => hpg0 g (mem_Ggt.mp hg).1))
    calc (∏ g ∈ Glt G g₀, pgOf A π g) * (∏ g ∈ Ggt G g₀ D, pgOf A π g)
        = (∏ g ∈ Glt G g₀, pgOf A π g) * (∏ g ∈ Ggt G g₀ D, pgOf A π g) * 1 := by ring
      _ ≤ (∏ g ∈ Glt G g₀, pgOf A π g) * (∏ g ∈ Ggt G g₀ D, pgOf A π g)
            * ((LamC F M D) ^ (Top G D).card * (∏ g ∈ Top G D, pgOf A π g)) :=
          mul_le_mul_of_nonneg_left hone hPG0
      _ = (LamC F M D) ^ (Top G D).card * (∏ g ∈ G, pgOf A π g) := by
          rw [← hpt]; ring
      _ ≤ (LamC F M D) ^ m * (∏ g ∈ G, pgOf A π g) :=
          mul_le_mul_of_nonneg_right hpowle (Finset.prod_nonneg (fun g hg => hpg0 g hg))
  -- the `b`-term
  have hGltsub : Glt G g₀ ⊆ G := fun _ hg => (mem_Glt.mp hg).1
  have hcGl : (Glt G g₀).card ≤ m := by rw [hm]; exact Finset.card_le_card hGltsub
  have hcDb : (dblG G g₀ D).card ≤ 2 * m := by
    rw [hm]; exact dblG_card_le_two G g₀ D
  have hη₁m : ThetaC F M (D - 1) (Glt G g₀).card ≤ ThetaC F M (D - 1) m :=
    ThetaC_mono_m hFpos hcGl
  have hη₂m : ThetaC F M (D - 1) (dblG G g₀ D).card ≤ ThetaC F M (D - 1) (2 * m) :=
    ThetaC_mono_m hFpos hcDb
  have hC₁m : XC F M (D - 1) (Glt G g₀).card ≤ XC F M (D - 1) m := XC_mono_m hcGl
  have hC₂m : XC F M (D - 1) (dblG G g₀ D).card ≤ XC F M (D - 1) (2 * m) := XC_mono_m hcDb
  have hpow0 : (0 : ℝ) ≤ (LamC F M D) ^ m := pow_nonneg (le_of_lt hLampos) m
  have hkey1 : Real.sqrt (1 + ThetaC F M (D - 1) (Glt G g₀).card)
        * Real.sqrt (1 + ThetaC F M (D - 1) (dblG G g₀ D).card) * (LamC F M D) ^ m
      ≤ (etaBC F M D m (ThetaC F M (D - 1)) (XC F M (D - 1)) / 2)
          * Real.sqrt (RgOf F M π g₀) := by
    rw [hRg_eq, etaBC_half hFpos]
    have h2 : Real.sqrt (1 + ThetaC F M (D - 1) (Glt G g₀).card)
          * Real.sqrt (1 + ThetaC F M (D - 1) (dblG G g₀ D).card) * (LamC F M D) ^ m
        ≤ Real.sqrt (1 + ThetaC F M (D - 1) m) * Real.sqrt (1 + ThetaC F M (D - 1) (2 * m))
          * (LamC F M D) ^ m :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_le_sqrt (by linarith))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hpow0
    have h3 : (0 : ℝ) ≤ Real.sqrt (rhoC F M)
        * (Real.sqrt (1 + ThetaC F M (D - 1) m) * Real.sqrt (XC F M (D - 1) (2 * m))
          + Real.sqrt (1 + ThetaC F M (D - 1) (2 * m)) * Real.sqrt (XC F M (D - 1) m))
        * (LupC F M) ^ m := by positivity
    linarith
  have hkey3 : Real.sqrt (XC F M (D - 1) (Glt G g₀).card * XC F M (D - 1) (dblG G g₀ D).card)
      ≤ (CBc F M D m (XC F M (D - 1)) / 2) * Real.sqrt (RgOf F M π g₀) := by
    rw [hRg_eq, CBc_half hFpos]
    exact Real.sqrt_le_sqrt
      (mul_le_mul (XC_mono_m hcGl) (XC_mono_m hcDb) (XC_nonneg _ _) (XC_nonneg _ _))
  have hkey2 : Real.sqrt (rhoC F M) * (Real.sqrt (1 + ThetaC F M (D - 1) (Glt G g₀).card)
          * Real.sqrt (XC F M (D - 1) (dblG G g₀ D).card)
        + Real.sqrt (1 + ThetaC F M (D - 1) (dblG G g₀ D).card)
          * Real.sqrt (XC F M (D - 1) (Glt G g₀).card))
      ≤ (etaBC F M D m (ThetaC F M (D - 1)) (XC F M (D - 1)) / 2)
          * Real.sqrt (RgOf F M π g₀) * (1 / LupC F M) ^ m := by
    have hBmul : ∀ (y : ℝ), y * (LupC F M) ^ m * (1 / LupC F M) ^ m = y := by
      intro y
      rw [mul_assoc, one_div, inv_pow,
        mul_inv_cancel₀ (pow_ne_zero m (ne_of_gt hLuppos)), mul_one]
    have hS : Real.sqrt (1 + ThetaC F M (D - 1) (Glt G g₀).card)
          * Real.sqrt (XC F M (D - 1) (dblG G g₀ D).card)
        + Real.sqrt (1 + ThetaC F M (D - 1) (dblG G g₀ D).card)
          * Real.sqrt (XC F M (D - 1) (Glt G g₀).card)
        ≤ Real.sqrt (1 + ThetaC F M (D - 1) m) * Real.sqrt (XC F M (D - 1) (2 * m))
          + Real.sqrt (1 + ThetaC F M (D - 1) (2 * m)) * Real.sqrt (XC F M (D - 1) m) :=
      add_le_add
        (mul_le_mul (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_le_sqrt (XC_mono_m hcDb))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (mul_le_mul (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_le_sqrt (XC_mono_m hcGl))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    rw [hRg_eq, etaBC_half hFpos, add_mul, hBmul]
    have h0 : (0 : ℝ) ≤ Real.sqrt (1 + ThetaC F M (D - 1) m)
        * Real.sqrt (1 + ThetaC F M (D - 1) (2 * m)) * (LamC F M D) ^ m
        * (1 / LupC F M) ^ m := by positivity
    linarith [mul_le_mul_of_nonneg_left hS (Real.sqrt_nonneg (rhoC F M))]
  -- assemble the `b`-term bound
  have hbterm := bterm_bound (V := V) (Hd := Hd) (A := A) (B := B) (B' := B')
      (κ := κ) (π := π) (G := G) (g₀ := g₀)
      hB hg₀ D hD hg₀card hGCHG
      (η₁ := ThetaC F M (D - 1) (Glt G g₀).card) (η₂ := ThetaC F M (D - 1) (dblG G g₀ D).card)
      (C₁ := XC F M (D - 1) (Glt G g₀).card) (C₂ := XC F M (D - 1) (dblG G g₀ D).card)
      (KK := (LamC F M D) ^ m) (L₂ := LupC F M)
      (ηB := etaBC F M D m (ThetaC F M (D - 1)) (XC F M (D - 1)))
      (CB := CBc F M D m (XC F M (D - 1))) (N := m)
      (ThetaC_nonneg hFpos _ _) (ThetaC_nonneg hFpos _ _)
      (XC_nonneg _ _) (XC_nonneg _ _) (rhoC_nonneg hFpos) hpow0 hLup1
      (by rw [RgOf, hg₀img]; exact_mod_cast hFpos (M D))
      (etaBC_nonneg hFpos D m _ _) hpg0 hpg1
      (by
        have h := le_trans (le_abs_self (Cnt π (Glt G g₀) (AgOf (V := V) A π G hB.inj)
          - ∏ g ∈ Glt G g₀, pgOf A π g)) hIHglt
        have he : (1 + ThetaC F M (D - 1) (Glt G g₀).card) * (∏ g ∈ Glt G g₀, pgOf A π g)
            = (∏ g ∈ Glt G g₀, pgOf A π g)
              + ThetaC F M (D - 1) (Glt G g₀).card * (∏ g ∈ Glt G g₀, pgOf A π g) := by ring
        rw [he]
        linarith)
      (by
        have h := le_trans (le_abs_self (Cnt (dblπ π g₀) (dblG G g₀ D)
          (AgDbl (V := V) A π G g₀ D hB.inj)
            - ∏ g ∈ dblG G g₀ D, pgOf A (dblπ π g₀) g)) hIHdbl
        rw [prod_dblG_pg (V := V) (A := A) π G hg₀card hD] at h
        have he : (1 + ThetaC F M (D - 1) (dblG G g₀ D).card)
              * ((∏ h ∈ Glt G g₀, pgOf A π h) * (∏ h ∈ Ggt G g₀ D, pgOf A π h) ^ 2)
            = ((∏ h ∈ Glt G g₀, pgOf A π h) * (∏ h ∈ Ggt G g₀ D, pgOf A π h) ^ 2)
              + ThetaC F M (D - 1) (dblG G g₀ D).card
                * ((∏ h ∈ Glt G g₀, pgOf A π h) * (∏ h ∈ Ggt G g₀ D, pgOf A π h) ^ 2) := by ring
        rw [he]
        linarith)
      hprod hP hkey1 hkey2 hkey3
  -- the `c`-term bound
  have hcterm : |avg (fun v : BPt V π => cgOf (V := V) B' A π G hB.inj g₀ v
      * ∏ g ∈ G.erase g₀, indicator (AgOf (V := V) A π G hB.inj g) v)| ≤ rhoC F M := by
    have h := hGCHG.h4 g₀ hg₀ G hg₀ (fun g' hg' => by rw [hg₀card]; exact hord g' hg')
    rwa [Finset.filter_ne'] at h
  -- the split, the bookkeeping and the arithmetic
  have hparts := gencount_of_parts (V := V) π G (AgOf (V := V) A π G hB.inj) (pgOf A π)
      g₀ hg₀ hB.closed (bgOf (V := V) B B' A π G hB.inj g₀) (cgOf (V := V) B' A π G hB.inj g₀)
      (fun v hv => hGCHG.h1 g₀ hg₀ v hv)
      (ThetaC F M D (G.erase g₀).card) (etaBC F M D m (ThetaC F M (D - 1)) (XC F M (D - 1)))
      (XC F M D (G.erase g₀).card) (CBc F M D m (XC F M (D - 1)))
      (ThetaC_nonneg hFpos _ _) (etaBC_nonneg hFpos _ _ _ _) hpg0 hpg1
      (XC_nonneg _ _) (CBc_nonneg _ _ _) (rhoC F M) (rhoC_nonneg hFpos) hIHerase
      (by
        have h := hbterm
        rw [← Finset.prod_erase_mul G (fun g => pgOf A π g) hg₀] at h
        have h2 : pgOf A π g₀ * (∏ g ∈ G.erase g₀, pgOf A π g)
            = (∏ g ∈ G.erase g₀, pgOf A π g) * pgOf A π g₀ := mul_comm _ _
        rw [h2]
        exact h)
      hcterm
  -- final constants
  have herasecard : (G.erase g₀).card = m - 1 := by
    rw [hm, Finset.card_erase_of_mem hg₀]
  have hstepT : ThetaC F M D (m - 1) + etaBC F M D m (ThetaC F M (D - 1)) (XC F M (D - 1))
      ≤ ThetaC F M D m := by
    have hD' : (D - 1).succ = D := by omega
    have h := ThetaC_step' (M := M) hFpos (D - 1) hm1
    rwa [hD'] at h
  have hstepX : XC F M D (m - 1) + CBc F M D m (XC F M (D - 1)) + 1 ≤ XC F M D m := by
    have hD' : (D - 1).succ = D := by omega
    have h := XC_step' (F := F) (M := M) (D - 1) hm1
    rwa [hD'] at h
  have hηtot : ThetaC F M D (G.erase g₀).card + etaBC F M D m (ThetaC F M (D - 1)) (XC F M (D - 1))
      ≤ ThetaC F M D m := by rw [herasecard]; exact hstepT
  have hCtot : XC F M D (G.erase g₀).card + CBc F M D m (XC F M (D - 1)) + 1 ≤ XC F M D m := by
    rw [herasecard]; exact hstepX
  have hP0 : (0 : ℝ) ≤ ∏ g ∈ G, pgOf A π g := Finset.prod_nonneg (fun g hg => hpg0 g hg)
  calc |Cnt π G (AgOf (V := V) A π G hB.inj) - ∏ g ∈ G, pgOf A π g|
      ≤ (ThetaC F M D (G.erase g₀).card + etaBC F M D m (ThetaC F M (D - 1)) (XC F M (D - 1)))
          * (∏ g ∈ G, pgOf A π g)
        + (XC F M D (G.erase g₀).card + CBc F M D m (XC F M (D - 1)) + 1) * rhoC F M := hparts
    _ ≤ ThetaC F M D m * (∏ g ∈ G, pgOf A π g) + XC F M D m * rhoC F M := by
        exact add_le_add (mul_le_mul_of_nonneg_right hηtot hP0)
          (mul_le_mul_of_nonneg_right hCtot (rhoC_nonneg hFpos))

theorem isBundle_erase {Hd : Finset (Finset ι)} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {π : κ → ι} {G : Finset (Finset κ)} {g₀ : Finset κ} {D : ℕ}
    (hB : IsBundle Hd π G) (hord : ∀ g ∈ G, g.card ≤ D) (hg₀card : g₀.card = D) :
    IsBundle Hd π (G.erase g₀) where
  closed := fun g hg g' hg' => by
    rw [Finset.mem_erase] at hg ⊢
    refine ⟨?_, hB.closed g hg.2 g' hg'⟩
    intro hge
    have hlt : g₀.card < g.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hge ▸ hg', Ne.symm hg.1⟩)
    have := hord g hg.2
    omega
  inj := fun g hg => hB.inj g (Finset.mem_of_mem_erase hg)
  img := fun g hg => hB.img g (Finset.mem_of_mem_erase hg)

/-- `liftSet` does not depend on the injectivity proof. -/
theorem liftSet_hinj_congr {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι}
    {g : Finset κ} {hinj₁ hinj₂ : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b}
    {A : Finset (Pt V)} :
    liftSet (V := V) π g hinj₁ A = liftSet (V := V) π g hinj₂ A := by
  rw [Subsingleton.elim hinj₁ hinj₂]

/-- `AgOf` is independent of the bundle presentation. -/
theorem AgOf_eq {κ : Type*} [Fintype κ] [DecidableEq κ] {A : Finset ι → Finset (Pt V)}
    {π : κ → ι} {G G' : Finset (Finset κ)}
    {hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b}
    {hinj' : ∀ h ∈ G', ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b}
    {g : Finset κ} (hg : g ∈ G) (hg' : g ∈ G') :
    AgOf (V := V) A π G hinj g = AgOf (V := V) A π G' hinj' g := by
  rw [AgOf_of_mem (V := V) A π G hinj hg, AgOf_of_mem (V := V) A π G' hinj' hg']

/-- `AgOf` on the doubled bundle is `AgDbl`. -/
theorem AgOf_dblG_eq {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Finset ι → Finset (Pt V)} {π : κ → ι} {G : Finset (Finset κ)}
    {g₀ : Finset κ} {d' : ℕ} {Hd : Finset (Finset ι)}
    (hB : IsBundle Hd π G) {gg : Finset (DblIdx g₀)} (hgg : gg ∈ dblG G g₀ d') :
    AgOf (V := V) A (dblπ π g₀) (dblG G g₀ d')
        (isBundle_dblG (g₀ := g₀) (D := d') hB).inj gg
      = AgDbl (V := V) A π G g₀ d' hB.inj gg := by
  rw [AgOf_of_mem (V := V) A (dblπ π g₀) (dblG G g₀ d') _ hgg,
    AgDbl_of_mem (V := V) A π G g₀ d' hB.inj hgg]

/-- `Cnt` only depends on the values of the family on `G`. -/
theorem Cnt_congr {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι}
    {G : Finset (Finset κ)} {Ag Ag' : Finset κ → Finset (BPt V π)}
    (h : ∀ g ∈ G, Ag g = Ag' g) : Cnt π G Ag = Cnt π G Ag' := by
  simp only [Cnt]
  congr 1
  funext v
  exact Finset.prod_congr rfl (fun g hg => by rw [h g hg])

/-- **The generalized counting lemma** (Tao, `gencount`), inductive statement. -/
theorem gencount_aux
    {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)} {Md : ℕ}
    {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    {A : Finset ι → Finset (Pt V)}
    (hHd : ∀ e ∈ Hd, e.card = d)
    (hBd : ∀ e ∈ Hd, (Bd e).Refines (coord (V := V) e))
    (hAtom : ∀ f ∈ Hall Hd, A f ∈ (algOf (V := V) d Bd B f).atoms)
    (hGood : ∀ e ∈ Hall Hd, GoodAt (V := V) d Bd B B' M F A e.card e)
    (hR : RegOK2 (V := V) d Hd Bd Md F B B' M)
    (hF1 : 1 ≤ F (M 0)) (hFmono : Monotone F) (hFgrow : ∀ n, n + 1 ≤ F n)
    (hlog : ∀ e ∈ Hall Hd, 1 ≤ Real.log ((F (M e.card) : ℕ) : ℝ))
    (hempty : A ∅ = Finset.univ) :
    ∀ (D m : ℕ) {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (G : Finset (Finset κ))
      (hB : IsBundle Hd π G), (∀ g ∈ G, g.card ≤ D) → G.card ≤ m →
      |Cnt π G (AgOf (V := V) A π G hB.inj) - ∏ g ∈ G, pgOf A π g|
        ≤ ThetaC F M D G.card * (∏ g ∈ G, pgOf A π g) + XC F M D G.card * rhoC F M := by
  have hFpos : ∀ n, 1 ≤ F n := fun n => le_trans (by omega) (hFgrow n)
  have hrho : 0 ≤ rhoC F M := rhoC_nonneg hFpos
  intro D
  induction D with
  | zero =>
    intro m κ _ _ π G hB hord _
    have hsub : ∀ g ∈ G, g = ∅ := fun g hg =>
      Finset.card_eq_zero.mp (by have := hord g hg; omega)
    have hbdry : bdrySet A (∅ : Finset ι) = Finset.univ := by
      ext x
      rw [mem_bdrySet]
      constructor
      · intro _; exact Finset.mem_univ _
      · intro _ f hf
        have h := (mem_del.mp hf).2
        rw [Finset.card_empty] at h
        omega
    have hp : pOf A (∅ : Finset ι) = 1 := by
      rw [pOf, hbdry, Finset.univ_inter, hempty]
      rw [dif_neg (by rw [Finset.card_univ]; exact Fintype.card_ne_zero)]
      rw [div_self]
      rw [Finset.card_univ]
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Pt V) ≠ 0)
    have key : Cnt π G (AgOf (V := V) A π G hB.inj) = ∏ g ∈ G, pgOf A π g := by
      by_cases hnil : (∅ : Finset κ) ∈ G
      · have hGeq : G = {∅} := by
          refine Finset.Subset.antisymm (fun g hg => ?_) (fun g hg => ?_)
          · rw [Finset.mem_singleton]; exact hsub g hg
          · rw [Finset.mem_singleton] at hg; rw [hg]; exact hnil
        subst hGeq
        have hAg : AgOf (V := V) A π {∅} (hB.inj) ∅ = Finset.univ := by
          rw [AgOf_of_mem (V := V) A π {∅} (hB.inj) (Finset.mem_singleton_self ∅)]
          rw [show (∅ : Finset κ).image π = ∅ from Finset.image_empty π, hempty]
          ext v
          rw [mem_liftSet_iff]
          exact ⟨fun _ => Finset.mem_univ _,
            fun _ => ⟨Classical.arbitrary (Pt V), Finset.mem_univ _, fun k hk => absurd hk (by simp)⟩⟩
        rw [Cnt]
        simp only [Finset.prod_singleton]
        rw [hAg]
        rw [show (fun v : BPt V π => indicator (Finset.univ : Finset (BPt V π)) v)
              = fun _ => (1 : ℝ) from
          funext (fun v => by rw [indicator, if_pos (Finset.mem_univ _)]), avg_const]
        rw [pgOf, Finset.image_empty]
        exact hp.symm
      · have hGeq : G = ∅ := not_nonempty_iff_eq_empty.mp
          (fun hn => hn.elim (fun g hg => hnil (by rw [← hsub g hg]; exact hg)))
        subst hGeq
        rw [Cnt]
        simp only [Finset.prod_empty]
        rw [avg_const]
    rw [key, sub_self, abs_zero]
    simp only [ThetaC_zero, XC_zero]
    simpa using hrho
  | succ D ihD =>
    intro m
    induction m using Nat.strong_induction_on with
    | h m IHm =>
      intro κ _ _ π G hB hord hcard
      rcases Finset.eq_empty_or_nonempty G with hG | ⟨g₀, hg₀⟩
      · subst hG
        rw [Cnt]
        simp only [Finset.prod_empty]
        rw [avg_const, sub_self, abs_zero]
        simp only [Finset.card_empty, mul_one, zero_mul]
        have h1 : 0 ≤ ThetaC F M (D + 1) 0 := ThetaC_nonneg hFpos _ _
        have h2 : 0 ≤ XC F M (D + 1) 0 * rhoC F M := mul_nonneg (XC_nonneg _ _) hrho
        linarith
      · by_cases htop : ∃ g ∈ G, g.card = D + 1
        · obtain ⟨g₀, hg₀, hg₀card⟩ := htop
          have herase_lt : (G.erase g₀).card < m := by
            have := Finset.card_erase_lt_of_mem hg₀; omega
          have hord_erase : ∀ g ∈ G.erase g₀, g.card ≤ D + 1 :=
            fun g hg => hord g (Finset.mem_of_mem_erase hg)
          have hord_glt : ∀ g ∈ Glt G g₀, g.card ≤ D := by
            intro g hg
            have h := Finset.card_lt_card (mem_Glt.mp hg).2
            omega
          have hord_dbl : ∀ g ∈ dblG G g₀ (D + 1), g.card ≤ D := by
            intro g hg
            have := dblG_card_le hg₀card hg
            omega
          have hIHerase : |Cnt π (G.erase g₀) (AgOf (V := V) A π G hB.inj)
                - ∏ g ∈ G.erase g₀, pgOf A π g|
              ≤ ThetaC F M (D + 1) (G.erase g₀).card * (∏ g ∈ G.erase g₀, pgOf A π g)
                + XC F M (D + 1) (G.erase g₀).card * rhoC F M := by
            have h := IHm (G.erase g₀).card herase_lt π (G.erase g₀)
              (isBundle_erase hB hord hg₀card) hord_erase le_rfl
            rwa [Cnt_congr (fun g hg =>
              AgOf_eq (V := V) (A := A) (G := G.erase g₀) (G' := G) hg
                (Finset.mem_of_mem_erase hg))] at h
          have hIHglt : |Cnt π (Glt G g₀) (AgOf (V := V) A π G hB.inj)
                - ∏ g ∈ Glt G g₀, pgOf A π g|
              ≤ ThetaC F M D (Glt G g₀).card * (∏ g ∈ Glt G g₀, pgOf A π g)
                + XC F M D (Glt G g₀).card * rhoC F M := by
            have h := ihD (Glt G g₀).card π (Glt G g₀) (isBundle_Glt hB) hord_glt le_rfl
            rwa [Cnt_congr (fun g hg =>
              AgOf_eq (V := V) (A := A) (G := Glt G g₀) (G' := G) hg (mem_Glt.mp hg).1)] at h
          have hIHdbl : |Cnt (dblπ π g₀) (dblG G g₀ (D + 1)) (AgDbl (V := V) A π G g₀ (D + 1) hB.inj)
                - ∏ g ∈ dblG G g₀ (D + 1), pgOf A (dblπ π g₀) g|
              ≤ ThetaC F M D (dblG G g₀ (D + 1)).card
                  * (∏ g ∈ dblG G g₀ (D + 1), pgOf A (dblπ π g₀) g)
                + XC F M D (dblG G g₀ (D + 1)).card * rhoC F M := by
            have h := ihD (dblG G g₀ (D + 1)).card (dblπ π g₀) (dblG G g₀ (D + 1))
              (isBundle_dblG (g₀ := g₀) (D := D + 1) hB) hord_dbl le_rfl
            rwa [Cnt_congr (fun gg hgg => AgOf_dblG_eq (V := V) (A := A) (d' := D + 1) hB hgg)] at h
          exact gencount_step (V := V) hHd hBd hAtom hGood hR hF1 hFmono hFgrow hlog hB hg₀
            (by omega) hg₀card hord hIHerase hIHglt hIHdbl
        · push_neg at htop
          have hord' : ∀ g ∈ G, g.card ≤ D := fun g hg => by
            have h1 := hord g hg
            have h2 := htop g hg
            omega
          have hres := ihD m π G hB hord' hcard
          have hT : ThetaC F M D G.card ≤ ThetaC F M (D + 1) G.card :=
            ThetaC_succ_ge hFpos D G.card
          have hX : XC F M D G.card ≤ XC F M (D + 1) G.card := XC_succ_ge D G.card
          have hP0 : (0 : ℝ) ≤ ∏ g ∈ G, pgOf A π g :=
            Finset.prod_nonneg (fun g hg => pOf_nonneg A (g.image π))
          exact le_trans hres (add_le_add (mul_le_mul_of_nonneg_right hT hP0)
            (mul_le_mul_of_nonneg_right hX hrho))

/-- **The generalized counting lemma** (Tao, `gencount`), final form. -/
theorem gencount
    {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)} {Md : ℕ}
    {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    {A : Finset ι → Finset (Pt V)}
    (hHd : ∀ e ∈ Hd, e.card = d)
    (hBd : ∀ e ∈ Hd, (Bd e).Refines (coord (V := V) e))
    (hAtom : ∀ f ∈ Hall Hd, A f ∈ (algOf (V := V) d Bd B f).atoms)
    (hGood : ∀ e ∈ Hall Hd, GoodAt (V := V) d Bd B B' M F A e.card e)
    (hR : RegOK2 (V := V) d Hd Bd Md F B B' M)
    (hF1 : 1 ≤ F (M 0)) (hFmono : Monotone F) (hFgrow : ∀ n, n + 1 ≤ F n)
    (hlog : ∀ e ∈ Hall Hd, 1 ≤ Real.log ((F (M e.card) : ℕ) : ℝ))
    (hempty : A ∅ = Finset.univ)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (G : Finset (Finset κ))
    (hB : IsBundle Hd π G) (hord : ∀ g ∈ G, g.card ≤ d) :
    |Cnt π G (AgOf (V := V) A π G hB.inj) - ∏ g ∈ G, pgOf A π g|
      ≤ ThetaC F M d G.card * (∏ g ∈ G, pgOf A π g) + XC F M d G.card * rhoC F M :=
  gencount_aux hHd hBd hAtom hGood hR hF1 hFmono hFgrow hlog hempty d G.card π G hB hord le_rfl

end Szemeredi.Removal
