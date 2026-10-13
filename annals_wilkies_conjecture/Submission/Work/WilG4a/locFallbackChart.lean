import Mathlib
import Submission.Work.WilG4a.f1affine1_of_signConst
import Submission.Work.WilG4a.locGoodDefs
import Submission.Work.WilG4a.CD.slice_bad_finite
import Submission.Work.WilG4a.CD.badLocus_interior_eq_empty
import Submission.Work.WilG4a.sInf_sSup_fibre_graph_mem
import Submission.Work.WilG4a.lt_locus_graph_mem
import Submission.Work.WilG4a.ite_graph_mem
import Submission.Work.WilG4a.affine_cover_params
import Submission.Work.WilG4a.affine_reparam_bound
import Submission.Work.WilG4a.CD.inflated_mem
import Submission.Work.WilG4a.CD.fibDerivGraph_mem
import Submission.Work.WilG4a.cellDecomp_exists
import Submission.Work.WilG4a.goodCell_fibre_dichotomy
import Submission.Work.WilG4a.goodCell_chart_conditions
import Submission.Work.WilG4a.setOf_lt_graph_mem
import Submission.Work.WilG4a.affine_comb_graph_mem
import Submission.Work.WilG4a.Bounds
import Submission.Work.WilG4a.locFallbackAux.iUnion_fintype_mem
import Submission.Work.WilG4a.locFallbackAux.realPoly_le_natPoly
import Submission.Work.WilG4a.locFallbackAux.exists_nondegen_cell
import Submission.Work.WilG4a.locFallbackAux.firstLocus_unique

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilG4a

open WilkiesDesign
open Work.WilG4a.locFallbackAux

/-! ## A triviality used below

`GoodCell_w` already contains the strip condition `κ ⊆ strip p`, and `DegCell` is inherited by
subsets, so intersecting a cell with the strip changes nothing. -/
theorem cell_inter_strip {p k r : ℕ} {F : Fin k → (Fin p → ℝ) → ℝ → ℝ}
    {κ : Set (Fin (p + 1) → ℝ)} (h : GoodCell_w k r F κ ∨ DegCell κ) :
    GoodCell_w k r F (κ ∩ strip p) ∨ DegCell (κ ∩ strip p) := by
  rcases h with hg | hd
  · left
    rw [Set.inter_eq_left.mpr hg.1]
    exact hg
  · right
    intro l x hx y hy
    exact hd l (Set.mem_of_mem_inter_left hx) (Set.mem_of_mem_inter_left hy)

/-- **The global ("fallback") chart**

Given the sharp cell decomposition and sharp derivatives of `S`, plus the two one-dimensional
analytic inputs `hG3a`, `hG3b`, there are a format `a` and a degree polynomial `b` (depending
only on `p`, `F0`, `aΓ`, `bΓ`) such that for every family member `f` of format `F0` and degree
`D` whose slices map `I` into `I` on `Λ`, there is a *single* affine chart
`x = α l + β l · t` with `Ω`-definable coefficients of format `a` and degree `b.eval ![D,r]`,
which is valid (nondegenerate, inside `I`, and with all derivatives of the composites of order
`≤ r` bounded by `1`) at *every* `l ∈ Λ`.

The construction: decompose the strip over `Λ` (`cellDecomp_exists`, at order `r`) into cells
which are either good (fibres are points or intervals, with `C^{r+1}` slices and
constant-signed derivatives on them) or degenerate (subsingleton fibres).  For a cell `κ`, let
`lo`, `hi` be the infimum/supremum of its fibre.  The non-degeneracy locus `P_σ = {lo < hi}`
is `Ω`-definable (`setOf_lt_graph_mem`); let `P'_σ` be the "first" locus (`firstLocus`), whose
members are pairwise disjoint.  The set

  `H := ⋃_σ (κ'_σ ∩ {z | init z ∈ P'_σ})`

has fibre over `l` exactly the fibre of the *first* nondegenerate cell (`exists_nondegen_cell`
guarantees there is one, since a finite union of subsingletons cannot cover `I`).  Taking the
infimum/supremum of the fibre of `H` therefore produces a single good interval, and the affine
chart with the Whitney-cover parameter of `affine_cover_params` is valid there by
`goodCell_chart_conditions`. -/
theorem locFallbackChart (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (hG3a : ∀ (r : ℕ) (f : ℝ → ℝ), ContDiffOn ℝ (r + 1) f (Set.Ioo 0 1) → (∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ∈ Set.Ioo (0 : ℝ) 1) → (∀ j ≤ r + 1, (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨ (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0)) → ∀ M : ℝ, 1 < M → ∀ j ≤ r, ∀ x ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < x → x < 1 - j / M → |iteratedDerivWithin j f (Set.Ioo 0 1) x| < M ^ j) (hG3b : ∀ (r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ s : Finset (ℝ × ℝ), (s.card : ℝ) ≤ 8 * (r + 1) * (-Real.log ε + 2) ∧ (∀ p ∈ s, 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1 ∧ (p.2 - p.1) * (r + 1) ≤ min p.1 (1 - p.2)) ∧ (Set.Icc ε (1 - ε) ⊆ (⋃ p ∈ s, Set.Icc p.1 p.2))) (p F0 : ℕ) (aΓ : ℕ) (bΓ : MvPolynomial (Fin 2) ℕ) : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D r : ℕ) (Λ : Set (Fin p → ℝ)) (f : (Fin p → ℝ) → ℝ → ℝ), Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) → (∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, f l x ∈ Work.WilG4a.I) → Work.WilG4a.locGoodSet f r ∈ S.Ω aΓ (MvPolynomial.eval ![D, r] bΓ) (p + 1) → ∃ (α β : (Fin p → ℝ) → ℝ), Work.WilG4a.Chart1 S p a (MvPolynomial.eval ![D, r] b) Λ 1 r (fun _ : Fin 1 => f) α β := by
  classical
  -- =========================================================================
  -- 1. The uniform data, depending only on `p`, `F0` (and not on `D`, `r`).
  -- =========================================================================
  obtain ⟨a1, b1, cc1, h1⟩ := cellDecomp_exists S hcd hder p F0
  obtain ⟨aS, bS, hS⟩ := strip_mem_y S p
  obtain ⟨bm, hbm⟩ := Work.WilG4a.locFallbackAux.realPoly_le_natPoly cc1
  -- the fibre end points of the cells
  obtain ⟨aE, pE, pE', hE⟩ := sInf_sSup_fibre_graph_mem S p (max a1 aS + 1)
  -- the comparison of two `Ω`-graphs
  obtain ⟨aP, bP, hP⟩ := setOf_lt_graph_mem S p aE
  set bC : MvPolynomial (Fin 2) ℕ := b1 + bS with hbC
  set bLoh : MvPolynomial (Fin 2) ℕ := MvPolynomial.C pE * bC + MvPolynomial.C pE' with hbLoh
  obtain ⟨bPc, hbPc⟩ := exists_eval_comp bP bLoh
  -- `bU` bounds the degree of the union of the non-degeneracy loci, `bQ` that of the
  -- "first"' locus, and `bH` that of the selected set.
  set bU : MvPolynomial (Fin 2) ℕ := bm * bPc with hbU
  set bQ : MvPolynomial (Fin 2) ℕ := bPc + bU with hbQ
  set bH : MvPolynomial (Fin 2) ℕ := bm * (bC + bQ) with hbH
  -- the common format of the pieces of `H`, and the format of `H`
  set FM : ℕ := max (max a1 aS + 1) (aP + 3) with hFM
  set FH : ℕ := FM + 1 with hFH
  -- the fibre end points of `H`
  obtain ⟨aE2, pE2, pE2', hE2⟩ := sInf_sSup_fibre_graph_mem S p FH
  set bH2 : MvPolynomial (Fin 2) ℕ := MvPolynomial.C pE2 * bH + MvPolynomial.C pE2' with hbH2
  -- the affine combination of two `Ω`-graphs
  obtain ⟨aA, bA, hA⟩ := affine_comb_graph_mem S p aE2
  obtain ⟨bAc, hbAc⟩ := exists_eval_comp bA bH2
  refine ⟨aA, bAc, ?_⟩
  intro D r Λ f hfΩ hfI hloc
  -- =========================================================================
  -- 2. The cell decomposition of the strip over `Λ`, at order `r`.
  -- =========================================================================
  obtain ⟨m, hm, κ, hκΩ, hκdich, hκcov⟩ := h1 D r 1 Λ (fun _ : Fin 1 => f)
    (by intro i; simpa using hfΩ) (by intro i l' hl' x hx; simpa using hfI l' hl' x hx)
  have hm_nat : m ≤ bm.eval ![D, r] := by
    have hm' := hm
    simp only [Nat.cast_one] at hm'
    have h3 : (m : ℝ) ≤ (bm.eval ![D, r] : ℝ) := le_trans hm' (hbm D r)
    exact_mod_cast h3
  set κ' : Fin m → Set (Fin (p + 1) → ℝ) := fun σ => κ σ ∩ strip p with hκ'
  have hbC' : bC.eval ![D, r] = b1.eval ![D, r] + bS.eval ![D, r] := by
    rw [hbC, MvPolynomial.eval_add]
  have hκ'Ω : ∀ σ, κ' σ ∈ S.Ω (max a1 aS + 1) (bC.eval ![D, r]) (p + 1) := by
    intro σ
    have hA : κ σ ∈ S.Ω (max a1 aS) (b1.eval ![D, r]) (p + 1) :=
      Work.WilG0.Omega_mono_F (S := S) (le_max_left a1 aS) (hκΩ σ)
    have hB : strip p ∈ S.Ω (max a1 aS) (bS.eval ![D, r]) (p + 1) :=
      Work.WilG0.Omega_mono_F (S := S) (le_max_right a1 aS) (hS D r)
    have h := Work.WilG0.Omega_inter2 (S := S) hA hB
    rw [hbC']
    exact h
  have hκ'dich : ∀ σ, GoodCell_w 1 r (fun _ : Fin 1 => f) (κ' σ) ∨ DegCell (κ' σ) :=
    fun σ => cell_inter_strip (hκdich σ)
  have hκ'strip : ∀ σ, κ' σ ⊆ strip p := fun σ => Set.inter_subset_right
  have hκ'cov : ∀ l ∈ Λ, ∀ x ∈ I, ∃ σ, Fin.snoc l x ∈ κ' σ := by
    intro l hl x hx
    obtain ⟨σ, hσ⟩ := hκcov l hl x hx
    exact ⟨σ, hσ, (strip_mem_iff_snoc l x).mpr hx⟩
  -- =========================================================================
  -- 3. The fibre end points of the cells, and the "first nondegenerate cell" locus.
  -- =========================================================================
  set lo : Fin m → (Fin p → ℝ) → ℝ := fun σ l => sInf (fibre (κ' σ) l) with hlo
  set hi : Fin m → (Fin p → ℝ) → ℝ := fun σ l => sSup (fibre (κ' σ) l) with hhi
  have hsplit : ∀ σ, graphOf (lo σ) ∈ S.Ω aE (bLoh.eval ![D, r]) (p + 1) ∧
      graphOf (hi σ) ∈ S.Ω aE (bLoh.eval ![D, r]) (p + 1) := by
    intro σ
    have h := hE (bC.eval ![D, r]) (κ' σ) (hκ'Ω σ) (fun z hz => hκ'strip σ hz)
    have he : bLoh.eval ![D, r] = pE * bC.eval ![D, r] + pE' := by
      simp only [hbLoh, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
    constructor
    · rw [he]
      simpa [hlo, fibre] using h.1
    · rw [he]
      simpa [hhi, fibre] using h.2
  set Ploc : Fin m → Set (Fin p → ℝ) := fun σ => {l | lo σ l < hi σ l} with hPloc
  have hbPc' : ∀ D' r' : ℕ, bP.eval ![bLoh.eval ![D', r'], r'] = bPc.eval ![D', r'] := by
    intro D' r'
    rw [hbLoh, hbC]
    exact hbPc D' r'
  have hPloc_mem : ∀ σ, Ploc σ ∈ S.Ω aP (bPc.eval ![D, r]) p := by
    intro σ
    have h := hP (bLoh.eval ![D, r]) r (hsplit σ).1 (hsplit σ).2
    rw [← hbPc' D r]
    exact h
  have hU_mem : ∀ σ : Fin m, (⋃ τ : {τ : Fin m // τ < σ}, Ploc τ.val) ∈
      S.Ω aP (bU.eval ![D, r]) p := by
    intro σ
    have hunion := Work.WilG4a.locFallbackAux.iUnion_fintype_mem S
      (fun τ : {τ : Fin m // τ < σ} => Ploc τ.val) (fun τ => hPloc_mem τ.val)
    have hcard : Fintype.card {τ : Fin m // τ < σ} ≤ m := by
      simpa using Fintype.card_subtype_le (fun τ : Fin m => τ < σ)
    have hdeg : Fintype.card {τ : Fin m // τ < σ} * bPc.eval ![D, r] ≤ bU.eval ![D, r] := by
      have h1' : Fintype.card {τ : Fin m // τ < σ} * bPc.eval ![D, r] ≤
          m * bPc.eval ![D, r] := Nat.mul_le_mul_right _ hcard
      have h2' : m * bPc.eval ![D, r] ≤ bm.eval ![D, r] * bPc.eval ![D, r] :=
        Nat.mul_le_mul_right _ hm_nat
      have h3' : (bm * bPc).eval ![D, r] = bm.eval ![D, r] * bPc.eval ![D, r] := by
        rw [MvPolynomial.eval_mul]
      rw [hbU, h3']
      exact le_trans h1' h2'
    exact Work.WilG0.Omega_mono_D (S := S) hdeg hunion
  have hPloc'_mem : ∀ σ, firstLocus Ploc σ ∈ S.Ω (aP + 2) (bQ.eval ![D, r]) p := by
    intro σ
    have hA : Ploc σ ∈ S.Ω (aP + 1) (bPc.eval ![D, r]) p :=
      Work.WilG0.Omega_mono_F (S := S) (by omega : aP ≤ aP + 1) (hPloc_mem σ)
    have hB : (⋃ τ : {τ : Fin m // τ < σ}, Ploc τ.val)ᶜ ∈ S.Ω (aP + 1) (bU.eval ![D, r]) p :=
      S.compl (hU_mem σ)
    have hinter := Work.WilG0.Omega_inter2 (S := S) hA hB
    have hfmt : aP + 1 + 1 ≤ aP + 2 := by omega
    have hdd : bPc.eval ![D, r] + bU.eval ![D, r] ≤ bQ.eval ![D, r] := by
      rw [hbQ, MvPolynomial.eval_add]
    have hfin := Work.WilG0.Omega_mono_FD (S := S) hfmt hdd hinter
    simpa only [firstLocus] using hfin
  -- =========================================================================
  -- 4. The selected set `H`, whose fibre over `l` is the fibre of the first
  --    nondegenerate cell.
  -- =========================================================================
  set H : Set (Fin (p + 1) → ℝ) :=
    ⋃ σ : Fin m, (κ' σ ∩ {z : Fin (p + 1) → ℝ | Fin.init z ∈ firstLocus Ploc σ}) with hH
  have hHmem : H ∈ S.Ω FH (bH.eval ![D, r]) (p + 1) := by
    have hpiece : ∀ σ : Fin m, (κ' σ ∩ {z : Fin (p + 1) → ℝ | Fin.init z ∈ firstLocus Ploc σ}) ∈
        S.Ω FH (bC.eval ![D, r] + bQ.eval ![D, r]) (p + 1) := by
      intro σ
      have hA : κ' σ ∈ S.Ω FM (bC.eval ![D, r]) (p + 1) :=
        Work.WilG0.Omega_mono_F (S := S) (by rw [hFM]; omega) (hκ'Ω σ)
      have hpr : {z : Fin (p + 1) → ℝ | Fin.init z ∈ firstLocus Ploc σ} ∈
          S.Ω (aP + 3) (bQ.eval ![D, r]) (p + 1) := S.prod_right (hPloc'_mem σ)
      have hB : {z : Fin (p + 1) → ℝ | Fin.init z ∈ firstLocus Ploc σ} ∈
          S.Ω FM (bQ.eval ![D, r]) (p + 1) :=
        Work.WilG0.Omega_mono_F (S := S) (by rw [hFM]; omega) hpr
      have hinter := Work.WilG0.Omega_inter2 (S := S) hA hB
      rw [hFH]
      exact hinter
    have hunion := Work.WilG4a.locFallbackAux.iUnion_fintype_mem S
      (fun σ : Fin m => (κ' σ ∩ {z : Fin (p + 1) → ℝ | Fin.init z ∈ firstLocus Ploc σ})) hpiece
    rw [hH]
    refine Work.WilG0.Omega_mono_D (S := S) ?_ hunion
    have hdeg : Fintype.card (Fin m) * (bC.eval ![D, r] + bQ.eval ![D, r]) ≤ bH.eval ![D, r] := by
      have h2' : bH.eval ![D, r] = bm.eval ![D, r] * (bC.eval ![D, r] + bQ.eval ![D, r]) := by
        rw [hbH, MvPolynomial.eval_mul, MvPolynomial.eval_add]
      rw [Fintype.card_fin, h2']
      exact Nat.mul_le_mul_right _ hm_nat
    exact hdeg
  have hHstrip : H ⊆ strip p := by
    intro z hz
    rw [hH] at hz
    rcases Set.mem_iUnion.mp hz with ⟨σ, hzσ⟩
    exact hκ'strip σ (Set.mem_of_mem_inter_left hzσ)
  -- =========================================================================
  -- 5. The end points of the fibre of `H`, and the chart.
  -- =========================================================================
  set Lo : (Fin p → ℝ) → ℝ := fun l => sInf (fibre H l) with hLo
  set Hi : (Fin p → ℝ) → ℝ := fun l => sSup (fibre H l) with hHi
  have hE2app := hE2 (bH.eval ![D, r]) H hHmem hHstrip
  have hbH2' : bH2.eval ![D, r] = pE2 * bH.eval ![D, r] + pE2' := by
    simp only [hbH2, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  have hLoΩ : graphOf Lo ∈ S.Ω aE2 (bH2.eval ![D, r]) (p + 1) := by
    rw [hbH2']
    simpa [hLo, fibre] using hE2app.1
  have hHiΩ : graphOf Hi ∈ S.Ω aE2 (bH2.eval ![D, r]) (p + 1) := by
    rw [hbH2']
    simpa [hHi, fibre] using hE2app.2
  -- the Whitney-cover parameter
  obtain ⟨s, hsP, -, hscov⟩ :=
    affine_cover_params hG3b r (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 : ℝ) / 2 < 1 by norm_num)
  obtain ⟨q, hqmem, -⟩ := hscov (1 / 2) (by refine ⟨by norm_num, by norm_num⟩)
  have hq := hsP q hqmem
  -- the chart
  set α : (Fin p → ℝ) → ℝ := fun l => (0 : ℝ) + (1 - q.1) * Lo l + q.1 * Hi l with hα
  set β : (Fin p → ℝ) → ℝ := fun l => (0 : ℝ) + (-q.2) * Lo l + q.2 * Hi l with hβ
  have hαΩ : graphOf α ∈ S.Ω aA (bAc.eval ![D, r]) (p + 1) := by
    have h := hA (bH2.eval ![D, r]) r hLoΩ hHiΩ (0 : ℝ) (1 - q.1) q.1
    rw [hbAc D r] at h
    simpa only [hα] using h
  have hβΩ : graphOf β ∈ S.Ω aA (bAc.eval ![D, r]) (p + 1) := by
    have h := hA (bH2.eval ![D, r]) r hLoΩ hHiΩ (0 : ℝ) (-q.2) q.2
    rw [hbAc D r] at h
    simpa only [hβ] using h
  refine ⟨α, β, hαΩ, hβΩ, ?_⟩
  intro l hl
  -- =========================================================================
  -- 6. At a parameter `l ∈ Λ`: the fibre of `H` is the fibre of the first
  --    nondegenerate cell.
  -- =========================================================================
  obtain ⟨σ₀, hcell₀, a₀, b₀, hlt₀, hfib₀⟩ :=
    Work.WilG4a.locFallbackAux.exists_nondegen_cell κ' l hκ'dich (hκ'cov l hl)
  have hP₀ : l ∈ Ploc σ₀ := by
    rcases goodCell_fibre_dichotomy hcell₀ l with ⟨hsub, heq⟩ | ⟨hf, hlt, h0, h1⟩
    · exfalso
      rw [hfib₀] at hsub
      exact Set.Ioo_infinite hlt₀ hsub.finite
    · exact hlt
  obtain ⟨σs, hσsP, hσs_le, hσs_uniq⟩ :=
    Work.WilG4a.locFallbackAux.firstLocus_unique Ploc ⟨σ₀, hP₀⟩
  have hlt_s : lo σs l < hi σs l := hσsP
  have hσs_cell : GoodCell_w 1 r (fun _ : Fin 1 => f) (κ' σs) := by
    rcases hκ'dich σs with hg | hd
    · exact hg
    · exfalso
      have heq : lo σs l = hi σs l := subsingleton_sInf_eq_sSup (hd l)
      have hlt : lo σs l < hi σs l := hσsP
      exact absurd heq hlt.ne
  have hσs_dich : fibre (κ' σs) l = Set.Ioo (lo σs l) (hi σs l) ∧
      0 ≤ lo σs l ∧ hi σs l ≤ 1 := by
    rcases goodCell_fibre_dichotomy hσs_cell l with ⟨hsub, heq⟩ | ⟨hf, hlt, h0, h1⟩
    · exfalso
      have heq' : lo σs l = hi σs l := heq
      have hlt' : lo σs l < hi σs l := hσsP
      exact absurd heq' hlt'.ne
    · exact ⟨hf, h0, h1⟩
  have hHfib : fibre H l = fibre (κ' σs) l := by
    ext y
    constructor
    · intro hy
      rw [hH] at hy
      rcases Set.mem_iUnion.mp hy with ⟨σ, hσ1, hσ2⟩
      simp only [Set.mem_ofPred_eq, Fin.init_snoc] at hσ2
      have hσeq : σ = σs := hσs_uniq σ hσ2
      rw [hσeq] at hσ1
      exact hσ1
    · intro hy
      rw [hH]
      refine Set.mem_iUnion.mpr ⟨σs, hy, ?_⟩
      simp only [Set.mem_ofPred_eq, Fin.init_snoc]
      refine ⟨hσsP, ?_⟩
      rw [Set.mem_compl_iff, Set.mem_iUnion]
      rintro ⟨τ, hτ⟩
      exact absurd (hσs_le τ.val hτ) (not_le.mpr τ.property)
  have hLo_eq : Lo l = lo σs l := by
    simp only [hLo, hlo]
    rw [hHfib]
  have hHi_eq : Hi l = hi σs l := by
    simp only [hHi, hhi]
    rw [hHfib]
  -- =========================================================================
  -- 7. The chart conditions, from the chart of the good cell `κ' σs`.
  -- =========================================================================
  have hvalid := goodCell_chart_conditions (hG3a := hG3a)
    (F := fun _ : Fin 1 => f) (κ := κ' σs) (Λ := {l}) (lo := lo σs) (hi := hi σs)
    hσs_cell
    (by
      intro i l' hl' x hx
      rw [Set.mem_singleton_iff] at hl'
      rw [hl']
      simpa using hfI l hl x hx)
    (by
      intro l' hl'
      rw [Set.mem_singleton_iff] at hl'
      rw [hl']
      exact ⟨(lo σs l + hi σs l) / 2, by
        show (lo σs l + hi σs l) / 2 ∈ fibre (κ' σs) l
        rw [hσs_dich.1]
        exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩⟩)
    (by
      intro l' hl'
      rw [Set.mem_singleton_iff] at hl'
      rw [hl']
      exact hσs_dich.1)
    (a := q.1) (b := q.2) hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
  have hres := hvalid l rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `0 < β l`
    change 0 < (0 : ℝ) + (-q.2) * Lo l + q.2 * Hi l
    rw [hLo_eq, hHi_eq]
    linarith [hres.1]
  · -- `0 ≤ α l`
    change 0 ≤ (0 : ℝ) + (1 - q.1) * Lo l + q.1 * Hi l
    rw [hLo_eq, hHi_eq]
    linarith [hres.2.1]
  · -- `α l + β l ≤ 1`
    change (0 : ℝ) + (1 - q.1) * Lo l + q.1 * Hi l +
      ((0 : ℝ) + (-q.2) * Lo l + q.2 * Hi l) ≤ 1
    rw [hLo_eq, hHi_eq]
    linarith [hres.2.2.1]
  · -- smoothness and the derivative bounds along the chart
    intro i
    fin_cases i
    constructor
    · have h := (hres.2.2.2 (0 : Fin 1)).1
      change ContDiffOn ℝ r (fun t : ℝ => (fun _ : Fin 1 => f) 0 l (α l + β l * t)) I
      refine h.congr (fun t ht => ?_)
      have harg : lo σs l + (hi σs l - lo σs l) * q.1 + (hi σs l - lo σs l) * q.2 * t =
          α l + β l * t := by
        simp only [hα, hβ, hLo_eq, hHi_eq]
        ring
      simp only [harg]
    · intro m' hm' t ht
      have h := (hres.2.2.2 (0 : Fin 1)).2 m' hm' t ht
      change |iteratedDeriv m' (fun s : ℝ => (fun _ : Fin 1 => f) 0 l (α l + β l * s)) t| ≤ 1
      have hfun : (fun s : ℝ => (fun _ : Fin 1 => f) 0 l (α l + β l * s)) =
          (fun s : ℝ => (fun _ : Fin 1 => f) 0 l
            (lo σs l + (hi σs l - lo σs l) * q.1 + (hi σs l - lo σs l) * q.2 * s)) := by
        funext s
        have harg : α l + β l * s =
            lo σs l + (hi σs l - lo σs l) * q.1 + (hi σs l - lo σs l) * q.2 * s := by
          simp only [hα, hβ, hLo_eq, hHi_eq]
          ring
        simp only [harg]
      rw [hfun]
      exact h

end Work.WilG4a
