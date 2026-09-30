import Mathlib
import Submission.Work.SymQuot.DivOf.C1Defs
import Submission.Work.SymQuot.DivOf.genGenerator_map_eq
import Submission.Work.SymQuot.DivOf.secAlpha_sub_mem_placeIdeal
import Submission.Work.SymQuot.DivOf.ptPlace_mem_bcOpens
import Submission.Work.SymQuot.DivOf.lift_mem_V
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_prod_placeIdeal
import Submission.Work.SymQuot.DivOf.eq_of_le_of_forall_placeOrder_le
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_injective
import Submission.Work.SymQuot.DivOf.exists_eq_sum_secAlpha
import Submission.Work.SymQuot.DivOf.CharIdealGenMapDefs
import Submission.Work.SymQuot.DivOf.exists_mem_placeIdeal_notMem_sq
import Submission.Work.SymQuot.DivOf.coeff_prod_mem_prod_ideal
import Submission.Work.SymQuot.DivOf.placeOrder_mono
import Submission.Work.SymQuot.DivOf.placeOrder_span_eq_iff
import Submission.Work.SymQuot.DivOf.placeOrder_span_prod
import Submission.Work.SymQuot.DivOf.exists_crt_placeIdeal_sq_one
import Submission.Work.SymQuot.DivOf.prod_sub_mem_charIdealGen_map

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.DivOf

universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
namespace Work.SymQuot.DivOf
open Work.CurveBasics

theorem charIdealGen_map_eq {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) {F'' : Type u} [Field F''] [Algebra K F'']
    [Algebra F F''] [IsScalarTower K F F''] (x : Fin n → Work.SpecLin.CurveFPt C F'')
    (hx : Work.SymQuot.Sym.powMap C n x =
      Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F'') p) :
    (charIdealGen F d).map (bcSec (C := C) F F'' d.V) =
      prodPtPlaceIdeal d x
        (fun m => Work.SymQuot.DivOf.ptPlace_mem_bcOpens d x m (lift_mem_V d x hx)) := by

  classical
  set hmem : ∀ m : Fin n, (Work.SpecLin.ptPlace (x m)).point ∈ C.bcOpens F'' d.V :=
    fun m => Work.SymQuot.DivOf.ptPlace_mem_bcOpens d x m (lift_mem_V d x hx) with hmem_def
  change (charIdealGen F d).map (bcSec (C := C) F F'' d.V) =
    ∏ m : Fin n, placeIdeal (C.baseChange F'') (C.bcOpens F'' d.V)
      (Work.SpecLin.ptPlace (x m)) (hmem m)
  have hLI : (⊤ : (Work.SpecLin.specOf (K := K) F'').left.Opens) ≤
      ((Limits.Pi.lift x : Work.SpecLin.specOf (K := K) F'' ⟶
        Work.SymQuot.prod C.toOver n)).left ⁻¹ᵁ d.openOf := lift_mem_V d x hx
  let m₀ : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  haveI hVne : Nonempty d.V := nonempty_chart_of_hmem x d.V m₀ (hmem m₀)
  have hW : IsAffineOpen (C.bcOpens F'' d.V) :=
    BaseChange.isAffineOpen_bcOpens F'' d.V d.isAffineOpen_V
  haveI hDed : IsDedekindDomain Γ((C.baseChange F'').left, C.bcOpens F'' d.V) :=
    isDedekindDomain_sections (F := F'') (C := C.baseChange F'') hW
  -- Step 1: the image of the divisor ideal is contained in the product of the place ideals
  have hIJ : (charIdealGen F d).map (bcSec (C := C) F F'' d.V) ≤
      ∏ m : Fin n, placeIdeal (C.baseChange F'') (C.bcOpens F'' d.V)
        (Work.SpecLin.ptPlace (x m)) (hmem m) := by
    rw [charIdealGen, Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro y ⟨g, ⟨r, b, α, hg⟩, rfl⟩
    rw [hg, ← MvPolynomial.coeff_map (bcSec (C := C) F F'' d.V),
      genGenerator_map_eq d x hx b]
    exact coeff_prod_mem_prod_ideal
      (fun m => placeIdeal (C.baseChange F'') (C.bcOpens F'' d.V)
        (Work.SpecLin.ptPlace (x m)) (hmem m))
      (fun m i => secAlpha C F'' d.V (b i) - secConst C F'' d.V
        (valAtLift d x (lift_mem_V d x hx) m (b i)))
      (fun m i => secAlpha_sub_mem_placeIdeal d x (lift_mem_V d x hx) hmem m (b i)) α
  -- Step 2: for every place, an element of the ideal of small order at that place
  have exists_g : ∀ (z : (C.baseChange F'').Place) (hz : z.point ∈ C.bcOpens F'' d.V),
      ∃ g : Γ((C.baseChange F'').left, C.bcOpens F'' d.V),
        g ∈ (charIdealGen F d).map (bcSec (C := C) F F'' d.V) ∧ g ≠ 0 ∧
        placeOrder (C.baseChange F'') (C.bcOpens F'' d.V) (Ideal.span {g}) z hz =
          (Finset.univ.filter (fun m : Fin n => Work.SpecLin.ptPlace (x m) = z)).card := by
    intro z hz
    obtain ⟨a, ha_mem, ha_notmem⟩ :=
      exists_mem_placeIdeal_notMem_sq (C := C.baseChange F'') (C.bcOpens F'' d.V) hW z hz
    obtain ⟨b', hb'a, hb'1⟩ :=
      exists_crt_placeIdeal_sq_one (C := C.baseChange F'') hW
        (fun m => Work.SpecLin.ptPlace (x m)) hmem z hz a ha_notmem
    have hsq : (placeIdeal (C.baseChange F'') (C.bcOpens F'' d.V) z hz) ^ 2 ≤
        placeIdeal (C.baseChange F'') (C.bcOpens F'' d.V) z hz := by
      rw [pow_two]; exact Ideal.mul_le_left
    have hab : a - b' ∈ (placeIdeal (C.baseChange F'') (C.bcOpens F'' d.V) z hz) ^ 2 := by
      have h := neg_mem hb'a
      rwa [neg_sub] at h
    have hb'_mem : b' ∈ placeIdeal (C.baseChange F'') (C.bcOpens F'' d.V) z hz := by
      have h : b' = a + (b' - a) := by ring
      rw [h]; exact Ideal.add_mem _ ha_mem (hsq hb'a)
    have hb'_notmem2 : b' ∉ (placeIdeal (C.baseChange F'') (C.bcOpens F'' d.V) z hz) ^ 2 := by
      intro h
      apply ha_notmem
      have h' : a = b' - (b' - a) := by ring
      rw [h']
      exact Ideal.sub_mem _ h hb'a
    have hb'_ne : b' ≠ 0 := fun h0 => hb'_notmem2 (h0 ▸ Ideal.zero_mem _)
    have hb'1_notmem : b' - 1 ∉ placeIdeal (C.baseChange F'') (C.bcOpens F'' d.V) z hz := by
      intro h
      have h1 : (1 : Γ((C.baseChange F'').left, C.bcOpens F'' d.V)) ∈
          placeIdeal (C.baseChange F'') (C.bcOpens F'' d.V) z hz := by
        have h2 : a - 1 ∈ placeIdeal (C.baseChange F'') (C.bcOpens F'' d.V) z hz := by
          have hsplit : a - 1 = (a - b') + (b' - 1) := by ring
          rw [hsplit]
          exact Ideal.add_mem _ (hsq hab) h
        have h3 : (1 : Γ((C.baseChange F'').left, C.bcOpens F'' d.V)) = a - (a - 1) := by ring
        rw [h3]
        exact Ideal.sub_mem _ ha_mem h2
      exact (placeIdeal_isMaximal hW z hz).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
    let ev : Fin n → F'' := fun m => ptEval x d.V hmem m b'
    let Fm : Fin n → Γ((C.baseChange F'').left, C.bcOpens F'' d.V) :=
      fun m => b' - secConst C F'' d.V (ev m)
    let g : Γ((C.baseChange F'').left, C.bcOpens F'' d.V) := ∏ m, Fm m
    have hev_zero : ∀ m, Work.SpecLin.ptPlace (x m) = z → ev m = 0 := by
      intro m hm
      have hbm : b' ∈ placeIdeal (C.baseChange F'') (C.bcOpens F'' d.V)
          (Work.SpecLin.ptPlace (x m)) (hmem m) :=
        mem_placeIdeal_of_place_eq (C := C.baseChange F'') (V := C.bcOpens F'' d.V)
          hm.symm hz (hmem m) hb'_mem
      have h := (mem_placeIdeal_iff_ptEval_eq_zero x d.isAffineOpen_V hmem m b').mp hbm
      simpa [ev] using h
    have hev_one : ∀ m, Work.SpecLin.ptPlace (x m) ≠ z → ev m = 1 := by
      intro m hm
      have hmm : b' - 1 ∈ placeIdeal (C.baseChange F'') (C.bcOpens F'' d.V)
          (Work.SpecLin.ptPlace (x m)) (hmem m) := hb'1 m hm
      have h0 : ptEval x d.V hmem m (b' - 1) = 0 :=
        (mem_placeIdeal_iff_ptEval_eq_zero x d.isAffineOpen_V hmem m (b' - 1)).mp hmm
      simp only [map_sub, map_one] at h0
      have h1 : ptEval x d.V hmem m b' = 1 := sub_eq_zero.mp h0
      simpa [ev] using h1
    have hFm_zero : ∀ m, Work.SpecLin.ptPlace (x m) = z → Fm m = b' := by
      intro m hm
      show b' - secConst C F'' d.V (ev m) = b'
      rw [hev_zero m hm, map_zero, sub_zero]
    have hFm_one : ∀ m, Work.SpecLin.ptPlace (x m) ≠ z → Fm m = b' - 1 := by
      intro m hm
      show b' - secConst C F'' d.V (ev m) = b' - 1
      rw [hev_one m hm, map_one]
    have hFm_ne : ∀ m, Fm m ≠ 0 := by
      intro m
      by_cases hm : Work.SpecLin.ptPlace (x m) = z
      · rw [hFm_zero m hm]; exact hb'_ne
      · rw [hFm_one m hm]
        intro h0
        exact hb'1_notmem (h0.symm ▸ Ideal.zero_mem _)
    have hFm_order : ∀ m, placeOrder (C.baseChange F'') (C.bcOpens F'' d.V)
        (Ideal.span {Fm m}) z hz =
        (if Work.SpecLin.ptPlace (x m) = z then 1 else 0) := by
      intro m
      by_cases hm : Work.SpecLin.ptPlace (x m) = z
      · rw [if_pos hm, hFm_zero m hm]
        refine (placeOrder_span_eq_iff hW hb'_ne z hz 1).mpr ⟨?_, ?_⟩
        · rw [pow_one]; exact hb'_mem
        · exact hb'_notmem2
      · rw [if_neg hm, hFm_one m hm]
        refine (placeOrder_span_eq_iff hW ?_ z hz 0).mpr ⟨?_, ?_⟩
        · intro h0
          exact hb'1_notmem (h0.symm ▸ Ideal.zero_mem _)
        · rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
        · rw [pow_one]; exact hb'1_notmem
    have hg_mem : g ∈ (charIdealGen F d).map (bcSec (C := C) F F'' d.V) := by
      obtain ⟨r, bfam, fvec, hb'⟩ := exists_eq_sum_secAlpha (C := C) F'' d.V d.isAffineOpen_V b'
      have hchild := prod_sub_mem_charIdealGen_map d x hx bfam fvec
      have hevsum : ∀ m, ev m = ∑ i, fvec i * valAtLift d x hLI m (bfam i) := by
        intro m
        show ptEval x d.V hmem m b' = _
        rw [hb', map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_mul, ptEval_secConst, ptEval_secAlpha_eq_valAtLift]
      have hg_eq : g = ∏ m, ((∑ i, secConst C F'' d.V (fvec i) *
            secAlpha C F'' d.V (bfam i)) -
            secConst C F'' d.V (∑ i, fvec i * valAtLift d x hLI m (bfam i))) := by
        show (∏ m, (b' - secConst C F'' d.V (ev m))) = _
        refine Finset.prod_congr rfl (fun m _ => ?_)
        rw [hevsum m, hb']
      rwa [← hg_eq] at hchild
    have hg_order : placeOrder (C.baseChange F'') (C.bcOpens F'' d.V) (Ideal.span {g}) z hz =
        (Finset.univ.filter (fun m : Fin n => Work.SpecLin.ptPlace (x m) = z)).card := by
      have h1 : placeOrder (C.baseChange F'') (C.bcOpens F'' d.V) (Ideal.span {g}) z hz =
          ∑ m, placeOrder (C.baseChange F'') (C.bcOpens F'' d.V) (Ideal.span {Fm m}) z hz :=
        placeOrder_span_prod (C := C.baseChange F'') hW
          (Finset.univ : Finset (Fin n)) Fm (fun m _ => hFm_ne m) z hz
      rw [h1, Finset.sum_congr rfl (fun m _ => hFm_order m), Finset.sum_boole]
      simp
    exact ⟨g, hg_mem, Finset.prod_ne_zero_iff.mpr (fun m _ => hFm_ne m), hg_order⟩
  have hI_ne_bot : ((charIdealGen F d).map (bcSec (C := C) F F'' d.V)) ≠ ⊥ := by
    obtain ⟨g, hg_mem, hg_ne, -⟩ := exists_g (Work.SpecLin.ptPlace (x m₀)) (hmem m₀)
    intro hbot
    have hle : Ideal.span {g} ≤ ((charIdealGen F d).map (bcSec (C := C) F F'' d.V)) :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hg_mem)
    rw [hbot] at hle
    exact hg_ne (Ideal.span_singleton_eq_bot.mp (le_bot_iff.mp hle))
  have hJ_ne_bot : (∏ m : Fin n, placeIdeal (C.baseChange F'') (C.bcOpens F'' d.V)
      (Work.SpecLin.ptPlace (x m)) (hmem m)) ≠ ⊥ := by
    intro hbot
    have h := placeOrder_prod_placeIdeal (C := C.baseChange F'') (C.bcOpens F'' d.V) hW
      (fun m => Work.SpecLin.ptPlace (x m)) hmem (Work.SpecLin.ptPlace (x m₀)) (hmem m₀)
    rw [hbot, placeOrder_bot] at h
    have hpos : 0 < (Finset.univ.filter (fun m : Fin n =>
        Work.SpecLin.ptPlace (x m) = Work.SpecLin.ptPlace (x m₀))).card :=
      Finset.card_pos.mpr ⟨m₀, Finset.mem_filter.mpr ⟨Finset.mem_univ m₀, rfl⟩⟩
    omega
  refine eq_of_le_of_forall_placeOrder_le (C := C.baseChange F'') (C.bcOpens F'' d.V)
    hW hIJ hI_ne_bot hJ_ne_bot ?_
  intro z hz
  obtain ⟨g, hg_mem, hg_ne, hg_order⟩ := exists_g z hz
  rw [placeOrder_prod_placeIdeal (C := C.baseChange F'') (C.bcOpens F'' d.V) hW
    (fun m => Work.SpecLin.ptPlace (x m)) hmem z hz, ← hg_order]
  exact placeOrder_mono hW (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hg_mem))
    (fun h0 => hg_ne (Ideal.span_singleton_eq_bot.mp h0)) z hz

end Work.SymQuot.DivOf

/-- The statement as requested at the path of this file: the single-namespace form of
`Work.SymQuot.DivOf.Work.SymQuot.DivOf.charIdealGen_map_eq` (the declaration above, which sits in
the doubly opened namespace inherited from this file's original skeleton). -/
theorem charIdealGen_map_eq {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) {F'' : Type u} [Field F''] [Algebra K F'']
    [Algebra F F''] [IsScalarTower K F F''] (x : Fin n → Work.SpecLin.CurveFPt C F'')
    (hx : Work.SymQuot.Sym.powMap C n x =
      Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F'') p) :
    (charIdealGen F d).map (bcSec (C := C) F F'' d.V) =
      prodPtPlaceIdeal d x
        (fun m => Work.SymQuot.DivOf.ptPlace_mem_bcOpens d x m (lift_mem_V d x hx)) :=
  Work.SymQuot.DivOf.Work.SymQuot.DivOf.charIdealGen_map_eq d x hx

end Work.SymQuot.DivOf
